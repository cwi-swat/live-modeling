module benchmark::statemachine::StateMachineBenchmark

import benchmark::statemachine::Scenario1;
import benchmark::statemachine::Scenario2;

import ide::CombinedAST;
import ide::CombinedModelFinder;
import ide::vis::ModelVisualizer;

import util::MemoCacheClearer;

import util::Maybe;
import List;
import IO;
import Map;
import Set;

alias Statistic = tuple[int scenario, int nrOfStates, int nrOfTransitions, int currentRun, int translationTime, int solvingTime, int totalTime];

private set[str] alleAlleMods() = {"translation::Relation","translation::Environment"};

void visScenario1(int nrOfStates) = visSolution(constructScenario1Problem(nrOfStates));
void visScenario2(int nrOfStates) = visSolution(constructScenario2Problem(nrOfStates));

void visSolution(Problem p) {
  ModelFinderResult sol = checkInitialSolution(p);

  if (sat(Model currentModel, Model (Domain) nextModel, void () stop) := sol) {
    renderModel(currentModel, nextModel, stop);
  }
}

void runBothScenarios() { runScenario1Benchmark(); runScenario2Benchmark(); }
void runScenario1Benchmark() = runBenchmark(1, 10, 100, 20, |project://nextstep/benchmark/result_scenario1.csv|, true);
void runScenario2Benchmark() = runBenchmark(2, 10, 20, 10, |project://nextstep/benchmark/result_scenario2.csv|, true);

void runBenchmark(int scenario, int startNrOfStates, int endNrOfStates, int runsPerConfig, loc csv, bool saveResult) {
  println("Warming up");
  Problem warmup = scenario == 1 ? constructScenario1Problem(endNrOfStates/2) : constructScenario2Problem(endNrOfStates/2);
  for (int i <- [0..10]) {
    singleRun(scenario, endNrOfStates/2, i, warmup);
  } 
  println("Warm up done");
  
  clearMemoCache(alleAlleMods(), debug = true);

  map[int, list[Statistic]] benchmarkResult = ();
  
  for (int i <- [startNrOfStates..endNrOfStates+1]) {
    print("Start translating scenario <scenario> for <i> states");
    benchmarkResult[i-startNrOfStates] = [];
        
    Problem p = scenario == 1 ? constructScenario1Problem(i) : constructScenario2Problem(i);
    for (int r <- [0..runsPerConfig]) {
      benchmarkResult[i-startNrOfStates] += singleRun(scenario, i, r, p);
      print(".");
    }
    print("done\n");
  } 
    
  if (saveResult) {
    println("Completely done, saving to csv");
    saveToCSV(benchmarkResult, startNrOfStates, csv);
  }
  else {
    println("Completely done, NOT saving to csv");
  }
}


private Statistic singleRun(int scenario, int nrOfStates, int currentRun, Problem p) {
  clearMemoCache(alleAlleMods());

  ModelFinderResult sol = checkInitialSolution(p);
  
  if (sat(Model currentModel, Model (Domain) nextModel, void () stop) := sol) {
    stop();
  } else {
    throw "Model finder did not return SAT.";
  }      
  
  return <scenario, nrOfStates, nrOfStates*2 - 2, currentRun, sol.translationTime, sol.solvingTime, 0>; 
}

private void saveToCSV(map[int, list[Statistic]] benchmarkTimes, int startNrOfStates, loc csvLoc) {
  println(benchmarkTimes);
  map[int, Statistic] aggregated = aggregate(benchmarkTimes);
  str csv = "#Scenario,#States,#Transition,TranslationTime,SolvingTime,TotalTime <for (int i <- sort(domain(aggregated))) {>
            '<aggregated[i].scenario>,<aggregated[i].nrOfStates>,<aggregated[i].nrOfTransitions>,<aggregated[i].translationTime>,<aggregated[i].solvingTime>,<aggregated[i].totalTime><}>";
            
  writeFile(csvLoc, csv);
}

private list[Statistic] sortByTranslationTime(list[Statistic] stats) 
  = sort(stats, bool (Statistic a, Statistic b) { return a.translationTime < b.translationTime;});
  
private list[Statistic] sortBySolvingTime(list[Statistic] stats) 
  = sort(stats, bool (Statistic a, Statistic b) { return a.solvingTime < b.solvingTime;});
  
private map[int, Statistic] aggregate(map[int, list[Statistic]] benchmarkTimes) {
  map[int, Statistic] aggregated = ();
     
  for (int i <- benchmarkTimes) {
    list[Statistic] sortedByTranslationTime = sortByTranslationTime(benchmarkTimes[i]);
    list[Statistic] sortedBySolvingTime = sortBySolvingTime(benchmarkTimes[i]);

    // get the means
    int translationMean;
    int solvingMean;
    if (size(sortedByTranslationTime)%2 == 0) {
      translationMean = (sortedByTranslationTime[size(sortedByTranslationTime)/2].translationTime + sortedByTranslationTime[size(sortedByTranslationTime)/2 + 1].translationTime) / 2;
      solvingMean = (sortedBySolvingTime[size(sortedBySolvingTime)/2].solvingTime + sortedBySolvingTime[size(sortedBySolvingTime)/2 + 1].solvingTime) / 2;
    } else {
      translationMean = sortedByTranslationTime[size(sortedByTranslationTime)/2].translationTime;
      solvingMean = sortedBySolvingTime[size(sortedBySolvingTime)/2].translationTime;
    } 
    Statistic s = getOneFrom(benchmarkTimes[i]);

    aggregated[i] = <s.scenario, s.nrOfStates, s.nrOfTransitions, 0, translationMean, solvingMean, translationMean + solvingMean>;           
  }
  
  return aggregated;
}
