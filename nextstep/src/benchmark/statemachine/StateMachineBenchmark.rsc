module benchmark::statemachine::StateMachineBenchmark

import benchmark::statemachine::Scenario1;
import benchmark::statemachine::Scenario2;

import ide::CombinedAST;
import ide::CombinedModelFinder;
import ide::vis::ModelVisualizer;

import lang::nextstep::Syntax;
import Pipeline;

import util::MemoCacheClearer;

import util::Maybe;
import util::Benchmark;
import List;
import IO;
import Map;
import Set;

alias Statistic = tuple[int scenario, int nrOfStates, int nrOfTransitions, int currentRun, int nxtpToAlleTransTime, int alleToSmtTransTime, int solvingTime, int totalTime];
alias AggregatedStatistic = tuple[int scenario, int nrOfStates, int nrOfTransitions, BoxPlotData nxtpToAlleTransTime, BoxPlotData alleToSmtTransTime, BoxPlotData solvingTime, BoxPlotData totalTime];
alias BoxPlotData = tuple[int min, int max, int firstQuartile, int thirdQuartile, int mean];

private set[str] alleAlleMods() = {"translation::Relation","translation::Environment"};

void visScenario1(int nrOfStates) = visSolution(constructScenario1(nrOfStates));
void visScenario2(int nrOfStates) = visSolution(constructScenario2(nrOfStates));

void visSolution(Spec spc) {
  Problem p = translateNxtpToAlle(spc);
  ModelFinderResult sol = checkInitialSolution(p);

  if (sat(Model currentModel, Model (Domain) nextModel, void () stop) := sol) {
    renderModel(currentModel, nextModel, stop);
  }
}

void runBothScenarios() { runScenario1Benchmark(); runScenario2Benchmark(); }
void runScenario1Benchmark() = runBenchmark(1, 10, 11, 10, 3000, |project://nextstep/benchmark/result_scenario1.csv|, true);
void runScenario2Benchmark() = runBenchmark(2, 6, 40, 10, 3000, |project://nextstep/benchmark/result_scenario2.csv|, true);

void runBenchmark(int scenario, int startNrOfStates, int endNrOfStates, int runsPerConfig, int solverTimeOutInMs, loc csv, bool saveResult) {
  println("Warming up");
  Spec spc = scenario == 1 ? constructScenario1(startNrOfStates) : constructScenario2(startNrOfStates);
  
  for (int i <- [0..10]) {
    singleRun(scenario, startNrOfStates, i, spc, solverTimeOutInMs);
  } 
  println("Warm up done");
  
  clearMemoCache(alleAlleMods(), debug = true);

  map[int, list[Statistic]] benchmarkResult = ();
  
  for (int i <- [startNrOfStates..endNrOfStates+1]) {
    print("Start translating scenario <scenario> for <i> states");
    benchmarkResult[i-startNrOfStates] = [];
        
    Spec spc = scenario == 1 ? constructScenario1(i) : constructScenario2(i);
    writeFile(|project://nextstep/output/latestBM.nxst|, spc);
  
    for (int r <- [0..runsPerConfig]) {
      benchmarkResult[i-startNrOfStates] += singleRun(scenario, i, r, spc, solverTimeOutInMs);
      print(".");
    }
    print("done\n");
  } 
    
  if (saveResult) {
    println("Completely done, saving to csv");
    saveRawToCSV(benchmarkResult, startNrOfStates, csv);
    saveToCSV(benchmarkResult, startNrOfStates, csv);
  }
  else {
    println("Completely done, NOT saving to csv");
  }
}


private Statistic singleRun(int scenario, int nrOfStates, int currentRun, Spec spc, int solverTimeOutInMs) {
  clearMemoCache(alleAlleMods());

  tuple[int time, Problem p] trans = translate(spc);
  ModelFinderResult sol = checkInitialSolution(trans.p, timeOutInMs = solverTimeOutInMs);

  switch (sol) {
    case sat(Model currentModel, Model (Domain) nextModel, void () stop): {
      stop();
    }
    case timeout(): ; 
    default: {
      throw "Unable to solve nextep model. Unsat or unknown returned by solver";
    }
  }
    
  return <scenario, nrOfStates, nrOfStates*2 - 2, currentRun, trans.time, sol.translationTime, sol.solvingTime, trans.time + sol.translationTime + sol.solvingTime>; 
}

private tuple[int,Problem] translate(Spec spc) {
   int now = userTime();
   NxtpToAlleTransResult result = translateNxtpToAlle(spc);
   return <(userTime() - now) / 1000000, result.alleProblem>;
}

private void saveRawToCSV(map[int, list[Statistic]] benchmarkTimes, int startNrOfStates, loc csvLoc) {
 //int scenario, int nrOfStates, int nrOfTransitions, int currentRun, int nxtpToAlleTransTime, int alleToSmtTransTime, int solvingTime, int totalTime];
  str csv = "#Scenario,#States,#Transition,#Run,NxtpToAlleTransTime,AlleToSmtTransTime,SolvingTime,TotalTime <for (int i <- sort(domain(benchmarkTimes))) {>
            '<benchmarkTimes[i].scenario>,<benchmarkTimes[i].nrOfStates>,<benchmarkTimes[i].nrOfTransitions>,<benchmarkTimes[i].currentRun>,<benchmarkTimes[i].nxtpToAlleTransTime>,<benchmarkTimes[i].alleToSmtTransTime>,<benchmarkTimes[i].solvingTime>,<benchmarkTimes[i].totalTime><}>";
            
  writeFile(csvLoc[file = "<csvLoc.file>.raw"], csv);
}

private void saveToCSV(map[int, list[Statistic]] benchmarkTimes, int startNrOfStates, loc csvLoc) {
  println(benchmarkTimes);
  map[int, AggregatedStatistic] aggregated = aggregate(benchmarkTimes);
 
  str boxPlotDataToStr(BoxPlotData bpd) =
    "<bpd.min>,<bpd.max>,<bpd.firstQuartile>,<bpd.thirdQuartile>,<bpd.mean>";
 
  str nxtpToAlleCols = "NxtpToAlleMinTransTime,NxtpToAlleMaxTransTime,NxtpToAlleFirstQuartileTransTime,NxtpToAlleThirdQuartileTransTime, NxtpToAlleMeanTransTime";
  str alleToSmtCols = "AlleToSmtMinTransTime,AlleToSmtMaxTransTime,AlleToSmtFirstQuartileTransTime, AlleToSmtThirdQuartileTransTime, AlleToSmtMeanTransTime";
  str solvingTimeCols = "SolvingTimeMinTime,SolvingTimeMaxTime,SolvingTimeFirstQuartileTime, SolvingTimeThirdQuartileTime, SolvingTimeMeanTime";
  str totalTimeCols = "TotalTimeMinTime,TotalTimeMaxTime,TotalTimeFirstQuartileTime, TotalTimeThirdQuartileTime, TotalTimeMeanTime";
  
  str csv = "#Scenario,#States,#Transition,<nxtpToAlleCols>,<alleToSmtCols>,<solvingTimeCols>,<totalTimeCols> <for (int i <- sort(domain(aggregated))) {>
            '<aggregated[i].scenario>,<aggregated[i].nrOfStates>,<aggregated[i].nrOfTransitions>,<boxPlotDataToStr(aggregated[i].nxtpToAlleTransTime)>,<boxPlotDataToStr(aggregated[i].alleToSmtTransTime)>,<boxPlotDataToStr(aggregated[i].solvingTime)>,<boxPlotDataToStr(aggregated[i].totalTime)><}>";
            
  writeFile(csvLoc, csv);
}

private list[Statistic] sortByNxtpToAlleTranslationTime(list[Statistic] stats) 
  = sort(stats, bool (Statistic a, Statistic b) { return a.nxtpToAlleTransTime < b.nxtpToAlleTransTime;});

private list[Statistic] sortByAlleToSmtTranslationTime(list[Statistic] stats) 
  = sort(stats, bool (Statistic a, Statistic b) { return a.alleToSmtTransTime < b.alleToSmtTransTime;});
  
private list[Statistic] sortBySolvingTime(list[Statistic] stats) 
  = sort(stats, bool (Statistic a, Statistic b) { return a.solvingTime < b.solvingTime;});

private list[Statistic] sortByTotalTime(list[Statistic] stats) 
  = sort(stats, bool (Statistic a, Statistic b) { return a.totalTime < b.totalTime;});

private BoxPlotData aggregateBoxPlotData(list[Statistic] stats, list[Statistic] (list[Statistic]) sortFunc, int (Statistic) getTimeInstance) {
  list[Statistic] sortedStats = sortFunc(stats);
  println(sortedStats);
  
  int min = getTimeInstance(sortedStats[0]);
  int max = getTimeInstance(sortedStats[-1]);
    
  int getMean(list[Statistic] sorted) = (getTimeInstance(sorted[size(sorted)/2]) + getTimeInstance(sorted[size(sorted)/2+1])) / 2 when size(sorted) % 2 == 0;
  int getMean(list[Statistic] sorted) = getTimeInstance(sorted[size(sorted)/2]) when size(sorted) % 2 != 0;
  
  list[Statistic] bottomHalf = [sortedStats[i] | int i <- [0..size(sortedStats)/2]]; 
  list[Statistic] topHalf = [sortedStats[i] | int i <- [(size(sortedStats)%2 == 0 ? size(sortedStats) / 2 : (size(sortedStats) / 2) + 1) .. size(sortedStats)]]; 
  
  int mean = getMean(sortedStats);
  int firstQuartile = getMean(bottomHalf);
  int thirdQuartile = getMean(topHalf);
  
  return <min, max, firstQuartile, thirdQuartile, mean>;
}

private int getNxtpToAlleTransTime(Statistic s) = s.nxtpToAlleTransTime;
private int getAlleToSmtTransTime(Statistic s) = s.alleToSmtTransTime;
private int getSolvingTime(Statistic s) = s.solvingTime;
private int getTotalTime(Statistic s) = s.totalTime;
  
private map[int, AggregatedStatistic] aggregate(map[int, list[Statistic]] benchmarkTimes) {
  map[int, AggregatedStatistic] aggregated = ();
     
  for (int i <- benchmarkTimes) {
    BoxPlotData nxtpToAlle = aggregateBoxPlotData(benchmarkTimes[i], sortByNxtpToAlleTranslationTime, getNxtpToAlleTransTime);
    BoxPlotData alleToSmt = aggregateBoxPlotData(benchmarkTimes[i], sortByAlleToSmtTranslationTime, getAlleToSmtTransTime);
    BoxPlotData solvingTime = aggregateBoxPlotData(benchmarkTimes[i], sortBySolvingTime, getSolvingTime);  
    BoxPlotData totalTime = aggregateBoxPlotData(benchmarkTimes[i], sortByTotalTime, getTotalTime);  

    Statistic s = getOneFrom(benchmarkTimes[i]);

    aggregated[i] = <s.scenario, s.nrOfStates, s.nrOfTransitions, nxtpToAlle, alleToSmt, solvingTime, totalTime>;           
  }
  
  return aggregated;
}
