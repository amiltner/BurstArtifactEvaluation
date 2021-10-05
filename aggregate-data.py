import pandas as pd
import os
import pretty_csv

def ensure_dir(f):
    d = os.path.dirname(f)
    if not os.path.exists(d):
        os.makedirs(d)

ensure_dir("generated-data/")

dfburst=pd.read_csv("burst/generated-data/logical.csv")
dfleon=pd.read_csv("synquid/generated-data/data.csv")
dfsynquid=pd.read_csv("leon/generated-data/data.csv")
dfburstcorr=pd.read_csv("burst/manual-data/logical.csv")
dfleoncorr=pd.read_csv("leon/manual-data/logical.csv")
dfsynquidcorr=pd.read_csv("synquid/manual-data/logical.csv")
result1=dfburst.merge(dfleon,on="Test",how="outer")
result2=result1.merge(dfsynquid,on="Test",how="outer")
result3=result2.merge(dfburstcorr,on="Test",how="outer")
result4=result3.merge(dfleoncorr,on="Test",how="outer")
result5=result4.merge(dfsynquidcorr,on="Test",how="outer")
result6=result5.rename(columns={"ComputationTime":"BurstTime", "Correct":"BurstCorrect"})
result6.loc[result4.LeonSatisfies == "n","LeonTime"]="\\incorrect"
result7=result6[['Test','BurstTime','BurstCorrect','LeonTime','LeonCorrect','SynquidTime','SynquidCorrect']]
result7.to_csv("generated-data/logical.csv", index=False)
if os.path.exists("generated-data/logical_pretty.txt"):
    os.remove("generated-data/logical_pretty.txt")
pretty_csv.pretty_file("generated-data/logical.csv",new_filename="generated-data/logical_pretty.txt")

dfex=pd.read_csv("burst/generated-data/io.csv")
dfcorrect=pd.read_csv("burst/manual-data/io.csv")
result1=dfex.merge(dfcorrect,on="Test",how="outer")
result2=result1.rename(columns={"ComputationTime":"BurstTime", "Correct":"BurstCorrect", "SmythComputationTime":"SmythTime"})
result3=result2[['Test','BurstTime','BurstCorrect','SmythTime','SmythCorrect']]
result3.to_csv("generated-data/io.csv", index=False)
if os.path.exists("generated-data/io_pretty.txt"):
    os.remove("generated-data/io_pretty.txt")
pretty_csv.pretty_file("generated-data/io.csv",new_filename="generated-data/io_pretty.txt")

dfequiv=pd.read_csv("burst/generated-data/ref.csv")
result1 = dfequiv.rename(columns={"ComputationTime":"BurstTime", "LoopCount":"BurstIters", "SmythComputationTime":"SmythTime", "SmythLoopCount":"SmythIters"})
result2=result1[['Test','BurstTime','BurstIters','SmythTime','SmythIters']]
result2.to_csv("generated-data/ref.csv", index=False)
if os.path.exists("generated-data/ref_pretty.txt"):
    os.remove("generated-data/ref_pretty.txt")
pretty_csv.pretty_file("generated-data/ref.csv",new_filename="generated-data/ref_pretty.txt")

post_renamed=dfburst.rename(columns={"ComputationTime":"PostBurstTime", "SimpleComputationTime":"PostSimpleTime"})
post_simplified=post_renamed[['Test','PostBurstTime','PostSimpleTime']]
ex_renamed=dfex.rename(columns={"ComputationTime":"ExBurstTime", "SimpleComputationTime":"ExSimpleTime"})
ex_simplified=ex_renamed[['Test','ExBurstTime','ExSimpleTime']]
equiv_renamed=dfequiv.rename(columns={"ComputationTime":"EquivBurstTime", "SimpleComputationTime":"EquivSimpleTime"})
equiv_simplified=equiv_renamed[['Test','EquivBurstTime','EquivSimpleTime']]
result1=post_simplified.merge(ex_simplified,on="Test",how="outer")
result2=result1.merge(equiv_simplified,on="Test",how="outer")
total=float(len(result2.index))
burstex=float(len(result2[result2["ExBurstTime"] != "\\incorrect"]))
simpleex=float(len(result2[result2["ExSimpleTime"] != "\\incorrect"]))
burstequiv=float(len(result2[result2["EquivBurstTime"] != "\\incorrect"]))
simpleequiv=float(len(result2[result2["EquivSimpleTime"] != "\\incorrect"]))
burstpost=float(len(result2[result2["PostBurstTime"] != "\\incorrect"]))
simplepost=float(len(result2[result2["PostSimpleTime"] != "\\incorrect"]))
burstexprop=burstex/total
simpleexprop=simpleex/total
burstequivprop=burstequiv/total
simpleequivprop=simpleequiv/total
burstpostprop=burstpost/total
simplepostprop=simplepost/total
ablationdata={"": ["Burst","BurstDagger"], "IO": [burstexprop,simpleexprop], "Ref": [burstequivprop,simpleequivprop], "Logical": [burstpostprop,simplepostprop]}
df=pd.DataFrame(data=ablationdata)
df.to_csv("generated-data/ablation.csv", index=False)
if os.path.exists("generated-data/ablation_pretty.txt"):
    os.remove("generated-data/ablation_pretty.txt")
pretty_csv.pretty_file("generated-data/ablation.csv",new_filename="generated-data/ablation_pretty.txt")
