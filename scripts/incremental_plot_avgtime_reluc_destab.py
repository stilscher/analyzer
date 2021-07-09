import matplotlib.pyplot as plt
import sys
import os
import pandas as pd

assert(len(sys.argv) == 4)
args = sys.argv
dir1 = os.path.join(os.getcwd(),args[1])
dir2 = os.path.join(os.getcwd(),args[2])
repetitions = int(args[3])

column_names_orig = ["index_commit", "commit", "l_ins", "l_del", "l_max", "time-orig", "vars-orig", "evals-orig", "changed", "added", "removed", "changed_start", "new_start"]
orig = pd.read_csv(os.path.join(dir1, "incremental_runtime_0.log"), sep="\t", header=0, names=column_names_orig).fillna(0)

column_names_new = ["index_commit", "commit", "l_ins", "l_del", "l_max", "time-new", "vars-new", "evals-new", "changed", "added", "removed", "changed_start", "new_start"]
new = pd.read_csv(os.path.join(dir2, "incremental_runtime_0.log"), sep="\t", header=0, names=column_names_new).fillna(0)

for i in range(1, repetitions):
    next_orig = pd.read_csv(os.path.join(dir1, "incremental_runtime_" + str(i) + ".log"), sep="\t", header=0, names=column_names_orig).fillna(0)
    orig = orig.append(next_orig)
    
    next_new = pd.read_csv(os.path.join(dir2, "incremental_runtime_" + str(i) + ".log"), sep="\t", header=0, names=column_names_new).fillna(0)
    new = new.append(next_new)

orig = orig.groupby(by=["index_commit", "commit", "l_ins", "l_del", "l_max", "vars-orig", "evals-orig", "changed", "added", "removed", "changed_start", "new_start"]).agg(['mean','std'])
orig.columns = orig.columns.droplevel(0)
orig = orig.reset_index()
orig.rename(columns={'mean': 'time-orig-avg', 'std': 'time-orig-var'}, inplace=True)
new = new.groupby(by=["index_commit", "commit", "l_ins", "l_del", "l_max", "vars-new", "evals-new", "changed", "added", "removed", "changed_start", "new_start"]).agg(["mean", "std"])
new.columns = new.columns.droplevel(0)
new = new.reset_index()
new.rename(columns={'mean': 'time-new-avg', 'std': 'time-new-var'}, inplace=True)
df = pd.merge(orig, new, on=['index_commit','commit','l_ins','l_del','l_max','changed','added','removed','changed_start','new_start'])
print(df)

condition = (df['changed'] == 0) & (df['added'] == 0) & (df['removed'] == 0) & (df['changed_start'] == 0) & (df['new_start'] == 0)
df.drop(df.index[condition], inplace=True)
df.rename(columns={'l_max': 'changed LOC', 'time-orig-avg': 'Runtime of the basic incremental analysis in s', 'time-new-avg': 'Runtime of the analysis run with reluctant destabilization in s'}, inplace=True)

df.plot(x="index_commit", y=["changed LOC", "Runtime of the basic incremental analysis in s", "Runtime of the analysis run with reluctant destabilization in s"], kind="bar", yerr={'Runtime of the basic incremental analysis in s': df['time-orig-var'], 'Runtime of the analysis run with reluctant destabilization in s': df['time-new-var']}, width=0.7, figsize=(8,6), capsize=2)
plt.ylim(top=15)
plt.xlabel("Commit")
plt.legend(loc="upper right")
plt.savefig("avg_time_figlet_reluc_destab.pdf", bbox_inches = 'tight', pad_inches = 0)
