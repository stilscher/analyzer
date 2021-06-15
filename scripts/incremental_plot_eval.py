import matplotlib.pyplot as plt
import sys
import os
import pandas as pd

assert(len(sys.argv) == 3)
args = sys.argv
fileName1 = os.path.join(os.getcwd(),args[1])
fileName2 = os.path.join(os.getcwd(),args[2])

column_names_orig = ["index_commit", "commit", "l_ins", "l_del", "l_max", "time-orig", "vars-orig", "evals-orig", "changed", "added", "removed", "changed_start", "new_start"]
orig = pd.read_csv(fileName1, sep=";", skiprows=[0], names=column_names_orig).fillna(0)
column_names_new = ["index_commit", "commit", "l_ins", "l_del", "l_max", "time-new", "vars-new", "evals-new", "changed", "added", "removed", "changed_start", "new_start"]
new = pd.read_csv(fileName2, sep=";", skiprows=[0], names=column_names_new).fillna(0)

df = pd.merge(orig, new, on=['index_commit','commit','l_ins','l_del','l_max','changed','added','removed','changed_start','new_start'])

condition = (df['changed'] == 0) & (df['added'] == 0) & (df['removed'] == 0) & (df['changed_start'] == 0) & (df['new_start'] == 0)
df.drop(df.index[condition], inplace=True)
df['evals-orig']=df['evals-orig']/100
df['evals-new']=df['evals-new']/100
df.rename(columns={'l_max': 'LOC', 'evals-orig': 'Previously required evaluations / 100', 'evals-new': 'Evaluations utilizing intra-functional changes / 100'}, inplace=True)

df.plot(x="index_commit", y=["LOC", "Previously required evaluations / 100", "Evaluations utilizing intra-functional changes / 100"], kind="bar", width=0.7, figsize=(8,6))
plt.ylim(top=100)
plt.xlabel("Commit")
plt.legend(loc="upper right")
plt.savefig("evaluations_figlet_intra_func_changes.pdf", bbox_inches = 'tight', pad_inches = 0)
