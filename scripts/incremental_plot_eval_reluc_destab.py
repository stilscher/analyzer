import matplotlib.pyplot as plt
import sys
import os
import pandas as pd
import numpy as np
from brokenaxes import brokenaxes

assert(len(sys.argv) == 3)
args = sys.argv
fileName1 = os.path.join(os.getcwd(),args[1])
fileName2 = os.path.join(os.getcwd(),args[2])

column_names_orig = ["index_commit", "commit", "l_ins", "l_del", "l_max", "time-orig", "vars-orig", "evals-orig", "changed", "added", "removed", "changed_start", "new_start"]
orig = pd.read_csv(fileName1, sep="\t", skiprows=[0], names=column_names_orig).fillna(0)
column_names_new = ["index_commit", "commit", "l_ins", "l_del", "l_max", "time-new", "vars-new", "evals-new", "changed", "added", "removed", "changed_start", "new_start"]
new = pd.read_csv(fileName2, sep="\t", skiprows=[0], names=column_names_new).fillna(0)

df = pd.merge(orig, new, on=['index_commit','commit','l_ins','l_del','l_max','changed','added','removed','changed_start','new_start'])

condition = (df['changed'] == 0) & (df['added'] == 0) & (df['removed'] == 0) & (df['changed_start'] == 0) & (df['new_start'] == 0)
df.drop(df.index[condition], inplace=True)
df['evals-orig']=df['evals-orig']/100
df['evals-new']=df['evals-new']/100
df.rename(columns={'l_max': 'changed LOC', 'evals-orig': 'Previously required evaluations / 100', 'evals-new': 'Evaluations with reluctant destabilization / 100'}, inplace=True)

f, (ax, ax2) = plt.subplots(2, 1, sharex=True)
# plot the same data on both axes
df.plot(ax=ax, x="index_commit", y=["changed LOC", "Previously required evaluations / 100", "Evaluations with reluctant destabilization / 100"], kind="bar", width=0.7, figsize=(8,6))
df.plot(ax=ax2, x="index_commit", y=["changed LOC", "Previously required evaluations / 100", "Evaluations with reluctant destabilization / 100"], kind="bar", width=0.7, figsize=(8,6))

# limit the view to different portions of the data
ax.set_ylim(390,480)  # outliers only
ax2.set_ylim(0, 90)  # most of the data

# hide the spines between ax and ax2
ax.spines['bottom'].set_visible(False)
ax2.spines['top'].set_visible(False)
# format x axis ticks and labels
ax.tick_params(axis='x',which='both',bottom=False,top=False,labelbottom=False)
ax2.tick_params(axis='x',which='both',bottom=True,top=False,labelbottom=True)
# diagonal marks at broken y axis
d = .01
kwargs = dict(transform=ax.transAxes, color='k', clip_on=False)
ax.plot((-d, +d), (-d, +d), **kwargs)
ax.plot((1 - d, 1 + d), (-d, +d), **kwargs)
kwargs.update(transform=ax2.transAxes)
ax2.plot((-d, +d), (1 - d, 1 + d), **kwargs)
ax2.plot((1 - d, 1 + d), (1 - d, 1 + d), **kwargs)

#plt.yticks(np.concatenate(np.arrange(0,380,20),np.arrange(400,450,20))
plt.subplots_adjust(hspace=0.1)
plt.xlabel("Commit")
plt.legend(loc="upper right")
ax2.get_legend().remove()
plt.savefig("evaluations_figlet_reluc_destab.pdf", bbox_inches = 'tight', pad_inches = 0)
