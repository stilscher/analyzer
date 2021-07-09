import matplotlib.pyplot as plt
import sys
import os
import pandas as pd

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
df.rename(columns={'l_max': 'changed LOC', 'evals-orig': 'Previously required evaluations / 100', 'evals-new': 'Evaluations utilizing intra-functional changes / 100'}, inplace=True)

f, (ax, ax2, ax3) = plt.subplots(3, 1, sharex=True)
# plot the same data on both axes
df.plot(ax=ax, x="index_commit", y=["changed LOC", "Previously required evaluations / 100", "Evaluations utilizing intra-functional changes / 100"], kind="bar", width=0.7, figsize=(8,6))
df.plot(ax=ax2, x="index_commit", y=["changed LOC", "Previously required evaluations / 100", "Evaluations utilizing intra-functional changes / 100"], kind="bar", width=0.7, figsize=(8,6))
df.plot(ax=ax3, x="index_commit", y=["changed LOC", "Previously required evaluations / 100", "Evaluations utilizing intra-functional changes / 100"], kind="bar", width=0.7, figsize=(8,6))

# limit the view to different portions of the data
ax.set_ylim(540,620) # outliers only
ax2.set_ylim(390,470)
ax3.set_ylim(0, 80)  # most of the data

# hide the spines between ax and ax2
ax.spines['bottom'].set_visible(False)
ax2.spines['bottom'].set_visible(False)
ax2.spines['top'].set_visible(False)
ax3.spines['top'].set_visible(False)
# format x axis ticks and labels
ax.tick_params(axis='x',which='both',bottom=False,top=False,labelbottom=False)
ax2.tick_params(axis='x',which='both',bottom=False,top=False,labelbottom=False)
ax3.tick_params(axis='x',which='both',bottom=True,top=False,labelbottom=True)
# diagonal marks at broken y axis
d = .01
kwargs = dict(transform=ax.transAxes, color='k', clip_on=False)
ax.plot((-d, +d), (-d, +d), **kwargs)
ax.plot((1 - d, 1 + d), (-d, +d), **kwargs)
kwargs.update(transform=ax2.transAxes)
ax2.plot((-d, +d), (1 - d, 1 + d), **kwargs)
ax2.plot((1 - d, 1 + d), (1 - d, 1 + d), **kwargs)
ax2.plot((-d, +d), (-d, +d), **kwargs)
ax2.plot((1 - d, 1 + d), (-d, +d), **kwargs)
kwargs.update(transform=ax3.transAxes)
ax3.plot((-d, +d), (1 - d, 1 + d), **kwargs)
ax3.plot((1 - d, 1 + d), (1 - d, 1 + d), **kwargs)

plt.subplots_adjust(hspace=0.1)
plt.xlabel("Commit")
plt.legend(loc="upper right")
ax2.get_legend().remove()
ax3.get_legend().remove()
plt.savefig("evaluations_figlet_intra_func_changes.pdf", bbox_inches = 'tight', pad_inches = 0)

