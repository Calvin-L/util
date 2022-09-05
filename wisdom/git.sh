# Git tips and tricks

# Squash all of history down to a single fresh commit
# https://stackoverflow.com/a/23486788/784284
git reset "$(git commit-tree 'HEAD^{tree}' -m 'A fresh start')"

# Although, you'll probably want to change the message and GPG-sign, so next:
git commit --amend
