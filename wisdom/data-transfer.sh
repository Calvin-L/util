# sync the contents of two folders
rsync [flags] folderA/ folderB/

# resume-able sync with other niceties
rsync -avzH --progress --append src/ dst/

# resume a failed curl download
curl -O URL # suppose this fails
curl -C - -O URL # resume with this (assuming server supports byte ranges)
