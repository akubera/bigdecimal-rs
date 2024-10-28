
# git tasks to start next development version
prepare-dev-version v:
    git checkout trunk
    gsed -zE -i 's/(name = "bigdecimal"\nversion )= [^\n]*/\1= "{{v}}+dev"/' Cargo.toml Cargo.lock
    git add Cargo.toml Cargo.lock
    git commit -m 'Begin v{{v}} development'


# git tasks to run to merge trunk into master
prepare-release v:
    git checkout trunk
    cargo clippy
    gsed -zE -i 's/(name = "bigdecimal"\nversion )= [^\n]*/\1= "{{v}}"/' Cargo.toml Cargo.lock
    git add Cargo.toml Cargo.lock
    git commit -m 'Version {{v}}'
    git checkout master
    git merge trunk --no-ff -m 'v{{v}}'
    # git tag 'v{{v}}'

