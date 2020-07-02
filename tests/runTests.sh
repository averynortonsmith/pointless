
function runTests {
  for file in "${@:2}"; do
    echo ${file}
    touch "${file}.out"
    bin/debug ${file} "$1" 2>&1 | diff --color "${file}.out" -
  done
}

function commit {
  for file in "${@:2}"; do
    echo "${file}.out"
    touch "${file}.out"
    bin/debug ${file} "$1" 2>&1 | diff --color "${file}.out" -
    bin/debug ${file} "$1" &> "${file}.out"
  done
}

if [[ "$1" == "--commit" ]]; then
  commit "${@:2}"
else
  runTests "${@:2}"
fi
