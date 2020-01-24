set datafile separator ";"
set terminal png size 550,430 enhanced
set output 'as.png'
set xlabel 'Input size (Thousands of "a"s)'
set ylabel 'Time (sec)'
set title 'Matching (a + b + ab)* with sequences of "a"s'
set key left top
plot 'as.csv' using 2 title 'vm' with linespoints,\
     'as.csv' using 3 title 're-app' with linespoints
set output 'abs.png'
set xlabel 'Input size (Thousands of "ab"s)'
set ylabel 'Time (sec)'
set title 'Matching (a + b + ab)* with sequences of "ab"s'
set key left top
plot 'abs.csv' using 2 title 'vm' with linespoints,\
     'abs.csv' using 3 title 're-app' with linespoints
set output 'backtrack.png'
set title 'Matching backtracking worst case'
set xlabel 'Input size (Thousands of "a"s)'
set key left top
plot 'back.csv' using 2 title 'vm' with linespoints,\
     'back.csv' using 3 title 're-app' with linespoints
set output 'back1.png'
set title 'Matching backtracking worst case'
set xlabel 'Input size (Thousands of "a"s)'
set key left top
plot 'back.csv' using 2 title 'vm' with linespoints
set output 'random.png'
set title 'Time against random RE and random strings'
set xlabel 'Input size (thousands of random inputs)'
set key left top
plot 'random.csv' using 2 title 're-app' with linespoints, \
     'random.csv' using 3 title 'vm' with linespoints