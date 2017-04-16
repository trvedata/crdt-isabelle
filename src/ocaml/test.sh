./network.native -id 0 -port 8765 -nodes \
  "localhost:8765;localhost:8766;localhost:8767;localhost:8768" &
./network.native -id 1 -port 8766 -nodes \
  "localhost:8765;localhost:8766;localhost:8767;localhost:8768" &
./network.native -id 2 -port 8767 -nodes \
  "localhost:8765;localhost:8766;localhost:8767;localhost:8768" &
./network.native -id 3 -port 8768 -nodes \
  "localhost:8765;localhost:8766;localhost:8767;localhost:8768" &

# to terminate nodes: pkill -9 network
# to probe nodes: nc 127.0.0.1 8765
# either log or showall