./build operational &&
./bin/kboogie --definition operational test/operational/control-flow/while.bpl

./build boogie;



for i in {150..200}; do
echo "Step $i"
"ext/k/k-distribution/target/release/k/bin/krun" --search-final \
    --directory .build/defn/boogie \
    .build/test/ --depth $i;
echo -e "${BLUE}==================================================${NC}"
done




for i in {10..30}; do
echo "Step $i"
./bin/kboogie --full --definition operational test/operational/control-flow/while.bpl --depth $i
echo -e "${BLUE}==================================================${NC}"
done


for i in {10..30}; do
echo "Step $i"
./bin/kboogie --definition verification test/operational/arithmetic/arrays.bpl --depth $i
echo -e "${BLUE}==================================================${NC}"
done
