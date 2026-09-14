

// @Require 0 <= x <= 100
int get_percentile(int x);

// @Assume x >= 0
// @Safety heap_ok()
int get_latest(int x);

int y;

int value() {
    int latest = get_latest(y);
    return get_percentile(latest);
}


// @Safety heap_ok()
void main () {
    assume heap_ok();
    assert heap_ok();
    int ghost1 = y;
    assert heap_ok();
    int ghost2 = get_latest(ghost1);
    assert heap_ok();
    int x = ghost2 + ghost1; 
    assert heap_ok();
}