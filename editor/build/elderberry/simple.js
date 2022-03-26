import * as _eldb from "./runtime/main.js";
let snd = ((_eldb_a0, _eldb_a1, ) => {
    let _eldb_res;
    if (_eldb_res = _eldb.matches("__eldb_pat", _eldb_a0)) {
        let [x, ] = _eldb_res;
        if (_eldb_res = _eldb.matches("__eldb_pat", _eldb_a1)) {
            let [y, ] = _eldb_res;
            return y;
        }
    }
    _eldb.unhandled_match()
});
let main = (() => {
    let x = 2;
    return snd({
        foo: (() => {})(),
    }, {
        Apple: [x, x, x, ]
    }, )
})();