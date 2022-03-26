import * as _eldb from "./runtime/main.js";
let x = false;
let print = (console).log;
let y = (() => {
    if (x) {
        return (() => {
            return print("wow okay", )
        })();
    } else {
        return (() => {
            return print(2, )
        })();
    }
})();
let a = (console).log("hi there", );