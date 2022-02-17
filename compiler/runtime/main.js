function isObject(obj) {
  return typeof obj === "object" && obj !== null;
}

function isUppercase(str) {
  return str.length > 0 && str.charAt(0) === str.charAt(0).toUpperCase();
}

function variantName(obj) {
  let keys = Object.keys(obj);
  if (keys.length === 1 && isUppercase(keys[0])) {
    return keys[0];
  } else {
    return null;
  }
}

function isVariant(obj) {
  return variantName(obj) !== null;
}

// Note: This has to conform to Pattern::captures_in_order in the rust.
export function matches(pattern, expression) {
  if (isObject(pattern) && isObject(expression)) {
    if (
      isVariant(pattern) &&
      isVariant(expression) &&
      variantName(pattern) == variantName(expression)
    ) {
      return matches(Object.values(pattern)[0], Object.values(expression)[0]);
    } else {
      let res = [];
      for (const key in pattern) {
        if (expression[key] === undefined) {
          return null;
        }
        let match = matches(pattern[key], expression[key]);
        if (match === null) {
          return null;
        }
        res.concat(match);
      }
      return res;
    }
  } else if (pattern === "__eldb_pat") {
    return [expression];
  } else if (pattern === "__eldb_wildcard") {
    return [];
  }
  return null;
}

export function unhandled_match() {
  throw "unhandled match statement";
}
