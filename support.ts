
function jsCreateElemNS(ns, tag) {
    return document.createElementNS(ns, tag);
}

function jsSetAttrNS(elem, prop, val) {
    elem.setAttributeNS(null, prop, val);
}

