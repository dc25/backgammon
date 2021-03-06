///<reference path="velocity-animate/velocity-animate.d.ts" />
///<reference path="interactjs/interact.d.ts" />
"use strict";
// A & B are required by haste for callbacks.  See: 
// https://github.com/valderman/haste-compiler/blob/master/doc/js-externals.txt
// for details.
var A;
var B;
// For debugging.
function showAlert_ffi(msg) {
    alert(msg);
}
// For debugging.
function consoleLog_ffi(msg) {
    console.log(msg);
}
var selectedElement = null;
var currentX = 0;
var currentY = 0;
function cloneToTop(oldEl) {
    // already at top, don't go farther…
    if (oldEl.atTop == true)
        return oldEl;
    // make a copy of this node
    var el = oldEl.cloneNode(true);
    // select all draggable elements, none of them are at top anymore
    var dragEls = oldEl.ownerDocument.documentElement.querySelectorAll('.draggable');
    for (var i = 0; i < dragEls.length; i++) {
        dragEls[i].atTop = null;
    }
    var parent = oldEl.parentNode;
    // remove the original node
    parent.removeChild(oldEl);
    // insert our new node at top (last element drawn is first visible in svg)
    parent.appendChild(el);
    // Tell the world that our new element is at Top
    el.atTop = true;
    return el;
}
function selectElement(evt) {
    var evtTarget = evt.target;
    selectedElement = cloneToTop(evtTarget);
}
function moveElement(evt) {
    var cx = parseFloat(selectedElement.getAttribute("cx"));
    var cy = parseFloat(selectedElement.getAttribute("cy"));
    cx += evt.dx / 3.1;
    cy += evt.dy / 3.1;
    selectedElement.setAttribute("cx", cx.toString());
    selectedElement.setAttribute("cy", cy.toString());
}
// Provide for callback into haskell when object stops being dragged.
var dropCheckerCallback;
function deselectElement(evt) {
    if (selectedElement != null) {
        B(A(dropCheckerCallback, [[0, selectedElement.getAttribute("class")], [0, parseFloat(selectedElement.getAttribute("cx"))], [0, parseFloat(selectedElement.getAttribute("cy"))], 0]));
        selectedElement = null;
    }
}
// Called from haskell
function setDropCheckerCallback_ffi(cb) {
    dropCheckerCallback = cb;
    // target elements with the "draggable" class
    interact('.draggable').draggable({
        onstart: selectElement,
        onmove: moveElement,
        onend: deselectElement
    });
}
// Use velocity.js to slide a circle to a point.
function animateCircle_ffi(elem, cx, cy, duration) {
    $(elem).velocity({ cx: cx, cy: cy }, { duration: duration });
}
