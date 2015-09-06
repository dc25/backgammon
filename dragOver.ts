///<reference path="../DefinitelyTyped/velocity-animate/velocity-animate.d.ts" />
///<reference path="../DefinitelyTyped/interactjs/interact.d.ts" />

"use strict";

var selectedElement:SVGElement = null;
var currentX = 0;
var currentY = 0;

function cloneToTop(oldEl){
  // already at top, don't go farther…
  if(oldEl.atTop==true) 
      return oldEl;

  // make a copy of this node
  var el = oldEl.cloneNode(true);

  // select all draggable elements, none of them are at top anymore
  var dragEls= oldEl.ownerDocument.documentElement.querySelectorAll('.draggable');
  for(var i=0; i<dragEls.length; i++){
    dragEls[i].atTop=null;
  }

  var parent = oldEl.parentNode;
  // remove the original node
  parent.removeChild(oldEl);
  // insert our new node at top (last element drawn is first visible in svg)
  parent.appendChild(el);
  // Tell the world that our new element is at Top
  el.atTop= true;
  return el;
}

function selectElement(evt) {
  var evtTarget:SVGElement = evt.target
  selectedElement = cloneToTop(evtTarget);
}
    
function moveElement(evt) {

  var cx = parseFloat(selectedElement.getAttribute("cx"));
  var cy = parseFloat(selectedElement.getAttribute("cy"));

  cx += evt.dx/3.1;
  cy += evt.dy/3.1;
  
  selectedElement.setAttribute("cx", cx.toString());
  selectedElement.setAttribute("cy", cy.toString());

}
    
// Provide for callback into haskell when object stops being dragged.
var dropCheckerCallback;

function deselectElement(evt) {
  if(selectedElement != null) {

      dropCheckerCallback( selectedElement.getAttribute("class"), 
                           parseFloat(selectedElement.getAttribute("cx")),
                           parseFloat(selectedElement.getAttribute("cy")));

      selectedElement = null;
  }
}

// Called from haskell
function setDropCheckerCallback_ffi(cb) {
    dropCheckerCallback = cb;

    // target elements with the "draggable" class
    interact('.draggable')
      .draggable({
        onstart: selectElement,
        onmove: moveElement,
        onend: deselectElement
      });
}

// Use velocity.js to slide a circle to a point.
function animateCircle_ffi (elem, cx, cy, duration) {
    $(elem).velocity({ cx: cx, cy: cy }, { duration: duration });
}
