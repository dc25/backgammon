"use strict";


// A & B are required by haste for callbacks.  See: 
// https://github.com/valderman/haste-compiler/blob/master/doc/js-externals.txt
// for details.
var A:any;
var B:any;

// For debugging.
function showAlert_ffi(msg:string) {
    alert(msg);
}

// For debugging.
function consoleLog_ffi(msg:string) {
    console.log(msg);
}



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

// from http://stackoverflow.com/questions/5898656/test-if-an-element-contains-a-class
function hasClass(element:SVGElement, cls:String) {
    return (' ' + element.getAttribute("class") + ' ').indexOf(' ' + cls + ' ') > -1;
}

function selectElement(evt) {
  var evtTarget:SVGElement = evt.target
  selectedElement = cloneToTop(evtTarget);
  currentX = evt.clientX;
  currentY = evt.clientY;

  selectedElement.setAttribute("onmousemove", "moveElement(evt)");
  selectedElement.setAttribute("onmouseout", "deselectElement(evt)");
  selectedElement.setAttribute("onmouseup", "deselectElement(evt)");
}
    
function moveElement(evt) {

  var dx = evt.clientX - currentX;
  var dy = evt.clientY - currentY;

  var cx = parseFloat(selectedElement.getAttribute("cx"));
  var cy = parseFloat(selectedElement.getAttribute("cy"));

  cx += dx/3.1;
  cy += dy/3.1;
  
  selectedElement.setAttribute("cx", cx.toString());
  selectedElement.setAttribute("cy", cy.toString());

  currentX = evt.clientX;
  currentY = evt.clientY;

}
    
// Provide for callback into haskell when object stops being dragged.
var dropCheckerCallback;

function deselectElement(evt) {
  if(selectedElement != null) {
      selectedElement.removeAttribute("onmousemove");
      selectedElement.removeAttribute("onmouseout");
      selectedElement.removeAttribute("onmouseup");
      B(A(dropCheckerCallback, [ [0,selectedElement.getAttribute("class")], 
                                 [0,parseFloat(selectedElement.getAttribute("cx"))], 
                                 [0,parseFloat(selectedElement.getAttribute("cy"))], 
                                 0]));
      selectedElement = null;
  }
}
        
// Called from haskell
function setDropCheckerCallback_ffi(cb) {
    dropCheckerCallback = cb;
}

