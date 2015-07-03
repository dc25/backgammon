/// <reference path="webrtc.d.ts" />
var sharedKeyElement = document.getElementById('sharedKey');
var chatInputElement = document.getElementById('chatInput');
var dc;
// This is called on an incoming message from our peer
// You probably want to overwrite this to do something more useful!
function handleMessage(event) {
    console.log("Recieved Message: " + event.data);
    var chatLog = document.getElementById("transcript");
    chatLog.value = chatLog.value + event.data;
}
sharedKeyElement.onkeydown = function (e) {
    if (e.keyCode == 13) {
        dc = new DataConnection(sharedKeyElement.value, handleMessage);
    }
};
chatInputElement.onkeydown = function (e) {
    if (e.keyCode == 13) {
        dc.send(chatInputElement.value);
    }
};
