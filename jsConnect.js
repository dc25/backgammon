/// <reference path="webrtc.d.ts" />
var dc;
function jsConnect(connectionID) {
    return new DataConnection(connectionID, handleMessage);
}
// This is called on an incoming message from our peer
// You probably want to overwrite this to do something more useful!
function handleMessage(event) {
    console.log("Recieved Message: " + event.data);
    var chatLog = document.getElementById("transcript");
    chatLog.value = chatLog.value + event.data;
}
