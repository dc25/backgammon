/// <reference path="webrtc.d.ts" />
var sharedKeyElement = document.getElementById('sharedKey');
var chatInputElement = document.getElementById('chatInput');
var joinGameInputElement = document.getElementById('joinGame');
var dc;
function initConnection() {
    dc = new DataConnection(sharedKeyElement.value, handleMessage);
}
// This is called on an incoming message from our peer
// You probably want to overwrite this to do something more useful!
function handleMessage(event) {
    console.log("Recieved Message: " + event.data);
    var chatLog = document.getElementById("transcript");
    chatLog.value = chatLog.value + event.data;
}
sharedKeyElement.onkeydown = function (e) {
    if (e.keyCode == 13) {
        initConnection();
        return false; // don't do default action (refresh page)
    }
    return true; // do default action (display char)
};
chatInputElement.onkeydown = function (e) {
    if (e.keyCode == 13) {
        dc.send(chatInputElement.value);
        return false; // don't do default action (refresh page)
    }
    return true; // do default action (display char)
};
