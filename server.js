const express = require('express');
const path = require('path');
const os = require('os');

const app = express();
const PORT = process.env.PORT || 3000;

app.use(express.static(path.join(__dirname)));

app.listen(PORT, '0.0.0.0', () => {
  console.log('');
  console.log('  ╔══════════════════════════════════════╗');
  console.log('  ║   4×4 卡诺图工具  K-Map Tool        ║');
  console.log('  ╚══════════════════════════════════════╝');
  console.log('');
  console.log('  Local:    http://localhost:' + PORT);
  console.log('  Network:  http://' + getLocalIP() + ':' + PORT);
  console.log('');
  console.log('  按 Ctrl+C 停止服务');
  console.log('');
});

function getLocalIP() {
  const interfaces = os.networkInterfaces();
  for (const name of Object.keys(interfaces)) {
    for (const iface of interfaces[name]) {
      if (iface.family === 'IPv4' && !iface.internal) {
        return iface.address;
      }
    }
  }
  return '0.0.0.0';
}
