// weather_stations.js

// ---------------------------------------------------------------
// CORE SETUP
// ---------------------------------------------------------------
d3.selectAll('svg > *').remove();

// ---------------------------------------------------------------
// MAIN NETWORK LAYOUT & POSITIONING
// ---------------------------------------------------------------
const CEN_X = 220;
const CEN_Y = 200;
const RAD = 140;

const CTRL_X = 350, CTRL_Y = 15, CTRL_W = 150;
const LEG_X = 10, LEG_Y = 360, LEG_W = 480, LEG_H = 260;

// ---------------------------------------------------------------
// ROBUST STATE EXTRACTION
// ---------------------------------------------------------------
function getAllStates() {
  const out = [];
  if (!instances || !instances.length) return out;

  const stationAtoms = instances[0].signature("Station").atoms();
  const stations = stationAtoms.map(a => String(a.id ? a.id() : a).trim());

  const poses = {};
  const degs = (Math.PI * 2) / stations.length;
  stations.forEach((sId, i) => {
    poses[sId] = {
      x: CEN_X + RAD * Math.cos((i * degs) - Math.PI / 2),
      y: CEN_Y + RAD * Math.sin((i * degs) - Math.PI / 2)
    };
  });

  instances.forEach((inst) => {
    let stateData = { nodes: {}, edges: [] };

    stations.forEach(sId => {
      stateData.nodes[sId] = {
        id: sId,
        name: sId.replace(/[0-9]/g, ""),
        isFailed: false,
        isByzantine: false,
        stormInfo: "waiting",
        parentBeats: 0,
        backupBeats: 0,
        x: poses[sId].x,
        y: poses[sId].y
      };
    });

    const getStr = a => String(a.id ? a.id() : a).trim();

    const process2 = (fieldStr, cb) => {
      try {
        let f = inst.field(fieldStr);
        if (!f) return;
        let tups = typeof f.tuples === 'function' ? f.tuples() : f;
        for (let t of tups) {
          let ats = typeof t.atoms === 'function' ? t.atoms() : t;
          if (ats.length >= 2) cb(getStr(ats[0]), getStr(ats[1]));
        }
      } catch (e) { }
    };

    const process3 = (fieldStr, cb) => {
      try {
        let f = inst.field(fieldStr);
        if (!f) return;
        let tups = typeof f.tuples === 'function' ? f.tuples() : f;
        for (let t of tups) {
          let ats = typeof t.atoms === 'function' ? t.atoms() : t;
          if (ats.length >= 3) cb(getStr(ats[0]), getStr(ats[1]), getStr(ats[2]));
        }
      } catch (e) { }
    };

    process2("failed", src => { if (stateData.nodes[src]) stateData.nodes[src].isFailed = true; });
    process2("isByzantine", src => { if (stateData.nodes[src]) stateData.nodes[src].isByzantine = true; });
    process2("stormInfo", (src, tgt) => {
      if (stateData.nodes[src]) stateData.nodes[src].stormInfo = tgt.includes("StormTrue") ? "true" : "false";
    });
    process2("parentBeats", (src, tgt) => {
      if (stateData.nodes[src]) stateData.nodes[src].parentBeats = parseInt(tgt.replace(/[^0-9-]/g, "")) || 0;
    });
    process2("backupBeats", (src, tgt) => {
      if (stateData.nodes[src]) stateData.nodes[src].backupBeats = parseInt(tgt.replace(/[^0-9-]/g, "")) || 0;
    });

    const activePasses = new Set();
    process2("passStormInfo", (src, tgt) => {
      activePasses.add(`${src}->${tgt}`);
    });

    const addEdge = (src, tgt, type) => {
      if (stateData.nodes[src] && stateData.nodes[tgt]) {
        stateData.edges.push({ source: src, target: tgt, type: type });
      }
    };

    const TIMEOUT = 3;

    // HELPER: Determine the actual payload being broadcasted
    const getBroadcastedInfo = (node) => {
      if (!node) return "waiting";
      if (!node.isByzantine) return node.stormInfo;
      // Byzantine flip logic
      if (node.stormInfo === "true") return "false";
      if (node.stormInfo === "false") return "true";
      return node.stormInfo;
    };

    // GENERATE PARENT EDGES
    process2("parent", (child, parent) => {
      const isActive = activePasses.has(`${child}->${parent}`);
      const parentNode = stateData.nodes[parent];
      const broadcastedInfo = getBroadcastedInfo(parentNode);
      const beats = stateData.nodes[child].parentBeats;

      let edgeType = "parentNotYetPassing";
      if (isActive) {
        // Now evaluates the FAKED info if Byzantine, or REAL info if normal
        edgeType = broadcastedInfo === "true" ? "parentPassingTrue" : "parentPassingFalse";
      } else if (beats >= TIMEOUT || (parentNode && parentNode.isFailed)) {
        edgeType = "parentFailIgnore";
      }
      addEdge(child, parent, edgeType);
    });

    // GENERATE BACKUP EDGES
    process3("backup", (child, targetParent, backupNode) => {
      const isActive = activePasses.has(`${child}->${backupNode}`);
      const backupNodeData = stateData.nodes[backupNode];
      const broadcastedInfo = getBroadcastedInfo(backupNodeData);
      const beats = stateData.nodes[child].backupBeats;

      let edgeType = "backupNotYetPassing";
      if (isActive) {
        edgeType = broadcastedInfo === "true" ? "backupPassingTrue" : "backupPassingFalse";
      } else if (beats >= TIMEOUT || (backupNodeData && backupNodeData.isFailed)) {
        edgeType = "backupFailIgnore";
      }
      addEdge(child, backupNode, edgeType);
    });

    out.push(stateData);
  });

  return out;
}

const states = getAllStates();
const nStates = states.length || 1;
let curIdx = 0;

// ---------------------------------------------------------------
// SETUP SVG GRAPHICS & ARROW MARKERS
// ---------------------------------------------------------------
const root = d3.select(svg);

const title = root.append('text')
  .attr('x', 15).attr('y', 25)
  .style('font-size', '14px').style('font-weight', 'bold').style('fill', '#222');

const defs = root.append("defs");
const addMarker = (id, color, scale) => {
  defs.append("marker")
    .attr("id", id).attr("viewBox", "0 -5 10 10")
    .attr("refX", 22)
    .attr("refY", 0)
    .attr("markerWidth", 6 * scale).attr("markerHeight", 6 * scale)
    .attr("orient", "auto")
    .append("path").attr("d", "M0,-5L10,0L0,5").attr("fill", color);
};

const colors = {
  parentPassingTrue: "#2ca02c",
  parentPassingFalse: "#d62728",
  parentNotYetPassing: "#cccccc",
  parentFailIgnore: "#555555",
  backupPassingTrue: "#2ca02c",
  backupPassingFalse: "#d62728",
  backupNotYetPassing: "#cccccc",
  backupFailIgnore: "#555555"
};

Object.entries(colors).forEach(([key, color]) => {
  addMarker(`arrow-${key}`, color, key.includes("Passing") ? 1.3 : 1);
});

const gEdges = root.append("g");
const gNodes = root.append("g");

// ---------------------------------------------------------------
// UI CONTROLS & NEW STACKED LEGEND
// ---------------------------------------------------------------
const foControls = root.append('foreignObject')
  .attr('x', CTRL_X).attr('y', CTRL_Y).attr('width', CTRL_W).attr('height', 50);

const btnRow = foControls.append('xhtml:div')
  .style('display', 'flex').style('gap', '6px').style('font-family', 'sans-serif');
const prevBtn = btnRow.append('xhtml:button').text('\u2190 Prev').style('cursor', 'pointer').style('flex', '1').style('padding', '6px');
const nextBtn = btnRow.append('xhtml:button').text('Next \u2192').style('cursor', 'pointer').style('flex', '1').style('padding', '6px');

const foLegend = root.append('foreignObject')
  .attr('x', LEG_X).attr('y', LEG_Y).attr('width', LEG_W).attr('height', LEG_H);

const legendContainer = foLegend.append('xhtml:div')
  .style('font-family', 'sans-serif').style('font-size', '12px')
  .style('background', '#f8f9fa').style('border', '1px solid #ddd')
  .style('border-radius', '6px').style('padding', '12px').style('box-sizing', 'border-box')
  .style('display', 'flex').style('justify-content', 'space-between').style('gap', '20px');

const col1 = legendContainer.append('xhtml:div').style('flex', '1');
const col2 = legendContainer.append('xhtml:div').style('flex', '1');

const mkItem = (parent, icon, text) => {
  const d = parent.append('xhtml:div').style('margin-bottom', '4px').style('display', 'flex').style('align-items', 'center');
  d.append('xhtml:span').style('width', '28px').style('text-align', 'center').html(icon);
  d.append('xhtml:span').text(text);
};

// --- COLUMN 1: NODES
col1.append('xhtml:div').text('Node Shape (Status)').style('font-weight', 'bold').style('margin-bottom', '4px').style('border-bottom', '1px solid #ccc');
mkItem(col1, '⭕', 'Normal Node');
mkItem(col1, '💠', 'Byzantine Node');
mkItem(col1, '✖️', 'Failed/Silent Node');

col1.append('xhtml:div').text('Node Color (Memory)').style('font-weight', 'bold').style('margin-top', '12px').style('margin-bottom', '4px').style('border-bottom', '1px solid #ccc');
mkItem(col1, '🟢', 'Holding StormTrue');
mkItem(col1, '🔴', 'Holding StormFalse');
mkItem(col1, '⚪', 'Waiting for Data');
mkItem(col1, '⚫', 'Offline (Grayed Out)');

// --- COLUMN 2: EDGES
col2.append('xhtml:div').text('Parent Links').style('font-weight', 'bold').style('margin-bottom', '4px').style('border-bottom', '1px solid #ccc');
mkItem(col2, `<div style="width:20px;height:4px;background:${colors.parentPassingTrue};"></div>`, 'Passing True');
mkItem(col2, `<div style="width:20px;height:4px;background:${colors.parentPassingFalse};"></div>`, 'Passing False');
mkItem(col2, `<div style="width:20px;height:2px;background:${colors.parentNotYetPassing};"></div>`, 'Not Yet Passing');
mkItem(col2, `<div style="width:20px;height:2px;background:${colors.parentFailIgnore};"></div>`, 'Failed / Ignored');

col2.append('xhtml:div').text('Backup Links').style('font-weight', 'bold').style('margin-top', '12px').style('margin-bottom', '4px').style('border-bottom', '1px solid #ccc');
mkItem(col2, `<div style="width:20px;height:4px;border-top:4px dashed ${colors.backupPassingTrue};"></div>`, 'Passing True (Backup)');
mkItem(col2, `<div style="width:20px;height:4px;border-top:4px dashed ${colors.backupPassingFalse};"></div>`, 'Passing False (Backup)');
mkItem(col2, `<div style="width:20px;height:2px;border-top:2px dashed ${colors.backupNotYetPassing};"></div>`, 'Not Yet Passing (Backup)');
mkItem(col2, `<div style="width:20px;height:2px;border-top:2px dashed ${colors.backupFailIgnore};"></div>`, 'Failed / Ignored (Backup)');

// ---------------------------------------------------------------
// RENDER LOOP
// ---------------------------------------------------------------
function render(idx) {
  curIdx = Math.max(0, Math.min(nStates - 1, idx));
  const state = states[curIdx];

  title.text(`Weather Stations  ·  State ${curIdx + 1} / ${nStates}`);

  const edgeData = state ? state.edges : [];
  const link = gEdges.selectAll("line").data(edgeData, d => `${d.source}-${d.target}-${d.type}`);

  link.enter().append("line")
    .merge(link)
    .attr("x1", d => state.nodes[d.source] ? state.nodes[d.source].x : 0)
    .attr("y1", d => state.nodes[d.source] ? state.nodes[d.source].y : 0)
    .attr("x2", d => state.nodes[d.target] ? state.nodes[d.target].x : 0)
    .attr("y2", d => state.nodes[d.target] ? state.nodes[d.target].y : 0)
    .attr("stroke", d => colors[d.type])
    .attr("stroke-width", d => d.type.includes('Passing') ? 3 : 1.5)
    .attr("stroke-dasharray", d => d.type.includes('backup') ? "6,4" : "none")
    .attr("marker-end", d => `url(#arrow-${d.type})`);

  link.exit().remove();

  const nodeData = state ? Object.values(state.nodes) : [];
  const nodeBind = gNodes.selectAll("g.node").data(nodeData, d => d.id);

  const nodeEnter = nodeBind.enter().append("g").attr("class", "node")
    .attr("transform", d => `translate(${d.x}, ${d.y})`);

  nodeEnter.append("path").attr("class", "shape").attr("stroke", "#333").attr("stroke-width", 1.5);
  nodeEnter.append("text").attr("class", "name").attr("dy", -16).attr("text-anchor", "middle").style("font-size", "11px").style("font-weight", "bold");
  nodeEnter.append("text").attr("class", "beats").attr("dy", 24).attr("text-anchor", "middle").style("font-size", "10px").style("fill", "#666");

  const nodeUpdate = nodeEnter.merge(nodeBind);

  nodeUpdate.select("path.shape")
    .attr("d", d => {
      let sym = d3.symbolCircle;
      if (d.isFailed) sym = d3.symbolCross;
      else if (d.isByzantine) sym = d3.symbolDiamond;
      return d3.symbol().type(sym).size(280)();
    })
    .attr("transform", d => d.isFailed ? "rotate(45)" : "rotate(0)")
    .attr("fill", d => {
      if (d.isFailed) return "#555555";
      if (d.stormInfo === "true") return "#2ca02c";
      if (d.stormInfo === "false") return "#d62728";
      return "#f0f0f0";
    });

  nodeUpdate.select("text.name").text(d => d.name);
  nodeUpdate.select("text.beats").text(d => {
    if (d.parentBeats > 0 || d.backupBeats > 0) return `P:${d.parentBeats} B:${d.backupBeats}`;
    return "";
  });

  nodeBind.exit().remove();

  prevBtn.property('disabled', curIdx === 0);
  nextBtn.property('disabled', curIdx === nStates - 1);
}

prevBtn.on('click', () => render(curIdx - 1));
nextBtn.on('click', () => render(curIdx + 1));

render(0);