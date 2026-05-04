// weather_stations.js

// 1. D3 is globally injected by Sterling. DO NOT use require('d3').
// Clear any previous renders to prevent ghosting.
d3.selectAll('svg > *').remove();

// ---------------------------------------------------------------
// ROBUST STATE EXTRACTION
// ---------------------------------------------------------------
// Layout Calculation
const CEN_X = 180, CEN_Y = 180, RAD = 120;
const CTRL_X = 350, CTRL_Y = 15, CTRL_W = 150;
const LEG_X = 14, LEG_Y = 380, LEG_W = 500;

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

    // Baseline nodes
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

    // Extract Node States
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

    // 1. First, map out which links are actively passing info this tick
    const activePasses = new Set();
    process2("passStormInfo", (src, tgt) => {
      activePasses.add(`${src}->${tgt}`);
    });

    // Safely add edge
    const addEdge = (src, tgt, type) => {
      if (stateData.nodes[src] && stateData.nodes[tgt]) {
        stateData.edges.push({ source: src, target: tgt, type: type });
      }
    };

    // 2. Generate parent edges and style based on activePasses lookup
    process2("parent", (src, tgt) => {
      const isActive = activePasses.has(`${src}->${tgt}`);
      addEdge(src, tgt, isActive ? "parent-active" : "parent-inactive");
    });

    // 3. Generate backup edges and style based on activePasses lookup
    process3("backup", (src, parent, tgt) => {
      const isActive = activePasses.has(`${src}->${tgt}`);
      addEdge(src, tgt, isActive ? "backup-active" : "backup-inactive");
    });

    out.push(stateData);
  });

  return out;
}

const states = getAllStates();
const nStates = states.length || 1;
let curIdx = 0;

// ---------------------------------------------------------------
// SETUP SVG & LAYERS
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

// Create the 4 distinct markers
addMarker("arrow-parent-inactive", "#999999", 1);
addMarker("arrow-parent-active", "#2ca02c", 1.3);
addMarker("arrow-backup-inactive", "#6495ED", 1);
addMarker("arrow-backup-active", "#FF8C00", 1.3);

const gEdges = root.append("g");
const gNodes = root.append("g");

// ---------------------------------------------------------------
// UI PANELS
// ---------------------------------------------------------------
const foControls = root.append('foreignObject')
  .attr('x', CTRL_X).attr('y', CTRL_Y).attr('width', CTRL_W).attr('height', 50);

const btnRow = foControls.append('xhtml:div')
  .style('display', 'flex').style('gap', '6px').style('font-family', 'sans-serif');
const prevBtn = btnRow.append('xhtml:button').text('\u2190 Prev').style('cursor', 'pointer').style('flex', '1').style('padding', '6px');
const nextBtn = btnRow.append('xhtml:button').text('Next \u2192').style('cursor', 'pointer').style('flex', '1').style('padding', '6px');

const foLegend = root.append('foreignObject')
  .attr('x', LEG_X).attr('y', LEG_Y).attr('width', LEG_W).attr('height', 160);

const legendContainer = foLegend.append('xhtml:div')
  .style('font-family', 'sans-serif').style('font-size', '12px')
  .style('background', '#f8f9fa').style('border', '1px solid #ddd')
  .style('border-radius', '6px').style('padding', '12px').style('box-sizing', 'border-box')
  .style('display', 'flex').style('justify-content', 'space-around');

const col1 = legendContainer.append('xhtml:div');
col1.append('xhtml:div').text('Node Status').style('font-weight', 'bold').style('margin-bottom', '6px').style('border-bottom', '1px solid #ccc');
const col2 = legendContainer.append('xhtml:div');
col2.append('xhtml:div').text('Network Edges').style('font-weight', 'bold').style('margin-bottom', '6px').style('border-bottom', '1px solid #ccc');

const mkItem = (parent, icon, text) => {
  const d = parent.append('xhtml:div').style('margin-bottom', '6px').style('display', 'flex').style('align-items', 'center');
  d.append('xhtml:span').style('width', '28px').style('text-align', 'center').html(icon);
  d.append('xhtml:span').text(text);
};

mkItem(col1, '🟢', 'StormTrue');
mkItem(col1, '🔴', 'StormFalse');
mkItem(col1, '⚪', 'Waiting');
mkItem(col1, '💠', 'Byzantine Node');
mkItem(col1, '✖️', 'Failed/Silent Node');

// The 4 dynamic edge states
mkItem(col2, '<div style="width:20px;height:2px;background:#999999;"></div>', 'Parent (Not in use)');
mkItem(col2, '<div style="width:20px;height:4px;background:#2ca02c;"></div>', 'Parent (Passing Info)');
mkItem(col2, '<div style="width:20px;height:2px;border-top:2px dashed #6495ED;"></div>', 'Backup (Not in use)');
mkItem(col2, '<div style="width:20px;height:4px;border-top:4px dashed #FF8C00;"></div>', 'Backup (Passing Info)');

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
    .attr("stroke", d => {
      if (d.type === 'parent-inactive') return '#999999';
      if (d.type === 'parent-active') return '#2ca02c';
      if (d.type === 'backup-inactive') return '#6495ED';
      if (d.type === 'backup-active') return '#FF8C00';
    })
    .attr("stroke-width", d => d.type.includes('active') ? 3 : 1.5)
    .attr("stroke-dasharray", d => d.type.includes('backup') ? "5,3" : "none")
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
      if (d.isFailed) return "#333";
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