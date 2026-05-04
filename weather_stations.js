const d3 = require('d3');

// Clear any previous renders to prevent ghosting
d3.selectAll('svg > *').remove();

// ---------------------------------------------------------------
// 1. ROBUST STATE EXTRACTION (Modeled after Game of Life script)
// Extracts all trace states upfront.
// ---------------------------------------------------------------
const CEN_X = 130, CEN_Y = 180, RAD = 95;
const UI_X = 260, UI_Y = 15, UI_W = 250;

function getAllStates() {
  const out = [];
  if (!instances || !instances.length) return out;

  const stationAtoms = instances[0].signature("Station").atoms();
  const stations = stationAtoms.map(a => String(a.id ? a.id() : a).trim());

  // Fixed orbital positions for stations
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

    // Baseline Nodes
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

    // Safe field extractors
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

    // Populate node states
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

    // Populate edge states with strict verification
    const addEdge = (src, tgt, type) => {
      if (poses[src] && poses[tgt]) {
        stateData.edges.push({ source: src, target: tgt, type: type });
      }
    };

    process2("parent", (src, tgt) => addEdge(src, tgt, "parent"));
    process2("passStormComing", (src, tgt) => addEdge(src, tgt, "pass"));
    process3("backup", (src, parent, tgt) => addEdge(src, tgt, "backup"));

    out.push(stateData);
  });

  return out;
}

const states = getAllStates();
const nStates = states.length || 1;
let curIdx = 0;

// ---------------------------------------------------------------
// 2. SETUP SVG & LAYERS
// ---------------------------------------------------------------
const root = d3.select(svg);

// Top-left Native SVG Title
const title = root.append('text')
  .attr('x', 15).attr('y', 25)
  .style('font-size', '14px').style('font-weight', 'bold').style('fill', '#222');

const defs = root.append("defs");
const addMarker = (id, color, scale) => {
  defs.append("marker")
    .attr("id", id).attr("viewBox", "0 -5 10 10")
    .attr("refX", 22) // Offset exactly to edge of symbol
    .attr("refY", 0)
    .attr("markerWidth", 6 * scale).attr("markerHeight", 6 * scale)
    .attr("orient", "auto")
    .append("path").attr("d", "M0,-5L10,0L0,5").attr("fill", color);
};
addMarker("arrow-parent", "#999", 1);
addMarker("arrow-backup", "#6495ED", 1);
addMarker("arrow-pass", "#FF8C00", 1.2);

const gEdges = root.append("g");
const gNodes = root.append("g");

// ---------------------------------------------------------------
// 3. CLEAN UI PANEL (Strictly Side-by-Side)
// ---------------------------------------------------------------
const fo = root.append('foreignObject')
  .attr('x', UI_X).attr('y', UI_Y).attr('width', UI_W).attr('height', 500);

const container = fo.append('xhtml:div')
  .style('font-family', 'sans-serif').style('font-size', '12px')
  .style('background', '#f8f9fa').style('border', '1px solid #ddd')
  .style('border-radius', '6px').style('padding', '12px').style('box-sizing', 'border-box');

const btnRow = container.append('xhtml:div')
  .style('margin-bottom', '15px').style('display', 'flex').style('gap', '6px');
const prevBtn = btnRow.append('xhtml:button').text('\u2190 Prev').style('cursor', 'pointer').style('flex', '1').style('padding', '6px');
const nextBtn = btnRow.append('xhtml:button').text('Next \u2192').style('cursor', 'pointer').style('flex', '1').style('padding', '6px');

const legend = container.append('xhtml:div');
legend.append('xhtml:div').text('Node Status').style('font-weight', 'bold').style('margin-bottom', '6px').style('border-bottom', '1px solid #ccc').style('padding-bottom', '4px');

const mkItem = (icon, text) => {
  const d = legend.append('xhtml:div').style('margin-bottom', '5px').style('display', 'flex').style('align-items', 'center');
  d.append('xhtml:span').style('width', '24px').style('text-align', 'center').html(icon);
  d.append('xhtml:span').text(text);
};

mkItem('🟢', 'StormTrue');
mkItem('🔴', 'StormFalse');
mkItem('⚪', 'Waiting');
mkItem('⚫', 'Failed/Silent');
mkItem('💠', 'Byzantine Node');
mkItem('✖️', 'Failed Node');

legend.append('xhtml:div').text('Network Edges').style('font-weight', 'bold').style('margin-top', '12px').style('margin-bottom', '6px').style('border-bottom', '1px solid #ccc').style('padding-bottom', '4px');
mkItem('<div style="width:20px;height:2px;background:#999;"></div>', 'Parent Link');
mkItem('<div style="width:20px;height:2px;border-top:2px dashed #6495ED;"></div>', 'Backup Link');
mkItem('<div style="width:20px;height:4px;background:#FF8C00;"></div>', 'PassStormComing');

// ---------------------------------------------------------------
// 4. RENDER LOOP (Proper Enter/Merge/Exit D3 Pattern)
// ---------------------------------------------------------------
function render(idx) {
  curIdx = Math.max(0, Math.min(nStates - 1, idx));
  const state = states[curIdx];

  title.text(`Weather Stations  ·  State ${curIdx + 1} / ${nStates}`);

  // --- Draw Edges ---
  const edgeData = state ? state.edges : [];
  const link = gEdges.selectAll("line").data(edgeData, d => `${d.source}-${d.target}-${d.type}`);

  link.enter().append("line")
    .merge(link)
    .attr("x1", d => state.nodes[d.source].x)
    .attr("y1", d => state.nodes[d.source].y)
    .attr("x2", d => state.nodes[d.target].x)
    .attr("y2", d => state.nodes[d.target].y)
    .attr("stroke", d => d.type === 'parent' ? '#999' : d.type === 'backup' ? '#6495ED' : '#FF8C00')
    .attr("stroke-width", d => d.type === 'pass' ? 3 : 1.5)
    .attr("stroke-dasharray", d => d.type === 'backup' ? "5,3" : "none")
    .attr("marker-end", d => `url(#arrow-${d.type})`);

  link.exit().remove();

  // --- Draw Nodes ---
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

  // --- Update UI ---
  prevBtn.property('disabled', curIdx === 0);
  nextBtn.property('disabled', curIdx === nStates - 1);
}

prevBtn.on('click', () => render(curIdx - 1));
nextBtn.on('click', () => render(curIdx + 1));

render(0);