/* 规程真值维护台 —— 与 TMS API 交互的单页逻辑(无框架)。 */
"use strict";

const $ = (sel) => document.querySelector(sel);

async function api(path, options = {}) {
  const init = { headers: { "Accept": "application/json" }, ...options };
  if (init.body && typeof init.body !== "string") {
    init.body = JSON.stringify(init.body);
    init.headers["Content-Type"] = "application/json";
  }
  const resp = await fetch(path, init);
  let data = null;
  try { data = await resp.json(); } catch (e) { /* non-JSON */ }
  if (!resp.ok) {
    const msg = data && data.error ? data.error.message : `HTTP ${resp.status}`;
    const err = new Error(msg);
    err.status = resp.status;
    throw err;
  }
  return data;
}

function toast(message, isError = false) {
  const el = $("#toast");
  el.textContent = message;
  el.className = isError ? "error" : "";
  el.hidden = false;
  clearTimeout(toast._timer);
  toast._timer = setTimeout(() => { el.hidden = true; }, 4200);
}

const esc = (s) => String(s).replace(/[&<>"]/g,
  (c) => ({ "&": "&amp;", "<": "&lt;", ">": "&gt;", '"': "&quot;" }[c]));

/* ------------------------------------------------------------- 健康检查 */

async function refreshHealth() {
  const el = $("#health");
  try {
    const health = await api("/api/healthz");
    el.textContent = `健康:${health.status === "ok" ? "接口可用" : "降级"}`;
    el.className = "badge " + (health.status === "ok" ? "badge-ok" : "badge-warn");
  } catch (e) {
    el.textContent = "健康:接口不可用";
    el.className = "badge badge-bad";
  }
}

/* --------------------------------------------------------------- 状态渲染 */

async function refreshState() {
  const state = await api("/api/state");
  renderFacts(state);
  renderRules(state);
  renderConclusions(state);
  if (state.last_event && state.last_event.type === "fact_retracted") {
    renderVerdict(state.last_event.payload, true);
  }
}

function renderFacts(state) {
  const tbody = $("#fact-table tbody");
  tbody.innerHTML = "";
  for (const fact of state.facts) {
    const tr = document.createElement("tr");
    const status = fact.status === "asserted"
      ? '<span class="badge badge-ok">有效</span>'
      : '<span class="badge badge-bad">已撤回</span>';
    const action = fact.status === "asserted"
      ? `<button class="danger" data-retract="${esc(fact.id)}">撤回</button>`
      : `<button class="ghost" data-assert="${esc(fact.id)}">恢复</button>`;
    tr.innerHTML = `<td class="mono">${esc(fact.id)}</td>
      <td>${esc(fact.label || "—")}</td><td>${status}</td><td>${action}</td>`;
    tbody.appendChild(tr);
  }
  if (!state.facts.length) {
    tbody.innerHTML = '<tr><td colspan="4" class="hint">暂无事实</td></tr>';
  }
  $("#retracted-list").textContent =
    state.retracted_facts.length ? state.retracted_facts.join(", ") : "无";
}

function renderRules(state) {
  const tbody = $("#rule-table tbody");
  tbody.innerHTML = "";
  for (const rule of state.rules) {
    const tr = document.createElement("tr");
    const firing = rule.firing
      ? '<span class="badge badge-ok">触发中</span>'
      : '<span class="badge badge-unknown">未触发</span>';
    tr.innerHTML = `<td class="mono">${esc(rule.id)}</td>
      <td class="mono">${esc(rule.premises.join(" ∧ "))}</td>
      <td class="mono">${esc(rule.conclusion)}</td><td>${firing}</td>`;
    tbody.appendChild(tr);
  }
  if (!state.rules.length) {
    tbody.innerHTML = '<tr><td colspan="4" class="hint">暂无规则</td></tr>';
  }
}

function renderConclusions(state) {
  const host = $("#conclusion-list");
  host.innerHTML = "";
  if (!state.conclusions.length) {
    host.innerHTML = '<p class="hint">暂无结论。添加规则后此处展示每个结论的完整依据。</p>';
    return;
  }
  for (const concl of state.conclusions) {
    const div = document.createElement("div");
    div.className = "conclusion " + (concl.valid ? "valid" : "invalid");
    const badge = concl.valid
      ? '<span class="badge badge-ok">有效</span>'
      : '<span class="badge badge-bad">已失效</span>';
    const supports = concl.supports.map((s) => {
      const cls = s.status === "valid" ? "support valid" : "support invalid";
      const mark = s.status === "valid"
        ? '<span class="badge badge-ok">完整支持</span>'
        : '<span class="badge badge-bad">支持已破</span>';
      return `<div class="${cls}"><span class="rule">${esc(s.rule_id)}</span>
        ← <span class="mono">${esc(s.premises.join(" ∧ "))}</span> ${mark}</div>`;
    }).join("");
    div.innerHTML = `<div class="conclusion-head">
        <span class="node">${esc(concl.id)}</span>${badge}
        <button class="ghost" data-basis="${esc(concl.id)}">完整依据</button>
      </div>
      <div class="supports">${supports || '<span class="hint">无支持</span>'}</div>
      <div class="basis" hidden></div>`;
    host.appendChild(div);
  }
}

/* 渲染完整依据:节点与依据各只序列化一次,共享前提以可跳转引用(↪)表示,
   循环回到当前展开路径上的节点以 ↩ 标记,不再无限或重复展开。 */
function renderBasisGraph(graph) {
  const nodes = graph.nodes;
  const supports = graph.supports;
  const seen = new Set();

  function refChip(id, cyclic) {
    const cls = "node-ref mono" + (cyclic ? " cyclic-ref" : "");
    const arrow = cyclic ? "↩" : "↪";
    const hint = cyclic ? "循环回到已展开节点" : "共享前提·复用同一节点";
    return `<li><a class="${cls}" href="#basis-node-${esc(id)}">${arrow} ${esc(id)}</a>
      <span class="hint">(${hint})</span></li>`;
  }

  function nodeBadges(node) {
    if (node.kind === "fact") {
      return node.status === "asserted"
        ? '<span class="badge badge-ok">事实·有效</span>'
        : '<span class="badge badge-bad">事实·已撤回</span>';
    }
    const badges = [node.valid
      ? '<span class="badge badge-ok">有效</span>'
      : '<span class="badge badge-bad">已失效</span>'];
    if (node.cyclic) badges.push('<span class="badge badge-warn">处于循环支持</span>');
    return badges.join(" ");
  }

  function renderNode(id, ancestors) {
    const node = nodes[id];
    if (ancestors.has(id)) return refChip(id, true);
    const shared = seen.has(id);
    seen.add(id);

    if (node.kind === "fact") {
      const cls = node.status === "asserted"
        ? "fact-leaf asserted" : "fact-leaf retracted";
      return `<li id="basis-node-${esc(id)}">
        <span class="${cls} mono">${esc(id)}</span> ${nodeBadges(node)}
        ${node.label ? `<span class="hint">(${esc(node.label)})</span>` : ""}
      </li>`;
    }

    const next = new Set(ancestors);
    next.add(id);
    const supportHtml = (node.support_ids || []).map((sid) => {
      const s = supports[sid];
      const mark = s.status === "valid"
        ? '<span class="badge badge-ok">完整支持</span>'
        : '<span class="badge badge-bad">支持已破</span>';
      const cyclicMark = s.cyclic
        ? ' <span class="badge badge-warn">含循环前提</span>' : "";
      const premiseHtml = s.premises.map((pid) => {
        if (next.has(pid)) return refChip(pid, true);
        if (seen.has(pid)) return refChip(pid, false);
        return renderNode(pid, next);
      }).join("");
      return `<li><span class="mono">${esc(sid)}</span> ${mark}${cyclicMark}
        <ul class="basis-tree">${premiseHtml}</ul></li>`;
    }).join("");

    return `<li id="basis-node-${esc(id)}">
      <span class="mono">${esc(id)}</span> ${nodeBadges(node)}
      ${shared ? '<span class="hint">(共享节点)</span>' : ""}
      <ul class="basis-tree">${supportHtml || '<li class="hint">无支持</li>'}</ul>
    </li>`;
  }

  const cycleCount = (graph.cycles || []).length;
  const summary = `<p class="hint">完整依据图:节点 ${Object.keys(nodes).length} 个、`
    + `依据 ${Object.keys(supports).length} 条${cycleCount ? `、循环边 ${cycleCount} 条` : ""}
    —— 共享前提以 ↪ 引用同一节点,不重复复制子树。</p>`;
  return `${summary}<ul class="basis-tree">${renderNode(graph.root, new Set())}</ul>`;
}

/* ------------------------------------------------------------- 裁决渲染 */

function renderVerdict(verdict, isReplay = false) {
  const host = $("#verdict");
  const invalidated = verdict.invalidated || [];
  const retained = verdict.retained || [];
  const propagation = verdict.propagation || [];

  const invalidatedHtml = invalidated.length
    ? invalidated.map((item) => {
        const lost = item.lost_supports.map((s) =>
          `<div class="support invalid"><span class="rule">${esc(s.rule_id)}</span>
           ← <span class="mono">${esc(s.premises.join(" ∧ "))}</span>
           (断裂前提:<span class="broken mono">${esc(s.broken_premises.join(", "))}</span>)</div>`
        ).join("");
        return `<div><span class="mono">${esc(item.node)}</span>
          <span class="badge badge-bad">已失效</span>${lost}</div>`;
      }).join("")
    : '<p class="hint">无结论失效。</p>';

  const retainedHtml = retained.length
    ? retained.map((item) => {
        const rest = item.remaining_supports.map((s) =>
          `<div class="support valid"><span class="rule">${esc(s.rule_id)}</span>
           ← <span class="mono">${esc(s.premises.join(" ∧ "))}</span>
           <span class="badge badge-ok">剩余完整依据</span></div>`
        ).join("");
        return `<div><span class="mono">${esc(item.node)}</span>
          <span class="badge badge-ok">保持有效</span>${rest}</div>`;
      }).join("")
    : "";

  const chainHtml = propagation.length
    ? `<ol class="chain">${propagation.map((step) =>
        `<li class="${step.cause === "cyclic-support-collapsed" ? "cyclic" : ""}">
          <span class="depth">第 ${step.depth + 1} 层</span>
          <span class="mono">${esc(step.node)}</span> —
          ${step.cause === "support-exhausted" ? "支持耗尽" : "循环支持坍塌"}
        </li>`).join("")}</ol>`
    : '<p class="hint">本次撤回未形成失效传播。</p>';

  host.innerHTML = `<div class="verdict-block">
    <h3>撤回 <span class="mono">${esc(verdict.fact_id)}</span>
      ${isReplay ? '<span class="badge badge-warn">历史裁决回放</span>' : ""}
      ${verdict.replayed ? '<span class="badge badge-warn">重复撤回·返回既有裁决</span>' : ""}
    </h3>
    <p class="hint">裁决时间:${esc(verdict.at || "")}</p>
    <h3>受影响结论(失效)</h3>${invalidatedHtml}
    ${retainedHtml ? `<h3>保持有效的结论及剩余依据</h3>${retainedHtml}` : ""}
    <h3>传播链</h3>${chainHtml}
  </div>`;
}

/* --------------------------------------------------------------- 事件绑定 */

document.addEventListener("click", async (event) => {
  const target = event.target;
  if (!(target instanceof HTMLElement)) return;

  if (target.dataset.retract) {
    try {
      const verdict = await api(
        `/api/facts/${encodeURIComponent(target.dataset.retract)}/retract`,
        { method: "POST" });
      renderVerdict(verdict);
      toast(verdict.replayed
        ? `事实 ${verdict.fact_id} 此前已撤回,返回既有裁决。`
        : `已撤回 ${verdict.fact_id},失效结论 ${verdict.invalidated.length} 个。`);
      await refreshState();
    } catch (e) { toast(`撤回失败:${e.message}`, true); }
  }

  if (target.dataset.assert) {
    try {
      await api(`/api/facts/${encodeURIComponent(target.dataset.assert)}/assert`,
                { method: "POST" });
      toast(`已恢复 ${target.dataset.assert}`);
      await refreshState();
    } catch (e) { toast(`恢复失败:${e.message}`, true); }
  }

  if (target.dataset.basis) {
    const box = target.closest(".conclusion").querySelector(".basis");
    if (box.hidden) {
      try {
        const graph = await api(
          `/api/conclusions/${encodeURIComponent(target.dataset.basis)}/justification`);
        box.innerHTML = renderBasisGraph(graph);
        box.hidden = false;
        target.textContent = "收起依据";
      } catch (e) { toast(`查询依据失败:${e.message}`, true); }
    } else {
      box.hidden = true;
      target.textContent = "完整依据";
    }
  }
});

$("#fact-form").addEventListener("submit", async (event) => {
  event.preventDefault();
  const form = event.target;
  try {
    await api("/api/facts", { method: "POST",
      body: { id: form.id.value.trim(), label: form.label.value.trim() } });
    form.reset();
    toast("事实已添加");
    await refreshState();
  } catch (e) { toast(`添加事实被拒绝:${e.message}`, true); }
});

$("#rule-form").addEventListener("submit", async (event) => {
  event.preventDefault();
  const form = event.target;
  const premises = form.premises.value.split(",").map((s) => s.trim())
    .filter(Boolean);
  try {
    await api("/api/rules", { method: "POST",
      body: { id: form.id.value.trim(), premises,
              conclusion: form.conclusion.value.trim() } });
    form.reset();
    toast("规则已添加");
    await refreshState();
  } catch (e) { toast(`添加规则被拒绝:${e.message}`, true); }
});

$("#batch-form").addEventListener("submit", async (event) => {
  event.preventDefault();
  const textarea = event.target.batch;
  let rules;
  try { rules = JSON.parse(textarea.value); }
  catch (e) { toast("批量内容不是合法 JSON", true); return; }
  try {
    await api("/api/rules", { method: "POST", body: rules });
    textarea.value = "";
    toast("批量规则已原子提交");
    await refreshState();
  } catch (e) { toast(`批量添加被拒绝(规程未被污染):${e.message}`, true); }
});

/* ------------------------------------------------------------------ 启动 */

(async function boot() {
  await refreshHealth();
  setInterval(refreshHealth, 5000);
  try { await refreshState(); }
  catch (e) { toast(`加载状态失败:${e.message}`, true); }
})();
