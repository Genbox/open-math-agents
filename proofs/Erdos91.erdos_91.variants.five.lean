import FormalConjectures.ErdosProblems.«91»

/-! The five-point case follows from a finite classification of rank-two distance matrices. -/

open scoped EuclideanGeometry

namespace FiveDistances

private def edgeIndex (i j : Fin 5) : ℕ :=
  let a := min i.val j.val
  let b := max i.val j.val
  a * (9 - a) / 2 + (b - a - 1)

private def distanceCode (c : ℕ) (s : ℝ) (i j : Fin 5) : ℝ :=
  if i = j then 0 else if c.testBit (edgeIndex i j) then s else 1

private def gram (c : ℕ) (s : ℝ) (i j : Fin 5) : ℝ :=
  distanceCode c s 0 i + distanceCode c s 0 j - distanceCode c s i j

private def minor (c : ℕ) (s : ℝ) (a b d e f g : Fin 5) : ℝ :=
  gram c s a e * (gram c s b f * gram c s d g - gram c s b g * gram c s d f) -
  gram c s a f * (gram c s b e * gram c s d g - gram c s b g * gram c s d e) +
  gram c s a g * (gram c s b e * gram c s d f - gram c s b f * gram c s d e)

private def representatives : List ℕ :=
  [0, 1, 3, 7, 15, 19, 20, 21, 23, 28, 29, 31, 54, 55, 58, 59, 62, 63, 126, 127, 183, 184, 185, 187, 191, 207, 220, 221, 223, 254, 255, 495, 511, 1023]

private def table : Fin 16 → Array ℕ := ![
  #[198656, 1767425, 1128449, 2467843, 1001473, 1832963, 1218563, 2754567, 976897, 1710083, 1095683, 2119687, 993283, 1505287, 993287, 993295, 493569, 2443267, 2439171, 2439187, 2598932, 2893845, 2766869, 2979863, 1959956, 2279445, 2152469, 2467863, 2467868, 2488349, 2467869, 2467871, 366593, 1808387, 2701332, 2996245, 1800195, 1800211, 2742293, 2856983, 1325076, 1767445, 1832988, 1873949, 1513493, 1832983, 1832989, 1832991, 579587, 2627591, 2643989, 2955287, 2619413, 2832407, 2598966, 2893879, 1685532, 1767453, 2484282, 2484283, 1869882, 1869883, 2897982, 2897983],
  #[342017, 1685507, 2062356, 2484245, 1427476, 1869845, 1710108, 1771549, 1673219, 1673235, 2103317, 2222103, 1488917, 1710103, 1710109, 1710111, 456707, 1992711, 2029589, 2443287, 1808412, 1869853, 2996282, 2996283, 1980437, 2197527, 1959990, 2279479, 1767482, 1767483, 2283582, 2283583, 354307, 1378311, 2443292, 2484253, 1390613, 1808407, 2893882, 2893883, 1366037, 1685527, 2279482, 2279483, 1325110, 1767479, 1771582, 1771583, 354311, 354319, 2443293, 2443295, 1808413, 1808415, 2893886, 2893887, 1685533, 1685535, 2279486, 2279487, 1767486, 1767487, 1767550, 1767551],
  #[243713, 2824212, 1169411, 2971669, 1165315, 2844693, 1165331, 2754583, 710676, 1218588, 1128469, 1239069, 1001493, 1218589, 1218583, 1218591, 555011, 2951189, 2603015, 2951191, 2598933, 2619446, 2705431, 2766903, 1046556, 2459706, 1128477, 2459707, 1230906, 2775102, 1230907, 2775103, 550915, 2824213, 2701333, 2742326, 2598919, 2824215, 2701335, 2742327, 919580, 1820730, 1206330, 2754622, 1001501, 1820731, 1206331, 2754623, 550931, 2627607, 2603031, 2644023, 2598935, 2619447, 2598967, 2599095, 198840, 2898105, 2775225, 2980027, 2754745, 2857147, 2754747, 2754751],
  #[198676, 579612, 432156, 2439226, 305180, 1800250, 710840, 2894009, 198684, 1329336, 1038394, 2152633, 915514, 1513657, 977081, 993487, 493589, 600093, 493597, 2439227, 571450, 2627646, 2648249, 2955451, 423994, 2029753, 1968190, 2439355, 198876, 2894045, 2152669, 2468063, 366613, 579613, 596026, 2648126, 366621, 1800251, 2627769, 2832571, 301114, 1390777, 710876, 2996445, 1329214, 1800379, 1513693, 1833183, 579607, 579615, 596027, 2648127, 571451, 2627647, 2627771, 2627775, 342201, 354511, 2029789, 2443487, 1390813, 1808607, 2894078, 2894079],
  #[219137, 2185236, 1046531, 2459669, 915476, 1095708, 1230869, 1136669, 1038339, 2205717, 1038355, 2119703, 976917, 1095709, 1095703, 1095711, 432131, 2439189, 1968135, 2439191, 1169436, 2971706, 1230877, 2971707, 1959957, 1980470, 2070551, 2152503, 1128506, 2160702, 1128507, 2160703, 301076, 456732, 555036, 2951226, 202780, 1325240, 1165370, 2767033, 301084, 1673274, 714936, 2279609, 1427514, 1489081, 1001657, 1505487, 595989, 497693, 595997, 2951227, 550970, 2644153, 2603070, 2951355, 444474, 1992766, 2033849, 2443451, 301276, 2279645, 2767069, 2980063],
  #[423939, 2185237, 2062357, 2103350, 915484, 1693754, 1079354, 2119742, 1959943, 2185239, 2062359, 2103351, 976925, 1693755, 1079355, 2119743, 423955, 1992727, 1968151, 2029623, 202936, 2283705, 2160825, 2468027, 1959959, 1980471, 1959991, 1960119, 2119865, 2222267, 2119867, 2119871, 342037, 456733, 493626, 2033726, 1325114, 1366201, 915676, 2484445, 342045, 1673275, 1992889, 2197691, 1325118, 1673403, 1489117, 1710303, 456727, 456735, 493627, 2033727, 366777, 1378511, 2644189, 2955487, 444475, 1992767, 1992891, 1992895, 1366237, 1685727, 2279678, 2279679],
  #[227331, 2439196, 739335, 2459677, 755733, 2766906, 1169431, 2766907, 731157, 2152506, 1046551, 2152507, 710710, 1136702, 1128503, 1136703, 227335, 2439197, 227343, 2439199, 1169437, 2766910, 1169439, 2766911, 1046557, 2152510, 1046559, 2152511, 1128510, 1128574, 1128511, 1128575, 243733, 2644026, 555037, 2644030, 243741, 2603193, 1165371, 2705595, 198714, 1325276, 755897, 2971869, 714814, 1001693, 1165499, 1218783, 555031, 2644027, 555039, 2644031, 550971, 2603195, 2603071, 2603199, 219321, 2439389, 227535, 2439391, 755933, 2767102, 1169631, 2767103],
  #[219157, 2029626, 432157, 2029630, 710714, 1427676, 731321, 2459869, 219165, 1968313, 1038395, 2070715, 710718, 977117, 1038523, 1095903, 432151, 2029627, 432159, 2029631, 243897, 2951389, 739535, 2951391, 423995, 1968315, 1968191, 1968319, 731357, 2152702, 1046751, 2152703, 198710, 497726, 493630, 493694, 202814, 366813, 243933, 2644222, 198718, 342237, 219357, 2029822, 198782, 1325310, 710910, 993775, 493623, 497727, 493631, 493695, 551099, 579807, 555231, 2644223, 424123, 456927, 432351, 2029823, 198910, 354799, 227823, 2439679],
  #[198657, 1673236, 1038356, 993308, 919555, 1820693, 1206293, 1013789, 915459, 1693717, 1079317, 993309, 915475, 1505303, 993303, 993311, 423956, 354332, 227356, 1960120, 550940, 2824250, 2701370, 2742457, 423964, 2185274, 2062394, 2103481, 739512, 1767609, 1128633, 2119887, 305155, 1800213, 1165340, 2844730, 1329159, 1800215, 1206301, 2844731, 1325077, 1366070, 1001530, 1525822, 1431575, 1513527, 1001531, 1525823, 571413, 374813, 2598970, 2619577, 571421, 2824251, 2598974, 2824379, 342074, 1378366, 424156, 1767645, 1398969, 1808571, 2742493, 2857183],
  #[301059, 1673237, 1038364, 2205754, 1427477, 1488950, 976954, 1505342, 1325063, 1673239, 1079325, 2205755, 1427479, 1488951, 976955, 1505343, 444437, 354333, 1959994, 1980601, 366650, 1398846, 1038556, 1870045, 444445, 2185275, 1959998, 2185403, 1378489, 1685691, 2103517, 2222303, 301075, 1378327, 227512, 1771705, 1329175, 1390647, 1525945, 1833147, 1325079, 1366071, 1505465, 1710267, 1325111, 1325239, 1505467, 1505471, 354327, 354335, 493753, 1992911, 366651, 1398847, 2619613, 2832607, 342075, 1378367, 1980637, 2197727, 1378491, 1378495, 1767678, 1767679],
  #[202755, 1800220, 1165333, 2742330, 714759, 1820701, 1165335, 2742331, 710677, 1513530, 731190, 1013822, 919575, 1513531, 1001527, 1013823, 550933, 2619450, 247837, 2599097, 550941, 2619454, 2701371, 2701499, 219194, 1960156, 739390, 1128669, 759993, 2844893, 1169595, 2754783, 202759, 1800221, 1165341, 2742334, 202767, 1800223, 1165343, 2742335, 919581, 1513534, 1001534, 1001598, 919583, 1513535, 1001535, 1001599, 550935, 2619451, 2598971, 2599099, 550943, 2619455, 2598975, 2599103, 198841, 1800413, 1165533, 2742526, 202959, 1800415, 1165535, 2742527],
  #[198677, 1390650, 731194, 2062556, 305181, 1390654, 710841, 1820893, 198685, 1329337, 731198, 1079517, 915515, 1431739, 915643, 993503, 219190, 374846, 227390, 493789, 366654, 366718, 551133, 2619646, 219198, 444637, 219262, 1960190, 198877, 1390846, 731390, 1096175, 305175, 1390651, 247993, 2824413, 305183, 1390655, 714959, 2824415, 301115, 1329339, 710877, 1513726, 1329215, 1329343, 919775, 1513727, 366647, 374847, 555195, 2627807, 366655, 366719, 551135, 2619647, 301243, 354527, 219390, 457199, 305375, 1390847, 203247, 1800703],
  #[198659, 1673244, 1038357, 2103354, 915477, 1488954, 976950, 993342, 710663, 1693725, 1038359, 2103355, 915479, 1488955, 976951, 993343, 423957, 1980474, 227357, 1960121, 243770, 1673436, 759870, 1231069, 423965, 1980478, 2062395, 2062523, 739513, 2205917, 1046715, 2119903, 301077, 1366074, 755770, 2185436, 202781, 1325241, 755774, 1206493, 301085, 1366078, 714937, 1693917, 1427515, 1427643, 919739, 1505503, 342070, 354366, 247870, 596189, 243774, 571613, 243838, 2599166, 342078, 342142, 424157, 1980670, 301277, 1366270, 755966, 1710575],
  #[198663, 1673245, 1038365, 2103358, 915485, 1488958, 976958, 977022, 198671, 1673247, 1038367, 2103359, 915487, 1488959, 976959, 977023, 423959, 1980475, 1959995, 1960123, 202937, 1673437, 1038557, 2103550, 423967, 1980479, 1959999, 1960127, 198863, 1673439, 1038559, 2103551, 301079, 1366075, 227513, 2185437, 1325115, 1325243, 915677, 1489150, 301087, 1366079, 710863, 2185439, 1325119, 1325247, 915679, 1489151, 342071, 354367, 432315, 1992927, 305339, 1378527, 243966, 1685999, 342079, 342143, 424159, 1980671, 301279, 1366271, 199151, 1673727],
  #[198675, 354488, 739351, 1136825, 714775, 1013945, 755767, 1218747, 710679, 993465, 731191, 1095867, 710711, 993467, 710839, 993471, 227351, 497849, 227359, 1968335, 243771, 2599133, 759871, 2705631, 219195, 1960157, 739391, 2070751, 739515, 1128702, 739519, 1128703, 202775, 374969, 755771, 2701533, 202783, 1329359, 755775, 2701535, 198715, 1325277, 714939, 1001726, 714815, 1431775, 714943, 1001727, 243767, 579771, 247871, 2603231, 243775, 2599135, 243839, 2599167, 198843, 342270, 227551, 432623, 202975, 305647, 755967, 1165823],
  #[198679, 354489, 731195, 2062557, 710715, 1427677, 710843, 977150, 198687, 1325263, 731199, 2062559, 710719, 1427679, 710847, 977151, 219191, 456891, 227391, 1968351, 202939, 366846, 739551, 1047023, 219199, 1960159, 219263, 1960191, 198879, 301551, 731391, 1038847, 198711, 354491, 227515, 493822, 202815, 1329375, 714975, 920047, 198719, 1325279, 710879, 915951, 198783, 1325311, 710911, 915967, 198839, 354495, 227519, 493823, 202943, 366847, 243967, 551423, 198847, 342271, 219391, 424447, 198911, 301567, 199167, 199679]]

private theorem eliminate (s : ℝ) (hs : 1 < s) (c : ℕ)
    (hc : c ∈ representatives)
    (h : ∀ a b d e f g : Fin 5, minor c s a b d e f g = 0) :
    c = 220 ∧ s ^ 2 - 3 * s + 1 = 0 := by
  have hs0 : 0 < s := by linarith
  simp only [representatives, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have h0 := h 1 2 3 1 2 3
    norm_num [minor, gram, distanceCode, edgeIndex, Nat.testBit_eq_decide_div_mod_eq, Fin.ext_iff] at h0
  · have h9 := h 2 3 4 2 3 4
    norm_num [minor, gram, distanceCode, edgeIndex, Nat.testBit_eq_decide_div_mod_eq, Fin.ext_iff] at h9
  · have h7 := h 1 3 4 1 3 4
    have h8 := h 1 3 4 2 3 4
    norm_num [minor, gram, distanceCode, edgeIndex, Nat.testBit_eq_decide_div_mod_eq, Fin.ext_iff] at h7 h8
    exfalso
    have hzero : (1 : ℝ) = 0 := by linear_combination ((1/3 : ℝ)) * h7 + ((-1/3 : ℝ)) * h8
    exact (show 0 < (1 : ℝ) by positivity).ne' hzero
  · have h0 := h 1 2 3 1 2 3
    have h1 := h 1 2 3 1 2 4
    norm_num [minor, gram, distanceCode, edgeIndex, Nat.testBit_eq_decide_div_mod_eq, Fin.ext_iff] at h0 h1
    exfalso
    have hzero : (1 : ℝ) = 0 := by linear_combination ((-1/2 : ℝ)) * h0 + ((3 : ℝ)) * h1
    exact (show 0 < (1 : ℝ) by positivity).ne' hzero
  · have h0 := h 1 2 3 1 2 3
    have h1 := h 1 2 3 1 2 4
    norm_num [minor, gram, distanceCode, edgeIndex, Nat.testBit_eq_decide_div_mod_eq, Fin.ext_iff] at h0 h1
    exfalso
    have hzero : (1 : ℝ) = 0 := by linear_combination ((1 : ℝ)) * h0 + ((-3 : ℝ)) * h1
    exact (show 0 < (1 : ℝ) by positivity).ne' hzero
  · have h6 := h 1 2 4 2 3 4
    have h7 := h 1 3 4 1 3 4
    norm_num [minor, gram, distanceCode, edgeIndex, Nat.testBit_eq_decide_div_mod_eq, Fin.ext_iff] at h6 h7
    exfalso
    have hzero : s = 0 := by linear_combination ((-1/3 : ℝ)) * h6 + ((1/6 : ℝ)) * h7
    exact (show 0 < s by positivity).ne' hzero
  · have h4 := h 1 2 4 1 2 4
    have h5 := h 1 2 4 1 3 4
    norm_num [minor, gram, distanceCode, edgeIndex, Nat.testBit_eq_decide_div_mod_eq, Fin.ext_iff] at h4 h5
    exfalso
    have hzero : s = 0 := by linear_combination ((1/6 : ℝ)) * h4 + ((1/3 : ℝ)) * h5
    exact (show 0 < s by positivity).ne' hzero
  · have h1 := h 1 2 3 1 2 4
    have h9 := h 2 3 4 2 3 4
    norm_num [minor, gram, distanceCode, edgeIndex, Nat.testBit_eq_decide_div_mod_eq, Fin.ext_iff] at h1 h9
    exfalso
    have hzero : (1 : ℝ) = 0 := by linear_combination ((-1 : ℝ)) * h1 + ((1/2 : ℝ)) * h9
    exact (show 0 < (1 : ℝ) by positivity).ne' hzero
  · have h2 := h 1 2 3 1 3 4
    have h7 := h 1 3 4 1 3 4
    norm_num [minor, gram, distanceCode, edgeIndex, Nat.testBit_eq_decide_div_mod_eq, Fin.ext_iff] at h2 h7
    exfalso
    have hzero : (1 : ℝ) = 0 := by linear_combination ((-15 : ℝ) + (4 : ℝ) * s ^ 1) * h2 + ((-1/2 : ℝ) + (-2 : ℝ) * s ^ 1) * h7
    exact (show 0 < (1 : ℝ) by positivity).ne' hzero
  · have h2 := h 1 2 3 1 3 4
    have h7 := h 1 3 4 1 3 4
    norm_num [minor, gram, distanceCode, edgeIndex, Nat.testBit_eq_decide_div_mod_eq, Fin.ext_iff] at h2 h7
    exfalso
    have hzero : (1 : ℝ) = 0 := by linear_combination ((-15 : ℝ) + (4 : ℝ) * s ^ 1) * h2 + ((-1/2 : ℝ) + (-2 : ℝ) * s ^ 1) * h7
    exact (show 0 < (1 : ℝ) by positivity).ne' hzero
  · have h3 := h 1 2 3 2 3 4
    have h7 := h 1 3 4 1 3 4
    norm_num [minor, gram, distanceCode, edgeIndex, Nat.testBit_eq_decide_div_mod_eq, Fin.ext_iff] at h3 h7
    exfalso
    have hzero : (1 : ℝ) = 0 := by linear_combination ((-1 : ℝ)) * h3 + ((1/2 : ℝ)) * h7
    exact (show 0 < (1 : ℝ) by positivity).ne' hzero
  · have h2 := h 1 2 3 1 3 4
    have h7 := h 1 3 4 1 3 4
    norm_num [minor, gram, distanceCode, edgeIndex, Nat.testBit_eq_decide_div_mod_eq, Fin.ext_iff] at h2 h7
    exfalso
    have hzero : (1 : ℝ) = 0 := by linear_combination ((9 : ℝ)) * h2 + ((-1/2 : ℝ) + (3 : ℝ) * s ^ 1) * h7
    exact (show 0 < (1 : ℝ) by positivity).ne' hzero
  · have h0 := h 1 2 3 1 2 3
    have h6 := h 1 2 4 2 3 4
    norm_num [minor, gram, distanceCode, edgeIndex, Nat.testBit_eq_decide_div_mod_eq, Fin.ext_iff] at h0 h6
    exfalso
    have hzero : (1 : ℝ) = 0 := by linear_combination ((1/12 : ℝ)) * h0 + ((-2/3 : ℝ)) * h6
    exact (show 0 < (1 : ℝ) by positivity).ne' hzero
  · have h0 := h 1 2 3 1 2 3
    have h9 := h 2 3 4 2 3 4
    norm_num [minor, gram, distanceCode, edgeIndex, Nat.testBit_eq_decide_div_mod_eq, Fin.ext_iff] at h0 h9
    exfalso
    have hzero : (1 : ℝ) = 0 := by linear_combination ((-41/4 : ℝ) + (11/4 : ℝ) * s ^ 1) * h0 + ((-1/2 : ℝ) + (33/4 : ℝ) * s ^ 1) * h9
    exact (show 0 < (1 : ℝ) by positivity).ne' hzero
  · have h3 := h 1 2 3 2 3 4
    have h8 := h 1 3 4 2 3 4
    norm_num [minor, gram, distanceCode, edgeIndex, Nat.testBit_eq_decide_div_mod_eq, Fin.ext_iff] at h3 h8
    exfalso
    have hzero : (1 : ℝ) = 0 := by linear_combination ((1/2 : ℝ) + (-1/6 : ℝ) * s ^ 1) * h3 + ((5/6 : ℝ) + (-1/6 : ℝ) * s ^ 1) * h8
    exact (show 0 < (1 : ℝ) by positivity).ne' hzero
  · have h6 := h 1 2 4 2 3 4
    have h9 := h 2 3 4 2 3 4
    norm_num [minor, gram, distanceCode, edgeIndex, Nat.testBit_eq_decide_div_mod_eq, Fin.ext_iff] at h6 h9
    exfalso
    have hzero : (1 : ℝ) = 0 := by linear_combination ((-26/3 : ℝ) + (7/3 : ℝ) * s ^ 1) * h6 + ((-29/6 : ℝ) + (7/2 : ℝ) * s ^ 1) * h9
    exact (show 0 < (1 : ℝ) by positivity).ne' hzero
  · have h0 := h 1 2 3 1 2 3
    have h1 := h 1 2 3 1 2 4
    norm_num [minor, gram, distanceCode, edgeIndex, Nat.testBit_eq_decide_div_mod_eq, Fin.ext_iff] at h0 h1
    exfalso
    have hzero : (1 : ℝ) = 0 := by linear_combination ((3/4 : ℝ)) * h0 + ((-2 : ℝ)) * h1
    exact (show 0 < (1 : ℝ) by positivity).ne' hzero
  · have h1 := h 1 2 3 1 2 4
    have h9 := h 2 3 4 2 3 4
    norm_num [minor, gram, distanceCode, edgeIndex, Nat.testBit_eq_decide_div_mod_eq, Fin.ext_iff] at h1 h9
    exfalso
    have hzero : (1 : ℝ) = 0 := by linear_combination ((-9 : ℝ)) * h1 + ((-1/2 : ℝ) + (3 : ℝ) * s ^ 1) * h9
    exact (show 0 < (1 : ℝ) by positivity).ne' hzero
  · have h3 := h 1 2 3 2 3 4
    norm_num [minor, gram, distanceCode, edgeIndex, Nat.testBit_eq_decide_div_mod_eq, Fin.ext_iff] at h3
    exfalso
    have hzero : (1 : ℝ) = 0 := by linear_combination ((1 : ℝ)) * h3
    exact (show 0 < (1 : ℝ) by positivity).ne' hzero
  · have h8 := h 1 3 4 2 3 4
    have h9 := h 2 3 4 2 3 4
    norm_num [minor, gram, distanceCode, edgeIndex, Nat.testBit_eq_decide_div_mod_eq, Fin.ext_iff] at h8 h9
    exfalso
    have hzero : (1 : ℝ) = 0 := by linear_combination ((3 : ℝ)) * h8 + ((-1/2 : ℝ)) * h9
    exact (show 0 < (1 : ℝ) by positivity).ne' hzero
  · have h3 := h 1 2 3 2 3 4
    have h4 := h 1 2 4 1 2 4
    norm_num [minor, gram, distanceCode, edgeIndex, Nat.testBit_eq_decide_div_mod_eq, Fin.ext_iff] at h3 h4
    exfalso
    have hzero : s ^ 2 = 0 := by linear_combination ((1/3 : ℝ)) * h3 + ((1/6 : ℝ)) * h4
    exact (show 0 < s ^ 2 by positivity).ne' hzero
  · have h0 := h 1 2 3 1 2 3
    have h1 := h 1 2 3 1 2 4
    norm_num [minor, gram, distanceCode, edgeIndex, Nat.testBit_eq_decide_div_mod_eq, Fin.ext_iff] at h0 h1
    exfalso
    have hzero : s ^ 2 = 0 := by linear_combination ((1/6 : ℝ)) * h0 + ((1/3 : ℝ)) * h1
    exact (show 0 < s ^ 2 by positivity).ne' hzero
  · have h0 := h 1 2 3 1 2 3
    have h4 := h 1 2 4 1 2 4
    norm_num [minor, gram, distanceCode, edgeIndex, Nat.testBit_eq_decide_div_mod_eq, Fin.ext_iff] at h0 h4
    exfalso
    have hzero : (1 : ℝ) = 0 := by linear_combination ((35/12 : ℝ) + (7/4 : ℝ) * s ^ 1 + (-13/12 : ℝ) * s ^ 2) * h0 + ((-1/2 : ℝ) + (-47/12 : ℝ) * s ^ 1 + (13/12 : ℝ) * s ^ 2) * h4
    exact (show 0 < (1 : ℝ) by positivity).ne' hzero
  · have h0 := h 1 2 3 1 2 3
    have h7 := h 1 3 4 1 3 4
    norm_num [minor, gram, distanceCode, edgeIndex, Nat.testBit_eq_decide_div_mod_eq, Fin.ext_iff] at h0 h7
    exfalso
    have hzero : (1 : ℝ) = 0 := by linear_combination ((61/8 : ℝ) + (37/8 : ℝ) * s ^ 1 + (-23/8 : ℝ) * s ^ 2) * h0 + ((-1/2 : ℝ) + (-69/8 : ℝ) * s ^ 1) * h7
    exact (show 0 < (1 : ℝ) by positivity).ne' hzero
  · have h0 := h 1 2 3 1 2 3
    have h4 := h 1 2 4 1 2 4
    norm_num [minor, gram, distanceCode, edgeIndex, Nat.testBit_eq_decide_div_mod_eq, Fin.ext_iff] at h0 h4
    exfalso
    have hzero : s = 0 := by linear_combination ((15/4 : ℝ) + (-1 : ℝ) * s ^ 1) * h0 + ((-1/2 : ℝ) + (-2 : ℝ) * s ^ 1) * h4
    exact (show 0 < s by positivity).ne' hzero
  · have h0 := h 1 2 3 1 2 3
    have h1 := h 1 2 3 1 2 4
    norm_num [minor, gram, distanceCode, edgeIndex, Nat.testBit_eq_decide_div_mod_eq, Fin.ext_iff] at h0 h1
    exfalso
    have hzero : s = 0 := by linear_combination ((-1/2 : ℝ) + (7/3 : ℝ) * s ^ 1) * h0 + ((-26/3 : ℝ) + (7/3 : ℝ) * s ^ 1) * h1
    exact (show 0 < s by positivity).ne' hzero
  · have h0 := h 1 2 3 1 2 3
    have h1 := h 1 2 3 1 2 4
    norm_num [minor, gram, distanceCode, edgeIndex, Nat.testBit_eq_decide_div_mod_eq, Fin.ext_iff] at h0 h1
    refine ⟨rfl, ?_⟩
    linear_combination ((-3/10 : ℝ)) * h0 + ((1/5 : ℝ)) * h1
  · have h0 := h 1 2 3 1 2 3
    have h4 := h 1 2 4 1 2 4
    norm_num [minor, gram, distanceCode, edgeIndex, Nat.testBit_eq_decide_div_mod_eq, Fin.ext_iff] at h0 h4
    exfalso
    have hzero : (1 : ℝ) = 0 := by linear_combination ((-1/4 : ℝ) + (-7/6 : ℝ) * s ^ 1 + (1/3 : ℝ) * s ^ 2) * h0 + ((4/3 : ℝ)) * h4
    exact (show 0 < (1 : ℝ) by positivity).ne' hzero
  · have h0 := h 1 2 3 1 2 3
    have h2 := h 1 2 3 1 3 4
    norm_num [minor, gram, distanceCode, edgeIndex, Nat.testBit_eq_decide_div_mod_eq, Fin.ext_iff] at h0 h2
    exfalso
    have hzero : (1 : ℝ) = 0 := by linear_combination ((-35/2 : ℝ) + (25 : ℝ) * s ^ 1) * h0 + ((-1 : ℝ) + (30 : ℝ) * s ^ 1) * h2
    exact (show 0 < (1 : ℝ) by positivity).ne' hzero
  · have h4 := h 1 2 4 1 2 4
    have h6 := h 1 2 4 2 3 4
    norm_num [minor, gram, distanceCode, edgeIndex, Nat.testBit_eq_decide_div_mod_eq, Fin.ext_iff] at h4 h6
    exfalso
    have hzero : (1 : ℝ) = 0 := by linear_combination ((-1/4 : ℝ)) * h4 + ((-2 : ℝ)) * h6
    exact (show 0 < (1 : ℝ) by positivity).ne' hzero
  · have h3 := h 1 2 3 2 3 4
    have h5 := h 1 2 4 1 3 4
    norm_num [minor, gram, distanceCode, edgeIndex, Nat.testBit_eq_decide_div_mod_eq, Fin.ext_iff] at h3 h5
    exfalso
    have hzero : s = 0 := by linear_combination ((3/2 : ℝ)) * h3 + ((-1/2 : ℝ)) * h5
    exact (show 0 < s by positivity).ne' hzero
  · have h1 := h 1 2 3 1 2 4
    have h2 := h 1 2 3 1 3 4
    norm_num [minor, gram, distanceCode, edgeIndex, Nat.testBit_eq_decide_div_mod_eq, Fin.ext_iff] at h1 h2
    exfalso
    have hzero : (1 : ℝ) = 0 := by linear_combination ((1 : ℝ)) * h1 + ((-6 : ℝ) + (6 : ℝ) * s ^ 1) * h2
    exact (show 0 < (1 : ℝ) by positivity).ne' hzero
  · have h6 := h 1 2 4 2 3 4
    have h7 := h 1 3 4 1 3 4
    norm_num [minor, gram, distanceCode, edgeIndex, Nat.testBit_eq_decide_div_mod_eq, Fin.ext_iff] at h6 h7
    exfalso
    have hzero : s = 0 := by linear_combination ((-3 : ℝ)) * h6 + ((-1/2 : ℝ)) * h7
    exact (show 0 < s by positivity).ne' hzero
  · have h9 := h 2 3 4 2 3 4
    norm_num [minor, gram, distanceCode, edgeIndex, Nat.testBit_eq_decide_div_mod_eq, Fin.ext_iff] at h9
    exfalso
    have hzero : s ^ 3 = 0 := by linear_combination ((1/4 : ℝ)) * h9
    exact (show 0 < s ^ 3 by positivity).ne' hzero

private def number (m : Fin 16) (n : Fin 64) : ℕ := 64 * m.val + n.val
private def entry (m : Fin 16) (n : Fin 64) : ℕ := (table m)[n.val]!
private def relabel (word : ℕ) (i : Fin 5) : Fin 5 :=
  ⟨word / 5 ^ i.val % 5, Nat.mod_lt _ (by decide)⟩

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
private theorem table_spec (m : Fin 16) : ∀ n : Fin 64,
    (entry m n % 1024) ∈ representatives ∧
    Function.Injective (relabel (entry m n / 1024)) ∧
    ∀ i j : Fin 5, i ≠ j →
      (number m n).testBit (edgeIndex (relabel (entry m n / 1024) i)
        (relabel (entry m n / 1024) j)) =
      (entry m n % 1024).testBit (edgeIndex i j) := by
  fin_cases m <;> decide +kernel

private theorem representative (c : ℕ) (hc : c < 1024) :
    ∃ d ∈ representatives, ∃ σ : Equiv.Perm (Fin 5),
      ∀ i j, i ≠ j → c.testBit (edgeIndex (σ i) (σ j)) = d.testBit (edgeIndex i j) := by
  let m : Fin 16 := ⟨c / 64, by omega⟩
  let n : Fin 64 := ⟨c % 64, by omega⟩
  have hnum : number m n = c := by dsimp [number, m, n]; omega
  obtain ⟨hd, hσ, hp⟩ := table_spec m n
  simp only [hnum] at hp
  exact ⟨_, hd, Equiv.ofBijective _ ⟨hσ, Finite.surjective_of_injective hσ⟩, hp⟩

private theorem point_minor (p : Fin 5 → ℝ²) (c : ℕ) (s : ℝ)
    (h : ∀ i j, dist (p i) (p j) ^ 2 = distanceCode c s i j)
    (a b d e f g : Fin 5) : minor c s a b d e f g = 0 := by
  have hg (i j : Fin 5) : gram c s i j =
      2 * (((p i) 0 - (p 0) 0) * ((p j) 0 - (p 0) 0) +
           ((p i) 1 - (p 0) 1) * ((p j) 1 - (p 0) 1)) := by
    simp only [gram, ← h, EuclideanSpace.dist_sq_eq, Fin.sum_univ_two, Real.dist_eq, sq_abs]
    ring
  simp only [minor, hg]
  ring

private theorem all_bits (n : ℕ) (f : Fin n → Bool) :
    ∃ c < 2 ^ n, ∀ i : Fin n, c.testBit i.val = f i := by
  induction n with
  | zero => exact ⟨0, by simp, fun i => Fin.elim0 i⟩
  | succ n ih =>
    obtain ⟨c, hc, hbit⟩ := ih (f ∘ Fin.succ)
    refine ⟨Nat.bit (f 0) c, Nat.bit_lt_two_pow_succ_iff.mpr hc, ?_⟩
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp
    · simpa [Nat.testBit_bit_succ] using hbit j

private def pairAt : Fin 10 → Fin 5 × Fin 5 :=
  ![(0,1), (0,2), (0,3), (0,4), (1,2), (1,3), (1,4), (2,3), (2,4), (3,4)]

private theorem pairAt_spec : ∀ i j : Fin 5, i ≠ j →
    ∃ k : Fin 10, edgeIndex i j = k.val ∧
      (pairAt k = (i,j) ∨ pairAt k = (j,i)) := by decide +kernel

private theorem normalized_pattern (p : Fin 5 → ℝ²) (s : ℝ) (hs : 1 < s)
    (h : ∀ i j, i ≠ j → dist (p i) (p j)^2 = 1 ∨ dist (p i) (p j)^2 = s) :
    (s^2 - 3 * s + 1 = 0) ∧
    ∃ σ : Equiv.Perm (Fin 5), ∀ i j,
      dist (p (σ i)) (p (σ j))^2 = distanceCode 220 s i j := by
  classical
  let f (k : Fin 10) : Bool := decide (dist (p (pairAt k).1) (p (pairAt k).2)^2 = s)
  obtain ⟨c, hc, hbit⟩ := all_bits 10 f
  have hpat (i j : Fin 5) : dist (p i) (p j)^2 = distanceCode c s i j := by
    by_cases hij : i = j
    · subst j
      simp [distanceCode]
    obtain ⟨k, hk, hpair⟩ := pairAt_spec i j hij
    have hbit' : c.testBit (edgeIndex i j) = decide (dist (p i) (p j)^2 = s) := by
      rw [hk, hbit]
      rcases hpair with hpair | hpair
      · simp [f, hpair]
      · simp [f, hpair, dist_comm]
    rw [distanceCode, if_neg hij, hbit']
    rcases h i j hij with heq | heq
    · have hne : (1 : ℝ) ≠ s := ne_of_lt hs
      simp [heq, hne]
    · simp [heq]
  obtain ⟨d, hd, σ, hσ⟩ := representative c hc
  have hp (i j : Fin 5) : dist (p (σ i)) (p (σ j))^2 = distanceCode d s i j := by
    by_cases hij : i = j
    · subst j
      simp [distanceCode]
    rw [hpat, distanceCode, if_neg (σ.injective.ne hij), hσ i j hij, distanceCode, if_neg hij]
  obtain ⟨rfl, hs'⟩ := eliminate s hs d hd (point_minor (p ∘ σ) d s hp)
  exact ⟨hs', σ, hp⟩

private noncomputable def planeComplex : ℝ² ≃ₗᵢ[ℝ] ℂ :=
  (Complex.isometryOfOrthonormal (EuclideanSpace.basisFun (Fin 2) ℝ)).symm

private theorem witness : ∃ A : Finset ℝ², A.card = 5 ∧ distinctDistances A ≤ 2 := by
  classical
  let z : ℂ := Complex.exp (2 * Real.pi * Complex.I / 5)
  have hz : IsPrimitiveRoot z 5 := by
    simpa [z] using (Complex.isPrimitiveRoot_exp 5 (by decide))
  have hn : ‖z‖ = 1 := by
    have h := congrArg norm hz.pow_eq_one
    rw [norm_pow, norm_one] at h
    exact (pow_left_inj₀ (norm_nonneg _) zero_le_one (by decide : 5 ≠ 0)).mp
      (h.trans (one_pow 5).symm)
  let p (i : Fin 5) : ℝ² := planeComplex.symm (z ^ i.val)
  have hinj : Function.Injective p := by
    intro i j h
    exact Fin.ext (hz.pow_inj i.isLt j.isLt (planeComplex.symm.injective h))
  let A := Finset.univ.image p
  refine ⟨A, by rw [Finset.card_image_of_injective _ hinj]; simp, ?_⟩
  have pair (i j : Fin 5) (h : i < j) :
      dist (p i) (p j) ∈ ({‖1 - z‖, ‖1 - z^2‖} : Finset ℝ) := by
    let k := j.val - i.val
    have hk : 0 < k := Nat.sub_pos_of_lt h
    have hk' : k < 5 := by dsimp [k]; omega
    have hsum : j.val = i.val + k := by dsimp [k]; omega
    have hdist : dist (p i) (p j) = ‖1 - z^k‖ := by
      dsimp [p]
      rw [planeComplex.symm.dist_map, dist_eq_norm, hsum, pow_add,
        show z ^ i.val - z ^ i.val * z ^ k = z ^ i.val * (1 - z ^ k) by ring,
        norm_mul, norm_pow, hn, one_pow, one_mul]
    have hc (a b : ℕ) (hab : a + b = 5) : ‖1 - z^b‖ = ‖1 - z^a‖ := by
      calc
        ‖1 - z^b‖ = ‖z^a * (1 - z^b)‖ := by rw [norm_mul, norm_pow, hn, one_pow, one_mul]
        _ = ‖z^a - 1‖ := by
          rw [mul_sub, mul_one, ← pow_add, hab, hz.pow_eq_one]
        _ = _ := norm_sub_rev _ _
    rw [hdist]
    interval_cases k
    · simp
    · simp
    · rw [hc 2 3 (by decide)]
      simp
    · rw [hc 1 4 (by decide)]
      simp
  unfold distinctDistances distanceSet
  have hs : A.offDiag.image (fun ab : ℝ² × ℝ² => dist ab.1 ab.2) ⊆ {‖1 - z‖, ‖1 - z^2‖} := by
    intro d hd
    obtain ⟨⟨a,b⟩, hab, rfl⟩ := Finset.mem_image.mp hd
    obtain ⟨ha,hb,hab'⟩ := Finset.mem_offDiag.mp hab
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hb
    rcases lt_or_gt_of_ne (fun he => hab' (congrArg p he)) with hij | hji
    · exact pair i j hij
    · rw [dist_comm]
      exact pair j i hji
  exact (Finset.card_le_card hs).trans (Finset.card_insert_le _ _ |>.trans (by simp))

private theorem optimal_shape (A : Finset ℝ²) (hA : Erdos91.IsOptimal A 5) :
    ∃ r : ℝ, 0 < r ∧ ∃ s : ℝ, 1 < s ∧ s^2 - 3*s + 1 = 0 ∧
      ∃ q : Fin 5 → ℝ², Set.range q = A ∧
        ∀ i j, dist (q i) (q j)^2 = r^2 * distanceCode 220 s i j := by
  classical
  obtain ⟨B, hB, hB'⟩ := witness
  have hcount : distinctDistances A ≤ 2 := by
    rw [hA.2]
    have hmin : minimalDistinctDistances ℝ² 5 ≤ distinctDistances B := by
      unfold minimalDistinctDistances
      exact Nat.sInf_le ⟨B, hB, by exact_mod_cast rfl⟩
    exact hmin.trans hB'
  let e : A ≃ Fin 5 := Fintype.equivFinOfCardEq (by simpa using hA.1)
  let p : Fin 5 → ℝ² := fun i => (e.symm i).val
  have hp : Function.Injective p := Subtype.val_injective.comp e.symm.injective
  have hpr : Set.range p = (A : Set ℝ²) := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      exact (e.symm i).property
    · intro hx
      exact ⟨e ⟨x,hx⟩, by simp [p]⟩
  have hi (i j : Fin 5) (h : i ≠ j) : dist (p i) (p j) ∈ distanceSet A :=
    Finset.mem_image.mpr ⟨(p i,p j),
      Finset.mem_offDiag.mpr ⟨(e.symm i).property, (e.symm j).property, hp.ne h⟩, rfl⟩
  have hne : (distanceSet A).Nonempty := ⟨_, hi 0 1 (by decide)⟩
  let r := (distanceSet A).min' hne
  let R := (distanceSet A).max' hne
  have hmemr : r ∈ distanceSet A := Finset.min'_mem _ _
  have hmemR : R ∈ distanceSet A := Finset.max'_mem _ _
  have hpos : 0 < r := by
    obtain ⟨⟨a,b⟩, hab, hr⟩ := Finset.mem_image.mp hmemr
    exact hr ▸ dist_pos.mpr (Finset.mem_offDiag.mp hab).2.2
  have hR : r ≤ R := Finset.min'_le _ _ hmemR
  have hvals (d : ℝ) (hd : d ∈ distanceSet A) : d = r ∨ d = R := by
    have h₁ := Finset.min'_le _ _ hd
    have h₂ := Finset.le_max' _ _ hd
    by_cases hrR : r = R
    · exact Or.inl (by linarith)
    · by_contra! H
      have hsubset : ({d,r,R} : Finset ℝ) ⊆ distanceSet A := by
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl | rfl
        · exact hd
        · exact hmemr
        · exact hmemR
      have h3 := Finset.card_le_card hsubset
      have hcard : ({d,r,R} : Finset ℝ).card = 3 := by simp [H.1, H.2, hrR]
      rw [hcard] at h3
      change (distanceSet A).card ≤ 2 at hcount
      exact (by omega : False)
  let u (i : Fin 5) := r⁻¹ • p i
  have hscaled (i j : Fin 5) : dist (u i) (u j) = dist (p i) (p j) / r := by
    dsimp [u]
    rw [dist_eq_norm, ← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hpos),
      ← dist_eq_norm, div_eq_inv_mul]
  have hlt : r < R := by
    by_contra! H
    have heq := le_antisymm H hR
    have hall (i j : Fin 5) : dist (u i) (u j)^2 = distanceCode 0 2 i j := by
      by_cases hij : i = j
      · subst j
        simp [distanceCode]
      · have h := (hvals _ (hi i j hij)).elim id (fun h => h.trans heq)
        simp [hscaled, h, hpos.ne', distanceCode, hij]
    have hh := point_minor u 0 2 hall 1 2 3 1 2 3
    norm_num [minor, gram, distanceCode, Fin.ext_iff] at hh
  let s := (R / r)^2
  have hs : 1 < s := by
    have hq : 1 < R / r := (lt_div_iff₀ hpos).mpr (by simpa using hlt)
    dsimp [s]
    nlinarith
  have hdist (i j : Fin 5) (hij : i ≠ j) :
      dist (u i) (u j)^2 = 1 ∨ dist (u i) (u j)^2 = s := by
    rw [hscaled]
    rcases hvals _ (hi i j hij) with h | h
    · exact Or.inl (by simp [h, hpos.ne'])
    · exact Or.inr (by rw [h])
  obtain ⟨hs', σ, hσ⟩ := normalized_pattern u s hs hdist
  refine ⟨r, hpos, s, hs, hs', p ∘ σ, ?_, ?_⟩
  · rw [Function.Surjective.range_comp σ.surjective, hpr]
  · intro i j
    have hh := hσ i j
    rw [hscaled, div_pow, div_eq_iff (pow_ne_zero _ hpos.ne')] at hh
    simpa [Function.comp_apply, mul_comm] using hh

private noncomputable def chordNormalize (a b : ℂ) (h : a ≠ b) : ℂ ≃ᵈ ℂ where
  toEquiv :=
    { toFun := fun x => (x-a)/(b-a)
      invFun := fun x => x*(b-a)+a
      left_inv := fun x => by dsimp only; rw [div_mul_cancel₀ _ (sub_ne_zero.mpr h.symm), sub_add_cancel]
      right_inv := fun x => by dsimp only; rw [add_sub_cancel_right, mul_div_cancel_right₀ _ (sub_ne_zero.mpr h.symm)] }
  __ := Dilation.mkOfDistEq (fun x : ℂ => (x-a)/(b-a)) (by
    have hn : ‖(b-a)⁻¹‖₊ ≠ 0 := by
      simp [sub_ne_zero.mpr h.symm]
    refine ⟨‖(b-a)⁻¹‖₊, hn, ?_⟩
    intro x y
    simp only [dist_eq_norm, coe_nnnorm]
    rw [← sub_div, sub_sub_sub_cancel_right, norm_div, norm_inv, div_eq_mul_inv, mul_comm])

private theorem chordSq {a b : ℂ} (h : a ≠ b) (x y : ℂ) :
    dist (chordNormalize a b h x) (chordNormalize a b h y)^2 =
      dist x y ^ 2 / dist a b ^ 2 := by
  change dist ((x-a)/(b-a)) ((y-a)/(b-a))^2 = _
  rw [dist_eq_norm, ← sub_div, sub_sub_sub_cancel_right, norm_div, div_pow, dist_eq_norm,
    dist_eq_norm, norm_sub_rev a b]

private theorem distSqComplex (x y : ℂ) :
    dist x y ^ 2 = (x.re - y.re)^2 + (x.im - y.im)^2 := by
  rw [dist_eq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im]
  ring

private theorem conjugate_or_equal (a b : Fin 5 → ℂ)
    (ha0 : a 0 = 0) (ha1 : a 1 = 1) (hb0 : b 0 = 0) (hb1 : b 1 = 1)
    (h : ∀ i j, dist (a i) (a j)^2 = dist (b i) (b j)^2) :
    (∀ i, a i = b i) ∨ (∀ i, star (a i) = b i) := by
  have hre (i : Fin 5) : (a i).re = (b i).re := by
    have h₀ := h i 0
    have h₁ := h i 1
    simp only [ha0, hb0, ha1, hb1, distSqComplex, Complex.zero_re, Complex.zero_im,
      Complex.one_re, Complex.one_im, sub_zero] at h₀ h₁
    nlinarith only [h₀, h₁]
  have hi (i : Fin 5) : (a i).im ^ 2 = (b i).im ^ 2 := by
    have hh := h i 0
    simp only [ha0, hb0, distSqComplex, Complex.zero_re, Complex.zero_im, sub_zero, hre i] at hh
    linarith only [hh]
  have hmul (i j : Fin 5) : (a i).im * (a j).im = (b i).im * (b j).im := by
    have hh := h i j
    simp only [distSqComplex, hre i, hre j, add_right_inj] at hh
    nlinarith only [hh, hi i, hi j]
  by_cases hall : ∀ i, (a i).im = 0
  · refine Or.inl fun i => Complex.ext (hre i) ?_
    have hh : (b i).im = 0 := by simpa [hall i, pow_two, eq_comm] using hi i
    rw [hh, hall]
  · push Not at hall
    obtain ⟨j, hj⟩ := hall
    have hcases : (a j).im = (b j).im ∨ -(a j).im = (b j).im := by
      have he : ((a j).im - (b j).im) * (-(a j).im - (b j).im) = 0 := by
        nlinarith only [hi j]
      exact (mul_eq_zero.mp he).imp sub_eq_zero.mp sub_eq_zero.mp
    rcases hcases with hsame | hneg
    · refine Or.inl fun i => Complex.ext (hre i) ?_
      have hh := hmul i j
      rw [← hsame] at hh
      exact mul_right_cancel₀ hj hh
    · refine Or.inr fun i => Complex.ext (by simpa using hre i) ?_
      change -(a i).im = (b i).im
      apply mul_right_cancel₀ hj
      have hh := hmul i j
      rw [← hneg] at hh
      linarith only [hh]

private theorem similarity_of_scaled_dist (p q : Fin 5 → ℝ²) (r t : ℝ) (hr : 0 < r) (ht : 0 < t)
    (hp : p 0 ≠ p 1) (hq : q 0 ≠ q 1)
    (hd : ∀ i j, dist (p i) (p j)^2 / r^2 = dist (q i) (q j)^2 / t^2) :
    ∃ f : ℝ² ≃ᵈ ℝ², ∀ i, f (p i) = q i := by
  let e := planeComplex.toIsometryEquiv.toDilationEquiv
  let A := chordNormalize (e (p 0)) (e (p 1)) (e.injective.ne hp)
  let B := chordNormalize (e (q 0)) (e (q 1)) (e.injective.ne hq)
  let a := A ∘ e ∘ p
  let b := B ∘ e ∘ q
  have ha0 : a 0 = 0 := by
    change (e (p 0) - e (p 0)) / (e (p 1) - e (p 0)) = 0
    simp
  have hb0 : b 0 = 0 := by
    change (e (q 0) - e (q 0)) / (e (q 1) - e (q 0)) = 0
    simp
  have ha1 : a 1 = 1 := by
    change (e (p 1) - e (p 0)) / (e (p 1) - e (p 0)) = 1
    exact div_self (sub_ne_zero.mpr (e.injective.ne hp.symm))
  have hb1 : b 1 = 1 := by
    change (e (q 1) - e (q 0)) / (e (q 1) - e (q 0)) = 1
    exact div_self (sub_ne_zero.mpr (e.injective.ne hq.symm))
  have hab (i j : Fin 5) : dist (a i) (a j)^2 = dist (b i) (b j)^2 := by
    have hh := hd i j
    have hk := hd 0 1
    have hn : dist (p 0) (p 1) ≠ 0 := dist_ne_zero.mpr hp
    have hn' : dist (q 0) (q 1) ≠ 0 := dist_ne_zero.mpr hq
    dsimp [a,b,A,B,Function.comp_apply]
    rw [chordSq, chordSq]
    change dist (planeComplex (p i)) (planeComplex (p j))^2 /
      dist (planeComplex (p 0)) (planeComplex (p 1))^2 =
      dist (planeComplex (q i)) (planeComplex (q j))^2 /
      dist (planeComplex (q 0)) (planeComplex (q 1))^2
    simp only [planeComplex.dist_map]
    calc
      _ = (dist (p i) (p j)^2 / r^2) / (dist (p 0) (p 1)^2 / r^2) := by
        field_simp
      _ = (dist (q i) (q j)^2 / t^2) / (dist (q 0) (q 1)^2 / t^2) := by rw [hh, hk]
      _ = _ := by field_simp
  have he (F : ℂ ≃ᵈ ℂ) (h : ∀ i, F (a i) = b i) :
      ∃ f : ℝ² ≃ᵈ ℝ², ∀ i, f (p i) = q i := by
    refine ⟨(e.trans A).trans (F.trans (e.trans B).symm), fun i => ?_⟩
    change (e.trans B).symm (F (a i)) = q i
    rw [h]
    exact (e.trans B).symm_apply_apply (q i)
  rcases conjugate_or_equal a b ha0 ha1 hb0 hb1 hab with h | h
  · exact he (DilationEquiv.refl ℂ) h
  · exact he Complex.conjLIE.toIsometryEquiv.toDilationEquiv h

end FiveDistances

theorem OMA.solution : type_of% @Erdos91.erdos_91.variants.five := by
  intro A B hA hB
  obtain ⟨r, hr, s, hs, hsp, p, hp, hpd⟩ := FiveDistances.optimal_shape A hA
  obtain ⟨t, ht, u, hu, hup, q, hq, hqd⟩ := FiveDistances.optimal_shape B hB
  have hsu : s = u := by
    have hh : (s-u) * (s+u-3) = 0 := by nlinarith only [hsp, hup]
    rcases mul_eq_zero.mp hh with he | he
    · exact sub_eq_zero.mp he
    · have h : (s-1)*(u-1) = -1 := by
        have he' : u = 3-s := by linarith only [he]
        rw [he']
        nlinarith only [hsp]
      nlinarith only [h, mul_pos (sub_pos.mpr hs) (sub_pos.mpr hu)]
  have hpn : p 0 ≠ p 1 := by
    intro H
    have hh := hpd 0 1
    norm_num [H, FiveDistances.distanceCode, FiveDistances.edgeIndex,
      Nat.testBit_eq_decide_div_mod_eq] at hh
    nlinarith only [hh, sq_pos_of_pos hr]
  have hqn : q 0 ≠ q 1 := by
    intro H
    have hh := hqd 0 1
    norm_num [H, FiveDistances.distanceCode, FiveDistances.edgeIndex,
      Nat.testBit_eq_decide_div_mod_eq] at hh
    nlinarith only [hh, sq_pos_of_pos ht]
  obtain ⟨f,hf⟩ := FiveDistances.similarity_of_scaled_dist p q r t hr ht hpn hqn (fun i j => by
    rw [hpd, hqd, hsu, mul_comm (r^2), mul_comm (t^2),
      mul_div_cancel_right₀ _ (pow_ne_zero _ hr.ne'),
      mul_div_cancel_right₀ _ (pow_ne_zero _ ht.ne')])
  refine ⟨f, ?_⟩
  have he : (f : ℝ² → ℝ²) ∘ p = q := funext hf
  rw [← hp, ← hq, ← Set.range_comp, he]