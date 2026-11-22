/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.ClassifyingSpace.Action
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Algebra.InfiniteSum.Basic
public import Mathlib.Topology.Algebra.MulAction
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.Separation.Hausdorff

/-!
# The strong-coordinate Milnor join of a topological space or group

Following Milnor (*Construction of universal bundles, II*, §2) and tom Dieck (*Algebraic Topology*,
§14.4.3), `TauCeti.MilnorTotalSpace G` is a distinct type copy of `universalGSpace G` carrying the
*strong coordinate topology*: the coarsest topology making every weight `t_i : EG → ℝ` continuous
and every vertex label `g_i : U_i → G` continuous on `U_i = {p | 0 < t_i p}`, avoiding diamonds
with the weak simplicial topology and left group action on `universalGSpace G`.

## Main definitions and results

* `TauCeti.MilnorTotalSpace`, `weight`, `coordSet`, `label`, `map`, `continuous_iff`, `instT2Space`:
  strong-topology join, coordinates `(t_i, g_i)`, universal continuity criterion, and Hausdorffness.
* `TauCeti.MilnorTotalSpace.instContinuousSMul`, `invEquiv`, `TauCeti.weakToMilnorTotalSpace`,
  `MonoidHom.milnorTotalSpaceMap`: joint continuity of the right `Gᵐᵒᵖ`-action from `ContinuousMul`,
  label-inversion dictionary (`g⁻¹ • x ↦ (invEquiv x) · g`), and functoriality.

## References

* J. Milnor, *Construction of universal bundles, II*, Ann. of Math. (2) 63 (1956), 430–436, §§2–3.
* T. tom Dieck, *Algebraic Topology*, EMS Textbooks in Mathematics, 2008, §14.4.3.
-/

public section

noncomputable section

open AbstractSimplicialComplex Filter Function MulOpposite Set Topology

universe u v w

namespace TauCeti

/-- Milnor's countable join of copies of `G`, realized as a distinct type copy of
`universalGSpace G` carrying the strong coordinate topology and right label action. -/
@[ext] structure MilnorTotalSpace (G : Type u) where
  /-- View a point of the simplicial countable join as a point of `MilnorTotalSpace G`. -/
  ofRealization ::
  /-- The underlying point of the simplicial countable join `universalGSpace G`. -/
  toRealization : universalGSpace G

namespace MilnorTotalSpace

section Coordinates

variable {G : Type u}

/-- The carrier equivalence between `MilnorTotalSpace G` and `universalGSpace G`. -/
def equivRealization (G : Type u) : MilnorTotalSpace G ≃ universalGSpace G :=
  ⟨toRealization, ofRealization, fun _ ↦ rfl, fun _ ↦ rfl⟩

@[simp] theorem equivRealization_apply (p : MilnorTotalSpace G) :
    equivRealization G p = p.toRealization := (rfl)
@[simp] theorem equivRealization_symm_apply (x : universalGSpace G) :
    (equivRealization G).symm x = ofRealization x := (rfl)

/-- Underlying finitely supported barycentric coordinate vector on `Σ _ : ℕ, G`. -/
def val (p : MilnorTotalSpace G) : (Σ _ : ℕ, G) →₀ ℝ := p.toRealization.val

@[simp] theorem val_ofRealization (x : universalGSpace G) : (ofRealization x).val = x.val := (rfl)

theorem ext_val {p q : MilnorTotalSpace G} (h : p.val = q.val) : p = q :=
  MilnorTotalSpace.ext (Subtype.ext h)

theorem val_nonneg (p : MilnorTotalSpace G) (v : Σ _ : ℕ, G) : 0 ≤ p.val v :=
  Realization.nonneg _ p.toRealization v
theorem sum_val (p : MilnorTotalSpace G) : p.val.sum (fun _ r ↦ r) = 1 :=
  Realization.sum_eq_one _ p.toRealization
theorem support_val_injOn_fst (p : MilnorTotalSpace G) :
    InjOn Sigma.fst (p.val.support : Set (Σ _ : ℕ, G)) :=
  realization_support_injOn_fst p.toRealization

/-- The vertex of `MilnorTotalSpace G` concentrated at index `i` with label `a`. -/
def vertex (i : ℕ) (a : G) : MilnorTotalSpace G :=
  ofRealization ((indexedJoin fun _ : ℕ ↦ G).vertex ⟨i, a⟩)

@[simp] theorem toRealization_vertex (i : ℕ) (a : G) :
    (vertex i a).toRealization = (indexedJoin fun _ : ℕ ↦ G).vertex ⟨i, a⟩ := (rfl)
@[simp] theorem val_vertex (i : ℕ) (a : G) : (vertex i a).val = Finsupp.single ⟨i, a⟩ 1 := by
  let _ : DecidableEq (Σ _ : ℕ, G) := Classical.decEq _
  exact AbstractSimplicialComplex.vertex_val (indexedJoin fun _ : ℕ ↦ G) (⟨i, a⟩ : Σ _ : ℕ, G)

/-- The distinguished base point of `MilnorTotalSpace G` at index `0` and label `1`. -/
def basepoint (G : Type u) [One G] : MilnorTotalSpace G := vertex 0 1

@[simp] theorem val_basepoint (G : Type u) [One G] : (basepoint G).val = Finsupp.single ⟨0, 1⟩ 1 :=
  val_vertex 0 1
@[simp] theorem toRealization_basepoint (G : Type u) [One G] :
    (basepoint G).toRealization = universalGSpaceBasepoint G :=
  Subtype.ext ((val_basepoint G).trans (universalGSpaceBasepoint_val G).symm)

instance instNonempty [Nonempty G] : Nonempty (MilnorTotalSpace G) :=
  let ⟨a⟩ := ‹Nonempty G›; ⟨vertex 0 a⟩
instance instInhabited [One G] : Inhabited (MilnorTotalSpace G) := ⟨basepoint G⟩

theorem nonempty_of_milnorTotalSpace (p : MilnorTotalSpace G) : Nonempty G := by
  have hne : p.val.support.Nonempty := Finsupp.support_nonempty_iff.mpr fun h0 ↦
    zero_ne_one (α := ℝ) (by simpa [h0] using p.sum_val)
  exact ⟨hne.choose.2⟩

@[simp] theorem isEmpty_iff : IsEmpty (MilnorTotalSpace G) ↔ IsEmpty G :=
  ⟨fun h ↦ ⟨fun a ↦ h.false (vertex 0 a)⟩,
    fun h ↦ ⟨fun p ↦ (nonempty_of_milnorTotalSpace p).elim h.false⟩⟩

private def weightFinsupp (p : MilnorTotalSpace G) : ℕ →₀ ℝ := Finsupp.mapDomain Sigma.fst p.val

/-- The `i`-th barycentric weight `t_i(p)` of a point in `MilnorTotalSpace G`. -/
def weight (i : ℕ) (p : MilnorTotalSpace G) : ℝ := p.weightFinsupp i

theorem weight_def (i : ℕ) (p : MilnorTotalSpace G) :
    weight i p = Finsupp.mapDomain Sigma.fst p.val i := (rfl)

theorem weight_eq_val_of_ne_zero {i : ℕ} {a : G} {p : MilnorTotalSpace G} (ha : p.val ⟨i, a⟩ ≠ 0) :
    weight i p = p.val ⟨i, a⟩ :=
  Finsupp.mapDomain_apply' p.val.support p.val Subset.rfl p.support_val_injOn_fst
    (Finsupp.mem_support_iff.mpr ha)

private theorem support_weightFinsupp (p : MilnorTotalSpace G) :
    p.weightFinsupp.support = p.val.support.image Sigma.fst :=
  Finsupp.mapDomain_support_of_injOn p.val p.support_val_injOn_fst

theorem weight_ne_zero_iff {i : ℕ} {p : MilnorTotalSpace G} :
    weight i p ≠ 0 ↔ ∃ a : G, p.val ⟨i, a⟩ ≠ 0 := by
  rw [weight, ← Finsupp.mem_support_iff, support_weightFinsupp, Finset.mem_image]
  exact ⟨fun ⟨⟨_, a⟩, hv, rfl⟩ ↦ ⟨a, Finsupp.mem_support_iff.mp hv⟩,
    fun ⟨a, ha⟩ ↦ ⟨⟨i, a⟩, Finsupp.mem_support_iff.mpr ha, rfl⟩⟩

theorem weight_nonneg (i : ℕ) (p : MilnorTotalSpace G) : 0 ≤ weight i p := by
  by_cases h : weight i p = 0
  · exact h.symm.le
  · obtain ⟨a, ha⟩ := weight_ne_zero_iff.mp h
    rw [weight_eq_val_of_ne_zero ha]; exact p.val_nonneg ⟨i, a⟩

theorem weight_pos_iff {i : ℕ} {p : MilnorTotalSpace G} :
    0 < weight i p ↔ ∃ a : G, 0 < p.val ⟨i, a⟩ :=
  ⟨fun hp ↦ let ⟨a, ha⟩ := weight_ne_zero_iff.mp hp.ne'
    ⟨a, lt_of_le_of_ne (p.val_nonneg ⟨i, a⟩) ha.symm⟩,
   fun ⟨_, ha⟩ ↦ (weight_eq_val_of_ne_zero ha.ne').symm ▸ ha⟩

/-- The open star `U_i = {p | 0 < t_i(p)}` of points with positive `i`-th weight. -/
def coordSet (G : Type u) (i : ℕ) : Set (MilnorTotalSpace G) := {p | 0 < weight i p}

@[simp] theorem mem_coordSet_iff {i : ℕ} {p : MilnorTotalSpace G} :
    p ∈ coordSet G i ↔ 0 < weight i p := Iff.rfl

theorem finite_support_weight (p : MilnorTotalSpace G) :
    (Function.support fun i ↦ weight i p).Finite := by
  convert p.weightFinsupp.support.finite_toSet using 1
  ext i; exact (Finsupp.mem_support_iff (f := p.weightFinsupp)).symm

private theorem sum_weightFinsupp (p : MilnorTotalSpace G) :
    p.weightFinsupp.sum (fun _ r ↦ r) = 1 := by
  rw [weightFinsupp, Finsupp.sum_mapDomain_index (fun _ ↦ rfl) (fun _ _ _ ↦ rfl), p.sum_val]

theorem hasSum_weight (p : MilnorTotalSpace G) : HasSum (fun i ↦ weight i p) 1 :=
  p.sum_weightFinsupp ▸ hasSum_sum_of_ne_finset_zero fun _ ↦ Finsupp.notMem_support_iff.mp

@[simp] theorem tsum_weight (p : MilnorTotalSpace G) : ∑' i, weight i p = 1 :=
  (hasSum_weight p).tsum_eq

@[simp] theorem finsum_weight (p : MilnorTotalSpace G) : ∑ᶠ i, weight i p = 1 :=
  (tsum_eq_finsum (L := SummationFilter.unconditional ℕ) (finite_support_weight p)).symm.trans
    (tsum_weight p)

theorem weight_le_one (i : ℕ) (p : MilnorTotalSpace G) : weight i p ≤ 1 :=
  le_hasSum (hasSum_weight p) i fun j _ ↦ weight_nonneg j p

theorem exists_weight_pos (p : MilnorTotalSpace G) : ∃ i, 0 < weight i p := by
  by_contra! h
  simpa [fun i ↦ le_antisymm (h i) (weight_nonneg i p)] using tsum_weight p

@[simp] theorem iUnion_coordSet (G : Type u) : ⋃ i, coordSet G i = univ :=
  eq_univ_of_forall fun p ↦ mem_iUnion.mpr (exists_weight_pos p)

/-- The `i`-th vertex label `g_i(p)` of `p : MilnorTotalSpace G` (unique when `0 < weight i p`). -/
def label (i : ℕ) (p : MilnorTotalSpace G) : G := by
  classical
  exact if h : ∃ a : G, p.val ⟨i, a⟩ ≠ 0 then h.choose else (nonempty_of_milnorTotalSpace p).some

theorem val_label_eq_weight {i : ℕ} {p : MilnorTotalSpace G} (hp : p ∈ coordSet G i) :
    p.val ⟨i, label i p⟩ = weight i p := by
  classical
  have hex : ∃ a : G, p.val ⟨i, a⟩ ≠ 0 := weight_ne_zero_iff.mp hp.ne'
  exact (weight_eq_val_of_ne_zero (by simpa [label, hex] using hex.choose_spec)).symm

theorem eq_label_of_val_ne_zero {i : ℕ} {a : G} {p : MilnorTotalSpace G} (ha : p.val ⟨i, a⟩ ≠ 0) :
    a = label i p := by
  have hp : p ∈ coordSet G i := mem_coordSet_iff.mpr <|
    (weight_eq_val_of_ne_zero ha).symm ▸ lt_of_le_of_ne (p.val_nonneg ⟨i, a⟩) ha.symm
  have hl : p.val ⟨i, label i p⟩ ≠ 0 := (val_label_eq_weight hp).symm ▸ hp.ne'
  by_contra hne
  exact (realization_apply_eq_zero_of_fst_eq (x := p.toRealization) (v := ⟨i, a⟩)
    (w := ⟨i, label i p⟩) rfl (fun h ↦ hne (congrArg Sigma.snd h))).elim ha hl

theorem eq_label_of_val_pos {i : ℕ} {a : G} {p : MilnorTotalSpace G} (ha : 0 < p.val ⟨i, a⟩) :
    a = label i p := eq_label_of_val_ne_zero ha.ne'

theorem val_apply_eq_ite [DecidableEq G] (i : ℕ) (a : G) (p : MilnorTotalSpace G) :
    p.val ⟨i, a⟩ = if a = label i p then weight i p else 0 := by
  by_cases hp : p ∈ coordSet G i
  · split_ifs with h
    · rw [h, val_label_eq_weight hp]
    · exact not_not.mp fun hne ↦ h (eq_label_of_val_ne_zero hne)
  · have hw : weight i p = 0 := le_antisymm (not_lt.mp hp) (weight_nonneg i p)
    rw [not_not.mp fun hne ↦ weight_ne_zero_iff.mpr ⟨a, hne⟩ hw, hw, ite_self]

/-- Coordinate extensionality: two points agree iff their weights and positive-weight labels do. -/
theorem ext_coord {p q : MilnorTotalSpace G} (hw : ∀ i, weight i p = weight i q)
    (hl : ∀ i, p ∈ coordSet G i → label i p = label i q) : p = q := by
  classical
  refine ext_val (Finsupp.ext fun ⟨i, a⟩ ↦ ?_)
  rw [val_apply_eq_ite, val_apply_eq_ite, hw i]
  by_cases hp : p ∈ coordSet G i
  · rw [hl i hp]
  · rw [← hw i, le_antisymm (not_lt.mp hp) (weight_nonneg i p), ite_self, ite_self]

@[simp] theorem weight_vertex (i j : ℕ) (a : G) :
    weight i (vertex j a) = if i = j then 1 else 0 := by
  classical
  rw [weight_def, val_vertex, Finsupp.mapDomain_single]; simp [Finsupp.single_apply, eq_comm]
@[simp] theorem label_vertex (i : ℕ) (a : G) : label i (vertex i a) = a :=
  (eq_label_of_val_pos (p := vertex i a) (by simp)).symm
@[simp] theorem weight_basepoint (G : Type u) [One G] (i : ℕ) :
    weight i (basepoint G) = if i = 0 then 1 else 0 := weight_vertex i 0 1
@[simp] theorem label_basepoint (G : Type u) [One G] : label 0 (basepoint G) = 1 :=
  label_vertex 0 1

/-- Vertex relabelling `MilnorTotalSpace X → MilnorTotalSpace Y` induced by `f : X → Y`. -/
def relabel {X : Type u} {Y : Type v} (f : X → Y) (p : MilnorTotalSpace X) : MilnorTotalSpace Y :=
  letI := Classical.decEq ℕ; letI := Classical.decEq X; letI := Classical.decEq Y
  ofRealization ((indexedJoinMap (A := fun _ : ℕ ↦ X) (B := fun _ : ℕ ↦ Y)
    _root_.id Function.injective_id (fun _ ↦ f)).realizationMap p.toRealization)

theorem val_relabel {X : Type u} {Y : Type v} (f : X → Y) (p : MilnorTotalSpace X) :
    (relabel f p).val =
      Finsupp.mapDomain (fun v : Σ _ : ℕ, X ↦ (⟨v.1, f v.2⟩ : Σ _ : ℕ, Y)) p.val := by
  let _ := Classical.decEq ℕ; let _ := Classical.decEq X; let _ := Classical.decEq Y
  exact (PreAbstractSimplicialComplex.SimplicialMap.realizationMap_val
    (indexedJoinMap (A := fun _ : ℕ ↦ X) (B := fun _ : ℕ ↦ Y)
      _root_.id Function.injective_id (fun _ ↦ f)) p.toRealization).trans
    (congrArg (Finsupp.mapDomain · p.val) (funext (indexedJoinMap_apply
      (A := fun _ : ℕ ↦ X) (B := fun _ : ℕ ↦ Y) _root_.id Function.injective_id (fun _ ↦ f))))

@[simp] theorem weight_relabel {X : Type u} {Y : Type v} (f : X → Y) (i : ℕ)
    (p : MilnorTotalSpace X) : weight i (relabel f p) = weight i p := by
  rw [weight_def, weight_def, val_relabel, ← Finsupp.mapDomain_comp]; rfl

@[simp] theorem label_relabel {X : Type u} {Y : Type v} (f : X → Y) {i : ℕ}
    {p : MilnorTotalSpace X} (hp : p ∈ coordSet X i) :
    label i (relabel f p) = f (label i p) := by
  symm; apply eq_label_of_val_pos; rw [val_relabel]
  have hinj : InjOn (fun v : Σ _ : ℕ, X ↦ (⟨v.1, f v.2⟩ : Σ _ : ℕ, Y)) p.val.support :=
    fun u hu v hv huv ↦ p.support_val_injOn_fst hu hv (Sigma.mk.inj huv).1
  have hmem : (⟨i, label i p⟩ : Σ _ : ℕ, X) ∈ p.val.support :=
    Finsupp.mem_support_iff.mpr (by rw [val_label_eq_weight hp]; exact hp.ne')
  rwa [Finsupp.mapDomain_apply' p.val.support p.val Subset.rfl hinj hmem, val_label_eq_weight hp]

@[simp] theorem relabel_id (p : MilnorTotalSpace G) : relabel _root_.id p = p :=
  ext_val (by simp [val_relabel])
@[simp] theorem relabel_comp {X : Type u} {Y : Type v} {Z : Type w}
    (g : Y → Z) (f : X → Y) (p : MilnorTotalSpace X) :
    relabel g (relabel f p) = relabel (g ∘ f) p :=
  ext_val (by simp only [val_relabel, ← Finsupp.mapDomain_comp]; rfl)

end Coordinates

/-! ### Strong coordinate topology -/

section Topology

variable {G : Type u} [TopologicalSpace G]

/-- The strong coordinate topology on `MilnorTotalSpace G`, generated by `weight i` and `label i`
on `coordSet G i`. -/
instance instTopologicalSpace : TopologicalSpace (MilnorTotalSpace G) :=
  TopologicalSpace.generateFrom
    ({s | ∃ (i : ℕ) (W : Set ℝ), IsOpen W ∧ s = weight i ⁻¹' W} ∪
      {s | ∃ (i : ℕ) (V : Set G), IsOpen V ∧ s = coordSet G i ∩ label i ⁻¹' V})

/-- **Universal continuity criterion for the strong coordinate topology.** -/
theorem continuous_iff {Z : Type*} [TopologicalSpace Z] {f : Z → MilnorTotalSpace G} :
    Continuous f ↔ (∀ i, Continuous fun z ↦ weight i (f z)) ∧
      ∀ i, ContinuousOn (fun z ↦ label i (f z)) {z | 0 < weight i (f z)} := by
  rw [continuous_generateFrom_iff]
  constructor
  · intro hf
    refine ⟨fun i ↦ continuous_def.mpr fun W hW ↦ hf _ (Or.inl ⟨i, W, hW, rfl⟩), fun i ↦ ?_⟩
    rw [continuousOn_iff_continuous_domRestrict, continuous_def]; intro V hV
    convert (hf _ (Or.inr ⟨i, V, hV, rfl⟩)).preimage
      (continuous_subtypeVal (p := fun z ↦ 0 < weight i (f z))) using 1
    ext ⟨z, hz⟩; exact ⟨fun h ↦ ⟨hz, h⟩, fun h ↦ h.2⟩
  · rintro ⟨hw, hl⟩ s (⟨i, W, hW, rfl⟩ | ⟨i, V, hV, rfl⟩)
    · exact hW.preimage (hw i)
    · have hO : IsOpen {z | 0 < weight i (f z)} := isOpen_lt continuous_const (hw i)
      obtain ⟨U, hU, hUV⟩ := continuousOn_iff'.mp (hl i) V hV
      convert hU.inter hO using 1
      ext z; have hz := Set.ext_iff.mp hUV z
      simp only [mem_preimage, mem_inter_iff, mem_coordSet_iff, mem_ofPred_eq] at hz ⊢
      exact ⟨fun h ↦ ⟨(hz.mp ⟨h.2, h.1⟩).1, h.1⟩, fun h ↦ ⟨h.2, (hz.mpr h).1⟩⟩

@[fun_prop, continuity]
theorem continuous_weight (i : ℕ) : Continuous (weight i : MilnorTotalSpace G → ℝ) :=
  (continuous_iff.mp continuous_id).1 i

theorem isOpen_coordSet (i : ℕ) : IsOpen (coordSet G i) :=
  isOpen_lt continuous_const (continuous_weight i)

theorem continuousOn_label (i : ℕ) :
    ContinuousOn (label i : MilnorTotalSpace G → G) (coordSet G i) :=
  (continuous_iff.mp continuous_id).2 i

@[fun_prop, continuity]
theorem continuous_vertex (i : ℕ) : Continuous (vertex i : G → MilnorTotalSpace G) := by
  rw [continuous_iff]
  refine ⟨fun j ↦ by simp only [weight_vertex]; exact continuous_const, fun j ↦ ?_⟩
  by_cases hij : j = i
  · subst hij; simp only [weight_vertex, ↓reduceIte, zero_lt_one, Set.ofPred_true, label_vertex]
    exact continuousOn_id
  · simp only [weight_vertex, hij, ↓reduceIte, lt_self_iff_false, Set.ofPred_false]
    exact continuousOn_empty _

instance instT2Space [T2Space G] : T2Space (MilnorTotalSpace G) :=
  t2Space_iff_disjoint_nhds.mpr fun p q hpq ↦ by
    by_cases hw : ∀ i, weight i p = weight i q
    · have ⟨i, hpi, hlpq⟩ : ∃ i, p ∈ coordSet G i ∧ label i p ≠ label i q := by
        by_contra! h; exact hpq (ext_coord hw h)
      have hqi : q ∈ coordSet G i := by rwa [mem_coordSet_iff, ← hw i]
      exact ((continuousOn_label i).continuousAt
        ((isOpen_coordSet i).mem_nhds hpi)).tendsto.disjoint
        (disjoint_nhds_nhds.mpr hlpq)
        ((continuousOn_label i).continuousAt ((isOpen_coordSet i).mem_nhds hqi)).tendsto
    · obtain ⟨i, hi⟩ := not_forall.mp hw
      exact (continuous_weight i).continuousAt.tendsto.disjoint (disjoint_nhds_nhds.mpr hi)
        (continuous_weight i).continuousAt.tendsto

/-- The carrier identification from `universalGSpace G` (weak simplicial realization topology)
to `MilnorTotalSpace G` (strong coordinate topology) is continuous. -/
theorem continuous_ofRealization :
    Continuous (ofRealization : universalGSpace G → MilnorTotalSpace G) := by
  rw [continuous_iff_faceInclusion]; intro σ; rw [continuous_iff]
  let F : StandardSimplex σ.val → MilnorTotalSpace G :=
    ofRealization ∘ (indexedJoin fun _ : ℕ ↦ G).faceInclusion σ
  have hval (x : StandardSimplex σ.val) : (F x).val = x.val := faceInclusion_val _ σ x
  have hmem {i : ℕ} {b : G} {x : StandardSimplex σ.val} (hb : x.val ⟨i, b⟩ ≠ 0) :
      (⟨i, b⟩ : Σ _ : ℕ, G) ∈ σ.val :=
    StandardSimplex.support_subset x (Finsupp.mem_support_iff.mpr hb)
  refine ⟨fun i ↦ ?_, fun i ↦ ?_⟩
  · by_cases hex : ∃ a : G, (⟨i, a⟩ : Σ _ : ℕ, G) ∈ σ.val
    · obtain ⟨a, ha⟩ := hex
      suffices (fun x ↦ weight i (F x)) = fun x ↦ x.val ⟨i, a⟩ from
        this ▸ (continuous_apply (⟨i, a⟩ : Σ _ : ℕ, G)).comp continuous_induced_dom
      ext x
      by_cases hx0 : x.val ⟨i, a⟩ = 0
      · rw [hx0]; refine not_not.mp fun hne ↦ ?_
        obtain ⟨b, hb⟩ := weight_ne_zero_iff.mp hne; rw [hval x] at hb
        exact hb (by simpa [eq_of_mem_indexedJoin σ.property (hmem hb) ha rfl] using hx0)
      · exact (weight_eq_val_of_ne_zero (by rwa [hval x])).trans (by rw [hval x])
    · push Not at hex
      suffices (fun x ↦ weight i (F x)) = 0 from this ▸ continuous_const
      ext x; refine not_not.mp fun hne ↦ ?_
      obtain ⟨a, ha⟩ := weight_ne_zero_iff.mp hne
      exact hex a (hmem (by rwa [hval x] at ha))
  · by_cases hex : ∃ a : G, (⟨i, a⟩ : Σ _ : ℕ, G) ∈ σ.val
    · obtain ⟨a, ha⟩ := hex
      refine (continuousOn_const (c := a)).congr fun x hx ↦ ?_
      obtain ⟨b, hb⟩ := weight_pos_iff.mp hx
      have hb' : x.val ⟨i, b⟩ ≠ 0 := by rw [← hval x]; exact hb.ne'
      exact (eq_label_of_val_pos hb).symm.trans
        (congrArg Sigma.snd (eq_of_mem_indexedJoin σ.property (hmem hb') ha rfl))
    · push Not at hex
      refine (continuousOn_empty _).mono fun x hx ↦ ?_
      obtain ⟨a, ha⟩ := weight_pos_iff.mp hx
      exact hex a (hmem (by rw [← hval x]; exact ha.ne'))

/-- Functorial map `MilnorTotalSpace X → MilnorTotalSpace Y` induced by `f : C(X, Y)`. -/
def map {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y] (f : C(X, Y)) :
    C(MilnorTotalSpace X, MilnorTotalSpace Y) where
  toFun := relabel f
  continuous_toFun := continuous_iff.mpr
    ⟨fun i ↦ by simp_rw [weight_relabel]; exact continuous_weight i,
     fun i ↦ by
      simp_rw [weight_relabel]
      exact (f.continuous.comp_continuousOn (continuousOn_label i)).congr fun _ ↦ label_relabel f⟩

theorem val_map {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) (p : MilnorTotalSpace X) :
    (map f p).val =
      Finsupp.mapDomain (fun v : Σ _ : ℕ, X ↦ (⟨v.1, f v.2⟩ : Σ _ : ℕ, Y)) p.val :=
  val_relabel f p

@[simp] theorem weight_map {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) (i : ℕ) (p : MilnorTotalSpace X) :
    weight i (map f p) = weight i p := weight_relabel f i p
@[simp] theorem label_map {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) {i : ℕ} {p : MilnorTotalSpace X} (hp : p ∈ coordSet X i) :
    label i (map f p) = f (label i p) := label_relabel f hp
@[simp] theorem map_vertex {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) (i : ℕ) (x : X) : map f (vertex i x) = vertex i (f x) :=
  ext_val (by rw [val_map, val_vertex, val_vertex, Finsupp.mapDomain_single])
@[simp] theorem map_id (X : Type u) [TopologicalSpace X] :
    map (ContinuousMap.id X) = ContinuousMap.id (MilnorTotalSpace X) := by
  ext p : 1; exact relabel_id p
@[simp] theorem map_comp {X : Type u} {Y : Type v} {Z : Type w}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] (g : C(Y, Z)) (f : C(X, Y)) :
    map (g.comp f) = (map g).comp (map f) := by
  ext p : 1; exact (relabel_comp g f p).symm

end Topology

/-! ### Right action dictionary and joint continuity -/

section RightAction

variable {G : Type u}

section Monoid

variable [Monoid G]

instance instSMulOp : SMul Gᵐᵒᵖ (MilnorTotalSpace G) := ⟨fun g p ↦ relabel (· * g.unop) p⟩

private theorem smul_def (g : Gᵐᵒᵖ) (p : MilnorTotalSpace G) :
    g • p = relabel (· * g.unop) p := rfl

theorem val_op_smul (g : G) (p : MilnorTotalSpace G) :
    (op g • p).val =
      Finsupp.mapDomain (fun v : Σ _ : ℕ, G ↦ (⟨v.1, v.2 * g⟩ : Σ _ : ℕ, G)) p.val :=
  val_relabel (· * g) p

instance instMulActionOp : MulAction Gᵐᵒᵖ (MilnorTotalSpace G) where
  one_smul p := by
    have hid : (· * (1 : G)) = _root_.id := funext mul_one
    rw [smul_def, unop_one, hid, relabel_id]
  mul_smul g h p := by
    rw [smul_def, smul_def, smul_def, relabel_comp, unop_mul]
    congr 1; funext a; exact (mul_assoc a h.unop g.unop).symm

@[simp] theorem weight_smul (g : Gᵐᵒᵖ) (i : ℕ) (p : MilnorTotalSpace G) :
    weight i (g • p) = weight i p := weight_relabel (· * g.unop) i p
theorem smul_mem_coordSet_iff (g : Gᵐᵒᵖ) {i : ℕ} {p : MilnorTotalSpace G} :
    g • p ∈ coordSet G i ↔ p ∈ coordSet G i := by simp [mem_coordSet_iff]
@[simp] theorem label_op_smul (g : G) {i : ℕ} {p : MilnorTotalSpace G} (hp : p ∈ coordSet G i) :
    label i (op g • p) = label i p * g := label_relabel (· * g) hp
@[simp] theorem op_smul_vertex (g : G) (i : ℕ) (a : G) : op g • vertex i a = vertex i (a * g) :=
  ext_val (by rw [val_op_smul, val_vertex, val_vertex, Finsupp.mapDomain_single])
@[simp] theorem op_smul_basepoint (g : G) : op g • basepoint G = vertex 0 g := by
  rw [basepoint, op_smul_vertex, one_mul]

/-- **Joint continuity of the right action on `MilnorTotalSpace G`** from `ContinuousMul G`. -/
instance instContinuousSMul [TopologicalSpace G] [ContinuousMul G] :
    ContinuousSMul Gᵐᵒᵖ (MilnorTotalSpace G) where
  continuous_smul := continuous_iff.mpr
    ⟨fun i ↦ by simp_rw [weight_smul]; exact (continuous_weight i).comp continuous_snd, fun i ↦ by
      have hdom : {x : Gᵐᵒᵖ × MilnorTotalSpace G | 0 < weight i (x.1 • x.2)} =
          univ ×ˢ coordSet G i := by ext ⟨g, p⟩; simp [mem_coordSet_iff]
      rw [hdom]
      exact (((continuousOn_label i).comp continuous_snd.continuousOn
        fun _ (hx : _ ∈ univ ×ˢ coordSet G i) ↦ hx.2).mul
        (continuous_unop.comp continuous_fst).continuousOn).congr
        fun ⟨g, _⟩ ⟨_, hp⟩ ↦ label_op_smul g.unop hp⟩

end Monoid

section Group

variable [Group G]

instance instIsCancelSMulOp : IsCancelSMul Gᵐᵒᵖ (MilnorTotalSpace G) :=
  (isCancelSMul_iff_eq_one_of_smul_eq (α := Gᵐᵒᵖ) (β := MilnorTotalSpace G)).mpr fun g p hgp ↦ by
    obtain ⟨i, hi⟩ := exists_weight_pos p
    have hl : label i (op g.unop • p) = label i p := by rw [op_unop, hgp]
    rw [label_op_smul g.unop hi, mul_eq_left] at hl; exact unop_injective hl

private def invRealizationHomeomorph (G : Type u) [Group G] :
    universalGSpace G ≃ₜ universalGSpace G :=
  letI : DecidableEq ℕ := Classical.decEq ℕ
  letI : DecidableEq G := Classical.decEq G
  let f := indexedJoinMap (A := fun _ : ℕ ↦ G) (B := fun _ : ℕ ↦ G)
    _root_.id Function.injective_id (fun _ a ↦ a⁻¹)
  have hff : f.comp f =
      PreAbstractSimplicialComplex.SimplicialMap.id
        (indexedJoin fun _ : ℕ ↦ G).toPreAbstractSimplicialComplex := by
    rw [← indexedJoinMap_comp]
    simp only [Function.comp_id, inv_inv]
    exact indexedJoinMap_id
  f.realizationHomeomorph f hff hff

/-- Equivalence `universalGSpace G ≃ MilnorTotalSpace G` inverting every vertex label. -/
def invEquiv (G : Type u) [Group G] : universalGSpace G ≃ MilnorTotalSpace G :=
  (invRealizationHomeomorph G).toEquiv.trans (equivRealization G).symm

theorem val_invEquiv (x : universalGSpace G) :
    (invEquiv G x).val =
      Finsupp.mapDomain (fun v : Σ _ : ℕ, G ↦ (⟨v.1, v.2⁻¹⟩ : Σ _ : ℕ, G)) x.val := by
  let : DecidableEq ℕ := Classical.decEq ℕ
  let : DecidableEq G := Classical.decEq G
  rw [invEquiv, Equiv.trans_apply, Homeomorph.coe_toEquiv, equivRealization_symm_apply,
    val_ofRealization, invRealizationHomeomorph,
    PreAbstractSimplicialComplex.SimplicialMap.realizationHomeomorph_apply]
  exact (PreAbstractSimplicialComplex.SimplicialMap.realizationMap_val
    (indexedJoinMap (A := fun _ : ℕ ↦ G) (B := fun _ : ℕ ↦ G)
      _root_.id Function.injective_id (fun _ a ↦ a⁻¹)) x).trans
    (congrArg (Finsupp.mapDomain · x.val) (funext (indexedJoinMap_apply
      (A := fun _ : ℕ ↦ G) (B := fun _ : ℕ ↦ G)
      _root_.id Function.injective_id (fun _ a ↦ a⁻¹))))

@[simp] theorem invEquiv_basepoint : invEquiv G (universalGSpaceBasepoint G) = basepoint G :=
  ext_val (by
    rw [val_invEquiv, universalGSpaceBasepoint_val, val_basepoint, Finsupp.mapDomain_single,
      inv_one])

/-- Label inversion carries left multiplication by `g` to right multiplication by `g⁻¹`. -/
@[simp] theorem invEquiv_smul (g : G) (x : universalGSpace G) :
    invEquiv G (g • x) = op g⁻¹ • invEquiv G x := by
  apply ext_val
  rw [val_invEquiv, universalGSpace_smul_val, val_op_smul, val_invEquiv,
    ← Finsupp.mapDomain_comp, ← Finsupp.mapDomain_comp]
  congr 1; funext ⟨_, a⟩; simp [mul_inv_rev]

end Group

end RightAction

end MilnorTotalSpace

/-- Continuous equivariant comparison from `universalGSpace G` to `MilnorTotalSpace G`. -/
def weakToMilnorTotalSpace (G : Type u) [Group G] [TopologicalSpace G] :
    C(universalGSpace G, MilnorTotalSpace G) :=
  ContinuousMap.comp
    ⟨MilnorTotalSpace.ofRealization, MilnorTotalSpace.continuous_ofRealization⟩
    (MilnorTotalSpace.invRealizationHomeomorph G : C(universalGSpace G, universalGSpace G))

@[simp] theorem coe_weakToMilnorTotalSpace (G : Type u) [Group G] [TopologicalSpace G] :
    (weakToMilnorTotalSpace G : universalGSpace G → MilnorTotalSpace G) =
      MilnorTotalSpace.invEquiv G := (rfl)
@[simp] theorem weakToMilnorTotalSpace_basepoint (G : Type u) [Group G] [TopologicalSpace G] :
    weakToMilnorTotalSpace G (universalGSpaceBasepoint G) = MilnorTotalSpace.basepoint G :=
  MilnorTotalSpace.invEquiv_basepoint
@[simp] theorem weakToMilnorTotalSpace_smul {G : Type u} [Group G] [TopologicalSpace G]
    (g : G) (x : universalGSpace G) :
    weakToMilnorTotalSpace G (g • x) = op g⁻¹ • weakToMilnorTotalSpace G x :=
  MilnorTotalSpace.invEquiv_smul g x

end TauCeti

namespace Continuous

open TauCeti

/-- For a continuous map `f : Z → MilnorTotalSpace G`, `MilnorTotalSpace.label i ∘ f` is
continuous at every point where `0 < MilnorTotalSpace.weight i (f z)`. -/
theorem continuousAt_milnorTotalSpace_label_comp {G : Type u} [TopologicalSpace G]
    {Z : Type*} [TopologicalSpace Z] {f : Z → MilnorTotalSpace G} (hf : Continuous f)
    {i : ℕ} {z : Z} (hz : 0 < MilnorTotalSpace.weight i (f z)) :
    ContinuousAt (fun x ↦ MilnorTotalSpace.label i (f x)) z :=
  ((MilnorTotalSpace.continuous_iff.mp hf).2 i).continuousAt
    ((isOpen_lt continuous_const ((MilnorTotalSpace.continuous_iff.mp hf).1 i)).mem_nhds hz)

end Continuous

namespace MonoidHom

open TauCeti

variable {G : Type u} {H : Type v} [Monoid G] [Monoid H] [TopologicalSpace G] [TopologicalSpace H]

/-- A continuous monoid homomorphism induces a continuous equivariant map on Milnor total spaces. -/
def milnorTotalSpaceMap (φ : G →* H) (hφ : Continuous φ) :
    C(MilnorTotalSpace G, MilnorTotalSpace H) :=
  MilnorTotalSpace.map ⟨φ, hφ⟩

@[simp] theorem weight_milnorTotalSpaceMap (φ : G →* H) (hφ : Continuous φ) (i : ℕ)
    (p : MilnorTotalSpace G) :
    MilnorTotalSpace.weight i (φ.milnorTotalSpaceMap hφ p) = MilnorTotalSpace.weight i p :=
  MilnorTotalSpace.weight_map ⟨φ, hφ⟩ i p
@[simp] theorem label_milnorTotalSpaceMap (φ : G →* H) (hφ : Continuous φ) {i : ℕ}
    {p : MilnorTotalSpace G} (hp : p ∈ MilnorTotalSpace.coordSet G i) :
    MilnorTotalSpace.label i (φ.milnorTotalSpaceMap hφ p) = φ (MilnorTotalSpace.label i p) :=
  MilnorTotalSpace.label_map ⟨φ, hφ⟩ hp
@[simp] theorem milnorTotalSpaceMap_basepoint (φ : G →* H) (hφ : Continuous φ) :
    φ.milnorTotalSpaceMap hφ (MilnorTotalSpace.basepoint G) = MilnorTotalSpace.basepoint H := by
  simp [milnorTotalSpaceMap, MilnorTotalSpace.basepoint]
@[simp] theorem milnorTotalSpaceMap_op_smul (φ : G →* H) (hφ : Continuous φ) (g : G)
    (p : MilnorTotalSpace G) :
    φ.milnorTotalSpaceMap hφ (MulOpposite.op g • p) =
      MulOpposite.op (φ g) • φ.milnorTotalSpaceMap hφ p := by
  apply MilnorTotalSpace.ext_val
  simp only [milnorTotalSpaceMap, MilnorTotalSpace.val_map, MilnorTotalSpace.val_op_smul,
    ← Finsupp.mapDomain_comp]
  congr 1; funext ⟨_, _⟩; simp
@[simp] theorem milnorTotalSpaceMap_id :
    (MonoidHom.id G).milnorTotalSpaceMap continuous_id = ContinuousMap.id (MilnorTotalSpace G) :=
  MilnorTotalSpace.map_id G
@[simp] theorem milnorTotalSpaceMap_comp {K : Type w} [Monoid K] [TopologicalSpace K]
    (ψ : H →* K) (hψ : Continuous ψ) (φ : G →* H) (hφ : Continuous φ) :
    (ψ.comp φ).milnorTotalSpaceMap (hψ.comp hφ) =
      (ψ.milnorTotalSpaceMap hψ).comp (φ.milnorTotalSpaceMap hφ) :=
  MilnorTotalSpace.map_comp ⟨ψ, hψ⟩ ⟨φ, hφ⟩

end MonoidHom
