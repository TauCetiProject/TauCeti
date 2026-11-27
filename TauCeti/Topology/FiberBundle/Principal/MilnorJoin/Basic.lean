/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.ClassifyingSpace.Action
public import Mathlib.Topology.Algebra.InfiniteSum.Basic
public import Mathlib.Topology.Homotopy.Path
import Mathlib.Topology.Algebra.InfiniteSum.Order
import TauCeti.Topology.Algebra.InfiniteSum.Real

/-!
# The strong-coordinate Milnor join of a topological space or group

Following Milnor (*Construction of universal bundles, II*, §2) and tom Dieck (*Algebraic Topology*,
§14.4.3), `TauCeti.MilnorTotalSpace G` is a distinct type copy of `universalGSpace G` carrying the
*strong coordinate topology*: the coarsest topology making every weight `t_i : EG → ℝ` continuous
and every vertex label `g_i : U_i → G` continuous on `U_i = {p | 0 < t_i p}`, avoiding diamonds
with the weak simplicial topology and left group action on `universalGSpace G`.

## Main definitions and results

* `TauCeti.MilnorTotalSpace`, `weight`, `coordSet`, `label`, `ofFinsetCoord`, `map`,
  `continuous_iff`, `coneAtFreshIndexHomotopy`, `weight_coneAtFreshIndexHomotopy`,
  `label_coneAtFreshIndexHomotopy_self`, `label_coneAtFreshIndexHomotopy_of_ne`,
  `instPathConnectedSpaceMilnorTotalSpace`, `instT2Space`: strong-topology join,
  coordinates `(t_i, g_i)`, finite-support coordinate constructor, universal continuity criterion,
  fresh-index cone homotopy, path-connectedness, and Hausdorffness.
* `TauCeti.MilnorTotalSpace.instContinuousSMul`, `instIsCancelSMulOp`,
  `TauCeti.weakToMilnorTotalSpace`, `MilnorTotalSpace.map_basepoint`,
  `MilnorTotalSpace.map_op_smul`,
  `ContinuousMonoidHom.milnorTotalSpaceMap_comp_weakToMilnorTotalSpace`: joint continuity and
  freeness of the right `Gᵐᵒᵖ`-action, label-inversion dictionary
  (`g⁻¹ • x ↦ weakToMilnorTotalSpace G x · g`), and homomorphism naturality.

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

theorem exists_weight_pos (p : MilnorTotalSpace G) : ∃ i, 0 < weight i p :=
  (hasSum_weight p).exists_pos (fun i ↦ weight_nonneg i p) zero_lt_one

@[simp] theorem iUnion_coordSet (G : Type u) : ⋃ i, coordSet G i = univ :=
  eq_univ_of_forall fun p ↦ mem_iUnion.mpr (exists_weight_pos p)

/-- The `i`-th vertex label `g_i(p)` of `p : MilnorTotalSpace G`; uniquely determined when
`0 < weight i p`, and an arbitrary choice when `weight i p = 0`. -/
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

private def relabelSimplicialMap {X : Type u} {Y : Type v} (f : X → Y) :=
  indexedJoinMap (A := fun _ : ℕ ↦ X) (B := fun _ : ℕ ↦ Y)
    _root_.id Function.injective_id (fun _ ↦ f)

/-- Vertex relabelling `MilnorTotalSpace X → MilnorTotalSpace Y` induced by `f : X → Y`. -/
def relabel {X : Type u} {Y : Type v} (f : X → Y) (p : MilnorTotalSpace X) : MilnorTotalSpace Y :=
  letI := Classical.decEq ℕ; letI := Classical.decEq X; letI := Classical.decEq Y
  ofRealization ((relabelSimplicialMap f).realizationMap p.toRealization)

theorem val_relabel {X : Type u} {Y : Type v} (f : X → Y) (p : MilnorTotalSpace X) :
    (relabel f p).val =
      Finsupp.mapDomain (fun v : Σ _ : ℕ, X ↦ (⟨v.1, f v.2⟩ : Σ _ : ℕ, Y)) p.val := by
  let _ := Classical.decEq ℕ; let _ := Classical.decEq X; let _ := Classical.decEq Y
  refine (PreAbstractSimplicialComplex.SimplicialMap.realizationMap_val
    (relabelSimplicialMap f) p.toRealization).trans ?_
  unfold relabelSimplicialMap
  exact congrArg (Finsupp.mapDomain · p.val) (funext (indexedJoinMap_apply
    (A := fun _ : ℕ ↦ X) (B := fun _ : ℕ ↦ Y) _root_.id Function.injective_id (fun _ ↦ f)))

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

private def labelEmbedding (ℓ : ℕ → G) : ℕ ↪ Σ _ : ℕ, G :=
  ⟨fun i ↦ ⟨i, ℓ i⟩, fun _ _ h ↦ (Sigma.ext_iff.mp h).1⟩

private theorem labelEmbedding_apply (ℓ : ℕ → G) (i : ℕ) :
    labelEmbedding ℓ i = ⟨i, ℓ i⟩ := rfl

private theorem fst_comp_labelEmbedding (ℓ : ℕ → G) :
    Sigma.fst ∘ labelEmbedding ℓ = _root_.id := rfl

private def ofFinsetCoordVal (S : Finset ℕ) (w : ℕ → ℝ) (ℓ : ℕ → G) : (Σ _ : ℕ, G) →₀ ℝ :=
  (Finsupp.indicator S fun i _ ↦ w i).embDomain (labelEmbedding ℓ)

private theorem ofFinsetCoordVal_apply_self (S : Finset ℕ) (w : ℕ → ℝ) (ℓ : ℕ → G) (i : ℕ) :
    ofFinsetCoordVal S w ℓ ⟨i, ℓ i⟩ = if i ∈ S then w i else 0 := by
  simp [ofFinsetCoordVal, ← labelEmbedding_apply ℓ i, Finsupp.indicator_apply]

/-- Construct a point of `MilnorTotalSpace G` from a finite index set `S : Finset ℕ`, nonnegative
weights `w` summing to `1` over `S`, and vertex labels `ℓ`. -/
def ofFinsetCoord (S : Finset ℕ) (w : ℕ → ℝ) (ℓ : ℕ → G)
    (hw_nonneg : ∀ i ∈ S, 0 ≤ w i) (hw_sum : ∑ i ∈ S, w i = 1) : MilnorTotalSpace G :=
  ofRealization ⟨ofFinsetCoordVal S w ℓ, mem_indexedJoin_realization_iff.mpr <| by
    classical
    refine ⟨?_, ?_, ?_⟩
    · intro v
      rw [ofFinsetCoordVal, Finsupp.embDomain_apply]
      split_ifs with h
      · rw [Finsupp.indicator_apply]
        split_ifs with hs
        · exact hw_nonneg _ hs
        · exact le_rfl
      · exact le_rfl
    · rw [ofFinsetCoordVal, Finsupp.sum_embDomain,
        Finsupp.sum_indicator_index (h_zero := fun _ _ ↦ rfl)]
      exact hw_sum
    · intro v₁ v₂ hv₁ hv₂ h12
      rw [← Finsupp.mem_support_iff, ofFinsetCoordVal, Finsupp.support_embDomain,
        Finset.mem_map] at hv₁ hv₂
      obtain ⟨j₁, _, rfl⟩ := hv₁
      obtain ⟨j₂, _, rfl⟩ := hv₂
      obtain rfl : j₁ = j₂ := h12
      rfl⟩

/-- The `i`-th barycentric weight of `ofFinsetCoord S w ℓ` is `w i` when `i ∈ S` and `0`
otherwise. -/
@[simp] theorem weight_ofFinsetCoord (S : Finset ℕ) (w : ℕ → ℝ) (ℓ : ℕ → G)
    (hw_nonneg : ∀ i ∈ S, 0 ≤ w i) (hw_sum : ∑ i ∈ S, w i = 1) (i : ℕ) :
    weight i (ofFinsetCoord S w ℓ hw_nonneg hw_sum) = if i ∈ S then w i else 0 := by
  classical
  have hval : (ofFinsetCoord S w ℓ hw_nonneg hw_sum).val =
      (Finsupp.indicator S fun i _ ↦ w i).embDomain (labelEmbedding ℓ) :=
    val_ofRealization _
  simp only [weight_def, hval, Finsupp.embDomain_eq_mapDomain, ← Finsupp.mapDomain_comp,
    fst_comp_labelEmbedding, Finsupp.mapDomain_id, Finsupp.indicator_apply, dite_eq_ite]

/-- When `i ∈ S` and `0 < w i`, the `i`-th label of `ofFinsetCoord S w ℓ` is `ℓ i`. -/
@[simp] theorem label_ofFinsetCoord (S : Finset ℕ) (w : ℕ → ℝ) (ℓ : ℕ → G)
    (hw_nonneg : ∀ i ∈ S, 0 ≤ w i) (hw_sum : ∑ i ∈ S, w i = 1) {i : ℕ}
    (hi : i ∈ S) (hwi : 0 < w i) :
    label i (ofFinsetCoord S w ℓ hw_nonneg hw_sum) = ℓ i := by
  refine (eq_label_of_val_pos (p := ofFinsetCoord S w ℓ hw_nonneg hw_sum) ?_).symm
  rw [ofFinsetCoord, val_ofRealization, ofFinsetCoordVal_apply_self]
  simpa [hi] using hwi

/-- Any index outside the finite weight support of `p` has weight `0`. -/
theorem weight_eq_zero_of_notMem {p : MilnorTotalSpace G} {i : ℕ}
    (hi : i ∉ (finite_support_weight p).toFinset) : weight i p = 0 :=
  not_not.mp fun hne ↦ hi ((finite_support_weight p).mem_toFinset.mpr hne)

/-- Every point of `MilnorTotalSpace G` has all barycentric weights `0` from some index
onwards. -/
theorem exists_forall_le_weight_eq_zero (p : MilnorTotalSpace G) :
    ∃ N : ℕ, ∀ i, N ≤ i → weight i p = 0 := by
  classical
  refine ⟨(finite_support_weight p).toFinset.sup _root_.id + 1, fun i hi ↦
    weight_eq_zero_of_notMem fun hm ↦ ?_⟩
  exact Nat.not_succ_le_self _
    (hi.trans ((finite_support_weight p).toFinset.le_sup (f := _root_.id) hm))

/-- The barycentric weights of `p` sum to `1` over any finite set `S` outside which all weights
vanish. -/
theorem sum_weight_of_support_subset {p : MilnorTotalSpace G} {S : Finset ℕ}
    (hS : ∀ i, i ∉ S → weight i p = 0) : ∑ i ∈ S, weight i p = 1 :=
  (tsum_eq_sum hS).symm.trans (tsum_weight p)

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

/-- Each coordinate weight `weight i : MilnorTotalSpace G → ℝ` is continuous in the strong
coordinate topology. -/
@[fun_prop, continuity]
theorem continuous_weight (i : ℕ) : Continuous (weight i : MilnorTotalSpace G → ℝ) :=
  (continuous_iff.mp continuous_id).1 i

theorem isOpen_coordSet (i : ℕ) : IsOpen (coordSet G i) :=
  isOpen_lt continuous_const (continuous_weight i)

/-- The `i`-th vertex label `label i` is continuous on the positive-weight domain
`coordSet G i = {p | 0 < weight i p}`. -/
theorem continuousOn_label (i : ℕ) :
    ContinuousOn (label i : MilnorTotalSpace G → G) (coordSet G i) :=
  (continuous_iff.mp continuous_id).2 i

/-- Vertex inclusion `vertex i : G → MilnorTotalSpace G` into the `i`-th coordinate copy is
continuous. -/
@[fun_prop, continuity]
theorem continuous_vertex (i : ℕ) : Continuous (vertex i : G → MilnorTotalSpace G) := by
  rw [continuous_iff]
  refine ⟨fun j ↦ by simp only [weight_vertex]; exact continuous_const, fun j ↦ ?_⟩
  by_cases hij : j = i
  · subst hij; simp only [weight_vertex, ↓reduceIte, zero_lt_one, Set.ofPred_true, label_vertex]
    exact continuousOn_id
  · simp only [weight_vertex, hij, ↓reduceIte, lt_self_iff_false, Set.ofPred_false]
    exact continuousOn_empty _

section Cone

open unitInterval

variable {X : Type v} [TopologicalSpace X]

private def coneWeight (N : ℕ) (g : C(X, MilnorTotalSpace G)) (z : I × X) (i : ℕ) : ℝ :=
  if i = N then (z.1 : ℝ) else (1 - (z.1 : ℝ)) * weight i (g z.2)

private theorem weight_pos_of_coneWeight_pos {N : ℕ} {g : C(X, MilnorTotalSpace G)}
    {z : I × X} {i : ℕ} (hiN : i ≠ N) (hz : 0 < coneWeight N g z i) : 0 < weight i (g z.2) := by
  by_contra hle; simp [coneWeight, hiN, le_antisymm (not_lt.mp hle) (weight_nonneg i (g z.2))] at hz

private def conePt (N : ℕ) (a : G) (g : C(X, MilnorTotalSpace G))
    (hg : ∀ x, weight N (g x) = 0) (z : I × X) : MilnorTotalSpace G :=
  let S := (finite_support_weight (g z.2)).toFinset
  have hN : N ∉ S := fun hm ↦ (finite_support_weight (g z.2)).mem_toFinset.mp hm (hg z.2)
  ofFinsetCoord (insert N S) (coneWeight N g z) (fun i ↦ if i = N then a else label i (g z.2))
    (fun i _ ↦ by
      unfold coneWeight; split_ifs
      exacts [z.1.property.1, mul_nonneg (sub_nonneg.mpr z.1.property.2) (weight_nonneg i (g z.2))])
    (by
      rw [Finset.sum_insert hN]
      have hS : ∑ i ∈ S, coneWeight N g z i = 1 - (z.1 : ℝ) := by
        calc ∑ i ∈ S, coneWeight N g z i
            = ∑ i ∈ S, (1 - (z.1 : ℝ)) * weight i (g z.2) :=
              Finset.sum_congr rfl fun _ hi ↦ by simp [coneWeight, ne_of_mem_of_not_mem hi hN]
          _ = (1 - (z.1 : ℝ)) * ∑ i ∈ S, weight i (g z.2) := by rw [← Finset.mul_sum]
          _ = 1 - (z.1 : ℝ) := by
              rw [sum_weight_of_support_subset fun _ ↦ weight_eq_zero_of_notMem, mul_one]
      rw [hS]
      simp [coneWeight])

private theorem weight_conePt (N : ℕ) (a : G) (g : C(X, MilnorTotalSpace G))
    (hg : ∀ x, weight N (g x) = 0) (z : I × X) (i : ℕ) :
    weight i (conePt N a g hg z) = coneWeight N g z i := by
  unfold conePt; rw [weight_ofFinsetCoord]
  by_cases hiN : i = N
  · simp [hiN]
  · simp only [Finset.mem_insert, hiN, false_or]
    split_ifs with hi
    · rfl
    · simp [coneWeight, hiN, weight_eq_zero_of_notMem hi]

private theorem label_conePt_self (N : ℕ) (a : G) (g : C(X, MilnorTotalSpace G))
    (hg : ∀ x, weight N (g x) = 0) {z : I × X} (hs : 0 < (z.1 : ℝ)) :
    label N (conePt N a g hg z) = a := by
  unfold conePt
  rw [label_ofFinsetCoord _ _ _ _ _ (Finset.mem_insert_self N _) (by simp [coneWeight, hs])]
  exact ite_eq_left rfl

private theorem label_conePt_of_ne (N : ℕ) (a : G) (g : C(X, MilnorTotalSpace G))
    (hg : ∀ x, weight N (g x) = 0) {z : I × X} {i : ℕ} (hiN : i ≠ N)
    (hz : 0 < coneWeight N g z i) : label i (conePt N a g hg z) = label i (g z.2) := by
  unfold conePt
  rw [label_ofFinsetCoord _ _ _ _ _ (Finset.mem_insert_of_mem
    ((finite_support_weight (g z.2)).mem_toFinset.mpr
      (weight_pos_of_coneWeight_pos hiN hz).ne')) hz]
  exact ite_eq_right hiN

/-- **Cone homotopy at an unused index** to the constant map at `vertex N a`. -/
def coneAtFreshIndexHomotopy (N : ℕ) (a : G) (g : C(X, MilnorTotalSpace G))
    (hg : ∀ x, weight N (g x) = 0) : g.Homotopy (ContinuousMap.const X (vertex N a)) where
  toFun := conePt N a g hg
  continuous_toFun := continuous_iff.mpr ⟨fun i ↦ by
      simp_rw [weight_conePt]; unfold coneWeight
      by_cases hiN : i = N <;> simp only [hiN, ↓reduceIte]
      exacts [continuous_subtypeVal.comp continuous_fst, by fun_prop], fun i ↦ by
      simp_rw [weight_conePt]
      by_cases hiN : i = N
      · subst hiN; exact (continuousOn_const (c := a)).congr fun _ hz ↦
          label_conePt_self i a g hg (by simpa [coneWeight] using hz)
      · exact ((continuousOn_label i).comp (g.continuous.comp continuous_snd).continuousOn
          fun _ hz ↦ mem_coordSet_iff.mpr (weight_pos_of_coneWeight_pos hiN hz)).congr fun _ hz ↦
          label_conePt_of_ne N a g hg hiN hz⟩
  map_zero_left x := by
    rw [ContinuousMap.coe_mk]
    refine (ext_coord
      (fun i ↦ by
        rw [weight_conePt]; by_cases hiN : i = N
        · subst hiN; simp [coneWeight, hg x]
        · simp [coneWeight, hiN])
      (fun i hi ↦ by
        have hiN : i ≠ N := fun h ↦ (mem_coordSet_iff.mp hi).ne' (h ▸ hg x)
        exact (label_conePt_of_ne N a g hg hiN (z := (0, x))
          (by simpa [coneWeight, hiN] using mem_coordSet_iff.mp hi)).symm)).symm
  map_one_left x := by
    rw [ContinuousMap.coe_mk, ContinuousMap.toFun_eq_coe, ContinuousMap.const_apply]
    refine ext_coord
      (fun i ↦ by
        rw [weight_conePt, weight_vertex]; by_cases hiN : i = N <;> simp [coneWeight, hiN])
      (fun i hi ↦ by
        have hi' : 0 < coneWeight N g (1, x) i :=
          weight_conePt N a g hg (1, x) i ▸ mem_coordSet_iff.mp hi
        by_cases hiN : i = N
        · subst hiN; exact (label_conePt_self i a g hg zero_lt_one).trans (label_vertex i a).symm
        · simp [coneWeight, hiN] at hi')

/-- The `i`-th barycentric weight along `coneAtFreshIndexHomotopy N a g hg` at `(s, x)`. -/
@[simp] theorem weight_coneAtFreshIndexHomotopy (N : ℕ) (a : G)
    (g : C(X, MilnorTotalSpace G)) (hg : ∀ x, weight N (g x) = 0) (s : I) (x : X) (i : ℕ) :
    weight i (coneAtFreshIndexHomotopy N a g hg (s, x)) =
      if i = N then (s : ℝ) else (1 - (s : ℝ)) * weight i (g x) :=
  weight_conePt N a g hg (s, x) i

/-- When `0 < (s : ℝ)`, the label at the fresh index `N` along `coneAtFreshIndexHomotopy` is
`a`. -/
@[simp] theorem label_coneAtFreshIndexHomotopy_self (N : ℕ) (a : G)
    (g : C(X, MilnorTotalSpace G)) (hg : ∀ x, weight N (g x) = 0) {s : I} (hs : 0 < (s : ℝ))
    (x : X) :
    label N (coneAtFreshIndexHomotopy N a g hg (s, x)) = a :=
  label_conePt_self N a g hg (z := (s, x)) hs

/-- For `i ≠ N`, every positive-weight coordinate along `coneAtFreshIndexHomotopy N a g hg`
retains the original vertex label `label i (g x)`. -/
@[simp] theorem label_coneAtFreshIndexHomotopy_of_ne (N : ℕ) (a : G)
    (g : C(X, MilnorTotalSpace G)) (hg : ∀ x, weight N (g x) = 0) {s : I} {x : X} {i : ℕ}
    (hiN : i ≠ N) (h : coneAtFreshIndexHomotopy N a g hg (s, x) ∈ coordSet G i) :
    label i (coneAtFreshIndexHomotopy N a g hg (s, x)) = label i (g x) :=
  label_conePt_of_ne N a g hg hiN
    (weight_conePt N a g hg (s, x) i ▸ mem_coordSet_iff.mp h)

end Cone

/-- `MilnorTotalSpace G` is path-connected whenever `G` is nonempty: any two points join to a
vertex at an index beyond both of their finite supports. -/
instance instPathConnectedSpaceMilnorTotalSpace [Nonempty G] :
    PathConnectedSpace (MilnorTotalSpace G) where
  nonempty := inferInstance
  joined p q := by
    obtain ⟨a⟩ := ‹Nonempty G›
    obtain ⟨N₁, hN₁⟩ := exists_forall_le_weight_eq_zero p
    obtain ⟨N₂, hN₂⟩ := exists_forall_le_weight_eq_zero q
    let N := max N₁ N₂
    have hp : weight N p = 0 := hN₁ N (le_max_left N₁ N₂)
    have hq : weight N q = 0 := hN₂ N (le_max_right N₁ N₂)
    exact ⟨((coneAtFreshIndexHomotopy N a (ContinuousMap.const Unit p) fun _ ↦ hp).evalAt ()).trans
      ((coneAtFreshIndexHomotopy N a (ContinuousMap.const Unit q) fun _ ↦ hq).evalAt ()).symm⟩


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

/-- Right scalar multiplication by `Gᵐᵒᵖ` on `MilnorTotalSpace G` multiplies every vertex label
on the right: `(op g • p)` relabels `a ↦ a * g`. -/
instance instSMulOp : SMul Gᵐᵒᵖ (MilnorTotalSpace G) := ⟨fun g p ↦ relabel (· * g.unop) p⟩

private theorem smul_def (g : Gᵐᵒᵖ) (p : MilnorTotalSpace G) :
    g • p = relabel (· * g.unop) p := rfl

theorem val_op_smul (g : G) (p : MilnorTotalSpace G) :
    (op g • p).val =
      Finsupp.mapDomain (fun v : Σ _ : ℕ, G ↦ (⟨v.1, v.2 * g⟩ : Σ _ : ℕ, G)) p.val :=
  val_relabel (· * g) p

/-- Right multiplication on vertex labels defines a `MulAction` of the opposite monoid `Gᵐᵒᵖ` on
`MilnorTotalSpace G`. -/
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

/-- The right `Gᵐᵒᵖ`-action on `MilnorTotalSpace G` is free (`IsCancelSMul`): any point has a
positive-weight coordinate whose vertex label determines the acting group element uniquely. -/
instance instIsCancelSMulOp : IsCancelSMul Gᵐᵒᵖ (MilnorTotalSpace G) :=
  (isCancelSMul_iff_eq_one_of_smul_eq (α := Gᵐᵒᵖ) (β := MilnorTotalSpace G)).mpr fun g p hgp ↦ by
    obtain ⟨i, hi⟩ := exists_weight_pos p
    have hl : label i (op g.unop • p) = label i p := by rw [op_unop, hgp]
    rw [label_op_smul g.unop hi, mul_eq_left] at hl; exact unop_injective hl

private def invRealizationHomeomorph (G : Type u) [Group G] :
    universalGSpace G ≃ₜ universalGSpace G :=
  letI : DecidableEq ℕ := Classical.decEq ℕ
  letI : DecidableEq G := Classical.decEq G
  have hff : (relabelSimplicialMap (Inv.inv : G → G)).comp
        (relabelSimplicialMap (Inv.inv : G → G)) =
      PreAbstractSimplicialComplex.SimplicialMap.id
        (indexedJoin fun _ : ℕ ↦ G).toPreAbstractSimplicialComplex := by
    unfold relabelSimplicialMap
    rw [← indexedJoinMap_comp]
    simp only [Function.comp_id, inv_inv]
    exact indexedJoinMap_id
  (relabelSimplicialMap (Inv.inv : G → G)).realizationHomeomorph
    (relabelSimplicialMap (Inv.inv : G → G)) hff hff

private theorem ofRealization_invRealizationHomeomorph (x : universalGSpace G) :
    ofRealization (invRealizationHomeomorph G x) = relabel Inv.inv (ofRealization x) := by
  let _ := Classical.decEq ℕ; let _ := Classical.decEq G
  exact congrArg ofRealization
    (PreAbstractSimplicialComplex.SimplicialMap.realizationHomeomorph_apply _ _ _ _ x)

end Group

end RightAction

section Homomorphism

variable {G : Type u} {H : Type v} [Monoid G] [Monoid H] [TopologicalSpace G] [TopologicalSpace H]

/-- A continuous monoid homomorphism preserves the base point of `MilnorTotalSpace`. -/
@[simp] theorem map_basepoint (φ : G →ₜ* H) :
    map (φ : C(G, H)) (basepoint G) = basepoint H := by
  simp [basepoint]

/-- A continuous monoid homomorphism is equivariant with respect to the right `G`-action on
`MilnorTotalSpace`. -/
@[simp] theorem map_op_smul (φ : G →ₜ* H) (g : G) (p : MilnorTotalSpace G) :
    map (φ : C(G, H)) (op g • p) = op (φ g) • map (φ : C(G, H)) p := by
  apply ext_val
  simp only [val_map, val_op_smul, ← Finsupp.mapDomain_comp]
  congr 1; funext ⟨_, _⟩; simp

end Homomorphism

end MilnorTotalSpace

/-- Continuous equivariant comparison from `universalGSpace G` to `MilnorTotalSpace G`. -/
def weakToMilnorTotalSpace (G : Type u) [Group G] [TopologicalSpace G] :
    C(universalGSpace G, MilnorTotalSpace G) :=
  ContinuousMap.comp
    ⟨MilnorTotalSpace.ofRealization, MilnorTotalSpace.continuous_ofRealization⟩
    (MilnorTotalSpace.invRealizationHomeomorph G : C(universalGSpace G, universalGSpace G))

/-- Pointwise formula for the comparison map `weakToMilnorTotalSpace G`. -/
theorem weakToMilnorTotalSpace_apply (G : Type u) [Group G] [TopologicalSpace G]
    (x : universalGSpace G) :
    weakToMilnorTotalSpace G x =
      MilnorTotalSpace.relabel Inv.inv (MilnorTotalSpace.ofRealization x) :=
  MilnorTotalSpace.ofRealization_invRealizationHomeomorph x

/-- Coordinate vector of `weakToMilnorTotalSpace G x`, obtained by inverting every vertex
label. -/
theorem val_weakToMilnorTotalSpace (G : Type u) [Group G] [TopologicalSpace G]
    (x : universalGSpace G) :
    (weakToMilnorTotalSpace G x).val =
      Finsupp.mapDomain (fun v : Σ _ : ℕ, G ↦ (⟨v.1, v.2⁻¹⟩ : Σ _ : ℕ, G)) x.val := by
  rw [weakToMilnorTotalSpace_apply]
  exact MilnorTotalSpace.val_relabel Inv.inv (MilnorTotalSpace.ofRealization x)

/-- `weakToMilnorTotalSpace G` preserves the distinguished base point. -/
@[simp] theorem weakToMilnorTotalSpace_basepoint (G : Type u) [Group G] [TopologicalSpace G] :
    weakToMilnorTotalSpace G (universalGSpaceBasepoint G) = MilnorTotalSpace.basepoint G :=
  MilnorTotalSpace.ext_val (by
    rw [val_weakToMilnorTotalSpace, universalGSpaceBasepoint_val, MilnorTotalSpace.val_basepoint,
      Finsupp.mapDomain_single, inv_one])

/-- Label inversion carries left multiplication by `g` to right multiplication by `g⁻¹`. -/
@[simp] theorem weakToMilnorTotalSpace_smul {G : Type u} [Group G] [TopologicalSpace G]
    (g : G) (x : universalGSpace G) :
    weakToMilnorTotalSpace G (g • x) = op g⁻¹ • weakToMilnorTotalSpace G x := by
  apply MilnorTotalSpace.ext_val
  rw [val_weakToMilnorTotalSpace, universalGSpace_smul_val, MilnorTotalSpace.val_op_smul,
    val_weakToMilnorTotalSpace, ← Finsupp.mapDomain_comp, ← Finsupp.mapDomain_comp]
  congr 1; funext ⟨_, a⟩; simp [mul_inv_rev]

end TauCeti

namespace ContinuousMonoidHom

open TauCeti

variable {G : Type u} {H : Type v} [Group G] [Group H] [TopologicalSpace G] [TopologicalSpace H]

/-- **Naturality of `weakToMilnorTotalSpace`** with respect to continuous group homomorphisms. -/
theorem milnorTotalSpaceMap_comp_weakToMilnorTotalSpace (φ : G →ₜ* H) :
    (MilnorTotalSpace.map (φ : C(G, H))).comp (weakToMilnorTotalSpace G) =
      (weakToMilnorTotalSpace H).comp φ.toMonoidHom.universalGSpaceMap := by
  ext1 x
  apply MilnorTotalSpace.ext_val
  simp only [ContinuousMap.comp_apply, val_weakToMilnorTotalSpace,
    MilnorTotalSpace.val_map, MonoidHom.universalGSpaceMap_val, ← Finsupp.mapDomain_comp]
  congr 1
  funext ⟨_, _⟩
  simp

end ContinuousMonoidHom
