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
import Mathlib.Topology.Separation.Hausdorff

/-!
# The strong-coordinate Milnor join of a topological space or group

For a topological group `G`, the weak simplicial topology on `universalGSpace G` ignores the
topology of `G` and treats the vertices as discrete. Following Milnor (*Construction of universal
bundles, II*, §2) and tom Dieck (*Algebraic Topology*, §14.4.3), this file introduces a distinct
type copy `TauCeti.MilnorTotalSpace G` of the countable indexed-join realization equipped with the
*strong coordinate topology*: the coarsest topology making every index weight `t_i : EG → ℝ`
continuous and every vertex-label coordinate `g_i : U_i → G` continuous on the positive-weight open
star `U_i = {p | 0 < t_i p}`. Keeping `MilnorTotalSpace G` as a separate structure prevents
typeclass diamonds with both the weak simplicial topology and the left group action on
`universalGSpace G`.

A map `f : Z → MilnorTotalSpace G` from any topological space (including a product) is continuous
if and only if every `t_i ∘ f` is continuous and every `g_i ∘ f` is continuous on
`{z | 0 < t_i (f z)}` (`TauCeti.MilnorTotalSpace.continuous_iff`). When `G` is Hausdorff, coordinate
and label separation makes `MilnorTotalSpace G` Hausdorff.

When `G` is a monoid, `Gᵐᵒᵖ` acts on the right on `MilnorTotalSpace G` by multiplying every vertex
label on the right, preserving each weight `t_i` and satisfying `g_i(p · g) = g_i(p) * g` on `U_i`.
By the coordinate continuity criterion, continuity of multiplication on `G` alone makes this right
action jointly continuous (`TauCeti.MilnorTotalSpace.instContinuousSMul`), with no metric or local
compactness assumption. When `G` is a group, the action is free, and inverting vertex labels gives a
continuous comparison from the weak-topology model `universalGSpace G` intertwining the left action
of `g⁻¹` with the right action of `g`.

## Main definitions

* `TauCeti.MilnorTotalSpace`: type copy of the countable join `universalGSpace G` carrying the
  strong coordinate topology and the right `G`-action.
* `TauCeti.MilnorTotalSpace.weight`, `TauCeti.MilnorTotalSpace.coordSet`,
  `TauCeti.MilnorTotalSpace.label`: the index weights `t_i`, positive-weight sets `U_i`, and vertex
  labels `g_i`.
* `TauCeti.MilnorTotalSpace.map`: functorial map on strong-topology joins induced by `C(X, Y)`.
* `TauCeti.MilnorTotalSpace.invEquiv`, `TauCeti.weakToMilnorTotalSpace`: label-inversion dictionary
  and continuous comparison from the weak simplicial join `universalGSpace G`.
* `MonoidHom.milnorTotalSpaceMap`: continuous equivariant map induced by a continuous homomorphism.

## Main results

* `TauCeti.MilnorTotalSpace.continuous_iff`: universal coordinate continuity criterion into
  `MilnorTotalSpace G`.
* `TauCeti.MilnorTotalSpace.instT2Space`: `MilnorTotalSpace G` is Hausdorff when `G` is Hausdorff.
* `TauCeti.MilnorTotalSpace.instContinuousSMul`: joint continuity of the right action of `Gᵐᵒᵖ`.
* `TauCeti.MilnorTotalSpace.invEquiv_inv_smul`: label inversion carries left multiplication by
  `g⁻¹` on `universalGSpace G` to right multiplication by `g` on `MilnorTotalSpace G`.

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
`universalGSpace G` so that it carries the strong coordinate topology and the right
label-multiplication action without colliding with the weak simplicial topology or left action on
`universalGSpace G`. -/
@[ext]
structure MilnorTotalSpace (G : Type u) where
  /-- View a point of the simplicial countable join as a point of `MilnorTotalSpace G`. -/
  ofRealization ::
  /-- The underlying point of the simplicial countable join `universalGSpace G`. -/
  toRealization : universalGSpace G

namespace MilnorTotalSpace

section Coordinates

variable {G : Type u}

/-- The carrier equivalence between `MilnorTotalSpace G` and `universalGSpace G`. -/
def equivRealization (G : Type u) : MilnorTotalSpace G ≃ universalGSpace G where
  toFun := toRealization
  invFun := ofRealization
  left_inv _ := rfl
  right_inv _ := rfl

@[simp]
theorem equivRealization_apply (p : MilnorTotalSpace G) :
    equivRealization G p = p.toRealization :=
  (rfl)

@[simp]
theorem equivRealization_symm_apply (x : universalGSpace G) :
    (equivRealization G).symm x = ofRealization x :=
  (rfl)

/-- Underlying finitely supported barycentric coordinate vector on `Σ _ : ℕ, G`. -/
def val (p : MilnorTotalSpace G) : (Σ _ : ℕ, G) →₀ ℝ :=
  p.toRealization.1

@[simp]
theorem val_ofRealization (x : universalGSpace G) : (ofRealization x).val = x.1 :=
  (rfl)

/-- Two points of `MilnorTotalSpace G` agree once their barycentric coordinate vectors agree. -/
theorem ext_val {p q : MilnorTotalSpace G} (h : p.val = q.val) : p = q :=
  MilnorTotalSpace.ext (Subtype.ext h)

/-- Every barycentric coordinate of a point in `MilnorTotalSpace G` is nonnegative. -/
theorem val_nonneg (p : MilnorTotalSpace G) (v : Σ _ : ℕ, G) : 0 ≤ p.val v :=
  Realization.nonneg _ p.toRealization v

/-- The barycentric coordinates of a point in `MilnorTotalSpace G` sum to `1`. -/
theorem sum_val (p : MilnorTotalSpace G) : p.val.sum (fun _ r ↦ r) = 1 :=
  Realization.sum_eq_one _ p.toRealization

/-- At most one vertex over each index has nonzero coordinate in `p`. -/
theorem support_val_injOn_fst (p : MilnorTotalSpace G) :
    InjOn Sigma.fst (p.val.support : Set (Σ _ : ℕ, G)) :=
  realization_support_injOn_fst p.toRealization

/-- The vertex of `MilnorTotalSpace G` concentrated at index `i` with label `a`. -/
def vertex (i : ℕ) (a : G) : MilnorTotalSpace G :=
  ofRealization ((indexedJoin fun _ : ℕ ↦ G).vertex ⟨i, a⟩)

@[simp]
theorem toRealization_vertex (i : ℕ) (a : G) :
    (vertex i a).toRealization = (indexedJoin fun _ : ℕ ↦ G).vertex ⟨i, a⟩ :=
  (rfl)

@[simp]
theorem val_vertex (i : ℕ) (a : G) : (vertex i a).val = Finsupp.single ⟨i, a⟩ 1 := by
  let _ : DecidableEq (Σ _ : ℕ, G) := Classical.decEq _
  exact AbstractSimplicialComplex.vertex_val (indexedJoin fun _ : ℕ ↦ G) (⟨i, a⟩ : Σ _ : ℕ, G)

/-- The distinguished base point of `MilnorTotalSpace G` at index `0` and label `1`. -/
def basepoint (G : Type u) [One G] : MilnorTotalSpace G :=
  vertex 0 1

@[simp]
theorem val_basepoint (G : Type u) [One G] : (basepoint G).val = Finsupp.single ⟨0, 1⟩ 1 :=
  val_vertex 0 1

@[simp]
theorem toRealization_basepoint (G : Type u) [One G] :
    (basepoint G).toRealization = universalGSpaceBasepoint G :=
  Subtype.ext ((val_basepoint G).trans (universalGSpaceBasepoint_val G).symm)

instance instNonempty [Nonempty G] : Nonempty (MilnorTotalSpace G) :=
  let ⟨a⟩ := ‹Nonempty G›
  ⟨vertex 0 a⟩

instance instInhabited [One G] : Inhabited (MilnorTotalSpace G) :=
  ⟨basepoint G⟩

/-- A point of `MilnorTotalSpace G` witnesses that `G` is nonempty. -/
theorem nonempty_of_milnorTotalSpace (p : MilnorTotalSpace G) : Nonempty G := by
  have hne : p.val.support.Nonempty := by
    rw [Finsupp.support_nonempty_iff]
    intro h0
    have hsum := p.sum_val
    rw [h0, Finsupp.sum_zero_index] at hsum
    exact zero_ne_one hsum
  exact ⟨hne.choose.2⟩

/-- `MilnorTotalSpace G` is empty if and only if `G` is empty. -/
@[simp]
theorem isEmpty_iff : IsEmpty (MilnorTotalSpace G) ↔ IsEmpty G :=
  ⟨fun h ↦ ⟨fun a ↦ h.false (vertex 0 a)⟩,
    fun h ↦ ⟨fun p ↦ (nonempty_of_milnorTotalSpace p).elim h.false⟩⟩

/-- Finitely supported index-weight vector obtained by summing coordinates over each index. -/
private def weightFinsupp (p : MilnorTotalSpace G) : ℕ →₀ ℝ :=
  Finsupp.mapDomain Sigma.fst p.val

/-- The `i`-th barycentric weight `t_i(p)` of a point in `MilnorTotalSpace G`. -/
def weight (i : ℕ) (p : MilnorTotalSpace G) : ℝ :=
  p.weightFinsupp i

theorem weight_def (i : ℕ) (p : MilnorTotalSpace G) :
    weight i p = Finsupp.mapDomain Sigma.fst p.val i :=
  (rfl)

/-- If `⟨i, a⟩` has nonzero coordinate in `p`, then `weight i p` equals that coordinate. -/
theorem weight_eq_val_of_ne_zero {i : ℕ} {a : G} {p : MilnorTotalSpace G}
    (ha : p.val ⟨i, a⟩ ≠ 0) : weight i p = p.val ⟨i, a⟩ :=
  Finsupp.mapDomain_apply' p.val.support p.val Subset.rfl p.support_val_injOn_fst
    (Finsupp.mem_support_iff.mpr ha)

/-- The support of `weightFinsupp p` is the image of `p.val.support` under `Sigma.fst`. -/
private theorem support_weightFinsupp (p : MilnorTotalSpace G) :
    p.weightFinsupp.support = p.val.support.image Sigma.fst :=
  Finsupp.mapDomain_support_of_injOn p.val p.support_val_injOn_fst

/-- The weight `weight i p` is nonzero if and only if some vertex over `i` has nonzero
coordinate. -/
theorem weight_ne_zero_iff {i : ℕ} {p : MilnorTotalSpace G} :
    weight i p ≠ 0 ↔ ∃ a : G, p.val ⟨i, a⟩ ≠ 0 := by
  have hmem : p.weightFinsupp i ≠ 0 ↔ i ∈ p.weightFinsupp.support :=
    Finsupp.mem_support_iff.symm
  rw [weight, hmem, support_weightFinsupp, Finset.mem_image]
  constructor
  · rintro ⟨⟨j, a⟩, hv, rfl⟩
    exact ⟨a, Finsupp.mem_support_iff.mp hv⟩
  · rintro ⟨a, ha⟩
    exact ⟨⟨i, a⟩, Finsupp.mem_support_iff.mpr ha, rfl⟩

/-- Every index weight `weight i p` is nonnegative. -/
theorem weight_nonneg (i : ℕ) (p : MilnorTotalSpace G) : 0 ≤ weight i p := by
  by_cases h : weight i p = 0
  · exact h.symm.le
  · obtain ⟨a, ha⟩ := weight_ne_zero_iff.mp h
    rw [weight_eq_val_of_ne_zero ha]
    exact p.val_nonneg ⟨i, a⟩

/-- The weight `weight i p` is positive if and only if some vertex over `i` has positive
coordinate. -/
theorem weight_pos_iff {i : ℕ} {p : MilnorTotalSpace G} :
    0 < weight i p ↔ ∃ a : G, 0 < p.val ⟨i, a⟩ := by
  constructor
  · intro hp
    obtain ⟨a, ha⟩ := weight_ne_zero_iff.mp hp.ne'
    exact ⟨a, lt_of_le_of_ne (p.val_nonneg ⟨i, a⟩) ha.symm⟩
  · rintro ⟨a, ha⟩
    rw [weight_eq_val_of_ne_zero ha.ne']
    exact ha

/-- The open star `U_i = {p | 0 < t_i(p)}` of points with positive `i`-th weight. -/
def coordSet (G : Type u) (i : ℕ) : Set (MilnorTotalSpace G) :=
  {p | 0 < weight i p}

@[simp]
theorem mem_coordSet_iff {i : ℕ} {p : MilnorTotalSpace G} :
    p ∈ coordSet G i ↔ 0 < weight i p :=
  Iff.rfl

/-- Only finitely many weights of a point in `MilnorTotalSpace G` are nonzero. -/
theorem finite_support_weight (p : MilnorTotalSpace G) :
    (Function.support fun i ↦ weight i p).Finite := by
  convert p.weightFinsupp.support.finite_toSet using 1
  ext i
  exact (Finsupp.mem_support_iff (f := p.weightFinsupp)).symm

/-- The finite sum of `weightFinsupp p` equals `1`. -/
private theorem sum_weightFinsupp (p : MilnorTotalSpace G) :
    p.weightFinsupp.sum (fun _ r ↦ r) = 1 := by
  rw [weightFinsupp, Finsupp.sum_mapDomain_index (fun _ ↦ rfl) (fun _ _ _ ↦ rfl), p.sum_val]

/-- The weights of every point in `MilnorTotalSpace G` have sum `1`. -/
theorem hasSum_weight (p : MilnorTotalSpace G) : HasSum (fun i ↦ weight i p) 1 := by
  rw [← p.sum_weightFinsupp]
  exact hasSum_sum_of_ne_finset_zero fun i hi ↦ Finsupp.notMem_support_iff.mp hi

@[simp]
theorem tsum_weight (p : MilnorTotalSpace G) : ∑' i, weight i p = 1 :=
  (hasSum_weight p).tsum_eq

@[simp]
theorem finsum_weight (p : MilnorTotalSpace G) : ∑ᶠ i, weight i p = 1 := by
  rw [finsum_eq_sum _ (finite_support_weight p)]
  convert p.sum_weightFinsupp using 1
  refine Finset.sum_subset (fun i hi ↦ ?_) (fun i _ hi ↦ ?_)
  · exact Finsupp.mem_support_iff.mpr ((finite_support_weight p).mem_toFinset.mp hi)
  · exact not_not.mp fun hne ↦ hi ((finite_support_weight p).mem_toFinset.mpr hne)

/-- Every index weight is at most `1`. -/
theorem weight_le_one (i : ℕ) (p : MilnorTotalSpace G) : weight i p ≤ 1 := by
  rw [← p.sum_weightFinsupp, Finsupp.sum]
  by_cases hi : i ∈ p.weightFinsupp.support
  · exact Finset.single_le_sum (fun j _ ↦ weight_nonneg j p) hi
  · have hw0 : weight i p = 0 := Finsupp.notMem_support_iff.mp hi
    rw [hw0]
    exact Finset.sum_nonneg fun j _ ↦ weight_nonneg j p

/-- Every point of `MilnorTotalSpace G` has at least one positive weight. -/
theorem exists_weight_pos (p : MilnorTotalSpace G) : ∃ i, 0 < weight i p := by
  by_contra! h
  have h0 : ∀ i, weight i p = 0 := fun i ↦ le_antisymm (h i) (weight_nonneg i p)
  have hsum := tsum_weight p
  simp [h0] at hsum

/-- The sets `coordSet G i` cover `MilnorTotalSpace G`. -/
@[simp]
theorem iUnion_coordSet (G : Type u) : ⋃ i, coordSet G i = univ :=
  eq_univ_of_forall fun p ↦ mem_iUnion.mpr (exists_weight_pos p)

/-- The `i`-th vertex label `g_i(p)` of `p : MilnorTotalSpace G`. When `0 < weight i p`, this is the
unique label `a : G` with `p.val ⟨i, a⟩ = weight i p`. -/
def label (i : ℕ) (p : MilnorTotalSpace G) : G := by
  classical
  exact if h : ∃ a : G, p.val ⟨i, a⟩ ≠ 0 then h.choose else (nonempty_of_milnorTotalSpace p).some

/-- On `coordSet G i`, the coordinate at `⟨i, label i p⟩` equals `weight i p`. -/
theorem val_label_eq_weight {i : ℕ} {p : MilnorTotalSpace G} (hp : p ∈ coordSet G i) :
    p.val ⟨i, label i p⟩ = weight i p := by
  classical
  have hex : ∃ a : G, p.val ⟨i, a⟩ ≠ 0 := weight_ne_zero_iff.mp hp.ne'
  have hchoose : p.val ⟨i, label i p⟩ ≠ 0 := by
    simp only [label, hex, ↓reduceDIte]
    exact hex.choose_spec
  exact (weight_eq_val_of_ne_zero hchoose).symm

/-- If `⟨i, a⟩` has nonzero coordinate in `p`, then `a = label i p`. -/
theorem eq_label_of_val_ne_zero {i : ℕ} {a : G} {p : MilnorTotalSpace G}
    (ha : p.val ⟨i, a⟩ ≠ 0) : a = label i p := by
  have hp : p ∈ coordSet G i := by
    rw [mem_coordSet_iff, weight_eq_val_of_ne_zero ha]
    exact lt_of_le_of_ne (p.val_nonneg ⟨i, a⟩) ha.symm
  have hl : p.val ⟨i, label i p⟩ ≠ 0 := by
    rw [val_label_eq_weight hp]
    exact hp.ne'
  by_contra hne
  rcases realization_apply_eq_zero_of_fst_eq (x := p.toRealization)
      (v := ⟨i, a⟩) (w := ⟨i, label i p⟩) rfl (fun h ↦ hne (congrArg Sigma.snd h)) with h0 | h0
  · exact ha h0
  · exact hl h0

/-- If `0 < p.val ⟨i, a⟩`, then `a = label i p`. -/
theorem eq_label_of_val_pos {i : ℕ} {a : G} {p : MilnorTotalSpace G}
    (ha : 0 < p.val ⟨i, a⟩) : a = label i p :=
  eq_label_of_val_ne_zero ha.ne'

/-- Complete coordinate formula: `p.val ⟨i, a⟩` is `weight i p` at `a = label i p` and `0`
otherwise. -/
theorem val_apply_eq_ite [DecidableEq G] (i : ℕ) (a : G) (p : MilnorTotalSpace G) :
    p.val ⟨i, a⟩ = if a = label i p then weight i p else 0 := by
  by_cases hp : p ∈ coordSet G i
  · split_ifs with h
    · rw [h, val_label_eq_weight hp]
    · by_contra hne
      exact h (eq_label_of_val_ne_zero hne)
  · have hw : weight i p = 0 :=
      le_antisymm (not_lt.mp hp) (weight_nonneg i p)
    have hva : p.val ⟨i, a⟩ = 0 := by
      by_contra hne
      exact weight_ne_zero_iff.mpr ⟨a, hne⟩ hw
    rw [hva, hw, ite_self]

/-- Coordinate extensionality: two points of `MilnorTotalSpace G` are equal if and only if they have
the same weights and the same labels at all indices of positive weight. -/
theorem ext_coord {p q : MilnorTotalSpace G} (hw : ∀ i, weight i p = weight i q)
    (hl : ∀ i, p ∈ coordSet G i → label i p = label i q) : p = q := by
  classical
  refine ext_val (Finsupp.ext fun ⟨i, a⟩ ↦ ?_)
  rw [val_apply_eq_ite, val_apply_eq_ite, hw i]
  by_cases hp : p ∈ coordSet G i
  · rw [hl i hp]
  · have hq : weight i q = 0 := by
      rw [← hw i]
      exact le_antisymm (not_lt.mp hp) (weight_nonneg i p)
    rw [hq, ite_self, ite_self]

@[simp]
theorem weight_vertex (i j : ℕ) (a : G) :
    weight i (vertex j a) = if i = j then 1 else 0 := by
  classical
  rw [weight_def, val_vertex, Finsupp.mapDomain_single]
  simp [Finsupp.single_apply, eq_comm]

@[simp]
theorem label_vertex (i : ℕ) (a : G) : label i (vertex i a) = a :=
  (eq_label_of_val_pos (p := vertex i a) (by simp)).symm

@[simp]
theorem weight_basepoint (G : Type u) [One G] (i : ℕ) :
    weight i (basepoint G) = if i = 0 then 1 else 0 :=
  weight_vertex i 0 1

@[simp]
theorem label_basepoint (G : Type u) [One G] : label 0 (basepoint G) = 1 :=
  label_vertex 0 1

/-- Set-level vertex relabelling `MilnorTotalSpace X → MilnorTotalSpace Y` induced by an arbitrary
function `f : X → Y`, sending each vertex `⟨i, x⟩` to `⟨i, f x⟩` while preserving weights. -/
def relabel {X : Type u} {Y : Type v} (f : X → Y) (p : MilnorTotalSpace X) :
    MilnorTotalSpace Y :=
  letI : DecidableEq ℕ := Classical.decEq ℕ
  letI : DecidableEq X := Classical.decEq X
  letI : DecidableEq Y := Classical.decEq Y
  ofRealization
    ((indexedJoinMap (A := fun _ : ℕ ↦ X) (B := fun _ : ℕ ↦ Y)
      _root_.id Function.injective_id (fun _ ↦ f)).realizationMap p.toRealization)

theorem val_relabel {X : Type u} {Y : Type v} (f : X → Y) (p : MilnorTotalSpace X) :
    (relabel f p).val =
      Finsupp.mapDomain (fun v : Σ _ : ℕ, X ↦ (⟨v.1, f v.2⟩ : Σ _ : ℕ, Y)) p.val := by
  let _ : DecidableEq ℕ := Classical.decEq ℕ
  let _ : DecidableEq X := Classical.decEq X
  let _ : DecidableEq Y := Classical.decEq Y
  exact (PreAbstractSimplicialComplex.SimplicialMap.realizationMap_val
    (indexedJoinMap (A := fun _ : ℕ ↦ X) (B := fun _ : ℕ ↦ Y)
      _root_.id Function.injective_id (fun _ ↦ f)) p.toRealization).trans
    (congrArg (Finsupp.mapDomain · p.val)
      (funext (indexedJoinMap_apply (A := fun _ : ℕ ↦ X) (B := fun _ : ℕ ↦ Y)
        _root_.id Function.injective_id (fun _ ↦ f))))

@[simp]
theorem weight_relabel {X : Type u} {Y : Type v} (f : X → Y) (i : ℕ)
    (p : MilnorTotalSpace X) : weight i (relabel f p) = weight i p := by
  rw [weight_def, weight_def, val_relabel, ← Finsupp.mapDomain_comp]
  rfl

@[simp]
theorem label_relabel {X : Type u} {Y : Type v} (f : X → Y) {i : ℕ}
    {p : MilnorTotalSpace X} (hp : p ∈ coordSet X i) :
    label i (relabel f p) = f (label i p) := by
  symm
  apply eq_label_of_val_pos
  rw [val_relabel]
  have hinj : InjOn (fun v : Σ _ : ℕ, X ↦ (⟨v.1, f v.2⟩ : Σ _ : ℕ, Y)) p.val.support :=
    fun u hu v hv huv ↦ p.support_val_injOn_fst hu hv (Sigma.mk.inj huv).1
  have hmem : (⟨i, label i p⟩ : Σ _ : ℕ, X) ∈ p.val.support :=
    Finsupp.mem_support_iff.mpr (by rw [val_label_eq_weight hp]; exact hp.ne')
  rw [Finsupp.mapDomain_apply' p.val.support p.val Subset.rfl hinj hmem, val_label_eq_weight hp]
  exact hp

@[simp]
theorem relabel_id (p : MilnorTotalSpace G) : relabel _root_.id p = p := by
  apply ext_val
  simp [val_relabel]

@[simp]
theorem relabel_id' (p : MilnorTotalSpace G) : relabel (fun a ↦ a) p = p :=
  relabel_id p

@[simp]
theorem relabel_comp {X : Type u} {Y : Type v} {Z : Type w}
    (g : Y → Z) (f : X → Y) (p : MilnorTotalSpace X) :
    relabel g (relabel f p) = relabel (g ∘ f) p := by
  apply ext_val
  simp only [val_relabel, ← Finsupp.mapDomain_comp]
  rfl

end Coordinates

/-! ### Strong coordinate topology -/

section Topology

variable {G : Type u} [TopologicalSpace G]

/-- The strong coordinate topology on `MilnorTotalSpace G`, generated by the weights `weight i` and
the labels `label i` on `coordSet G i`. -/
instance instTopologicalSpace : TopologicalSpace (MilnorTotalSpace G) :=
  TopologicalSpace.generateFrom
    ({s | ∃ (i : ℕ) (W : Set ℝ), IsOpen W ∧ s = weight i ⁻¹' W} ∪
      {s | ∃ (i : ℕ) (V : Set G), IsOpen V ∧ s = coordSet G i ∩ label i ⁻¹' V})

/-- **Universal continuity criterion for the strong coordinate topology.** A map `f` from any
topological space `Z` (including a product space) into `MilnorTotalSpace G` is continuous if and
only if every weight `weight i ∘ f` is continuous and every label `label i ∘ f` is continuous on
`{z | 0 < weight i (f z)}`. -/
theorem continuous_iff {Z : Type*} [TopologicalSpace Z] {f : Z → MilnorTotalSpace G} :
    Continuous f ↔
      (∀ i, Continuous fun z ↦ weight i (f z)) ∧
        ∀ i, ContinuousOn (fun z ↦ label i (f z)) {z | 0 < weight i (f z)} := by
  rw [continuous_generateFrom_iff]
  constructor
  · intro hf
    have hw : ∀ i, Continuous fun z ↦ weight i (f z) := fun i ↦
      continuous_def.mpr fun W hW ↦ hf _ (Or.inl ⟨i, W, hW, rfl⟩)
    refine ⟨hw, fun i ↦ continuousOn_iff_continuous_domRestrict.mpr ?_⟩
    refine continuous_def.mpr fun V hV ↦ ?_
    have hpre := hf _ (Or.inr ⟨i, V, hV, rfl⟩)
    convert hpre.preimage (continuous_subtype_val (p := fun z ↦ 0 < weight i (f z))) using 1
    ext ⟨z, hz⟩
    exact ⟨fun h ↦ ⟨hz, h⟩, fun h ↦ h.2⟩
  · rintro ⟨hw, hl⟩ s (⟨i, W, hW, rfl⟩ | ⟨i, V, hV, rfl⟩)
    · exact hW.preimage (hw i)
    · have hO : IsOpen {z | 0 < weight i (f z)} := isOpen_lt continuous_const (hw i)
      obtain ⟨U, hU, hUV⟩ := continuousOn_iff'.mp (hl i) V hV
      convert hU.inter hO using 1
      ext z
      have hz := Set.ext_iff.mp hUV z
      simp only [mem_preimage, mem_inter_iff, mem_coordSet_iff, mem_ofPred_eq] at hz ⊢
      exact ⟨fun h ↦ ⟨(hz.mp ⟨h.2, h.1⟩).1, h.1⟩, fun h ↦ ⟨h.2, (hz.mpr h).1⟩⟩

/-- Each index weight `weight i : MilnorTotalSpace G → ℝ` is continuous. -/
@[fun_prop, continuity]
theorem continuous_weight (i : ℕ) : Continuous (weight i : MilnorTotalSpace G → ℝ) :=
  (continuous_iff.mp continuous_id).1 i

/-- Each positive-weight star `coordSet G i = {p | 0 < weight i p}` is open. -/
theorem isOpen_coordSet (i : ℕ) : IsOpen (coordSet G i) :=
  isOpen_lt continuous_const (continuous_weight i)

/-- On `coordSet G i`, the vertex label `label i` is continuous. -/
theorem continuousOn_label (i : ℕ) :
    ContinuousOn (label i : MilnorTotalSpace G → G) (coordSet G i) :=
  (continuous_iff.mp continuous_id).2 i

/-- For a continuous map `f : Z → MilnorTotalSpace G`, `label i ∘ f` is continuous at every point
where `0 < weight i (f z)`. -/
theorem Continuous.continuousAt_label_comp {Z : Type*} [TopologicalSpace Z]
    {f : Z → MilnorTotalSpace G} (hf : Continuous f) {i : ℕ} {z : Z}
    (hz : 0 < weight i (f z)) : ContinuousAt (fun x ↦ label i (f x)) z :=
  ((continuous_iff.mp hf).2 i).continuousAt
    ((isOpen_lt continuous_const ((continuous_iff.mp hf).1 i)).mem_nhds hz)

/-- The vertex inclusion `a ↦ vertex i a` at a fixed index `i` is continuous. -/
@[fun_prop, continuity]
theorem continuous_vertex (i : ℕ) : Continuous (vertex i : G → MilnorTotalSpace G) := by
  rw [continuous_iff]
  refine ⟨fun j ↦ ?_, fun j ↦ ?_⟩
  · simp only [weight_vertex]
    exact continuous_const
  · by_cases hij : j = i
    · subst hij
      simp only [weight_vertex, ↓reduceIte, zero_lt_one, Set.ofPred_true, label_vertex]
      exact continuousOn_id
    · simp only [weight_vertex, hij, ↓reduceIte, lt_self_iff_false, Set.ofPred_false]
      exact continuousOn_empty _

/-- If `G` is Hausdorff, then `MilnorTotalSpace G` is Hausdorff. -/
instance instT2Space [T2Space G] : T2Space (MilnorTotalSpace G) := by
  refine ⟨fun p q hpq ↦ ?_⟩
  by_cases hw : ∀ i, weight i p = weight i q
  · have hl : ∃ i, p ∈ coordSet G i ∧ label i p ≠ label i q := by
      by_contra! h
      exact hpq (ext_coord hw h)
    obtain ⟨i, hpi, hlpq⟩ := hl
    have hqi : q ∈ coordSet G i := by
      rw [mem_coordSet_iff, ← hw i]
      exact hpi
    obtain ⟨U, V, hU, hV, hpU, hqV, hdisj⟩ := t2_separation hlpq
    obtain ⟨U', hU', hU'eq⟩ := continuousOn_iff'.mp (continuousOn_label i) U hU
    obtain ⟨V', hV', hV'eq⟩ := continuousOn_iff'.mp (continuousOn_label i) V hV
    refine ⟨U' ∩ coordSet G i, V' ∩ coordSet G i,
      hU'.inter (isOpen_coordSet i), hV'.inter (isOpen_coordSet i), ?_, ?_, ?_⟩
    · rw [← hU'eq]
      exact ⟨hpU, hpi⟩
    · rw [← hV'eq]
      exact ⟨hqV, hqi⟩
    · rw [← hU'eq, ← hV'eq]
      exact Disjoint.mono inter_subset_left inter_subset_left (hdisj.preimage _)
  · push Not at hw
    obtain ⟨i, hi⟩ := hw
    obtain ⟨U, V, hU, hV, hpU, hqV, hdisj⟩ := t2_separation hi
    exact ⟨weight i ⁻¹' U, weight i ⁻¹' V,
      hU.preimage (continuous_weight i), hV.preimage (continuous_weight i),
      hpU, hqV, hdisj.preimage _⟩

/-- The canonical identity comparison from the weak simplicial topology on `universalGSpace G` to
the strong coordinate topology on `MilnorTotalSpace G` is continuous for every topological space
`G`. -/
theorem continuous_ofRealization :
    Continuous (ofRealization : universalGSpace G → MilnorTotalSpace G) := by
  rw [continuous_iff_faceInclusion]
  intro σ
  rw [continuous_iff]
  have hval_face : ∀ x : StandardSimplex σ.1,
      (ofRealization ((indexedJoin fun _ : ℕ ↦ G).faceInclusion σ x)).val = x.1 := fun x ↦ by
    rw [val_ofRealization, faceInclusion_val]
  refine ⟨fun i ↦ ?_, fun i ↦ ?_⟩
  · classical
    by_cases hex : ∃ a : G, (⟨i, a⟩ : Σ _ : ℕ, G) ∈ σ.1
    · obtain ⟨a, ha⟩ := hex
      have heq : (fun x : StandardSimplex σ.1 ↦
          weight i ((ofRealization ∘ (indexedJoin fun _ : ℕ ↦ G).faceInclusion σ) x)) =
          fun x ↦ x.1 ⟨i, a⟩ := by
        ext x
        simp only [Function.comp_apply]
        by_cases hx0 : x.1 ⟨i, a⟩ = 0
        · rw [hx0]
          by_contra hne
          obtain ⟨b, hb⟩ := weight_ne_zero_iff.mp hne
          rw [hval_face x] at hb
          have hmem : (⟨i, b⟩ : Σ _ : ℕ, G) ∈ σ.1 :=
            StandardSimplex.support_subset x (Finsupp.mem_support_iff.mpr hb)
          have hab : (⟨i, b⟩ : Σ _ : ℕ, G) = ⟨i, a⟩ :=
            eq_of_mem_indexedJoin σ.2 hmem ha rfl
          exact hb (by simpa [hab] using hx0)
        · have hx0' :
              (ofRealization ((indexedJoin fun _ : ℕ ↦ G).faceInclusion σ x)).val ⟨i, a⟩ ≠ 0 := by
            rwa [hval_face x]
          exact (weight_eq_val_of_ne_zero hx0').trans (by rw [hval_face x])
      rw [heq]
      exact (continuous_apply (⟨i, a⟩ : Σ _ : ℕ, G)).comp continuous_induced_dom
    · push Not at hex
      have heq : (fun x : StandardSimplex σ.1 ↦
          weight i ((ofRealization ∘ (indexedJoin fun _ : ℕ ↦ G).faceInclusion σ) x)) =
          fun _ ↦ 0 := by
        ext x
        simp only [Function.comp_apply]
        by_contra hne
        obtain ⟨a, ha⟩ := weight_ne_zero_iff.mp hne
        rw [hval_face x] at ha
        exact hex a (StandardSimplex.support_subset x (Finsupp.mem_support_iff.mpr ha))
      rw [heq]
      exact continuous_const
  · classical
    by_cases hex : ∃ a : G, (⟨i, a⟩ : Σ _ : ℕ, G) ∈ σ.1
    · obtain ⟨a, ha⟩ := hex
      refine (continuousOn_const (c := a)).congr fun x hx ↦ ?_
      simp only [Function.comp_apply, mem_ofPred_eq] at hx ⊢
      obtain ⟨b, hb⟩ := weight_pos_iff.mp hx
      have hb' : 0 < x.1 ⟨i, b⟩ := by rwa [← hval_face x]
      have hmem : (⟨i, b⟩ : Σ _ : ℕ, G) ∈ σ.1 :=
        StandardSimplex.support_subset x (Finsupp.mem_support_iff.mpr hb'.ne')
      have hab : b = a := congrArg Sigma.snd (eq_of_mem_indexedJoin σ.2 hmem ha rfl)
      exact (eq_label_of_val_pos hb).symm.trans hab
    · push Not at hex
      have hemp : {z : StandardSimplex σ.1 |
          0 < weight i ((ofRealization ∘ (indexedJoin fun _ : ℕ ↦ G).faceInclusion σ) z)} = ∅ := by
        ext x
        simp only [Function.comp_apply, mem_ofPred_eq, mem_empty_iff_false, iff_false, not_lt]
        by_contra hpos
        obtain ⟨a, ha⟩ := weight_pos_iff.mp (not_le.mp hpos)
        rw [hval_face x] at ha
        exact hex a (StandardSimplex.support_subset x (Finsupp.mem_support_iff.mpr ha.ne'))
      rw [hemp]
      exact continuousOn_empty _

/-- Functorial map `MilnorTotalSpace X → MilnorTotalSpace Y` induced by a continuous map
`f : C(X, Y)`, relabelling each vertex `⟨i, x⟩` to `⟨i, f x⟩`. -/
def map {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y] (f : C(X, Y)) :
    C(MilnorTotalSpace X, MilnorTotalSpace Y) where
  toFun := relabel f
  continuous_toFun := by
    rw [continuous_iff]
    refine ⟨fun i ↦ ?_, fun i ↦ ?_⟩
    · simp_rw [weight_relabel]
      exact continuous_weight i
    · simp_rw [weight_relabel]
      exact (f.continuous.comp_continuousOn (continuousOn_label i)).congr
        fun p hp ↦ label_relabel f hp

theorem val_map {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) (p : MilnorTotalSpace X) :
    (map f p).val =
      Finsupp.mapDomain (fun v : Σ _ : ℕ, X ↦ (⟨v.1, f v.2⟩ : Σ _ : ℕ, Y)) p.val :=
  val_relabel f p

@[simp]
theorem weight_map {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) (i : ℕ) (p : MilnorTotalSpace X) :
    weight i (map f p) = weight i p :=
  weight_relabel f i p

@[simp]
theorem label_map {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) {i : ℕ} {p : MilnorTotalSpace X} (hp : p ∈ coordSet X i) :
    label i (map f p) = f (label i p) :=
  label_relabel f hp

@[simp]
theorem map_vertex {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) (i : ℕ) (x : X) :
    map f (vertex i x) = vertex i (f x) := by
  apply ext_val
  rw [val_map, val_vertex, val_vertex, Finsupp.mapDomain_single]

@[simp]
theorem map_id (X : Type u) [TopologicalSpace X] :
    map (ContinuousMap.id X) = ContinuousMap.id (MilnorTotalSpace X) := by
  ext p : 1
  exact relabel_id p

@[simp]
theorem map_comp {X : Type u} {Y : Type v} {Z : Type w}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    (g : C(Y, Z)) (f : C(X, Y)) :
    map (g.comp f) = (map g).comp (map f) := by
  ext p : 1
  exact (relabel_comp g f p).symm

end Topology

/-! ### Right action dictionary and joint continuity -/

section RightAction

variable {G : Type u}

section Monoid

variable [Monoid G]

/-- Right multiplication of vertex labels defines a right action of `G` (an action of `Gᵐᵒᵖ`) on
`MilnorTotalSpace G`. -/
instance instSMulOp : SMul Gᵐᵒᵖ (MilnorTotalSpace G) where
  smul g p := relabel (· * g.unop) p

theorem val_op_smul (g : G) (p : MilnorTotalSpace G) :
    (op g • p).val =
      Finsupp.mapDomain (fun v : Σ _ : ℕ, G ↦ (⟨v.1, v.2 * g⟩ : Σ _ : ℕ, G)) p.val :=
  val_relabel (· * g) p

/-- Relabelling on the right by `g` and then by `h` agrees with relabelling by `g * h`. -/
theorem op_smul_op_smul (g h : G) (p : MilnorTotalSpace G) :
    op h • (op g • p) = op (g * h) • p := by
  change relabel (· * h) (relabel (· * g) p) = relabel (· * (g * h)) p
  rw [relabel_comp]
  congr 1
  funext a
  exact mul_assoc a g h

/-- Right action of `Gᵐᵒᵖ` on `MilnorTotalSpace G` by multiplying labels on the right. -/
instance instMulActionOp : MulAction Gᵐᵒᵖ (MilnorTotalSpace G) where
  one_smul p := by
    change relabel (· * 1) p = p
    simp
  mul_smul g h p := (op_smul_op_smul h.unop g.unop p).symm

/-- Right relabelling preserves every index weight `t_i`. -/
@[simp]
theorem weight_smul (g : Gᵐᵒᵖ) (i : ℕ) (p : MilnorTotalSpace G) :
    weight i (g • p) = weight i p :=
  weight_relabel (· * g.unop) i p

/-- Right relabelling preserves membership in each positive-weight star `coordSet G i`. -/
theorem smul_mem_coordSet_iff (g : Gᵐᵒᵖ) {i : ℕ} {p : MilnorTotalSpace G} :
    g • p ∈ coordSet G i ↔ p ∈ coordSet G i := by
  simp [mem_coordSet_iff]

/-- On `coordSet G i`, acting on the right by `g` multiplies the `i`-th vertex label on the right by
`g`: `g_i(p · g) = g_i(p) * g`. -/
@[simp]
theorem label_op_smul (g : G) {i : ℕ} {p : MilnorTotalSpace G} (hp : p ∈ coordSet G i) :
    label i (op g • p) = label i p * g :=
  label_relabel (· * g) hp

@[simp]
theorem op_smul_vertex (g : G) (i : ℕ) (a : G) :
    op g • vertex i a = vertex i (a * g) := by
  apply ext_val
  rw [val_op_smul, val_vertex, val_vertex, Finsupp.mapDomain_single]

@[simp]
theorem op_smul_basepoint (g : G) : op g • basepoint G = vertex 0 g := by
  rw [basepoint, op_smul_vertex, one_mul]

/-- **Joint continuity of the right action on `MilnorTotalSpace G`**, proved directly from
`g_i(p · g) = g_i(p) * g` and continuity of multiplication on `G` with no metric or local
compactness hypothesis. -/
instance instContinuousSMul [TopologicalSpace G] [ContinuousMul G] :
    ContinuousSMul Gᵐᵒᵖ (MilnorTotalSpace G) where
  continuous_smul := by
    rw [continuous_iff]
    refine ⟨fun i ↦ ?_, fun i ↦ ?_⟩
    · simp_rw [weight_smul]
      exact (continuous_weight i).comp continuous_snd
    · have hdom : {x : Gᵐᵒᵖ × MilnorTotalSpace G | 0 < weight i (x.1 • x.2)} =
          univ ×ˢ coordSet G i := by
        ext ⟨g, p⟩
        simp [mem_coordSet_iff]
      rw [hdom]
      refine (((continuousOn_label i).comp continuous_snd.continuousOn
        fun x (hx : x ∈ univ ×ˢ coordSet G i) ↦ hx.2).mul
        (continuous_unop.comp continuous_fst).continuousOn).congr ?_
      rintro ⟨g, p⟩ ⟨-, hp⟩
      exact label_op_smul g.unop hp

end Monoid

section Group

variable [Group G]

/-- The right action of a group `G` on `MilnorTotalSpace G` is free. -/
instance instIsCancelSMulOp : IsCancelSMul Gᵐᵒᵖ (MilnorTotalSpace G) :=
  (isCancelSMul_iff_eq_one_of_smul_eq (α := Gᵐᵒᵖ) (β := MilnorTotalSpace G)).mpr
    fun g p hgp ↦ by
      obtain ⟨i, hi⟩ := exists_weight_pos p
      have hl : label i (op g.unop • p) = label i p := by
        rw [op_unop, hgp]
      rw [label_op_smul g.unop hi, mul_eq_left] at hl
      exact unop_injective hl

/-- Equivalence `universalGSpace G ≃ MilnorTotalSpace G` inverting every vertex label. It carries
the left action of `g⁻¹` on `universalGSpace G` to the right action of `g` on
`MilnorTotalSpace G`. -/
def invEquiv (G : Type u) [Group G] : universalGSpace G ≃ MilnorTotalSpace G where
  toFun x := relabel Inv.inv (ofRealization x)
  invFun p := (relabel Inv.inv p).toRealization
  left_inv x := by
    have h : relabel Inv.inv (relabel Inv.inv (ofRealization x)) = ofRealization x := by
      rw [relabel_comp]
      simp
    exact congrArg toRealization h
  right_inv p := by
    change relabel Inv.inv (relabel Inv.inv p) = p
    rw [relabel_comp]
    simp

theorem val_invEquiv (x : universalGSpace G) :
    (invEquiv G x).val =
      Finsupp.mapDomain (fun v : Σ _ : ℕ, G ↦ (⟨v.1, v.2⁻¹⟩ : Σ _ : ℕ, G)) x.1 :=
  val_relabel Inv.inv (ofRealization x)

@[simp]
theorem invEquiv_basepoint : invEquiv G (universalGSpaceBasepoint G) = basepoint G := by
  apply ext_val
  rw [val_invEquiv, universalGSpaceBasepoint_val, val_basepoint, Finsupp.mapDomain_single, inv_one]

/-- **Left-to-right action dictionary.** Label inversion carries the left action of `g⁻¹` on
`universalGSpace G` to the right action of `g` on `MilnorTotalSpace G`. -/
theorem invEquiv_inv_smul (g : G) (x : universalGSpace G) :
    invEquiv G (g⁻¹ • x) = op g • invEquiv G x := by
  apply ext_val
  rw [val_invEquiv, universalGSpace_smul_val, val_op_smul, val_invEquiv,
    ← Finsupp.mapDomain_comp, ← Finsupp.mapDomain_comp]
  congr 1
  funext ⟨i, a⟩
  simp [mul_inv_rev]

/-- Label inversion carries the left action of `g` on `universalGSpace G` to the right action of
`g⁻¹` on `MilnorTotalSpace G`. -/
@[simp]
theorem invEquiv_smul (g : G) (x : universalGSpace G) :
    invEquiv G (g • x) = op g⁻¹ • invEquiv G x := by
  simpa using invEquiv_inv_smul g⁻¹ x

end Group

end RightAction

end MilnorTotalSpace

/-- Continuous equivariant comparison map from the weak-topology join `universalGSpace G` to the
strong-topology join `MilnorTotalSpace G`, defined by inverting labels (`MilnorTotalSpace.invEquiv`)
so that left translation by `g⁻¹` corresponds to right translation by `g`. -/
def weakToMilnorTotalSpace (G : Type u) [Group G] [TopologicalSpace G] :
    C(universalGSpace G, MilnorTotalSpace G) where
  toFun := MilnorTotalSpace.invEquiv G
  continuous_toFun := by
    let _ : DecidableEq ℕ := Classical.decEq ℕ
    let _ : DecidableEq G := Classical.decEq G
    exact MilnorTotalSpace.continuous_ofRealization.comp
      (indexedJoinMap (A := fun _ : ℕ ↦ G) (B := fun _ : ℕ ↦ G)
        _root_.id Function.injective_id (fun _ a ↦ a⁻¹)).realizationMap.continuous

@[simp]
theorem coe_weakToMilnorTotalSpace (G : Type u) [Group G] [TopologicalSpace G] :
    (weakToMilnorTotalSpace G : universalGSpace G → MilnorTotalSpace G) =
      MilnorTotalSpace.invEquiv G :=
  (rfl)

@[simp]
theorem weakToMilnorTotalSpace_basepoint (G : Type u) [Group G] [TopologicalSpace G] :
    weakToMilnorTotalSpace G (universalGSpaceBasepoint G) = MilnorTotalSpace.basepoint G :=
  MilnorTotalSpace.invEquiv_basepoint

theorem weakToMilnorTotalSpace_inv_smul {G : Type u} [Group G] [TopologicalSpace G]
    (g : G) (x : universalGSpace G) :
    weakToMilnorTotalSpace G (g⁻¹ • x) = op g • weakToMilnorTotalSpace G x :=
  MilnorTotalSpace.invEquiv_inv_smul g x

@[simp]
theorem weakToMilnorTotalSpace_smul {G : Type u} [Group G] [TopologicalSpace G]
    (g : G) (x : universalGSpace G) :
    weakToMilnorTotalSpace G (g • x) = op g⁻¹ • weakToMilnorTotalSpace G x :=
  MilnorTotalSpace.invEquiv_smul g x

end TauCeti

namespace MonoidHom

open TauCeti

variable {G : Type u} {H : Type v} [Monoid G] [Monoid H] [TopologicalSpace G] [TopologicalSpace H]

/-- A continuous monoid homomorphism induces a continuous right-equivariant map on strong-topology
Milnor total spaces. -/
def milnorTotalSpaceMap (φ : G →* H) (hφ : Continuous φ) :
    C(MilnorTotalSpace G, MilnorTotalSpace H) :=
  MilnorTotalSpace.map ⟨φ, hφ⟩

@[simp]
theorem weight_milnorTotalSpaceMap (φ : G →* H) (hφ : Continuous φ) (i : ℕ)
    (p : MilnorTotalSpace G) :
    MilnorTotalSpace.weight i (φ.milnorTotalSpaceMap hφ p) = MilnorTotalSpace.weight i p :=
  MilnorTotalSpace.weight_map ⟨φ, hφ⟩ i p

@[simp]
theorem label_milnorTotalSpaceMap (φ : G →* H) (hφ : Continuous φ) {i : ℕ}
    {p : MilnorTotalSpace G} (hp : p ∈ MilnorTotalSpace.coordSet G i) :
    MilnorTotalSpace.label i (φ.milnorTotalSpaceMap hφ p) = φ (MilnorTotalSpace.label i p) :=
  MilnorTotalSpace.label_map ⟨φ, hφ⟩ hp

@[simp]
theorem milnorTotalSpaceMap_basepoint (φ : G →* H) (hφ : Continuous φ) :
    φ.milnorTotalSpaceMap hφ (MilnorTotalSpace.basepoint G) = MilnorTotalSpace.basepoint H := by
  rw [milnorTotalSpaceMap, MilnorTotalSpace.basepoint, MilnorTotalSpace.map_vertex]
  simp [MilnorTotalSpace.basepoint]

@[simp]
theorem milnorTotalSpaceMap_op_smul (φ : G →* H) (hφ : Continuous φ) (g : G)
    (p : MilnorTotalSpace G) :
    φ.milnorTotalSpaceMap hφ (MulOpposite.op g • p) =
      MulOpposite.op (φ g) • φ.milnorTotalSpaceMap hφ p := by
  apply MilnorTotalSpace.ext_val
  simp only [milnorTotalSpaceMap, MilnorTotalSpace.val_map, MilnorTotalSpace.val_op_smul,
    ← Finsupp.mapDomain_comp]
  congr 1
  funext ⟨i, a⟩
  simp

@[simp]
theorem milnorTotalSpaceMap_id :
    (MonoidHom.id G).milnorTotalSpaceMap continuous_id =
      ContinuousMap.id (MilnorTotalSpace G) :=
  MilnorTotalSpace.map_id G

@[simp]
theorem milnorTotalSpaceMap_comp {K : Type w} [Monoid K] [TopologicalSpace K]
    (ψ : H →* K) (hψ : Continuous ψ) (φ : G →* H) (hφ : Continuous φ) :
    (ψ.comp φ).milnorTotalSpaceMap (hψ.comp hφ) =
      (ψ.milnorTotalSpaceMap hψ).comp (φ.milnorTotalSpaceMap hφ) :=
  MilnorTotalSpace.map_comp ⟨ψ, hψ⟩ ⟨φ, hφ⟩

end MonoidHom
