/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.ContinuousMap.Algebra
public import TauCeti.AlgebraicTopology.Singular.LocalHomology.RegularValue
import Mathlib.Analysis.Convex.Contractible

/-!
# The local fixed-point index

Let `E` be a finite-dimensional real normed space, `U ⊆ E` open and `f : U → E` continuous. The
fixed points of `f` are the zeros of the map `x ↦ x - f x`. When the fixed set
`{x | f x = x}` is compact, the **fixed-point index** of `f` is the local degree of
`x ↦ x - f x` at `0` (`TauCeti.HomologicalOrientation.localDegree`): the integer `i(f)` with

`(id - f)_*[U]_{Fix f} = i(f) • o 0`  in  `Hₙ(E, E ∖ {0}; ℤ)`,

where `[U]_{Fix f}` is the fundamental class of `U` along the fixed set. The same orientation `o`
of `E` is used on the source and on the target, so reversing it negates both sides of this
equation and leaves the integer `i(f)` unchanged: the index does not depend on an orientation of
`E` (`ContinuousMap.fixedPointIndex_eq_localDegree`). By convention the index is `0` when the fixed
set is not compact. No differentiability of `f` and no finiteness of the fixed set is needed.

The index has the following properties.

* **Normalization at nondegenerate fixed points.** If `f` agrees on `U` with a map `φ` which is
  differentiable at a point `x ∈ U` with `det (1 - Dφ(x)) ≠ 0`, the local index of
  `x ↦ x - f x` at `x` is `sign det (1 - Dφ(x))`
  (`TauCeti.HomologicalOrientation.localIndex_subtypeValSub_eq_sign_det`). A compact fixed set of
  such nondegenerate fixed points is finite
  (`IsCompact.finite_setOf_apply_eq_self_of_hasFDerivAt`), and the index is then the signed
  count `∑_{f x = x} sign det (1 - Dφ(x))` (`ContinuousMap.fixedPointIndex_eq_sum_sign_det`). In
  particular a constant map with value `c` has index `1` if `c ∈ U` and `0` otherwise
  (`ContinuousMap.fixedPointIndex_const_of_mem`, `ContinuousMap.fixedPointIndex_const_of_notMem`,
  and `ContinuousMap.fixedPointIndex_zero_of_mem`, `ContinuousMap.fixedPointIndex_zero_of_notMem`
  for the zero map).
* **Homotopy invariance.** Maps joined by a homotopy `H : [0, 1] × U → E` whose fixed set
  `{(t, x) | H (t, x) = x}` is compact have the same index
  (`ContinuousMap.fixedPointIndex_eq_of_homotopy`). For instance, if `U` has compact closure
  and `H` extends continuously to `[0, 1] × closure U` with no fixed point on the boundary, the
  fixed set is compact.
* **Excision.** Restricting `f` to an open subset containing all of its fixed points does not
  change the index (`ContinuousMap.fixedPointIndex_comp_inclusion`). Applied to `U₁ ∩ U₂`, this
  shows that the index of an isolated fixed set does not depend on the isolating neighbourhood.
* **Additivity.** If the fixed set is compact and covered by open subsets `V` and `W` of `U` with
  no fixed point in both, the index is the sum of the indices of the restrictions to `V` and to
  `W` (`ContinuousMap.fixedPointIndex_eq_add`).
* A map without fixed points has index `0` (`ContinuousMap.fixedPointIndex_eq_zero_of_forall_ne`).

Together, these compute the index of a degenerate map as the signed count of the fixed points of
a nondegenerate map joined to it by a homotopy with compact fixed set, such as a small
perturbation that keeps the boundary of an isolating neighbourhood free of fixed points. For
example, on `ℝ` the degenerate fixed point `0` of `x ↦ x + x³` has index `-1`: the homotopy
`x ↦ x + x³ + t x`, `t ∈ [0, 1]`, has `0` as its only fixed point, and ends at a map whose
derivative at `0` is `2`, with `sign (1 - 2) = -1`. This computation is checked in
`TauCeti/Examples/AlgebraicTopology/Singular/LocalHomology/FixedPointIndex.lean`.

## Main definitions

* `ContinuousMap.fixedPointIndex f`: the fixed-point index of `f : C(U, E)`.

## Main results

* `ContinuousMap.fixedPointIndex_eq_localDegree`: the index is the local degree at `0` of
  `x ↦ x - f x`, for any orientation of `E`.
* `ContinuousMap.fixedPointIndex_of_not_isCompact`,
  `ContinuousMap.fixedPointIndex_eq_zero_of_forall_ne`: the index vanishes when the fixed set is
  not compact, or empty.
* `ContinuousMap.fixedPointIndex_eq_sum_sign_det`, `ContinuousMap.fixedPointIndex_eq_sign_det`:
  the index is the signed count of nondegenerate fixed points.
* `ContinuousMap.fixedPointIndex_const_of_mem`: a constant map with value in `U` has index `1`.
* `ContinuousMap.fixedPointIndex_eq_of_homotopy`: homotopy invariance.
* `ContinuousMap.fixedPointIndex_comp_inclusion`: excision.
* `ContinuousMap.fixedPointIndex_eq_add`: additivity.

## References

* A. Dold, *Lectures on Algebraic Topology*, Springer, 1972, Chapter VII, §5 (the fixed-point
  index of a map of an open subset of `ℝⁿ`, defined through the map `x ↦ x - f x` on
  local homology, and its normalization, homotopy, excision and additivity properties).
-/

public section

noncomputable section

open Module Set TopologicalSpace Topology
open TauCeti TauCeti.HomologicalOrientation

namespace ContinuousMap

section SubtypeValSub

variable {E : Type*} [TopologicalSpace E] {U : Opens E}

/-- The map `x ↦ x - f x` of a map `f : U → E`, that is `ContinuousMap.subtypeVal U - f`. Its
zeros are the fixed points of `f` (`ContinuousMap.preimage_subtypeValSub_zero`). -/
def subtypeValSub [Sub E] [ContinuousSub E] (f : C(U, E)) : C(U, E) :=
  ⟨fun x ↦ (x : E) - f x, by fun_prop⟩

@[simp]
theorem subtypeValSub_apply [Sub E] [ContinuousSub E] (f : C(U, E)) (x : U) :
    f.subtypeValSub x = (x : E) - f x :=
  (rfl)

/-- The zeros of `x ↦ x - f x` are the fixed points of `f`. -/
@[simp]
theorem preimage_subtypeValSub_zero [AddGroup E] [ContinuousSub E] (f : C(U, E)) :
    f.subtypeValSub ⁻¹' {0} = {x | f x = x} := by
  ext x
  simp only [mem_preimage, subtypeValSub_apply, mem_singleton_iff, sub_eq_zero, mem_ofPred_eq]
  exact eq_comm

/-- The map `x ↦ x - f x` commutes with restriction to an open subset `V ⊆ U`. -/
@[simp]
theorem subtypeValSub_comp_inclusion [Sub E] [ContinuousSub E] {V : Opens E} (hVU : V ≤ U)
    (f : C(U, E)) :
    (f.comp (inclusion (SetLike.coe_subset_coe.2 hVU))).subtypeValSub =
      f.subtypeValSub.comp (inclusion (SetLike.coe_subset_coe.2 hVU)) := by
  ext x
  rw [comp_apply, subtypeValSub_apply, subtypeValSub_apply, comp_apply, inclusion_apply_coe]

end SubtypeValSub

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {U : Opens E}

/-- The **fixed-point index** of a continuous map `f : U → E` on an open subset `U` of a
finite-dimensional real normed space: the local degree at `0` of the map `x ↦ x - f x`,
whose zeros are the fixed points of `f`, for one orientation of `E` used on both sides. It is `0`
when the fixed set of `f` is not compact. It does not depend on the orientation
(`ContinuousMap.fixedPointIndex_eq_localDegree`). -/
def fixedPointIndex (f : C(U, E)) : ℤ :=
  let o := (nonempty_of_simplyConnectedSpace (M := E) (E := E) (d := finrank ℝ E) rfl).some
  (o.comap U.isOpenEmbedding').localDegree o rfl f.subtypeValSub 0

/-- **The fixed-point index does not depend on the orientation**: for every orientation `o` of
`E`, it is the local degree at `0` of the map `x ↦ x - f x`, for the orientation `o` on
the target and its restriction to `U` on the source. -/
theorem fixedPointIndex_eq_localDegree {n : ℕ} (o : HomologicalOrientation E E n)
    (hE : finrank ℝ E = n) (f : C(U, E)) :
    f.fixedPointIndex =
      (o.comap U.isOpenEmbedding').localDegree o hE f.subtypeValSub 0 := by
  subst hE
  rw [fixedPointIndex]
  rcases eq_or_eq_neg rfl (nonempty_of_simplyConnectedSpace (M := E) (E := E) rfl).some o with
    h | h
  · rw [h]
  · -- Reversing the orientation on both sides changes the local degree by `(-1)²`.
    rw [h, comap_neg, localDegree_neg_left _ _ _ rfl, localDegree_neg_right _ _ _ rfl, neg_neg]

/-- The fixed-point index vanishes when the fixed set is not compact. -/
@[simp]
theorem fixedPointIndex_of_not_isCompact {f : C(U, E)} (h : ¬IsCompact {x | f x = x}) :
    f.fixedPointIndex = 0 := by
  obtain ⟨o⟩ := nonempty_of_simplyConnectedSpace (M := E) (E := E) (d := finrank ℝ E) rfl
  rw [fixedPointIndex_eq_localDegree o rfl, localDegree_of_not_isCompact]
  rwa [preimage_subtypeValSub_zero]

/-- A map without fixed points has fixed-point index `0`. -/
@[simp]
theorem fixedPointIndex_eq_zero_of_forall_ne {f : C(U, E)} (h : ∀ x : U, f x ≠ x) :
    f.fixedPointIndex = 0 := by
  obtain ⟨o⟩ := nonempty_of_simplyConnectedSpace (M := E) (E := E) (d := finrank ℝ E) rfl
  rw [fixedPointIndex_eq_localDegree o rfl]
  exact localDegree_eq_zero_of_notMem_range _ _ _ rfl _ fun ⟨x, hx⟩ ↦ h x (sub_eq_zero.1 hx).symm

/-- A map on the empty open set has fixed-point index `0`. -/
theorem fixedPointIndex_of_isEmpty [IsEmpty U] (f : C(U, E)) : f.fixedPointIndex = 0 :=
  fixedPointIndex_eq_zero_of_forall_ne fun x ↦ isEmptyElim x

/-- A constant map with value outside `U` has no fixed point, so it has fixed-point index `0`. -/
@[simp]
theorem fixedPointIndex_const_of_notMem {c : E} (hc : c ∉ U) :
    (ContinuousMap.const U c).fixedPointIndex = 0 :=
  fixedPointIndex_eq_zero_of_forall_ne fun x (hx : c = x) ↦ hc (hx ▸ x.2)

/-- If `f` agrees on `U` with a map `φ : E → E` which is differentiable at `x ∈ U` with
`det (1 - Dφ(x)) ≠ 0`, the map `x ↦ x - f x` has local index `sign det (1 - Dφ(x))` at
`x`, for the orientation `o` of `E` on the target and its restriction to `U` on the source. -/
theorem _root_.TauCeti.HomologicalOrientation.localIndex_subtypeValSub_eq_sign_det {n : ℕ}
    (o : HomologicalOrientation E E n) (hE : finrank ℝ E = n) {f : C(U, E)} {φ : E → E}
    (hφ : ∀ z : U, φ z = f z) {φ' : E →L[ℝ] E} {x : U} (hd : HasFDerivAt φ φ' x)
    (hdet : (ContinuousLinearMap.id ℝ E - φ').det ≠ 0) :
    (o.comap U.isOpenEmbedding').localIndex o f.subtypeValSub x =
      SignType.sign (ContinuousLinearMap.id ℝ E - φ').det := by
  -- Read `x ↦ x - f x` as a map into the open set `E` itself, where the Jacobian formula for
  -- maps between open subsets applies.
  let g : C(U, (⊤ : Opens E)) := ⟨fun z ↦ ⟨(z : E) - f z, trivial⟩, by fun_prop⟩
  have h := localIndex_comap hE (o.comap U.isOpenEmbedding') o IsOpenEmbedding.id
    (⊤ : Opens E).isOpenEmbedding' (f := g) (g := f.subtypeValSub) (x := x)
    (Filter.Eventually.of_forall fun _ ↦ rfl)
  rw [comap_id, id_eq] at h
  rw [← h]
  exact o.localIndex_comap_eq_sign_det hE (φ := fun z ↦ z - φ z) (fun z ↦ by simp [g, hφ])
    ((hasFDerivAt_id _).sub hd) hdet

/-- **The fixed-point index counts nondegenerate fixed points with signs.** If `f` agrees on `U`
with a map `φ`, the fixed set of `f` is finite, and at each fixed point `x` the map `φ` is
differentiable with `det (1 - Dφ(x)) ≠ 0`, then the index is `∑_{f x = x} sign det (1 - Dφ(x))`. -/
theorem fixedPointIndex_eq_sum_sign_det {f : C(U, E)} {φ : E → E} (hφ : ∀ z : U, φ z = f z)
    {φ' : E → E →L[ℝ] E} (hfin : {x | f x = x}.Finite)
    (hd : ∀ x ∈ {x | f x = x}, HasFDerivAt φ (φ' x) x)
    (hdet : ∀ x ∈ {x | f x = x}, (ContinuousLinearMap.id ℝ E - φ' x).det ≠ 0) :
    f.fixedPointIndex =
      ∑ x ∈ hfin.toFinset, (SignType.sign (ContinuousLinearMap.id ℝ E - φ' x).det : ℤ) := by
  obtain ⟨o⟩ := nonempty_of_simplyConnectedSpace (M := E) (E := E) (d := finrank ℝ E) rfl
  have hpre := preimage_subtypeValSub_zero f
  rw [fixedPointIndex_eq_localDegree o rfl,
    localDegree_eq_sum_localIndex _ _ rfl rfl _ (hpre ▸ hfin)]
  refine Finset.sum_congr (by ext; simp [hpre]) fun x hx ↦ ?_
  rw [Finite.mem_toFinset] at hx
  exact o.localIndex_subtypeValSub_eq_sign_det rfl hφ (hd x hx) (hdet x hx)

/-- **The fixed-point index of a nondegenerate fixed point** is `sign det (1 - Dφ(x))`, when `x`
is the only fixed point of `f` and `f` agrees on `U` with a map `φ` differentiable at `x`. -/
theorem fixedPointIndex_eq_sign_det {f : C(U, E)} {φ : E → E} (hφ : ∀ z : U, φ z = f z)
    {φ' : E →L[ℝ] E} {x : U} (hfix : {x | f x = x} = {x}) (hd : HasFDerivAt φ φ' x)
    (hdet : (ContinuousLinearMap.id ℝ E - φ').det ≠ 0) :
    f.fixedPointIndex = SignType.sign (ContinuousLinearMap.id ℝ E - φ').det := by
  obtain ⟨o⟩ := nonempty_of_simplyConnectedSpace (M := E) (E := E) (d := finrank ℝ E) rfl
  rw [fixedPointIndex_eq_localDegree o rfl,
    localDegree_eq_localIndex _ _ rfl rfl _ ((preimage_subtypeValSub_zero f).trans hfix),
    o.localIndex_subtypeValSub_eq_sign_det rfl hφ hd hdet]

/-- **Normalization of the fixed-point index**: a constant map with value `c ∈ U` has fixed-point
index `1`. -/
@[simp]
theorem fixedPointIndex_const_of_mem {c : E} (hc : c ∈ U) :
    (ContinuousMap.const U c).fixedPointIndex = 1 := by
  have hfix : {x : U | ContinuousMap.const U c x = x} = {⟨c, hc⟩} := by
    ext x
    simp [Subtype.ext_iff, eq_comm]
  rw [fixedPointIndex_eq_sign_det (φ := fun _ ↦ c) (fun _ ↦ rfl) hfix (hasFDerivAt_const c _)
    (by simp [ContinuousLinearMap.det])]
  simp [ContinuousLinearMap.det]

/-- The zero map has fixed-point index `1` when `0 ∈ U`. -/
@[simp]
theorem fixedPointIndex_zero_of_mem (h : (0 : E) ∈ U) : (0 : C(U, E)).fixedPointIndex = 1 := by
  rw [← const_zero, fixedPointIndex_const_of_mem h]

/-- The zero map has fixed-point index `0` when `0 ∉ U`. -/
@[simp]
theorem fixedPointIndex_zero_of_notMem (h : (0 : E) ∉ U) : (0 : C(U, E)).fixedPointIndex = 0 := by
  rw [← const_zero, fixedPointIndex_const_of_notMem h]

/-- **Homotopy invariance of the fixed-point index.** Maps `f₀, f₁ : U → E` joined by a homotopy
`H` whose fixed set `{(t, x) | H (t, x) = x}` is compact have the same fixed-point index. -/
theorem fixedPointIndex_eq_of_homotopy {f₀ f₁ : C(U, E)} (H : f₀.Homotopy f₁)
    (hH : IsCompact {p : unitInterval × U | H p = p.2}) :
    f₀.fixedPointIndex = f₁.fixedPointIndex := by
  obtain ⟨o⟩ := nonempty_of_simplyConnectedSpace (M := E) (E := E) (d := finrank ℝ E) rfl
  -- The maps `x ↦ x - fᵢ x` are joined by `(t, x) ↦ x - H (t, x)`, whose zeros are the fixed
  -- points of `H`.
  let G : f₀.subtypeValSub.Homotopy f₁.subtypeValSub :=
    { toFun := fun p ↦ (p.2 : E) - H p
      continuous_toFun := by fun_prop
      map_zero_left := fun x ↦ by simp
      map_one_left := fun x ↦ by simp }
  have hG : G ⁻¹' {0} = {p | H p = p.2} := by
    ext p
    exact sub_eq_zero.trans eq_comm
  rw [fixedPointIndex_eq_localDegree o rfl, fixedPointIndex_eq_localDegree o rfl]
  exact localDegree_eq_of_homotopy _ _ _ rfl G (hG ▸ hH)

/-- The fixed-point index of the restriction of `f` to an open subset `V ⊆ U`, as the local degree
of `x ↦ x - f x` composed with the inclusion, for the orientation of `U` pulled back to
`V`. -/
private theorem fixedPointIndex_comp_inclusion_eq_localDegree {n : ℕ}
    (o : HomologicalOrientation E E n) (hE : finrank ℝ E = n) {V : Opens E} (hVU : V ≤ U)
    (f : C(U, E)) :
    (f.comp (inclusion (SetLike.coe_subset_coe.2 hVU))).fixedPointIndex =
      ((o.comap U.isOpenEmbedding').comap (j := Opens.inclusion hVU)
        (Opens.isOpenEmbedding_of_le hVU)).localDegree o hE
        (f.subtypeValSub.comp ⟨Opens.inclusion hVU, (Opens.isOpenEmbedding_of_le hVU).continuous⟩)
        0 := by
  have hincl : inclusion (SetLike.coe_subset_coe.2 hVU) =
      ⟨Opens.inclusion hVU, (Opens.isOpenEmbedding_of_le hVU).continuous⟩ := by
    ext x
    rw [inclusion_apply_coe, coe_mk]
  -- The orientation of `V` is the one of `U` pulled back along the inclusion, and the
  -- map `x ↦ x - f x` commutes with restriction.
  rw [comap_comap, o.comap_congr _ V.isOpenEmbedding'
      (Set.val_comp_inclusion (SetLike.coe_subset_coe.2 hVU)),
    fixedPointIndex_eq_localDegree o hE, subtypeValSub_comp_inclusion hVU, hincl]

/-- **Excision for the fixed-point index.** Restricting `f` to an open subset `V ⊆ U` containing
all fixed points of `f` does not change the fixed-point index. -/
theorem fixedPointIndex_comp_inclusion {V : Opens E} (hVU : V ≤ U) {f : C(U, E)}
    (hV : ∀ x : U, f x = x → (x : E) ∈ V) :
    (f.comp (inclusion (SetLike.coe_subset_coe.2 hVU))).fixedPointIndex =
      f.fixedPointIndex := by
  obtain ⟨o⟩ := nonempty_of_simplyConnectedSpace (M := E) (E := E) (d := finrank ℝ E) rfl
  rw [fixedPointIndex_comp_inclusion_eq_localDegree o rfl hVU,
    fixedPointIndex_eq_localDegree o rfl, localDegree_comap _ _ rfl rfl]
  rw [preimage_subtypeValSub_zero, Set.range_inclusion (SetLike.coe_subset_coe.2 hVU)]
  exact hV

/-- **Additivity of the fixed-point index.** If the fixed set of `f` is compact and covered by
open subsets `V` and `W` of `U` with no fixed point in both, the fixed-point index of `f` is the
sum of those of its restrictions to `V` and to `W`. -/
theorem fixedPointIndex_eq_add {V W : Opens E} (hVU : V ≤ U) (hWU : W ≤ U)
    {f : C(U, E)} (hc : IsCompact {x | f x = x})
    (hfix : ∀ x : U, f x = x → (x : E) ∈ V ∨ (x : E) ∈ W)
    (hVW : ∀ x : U, f x = x → (x : E) ∈ V → (x : E) ∉ W) :
    f.fixedPointIndex = (f.comp (inclusion (SetLike.coe_subset_coe.2 hVU))).fixedPointIndex +
      (f.comp (inclusion (SetLike.coe_subset_coe.2 hWU))).fixedPointIndex := by
  obtain ⟨o⟩ := nonempty_of_simplyConnectedSpace (M := E) (E := E) (d := finrank ℝ E) rfl
  rw [fixedPointIndex_comp_inclusion_eq_localDegree o rfl hVU,
    fixedPointIndex_comp_inclusion_eq_localDegree o rfl hWU,
    fixedPointIndex_eq_localDegree o rfl]
  refine localDegree_eq_add _ _ rfl rfl _ _ _ (preimage_subtypeValSub_zero f ▸ hc) ?_ ?_
  all_goals
    -- The ranges of the two inclusions are the points of `U` lying in `V` and in `W`.
    rw [preimage_subtypeValSub_zero, Set.range_inclusion (SetLike.coe_subset_coe.2 hVU),
      Set.range_inclusion (SetLike.coe_subset_coe.2 hWU)]
  · exact hfix
  · exact disjoint_left.2 fun x ⟨hx, hxV⟩ ⟨_, hxW⟩ ↦ hVW x hx hxV hxW

end ContinuousMap
