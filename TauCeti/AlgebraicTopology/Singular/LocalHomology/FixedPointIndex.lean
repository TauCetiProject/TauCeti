/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.LocalHomology.RegularValue
import Mathlib.Analysis.Convex.Contractible

/-!
# The local fixed-point index

Let `E` be a finite-dimensional real normed space, `U ⊆ E` open and `f : U → E` continuous. The
fixed points of `f` are the zeros of its displacement `x ↦ x - f x`. When the fixed set
`{x | f x = x}` is compact, the **fixed-point index** of `f` is the local degree of the
displacement at `0` (`TauCeti.HomologicalOrientation.localDegree`): the integer `i(f)` with

`(id - f)_*[U]_{Fix f} = i(f) • o 0`  in  `Hₙ(E, E ∖ {0}; ℤ)`,

where `[U]_{Fix f}` is the fundamental class of `U` along the fixed set. The same orientation `o`
of `E` is used on the source and on the target, so reversing it changes neither side and the
index does not depend on an orientation of `E`
(`ContinuousMap.fixedPointIndex_eq_localDegree`). By convention the index is `0` when the fixed
set is not compact. No differentiability of `f` and no finiteness of the fixed set is needed.

The index has the following properties.

* **Normalization at nondegenerate fixed points.** If `f` agrees on `U` with a map `φ` which is
  differentiable at a fixed point `x` with `det (1 - Dφ(x)) ≠ 0`, the local index of the
  displacement at `x` is `sign det (1 - Dφ(x))`
  (`ContinuousMap.localIndex_displacement_eq_sign_det`). So when the fixed set is finite and every
  fixed point is nondegenerate, the index is the signed count
  `∑_{f x = x} sign det (1 - Dφ(x))` (`ContinuousMap.fixedPointIndex_eq_sum_sign_det`).
* **Homotopy invariance.** Maps joined by a homotopy `H : [0, 1] × U → E` whose fixed set
  `{(t, x) | H (t, x) = x}` is compact have the same index
  (`ContinuousMap.fixedPointIndex_eq_of_homotopy`). For instance, if `U` has compact closure
  and `H` extends continuously to `[0, 1] × closure U` with no fixed point on the boundary, the
  fixed set is compact.
* **Excision.** Restricting `f` to an open subset containing all of its fixed points does not
  change the index (`ContinuousMap.fixedPointIndex_comp_inclusion`); with homotopy invariance,
  the index of an isolated fixed set does not depend on the isolating neighbourhood.
* **Additivity.** If the fixed set is covered by disjoint open sets `V` and `W`, the index is the
  sum of the indices of the restrictions to `V` and to `W`
  (`ContinuousMap.fixedPointIndex_eq_add`).
* A map without fixed points has index `0` (`ContinuousMap.fixedPointIndex_eq_zero_of_forall_ne`).

Together, these compute the index of a degenerate map as the signed count of the fixed points of
a nondegenerate map joined to it by a homotopy with compact fixed set, such as a small
perturbation that keeps the boundary of an isolating neighbourhood free of fixed points. For
example, on `ℝ` the degenerate fixed point `0`
of `x ↦ x + x³` has index `-1`: the homotopy `x ↦ x + x³ + t x`, `t ∈ [0, 1]`, has `0` as its only
fixed point, and ends at a map whose derivative at `0` is `2`, with `sign (1 - 2) = -1`
(`TauCeti.fixedPointIndex_add_pow_three`).

## Main definitions

* `ContinuousMap.fixedPointIndex f`: the fixed-point index of `f : C(U, E)`.

## Main results

* `ContinuousMap.fixedPointIndex_eq_localDegree`: the index is the local degree at `0` of the
  displacement, for any orientation of `E`.
* `ContinuousMap.fixedPointIndex_of_not_isCompact`,
  `ContinuousMap.fixedPointIndex_eq_zero_of_forall_ne`: the index vanishes when the fixed set is
  not compact, or empty.
* `ContinuousMap.fixedPointIndex_eq_sum_sign_det`, `ContinuousMap.fixedPointIndex_eq_sign_det`:
  the index is the signed count of nondegenerate fixed points.
* `ContinuousMap.fixedPointIndex_eq_of_homotopy`: homotopy invariance.
* `ContinuousMap.fixedPointIndex_comp_inclusion`: excision.
* `ContinuousMap.fixedPointIndex_eq_add`: additivity.
* `TauCeti.fixedPointIndex_add_pow_three`: the degenerate fixed point `0` of `x ↦ x + x³` on `ℝ`
  has index `-1`.

## References

* A. Dold, *Lectures on Algebraic Topology*, Springer, 1972, Chapter VII, §5 (the fixed-point
  index of a map of an open subset of `ℝⁿ`, defined through the displacement `x ↦ x - f x` on
  local homology, and its normalization, homotopy, excision and additivity properties).
-/

public section

noncomputable section

open Module Set TopologicalSpace Topology
open TauCeti TauCeti.HomologicalOrientation

namespace ContinuousMap

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {U : Opens E}

/-- The **displacement** `x ↦ x - f x` of a map `f : U → E`. Its zeros are the fixed points of
`f` (`ContinuousMap.preimage_displacement_zero`). -/
def displacement (f : C(U, E)) : C(U, E) :=
  ⟨fun x ↦ (x : E) - f x, by fun_prop⟩

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
@[simp]
theorem displacement_apply (f : C(U, E)) (x : U) : f.displacement x = (x : E) - f x :=
  (rfl)

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
/-- The zeros of the displacement `x ↦ x - f x` are the fixed points of `f`. -/
theorem preimage_displacement_zero (f : C(U, E)) : f.displacement ⁻¹' {0} = {x | f x = x} := by
  ext x
  simp only [mem_preimage, displacement_apply, mem_singleton_iff, sub_eq_zero, mem_ofPred_eq]
  exact eq_comm

/-- The **fixed-point index** of a continuous map `f : U → E` on an open subset `U` of a
finite-dimensional real normed space: the local degree at `0` of the displacement `x ↦ x - f x`,
whose zeros are the fixed points of `f`, for one orientation of `E` used on both sides. It is `0`
when the fixed set of `f` is not compact. It does not depend on the orientation
(`ContinuousMap.fixedPointIndex_eq_localDegree`). -/
def fixedPointIndex (f : C(U, E)) : ℤ :=
  let o := (nonempty_of_simplyConnectedSpace (M := E) (E := E) (d := finrank ℝ E) rfl).some
  (o.comap U.isOpenEmbedding').localDegree o rfl f.displacement 0

/-- **The fixed-point index does not depend on the orientation**: for every orientation `o` of
`E`, it is the local degree at `0` of the displacement `x ↦ x - f x`, for the orientation `o` on
the target and its restriction to `U` on the source. -/
theorem fixedPointIndex_eq_localDegree {n : ℕ} (o : HomologicalOrientation E E n)
    (hE : finrank ℝ E = n) (f : C(U, E)) :
    f.fixedPointIndex =
      (o.comap U.isOpenEmbedding').localDegree o hE f.displacement 0 := by
  subst hE
  rw [fixedPointIndex]
  rcases eq_or_eq_neg rfl (nonempty_of_simplyConnectedSpace (M := E) (E := E) rfl).some o with
    h | h
  · rw [h]
  · -- Reversing the orientation on both sides changes the local degree by `(-1)²`.
    rw [h, comap_neg, localDegree_neg_left _ _ _ rfl, localDegree_neg_right _ _ _ rfl, neg_neg]

/-- The fixed-point index vanishes when the fixed set is not compact. -/
theorem fixedPointIndex_of_not_isCompact {f : C(U, E)} (h : ¬IsCompact {x | f x = x}) :
    f.fixedPointIndex = 0 := by
  obtain ⟨o⟩ := nonempty_of_simplyConnectedSpace (M := E) (E := E) (d := finrank ℝ E) rfl
  rw [fixedPointIndex_eq_localDegree o rfl, localDegree_of_not_isCompact]
  rwa [preimage_displacement_zero]

/-- A map without fixed points has fixed-point index `0`. -/
theorem fixedPointIndex_eq_zero_of_forall_ne {f : C(U, E)} (h : ∀ x : U, f x ≠ x) :
    f.fixedPointIndex = 0 := by
  obtain ⟨o⟩ := nonempty_of_simplyConnectedSpace (M := E) (E := E) (d := finrank ℝ E) rfl
  rw [fixedPointIndex_eq_localDegree o rfl]
  exact localDegree_eq_zero_of_notMem_range _ _ _ rfl _ fun ⟨x, hx⟩ ↦ h x (sub_eq_zero.1 hx).symm

/-- At a fixed point `x` where `f` agrees with a map `φ` differentiable at `x` with
`det (1 - Dφ(x)) ≠ 0`, the displacement has local index `sign det (1 - Dφ(x))`. -/
theorem localIndex_displacement_eq_sign_det {n : ℕ} (o : HomologicalOrientation E E n)
    (hE : finrank ℝ E = n) {f : C(U, E)} {φ : E → E} (hφ : ∀ z : U, φ z = f z)
    {φ' : E →L[ℝ] E} {x : U} (hd : HasFDerivAt φ φ' x)
    (hdet : (ContinuousLinearMap.id ℝ E - φ').det ≠ 0) :
    (o.comap U.isOpenEmbedding').localIndex o f.displacement x =
      SignType.sign (ContinuousLinearMap.id ℝ E - φ').det := by
  -- Read the displacement as a map into the open set `E` itself, where the Jacobian formula for
  -- maps between open subsets applies.
  let g : C(U, (⊤ : Opens E)) := ⟨fun z ↦ ⟨(z : E) - f z, trivial⟩, by fun_prop⟩
  have h := localIndex_comap hE (o.comap U.isOpenEmbedding') o IsOpenEmbedding.id
    (⊤ : Opens E).isOpenEmbedding' (f := g) (g := f.displacement) (x := x)
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
  have hpre := preimage_displacement_zero f
  rw [fixedPointIndex_eq_localDegree o rfl,
    localDegree_eq_sum_localIndex _ _ rfl rfl _ (hpre ▸ hfin)]
  refine Finset.sum_congr (by ext; simp [hpre]) fun x hx ↦ ?_
  rw [Finite.mem_toFinset] at hx
  exact localIndex_displacement_eq_sign_det o rfl hφ (hd x hx) (hdet x hx)

/-- **The fixed-point index of a nondegenerate fixed point** is `sign det (1 - Dφ(x))`, when `x`
is the only fixed point of `f` and `f` agrees on `U` with a map `φ` differentiable at `x`. -/
theorem fixedPointIndex_eq_sign_det {f : C(U, E)} {φ : E → E} (hφ : ∀ z : U, φ z = f z)
    {φ' : E →L[ℝ] E} {x : U} (hfix : {x | f x = x} = {x}) (hd : HasFDerivAt φ φ' x)
    (hdet : (ContinuousLinearMap.id ℝ E - φ').det ≠ 0) :
    f.fixedPointIndex = SignType.sign (ContinuousLinearMap.id ℝ E - φ').det := by
  have hfin : {x | f x = x}.Finite := hfix ▸ finite_singleton x
  rw [fixedPointIndex_eq_sum_sign_det hφ (φ' := fun _ ↦ φ') hfin
    (fun z hz ↦ by rw [hfix, mem_singleton_iff] at hz; exact hz ▸ hd) fun _ _ ↦ hdet]
  have hs : hfin.toFinset = {x} := by ext; simp [hfix]
  rw [hs, Finset.sum_singleton]

/-- **Homotopy invariance of the fixed-point index.** Maps `f₀, f₁ : U → E` joined by a homotopy
`H` whose fixed set `{(t, x) | H (t, x) = x}` is compact have the same fixed-point index. -/
theorem fixedPointIndex_eq_of_homotopy {f₀ f₁ : C(U, E)} (H : f₀.Homotopy f₁)
    (hH : IsCompact {p : unitInterval × U | H p = p.2}) :
    f₀.fixedPointIndex = f₁.fixedPointIndex := by
  obtain ⟨o⟩ := nonempty_of_simplyConnectedSpace (M := E) (E := E) (d := finrank ℝ E) rfl
  -- The displacements are joined by the displacement of `H`, whose zeros are its fixed points.
  let G : f₀.displacement.Homotopy f₁.displacement :=
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
of the displacement of `f` composed with the inclusion, for the orientation of `U` pulled back to
`V`. -/
private theorem fixedPointIndex_comp_inclusion_eq_localDegree {n : ℕ}
    (o : HomologicalOrientation E E n) (hE : finrank ℝ E = n) {V : Opens E} (hVU : V ≤ U)
    (hj : IsOpenEmbedding (Opens.inclusion hVU)) (f : C(U, E)) :
    (f.comp ⟨Opens.inclusion hVU, continuous_inclusion hVU⟩).fixedPointIndex =
      ((o.comap U.isOpenEmbedding').comap hj).localDegree o hE
        (f.displacement.comp ⟨Opens.inclusion hVU, hj.continuous⟩) 0 := by
  -- The orientation of `V` is the one of `U` pulled back along the inclusion, and the
  -- displacement commutes with restriction.
  rw [comap_comap, o.comap_congr _ V.isOpenEmbedding' rfl, fixedPointIndex_eq_localDegree o hE]
  exact congrArg (fun g ↦ (o.comap V.isOpenEmbedding').localDegree o hE g 0)
    (ContinuousMap.ext fun _ ↦ rfl)

/-- **Excision for the fixed-point index.** Restricting `f` to an open subset `V ⊆ U` containing
all fixed points of `f` does not change the fixed-point index. -/
theorem fixedPointIndex_comp_inclusion {V : Opens E} (hVU : V ≤ U) {f : C(U, E)}
    (hV : ∀ x : U, f x = x → (x : E) ∈ V) :
    (f.comp ⟨Opens.inclusion hVU, continuous_inclusion hVU⟩).fixedPointIndex =
      f.fixedPointIndex := by
  obtain ⟨o⟩ := nonempty_of_simplyConnectedSpace (M := E) (E := E) (d := finrank ℝ E) rfl
  rw [fixedPointIndex_comp_inclusion_eq_localDegree o rfl hVU (Opens.isOpenEmbedding_of_le hVU),
    fixedPointIndex_eq_localDegree o rfl, localDegree_comap _ _ rfl rfl]
  intro x hx
  rw [preimage_displacement_zero] at hx
  exact ⟨⟨x, hV x hx⟩, rfl⟩

/-- **Additivity of the fixed-point index.** If the fixed set of `f` is compact and covered by
disjoint open subsets `V` and `W` of `U`, the fixed-point index of `f` is the sum of those of its
restrictions to `V` and to `W`. -/
theorem fixedPointIndex_eq_add {V W : Opens E} (hVU : V ≤ U) (hWU : W ≤ U) (hVW : Disjoint V W)
    {f : C(U, E)} (hc : IsCompact {x | f x = x})
    (hfix : ∀ x : U, f x = x → (x : E) ∈ V ∨ (x : E) ∈ W) :
    f.fixedPointIndex = (f.comp ⟨Opens.inclusion hVU, continuous_inclusion hVU⟩).fixedPointIndex +
      (f.comp ⟨Opens.inclusion hWU, continuous_inclusion hWU⟩).fixedPointIndex := by
  obtain ⟨o⟩ := nonempty_of_simplyConnectedSpace (M := E) (E := E) (d := finrank ℝ E) rfl
  have hV : IsOpenEmbedding (Opens.inclusion hVU) := Opens.isOpenEmbedding_of_le hVU
  have hW : IsOpenEmbedding (Opens.inclusion hWU) := Opens.isOpenEmbedding_of_le hWU
  rw [fixedPointIndex_comp_inclusion_eq_localDegree o rfl hVU hV,
    fixedPointIndex_comp_inclusion_eq_localDegree o rfl hWU hW,
    fixedPointIndex_eq_localDegree o rfl]
  refine localDegree_eq_add _ _ rfl rfl hV hW ?_ _ (preimage_displacement_zero f ▸ hc) ?_
  · -- The ranges of the two inclusions are the points of `U` lying in `V` and in `W`.
    refine Set.disjoint_left.2 ?_
    rintro _ ⟨a, rfl⟩ ⟨b, hb⟩
    exact Set.disjoint_left.1 (Opens.coe_disjoint.2 hVW) a.2 (congrArg Subtype.val hb ▸ b.2)
  · intro x hx
    rw [preimage_displacement_zero] at hx
    rcases hfix x hx with h | h
    · exact Or.inl ⟨⟨x, h⟩, rfl⟩
    · exact Or.inr ⟨⟨x, h⟩, rfl⟩

end ContinuousMap

namespace TauCeti

/-- On `ℝ`, the degenerate fixed point `0` of `x ↦ x + x³` has fixed-point index `-1`. The
homotopy `x ↦ x + x³ + t x`, `t ∈ [0, 1]`, has `0` as its only fixed point, and ends at a map with
nondegenerate fixed point `0` and derivative `2` there, of sign `sign (1 - 2) = -1`. -/
theorem fixedPointIndex_add_pow_three :
    (⟨fun x ↦ (x : ℝ) + (x : ℝ) ^ 3, by fun_prop⟩ : C((⊤ : Opens ℝ), ℝ)).fixedPointIndex = -1 := by
  let H : ContinuousMap.Homotopy
      (⟨fun x ↦ (x : ℝ) + (x : ℝ) ^ 3, by fun_prop⟩ : C((⊤ : Opens ℝ), ℝ))
      ⟨fun x ↦ (x : ℝ) + (x : ℝ) ^ 3 + x, by fun_prop⟩ :=
    { toFun := fun p ↦ (p.2 : ℝ) + (p.2 : ℝ) ^ 3 + (p.1 : ℝ) * p.2
      continuous_toFun := by fun_prop
      map_zero_left := fun x ↦ by simp
      map_one_left := fun x ↦ by simp }
  -- A fixed point `x` of `x ↦ x + x³ + t x` satisfies `x (x² + t) = 0` with `t ≥ 0`, so `x = 0`.
  have hfix : ∀ (t : unitInterval) (x : (⊤ : Opens ℝ)),
      (x : ℝ) + (x : ℝ) ^ 3 + (t : ℝ) * x = x ↔ (x : ℝ) = 0 := by
    intro t x
    constructor
    · intro h
      have h' : (x : ℝ) * ((x : ℝ) ^ 2 + t) = 0 := by linear_combination h
      rcases mul_eq_zero.1 h' with h0 | h0
      · exact h0
      · nlinarith [sq_nonneg (x : ℝ), t.2.1]
    · intro h
      simp [h]
  have hH : {p : unitInterval × (⊤ : Opens ℝ) | H p = p.2} = univ ×ˢ {⟨0, trivial⟩} := by
    ext p
    simp only [mem_ofPred_eq, mem_prod, mem_univ, mem_singleton_iff, true_and, Subtype.ext_iff]
    exact hfix p.1 p.2
  rw [ContinuousMap.fixedPointIndex_eq_of_homotopy H (hH ▸ isCompact_univ.prod isCompact_singleton)]
  -- The derivative of `x ↦ x + x³ + x` at `0` is `2`, and `sign det (1 - 2) = -1`.
  have hd : HasDerivAt (fun x : ℝ ↦ x + x ^ 3 + x) 2 0 := by
    have := ((hasDerivAt_id' (0 : ℝ)).add ((hasDerivAt_id' (0 : ℝ)).pow 3)).add
      (hasDerivAt_id' (0 : ℝ))
    norm_num at this
    exact this
  have hdet : (ContinuousLinearMap.id ℝ ℝ - ContinuousLinearMap.toSpanSingleton ℝ 2).det = -1 := by
    rw [ContinuousLinearMap.det, LinearMap.det_ring]
    norm_num
  rw [ContinuousMap.fixedPointIndex_eq_sign_det (φ := fun x : ℝ ↦ x + x ^ 3 + x) (fun _ ↦ rfl)
    (x := ⟨0, trivial⟩) ?_ hd.hasFDerivAt (by rw [hdet]; norm_num), hdet]
  · simp
  · ext x
    simpa [Subtype.ext_iff] using hfix 1 x

end TauCeti
