/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Toric.Delzant.Basic

import Mathlib.LinearAlgebra.Dimension.OrzechProperty
import Mathlib.LinearAlgebra.StdBasis
import TauCeti.Algebra.Group.Pi.Lemmas
import TauCeti.LinearAlgebra.Pi

/-!
# The standard simplex as a Delzant polytope

The moment polytope of complex projective space `ℂPⁿ`, for the action of the torus `Tⁿ` rotating
the last `n` homogeneous coordinates, is a standard simplex. On `ℝ^κ` with its integral lattice
`ℤ^κ` (`(Int.castAddHom ℝ).compLeft κ`), the inward normals

* `e k` for each `k : κ`, with support constant `0`, and
* `-∑ k, e k = -1`, with support constant `-a`,

(`TauCeti.Toric.simplexNormal κ` and `TauCeti.Toric.simplexSupport a`, indexed by `Option κ`)
cut out the simplex

`{x ∈ (ℝ^κ)* | 0 ≤ x (e k) for every k, and ∑ k, x (e k) ≤ a}`

(`TauCeti.Toric.mem_facetPolyhedron_simplex_iff`). It is bounded, since its points have norm at
most `|a|` (`TauCeti.Toric.isBounded_facetPolyhedron_simplex`). For `a > 0` and `κ` nonempty
this is a Delzant polytope (`TauCeti.Toric.isDelzant_simplex`). Each of its `#κ + 1` facets is cut
out by one of the normals. At a vertex all constraints but one are active: if two constraints
`o₁ ≠ o₂` were inactive, a nonzero functional on `ℝ^κ` (a coordinate, or a difference of two
coordinates) would vanish on all the active normals. Any `#κ` of the `#κ + 1` normals generate
`ℤ^κ`, since the missing one is minus the sum of the others when it is `-1`, and is recovered as
`e k = -(-1) - ∑_{m ≠ k} e m` otherwise. Having `#κ = rank ℤ^κ` elements, they then form a basis
of `ℤ^κ`.

## Main definitions

* `TauCeti.Toric.simplexNormal κ`: the normals `e k` and `-1` of the standard simplex.
* `TauCeti.Toric.simplexSupport a`: the support constants `0` and `-a`.

## Main results

* `TauCeti.Toric.mem_facetPolyhedron_simplex_iff`: the polyhedron is the simplex of size `a`.
* `TauCeti.Toric.none_mem_activeSet_simplex_iff`, `TauCeti.Toric.some_mem_activeSet_simplex_iff`:
  the facets of the simplex.
* `TauCeti.Toric.isBounded_facetPolyhedron_simplex`: the simplex is bounded.
* `TauCeti.Toric.isDelzant_simplex`: for `a > 0` and `κ` nonempty it is a Delzant polytope.

## References

* A. Cannas da Silva, *Lectures on Symplectic Geometry*, Lecture Notes in Mathematics 1764,
  Springer, 2001, Sections 27 and 28.
* V. Guillemin, *Moment Maps and Combinatorial Invariants of Hamiltonian `T^n`-spaces*,
  Birkhäuser, 1994, Chapter 1.
-/

public section

noncomputable section

open Set

namespace TauCeti.Toric

variable {κ : Type*}

/-- The support constants of the standard simplex of size `a`: `-a` for the facet with normal
`-1`, indexed by `none`, and `0` for the coordinate facets. -/
def simplexSupport (a : ℝ) : Option κ → ℝ
  | none => -a
  | some _ => 0

@[simp]
theorem simplexSupport_none (a : ℝ) : simplexSupport (κ := κ) a none = -a :=
  (rfl)

@[simp]
theorem simplexSupport_some (a : ℝ) (k : κ) : simplexSupport a (some k) = 0 :=
  (rfl)

variable [DecidableEq κ]

variable (κ) in
/-- The inward facet normals of the standard simplex in `ℝ^κ`: the coordinate vectors `e k` of
`ℤ^κ`, indexed by `some k`, and `-∑ k, e k = -1`, indexed by `none`. -/
def simplexNormal : Option κ → κ → ℤ
  | none => -1
  | some k => Pi.single k 1

@[simp]
theorem simplexNormal_none : simplexNormal κ none = -1 :=
  (rfl)

@[simp]
theorem simplexNormal_some (k : κ) : simplexNormal κ (some k) = Pi.single k 1 :=
  (rfl)

/-- Any two of the normals can be omitted by a nonzero functional on `ℝ^κ` vanishing on all the
others: a coordinate, or a difference of two coordinates. -/
private theorem exists_ne_zero_forall_apply_simplexNormal_eq_zero {o₁ o₂ : Option κ}
    (h : o₁ ≠ o₂) : ∃ w : StrongDual ℝ (κ → ℝ), w ≠ 0 ∧ ∀ o, o ≠ o₁ → o ≠ o₂ →
      w ((Int.castAddHom ℝ).compLeft κ (simplexNormal κ o)) = 0 := by
  let p (k : κ) : StrongDual ℝ (κ → ℝ) := ContinuousLinearMap.proj k
  have hp (k : κ) : p k ≠ 0 := fun h ↦ by simpa [p] using congrArg (· (Pi.single k 1)) h
  match o₁, o₂ with
  | none, none => exact absurd rfl h
  | none, some l =>
    refine ⟨p l, hp l, fun o h₁ h₂ ↦ ?_⟩
    obtain ⟨m, rfl⟩ := Option.ne_none_iff_exists'.1 h₁
    simp [p, show m ≠ l by rintro rfl; exact h₂ rfl]
  | some k, none =>
    refine ⟨p k, hp k, fun o h₁ h₂ ↦ ?_⟩
    obtain ⟨m, rfl⟩ := Option.ne_none_iff_exists'.1 h₂
    simp [p, show m ≠ k by rintro rfl; exact h₁ rfl]
  | some k, some l =>
    have hkl : k ≠ l := fun hkl ↦ h (hkl ▸ rfl)
    refine ⟨p k - p l, fun h ↦ ?_, fun o h₁ h₂ ↦ ?_⟩
    · simpa [p, hkl] using congrArg (· (Pi.single k 1)) h
    cases o with
    | none => simp [p]
    | some m =>
      simp [p, show m ≠ k by rintro rfl; exact h₁ rfl,
        show m ≠ l by rintro rfl; exact h₂ rfl]

/-- The normals other than `simplexNormal κ o` generate `ℤ^κ`. -/
private theorem span_simplexNormal_compl [Finite κ] (o : Option κ) :
    Submodule.span ℤ (simplexNormal κ '' {o}ᶜ) = ⊤ := by
  have := Fintype.ofFinite κ
  set S := Submodule.span ℤ (simplexNormal κ '' {o}ᶜ)
  have hmem {o'} (h : o' ≠ o) : simplexNormal κ o' ∈ S := Submodule.subset_span ⟨o', h, rfl⟩
  have hsingle (k : κ) (hk : some k ≠ o) : Pi.single k (1 : ℤ) ∈ S := hmem hk
  rw [eq_top_iff, ← (Pi.basisFun ℤ κ).span_eq, Submodule.span_le]
  rintro _ ⟨k, rfl⟩
  rw [Pi.basisFun_apply]
  by_cases hk : some k = o
  · -- The omitted normal is `e k`, which is `-(-1) - ∑_{m ≠ k} e m`.
    subst hk
    have hsum : Pi.single k (1 : ℤ) + ∑ m ∈ Finset.univ.erase k, (Pi.single m 1 : κ → ℤ) = 1 := by
      rw [Finset.add_sum_erase _ (fun m ↦ (Pi.single m 1 : κ → ℤ)) (Finset.mem_univ k)]
      simpa using Finset.univ_sum_single (1 : κ → ℤ)
    rw [SetLike.mem_coe, eq_sub_iff_add_eq.2 hsum]
    refine S.sub_mem (by simpa using S.neg_mem (hmem (o' := none) (by simp))) ?_
    exact S.sum_mem fun m hm ↦ hsingle m (by simpa using Finset.ne_of_mem_erase hm)
  · exact hsingle k hk

variable [Fintype κ]

/-- A functional on `ℝ^κ` sends the image `1` of `1 ∈ ℤ^κ` to the sum of its values on the
coordinate vectors. -/
private theorem apply_compLeft_one (x : StrongDual ℝ (κ → ℝ)) :
    x ((Int.castAddHom ℝ).compLeft κ 1) = ∑ k, x (Pi.single k 1) := by
  rw [show (Int.castAddHom ℝ).compLeft κ 1 = 1 by ext; simp]
  simpa using (x : (κ → ℝ) →ₗ[ℝ] ℝ).pi_apply_eq_sum_single 1

/-- **The standard simplex.** The polyhedron cut out by the normals `e k` and `-1` with support
constants `0` and `-a` is the simplex `{x | 0 ≤ x (e k) for every k, and ∑ k, x (e k) ≤ a}`. -/
theorem mem_facetPolyhedron_simplex_iff {a : ℝ} {x : StrongDual ℝ (κ → ℝ)} :
    x ∈ facetPolyhedron ((Int.castAddHom ℝ).compLeft κ) (simplexNormal κ) (simplexSupport a) ↔
      (∀ k, 0 ≤ x (Pi.single k 1)) ∧ ∑ k, x (Pi.single k 1) ≤ a := by
  simp [Option.forall, apply_compLeft_one, and_comm]

/-- The slanted facet `∑ k, x (e k) = a` of the simplex. -/
theorem none_mem_activeSet_simplex_iff {a : ℝ} {x : StrongDual ℝ (κ → ℝ)} :
    none ∈ activeSet (facetPairing ((Int.castAddHom ℝ).compLeft κ) (simplexNormal κ))
      (simplexSupport a) x ↔ ∑ k, x (Pi.single k 1) = a := by
  simp [apply_compLeft_one]

/-- The coordinate facet `x (e k) = 0` of the simplex. -/
theorem some_mem_activeSet_simplex_iff {a : ℝ} {x : StrongDual ℝ (κ → ℝ)} {k : κ} :
    some k ∈ activeSet (facetPairing ((Int.castAddHom ℝ).compLeft κ) (simplexNormal κ))
      (simplexSupport a) x ↔ x (Pi.single k 1) = 0 := by
  simp

/-- **The simplex is bounded.** Its points have norm at most `|a|`. -/
theorem isBounded_facetPolyhedron_simplex (a : ℝ) :
    Bornology.IsBounded
      (facetPolyhedron ((Int.castAddHom ℝ).compLeft κ) (simplexNormal κ) (simplexSupport a)) := by
  refine (Metric.isBounded_iff_subset_closedBall 0).2 ⟨|a|, fun x hx ↦ ?_⟩
  obtain ⟨hx₀, hxa⟩ := mem_facetPolyhedron_simplex_iff.1 hx
  rw [Metric.mem_closedBall, dist_zero_right]
  refine ContinuousLinearMap.opNorm_le_bound x (abs_nonneg a) fun v ↦ ?_
  have hxv : x v = ∑ k, v k * x (Pi.single k 1) := by
    simpa using (x : (κ → ℝ) →ₗ[ℝ] ℝ).pi_apply_eq_sum_single v
  rw [hxv, mul_comm |a|]
  calc ‖∑ k, v k * x (Pi.single k 1)‖ ≤ ∑ k, ‖v‖ * x (Pi.single k 1) := by
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ ↦ ?_)
        rw [norm_mul, Real.norm_of_nonneg (hx₀ k)]
        exact mul_le_mul_of_nonneg_right (norm_le_pi_norm v k) (hx₀ k)
    _ ≤ ‖v‖ * |a| := by
        rw [← Finset.mul_sum]
        exact mul_le_mul_of_nonneg_left (hxa.trans (le_abs_self a)) (norm_nonneg v)

/-- At a vertex of the simplex, all constraints but one are active. -/
private theorem exists_activeSet_eq_compl_of_mem_extremePoints {a : ℝ} (ha : a ≠ 0)
    {x : StrongDual ℝ (κ → ℝ)} (hx : x ∈ (facetPolyhedron ((Int.castAddHom ℝ).compLeft κ)
      (simplexNormal κ) (simplexSupport a)).extremePoints ℝ) :
    ∃ o, activeSet (facetPairing ((Int.castAddHom ℝ).compLeft κ) (simplexNormal κ))
      (simplexSupport a) x = {o}ᶜ := by
  obtain ⟨-, hker⟩ := mem_extremePoints_facetPolyhedron_iff.1 hx
  set A := activeSet (facetPairing ((Int.castAddHom ℝ).compLeft κ) (simplexNormal κ))
    (simplexSupport a) x
  -- Not every constraint is active: otherwise `∑ k, x (e k)` would be both `0` and `a`.
  obtain ⟨o, ho⟩ : ∃ o, o ∉ A := by
    by_contra! hall
    have h₀ : ∀ k, x (Pi.single k 1) = 0 := fun k ↦ some_mem_activeSet_simplex_iff.1 (hall _)
    exact ha (by simpa [h₀] using (none_mem_activeSet_simplex_iff.1 (hall none)).symm)
  -- Two inactive constraints would leave a nonzero functional vanishing on the active normals.
  refine ⟨o, Set.ext fun o' ↦ ⟨fun h₁ h₂ ↦ ho (h₂ ▸ h₁), fun h₁ ↦ ?_⟩⟩
  by_contra h₂
  obtain ⟨w, hw, hw₀⟩ := exists_ne_zero_forall_apply_simplexNormal_eq_zero h₁
  exact hw (hker w fun j hj ↦ hw₀ j (fun h ↦ h₂ (h ▸ hj)) fun h ↦ ho (h ▸ hj))

/-- A point at which all constraints but one are active is a smooth vertex: the remaining `#κ`
normals form a basis of `ℤ^κ`. -/
private theorem isSmoothVertex_simplex_of_activeSet_eq_compl {a : ℝ}
    {x : StrongDual ℝ (κ → ℝ)} {o : Option κ}
    (hx : activeSet (facetPairing ((Int.castAddHom ℝ).compLeft κ) (simplexNormal κ))
      (simplexSupport a) x = {o}ᶜ) :
    IsSmoothVertex ((Int.castAddHom ℝ).compLeft κ) (simplexNormal κ) (simplexSupport a) x := by
  rw [isSmoothVertex_iff_linearIndepOn, hx]
  refine ⟨linearIndependent_of_top_le_span_of_card_eq_finrank ?_ ?_, span_simplexNormal_compl o⟩
  · rw [← image_eq_range, span_simplexNormal_compl]
  · rw [Module.finrank_fintype_fun_eq_card, Fintype.card_compl_set, Fintype.card_option,
      Set.card_singleton, Nat.add_sub_cancel]

/-- **The standard simplex is a Delzant polytope.** For `a > 0` and `κ` nonempty, the simplex
`{x | 0 ≤ x (e k), ∑ k, x (e k) ≤ a}` cut out by the normals `e k` and `-1` of `ℤ^κ` is a Delzant
polytope: the moment polytope of `ℂPⁿ` for `n = #κ`. -/
theorem isDelzant_simplex [Nonempty κ] {a : ℝ} (ha : 0 < a) :
    IsDelzant ((Int.castAddHom ℝ).compLeft κ) (simplexNormal κ) (simplexSupport a) := by
  -- The point with coordinates `y`.
  let pt (y : κ → ℝ) : StrongDual ℝ (κ → ℝ) := ∑ k, y k • ContinuousLinearMap.proj k
  have hpt (y : κ → ℝ) (m : κ) : pt y (Pi.single m 1) = y m := by
    simp [pt, Pi.single_apply]
  have hn : (0 : ℝ) < Fintype.card κ := Nat.cast_pos.2 Fintype.card_pos
  refine ⟨isBounded_facetPolyhedron_simplex a, fun x hx ↦ ?_, fun o ↦ ?_⟩
  · obtain ⟨o, ho⟩ := exists_activeSet_eq_compl_of_mem_extremePoints ha.ne' hx
    exact isSmoothVertex_simplex_of_activeSet_eq_compl ho
  · cases o with
    | none =>
      -- The barycentre of the facet `∑ k, x (e k) = a`.
      refine ⟨pt fun _ ↦ a / Fintype.card κ, mem_facetPolyhedron_simplex_iff.2 ⟨fun k ↦ ?_, ?_⟩,
        Set.ext fun o ↦ ?_⟩
      · rw [hpt]; positivity
      · simp [hpt, mul_div_cancel₀ _ hn.ne']
      · cases o with
        | none => simp [apply_compLeft_one, hpt, mul_div_cancel₀ _ hn.ne']
        | some k => simp [hpt, ha.ne', hn.ne']
    | some k =>
      -- A point with `x (e k) = 0` and all other coordinates equal to `a / (#κ + 1)`.
      set b := a / (Fintype.card κ + 1)
      have hb : 0 < b := by positivity
      have hsum : ∑ m, pt (fun m ↦ if m = k then 0 else b) (Pi.single m 1) < a := by
        calc ∑ m, pt (fun m ↦ if m = k then 0 else b) (Pi.single m 1) ≤ ∑ _m : κ, b := by
              refine Finset.sum_le_sum fun m _ ↦ ?_
              rw [hpt]
              split_ifs <;> simp [hb.le]
          _ < a := by
              rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_div_assoc', div_lt_iff₀
                (by positivity)]
              nlinarith
      refine ⟨pt fun m ↦ if m = k then 0 else b,
        mem_facetPolyhedron_simplex_iff.2 ⟨fun m ↦ ?_, hsum.le⟩, Set.ext fun o ↦ ?_⟩
      · rw [hpt]; split_ifs <;> simp [hb.le]
      · cases o with
        | none => simpa [apply_compLeft_one] using hsum.ne
        | some m => simp [hpt, hb.ne']

end TauCeti.Toric
