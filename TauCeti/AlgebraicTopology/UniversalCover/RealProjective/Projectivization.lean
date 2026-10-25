/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module
public import TauCeti.AlgebraicTopology.UniversalCover.RealProjective.Basic
public import TauCeti.Topology.Algebra.Projectivization

/-!
# Comparing the antipodal quotient with native projective space

The map sending a unit vector to its real line descends to the antipodal quotient.
Two unit vectors on the same line differ by a sign, so this continuous map is bijective.
Compactness of the sphere quotient and the Hausdorff property of projective space make it a
homeomorphism. Composing with the coordinate linear equivalence identifies the quotient with
`Projectivization ℝ (Fin (n + 1) → ℝ)`.
-/

public section

open Metric
open scoped EuclideanSpace LinearAlgebra.Projectivization
namespace TauCeti.RealProjectiveSpace
variable (n : ℕ)

/-- The line spanned by a unit-vector representative of an antipodal class. -/
noncomputable def toProjectivization :
    RealProjectiveSpace n → ℙ ℝ (EuclideanSpace ℝ (Fin (n + 1))) :=
  RealProjectiveSpace.lift n
    (fun x => Projectivization.mk ℝ (x : EuclideanSpace ℝ (Fin (n + 1)))
      (ne_zero_of_mem_sphere one_ne_zero x)) (fun x => by
        apply (Projectivization.mk_eq_mk_iff' ℝ _ _ _ _).2
        exact ⟨-1, by simp⟩)

/-- The comparison sends the class of a unit vector to its line. -/
@[simp]
theorem toProjectivization_mk
    (x : sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) :
    toProjectivization n (mk n x) = Projectivization.mk ℝ x.val
      (ne_zero_of_mem_sphere one_ne_zero x) := by
  rw [toProjectivization, RealProjectiveSpace.lift_mk]

/-- The comparison is continuous for the quotient topologies on both spaces. -/
@[fun_prop]
theorem continuous_toProjectivization : Continuous (toProjectivization n) := by
  apply (isQuotientMap_mk n).continuous_iff.2
  simpa only [Function.comp_def, toProjectivization_mk] using
    Projectivization.continuous_mk continuous_subtype_val
      (fun x : sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 =>
        ne_zero_of_mem_sphere one_ne_zero x)

/-- Unit vectors spanning the same real line are equal or antipodal. -/
theorem toProjectivization_injective : Function.Injective (toProjectivization n) := by
  intro x y
  induction x using RealProjectiveSpace.inductionOn
  induction y using RealProjectiveSpace.inductionOn
  rename_i x y
  intro h
  rw [toProjectivization_mk, toProjectivization_mk, Projectivization.mk_eq_mk_iff'] at h
  obtain ⟨a, ha⟩ := h
  have hx : ‖(x : EuclideanSpace ℝ (Fin (n + 1)))‖ = 1 := mem_sphere_zero_iff_norm.mp x.2
  have hy : ‖(y : EuclideanSpace ℝ (Fin (n + 1)))‖ = 1 := mem_sphere_zero_iff_norm.mp y.2
  have habs : |a| = 1 := by
    simpa only [norm_smul, Real.norm_eq_abs, hy, mul_one, hx] using congrArg norm ha
  rcases (abs_eq (show (0 : ℝ) ≤ 1 by norm_num)).mp habs with rfl | rfl
  · apply (mk_eq_mk_iff n x y).2
    exact Or.inl (Subtype.ext (by simpa using ha.symm))
  · apply (mk_eq_mk_iff n x y).2
    exact Or.inr (Subtype.ext (by simpa using ha.symm))

/-- Every real line has a unit-vector representative. -/
theorem toProjectivization_surjective : Function.Surjective (toProjectivization n) := by
  intro z
  obtain ⟨v, hv, hnorm, rfl⟩ := Projectivization.exists_norm_eq_one_mk_eq z
  exact ⟨mk n ⟨v, mem_sphere_zero_iff_norm.mpr hnorm⟩, by rw [toProjectivization_mk]⟩

/-- The antipodal sphere quotient is homeomorphic to the projectivization of Euclidean space. -/
noncomputable def homeomorphProjectivization :
    RealProjectiveSpace n ≃ₜ ℙ ℝ (EuclideanSpace ℝ (Fin (n + 1))) :=
  Continuous.homeoOfEquivCompactToT2
    (f := Equiv.ofBijective (toProjectivization n)
      ⟨toProjectivization_injective n, toProjectivization_surjective n⟩)
    (continuous_toProjectivization n)

/-- The Euclidean-space comparison sends a unit-vector class to its line. -/
@[simp]
theorem homeomorphProjectivization_mk
    (x : sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) :
    homeomorphProjectivization n (mk n x) = Projectivization.mk ℝ x.val
      (ne_zero_of_mem_sphere one_ne_zero x) :=
  toProjectivization_mk n x

/-- The antipodal sphere quotient is homeomorphic to native projective coordinate space. -/
noncomputable def homeomorphProjectivizationPi :
    RealProjectiveSpace n ≃ₜ ℙ ℝ (Fin (n + 1) → ℝ) := by
  let e := PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin (n + 1) => ℝ)
  let f := Projectivization.map e.toLinearMap e.injective
  have hf : Continuous f := Projectivization.continuous_map e.injective e.continuous
  have hi : Function.Injective f := Projectivization.map_injective e.toLinearMap e.injective
  have hs : Function.Surjective f := by
    intro z
    induction z using Projectivization.ind with
    | h v hv =>
      refine ⟨Projectivization.mk ℝ (e.symm v) (by simpa using hv), ?_⟩
      dsimp only [f]
      rw [Projectivization.map_mk]
      rfl
  exact (homeomorphProjectivization n).trans
    (Continuous.homeoOfEquivCompactToT2 (f := Equiv.ofBijective f ⟨hi, hs⟩) hf)

/-- The coordinate comparison sends a unit-vector class to the line of its coordinates. -/
@[simp]
theorem homeomorphProjectivizationPi_mk
    (x : sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) :
    homeomorphProjectivizationPi n (mk n x) = Projectivization.mk ℝ (fun i => x.val i)
      (by
        intro h
        apply ne_zero_of_mem_sphere one_ne_zero x
        ext i
        exact congrFun h i) := by
  let e := PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin (n + 1) => ℝ)
  change Projectivization.map e.toLinearMap e.injective (toProjectivization n (mk n x)) = _
  rw [toProjectivization_mk, Projectivization.map_mk]
  rfl

end TauCeti.RealProjectiveSpace
