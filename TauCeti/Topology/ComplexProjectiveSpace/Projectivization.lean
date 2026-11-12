/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.Projectivization
public import TauCeti.Topology.ComplexProjectiveSpace.Basic

/-!
# The sphere-quotient model of `CPⁿ` and the projectivization `ℙ ℂ (Fin (n + 1) → ℂ)`

Tau Ceti has two models of complex projective space: the circle quotient of the unit sphere
`TauCeti.ComplexProjectiveSpace n`, and the space of lines `ℙ ℂ (Fin (n + 1) → ℂ)` with the
quotient topology from the nonzero vectors. Sending the class of a unit vector to the line it
spans is well defined, since unit multiples span the same line, and bijective: two unit vectors
spanning the same line differ by a scalar of norm one, and every line is spanned by a unit vector.
It is continuous, and `CPⁿ` is compact while `ℙ ℂ (Fin (n + 1) → ℂ)` is Hausdorff, so it is a
homeomorphism, whose inverse sends a line `[v]` to the class of `v / ‖v‖`.

## Main declarations

* `TauCeti.ComplexProjectiveSpace.homeomorphProjectivization`: the homeomorphism
  `CPⁿ ≃ₜ ℙ ℂ (Fin (n + 1) → ℂ)` sending the class of a unit vector to the line it spans.
-/

public section

open Metric
open scoped LinearAlgebra.Projectivization

namespace TauCeti

namespace ComplexProjectiveSpace

variable (n : ℕ)

/-- The line spanned by a unit vector of `EuclideanSpace ℂ (Fin (n + 1))`, as a point of
`ℙ ℂ (Fin (n + 1) → ℂ)`. -/
private noncomputable def lineOfSphere (x : sphere (0 : EuclideanSpace ℂ (Fin (n + 1))) 1) :
    ℙ ℂ (Fin (n + 1) → ℂ) :=
  Projectivization.mk ℂ (WithLp.ofLp (x : EuclideanSpace ℂ (Fin (n + 1))))
    ((WithLp.ofLp_eq_zero _).not.2 (ne_zero_of_mem_sphere one_ne_zero x))

private theorem lineOfSphere_smul (c : sphere (0 : ℂ) 1)
    (x : sphere (0 : EuclideanSpace ℂ (Fin (n + 1))) 1) :
    lineOfSphere n (c • x) = lineOfSphere n x :=
  (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).2 ⟨c, rfl⟩

private theorem lift_lineOfSphere_mk (x : sphere (0 : EuclideanSpace ℂ (Fin (n + 1))) 1) :
    ComplexProjectiveSpace.lift n (lineOfSphere n) (lineOfSphere_smul n) (mk n x) =
      lineOfSphere n x :=
  ComplexProjectiveSpace.lift_mk n _ _ x

private theorem bijective_lift_lineOfSphere :
    Function.Bijective (ComplexProjectiveSpace.lift n (lineOfSphere n) (lineOfSphere_smul n)) := by
  constructor
  · intro x y
    induction x using ComplexProjectiveSpace.inductionOn with | h x => ?_
    induction y using ComplexProjectiveSpace.inductionOn with | h y => ?_
    intro h
    rw [lift_lineOfSphere_mk, lift_lineOfSphere_mk] at h
    obtain ⟨a, ha⟩ := (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).1 h
    replace ha : a • (y : EuclideanSpace ℂ (Fin (n + 1))) = x := WithLp.ofLp_injective 2 ha
    have hnorm : ‖a‖ = 1 := by
      simpa [norm_smul, norm_eq_of_mem_sphere] using congrArg norm ha
    exact (mk_eq_mk_iff n x y).2 ⟨⟨a, mem_sphere_zero_iff_norm.2 hnorm⟩, Subtype.ext ha⟩
  · intro p
    have hw : WithLp.toLp 2 p.rep ≠ 0 := (WithLp.toLp_eq_zero _).not.2 p.rep_ne_zero
    refine ⟨mk n ⟨(‖WithLp.toLp 2 p.rep‖⁻¹ : ℂ) • WithLp.toLp 2 p.rep,
      mem_sphere_zero_iff_norm.2 (norm_smul_inv_norm hw)⟩, ?_⟩
    rw [lift_lineOfSphere_mk]
    conv_rhs => rw [← p.mk_rep]
    exact (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).2 ⟨_, rfl⟩

private theorem continuous_lift_lineOfSphere :
    Continuous (ComplexProjectiveSpace.lift n (lineOfSphere n) (lineOfSphere_smul n)) := by
  refine (isOpenQuotientMap_mk n).isQuotientMap.continuous_iff.2 ?_
  have : ComplexProjectiveSpace.lift n (lineOfSphere n) (lineOfSphere_smul n) ∘ mk n =
      lineOfSphere n := funext (lift_lineOfSphere_mk n)
  rw [this]
  exact Projectivization.continuous_mk (by fun_prop) _

/-- The homeomorphism from the sphere-quotient model `CPⁿ` to the projectivization
`ℙ ℂ (Fin (n + 1) → ℂ)`, sending the class of a unit vector to the line it spans. -/
noncomputable def homeomorphProjectivization :
    ComplexProjectiveSpace n ≃ₜ ℙ ℂ (Fin (n + 1) → ℂ) :=
  (continuous_lift_lineOfSphere n).homeoOfEquivCompactToT2
    (f := Equiv.ofBijective _ (bijective_lift_lineOfSphere n))

/-- The homeomorphism `CPⁿ ≃ₜ ℙ ℂ (Fin (n + 1) → ℂ)` sends the class of a unit vector to the line
it spans. -/
@[simp]
theorem homeomorphProjectivization_mk (x : sphere (0 : EuclideanSpace ℂ (Fin (n + 1))) 1) :
    homeomorphProjectivization n (mk n x) =
      Projectivization.mk ℂ (WithLp.ofLp (x : EuclideanSpace ℂ (Fin (n + 1))))
        ((WithLp.ofLp_eq_zero _).not.2 (ne_zero_of_mem_sphere one_ne_zero x)) :=
  lift_lineOfSphere_mk n x

end ComplexProjectiveSpace

end TauCeti
