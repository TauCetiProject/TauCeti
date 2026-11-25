/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.CliffordAlgebra.Spin.Basic
import TauCeti.Topology.Algebra.CliffordAlgebra.Spin.Covering.Basic
import TauCeti.Topology.Algebra.CliffordAlgebra.Spin.Rotation

/-!
# Continuous lift obstructions for the compact real Spin double cover

Using path-lifting uniqueness along the Spin covering map
`CliffordAlgebra.isCoveringMap_spinToSpecialOrthogonal_realCliffordForm` and the explicit rotation
path from `1` to `-1` in `Spin(n + 2)`
(`CliffordAlgebra.joined_one_negOne_realCliffordSpinGroupZero_add_two`),
any map `φ : SO(n + 2) → SO(N)` covered by a continuous map `ψ : Spin(n + 2) → Spin(N)` with
`ψ (-1) ≠ ψ 1` admits no continuous lift `SO(n + 2) → Spin(N)`. In particular, the Spin double
cover `Spin(n + 2) → SO(n + 2)` admits no continuous section.

## Main results

* `TauCeti.not_exists_continuous_lift_of_spinLift_ne`: general Spin-lift obstruction in rank `≥ 2`
  from a continuous cover `ψ` separating `-1` and `1`.
* `TauCeti.not_exists_continuous_lift_of_spinLift_monoidHom`: homomorphic specialization when `ψ`
  is a continuous homomorphism sending `-1` to `-1`.
* `TauCeti.not_exists_continuous_section_realCliffordSpin`: non-existence of a continuous section
  of `Spin(n + 2) → SO(n + 2)`.

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I, Section 2.
-/

public section

namespace TauCeti

open _root_.CliffordAlgebra

noncomputable section

/-- **General Spin-lift obstruction in rank `≥ 2`**: if a map `φ : SO(n + 2) → SO(N)` is covered by
a continuous map `ψ : Spin(n + 2) → Spin(N)` satisfying `ψ (-1) ≠ ψ 1`, then `φ` admits no
continuous lift `SO(n + 2) → Spin(N)`. -/
theorem not_exists_continuous_lift_of_spinLift_ne {n N : ℕ}
    {φ : QuadraticMap.specialOrthogonalGroup (realCliffordForm (n + 2) 0) →
      QuadraticMap.specialOrthogonalGroup (realCliffordForm N 0)}
    {ψ : realCliffordSpinGroupZero (n + 2) → realCliffordSpinGroupZero N}
    (hψ_cont : Continuous ψ)
    (hψ_lift : ∀ x, spinToSpecialOrthogonal (realCliffordForm N 0) (ψ x) =
      φ (spinToSpecialOrthogonal (realCliffordForm (n + 2) 0) x))
    (hψ_ne : ψ (spinGroup.negOne (realCliffordForm (n + 2) 0)
        (nondegenerate_realCliffordForm (n + 2) 0).ne_zero) ≠ ψ 1) :
    ¬ ∃ f : QuadraticMap.specialOrthogonalGroup (realCliffordForm (n + 2) 0) →
        realCliffordSpinGroupZero N,
      Continuous f ∧ ∀ g, spinToSpecialOrthogonal (realCliffordForm N 0) (f g) = φ g := by
  obtain rfl | hN := Nat.eq_zero_or_pos N
  · have : Subsingleton (Fin (0 + 0) → ℝ) := inferInstanceAs (Subsingleton (Fin 0 → ℝ))
    exact absurd (Subsingleton.elim _ _) hψ_ne
  have : NeZero N := ⟨hN.ne'⟩
  rintro ⟨f, hf_cont, hf_lift⟩
  -- Normalize `f` so that it sends `1` to `ψ 1` while lifting the same map `φ`.
  have hφ1 : spinToSpecialOrthogonal (realCliffordForm N 0) (ψ 1) = φ 1 := by
    simpa using hψ_lift 1
  let f' : QuadraticMap.specialOrthogonalGroup (realCliffordForm (n + 2) 0) →
      realCliffordSpinGroupZero N := fun g ↦ ψ 1 * (f 1)⁻¹ * f g
  have hf'_lift : ∀ g, spinToSpecialOrthogonal (realCliffordForm N 0) (f' g) = φ g := fun g ↦ by
    simp [f', hf_lift, hφ1]
  -- Pull both lifts back along a path from `1` to `-1` in `Spin(n + 2)`.
  obtain ⟨γ⟩ := joined_one_negOne_realCliffordSpinGroupZero_add_two n
  have heq : (fun t : unitInterval ↦ f' (spinToSpecialOrthogonal (realCliffordForm (n + 2) 0)
      (γ t))) = fun t ↦ ψ (γ t) := by
    refine (isCoveringMap_spinToSpecialOrthogonal_realCliffordForm N).eq_of_comp_eq
      ((continuous_const.mul hf_cont).comp
        ((continuous_spinToSpecialOrthogonal_pi (realCliffordForm (n + 2) 0)).comp γ.continuous))
      (hψ_cont.comp γ.continuous) ?_ 0 ?_
    · funext t
      exact (hf'_lift _).trans (hψ_lift (γ t)).symm
    · simp [f', γ.source]
  have h1 := congrFun heq 1
  simp only [γ.target, spinGroup.spinToSpecialOrthogonal_negOne, f', mul_assoc,
    inv_mul_cancel, mul_one] at h1
  exact hψ_ne h1.symm

/-- **Homomorphic Spin-lift obstruction in rank `≥ 2`**: if a map `φ : SO(n + 2) → SO(N)` is
covered by a continuous homomorphism `ψ : Spin(n + 2) →* Spin(N)` sending `-1` to `-1`, then `φ`
admits no continuous lift `SO(n + 2) → Spin(N)`. -/
theorem not_exists_continuous_lift_of_spinLift_monoidHom {n N : ℕ} [NeZero N]
    {φ : QuadraticMap.specialOrthogonalGroup (realCliffordForm (n + 2) 0) →
      QuadraticMap.specialOrthogonalGroup (realCliffordForm N 0)}
    (ψ : realCliffordSpinGroupZero (n + 2) →* realCliffordSpinGroupZero N)
    (hψ_cont : Continuous ψ)
    (hψ_lift : ∀ x, spinToSpecialOrthogonal (realCliffordForm N 0) (ψ x) =
      φ (spinToSpecialOrthogonal (realCliffordForm (n + 2) 0) x))
    (hψ_negOne : ψ (spinGroup.negOne (realCliffordForm (n + 2) 0)
        (nondegenerate_realCliffordForm (n + 2) 0).ne_zero) =
      spinGroup.negOne (realCliffordForm N 0) (nondegenerate_realCliffordForm N 0).ne_zero) :
    ¬ ∃ f : QuadraticMap.specialOrthogonalGroup (realCliffordForm (n + 2) 0) →
        realCliffordSpinGroupZero N,
      Continuous f ∧ ∀ g, spinToSpecialOrthogonal (realCliffordForm N 0) (f g) = φ g :=
  not_exists_continuous_lift_of_spinLift_ne hψ_cont hψ_lift <| by
    rw [hψ_negOne, map_one]
    exact spinGroup.negOne_ne_one _ _

/-- **The Spin double cover `Spin(n + 2) → SO(n + 2)` has no continuous section.** -/
theorem not_exists_continuous_section_realCliffordSpin (n : ℕ) :
    ¬ ∃ f : QuadraticMap.specialOrthogonalGroup (realCliffordForm (n + 2) 0) →
        realCliffordSpinGroupZero (n + 2),
      Continuous f ∧
        ∀ g, spinToSpecialOrthogonal (realCliffordForm (n + 2) 0) (f g) = g :=
  not_exists_continuous_lift_of_spinLift_monoidHom
    (MonoidHom.id _) continuous_id (fun _ ↦ rfl) rfl

end

end TauCeti
