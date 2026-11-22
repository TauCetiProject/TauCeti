/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.LowRank.Zero
public import TauCeti.Topology.Algebra.CliffordAlgebra.Spin.Basic
public import TauCeti.Topology.Algebra.ContinuousMonoidHom.Descent
public import Mathlib.Topology.Covering.Quotient
import TauCeti.Topology.Algebra.CliffordAlgebra.Spin.Compact
import TauCeti.Topology.Algebra.CliffordAlgebra.Spin.Rotation

/-!
# The compact real Spin double cover

The projection from the compact real Spin group to the special orthogonal group is a covering map.
Indeed, the real Spin group is compact
(`CliffordAlgebra.instCompactSpaceRealCliffordSpinGroupZero`), so the projection is a continuous
surjection from a compact space to a Hausdorff space, hence a quotient map. Its kernel is the
finite image of the included group `Multiplicative (ZMod 2)`, so the standard quotient-covering
construction applies.

The two lowest ranks are degenerate. In rank one, `Spin(1) = {1, -1}` is finite
(`CliffordAlgebra.finite_realCliffordSpinGroupZero_one`), hence discrete, and `SO(1)` is trivial,
so the double cover is the trivial two-sheeted cover of a point. In rank zero Mathlib's Spin
group is trivial and the geometric double cover is instead the even unitary group `μ₂ = {1, -1}`
of the Clifford algebra over the trivial group `SO(0)`
(`CliffordAlgebra.evenUnitaryDoubleCoverOfSubsingleton`); its projection is again a covering map.

## Main results

* `CliffordAlgebra.isQuotientCoveringMap_realCliffordSpinDoubleCoverZero_rightHom` packages the
  compact real Spin projection as a quotient covering map by its kernel.
* `CliffordAlgebra.isCoveringMap_realCliffordSpinDoubleCoverZero_rightHom` packages the projection
  as an ordinary covering map.
* `CliffordAlgebra.isCoveringMap_realCliffordSpinProjectionZero` gives the same result for the
  bundled continuous homomorphism.
* `CliffordAlgebra.realCliffordSpinHomEquivKer` identifies continuous homomorphisms out of
  `SO(n)` with continuous homomorphisms out of `Spin(n)` that kill the double-cover kernel.
* `CliffordAlgebra.isCoveringMap_evenUnitaryDoubleCoverOfSubsingleton_rightHom`: the rank-zero
  double cover `μ₂ → SO(0)` is a covering map.
* `TauCeti.not_exists_continuous_lift_of_spinLift_ne`,
  `TauCeti.not_exists_continuous_lift_of_spinLift_monoidHom`, and
  `TauCeti.not_exists_continuous_section_realCliffordSpin`: general Spin-lift obstructions in rank
  `≥ 2` and non-existence of a continuous section of `Spin(n + 2) → SO(n + 2)`.

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I, Section 2.
-/

public section

namespace CliffordAlgebra

open TauCeti

/-- The compact real Spin projection, bundled as a continuous homomorphism. -/
noncomputable def realCliffordSpinProjectionZero (n : ℕ) [NeZero n] :
    realCliffordSpinGroupZero n →ₜ*
      QuadraticMap.specialOrthogonalGroup (realCliffordForm n 0) :=
  ⟨(realCliffordSpinDoubleCoverZero n).rightHom,
    continuous_realCliffordSpinDoubleCoverZero_rightHom n⟩

/-- The bundled compact real Spin projection agrees with the projection of the double-cover
extension. -/
@[simp]
theorem realCliffordSpinProjectionZero_apply (n : ℕ) [NeZero n]
    (x : realCliffordSpinGroupZero n) :
    realCliffordSpinProjectionZero n x = (realCliffordSpinDoubleCoverZero n).rightHom x := by
  rw [realCliffordSpinProjectionZero]
  rfl

/-- The compact real Spin projection has the same underlying monoid homomorphism as the projection
of the double-cover extension. -/
@[simp]
theorem coeMonoidHom_realCliffordSpinProjectionZero (n : ℕ) [NeZero n] :
    (realCliffordSpinProjectionZero n : realCliffordSpinGroupZero n →*
      QuadraticMap.specialOrthogonalGroup (realCliffordForm n 0)) =
        (realCliffordSpinDoubleCoverZero n).rightHom := by
  rw [realCliffordSpinProjectionZero]
  rfl

/-- The compact real Spin projection has the same underlying function as the projection of the
double-cover extension. -/
theorem coe_realCliffordSpinProjectionZero (n : ℕ) [NeZero n] :
    (realCliffordSpinProjectionZero n : realCliffordSpinGroupZero n →
      QuadraticMap.specialOrthogonalGroup (realCliffordForm n 0)) =
        (realCliffordSpinDoubleCoverZero n).rightHom :=
  funext (realCliffordSpinProjectionZero_apply n)

/-- The compact Spin projection sends the element `-1` of `Spin(n)` to the identity of `SO(n)`. -/
theorem realCliffordSpinProjectionZero_negOne (n : ℕ) [NeZero n] :
    realCliffordSpinProjectionZero n
        (spinGroup.negOne (realCliffordForm n 0) (nondegenerate_realCliffordForm n 0).ne_zero) =
      1 := by
  simp

/-- The compact real Spin projection is a quotient covering map by its kernel. -/
theorem isQuotientCoveringMap_realCliffordSpinDoubleCoverZero_rightHom
    (n : ℕ) [NeZero n] :
    IsQuotientCoveringMap (realCliffordSpinDoubleCoverZero n).rightHom
      (realCliffordSpinDoubleCoverZero n).rightHom.ker := by
  let S := realCliffordSpinDoubleCoverZero n
  have hquot : Topology.IsQuotientMap S.rightHom :=
    Topology.IsQuotientMap.of_surjective_continuous S.rightHom_surjective
      (continuous_realCliffordSpinDoubleCoverZero_rightHom n)
  apply hquot.isQuotientCoveringMap_of_isDiscrete_ker_monoidHom
  rw [← S.range_inl_eq_ker_rightHom]
  exact (Set.finite_range S.inl).isDiscrete

/-- The projection from the compact real Spin group to the special orthogonal group is a covering
map. -/
theorem isCoveringMap_realCliffordSpinDoubleCoverZero_rightHom
    (n : ℕ) [NeZero n] :
    IsCoveringMap (realCliffordSpinDoubleCoverZero n).rightHom :=
  (isQuotientCoveringMap_realCliffordSpinDoubleCoverZero_rightHom n).isCoveringMap

/-- The bundled compact real Spin projection is a covering map. -/
theorem isCoveringMap_realCliffordSpinProjectionZero
    (n : ℕ) [NeZero n] :
    IsCoveringMap (realCliffordSpinProjectionZero n) := by
  rw [coe_realCliffordSpinProjectionZero]
  exact isCoveringMap_realCliffordSpinDoubleCoverZero_rightHom n

/-- Continuous homomorphisms out of `SO(n)` are equivalent to continuous homomorphisms out of
compact `Spin(n)` that kill the kernel of the double-cover projection. -/
noncomputable def realCliffordSpinHomEquivKer (n : ℕ) [NeZero n]
    {H : Type*} [Monoid H] [TopologicalSpace H] :
    (QuadraticMap.specialOrthogonalGroup (realCliffordForm n 0) →ₜ* H) ≃
      {f : realCliffordSpinGroupZero n →ₜ* H //
        (realCliffordSpinDoubleCoverZero n).rightHom.ker ≤
          (f : realCliffordSpinGroupZero n →* H).ker} := by
  simpa only [coeMonoidHom_realCliffordSpinProjectionZero] using
    ContinuousMonoidHom.homEquivOfIsQuotientMap (realCliffordSpinProjectionZero n) <| by
      rw [coe_realCliffordSpinProjectionZero]
      exact
        (isQuotientCoveringMap_realCliffordSpinDoubleCoverZero_rightHom n).toIsQuotientMap

/-- The compact Spin correspondence sends a homomorphism on `SO(n)` to its composition with the
Spin projection. -/
@[simp]
theorem realCliffordSpinHomEquivKer_apply_coe (n : ℕ) [NeZero n]
    {H : Type*} [Monoid H] [TopologicalSpace H]
    (f : QuadraticMap.specialOrthogonalGroup (realCliffordForm n 0) →ₜ* H) :
    ((realCliffordSpinHomEquivKer n f :
      {g : realCliffordSpinGroupZero n →ₜ* H //
        (realCliffordSpinDoubleCoverZero n).rightHom.ker ≤
          (g : realCliffordSpinGroupZero n →* H).ker}) :
      realCliffordSpinGroupZero n →ₜ* H) =
        f.comp (realCliffordSpinProjectionZero n) := by
  rw [realCliffordSpinHomEquivKer]
  exact ContinuousMonoidHom.homEquivOfIsQuotientMap_apply_coe _ _ f

/-- Descending a homomorphism from compact `Spin(n)` and composing again with the Spin projection
recovers the original homomorphism. -/
@[simp]
theorem realCliffordSpinHomEquivKer_symm_apply_comp (n : ℕ) [NeZero n]
    {H : Type*} [Monoid H] [TopologicalSpace H]
    (f : {g : realCliffordSpinGroupZero n →ₜ* H //
      (realCliffordSpinDoubleCoverZero n).rightHom.ker ≤
        (g : realCliffordSpinGroupZero n →* H).ker}) :
    ((realCliffordSpinHomEquivKer n).symm f).comp (realCliffordSpinProjectionZero n) = f.val := by
  have h := congrArg Subtype.val ((realCliffordSpinHomEquivKer n).apply_symm_apply f)
  rw [realCliffordSpinHomEquivKer_apply_coe] at h
  exact h

/-- In dimension zero, the projection of the even unitary group `μ₂ = {1, -1}` onto the trivial
special orthogonal group is a covering map, for the subgroup topology on Clifford units and any
topology on the one-point special orthogonal group, such as the coordinate topology on
`ι → K`. For `realCliffordForm 0 0` this is the rank-zero geometric replacement for
`CliffordAlgebra.isCoveringMap_realCliffordSpinDoubleCoverZero_rightHom`, since Mathlib's Spin
group is trivial in dimension zero. -/
theorem isCoveringMap_evenUnitaryDoubleCoverOfSubsingleton_rightHom
    {K : Type*} [Field K] [TopologicalSpace K] [IsTopologicalSemiring K] [T2Space K]
    {V : Type*} [AddCommGroup V] [Module K V] [Subsingleton V] (Q : QuadraticForm K V)
    [TopologicalSpace (TauCeti.QuadraticMap.specialOrthogonalGroup Q)] (h2 : (2 : K) ≠ 0) :
    IsCoveringMap (evenUnitaryDoubleCoverOfSubsingleton Q h2).rightHom :=
  .of_discreteTopology _

end CliffordAlgebra

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
    refine (isCoveringMap_realCliffordSpinDoubleCoverZero_rightHom N).eq_of_comp_eq
      ((continuous_const.mul hf_cont).comp
        ((continuous_spinToSpecialOrthogonal_pi (realCliffordForm (n + 2) 0)).comp γ.continuous))
      (hψ_cont.comp γ.continuous) ?_ 0 ?_
    · funext t
      simpa using (hf'_lift _).trans (hψ_lift (γ t)).symm
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
