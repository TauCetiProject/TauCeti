/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.CappedCylinder.SemiFredholm
public import TauCeti.Geometry.Symplectic.Floer.Sobolev.Realization

/-!
# The linearized operator of the pair of pants capped at `1` on `W^{1,2}`

Plumbing the negative PSS plane with Hamiltonian `H_1` into the input end at `1` of the pair of
pants `ℂ ∖ {0, 1}` with Hamiltonians `H_0`, `H_1`, `H_∞`, along a neck of length `L > 4`, gives a
Floer datum on the standard cylinder with the components
`TauCeti.Floer.cappedCylinderComponent Hb L 1` and `TauCeti.Floer.cappedCylinderComponent Hb L I`
(`TauCeti.Geometry.Symplectic.Floer.PairOfPants.CappedCylinder`). Its solutions are the cylinders
counted in the unit property of the pair-of-pants product, and their regularity is a statement
about the linearized operator `D_u` of this datum. The end `c = 1` of the family capping the input
at `0` instead is, in the cylinder coordinates of the end at `1`, this datum for the exchanged
Hamiltonians (`TauCeti.Floer.cappedCylinderComponent_exchangeEndData`), so the results apply there
too.

This file realizes `D_u` along a cylinder `u` asymptotic to a nondegenerate one-periodic orbit
`x₊` of `H_0` at `+∞` and `x₋` of `H_∞` at `-∞` as the bounded operator
`TauCeti.SymplecticForm.floerSobolevOperator` from `W^{1,2}(ℝ × S¹, V)` to `L²(ℝ × S¹, V)`, for
almost complex structures `J(z)` equal to `J₊_t` for `s ≥ R` and to `J₋_t` for `s ≤ -R`, and proves
that

* its coefficients are essentially bounded on the cylinder
  (`TauCeti.SymplecticForm.memLp_floerJetCoeff_cappedCylinderComponent`), so that it acts on the
  jet of a test section as `D_u`;
* it has finite-dimensional kernel
  (`TauCeti.SymplecticForm.finiteDimensional_ker_floerSobolevOperator_cappedCylinderComponent`);
* it has closed range
  (`TauCeti.SymplecticForm.isClosed_range_floerSobolevOperator_cappedCylinderComponent`).

The capped datum is cylindrical near the ends with radius `max R 3`
(`TauCeti.Floer.isCylindricalNearEnds_cappedCylinderComponent`), so these are cases of the
corresponding statements for Floer data cylindrical near the ends in
`TauCeti.Geometry.Symplectic.Floer.Sobolev.Realization`, whose input is the semi-Fredholm estimate
of `TauCeti.Geometry.Symplectic.Floer.PairOfPants.CappedCylinder.SemiFredholm`. The finiteness of
the cokernel, hence the Fredholm property and the index, needs the same estimate for the formal
adjoint of `D_u`.

## References

* S. Piunikhin, D. Salamon and M. Schwarz, *Symplectic Floer–Donaldson theory and quantum
  cohomology*, in *Contact and symplectic geometry*, Publ. Newton Inst. 8 (1996), 171–200, on the
  unit of the pair-of-pants product.
* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, 2nd ed., Section 3.1
  and Appendix B, on the semi-Fredholm estimate and Peetre's argument.
-/

public section

open Set Filter MeasureTheory Function
open scoped NNReal ENNReal Manifold
open TauCeti.ThricePuncturedSphere TauCeti.ThricePuncturedSphere.Puncture

namespace TauCeti.SymplecticForm

open CylinderSobolev Floer
open StripSobolev (stripMeasure)

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

/-- **The coefficients of the linearized operator of the pair of pants capped at `1` are
bounded.** Let `Hb r` be jointly `C²` Hamiltonians of period one in `t` and let `L > 4`. Let
`J(z)` be almost complex structures on the cylinder, `C¹` along the graph of a `C¹` map `u`, equal
to a `C¹` family `Jp_t` for `s ≥ R` and to a `C¹` family `Jm_t` for `s ≤ -R`. If the loops of `u`
converge uniformly at both ends, with slice defect `∂t u - X_{Hb ∞}(u)` tending uniformly to zero
at `-∞` and `∂t u - X_{Hb 0}(u)` at `+∞`, then the coefficient field on jets of the linearized
Floer operator of `J` and of the capped datum is essentially bounded on the cylinder. -/
theorem memLp_floerJetCoeff_cappedCylinderComponent (ω : SymplecticForm V)
    {Hb : Puncture → ℝ → V → ℝ} (hHb : ∀ r, Periodic (Hb r) 1)
    (hHbs : ∀ r, ContDiff ℝ 2 (uncurry (Hb r))) {L : ℝ} (hL : 4 < L)
    {Jm Jp : ℝ → V → AlmostComplexStructure V}
    (hJm : ContDiff ℝ 1 fun p : ℝ × V ↦ (Jm p.1 p.2).toLinearMap.toContinuousLinearMap)
    (hJp : ContDiff ℝ 1 fun p : ℝ × V ↦ (Jp p.1 p.2).toLinearMap.toContinuousLinearMap)
    {J : ℝ × ℝ → V → AlmostComplexStructure V} {u : ℝ × ℝ → V}
    (hJ : ∀ z, ContDiffAt ℝ 1
      (fun p : (ℝ × ℝ) × V ↦ (J p.1 p.2).toLinearMap.toContinuousLinearMap) (z, u z)) {R : ℝ}
    (hJRp : ∀ s t, R ≤ s → J (s, t) = Jp t) (hJRm : ∀ s t, s ≤ -R → J (s, t) = Jm t)
    (hu : ContDiff ℝ 1 u) {xm xp : ℝ → V}
    (huxm : TendstoUniformlyOn (fun s t ↦ u (s, t)) xm atBot (Icc 0 1))
    (hδm : TendstoUniformlyOn
      (fun s t ↦ sliceDefect (fun t ↦ ω.hamiltonianVectorField (Hb inf t)) u (s, t)) 0 atBot
        (Icc 0 1))
    (huxp : TendstoUniformlyOn (fun s t ↦ u (s, t)) xp atTop (Icc 0 1))
    (hδp : TendstoUniformlyOn
      (fun s t ↦ sliceDefect (fun t ↦ ω.hamiltonianVectorField (Hb zero t)) u (s, t)) 0 atTop
        (Icc 0 1)) :
    MemLp (ω.floerJetCoeff (fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap)
      (cappedCylinderComponent Hb L 1) (cappedCylinderComponent Hb L Complex.I) u) ∞
        stripMeasure :=
  ω.memLp_floerJetCoeff_of_cylindrical
    (isCylindricalNearEnds_cappedCylinderComponent hHb hHbs hL hJ hJRp hJRm) hu (hHbs inf) hJm huxm
    hδm (hHbs zero) hJp huxp hδp

/-- **The linearized operator of the pair of pants capped at `1` has finite-dimensional kernel on
`W^{1,2}`.** Under the hypotheses of the semi-Fredholm estimate
`exists_forall_setIntegral_le_mul_setIntegral_floerLinearization_cappedCylinderComponent_add`
(almost complex structures cylindrical on the two ends and compatible along `u`, and a map `u`
asymptotic to a nondegenerate one-periodic orbit `xm` of `Hb ∞` at `-∞` and `xp` of `Hb 0` at
`+∞`), the realization `D_u : W^{1,2}(ℝ × S¹, V) → L²(ℝ × S¹, V)` of the linearized Floer operator
of the capped datum has finite-dimensional kernel. -/
theorem finiteDimensional_ker_floerSobolevOperator_cappedCylinderComponent (ω : SymplecticForm V)
    {Hb : Puncture → ℝ → V → ℝ} (hHb : ∀ r, Periodic (Hb r) 1)
    (hHbs : ∀ r, ContDiff ℝ 2 (uncurry (Hb r))) {L : ℝ} (hL : 4 < L) {Km Kp : ℝ≥0}
    (hXm : LipschitzWith Km (ω.timeDependentHamiltonianSuspension (Hb inf)))
    (hXp : LipschitzWith Kp (ω.timeDependentHamiltonianSuspension (Hb zero))) {xm xp : ℝ → V}
    (hxm : ∀ t, HasDerivAt xm (ω.hamiltonianVectorField (Hb inf t) (xm t)) t)
    (hndm : IsNondegenerateFixedPt 𝓘(ℝ, V) (ω.timeDependentHamiltonianFlow (Hb inf) hXm 0 1)
      (xm 0))
    (hxp : ∀ t, HasDerivAt xp (ω.hamiltonianVectorField (Hb zero t) (xp t)) t)
    (hndp : IsNondegenerateFixedPt 𝓘(ℝ, V) (ω.timeDependentHamiltonianFlow (Hb zero) hXp 0 1)
      (xp 0))
    {Jm Jp : ℝ → V → AlmostComplexStructure V}
    (hJm : ContDiff ℝ 1 fun p : ℝ × V ↦ (Jm p.1 p.2).toLinearMap.toContinuousLinearMap)
    (hJp : ContDiff ℝ 1 fun p : ℝ × V ↦ (Jp p.1 p.2).toLinearMap.toContinuousLinearMap)
    (hJxm : ∀ t, ω.Compatible (Jm t (xm t))) (hJxp : ∀ t, ω.Compatible (Jp t (xp t)))
    {J : ℝ × ℝ → V → AlmostComplexStructure V} {u : ℝ × ℝ → V}
    (hJ : ∀ z, ContDiffAt ℝ 1
      (fun p : (ℝ × ℝ) × V ↦ (J p.1 p.2).toLinearMap.toContinuousLinearMap) (z, u z)) {R : ℝ}
    (hJRp : ∀ s t, R ≤ s → J (s, t) = Jp t) (hJRm : ∀ s t, s ≤ -R → J (s, t) = Jm t)
    (hu : ContDiff ℝ 1 u) (hJu : ∀ z, ω.Compatible (J z (u z)))
    (huxm : TendstoUniformlyOn (fun s t ↦ u (s, t)) xm atBot (Icc 0 1))
    (huxp : TendstoUniformlyOn (fun s t ↦ u (s, t)) xp atTop (Icc 0 1))
    (hδm : TendstoUniformlyOn
      (fun s t ↦ sliceDefect (fun t ↦ ω.hamiltonianVectorField (Hb inf t)) u (s, t)) 0 atBot
        (Icc 0 1))
    (hδp : TendstoUniformlyOn
      (fun s t ↦ sliceDefect (fun t ↦ ω.hamiltonianVectorField (Hb zero t)) u (s, t)) 0 atTop
        (Icc 0 1)) :
    FiniteDimensional ℝ (ω.floerSobolevOperator
      (fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap)
      (cappedCylinderComponent Hb L 1) (cappedCylinderComponent Hb L Complex.I) u).ker :=
  ω.finiteDimensional_ker_floerSobolevOperator_of_cylindrical
    (isCylindricalNearEnds_cappedCylinderComponent hHb hHbs hL hJ hJRp hJRm) hu hJu hXm (hHbs inf)
    hxm hndm hJm hJxm huxm hδm hXp (hHbs zero) hxp hndp hJp hJxp huxp hδp

/-- **The linearized operator of the pair of pants capped at `1` has closed range on
`W^{1,2}`.** Under the hypotheses of
`finiteDimensional_ker_floerSobolevOperator_cappedCylinderComponent`, the realization
`D_u : W^{1,2}(ℝ × S¹, V) → L²(ℝ × S¹, V)` of the linearized Floer operator of the capped datum
has closed range. -/
theorem isClosed_range_floerSobolevOperator_cappedCylinderComponent (ω : SymplecticForm V)
    {Hb : Puncture → ℝ → V → ℝ} (hHb : ∀ r, Periodic (Hb r) 1)
    (hHbs : ∀ r, ContDiff ℝ 2 (uncurry (Hb r))) {L : ℝ} (hL : 4 < L) {Km Kp : ℝ≥0}
    (hXm : LipschitzWith Km (ω.timeDependentHamiltonianSuspension (Hb inf)))
    (hXp : LipschitzWith Kp (ω.timeDependentHamiltonianSuspension (Hb zero))) {xm xp : ℝ → V}
    (hxm : ∀ t, HasDerivAt xm (ω.hamiltonianVectorField (Hb inf t) (xm t)) t)
    (hndm : IsNondegenerateFixedPt 𝓘(ℝ, V) (ω.timeDependentHamiltonianFlow (Hb inf) hXm 0 1)
      (xm 0))
    (hxp : ∀ t, HasDerivAt xp (ω.hamiltonianVectorField (Hb zero t) (xp t)) t)
    (hndp : IsNondegenerateFixedPt 𝓘(ℝ, V) (ω.timeDependentHamiltonianFlow (Hb zero) hXp 0 1)
      (xp 0))
    {Jm Jp : ℝ → V → AlmostComplexStructure V}
    (hJm : ContDiff ℝ 1 fun p : ℝ × V ↦ (Jm p.1 p.2).toLinearMap.toContinuousLinearMap)
    (hJp : ContDiff ℝ 1 fun p : ℝ × V ↦ (Jp p.1 p.2).toLinearMap.toContinuousLinearMap)
    (hJxm : ∀ t, ω.Compatible (Jm t (xm t))) (hJxp : ∀ t, ω.Compatible (Jp t (xp t)))
    {J : ℝ × ℝ → V → AlmostComplexStructure V} {u : ℝ × ℝ → V}
    (hJ : ∀ z, ContDiffAt ℝ 1
      (fun p : (ℝ × ℝ) × V ↦ (J p.1 p.2).toLinearMap.toContinuousLinearMap) (z, u z)) {R : ℝ}
    (hJRp : ∀ s t, R ≤ s → J (s, t) = Jp t) (hJRm : ∀ s t, s ≤ -R → J (s, t) = Jm t)
    (hu : ContDiff ℝ 1 u) (hJu : ∀ z, ω.Compatible (J z (u z)))
    (huxm : TendstoUniformlyOn (fun s t ↦ u (s, t)) xm atBot (Icc 0 1))
    (huxp : TendstoUniformlyOn (fun s t ↦ u (s, t)) xp atTop (Icc 0 1))
    (hδm : TendstoUniformlyOn
      (fun s t ↦ sliceDefect (fun t ↦ ω.hamiltonianVectorField (Hb inf t)) u (s, t)) 0 atBot
        (Icc 0 1))
    (hδp : TendstoUniformlyOn
      (fun s t ↦ sliceDefect (fun t ↦ ω.hamiltonianVectorField (Hb zero t)) u (s, t)) 0 atTop
        (Icc 0 1)) :
    IsClosed ((ω.floerSobolevOperator
      (fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap)
      (cappedCylinderComponent Hb L 1) (cappedCylinderComponent Hb L Complex.I) u).range :
        Set (Lp V 2 stripMeasure)) :=
  ω.isClosed_range_floerSobolevOperator_of_cylindrical
    (isCylindricalNearEnds_cappedCylinderComponent hHb hHbs hL hJ hJRp hJRm) hu hJu hXm (hHbs inf)
    hxm hndm hJm hJxm huxm hδm hXp (hHbs zero) hxp hndp hJp hJxp huxp hδp

end TauCeti.SymplecticForm
