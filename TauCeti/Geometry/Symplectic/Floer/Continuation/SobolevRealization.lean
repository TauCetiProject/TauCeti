/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.Continuation.SemiFredholm
public import TauCeti.Geometry.Symplectic.Floer.Sobolev.Realization

/-!
# The linearized Floer operator of a continuation cylinder on `W^{1,2}`

A Floer continuation cylinder from `H₋` to `H₊` solves the Floer equation for the `s`-dependent
Hamiltonian `TauCeti.Floer.continuationHomotopy H₋ H₊`, which is `H₋` for `s ≤ 0` and `H₊` for
`s ≥ 1`, with the almost complex structures `TauCeti.Floer.continuationAlmostComplex h₀ J₋ J₊`,
which are `J₋` for `s ≤ 0` and `J₊` for `s ≥ 1`. Counts of rigid continuation cylinders define
the continuation maps between Floer complexes of different Hamiltonians, and their regularity is a
statement about the linearized operator `D_u` of this datum.

This file realizes `D_u` along a continuation cylinder `u` asymptotic to nondegenerate one-periodic
orbits `x₋` of `H₋` at `-∞` and `x₊` of `H₊` at `+∞` as the bounded operator
`TauCeti.SymplecticForm.floerSobolevOperator` from `W^{1,2}(ℝ × S¹, V)` to `L²(ℝ × S¹, V)`, and
proves that

* its coefficients are essentially bounded on the cylinder
  (`TauCeti.SymplecticForm.memLp_floerJetCoeff_continuationHomotopy`), so that it acts on the jet
  of a test section as `D_u`;
* it has finite-dimensional kernel
  (`TauCeti.SymplecticForm.finiteDimensional_ker_floerSobolevOperator_continuationHomotopy`);
* it has closed range
  (`TauCeti.SymplecticForm.isClosed_range_floerSobolevOperator_continuationHomotopy`).

These are the cases `R = 1` of the corresponding statements for Floer data cylindrical near the
ends in `TauCeti.Geometry.Symplectic.Floer.Sobolev.Realization`, whose input is the semi-Fredholm
estimate of `TauCeti.Geometry.Symplectic.Floer.Continuation.SemiFredholm`. The semi-Fredholm
estimate for the formal adjoint `D_u^*` on `C²` covector fields, for Floer data cylindrical near
the ends such as continuation data, is the `_of_cylindrical` version of
`TauCeti.SymplecticForm.exists_forall_setIntegral_le_mul_setIntegral_floerLinearizationAdjoint_add`.
In a unitary trivialization the Fredholm property follows from a parametrix built from the
invertible end models, without the adjoint
(`TauCeti.SymplecticForm.isFredholm_floerSobolevOperator_of_cylindrical` in
`TauCeti.Geometry.Symplectic.Floer.Sobolev.Asymptotic`); the case of a general `J` and the value
of the index remain open.

## References

* D. Salamon, *Lectures on Floer homology*, in *Symplectic geometry and topology*, IAS/Park City
  Math. Ser. 7 (1999), Lectures 2 and 3, on the Fredholm property of the linearized operator and
  on continuation maps.
* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, 2nd ed., Section 3.1
  and Appendix B, on the semi-Fredholm estimate and Peetre's argument.
-/

public section

open Set Filter MeasureTheory
open scoped NNReal ENNReal Manifold

namespace TauCeti.SymplecticForm

open CylinderSobolev Floer
open StripSobolev (stripMeasure)

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

/-- **The coefficients of the linearized Floer operator along a continuation cylinder are
bounded.** Let `H₋`, `H₊` be jointly `C²` Hamiltonians and `J₋_t(y)`, `J₊_t(y)` be `C¹` families of
`ω`-tame almost complex structures. Let `u` be a `C¹` map whose loops converge uniformly at both
ends, with slice defect `∂t u - X_{H₋_t}(u)` tending uniformly to zero at `-∞` and
`∂t u - X_{H₊_t}(u)` at `+∞`. Then the coefficient field on jets of the linearized Floer operator
of the continuation datum `K = H_{(s, t)} dt`, `H = continuationHomotopy H₋ H₊`, with the
continuation homotopy of almost complex structures from `J₋` to `J₊`, is essentially bounded on
the cylinder. -/
theorem memLp_floerJetCoeff_continuationHomotopy (ω : SymplecticForm V)
    {J₀ : AlmostComplexStructure V} (h₀ : ω.Compatible J₀)
    {Jm Jp : ℝ → V → AlmostComplexStructure V} {hJmt : ∀ t x, ω.Tames (Jm t x)}
    {hJpt : ∀ t x, ω.Tames (Jp t x)}
    (hJm : ContDiff ℝ 1 fun p : ℝ × V ↦ (Jm p.1 p.2).toLinearMap.toContinuousLinearMap)
    (hJp : ContDiff ℝ 1 fun p : ℝ × V ↦ (Jp p.1 p.2).toLinearMap.toContinuousLinearMap)
    {Hm Hp : ℝ → V → ℝ} (hHm : ContDiff ℝ 2 (Function.uncurry Hm))
    (hHp : ContDiff ℝ 2 (Function.uncurry Hp)) {xm xp : ℝ → V} {u : ℝ × ℝ → V}
    (hu : ContDiff ℝ 1 u) (huxm : TendstoUniformlyOn (fun s t ↦ u (s, t)) xm atBot (Icc 0 1))
    (hδm : TendstoUniformlyOn
      (fun s t ↦ sliceDefect (fun t ↦ ω.hamiltonianVectorField (Hm t)) u (s, t)) 0 atBot
        (Icc 0 1))
    (huxp : TendstoUniformlyOn (fun s t ↦ u (s, t)) xp atTop (Icc 0 1))
    (hδp : TendstoUniformlyOn
      (fun s t ↦ sliceDefect (fun t ↦ ω.hamiltonianVectorField (Hp t)) u (s, t)) 0 atTop
        (Icc 0 1)) :
    MemLp (ω.floerJetCoeff
      (fun w y ↦ (continuationAlmostComplex h₀ Jm Jp hJmt hJpt w y).toLinearMap
        |>.toContinuousLinearMap)
      (fun _ _ ↦ 0) (continuationHomotopy Hm Hp) u) ∞ stripMeasure :=
  ω.memLp_floerJetCoeff_of_cylindrical
    (isCylindricalNearEnds_continuationHomotopy h₀ hJm hJp hHm hHp u) hu hHm hJm huxm hδm hHp hJp
    huxp hδp

/-- **The linearized Floer operator along a continuation cylinder has finite-dimensional kernel on
`W^{1,2}`.** Under the hypotheses of the semi-Fredholm estimate
`exists_forall_setIntegral_le_mul_setIntegral_floerLinearization_continuationHomotopy_add` (a map
`u` along which the continuation homotopy of almost complex structures is `ω`-compatible,
asymptotic at `-∞` to a nondegenerate one-periodic orbit `x₋` of `H₋` and at `+∞` to a
nondegenerate one-periodic orbit `x₊` of `H₊`), the realization
`D_u : W^{1,2}(ℝ × S¹, V) → L²(ℝ × S¹, V)` of the linearized Floer operator of the continuation
datum has finite-dimensional kernel. -/
theorem finiteDimensional_ker_floerSobolevOperator_continuationHomotopy (ω : SymplecticForm V)
    {J₀ : AlmostComplexStructure V} (h₀ : ω.Compatible J₀)
    {Jm Jp : ℝ → V → AlmostComplexStructure V} {hJmt : ∀ t x, ω.Tames (Jm t x)}
    {hJpt : ∀ t x, ω.Tames (Jp t x)}
    (hJm : ContDiff ℝ 1 fun p : ℝ × V ↦ (Jm p.1 p.2).toLinearMap.toContinuousLinearMap)
    (hJp : ContDiff ℝ 1 fun p : ℝ × V ↦ (Jp p.1 p.2).toLinearMap.toContinuousLinearMap)
    {Hm Hp : ℝ → V → ℝ} {Km Kp : ℝ≥0}
    (hXm : LipschitzWith Km (ω.timeDependentHamiltonianSuspension Hm))
    (hHm : ContDiff ℝ 2 (Function.uncurry Hm))
    (hXp : LipschitzWith Kp (ω.timeDependentHamiltonianSuspension Hp))
    (hHp : ContDiff ℝ 2 (Function.uncurry Hp)) {xm xp : ℝ → V}
    (hxm : ∀ t, HasDerivAt xm (ω.hamiltonianVectorField (Hm t) (xm t)) t)
    (hndm : IsNondegenerateFixedPt 𝓘(ℝ, V) (ω.timeDependentHamiltonianFlow Hm hXm 0 1) (xm 0))
    (hJxm : ∀ t, ω.Compatible (Jm t (xm t)))
    (hxp : ∀ t, HasDerivAt xp (ω.hamiltonianVectorField (Hp t) (xp t)) t)
    (hndp : IsNondegenerateFixedPt 𝓘(ℝ, V) (ω.timeDependentHamiltonianFlow Hp hXp 0 1) (xp 0))
    (hJxp : ∀ t, ω.Compatible (Jp t (xp t))) {u : ℝ × ℝ → V} (hu : ContDiff ℝ 1 u)
    (hJu : ∀ z, ω.Compatible (continuationAlmostComplex h₀ Jm Jp hJmt hJpt z (u z)))
    (huxm : TendstoUniformlyOn (fun s t ↦ u (s, t)) xm atBot (Icc 0 1))
    (hδm : TendstoUniformlyOn
      (fun s t ↦ sliceDefect (fun t ↦ ω.hamiltonianVectorField (Hm t)) u (s, t)) 0 atBot
        (Icc 0 1))
    (huxp : TendstoUniformlyOn (fun s t ↦ u (s, t)) xp atTop (Icc 0 1))
    (hδp : TendstoUniformlyOn
      (fun s t ↦ sliceDefect (fun t ↦ ω.hamiltonianVectorField (Hp t)) u (s, t)) 0 atTop
        (Icc 0 1)) :
    FiniteDimensional ℝ (ω.floerSobolevOperator
      (fun w y ↦ (continuationAlmostComplex h₀ Jm Jp hJmt hJpt w y).toLinearMap
        |>.toContinuousLinearMap)
      (fun _ _ ↦ 0) (continuationHomotopy Hm Hp) u).ker :=
  ω.finiteDimensional_ker_floerSobolevOperator_of_cylindrical
    (isCylindricalNearEnds_continuationHomotopy h₀ hJm hJp hHm hHp u) hu hJu hXm hHm hxm hndm hJm
    hJxm huxm hδm hXp hHp hxp hndp hJp hJxp huxp hδp

/-- **The linearized Floer operator along a continuation cylinder has closed range on
`W^{1,2}`.** Under the hypotheses of
`finiteDimensional_ker_floerSobolevOperator_continuationHomotopy`, the realization
`D_u : W^{1,2}(ℝ × S¹, V) → L²(ℝ × S¹, V)` of the linearized Floer operator of the continuation
datum has closed range. -/
theorem isClosed_range_floerSobolevOperator_continuationHomotopy (ω : SymplecticForm V)
    {J₀ : AlmostComplexStructure V} (h₀ : ω.Compatible J₀)
    {Jm Jp : ℝ → V → AlmostComplexStructure V} {hJmt : ∀ t x, ω.Tames (Jm t x)}
    {hJpt : ∀ t x, ω.Tames (Jp t x)}
    (hJm : ContDiff ℝ 1 fun p : ℝ × V ↦ (Jm p.1 p.2).toLinearMap.toContinuousLinearMap)
    (hJp : ContDiff ℝ 1 fun p : ℝ × V ↦ (Jp p.1 p.2).toLinearMap.toContinuousLinearMap)
    {Hm Hp : ℝ → V → ℝ} {Km Kp : ℝ≥0}
    (hXm : LipschitzWith Km (ω.timeDependentHamiltonianSuspension Hm))
    (hHm : ContDiff ℝ 2 (Function.uncurry Hm))
    (hXp : LipschitzWith Kp (ω.timeDependentHamiltonianSuspension Hp))
    (hHp : ContDiff ℝ 2 (Function.uncurry Hp)) {xm xp : ℝ → V}
    (hxm : ∀ t, HasDerivAt xm (ω.hamiltonianVectorField (Hm t) (xm t)) t)
    (hndm : IsNondegenerateFixedPt 𝓘(ℝ, V) (ω.timeDependentHamiltonianFlow Hm hXm 0 1) (xm 0))
    (hJxm : ∀ t, ω.Compatible (Jm t (xm t)))
    (hxp : ∀ t, HasDerivAt xp (ω.hamiltonianVectorField (Hp t) (xp t)) t)
    (hndp : IsNondegenerateFixedPt 𝓘(ℝ, V) (ω.timeDependentHamiltonianFlow Hp hXp 0 1) (xp 0))
    (hJxp : ∀ t, ω.Compatible (Jp t (xp t))) {u : ℝ × ℝ → V} (hu : ContDiff ℝ 1 u)
    (hJu : ∀ z, ω.Compatible (continuationAlmostComplex h₀ Jm Jp hJmt hJpt z (u z)))
    (huxm : TendstoUniformlyOn (fun s t ↦ u (s, t)) xm atBot (Icc 0 1))
    (hδm : TendstoUniformlyOn
      (fun s t ↦ sliceDefect (fun t ↦ ω.hamiltonianVectorField (Hm t)) u (s, t)) 0 atBot
        (Icc 0 1))
    (huxp : TendstoUniformlyOn (fun s t ↦ u (s, t)) xp atTop (Icc 0 1))
    (hδp : TendstoUniformlyOn
      (fun s t ↦ sliceDefect (fun t ↦ ω.hamiltonianVectorField (Hp t)) u (s, t)) 0 atTop
        (Icc 0 1)) :
    IsClosed ((ω.floerSobolevOperator
      (fun w y ↦ (continuationAlmostComplex h₀ Jm Jp hJmt hJpt w y).toLinearMap
        |>.toContinuousLinearMap)
      (fun _ _ ↦ 0) (continuationHomotopy Hm Hp) u).range : Set (Lp V 2 stripMeasure)) :=
  ω.isClosed_range_floerSobolevOperator_of_cylindrical
    (isCylindricalNearEnds_continuationHomotopy h₀ hJm hJp hHm hHp u) hu hJu hXm hHm hxm hndm hJm
    hJxm huxm hδm hXp hHp hxp hndp hJp hJxp huxp hδp

end TauCeti.SymplecticForm
