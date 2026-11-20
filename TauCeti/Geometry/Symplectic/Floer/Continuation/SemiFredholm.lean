/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.Continuation
public import TauCeti.Geometry.Symplectic.Floer.Continuation.AlmostComplex
public import TauCeti.Geometry.Symplectic.Floer.SemiFredholm

/-!
# The semi-Fredholm estimate of the linearized Floer operator along a continuation cylinder

A Floer continuation cylinder from `H₋` to `H₊` solves the Floer equation for the
`s`-dependent Hamiltonian `TauCeti.Floer.continuationHomotopy H₋ H₊`, which is `H₋` for `s ≤ 0`
and `H₊` for `s ≥ 1`, with the almost complex structures
`TauCeti.Floer.continuationAlmostComplex h₀ J₋ J₊`, which are `J₋` for `s ≤ 0` and `J₊` for
`s ≥ 1`. These data are cylindrical outside `[0, 1] × S¹`, with different Hamiltonians and
almost complex structures at the two ends, so the semi-Fredholm estimate for data that are
cylindrical near the ends,
`exists_forall_setIntegral_le_mul_setIntegral_floerLinearization_add_of_cylindrical`
in `TauCeti.Geometry.Symplectic.Floer.SemiFredholm`, applies to them. This file records the
resulting estimate for the linearized operator `D_u` along a map `u` of the cylinder asymptotic to
a nondegenerate one-periodic orbit `x₋` of `H₋` at `-∞` and to a nondegenerate one-periodic orbit
`x₊` of `H₊` at `+∞`: there are `C ≥ 0` and `T` such that

`∫ (‖∂s ξ‖² + ‖∂t ξ‖² + ‖ξ‖²) ≤ C (∫ ‖D_u ξ‖² + ∫_{[-T, T] × [0, 1]} ‖ξ‖²)`

for every `C²` section `ξ` of period one in `t` vanishing outside a strip `(a, b) × ℝ`
(`exists_forall_setIntegral_le_mul_setIntegral_floerLinearization_continuationHomotopy_add`, in
the namespace `TauCeti.SymplecticForm`).
This is the a priori estimate behind finite dimensional kernel and closed range of the linearized
operator of continuation cylinders, whose counts define continuation maps. The Sobolev completion
and the Fredholm property itself are not treated here.

## References

* D. Salamon, *Lectures on Floer homology*, in *Symplectic geometry and topology*, IAS/Park City
  Math. Ser. 7 (1999), Lectures 2 and 3, on the Fredholm property of the linearized operator and
  on continuation maps.
-/

public section

open Set Filter
open scoped NNReal Manifold

namespace TauCeti.SymplecticForm

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

open Floer in
/-- **The semi-Fredholm estimate along a continuation cylinder.** Let `H₋`, `H₊` be jointly `C²`
Hamiltonians with globally Lipschitz suspended vector fields, and `J₋_t(y)`, `J₊_t(y)` be `C¹`
families of `ω`-tame almost complex structures. Let `u : ℝ × ℝ → V` be a `C¹` map along which the
continuation homotopy of almost complex structures from `J₋` to `J₊` is `ω`-compatible, whose
loops converge uniformly at `-∞` to an orbit `x₋` of `H₋` and at `+∞` to an orbit `x₊` of `H₊`,
starting at nondegenerate fixed points of the time-one maps and along which `J₋`, respectively
`J₊`, is compatible, while the slice defects `∂t u - X_{H±_t}(u)` tend uniformly to zero there.
Then there are `C ≥ 0` and `T` such that every `C²` map `ξ` of period one in `t` vanishing for
`s ∉ (a, b)` satisfies

`∫ (‖∂s ξ‖² + ‖∂t ξ‖² + ‖ξ‖²) ≤ C (∫ ‖D_u ξ‖² + ∫_{[-T, T] × [0, 1]} ‖ξ‖²)`

over `[a, b] × [0, 1]`, for the linearized Floer operator `D_u` of the continuation datum
`K = H_{(s, t)} dt`, `H = continuationHomotopy H₋ H₊`. -/
theorem exists_forall_setIntegral_le_mul_setIntegral_floerLinearization_continuationHomotopy_add
    (ω : SymplecticForm V) {J₀ : AlmostComplexStructure V} (h₀ : ω.Compatible J₀)
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
    ∃ C, 0 ≤ C ∧ ∃ T, ∀ ⦃ξ : ℝ × ℝ → V⦄, ContDiff ℝ 2 ξ → (∀ s t, ξ (s, t + 1) = ξ (s, t)) →
      ∀ ⦃a b : ℝ⦄, a ≤ b → (∀ s t, s ∉ Ioo a b → ξ (s, t) = 0) →
        ∫ z in Icc a b ×ˢ Icc (0 : ℝ) 1, (‖fderiv ℝ ξ z stdComplexLineReal‖ ^ 2 +
            ‖fderiv ℝ ξ z stdComplexLineImag‖ ^ 2 + ‖ξ z‖ ^ 2) ≤
          C * ((∫ z in Icc a b ×ˢ Icc (0 : ℝ) 1, ‖ω.floerLinearization
            (fun w y ↦ (continuationAlmostComplex h₀ Jm Jp hJmt hJpt w y).toLinearMap
              |>.toContinuousLinearMap)
            (fun _ _ ↦ 0) (continuationHomotopy Hm Hp) u ξ z‖ ^ 2) +
            ∫ z in Icc (-T) T ×ˢ Icc (0 : ℝ) 1, ‖ξ z‖ ^ 2) :=
  ω.exists_forall_setIntegral_le_mul_setIntegral_floerLinearization_add_of_cylindrical
    (Ks := fun _ _ ↦ 0) (R := 1)
    (fun _ hz ↦ funext (continuationAlmostComplex_of_nonpos h₀ (by linarith)))
    (fun _ hz ↦ funext (continuationAlmostComplex_of_one_le h₀ hz)) (fun _ _ ↦ rfl)
    (fun _ hz ↦ funext (continuationHomotopy_of_nonpos (by linarith)))
    (fun _ hz ↦ funext (continuationHomotopy_of_one_le hz))
    (fun _ ↦ (contDiff_continuationAlmostComplex h₀ hJm hJp).contDiffAt)
    (fun _ ↦ contDiffAt_const) (fun _ ↦ (contDiff_uncurry_continuationHomotopy hHm hHp).contDiffAt)
    hu hJu hXm hHm hxm hndm hJm hJxm huxm hδm hXp hHp hxp hndp hJp hJxp huxp hδp

end TauCeti.SymplecticForm
