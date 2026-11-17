/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.Continuation
public import TauCeti.Geometry.Symplectic.Floer.Continuation.AlmostComplex
public import TauCeti.Geometry.Symplectic.Floer.SemiFredholm
import TauCeti.Geometry.Manifold.ContMDiff.Prod

/-!
# The semi-Fredholm estimate of the linearized operator of a continuation cylinder

A Floer continuation map between the Hamiltonians `Hm` and `Hp` counts continuation cylinders:
solutions `u : ℝ × ℝ → V`, of period one in `t`, of

`∂_s u + J_{(s, t)}(u) (∂_t u - X_{H_{(s, t)}}(u)) = 0`

for the continuation homotopy `H = TauCeti.Floer.continuationHomotopy Hm Hp`, equal to `Hm` for
`s ≤ 0` and to `Hp` for `s ≥ 1`, and the continuation homotopy
`J = TauCeti.Floer.continuationAlmostComplex h₀ Jm Jp` of `ω`-compatible families of almost
complex structures. With the conventions of `TauCeti.Geometry.Symplectic.Floer.SemiFredholm`, the
loops of `u` converge to an orbit `xm` of `Hm` as `s → -∞` and to an orbit `xp` of `Hp` as
`s → ∞`.

Unlike a Floer trajectory, a continuation cylinder is not invariant under translation in `s`, so
its moduli spaces are not divided by translations. This file proves the estimate behind the
Fredholm property of its linearized operator `D_u`: when `xm` and `xp` are nondegenerate there are
`C ≥ 0` and `T` such that

`∫ (‖∂s ξ‖² + ‖∂t ξ‖² + ‖ξ‖²) ≤ C (∫ ‖D_u ξ‖² + ∫_{[-T, T] × [0, 1]} ‖ξ‖²)`

for every `C²` section `ξ` of period one in `t` vanishing outside a strip `(a, b) × ℝ`, with the
integrals over `[a, b] × [0, 1]`
(`exists_forall_setIntegral_le_mul_setIntegral_floerLinearization_continuationHomotopy_add`, in
the namespace `TauCeti.SymplecticForm`). It is the estimate for data that are cylindrical on the
ends, `exists_forall_setIntegral_le_mul_setIntegral_floerLinearization_add_of_cylindrical`, applied
with `R = 1`. The almost complex structures are compatible everywhere, so `J` is
compatible along `u`, and they are as smooth as `Jm` and `Jp`
(`TauCeti.Floer.contMDiff_continuationAlmostComplex`).

## References

* D. Salamon, *Lectures on Floer homology*, in *Symplectic geometry and topology*, IAS/Park City
  Math. Ser. 7 (1999), Lecture 2, on the Fredholm property of `∂s + J ∂t + S(s, t)` and
  continuation maps.
-/

public section

open Filter Set Function
open scoped NNReal Manifold

namespace TauCeti.SymplecticForm

open Floer

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

/-- **The semi-Fredholm estimate along a continuation cylinder.** Let `Hm` and `Hp` be jointly
`C²` Hamiltonians whose suspended vector fields are globally Lipschitz, and let `Jm`, `Jp` be `C¹`
families of `ω`-compatible almost complex structures. Let `u : ℝ × ℝ → V` be a `C¹` map whose
loops converge uniformly to an orbit `xm` of `Hm` at `-∞` and to an orbit `xp` of `Hp` at `+∞`,
starting at nondegenerate fixed points of the time-one maps, while the slice defects
`∂t u - X_{Hm_t}(u)` and `∂t u - X_{Hp_t}(u)` tend uniformly to zero at the respective ends, as
for a continuation cylinder from `xm` to `xp`. Then there are `C ≥ 0` and `T` such that every
`C²` map `ξ` of period one in `t` that vanishes for `s ∉ (a, b)` satisfies

`∫ (‖∂s ξ‖² + ‖∂t ξ‖² + ‖ξ‖²) ≤ C (∫ ‖D_u ξ‖² + ∫_{[-T, T] × [0, 1]} ‖ξ‖²)`

over `[a, b] × [0, 1]`, for the linearized Floer operator `D_u` of the continuation homotopies
`K = H_{(s, t)} dt` from `Hm` to `Hp` and `J` from `Jm` to `Jp`. -/
theorem exists_forall_setIntegral_le_mul_setIntegral_floerLinearization_continuationHomotopy_add
    (ω : SymplecticForm V) {Hm Hp : ℝ → V → ℝ} {Km Kp : ℝ≥0}
    (hXm : LipschitzWith Km (ω.timeDependentHamiltonianSuspension Hm))
    (hXp : LipschitzWith Kp (ω.timeDependentHamiltonianSuspension Hp))
    (hHm : ContDiff ℝ 2 (uncurry Hm)) (hHp : ContDiff ℝ 2 (uncurry Hp)) {xm xp : ℝ → V}
    (hxm : ∀ t, HasDerivAt xm (ω.hamiltonianVectorField (Hm t) (xm t)) t)
    (hndm : IsNondegenerateFixedPt 𝓘(ℝ, V) (ω.timeDependentHamiltonianFlow Hm hXm 0 1) (xm 0))
    (hxp : ∀ t, HasDerivAt xp (ω.hamiltonianVectorField (Hp t) (xp t)) t)
    (hndp : IsNondegenerateFixedPt 𝓘(ℝ, V) (ω.timeDependentHamiltonianFlow Hp hXp 0 1) (xp 0))
    {J₀ : AlmostComplexStructure V} (h₀ : ω.Compatible J₀)
    {Jm Jp : ℝ → V → AlmostComplexStructure V} (hJmc : ∀ t x, ω.Compatible (Jm t x))
    (hJpc : ∀ t x, ω.Compatible (Jp t x))
    (hJm : ContDiff ℝ 1 fun p : ℝ × V ↦ (Jm p.1 p.2).toLinearMap.toContinuousLinearMap)
    (hJp : ContDiff ℝ 1 fun p : ℝ × V ↦ (Jp p.1 p.2).toLinearMap.toContinuousLinearMap)
    {u : ℝ × ℝ → V} (hu : ContDiff ℝ 1 u)
    (huxm : TendstoUniformlyOn (fun s t ↦ u (s, t)) xm atBot (Icc 0 1))
    (huxp : TendstoUniformlyOn (fun s t ↦ u (s, t)) xp atTop (Icc 0 1))
    (hδm : TendstoUniformlyOn
      (fun s t ↦ sliceDefect (fun t ↦ ω.hamiltonianVectorField (Hm t)) u (s, t)) 0 atBot
        (Icc 0 1))
    (hδp : TendstoUniformlyOn
      (fun s t ↦ sliceDefect (fun t ↦ ω.hamiltonianVectorField (Hp t)) u (s, t)) 0 atTop
        (Icc 0 1)) :
    ∃ C, 0 ≤ C ∧ ∃ T, ∀ ⦃ξ : ℝ × ℝ → V⦄, ContDiff ℝ 2 ξ → (∀ s t, ξ (s, t + 1) = ξ (s, t)) →
      ∀ ⦃a b : ℝ⦄, a ≤ b → (∀ s t, s ∉ Ioo a b → ξ (s, t) = 0) →
        ∫ z in Icc a b ×ˢ Icc (0 : ℝ) 1, (‖fderiv ℝ ξ z stdComplexLineReal‖ ^ 2 +
            ‖fderiv ℝ ξ z stdComplexLineImag‖ ^ 2 + ‖ξ z‖ ^ 2) ≤
          C * ((∫ z in Icc a b ×ˢ Icc (0 : ℝ) 1, ‖ω.floerLinearization
            (fun w y ↦ (continuationAlmostComplex h₀ Jm Jp (fun t x ↦ (hJmc t x).tames)
              (fun t x ↦ (hJpc t x).tames) w y).toLinearMap.toContinuousLinearMap)
            (fun _ _ ↦ 0) (continuationHomotopy Hm Hp) u ξ z‖ ^ 2) +
            ∫ z in Icc (-T) T ×ˢ Icc (0 : ℝ) 1, ‖ξ z‖ ^ 2) := by
  have hJ : ContDiff ℝ 1 fun p : (ℝ × ℝ) × V ↦
      (continuationAlmostComplex h₀ Jm Jp (fun t x ↦ (hJmc t x).tames)
        (fun t x ↦ (hJpc t x).tames) p.1 p.2).toLinearMap.toContinuousLinearMap :=
    (contMDiff_prod_modelWithCornersSelf_iff.1 (contMDiff_continuationAlmostComplex h₀
      (contMDiff_prod_modelWithCornersSelf_iff.2 hJm.contMDiff)
      (contMDiff_prod_modelWithCornersSelf_iff.2 hJp.contMDiff))).contDiff
  exact ω.exists_forall_setIntegral_le_mul_setIntegral_floerLinearization_add_of_cylindrical hXm hXp
    hHm hHp hxm hndm hxp hndp hJm hJp (fun t ↦ hJmc t (xm t)) (fun t ↦ hJpc t (xp t))
    (fun _ ↦ hJ.contDiffAt) (fun _ ↦ contDiffAt_const)
    (fun _ ↦ (contDiff_uncurry_continuationHomotopy hHm hHp).contDiffAt) (R := 1)
    (fun s t hs ↦ funext (continuationAlmostComplex_of_one_le h₀ (z := (s, t)) hs))
    (fun s t hs ↦ funext (continuationAlmostComplex_of_nonpos h₀ (z := (s, t)) (by linarith)))
    (fun _ _ _ ↦ rfl) (fun s t hs ↦ funext (continuationHomotopy_of_one_le (z := (s, t)) hs))
    (fun s t hs ↦ funext (continuationHomotopy_of_nonpos (z := (s, t)) (by linarith))) hu
    (fun z ↦ compatible_continuationAlmostComplex h₀ hJmc hJpc z (u z)) huxm huxp hδm hδp

end TauCeti.SymplecticForm
