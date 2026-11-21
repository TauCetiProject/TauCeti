/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.CappedCylinder
public import TauCeti.Geometry.Symplectic.Floer.SemiFredholm

/-!
# The semi-Fredholm estimate of the linearized operator of the pair of pants capped at `1`

Plumbing the negative PSS plane with Hamiltonian `H_1` into the input end at `1` of the pair of
pants `ℂ ∖ {0, 1}` with Hamiltonians `H_0`, `H_1`, `H_∞` gives a Floer datum on a cylinder whose
two ends are the remaining input at `0` and the output at `∞`. On the standard cylinder its
perturbation one-form has the components `TauCeti.Floer.cappedCylinderComponent Hb L 1` and
`TauCeti.Floer.cappedCylinderComponent Hb L Complex.I`
(`TauCeti.Geometry.Symplectic.Floer.PairOfPants.CappedCylinder`); it is `H_0(t) dt` for `s ≥ 2`
and `H_∞(t) dt` for `s ≤ -3`, and arbitrary in between. Its solutions are the cylinders counted in
the unit property of the pair-of-pants product, which compares them with continuation cylinders
between `H_∞` and `H_0`, and, like those, they are not divided by translations.

This file proves the estimate behind the Fredholm property of the linearized operator `D_u` of
this datum, for any almost complex structures `J(z)` that are cylindrical on the two ends and
compatible along `u`: when the loops of `u` converge to a nondegenerate orbit of `H_0` as
`s → ∞` and to a nondegenerate orbit of `H_∞` as `s → -∞`, there are `C ≥ 0` and `T` such that

`∫ (‖∂s ξ‖² + ‖∂t ξ‖² + ‖ξ‖²) ≤ C (∫ ‖D_u ξ‖² + ∫_{[-T, T] × [0, 1]} ‖ξ‖²)`

for every `C²` section `ξ` of period one in `t` vanishing outside a strip `(a, b) × ℝ`, with the
integrals over `[a, b] × [0, 1]`
(`exists_forall_setIntegral_le_mul_setIntegral_floerLinearization_cappedCylinderComponent_add`, in
the namespace `TauCeti.SymplecticForm`). The estimate holds at every neck length `L > 4`, where the
capped datum is smooth. It is the estimate for data that are cylindrical on the ends,
`exists_forall_setIntegral_le_mul_setIntegral_floerLinearization_add_of_cylindrical`.

## References

* S. Piunikhin, D. Salamon and M. Schwarz, *Symplectic Floer–Donaldson theory and quantum
  cohomology*, in *Contact and symplectic geometry*, Publ. Newton Inst. 8 (1996), 171–200, on the
  unit of the pair-of-pants product.
* D. Salamon, *Lectures on Floer homology*, in *Symplectic geometry and topology*, IAS/Park City
  Math. Ser. 7 (1999), Lecture 2, on the Fredholm property of `∂s + J ∂t + S(s, t)`.
-/

public section

open Filter Set Function
open scoped NNReal Manifold
open TauCeti.ThricePuncturedSphere TauCeti.ThricePuncturedSphere.Puncture

namespace TauCeti.SymplecticForm

open Floer

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

/-- **The semi-Fredholm estimate along the pair of pants capped at `1`.** Let `Hb r` be jointly
`C²` Hamiltonians of period one in `t`, with the suspended vector fields of `Hb 0` and `Hb ∞`
globally Lipschitz, and let `L > 4`. Let `J(z)` be almost complex structures on the cylinder, `C¹`
along `u`, equal to a `C¹` family `Jp_t` for `s ≥ R` and to a `C¹` family `Jm_t` for `s ≤ -R`.
Let `u : ℝ × ℝ → V` be a `C¹` map along which `J` is `ω`-compatible, whose loops converge
uniformly to an orbit `xp` of `Hb 0` at `+∞` and to an orbit `xm` of `Hb ∞` at `-∞`, starting at
nondegenerate fixed points of the time-one maps, with `Jp_t`, `Jm_t` compatible along them, while
the slice defects `∂t u - X_{Hb 0}(u)` and `∂t u - X_{Hb ∞}(u)` tend uniformly to zero at the
respective ends. Then there are `C ≥ 0` and `T` such that every `C²` map `ξ` of period one in `t`
that vanishes for `s ∉ (a, b)` satisfies

`∫ (‖∂s ξ‖² + ‖∂t ξ‖² + ‖ξ‖²) ≤ C (∫ ‖D_u ξ‖² + ∫_{[-T, T] × [0, 1]} ‖ξ‖²)`

over `[a, b] × [0, 1]`, for the linearized Floer operator `D_u` of `J` and of the datum of the
pair of pants with Hamiltonians `Hb` capped at `1` along a neck of length `L`. -/
theorem exists_forall_setIntegral_le_mul_setIntegral_floerLinearization_cappedCylinderComponent_add
    (ω : SymplecticForm V) {Hb : Puncture → ℝ → V → ℝ} (hHb : ∀ r, Periodic (Hb r) 1)
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
    ∃ C, 0 ≤ C ∧ ∃ T, ∀ ⦃ξ : ℝ × ℝ → V⦄, ContDiff ℝ 2 ξ → (∀ s t, ξ (s, t + 1) = ξ (s, t)) →
      ∀ ⦃a b : ℝ⦄, a ≤ b → (∀ s t, s ∉ Ioo a b → ξ (s, t) = 0) →
        ∫ z in Icc a b ×ˢ Icc (0 : ℝ) 1, (‖fderiv ℝ ξ z stdComplexLineReal‖ ^ 2 +
            ‖fderiv ℝ ξ z stdComplexLineImag‖ ^ 2 + ‖ξ z‖ ^ 2) ≤
          C * ((∫ z in Icc a b ×ˢ Icc (0 : ℝ) 1, ‖ω.floerLinearization
            (fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap)
            (cappedCylinderComponent Hb L 1) (cappedCylinderComponent Hb L Complex.I) u ξ z‖ ^ 2) +
            ∫ z in Icc (-T) T ×ˢ Icc (0 : ℝ) 1, ‖ξ z‖ ^ 2) := by
  have hL₂ : 2 ≤ L := by linarith
  have hK (v : ℂ) : ContDiff ℝ 2 (uncurry (cappedCylinderComponent Hb L v)) :=
    contDiff_uncurry_cappedCylinderComponent hHb hHbs hL v
  -- Beyond `max R 3` the datum is `Hb 0 (t) dt` on the input end and `Hb ∞ (t) dt` on the output.
  have hp (v : ℂ) (s t : ℝ) (hs : max R 3 ≤ s) :
      cappedCylinderComponent Hb L v (s, t) = fun x ↦ v.im * Hb zero t x :=
    funext (cappedCylinderComponent_of_two_le (hHb zero) hL₂ (z := (s, t))
      (by linarith [le_max_right R 3]) v)
  have hm (v : ℂ) (s t : ℝ) (hs : s ≤ -max R 3) :
      cappedCylinderComponent Hb L v (s, t) = fun x ↦ v.im * Hb inf t x :=
    funext (cappedCylinderComponent_of_le_neg_three (hHb inf) hL₂ (z := (s, t))
      (by linarith [le_max_right R 3]) v)
  refine ω.exists_forall_setIntegral_le_mul_setIntegral_floerLinearization_add_of_cylindrical
    (R := max R 3) ⟨fun ⟨s, t⟩ hs ↦ hJRm s t (hs.trans (neg_le_neg (le_max_left _ _))),
      fun ⟨s, t⟩ hs ↦ hJRp s t ((le_max_left _ _).trans hs), fun ⟨s, t⟩ hs ↦ ?_,
      fun ⟨s, t⟩ hs ↦ by simp [hm _ s t hs], fun ⟨s, t⟩ hs ↦ by simp [hp _ s t hs], hJ,
      fun _ ↦ (hK 1).contDiffAt, fun _ ↦ (hK Complex.I).contDiffAt⟩
    hu hJu hXm (hHbs inf) hxm hndm hJm hJxm huxm hδm hXp (hHbs zero) hxp hndp hJp hJxp huxp hδp
  funext x
  rw [mem_Ioo, not_and_or, not_lt, not_lt] at hs
  rcases hs with hs | hs
  · simp [hm 1 s t hs]
  · simp [hp 1 s t hs]

end TauCeti.SymplecticForm
