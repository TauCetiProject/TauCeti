/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.CongruenceSubgroups.FunctionField.Basic
import TauCeti.Analysis.Complex.Fuchsian.Arithmetic
import TauCeti.Analysis.Complex.Fuchsian.Compactification.Extension

/-!
# Modular functions of level `N` from invariant functions on the upper half-plane

A holomorphic function `f` on the upper half-plane that is invariant under the principal
congruence subgroup `Γ(N)` is a function on the open modular curve `Γ(N) \ ℍ`. It extends to a
meromorphic function on the compactified modular curve `X(N)` as soon as it has at most
exponential growth at every cusp. The cusps of `Γ(N)` are the orbits of the points `γ • ∞` for
`γ ∈ SL(2, ℤ)`, and at the cusp of `γ • ∞` the function is read through `τ ↦ f (γ • τ)`, so the
condition is that each `τ ↦ f (γ • τ)` is `O(exp (c Im τ))` at `i∞` for some real `c`. Such a
bound forces at most a pole at the cusp, since `exp (c Im τ)` is a power of `|q_N|⁻¹` up to a
bounded factor.

This file packages the extension (`TauCeti.meromorphicFunctionOfGammaInvariant`), so that a
modular function of level `N` can be produced from its formula on the upper half-plane, its
transformation law under `Γ(N)` and its growth at `i∞`. The action of `SL(2, ℤ)` on the result
is computed on the upper half-plane by `TauCeti.modularFunctionAction_apply_ofQuotient`.

## Main declarations

* `TauCeti.meromorphicFunctionOfGammaInvariant`: the meromorphic function on `X(N)` defined by a
  holomorphic `Γ(N)`-invariant function of exponential growth at every cusp.
* `TauCeti.meromorphicFunctionOfGammaInvariant_ofQuotient_mk`: its value at the orbit of `τ` is
  `f τ`.
-/

public noncomputable section

open Asymptotics CongruenceSubgroup Filter UpperHalfPlane
open Subgroup.CompactifiedQuotient TauCeti.RiemannSurface
open scoped Manifold MatrixGroups

namespace TauCeti

variable {N : ℕ} {f : ℍ → ℂ}

/-- A `Γ(N)`-invariant function is invariant under the effective image of `Γ(N)`. -/
private theorem apply_smul_of_mem_map
    (hinv : ∀ γ ∈ Gamma N, ∀ τ : ℍ, f (γ • τ) = f τ) {g : PSL(2, ℝ)}
    (hg : g ∈ (Gamma N).map sl2zToPSL2R) (τ : ℍ) : f (g • τ) = f τ := by
  obtain ⟨γ, hγ, rfl⟩ := hg
  rw [UpperHalfPlane.sl2zToPSL2R_smul, hinv γ hγ]

/-- A `Γ(N)`-invariant function as a function on `X(N)`. Its value at the cusps is `0`; it only
matters through its germs there, which do not see it. -/
private def compactifiedOfInvariant (f : ℍ → ℂ)
    (hinv : ∀ γ ∈ Gamma N, ∀ τ : ℍ, f (γ • τ) = f τ) :
    ((Gamma N).map sl2zToPSL2R).CompactifiedQuotient → ℂ
  | .ofQuotient p => Quotient.lift f (fun _ _ h ↦ by
      obtain ⟨g, rfl⟩ := MulAction.mem_orbit_iff.mp (MulAction.orbitRel_apply.mp h)
      exact apply_smul_of_mem_map hinv g.property _) p
  | .ofCusp _ => 0

private theorem compactifiedOfInvariant_ofQuotient_mk
    (hinv : ∀ γ ∈ Gamma N, ∀ τ : ℍ, f (γ • τ) = f τ) (τ : ℍ) :
    compactifiedOfInvariant f hinv (ofQuotient (Quotient.mk _ τ)) = f τ :=
  (rfl)

private theorem continuousAt_compactifiedOfInvariant_ofQuotient (hf : MDiff f)
    (hinv : ∀ γ ∈ Gamma N, ∀ τ : ℍ, f (γ • τ) = f τ)
    (p : MulAction.orbitRel.Quotient ((Gamma N).map sl2zToPSL2R) ℍ) :
    ContinuousAt (compactifiedOfInvariant f hinv) (ofQuotient p) :=
  isOpenEmbedding_ofQuotient.continuousAt_iff.mp <| Continuous.continuousAt <|
    isQuotientMap_quotient_mk'.continuous_iff
      (g := compactifiedOfInvariant f hinv ∘ ofQuotient) |>.mpr <|
        hf.continuous.congr fun τ ↦ (compactifiedOfInvariant_ofQuotient_mk hinv τ).symm

variable [NeZero N]

/-- A bound `O(exp (c Im τ))` is a bound `O(exp (2π k Im τ / N))` for an integer `k`. -/
private theorem exists_isBigO_exp_div {c : ℝ} {g : ℍ → ℂ}
    (hg : g =O[atImInfty] fun τ ↦ Real.exp (c * τ.im)) :
    ∃ k : ℤ, g =O[atImInfty] fun τ ↦ Real.exp (2 * Real.pi * k * τ.im / N) := by
  have hN : (0 : ℝ) < N := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne N))
  refine ⟨⌈c * N / (2 * Real.pi)⌉, hg.trans (isBigO_of_le _ fun τ ↦ ?_)⟩
  rw [Real.norm_of_nonneg (Real.exp_pos _).le, Real.norm_of_nonneg (Real.exp_pos _).le,
    Real.exp_le_exp]
  have hc : c ≤ 2 * Real.pi * ⌈c * N / (2 * Real.pi)⌉ / N := by
    rw [le_div_iff₀ hN, ← div_le_iff₀' (by positivity)]
    exact Int.le_ceil _
  calc c * τ.im ≤ 2 * Real.pi * ⌈c * N / (2 * Real.pi)⌉ / N * τ.im :=
        mul_le_mul_of_nonneg_right hc τ.im_pos.le
    _ = _ := by ring

/-- The function on `X(N)` is meromorphic. At the cusp of `γ • ∞` it is read in the cusp datum
of `∞` transported by `γ`, where it is `τ ↦ f (γ • τ)`. -/
private theorem meromorphicAt_compactifiedOfInvariant (hf : MDiff f)
    (hinv : ∀ γ ∈ Gamma N, ∀ τ : ℍ, f (γ • τ) = f τ)
    (hgrowth : ∀ γ : SL(2, ℤ), ∃ c : ℝ,
      (fun τ : ℍ ↦ f (γ • τ)) =O[atImInfty] fun τ ↦ Real.exp (c * τ.im))
    (x : ((Gamma N).map sl2zToPSL2R).CompactifiedQuotient) :
    RiemannSurface.MeromorphicAt (compactifiedOfInvariant f hinv) x := by
  refine Fuchsian.meromorphicAt_of_forall_isBigO (compactifiedOfInvariant_ofQuotient_mk hinv)
    (fun τ ↦ meromorphicAt_of_eventually_mdifferentiableAt (.of_forall hf)) (fun C ↦ ?_) x
  obtain ⟨γ, rfl⟩ := (Gamma N).cuspOrbitOfSL2Z_surjective C
  obtain ⟨c, hc⟩ := hgrowth γ
  obtain ⟨k, hk⟩ := exists_isBigO_exp_div (N := N) hc
  refine ⟨(cuspDatumInftyGamma N).conj (conjAct_sl2zToPSL2R_smul_map_Gamma γ), k,
    Subtype.ext ?_, .of_forall fun τ ↦ hf _, ?_⟩
  · rw [Subgroup.CuspDatum.cuspOrbit_val, Subgroup.cuspOrbitOfSL2Z_val,
      Subgroup.CuspDatum.conj_cusp, cuspDatumInftyGamma_cusp]
  · simp only [Subgroup.CuspDatum.conj_scaling, cuspDatumInftyGamma_scaling, one_mul, inv_inv,
      UpperHalfPlane.sl2zToPSL2R_smul, Subgroup.CuspDatum.conj_width, cuspDatumInftyGamma_width]
    simpa only [Int.cast_natCast] using hk

/-- **A modular function of level `N` from its values on the upper half-plane.** A holomorphic
function `f` on `ℍ`, invariant under `Γ(N)`, such that `τ ↦ f (γ • τ)` is `O(exp (c Im τ))` at
`i∞` for every `γ ∈ SL(2, ℤ)` and some real `c`, defines a meromorphic function on `X(N)` whose
value at the orbit of `τ` is `f τ`
(`TauCeti.meromorphicFunctionOfGammaInvariant_ofQuotient_mk`). -/
def meromorphicFunctionOfGammaInvariant (f : ℍ → ℂ) (hf : MDiff f)
    (hinv : ∀ γ ∈ Gamma N, ∀ τ : ℍ, f (γ • τ) = f τ)
    (hgrowth : ∀ γ : SL(2, ℤ), ∃ c : ℝ,
      (fun τ : ℍ ↦ f (γ • τ)) =O[atImInfty] fun τ ↦ Real.exp (c * τ.im)) :
    MeromorphicFunction ((Gamma N).map sl2zToPSL2R).CompactifiedQuotient :=
  MeromorphicFunction.ofMeromorphic (meromorphicAt_compactifiedOfInvariant hf hinv hgrowth)

/-- The value of `TauCeti.meromorphicFunctionOfGammaInvariant f` at the orbit of `τ` is
`f τ`. -/
@[simp]
theorem meromorphicFunctionOfGammaInvariant_ofQuotient_mk (hf : MDiff f)
    (hinv : ∀ γ ∈ Gamma N, ∀ τ : ℍ, f (γ • τ) = f τ)
    (hgrowth : ∀ γ : SL(2, ℤ), ∃ c : ℝ,
      (fun τ : ℍ ↦ f (γ • τ)) =O[atImInfty] fun τ ↦ Real.exp (c * τ.im)) (τ : ℍ) :
    meromorphicFunctionOfGammaInvariant f hf hinv hgrowth (ofQuotient (Quotient.mk _ τ)) =
      f τ :=
  MeromorphicFunction.ofMeromorphic_apply_of_continuousAt _
    (continuousAt_compactifiedOfInvariant_ofQuotient hf hinv _)

/-- The finite part of `TauCeti.meromorphicFunctionOfGammaInvariant f` at the orbit of `τ` is
`f τ`. -/
@[simp]
theorem finitePart_meromorphicFunctionOfGammaInvariant_ofQuotient_mk (hf : MDiff f)
    (hinv : ∀ γ ∈ Gamma N, ∀ τ : ℍ, f (γ • τ) = f τ)
    (hgrowth : ∀ γ : SL(2, ℤ), ∃ c : ℝ,
      (fun τ : ℍ ↦ f (γ • τ)) =O[atImInfty] fun τ ↦ Real.exp (c * τ.im)) (τ : ℍ) :
    (meromorphicFunctionOfGammaInvariant f hf hinv hgrowth).finitePart
      (ofQuotient (Quotient.mk _ τ)) = f τ :=
  MeromorphicFunction.finitePart_of_eq_coe
    (meromorphicFunctionOfGammaInvariant_ofQuotient_mk hf hinv hgrowth τ)

end TauCeti
