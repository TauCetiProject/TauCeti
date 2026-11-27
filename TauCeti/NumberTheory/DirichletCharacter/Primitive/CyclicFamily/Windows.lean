/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.DirichletCharacter.LFunction.FiniteFamily.WindowedLandau
public import TauCeti.NumberTheory.DirichletCharacter.LFunction.GRH
public import TauCeti.NumberTheory.DirichletCharacter.Primitive.CyclicFamily.Basic
import TauCeti.NumberTheory.DirichletCharacter.LFunction.ZeroFree
import TauCeti.NumberTheory.DirichletCharacter.LFunction.ZeroReflection

/-!
# Zero-freeness from cyclic-family Riesz windows

Apply the windowed Landau theorem to weighted sums over the primitive characters inducing
powers of a fixed Dirichlet character. Such bounds for every cyclic family at exponents
arbitrarily close to `1/2` from above imply the generalized Riemann hypothesis, including
for imprimitive characters.

This is the implication from Riesz windows to zero-freeness in Levent Alpöge's
`UpperTheory.Comparison₂.formB` in `Development/AutomorphicArithmetic/PrimitiveCosets/Imports.lean`
of the [published formalization][alpoege].

[alpoege]: https://github.com/leanprover-community/riemann-hypothesis/tree/40e56bab026552e089d7afcfeff08d2defb9c005
-/

public section

namespace TauCeti

/-- Weighted Riesz windows of a primitive cyclic family at every exponent above `σ`
exclude zeros to the right of `σ` for all members of that family. The positive weights
and the window ratio may vary with the exponent. -/
theorem zeroFreeRightOf_of_hasWindows_cyclicFamily_riesz
    {ψ : PrimitiveDirichletCharacter} {σ : ℝ} (hσ : 0 ≤ σ)
    (hwin : ∀ ε > (0 : ℝ), ∃ (w : PrimitiveDirichletCharacter → ℝ) (L : ℝ),
      (∀ χ ∈ ψ.cyclicFamily, 0 < w χ) ∧ 1 < L ∧
        HasWindows {y | ∑ χ ∈ ψ.cyclicFamily, w χ * (χ.rieszRemainder y).re ≤ y ^ (σ + ε)} L) :
    ∀ χ ∈ ψ.cyclicFamily, ZeroFreeRightOf σ χ.character.LFunction := by
  classical
  intro χ hχ
  refine zeroFreeRightOf_of_forall_dirichletFamilyRiesz_hasWindows hσ fun θ hθ ↦ ?_
  obtain ⟨w, L, hw, hL, h⟩ := hwin (θ - σ) (sub_pos.mpr hθ)
  let v := Finsupp.indicator ψ.cyclicFamily fun κ _ ↦ w κ
  refine ⟨v, L, Finsupp.le_def.mpr ?_, ?_, hL, ?_⟩
  · intro κ
    by_cases hk : κ ∈ ψ.cyclicFamily
    · simpa only [v, Finsupp.zero_apply, Finsupp.indicator_of_mem hk] using (hw κ hk).le
    · simp only [v, Finsupp.zero_apply, Finsupp.indicator_of_notMem hk, le_refl]
  · simpa only [v, Finsupp.mem_support_iff, Finsupp.indicator_of_mem hχ] using (hw χ hχ).ne'
  · refine h.mono fun y hy ↦ ?_
    dsimp only [Set.mem_ofPred_eq, v]
    rw [Finsupp.sum_indicator_index w (h := fun κ c ↦ c * (κ.rieszRemainder y).re)
      (fun _ _ ↦ zero_mul _)]
    simpa only [Set.mem_ofPred_eq, add_sub_cancel] using hy

/-- If every primitive cyclic family admits positive weighted Riesz windows at every
exponent `1/2 + ε` with `ε > 0`, then `GRH` holds for all Dirichlet characters. -/
theorem grh_of_hasWindows_cyclicFamily_riesz
    (hwin : ∀ ψ : PrimitiveDirichletCharacter, ∀ ε > (0 : ℝ),
      ∃ (w : PrimitiveDirichletCharacter → ℝ) (L : ℝ),
        (∀ χ ∈ ψ.cyclicFamily, 0 < w χ) ∧ 1 < L ∧
          HasWindows {y | ∑ χ ∈ ψ.cyclicFamily, w χ * (χ.rieszRemainder y).re ≤
            y ^ ((1 / 2 : ℝ) + ε)} L) : GRH := by
  rw [grh_def]
  intro N _ χ
  rw [χ.dirichletGRH_def, ← χ.zeroFreeRightOf_one_half_LFunction_iff_forall_re_pos]
  exact (forall_zeroFreeRightOf_LFunction_iff_forall_mem_cyclicFamily (by norm_num)).mpr
    (fun ψ ↦ zeroFreeRightOf_of_hasWindows_cyclicFamily_riesz (by norm_num) (hwin ψ)) N χ

end TauCeti
