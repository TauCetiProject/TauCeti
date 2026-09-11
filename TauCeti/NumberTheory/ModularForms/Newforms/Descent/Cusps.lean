/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.Cusps.Rat.Slash
public import TauCeti.NumberTheory.ModularForms.Newforms.Descent.Sum

/-!
# The descent slash sum at the cusps

Every member of the descent family is the image of a rational matrix (`descendMatrix_eq_map`),
so the descent slash sum is a finite sum of rational slashes, and a function vanishing, resp.
bounded, at every cusp keeps that property after it (`OnePoint.isZeroAt_sum_rat_slash`,
`OnePoint.isBoundedAt_sum_rat_slash`). This is the cusp half of the statement that the descent
sends cusp forms to cusp forms; the other half, invariance, is `Descent/Sum.lean`.

## Main results

* `TauCeti.isZeroAt_descendSlash`: the descent slash sum of a function vanishing at every cusp
  vanishes at every cusp.
* `TauCeti.isBoundedAt_descendSlash`: the same for boundedness.

Corresponds to `miyake_hecke_descend_cusp` of the AINTLIB `LeanModularForms` project
(`LeanModularForms/StrongMultiplicityOne/HeckeDescent.lean`, Chris Birkbeck, commit
`2baa76f742bdb4fb8ee323fabba41203bd390e08`, Apache-2.0,
<https://github.com/CBirkbeck/AINTLIB/tree/main/projects/LeanModularForms>), which argues
summand by summand for cusp forms of level `Γ₁(N)`; here the family's rationality feeds the
general finite-sum statement, for any function and any arithmetic group.
-/

public section

open UpperHalfPlane

open scoped MatrixGroups ModularForm

namespace TauCeti

variable {p N : ℕ} (k : ℤ) {Γ : Subgroup (GL (Fin 2) ℝ)} [Γ.IsArithmetic] {f : ℍ → ℂ}
  {c : OnePoint ℝ}

/-- **The descent slash sum vanishes at every cusp** when the function does. -/
theorem isZeroAt_descendSlash [NeZero p] (hf : ∀ c : OnePoint ℝ, IsCusp c Γ → c.IsZeroAt f k)
    (hc : IsCusp c Γ) : c.IsZeroAt (descendSlash k p N f) k := by
  rw [descendSlash_def]
  simp_rw [descendMatrix_eq_map, ← ModularForm.rat_slash]
  exact OnePoint.isZeroAt_sum_rat_slash k _ _ hf hc

/-- **The descent slash sum is bounded at every cusp** when the function is. -/
theorem isBoundedAt_descendSlash [NeZero p]
    (hf : ∀ c : OnePoint ℝ, IsCusp c Γ → c.IsBoundedAt f k) (hc : IsCusp c Γ) :
    c.IsBoundedAt (descendSlash k p N f) k := by
  rw [descendSlash_def]
  simp_rw [descendMatrix_eq_map, ← ModularForm.rat_slash]
  exact OnePoint.isBoundedAt_sum_rat_slash k _ _ hf hc

end TauCeti
