/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.HeckeSlash.Basic
public import TauCeti.NumberTheory.ModularForms.SlashAdjugate

/-!
# The adjugates of the Hecke coset representatives

`HeckeRing.GL2.heckeSlashSum` sums `f ∣[k] aᵥ` over `aᵥ = rightCosetRep D v = δ τᵥ⁻¹`, where `δ`
represents the double coset and `τᵥ` runs over `Γ₂ ⧸ (Γ₂ ∩ δ⁻¹Γ₁δ)`. Moving that sum across the
Petersson pairing replaces each `aᵥ` by its main involution `aᵥ^ι = adjugateGL aᵥ`
(`UpperHalfPlane.peterssonInner_sum_slash_left_adjugateGL`), and the resulting pairing is an
integral of `g ∣[k] aᵥ^ι` over a translate of a fundamental domain — one integrand per `v`.

This file records the fact that collapses those integrands to one. The adjugate is
*anti*-multiplicative, so

```text
aᵥ^ι = (δ τᵥ⁻¹)^ι = (τᵥ⁻¹)^ι δ^ι = τᵥ δ^ι
```

as soon as `τᵥ` has determinant one, and the left factor lies in `Γ₂`. A function invariant under
the weight-`k` slash action of that factor therefore does not see it:
`g ∣[k] aᵥ^ι = g ∣[k] δ^ι` for every `v`. That is exactly the constancy hypothesis of
`UpperHalfPlane.peterssonInner_sum_slash_left_adjugateGL_biUnion`, which is what lets the
translated pairings reassemble into a single one.

## Main results

* `HeckeRing.GL2.adjugateGL_rightCosetRep`: `aᵥ^ι = τᵥ δ^ι`, the adjugate of a right-coset
  representative split off from the adjugate of the double-coset representative.
* `HeckeRing.GL2.slash_adjugateGL_rightCosetRep`: consequently `g ∣[k] aᵥ^ι = g ∣[k] δ^ι` for a
  `g` invariant under `τᵥ`, independent of `v`.

Both are stated at a single `v`, with the determinant and invariance hypotheses asked of `τᵥ`
alone. A caller quantifying over `v` — which is what the aggregate identity needs — supplies them
from whatever it knows about `Γ₂`, and `HeckeCoset` itself puts no condition on its subgroups.

## References

* [G. Shimura, *Introduction to the arithmetic theory of automorphic functions*][shimura1971],
  Chapter 3.
* The AINTLIB `LeanModularForms` project,
  <https://github.com/CBirkbeck/AINTLIB/tree/main/projects/LeanModularForms>, commit
  `6d87d596a5372d5b122c47b7082d4c3afa9b7c3b`, Apache-2.0 —
  `HeckeRIngs/GL2/AdjointTheory/SummandAdjoint.lean` proves the corresponding statements
  (`slash_peterssonAdj_glMap_T_p_upper_eq_slash_T_p_lower`, :716, and its `M_∞` companion) for the
  concrete `Tₚ` family on `Γ₁(N)`, one matrix at a time. Here the double coset is abstract, so the
  anti-multiplicativity of the adjugate does the work that explicit matrices do there.
-/

public section

noncomputable section

open Matrix TauCeti UpperHalfPlane DoubleCoset

open scoped MatrixGroups ModularForm Pointwise

namespace HeckeRing.GL2

variable (k : ℤ) {Δ : Submonoid (GL (Fin 2) ℚ)} {Γ₁ Γ₂ : Subgroup (GL (Fin 2) ℚ)}
  (D : HeckeCoset Δ Γ₁ Γ₂)

/-- **The adjugate of a right-coset representative peels off a `Γ₂`-element on the left.** The
adjugate is anti-multiplicative and inverts a determinant-one matrix, so
`(δ τᵥ⁻¹)^ι = τᵥ · δ^ι`.

The determinant hypothesis is asked of `τᵥ` alone, not of `Γ₂`: the statement is about one `v`,
and `HeckeCoset` puts no condition on its subgroups. A caller quantifying over `v` supplies it
from whatever it knows about `Γ₂`. -/
theorem adjugateGL_rightCosetRep (v : DecompQuotient Γ₂ Γ₁ (D.out : GL (Fin 2) ℚ)⁻¹)
    (hdet : ((((v.out : Γ₂) : GL (Fin 2) ℚ)) : Matrix (Fin 2) (Fin 2) ℚ).det = 1) :
    adjugateGL (rightCosetRep D v) =
      ((v.out : Γ₂) : GL (Fin 2) ℚ) * adjugateGL (D.out : GL (Fin 2) ℚ) := by
  have hinv : (((((v.out : Γ₂) : GL (Fin 2) ℚ))⁻¹ : GL (Fin 2) ℚ) :
      Matrix (Fin 2) (Fin 2) ℚ).det = 1 := by
    rw [Matrix.coe_units_inv, Matrix.det_nonsing_inv, hdet, Ring.inverse_one]
  rw [rightCosetRep_def, adjugateGL_mul, adjugateGL_eq_inv hinv, inv_inv]

/-- **A `Γ₂`-invariant function does not see which right-coset representative it is slashed by,
once the adjugate is taken**: `g ∣[k] aᵥ^ι = g ∣[k] δ^ι` for every `v`.

This is the constancy that
`UpperHalfPlane.peterssonInner_sum_slash_left_adjugateGL_biUnion` asks for, and the reason a
Hecke operator's translated pairings reassemble into one. -/
theorem slash_adjugateGL_rightCosetRep (v : DecompQuotient Γ₂ Γ₁ (D.out : GL (Fin 2) ℚ)⁻¹)
    (hdet : ((((v.out : Γ₂) : GL (Fin 2) ℚ)) : Matrix (Fin 2) (Fin 2) ℚ).det = 1)
    {g : ℍ → ℂ} (hg : g ∣[k] ((v.out : Γ₂) : GL (Fin 2) ℚ) = g) :
    g ∣[k] adjugateGL (rightCosetRep D v) = g ∣[k] adjugateGL (D.out : GL (Fin 2) ℚ) := by
  rw [adjugateGL_rightCosetRep D v hdet, SlashAction.slash_mul, hg]

end HeckeRing.GL2
