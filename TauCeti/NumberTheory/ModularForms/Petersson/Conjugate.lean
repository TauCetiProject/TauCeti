/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.Conjugate
public import TauCeti.NumberTheory.ModularForms.Petersson.FiniteIndex
import TauCeti.NumberTheory.ModularForms.Petersson.Adjoint
import TauCeti.NumberTheory.Modular

/-!
# The Petersson product of conjugate forms

The conjugate form `f_ρ(τ) = conj (f (-conj τ))` is the slash of `f` by the reflection
`J = !![-1, 0; 0, 1]` (`CuspForm.conj`). The reflection `τ ↦ -conj τ` preserves the
invariant measure of `ℍ`, and the Petersson integrand of `f ∣[k] J` and `g ∣[k] J` at `τ` is the
complex conjugate of that of `f` and `g` at `J • τ`. So conjugating both arguments conjugates the
Petersson product,

```text
⟪f_ρ, g_ρ⟫ = conj ⟪f, g⟫,
```

for a finite-index `Γ ≤ SL₂(ℤ)` normalized by `J`, such as `Γ₀(N)` and `Γ₁(N)`: `J` carries a
fundamental domain of `Γ` to another one. In particular `f ↦ f_ρ` preserves Petersson
orthogonality, which is how it acts on the old and new subspaces.

## Main results

* `UpperHalfPlane.peterssonInner_slash_slash_J`: slashing both arguments by `J` conjugates the
  pairing and reflects its domain.
* `CuspForm.peterssonInnerCosets_conj_conj`: `⟪f_ρ, g_ρ⟫ = conj ⟪f, g⟫` on `S_k(Γ)`.

## References

* [T. Miyake, *Modular forms*][miyake1989], §4.6, where the conjugate form is written `f_ρ`.
-/

public section

open MeasureTheory UpperHalfPlane Matrix.SpecialLinearGroup TauCeti

open scoped MatrixGroups ModularForm ComplexConjugate Pointwise

namespace UpperHalfPlane

/-- **Slashing both arguments by the reflection `J` conjugates the Petersson pairing**:
`⟪f ∣[k] J, h ∣[k] J⟫_S = conj ⟪f, h⟫_{J • S}`. The slash by the determinant `-1` matrix `J`
conjugates values, and `J` preserves the invariant measure. -/
theorem peterssonInner_slash_slash_J (k : ℤ) (S : Set ℍ) (f h : ℍ → ℂ) :
    peterssonInner k S (f ∣[k] J) (h ∣[k] J) = conj (peterssonInner k (J • S) f h) := by
  rw [peterssonInner_def, peterssonInner_def, ← Set.image_smul,
    (measurePreserving_smul J volume).setIntegral_image_emb (measurableEmbedding_const_smul J)]
  simp_rw [petersson_slash]
  simp [integral_conj]

end UpperHalfPlane

namespace CuspForm

variable {Γ : Subgroup SL(2, ℤ)} [Γ.FiniteIndex] {k : ℤ}

/-- **Conjugating both forms conjugates the Petersson product**: `⟪f_ρ, g_ρ⟫ = conj ⟪f, g⟫` on
`S_k(Γ)`, for a finite-index `Γ ≤ SL₂(ℤ)` normalized by the reflection `J`. -/
theorem peterssonInnerCosets_conj_conj
    (hJ : Γ.map (mapGL ℝ) ≤ ConjAct.toConjAct J⁻¹ • Γ.map (mapGL ℝ))
    (f g : CuspForm (Γ.map (mapGL ℝ)) k) :
    peterssonInnerCosets (CuspForm.conj hJ f) (CuspForm.conj hJ g) =
      conj (peterssonInnerCosets f g) := by
  -- the reflection `J` carries the coset fundamental domain `D` of `Γ` to another one
  have hD := ModularGroup.isFundamentalDomain_iUnion_out_inv_smul_fdo_withCenter Γ
  have hJD := ModularGroup.isFundamentalDomain_smul_of_inv_conjAct_eq
    (conjAct_inv_J_smul_eq_of_le hJ) hD
  rw [peterssonInnerCosets_eq_peterssonInner, peterssonInnerCosets_eq_peterssonInner,
    CuspForm.coe_conj, CuspForm.coe_conj, peterssonInner_slash_slash_J,
    UpperHalfPlane.peterssonInner_eq_of_isFundamentalDomain k f g hJD hD]

end CuspForm
