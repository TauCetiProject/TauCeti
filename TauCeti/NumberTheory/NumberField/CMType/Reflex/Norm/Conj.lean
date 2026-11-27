/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.CMField
public import TauCeti.NumberTheory.NumberField.CMType.Reflex.Norm.Basic

/-!
# The reflex norm of the complementary type

Let `Φ` be a CM type on a formally unramified finite `ℚ`-algebra `E`, such as a number field, and
`σ` a ring automorphism of `E` with `φ ∘ σ = ι ∘ φ` for every complex embedding `φ`, such as
complex conjugation `ι_E` of a CM field.
For a subfield `k ⊆ ℂ` containing the reflex field, the reflex norm of the complementary type
`ιΦ` is `N_{k,ιΦ} = σ⁻¹ ∘ N_{k,Φ}` (`TauCeti.CMType.reflexNorm_star_apply`); for a CM field,
`N_{k,ιΦ} = ι_E ∘ N_{k,Φ}` (`TauCeti.CMType.reflexNorm_star_apply_complexConj`), as in Milne,
*Complex Multiplication*, Remark 1.24(b), p.16.

Twisting the action of `E` on the representation `V` with the type trace of `Φ` by `σ` gives a
representation with the type trace of `ιΦ`, since `typeTrace_Φ(σ c) = typeTrace_{ιΦ}(c)`. So the
representation `V'` of `ιΦ` is `σ`-semilinearly isomorphic to `V`, compatibly with `k`, and the
determinant over `E` of the scalar action of `k` changes by `σ⁻¹`
(`TauCeti.smulDet_eq_symm_apply_of_map_smul`).

## Main results

* `TauCeti.CMType.reflexNorm_star_apply`: `N_{k,ιΦ}(a) = σ⁻¹(N_{k,Φ}(a))`.
* `TauCeti.CMType.reflexNorm_star_apply_complexConj`: on a CM field, `N_{k,ιΦ} = ι_E ∘ N_{k,Φ}`.

## References

* J. S. Milne, *Complex Multiplication*, §1, Remark 1.24(b), p.16.
-/

public section

namespace TauCeti

namespace CMType

section FormallyUnramified

variable {E : Type*} [CommRing E] [Finite (E →+* ℂ)] [Algebra ℚ E] [Module.Finite ℚ E]
  [Algebra.FormallyUnramified ℚ E] {k : IntermediateField ℚ ℂ}

/-- **The reflex norm of the complementary type.** If a ring automorphism `σ` of `E` satisfies
`φ ∘ σ = ι ∘ φ` for every complex embedding `φ`, then `N_{k,ιΦ}(a) = σ⁻¹(N_{k,Φ}(a))`. -/
theorem reflexNorm_star_apply (Φ : CMType E) (hk : Φ.reflexField ≤ k) (σ : E ≃+* E)
    (hσ : ∀ φ : E →+* ℂ, φ.comp σ.toRingHom = star φ) (a : k) :
    (star Φ).reflexNorm (reflexField_star Φ ▸ hk) a = σ.symm (Φ.reflexNorm hk a) := by
  -- The representations `V` and `V'` with the type traces of `Φ` and `ιΦ`.
  obtain ⟨n, ρ, hρ⟩ := Φ.exists_trace_eq_typeTrace hk
  obtain ⟨n', ρ', hρ'⟩ := (star Φ).exists_trace_eq_typeTrace (reflexField_star Φ ▸ hk)
  -- Twisted by `σ`, `V` has the type trace of `ιΦ`: `typeTrace_Φ(σ c) = typeTrace_{ιΦ}(c)`.
  obtain ⟨e, he⟩ := exists_linearEquiv_of_trace_eq_typeTrace (star Φ) k ρ' (ρ.comp σ.toRingHom)
    hρ' fun c ↦ (hρ (σ c)).trans (typeTrace_star_eq_typeTrace_apply Φ hσ c).symm
  rw [reflexNorm_eq_smulDet_compHom Φ hk ρ hρ, reflexNorm_eq_smulDet_compHom (star Φ) _ ρ' hρ']
  -- `E` acts on `V` and `V'` through `ρ` and `ρ'`, and `e` is `σ`-semilinear for these actions.
  let := Module.compHom (Fin n → k) ρ
  have := SMul.comp.smulCommClass (α := Fin n → k) (β := k) ρ
  let := Module.compHom (Fin n' → k) ρ'
  have := SMul.comp.smulCommClass (α := Fin n' → k) (β := k) ρ'
  -- Under `Module.compHom`, `c • v` is by definition `ρ' c v` on `V'` and `ρ c v` on `V`.
  have he' : ∀ (c : E) (v : Fin n' → k), e (c • v) = σ c • e v := he
  exact smulDet_eq_symm_apply_of_map_smul σ e he' a

end FormallyUnramified

section Field

variable {E : Type*} [Field E] [NumberField E] {k : IntermediateField ℚ ℂ}

-- A number field is formally unramified over `ℚ`, so its reflex norm is defined.
attribute [local instance] Algebra.FormallyUnramified.of_isSeparable

/-- **The reflex norm of the complementary type of a CM field** is the complex conjugate of the
reflex norm: `N_{k,ιΦ} = ι_E ∘ N_{k,Φ}`. -/
theorem reflexNorm_star_apply_complexConj [NumberField.IsCMField E] (Φ : CMType E)
    (hk : Φ.reflexField ≤ k) (a : k) :
    (star Φ).reflexNorm (reflexField_star Φ ▸ hk) a =
      NumberField.IsCMField.complexConj E (Φ.reflexNorm hk a) := by
  rw [reflexNorm_star_apply Φ hk (NumberField.IsCMField.complexConj E).toRingEquiv
    fun φ ↦ RingHom.ext fun x ↦ by simp [RingHom.star_apply]]
  apply (NumberField.IsCMField.complexConj E).injective
  simp

end Field

end CMType

end TauCeti
