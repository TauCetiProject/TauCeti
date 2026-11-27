/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.AlgebraicClosure
public import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Algebra.Algebra.Hom.Rat
import TauCeti.FieldTheory.IsAlgClosed.Automorphism
import TauCeti.FieldTheory.Normal.Embeddings

/-!
# Extending embeddings of algebraic subfields to automorphisms

Let `Ω` be an algebraically closed field over `F` and `K` an intermediate field of `Ω / F`,
algebraic over `F`. Every `F`-embedding `φ : K → Ω` extends to an `F`-automorphism of `Ω`. The
embedding takes values in the relative algebraic closure `A` of `F` in `Ω`, which is normal
over `F`, so an automorphism of `A` carries the inclusion `K ⊆ A` to it
(`AlgEquiv.isPretransitiveAlgHom`), and an automorphism of `A` extends to `Ω`
(`AlgEquiv.exists_algEquiv_apply_algebraMap`). For `Ω = ℂ`, every complex embedding of a subfield
of `ℂ` of finite degree over `ℚ` is the restriction of an automorphism of `ℂ`.

## Main results

* `IntermediateField.exists_algEquiv_apply_eq_of_isAlgebraic`: an `F`-embedding into `Ω` of an
  algebraic intermediate field of `Ω / F` extends to an `F`-automorphism of `Ω`.
* `IntermediateField.exists_ringEquiv_apply_eq_of_isAlgebraic`: the same for ring
  homomorphisms of algebraic subfields of a field of characteristic zero, over `ℚ`.
-/

public section

namespace IntermediateField

variable {F Ω : Type*} [Field F] [Field Ω] [IsAlgClosed Ω] [Algebra F Ω]

/-- **Embeddings extend to automorphisms.** An `F`-embedding into an algebraically closed field
`Ω` of an intermediate field `K` of `Ω / F`, algebraic over `F`, is the restriction of an
`F`-automorphism of `Ω`. -/
theorem exists_algEquiv_apply_eq_of_isAlgebraic (K : IntermediateField F Ω)
    [Algebra.IsAlgebraic F K] (φ : K →ₐ[F] Ω) : ∃ τ : Ω ≃ₐ[F] Ω, ∀ x : K, τ x = φ x := by
  let A := algebraicClosure F Ω
  have hKA : K ≤ A := le_algebraicClosure F Ω K
  -- `φ` takes values in `A`, since `K / F` is algebraic.
  have hmem (x : K) : φ x ∈ A.toSubalgebra :=
    mem_algebraicClosure_iff.mpr ((Algebra.IsAlgebraic.isAlgebraic x).algHom φ)
  -- `A / F` is normal, so `Aut(A/F)` moves the inclusion `K ⊆ A` to `φ`.
  obtain ⟨e, he⟩ := MulAction.exists_smul_eq (A ≃ₐ[F] A) (inclusion hKA)
    (φ.codRestrict A.toSubalgebra hmem)
  -- Extend the automorphism of `A` to `Ω`.
  obtain ⟨τ, hτ⟩ := AlgEquiv.exists_algEquiv_apply_algebraMap (R := A) (Ω := Ω) (K := F) e
  refine ⟨τ, fun x ↦ ?_⟩
  have := hτ (inclusion hKA x)
  simp only [← AlgEquiv.smul_algHom_apply, he, algebraMap_apply, coe_inclusion] at this
  -- The right side is the coercion to `Ω` of the codomain restriction of `φ`.
  exact this.trans (AlgHom.coe_codRestrict φ A.toSubalgebra hmem x)

/-- **Ring embeddings extend to automorphisms.** In an algebraically closed field `Ω` of
characteristic zero, a ring homomorphism into `Ω` of a subfield `K` algebraic over `ℚ`, such as a
complex embedding of a number field contained in `ℂ`, is the restriction of a ring automorphism
of `Ω`. -/
theorem exists_ringEquiv_apply_eq_of_isAlgebraic [CharZero Ω] (K : IntermediateField ℚ Ω)
    [Algebra.IsAlgebraic ℚ K] (φ : K →+* Ω) : ∃ τ : Ω ≃+* Ω, ∀ x : K, τ x = φ x := by
  obtain ⟨τ, hτ⟩ := exists_algEquiv_apply_eq_of_isAlgebraic K φ.toRatAlgHom
  exact ⟨τ.toRingEquiv, hτ⟩

end IntermediateField
