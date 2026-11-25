/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.AlgebraicClosure
public import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Algebra.Algebra.Hom.Rat
import Mathlib.FieldTheory.Extension
import TauCeti.FieldTheory.IsAlgClosed.Automorphism

/-!
# Extending embeddings of algebraic subfields to automorphisms

Let `Ω` be an algebraically closed field over `F` and `K` an intermediate field of `Ω / F`,
algebraic over `F`. Every `F`-embedding `φ : K → Ω` extends to an `F`-automorphism of `Ω`. The
embedding first extends to the relative algebraic closure `A` of `F` in `Ω`, where it is an
automorphism since `A / F` is algebraic, and an automorphism of `A` extends to `Ω`
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
  -- Extend `φ` to the relative algebraic closure `A`.
  obtain ⟨ψ, hψ⟩ := exists_algHom_of_splits (F := F) (E := A) (K := Ω) (L := restrict hKA)
    (fun s ↦ ⟨Algebra.IsIntegral.isIntegral s, IsAlgClosed.splits _⟩)
    (φ.comp (restrictAlgEquiv hKA).symm.toAlgHom)
  -- The extension takes values in `A`, and is an automorphism of `A` since `A / F` is algebraic.
  have hmem (a : A) : ψ a ∈ A.toSubalgebra :=
    mem_algebraicClosure_iff.mpr ((Algebra.IsAlgebraic.isAlgebraic a).algHom ψ)
  let ψ' : A →ₐ[F] A := ψ.codRestrict A.toSubalgebra hmem
  let e : A ≃ₐ[F] A := AlgEquiv.ofBijective ψ' (Algebra.IsAlgebraic.algHom_bijective ψ')
  -- Extend the automorphism of `A` to `Ω`.
  obtain ⟨τ, hτ⟩ := AlgEquiv.exists_algEquiv_apply_algebraMap (R := A) (Ω := Ω) (K := F) e
  refine ⟨τ, fun x ↦ ?_⟩
  -- Mathlib has no apply lemma for `restrictAlgEquiv`: it is the identity on underlying
  -- elements of `Ω` by definition.
  have hx : restrictAlgEquiv hKA x =
      ⟨⟨x, hKA x.property⟩, (mem_restrict hKA _).mpr x.property⟩ :=
    rfl
  -- `e` is `ψ` with codomain restricted to `A`, so it agrees with `ψ` after the inclusion of `A`.
  have he (a : A) : (e a : Ω) = ψ a := rfl
  have := hτ ⟨x, hKA x.property⟩
  have h2 := AlgHom.congr_fun hψ (restrictAlgEquiv hKA x)
  simp only [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, AlgEquiv.symm_apply_apply] at h2
  rw [← h2, hx]
  simpa [he] using this

/-- **Ring embeddings extend to automorphisms.** In an algebraically closed field `Ω` of
characteristic zero, a ring homomorphism into `Ω` of a subfield `K` algebraic over `ℚ`, such as a
complex embedding of a number field contained in `ℂ`, is the restriction of a ring automorphism
of `Ω`. -/
theorem exists_ringEquiv_apply_eq_of_isAlgebraic [CharZero Ω] (K : IntermediateField ℚ Ω)
    [Algebra.IsAlgebraic ℚ K] (φ : K →+* Ω) : ∃ τ : Ω ≃+* Ω, ∀ x : K, τ x = φ x := by
  obtain ⟨τ, hτ⟩ := exists_algEquiv_apply_eq_of_isAlgebraic K φ.toRatAlgHom
  exact ⟨τ.toRingEquiv, hτ⟩

end IntermediateField
