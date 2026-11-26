/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Basis.Fin
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import TauCeti.LinearAlgebra.SesquilinearForm.Basic
public import TauCeti.LinearAlgebra.SesquilinearForm.SignedHermitianSpace.Basic

/-!
# Orthogonal bases of signed hermitian spaces

Let `K` be a field with an involution `σ` that is not the identity, for instance a separable
quadratic extension `E/F` with its Galois conjugation. Every finite-dimensional signed hermitian
space `(V, h)` over `K` has an orthogonal basis `x₁, …, xₙ` with `h xᵢ xᵢ ≠ 0`. The values
`h x x` satisfy `σ (h x x) = ε h x x` (`TauCeti.SignedHermitianSpace.apply_form_self`): for a
hermitian form they lie in the fixed field `F` of `σ`, and for a skew-hermitian form in
`δ F` for any `δ ≠ 0` with `σ δ = -δ`.

The nontrivial involution is essential. A sesquilinear form all of whose values `B x x` vanish is
zero as soon as some `z` has `σ z ≠ z` (`LinearMap.eq_zero_of_forall_apply_self_eq_zero`); in
characteristic two this replaces polarization, which is not available. For the trivial
involution the alternating form `x₁ y₂ - x₂ y₁` on `K²` is a nondegenerate skew-symmetric form in
which every vector is isotropic, so it has no orthogonal basis. No hypothesis on the
characteristic is needed: over `𝔽₄/𝔽₂` the form `σ x₁ * y₁ + σ x₂ * y₂` has the orthogonal basis
`e₁, e₂`, while its isotropic vector `(1, 1)` belongs to no orthogonal basis.

## Main statements

* `TauCeti.exists_isOrthoᵢ_basis_of_forall_form_swap`: every `ε`-hermitian form on a
  finite-dimensional space, nondegenerate or not, has an orthogonal basis.
* `TauCeti.SignedHermitianSpace.exists_isOrthoᵢ_basis`: a signed hermitian space has an
  orthogonal basis whose vectors are anisotropic.

## Attribution

The inductive construction of `TauCeti.exists_isOrthoᵢ_basis_of_forall_form_swap`, splitting off
an anisotropic vector `x` and recursing on the kernel of `h x`, follows Mathlib's
`LinearMap.BilinForm.exists_orthogonal_basis` (`Mathlib.LinearAlgebra.QuadraticForm.Basic`), which
treats symmetric bilinear forms with `2` invertible; here the anisotropic vector comes from the
nontrivial involution instead of polarization.

## References

* W. Scharlau, *Quadratic and Hermitian Forms*, Grundlehren der mathematischen Wissenschaften
  270, Springer (1985), Chapter 7.
-/

public section

open Module

namespace TauCeti

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {σ : K →+* K} {ε : ℤˣ}

/-- **Orthogonal bases of `ε`-hermitian forms.** Over a field whose involution `σ` is not the
identity, every `ε`-hermitian form `B` on a finite-dimensional space, `B y x = ε σ (B x y)`, has an
orthogonal basis. The form need not be nondegenerate. -/
theorem exists_isOrthoᵢ_basis_of_forall_form_swap [FiniteDimensional K V] (hσ : ∃ z, σ z ≠ z)
    {B : V →ₛₗ[σ] V →ₗ[K] K} (hB : ∀ x y, B y x = ε • σ (B x y)) :
    ∃ b : Basis (Fin (finrank K V)) K V, B.IsOrthoᵢ b := by
  obtain ⟨z, hz⟩ := hσ
  have hz' : z - σ z ∈ nonZeroDivisors K := mem_nonZeroDivisors_of_ne_zero (sub_ne_zero.2 hz.symm)
  suffices ∀ d, finrank K V = d → ∃ b : Basis (Fin d) K V, B.IsOrthoᵢ b from this _ rfl
  intro d hd
  induction d generalizing V with
  | zero => exact ⟨basisOfFinrankZero hd, fun _ _ h ↦ (h (Subsingleton.elim _ _)).elim⟩
  | succ d ih =>
  by_cases hB₀ : B = 0
  · subst hB₀
    exact ⟨(Module.finBasis K V).reindex (finCongr hd), fun _ _ _ ↦ rfl⟩
  obtain ⟨x, hx⟩ : ∃ x, B x x ≠ 0 := by
    by_contra! h
    exact hB₀ (LinearMap.eq_zero_of_forall_apply_self_eq_zero hz' h)
  -- Split off the line through `x`: its complement is the kernel `W` of `B x`.
  set W := LinearMap.ker (B x)
  have hsurj : Function.Surjective (B x) := fun c ↦ ⟨(c / B x x) • x, by
    rw [map_smul, smul_eq_mul, div_mul_cancel₀ _ hx]⟩
  have hW : finrank K (LinearMap.ker (B x)) = d := by
    have := LinearMap.finrank_range_add_finrank_ker (B x)
    rw [LinearMap.range_eq_top.2 hsurj, finrank_top, finrank_self] at this
    lia
  obtain ⟨b', hb'⟩ := ih (B := B.domRestrict₁₂ W W) (fun u v ↦ hB u v) hW
  refine ⟨Basis.mkFinCons x b' (fun c y hy hc ↦ ?_) (fun y ↦ ⟨-(B x y / B x x), ?_⟩), ?_⟩
  · have := congrArg (B x) hc
    rw [map_add, map_smul, LinearMap.mem_ker.1 hy, map_zero, smul_eq_mul, add_zero] at this
    exact (mul_eq_zero.1 this).resolve_right hx
  · rw [LinearMap.mem_ker, map_add, map_smul, smul_eq_mul, neg_mul, div_mul_cancel₀ _ hx,
      add_neg_cancel]
  -- The new vector `x` is orthogonal to `W`, in both orders.
  have hxW (w : W) : B x w = 0 := LinearMap.mem_ker.1 w.property
  have hWx (w : W) : B w x = 0 := by rw [hB, hxW, map_zero, smul_zero]
  rw [Basis.coe_mkFinCons]
  intro i j hij
  induction i using Fin.cases <;> induction j using Fin.cases
  · exact (hij rfl).elim
  · exact hxW _
  · exact hWx _
  · exact hb' (fun h ↦ hij (congrArg Fin.succ h))

namespace SignedHermitianSpace

variable (H : SignedHermitianSpace K V σ ε)

/-- **Orthogonal bases** (Scharlau, Chapter 7). Over a field whose involution `σ` is not the
identity, a finite-dimensional signed hermitian space `(V, h)` has an orthogonal basis
`x₁, …, xₙ` with every `h xᵢ xᵢ` nonzero. -/
theorem exists_isOrthoᵢ_basis [FiniteDimensional K V] (hσ : ∃ z, σ z ≠ z) :
    ∃ b : Basis (Fin (finrank K V)) K V, H.form.IsOrthoᵢ b ∧ ∀ i, H.form (b i) (b i) ≠ 0 := by
  obtain ⟨b, hb⟩ := exists_isOrthoᵢ_basis_of_forall_form_swap hσ H.form_swap
  exact ⟨b, hb, hb.not_isOrtho_basis_self_of_separatingLeft H.separatingLeft⟩

end SignedHermitianSpace

end TauCeti
