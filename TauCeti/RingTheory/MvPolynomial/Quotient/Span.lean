/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Jie Xu, Shitan Xu
-/
module

public import TauCeti.LinearAlgebra.TensorProduct.Quotient
public import TauCeti.RingTheory.MvPolynomial.Quotient.Basic
public import Mathlib.RingTheory.Spectrum.Prime.FreeLocus
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.LocalRing.Module
public import TauCeti.RingTheory.Support.BaseChange

/-!
# Spanning loci for polynomial quotients

For a polynomial quotient finite over its coefficient ring, a family of polynomial classes
spans after coefficient extension exactly when its cokernel annihilator generates the unit ideal
after that extension. For finite flat
quotients, monomial spanning loci cover the base. These results supply the open basis loci
for affine Hilbert charts.
-/

public section

section

open TensorProduct

namespace MvPolynomial

variable {n A B : Type*} [CommRing A] [CommRing B]

/-- Spanning after base change. Let `I ⊆ A[n]` be an ideal with `A[n] ⧸ I` finite over `A`, let `φ :
A →+* B` and let `v` be a family of polynomials. The images of `v` span `B[n] ⧸ I B[n]` over `B`
if and only if the annihilator of the cokernel of `v` on `A[n] ⧸ I` generates the unit ideal of
`B`. -/
theorem _root_.RingHom.span_range_mk_map_eq_top_iff (φ : A →+* B) (I : Ideal (MvPolynomial n A))
    [Module.Finite A (MvPolynomial n A ⧸ I)] {ι : Type*} (v : ι → MvPolynomial n A) :
    Submodule.span B (Set.range fun i ↦ Ideal.Quotient.mk (I.map (map φ)) (map φ (v i))) = ⊤ ↔
      (Module.annihilator A ((MvPolynomial n A ⧸ I) ⧸
        Submodule.span A (Set.range fun i ↦ Ideal.Quotient.mk I (v i)))).map φ = ⊤ := by
  let _ := φ.toAlgebra
  let e := I.tensorQuotientMvPolynomialEquiv (B := B)
  have hspan : (Submodule.span A (Set.range fun i ↦ Ideal.Quotient.mk I (v i))).baseChange B =
      (Submodule.span B (Set.range fun i ↦
        Ideal.Quotient.mk (I.map (map φ)) (map φ (v i)))).map e.symm.toLinearMap := by
    rw [Submodule.baseChange_span, Submodule.map_span, ← Set.range_comp, ← Set.range_comp]
    congr 2
    ext i
    apply e.injective
    -- Unfold the base-change generator and the linear-equivalence coercions to
    -- expose the pure tensor in the tensor-quotient evaluation law.
    change e ((1 : B) ⊗ₜ[A] Ideal.Quotient.mk I (v i)) = e (e.symm _)
    rw [e.apply_symm_apply]
    simpa only [e, one_smul, RingHom.algebraMap_toAlgebra] using
      I.tensorQuotientMvPolynomialEquiv_tmul (B := B) 1 (v i)
  rw [← Submodule.map_eq_top_iff (e := e.symm.toLinearEquiv), ← hspan,
    Submodule.baseChange_eq_top_iff_subsingleton]
  exact TauCeti.Module.annihilator_map_eq_top_iff_subsingleton_tensorProduct.symm

attribute [local instance] Module.free_of_flat_of_isLocalRing in
/-- Monomial bases exist locally. If `A[n] ⧸ I` is a finite flat `A`-module of rank `d`
at the prime `p`, then there are `d` monomials whose images span `A[n] ⧸ I` near `p`: the
annihilator of the cokernel of their images is not contained in `p`. -/
theorem _root_.Ideal.exists_monomials_annihilator_not_le (I : Ideal (MvPolynomial n A))
    [Module.Finite A (MvPolynomial n A ⧸ I)] [Module.Flat A (MvPolynomial n A ⧸ I)]
    (p : PrimeSpectrum A) {d : ℕ} (hp : Module.rankAtStalk (MvPolynomial n A ⧸ I) p = d) :
    ∃ v : Fin d → (n →₀ ℕ), ¬ Module.annihilator A ((MvPolynomial n A ⧸ I) ⧸
      Submodule.span A (Set.range fun l ↦ Ideal.Quotient.mk I (monomial (v l) 1))) ≤
        p.asIdeal := by
  classical
  let f := LocalizedModule.mkLinearMap p.asIdeal.primeCompl (MvPolynomial n A ⧸ I)
  have hspan : Submodule.span (Localization.AtPrime p.asIdeal)
      (Set.range fun m : n →₀ ℕ ↦ f (Ideal.Quotient.mk I (monomial m 1))) = ⊤ := by
    rw [Set.range_comp' f, ← Submodule.localized'_span (S := Localization.AtPrime p.asIdeal)
      (p := p.asIdeal.primeCompl) (f := f), Ideal.span_range_mk_monomial_eq_top,
      Submodule.localized'_top]
  have : Module.FinitePresentation (Localization.AtPrime p.asIdeal)
      (LocalizedModule p.asIdeal.primeCompl (MvPolynomial n A ⧸ I)) :=
    Module.finitePresentation_of_projective _ _
  obtain ⟨κ, a, b, hb⟩ := Module.exists_basis_of_span_of_flat _ hspan
  have : Fintype κ :=
    have := Module.Finite.finite_basis b
    Fintype.ofFinite κ
  have hκ : Fintype.card κ = d := by rw [← hp, Module.rankAtStalk, Module.finrank_eq_card_basis b]
  let e : Fin d ≃ κ := (Fintype.equivFinOfCardEq hκ).symm
  refine ⟨a ∘ e, fun hle ↦ ?_⟩
  rw [← Module.mem_support_iff_of_finite (p := p)] at hle
  refine ((Module.notMem_support_iff' (p := p)).mpr fun c ↦ ?_) hle
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ c
  have hx : f x ∈ (Submodule.span A (Set.range fun l ↦ Ideal.Quotient.mk I
      (monomial ((a ∘ e) l) 1))).localized' (Localization.AtPrime p.asIdeal)
        p.asIdeal.primeCompl f := by
    have hr : f '' Set.range (fun l ↦ Ideal.Quotient.mk I (monomial ((a ∘ e) l) 1)) =
        Set.range b := by
      rw [← Set.range_comp', ← e.surjective.range_comp b]
      simp [Function.comp_def, hb]
    rw [Submodule.localized'_span, hr, b.span_eq]
    trivial
  let N := Submodule.span A (Set.range fun l ↦ Ideal.Quotient.mk I
    (monomial ((a ∘ e) l) 1))
  obtain ⟨m, hm⟩ := (IsLocalizedModule.eq_zero_iff p.asIdeal.primeCompl
    (N.toLocalizedQuotient' (Localization.AtPrime p.asIdeal) p.asIdeal.primeCompl f)).mp
      (by rw [Submodule.toLocalizedQuotient'_mk, Submodule.Quotient.mk_eq_zero]; exact hx)
  exact ⟨m, m.2, hm⟩

end MvPolynomial
