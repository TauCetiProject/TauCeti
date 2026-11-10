/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Jie Xu, Shitan Xu
-/
module

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
after that extension. For finitely presented flat
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
  classical
  let _ := φ.toAlgebra
  set N := Submodule.span A (Set.range fun i ↦ Ideal.Quotient.mk I (v i))
  set S := Submodule.span B (Set.range fun i ↦ Ideal.Quotient.mk (I.map (map φ)) (map φ (v i)))
  constructor
  · intro hS
    let e := I.tensorQuotientMvPolynomialEquiv (B := B)
    let Θ := e.symm
    have hΘmk (f : MvPolynomial n A) :
        Θ (Ideal.Quotient.mk _ (map φ f)) = (1 : B) ⊗ₜ[A] Ideal.Quotient.mk I f := by
      apply e.symm_apply_eq.mpr
      simpa only [one_smul, RingHom.algebraMap_toAlgebra] using
        (I.tensorQuotientMvPolynomialEquiv_tmul (B := B) 1 f).symm
    have hT := congrArg (Submodule.map Θ.toLinearMap) hS
    rw [Submodule.map_span, Submodule.map_top, LinearMap.range_eq_top.mpr Θ.surjective,
      ← Set.range_comp] at hT
    let π := LinearMap.baseChange B N.mkQ
    have hπ : Function.Surjective π := LinearMap.lTensor_surjective _ N.mkQ_surjective
    have hker : (⊤ : Submodule B (B ⊗[A] (MvPolynomial n A ⧸ I))) ≤ LinearMap.ker π := by
      rw [← hT, Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      -- Membership in the linear-map kernel is the equation π(value) = 0.
      change π (Θ (Ideal.Quotient.mk _ (map φ (v i)))) = 0
      rw [hΘmk, LinearMap.baseChange_tmul, Submodule.mkQ_apply,
        (Submodule.Quotient.mk_eq_zero N).mpr (Submodule.subset_span ⟨i, rfl⟩), tmul_zero]
    have : Subsingleton (B ⊗[A] ((MvPolynomial n A ⧸ I) ⧸ N)) := by
      refine subsingleton_of_forall_eq 0 fun y ↦ ?_
      obtain ⟨y, rfl⟩ := hπ y
      exact hker trivial
    exact TauCeti.Module.annihilator_map_eq_top_of_subsingleton_tensorProduct (B := B)
  · intro hJ
    let ψ := Ideal.quotientMap (I.map (map φ)) (map φ) Ideal.le_comap_map
    have hψmk (f : MvPolynomial n A) :
        ψ (Ideal.Quotient.mk I f) = Ideal.Quotient.mk _ (map φ f) :=
      Ideal.quotientMap_mk
    have hψ (a : A) (x : MvPolynomial n A ⧸ I) : ψ (a • x) = φ a • ψ x :=
      φ.quotientMap_mvPolynomial_smul I a x
    let ψₗ : (MvPolynomial n A ⧸ I) →ₛₗ[φ]
        (MvPolynomial n B ⧸ I.map (map φ)) :=
      { ψ.toAddMonoidHom with map_smul' := hψ }
    have hN : N ≤ S.comap ψₗ := by
      apply Submodule.span_le.mpr
      rintro _ ⟨i, rfl⟩
      exact Submodule.subset_span ⟨i, hψmk (v i)⟩
    have key (f : MvPolynomial n A) : Ideal.Quotient.mk _ (map φ f) ∈ S := by
      exact ψₗ.apply_mem_of_annihilator_quotient_map_eq_top N S hN hJ
        (Ideal.Quotient.mk I f)
    apply top_unique
    rw [← Ideal.span_range_mk_monomial_eq_top (I.map (map φ)), Submodule.span_le]
    rintro _ ⟨m, rfl⟩
    have h := key (monomial m 1)
    rw [map_monomial, map_one] at h
    exact h

attribute [local instance] Module.free_of_flat_of_isLocalRing in
/-- Monomial bases exist locally. If `A[n] ⧸ I` is a finitely presented flat `A`-module of rank `d`
at the prime `p`, then there are `d` monomials whose images span `A[n] ⧸ I` near `p`: the
annihilator of the cokernel of their images is not contained in `p`. -/
theorem _root_.Ideal.exists_monomials_annihilator_not_le (I : Ideal (MvPolynomial n A))
    [Module.FinitePresentation A (MvPolynomial n A ⧸ I)] [Module.Flat A (MvPolynomial n A ⧸ I)]
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
  obtain ⟨m, hm, s, hms⟩ := (Submodule.mem_localized' _ _ _ _ _).mp hx
  rw [IsLocalizedModule.mk'_eq_iff, Submonoid.smul_def, ← map_smul] at hms
  obtain ⟨c, hc⟩ := IsLocalizedModule.exists_of_eq (S := p.asIdeal.primeCompl) hms
  refine ⟨c * s, (c * s).2, ?_⟩
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, mul_smul,
    ← Submonoid.smul_def, ← hc]
  exact Submodule.smul_of_tower_mem _ c hm

end MvPolynomial
