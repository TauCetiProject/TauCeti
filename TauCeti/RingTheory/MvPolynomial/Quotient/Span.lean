/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Jie Xu, Shitan Xu
-/
module

public import TauCeti.LinearAlgebra.TensorProduct.Quotient
public import TauCeti.RingTheory.MvPolynomial.Quotient.Basic
public import TauCeti.RingTheory.Flat.Generators
public import TauCeti.RingTheory.Support.BaseChange

/-!
# Spanning loci for polynomial quotients

For a family of polynomial classes with finite cokernel, spanning after coefficient extension
is equivalent to the cokernel annihilator generating the unit ideal after that extension.
For finite flat quotients, monomial spanning loci cover the base. These results supply the open
basis loci for affine Hilbert charts.
-/

public section

section

open TensorProduct

namespace MvPolynomial

variable {n A B : Type*} [CommRing A] [CommRing B]

/-- Spanning after base change. If the polynomial classes of `v` have finite cokernel over `A`,
their images span `B[n] ⧸ I B[n]` over `B` if and only if the annihilator of that cokernel
generates the unit ideal of `B`. -/
theorem _root_.RingHom.span_range_mk_map_eq_top_iff (φ : A →+* B) (I : Ideal (MvPolynomial n A))
    {ι : Type*} (v : ι → MvPolynomial n A)
    [Module.Finite A ((MvPolynomial n A ⧸ I) ⧸
      Submodule.span A (Set.range fun i ↦ Ideal.Quotient.mk I (v i)))] :
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
    simp only [Function.comp_apply, TensorProduct.mk_apply, AlgEquiv.toLinearMap_apply,
      e.apply_symm_apply]
    simpa only [e, one_smul, RingHom.algebraMap_toAlgebra] using
      I.tensorQuotientMvPolynomialEquiv_tmul (B := B) 1 (v i)
  rw [← Submodule.map_eq_top_iff (e := e.symm.toLinearEquiv), ← hspan,
    Submodule.baseChange_eq_top_iff_subsingleton]
  exact TauCeti.Module.annihilator_map_eq_top_iff_subsingleton_tensorProduct.symm

/-- Monomial spanning families exist locally. If `A[n] ⧸ I` is a finite flat `A`-module of rank `d`
at the prime `p`, then there are `d` monomials whose images span `A[n] ⧸ I` near `p`: the
annihilator of the cokernel of their images is not contained in `p`. -/
theorem _root_.Ideal.exists_monomials_annihilator_not_le (I : Ideal (MvPolynomial n A))
    [Module.Finite A (MvPolynomial n A ⧸ I)] [Module.Flat A (MvPolynomial n A ⧸ I)]
    (p : PrimeSpectrum A) {d : ℕ} (hp : Module.rankAtStalk (MvPolynomial n A ⧸ I) p = d) :
    ∃ v : Fin d → (n →₀ ℕ), ¬ Module.annihilator A ((MvPolynomial n A ⧸ I) ⧸
      Submodule.span A (Set.range fun l ↦ Ideal.Quotient.mk I (monomial (v l) 1))) ≤
        p.asIdeal := by
  exact Module.exists_generators_annihilator_not_le _ I.span_range_mk_monomial_eq_top p hp

end MvPolynomial
