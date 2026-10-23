/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.DividedPowerAlgebra.UniversalLaw

/-!
# Uniqueness in Roby representability

Composition with the universal law `γ_d` sends a linear map `Γ^d_R(M) → N` to a homogeneous
polynomial law of degree `d`. This file constructs that linear comparison and proves it injective.
It does not assert that every homogeneous law arises this way.

The uniqueness statement requires scalar-extended values, rather than just ground values.
Evaluating at `∑ X_j ⊗ m_j` and extracting a mixed coefficient recovers the value of the linear
map on `∏ dp R (k j) (m j)`. These products span the homogeneous piece, even for modules with
torsion and without inverting factorials.

The construction uses `DividedPowerAlgebra.gamma` and its coefficient formula. The underlying
divided power algebra and polynomial laws are the Mathlib formalizations by Antoine
Chambert-Loir and María Inés de Frutos-Fernández.

## Main declarations

* `DividedPowerAlgebra.homogeneousLawMap`: the linear comparison to homogeneous laws.
* `DividedPowerAlgebra.lid_rTensor_lcoeff_homogeneousLawMap`: recovery by mixed coefficients.
* `DividedPowerAlgebra.homogeneousLawMap_injective`: uniqueness of a representing linear map.
* `DividedPowerAlgebra.homogeneousLawMap_comp` and
  `DividedPowerAlgebra.homogeneousLawMap_comp_mapHomogeneousSubmodule`: naturality in both modules.

## References

* [N. Roby, *Lois polynômes et lois formelles en théorie des modules* (1963),
  Théorème IV.1][Roby-1963]
-/

public section

noncomputable section

universe u

open TensorProduct

namespace DividedPowerAlgebra

variable {R : Type u} [CommSemiring R]
variable {M N P : Type*} [AddCommMonoid M] [Module R M]
variable [AddCommMonoid N] [Module R N] [AddCommMonoid P] [Module R P]

variable (R M N) in
/-- Composition with the universal degree-`d` law, as a linear map into homogeneous laws.
Injectivity is `homogeneousLawMap_injective`; surjectivity is not asserted here. -/
def homogeneousLawMap (d : ℕ) :
    (homogeneousSubmodule (R := R) (M := M) d →ₗ[R] N) →ₗ[R]
      PolynomialLaw.homogeneousSubmodule R M N d where
  toFun f := ⟨f.toPolynomialLaw.comp (gamma R M d), by
    simpa using f.isHomogeneousOfDegree_toPolynomialLaw.comp
      (isHomogeneousOfDegree_gamma (R := R) (M := M) d)⟩
  map_add' f g := by
    apply Subtype.ext
    ext S _ _ x
    simp
  map_smul' r f := by
    apply Subtype.ext
    ext S _ _ x
    simp

/-- The law associated with `f` is its linear polynomial law composed with `γ_d`. -/
@[simp]
theorem coe_homogeneousLawMap_apply (d : ℕ)
    (f : homogeneousSubmodule (R := R) (M := M) d →ₗ[R] N) :
    (homogeneousLawMap R M N d f : M →ₚₗ[R] N) = f.toPolynomialLaw.comp (gamma R M d) :=
  (rfl)

/-- At any scalar algebra, the comparison is the base change of `f` applied to `γ_d`. -/
theorem homogeneousLawMap_toFun (d : ℕ)
    (f : homogeneousSubmodule (R := R) (M := M) d →ₗ[R] N)
    (S : Type*) [CommSemiring S] [Algebra R S] (x : S ⊗[R] M) :
    (homogeneousLawMap R M N d f : M →ₚₗ[R] N).toFun S x =
      f.baseChange S ((gamma R M d).toFun S x) := by
  simp

/-- The ground value of the associated law is `f` evaluated on the divided-power generator. -/
@[simp]
theorem ground_toPolynomialLaw_comp_gamma_apply (d : ℕ)
    (f : homogeneousSubmodule (R := R) (M := M) d →ₗ[R] N) (m : M) :
    (f.toPolynomialLaw.comp (gamma R M d)).ground m =
      f ⟨dp R d m, dp_mem_homogeneousSubmodule d m⟩ := by
  simp [PolynomialLaw.ground_apply, PolynomialLaw.toFun'_eq_toFun, gamma_toFun_tmul]

open MvPolynomial in
/-- Mixed coefficients of the associated law recover `f` on products of divided powers.
The hypothesis fixes the total degree of the monomial, with no factorial factors. -/
theorem lid_rTensor_lcoeff_homogeneousLawMap (d : ℕ)
    (f : homogeneousSubmodule (R := R) (M := M) d →ₗ[R] N)
    {ι : Type*} [Fintype ι] (m : ι → M) (k : ι →₀ ℕ) (hk : ∑ j, k j = d) :
    TensorProduct.lid R N ((lcoeff R k).rTensor N
      ((homogeneousLawMap R M N d f : M →ₚₗ[R] N).toFun (MvPolynomial ι R)
        (∑ j, X j ⊗ₜ[R] m j))) =
      f ⟨∏ j, dp R (k j) (m j), prod_dp_mem_homogeneousSubmodule_of_sum_eq m k hk⟩ := by
  have hgamma : TensorProduct.lid R _ ((lcoeff R k).rTensor _
      ((gamma R M d).toFun (MvPolynomial ι R) (∑ j, X j ⊗ₜ[R] m j))) =
      ⟨∏ j, dp R (k j) (m j), prod_dp_mem_homogeneousSubmodule_of_sum_eq m k hk⟩ := by
    apply Subtype.ext
    simpa only [hk, ite_true] using
      coe_lid_rTensor_lcoeff_gamma_toFun_sum_X_tmul (R := R) d m k
  rw [homogeneousLawMap_toFun, ← hgamma]
  generalize (gamma R M d).toFun (MvPolynomial ι R) (∑ j, X j ⊗ₜ[R] m j) = z
  induction z using TensorProduct.inductionOn with
  | tmul s y => simp
  | add x y hx hy => simp_all

/-- Composition with `γ_d` determines a linear map on the entire homogeneous piece.
Ground values alone need not determine it; the proof uses mixed coefficients over polynomial
scalar algebras. -/
theorem homogeneousLawMap_injective (d : ℕ) :
    Function.Injective (homogeneousLawMap R M N d) := by
  intro f g hfg
  have hprod {ι : Type} [Fintype ι] (m : ι → M) (k : ι →₀ ℕ)
      (hk : ∑ j, k j = d) :
      f ⟨∏ j, dp R (k j) (m j), prod_dp_mem_homogeneousSubmodule_of_sum_eq m k hk⟩ =
      g ⟨∏ j, dp R (k j) (m j), prod_dp_mem_homogeneousSubmodule_of_sum_eq m k hk⟩ := by
    rw [← lid_rTensor_lcoeff_homogeneousLawMap d f m k hk,
      ← lid_rTensor_lcoeff_homogeneousLawMap d g m k hk, hfg]
  apply homogeneousSubmodule_ext
  intro l hl
  let k : Fin l.length →₀ ℕ := Finsupp.equivFunOnFinite.symm fun j ↦ l[j.1].1
  have hk : ∑ j, k j = d := by
    simpa [k] using hl
  have hp := Fin.prod_univ_fun_getElem l (fun nm : ℕ × M ↦ dp R nm.1 nm.2)
  simpa only [k, Finsupp.coe_equivFunOnFinite_symm, hp] using
    hprod (fun j : Fin l.length ↦ l[j.1].2) k hk

/-- Postcomposition of the representing linear map agrees with postcomposition of its law. -/
theorem homogeneousLawMap_comp (d : ℕ)
    (f : homogeneousSubmodule (R := R) (M := M) d →ₗ[R] N) (g : N →ₗ[R] P) :
    (homogeneousLawMap R M P d (g.comp f) : M →ₚₗ[R] P) =
      g.toPolynomialLaw.comp (homogeneousLawMap R M N d f) := by
  simp [PolynomialLaw.comp_assoc]

/-- Precomposition on homogeneous pieces agrees with precomposition of polynomial laws. -/
theorem homogeneousLawMap_comp_mapHomogeneousSubmodule (d : ℕ) (f : M →ₗ[R] N)
    (g : homogeneousSubmodule (R := R) (M := N) d →ₗ[R] P) :
    (homogeneousLawMap R M P d (g.comp (mapHomogeneousSubmodule f d)) : M →ₚₗ[R] P) =
      (homogeneousLawMap R N P d g : N →ₚₗ[R] P).comp f.toPolynomialLaw := by
  simp only [coe_homogeneousLawMap_apply, LinearMap.toPolynomialLaw_comp,
    ← PolynomialLaw.comp_assoc, gamma_comp_toPolynomialLaw]

end DividedPowerAlgebra
