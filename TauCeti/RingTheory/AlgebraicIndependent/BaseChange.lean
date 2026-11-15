/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.AlgebraicIndependent.Defs
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.TensorProduct.MvPolynomial
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Mathlib.RingTheory.AlgebraicIndependent.Basic
import Mathlib.RingTheory.RingHom.Finite
import Mathlib.RingTheory.TensorProduct.Finite

/-!
# Base change of algebraic independence and polynomial evaluation maps

For an `R`-algebra `A`, an `R`-algebra `S`, and a family `y : ι → A`, evaluating `S`-polynomials at
the base-changed family `i ↦ 1 ⊗ₜ[R] y i` in `S ⊗[R] A` factors as the `S`-algebra equivalence
`MvPolynomial ι S ≃ₐ[S] S ⊗[R] MvPolynomial ι R` followed by `Algebra.TensorProduct.lTensor S`
applied to `MvPolynomial.aeval y`. Consequently:

* `TauCeti.adjoin_range_one_tmul_eq_top` and `TauCeti.adjoin_range_one_tmul_eq_top_iff`: generating
  sets of `A` over `R` map to generating sets of `S ⊗[R] A` over `S`, with the converse under
  faithfully flat base change;
* `TauCeti.aeval_one_tmul_finite`: finiteness of `MvPolynomial.aeval y` is preserved under
  arbitrary base change `R → S`;
* `AlgebraicIndependent.one_tmul`: algebraic independence of `y` over `R` is preserved under flat
  base change `R → S`;
* `TauCeti.algebraicIndependent_one_tmul_iff`: faithfully flat base change `R → S` both preserves
  and reflects algebraic independence;
* `AlgebraicIndependent.linearIndependent_of_sum_smul`: if linear combinations
  `i ↦ ∑ j, C i j • x j` of a finite family `x : σ → A` are algebraically independent over `R`,
  then the coefficient rows `C : ι → σ → R` are `R`-linearly independent.
-/

public section

open scoped TensorProduct

namespace TauCeti

/-- Evaluating `S`-polynomials at `i ↦ 1 ⊗ₜ[R] y i` in `S ⊗[R] A` factors through
`MvPolynomial.algebraTensorAlgEquiv` and
`Algebra.TensorProduct.lTensor S (MvPolynomial.aeval y)`. -/
theorem aeval_one_tmul_eq_comp {R A ι : Type*} (S : Type*) [CommSemiring R] [CommSemiring S]
    [Algebra R S] [CommSemiring A] [Algebra R A] (y : ι → A) :
    (MvPolynomial.aeval fun i ↦ (1 ⊗ₜ[R] y i : S ⊗[R] A) : MvPolynomial ι S →ₐ[S] S ⊗[R] A) =
      (Algebra.TensorProduct.lTensor S (MvPolynomial.aeval y)).comp
        (MvPolynomial.algebraTensorAlgEquiv R S).symm.toAlgHom := by
  ext i
  simp

/-- Base-changing a finite polynomial evaluation map `R[X_ι] →ₐ[R] A` to any `R`-algebra `S`
produces a finite `S`-algebra evaluation map `S[X_ι] →ₐ[S] S ⊗[R] A`. -/
theorem aeval_one_tmul_finite {R S A ι : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [CommRing A] [Algebra R A] {y : ι → A}
    (hfin : (MvPolynomial.aeval y : MvPolynomial ι R →ₐ[R] A).Finite) :
    (MvPolynomial.aeval fun i ↦ (1 ⊗ₜ[R] y i : S ⊗[R] A) :
      MvPolynomial ι S →ₐ[S] S ⊗[R] A).Finite := by
  rw [aeval_one_tmul_eq_comp]
  have hid : (AlgHom.id R S).Finite := RingHom.Finite.id S
  change ((Algebra.TensorProduct.map (AlgHom.id R S) (MvPolynomial.aeval y)).toRingHom.comp
    (MvPolynomial.algebraTensorAlgEquiv R S).symm.toRingEquiv.toRingHom).Finite
  exact (RingHom.Finite.tensorProductMap hid hfin).comp
    (RingEquiv.finite (MvPolynomial.algebraTensorAlgEquiv R S).symm.toRingEquiv)

/-- If `x : ι → A` generates `A` as an `R`-algebra, then `i ↦ 1 ⊗ₜ[R] x i` generates `S ⊗[R] A`
as an `S`-algebra for any `R`-algebra `S`. -/
theorem adjoin_range_one_tmul_eq_top {R S A ι : Type*} [CommSemiring R] [CommSemiring S]
    [Algebra R S] [CommSemiring A] [Algebra R A] {x : ι → A}
    (hx : Algebra.adjoin R (Set.range x) = ⊤) :
    Algebra.adjoin S (Set.range fun i ↦ (1 ⊗ₜ[R] x i : S ⊗[R] A)) = ⊤ := by
  rw [Algebra.adjoin_range_eq_range_aeval, AlgHom.range_eq_top] at hx ⊢
  rw [aeval_one_tmul_eq_comp]
  have hl : Function.Surjective (Algebra.TensorProduct.lTensor S (MvPolynomial.aeval x)) :=
    LinearMap.lTensor_surjective S hx
  exact hl.comp (MvPolynomial.algebraTensorAlgEquiv R S).symm.surjective

/-- Under a faithfully flat base change `R → S`, `i ↦ 1 ⊗ₜ[R] x i` generates `S ⊗[R] A` over `S`
if and only if `x` generates `A` over `R`. -/
theorem adjoin_range_one_tmul_eq_top_iff {R S A ι : Type*} [CommRing R] [CommRing S]
    [Algebra R S] [Module.FaithfullyFlat R S] [CommRing A] [Algebra R A] {x : ι → A} :
    Algebra.adjoin S (Set.range fun i ↦ (1 ⊗ₜ[R] x i : S ⊗[R] A)) = ⊤ ↔
      Algebra.adjoin R (Set.range x) = ⊤ := by
  refine ⟨fun h ↦ ?_, adjoin_range_one_tmul_eq_top⟩
  rw [Algebra.adjoin_range_eq_range_aeval, AlgHom.range_eq_top] at h ⊢
  rw [aeval_one_tmul_eq_comp] at h
  have hl : Function.Surjective ((MvPolynomial.aeval x).toLinearMap.lTensor S) :=
    Function.Surjective.of_comp (g := (MvPolynomial.algebraTensorAlgEquiv R S).symm) h
  exact (Module.FaithfullyFlat.lTensor_surjective_iff_surjective R S
    (MvPolynomial.aeval x).toLinearMap).mp hl

end TauCeti

namespace AlgebraicIndependent

/-- Algebraic independence of `y : ι → A` over `R` is preserved by flat base change to `S ⊗[R] A`
over `S`. -/
theorem one_tmul {R A ι : Type*} (S : Type*) [CommRing R] [CommRing S] [Algebra R S]
    [Module.Flat R S] [CommRing A] [Algebra R A] {y : ι → A} (hy : AlgebraicIndependent R y) :
    AlgebraicIndependent S (fun i ↦ (1 ⊗ₜ[R] y i : S ⊗[R] A)) := by
  unfold AlgebraicIndependent
  rw [TauCeti.aeval_one_tmul_eq_comp]
  have hinj : Function.Injective (Algebra.TensorProduct.lTensor S (MvPolynomial.aeval y)) :=
    Module.Flat.lTensor_preserves_injective_linearMap (MvPolynomial.aeval y).toLinearMap hy
  exact hinj.comp (MvPolynomial.algebraTensorAlgEquiv R S).symm.injective

/-- If linear combinations `i ↦ ∑ j, C i j • x j` of a finite family `x : σ → A` are algebraically
independent over `R`, then the rows of `C` are `R`-linearly independent. -/
theorem linearIndependent_of_sum_smul {R A ι σ : Type*} [CommRing R] [CommRing A] [Algebra R A]
    [Fintype σ] {x : σ → A} {C : ι → σ → R}
    (hy : AlgebraicIndependent R (fun i ↦ ∑ j, C i j • x j)) :
    LinearIndependent R C :=
  LinearIndependent.of_comp (Fintype.linearCombination R x) hy.linearIndependent

end AlgebraicIndependent

namespace TauCeti

/-- Under a faithfully flat base change `R → S`, the family `i ↦ 1 ⊗ₜ[R] y i` in `S ⊗[R] A` is
algebraically independent over `S` if and only if `y` is algebraically independent over `R`. -/
theorem algebraicIndependent_one_tmul_iff {R S A ι : Type*} [CommRing R] [CommRing S]
    [Algebra R S] [Module.FaithfullyFlat R S] [CommRing A] [Algebra R A] {y : ι → A} :
    AlgebraicIndependent S (fun i ↦ (1 ⊗ₜ[R] y i : S ⊗[R] A)) ↔ AlgebraicIndependent R y := by
  refine ⟨fun h ↦ ?_, fun h ↦ h.one_tmul S⟩
  unfold AlgebraicIndependent at h ⊢
  let φ : MvPolynomial ι R →ₐ[R] A := MvPolynomial.aeval y
  have heq (z : S ⊗[R] MvPolynomial ι R) :
      (Algebra.TensorProduct.lTensor S φ : S ⊗[R] MvPolynomial ι R →ₐ[S] S ⊗[R] A) z =
        φ.toLinearMap.lTensor S z :=
    TensorProduct.inductionOn z (fun _ _ ↦ rfl) fun _ _ h₁ h₂ ↦ by simp [h₁, h₂]
  have hl : Function.Injective (φ.toLinearMap.lTensor S) := by
    intro u v huv
    apply (MvPolynomial.algebraTensorAlgEquiv R S).injective
    apply h
    rw [aeval_one_tmul_eq_comp, AlgHom.comp_apply, AlgHom.comp_apply]
    simp only [AlgEquiv.coe_toAlgHom, AlgEquiv.symm_apply_apply]
    exact (heq u).trans (huv.trans (heq v).symm)
  exact (Module.FaithfullyFlat.lTensor_injective_iff_injective R S φ.toLinearMap).mp hl

end TauCeti
