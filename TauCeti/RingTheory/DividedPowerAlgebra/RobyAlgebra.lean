/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.DividedPowerAlgebra.TensorMap
public import TauCeti.RingTheory.PolynomialLaw.Multiplicative
import Mathlib.LinearAlgebra.TensorProduct.Finiteness
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
import TauCeti.Algebra.MvPolynomial.Monomial
import TauCeti.RingTheory.TensorProduct.Maps
import TauCeti.RingTheory.TensorProduct.MvPolynomial

/-!
# The Roby algebra of multiplicative polynomial laws

For an `R`-algebra `A`, associative and unital but not necessarily commutative, and `d : ℕ`, the
homogeneous piece `Γ^d_R(A)` of the divided power algebra carries an internal multiplication: the
tensor map `Γ^d_R(A) ⊗ Γ^d_R(A) → Γ^d_R(A ⊗ A)` followed by `Γ^d` of the multiplication of `A`.
It satisfies `γ_d(x) γ_d(y) = γ_d(x y)` and has unit `γ_d(1)`, and it makes `Γ^d_R(A)` an
associative `R`-algebra, the Roby algebra `RobyAlgebra R A d`. This product is not the graded
product of `Γ_R(A)`: over `ℤ`, `γ_2(1) γ_2(1) = 6 γ_4(1)` in `Γ_ℤ(ℤ)`, while the internal product
of `γ_2(1)` with itself is `γ_2(1)`.

The algebra maps `Γ^d_R(A) → B` to any `R`-algebra `B` are identified with the multiplicative
polynomial laws `A → B` homogeneous of degree `d`, by composition with the universal
multiplicative law `x ↦ γ_d(x)`. In degree one, multiplicative laws are the algebra maps
`A →ₐ[R] B` (`PolynomialLaw.algHomEquiv`).

## Main declarations

* `DividedPowerAlgebra.homogeneousMul`: the internal product of `Γ^d_R(A)`, as a bilinear map.
* `DividedPowerAlgebra.homogeneousMul_baseChange_gamma`: after every scalar extension,
  `γ_d(u) γ_d(v) = γ_d(u v)`.
* `DividedPowerAlgebra.homogeneousMul_assoc`, `DividedPowerAlgebra.homogeneousMul_one_left` and
  `DividedPowerAlgebra.homogeneousMul_one_right`: the internal product is associative with unit
  `γ_d(1)`.
* `DividedPowerAlgebra.RobyAlgebra R A d`: the Roby algebra, with its `Semiring` and `Algebra R`
  instances; `DividedPowerAlgebra.RobyAlgebra.linearEquiv` identifies it with `Γ^d_R(A)` as an
  `R`-module, and `DividedPowerAlgebra.RobyAlgebra.linearEquiv_mul` computes its product.
* `DividedPowerAlgebra.RobyAlgebra.gamma`: the universal multiplicative law `A → Γ^d_R(A)`, with
  `DividedPowerAlgebra.RobyAlgebra.gamma_toFun`,
  `DividedPowerAlgebra.RobyAlgebra.isHomogeneousOfDegree_gamma` and
  `DividedPowerAlgebra.RobyAlgebra.isMultiplicative_gamma`.
* `DividedPowerAlgebra.RobyAlgebra.algHomEquiv`: algebra maps `Γ^d_R(A) →ₐ[R] B` are equivalent
  to multiplicative polynomial laws `A → B` homogeneous of degree `d`.

## Implementation notes

The homogeneous piece `Γ^d_R(A)` is spanned by products `∏ⱼ γ_{kⱼ}(mⱼ)` with `∑ⱼ kⱼ = d`, but
in general not by the elements `γ_d(x)`, so identities of the internal product cannot be checked
on the elements `γ_d(x)` alone. They are checked after scalar extension instead: the product
`∏ⱼ γ_{kⱼ}(mⱼ)` is the coefficient of `∏ⱼ Tⱼ ^ kⱼ` in `γ_d(∑ⱼ Tⱼ ⊗ mⱼ)` over the polynomial ring
`R[Tⱼ]`. Associativity compares coefficients of `γ_d(u) γ_d(v) γ_d(w) = γ_d(u v w)` for generic
`u`, `v` and `w` in three disjoint groups of variables, and the multiplicativity of the linear map
representing a multiplicative law compares coefficients in two groups. The identity
`γ_d(u) γ_d(v) = γ_d(u v)` itself follows from the mixed coefficient formula for the tensor map,
together with the vanishing of the coefficients of `γ_d(∑ᵢ ∑ⱼ XᵢYⱼ ⊗ (mᵢ ⊗ nⱼ))` outside
bidegree `(d, d)`.

## References

* [N. Roby, *Lois polynômes multiplicatives universelles*, C. R. Acad. Sci. Paris 290 (1980)]
* [G. Chenevier, *The p-adic analytic space of pseudocharacters of a profinite group and
  pseudorepresentations over arbitrary rings*](https://arxiv.org/abs/0809.0415), §1.1 and
  footnote 13
* [N. Roby, *Lois polynômes et lois formelles en théorie des modules* (1963), IV §11][Roby-1963]
* The ambient `DividedPowerAlgebra` and the `PolynomialLaw`s are the Mathlib formalizations by
  Antoine Chambert-Loir and María Inés de Frutos-Fernández.
-/

public section

noncomputable section

universe u

open TensorProduct MvPolynomial
open LinearMap (BilinMap)

namespace DividedPowerAlgebra

variable {R : Type u} [CommSemiring R] {A : Type*} [Semiring A] [Algebra R A]

variable (R A) in
/-- The internal product of the homogeneous piece `Γ^d_R(A)` of the divided power algebra of an
`R`-algebra `A`: the tensor map `Γ^d_R(A) ⊗ Γ^d_R(A) → Γ^d_R(A ⊗ A)` followed by `Γ^d` of the
multiplication `A ⊗ A → A` (`homogeneousMul_apply`). It sends `γ_d(x), γ_d(y)` to `γ_d(x * y)`
(`homogeneousMul_dp_dp`), and it is the multiplication of `RobyAlgebra R A d`. -/
def homogeneousMul (d : ℕ) :
    BilinMap R (homogeneousSubmodule (R := R) (M := A) d)
      (homogeneousSubmodule (R := R) (M := A) d) :=
  (TensorProduct.mk R _ _).compr₂
    (mapHomogeneousSubmodule (LinearMap.mul' R A) d ∘ₗ homogeneousTensorMap R A A d)

/-- The internal product is the tensor map followed by `Γ^d` of the multiplication of `A`. -/
theorem homogeneousMul_apply (d : ℕ) (x y : homogeneousSubmodule (R := R) (M := A) d) :
    homogeneousMul R A d x y =
      mapHomogeneousSubmodule (LinearMap.mul' R A) d (homogeneousTensorMap R A A d (x ⊗ₜ y)) :=
  (rfl)

/-- The internal product sends `γ_d(x), γ_d(y)` to `γ_d(x * y)`. -/
@[simp]
theorem homogeneousMul_dp_dp (d : ℕ) (x y : A) :
    homogeneousMul R A d ⟨dp R d x, dp_mem_homogeneousSubmodule d x⟩
        ⟨dp R d y, dp_mem_homogeneousSubmodule d y⟩ =
      ⟨dp R d (x * y), dp_mem_homogeneousSubmodule d (x * y)⟩ := by
  rw [homogeneousMul_apply, homogeneousTensorMap_dp_tmul_dp, mapHomogeneousSubmodule_dp,
    LinearMap.mul'_apply]

/-- The generic case of `homogeneousMul_baseChange_gamma`: two generic combinations in disjoint
groups of variables. -/
private theorem homogeneousMul_baseChange_gamma_generic (d : ℕ) {ι κ : Type*} [Fintype ι]
    [Fintype κ] (m : ι → A) (n : κ → A) :
    BilinMap.baseChange (MvPolynomial (ι ⊕ κ) R) (homogeneousMul R A d)
        ((gamma R A d).toFun _ (∑ i, X (Sum.inl i) ⊗ₜ[R] m i))
        ((gamma R A d).toFun _ (∑ j, X (Sum.inr j) ⊗ₜ[R] n j)) =
      (gamma R A d).toFun _
        ((∑ i, X (Sum.inl i) ⊗ₜ[R] m i) * ∑ j, X (Sum.inr j) ⊗ₜ[R] n j) := by
  classical
  set T := MvPolynomial (ι ⊕ κ) R
  -- The element `W = ∑ᵢ ∑ⱼ XᵢYⱼ ⊗ (mᵢ ⊗ nⱼ)` whose image under the multiplication is `U * V`.
  set W : T ⊗[R] (A ⊗[R] A) := ∑ i, ∑ j, (X (Sum.inl i) * X (Sum.inr j)) ⊗ₜ[R] (m i ⊗ₜ[R] n j)
  have hUV : (∑ i, X (Sum.inl i) ⊗ₜ[R] m i) * (∑ j, X (Sum.inr j) ⊗ₜ[R] n j) =
      (LinearMap.mul' R A).baseChange T W := by
    simp [W, Finset.sum_mul_sum, Algebra.TensorProduct.tmul_mul_tmul, map_sum]
  have hRHS : (gamma R A d).toFun T
      ((∑ i, X (Sum.inl i) ⊗ₜ[R] m i) * ∑ j, X (Sum.inr j) ⊗ₜ[R] n j) =
      (mapHomogeneousSubmodule (LinearMap.mul' R A) d).baseChange T
        ((gamma R (A ⊗[R] A) d).toFun T W) := by
    rw [hUV, ← LinearMap.toPolynomialLaw_toFun, ← PolynomialLaw.toFun_comp_apply,
      gamma_comp_toPolynomialLaw, PolynomialLaw.toFun_comp_apply, LinearMap.toPolynomialLaw_toFun]
  -- The coefficients of `γ_d(W)`: the tensor map in bidegree `(d, d)`, and zero elsewhere.
  have hG : (gamma R (A ⊗[R] A) d).toFun T W =
      ∑ a ∈ Finset.univ.finsuppAntidiag d, ∑ b ∈ Finset.univ.finsuppAntidiag d,
        ((∏ i, (X (Sum.inl i) : T) ^ a i) * ∏ j, (X (Sum.inr j) : T) ^ b j) ⊗ₜ[R]
          homogeneousTensorMap R A A d
            (DirectSum.decompose (homogeneousSubmodule (R := R) (M := A))
                (∏ i, dp R (a i) (m i)) d ⊗ₜ
              DirectSum.decompose (homogeneousSubmodule (R := R) (M := A))
                (∏ j, dp R (b j) (n j)) d) := by
    refine MvPolynomial.ext_lid_rTensor_lcoeff fun e ↦ ?_
    simp only [map_sum, LinearMap.rTensor_tmul, lcoeff_apply, TensorProduct.lid_tmul,
      coeff_prod_X_pow_mul_prod_X_pow, ite_smul, one_smul, zero_smul]
    by_cases h : (∑ i, e (Sum.inl i) = d) ∧ ∑ j, e (Sum.inr j) = d
    · -- In bidegree `(d, d)`, the coefficient is given by the mixed coefficient formula.
      set a₀ : ι →₀ ℕ := Finsupp.equivFunOnFinite.symm fun i ↦ e (Sum.inl i)
      set b₀ : κ →₀ ℕ := Finsupp.equivFunOnFinite.symm fun j ↦ e (Sum.inr j)
      have ha₀ : ∑ i, a₀ i = d := by simpa [a₀] using h.1
      have hb₀ : ∑ j, b₀ j = d := by simpa [b₀] using h.2
      have he : Finsupp.sumElim a₀ b₀ = e := by ext (k | k) <;> simp [a₀, b₀]
      have hcond (a : ι →₀ ℕ) (b : κ →₀ ℕ) :
          ((∀ i, a i = e (Sum.inl i)) ∧ ∀ j, b j = e (Sum.inr j)) ↔ b = b₀ ∧ a = a₀ := by
        simp [a₀, b₀, Finsupp.ext_iff, and_comm]
      have hmix := homogeneousTensorMap_tmul_prod_dp (R := R) d m n a₀ b₀ ha₀ hb₀
      rw [he] at hmix
      simp only [hcond, ite_and, Finset.sum_ite_eq', Finset.mem_finsuppAntidiag, ha₀, hb₀,
        Finset.subset_univ, and_self, ite_true]
      rw [decompose_prod_dp m a₀ ha₀, decompose_prod_dp n b₀ hb₀, hmix]
    · -- Outside bidegree `(d, d)`, both coefficients vanish: `γ_d(W)` only involves monomials
      -- `∏_{(i, j)} (XᵢYⱼ) ^ lᵢⱼ` with `∑ l = d`, of weight `d` in each group of variables.
      have hW :
          W = ∑ p : ι × κ, (X (Sum.inl p.1) * X (Sum.inr p.2)) ⊗ₜ[R] (m p.1 ⊗ₜ[R] n p.2) :=
        (Fintype.sum_prod_type' _).symm
      rw [hW, gamma_toFun_sum_tmul]
      simp only [map_sum, LinearMap.rTensor_tmul, lcoeff_apply, TensorProduct.lid_tmul]
      refine (Finset.sum_eq_zero fun l hl ↦ ?_).trans
        (Finset.sum_eq_zero fun a ha ↦ Finset.sum_eq_zero fun b hb ↦ ?_).symm
      · have hl := (Finset.mem_finsuppAntidiag.mp hl).1
        have hw (w : ι ⊕ κ → ℕ) : IsWeightedHomogeneous w
            (∏ p, (X (Sum.inl p.1) * X (Sum.inr p.2) : T) ^ l p)
            (∑ p, l p • (w (Sum.inl p.1) + w (Sum.inr p.2))) :=
          IsWeightedHomogeneous.prod _ _ _ fun p _ ↦
            ((isWeightedHomogeneous_X R w _).mul (isWeightedHomogeneous_X R w _)).pow (l p)
        have hweight (w : ι ⊕ κ → ℕ) : Finsupp.weight w e =
            ∑ i, e (Sum.inl i) * w (Sum.inl i) + ∑ j, e (Sum.inr j) * w (Sum.inr j) := by
          simp [Finsupp.weight_apply, Finsupp.sum_fintype, Fintype.sum_sum_type]
        rcases not_and_or.mp h with h | h
        · rw [(hw (Sum.elim 1 0)).coeff_eq_zero e (by simpa [hweight, hl] using h), zero_smul]
        · rw [(hw (Sum.elim 0 1)).coeff_eq_zero e (by simpa [hweight, hl] using h), zero_smul]
      · refine ite_eq_right_iff.mpr fun ⟨ha', hb'⟩ ↦ absurd ⟨?_, ?_⟩ h
        · simpa [ha'] using (Finset.mem_finsuppAntidiag.mp ha).1
        · simpa [hb'] using (Finset.mem_finsuppAntidiag.mp hb).1
  rw [hRHS, hG, gamma_toFun_sum_tmul, gamma_toFun_sum_tmul]
  simp only [map_sum, LinearMap.sum_apply, LinearMap.BilinMap.baseChange_tmul,
    LinearMap.baseChange_tmul, homogeneousMul_apply]
  exact Finset.sum_comm

/-- After scalar extension to any commutative `R`-algebra `S`, the internal product of
`Γ^d_R(A)` satisfies `γ_d(u) γ_d(v) = γ_d(u * v)` for all `u v : S ⊗[R] A`. -/
theorem homogeneousMul_baseChange_gamma (d : ℕ) {S : Type*} [CommSemiring S] [Algebra R S]
    (u v : S ⊗[R] A) :
    BilinMap.baseChange S (homogeneousMul R A d) ((gamma R A d).toFun S u)
        ((gamma R A d).toFun S v) =
      (gamma R A d).toFun S (u * v) := by
  -- Both sides are compatible with scalar extension, so it suffices to treat generic `u` and `v`.
  obtain ⟨p, s, m, rfl⟩ := TensorProduct.exists_sum_tmul_eq u
  obtain ⟨q, t, n, rfl⟩ := TensorProduct.exists_sum_tmul_eq v
  let θ : MvPolynomial (Fin p ⊕ Fin q) R →ₐ[R] S := aeval (Sum.elim s t)
  have hu : ∑ i, s i ⊗ₜ[R] m i = θ.toLinearMap.rTensor A (∑ i, X (Sum.inl i) ⊗ₜ[R] m i) := by
    simp [θ]
  have hv : ∑ j, t j ⊗ₜ[R] n j = θ.toLinearMap.rTensor A (∑ j, X (Sum.inr j) ⊗ₜ[R] n j) := by
    simp [θ]
  rw [hu, hv, ← PolynomialLaw.isCompat_apply, ← PolynomialLaw.isCompat_apply,
    ← LinearMap.BilinMap.rTensor_baseChange_apply, homogeneousMul_baseChange_gamma_generic,
    PolynomialLaw.isCompat_apply]
  simp only [AlgHom.rTensor_toLinearMap_apply, map_mul]

/-- Associativity of the internal product on products of divided powers, obtained by comparing
coefficients in `γ_d(u) γ_d(v) γ_d(w) = γ_d(u v w)` for generic `u`, `v` and `w` in three
disjoint groups of variables. -/
private theorem homogeneousMul_assoc_prod_dp (d : ℕ) {p q r : ℕ} (m : Fin p → A)
    (n : Fin q → A) (o : Fin r → A) (a : Fin p →₀ ℕ) (b : Fin q →₀ ℕ) (c : Fin r →₀ ℕ)
    (ha : ∑ i, a i = d) (hb : ∑ j, b j = d) (hc : ∑ k, c k = d) :
    homogeneousMul R A d
        (homogeneousMul R A d ⟨_, prod_dp_mem_homogeneousSubmodule_of_sum_eq m a ha⟩
          ⟨_, prod_dp_mem_homogeneousSubmodule_of_sum_eq n b hb⟩)
        ⟨_, prod_dp_mem_homogeneousSubmodule_of_sum_eq o c hc⟩ =
      homogeneousMul R A d ⟨_, prod_dp_mem_homogeneousSubmodule_of_sum_eq m a ha⟩
        (homogeneousMul R A d ⟨_, prod_dp_mem_homogeneousSubmodule_of_sum_eq n b hb⟩
          ⟨_, prod_dp_mem_homogeneousSubmodule_of_sum_eq o c hc⟩) := by
  classical
  -- Associativity for generic combinations in three disjoint groups of variables.
  have generic :
      BilinMap.baseChange (MvPolynomial ((Fin p ⊕ Fin q) ⊕ Fin r) R) (homogeneousMul R A d)
        (BilinMap.baseChange _ (homogeneousMul R A d)
          ((gamma R A d).toFun _ (∑ i, X (Sum.inl (Sum.inl i)) ⊗ₜ[R] m i))
          ((gamma R A d).toFun _ (∑ j, X (Sum.inl (Sum.inr j)) ⊗ₜ[R] n j)))
        ((gamma R A d).toFun _ (∑ k, X (Sum.inr k) ⊗ₜ[R] o k)) =
      BilinMap.baseChange _ (homogeneousMul R A d)
        ((gamma R A d).toFun _ (∑ i, X (Sum.inl (Sum.inl i)) ⊗ₜ[R] m i))
        (BilinMap.baseChange _ (homogeneousMul R A d)
          ((gamma R A d).toFun _ (∑ j, X (Sum.inl (Sum.inr j)) ⊗ₜ[R] n j))
          ((gamma R A d).toFun _ (∑ k, X (Sum.inr k) ⊗ₜ[R] o k))) := by
    simp only [homogeneousMul_baseChange_gamma, mul_assoc]
  have key := congrArg (fun z ↦ TensorProduct.lid R _
      ((lcoeff R (Finsupp.sumElim (Finsupp.sumElim a b) c)).rTensor _ z)) generic
  -- The coefficient of `Xᵃ Yᵇ Zᶜ` at the exponent `(a, b, c)` singles out one term.
  have hcoeff (a' : Fin p →₀ ℕ) (b' : Fin q →₀ ℕ) (c' : Fin r →₀ ℕ) :
      ((∏ i, (X (Sum.inl (Sum.inl i)) : MvPolynomial ((Fin p ⊕ Fin q) ⊕ Fin r) R) ^ a' i) *
        ((∏ j, (X (Sum.inl (Sum.inr j)) : MvPolynomial ((Fin p ⊕ Fin q) ⊕ Fin r) R) ^ b' j) *
          ∏ k, (X (Sum.inr k) : MvPolynomial ((Fin p ⊕ Fin q) ⊕ Fin r) R) ^ c' k)).coeff
          (Finsupp.sumElim (Finsupp.sumElim a b) c) =
        if a' = a ∧ b' = b ∧ c' = c then 1 else 0 := by
    have h := Fintype.prod_sum_type (fun k ↦
      (X (Sum.inl k) : MvPolynomial ((Fin p ⊕ Fin q) ⊕ Fin r) R) ^ Sum.elim a' b' k)
    simp only [Sum.elim_inl, Sum.elim_inr] at h
    rw [← mul_assoc, ← h, MvPolynomial.coeff_prod_X_pow_mul_prod_X_pow]
    simp [Sum.forall, Finsupp.ext_iff, and_assoc]
  simp only [gamma_toFun_sum_tmul, map_sum, LinearMap.sum_apply,
    LinearMap.BilinMap.baseChange_tmul, mul_assoc, LinearMap.rTensor_tmul, lcoeff_apply,
    TensorProduct.lid_tmul, hcoeff, ite_and, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq',
    Finset.mem_finsuppAntidiag, ha, hb, hc, Finset.subset_univ, and_self, ite_true] at key
  rwa [decompose_prod_dp m a ha, decompose_prod_dp n b hb, decompose_prod_dp o c hc] at key

/-- The internal product is associative. -/
theorem homogeneousMul_assoc (d : ℕ)
    (x y z : homogeneousSubmodule (R := R) (M := A) d) :
    homogeneousMul R A d (homogeneousMul R A d x y) z =
      homogeneousMul R A d x (homogeneousMul R A d y z) := by
  -- Reduce to products of divided powers in `z`, then in `y`, then in `x`.
  suffices hz : homogeneousMul R A d (homogeneousMul R A d x y) =
      homogeneousMul R A d x ∘ₗ homogeneousMul R A d y from
    LinearMap.congr_fun hz z
  refine homogeneousSubmodule_ext_prod_dp fun r o c hc ↦ ?_
  suffices hy :
      (homogeneousMul R A d).flip ⟨_, prod_dp_mem_homogeneousSubmodule_of_sum_eq o c hc⟩ ∘ₗ
        homogeneousMul R A d x = homogeneousMul R A d x ∘ₗ
          (homogeneousMul R A d).flip ⟨_, prod_dp_mem_homogeneousSubmodule_of_sum_eq o c hc⟩ from
    LinearMap.congr_fun hy y
  refine homogeneousSubmodule_ext_prod_dp fun q n b hb ↦ ?_
  suffices hx :
      (homogeneousMul R A d).flip ⟨_, prod_dp_mem_homogeneousSubmodule_of_sum_eq o c hc⟩ ∘ₗ
        (homogeneousMul R A d).flip ⟨_, prod_dp_mem_homogeneousSubmodule_of_sum_eq n b hb⟩ =
      (homogeneousMul R A d).flip
        (homogeneousMul R A d ⟨_, prod_dp_mem_homogeneousSubmodule_of_sum_eq n b hb⟩
          ⟨_, prod_dp_mem_homogeneousSubmodule_of_sum_eq o c hc⟩) from
    LinearMap.congr_fun hx x
  refine homogeneousSubmodule_ext_prod_dp fun p m a ha ↦ ?_
  exact homogeneousMul_assoc_prod_dp d m n o (Finsupp.equivFunOnFinite.symm a)
    (Finsupp.equivFunOnFinite.symm b) (Finsupp.equivFunOnFinite.symm c) ha hb hc

/-- `γ_d(1)` is a left unit for the internal product. -/
@[simp]
theorem homogeneousMul_one_left (d : ℕ) (y : homogeneousSubmodule (R := R) (M := A) d) :
    homogeneousMul R A d ⟨dp R d 1, dp_mem_homogeneousSubmodule d 1⟩ y = y := by
  suffices h : homogeneousMul R A d ⟨dp R d 1, dp_mem_homogeneousSubmodule d 1⟩ = LinearMap.id from
    LinearMap.congr_fun h y
  refine homogeneousLawMap_injective d (Subtype.ext ?_)
  ext S _ _ u
  rw [PolynomialLaw.toFun'_eq_toFun, PolynomialLaw.toFun'_eq_toFun, homogeneousLawMap_toFun,
    homogeneousLawMap_toFun, LinearMap.baseChange_id, LinearMap.id_apply]
  rw [← LinearMap.BilinMap.baseChange_one_tmul, ← gamma_toFun_one,
    homogeneousMul_baseChange_gamma, one_mul]

/-- `γ_d(1)` is a right unit for the internal product. -/
@[simp]
theorem homogeneousMul_one_right (d : ℕ) (x : homogeneousSubmodule (R := R) (M := A) d) :
    homogeneousMul R A d x ⟨dp R d 1, dp_mem_homogeneousSubmodule d 1⟩ = x := by
  suffices h :
      (homogeneousMul R A d).flip ⟨dp R d 1, dp_mem_homogeneousSubmodule d 1⟩ = LinearMap.id from
    LinearMap.congr_fun h x
  refine homogeneousLawMap_injective d (Subtype.ext ?_)
  ext S _ _ u
  rw [PolynomialLaw.toFun'_eq_toFun, PolynomialLaw.toFun'_eq_toFun, homogeneousLawMap_toFun,
    homogeneousLawMap_toFun, LinearMap.baseChange_id, LinearMap.id_apply]
  rw [← LinearMap.BilinMap.baseChange_tmul_one, ← gamma_toFun_one,
    homogeneousMul_baseChange_gamma, mul_one]

/-- The linear map representing a multiplicative homogeneous law of degree `d` is multiplicative
for the internal product. -/
private theorem homogeneousLawEquiv_symm_homogeneousMul {B : Type*} [Semiring B] [Algebra R B]
    (d : ℕ)
    (f : PolynomialLaw.homogeneousSubmodule R A B d) (hf : (f : A →ₚₗ[R] B).IsMultiplicative)
    (x y : homogeneousSubmodule (R := R) (M := A) d) :
    (homogeneousLawEquiv R A B d).symm f (homogeneousMul R A d x y) =
      (homogeneousLawEquiv R A B d).symm f x * (homogeneousLawEquiv R A B d).symm f y := by
  set ρ := (homogeneousLawEquiv R A B d).symm f
  have hρ {S : Type u} [CommSemiring S] [Algebra R S] (u : S ⊗[R] A) :
      ρ.baseChange S ((gamma R A d).toFun S u) = (f : A →ₚₗ[R] B).toFun S u := by
    rw [← homogeneousLawMap_toFun, ← homogeneousLawEquiv_apply, LinearEquiv.apply_symm_apply]
  suffices h : (homogeneousMul R A d).compr₂ ρ = (LinearMap.mul R B).compl₁₂ ρ ρ from
    LinearMap.congr_fun₂ h x y
  refine bilinMap_ext_gamma d fun p q m n ↦ ?_
  rw [LinearMap.BilinMap.baseChange_compr₂, LinearMap.BilinMap.baseChange_compl₁₂,
    LinearMap.compr₂_apply, LinearMap.compl₁₂_apply, homogeneousMul_baseChange_gamma, hρ, hρ, hρ,
    LinearMap.BilinMap.baseChange_mul, hf.toFun_mul]

variable (R A) in
/-- The **Roby algebra** `Γ^d_R(A)` of an `R`-algebra `A`, for `d : ℕ`. As an `R`-module it is
the degree-`d` homogeneous piece of the divided power algebra `Γ_R(A)`
(`DividedPowerAlgebra.RobyAlgebra.linearEquiv`). Its multiplication is the internal product
`Γ^d_R(A) ⊗ Γ^d_R(A) → Γ^d_R(A ⊗ A) → Γ^d_R(A)`, the tensor map followed by `Γ^d` of the
multiplication of `A`, so that `γ_d(x) * γ_d(y) = γ_d(x * y)`, with unit `γ_d(1)`. This product
is not the graded product of `Γ_R(A)`, and it is not necessarily commutative. The algebra maps
from `Γ^d_R(A)` to an `R`-algebra `B` classify the multiplicative polynomial laws `A → B`
homogeneous of degree `d` (`DividedPowerAlgebra.RobyAlgebra.algHomEquiv`). -/
def RobyAlgebra (d : ℕ) : Type _ := homogeneousSubmodule (R := R) (M := A) d

namespace RobyAlgebra

variable {d : ℕ}

instance : AddCommMonoid (RobyAlgebra R A d) :=
  inferInstanceAs (AddCommMonoid (homogeneousSubmodule (R := R) (M := A) d))

instance : Module R (RobyAlgebra R A d) :=
  inferInstanceAs (Module R (homogeneousSubmodule (R := R) (M := A) d))

variable (R A d) in
/-- The Roby algebra `Γ^d_R(A)` is the homogeneous piece `Γ^d_R(A)` of the divided power
algebra, as an `R`-module. -/
def linearEquiv : RobyAlgebra R A d ≃ₗ[R] homogeneousSubmodule (R := R) (M := A) d :=
  LinearEquiv.refl R _

/-- The product of the Roby algebra is the internal product `homogeneousMul`. -/
instance : Mul (RobyAlgebra R A d) where
  mul x y :=
    (linearEquiv R A d).symm (homogeneousMul R A d (linearEquiv R A d x) (linearEquiv R A d y))

/-- The unit of the Roby algebra is `γ_d(1)`. -/
instance : One (RobyAlgebra R A d) where
  one := (linearEquiv R A d).symm ⟨dp R d 1, dp_mem_homogeneousSubmodule d 1⟩

private theorem mul_def (x y : RobyAlgebra R A d) :
    x * y = (linearEquiv R A d).symm
      (homogeneousMul R A d (linearEquiv R A d x) (linearEquiv R A d y)) :=
  (rfl)

/-- The product of the Roby algebra is the tensor map
`Γ^d_R(A) ⊗ Γ^d_R(A) → Γ^d_R(A ⊗ A)` followed by `Γ^d` of the multiplication of `A`. -/
theorem linearEquiv_mul (x y : RobyAlgebra R A d) :
    linearEquiv R A d (x * y) = mapHomogeneousSubmodule (LinearMap.mul' R A) d
      (homogeneousTensorMap R A A d (linearEquiv R A d x ⊗ₜ linearEquiv R A d y)) := by
  rw [mul_def, LinearEquiv.apply_symm_apply, homogeneousMul_apply]

/-- The unit of the Roby algebra is `γ_d(1)`. -/
@[simp]
theorem linearEquiv_one :
    linearEquiv R A d 1 = ⟨dp R d 1, dp_mem_homogeneousSubmodule d 1⟩ :=
  LinearEquiv.apply_symm_apply _ _

/-- The Roby algebra is an associative semiring, noncommutative in general. -/
instance : Semiring (RobyAlgebra R A d) where
  left_distrib x y z := by simp only [mul_def, map_add]
  right_distrib x y z := by simp only [mul_def, map_add, LinearMap.add_apply]
  zero_mul x := by simp only [mul_def, map_zero, LinearMap.zero_apply]
  mul_zero x := by simp only [mul_def, map_zero]
  mul_assoc x y z := by simp only [mul_def, LinearEquiv.apply_symm_apply, homogeneousMul_assoc]
  one_mul x := by
    rw [mul_def, linearEquiv_one, homogeneousMul_one_left, LinearEquiv.symm_apply_apply]
  mul_one x := by
    rw [mul_def, linearEquiv_one, homogeneousMul_one_right, LinearEquiv.symm_apply_apply]

instance : Algebra R (RobyAlgebra R A d) :=
  Algebra.ofModule (fun r x y ↦ by simp only [mul_def, map_smul, LinearMap.smul_apply])
    (fun r x y ↦ by simp only [mul_def, map_smul])

variable (R A d) in
/-- The universal multiplicative polynomial law `A → Γ^d_R(A)` of degree `d`, whose ground value
is `x ↦ γ_d(x)` (`ground_gamma_apply`): the universal homogeneous law
`DividedPowerAlgebra.gamma R A d`, with values in the Roby algebra. -/
def gamma : A →ₚₗ[R] RobyAlgebra R A d :=
  (linearEquiv R A d).symm.toLinearMap.toPolynomialLaw.comp (DividedPowerAlgebra.gamma R A d)

/-- The ground value of the universal multiplicative law at `x` is `γ_d(x)`. -/
theorem ground_gamma_apply (x : A) :
    (gamma R A d).ground x =
      (linearEquiv R A d).symm ⟨dp R d x, dp_mem_homogeneousSubmodule d x⟩ := by
  rw [gamma, ground_toPolynomialLaw_comp_gamma_apply, LinearEquiv.coe_coe]

/-- After scalar extension to `S`, the universal multiplicative law is the base change of the
identification with `Γ^d_R(A)` applied to the universal homogeneous law. -/
theorem gamma_toFun {S : Type*} [CommSemiring S] [Algebra R S] (u : S ⊗[R] A) :
    (gamma R A d).toFun S u =
      (linearEquiv R A d).symm.toLinearMap.baseChange S
        ((DividedPowerAlgebra.gamma R A d).toFun S u) := by
  rw [gamma, PolynomialLaw.toFun_comp_apply, LinearMap.toPolynomialLaw_toFun]

/-- The universal multiplicative law is homogeneous of degree `d`. -/
theorem isHomogeneousOfDegree_gamma : (gamma R A d).IsHomogeneousOfDegree d := by
  rw [gamma]
  simpa using (linearEquiv R A d).symm.toLinearMap.isHomogeneousOfDegree_toPolynomialLaw.comp
    (DividedPowerAlgebra.isHomogeneousOfDegree_gamma (R := R) (M := A) d)

/-- **The universal multiplicative law**: `x ↦ γ_d(x)` is multiplicative for the product of the
Roby algebra, after every scalar extension. -/
theorem isMultiplicative_gamma : (gamma R A d).IsMultiplicative where
  toFun'_one S _ _ := by
    rw [PolynomialLaw.toFun'_eq_toFun, gamma_toFun, gamma_toFun_one, LinearMap.baseChange_tmul,
      Algebra.TensorProduct.one_def, LinearEquiv.coe_coe, ← linearEquiv_one,
      LinearEquiv.symm_apply_apply]
  toFun'_mul x y := by
    have h : (homogeneousMul R A d).compr₂ (linearEquiv R A d).symm.toLinearMap =
        (LinearMap.mul R (RobyAlgebra R A d)).compl₁₂ (linearEquiv R A d).symm.toLinearMap
          (linearEquiv R A d).symm.toLinearMap :=
      LinearMap.ext₂ fun x y ↦ by
        rw [LinearMap.compr₂_apply, LinearMap.compl₁₂_apply, LinearMap.mul_apply',
          LinearEquiv.coe_coe, mul_def, LinearEquiv.apply_symm_apply,
          LinearEquiv.apply_symm_apply]
    simp only [PolynomialLaw.toFun'_eq_toFun, gamma_toFun]
    rw [← homogeneousMul_baseChange_gamma, ← LinearMap.compr₂_apply,
      ← LinearMap.BilinMap.baseChange_compr₂, h, LinearMap.BilinMap.baseChange_compl₁₂,
      LinearMap.compl₁₂_apply, LinearMap.BilinMap.baseChange_mul]

/-- `γ_d(x * y) = γ_d(x) * γ_d(y)` in the Roby algebra. -/
@[simp]
theorem ground_gamma_mul (x y : A) :
    (gamma R A d).ground (x * y) = (gamma R A d).ground x * (gamma R A d).ground y :=
  isMultiplicative_gamma.ground_mul x y

/-- The unit of the Roby algebra is `γ_d(1)`. -/
@[simp]
theorem ground_gamma_one : (gamma R A d).ground 1 = 1 :=
  isMultiplicative_gamma.ground_one

variable {B : Type*} [Semiring B] [Algebra R B]

/-- The algebra map out of the Roby algebra representing a multiplicative law homogeneous of
degree `d`. -/
private def liftAlgHom (f : {f : A →ₚₗ[R] B // f.IsHomogeneousOfDegree d ∧ f.IsMultiplicative}) :
    RobyAlgebra R A d →ₐ[R] B :=
  AlgHom.ofLinearMap
    ((homogeneousLawEquiv R A B d).symm ⟨f.1, PolynomialLaw.mem_homogeneousSubmodule.mpr f.2.1⟩ ∘ₗ
      (linearEquiv R A d).toLinearMap)
    (by
      rw [LinearMap.comp_apply, LinearEquiv.coe_coe, linearEquiv_one,
        homogeneousLawEquiv_symm_apply_dp, f.2.2.ground_one])
    (fun x y ↦ by
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, mul_def,
        LinearEquiv.apply_symm_apply]
      exact homogeneousLawEquiv_symm_homogeneousMul d
        ⟨f.1, PolynomialLaw.mem_homogeneousSubmodule.mpr f.2.1⟩ f.2.2 _ _)

/-- The linear map underlying `liftAlgHom f` is the linear map representing `f`. -/
private theorem toLinearMap_liftAlgHom
    (f : {f : A →ₚₗ[R] B // f.IsHomogeneousOfDegree d ∧ f.IsMultiplicative}) :
    (liftAlgHom f).toLinearMap =
      (homogeneousLawEquiv R A B d).symm ⟨f.1, PolynomialLaw.mem_homogeneousSubmodule.mpr f.2.1⟩ ∘ₗ
        (linearEquiv R A d).toLinearMap :=
  (rfl)

/-- Composing a linear map out of the Roby algebra with the universal multiplicative law gives
the law of the corresponding linear map on `Γ^d_R(A)`. -/
private theorem toPolynomialLaw_comp_gamma (φ : RobyAlgebra R A d →ₗ[R] B) :
    φ.toPolynomialLaw.comp (gamma R A d) =
      (homogeneousLawMap R A B d (φ ∘ₗ (linearEquiv R A d).symm.toLinearMap) : A →ₚₗ[R] B) := by
  rw [coe_homogeneousLawMap_apply, LinearMap.toPolynomialLaw_comp, gamma,
    PolynomialLaw.comp_assoc]

/-- The algebra map representing a multiplicative law `f` recovers `f` by composition with the
universal multiplicative law. -/
private theorem liftAlgHom_comp_gamma
    (f : {f : A →ₚₗ[R] B // f.IsHomogeneousOfDegree d ∧ f.IsMultiplicative}) :
    (liftAlgHom f).toLinearMap.toPolynomialLaw.comp (gamma R A d) = f := by
  rw [toPolynomialLaw_comp_gamma, toLinearMap_liftAlgHom, LinearMap.comp_assoc,
    LinearEquiv.comp_symm, LinearMap.comp_id, ← homogeneousLawEquiv_apply,
    LinearEquiv.apply_symm_apply]

/-- Algebra maps out of the Roby algebra agree if their compositions with the universal
multiplicative law agree. -/
@[ext]
theorem algHom_ext {φ ψ : RobyAlgebra R A d →ₐ[R] B}
    (h : φ.toLinearMap.toPolynomialLaw.comp (gamma R A d) =
      ψ.toLinearMap.toPolynomialLaw.comp (gamma R A d)) : φ = ψ := by
  rw [toPolynomialLaw_comp_gamma, toPolynomialLaw_comp_gamma] at h
  have hrep : φ.toLinearMap ∘ₗ (linearEquiv R A d).symm.toLinearMap =
      ψ.toLinearMap ∘ₗ (linearEquiv R A d).symm.toLinearMap :=
    homogeneousLawMap_injective d (Subtype.ext h)
  refine AlgHom.toLinearMap_injective ?_
  simpa only [LinearMap.comp_assoc, LinearEquiv.symm_comp, LinearMap.comp_id] using
    congrArg (· ∘ₗ (linearEquiv R A d).toLinearMap) hrep

variable (R A d B) in
/-- **Roby algebras classify multiplicative laws**: algebra maps `Γ^d_R(A) →ₐ[R] B` are identified
with the multiplicative polynomial laws `A → B` homogeneous of degree `d`, by composition with the
universal multiplicative law `RobyAlgebra.gamma R A d`. In degree one, multiplicative laws are
also classified by `PolynomialLaw.algHomEquiv`. -/
def algHomEquiv :
    (RobyAlgebra R A d →ₐ[R] B) ≃
      {f : A →ₚₗ[R] B // f.IsHomogeneousOfDegree d ∧ f.IsMultiplicative} where
  toFun φ := ⟨φ.toLinearMap.toPolynomialLaw.comp (gamma R A d), by
    simpa using
      φ.toLinearMap.isHomogeneousOfDegree_toPolynomialLaw.comp isHomogeneousOfDegree_gamma,
    φ.isMultiplicative_toPolynomialLaw.comp isMultiplicative_gamma⟩
  invFun := liftAlgHom
  left_inv φ := algHom_ext (liftAlgHom_comp_gamma _)
  right_inv f := Subtype.ext (liftAlgHom_comp_gamma f)

/-- The law attached to an algebra map out of the Roby algebra is its composition with the
universal multiplicative law. -/
@[simp]
theorem coe_algHomEquiv_apply (φ : RobyAlgebra R A d →ₐ[R] B) :
    (algHomEquiv R A d B φ : A →ₚₗ[R] B) = φ.toLinearMap.toPolynomialLaw.comp (gamma R A d) :=
  (rfl)

/-- The algebra map classifying a multiplicative law `f` sends `γ_d(x)` to `f x`. -/
@[simp]
theorem algHomEquiv_symm_apply_ground_gamma
    (f : {f : A →ₚₗ[R] B // f.IsHomogeneousOfDegree d ∧ f.IsMultiplicative}) (x : A) :
    (algHomEquiv R A d B).symm f ((gamma R A d).ground x) = (f : A →ₚₗ[R] B).ground x := by
  have h : (algHomEquiv R A d B ((algHomEquiv R A d B).symm f) : A →ₚₗ[R] B).ground x =
      (f : A →ₚₗ[R] B).ground x := by
    rw [Equiv.apply_symm_apply]
  simpa only [coe_algHomEquiv_apply, toPolynomialLaw_comp_gamma, coe_homogeneousLawMap_apply,
    ground_toPolynomialLaw_comp_gamma_apply, LinearMap.comp_apply, AlgHom.toLinearMap_apply,
    LinearEquiv.coe_coe, ground_gamma_apply] using h

/-- The classification is natural in the target algebra: postcomposing an algebra map with
`ψ : B →ₐ[R] C` postcomposes its law with the law of `ψ`. -/
theorem algHomEquiv_comp {C : Type*} [Semiring C] [Algebra R C] (ψ : B →ₐ[R] C)
    (φ : RobyAlgebra R A d →ₐ[R] B) :
    (algHomEquiv R A d C (ψ.comp φ) : A →ₚₗ[R] C) =
      ψ.toLinearMap.toPolynomialLaw.comp (algHomEquiv R A d B φ) := by
  simp [PolynomialLaw.comp_assoc]

end RobyAlgebra

end DividedPowerAlgebra
