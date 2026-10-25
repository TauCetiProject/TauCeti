/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.DividedPowerAlgebra.Representability
public import TauCeti.RingTheory.PolynomialLaw.Bilinear

/-!
# The tensor map of homogeneous divided powers

For modules `M` and `N` over a commutative semiring `R` and `d : ℕ`, this file constructs Roby's
natural `R`-linear map
`Γ^d_R(M) ⊗[R] Γ^d_R(N) → Γ^d_R(M ⊗[R] N)`,
sending `dp R d m ⊗ dp R d n` to `dp R d (m ⊗ n)`. It is characterized by the polynomial law
`(m, n) ↦ γ_d(m ⊗ n)` on `M × N`, which is separately homogeneous of degree `d` in `m` and in `n`.
On products of divided powers it is given by the mixed coefficient formula: the image of
`(∏ᵢ dp R aᵢ mᵢ) ⊗ (∏ⱼ dp R bⱼ nⱼ)` is the coefficient of `∏ᵢ Xᵢ ^ aᵢ ∏ⱼ Yⱼ ^ bⱼ` in
`γ_d(∑ᵢ ∑ⱼ XᵢYⱼ ⊗ (mᵢ ⊗ nⱼ))`, computed over the polynomial ring `R[Xᵢ, Yⱼ]`. No factorial is
inverted, so the map is defined integrally: over `ℤ`, `dp 2 1 ⊗ dp 2 1` goes to `dp 2 (1 ⊗ 1)`,
with no factor `2` or `1/2`. No assertion that the map is an isomorphism is made.

Followed by `Γ^d` of the multiplication `A ⊗[R] A → A` of an `R`-algebra `A`, the tensor map gives
the internal multiplication of the Roby algebra `Γ^d_R(A)`, whose algebra maps classify the
multiplicative homogeneous polynomial laws on `A`.

## Main declarations

* `DividedPowerAlgebra.homogeneousTensorMap R M N d`: the linear map
  `Γ^d_R(M) ⊗[R] Γ^d_R(N) → Γ^d_R(M ⊗[R] N)`.
* `DividedPowerAlgebra.homogeneousTensorMap_tmul_prod_dp`: the mixed coefficient formula.
* `DividedPowerAlgebra.homogeneousTensorMap_dp_tmul_dp`: `dp R d m ⊗ dp R d n ↦ dp R d (m ⊗ n)`.
* `DividedPowerAlgebra.homogeneousTensorMap_comp_map`: naturality, i.e. the map commutes with
  `Γ^d(f) ⊗ Γ^d(g)` and `Γ^d(f ⊗ g)`.

## Implementation notes

The product `x ⊗ y ↦ Γ(inl)(x) Γ(inr)(y)` maps `Γ^d_R(M) ⊗[R] Γ^d_R(N)` to `Γ^{2d}_R(M × N)`.
The law `(m, n) ↦ γ_d(m ⊗ n)` is homogeneous of degree `2d` on `M × N`, so by Roby
representability (`DividedPowerAlgebra.homogeneousLawEquiv`) it is represented by a linear map
`Γ^{2d}_R(M × N) → Γ^d_R(M ⊗[R] N)`. The tensor map is the composite. Its values on products of
divided powers are coefficients of the law, and naturality follows from the naturality of
representability, since a representing linear map is unique.

## References

* [N. Roby, *Lois polynômes et lois formelles en théorie des modules* (1963),
  IV §11, Proposition IV.9][Roby-1963]
* [G. Chenevier, *The p-adic analytic space of pseudocharacters of a profinite group and
  pseudorepresentations over arbitrary rings*, §1.1](https://arxiv.org/abs/0809.0415)
* The ambient `DividedPowerAlgebra` and the `PolynomialLaw`s are the Mathlib formalizations by
  Antoine Chambert-Loir and María Inés de Frutos-Fernández.
-/

public section

noncomputable section

universe u

open TensorProduct

namespace DividedPowerAlgebra

variable {R : Type u} [CommSemiring R]
variable {M N M' N' : Type*} [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]
  [AddCommMonoid M'] [Module R M'] [AddCommMonoid N'] [Module R N']

variable (R M N) in
/-- The product `x ⊗ y ↦ Γ(inl)(x) Γ(inr)(y)`, from `Γ^d_R(M) ⊗[R] Γ^e_R(N)` to
`Γ^{d + e}_R(M × N)`. -/
private def prodMul (d e : ℕ) :
    homogeneousSubmodule (R := R) (M := M) d ⊗[R] homogeneousSubmodule (R := R) (M := N) e →ₗ[R]
      homogeneousSubmodule (R := R) (M := M × N) (d + e) :=
  TensorProduct.lift <| LinearMap.mk₂ R
    (fun x y ↦ ⟨map R (LinearMap.inl R M N) x * map R (LinearMap.inr R M N) y,
      mul_mem_homogeneousSubmodule (map_mem_homogeneousSubmodule _ x.2)
        (map_mem_homogeneousSubmodule _ y.2)⟩)
    (fun _ _ _ ↦ Subtype.ext <| by simp [add_mul])
    (fun _ _ _ ↦ Subtype.ext <| by simp)
    (fun _ _ _ ↦ Subtype.ext <| by simp [mul_add])
    (fun _ _ _ ↦ Subtype.ext <| by simp)

private theorem coe_prodMul_tmul (d e : ℕ) (x : homogeneousSubmodule (R := R) (M := M) d)
    (y : homogeneousSubmodule (R := R) (M := N) e) :
    (prodMul R M N d e (x ⊗ₜ y) : DividedPowerAlgebra R (M × N)) =
      map R (LinearMap.inl R M N) x * map R (LinearMap.inr R M N) y := by
  simp [prodMul]

/-- The product map is natural in both modules. -/
private theorem prodMul_comp_map (d e : ℕ) (f : M →ₗ[R] M') (g : N →ₗ[R] N') :
    prodMul R M' N' d e ∘ₗ
        TensorProduct.map (mapHomogeneousSubmodule f d) (mapHomogeneousSubmodule g e) =
      mapHomogeneousSubmodule (f.prodMap g) (d + e) ∘ₗ prodMul R M N d e := by
  have hinl : f.prodMap g ∘ₗ LinearMap.inl R M N = LinearMap.inl R M' N' ∘ₗ f := by
    ext <;> simp
  have hinr : f.prodMap g ∘ₗ LinearMap.inr R M N = LinearMap.inr R M' N' ∘ₗ g := by
    ext <;> simp
  refine TensorProduct.ext' fun x y ↦ Subtype.ext ?_
  simp only [LinearMap.comp_apply, TensorProduct.map_tmul, coe_prodMul_tmul,
    coe_mapHomogeneousSubmodule_apply, map_mul, ← AlgHom.comp_apply, ← map_comp, hinl, hinr]

variable (R M N) in
/-- The law `(m, n) ↦ γ_d(m ⊗ n)` on `M × N`, homogeneous of degree `d + d`. -/
private def tensorLaw (d : ℕ) :
    PolynomialLaw.homogeneousSubmodule R (M × N)
      (homogeneousSubmodule (R := R) (M := M ⊗[R] N) d) (d + d) :=
  ⟨(gamma R (M ⊗[R] N) d).comp (TensorProduct.mk R M N).toPolynomialLaw₂, by
    simpa [two_mul] using (isHomogeneousOfDegree_gamma (R := R) (M := M ⊗[R] N) d).comp
      (TensorProduct.mk R M N).isHomogeneousOfDegree_toPolynomialLaw₂⟩

/-- The law `(m, n) ↦ γ_d(m ⊗ n)` is natural in both modules. -/
private theorem tensorLaw_comp (d : ℕ) (f : M →ₗ[R] M') (g : N →ₗ[R] N') :
    (tensorLaw R M' N' d : M' × N' →ₚₗ[R] _).comp (f.prodMap g).toPolynomialLaw =
      (mapHomogeneousSubmodule (TensorProduct.map f g) d).toPolynomialLaw.comp
        (tensorLaw R M N d) := by
  have hmk : (TensorProduct.mk R M' N').compl₁₂ f g =
      (TensorProduct.mk R M N).compr₂ (TensorProduct.map f g) := by
    ext m n
    simp
  rw [tensorLaw, tensorLaw, Subtype.coe_mk, Subtype.coe_mk, ← PolynomialLaw.comp_assoc,
    ← LinearMap.toPolynomialLaw₂_compl₁₂, hmk, LinearMap.toPolynomialLaw₂_compr₂,
    PolynomialLaw.comp_assoc, gamma_comp_toPolynomialLaw, PolynomialLaw.comp_assoc]

variable (R M N) in
/-- Roby's tensor map `Γ^d_R(M) ⊗[R] Γ^d_R(N) → Γ^d_R(M ⊗[R] N)` of homogeneous divided powers,
sending `dp R d m ⊗ dp R d n` to `dp R d (m ⊗ n)` (`homogeneousTensorMap_dp_tmul_dp`). It is
characterized by the polynomial law `(m, n) ↦ γ_d(m ⊗ n)` on `M × N`, through the mixed
coefficient formula `homogeneousTensorMap_tmul_prod_dp`. -/
def homogeneousTensorMap (d : ℕ) :
    homogeneousSubmodule (R := R) (M := M) d ⊗[R] homogeneousSubmodule (R := R) (M := N) d →ₗ[R]
      homogeneousSubmodule (R := R) (M := M ⊗[R] N) d :=
  (homogeneousLawEquiv R (M × N) _ (d + d)).symm (tensorLaw R M N d) ∘ₗ prodMul R M N d d

open MvPolynomial in
/-- The mixed coefficient formula for the tensor map: for families `m : ι → M`, `n : κ → N` and
exponents `a`, `b` of total degree `d`, the image of `(∏ᵢ dp R aᵢ mᵢ) ⊗ (∏ⱼ dp R bⱼ nⱼ)` is the
coefficient of `∏ᵢ Xᵢ ^ aᵢ ∏ⱼ Yⱼ ^ bⱼ` in `γ_d(∑ᵢ ∑ⱼ XᵢYⱼ ⊗ (mᵢ ⊗ nⱼ))`, computed over the
polynomial ring in the variables `Xᵢ = X (inl i)` and `Yⱼ = X (inr j)`. -/
theorem homogeneousTensorMap_tmul_prod_dp (d : ℕ) {ι κ : Type*} [Fintype ι] [Fintype κ]
    (m : ι → M) (n : κ → N) (a : ι →₀ ℕ) (b : κ →₀ ℕ) (ha : ∑ i, a i = d)
    (hb : ∑ j, b j = d) :
    homogeneousTensorMap R M N d
        (⟨∏ i, dp R (a i) (m i), prod_dp_mem_homogeneousSubmodule_of_sum_eq m a ha⟩ ⊗ₜ
          ⟨∏ j, dp R (b j) (n j), prod_dp_mem_homogeneousSubmodule_of_sum_eq n b hb⟩) =
      TensorProduct.lid R _ ((lcoeff R (Finsupp.sumElim a b)).rTensor _
        ((gamma R (M ⊗[R] N) d).toFun (MvPolynomial (ι ⊕ κ) R)
          (∑ i, ∑ j, (X (Sum.inl i) * X (Sum.inr j)) ⊗ₜ[R] (m i ⊗ₜ[R] n j)))) := by
  let v : ι ⊕ κ → M × N := Sum.elim (fun i ↦ (m i, 0)) (fun j ↦ (0, n j))
  have hk : ∑ j, Finsupp.sumElim a b j = d + d := by
    simp [Fintype.sum_sum_type, ha, hb]
  have hprod : prodMul R M N d d
      (⟨∏ i, dp R (a i) (m i), prod_dp_mem_homogeneousSubmodule_of_sum_eq m a ha⟩ ⊗ₜ
        ⟨∏ j, dp R (b j) (n j), prod_dp_mem_homogeneousSubmodule_of_sum_eq n b hb⟩) =
      ⟨∏ j, dp R (Finsupp.sumElim a b j) (v j),
        prod_dp_mem_homogeneousSubmodule_of_sum_eq v _ hk⟩ := by
    apply Subtype.ext
    simp [coe_prodMul_tmul, Fintype.prod_sum_type, v, map_prod]
  rw [homogeneousTensorMap, LinearMap.comp_apply, hprod,
    homogeneousLawEquiv_symm_apply_prod_dp (d + d) _ v _ hk,
    PolynomialLaw.coeff_apply, tensorLaw, PolynomialLaw.toFun_comp_apply, Fintype.sum_sum_type]
  simp only [v, Sum.elim_inl, Sum.elim_inr, LinearMap.toPolynomialLaw₂_toFun_sum_add_sum,
    TensorProduct.mk_apply]

/-- The tensor map sends `dp R d m ⊗ dp R d n` to `dp R d (m ⊗ n)`. -/
@[simp]
theorem homogeneousTensorMap_dp_tmul_dp (d : ℕ) (m : M) (n : N) :
    homogeneousTensorMap R M N d
        (⟨dp R d m, dp_mem_homogeneousSubmodule d m⟩ ⊗ₜ
          ⟨dp R d n, dp_mem_homogeneousSubmodule d n⟩) =
      ⟨dp R d (m ⊗ₜ n), dp_mem_homogeneousSubmodule d (m ⊗ₜ n)⟩ := by
  classical
  have h := homogeneousTensorMap_tmul_prod_dp (R := R) d (fun _ : Unit ↦ m) (fun _ : Unit ↦ n)
    (Finsupp.single () d) (Finsupp.single () d) (by simp) (by simp)
  have hmon : (MvPolynomial.X (Sum.inl ()) * MvPolynomial.X (Sum.inr ()) :
      MvPolynomial (Unit ⊕ Unit) R) ^ d =
        MvPolynomial.monomial (Finsupp.sumElim (Finsupp.single () d) (Finsupp.single () d)) 1 := by
    rw [mul_pow, MvPolynomial.X_pow_eq_monomial, MvPolynomial.X_pow_eq_monomial,
      MvPolynomial.monomial_mul_monomial, one_mul]
    congr 1
    ext j
    cases j
    all_goals simp
  simp only [Finset.univ_unique, Finset.prod_singleton, Finsupp.single_eq_same,
    Finset.sum_singleton, gamma_toFun_tmul, hmon, LinearMap.rTensor_tmul,
    MvPolynomial.lcoeff_apply, MvPolynomial.coeff_monomial, ite_true,
    TensorProduct.lid_tmul, one_smul] at h
  exact h

/-- The tensor map is natural: it intertwines `Γ^d(f) ⊗ Γ^d(g)` with `Γ^d(f ⊗ g)`. -/
theorem homogeneousTensorMap_comp_map (d : ℕ) (f : M →ₗ[R] M') (g : N →ₗ[R] N') :
    homogeneousTensorMap R M' N' d ∘ₗ
        TensorProduct.map (mapHomogeneousSubmodule f d) (mapHomogeneousSubmodule g d) =
      mapHomogeneousSubmodule (TensorProduct.map f g) d ∘ₗ homogeneousTensorMap R M N d := by
  -- Both representing maps on `Γ^{2d}(M × N)` come from the same law, by `tensorLaw_comp`.
  have hrep :
      (homogeneousLawEquiv R (M' × N') _ (d + d)).symm (tensorLaw R M' N' d) ∘ₗ
          mapHomogeneousSubmodule (f.prodMap g) (d + d) =
        mapHomogeneousSubmodule (TensorProduct.map f g) d ∘ₗ
          (homogeneousLawEquiv R (M × N) _ (d + d)).symm (tensorLaw R M N d) := by
    refine homogeneousLawMap_injective (d + d) (Subtype.ext ?_)
    rw [homogeneousLawMap_comp_mapHomogeneousSubmodule, homogeneousLawMap_comp,
      ← homogeneousLawEquiv_apply, ← homogeneousLawEquiv_apply, LinearEquiv.apply_symm_apply,
      LinearEquiv.apply_symm_apply, tensorLaw_comp]
  rw [homogeneousTensorMap, homogeneousTensorMap, LinearMap.comp_assoc, prodMul_comp_map,
    ← LinearMap.comp_assoc, hrep, LinearMap.comp_assoc]

end DividedPowerAlgebra
