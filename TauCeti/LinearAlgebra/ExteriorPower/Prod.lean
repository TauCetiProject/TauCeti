/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.ExteriorAlgebra.Product
public import Mathlib.LinearAlgebra.ExteriorPower.WedgePairing
public import TauCeti.LinearAlgebra.ExteriorPower.Projection
import TauCeti.LinearAlgebra.ExteriorPower.WedgePairing

/-!
# Exterior powers of a product

For modules `M` and `N`, the wedge product `a ⊗ b ↦ a ∧ b` maps `⋀ᵖ M ⊗ ⋀^q N` to
`⋀ⁿ (M × N)` whenever `p + q = n`. These maps are the bigraded pieces of Mathlib's algebra
isomorphism `ExteriorAlgebra.prodEquivTensor` between `⋀ (M × N)` and the graded tensor product of
`⋀ M` and `⋀ N`.

## Main declarations

* `TauCeti.exteriorPower.wedgeTensor`: the wedge product `⋀ᵖ M ⊗ ⋀^q N → ⋀ⁿ (M × N)`.
* `TauCeti.exteriorPower.prodProj`: the projection `⋀ⁿ (M × N) → ⋀ᵖ M ⊗ ⋀^q N` onto the
  bidegree-`(p, q)` Künneth summand.
* `TauCeti.exteriorPower.prodEquiv`: the Künneth linear equivalence
  `⋀ⁿ (M × N) ≃ₗ[R] ∀ i : Fin (n + 1), ⋀ⁱ M ⊗ ⋀^(n - i) N`.
* `TauCeti.exteriorPower.map_prodMap_comp_wedgeTensor` and
  `TauCeti.exteriorPower.prodProj_comp_map_prodMap`: naturality of the Künneth inclusions and
  projections with respect to `LinearMap.prodMap`.

## References

* N. Bourbaki, *Algebra I*, Chapter III, §7.7, Proposition 10.
* The decomposition is extracted degreewise from Mathlib's `ExteriorAlgebra.prodEquivTensor`
  (`Mathlib.LinearAlgebra.ExteriorAlgebra.Product`, by Nailin Guan).
-/

public section

noncomputable section

open scoped TensorProduct

namespace TauCeti

namespace exteriorPower

variable {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

variable (R M N) in
/-- The wedge product `⋀ᵖ M ⊗ ⋀^q N → ⋀ⁿ (M × N)`, `a ⊗ b ↦ a ∧ b`, for `p + q = n`. -/
def wedgeTensor (p q n : ℕ) (h : p + q = n) :
    ⋀[R]^p M ⊗[R] ⋀[R]^q N →ₗ[R] ⋀[R]^n (M × N) :=
  (LinearEquiv.ofEq _ _ (by rw [h])).toLinearMap ∘ₗ
    TensorProduct.lift ((_root_.exteriorPower.wedge R (M × N) p q).compl₁₂
      (_root_.exteriorPower.map p (LinearMap.inl R M N))
      (_root_.exteriorPower.map q (LinearMap.inr R M N)))

/-- `wedgeTensor` sends `a ⊗ b` to the product of the images of `a` and `b` in `⋀ (M × N)`. -/
@[simp]
theorem coe_wedgeTensor_tmul (p q n : ℕ) (h : p + q = n) (a : ⋀[R]^p M) (b : ⋀[R]^q N) :
    (wedgeTensor R M N p q n h (a ⊗ₜ b) : ExteriorAlgebra R (M × N)) =
      ExteriorAlgebra.map (LinearMap.inl R M N) a *
        ExteriorAlgebra.map (LinearMap.inr R M N) b := by
  simp [wedgeTensor]

/-- On pure exterior products, `wedgeTensor` concatenates the left and right vector families. -/
@[simp]
theorem wedgeTensor_tmul_ιMulti (p q : ℕ) (u : Fin p → M) (v : Fin q → N) :
    wedgeTensor R M N p q (p + q) rfl
      (_root_.exteriorPower.ιMulti R p u ⊗ₜ _root_.exteriorPower.ιMulti R q v) =
    _root_.exteriorPower.ιMulti R (p + q)
      (Fin.append (LinearMap.inl R M N ∘ u) (LinearMap.inr R M N ∘ v)) := by
  apply Subtype.ext
  simp [coe_wedgeTensor_tmul, ExteriorAlgebra.ιMulti_mul_ιMulti]

/-- `wedgeTensor` intertwines the tensor product of exterior-power maps with the exterior power
of the product map. -/
theorem map_prodMap_comp_wedgeTensor {M' N' : Type*} [AddCommGroup M'] [Module R M']
    [AddCommGroup N'] [Module R N'] (f : M →ₗ[R] M') (g : N →ₗ[R] N')
    (p q n : ℕ) (h : p + q = n) :
    _root_.exteriorPower.map n (f.prodMap g) ∘ₗ wedgeTensor R M N p q n h =
      wedgeTensor R M' N' p q n h ∘ₗ
        TensorProduct.map (_root_.exteriorPower.map p f) (_root_.exteriorPower.map q g) := by
  have hinl : (f.prodMap g) ∘ₗ LinearMap.inl R M N = LinearMap.inl R M' N' ∘ₗ f :=
    LinearMap.ext fun _ ↦ by simp
  have hinr : (f.prodMap g) ∘ₗ LinearMap.inr R M N = LinearMap.inr R M' N' ∘ₗ g :=
    LinearMap.ext fun _ ↦ by simp
  refine TensorProduct.ext' fun a b ↦ Subtype.ext ?_
  simp only [LinearMap.comp_apply, TensorProduct.map_tmul, _root_.exteriorPower.coe_map,
    coe_wedgeTensor_tmul, map_mul, ← AlgHom.comp_apply, ExteriorAlgebra.map_comp_map, hinl, hinr]

/-- Pointwise form of `map_prodMap_comp_wedgeTensor`. -/
theorem map_prodMap_wedgeTensor_apply {M' N' : Type*} [AddCommGroup M'] [Module R M']
    [AddCommGroup N'] [Module R N'] (f : M →ₗ[R] M') (g : N →ₗ[R] N')
    (p q n : ℕ) (h : p + q = n) (z : ⋀[R]^p M ⊗[R] ⋀[R]^q N) :
    _root_.exteriorPower.map n (f.prodMap g) (wedgeTensor R M N p q n h z) =
      wedgeTensor R M' N' p q n h
        (TensorProduct.map (_root_.exteriorPower.map p f) (_root_.exteriorPower.map q g) z) :=
  DFunLike.congr_fun (map_prodMap_comp_wedgeTensor f g p q n h) z

/-- In degree `n`, the wedge products of the bidegree-`(i, n - i)` components of an element of
`⋀ M ⊗ ⋀ N` add up to the degree-`n` component of its image in `⋀ (M × N)` under
`ExteriorAlgebra.prodEquivTensor`. -/
theorem sum_coe_wedgeTensor_map_proj (n : ℕ) (y : ExteriorAlgebra R M ⊗[R] ExteriorAlgebra R N) :
    ∑ i : Fin (n + 1), (wedgeTensor R M N i (n - i) n (by omega)
        (TensorProduct.map (proj R M i) (proj R N (n - i)) y) : ExteriorAlgebra R (M × N)) =
      proj R (M × N) n
        ((ExteriorAlgebra.prodEquivTensor R M N).symm (GradedTensorProduct.of R _ _ y)) := by
  induction y using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, Submodule.coe_add, Finset.sum_add_distrib, hx, hy]
  | tmul a b =>
    induction a using DirectSum.Decomposition.inductionOn (fun i ↦ ⋀[R]^i M) with
    | zero => simp
    | add a a' ha ha' =>
      simp only [TensorProduct.add_tmul, map_add, Submodule.coe_add, Finset.sum_add_distrib, ha,
        ha']
    | @homogeneous p a =>
      induction b using DirectSum.Decomposition.inductionOn (fun i ↦ ⋀[R]^i N) with
      | zero => simp
      | add b b' hb hb' =>
        simp only [TensorProduct.tmul_add, map_add, Submodule.coe_add, Finset.sum_add_distrib, hb,
          hb']
      | @homogeneous q b =>
        have hab : ExteriorAlgebra.map (LinearMap.inl R M N) (a : ExteriorAlgebra R M) *
            ExteriorAlgebra.map (LinearMap.inr R M N) (b : ExteriorAlgebra R N) ∈
              ⋀[R]^(p + q) (M × N) := by
          rw [← _root_.exteriorPower.coe_map, ← _root_.exteriorPower.coe_map]
          exact SetLike.mul_mem_graded (Submodule.coe_mem _) (Submodule.coe_mem _)
        simp only [TensorProduct.map_tmul, coe_wedgeTensor_tmul, coe_proj_of_mem a.2,
          coe_proj_of_mem b.2]
        rw [← GradedTensorProduct.tmul, ExteriorAlgebra.prodEquivTensor_symm_tmul,
          coe_proj_of_mem hab]
        by_cases hpq : p + q = n
        · rw [ite_eq_left hpq, Finset.sum_eq_single ⟨p, by omega⟩]
          · simp [show q = n - p by omega]
          · rintro i - hi
            have : p ≠ i := fun h ↦ hi (Fin.ext h.symm)
            simp [this]
          · simp
        · rw [ite_eq_right hpq]
          refine Finset.sum_eq_zero fun i _ ↦ ?_
          by_cases hi : p = i
          · have : q ≠ n - i := by omega
            simp [this]
          · simp [hi]

variable (R M N) in
/-- The projection `⋀ⁿ (M × N) → ⋀ᵖ M ⊗ ⋀^q N` onto the bidegree-`(p, q)` Künneth summand,
extracted from `ExteriorAlgebra.prodEquivTensor` via `exteriorPower.proj`. -/
def prodProj (p q n : ℕ) : ⋀[R]^n (M × N) →ₗ[R] ⋀[R]^p M ⊗[R] ⋀[R]^q N :=
  TensorProduct.map (proj R M p) (proj R N q) ∘ₗ
    (GradedTensorProduct.of R (fun i ↦ ⋀[R]^i M) (fun i ↦ ⋀[R]^i N)).symm.toLinearMap ∘ₗ
    (ExteriorAlgebra.prodEquivTensor R M N).toLinearMap ∘ₗ
    (⋀[R]^n (M × N)).subtype

/-- On the wedge product of `a` and `b`, `prodProj` projects `a` and `b` onto degrees `p'` and
`q'`. -/
@[simp]
theorem prodProj_wedgeTensor_tmul (p' q' p q n : ℕ) (h : p + q = n)
    (a : ⋀[R]^p M) (b : ⋀[R]^q N) :
    prodProj R M N p' q' n (wedgeTensor R M N p q n h (a ⊗ₜ b)) =
      proj R M p' a ⊗ₜ proj R N q' b := by
  simp only [prodProj, LinearMap.comp_apply, Submodule.coe_subtype, coe_wedgeTensor_tmul,
    ← ExteriorAlgebra.prodEquivTensor_symm_tmul, AlgEquiv.toLinearMap_apply,
    AlgEquiv.apply_symm_apply, LinearEquiv.coe_toLinearMap, GradedTensorProduct.tmul,
    GradedTensorProduct.of_symm_of, TensorProduct.map_tmul]

/-- `prodProj` is left inverse to `wedgeTensor` in matching bidegree. -/
@[simp]
theorem prodProj_comp_wedgeTensor_self (p q n : ℕ) (h : p + q = n) :
    prodProj R M N p q n ∘ₗ wedgeTensor R M N p q n h = LinearMap.id :=
  TensorProduct.ext' fun a b ↦ by simp

/-- Pointwise form of `prodProj_comp_wedgeTensor_self`. -/
@[simp]
theorem prodProj_wedgeTensor_self (p q n : ℕ) (h : p + q = n)
    (z : ⋀[R]^p M ⊗[R] ⋀[R]^q N) :
    prodProj R M N p q n (wedgeTensor R M N p q n h z) = z :=
  DFunLike.congr_fun (prodProj_comp_wedgeTensor_self p q n h) z

/-- `prodProj` vanishes on the image of `wedgeTensor` in any differing bidegree. -/
theorem prodProj_comp_wedgeTensor_of_ne {p' q' p q n : ℕ} (h : p + q = n)
    (hne : p ≠ p' ∨ q ≠ q') :
    prodProj R M N p' q' n ∘ₗ wedgeTensor R M N p q n h = 0 := by
  refine TensorProduct.ext' fun a b ↦ ?_
  simp only [LinearMap.comp_apply, prodProj_wedgeTensor_tmul, LinearMap.zero_apply]
  rcases hne with hp | hq
  · have ha : proj R M p' a = 0 := Subtype.ext (by simp [coe_proj_of_mem a.2, hp])
    simp [ha]
  · have hb : proj R N q' b = 0 := Subtype.ext (by simp [coe_proj_of_mem b.2, hq])
    simp [hb]

/-- Pointwise form of `prodProj_comp_wedgeTensor_of_ne`. -/
theorem prodProj_wedgeTensor_of_ne {p' q' p q n : ℕ} (h : p + q = n)
    (hne : p ≠ p' ∨ q ≠ q') (z : ⋀[R]^p M ⊗[R] ⋀[R]^q N) :
    prodProj R M N p' q' n (wedgeTensor R M N p q n h z) = 0 :=
  DFunLike.congr_fun (prodProj_comp_wedgeTensor_of_ne h hne) z

/-- Every element of `⋀ⁿ (M × N)` is the sum of the wedge products of its bidegree-`(i, n - i)`
Künneth projections. -/
@[simp]
theorem sum_wedgeTensor_prodProj (n : ℕ) (x : ⋀[R]^n (M × N)) :
    ∑ i : Fin (n + 1),
      wedgeTensor R M N i (n - i) n (by omega) (prodProj R M N i (n - i) n x) = x := by
  apply Subtype.ext
  rw [Submodule.coe_sum]
  have h := sum_coe_wedgeTensor_map_proj n
    ((GradedTensorProduct.of R (fun i ↦ ⋀[R]^i M) (fun i ↦ ⋀[R]^i N)).symm
      (ExteriorAlgebra.prodEquivTensor R M N x))
  simp only [GradedTensorProduct.symm_of_of, AlgEquiv.symm_apply_apply, proj_coe] at h
  exact h

/-- Operator form of `sum_wedgeTensor_prodProj`: the composites `wedgeTensor ∘ₗ prodProj` over
`i : Fin (n + 1)` resolve the identity of `⋀ⁿ (M × N)`. -/
theorem sum_wedgeTensor_comp_prodProj (n : ℕ) :
    ∑ i : Fin (n + 1),
      wedgeTensor R M N i (n - i) n (by omega) ∘ₗ prodProj R M N i (n - i) n = LinearMap.id :=
  LinearMap.ext fun x ↦ by
    simp only [LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.id_apply]
    exact sum_wedgeTensor_prodProj n x

/-- `prodProj` vanishes outside total degree `n`. -/
theorem prodProj_eq_zero_of_add_ne {p q n : ℕ} (h : p + q ≠ n) :
    prodProj R M N p q n = 0 := by
  refine LinearMap.ext fun x ↦ ?_
  rw [← sum_wedgeTensor_prodProj n x, map_sum, LinearMap.zero_apply]
  exact Finset.sum_eq_zero fun i _ ↦ prodProj_wedgeTensor_of_ne (by omega) (by omega) _

/-- `prodProj` intertwines the exterior power of a product map with the tensor product of the
exterior-power maps. -/
theorem prodProj_comp_map_prodMap {M' N' : Type*} [AddCommGroup M'] [Module R M']
    [AddCommGroup N'] [Module R N'] (f : M →ₗ[R] M') (g : N →ₗ[R] N') (p q n : ℕ) :
    prodProj R M' N' p q n ∘ₗ _root_.exteriorPower.map n (f.prodMap g) =
      TensorProduct.map (_root_.exteriorPower.map p f) (_root_.exteriorPower.map q g) ∘ₗ
        prodProj R M N p q n := by
  by_cases hpq : p + q = n
  · refine LinearMap.ext fun x ↦ ?_
    simp only [LinearMap.comp_apply]
    conv_lhs => rw [← sum_wedgeTensor_prodProj n x]
    rw [map_sum, map_sum, Finset.sum_eq_single ⟨p, by omega⟩]
    · rcases (by omega : n - p = q) with rfl
      rw [map_prodMap_wedgeTensor_apply, prodProj_wedgeTensor_self]
    · rintro i - hi
      have hne : (i : ℕ) ≠ p := fun h ↦ hi (Fin.ext h)
      rw [map_prodMap_wedgeTensor_apply, prodProj_wedgeTensor_of_ne (by omega) (.inl hne)]
    · simp
  · simp [prodProj_eq_zero_of_add_ne hpq]

/-- Pointwise form of `prodProj_comp_map_prodMap`. -/
@[simp]
theorem prodProj_map_prodMap {M' N' : Type*} [AddCommGroup M'] [Module R M']
    [AddCommGroup N'] [Module R N'] (f : M →ₗ[R] M') (g : N →ₗ[R] N') (p q n : ℕ)
    (x : ⋀[R]^n (M × N)) :
    prodProj R M' N' p q n (_root_.exteriorPower.map n (f.prodMap g) x) =
      TensorProduct.map (_root_.exteriorPower.map p f) (_root_.exteriorPower.map q g)
        (prodProj R M N p q n x) :=
  DFunLike.congr_fun (prodProj_comp_map_prodMap f g p q n) x

private theorem prodProj_pi_comp_sum_wedgeTensor (n : ℕ) :
    (LinearMap.pi fun i : Fin (n + 1) ↦ prodProj R M N i (n - i) n) ∘ₗ
      (∑ i : Fin (n + 1),
        wedgeTensor R M N i (n - i) n (by omega) ∘ₗ
          LinearMap.proj (R := R) (φ := fun j : Fin (n + 1) ↦ ⋀[R]^j M ⊗[R] ⋀[R]^(n - j) N) i) =
    LinearMap.id :=
  LinearMap.ext fun z ↦ funext fun i ↦ by
    simp only [LinearMap.comp_apply, LinearMap.pi_apply, LinearMap.sum_apply, map_sum,
      LinearMap.id_apply]
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hji
      have hne : (j : ℕ) ≠ i := fun h ↦ hji (Fin.ext h)
      exact prodProj_wedgeTensor_of_ne (by omega) (.inl hne) (z j)
    · simp

private theorem sum_wedgeTensor_comp_prodProj_pi (n : ℕ) :
    (∑ i : Fin (n + 1),
      wedgeTensor R M N i (n - i) n (by omega) ∘ₗ
        LinearMap.proj (R := R) (φ := fun j : Fin (n + 1) ↦ ⋀[R]^j M ⊗[R] ⋀[R]^(n - j) N) i) ∘ₗ
      (LinearMap.pi fun i : Fin (n + 1) ↦ prodProj R M N i (n - i) n) =
    LinearMap.id :=
  LinearMap.ext fun x ↦ by
    simp only [LinearMap.comp_apply, LinearMap.sum_apply, LinearMap.pi_apply,
      LinearMap.proj_apply, LinearMap.id_apply]
    exact sum_wedgeTensor_prodProj n x

variable (R M N) in
/-- **Künneth decomposition of an exterior power of a product**: `⋀ⁿ (M × N)` is linearly
equivalent to the finite product `∀ i : Fin (n + 1), ⋀ⁱ M ⊗ ⋀^(n - i) N` of bigraded tensor
products, with forward components `prodProj` and inverse the sum of `wedgeTensor`. -/
def prodEquiv (n : ℕ) :
    ⋀[R]^n (M × N) ≃ₗ[R] ∀ i : Fin (n + 1), ⋀[R]^i M ⊗[R] ⋀[R]^(n - i) N :=
  LinearEquiv.ofLinearMap
    (LinearMap.pi fun i ↦ prodProj R M N i (n - i) n)
    (∑ i : Fin (n + 1),
      wedgeTensor R M N i (n - i) n (by omega) ∘ₗ
        LinearMap.proj (R := R) (φ := fun j : Fin (n + 1) ↦ ⋀[R]^j M ⊗[R] ⋀[R]^(n - j) N) i)
    (prodProj_pi_comp_sum_wedgeTensor n)
    (sum_wedgeTensor_comp_prodProj_pi n)

@[simp]
theorem prodEquiv_apply (n : ℕ) (x : ⋀[R]^n (M × N)) (i : Fin (n + 1)) :
    prodEquiv R M N n x i = prodProj R M N i (n - i) n x :=
  (rfl)

@[simp]
theorem prodEquiv_symm_apply (n : ℕ)
    (z : ∀ i : Fin (n + 1), ⋀[R]^i M ⊗[R] ⋀[R]^(n - i) N) :
    (prodEquiv R M N n).symm z =
      ∑ i : Fin (n + 1), wedgeTensor R M N i (n - i) n (by omega) (z i) := by
  simp [prodEquiv]

/-- On a single bidegree component, `(prodEquiv R M N n).symm` applies `wedgeTensor`. -/
theorem prodEquiv_symm_single (n : ℕ) (i : Fin (n + 1))
    (z : ⋀[R]^i M ⊗[R] ⋀[R]^(n - i) N) :
    (prodEquiv R M N n).symm (Pi.single i z) =
      wedgeTensor R M N i (n - i) n (by omega) z := by
  rw [prodEquiv_symm_apply, Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    simp [Pi.single_eq_of_ne hji]
  · simp

/-- `prodEquiv` intertwines `exteriorPower.map n (f.prodMap g)` componentwise with
`TensorProduct.map` of exterior-power maps. -/
theorem prodEquiv_map_prodMap {M' N' : Type*} [AddCommGroup M'] [Module R M']
    [AddCommGroup N'] [Module R N'] (f : M →ₗ[R] M') (g : N →ₗ[R] N') (n : ℕ)
    (x : ⋀[R]^n (M × N)) (i : Fin (n + 1)) :
    prodEquiv R M' N' n (_root_.exteriorPower.map n (f.prodMap g) x) i =
      TensorProduct.map (_root_.exteriorPower.map i f) (_root_.exteriorPower.map (n - i) g)
        (prodEquiv R M N n x i) :=
  prodProj_map_prodMap f g i (n - i) n x

end exteriorPower

end TauCeti
