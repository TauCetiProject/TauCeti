/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.ExteriorAlgebra.Product
public import Mathlib.LinearAlgebra.ExteriorPower.WedgePairing
public import TauCeti.LinearAlgebra.ExteriorPower.Basic
public import TauCeti.LinearAlgebra.ExteriorPower.Projection
import TauCeti.LinearAlgebra.ExteriorPower.WedgePairing

/-!
# Exterior powers of a product

For modules `M` and `N`, the wedge product `a ⊗ b ↦ a ∧ b` maps `⋀ᵖ M ⊗ ⋀^q N` to
`⋀ⁿ (M × N)` whenever `p + q = n`. These maps are the bigraded pieces of Mathlib's algebra
isomorphism `ExteriorAlgebra.prodEquivTensor` between `⋀ (M × N)` and the graded tensor product of
`⋀ M` and `⋀ N`. Restricting that isomorphism to degree `n` gives the exterior sum comparison
`⋀ⁿ (M × N) ≃ ⨁ᵢ ⋀ⁱ M ⊗ ⋀ⁿ⁻ⁱ N` for arbitrary modules over a commutative ring, the module form of
the sum formula `λⁿ(x + y) = ∑ᵢ λⁱ(x) λⁿ⁻ⁱ(y)` for exterior powers. Its inverse is ordered: it
wedges the factor from `M` before the factor from `N`.

## Main declarations

* `TauCeti.exteriorPower.wedgeTensor`: the wedge product `⋀ᵖ M ⊗ ⋀^q N → ⋀ⁿ (M × N)`.
* `TauCeti.exteriorPower.sum_coe_wedgeTensor_map_proj`: the degree-`n` component of an element
  of `⋀ (M × N)` is the sum of the wedge products of its bidegree-`(i, n - i)` components.
* `TauCeti.exteriorPower.map_fst_comp_map_inl`, `TauCeti.exteriorPower.map_fst_comp_wedgeLeft`
  and `TauCeti.exteriorPower.map_inl_comp_map_fst_zero`: the `⋀ M`-component `⋀ fst` of
  `⋀ (M × N)` is a retraction of `⋀ inl`, kills `(0, x) ∧ b` for `b ∈ ⋀ M`, and in degree zero
  is inverse to `⋀ inl`.
* `TauCeti.exteriorPower.prodEquivTensor`: the degree-`n` exterior sum comparison
  `⋀ⁿ (M × N) ≃ ⨁ᵢ ⋀ⁱ M ⊗ ⋀ⁿ⁻ⁱ N`, `i = 0, …, n`.
* `TauCeti.exteriorPower.prodEquivTensor_symm_lof_tmul_ιMulti`: its inverse sends a tensor of
  pure wedges to the concatenated wedge, the `M` factors first.
* `TauCeti.exteriorPower.prodEquivTensor_map_prodMap`: naturality in both modules.
* `TauCeti.exteriorPower.prodEquivTensor_zero_ιMulti`, `prodEquivTensor_one_ιMulti`: in degrees
  zero and one it is the unit comparison and the direct sum comparison.

## References

* C. A. Weibel, *The K-book: an introduction to algebraic K-theory*, Graduate Studies in
  Mathematics 145, American Mathematical Society, 2013, Chapter I, §3 (the sum formula for
  exterior powers of a direct sum).
-/

public section

noncomputable section

open scoped DirectSum TensorProduct

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
theorem wedgeTensor_tmul_ιMulti (p q n : ℕ) (h : p + q = n) (u : Fin p → M) (v : Fin q → N) :
    wedgeTensor R M N p q n h
      (_root_.exteriorPower.ιMulti R p u ⊗ₜ _root_.exteriorPower.ιMulti R q v) =
    _root_.exteriorPower.ιMulti R n
      (Fin.append (LinearMap.inl R M N ∘ u) (LinearMap.inr R M N ∘ v) ∘ Fin.cast h.symm) := by
  subst h
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
        simp only [TensorProduct.map_tmul, coe_wedgeTensor_tmul, coe_proj_of_mem a.property,
          coe_proj_of_mem b.property]
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

/-- The `⋀ M`-component of `a ∈ ⋀ M ⊆ ⋀ (M × N)` is `a`. -/
theorem map_fst_comp_map_inl (n : ℕ) :
    _root_.exteriorPower.map n (LinearMap.fst R M N) ∘ₗ
        _root_.exteriorPower.map n (LinearMap.inl R M N) = LinearMap.id := by
  rw [← _root_.exteriorPower.map_comp, LinearMap.fst_comp_inl, _root_.exteriorPower.map_id]

/-- The `⋀ M`-component of `e ∧ b` is zero, for `e = (0, x)` and `b ∈ ⋀ M ⊆ ⋀ (M × N)`. -/
theorem map_fst_comp_wedgeLeft (x : N) (n : ℕ) :
    _root_.exteriorPower.map (n + 1) (LinearMap.fst R M N) ∘ₗ
        (ExteriorAlgebra.wedgeLeft (LinearMap.inr R M N x) n ∘ₗ
          _root_.exteriorPower.map n (LinearMap.inl R M N)) = 0 :=
  LinearMap.ext fun b ↦ Subtype.ext <| by simp

/-- In degree zero, `⋀ (M × N)` has no `N`-part: `⋀⁰ inl ∘ ⋀⁰ fst = id`. -/
theorem map_inl_comp_map_fst_zero :
    _root_.exteriorPower.map 0 (LinearMap.inl R M N) ∘ₗ
        _root_.exteriorPower.map 0 (LinearMap.fst R M N) = LinearMap.id := by
  rw [← _root_.exteriorPower.map_comp]
  refine _root_.exteriorPower.linearMap_ext (AlternatingMap.ext fun v ↦ ?_)
  simp only [LinearMap.compAlternatingMap_apply, _root_.exteriorPower.map_apply_ιMulti,
    LinearMap.id_apply]
  exact congrArg _ (Subsingleton.elim _ _)

/-! ### The degree-`n` exterior sum comparison -/

section prodEquivTensor

variable (R M N) in
/-- The bidegree-`(i, n - i)` components of the image of `⋀ⁿ (M × N)` under
`ExteriorAlgebra.prodEquivTensor`, collected into a direct sum. -/
private def toDirectSum (n : ℕ) :
    ⋀[R]^n (M × N) →ₗ[R] ⨁ i : Fin (n + 1), ⋀[R]^(i : ℕ) M ⊗[R] ⋀[R]^(n - i) N :=
  (DirectSum.linearEquivFunOnFintype R _ _).symm.toLinearMap ∘ₗ
    LinearMap.pi fun i ↦ TensorProduct.map (proj R M i) (proj R N (n - i)) ∘ₗ
      (GradedTensorProduct.of R (fun i ↦ ⋀[R]^i M) (fun i ↦ ⋀[R]^i N)).symm.toLinearMap ∘ₗ
      (ExteriorAlgebra.prodEquivTensor R M N).toLinearMap ∘ₗ (⋀[R]^n (M × N)).subtype

variable (R M N) in
/-- The wedge products `⋀ⁱ M ⊗ ⋀ⁿ⁻ⁱ N → ⋀ⁿ (M × N)`, summed over `i`. -/
private def ofDirectSum (n : ℕ) :
    (⨁ i : Fin (n + 1), ⋀[R]^(i : ℕ) M ⊗[R] ⋀[R]^(n - i) N) →ₗ[R] ⋀[R]^n (M × N) :=
  DirectSum.toModule R _ _ fun i ↦ wedgeTensor R M N i (n - i) n (by omega)

private theorem toDirectSum_apply (n : ℕ) (x : ⋀[R]^n (M × N)) (i : Fin (n + 1)) :
    toDirectSum R M N n x i = TensorProduct.map (proj R M i) (proj R N (n - i))
      ((GradedTensorProduct.of R _ _).symm (ExteriorAlgebra.prodEquivTensor R M N x)) :=
  (rfl)

private theorem ofDirectSum_lof (n : ℕ) (i : Fin (n + 1)) (a : ⋀[R]^(i : ℕ) M)
    (b : ⋀[R]^(n - i) N) :
    (ofDirectSum R M N n (DirectSum.lof R _ _ i (a ⊗ₜ b)) : ExteriorAlgebra R (M × N)) =
      (ExteriorAlgebra.prodEquivTensor R M N).symm (a ᵍ⊗ₜ[R] b) := by
  simp [ofDirectSum, ExteriorAlgebra.prodEquivTensor_symm_tmul]

private theorem ofDirectSum_toDirectSum (n : ℕ) (x : ⋀[R]^n (M × N)) :
    ofDirectSum R M N n (toDirectSum R M N n x) = x := by
  apply Subtype.ext
  rw [← DirectSum.sum_univ_of (toDirectSum R M N n x)]
  simp only [map_sum, ← DirectSum.lof_eq_of R, Submodule.coe_sum, ofDirectSum,
    DirectSum.toModule_lof, toDirectSum_apply]
  rw [sum_coe_wedgeTensor_map_proj]
  simp

private theorem toDirectSum_ofDirectSum (n : ℕ)
    (y : ⨁ i : Fin (n + 1), ⋀[R]^(i : ℕ) M ⊗[R] ⋀[R]^(n - i) N) :
    toDirectSum R M N n (ofDirectSum R M N n y) = y := by
  induction y using DirectSum.induction_on with
  | zero => simp
  | add y y' hy hy' => simp [hy, hy']
  | of i t =>
    induction t using TensorProduct.inductionOn with
    | add t t' ht ht' => simp only [map_add, ht, ht']
    | tmul a b =>
      ext j
      rw [toDirectSum_apply, ← DirectSum.lof_eq_of R, ofDirectSum_lof]
      simp only [AlgEquiv.apply_symm_apply, GradedTensorProduct.tmul, LinearEquiv.symm_apply_apply,
        TensorProduct.map_tmul]
      by_cases hji : j = i
      · subst hji
        simp
      · have hval : (i : ℕ) ≠ j := fun h ↦ hji (Fin.ext h.symm)
        have ha : proj R M j (a : ExteriorAlgebra R M) = 0 :=
          Subtype.ext ((coe_proj_of_mem a.property).trans (ite_eq_right hval))
        rw [ha, TensorProduct.zero_tmul, DirectSum.lof_eq_of, DirectSum.of_eq_of_ne _ _ _ hji]

variable (R M N) in
/-- The degree-`n` exterior sum comparison `⋀ⁿ (M × N) ≃ ⨁ᵢ ⋀ⁱ M ⊗ ⋀ⁿ⁻ⁱ N`, the sum running over
`i = 0, …, n`. It is the degree-`n` part of Mathlib's `ExteriorAlgebra.prodEquivTensor`: the `i`th
component of the image of `x` is the bidegree-`(i, n - i)` component of
`ExteriorAlgebra.prodEquivTensor x` (`prodEquivTensor_apply`). The inverse sends `a ⊗ b` in the
`i`th summand to the wedge product `a ∧ b` in `⋀ⁿ (M × N)`, the factor from `M` first
(`coe_prodEquivTensor_symm_lof_tmul`, `prodEquivTensor_symm_lof_tmul_ιMulti`). -/
def prodEquivTensor (n : ℕ) :
    ⋀[R]^n (M × N) ≃ₗ[R] ⨁ i : Fin (n + 1), ⋀[R]^(i : ℕ) M ⊗[R] ⋀[R]^(n - i) N :=
  .ofLinearMap (toDirectSum R M N n) (ofDirectSum R M N n)
    (LinearMap.ext (toDirectSum_ofDirectSum n)) (LinearMap.ext (ofDirectSum_toDirectSum n))

/-- The `i`th component of `prodEquivTensor x` is the bidegree-`(i, n - i)` component of the image
of `x` under `ExteriorAlgebra.prodEquivTensor`. -/
theorem prodEquivTensor_apply (n : ℕ) (x : ⋀[R]^n (M × N)) (i : Fin (n + 1)) :
    prodEquivTensor R M N n x i = TensorProduct.map (proj R M i) (proj R N (n - i))
      ((GradedTensorProduct.of R _ _).symm (ExteriorAlgebra.prodEquivTensor R M N x)) :=
  (rfl)

/-- The inverse of `prodEquivTensor` is the sum of the wedge products `wedgeTensor`. -/
theorem prodEquivTensor_symm_lof (n : ℕ) (i : Fin (n + 1))
    (t : ⋀[R]^(i : ℕ) M ⊗[R] ⋀[R]^(n - i) N) :
    (prodEquivTensor R M N n).symm (DirectSum.lof R _ _ i t) =
      wedgeTensor R M N i (n - i) n (by omega) t :=
  DirectSum.toModule_lof R _ _

/-- The inverse of `prodEquivTensor` sends `a ⊗ b` to the wedge product of `a` and `b`, the factor
from `M` first. -/
@[simp]
theorem coe_prodEquivTensor_symm_lof_tmul (n : ℕ) (i : Fin (n + 1)) (a : ⋀[R]^(i : ℕ) M)
    (b : ⋀[R]^(n - i) N) :
    ((prodEquivTensor R M N n).symm (DirectSum.lof R _ _ i (a ⊗ₜ b)) :
        ExteriorAlgebra R (M × N)) =
      ExteriorAlgebra.map (LinearMap.inl R M N) a *
        ExteriorAlgebra.map (LinearMap.inr R M N) b := by
  rw [prodEquivTensor_symm_lof, coe_wedgeTensor_tmul]

/-- The ordered pure-wedge formula: the inverse of `prodEquivTensor` sends
`(m₁ ∧ ⋯ ∧ mᵢ) ⊗ (m'₁ ∧ ⋯ ∧ m'ₙ₋ᵢ)` to `(m₁, 0) ∧ ⋯ ∧ (mᵢ, 0) ∧ (0, m'₁) ∧ ⋯ ∧ (0, m'ₙ₋ᵢ)`. -/
@[simp]
theorem prodEquivTensor_symm_lof_tmul_ιMulti (n : ℕ) (i : Fin (n + 1)) (m : Fin i → M)
    (m' : Fin (n - i) → N) :
    (prodEquivTensor R M N n).symm (DirectSum.lof R _ _ i
        (_root_.exteriorPower.ιMulti R i m ⊗ₜ _root_.exteriorPower.ιMulti R (n - i) m')) =
      _root_.exteriorPower.ιMulti R n (Fin.append (LinearMap.inl R M N ∘ m)
        (LinearMap.inr R M N ∘ m') ∘ Fin.cast (by omega)) := by
  rw [prodEquivTensor_symm_lof, wedgeTensor_tmul_ιMulti]

/-- The ordered pure-wedge formula for `prodEquivTensor`: it sends
`(m₁, 0) ∧ ⋯ ∧ (mᵢ, 0) ∧ (0, m'₁) ∧ ⋯ ∧ (0, m'ₙ₋ᵢ)` to `(m₁ ∧ ⋯ ∧ mᵢ) ⊗ (m'₁ ∧ ⋯ ∧ m'ₙ₋ᵢ)` in the
`i`th summand. -/
theorem prodEquivTensor_ιMulti_append (n : ℕ) (i : Fin (n + 1)) (m : Fin i → M)
    (m' : Fin (n - i) → N) :
    prodEquivTensor R M N n (_root_.exteriorPower.ιMulti R n (Fin.append
        (LinearMap.inl R M N ∘ m) (LinearMap.inr R M N ∘ m') ∘ Fin.cast (by omega))) =
      DirectSum.lof R _ _ i
        (_root_.exteriorPower.ιMulti R i m ⊗ₜ _root_.exteriorPower.ιMulti R (n - i) m') := by
  rw [← prodEquivTensor_symm_lof_tmul_ιMulti, LinearEquiv.apply_symm_apply]

section map

variable {M' N' : Type*} [AddCommGroup M'] [Module R M'] [AddCommGroup N'] [Module R N']

/-- Naturality of the inverse of `prodEquivTensor`: for linear maps `f : M → M'` and
`g : N → N'`, it intertwines the sum of the maps `⋀ⁱ f ⊗ ⋀ⁿ⁻ⁱ g` with `⋀ⁿ (f × g)`. -/
theorem map_prodMap_prodEquivTensor_symm (f : M →ₗ[R] M') (g : N →ₗ[R] N') (n : ℕ)
    (y : ⨁ i : Fin (n + 1), ⋀[R]^(i : ℕ) M ⊗[R] ⋀[R]^(n - i) N) :
    _root_.exteriorPower.map n (f.prodMap g) ((prodEquivTensor R M N n).symm y) =
      (prodEquivTensor R M' N' n).symm (DirectSum.lmap (fun i : Fin (n + 1) ↦
        TensorProduct.map (_root_.exteriorPower.map i f) (_root_.exteriorPower.map (n - i) g))
          y) := by
  induction y using DirectSum.induction_on with
  | zero => simp
  | add y y' hy hy' => simp only [map_add, hy, hy']
  | of i t =>
    rw [← DirectSum.lof_eq_of R, prodEquivTensor_symm_lof, map_prodMap_wedgeTensor_apply,
      DirectSum.lmap_lof, prodEquivTensor_symm_lof]

/-- Naturality of `prodEquivTensor`: for linear maps `f : M → M'` and `g : N → N'`, it intertwines
`⋀ⁿ (f × g)` with the sum of the maps `⋀ⁱ f ⊗ ⋀ⁿ⁻ⁱ g`. -/
@[simp]
theorem prodEquivTensor_map_prodMap (f : M →ₗ[R] M') (g : N →ₗ[R] N') (n : ℕ)
    (x : ⋀[R]^n (M × N)) :
    prodEquivTensor R M' N' n (_root_.exteriorPower.map n (f.prodMap g) x) =
      DirectSum.lmap (fun i : Fin (n + 1) ↦ TensorProduct.map (_root_.exteriorPower.map i f)
        (_root_.exteriorPower.map (n - i) g)) (prodEquivTensor R M N n x) := by
  rw [← (prodEquivTensor R M N n).symm_apply_apply x, map_prodMap_prodEquivTensor_symm,
    LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]

end map

/-- In degree zero, `prodEquivTensor` is the unit comparison `R ≃ R ⊗ R`: it sends the empty
wedge to the tensor product of the empty wedges. -/
theorem prodEquivTensor_zero_ιMulti (v : Fin 0 → M × N) :
    prodEquivTensor R M N 0 (_root_.exteriorPower.ιMulti R 0 v) =
      DirectSum.lof R _ _ (0 : Fin 1)
        (_root_.exteriorPower.ιMulti R 0 ![] ⊗ₜ _root_.exteriorPower.ιMulti R 0 ![]) := by
  rw [← LinearEquiv.eq_symm_apply, prodEquivTensor_symm_lof]
  apply Subtype.ext
  simp

/-- In degree one, `prodEquivTensor` is the direct sum comparison: it sends `(m, m')` to `1 ⊗ m'`
in the summand `⋀⁰ M ⊗ ⋀¹ N` plus `m ⊗ 1` in the summand `⋀¹ M ⊗ ⋀⁰ N`. -/
theorem prodEquivTensor_one_ιMulti (v : Fin 1 → M × N) :
    prodEquivTensor R M N 1 (_root_.exteriorPower.ιMulti R 1 v) =
      DirectSum.lof R _ _ (0 : Fin 2) (_root_.exteriorPower.ιMulti R 0 ![] ⊗ₜ
          _root_.exteriorPower.ιMulti R 1 (Prod.snd ∘ v)) +
        DirectSum.lof R _ _ (1 : Fin 2) (_root_.exteriorPower.ιMulti R 1 (Prod.fst ∘ v) ⊗ₜ
          _root_.exteriorPower.ιMulti R 0 ![]) := by
  rw [← LinearEquiv.eq_symm_apply, map_add, prodEquivTensor_symm_lof, prodEquivTensor_symm_lof]
  apply Subtype.ext
  simp only [Submodule.coe_add, coe_wedgeTensor_tmul, _root_.exteriorPower.ιMulti_apply_coe,
    ExteriorAlgebra.ιMulti_zero_apply, ExteriorAlgebra.ιMulti_succ_apply, map_one, mul_one,
    one_mul, Function.comp_apply, ExteriorAlgebra.map_apply_ι, ← map_add]
  simp

end prodEquivTensor

end exteriorPower

end TauCeti
