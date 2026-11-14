/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Projective
public import Mathlib.LinearAlgebra.CliffordAlgebra.Prod
public import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.LinearAlgebra.Contraction
import Mathlib.LinearAlgebra.Projection
import Mathlib.LinearAlgebra.TensorProduct.Prod

/-!
# The graded tensor product of Clifford modules

Let `Q₁` and `Q₂` be quadratic forms on `M₁` and `M₂`, and let `E` and `F` be modules over their
Clifford algebras, given by algebra maps `ρ₁` and `ρ₂`; write `c₁(v) = ρ₁ (ι Q₁ v)` and
`c₂(w) = ρ₂ (ι Q₂ w)`. Suppose `E` carries a grading operator `γ`: an involution, `γ² = 1`, that
anticommutes with every `c₁(v)`. Then

  `c(v, w) = c₁(v) ⊗ 1 + γ ⊗ c₂(w)`

satisfies the Clifford relation `c(v, w)² = Q₁ v + Q₂ w` of the orthogonal sum `Q₁.prod Q₂`, so it
makes `E ⊗ F` a module over `CliffordAlgebra (Q₁.prod Q₂)`
(`AlgHom.cliffordProdTensor`). The cross terms `c₁(v) γ + γ c₁(v)` vanish by anticommutation; this
is the Koszul sign of the graded tensor product. Without it, the untwisted formula
`c₁(v) ⊗ 1 + 1 ⊗ c₂(w)` generally fails the Clifford relation, because its cross terms
`2 c₁(v) ⊗ c₂(w)` need not vanish.

The first summand acts through the first factor alone: an element `a` of `CliffordAlgebra Q₁`,
included by `CliffordAlgebra.map` along `QuadraticMap.Isometry.inl`, acts by `ρ₁ a ⊗ 1`. A
product of `k` vectors of the second summand acts by `γ ^ k ⊗ ρ₂ (·)`. If `F` is graded as well,
by `γ₂`, then the tensor grading `γ ⊗ γ₂` is again an involution anticommuting with every
`c(v, w)`, so `E ⊗ F` is a graded module and the construction can be iterated.

Mathlib's `CliffordAlgebra.prodEquiv` identifies `CliffordAlgebra (Q₁.prod Q₂)` with the graded
tensor product `evenOdd Q₁ ᵍ⊗ evenOdd Q₂`, and this action is the Koszul-signed tensor action
through it: an element `b` of `CliffordAlgebra Q₂` of parity `j` acts by `γ ^ j ⊗ ρ₂ b`, so the
pure tensor `a ᵍ⊗ b` acts by `ρ₁ a γ ^ j ⊗ ρ₂ b`, and on a homogeneous vector `e` of `γ`-degree `i`
evaluates `e ⊗ f` to `(-1) ^ (i * j) • (ρ₁ a e ⊗ ρ₂ b f)`. When `E` and `F` are finite projective
and `ρ₁`, `ρ₂` are bijective onto `End E` and `End F`, the graded product action is bijective onto
`End (E ⊗ F)`.

For the spinor modules of oriented even-dimensional Euclidean spaces, `γ` is the chirality
operator, and the normalized volume element of `V ⊕ W` then acts by the tensor grading; see
`TauCeti/LinearAlgebra/CliffordAlgebra/VolumeElement/Prod/Basic.lean`.

## Main definitions

* `AlgHom.cliffordProdTensor`: the action of `CliffordAlgebra (Q₁.prod Q₂)` on `E ⊗ F`.

## Main results

* `AlgHom.cliffordProdTensor_ι`: a vector `(v, w)` acts by `c₁(v) ⊗ 1 + γ ⊗ c₂(w)`.
* `AlgHom.cliffordProdTensor_map_inl`: `CliffordAlgebra Q₁` acts through the first factor.
* `AlgHom.cliffordProdTensor_map_inr_prod`: a product of `k` vectors of `M₂` acts by
  `γ ^ k ⊗ ρ₂ (·)`.
* `AlgHom.cliffordProdTensor_map_inr_of_mem_evenOdd`: an element of `CliffordAlgebra Q₂` of
  parity `j` acts by `γ ^ j ⊗ ρ₂ (·)`.
* `AlgHom.cliffordProdTensor_toProd_tmul` and `AlgHom.cliffordProdTensor_toProd_tmul_apply_tmul`:
  under `CliffordAlgebra.prodEquiv`, the pure tensor `a ᵍ⊗ b` with `b` of parity `j` acts by
  `ρ₁ a γ ^ j ⊗ ρ₂ b`, sending `e ⊗ f` to `(-1) ^ (i * j) • (ρ₁ a e ⊗ ρ₂ b f)` for `e` in the
  `(-1) ^ i`-eigenspace of `γ`.
* `AlgHom.cliffordProdTensor_bijective`: for finite projective `E` and `F`, bijectivity of `ρ₁` and
  `ρ₂` implies bijectivity of `cliffordProdTensor`.
* `AlgHom.map_mul_cliffordProdTensor_ι`: the tensor grading `γ ⊗ γ₂` anticommutes with every
  vector.

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I, §1 and §5.
* M. F. Atiyah, R. Bott and A. Shapiro, *Clifford modules*, Topology 3 (1964), §1.
-/

public section

open TensorProduct

namespace AlgHom

open CliffordAlgebra

variable {R M₁ M₂ E F : Type*} [CommRing R]
  [AddCommGroup M₁] [Module R M₁] [AddCommGroup M₂] [Module R M₂]
  {Q₁ : QuadraticForm R M₁} {Q₂ : QuadraticForm R M₂}
  [AddCommGroup E] [Module R E] [AddCommGroup F] [Module R F]

variable (ρ₁ : CliffordAlgebra Q₁ →ₐ[R] Module.End R E) (γ : Module.End R E)
  (hγ : γ * γ = 1) (hγρ : ∀ v, γ * ρ₁ (ι Q₁ v) = -(ρ₁ (ι Q₁ v) * γ))
  (ρ₂ : CliffordAlgebra Q₂ →ₐ[R] Module.End R F)

/-- The operator `c₁(v) ⊗ 1 + γ ⊗ c₂(w)` of a vector `(v, w)`, before the Clifford relation is
checked. -/
private def cliffordProdTensorAux : M₁ × M₂ →ₗ[R] Module.End R (E ⊗[R] F) where
  toFun x := map (ρ₁ (ι Q₁ x.1)) 1 + map γ (ρ₂ (ι Q₂ x.2))
  map_add' x y := by
    simp only [Prod.fst_add, Prod.snd_add, map_add, map_add_left, map_add_right]
    abel
  map_smul' r x := by
    simp only [Prod.smul_fst, Prod.smul_snd, map_smul, map_smul_left, map_smul_right,
      RingHom.id_apply, smul_add]

include hγ hγρ in
private theorem cliffordProdTensorAux_mul_self (x : M₁ × M₂) :
    cliffordProdTensorAux ρ₁ γ ρ₂ x * cliffordProdTensorAux ρ₁ γ ρ₂ x =
      algebraMap R _ ((Q₁.prod Q₂) x) := by
  have h : TensorProduct.map (γ * ρ₁ (ι Q₁ x.1)) (ρ₂ (ι Q₂ x.2)) =
      -TensorProduct.map (ρ₁ (ι Q₁ x.1) * γ) (ρ₂ (ι Q₂ x.2)) :=
    eq_neg_of_add_eq_zero_left (by rw [← map_add_left, hγρ, neg_add_cancel, map_zero_left])
  simp only [cliffordProdTensorAux, LinearMap.coe_mk, AddHom.coe_mk, add_mul, mul_add,
    ← TensorProduct.map_mul, mul_one, one_mul, hγ, ← map_mul, ι_sq_scalar, AlgHom.commutes, h,
    QuadraticMap.prod_apply]
  simp only [Algebra.algebraMap_eq_smul_one, map_smul_left, map_smul_right, TensorProduct.map_one]
  module

/-- **The graded tensor product of Clifford modules.** If `ρ₁` makes `E` a module over
`CliffordAlgebra Q₁` with a grading operator `γ`, an involution anticommuting with every vector,
and `ρ₂` makes `F` a module over `CliffordAlgebra Q₂`, then the vector `(v, w)` of the orthogonal
sum `Q₁.prod Q₂` acts on `E ⊗ F` by `c₁(v) ⊗ 1 + γ ⊗ c₂(w)`
(`AlgHom.cliffordProdTensor_ι`). -/
noncomputable def cliffordProdTensor :
    CliffordAlgebra (Q₁.prod Q₂) →ₐ[R] Module.End R (E ⊗[R] F) :=
  CliffordAlgebra.lift (Q₁.prod Q₂)
    ⟨cliffordProdTensorAux ρ₁ γ ρ₂, cliffordProdTensorAux_mul_self ρ₁ γ hγ hγρ ρ₂⟩

/-- A vector `(v, w)` acts on `E ⊗ F` by `c₁(v) ⊗ 1 + γ ⊗ c₂(w)`. -/
theorem cliffordProdTensor_ι (x : M₁ × M₂) :
    cliffordProdTensor ρ₁ γ hγ hγρ ρ₂ (ι (Q₁.prod Q₂) x) =
      (ρ₁ (ι Q₁ x.1)).rTensor F + map γ (ρ₂ (ι Q₂ x.2)) := by
  rw [cliffordProdTensor, lift_ι_apply]
  rfl

/-- On a pure tensor, `c(v, w) (e ⊗ f) = c₁(v) e ⊗ f + γ e ⊗ c₂(w) f`. -/
@[simp]
theorem cliffordProdTensor_ι_tmul (x : M₁ × M₂) (e : E) (f : F) :
    cliffordProdTensor ρ₁ γ hγ hγρ ρ₂ (ι (Q₁.prod Q₂) x) (e ⊗ₜ f) =
      ρ₁ (ι Q₁ x.1) e ⊗ₜ f + γ e ⊗ₜ ρ₂ (ι Q₂ x.2) f := by
  simp [cliffordProdTensor_ι]

/-- A vector of the first summand acts through the first factor: `c(v, 0) = c₁(v) ⊗ 1`. -/
@[simp]
theorem cliffordProdTensor_ι_inl (v : M₁) :
    cliffordProdTensor ρ₁ γ hγ hγρ ρ₂ (ι (Q₁.prod Q₂) (v, 0)) = (ρ₁ (ι Q₁ v)).rTensor F := by
  simp [cliffordProdTensor_ι]

/-- A vector of the second summand acts through the grading: `c(0, w) = γ ⊗ c₂(w)`. -/
@[simp]
theorem cliffordProdTensor_ι_inr (w : M₂) :
    cliffordProdTensor ρ₁ γ hγ hγρ ρ₂ (ι (Q₁.prod Q₂) (0, w)) = map γ (ρ₂ (ι Q₂ w)) := by
  simp [cliffordProdTensor_ι]

/-- **The first Clifford algebra acts through the first factor**: an element `a` of
`CliffordAlgebra Q₁`, included along `QuadraticMap.Isometry.inl`, acts by `ρ₁ a ⊗ 1`. -/
@[simp]
theorem cliffordProdTensor_map_inl (a : CliffordAlgebra Q₁) :
    cliffordProdTensor ρ₁ γ hγ hγρ ρ₂ (map (QuadraticMap.Isometry.inl Q₁ Q₂) a) =
      (ρ₁ a).rTensor F := by
  induction a using CliffordAlgebra.induction with
  | algebraMap r =>
    rw [AlgHom.commutes, AlgHom.commutes, AlgHom.commutes]
    simp only [Algebra.algebraMap_eq_smul_one, LinearMap.rTensor_smul, Module.End.one_eq_id,
      LinearMap.rTensor_id]
  | ι v => rw [map_apply_ι, QuadraticMap.Isometry.inl_apply, cliffordProdTensor_ι_inl]
  | mul a b ha hb => rw [map_mul, map_mul, ha, hb, map_mul, LinearMap.rTensor_mul]
  | add a b ha hb => rw [map_add, map_add, ha, hb, map_add, LinearMap.rTensor_add]

/-- **Products of vectors of the second summand**: the product `c(0, w₁) ⋯ c(0, wₖ)` acts by
`γ ^ k ⊗ c₂(w₁) ⋯ c₂(wₖ)`. -/
theorem cliffordProdTensor_map_inr_prod (l : List M₂) :
    cliffordProdTensor ρ₁ γ hγ hγρ ρ₂
        (map (QuadraticMap.Isometry.inr Q₁ Q₂) (l.map (ι Q₂)).prod) =
      map (γ ^ l.length) (ρ₂ (l.map (ι Q₂)).prod) := by
  induction l with
  | nil => simp [TensorProduct.map_one]
  | cons w l ih =>
    simp only [List.map_cons, List.prod_cons, List.length_cons, map_mul, ih, map_apply_ι,
      QuadraticMap.Isometry.inr_apply, cliffordProdTensor_ι_inr, pow_succ', TensorProduct.map_mul]

/-- **The tensor product of graded modules is graded**: if `γ₂` is a grading operator of `F`,
anticommuting with every `c₂(w)`, then the tensor grading `γ ⊗ γ₂` anticommutes with every vector
of `Q₁.prod Q₂`. It is an involution when `γ₂` is (`TensorProduct.map_mul`). -/
theorem map_mul_cliffordProdTensor_ι (γ₂ : Module.End R F)
    (hγ₂ρ : ∀ w, γ₂ * ρ₂ (ι Q₂ w) = -(ρ₂ (ι Q₂ w) * γ₂)) (x : M₁ × M₂) :
    map γ γ₂ * cliffordProdTensor ρ₁ γ hγ hγρ ρ₂ (ι (Q₁.prod Q₂) x) =
      -(cliffordProdTensor ρ₁ γ hγ hγρ ρ₂ (ι (Q₁.prod Q₂) x) * map γ γ₂) := by
  rw [eq_neg_iff_add_eq_zero, cliffordProdTensor_ι, LinearMap.rTensor, ← Module.End.one_eq_id]
  simp only [mul_add, add_mul, ← TensorProduct.map_mul, mul_one, one_mul]
  -- Collect the anticommutators `γ c₁(v) + c₁(v) γ` and `γ₂ c₂(w) + c₂(w) γ₂`, which vanish.
  rw [add_add_add_comm, ← map_add_left, ← map_add_right, hγρ, hγ₂ρ]
  simp

/-- **Products of `k` vectors of the second summand** act by `γ ^ k ⊗ ρ₂ (·)`: this extends
`AlgHom.cliffordProdTensor_map_inr_prod` to every element of the `k`-th power of the vector
subspace. -/
theorem cliffordProdTensor_map_inr_of_mem_pow {k : ℕ} {b : CliffordAlgebra Q₂}
    (hb : b ∈ LinearMap.range (ι Q₂) ^ k) :
    cliffordProdTensor ρ₁ γ hγ hγρ ρ₂ (map (QuadraticMap.Isometry.inr Q₁ Q₂) b) =
      map (γ ^ k) (ρ₂ b) := by
  induction hb using Submodule.pow_induction_on_left' with
  | algebraMap r =>
    rw [AlgHom.commutes, AlgHom.commutes, AlgHom.commutes, pow_zero]
    simp only [Algebra.algebraMap_eq_smul_one, map_smul_right, TensorProduct.map_one]
  | add x y i _ _ hx hy => rw [map_add, map_add, hx, hy, map_add ρ₂, map_add_right]
  | mem_mul m hm i x _ hx =>
    obtain ⟨w, rfl⟩ := hm
    rw [map_mul, map_mul, hx, map_apply_ι, QuadraticMap.Isometry.inr_apply,
      cliffordProdTensor_ι_inr, ← TensorProduct.map_mul, pow_succ', map_mul]

include hγ in
/-- **Homogeneous elements of the second summand act through the grading**: an element `b` of
`CliffordAlgebra Q₂` of parity `j` acts on `E ⊗ F` by `γ ^ j ⊗ ρ₂ b`, so even elements act by
`1 ⊗ ρ₂ b` and odd elements by `γ ⊗ ρ₂ b`. -/
theorem cliffordProdTensor_map_inr_of_mem_evenOdd {j : ZMod 2} {b : CliffordAlgebra Q₂}
    (hb : b ∈ evenOdd Q₂ j) :
    cliffordProdTensor ρ₁ γ hγ hγρ ρ₂ (map (QuadraticMap.Isometry.inr Q₁ Q₂) b) =
      map (γ ^ j.val) (ρ₂ b) := by
  induction b, hb using evenOdd_induction with
  | range_ι_pow v hv => exact cliffordProdTensor_map_inr_of_mem_pow ρ₁ γ hγ hγρ ρ₂ hv
  | add x y _ _ hx hy => rw [map_add, map_add, hx, hy, map_add ρ₂, map_add_right]
  | ι_mul_ι_mul m₁ m₂ x _ hx =>
    simp only [map_mul, hx, map_apply_ι, QuadraticMap.Isometry.inr_apply,
      cliffordProdTensor_ι_inr, ← TensorProduct.map_mul, hγ, one_mul]

include hγ in
/-- **The graded tensor product of Clifford modules is the Koszul-signed tensor action of
`CliffordAlgebra.prodEquiv`.** Under Mathlib's identification `CliffordAlgebra.prodEquiv` of
`CliffordAlgebra (Q₁.prod Q₂)` with the graded tensor product `evenOdd Q₁ ᵍ⊗ evenOdd Q₂`, whose
inverse is `CliffordAlgebra.toProd`, the pure tensor `a ᵍ⊗ b` with `b` of parity `j` acts on
`E ⊗ F` by `ρ₁ a γ ^ j ⊗ ρ₂ b`. -/
theorem cliffordProdTensor_toProd_tmul (a : CliffordAlgebra Q₁) {j : ZMod 2}
    {b : CliffordAlgebra Q₂} (hb : b ∈ evenOdd Q₂ j) :
    cliffordProdTensor ρ₁ γ hγ hγρ ρ₂ (toProd Q₁ Q₂ (a ᵍ⊗ₜ b)) =
      map (ρ₁ a * γ ^ j.val) (ρ₂ b) := by
  rw [toProd, GradedTensorProduct.lift_tmul, map_mul, cliffordProdTensor_map_inl,
    cliffordProdTensor_map_inr_of_mem_evenOdd ρ₁ γ hγ hγρ ρ₂ hb, LinearMap.rTensor,
    ← Module.End.one_eq_id, ← TensorProduct.map_mul, one_mul]

include hγ in
/-- **Koszul sign on homogeneous vectors.** If `b` has parity `j` in `CliffordAlgebra Q₂` and
`e` lies in the `(-1) ^ i`-eigenspace of `γ` (`i = 0` for even, `i = 1` for odd), then `a ᵍ⊗ b`
acts on `e ⊗ f` by `(-1) ^ (i * j.val) • (ρ₁ a e ⊗ ρ₂ b f)`. -/
theorem cliffordProdTensor_toProd_tmul_apply_tmul (a : CliffordAlgebra Q₁) {j : ZMod 2}
    {b : CliffordAlgebra Q₂} (hb : b ∈ evenOdd Q₂ j) {i : ℕ} {e : E}
    (he : e ∈ γ.eigenspace ((-1 : R) ^ i)) (f : F) :
    cliffordProdTensor ρ₁ γ hγ hγρ ρ₂ (toProd Q₁ Q₂ (a ᵍ⊗ₜ b)) (e ⊗ₜ f) =
      (-1 : R) ^ (i * j.val) • (ρ₁ a e ⊗ₜ ρ₂ b f) := by
  have hpow : ∀ k : ℕ, (γ ^ k) e = (-1 : R) ^ (i * k) • e := fun k ↦ by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ', mul_apply_eq_comp, ih, map_smul, Module.End.mem_eigenspace_iff.mp he,
        smul_smul, ← pow_add, mul_add, mul_one, add_comm]
  rw [cliffordProdTensor_toProd_tmul ρ₁ γ hγ hγρ ρ₂ a hb, map_tmul, mul_apply_eq_comp,
    hpow j.val, map_smul, smul_tmul']

/-- **Bijectivity of the graded tensor product of endomorphism representations.** When `E` and `F`
are finite projective `R`-modules and `ρ₁`, `ρ₂` are bijective onto `End_R E` and `End_R F`, the
graded tensor product action `cliffordProdTensor` is bijective onto `End_R (E ⊗ F)`. No finiteness
assumption on `M₁` or `M₂` and no invertibility of `2` is needed. -/
theorem cliffordProdTensor_bijective [Module.Finite R E] [Module.Projective R E]
    [Module.Finite R F] [Module.Projective R F]
    (hρ₁ : Function.Bijective ρ₁) (hρ₂ : Function.Bijective ρ₂) :
    Function.Bijective (cliffordProdTensor ρ₁ γ hγ hγρ ρ₂) := by
  -- Right-multiplying `End_R E` by the involution `γ` is an `R`-linear equivalence.
  let rγ : Module.End R E ≃ₗ[R] Module.End R E :=
    { toFun f := f * γ
      invFun f := f * γ
      left_inv f := (mul_assoc f γ γ).trans ((congrArg (f * ·) hγ).trans (mul_one f))
      right_inv f := (mul_assoc f γ γ).trans ((congrArg (f * ·) hγ).trans (mul_one f))
      map_add' f g := add_mul f g γ
      map_smul' r f := smul_mul_assoc r f γ }
  let s₂ : (evenOdd Q₂ 0 × evenOdd Q₂ 1) ≃ₗ[R] CliffordAlgebra Q₂ :=
    (evenOdd Q₂ 0).prodEquivOfIsCompl (evenOdd Q₂ 1) (evenOdd_isCompl Q₂)
  let e₁ : CliffordAlgebra (Q₁.prod Q₂) ≃ₗ[R] CliffordAlgebra Q₁ ⊗[R] CliffordAlgebra Q₂ :=
    (CliffordAlgebra.prodEquiv Q₁ Q₂).toLinearEquiv.trans
      (GradedTensorProduct.of R (evenOdd Q₁) (evenOdd Q₂)).symm
  -- Assemble the equivalence `CliffordAlgebra (Q₁.prod Q₂) ≃ₗ[R] End_R (E ⊗ F)` by untwisting the
  -- odd summand of `CliffordAlgebra Q₂` by `rγ` and applying `homTensorHomEquiv`.
  let Ψ : CliffordAlgebra (Q₁.prod Q₂) ≃ₗ[R] Module.End R (E ⊗[R] F) :=
    e₁ ≪≫ₗ TensorProduct.congr (LinearEquiv.ofBijective ρ₁.toLinearMap hρ₁) s₂.symm ≪≫ₗ
      TensorProduct.prodRight R R (Module.End R E) (evenOdd Q₂ 0) (evenOdd Q₂ 1) ≪≫ₗ
      LinearEquiv.prodCongr (.refl R _) (rγ.rTensor (evenOdd Q₂ 1)) ≪≫ₗ
      (TensorProduct.prodRight R R (Module.End R E) (evenOdd Q₂ 0) (evenOdd Q₂ 1)).symm ≪≫ₗ
      TensorProduct.congr (.refl R _) (s₂.trans (LinearEquiv.ofBijective ρ₂.toLinearMap hρ₂)) ≪≫ₗ
      homTensorHomEquiv R E F E F
  have hlin : (cliffordProdTensor ρ₁ γ hγ hγρ ρ₂).toLinearMap = Ψ.toLinearMap := by
    refine e₁.symm.surjective.injective_linearMapComp_right ?_
    apply TensorProduct.ext'
    intro a b
    obtain ⟨b₀, b₁, hbb⟩ : ∃ b₀ b₁, s₂.symm b = (b₀, b₁) := ⟨(s₂.symm b).1, (s₂.symm b).2, rfl⟩
    have hb : b = s₂ (b₀, 0) + s₂ (0, b₁) := by
      rw [← map_add, Prod.mk_add_mk, add_zero, zero_add, ← hbb, s₂.apply_symm_apply]
    have he₁ (x : CliffordAlgebra Q₁) (y : CliffordAlgebra Q₂) :
        e₁.symm (x ⊗ₜ y) = toProd Q₁ Q₂ (x ᵍ⊗ₜ y) := rfl
    have hs₀ : s₂ (b₀, 0) = (b₀ : CliffordAlgebra Q₂) := by
      simp [s₂, Submodule.coe_prodEquivOfIsCompl']
    have hs₁ : s₂ (0, b₁) = (b₁ : CliffordAlgebra Q₂) := by
      simp [s₂, Submodule.coe_prodEquivOfIsCompl']
    have hρ₁_eq (x : CliffordAlgebra Q₁) :
        LinearEquiv.ofBijective ρ₁.toLinearMap hρ₁ x = ρ₁ x := rfl
    have hρ₂_eq (y : CliffordAlgebra Q₂) :
        LinearEquiv.ofBijective ρ₂.toLinearMap hρ₂ y = ρ₂ y := rfl
    rw [hb, tmul_add, map_add, map_add]
    congr 1
    · simp only [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap, AlgHom.toLinearMap_apply]
      rw [he₁, hs₀, cliffordProdTensor_toProd_tmul ρ₁ γ hγ hγρ ρ₂ a b₀.2, ← hs₀, ← he₁]
      have hs₀_symm : s₂.symm (b₀ : CliffordAlgebra Q₂) = (b₀, 0) :=
        s₂.symm_apply_eq.mpr hs₀.symm
      have hp₀ : (prodRight R R (Module.End R E) (evenOdd Q₂ 0) (evenOdd Q₂ 1)).symm
          (ρ₁ a ⊗ₜ b₀, 0) = ρ₁ a ⊗ₜ (b₀, 0) := by
        rw [← tmul_zero (evenOdd Q₂ 1) (ρ₁ a)]
        exact (prodRight R R _ _ _).symm_apply_apply (ρ₁ a ⊗ₜ (b₀, 0))
      ext e f'
      simp [Ψ, rγ, ZMod.val_zero, hρ₁_eq, hρ₂_eq, hs₀_symm, hp₀, hs₀]
    · simp only [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap, AlgHom.toLinearMap_apply]
      rw [he₁, hs₁, cliffordProdTensor_toProd_tmul ρ₁ γ hγ hγρ ρ₂ a b₁.2, ← hs₁, ← he₁]
      have h1 : (1 : ZMod 2).val = 1 := rfl
      have hs₁_symm : s₂.symm (b₁ : CliffordAlgebra Q₂) = (0, b₁) :=
        s₂.symm_apply_eq.mpr hs₁.symm
      have hp₁ : (prodRight R R (Module.End R E) (evenOdd Q₂ 0) (evenOdd Q₂ 1)).symm
          (0, (ρ₁ a * γ) ⊗ₜ b₁) = (ρ₁ a * γ) ⊗ₜ (0, b₁) := by
        rw [← tmul_zero (evenOdd Q₂ 0) (ρ₁ a * γ)]
        exact (prodRight R R _ _ _).symm_apply_apply ((ρ₁ a * γ) ⊗ₜ (0, b₁))
      ext e f'
      simp [Ψ, rγ, h1, hρ₁_eq, hρ₂_eq, hs₁_symm, hp₁, hs₁]
  have hcoe : (cliffordProdTensor ρ₁ γ hγ hγρ ρ₂ : _ → _) = Ψ :=
    congrArg DFunLike.coe hlin
  exact hcoe ▸ Ψ.bijective

end AlgHom
