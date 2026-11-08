/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.CliffordAlgebra.Prod

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

For the spinor modules of oriented even-dimensional Euclidean spaces, `γ` is the chirality
operator, and the normalized volume element of `V ⊕ W` then acts by the tensor grading; see
`TauCeti/LinearAlgebra/CliffordAlgebra/VolumeElement/Prod.lean`.

## Main definitions

* `AlgHom.cliffordProdTensor`: the action of `CliffordAlgebra (Q₁.prod Q₂)` on `E ⊗ F`.

## Main results

* `AlgHom.cliffordProdTensor_ι`: a vector `(v, w)` acts by `c₁(v) ⊗ 1 + γ ⊗ c₂(w)`.
* `AlgHom.cliffordProdTensor_map_inl`: `CliffordAlgebra Q₁` acts through the first factor.
* `AlgHom.cliffordProdTensor_map_inr_prod`: a product of `k` vectors of `M₂` acts by
  `γ ^ k ⊗ ρ₂ (·)`.
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

end AlgHom
