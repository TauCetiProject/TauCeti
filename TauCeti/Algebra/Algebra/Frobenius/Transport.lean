/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Contraction
public import Mathlib.LinearAlgebra.Dual.BaseChange
public import Mathlib.LinearAlgebra.TensorProduct.Projective
public import Mathlib.RingTheory.Coalgebra.TensorProduct
public import Mathlib.RingTheory.TensorProduct.Finite
public import TauCeti.Algebra.Algebra.Frobenius.Coalgebra

/-!
# Transport, tensor products, and scalar extension of Frobenius algebras

This file develops structural operations on Frobenius coalgebras and trace-reconstructed Frobenius
algebras over an arbitrary commutative semiring `R`.

## Main definitions and results

* `Coalgebra.IsFrobenius.isPerfPair_compr₂_mul_counit`, `Coalgebra.IsFrobenius.traceTensorEquiv`,
  `Coalgebra.IsFrobenius.eq_of_counit_eq`: the trace pairing of a unital Frobenius coalgebra is
  perfect, and its counit uniquely determines its comultiplication.
* `CoalgEquiv.isFrobenius_iff`, `AlgEquiv.toCoalgEquivOfIsFrobenius`,
  `AlgEquiv.frobeniusCoalgEquiv`, `LinearMap.isPerfPair_compr₂_mul_iff_of_algEquiv`,
  `LinearMap.traceDualBasis_map`, `LinearMap.map_frobeniusCoalgebra_comul_of_algEquiv`: transport
  along algebra and coalgebra isomorphisms.
* `TensorProduct.instIsFrobenius`: the heterobasic tensor product `A ⊗[R] B` of an `S`-Frobenius
  coalgebra `A` and an `R`-Frobenius coalgebra `B` is `S`-Frobenius, unifying tensor products
  (`S = R`) and scalar extension (`A = S`).
* `LinearMap.isPerfPair_compr₂_mul_dualDistrib`, `LinearMap.frobeniusCoalgebra_dualDistrib`,
  `LinearMap.traceDualBasis_dualDistrib`, `LinearMap.isPerfPair_compr₂_mul_baseChange`,
  `LinearMap.frobeniusCoalgebra_baseChange`, `LinearMap.traceDualBasis_baseChange`: compatibility of
  perfect traces, `LinearMap.frobeniusCoalgebra`, and `LinearMap.traceDualBasis` with tensor
  products and scalar extension.

## References

* J. Kock, *Frobenius Algebras and 2D Topological Quantum Field Theories*, Chapter 2.
-/

public section

noncomputable section

open TensorProduct

/-! ### Perfectness and uniqueness for Frobenius coalgebras -/

namespace Coalgebra.IsFrobenius

section NonAssoc

variable {R A : Type*} [CommSemiring R] [NonAssocSemiring A] [Module R A] [Coalgebra R A]
  [SMulCommClass R A A] [IsScalarTower R A A] [IsFrobenius R A]

private theorem sum_counit_mul_left_smul_of_comul_one {S : Finset (A × A)}
    (hS : Coalgebra.comul (R := R) (1 : A) = ∑ i ∈ S, i.1 ⊗ₜ[R] i.2) (a : A) :
    ∑ x ∈ S, Coalgebra.counit (R := R) (a * x.1) • x.2 = a := by
  simpa [hS, tmul_sum, right_def] using
    congrArg (fun f : A ⊗[R] A →ₗ[R] A ⊗[R] A ↦
      TensorProduct.lid R A ((Coalgebra.counit (R := R) (A := A)).rTensor A (f (a ⊗ₜ[R] 1))))
      (right_eq_comul_comp_mul' (R := R) (A := A))

private theorem sum_counit_mul_right_smul_of_comul_one {S : Finset (A × A)}
    (hS : Coalgebra.comul (R := R) (1 : A) = ∑ i ∈ S, i.1 ⊗ₜ[R] i.2) (a : A) :
    ∑ x ∈ S, Coalgebra.counit (R := R) (x.2 * a) • x.1 = a := by
  simpa [hS, sum_tmul, left_def] using
    congrArg (fun f : A ⊗[R] A →ₗ[R] A ⊗[R] A ↦
      _root_.TensorProduct.rid R A ((Coalgebra.counit (R := R) (A := A)).lTensor A (f (1 ⊗ₜ[R] a))))
      (left_eq_comul_comp_mul' (R := R) (A := A))

/-- The flipped trace pairing `b ↦ (a ↦ counit (a * b))` of a unital Frobenius coalgebra is
bijective. -/
theorem compr₂_mul_counit_flip_bijective :
    Function.Bijective
      (((LinearMap.mul R A).compr₂ (Coalgebra.counit (R := R) (A := A))).flip) := by
  have ⟨S, hS⟩ := TensorProduct.exists_finset (R := R) (Coalgebra.comul (R := R) (1 : A))
  refine ⟨fun a b h ↦ ?_, fun f ↦ ⟨∑ x ∈ S, f x.2 • x.1, LinearMap.ext fun b ↦ ?_⟩⟩
  · rw [← sum_counit_mul_right_smul_of_comul_one hS b]
    simp only [LinearMap.ext_iff, LinearMap.flip_apply, LinearMap.compr₂_apply,
      LinearMap.mul_apply_apply] at h
    simp [← h, sum_counit_mul_right_smul_of_comul_one hS]
  · calc
      (((LinearMap.mul R A).compr₂ (Coalgebra.counit (R := R) (A := A))).flip
          (∑ x ∈ S, f x.2 • x.1)) b
        = ∑ x ∈ S, Coalgebra.counit (R := R) (b * x.1) • f x.2 := by simp [mul_comm (f _)]
      _ = f (∑ x ∈ S, Coalgebra.counit (R := R) (b * x.1) • x.2) := by
          simp only [← map_smul, ← map_sum]
      _ = f b := by rw [sum_counit_mul_left_smul_of_comul_one hS]

/-- The trace pairing `(a, b) ↦ counit (a * b)` of a unital Frobenius coalgebra is a perfect
pairing. -/
instance isPerfPair_compr₂_mul_counit :
    ((LinearMap.mul R A).compr₂ (Coalgebra.counit (R := R) (A := A))).IsPerfPair where
  bijective_left := compr₂_mul_counit_bijective
  bijective_right := compr₂_mul_counit_flip_bijective

end NonAssoc

section Semiring

variable (R A : Type*) [CommSemiring R] [Semiring A] [Algebra R A] [Coalgebra R A]
  [IsFrobenius R A]

/-- The tensor trace equivalence `A ⊗[R] A ≃ₗ[R] Module.Dual R (A ⊗[R] A)` of a Frobenius
coalgebra, sending `a ⊗ₜ b` to `x ⊗ₜ y ↦ counit (x * a) * counit (b * y)`. -/
def traceTensorEquiv : A ⊗[R] A ≃ₗ[R] Module.Dual R (A ⊗[R] A) :=
  (TensorProduct.congr
      (((LinearMap.mul R A).compr₂ (Coalgebra.counit (R := R) (A := A))).flip.toPerfPair)
      (((LinearMap.mul R A).compr₂ (Coalgebra.counit (R := R) (A := A))).toPerfPair)).trans
    (TensorProduct.dualDistribEquiv R A A)

variable {R A}

/-- Evaluation of `traceTensorEquiv` on pure tensors. -/
@[simp]
theorem traceTensorEquiv_tmul (a b x y : A) :
    traceTensorEquiv R A (a ⊗ₜ[R] b) (x ⊗ₜ[R] y) =
      Coalgebra.counit (R := R) (x * a) * Coalgebra.counit (R := R) (b * y) := by
  simp [traceTensorEquiv, mul_comm]

/-- On the comultiplication of `a`, `traceTensorEquiv` evaluates `x ⊗ₜ y` to
`counit (x * a * y)`. -/
@[simp]
theorem traceTensorEquiv_comul (a x y : A) :
    traceTensorEquiv R A (Coalgebra.comul (R := R) a) (x ⊗ₜ[R] y) =
      Coalgebra.counit (R := R) (x * a * y) := by
  have heval (t : A ⊗[R] A) :
      traceTensorEquiv R A t (x ⊗ₜ[R] y) =
        Coalgebra.counit (R := R)
          (_root_.TensorProduct.lid R A ((Coalgebra.counit (R := R) (A := A)).rTensor A
            ((LinearMap.mul' R A).rTensor A
              ((_root_.TensorProduct.assoc R A A A).symm (x ⊗ₜ[R] t)))) * y) := by
    induction t using TensorProduct.inductionOn with
    | tmul b z => simp
    | add t u ht hu => simp_all [tmul_add, add_mul]
  have h := congrArg (fun f : A ⊗[R] A →ₗ[R] A ⊗[R] A ↦ f (x ⊗ₜ[R] a))
    (right_eq_comul_comp_mul' (R := R) (A := A))
  simp only [right_def, LinearMap.comp_apply, LinearMap.lTensor_tmul, LinearEquiv.coe_coe,
    LinearMap.mul'_apply] at h
  rw [heval, h, Coalgebra.rTensor_counit_comul, _root_.TensorProduct.lid_tmul, one_smul]

end Semiring

/-- Two Frobenius coalgebra structures on the same algebra with the same counit are equal. -/
theorem eq_of_counit_eq {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A]
    (c₁ c₂ : Coalgebra R A) (h₁ : letI := c₁; IsFrobenius R A)
    (h₂ : letI := c₂; IsFrobenius R A) (hε : c₁.counit = c₂.counit) : c₁ = c₂ := by
  refine Coalgebra.ext ?_ hε
  let := c₁; have := h₁
  ext a
  apply (traceTensorEquiv R A).injective
  refine TensorProduct.ext' fun x y ↦ ?_
  rw [traceTensorEquiv_comul]
  have heq : traceTensorEquiv R A (c₂.comul a) (x ⊗ₜ[R] y) =
      letI := c₂; haveI := h₂; traceTensorEquiv R A (c₂.comul a) (x ⊗ₜ[R] y) := by
    induction c₂.comul a using TensorProduct.inductionOn with
    | tmul u v =>
      simp only [traceTensorEquiv_tmul]
      exact congrArg₂ (· * ·) (congrFun (congrArg DFunLike.coe hε) (x * u))
        (congrFun (congrArg DFunLike.coe hε) (v * y))
    | add t u ht hu => simp_all
  rw [heq]
  let := c₂; have := h₂
  rw [traceTensorEquiv_comul]
  exact congrFun (congrArg DFunLike.coe hε) (x * a * y)

end Coalgebra.IsFrobenius

/-! ### Transport along algebra and coalgebra isomorphisms -/

namespace CoalgEquiv

section NonUnital

variable {R A B : Type*} [CommSemiring R]
  [NonUnitalNonAssocSemiring A] [Module R A] [SMulCommClass R A A] [IsScalarTower R A A]
  [NonUnitalNonAssocSemiring B] [Module R B] [SMulCommClass R B B] [IsScalarTower R B B]
  [CoalgebraStruct R A] [CoalgebraStruct R B]

private theorem isFrobenius_of_mul (e : A ≃ₗc[R] B) (hmul : ∀ x y, e (x * y) = e x * e y)
    [Coalgebra.IsFrobenius R A] : Coalgebra.IsFrobenius R B := by
  constructor
  refine TensorProduct.ext' fun x y ↦ ?_
  obtain ⟨a, rfl⟩ := e.surjective x
  obtain ⟨b, rfl⟩ := e.surjective y
  have hcomul (c : A) : Coalgebra.comul (R := R) (e c) =
      TensorProduct.map e.toLinearMap e.toLinearMap (Coalgebra.comul (R := R) c) :=
    (congrArg (fun f : A →ₗ[R] B ⊗[R] B ↦ f c) e.map_comp_comul).symm
  have hleft : Coalgebra.IsFrobenius.left R B (e a ⊗ₜ[R] e b) =
      TensorProduct.map e.toLinearMap e.toLinearMap
        (Coalgebra.IsFrobenius.left R A (a ⊗ₜ[R] b)) := by
    simp only [Coalgebra.IsFrobenius.left_def, LinearMap.comp_apply, LinearMap.rTensor_tmul,
      LinearEquiv.coe_coe, hcomul]
    induction Coalgebra.comul (R := R) a using TensorProduct.inductionOn with
    | tmul u v => simp [hmul]
    | add t u ht hu => simp_all [add_tmul]
  have hright : Coalgebra.IsFrobenius.right R B (e a ⊗ₜ[R] e b) =
      TensorProduct.map e.toLinearMap e.toLinearMap
        (Coalgebra.IsFrobenius.right R A (a ⊗ₜ[R] b)) := by
    simp only [Coalgebra.IsFrobenius.right_def, LinearMap.comp_apply, LinearMap.lTensor_tmul,
      LinearEquiv.coe_coe, hcomul]
    induction Coalgebra.comul (R := R) b using TensorProduct.inductionOn with
    | tmul u v => simp [hmul]
    | add t u ht hu => simp_all [tmul_add]
  change Coalgebra.IsFrobenius.left R B (e a ⊗ₜ[R] e b) =
    Coalgebra.IsFrobenius.right R B (e a ⊗ₜ[R] e b)
  rw [hleft, hright, Coalgebra.IsFrobenius.left_eq_right (R := R) (A := A)]

/-- A multiplicative coalgebra equivalence preserves and reflects the Frobenius equation. -/
theorem isFrobenius_iff (e : A ≃ₗc[R] B) (hmul : ∀ x y, e (x * y) = e x * e y) :
    Coalgebra.IsFrobenius R A ↔ Coalgebra.IsFrobenius R B :=
  ⟨fun _ ↦ isFrobenius_of_mul e hmul,
    fun _ ↦ isFrobenius_of_mul e.symm fun x y ↦ e.injective (by simp [hmul])⟩

end NonUnital

end CoalgEquiv

namespace AlgEquiv

section IsFrobenius

variable {R A B : Type*} [CommSemiring R] [Semiring A] [Semiring B] [Algebra R A] [Algebra R B]
  [Coalgebra R A] [Coalgebra R B] [Coalgebra.IsFrobenius R A] [Coalgebra.IsFrobenius R B]

/-- A counit-preserving algebra isomorphism between Frobenius coalgebras is automatically a
coalgebra isomorphism. -/
def toCoalgEquivOfIsFrobenius (e : A ≃ₐ[R] B)
    (hε : Coalgebra.counit (R := R) (A := B) ∘ₗ e.toLinearMap =
      Coalgebra.counit (R := R) (A := A)) :
    A ≃ₗc[R] B where
  __ := e.toLinearEquiv
  counit_comp := hε
  map_comp_comul := by
    ext a
    apply (Coalgebra.IsFrobenius.traceTensorEquiv R B).injective
    refine TensorProduct.ext' fun x y ↦ ?_
    have hε_apply (u : A) : Coalgebra.counit (R := R) (e u) = Coalgebra.counit (R := R) u :=
      congrFun (congrArg DFunLike.coe hε) u
    have hmap (t : A ⊗[R] A) :
        Coalgebra.IsFrobenius.traceTensorEquiv R B
            (TensorProduct.map e.toLinearMap e.toLinearMap t) (x ⊗ₜ[R] y) =
          Coalgebra.IsFrobenius.traceTensorEquiv R A t (e.symm x ⊗ₜ[R] e.symm y) := by
      induction t using TensorProduct.inductionOn with
      | tmul u v =>
        simp only [TensorProduct.map_tmul, AlgEquiv.toLinearMap_apply,
          Coalgebra.IsFrobenius.traceTensorEquiv_tmul]
        rw [← hε_apply (e.symm x * u), ← hε_apply (v * e.symm y), map_mul e, map_mul e,
          e.apply_symm_apply, e.apply_symm_apply]
      | add t u ht hu => simp_all
    simp only [LinearMap.comp_apply, AlgEquiv.toLinearEquiv_toLinearMap, AlgEquiv.toLinearMap_apply]
    rw [hmap, Coalgebra.IsFrobenius.traceTensorEquiv_comul,
      Coalgebra.IsFrobenius.traceTensorEquiv_comul, ← hε_apply, map_mul e, map_mul e,
      e.apply_symm_apply, e.apply_symm_apply]

/-- The underlying function of `toCoalgEquivOfIsFrobenius` is the algebra equivalence. -/
@[simp]
theorem coe_toCoalgEquivOfIsFrobenius (e : A ≃ₐ[R] B)
    (hε : Coalgebra.counit (R := R) (A := B) ∘ₗ e.toLinearMap =
      Coalgebra.counit (R := R) (A := A)) : ⇑(e.toCoalgEquivOfIsFrobenius hε) = e := (rfl)

/-- The underlying linear equivalence of `toCoalgEquivOfIsFrobenius` is `e.toLinearEquiv`. -/
@[simp]
theorem toLinearEquiv_toCoalgEquivOfIsFrobenius (e : A ≃ₐ[R] B)
    (hε : Coalgebra.counit (R := R) (A := B) ∘ₗ e.toLinearMap =
      Coalgebra.counit (R := R) (A := A)) :
    (e.toCoalgEquivOfIsFrobenius hε).toLinearEquiv = e.toLinearEquiv := (rfl)

/-- The inverse of `toCoalgEquivOfIsFrobenius` has `e.symm` as underlying function. -/
@[simp]
theorem coe_toCoalgEquivOfIsFrobenius_symm (e : A ≃ₐ[R] B)
    (hε : Coalgebra.counit (R := R) (A := B) ∘ₗ e.toLinearMap =
      Coalgebra.counit (R := R) (A := A)) :
    ⇑(e.toCoalgEquivOfIsFrobenius hε).symm = e.symm := (rfl)

end IsFrobenius

end AlgEquiv

/-! ### Tensor products and scalar extension of Frobenius coalgebras -/

namespace TensorProduct

section IsFrobenius

variable {R S A B : Type*} [CommSemiring R] [CommSemiring S] [Algebra R S]
  [NonUnitalNonAssocSemiring A] [Module R A] [Module S A] [IsScalarTower R S A]
  [SMulCommClass R S A] [SMulCommClass R A A] [IsScalarTower R A A]
  [SMulCommClass S A A] [IsScalarTower S A A]
  [NonUnitalNonAssocSemiring B] [Module R B] [SMulCommClass R B B] [IsScalarTower R B B]
  [CoalgebraStruct S A] [CoalgebraStruct R B]
  [Coalgebra.IsFrobenius S A] [Coalgebra.IsFrobenius R B]

/-- The heterobasic tensor product `A ⊗[R] B` of an `S`-Frobenius coalgebra `A` and an
`R`-Frobenius coalgebra `B` is an `S`-Frobenius coalgebra. Taking `S = R` gives the tensor product
of Frobenius algebras; taking `A = S` gives scalar extension `S ⊗[R] B`. -/
instance instIsFrobenius : Coalgebra.IsFrobenius S (A ⊗[R] B) := by
  constructor
  refine TensorProduct.ext' fun x y ↦ ?_
  let φ := AlgebraTensorModule.tensorTensorTensorComm R S R S A A B B
  induction x using TensorProduct.inductionOn with
  | add x₁ x₂ hx₁ hx₂ => simp only [add_tmul, map_add, hx₁, hx₂]
  | tmul a₁ b₁ =>
    induction y using TensorProduct.inductionOn with
    | add y₁ y₂ hy₁ hy₂ => simp only [tmul_add, map_add, hy₁, hy₂]
    | tmul a₂ b₂ =>
      have hleft : Coalgebra.IsFrobenius.left S (A ⊗[R] B)
            ((a₁ ⊗ₜ[R] b₁) ⊗ₜ[S] (a₂ ⊗ₜ[R] b₂)) =
          φ (Coalgebra.IsFrobenius.left S A (a₁ ⊗ₜ[S] a₂) ⊗ₜ[R]
            Coalgebra.IsFrobenius.left R B (b₁ ⊗ₜ[R] b₂)) := by
        simp only [Coalgebra.IsFrobenius.left_def, LinearMap.comp_apply, LinearMap.rTensor_tmul,
          TensorProduct.comul_tmul, LinearEquiv.coe_coe]
        induction Coalgebra.comul (R := S) a₁ using TensorProduct.inductionOn with
        | add u v hu hv => simp only [add_tmul, map_add, hu, hv]
        | tmul u₁ u₂ =>
          induction Coalgebra.comul (R := R) b₁ using TensorProduct.inductionOn with
          | add v w hv hw => simp only [tmul_add, add_tmul, map_add, hv, hw]
          | tmul v₁ v₂ => simp [φ]
      have hright : Coalgebra.IsFrobenius.right S (A ⊗[R] B)
            ((a₁ ⊗ₜ[R] b₁) ⊗ₜ[S] (a₂ ⊗ₜ[R] b₂)) =
          φ (Coalgebra.IsFrobenius.right S A (a₁ ⊗ₜ[S] a₂) ⊗ₜ[R]
            Coalgebra.IsFrobenius.right R B (b₁ ⊗ₜ[R] b₂)) := by
        simp only [Coalgebra.IsFrobenius.right_def, LinearMap.comp_apply, LinearMap.lTensor_tmul,
          TensorProduct.comul_tmul, LinearEquiv.coe_coe]
        induction Coalgebra.comul (R := S) a₂ using TensorProduct.inductionOn with
        | add u v hu hv => simp only [add_tmul, tmul_add, map_add, hu, hv]
        | tmul u₁ u₂ =>
          induction Coalgebra.comul (R := R) b₂ using TensorProduct.inductionOn with
          | add v w hv hw => simp only [tmul_add, map_add, hv, hw]
          | tmul v₁ v₂ => simp [φ]
      rw [hleft, hright, Coalgebra.IsFrobenius.left_eq_right (R := S) (A := A),
        Coalgebra.IsFrobenius.left_eq_right (R := R) (A := B)]

end IsFrobenius

end TensorProduct

/-! ### Trace-reconstructed Frobenius coalgebras under isomorphisms, tensor products, and
base change -/

namespace LinearMap

section AlgEquivTransport

variable {R A B : Type*} [CommSemiring R] [Semiring A] [Semiring B] [Algebra R A] [Algebra R B]

/-- Pulling back a linear functional along an algebra isomorphism preserves and reflects
perfectness of its trace pairing. -/
theorem isPerfPair_compr₂_mul_iff_of_algEquiv (e : A ≃ₐ[R] B) (ε : B →ₗ[R] R) :
    ((mul R A).compr₂ (ε ∘ₗ e.toLinearMap)).IsPerfPair ↔ ((mul R B).compr₂ ε).IsPerfPair := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · have hcomp : (mul R B).compr₂ ε =
        ((mul R A).compr₂ (ε ∘ₗ e.toLinearMap)).compl₁₂
          e.symm.toLinearMap e.symm.toLinearMap := by ext; simp
    rw [hcomp]
    exact IsPerfPair.compl₁₂ (p := (mul R A).compr₂ (ε ∘ₗ e.toLinearMap))
      e.symm.toLinearEquiv e.symm.toLinearEquiv
  · have hcomp : (mul R A).compr₂ (ε ∘ₗ e.toLinearMap) =
        ((mul R B).compr₂ ε).compl₁₂ e.toLinearMap e.toLinearMap := by ext; simp
    rw [hcomp]
    exact IsPerfPair.compl₁₂ (p := (mul R B).compr₂ ε) e.toLinearEquiv e.toLinearEquiv

end AlgEquivTransport

section CommAlgEquiv

variable {R A B : Type*} [CommSemiring R] [CommSemiring A] [CommSemiring B]
  [Algebra R A] [Algebra R B]

/-- Pairing a basis element with a trace-dual basis element yields the Kronecker delta. -/
@[simp]
theorem apply_mul_traceDualBasis {ι : Type*} [Finite ι] [DecidableEq ι]
    (ε : A →ₗ[R] R) [((mul R A).compr₂ ε).IsPerfPair]
    (b : Module.Basis ι R A) (i j : ι) :
    ε (b i * traceDualBasis ε b j) = if i = j then 1 else 0 := by
  rw [mul_comm, traceDualBasis_mul, b.repr_self, Finsupp.single_apply, eq_comm]

/-- Transporting a basis along an algebra isomorphism commutes with forming the trace-dual basis. -/
theorem traceDualBasis_map {ι : Type*} [Finite ι] (e : A ≃ₐ[R] B) (ε : B →ₗ[R] R)
    [((mul R B).compr₂ ε).IsPerfPair] [((mul R A).compr₂ (ε ∘ₗ e.toLinearMap)).IsPerfPair]
    (b : Module.Basis ι R A) :
    traceDualBasis ε (b.map e.toLinearEquiv) =
      (traceDualBasis (ε ∘ₗ e.toLinearMap) b).map e.toLinearEquiv := by
  ext i
  apply ((mul R B).compr₂ ε).toPerfPair.injective
  ext y
  simp only [toPerfPair_apply, compr₂_apply, mul_apply_apply, traceDualBasis_mul,
    Module.Basis.map_repr, LinearEquiv.trans_apply, Module.Basis.map_apply,
    AlgEquiv.coe_toLinearEquiv]
  change (b.repr (e.symm y)) i = _
  rw [← traceDualBasis_mul (ε ∘ₗ e.toLinearMap) b i (e.symm y), comp_apply,
    AlgEquiv.toLinearMap_apply, map_mul e, e.apply_symm_apply]

variable [Module.Finite R A] [Module.Projective R A] [Module.Finite R B] [Module.Projective R B]

/-- An algebra isomorphism intertwines the trace-reconstructed comultiplications of `ε ∘ e` and
`ε`. -/
theorem map_frobeniusCoalgebra_comul_of_algEquiv (e : A ≃ₐ[R] B) (ε : B →ₗ[R] R)
    [((mul R B).compr₂ ε).IsPerfPair] [((mul R A).compr₂ (ε ∘ₗ e.toLinearMap)).IsPerfPair]
    (a : A) :
    TensorProduct.map e.toLinearMap e.toLinearMap
        ((ε ∘ₗ e.toLinearMap).frobeniusCoalgebra.comul a) =
      ε.frobeniusCoalgebra.comul (e a) := by
  let := (ε ∘ₗ e.toLinearMap).frobeniusCoalgebra; let := ε.frobeniusCoalgebra
  have := (ε ∘ₗ e.toLinearMap).frobeniusCoalgebra_isFrobenius
  have := ε.frobeniusCoalgebra_isFrobenius
  exact congrFun (congrArg DFunLike.coe (e.toCoalgEquivOfIsFrobenius (by simp)).map_comp_comul) a

end CommAlgEquiv

end LinearMap

namespace AlgEquiv

variable {R A B : Type*} [CommSemiring R] [CommSemiring A] [CommSemiring B]
  [Algebra R A] [Algebra R B] [Module.Finite R A] [Module.Projective R A]
  [Module.Finite R B] [Module.Projective R B]

/-- An algebra isomorphism induces a coalgebra isomorphism between the trace-reconstructed
Frobenius coalgebras for `ε ∘ e` and `ε`. -/
def frobeniusCoalgEquiv (e : A ≃ₐ[R] B) (ε : B →ₗ[R] R)
    [((LinearMap.mul R B).compr₂ ε).IsPerfPair]
    [((LinearMap.mul R A).compr₂ (ε ∘ₗ e.toLinearMap)).IsPerfPair] :
    letI := (ε ∘ₗ e.toLinearMap).frobeniusCoalgebra
    letI := ε.frobeniusCoalgebra
    A ≃ₗc[R] B :=
  letI := (ε ∘ₗ e.toLinearMap).frobeniusCoalgebra
  letI := ε.frobeniusCoalgebra
  haveI := (ε ∘ₗ e.toLinearMap).frobeniusCoalgebra_isFrobenius
  haveI := ε.frobeniusCoalgebra_isFrobenius
  e.toCoalgEquivOfIsFrobenius (by simp)

/-- The underlying function of `frobeniusCoalgEquiv` is `e`. -/
@[simp]
theorem coe_frobeniusCoalgEquiv (e : A ≃ₐ[R] B) (ε : B →ₗ[R] R)
    [((LinearMap.mul R B).compr₂ ε).IsPerfPair]
    [((LinearMap.mul R A).compr₂ (ε ∘ₗ e.toLinearMap)).IsPerfPair] :
    ⇑(e.frobeniusCoalgEquiv ε) = e := by simp [frobeniusCoalgEquiv]

/-- The inverse of `frobeniusCoalgEquiv` has `e.symm` as underlying function. -/
@[simp]
theorem coe_frobeniusCoalgEquiv_symm (e : A ≃ₐ[R] B) (ε : B →ₗ[R] R)
    [((LinearMap.mul R B).compr₂ ε).IsPerfPair]
    [((LinearMap.mul R A).compr₂ (ε ∘ₗ e.toLinearMap)).IsPerfPair] :
    letI := (ε ∘ₗ e.toLinearMap).frobeniusCoalgebra
    letI := ε.frobeniusCoalgebra
    ⇑(e.frobeniusCoalgEquiv ε).symm = e.symm := by simp [frobeniusCoalgEquiv]

end AlgEquiv

namespace LinearMap

section HeterobasicTensor

variable {R S A B : Type*} [CommSemiring R] [CommSemiring S] [Algebra R S]
  [CommSemiring A] [Algebra R A] [Algebra S A] [IsScalarTower R S A]
  [CommSemiring B] [Algebra R B]
  [Module.Finite S A] [Module.Projective S A] [Module.Finite R B] [Module.Projective R B]
  (εA : A →ₗ[S] S) (εB : B →ₗ[R] R)
  [((mul S A).compr₂ εA).IsPerfPair] [((mul R B).compr₂ εB).IsPerfPair]

/-- The heterobasic tensor product of two perfect traces is a perfect trace on `A ⊗[R] B`. -/
theorem isPerfPair_compr₂_mul_algebraTensorModule_dualDistrib :
    ((mul S (A ⊗[R] B)).compr₂
      (TensorProduct.AlgebraTensorModule.dualDistrib R S A B (εA ⊗ₜ[R] εB))).IsPerfPair := by
  let : Coalgebra S A := εA.frobeniusCoalgebra; let : Coalgebra R B := εB.frobeniusCoalgebra
  have := εA.frobeniusCoalgebra_isFrobenius; have := εB.frobeniusCoalgebra_isFrobenius
  have hcounit : Coalgebra.counit (R := S) (A := A ⊗[R] B) =
      TensorProduct.AlgebraTensorModule.dualDistrib R S A B (εA ⊗ₜ[R] εB) :=
    TensorProduct.AlgebraTensorModule.ext fun _ _ ↦ by
      simp [TensorProduct.AlgebraTensorModule.dualDistrib_apply, Coalgebra.counit]
  rw [← hcounit]
  exact Coalgebra.IsFrobenius.isPerfPair_compr₂_mul_counit

/-- On a heterobasic tensor product `A ⊗[R] B`, the Frobenius coalgebra reconstructed from the
tensor-product trace equals the tensor product of the reconstructed Frobenius coalgebras. -/
theorem frobeniusCoalgebra_algebraTensorModule_dualDistrib [Module.Finite S (A ⊗[R] B)]
    [((mul S (A ⊗[R] B)).compr₂
      (TensorProduct.AlgebraTensorModule.dualDistrib R S A B (εA ⊗ₜ[R] εB))).IsPerfPair] :
    (TensorProduct.AlgebraTensorModule.dualDistrib R S A B (εA ⊗ₜ[R] εB)).frobeniusCoalgebra =
      (letI := εA.frobeniusCoalgebra; letI := εB.frobeniusCoalgebra;
        TensorProduct.instCoalgebra (R := R) (S := S) (A := A) (B := B)) := by
  let : Coalgebra S A := εA.frobeniusCoalgebra; let : Coalgebra R B := εB.frobeniusCoalgebra
  have := εA.frobeniusCoalgebra_isFrobenius; have := εB.frobeniusCoalgebra_isFrobenius
  exact frobeniusCoalgebra_eq _ _
    (TensorProduct.AlgebraTensorModule.ext fun _ _ ↦ by
      simp [TensorProduct.AlgebraTensorModule.dualDistrib_apply, Coalgebra.counit])
    inferInstance

end HeterobasicTensor

section TensorProduct

variable {R A B : Type*} [CommSemiring R] [CommSemiring A] [CommSemiring B]
  [Algebra R A] [Algebra R B]
  [Module.Finite R A] [Module.Projective R A] [Module.Finite R B] [Module.Projective R B]
  (εA : A →ₗ[R] R) (εB : B →ₗ[R] R)
  [((mul R A).compr₂ εA).IsPerfPair] [((mul R B).compr₂ εB).IsPerfPair]

/-- The tensor product of two perfect traces on finite projective commutative `R`-algebras is a
perfect trace on `A ⊗[R] B`. -/
instance isPerfPair_compr₂_mul_dualDistrib :
    ((mul R (A ⊗[R] B)).compr₂ (TensorProduct.dualDistrib R A B (εA ⊗ₜ[R] εB))).IsPerfPair := by
  have heq : TensorProduct.dualDistrib R A B (εA ⊗ₜ[R] εB) =
      TensorProduct.AlgebraTensorModule.dualDistrib R R A B (εA ⊗ₜ[R] εB) := by
    ext a b; simp [mul_comm]
  rw [heq]
  exact isPerfPair_compr₂_mul_algebraTensorModule_dualDistrib εA εB

/-- The Frobenius coalgebra reconstructed from the tensor product of two perfect traces is the
tensor product of the reconstructed Frobenius coalgebras. -/
theorem frobeniusCoalgebra_dualDistrib :
    (TensorProduct.dualDistrib R A B (εA ⊗ₜ[R] εB)).frobeniusCoalgebra =
      (letI := εA.frobeniusCoalgebra; letI := εB.frobeniusCoalgebra;
        TensorProduct.instCoalgebra (R := R) (S := R) (A := A) (B := B)) := by
  let : Coalgebra R A := εA.frobeniusCoalgebra; let : Coalgebra R B := εB.frobeniusCoalgebra
  have := εA.frobeniusCoalgebra_isFrobenius; have := εB.frobeniusCoalgebra_isFrobenius
  exact frobeniusCoalgebra_eq _ _ (by ext a b; simp [Coalgebra.counit, mul_comm]) inferInstance

omit [Module.Finite R A] [Module.Projective R A] [Module.Finite R B] [Module.Projective R B] in
/-- The trace-dual basis of a tensor product of bases is the tensor product of the trace-dual
bases. -/
theorem traceDualBasis_dualDistrib {ι κ : Type*} [Finite ι] [Finite κ]
    [((mul R (A ⊗[R] B)).compr₂ (TensorProduct.dualDistrib R A B (εA ⊗ₜ[R] εB))).IsPerfPair]
    (bA : Module.Basis ι R A) (bB : Module.Basis κ R B) :
    traceDualBasis (TensorProduct.dualDistrib R A B (εA ⊗ₜ[R] εB)) (bA.tensorProduct bB) =
      (traceDualBasis εA bA).tensorProduct (traceDualBasis εB bB) := by
  ext ⟨i, j⟩
  apply ((mul R (A ⊗[R] B)).compr₂
    (TensorProduct.dualDistrib R A B (εA ⊗ₜ[R] εB))).toPerfPair.injective
  refine TensorProduct.ext' fun x y ↦ ?_
  simp only [toPerfPair_apply, compr₂_apply, mul_apply_apply]
  rw [traceDualBasis_mul, Module.Basis.tensorProduct_apply, Algebra.TensorProduct.tmul_mul_tmul,
    TensorProduct.dualDistrib_apply, traceDualBasis_mul, traceDualBasis_mul,
    Module.Basis.tensorProduct_repr_tmul_apply, smul_eq_mul, mul_comm]

end TensorProduct

section BaseChange

variable {R : Type*} (S : Type*) {A : Type*} [CommSemiring R] [CommSemiring S] [Algebra R S]
  [CommSemiring A] [Algebra R A] [Module.Finite R A] [Module.Projective R A]
  (ε : A →ₗ[R] R) [((mul R A).compr₂ ε).IsPerfPair]

/-- Extending scalars preserves perfectness of a trace on a finite projective commutative
algebra. -/
instance isPerfPair_compr₂_mul_baseChange :
    ((mul S (S ⊗[R] A)).compr₂ (Module.Dual.baseChange S ε)).IsPerfPair := by
  have : ((mul S S).compr₂ (LinearMap.id (R := S) (M := S))).IsPerfPair :=
    Coalgebra.IsFrobenius.isPerfPair_compr₂_mul_counit (R := S) (A := S)
  have heq : Module.Dual.baseChange S ε =
      TensorProduct.AlgebraTensorModule.dualDistrib R S S A
        ((LinearMap.id (R := S) (M := S)) ⊗ₜ[R] ε) :=
    TensorProduct.AlgebraTensorModule.ext fun _ _ ↦ rfl
  rw [heq]
  exact isPerfPair_compr₂_mul_algebraTensorModule_dualDistrib (LinearMap.id (R := S) (M := S)) ε

/-- The Frobenius coalgebra reconstructed from a base-changed trace `Module.Dual.baseChange S ε` is
the base change of the Frobenius coalgebra reconstructed from `ε`. -/
theorem frobeniusCoalgebra_baseChange :
    (Module.Dual.baseChange S ε).frobeniusCoalgebra =
      (letI := ε.frobeniusCoalgebra;
        TensorProduct.instCoalgebra (R := R) (S := S) (A := S) (B := A)) := by
  let : Coalgebra R A := ε.frobeniusCoalgebra
  have := ε.frobeniusCoalgebra_isFrobenius
  exact frobeniusCoalgebra_eq _ _
    (TensorProduct.AlgebraTensorModule.ext fun _ _ ↦ by simp [Coalgebra.counit]) inferInstance

omit [Module.Finite R A] [Module.Projective R A] in
/-- Base change of a finite basis commutes with forming the trace-dual basis. -/
theorem traceDualBasis_baseChange {ι : Type*} [Finite ι]
    [((mul S (S ⊗[R] A)).compr₂ (Module.Dual.baseChange S ε)).IsPerfPair]
    (b : Module.Basis ι R A) :
    traceDualBasis (Module.Dual.baseChange S ε) (b.baseChange S) =
      (traceDualBasis ε b).baseChange S := by
  ext i
  apply ((mul S (S ⊗[R] A)).compr₂ (Module.Dual.baseChange S ε)).toPerfPair.injective
  refine TensorProduct.AlgebraTensorModule.ext fun s a ↦ ?_
  simp only [toPerfPair_apply, compr₂_apply, mul_apply_apply]
  rw [traceDualBasis_mul, Module.Basis.baseChange_apply, Algebra.TensorProduct.tmul_mul_tmul,
    one_mul, Module.Dual.baseChange_apply_tmul, traceDualBasis_mul,
    Module.Basis.baseChange_repr_tmul, Algebra.smul_def, mul_comm]

end BaseChange

end LinearMap
