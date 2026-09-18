/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.TransferInstance
public import Mathlib.RingTheory.Binomial
public import TauCeti.Algebra.Module.GradedModule.Opposite

/-!
# The Koszul-signed opposite of an internally graded algebra

For an internally `ℤ`-graded algebra `A`, its graded opposite has the same underlying graded
module and the multiplication

`op a * op b = (-1) ^ (p * q) • op (b * a)`

when `a` and `b` have degrees `p` and `q`.  The sign is essential for differentials and higher
graded operations; Mathlib's ordinary `MulOpposite` reverses multiplication without it.

The construction transports the ordinary opposite ring structure through the involution which
multiplies degree `p` by `(-1) ^ (p choose 2)`.  The binomial identity
`(p + q choose 2) = (p choose 2) + (q choose 2) + p*q` gives exactly the Koszul sign in the
transported product.  This avoids choosing degrees for nonhomogeneous elements and makes
associativity follow from transport.

## Main definitions

* `InternalGrading.quadraticTwist`: multiplication of degree `p` by
  `(-1) ^ (p choose 2)`.
* `GradedOpposite G`: the Koszul-signed opposite algebra associated to an internal grading `G`.
* `GradedOpposite.op` and `GradedOpposite.unop`: the additive, degree-preserving passage between
  an algebra and its graded opposite.

## Main results

* `GradedOpposite.op_mul`: the signed reversed-product formula on homogeneous elements.
* `GradedOpposite.op_mem_piece_iff`: `op` preserves degree.

The convention follows B. Keller, *Introduction to A-infinity algebras and modules*, Sections 3
and 7.
-/

public section

open scoped DirectSum

namespace TauCeti

universe uR uA uM

namespace InternalGrading

section QuadraticTwist

variable {R : Type uR} {M : Type uM}
  [CommRing R] [AddCommMonoid M] [Module R M]

/-- The quadratic sign exponent attached to degree `p`, namely the generalized binomial
coefficient `p choose 2`. -/
def quadraticExponent (p : ℤ) : ℤ := Ring.choose p 2

/-- The quadratic exponent turns addition into addition plus the bilinear cross term. -/
theorem quadraticExponent_add (p q : ℤ) :
    quadraticExponent (p + q) = quadraticExponent p + quadraticExponent q + p * q := by
  rw [quadraticExponent, quadraticExponent, quadraticExponent,
    Ring.add_choose_eq 2 (Commute.all _ _)]
  norm_num [Finset.antidiagonal]
  ring

/-- The signs associated to the quadratic exponent differ under addition by the Koszul sign. -/
theorem negOnePow_quadraticExponent_add (p q : ℤ) :
    (quadraticExponent (p + q)).negOnePow =
      (p * q).negOnePow * (quadraticExponent p).negOnePow *
        (quadraticExponent q).negOnePow := by
  rw [quadraticExponent_add, Int.negOnePow_add, Int.negOnePow_add]
  ac_rfl

/-- The quadratic twist multiplies the degree-`p` component by `(-1) ^ (p choose 2)`.

Transporting the ordinary opposite multiplication through this involution produces the
Koszul-signed opposite multiplication. -/
noncomputable def quadraticTwist (G : InternalGrading R M) : M →ₗ[R] M :=
  DirectSum.coeLinearMap (fun p => G.piece p) ∘ₗ
    DirectSum.toModule R ℤ (⨁ p : ℤ, G.piece p)
      (fun p => (((quadraticExponent p).negOnePow : ℤ) : R) •
        DirectSum.lof R ℤ (fun p => G.piece p) p) ∘ₗ
    (DirectSum.decomposeLinearEquiv (ℳ := G.piece)).toLinearMap

/-- On a homogeneous element of degree `p`, the quadratic twist is multiplication by
`(-1) ^ (p choose 2)`. -/
theorem quadraticTwist_apply_of_mem (G : InternalGrading R M) {x : M} {p : ℤ}
    (hx : x ∈ G.piece p) :
    G.quadraticTwist x = (((quadraticExponent p).negOnePow : ℤ) : R) • x := by
  rw [quadraticTwist]
  simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
    DirectSum.decomposeLinearEquiv_apply]
  rw [DirectSum.decompose_of_mem (ℳ := G.piece) hx,
    ← DirectSum.lof_eq_of R ℤ (fun i : ℤ => G.piece i)]
  simp [DirectSum.toModule_lof]

/-- The quadratic twist preserves every homogeneous piece. -/
theorem quadraticTwist_mem_piece (G : InternalGrading R M) {x : M} {p : ℤ}
    (hx : x ∈ G.piece p) : G.quadraticTwist x ∈ G.piece p := by
  rw [G.quadraticTwist_apply_of_mem hx]
  exact Submodule.smul_mem _ _ hx

/-- Applying the quadratic twist twice is the identity. -/
theorem quadraticTwist_involutive (G : InternalGrading R M) :
    Function.Involutive G.quadraticTwist :=
  fun x => by
    have hmaps : G.quadraticTwist ∘ₗ G.quadraticTwist = LinearMap.id := by
      apply G.linearMap_ext
      intro p y hy
      simp only [LinearMap.comp_apply, LinearMap.id_apply]
      rw [G.quadraticTwist_apply_of_mem hy, map_smul, G.quadraticTwist_apply_of_mem hy,
        smul_smul]
      rw [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self]
      simp
    exact LinearMap.congr_fun hmaps x

/-- The quadratic twist as a linear involution. -/
noncomputable def quadraticTwistEquiv (G : InternalGrading R M) : M ≃ₗ[R] M :=
  LinearEquiv.ofInvolutive G.quadraticTwist G.quadraticTwist_involutive

@[simp]
theorem quadraticTwistEquiv_apply (G : InternalGrading R M) (x : M) :
    G.quadraticTwistEquiv x = G.quadraticTwist x := by
  exact congr_fun (LinearEquiv.coe_ofInvolutive G.quadraticTwist
    G.quadraticTwist_involutive) x

@[simp]
theorem quadraticTwistEquiv_symm_apply (G : InternalGrading R M) (x : M) :
    G.quadraticTwistEquiv.symm x = G.quadraticTwist x := by
  rfl

end QuadraticTwist

end InternalGrading

/-- The Koszul-signed opposite of the internally graded algebra `A`.

Its carrier is a copy of the ordinary opposite; its multiplication below includes the Koszul
sign. -/
structure GradedOpposite {R : Type uR} {A : Type uA} [CommRing R] [Ring A] [Algebra R A]
    (_G : InternalGrading R A) where
  /-- The underlying element in the ordinary multiplicative opposite. -/
  toMulOpposite : Aᵐᵒᵖ

namespace GradedOpposite

variable {R : Type uR} {A : Type uA} [CommRing R] [Ring A] [Algebra R A]

/-- The underlying type equivalence from the graded opposite to the ordinary opposite. -/
def toMulOppositeEquiv (G : InternalGrading R A) : GradedOpposite G ≃ Aᵐᵒᵖ where
  toFun := toMulOpposite
  invFun := fun x => ⟨x⟩
  left_inv x := by cases x; rfl
  right_inv _ := rfl

/-- The equivalence used to transport the ordinary opposite algebra structure.  It applies the
quadratic sign twist after forgetting that the source has graded-opposite multiplication. -/
noncomputable def transportEquiv (G : InternalGrading R A) : GradedOpposite G ≃ Aᵐᵒᵖ :=
  (toMulOppositeEquiv G).trans G.opposite.quadraticTwistEquiv.toEquiv

noncomputable instance instRing (G : InternalGrading R A) : Ring (GradedOpposite G) :=
  (transportEquiv G).ring

noncomputable instance instAlgebra (G : InternalGrading R A) : Algebra R (GradedOpposite G) :=
  Equiv.algebra R (transportEquiv G)

/-- The transport equivalence is an algebra equivalence to the ordinary opposite. -/
noncomputable def transportAlgEquiv (G : InternalGrading R A) :
  GradedOpposite G ≃ₐ[R] Aᵐᵒᵖ :=
  Equiv.algEquiv R (transportEquiv G)

/-- Regard an element as an element of the graded opposite. -/
def op (G : InternalGrading R A) (a : A) : GradedOpposite G := ⟨MulOpposite.op a⟩

/-- Return an element of the graded opposite to the original algebra. -/
def unop (G : InternalGrading R A) (a : GradedOpposite G) : A := a.toMulOpposite.unop

/-- The transport algebra equivalence sends a raw opposite element to its quadratic twist. -/
@[simp]
theorem transportAlgEquiv_op (G : InternalGrading R A) (a : A) :
    transportAlgEquiv G (op G a) =
      G.opposite.quadraticTwist (MulOpposite.op a) := by
  rw [transportAlgEquiv, Equiv.algEquiv_apply]
  simp [transportEquiv, toMulOppositeEquiv, op]

@[simp]
theorem unop_op (G : InternalGrading R A) (a : A) : unop G (op G a) = a := by
  simp [unop, op]

@[simp]
theorem op_unop (G : InternalGrading R A) (a : GradedOpposite G) : op G (unop G a) = a := by
  cases a
  rfl

/-- Passage to the graded opposite is an `R`-linear equivalence. -/
noncomputable def opLinearEquiv (G : InternalGrading R A) : A ≃ₗ[R] GradedOpposite G where
  toFun := op G
  invFun := unop G
  left_inv := unop_op G
  right_inv := op_unop G
  map_add' x y := by
    apply (transportAlgEquiv G).injective
    rw [map_add]
    simp only [transportAlgEquiv_op]
    rw [MulOpposite.op_add, map_add]
  map_smul' r x := by
    apply (transportAlgEquiv G).injective
    rw [map_smul]
    simp only [transportAlgEquiv_op, RingHom.id_apply]
    rw [MulOpposite.op_smul, map_smul]

@[simp]
theorem opLinearEquiv_apply (G : InternalGrading R A) (a : A) :
    opLinearEquiv G a = op G a := (rfl)

@[simp]
theorem opLinearEquiv_symm_apply (G : InternalGrading R A) (a : GradedOpposite G) :
    (opLinearEquiv G).symm a = unop G a := (rfl)

/-- The grading on the signed opposite, transported degreewise by `op`. -/
noncomputable def grading (G : InternalGrading R A) : InternalGrading R (GradedOpposite G) :=
  G.map (opLinearEquiv G)

/-- An element belongs to degree `p` of the graded opposite exactly when its underlying element
belongs to degree `p` in the original algebra. -/
@[simp]
theorem op_mem_piece_iff (G : InternalGrading R A) (p : ℤ) (a : A) :
    op G a ∈ (grading G).piece p ↔ a ∈ G.piece p := by
  simp [grading]

/-- Membership in a graded-opposite piece can be tested after applying `unop`. -/
@[simp]
theorem mem_piece_iff (G : InternalGrading R A) (p : ℤ) (a : GradedOpposite G) :
    a ∈ (grading G).piece p ↔ unop G a ∈ G.piece p := by
  simpa only [op_unop G a] using op_mem_piece_iff G p (unop G a)

@[simp]
theorem op_zero (G : InternalGrading R A) : op G (0 : A) = 0 :=
  (opLinearEquiv G).map_zero

@[simp]
theorem op_add (G : InternalGrading R A) (a b : A) : op G (a + b) = op G a + op G b :=
  (opLinearEquiv G).map_add a b

@[simp]
theorem op_smul (G : InternalGrading R A) (r : R) (a : A) : op G (r • a) = r • op G a :=
  (opLinearEquiv G).map_smul r a

@[simp]
theorem op_zsmul (G : InternalGrading R A) (n : ℤ) (a : A) : op G (n • a) = n • op G a :=
  map_zsmul (opLinearEquiv G) n a

@[simp]
theorem unop_zero (G : InternalGrading R A) : unop G (0 : GradedOpposite G) = 0 :=
  (opLinearEquiv G).symm.map_zero

@[simp]
theorem unop_add (G : InternalGrading R A) (a b : GradedOpposite G) :
    unop G (a + b) = unop G a + unop G b :=
  (opLinearEquiv G).symm.map_add a b

@[simp]
theorem unop_smul (G : InternalGrading R A) (r : R) (a : GradedOpposite G) :
    unop G (r • a) = r • unop G a :=
  (opLinearEquiv G).symm.map_smul r a

@[simp]
theorem unop_zsmul (G : InternalGrading R A) (n : ℤ) (a : GradedOpposite G) :
    unop G (n • a) = n • unop G a :=
  map_zsmul (opLinearEquiv G).symm n a

section Multiplication

variable (G : InternalGrading R A) [SetLike.GradedMonoid G.piece]

/-- The unit of the graded opposite is the image of the original unit. -/
@[simp]
theorem op_one : op G (1 : A) = 1 := by
  apply (transportAlgEquiv G).injective
  rw [map_one, transportAlgEquiv_op,
    G.opposite.quadraticTwist_apply_of_mem (G.op_mem_opposite_piece_iff 0 1 |>.2
      (SetLike.one_mem_graded G.piece))]
  simp [InternalGrading.quadraticExponent]

@[simp]
theorem unop_one : unop G (1 : GradedOpposite G) = 1 := by
  rw [← op_one G, unop_op]

/-- Multiplication in the graded opposite reverses homogeneous factors and inserts their Koszul
sign. -/
theorem op_mul {p q : ℤ} {a b : A} (ha : a ∈ G.piece p) (hb : b ∈ G.piece q) :
    op G a * op G b = (p * q).negOnePow • op G (b * a) := by
  rw [Units.smul_def]
  apply (transportAlgEquiv G).injective
  rw [map_mul, map_zsmul, transportAlgEquiv_op, transportAlgEquiv_op,
    G.opposite.quadraticTwist_apply_of_mem (G.op_mem_opposite_piece_iff p a |>.2 ha),
    G.opposite.quadraticTwist_apply_of_mem (G.op_mem_opposite_piece_iff q b |>.2 hb),
    transportAlgEquiv_op]
  have hba : b * a ∈ G.piece (p + q) := by
    rw [add_comm]
    exact SetLike.mul_mem_graded hb ha
  rw [G.opposite.quadraticTwist_apply_of_mem
    (G.op_mem_opposite_piece_iff (p + q) (b * a) |>.2 hba)]
  simp only [Algebra.smul_mul_assoc, Algebra.mul_smul_comm, ← MulOpposite.op_mul,
    ← Int.cast_smul_eq_zsmul R, smul_smul]
  apply congrArg (· • MulOpposite.op (b * a))
  simp only [← mul_assoc, ← Int.cast_mul, ← Units.val_mul,
    InternalGrading.negOnePow_quadraticExponent_add]
  have hsign : (p * q).negOnePow * (p * q).negOnePow = (1 : ℤˣ) :=
    Int.units_mul_self _
  rw [hsign, one_mul]
  congr 1
  ac_rfl

/-- Returning a homogeneous product from the graded opposite reverses its factors and retains the
Koszul sign. -/
theorem unop_mul {p q : ℤ} {a b : GradedOpposite G}
    (ha : a ∈ (grading G).piece p) (hb : b ∈ (grading G).piece q) :
    unop G (a * b) = (p * q).negOnePow • (unop G b * unop G a) := by
  have h := op_mul G ((mem_piece_iff G p a).1 ha) ((mem_piece_iff G q b).1 hb)
  rw [op_unop, op_unop] at h
  have key := congrArg (unop G) h
  simpa only [Units.smul_def, unop_zsmul, unop_op] using key

/-- The homogeneous pieces of a graded opposite are closed under its signed multiplication. -/
noncomputable instance instGradedMonoid : SetLike.GradedMonoid (grading G).piece where
  one_mem := by
    rw [← op_one G, op_mem_piece_iff]
    exact SetLike.one_mem_graded G.piece
  mul_mem := by
    intro p q x y hx hy
    rw [← op_unop G x, ← op_unop G y]
    rw [op_mul G ((mem_piece_iff G p x).1 hx) ((mem_piece_iff G q y).1 hy)]
    rw [Units.smul_def]
    exact ((grading G).piece (p + q)).toAddSubgroup.zsmul_mem
      ((op_mem_piece_iff G (p + q) _).2 <| by
      rw [add_comm]
      exact SetLike.mul_mem_graded ((mem_piece_iff G q y).1 hy)
        ((mem_piece_iff G p x).1 hx)) _

/-- The signed opposite is internally graded by the same degrees as the original algebra. -/
noncomputable instance instGradedAlgebra : GradedAlgebra (grading G).piece :=
  (grading G).isInternal.gradedAlgebra

end Multiplication

end GradedOpposite

end TauCeti
