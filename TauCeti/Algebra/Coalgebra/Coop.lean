/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Coalgebra.Basic
public import Mathlib.Algebra.Algebra.Equiv
public import Mathlib.Algebra.Module.Equiv.Opposite

/-!
# Co-opposite coalgebras

For an `R`-coalgebra `A`, the co-opposite `TauCeti.Coop A` carries the same `R`-module (and, when
present, `R`-algebra) structure as `A`, with the same counit and the reversed comultiplication
`Δᶜᵒᵖ = τ ∘ Δ`.

## Main declarations

* `TauCeti.Coop`: the co-opposite type wrapper.
* `TauCeti.Coop.linearEquiv`, `TauCeti.Coop.unopLinearEquiv`, `TauCeti.Coop.algEquiv`: canonical
  equivalences `Coop A ≃ A` and `(Coop A)ᵐᵒᵖ ≃ A`.
* `TauCeti.Coop.instCoalgebra`, `TauCeti.Coop.instIsCocomm`: coalgebra instances on `Coop A`.
* `TauCeti.Coop.comul_mk`, `TauCeti.Coop.counit_mk`, `TauCeti.Coop.comul_linearEquiv`: simp and
  transport lemmas for the co-opposite coalgebra operations.
* `Coalgebra.Repr.coop`: reverses the legs of a finite coproduct representation.
-/

public section

open scoped TensorProduct

namespace TauCeti

universe u v

/-- The co-opposite of a coalgebra (or bialgebra), keeping the algebra operations unchanged while
reversing the order of comultiplication (`Δᶜᵒᵖ = τ ∘ Δ`). -/
structure Coop (A : Type v) : Type v where
  /-- Wraps an element of `A` as an element of `Coop A`. -/
  mk ::
  /-- Unwraps an element of `Coop A` back into `A`. -/
  val : A

namespace Coop

variable {R : Type u} {A : Type v}

@[ext]
theorem ext {x y : Coop A} (h : x.val = y.val) : x = y := by
  cases x; cases y; congr

@[simp]
theorem val_mk (a : A) : (mk a).val = a :=
  rfl

@[simp]
theorem mk_val (x : Coop A) : mk x.val = x :=
  rfl

theorem val_injective : Function.Injective (@val A) := fun _ _ h ↦ ext h

theorem mk_injective : Function.Injective (@mk A) := fun _ _ h ↦ congrArg val h

theorem val_surjective : Function.Surjective (@val A) := fun a ↦ ⟨mk a, rfl⟩

theorem mk_surjective : Function.Surjective (@mk A) := fun x ↦ ⟨x.val, rfl⟩

variable (A) in
/-- The underlying bijection `Coop A ≃ A`. -/
def equiv : Coop A ≃ A where
  toFun := val
  invFun := mk
  left_inv _ := rfl
  right_inv _ := rfl

@[simp]
theorem equiv_apply (x : Coop A) : equiv A x = x.val := by
  rfl

@[simp]
theorem equiv_symm_apply (a : A) : (equiv A).symm a = mk a := by
  rfl

section Operations

instance [Zero A] : Zero (Coop A) where zero := ⟨0⟩
instance [One A] : One (Coop A) where one := ⟨1⟩
instance [Add A] : Add (Coop A) where add x y := ⟨x.val + y.val⟩
instance [Neg A] : Neg (Coop A) where neg x := ⟨-x.val⟩
instance [Sub A] : Sub (Coop A) where sub x y := ⟨x.val - y.val⟩
instance [Mul A] : Mul (Coop A) where mul x y := ⟨x.val * y.val⟩
instance [SMul R A] : SMul R (Coop A) where smul r x := ⟨r • x.val⟩
instance [Pow A ℕ] : Pow (Coop A) ℕ where pow x n := ⟨x.val ^ n⟩
instance [NatCast A] : NatCast (Coop A) where natCast n := ⟨n⟩
instance [IntCast A] : IntCast (Coop A) where intCast n := ⟨n⟩

@[simp] theorem val_zero [Zero A] : (0 : Coop A).val = 0 := rfl
@[simp] theorem mk_zero [Zero A] : mk (0 : A) = 0 := rfl
@[simp] theorem val_one [One A] : (1 : Coop A).val = 1 := rfl
@[simp] theorem mk_one [One A] : mk (1 : A) = 1 := rfl
@[simp] theorem val_add [Add A] (x y : Coop A) : (x + y).val = x.val + y.val := rfl
@[simp] theorem mk_add [Add A] (a b : A) : mk (a + b) = mk a + mk b := rfl
@[simp] theorem val_neg [Neg A] (x : Coop A) : (-x).val = -x.val := rfl
@[simp] theorem mk_neg [Neg A] (a : A) : mk (-a) = -mk a := rfl
@[simp] theorem val_sub [Sub A] (x y : Coop A) : (x - y).val = x.val - y.val := rfl
@[simp] theorem mk_sub [Sub A] (a b : A) : mk (a - b) = mk a - mk b := rfl
@[simp] theorem val_mul [Mul A] (x y : Coop A) : (x * y).val = x.val * y.val := rfl
@[simp] theorem mk_mul [Mul A] (a b : A) : mk (a * b) = mk a * mk b := rfl
@[simp] theorem val_smul [SMul R A] (r : R) (x : Coop A) : (r • x).val = r • x.val := rfl
@[simp] theorem mk_smul [SMul R A] (r : R) (a : A) : mk (r • a) = r • mk a := rfl
@[simp] theorem val_pow [Pow A ℕ] (x : Coop A) (n : ℕ) : (x ^ n).val = x.val ^ n := rfl
@[simp] theorem mk_pow [Pow A ℕ] (a : A) (n : ℕ) : mk (a ^ n) = mk a ^ n := rfl
@[simp] theorem val_natCast [NatCast A] (n : ℕ) : (n : Coop A).val = n := rfl
@[simp] theorem mk_natCast [NatCast A] (n : ℕ) : mk (n : A) = n := rfl
@[simp] theorem val_intCast [IntCast A] (n : ℤ) : (n : Coop A).val = n := rfl
@[simp] theorem mk_intCast [IntCast A] (n : ℤ) : mk (n : A) = n := rfl

end Operations

section AlgebraicInstances

instance instAddCommMonoid [AddCommMonoid A] : AddCommMonoid (Coop A) :=
  fast_instance% val_injective.addCommMonoid val rfl (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)

instance instAddCommGroup [AddCommGroup A] : AddCommGroup (Coop A) :=
  fast_instance% val_injective.addCommGroup val rfl (fun _ _ ↦ rfl) (fun _ ↦ rfl) (fun _ _ ↦ rfl)
    (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)

instance instModule [Semiring R] [AddCommMonoid A] [Module R A] : Module R (Coop A) :=
  fast_instance% val_injective.module R ⟨⟨val, rfl⟩, fun _ _ ↦ rfl⟩ (fun _ _ ↦ rfl)

instance instSemiring [Semiring A] : Semiring (Coop A) :=
  fast_instance% val_injective.semiring val rfl rfl (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)
    (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) (fun _ ↦ rfl)

instance instRing [Ring A] : Ring (Coop A) :=
  fast_instance% val_injective.ring val rfl rfl (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) (fun _ ↦ rfl)
    (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) (fun _ ↦ rfl) (fun _ ↦ rfl)

instance instCommSemiring [CommSemiring A] : CommSemiring (Coop A) :=
  fast_instance% val_injective.commSemiring val rfl rfl (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)
    (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) (fun _ ↦ rfl)

instance instCommRing [CommRing A] : CommRing (Coop A) :=
  fast_instance% val_injective.commRing val rfl rfl (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) (fun _ ↦ rfl)
    (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) (fun _ ↦ rfl) (fun _ ↦ rfl)

instance instAlgebra [CommSemiring R] [Semiring A] [Algebra R A] : Algebra R (Coop A) where
  algebraMap :=
    { toFun r := mk (algebraMap R A r)
      map_one' := ext (map_one _)
      map_mul' _ _ := ext (map_mul _ _ _)
      map_zero' := ext (map_zero _)
      map_add' _ _ := ext (map_add _ _ _) }
  commutes' r x := ext (Algebra.commutes r x.val)
  smul_def' r x := ext (Algebra.smul_def r x.val)

@[simp]
theorem val_algebraMap [CommSemiring R] [Semiring A] [Algebra R A] (r : R) :
    (algebraMap R (Coop A) r).val = algebraMap R A r :=
  rfl

@[simp]
theorem mk_algebraMap [CommSemiring R] [Semiring A] [Algebra R A] (r : R) :
    mk (algebraMap R A r) = algebraMap R (Coop A) r :=
  rfl

variable (A) in
/-- `Coop.val` as an additive equivalence `Coop A ≃+ A`. -/
def addEquiv [Add A] : Coop A ≃+ A where
  __ := equiv A
  map_add' _ _ := rfl

@[simp] theorem addEquiv_apply [Add A] (x : Coop A) : addEquiv A x = x.val := by rfl
@[simp] theorem addEquiv_symm_apply [Add A] (a : A) : (addEquiv A).symm a = mk a := by rfl

variable (R A) in
/-- `Coop.val` as an `R`-linear equivalence `Coop A ≃ₗ[R] A`. -/
def linearEquiv [Semiring R] [AddCommMonoid A] [Module R A] : Coop A ≃ₗ[R] A where
  __ := addEquiv A
  map_smul' _ _ := rfl

@[simp]
theorem linearEquiv_apply [Semiring R] [AddCommMonoid A] [Module R A] (x : Coop A) :
    linearEquiv R A x = x.val := by
  rfl

@[simp]
theorem linearEquiv_symm_apply [Semiring R] [AddCommMonoid A] [Module R A] (a : A) :
    (linearEquiv R A).symm a = mk a := by
  rfl

variable (R A) in
/-- The canonical `R`-linear equivalence `(Coop A)ᵐᵒᵖ ≃ₗ[R] A`. -/
def unopLinearEquiv [Semiring R] [AddCommMonoid A] [Module R A] : (Coop A)ᵐᵒᵖ ≃ₗ[R] A :=
  (MulOpposite.opLinearEquiv R).symm.trans (linearEquiv R A)

@[simp]
theorem unopLinearEquiv_apply [Semiring R] [AddCommMonoid A] [Module R A] (x : (Coop A)ᵐᵒᵖ) :
    unopLinearEquiv R A x = x.unop.val := by
  rfl

@[simp]
theorem unopLinearEquiv_symm_apply [Semiring R] [AddCommMonoid A] [Module R A] (a : A) :
    (unopLinearEquiv R A).symm a = MulOpposite.op (mk a) := by
  rfl

/-- The underlying linear map of `Coop.unopLinearEquiv R A` factors as
`Coop.linearEquiv R A ∘ₗ (MulOpposite.opLinearEquiv R).symm`. -/
theorem unopLinearEquiv_toLinearMap [Semiring R] [AddCommMonoid A] [Module R A] :
    (unopLinearEquiv R A).toLinearMap =
      (linearEquiv R A).toLinearMap ∘ₗ (MulOpposite.opLinearEquiv R).symm.toLinearMap := by
  rfl

variable (A) in
/-- `Coop.val` as a ring equivalence `Coop A ≃+* A`. -/
def ringEquiv [Add A] [Mul A] : Coop A ≃+* A where
  __ := equiv A
  map_mul' _ _ := rfl
  map_add' _ _ := rfl

@[simp] theorem ringEquiv_apply [Add A] [Mul A] (x : Coop A) : ringEquiv A x = x.val := by rfl
@[simp] theorem ringEquiv_symm_apply [Add A] [Mul A] (a : A) : (ringEquiv A).symm a = mk a := by
  rfl

variable (R A) in
/-- `Coop.val` as an `R`-algebra equivalence `Coop A ≃ₐ[R] A`. -/
def algEquiv [CommSemiring R] [Semiring A] [Algebra R A] : Coop A ≃ₐ[R] A where
  __ := ringEquiv A
  commutes' _ := rfl

@[simp]
theorem algEquiv_apply [CommSemiring R] [Semiring A] [Algebra R A] (x : Coop A) :
    algEquiv R A x = x.val := by
  rfl

@[simp]
theorem algEquiv_symm_apply [CommSemiring R] [Semiring A] [Algebra R A] (a : A) :
    (algEquiv R A).symm a = mk a := by
  rfl

end AlgebraicInstances

section Coalgebra

variable [CommSemiring R] [AddCommMonoid A] [Module R A]

noncomputable instance instCoalgebraStruct [CoalgebraStruct R A] : CoalgebraStruct R (Coop A) where
  comul :=
    TensorProduct.map (linearEquiv R A).symm.toLinearMap (linearEquiv R A).symm.toLinearMap ∘ₗ
      (TensorProduct.comm R A A).toLinearMap ∘ₗ Coalgebra.comul ∘ₗ (linearEquiv R A).toLinearMap
  counit := Coalgebra.counit ∘ₗ (linearEquiv R A).toLinearMap

theorem comul_def [CoalgebraStruct R A] :
    Coalgebra.comul (R := R) (A := Coop A) =
      TensorProduct.map (linearEquiv R A).symm.toLinearMap (linearEquiv R A).symm.toLinearMap ∘ₗ
        (TensorProduct.comm R A A).toLinearMap ∘ₗ Coalgebra.comul ∘ₗ
        (linearEquiv R A).toLinearMap :=
  rfl

theorem counit_def [CoalgebraStruct R A] :
    Coalgebra.counit (R := R) (A := Coop A) =
      Coalgebra.counit ∘ₗ (linearEquiv R A).toLinearMap :=
  rfl

@[simp]
theorem comul_mk [CoalgebraStruct R A] (a : A) :
    Coalgebra.comul (R := R) (mk a) =
      TensorProduct.map (linearEquiv R A).symm.toLinearMap (linearEquiv R A).symm.toLinearMap
        (TensorProduct.comm R A A (Coalgebra.comul (R := R) a)) := by
  rfl

@[simp]
theorem counit_mk [CoalgebraStruct R A] (a : A) :
    Coalgebra.counit (R := R) (mk a) = Coalgebra.counit (R := R) a := by
  rfl

theorem counit_apply [CoalgebraStruct R A] (x : Coop A) :
    Coalgebra.counit (R := R) x = Coalgebra.counit (R := R) x.val := by
  rfl

/-- Comultiplication commutes with `Coop.linearEquiv R A` up to swapping tensor factors. -/
theorem comul_linearEquiv [CoalgebraStruct R A] (x : Coop A) :
    Coalgebra.comul (R := R) (linearEquiv R A x) =
      TensorProduct.map (linearEquiv R A).toLinearMap (linearEquiv R A).toLinearMap
        (TensorProduct.comm R (Coop A) (Coop A) (Coalgebra.comul (R := R) x)) := by
  induction x with | mk a =>
  rw [linearEquiv_apply, val_mk, comul_mk, ← TensorProduct.map_comm, TensorProduct.map_map,
    LinearEquiv.comp_symm, TensorProduct.map_id, LinearMap.id_apply, TensorProduct.comm_comm]

private def tau (R : Type u) (A : Type v) [CommSemiring R] [AddCommMonoid A] [Module R A] :
    A ⊗[R] (A ⊗[R] A) →ₗ[R] A ⊗[R] (A ⊗[R] A) :=
  (TensorProduct.comm R A A).toLinearMap.lTensor A ∘ₗ
    (TensorProduct.comm R (A ⊗[R] A) A).toLinearMap ∘ₗ
    (TensorProduct.assoc R A A A).symm.toLinearMap

private theorem tau_assoc_rTensor (R : Type u) (A : Type v)
    [CommSemiring R] [AddCommMonoid A] [Module R A] [Coalgebra R A] :
    tau R A ∘ₗ (TensorProduct.assoc R A A A).toLinearMap ∘ₗ
        (Coalgebra.comul (R := R) (A := A)).rTensor A =
      ((TensorProduct.comm R A A).toLinearMap ∘ₗ Coalgebra.comul).lTensor A ∘ₗ
        (TensorProduct.comm R A A).toLinearMap := by
  refine TensorProduct.ext' fun a₁ a₂ ↦ ?_
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearMap.rTensor_tmul,
    LinearMap.lTensor_tmul, TensorProduct.comm_tmul, tau]
  induction Coalgebra.comul (R := R) a₁ using TensorProduct.inductionOn with
  | add u v hu hv => simp only [TensorProduct.add_tmul, TensorProduct.tmul_add, map_add, hu, hv]
  | tmul b₁ b₂ => simp

private theorem tau_lTensor (R : Type u) (A : Type v)
    [CommSemiring R] [AddCommMonoid A] [Module R A] [Coalgebra R A] :
    tau R A ∘ₗ (Coalgebra.comul (R := R) (A := A)).lTensor A =
      (TensorProduct.assoc R A A A).toLinearMap ∘ₗ
        ((TensorProduct.comm R A A).toLinearMap ∘ₗ Coalgebra.comul).rTensor A ∘ₗ
        (TensorProduct.comm R A A).toLinearMap := by
  refine TensorProduct.ext' fun a₁ a₂ ↦ ?_
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearMap.lTensor_tmul,
    LinearMap.rTensor_tmul, TensorProduct.comm_tmul, tau]
  induction Coalgebra.comul (R := R) a₂ using TensorProduct.inductionOn with
  | add u v hu hv => simp only [TensorProduct.tmul_add, TensorProduct.add_tmul, map_add, hu, hv]
  | tmul b₁ b₂ => simp

noncomputable instance instCoalgebra [Coalgebra R A] : Coalgebra R (Coop A) where
  coassoc := by
    let e : Coop A ≃ₗ[R] A := linearEquiv R A
    have hcomul :
        Coalgebra.comul (R := R) (A := Coop A) ∘ₗ e.symm.toLinearMap =
          TensorProduct.map e.symm.toLinearMap e.symm.toLinearMap ∘ₗ
            (TensorProduct.comm R A A).toLinearMap ∘ₗ Coalgebra.comul := by
      rw [comul_def, LinearMap.comp_assoc, LinearMap.comp_assoc, LinearMap.comp_assoc,
        e.comp_symm, LinearMap.comp_id]
    have hLHS :
        (TensorProduct.assoc R (Coop A) (Coop A) (Coop A)).toLinearMap ∘ₗ
            (Coalgebra.comul (R := R) (A := Coop A)).rTensor (Coop A) ∘ₗ
            TensorProduct.map e.symm.toLinearMap e.symm.toLinearMap =
          TensorProduct.map e.symm.toLinearMap
              (TensorProduct.map e.symm.toLinearMap e.symm.toLinearMap) ∘ₗ
            (TensorProduct.assoc R A A A).toLinearMap ∘ₗ
            ((TensorProduct.comm R A A).toLinearMap ∘ₗ Coalgebra.comul).rTensor A :=
      calc
        (TensorProduct.assoc R (Coop A) (Coop A) (Coop A)).toLinearMap ∘ₗ
              (Coalgebra.comul (R := R) (A := Coop A)).rTensor (Coop A) ∘ₗ
              TensorProduct.map e.symm.toLinearMap e.symm.toLinearMap
            = (TensorProduct.assoc R (Coop A) (Coop A) (Coop A)).toLinearMap ∘ₗ
                TensorProduct.map (Coalgebra.comul (R := R) (A := Coop A) ∘ₗ e.symm.toLinearMap)
                  e.symm.toLinearMap := by
              rw [LinearMap.rTensor_comp_map]
        _ = (TensorProduct.assoc R (Coop A) (Coop A) (Coop A)).toLinearMap ∘ₗ
              TensorProduct.map (TensorProduct.map e.symm.toLinearMap e.symm.toLinearMap)
                e.symm.toLinearMap ∘ₗ
              ((TensorProduct.comm R A A).toLinearMap ∘ₗ Coalgebra.comul).rTensor A := by
            rw [hcomul, ← LinearMap.map_comp_rTensor]
        _ = TensorProduct.map e.symm.toLinearMap
                (TensorProduct.map e.symm.toLinearMap e.symm.toLinearMap) ∘ₗ
              (TensorProduct.assoc R A A A).toLinearMap ∘ₗ
              ((TensorProduct.comm R A A).toLinearMap ∘ₗ Coalgebra.comul).rTensor A := by
            rw [← LinearMap.comp_assoc, ← LinearMap.comp_assoc,
              ← TensorProduct.map_map_comp_assoc_eq]
    have hRHS :
        (Coalgebra.comul (R := R) (A := Coop A)).lTensor (Coop A) ∘ₗ
            TensorProduct.map e.symm.toLinearMap e.symm.toLinearMap =
          TensorProduct.map e.symm.toLinearMap
              (TensorProduct.map e.symm.toLinearMap e.symm.toLinearMap) ∘ₗ
            ((TensorProduct.comm R A A).toLinearMap ∘ₗ Coalgebra.comul).lTensor A :=
      calc
        (Coalgebra.comul (R := R) (A := Coop A)).lTensor (Coop A) ∘ₗ
              TensorProduct.map e.symm.toLinearMap e.symm.toLinearMap
            = TensorProduct.map e.symm.toLinearMap
                (Coalgebra.comul (R := R) (A := Coop A) ∘ₗ e.symm.toLinearMap) :=
              LinearMap.lTensor_comp_map _ _ _ _
        _ = TensorProduct.map e.symm.toLinearMap
                (TensorProduct.map e.symm.toLinearMap e.symm.toLinearMap) ∘ₗ
              ((TensorProduct.comm R A A).toLinearMap ∘ₗ Coalgebra.comul).lTensor A := by
            rw [hcomul, ← LinearMap.map_comp_lTensor]
    refine LinearMap.ext fun x ↦ ?_
    have hco := congrArg (tau R A) (Coalgebra.coassoc_apply (R := R) (e x))
    have hL' := LinearMap.congr_fun (tau_assoc_rTensor R A) (Coalgebra.comul (R := R) (e x))
    have hR' := LinearMap.congr_fun (tau_lTensor R A) (Coalgebra.comul (R := R) (e x))
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe] at hL' hR'
    rw [hL', hR'] at hco
    have hmap := congrArg (TensorProduct.map e.symm.toLinearMap
      (TensorProduct.map e.symm.toLinearMap e.symm.toLinearMap)) hco.symm
    have hLHS' := LinearMap.congr_fun hLHS
      ((TensorProduct.comm R A A) (Coalgebra.comul (R := R) (e x)))
    have hRHS' := LinearMap.congr_fun hRHS
      ((TensorProduct.comm R A A) (Coalgebra.comul (R := R) (e x)))
    simp only [LinearMap.comp_apply] at hLHS' hRHS'
    exact hLHS'.trans (hmap.trans hRHS'.symm)
  rTensor_counit_comp_comul := by
    let e : Coop A ≃ₗ[R] A := linearEquiv R A
    have hL :
        (Coalgebra.counit (R := R) (A := Coop A)).rTensor (Coop A) ∘ₗ
            TensorProduct.map e.symm.toLinearMap e.symm.toLinearMap ∘ₗ
            (TensorProduct.comm R A A).toLinearMap =
          TensorProduct.map (LinearMap.id (R := R)) e.symm.toLinearMap ∘ₗ
            (TensorProduct.lid R A).symm.toLinearMap ∘ₗ (TensorProduct.rid R A).toLinearMap ∘ₗ
            (Coalgebra.counit (R := R)).lTensor A :=
      TensorProduct.ext' fun a b ↦ by simp [TensorProduct.smul_tmul', counit_def, e]
    refine LinearMap.ext fun x ↦ ?_
    have heq := LinearMap.congr_fun hL (Coalgebra.comul (R := R) (e x))
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, Coalgebra.lTensor_counit_comul] at heq
    simpa [comul_def, e] using heq
  lTensor_counit_comp_comul := by
    let e : Coop A ≃ₗ[R] A := linearEquiv R A
    have hL :
        (Coalgebra.counit (R := R) (A := Coop A)).lTensor (Coop A) ∘ₗ
            TensorProduct.map e.symm.toLinearMap e.symm.toLinearMap ∘ₗ
            (TensorProduct.comm R A A).toLinearMap =
          TensorProduct.map e.symm.toLinearMap (LinearMap.id (R := R)) ∘ₗ
            (TensorProduct.rid R A).symm.toLinearMap ∘ₗ (TensorProduct.lid R A).toLinearMap ∘ₗ
            (Coalgebra.counit (R := R)).rTensor A :=
      TensorProduct.ext' fun a b ↦ by simp [← TensorProduct.tmul_smul, counit_def, e]
    refine LinearMap.ext fun x ↦ ?_
    have heq := LinearMap.congr_fun hL (Coalgebra.comul (R := R) (e x))
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, Coalgebra.rTensor_counit_comul] at heq
    simpa [comul_def, e] using heq

instance instIsCocomm [Coalgebra R A] [Coalgebra.IsCocomm R A] :
    Coalgebra.IsCocomm R (Coop A) where
  comm_comp_comul := by
    ext x
    simp [comul_def, ← TensorProduct.map_comm, Coalgebra.comm_comul]

end Coalgebra

end Coop

end TauCeti

namespace Coalgebra.Repr

open TauCeti

variable {R A ι : Type*} [CommSemiring R] [AddCommMonoid A] [Module R A] [CoalgebraStruct R A]

/-- Reverses the legs of a finite coproduct representation to give a representation in
`TauCeti.Coop A`. -/
def coop {a : A} (r : Coalgebra.Repr R a ι) : Coalgebra.Repr R (Coop.mk a) ι where
  index := r.index
  left i := Coop.mk (r.right i)
  right i := Coop.mk (r.left i)
  eq := by
    have h := congrArg (TensorProduct.map (Coop.linearEquiv R A).symm.toLinearMap
      (Coop.linearEquiv R A).symm.toLinearMap ∘ₗ (TensorProduct.comm R A A).toLinearMap) r.eq
    simpa [map_sum] using h

@[simp]
theorem coop_index {a : A} (r : Coalgebra.Repr R a ι) : r.coop.index = r.index := by
  rfl

@[simp]
theorem coop_left {a : A} (r : Coalgebra.Repr R a ι) (i : ι) :
    r.coop.left i = Coop.mk (r.right i) := by
  rfl

@[simp]
theorem coop_right {a : A} (r : Coalgebra.Repr R a ι) (i : ι) :
    r.coop.right i = Coop.mk (r.left i) := by
  rfl

end Coalgebra.Repr
