/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.RingTheory.TensorProduct.MvPolynomial
import TauCeti.RingTheory.IsTensorProduct.Pushout

/-!
# Pushout universal property of multivariate polynomial rings

For a ring homomorphism `f : B →+* B'`, the polynomial ring `MvPolynomial σ B'` is the pushout
`B' ⊗_B MvPolynomial σ B` of `f` and `MvPolynomial.C`, with canonical inclusions `MvPolynomial.C`
and `MvPolynomial.map f`. `MvPolynomial.pushoutLift` packages this universal property as an
equivalence on ring homomorphisms.
-/

public section

noncomputable section

namespace MvPolynomial

variable {σ B B' R : Type*} [CommSemiring B] [CommSemiring B'] [CommSemiring R]

attribute [local instance] MvPolynomial.algebraMvPolynomial in
/-- **Universal property of `MvPolynomial σ B'` as the pushout `B' ⊗_B MvPolynomial σ B`** of
`f : B →+* B'` and `C`, via restriction along `C` and along `map f`. -/
def pushoutLift (f : B →+* B') :
    {p : (B' →+* R) × (MvPolynomial σ B →+* R) // p.1.comp f = p.2.comp C} ≃
      (MvPolynomial σ B' →+* R) where
  toFun p :=
    letI := f.toAlgebra
    Algebra.IsPushout.liftRingHom (R := B) (MvPolynomial σ B') p.val.1 p.val.2 p.property
  invFun k := ⟨(k.comp C, k.comp (map f)), RingHom.ext fun _ ↦ by simp⟩
  left_inv p := by
    let := f.toAlgebra
    exact Subtype.ext <| Prod.ext
      (RingHom.ext (Algebra.IsPushout.liftRingHom_algebraMap_left _ _ _))
      (RingHom.ext (Algebra.IsPushout.liftRingHom_algebraMap_right _ _ _))
  right_inv k := by
    let := f.toAlgebra
    exact Algebra.IsPushout.ringHom_ext (R := B) (S := B') (R' := MvPolynomial σ B)
      (RingHom.ext (Algebra.IsPushout.liftRingHom_algebraMap_left _ _ _))
      (RingHom.ext (Algebra.IsPushout.liftRingHom_algebraMap_right _ _ _))

/-- The left component classified by `k : MvPolynomial σ B' →+* R` is `k.comp C`. -/
@[simp] theorem pushoutLift_symm_apply_fst (f : B →+* B') (k : MvPolynomial σ B' →+* R) :
    ((pushoutLift f).symm k).val.1 = k.comp C := (rfl)
/-- The right component classified by `k : MvPolynomial σ B' →+* R` is `k.comp (map f)`. -/
@[simp] theorem pushoutLift_symm_apply_snd (f : B →+* B') (k : MvPolynomial σ B' →+* R) :
    ((pushoutLift f).symm k).val.2 = k.comp (map f) := (rfl)

section
variable (f : B →+* B') (p : {p : (B' →+* R) × (MvPolynomial σ B →+* R) // p.1.comp f = p.2.comp C})

/-- `pushoutLift f p` restricts to `p.val.1` along `C`. -/
@[simp] theorem pushoutLift_comp_C : (pushoutLift f p).comp C = p.val.1 :=
  congrArg (·.val.1) ((pushoutLift f).left_inv p)
/-- `pushoutLift f p` restricts to `p.val.2` along `map f`. -/
@[simp] theorem pushoutLift_comp_map : (pushoutLift f p).comp (map f) = p.val.2 :=
  congrArg (·.val.2) ((pushoutLift f).left_inv p)
/-- `pushoutLift f p` agrees with `p.val.1` on constants from `B'`. -/
@[simp] theorem pushoutLift_C (b : B') : pushoutLift f p (C b) = p.val.1 b :=
  RingHom.congr_fun (pushoutLift_comp_C f p) b
/-- `pushoutLift f p` agrees with `p.val.2` along `map f`. -/
@[simp] theorem pushoutLift_map (x : MvPolynomial σ B) : pushoutLift f p (map f x) = p.val.2 x :=
  RingHom.congr_fun (pushoutLift_comp_map f p) x
/-- `pushoutLift f p` agrees with `p.val.2` on the variables `X i`. -/
@[simp] theorem pushoutLift_X (i : σ) : pushoutLift f p (X i) = p.val.2 (X i) := by
  simpa using pushoutLift_map f p (X i)
end

end MvPolynomial
