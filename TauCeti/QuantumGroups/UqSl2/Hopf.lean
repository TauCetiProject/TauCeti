/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.QuantumGroups.UqSl2.Basic
public import Mathlib.RingTheory.HopfAlgebra.Convolution
import Mathlib.Tactic.Module

/-!
# The Hopf algebra structure on U_q(sl₂)

For a nonzero parameter, the presentation of `UqSl2 q` carries the coproduct
`ΔE = E ⊗ 1 + K ⊗ E`, `ΔF = F ⊗ K⁻¹ + 1 ⊗ F`, and `ΔK = K ⊗ K`.
The counit and antipode have their standard rank-one values. These maps descend through the
presentation's universal property. The coproduct supplies actions on tensor products of
representations, while the antipode supplies the corresponding dual actions.

The conventions follow A. Virelizier, *Quantum groups*, Sections 2.3--2.4.
-/

public section

open scoped TensorProduct

namespace TauCeti.UqSl2

variable (q : ℂ) [Fact (q ≠ 0)]

private def comulTuple : GeneratorTuple q (UqSl2 q ⊗[ℂ] UqSl2 q) where
  e := e q ⊗ₜ[ℂ] 1 + k q ⊗ₜ[ℂ] e q
  f := f q ⊗ₜ[ℂ] kInv q + 1 ⊗ₜ[ℂ] f q
  k := k q ⊗ₜ[ℂ] k q
  kInv := kInv q ⊗ₜ[ℂ] kInv q
  k_mul_kInv := by simp [Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.one_def]
  kInv_mul_k := by simp [Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.one_def]
  k_mul_e := by
    simp [mul_add, add_mul, Algebra.TensorProduct.tmul_mul_tmul, k_mul_e,
      TensorProduct.smul_tmul, TensorProduct.tmul_smul, smul_add]
  k_mul_f := by
    simp [mul_add, add_mul, Algebra.TensorProduct.tmul_mul_tmul, k_mul_f,
      TensorProduct.smul_tmul, TensorProduct.tmul_smul, smul_add]
  e_mul_f_sub_f_mul_e := by
    simp only [mul_add, add_mul, Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]
    rw [k_mul_f, e_mul_kInv]
    simp only [TensorProduct.smul_tmul, TensorProduct.tmul_smul, smul_smul]
    simp only [inv_pow, mul_inv_cancel₀ (pow_ne_zero 2 (Fact.out : q ≠ 0)), one_smul]
    calc
      _ = (e q * f q - f q * e q) ⊗ₜ[ℂ] kInv q +
          k q ⊗ₜ[ℂ] (e q * f q - f q * e q) := by
        simp only [TensorProduct.sub_tmul, TensorProduct.tmul_sub]
        abel
      _ = _ := by
        rw [e_mul_f_sub_f_mul_e]
        simp only [TensorProduct.smul_tmul, TensorProduct.tmul_smul, TensorProduct.sub_tmul,
          TensorProduct.tmul_sub, smul_sub]
        module

/-- The coproduct with `E` skew primitive relative to `K` and `F` relative to `K⁻¹`. -/
def comul : UqSl2 q →ₐ[ℂ] UqSl2 q ⊗[ℂ] UqSl2 q := lift (comulTuple q)

@[local simp] private theorem comul_eAux : comul q (e q) = e q ⊗ₜ[ℂ] 1 + k q ⊗ₜ[ℂ] e q := by
  simp [comul, comulTuple]

@[local simp] private theorem comul_fAux : comul q (f q) = f q ⊗ₜ[ℂ] kInv q + 1 ⊗ₜ[ℂ] f q := by
  simp [comul, comulTuple]

@[local simp] private theorem comul_kAux : comul q (k q) = k q ⊗ₜ[ℂ] k q := by
  simp [comul, comulTuple]

@[local simp] private theorem comul_kInvAux : comul q (kInv q) = kInv q ⊗ₜ[ℂ] kInv q := by
  simp [comul, comulTuple]

private def counitTuple (q : ℂ) : GeneratorTuple q ℂ where
  e := 0
  f := 0
  k := 1
  kInv := 1
  k_mul_kInv := by simp
  kInv_mul_k := by simp
  k_mul_e := by simp
  k_mul_f := by simp
  e_mul_f_sub_f_mul_e := by simp

/-- The unconditional augmentation, taking both weight generators to one and both root
generators to zero. -/
def counit (q : ℂ) : UqSl2 q →ₐ[ℂ] ℂ := lift (counitTuple q)

omit [Fact (q ≠ 0)] in
/-- The unconditional augmentation sends the raising generator to zero. -/
@[simp] theorem counit_apply_e : counit q (e q) = 0 := by simp [counit, counitTuple]

omit [Fact (q ≠ 0)] in
/-- The unconditional augmentation sends the lowering generator to zero. -/
@[simp] theorem counit_apply_f : counit q (f q) = 0 := by simp [counit, counitTuple]

omit [Fact (q ≠ 0)] in
/-- The unconditional augmentation sends the weight generator to one. -/
@[simp] theorem counit_apply_k : counit q (k q) = 1 := by simp [counit, counitTuple]

omit [Fact (q ≠ 0)] in
/-- The unconditional augmentation sends the inverse weight generator to one. -/
@[simp] theorem counit_apply_kInv :
    counit q (kInv q) = 1 := by simp [counit, counitTuple]

/-- The bialgebra structure determined by the presentation's coproduct and counit. -/
noncomputable instance instBialgebra : Bialgebra ℂ (UqSl2 q) := by
  exact Bialgebra.ofAlgHom (comul q) (counit q)
    (by
      apply hom_ext <;>
        simp [TensorProduct.tmul_add, TensorProduct.add_tmul, add_assoc,
          Algebra.TensorProduct.one_def])
    (by apply hom_ext <;> simp)
    (by apply hom_ext <;> simp)

private def antipodeTuple : GeneratorTuple q (UqSl2 q)ᵐᵒᵖ where
  e := MulOpposite.op (- (kInv q * e q))
  f := MulOpposite.op (- (f q * k q))
  k := MulOpposite.op (kInv q)
  kInv := MulOpposite.op (k q)
  k_mul_kInv := by apply MulOpposite.unop_injective; simp
  kInv_mul_k := by apply MulOpposite.unop_injective; simp
  k_mul_e := by
    apply MulOpposite.unop_injective
    simp only [MulOpposite.unop_mul, MulOpposite.unop_op, MulOpposite.unop_smul,
      neg_mul, mul_neg, mul_assoc]
    rw [e_mul_kInv]
    simp
  k_mul_f := by
    apply MulOpposite.unop_injective
    simp only [MulOpposite.unop_mul, MulOpposite.unop_op, MulOpposite.unop_smul,
      neg_mul, mul_neg, mul_assoc]
    rw [← mul_assoc (kInv q), kInv_mul_f]
    simp [mul_assoc, (Fact.out : q ≠ 0)]
  e_mul_f_sub_f_mul_e := by
    apply MulOpposite.unop_injective
    simp only [MulOpposite.unop_sub, MulOpposite.unop_mul, MulOpposite.unop_op,
      MulOpposite.unop_smul, neg_mul_neg]
    have h : kInv q * e q * (f q * k q) = e q * f q := by
      rw [kInv_mul_e, smul_mul_assoc, mul_assoc, ← mul_assoc (kInv q), kInv_mul_f,
        smul_mul_assoc, mul_smul_comm, smul_smul]
      simp [mul_assoc, (Fact.out : q ≠ 0)]
    rw [h]
    simp only [mul_assoc, ← mul_assoc (k q), k_mul_kInv, one_mul]
    rw [← neg_sub, e_mul_f_sub_f_mul_e, ← smul_neg, neg_sub]

/-- The antipode as an algebra homomorphism into the opposite algebra. -/
def antipodeOp : UqSl2 q →ₐ[ℂ] (UqSl2 q)ᵐᵒᵖ := lift (antipodeTuple q)

@[local simp] private theorem antipodeOp_e :
    antipodeOp q (e q) = MulOpposite.op (-(kInv q * e q)) := by
  simp [antipodeOp, antipodeTuple]

@[local simp] private theorem antipodeOp_f :
    antipodeOp q (f q) = MulOpposite.op (-(f q * k q)) := by
  simp [antipodeOp, antipodeTuple]

@[local simp] private theorem antipodeOp_k : antipodeOp q (k q) = MulOpposite.op (kInv q) := by
  simp [antipodeOp, antipodeTuple]

@[local simp] private theorem antipodeOp_kInv : antipodeOp q (kInv q) = MulOpposite.op (k q) := by
  simp [antipodeOp, antipodeTuple]

/-- The Hopf algebra structure of the rank-one quantized enveloping algebra. -/
noncomputable instance instHopfAlgebra : HopfAlgebra ℂ (UqSl2 q) := by
  -- Mathlib's constructor extends the antipode identities from the generators.
  exact HopfAlgebra.ofAntipodeOfAdjoin (antipodeOp q) (adjoin_range_generator q)
    (by
      rintro _ ⟨g, rfl⟩
      cases g <;>
        simp [Coalgebra.comul, Coalgebra.counit, mul_assoc])
    (by
      rintro _ ⟨g, rfl⟩
      cases g <;>
        simp [Coalgebra.comul, Coalgebra.counit, ← mul_assoc (k q)])

/-- The coproduct of the raising generator. -/
@[simp] theorem comul_e (q : ℂ) [Fact (q ≠ 0)] : Coalgebra.comul (R := ℂ) (e q) =
    e q ⊗ₜ[ℂ] 1 + k q ⊗ₜ[ℂ] e q := comul_eAux q

/-- The coproduct of the lowering generator. -/
@[simp] theorem comul_f (q : ℂ) [Fact (q ≠ 0)] : Coalgebra.comul (R := ℂ) (f q) =
    f q ⊗ₜ[ℂ] kInv q + 1 ⊗ₜ[ℂ] f q := comul_fAux q

/-- The weight generator is group-like for the coproduct. -/
@[simp] theorem comul_k (q : ℂ) [Fact (q ≠ 0)] : Coalgebra.comul (R := ℂ) (k q) =
    k q ⊗ₜ[ℂ] k q := comul_kAux q

/-- The inverse weight generator is group-like for the coproduct. -/
@[simp] theorem comul_kInv (q : ℂ) [Fact (q ≠ 0)] : Coalgebra.comul (R := ℂ) (kInv q) =
    kInv q ⊗ₜ[ℂ] kInv q := comul_kInvAux q

/-- The raising generator has zero counit. -/
@[simp] theorem counit_e (q : ℂ) [Fact (q ≠ 0)] : Coalgebra.counit (R := ℂ) (e q) = 0 :=
  counit_apply_e q

/-- The lowering generator has zero counit. -/
@[simp] theorem counit_f (q : ℂ) [Fact (q ≠ 0)] : Coalgebra.counit (R := ℂ) (f q) = 0 :=
  counit_apply_f q

/-- The weight generator has counit one. -/
@[simp] theorem counit_k (q : ℂ) [Fact (q ≠ 0)] : Coalgebra.counit (R := ℂ) (k q) = 1 :=
  counit_apply_k q

/-- The inverse weight generator has counit one. -/
@[simp] theorem counit_kInv (q : ℂ) [Fact (q ≠ 0)] : Coalgebra.counit (R := ℂ) (kInv q) = 1 :=
  counit_apply_kInv q

/-- The antipode of the raising generator. -/
@[simp] theorem antipode_e (q : ℂ) [Fact (q ≠ 0)] : HopfAlgebra.antipode ℂ (e q) =
    -(kInv q * e q) := by
  simp [HopfAlgebra.antipode]

/-- The antipode of the lowering generator. -/
@[simp] theorem antipode_f (q : ℂ) [Fact (q ≠ 0)] : HopfAlgebra.antipode ℂ (f q) =
    -(f q * k q) := by
  simp [HopfAlgebra.antipode]

/-- The antipode interchanges the weight generators. -/
@[simp] theorem antipode_k (q : ℂ) [Fact (q ≠ 0)] : HopfAlgebra.antipode ℂ (k q) = kInv q := by
  simp [HopfAlgebra.antipode]

/-- The antipode interchanges the inverse weight generators. -/
@[simp] theorem antipode_kInv (q : ℂ) [Fact (q ≠ 0)] : HopfAlgebra.antipode ℂ (kInv q) =
    k q := by
  simp [HopfAlgebra.antipode]

/-- The constructed coproduct agrees with the native coalgebra operation. -/
@[simp] theorem comul_apply (x : UqSl2 q) : comul q x = Coalgebra.comul x := (rfl)

/-- The constructed counit agrees with the native coalgebra operation. -/
@[simp] theorem counit_apply (x : UqSl2 q) : counit q x = Coalgebra.counit x := (rfl)

/-- The opposite-valued antipode agrees with the native linear antipode. -/
@[simp] theorem antipodeOp_apply (x : UqSl2 q) :
    antipodeOp q x = MulOpposite.op (HopfAlgebra.antipode ℂ x) := (rfl)

end TauCeti.UqSl2
