/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.QuantumGroups.UqSl2.OreTower

import Mathlib.LinearAlgebra.Basis.SMul
import Mathlib.RingTheory.AlgebraTower

/-!
# A PBW basis of `U_q(sl₂)`

For a nonzero parameter `q`, the monomials

`F ^ a * K ^ b * E ^ c`, with `a c : ℕ` and `b : ℤ`,

form a complex basis of `UqSl2 q`.  The construction transports the nested left-monomial bases
of the iterated Ore presentation.  Those bases initially put the Laurent monomial first, in the
order `K ^ b * F ^ a * E ^ c`; commuting `F ^ a` past `K ^ b` gives the displayed normalization.
Thus the coordinates supplied by `pbwBasis.repr` are the unique PBW coefficients of an element.

The basis and its normalization follow C. Kassel, *Quantum Groups*, Graduate Texts in
Mathematics 155, Section VI.1.
-/

public noncomputable section

open LaurentPolynomial

namespace TauCeti.UqSl2

variable (q : ℂ) [Fact (q ≠ 0)]

private theorem pbwScale_coe (a : ℕ) (b : ℤ) :
    (((Units.mk0 q Fact.out ^ 2) ^ (b * a) : ℂˣ) : ℂ) = q ^ (2 * b * a) := by
  rw [Units.val_zpow_eq_zpow_val, Units.val_pow_eq_pow_val, Units.val_mk0,
    ← zpow_natCast]
  calc
    (q ^ (2 : ℤ)) ^ (b * (a : ℤ)) = q ^ ((2 : ℤ) * (b * (a : ℤ))) :=
      (zpow_mul q 2 (b * (a : ℤ))).symm
    _ = q ^ (2 * b * a) := by ring_nf

/-- Moving `F` past an arbitrary integer power of `K` multiplies by `q ^ (2b)`. -/
theorem f_mul_kUnit_zpow (b : ℤ) :
    f q * ((kUnit q ^ b : (UqSl2 q)ˣ) : UqSl2 q) =
      q ^ (2 * b) •
        (((kUnit q ^ b : (UqSl2 q)ˣ) : UqSl2 q) * f q) := by
  have hk : f q * k q = q ^ (2 : ℤ) • (k q * f q) := by
    rw [k_mul_f, smul_smul, zpow_ofNat, ← mul_pow, mul_inv_cancel₀ Fact.out, one_pow, one_smul]
  have hkInv : f q * kInv q = q ^ (-2 : ℤ) • (kInv q * f q) := by
    rw [f_mul_kInv, zpow_neg, zpow_ofNat, inv_pow]
  induction b using Int.induction_on with
  | zero => simp
  | succ n ih =>
    have hExp : 2 * ((n : ℤ) + 1) = 2 * n + 2 := by ring
    calc
      f q * ((kUnit q ^ ((n : ℤ) + 1) : (UqSl2 q)ˣ) : UqSl2 q) =
          (f q * ((kUnit q ^ (n : ℤ) : (UqSl2 q)ˣ) : UqSl2 q)) * k q := by
        rw [zpow_add_one, Units.val_mul, kUnit_val, ← mul_assoc]
      _ = (q ^ (2 * (n : ℤ)) •
          (((kUnit q ^ (n : ℤ) : (UqSl2 q)ˣ) : UqSl2 q) * f q)) * k q := by
        rw [ih]
      _ = q ^ (2 * (n : ℤ)) •
          (((kUnit q ^ (n : ℤ) : (UqSl2 q)ˣ) : UqSl2 q) *
            (q ^ (2 : ℤ) • (k q * f q))) := by
        rw [smul_mul_assoc, mul_assoc, hk]
      _ = q ^ (2 * ((n : ℤ) + 1)) •
          (((kUnit q ^ ((n : ℤ) + 1) : (UqSl2 q)ˣ) : UqSl2 q) * f q) := by
        rw [hExp, zpow_add_one, Units.val_mul, kUnit_val]
        simp only [mul_smul_comm, smul_smul, mul_assoc,
          ← zpow_add₀ (Fact.out : q ≠ 0)]
  | pred n ih =>
    have hExp : 2 * (-(n : ℤ) - 1) = 2 * -n + -2 := by ring
    calc
      f q * ((kUnit q ^ (-(n : ℤ) - 1) : (UqSl2 q)ˣ) : UqSl2 q) =
          (f q * ((kUnit q ^ (-(n : ℤ)) : (UqSl2 q)ˣ) : UqSl2 q)) * kInv q := by
        rw [zpow_sub_one, Units.val_mul, kUnit_inv, ← mul_assoc]
      _ = (q ^ (2 * -(n : ℤ)) •
          (((kUnit q ^ (-(n : ℤ)) : (UqSl2 q)ˣ) : UqSl2 q) * f q)) * kInv q := by
        rw [ih]
      _ = q ^ (2 * -(n : ℤ)) •
          (((kUnit q ^ (-(n : ℤ)) : (UqSl2 q)ˣ) : UqSl2 q) *
            (q ^ (-2 : ℤ) • (kInv q * f q))) := by
        rw [smul_mul_assoc, mul_assoc, hkInv]
      _ = q ^ (2 * (-(n : ℤ) - 1)) •
          (((kUnit q ^ (-(n : ℤ) - 1) : (UqSl2 q)ˣ) : UqSl2 q) * f q) := by
        rw [hExp, zpow_sub_one, Units.val_mul, kUnit_inv]
        simp only [mul_smul_comm, smul_smul, mul_assoc,
          ← zpow_add₀ (Fact.out : q ≠ 0)]

/-- Moving a natural power of `F` past an integer power of `K`. -/
theorem f_pow_mul_kUnit_zpow (a : ℕ) (b : ℤ) :
    f q ^ a * ((kUnit q ^ b : (UqSl2 q)ˣ) : UqSl2 q) =
      q ^ (2 * b * a) •
        (((kUnit q ^ b : (UqSl2 q)ˣ) : UqSl2 q) * f q ^ a) := by
  induction a with
  | zero => simp
  | succ a ih =>
    have hExp : 2 * b * (a + 1 : ℕ) = 2 * b + 2 * b * a := by
      push_cast
      ring
    calc
      f q ^ (a + 1) * ((kUnit q ^ b : (UqSl2 q)ˣ) : UqSl2 q) =
          f q ^ a * (f q * ((kUnit q ^ b : (UqSl2 q)ˣ) : UqSl2 q)) := by
        rw [pow_succ, mul_assoc]
      _ = f q ^ a * (q ^ (2 * b) •
          (((kUnit q ^ b : (UqSl2 q)ˣ) : UqSl2 q) * f q)) := by
        rw [f_mul_kUnit_zpow]
      _ = q ^ (2 * b) •
          ((f q ^ a * ((kUnit q ^ b : (UqSl2 q)ˣ) : UqSl2 q)) * f q) := by
        rw [mul_smul_comm, ← mul_assoc]
      _ = q ^ (2 * b) •
          ((q ^ (2 * b * a) •
            (((kUnit q ^ b : (UqSl2 q)ˣ) : UqSl2 q) * f q ^ a)) * f q) := by
        rw [ih]
      _ = q ^ (2 * b * (a + 1 : ℕ)) •
          (((kUnit q ^ b : (UqSl2 q)ˣ) : UqSl2 q) * f q ^ (a + 1)) := by
        rw [hExp, pow_succ]
        simp only [smul_mul_assoc, smul_smul, mul_assoc,
          ← zpow_add₀ (Fact.out : q ≠ 0)]

/-- The reindexing from the nested Ore-extension exponents to PBW exponents `(a, b, c)`. -/
private def pbwIndexEquiv : ((ℤ × ℕ) × ℕ) ≃ ℕ × ℤ × ℕ where
  toFun := fun ⟨⟨b, a⟩, c⟩ => (a, b, c)
  invFun := fun ⟨a, b, c⟩ => ((b, a), c)
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl

@[simp]
private theorem pbwIndexEquiv_symm_apply (a : ℕ) (b : ℤ) (c : ℕ) :
    pbwIndexEquiv.symm (a, b, c) = ((b, a), c) :=
  rfl

/-- The basis obtained directly from the left-coefficient monomial bases of the two nested Ore
extensions, ordered as `K ^ b * F ^ a * E ^ c`. -/
private def cartanFirstPBWBasis : Module.Basis (ℕ × ℤ × ℕ) ℂ (UqSl2 q) :=
  ((((AddMonoidAlgebra.basis ℤ ℂ).smulTower
      (OreExtension.monomialBasis (σ := sigmaF q) (δ := 0))).smulTower
      (OreExtension.monomialBasis (σ := sigmaE q) (δ := deltaE q))).map
      (oreTowerEquiv q).symm.toLinearEquiv).reindex pbwIndexEquiv

private theorem cartanFirstPBWBasis_apply (a : ℕ) (b : ℤ) (c : ℕ) :
    cartanFirstPBWBasis q (a, b, c) =
      ((kUnit q ^ b : (UqSl2 q)ˣ) : UqSl2 q) * f q ^ a * e q ^ c := by
  rw [cartanFirstPBWBasis, Module.Basis.reindex_apply, Module.Basis.map_apply]
  simp only [pbwIndexEquiv_symm_apply, Module.Basis.smulTower_apply,
    AddMonoidAlgebra.basis_apply, OreExtension.monomialBasis_apply]
  rw [OreExtension.smul_eq_C_mul, OreExtension.smul_eq_C_mul,
    ← OreExtension.X_pow_eq_monomial, ← OreExtension.X_pow_eq_monomial,
    OreExtension.C_mul, AlgEquiv.toLinearEquiv_apply, map_mul, map_mul,
    oreTowerEquiv_symm_C_C]
  have hT : AddMonoidAlgebra.single b (1 : ℂ) = T b := rfl
  have hCX :
      OreExtension.C (σ := sigmaE q) (δ := deltaE q) (OreExtension.X ^ a) =
        (OreExtension.C OreExtension.X : OreTower q) ^ a :=
    by simpa only [OreExtension.CRingHom_eq_C] using
      (map_pow (OreExtension.CRingHom (σ := sigmaE q) (δ := deltaE q)) OreExtension.X a)
  rw [hT, laurentEval_T, hCX, map_pow, oreTowerEquiv_symm_C_X, map_pow,
    oreTowerEquiv_symm_X]

/-- The Poincaré--Birkhoff--Witt basis of `UqSl2 q`, indexed by the exponents `(a, b, c)`
of the ordered monomial `F ^ a * K ^ b * E ^ c`. -/
def pbwBasis : Module.Basis (ℕ × ℤ × ℕ) ℂ (UqSl2 q) :=
  (cartanFirstPBWBasis q).unitsSMul fun ⟨a, b, _⟩ => (Units.mk0 q Fact.out ^ 2) ^ (b * a)

/-- A vector of the PBW basis is the corresponding ordered monomial. -/
@[simp]
theorem pbwBasis_apply (a : ℕ) (b : ℤ) (c : ℕ) :
    pbwBasis q (a, b, c) =
      f q ^ a * ((kUnit q ^ b : (UqSl2 q)ˣ) : UqSl2 q) * e q ^ c := by
  rw [pbwBasis, Module.Basis.unitsSMul_apply, cartanFirstPBWBasis_apply,
    Units.smul_def, pbwScale_coe, f_pow_mul_kUnit_zpow, smul_mul_assoc]

end TauCeti.UqSl2
