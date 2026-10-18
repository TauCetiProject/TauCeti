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
  have hf : f q * (kUnit q : UqSl2 q) =
      ((Units.mk0 q Fact.out ^ 2 : ℂˣ) : ℂ) • ((kUnit q : UqSl2 q) * f q) := by
    rw [kUnit_val, k_mul_f, smul_smul, Units.val_pow_eq_pow_val, Units.val_mk0, inv_pow,
      mul_inv_cancel₀ (pow_ne_zero 2 Fact.out), one_smul]
  have hscale : (((Units.mk0 q Fact.out ^ 2) ^ b : ℂˣ) : ℂ) = q ^ (2 * b) := by
    simpa using pbwScale_coe q 1 b
  simpa only [laurentEval_T, rescale_T, map_mul, laurentEval_C, Algebra.smul_def, mul_assoc,
    Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_ofClass, map_zpow,
    Units.val_zpow_eq_zpow_val, hscale] using
    (TauCeti.mul_laurentEval hf (T b))

/-- Moving a natural power of `F` past an integer power of `K`. -/
theorem f_pow_mul_kUnit_zpow (a : ℕ) (b : ℤ) :
    f q ^ a * ((kUnit q ^ b : (UqSl2 q)ˣ) : UqSl2 q) =
      q ^ (2 * b * a) •
        (((kUnit q ^ b : (UqSl2 q)ˣ) : UqSl2 q) * f q ^ a) := by
  induction a with
  | zero => simp
  | succ a ih =>
    rw [pow_succ, mul_assoc, f_mul_kUnit_zpow, mul_smul_comm, ← mul_assoc, ih,
      smul_mul_assoc, smul_smul, ← zpow_add₀ Fact.out]
    simp only [mul_assoc]
    congr 3
    push_cast
    ring

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
