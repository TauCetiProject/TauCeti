/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.QuantumGroups.QuantumInteger.Basic
public import TauCeti.QuantumGroups.UqSl2.OreTower

import Mathlib.LinearAlgebra.Basis.SMul
import Mathlib.RingTheory.AlgebraTower
import TauCeti.LinearAlgebra.Basis.Basic
import TauCeti.QuantumGroups.UqSl2.Commutator

/-!
# A PBW basis of `U_q(sl₂)`

For a nonzero parameter `q`, the monomials

`F ^ a * K ^ b * E ^ c`, with `a c : ℕ` and `b : ℤ`,

form a complex basis of `UqSl2 q`.  The construction transports the nested left-monomial bases
of the iterated Ore presentation.  Those bases initially put the Laurent monomial first, in the
order `K ^ b * F ^ a * E ^ c`; commuting `F ^ a` past `K ^ b` gives the displayed normalization.
Thus the coordinates supplied by `pbwBasis.repr` are the unique PBW coefficients of an element.

Multiplying a PBW monomial on the left by a generator, or on the right by `E` or `K`, gives an
explicit combination of PBW monomials. Only left multiplication by `E` is not a multiple of a
single monomial: commuting `E` past `F ^ a` contributes two monomials of `F`-exponent `a - 1`.
These rules let PBW coordinates be tracked through products, for instance when determining the
center: right multiplication by `E` shifts coordinates (`pbwBasis_repr_mul_e`), and at a generic
parameter an element commuting with `K` has PBW coordinates only at monomials
`F ^ a * K ^ b * E ^ a` (`pbwBasis_repr_eq_zero_of_commute_k`), since conjugation by `K`
multiplies `F ^ a * K ^ b * E ^ c` by `q ^ (2 (c - a))`.

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

/-- Moving `E` past an arbitrary integer power of `K` multiplies by `q ^ (-2b)`. -/
theorem e_mul_kUnit_zpow (b : ℤ) :
    e q * ((kUnit q ^ b : (UqSl2 q)ˣ) : UqSl2 q) =
      q ^ (-2 * b) • (((kUnit q ^ b : (UqSl2 q)ˣ) : UqSl2 q) * e q) := by
  have hq : q ≠ 0 := Fact.out
  have hk : e q * k q = q ^ (-2 : ℤ) • (k q * e q) := by
    rw [k_mul_e, smul_smul, zpow_neg, zpow_ofNat, inv_mul_cancel₀ (pow_ne_zero 2 hq), one_smul]
  have hkInv : e q * kInv q = q ^ (2 : ℤ) • (kInv q * e q) := by
    rw [e_mul_kInv, zpow_ofNat]
  induction b using Int.induction_on with
  | zero => simp
  | succ n ih =>
    rw [zpow_add_one, Units.val_mul, kUnit_val, ← mul_assoc, ih, smul_mul_assoc, mul_assoc, hk,
      mul_smul_comm, smul_smul, ← mul_assoc, ← zpow_add₀ hq]
    ring_nf
  | pred n ih =>
    rw [zpow_sub_one, Units.val_mul, kUnit_inv, ← mul_assoc, ih, smul_mul_assoc, mul_assoc, hkInv,
      mul_smul_comm, smul_smul, ← mul_assoc, ← zpow_add₀ hq]
    ring_nf

/-- Moving a natural power of `E` past an integer power of `K`. -/
theorem e_pow_mul_kUnit_zpow (c : ℕ) (b : ℤ) :
    e q ^ c * ((kUnit q ^ b : (UqSl2 q)ˣ) : UqSl2 q) =
      q ^ (-2 * b * c) • (((kUnit q ^ b : (UqSl2 q)ˣ) : UqSl2 q) * e q ^ c) := by
  induction c with
  | zero => simp
  | succ c ih =>
    rw [pow_succ', mul_assoc, ih, mul_smul_comm, ← mul_assoc, e_mul_kUnit_zpow, smul_mul_assoc,
      smul_smul, ← zpow_add₀ (Fact.out : q ≠ 0), mul_assoc _ (e q)]
    congr 2
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

/-! ### Multiplying PBW monomials by generators -/

/-- Left multiplication by `F` raises the `F`-exponent of a PBW monomial. -/
theorem f_mul_pbwBasis (a : ℕ) (b : ℤ) (c : ℕ) :
    f q * pbwBasis q (a, b, c) = pbwBasis q (a + 1, b, c) := by
  simp only [pbwBasis_apply, ← mul_assoc, pow_succ']

/-- Right multiplication by `E` raises the `E`-exponent of a PBW monomial. -/
theorem pbwBasis_mul_e (a : ℕ) (b : ℤ) (c : ℕ) :
    pbwBasis q (a, b, c) * e q = pbwBasis q (a, b, c + 1) := by
  simp only [pbwBasis_apply, mul_assoc, pow_succ]

/-- Left multiplication by `K` on a PBW monomial. -/
theorem k_mul_pbwBasis (a : ℕ) (b : ℤ) (c : ℕ) :
    k q * pbwBasis q (a, b, c) = (q⁻¹ ^ 2) ^ a • pbwBasis q (a, b + 1, c) := by
  rw [pbwBasis_apply, pbwBasis_apply, add_comm b 1, zpow_one_add, Units.val_mul, kUnit_val]
  simp only [← mul_assoc, k_mul_f_pow, smul_mul_assoc]

/-- Left multiplication by `K⁻¹` on a PBW monomial. -/
theorem kInv_mul_pbwBasis (a : ℕ) (b : ℤ) (c : ℕ) :
    kInv q * pbwBasis q (a, b, c) = (q ^ 2) ^ a • pbwBasis q (a, b - 1, c) := by
  rw [pbwBasis_apply, pbwBasis_apply, sub_eq_neg_add, zpow_add, zpow_neg_one, Units.val_mul,
    kUnit_inv]
  simp only [← mul_assoc, kInv_mul_f_pow, smul_mul_assoc]

/-- Right multiplication by `K` on a PBW monomial. -/
theorem pbwBasis_mul_k (a : ℕ) (b : ℤ) (c : ℕ) :
    pbwBasis q (a, b, c) * k q = (q⁻¹ ^ 2) ^ c • pbwBasis q (a, b + 1, c) := by
  have h := e_pow_mul_kUnit_zpow q c 1
  rw [zpow_one, kUnit_val] at h
  rw [pbwBasis_apply, pbwBasis_apply, mul_assoc, h, mul_smul_comm, zpow_add_one, Units.val_mul,
    kUnit_val, ← mul_assoc, ← mul_assoc]
  congr 1
  have hc : -2 * 1 * (c : ℤ) = -((2 * c : ℕ) : ℤ) := by push_cast; ring
  rw [hc, zpow_neg, zpow_natCast, pow_mul, inv_pow, inv_pow]

/-- Left multiplication by `E` on a PBW monomial: commuting `E` past `F ^ a` produces, besides
`q ^ (-2b) F ^ a * K ^ b * E ^ (c + 1)`, two monomials of `F`-exponent `a - 1`. -/
theorem e_mul_pbwBasis (a : ℕ) (b : ℤ) (c : ℕ) :
    e q * pbwBasis q (a, b, c) = q ^ (-2 * b) • pbwBasis q (a, b, c + 1) +
      (quantumInteger q a * (q - q⁻¹)⁻¹) •
        (q⁻¹ ^ (a - 1) • pbwBasis q (a - 1, b + 1, c) -
          q ^ (a - 1) • pbwBasis q (a - 1, b - 1, c)) := by
  have hk (x : UqSl2 q) : k q * (((kUnit q ^ b : (UqSl2 q)ˣ) : UqSl2 q) * x) =
      ((kUnit q ^ (b + 1) : (UqSl2 q)ˣ) : UqSl2 q) * x := by
    rw [← mul_assoc, add_comm b 1, zpow_one_add, Units.val_mul, kUnit_val]
  have hkInv (x : UqSl2 q) : kInv q * (((kUnit q ^ b : (UqSl2 q)ˣ) : UqSl2 q) * x) =
      ((kUnit q ^ (b - 1) : (UqSl2 q)ˣ) : UqSl2 q) * x := by
    rw [← mul_assoc, sub_eq_neg_add, zpow_add, zpow_neg_one, Units.val_mul, kUnit_inv]
  have he (x : UqSl2 q) : e q * (((kUnit q ^ b : (UqSl2 q)ˣ) : UqSl2 q) * x) =
      q ^ (-2 * b) • (((kUnit q ^ b : (UqSl2 q)ˣ) : UqSl2 q) * (e q * x)) := by
    rw [← mul_assoc, e_mul_kUnit_zpow, smul_mul_assoc, mul_assoc]
  rcases ne_or_eq (q - q⁻¹) 0 with hq | hq
  · have hef (x : UqSl2 q) : e q * (f q ^ a * x) = f q ^ a * (e q * x) +
        (quantumInteger q a * (q - q⁻¹)⁻¹) •
          (f q ^ (a - 1) * (q⁻¹ ^ (a - 1) • (k q * x) - q ^ (a - 1) • (kInv q * x))) := by
      rw [← mul_assoc, e_mul_f_pow hq]
      simp only [add_mul, smul_mul_assoc, sub_mul, mul_assoc]
    simp only [pbwBasis_apply, mul_assoc, hef, he, hk, hkInv, pow_succ', mul_smul_comm, mul_sub,
      smul_sub]
  · -- When `q - q⁻¹ = 0`, the commutator relation says that `E` and `F` commute.
    have hc : Commute (e q) (f q) :=
      sub_eq_zero.mp (by rw [e_mul_f_sub_f_mul_e, hq, inv_zero, zero_smul])
    simp only [pbwBasis_apply, hq, inv_zero, mul_zero, zero_smul, add_zero, mul_assoc]
    rw [← mul_assoc (e q), (hc.pow_right a).eq, mul_assoc, he, mul_smul_comm, pow_succ']

/-! ### PBW coordinates of products -/

/-- Right multiplication by `E` shifts the PBW coordinates in the exponent of `E`. -/
@[simp]
theorem pbwBasis_repr_mul_e (x : UqSl2 q) (a : ℕ) (b : ℤ) (c : ℕ) :
    (pbwBasis q).repr (x * e q) (a, b, c + 1) = (pbwBasis q).repr x (a, b, c) := by
  have hg : Function.Injective fun i : ℕ × ℤ × ℕ => (i.1, i.2.1, i.2.2 + 1) := by
    rintro ⟨a, b, c⟩ ⟨a', b', c'⟩ h
    simp only [Prod.mk.injEq, add_left_inj] at h
    simp [h]
  simpa using (pbwBasis q).repr_map_apply_of_map_eq_smul (pbwBasis q)
    (LinearMap.mulRight ℂ (e q)) hg (fun _ => 1)
    (fun ⟨a, b, c⟩ => by rw [LinearMap.mulRight_apply, pbwBasis_mul_e, one_smul]) x (a, b, c)

variable {q}

/-- **Weight-zero coordinates.** At a generic parameter, an element commuting with `K` has no PBW
coordinate at `F ^ a * K ^ b * E ^ c` with `a ≠ c`. -/
theorem pbwBasis_repr_eq_zero_of_commute_k (hq : IsGenericQuantumParameter q) {x : UqSl2 q}
    (hx : Commute (k q) x) {a : ℕ} (b : ℤ) {c : ℕ} (hac : a ≠ c) :
    (pbwBasis q).repr x (a, b, c) = 0 := by
  have hg : Function.Injective fun i : ℕ × ℤ × ℕ => (i.1, i.2.1 + 1, i.2.2) := by
    rintro ⟨a, b, c⟩ ⟨a', b', c'⟩ h
    simp only [Prod.mk.injEq, add_left_inj] at h
    simp [h]
  have hl := (pbwBasis q).repr_map_apply_of_map_eq_smul (pbwBasis q) (LinearMap.mulLeft ℂ (k q))
    hg (fun i => (q⁻¹ ^ 2) ^ i.1) (fun ⟨a, b, c⟩ => k_mul_pbwBasis q a b c) x (a, b, c)
  have hr := (pbwBasis q).repr_map_apply_of_map_eq_smul (pbwBasis q) (LinearMap.mulRight ℂ (k q))
    hg (fun i => (q⁻¹ ^ 2) ^ i.2.2) (fun ⟨a, b, c⟩ => pbwBasis_mul_k q a b c) x (a, b, c)
  simp only [LinearMap.mulLeft_apply, LinearMap.mulRight_apply, hx.eq] at hl hr
  rw [hl] at hr
  have hs : (q⁻¹ ^ 2) ^ a ≠ (q⁻¹ ^ 2) ^ c := fun h => hac <| by
    have := hq.inv.pow_injective (by simpa only [← pow_mul] using h)
    omega
  exact (mul_eq_mul_right_iff.mp hr).resolve_left hs

end TauCeti.UqSl2
