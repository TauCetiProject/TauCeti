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
import Mathlib.Tactic
import TauCeti.QuantumGroups.UqSl2.Commutator
import TauCeti.QuantumGroups.UqSl2.Rescale

/-!
# A PBW basis of `U_q(sl₂)`

For a nonzero parameter `q`, the monomials

`F ^ a * K ^ b * E ^ c`, with `a c : ℕ` and `b : ℤ`,

form a complex basis of `UqSl2 q`.  The construction transports the nested left-monomial bases
of the iterated Ore presentation.  Those bases initially put the Laurent monomial first, in the
order `K ^ b * F ^ a * E ^ c`; commuting `F ^ a` past `K ^ b` gives the displayed normalization.
Thus the coordinates supplied by `pbwBasis.repr` are the unique PBW coefficients of an element.

The second half of the file reads off how the generators act on PBW coordinates, which is the
input to leading-coefficient arguments such as the computation of the center.

* `TauCeti.UqSl2.pbwBasis_repr_eq_zero_of_commute_k`: at a generic parameter, an element
  commuting with `K` has no PBW monomial `F ^ a * K ^ b * E ^ c` with `a ≠ c`.
* `TauCeti.UqSl2.e_mul_pbwBasis_sub_mem`: left multiplication by `E` raises the `E`-exponent of a
  PBW monomial by one, with leading coefficient `q ^ (-2b)`, up to monomials with the same
  `E`-exponent.
* `TauCeti.UqSl2.pbwBasis_repr_of_raise`: for a linear map with this raising behaviour, the
  coordinates of the image with the new largest `E`-exponent are read off from the old ones.
* `TauCeti.UqSl2.pbwBasis_repr_eq_zero_of_commute_e`: at a generic parameter, an element
  commuting with `E` has no monomial `F ^ a * K ^ b * E ^ n` with `b ≠ 0` and `n` its largest
  `E`-exponent.

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

/-- Commuting `E` past an integer power of `K` multiplies by `q ^ (-2b)`. -/
theorem e_mul_kUnit_zpow (b : ℤ) :
    e q * ((kUnit q ^ b : (UqSl2 q)ˣ) : UqSl2 q) =
      q ^ (-2 * b) • (((kUnit q ^ b : (UqSl2 q)ˣ) : UqSl2 q) * e q) := by
  have h := kUnit_zpow_mul_e_mul_inv (q := q) (-b)
  rw [zpow_neg, inv_inv] at h
  have hconj : e q * ((kUnit q ^ b : (UqSl2 q)ˣ) : UqSl2 q) =
      ((kUnit q ^ b : (UqSl2 q)ˣ) : UqSl2 q) *
        (((kUnit q ^ b)⁻¹ : (UqSl2 q)ˣ) * e q * ((kUnit q ^ b : (UqSl2 q)ˣ) : UqSl2 q)) := by
    rw [mul_assoc, Units.mul_inv_cancel_left]
  rw [hconj, h, mul_smul_comm, mul_neg, neg_mul]

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

variable {q}

/-! ### Commuting with `K` -/

/-- **Weight-zero reduction.** At a generic parameter, an element commuting with `K` has no PBW
monomial `F ^ a * K ^ b * E ^ c` with `a ≠ c`. -/
theorem pbwBasis_repr_eq_zero_of_commute_k (hq : IsGenericQuantumParameter q) {z : UqSl2 q}
    (hz : Commute (k q) z) {a : ℕ} {b : ℤ} {c : ℕ} (hac : a ≠ c) :
    (pbwBasis q).repr z (a, b, c) = 0 := by
  set t : ℂˣ := Units.mk0 q Fact.out ^ 2
  -- `rescale q t` is conjugation by `K`, so it fixes `z`; it multiplies the PBW monomial
  -- `F ^ a * K ^ b * E ^ c` by `t⁻ᵃ tᶜ`.
  have hfix : rescale q t z = z := by
    rw [← toAlgEquiv_conjAct_kUnit, MulSemiringAction.toAlgEquiv_apply,
      ConjAct.units_smul_def, ConjAct.ofConjAct_toConjAct, kUnit_val, hz.eq, mul_assoc,
      kUnit_inv, k_mul_kInv, mul_one]
  have hcoord : ((pbwBasis q).coord (a, b, c)).comp (rescale q t).toLinearMap =
      (((t⁻¹ : ℂˣ) : ℂ) ^ a * (t : ℂ) ^ c) • (pbwBasis q).coord (a, b, c) := by
    refine (pbwBasis q).ext fun ⟨a', b', c'⟩ => ?_
    simp only [LinearMap.comp_apply, AlgEquiv.toLinearMap_apply, pbwBasis_apply,
      rescale_orderedMonomial, LinearMap.smul_apply]
    rw [← pbwBasis_apply, map_smul, Module.Basis.coord_apply, Module.Basis.repr_self]
    by_cases h : (a', b', c') = (a, b, c)
    · simp only [Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      simp
    · simp [h]
  have h := LinearMap.congr_fun hcoord z
  simp only [LinearMap.comp_apply, AlgEquiv.toLinearMap_apply, hfix, LinearMap.smul_apply,
    Module.Basis.coord_apply, smul_eq_mul] at h
  by_contra hne
  have hs := (mul_eq_right₀ hne).mp h.symm
  apply hac
  simp only [t, Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val, Units.val_mk0, inv_pow] at hs
  rw [inv_mul_eq_one₀ (pow_ne_zero _ (pow_ne_zero _ Fact.out)), ← pow_mul, ← pow_mul] at hs
  have := hq.pow_injective hs
  omega

/-! ### Raising the `E`-exponent -/

/-- Left multiplication by `E` raises the `E`-exponent of a PBW monomial by one, with leading
coefficient `q ^ (-2b)`, up to monomials with the same `E`-exponent. -/
theorem e_mul_pbwBasis_sub_mem (a : ℕ) (b : ℤ) (c : ℕ) :
    e q * pbwBasis q (a, b, c) - q ^ (-2 * b) • pbwBasis q (a, b, c + 1) ∈
      Submodule.span ℂ (pbwBasis q '' {i | i.2.2 = c}) := by
  cases a with
  | zero =>
    convert Submodule.zero_mem _
    rw [sub_eq_zero]
    simp only [pbwBasis_apply, pow_zero, one_mul, ← mul_assoc, e_mul_kUnit_zpow, smul_mul_assoc,
      pow_succ']
  | succ n =>
    obtain ⟨α, β, h⟩ := exists_e_mul_f_pow_succ (q := q) n
    have key : e q * pbwBasis q (n + 1, b, c) = q ^ (-2 * b) • pbwBasis q (n + 1, b, c + 1) +
        (α • pbwBasis q (n, b + 1, c) + β • pbwBasis q (n, b - 1, c)) := by
      simp only [pbwBasis_apply]
      rw [← mul_assoc, ← mul_assoc, h]
      simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, mul_assoc, e_mul_kUnit_zpow,
        k_mul_kUnit_zpow, kInv_mul_kUnit_zpow, pow_succ']
    rw [key, add_sub_cancel_left]
    exact add_mem (Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_image_of_mem _ rfl)))
      (Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_image_of_mem _ rfl)))

/-- Left multiplication by `F` raises the `F`-exponent of a PBW monomial by one. -/
theorem f_mul_pbwBasis (a : ℕ) (b : ℤ) (c : ℕ) :
    f q * pbwBasis q (a, b, c) = pbwBasis q (a + 1, b, c) := by
  simp only [pbwBasis_apply, pow_succ', mul_assoc]

/-- Let `ψ` be a linear endomorphism sending each PBW monomial `F ^ a * K ^ b * E ^ c` to
`s b • F ^ (a + d) * K ^ b * E ^ (c + 1)` modulo monomials with `E`-exponent `c`. If the
`E`-exponents of `x` are at most `n`, then those of `ψ x` are at most `n + 1`, and the
coordinates of `ψ x` with `E`-exponent `n + 1` are read off from those of `x` with `E`-exponent
`n`. -/
theorem pbwBasis_repr_of_raise {ψ : UqSl2 q →ₗ[ℂ] UqSl2 q} {d : ℕ} {s : ℤ → ℂ}
    (hψ : ∀ a b c, ψ (pbwBasis q (a, b, c)) - s b • pbwBasis q (a + d, b, c + 1) ∈
      Submodule.span ℂ (pbwBasis q '' {i | i.2.2 = c}))
    {x : UqSl2 q} {n : ℕ} (hx : ∀ i ∈ ((pbwBasis q).repr x).support, i.2.2 ≤ n) :
    (∀ i ∈ ((pbwBasis q).repr (ψ x)).support, i.2.2 ≤ n + 1) ∧
      ∀ a b, (pbwBasis q).repr (ψ x) (a + d, b, n + 1) = s b * (pbwBasis q).repr x (a, b, n) := by
  have hxs : x ∈ Submodule.span ℂ (pbwBasis q '' {i | i.2.2 ≤ n}) :=
    (pbwBasis q).mem_span_image.mpr fun i hi => hx i hi
  -- Each `ψ (F ^ a * K ^ b * E ^ c)` splits as its leading monomial plus a remainder.
  have hsplit (a : ℕ) (b : ℤ) (c : ℕ) : ∃ y ∈ Submodule.span ℂ (pbwBasis q '' {i | i.2.2 = c}),
      ψ (pbwBasis q (a, b, c)) = s b • pbwBasis q (a + d, b, c + 1) + y :=
    ⟨_, hψ a b c, (add_sub_cancel _ _).symm⟩
  constructor
  · suffices ψ x ∈ Submodule.span ℂ (pbwBasis q '' {i | i.2.2 ≤ n + 1}) from
      fun i hi => (pbwBasis q).mem_span_image.mp this hi
    refine (Submodule.span_le (p := (Submodule.span ℂ (pbwBasis q '' {i | i.2.2 ≤ n + 1})).comap
      ψ)).mpr ?_ hxs
    rintro _ ⟨⟨a, b, c⟩, hc, rfl⟩
    simp only [Set.mem_ofPred_eq] at hc
    obtain ⟨y, hy, hψy⟩ := hsplit a b c
    rw [SetLike.mem_coe, Submodule.mem_comap, hψy]
    refine add_mem (Submodule.smul_mem _ _ (Submodule.subset_span
      (Set.mem_image_of_mem _ (by simpa using hc)))) ?_
    refine Submodule.span_mono (Set.image_mono fun i hi => ?_) hy
    simp only [Set.mem_ofPred_eq] at hi ⊢
    omega
  · intro a b
    let ℓ : UqSl2 q →ₗ[ℂ] ℂ :=
      ((pbwBasis q).coord (a + d, b, n + 1)).comp ψ - s b • (pbwBasis q).coord (a, b, n)
    suffices ℓ x = 0 by simpa [ℓ, sub_eq_zero] using this
    refine (Submodule.span_le (p := LinearMap.ker ℓ)).mpr ?_ hxs
    rintro _ ⟨⟨a', b', c⟩, hc, rfl⟩
    obtain ⟨y, hy, hψy⟩ := hsplit a' b' c
    have hy0 : (pbwBasis q).repr y (a + d, b, n + 1) = 0 :=
      Finsupp.notMem_support_iff.mp fun h => by
        have h1 : n + 1 = c := (pbwBasis q).mem_span_image.mp hy h
        have h2 : c ≤ n := hc
        omega
    simp only [SetLike.mem_coe, LinearMap.mem_ker, ℓ, LinearMap.sub_apply, LinearMap.comp_apply,
      LinearMap.smul_apply, Module.Basis.coord_apply, hψy, map_add, map_smul,
      Module.Basis.repr_self, hy0, smul_eq_mul, add_zero]
    by_cases h : (a', b', c) = (a, b, n)
    · simp only [Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      simp
    · have h' : (a' + d, b', c + 1) ≠ (a + d, b, n + 1) := by
        simpa [Prod.mk.injEq] using h
      simp [h, h']

/-! ### Commuting with `E` -/

/-- At a generic parameter, an element commuting with `E` whose PBW monomials all have
`E`-exponent at most `n` has no monomial `F ^ a * K ^ b * E ^ n` with `b ≠ 0`. -/
theorem pbwBasis_repr_eq_zero_of_commute_e (hq : IsGenericQuantumParameter q)
    {z : UqSl2 q} (hz : Commute (e q) z) {n : ℕ}
    (hn : ∀ i ∈ ((pbwBasis q).repr z).support, i.2.2 ≤ n) (a : ℕ) {b : ℤ} (hb : b ≠ 0) :
    (pbwBasis q).repr z (a, b, n) = 0 := by
  have hψ (a : ℕ) (b : ℤ) (c : ℕ) :
      (LinearMap.mulLeft ℂ (e q) - LinearMap.mulRight ℂ (e q)) (pbwBasis q (a, b, c)) -
        (q ^ (-2 * b) - 1) • pbwBasis q (a + 0, b, c + 1) ∈
        Submodule.span ℂ (pbwBasis q '' {i | i.2.2 = c}) := by
    have hright : pbwBasis q (a, b, c) * e q = pbwBasis q (a, b, c + 1) := by
      simp only [pbwBasis_apply, pow_succ, mul_assoc]
    convert e_mul_pbwBasis_sub_mem a b c using 1
    simp only [LinearMap.sub_apply, LinearMap.mulLeft_apply, LinearMap.mulRight_apply, hright,
      add_zero, sub_smul, one_smul]
    abel
  have h := (pbwBasis_repr_of_raise hψ hn).2 a b
  simp only [LinearMap.sub_apply, LinearMap.mulLeft_apply, LinearMap.mulRight_apply, hz.eq,
    sub_self, map_zero, Finsupp.coe_zero, Pi.zero_apply] at h
  refine (mul_eq_zero.mp h.symm).resolve_left (sub_ne_zero.mpr fun h1 => hb ?_)
  have := hq.zpow_injective (h1.trans (zpow_zero q).symm)
  omega

end TauCeti.UqSl2
