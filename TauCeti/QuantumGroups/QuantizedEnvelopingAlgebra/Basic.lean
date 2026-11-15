/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Subalgebra.Basic
public import Mathlib.Algebra.FreeAlgebra
public import Mathlib.Algebra.RingQuot
public import TauCeti.LinearAlgebra.Matrix.Cartan.Datum.Hom
public import TauCeti.QuantumGroups.QuantumInteger.DividedPower

import Mathlib.Tactic

/-!
# The Drinfeld–Jimbo quantized enveloping algebra of a Cartan datum

Given a symmetrizable Cartan datum `D : CartanDatum ι X Y`, a field `K`, and a parameter `q : K`,
this file defines the quantized enveloping algebra `QuantizedEnvelopingAlgebra D q` over `K` by
generators `Eᵢ` (`i : ι`), `Fᵢ` (`i : ι`), and `K_y` (`y : Y`) subject to the group-algebra torus
relations `K_0 = 1` and `K_(y + z) = K_y K_z`, weight conjugations `K_y Eᵢ = q^⟨αᵢ, y⟩ Eᵢ K_y` and
`K_y Fᵢ = q^(-⟨αᵢ, y⟩) Fᵢ K_y`, commutators
`[Eᵢ, Fⱼ] = δᵢⱼ (qᵢ - qᵢ⁻¹)⁻¹ • (Kᵢ - Kᵢ⁻¹)` with `qᵢ = q^(dᵢ)` and `Kᵢ = K_(dᵢ hᵢ)`, and the
divided-power quantum Serre relations of length `1 - aᵢⱼ` for `i ≠ j`.

Toral generators are indexed by the full coweight lattice `Y`, retaining central and intermediate
isogeny directions, without finiteness or decidability assumptions on `ι` or freeness assumptions on
`X` and `Y`. At `q = 0` the weight relations force `Eᵢ = Fᵢ = 0`, so presentation-level commutation,
functoriality (`map`), and diagonal rescaling (`rescaleAlgEquiv`) hold for all `q : K`.

## References

* G. Lusztig, *Introduction to Quantum Groups*, Birkhäuser, 1993, §3.1.
* J. C. Jantzen, *Lectures on Quantum Groups*, American Mathematical Society, 1996, Chapter 4.
* S. Lentner, *Quantum groups and Nichols algebras acting on conformal field theories*, Adv. Math.
  268 (2014), Definition 3.2.
* K. McGerty, *Generalized `q`-Schur algebras and quantum Frobenius*, Adv. Math. 214 (2007), §2.
-/

public section

namespace TauCeti

namespace CartanDatum

section SerreLength

variable {ι X Y : Type*} [AddCommGroup X] [AddCommGroup Y] (D : CartanDatum ι X Y)

/-- The quantum Serre exponent `(1 - aᵢⱼ).toNat` between nodes `i` and `j`: equal to `1 - aᵢⱼ ≥ 1`
for `i ≠ j`, and `0` on the diagonal `i = j`. -/
def serreLength (i j : ι) : ℕ := (1 - D.cartan i j).toNat

lemma serreLength_def (i j : ι) : D.serreLength i j = (1 - D.cartan i j).toNat := (rfl)
@[simp] lemma serreLength_self (i : ι) : D.serreLength i i = 0 := by simp [serreLength_def]

/-- For distinct nodes `i ≠ j`, `aᵢⱼ ≤ 0`, so `(serreLength i j : ℤ) = 1 - aᵢⱼ`. -/
lemma serreLength_cast_of_ne {i j : ι} (hij : i ≠ j) :
    (D.serreLength i j : ℤ) = 1 - D.cartan i j := by
  have := D.cartan_nonpos hij; rw [serreLength_def, Int.toNat_of_nonneg (by omega)]

lemma serreLength_pos_of_ne {i j : ι} (hij : i ≠ j) : 0 < D.serreLength i j := by
  have := D.cartan_nonpos hij; have := D.serreLength_cast_of_ne hij; omega
lemma serreLength_ne_zero_of_ne {i j : ι} (hij : i ≠ j) : D.serreLength i j ≠ 0 :=
  (D.serreLength_pos_of_ne hij).ne'
lemma serreLength_of_cartan_eq_zero {i j : ι} (h : D.cartan i j = 0) : D.serreLength i j = 1 := by
  simp [serreLength_def, h]

/-- Symmetrizability `dᵢ aᵢⱼ = dⱼ aⱼᵢ` equates `(q^(dᵢ))^(aᵢⱼ)` and `(q^(dⱼ))^(aⱼᵢ)`. -/
lemma pow_symmetrizer_zpow_cartan {G₀ : Type*} [GroupWithZero G₀] (q : G₀) (i j : ι) :
    (q ^ D.symmetrizer i) ^ D.cartan i j = (q ^ D.symmetrizer j) ^ D.cartan j i := by
  rw [← zpow_natCast, ← zpow_mul, D.symmetrizer_mul_cartan, zpow_mul, zpow_natCast]

lemma Hom.serreLength_eq {X' Y' : Type*} [AddCommGroup X'] [AddCommGroup Y']
    {D : CartanDatum ι X Y} {D' : CartanDatum ι X' Y'} (φ : D.Hom D') (i j : ι) :
    D'.serreLength i j = D.serreLength i j := by simp [serreLength_def, φ.cartan_eq]

end SerreLength

end CartanDatum

namespace QuantizedEnvelopingAlgebra

/-- The formal generators `Eᵢ`, `Fᵢ` (`i : ι`), and `K_y` (`y : Y`) of a quantized enveloping
algebra. -/
inductive Generator (ι Y : Type*)
  | e (i : ι)
  | f (i : ι)
  | k (y : Y)
  deriving DecidableEq

/-- The Drinfeld–Jimbo defining relations on the free `K`-algebra on `Generator ι Y`. -/
inductive Rel {ι X Y K : Type*} [AddCommGroup X] [AddCommGroup Y] [Field K]
    (D : CartanDatum ι X Y) (q : K) :
    FreeAlgebra K (Generator ι Y) → FreeAlgebra K (Generator ι Y) → Prop
  | k_zero : Rel D q (FreeAlgebra.ι K (.k 0)) 1
  | k_add (y z : Y) :
      Rel D q (FreeAlgebra.ι K (.k (y + z))) (FreeAlgebra.ι K (.k y) * FreeAlgebra.ι K (.k z))
  | k_mul_e (i : ι) (y : Y) :
      Rel D q (FreeAlgebra.ι K (.k y) * FreeAlgebra.ι K (.e i))
        (q ^ D.pairing (D.root i) y • (FreeAlgebra.ι K (.e i) * FreeAlgebra.ι K (.k y)))
  | k_mul_f (i : ι) (y : Y) :
      Rel D q (FreeAlgebra.ι K (.k y) * FreeAlgebra.ι K (.f i))
        (q ^ (-D.pairing (D.root i) y) • (FreeAlgebra.ι K (.f i) * FreeAlgebra.ι K (.k y)))
  | commutator_self (i : ι) :
      Rel D q (FreeAlgebra.ι K (.e i) * FreeAlgebra.ι K (.f i) -
          FreeAlgebra.ι K (.f i) * FreeAlgebra.ι K (.e i))
        ((q ^ D.symmetrizer i - (q ^ D.symmetrizer i)⁻¹)⁻¹ •
          (FreeAlgebra.ι K (.k (D.simpleTorus i)) - FreeAlgebra.ι K (.k (-D.simpleTorus i))))
  | commutator_ne {i j : ι} (hij : i ≠ j) :
      Rel D q (FreeAlgebra.ι K (.e i) * FreeAlgebra.ι K (.f j) -
        FreeAlgebra.ι K (.f j) * FreeAlgebra.ι K (.e i)) 0
  | serre_e {i j : ι} (hij : i ≠ j) :
      Rel D q (quantumSerre (q ^ D.symmetrizer i) (D.serreLength i j)
        (FreeAlgebra.ι K (.e i)) (FreeAlgebra.ι K (.e j))) 0
  | serre_f {i j : ι} (hij : i ≠ j) :
      Rel D q (quantumSerre (q ^ D.symmetrizer i) (D.serreLength i j)
        (FreeAlgebra.ι K (.f i)) (FreeAlgebra.ι K (.f j))) 0

end QuantizedEnvelopingAlgebra

/-- The **Drinfeld–Jimbo quantized enveloping algebra** `U_q(D)` over `K` attached to a
symmetrizable Cartan datum `D : CartanDatum ι X Y` and parameter `q : K`. -/
@[expose]
def QuantizedEnvelopingAlgebra {ι X Y K : Type*} [AddCommGroup X] [AddCommGroup Y] [Field K]
    (D : CartanDatum ι X Y) (q : K) : Type _ :=
  RingQuot (QuantizedEnvelopingAlgebra.Rel D q)

namespace QuantizedEnvelopingAlgebra

section Basic

variable {ι X Y K : Type*} [AddCommGroup X] [AddCommGroup Y] [Field K]

instance (D : CartanDatum ι X Y) (q : K) : Ring (QuantizedEnvelopingAlgebra D q) :=
  inferInstanceAs (Ring (RingQuot (Rel D q)))
instance (D : CartanDatum ι X Y) (q : K) : Algebra K (QuantizedEnvelopingAlgebra D q) :=
  inferInstanceAs (Algebra K (RingQuot (Rel D q)))
instance (D : CartanDatum ι X Y) (q : K) : Inhabited (QuantizedEnvelopingAlgebra D q) := ⟨0⟩

/-- The canonical quotient algebra homomorphism onto `QuantizedEnvelopingAlgebra D q`. -/
def mkAlgHom (D : CartanDatum ι X Y) (q : K) :
    FreeAlgebra K (Generator ι Y) →ₐ[K] QuantizedEnvelopingAlgebra D q :=
  RingQuot.mkAlgHom K (Rel D q)

theorem mkAlgHom_surjective (D : CartanDatum ι X Y) (q : K) :
    Function.Surjective (mkAlgHom D q) := RingQuot.mkAlgHom_surjective K (Rel D q)
theorem mkAlgHom_rel {D : CartanDatum ι X Y} {q : K}
    {a b : FreeAlgebra K (Generator ι Y)} (h : Rel D q a b) : mkAlgHom D q a = mkAlgHom D q b :=
  RingQuot.mkAlgHom_rel K h

/-- The image of a formal generator in `QuantizedEnvelopingAlgebra D q`. -/
def generator (D : CartanDatum ι X Y) (q : K) (g : Generator ι Y) :
    QuantizedEnvelopingAlgebra D q := mkAlgHom D q (FreeAlgebra.ι K g)

@[simp] theorem mkAlgHom_ι (D : CartanDatum ι X Y) (q : K) (g : Generator ι Y) :
    mkAlgHom D q (FreeAlgebra.ι K g) = generator D q g := (rfl)

/-- The raising Chevalley generator `Eᵢ`. -/
def e (D : CartanDatum ι X Y) (q : K) (i : ι) : QuantizedEnvelopingAlgebra D q :=
  generator D q (.e i)
/-- The lowering Chevalley generator `Fᵢ`. -/
def f (D : CartanDatum ι X Y) (q : K) (i : ι) : QuantizedEnvelopingAlgebra D q :=
  generator D q (.f i)
/-- The toral generator `K_y` attached to a coweight `y ∈ Y`. -/
def k (D : CartanDatum ι X Y) (q : K) (y : Y) : QuantizedEnvelopingAlgebra D q :=
  generator D q (.k y)

@[simp] theorem generator_e (D : CartanDatum ι X Y) (q : K) (i : ι) :
    generator D q (.e i) = e D q i := (rfl)
@[simp] theorem generator_f (D : CartanDatum ι X Y) (q : K) (i : ι) :
    generator D q (.f i) = f D q i := (rfl)
@[simp] theorem generator_k (D : CartanDatum ι X Y) (q : K) (y : Y) :
    generator D q (.k y) = k D q y := (rfl)

/-- The simple toral generator `Kᵢ = K_(dᵢ hᵢ)`. -/
def simpleK (D : CartanDatum ι X Y) (q : K) (i : ι) : QuantizedEnvelopingAlgebra D q :=
  k D q (D.simpleTorus i)
theorem simpleK_def (D : CartanDatum ι X Y) (q : K) (i : ι) :
    simpleK D q i = k D q (D.simpleTorus i) := (rfl)

/-- The inverse simple toral generator `Kᵢ⁻¹ = K_(-dᵢ hᵢ)`. -/
def simpleKInv (D : CartanDatum ι X Y) (q : K) (i : ι) : QuantizedEnvelopingAlgebra D q :=
  k D q (-D.simpleTorus i)
theorem simpleKInv_def (D : CartanDatum ι X Y) (q : K) (i : ι) :
    simpleKInv D q i = k D q (-D.simpleTorus i) := (rfl)

variable {D : CartanDatum ι X Y} {q : K}

@[simp] theorem k_zero : k D q 0 = 1 := by
  simpa only [map_one, mkAlgHom_ι, generator_k] using mkAlgHom_rel (Rel.k_zero (D := D) (q := q))
theorem k_add (y z : Y) : k D q (y + z) = k D q y * k D q z := by
  simpa only [map_mul, mkAlgHom_ι, generator_k] using mkAlgHom_rel (Rel.k_add (D := D) (q := q) y z)
@[simp] theorem k_mul_k_neg (y : Y) : k D q y * k D q (-y) = 1 := by
  rw [← k_add, add_neg_cancel, k_zero]
@[simp] theorem k_neg_mul_k (y : Y) : k D q (-y) * k D q y = 1 := by
  rw [← k_add, neg_add_cancel, k_zero]
theorem commute_k (y z : Y) : Commute (k D q y) (k D q z) := by
  rw [Commute, SemiconjBy, ← k_add, ← k_add, add_comm]

/-- The toral generator `K_y` packaged as a unit with inverse `K_(-y)`. -/
def kUnit (D : CartanDatum ι X Y) (q : K) (y : Y) : (QuantizedEnvelopingAlgebra D q)ˣ :=
  ⟨k D q y, k D q (-y), k_mul_k_neg y, k_neg_mul_k y⟩

@[simp] theorem kUnit_val (y : Y) : (kUnit D q y : QuantizedEnvelopingAlgebra D q) = k D q y :=
  (rfl)
@[simp] theorem kUnit_inv (y : Y) : ↑(kUnit D q y)⁻¹ = k D q (-y) := (rfl)
@[simp] theorem k_mul_k_neg_mul (y : Y) (x : QuantizedEnvelopingAlgebra D q) :
    k D q y * (k D q (-y) * x) = x := Units.mul_inv_cancel_left (kUnit D q y) x
@[simp] theorem k_neg_mul_k_mul (y : Y) (x : QuantizedEnvelopingAlgebra D q) :
    k D q (-y) * (k D q y * x) = x := Units.inv_mul_cancel_left (kUnit D q y) x

theorem k_nsmul (n : ℕ) (y : Y) : k D q (n • y) = k D q y ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [succ_nsmul, k_add, ih, pow_succ]

theorem k_zsmul (m : ℤ) (y : Y) :
    k D q (m • y) = ((kUnit D q y ^ m : (QuantizedEnvelopingAlgebra D q)ˣ) :
      QuantizedEnvelopingAlgebra D q) := by
  cases m with
  | ofNat n => simp [k_nsmul]
  | negSucc n =>
    rw [negSucc_zsmul, zpow_negSucc, ← inv_pow, Units.val_pow_eq_pow_val, kUnit_inv, ← k_nsmul,
      ← smul_neg]

@[simp] theorem simpleK_mul_simpleKInv (i : ι) : simpleK D q i * simpleKInv D q i = 1 :=
  k_mul_k_neg (D.simpleTorus i)
@[simp] theorem simpleKInv_mul_simpleK (i : ι) : simpleKInv D q i * simpleK D q i = 1 :=
  k_neg_mul_k (D.simpleTorus i)
@[simp] theorem simpleK_mul_simpleKInv_mul (i : ι) (x : QuantizedEnvelopingAlgebra D q) :
    simpleK D q i * (simpleKInv D q i * x) = x := k_mul_k_neg_mul (D.simpleTorus i) x
@[simp] theorem simpleKInv_mul_simpleK_mul (i : ι) (x : QuantizedEnvelopingAlgebra D q) :
    simpleKInv D q i * (simpleK D q i * x) = x := k_neg_mul_k_mul (D.simpleTorus i) x
theorem simpleK_pow (i : ι) (n : ℕ) : simpleK D q i ^ n = k D q (n • D.simpleTorus i) :=
  (k_nsmul n (D.simpleTorus i)).symm
theorem simpleKInv_pow (i : ι) (n : ℕ) : simpleKInv D q i ^ n = k D q (-(n • D.simpleTorus i)) := by
  rw [simpleKInv_def, ← k_nsmul, smul_neg]

/-- The defining commutation relation `K_y * Eᵢ = q^⟨αᵢ, y⟩ • (Eᵢ * K_y)`. -/
theorem k_mul_e (i : ι) (y : Y) :
    k D q y * e D q i = q ^ D.pairing (D.root i) y • (e D q i * k D q y) := by
  simpa only [map_mul, map_smul, mkAlgHom_ι, generator_k, generator_e] using
    mkAlgHom_rel (Rel.k_mul_e (D := D) (q := q) i y)

/-- The defining commutation relation `K_y * Fᵢ = q^(-⟨αᵢ, y⟩) • (Fᵢ * K_y)`. -/
theorem k_mul_f (i : ι) (y : Y) :
    k D q y * f D q i = q ^ (-D.pairing (D.root i) y) • (f D q i * k D q y) := by
  simpa only [map_mul, map_smul, mkAlgHom_ι, generator_k, generator_f] using
    mkAlgHom_rel (Rel.k_mul_f (D := D) (q := q) i y)

theorem k_mul_e_mul_k_neg (i : ι) (y : Y) :
    k D q y * e D q i * k D q (-y) = q ^ D.pairing (D.root i) y • e D q i := by
  rw [k_mul_e, smul_mul_assoc, mul_assoc, k_mul_k_neg, mul_one]
theorem k_mul_f_mul_k_neg (i : ι) (y : Y) :
    k D q y * f D q i * k D q (-y) = q ^ (-D.pairing (D.root i) y) • f D q i := by
  rw [k_mul_f, smul_mul_assoc, mul_assoc, k_mul_k_neg, mul_one]

theorem e_mul_k (i : ι) (y : Y) :
    e D q i * k D q y = q ^ (-D.pairing (D.root i) y) • (k D q y * e D q i) := by
  rw [← k_mul_k_neg_mul y (e D q i * k D q y), ← mul_assoc (k D q (-y)), k_mul_e i (-y),
    map_neg, smul_mul_assoc, mul_smul_comm, mul_assoc, k_neg_mul_k, mul_one]
theorem f_mul_k (i : ι) (y : Y) :
    f D q i * k D q y = q ^ D.pairing (D.root i) y • (k D q y * f D q i) := by
  rw [← k_mul_k_neg_mul y (f D q i * k D q y), ← mul_assoc (k D q (-y)), k_mul_f i (-y),
    map_neg, neg_neg, smul_mul_assoc, mul_smul_comm, mul_assoc, k_neg_mul_k, mul_one]

@[simp] theorem e_zero (i : ι) : e D (0 : K) i = 0 := by
  rw [← k_neg_mul_k_mul (D.coroot i) (e D (0 : K) i), k_mul_e, D.pairing_root_coroot_self]; simp
@[simp] theorem f_zero (i : ι) : f D (0 : K) i = 0 := by
  rw [← k_mul_k_neg_mul (D.coroot i) (f D (0 : K) i), k_mul_f, map_neg, neg_neg,
    D.pairing_root_coroot_self]; simp

private theorem pairing_simpleTorus_zpow (i j : ι) :
    q ^ D.pairing (D.root j) (D.simpleTorus i) = (q ^ D.symmetrizer i) ^ D.cartan i j := by
  rw [D.pairing_root_simpleTorus, ← D.symmetrizer_mul_cartan, zpow_mul, zpow_natCast]

theorem simpleK_mul_e (i j : ι) :
    simpleK D q i * e D q j =
      (q ^ D.symmetrizer i) ^ D.cartan i j • (e D q j * simpleK D q i) := by
  rw [simpleK_def, k_mul_e, pairing_simpleTorus_zpow]
theorem e_mul_simpleKInv (i j : ι) :
    e D q j * simpleKInv D q i =
      (q ^ D.symmetrizer i) ^ D.cartan i j • (simpleKInv D q i * e D q j) := by
  rw [simpleKInv_def, e_mul_k, map_neg, neg_neg, pairing_simpleTorus_zpow]
theorem simpleKInv_mul_e (i j : ι) :
    simpleKInv D q i * e D q j =
      (q ^ D.symmetrizer i) ^ (-D.cartan i j) • (e D q j * simpleKInv D q i) := by
  rw [simpleKInv_def, k_mul_e, map_neg, zpow_neg, pairing_simpleTorus_zpow, zpow_neg]
theorem simpleK_mul_f (i j : ι) :
    simpleK D q i * f D q j =
      (q ^ D.symmetrizer i) ^ (-D.cartan i j) • (f D q j * simpleK D q i) := by
  rw [simpleK_def, k_mul_f, zpow_neg, pairing_simpleTorus_zpow, zpow_neg]
theorem simpleKInv_mul_f (i j : ι) :
    simpleKInv D q i * f D q j =
      (q ^ D.symmetrizer i) ^ D.cartan i j • (f D q j * simpleKInv D q i) := by
  rw [simpleKInv_def, k_mul_f, map_neg, neg_neg, pairing_simpleTorus_zpow]
theorem f_mul_simpleK (i j : ι) :
    f D q j * simpleK D q i =
      (q ^ D.symmetrizer i) ^ D.cartan i j • (simpleK D q i * f D q j) := by
  rw [simpleK_def, f_mul_k, pairing_simpleTorus_zpow]

/-- The diagonal commutator relation `Eᵢ Fᵢ - Fᵢ Eᵢ = (qᵢ - qᵢ⁻¹)⁻¹ • (Kᵢ - Kᵢ⁻¹)`. -/
theorem e_mul_f_sub_f_mul_e_self (i : ι) :
    e D q i * f D q i - f D q i * e D q i =
      (q ^ D.symmetrizer i - (q ^ D.symmetrizer i)⁻¹)⁻¹ •
        (simpleK D q i - simpleKInv D q i) := by
  simpa only [map_sub, map_mul, map_smul, mkAlgHom_ι, generator_e, generator_f, generator_k,
    ← simpleK_def, ← simpleKInv_def] using mkAlgHom_rel (Rel.commutator_self (D := D) (q := q) i)

theorem e_mul_f_sub_f_mul_e_ne {i j : ι} (hij : i ≠ j) :
    e D q i * f D q j - f D q j * e D q i = 0 := by
  simpa only [map_sub, map_mul, map_zero, mkAlgHom_ι, generator_e, generator_f] using
    mkAlgHom_rel (Rel.commutator_ne (D := D) (q := q) hij)
theorem e_mul_f_of_ne {i j : ι} (hij : i ≠ j) : e D q i * f D q j = f D q j * e D q i :=
  sub_eq_zero.mp (e_mul_f_sub_f_mul_e_ne hij)

/-- Combined Kronecker-delta form of the `[Eᵢ, Fⱼ]` commutator relation. -/
theorem e_mul_f_sub_f_mul_e [DecidableEq ι] (i j : ι) :
    e D q i * f D q j - f D q j * e D q i =
      if i = j then
        (q ^ D.symmetrizer i - (q ^ D.symmetrizer i)⁻¹)⁻¹ • (simpleK D q i - simpleKInv D q i)
      else 0 := by
  split_ifs with hij; · exact hij ▸ e_mul_f_sub_f_mul_e_self i
  exact e_mul_f_sub_f_mul_e_ne hij

/-- The raising quantum Serre relation for `i ≠ j`. -/
theorem serre_e_eq_zero {i j : ι} (hij : i ≠ j) :
    quantumSerre (q ^ D.symmetrizer i) (D.serreLength i j) (e D q i) (e D q j) = 0 := by
  simpa only [AlgHom.map_quantumSerre, map_zero, mkAlgHom_ι, generator_e] using
    mkAlgHom_rel (Rel.serre_e (D := D) (q := q) hij)

/-- The lowering quantum Serre relation for `i ≠ j`. -/
theorem serre_f_eq_zero {i j : ι} (hij : i ≠ j) :
    quantumSerre (q ^ D.symmetrizer i) (D.serreLength i j) (f D q i) (f D q j) = 0 := by
  simpa only [AlgHom.map_quantumSerre, map_zero, mkAlgHom_ι, generator_f] using
    mkAlgHom_rel (Rel.serre_f (D := D) (q := q) hij)

private theorem sub_inv_ne_zero_of_sq_ne_one {u : K} (hu₀ : u ≠ 0) (hu : u ^ 2 ≠ 1) :
    u - u⁻¹ ≠ 0 := fun h0 =>
  hu (by have h := mul_inv_cancel₀ hu₀; rwa [← sub_eq_zero.mp h0, ← sq] at h)

/-- When `aᵢⱼ = 0` and `(q^(dᵢ))² ≠ 1`, the raising generators `Eᵢ` and `Eⱼ` commute. -/
theorem e_mul_e_of_cartan_eq_zero {i j : ι} (h : D.cartan i j = 0)
    (hq : (q ^ D.symmetrizer i) ^ 2 ≠ 1) : e D q i * e D q j = e D q j * e D q i := by
  rcases eq_or_ne q 0 with rfl | hq₀; · simp
  have hserre := serre_e_eq_zero (D := D) (q := q) (by rintro rfl; simp at h : i ≠ j)
  rw [D.serreLength_of_cartan_eq_zero h,
    quantumSerre_one (sub_inv_ne_zero_of_sq_ne_one (pow_ne_zero _ hq₀) hq)] at hserre
  exact (sub_eq_zero.mp hserre).symm

/-- When `aᵢⱼ = 0` and `(q^(dᵢ))² ≠ 1`, the lowering generators `Fᵢ` and `Fⱼ` commute. -/
theorem f_mul_f_of_cartan_eq_zero {i j : ι} (h : D.cartan i j = 0)
    (hq : (q ^ D.symmetrizer i) ^ 2 ≠ 1) : f D q i * f D q j = f D q j * f D q i := by
  rcases eq_or_ne q 0 with rfl | hq₀; · simp
  have hserre := serre_f_eq_zero (D := D) (q := q) (by rintro rfl; simp at h : i ≠ j)
  rw [D.serreLength_of_cartan_eq_zero h,
    quantumSerre_one (sub_inv_ne_zero_of_sq_ne_one (pow_ne_zero _ hq₀) hq)] at hserre
  exact (sub_eq_zero.mp hserre).symm

end Basic

section UniversalProperty

variable {ι X Y K : Type*} [AddCommGroup X] [AddCommGroup Y] [Field K]

/-- A family of elements `(eᵢ), (fᵢ), (k_y)` in a `K`-algebra `A` satisfying the defining
Drinfeld–Jimbo relations of `QuantizedEnvelopingAlgebra D q`. -/
structure GeneratorTuple (D : CartanDatum ι X Y) (q : K) (A : Type*) [Ring A] [Algebra K A] where
  /-- Proposed images of the raising generators `Eᵢ`. -/
  e : ι → A
  /-- Proposed images of the lowering generators `Fᵢ`. -/
  f : ι → A
  /-- Proposed images of the toral generators `K_y`. -/
  k : Y → A
  k_zero : k 0 = 1
  k_add (y z : Y) : k (y + z) = k y * k z
  k_mul_e (i : ι) (y : Y) : k y * e i = q ^ D.pairing (D.root i) y • (e i * k y)
  k_mul_f (i : ι) (y : Y) : k y * f i = q ^ (-D.pairing (D.root i) y) • (f i * k y)
  commutator_self (i : ι) :
    e i * f i - f i * e i =
      (q ^ D.symmetrizer i - (q ^ D.symmetrizer i)⁻¹)⁻¹ •
        (k (D.simpleTorus i) - k (-D.simpleTorus i))
  commutator_ne {i j : ι} (hij : i ≠ j) : e i * f j - f j * e i = 0
  serre_e {i j : ι} (hij : i ≠ j) :
    quantumSerre (q ^ D.symmetrizer i) (D.serreLength i j) (e i) (e j) = 0
  serre_f {i j : ι} (hij : i ≠ j) :
    quantumSerre (q ^ D.symmetrizer i) (D.serreLength i j) (f i) (f j) = 0

namespace GeneratorTuple

variable {D : CartanDatum ι X Y} {q : K} {A : Type*} [Ring A] [Algebra K A]

/-- Evaluation of a `GeneratorTuple` on formal generators. -/
def toFun (t : GeneratorTuple D q A) : Generator ι Y → A
  | .e i => t.e i
  | .f i => t.f i
  | .k y => t.k y

@[simp] theorem toFun_e (t : GeneratorTuple D q A) (i : ι) : t.toFun (.e i) = t.e i := (rfl)
@[simp] theorem toFun_f (t : GeneratorTuple D q A) (i : ι) : t.toFun (.f i) = t.f i := (rfl)
@[simp] theorem toFun_k (t : GeneratorTuple D q A) (y : Y) : t.toFun (.k y) = t.k y := (rfl)

@[ext] theorem ext {s t : GeneratorTuple D q A}
    (he : ∀ i, s.e i = t.e i) (hf : ∀ i, s.f i = t.f i) (hk : ∀ y, s.k y = t.k y) : s = t := by
  cases s; cases t; simp only [mk.injEq]; exact ⟨funext he, funext hf, funext hk⟩

end GeneratorTuple

section Lift

variable {D : CartanDatum ι X Y} {q : K} {A : Type*} [Ring A] [Algebra K A]

/-- The universal property of `QuantizedEnvelopingAlgebra D q`: a `GeneratorTuple` extends to a
`K`-algebra homomorphism. -/
def lift (t : GeneratorTuple D q A) : QuantizedEnvelopingAlgebra D q →ₐ[K] A :=
  RingQuot.liftAlgHom K ⟨FreeAlgebra.lift K t.toFun, by
    rintro a b (_ | ⟨y, z⟩ | ⟨i, y⟩ | ⟨i, y⟩ | ⟨i⟩ | @⟨i, j, hij⟩ | @⟨i, j, hij⟩ | @⟨i, j, hij⟩)
    exacts [by simpa using t.k_zero, by simpa using t.k_add y z, by simpa using t.k_mul_e i y,
      by simpa using t.k_mul_f i y, by simpa using t.commutator_self i,
      by simpa using t.commutator_ne hij, by simpa using t.serre_e hij,
      by simpa using t.serre_f hij]⟩

@[simp] theorem lift_generator (t : GeneratorTuple D q A) (g : Generator ι Y) :
    lift t (generator D q g) = t.toFun g :=
  (RingQuot.liftAlgHom_mkAlgHom_apply K _ _ _).trans (FreeAlgebra.lift_ι_apply _ _)
@[simp] theorem lift_e (t : GeneratorTuple D q A) (i : ι) : lift t (e D q i) = t.e i :=
  lift_generator t (.e i)
@[simp] theorem lift_f (t : GeneratorTuple D q A) (i : ι) : lift t (f D q i) = t.f i :=
  lift_generator t (.f i)
@[simp] theorem lift_k (t : GeneratorTuple D q A) (y : Y) : lift t (k D q y) = t.k y :=
  lift_generator t (.k y)
@[simp] theorem lift_simpleK (t : GeneratorTuple D q A) (i : ι) :
    lift t (simpleK D q i) = t.k (D.simpleTorus i) := lift_k t (D.simpleTorus i)
@[simp] theorem lift_simpleKInv (t : GeneratorTuple D q A) (i : ι) :
    lift t (simpleKInv D q i) = t.k (-D.simpleTorus i) := lift_k t (-D.simpleTorus i)

/-- Two `K`-algebra homomorphisms from `QuantizedEnvelopingAlgebra D q` agreeing on `Eᵢ`, `Fᵢ`,
and `K_y` are equal. -/
@[ext high]
theorem hom_ext {φ ψ : QuantizedEnvelopingAlgebra D q →ₐ[K] A}
    (he : ∀ i, φ (e D q i) = ψ (e D q i)) (hf : ∀ i, φ (f D q i) = ψ (f D q i))
    (hk : ∀ y, φ (k D q y) = ψ (k D q y)) : φ = ψ := by
  refine RingQuot.ringQuot_ext' K φ ψ (FreeAlgebra.hom_ext (funext fun g => ?_))
  cases g; exacts [he _, hf _, hk _]

/-- `K`-algebra homomorphisms out of `QuantizedEnvelopingAlgebra D q` are equivalent to
`GeneratorTuple D q A`. -/
def liftEquiv : (QuantizedEnvelopingAlgebra D q →ₐ[K] A) ≃ GeneratorTuple D q A where
  toFun φ :=
    { e i := φ (e D q i), f i := φ (f D q i), k y := φ (k D q y),
      k_zero := by rw [k_zero, map_one]
      k_add y z := by rw [k_add, map_mul]
      k_mul_e i y := by simpa only [map_mul, map_smul] using congrArg φ (k_mul_e i y)
      k_mul_f i y := by simpa only [map_mul, map_smul] using congrArg φ (k_mul_f i y)
      commutator_self i := by
        simpa only [map_sub, map_mul, map_smul, simpleK_def, simpleKInv_def] using
          congrArg φ (e_mul_f_sub_f_mul_e_self i)
      commutator_ne hij := by
        simpa only [map_sub, map_mul, map_zero] using congrArg φ (e_mul_f_sub_f_mul_e_ne hij)
      serre_e hij := by
        simpa only [AlgHom.map_quantumSerre, map_zero] using congrArg φ (serre_e_eq_zero hij)
      serre_f hij := by
        simpa only [AlgHom.map_quantumSerre, map_zero] using congrArg φ (serre_f_eq_zero hij) }
  invFun := lift
  left_inv _ := hom_ext (by simp) (by simp) (by simp)
  right_inv _ := by ext <;> simp

@[simp] theorem liftEquiv_apply_e (φ : QuantizedEnvelopingAlgebra D q →ₐ[K] A) (i : ι) :
    (liftEquiv φ).e i = φ (e D q i) := (rfl)
@[simp] theorem liftEquiv_apply_f (φ : QuantizedEnvelopingAlgebra D q →ₐ[K] A) (i : ι) :
    (liftEquiv φ).f i = φ (f D q i) := (rfl)
@[simp] theorem liftEquiv_apply_k (φ : QuantizedEnvelopingAlgebra D q →ₐ[K] A) (y : Y) :
    (liftEquiv φ).k y = φ (k D q y) := (rfl)
@[simp] theorem liftEquiv_symm_apply (t : GeneratorTuple D q A) : liftEquiv.symm t = lift t :=
  (rfl)

end Lift

/-- The formal generators `Eᵢ`, `Fᵢ`, and `K_y` generate `QuantizedEnvelopingAlgebra D q` as a
`K`-algebra. -/
theorem adjoin_range_generator (D : CartanDatum ι X Y) (q : K) :
    Algebra.adjoin K (Set.range (generator D q)) = ⊤ := by
  have h : FreeAlgebra.lift K (generator D q) = mkAlgHom D q :=
    FreeAlgebra.hom_ext (funext <| by simp)
  rw [Algebra.adjoin_range_eq_range_freeAlgebra_lift, h, AlgHom.range_eq_top]
  exact mkAlgHom_surjective D q

variable {D : CartanDatum ι X Y} {q : K}

/-- Structural induction on `QuantizedEnvelopingAlgebra D q` from scalars and generators `Eᵢ`,
`Fᵢ`, `K_y` under multiplication and addition. -/
@[elab_as_elim]
theorem induction {P : QuantizedEnvelopingAlgebra D q → Prop}
    (algebraMap : ∀ c : K, P (algebraMap K (QuantizedEnvelopingAlgebra D q) c))
    (e : ∀ i, P (QuantizedEnvelopingAlgebra.e D q i))
    (f : ∀ i, P (QuantizedEnvelopingAlgebra.f D q i))
    (k : ∀ y, P (QuantizedEnvelopingAlgebra.k D q y))
    (mul : ∀ a b, P a → P b → P (a * b)) (add : ∀ a b, P a → P b → P (a + b))
    (x : QuantizedEnvelopingAlgebra D q) : P x := by
  have hx : x ∈ Algebra.adjoin K (Set.range (generator D q)) :=
    (adjoin_range_generator D q).symm ▸ Algebra.mem_top
  induction hx using Algebra.adjoin_induction with
  | mem _ ha => obtain ⟨g, rfl⟩ := ha; cases g; exacts [e _, f _, k _]
  | algebraMap c => exact algebraMap c
  | add a b _ _ ha hb => exact add a b ha hb
  | mul a b _ _ ha hb => exact mul a b ha hb

theorem commute_of_commute_generators {z : QuantizedEnvelopingAlgebra D q}
    (he : ∀ i, Commute (e D q i) z) (hf : ∀ i, Commute (f D q i) z)
    (hk : ∀ y, Commute (k D q y) z) (a : QuantizedEnvelopingAlgebra D q) : Commute a z := by
  refine (Algebra.commute_of_mem_adjoin_of_forall_mem_commute (R := K)
    (s := Set.range (generator D q)) ((adjoin_range_generator D q).symm ▸ Algebra.mem_top) ?_).symm
  rintro _ ⟨g, rfl⟩; cases g; exacts [(he _).symm, (hf _).symm, (hk _).symm]

/-- For a coweight `c ∈ Y` annihilated by every simple root (`⟨αᵢ, c⟩ = 0` for all `i`), the toral
generator `K_c` lies in the center of `QuantizedEnvelopingAlgebra D q`. -/
theorem k_mem_center_of_pairing_root_eq_zero {c : Y} (hc : ∀ i, D.pairing (D.root i) c = 0) :
    k D q c ∈ Subalgebra.center K (QuantizedEnvelopingAlgebra D q) := by
  rw [Subalgebra.mem_center_iff]
  refine commute_of_commute_generators (fun i => ?_) (fun i => ?_) (fun y => commute_k y c)
  · rw [Commute, SemiconjBy, k_mul_e, hc i, zpow_zero, one_smul]
  · rw [Commute, SemiconjBy, k_mul_f, hc i, neg_zero, zpow_zero, one_smul]

end UniversalProperty

section Map

variable {ι X Y X' Y' X'' Y'' K : Type*} [AddCommGroup X] [AddCommGroup Y]
  [AddCommGroup X'] [AddCommGroup Y'] [AddCommGroup X''] [AddCommGroup Y''] [Field K]
  {D : CartanDatum ι X Y} {D' : CartanDatum ι X' Y'}

/-- A morphism of Cartan data `φ : D.Hom D'` induces a `K`-algebra homomorphism
`QuantizedEnvelopingAlgebra D q →ₐ[K] QuantizedEnvelopingAlgebra D' q` sending `Eᵢ ↦ Eᵢ`,
`Fᵢ ↦ Fᵢ`, and `K_y ↦ K_(φ y)`. -/
def map (φ : D.Hom D') (q : K) :
    QuantizedEnvelopingAlgebra D q →ₐ[K] QuantizedEnvelopingAlgebra D' q :=
  lift
    { e i := e D' q i, f i := f D' q i, k y := k D' q (φ.toLinearMap y), k_zero := (by simp),
      k_add y z := by rw [map_add, k_add]
      k_mul_e i y := by rw [k_mul_e, φ.pairing_root_map]
      k_mul_f i y := by rw [k_mul_f, φ.pairing_root_map]
      commutator_self i := by
        rw [e_mul_f_sub_f_mul_e_self, φ.symmetrizer_eq, simpleK_def, simpleKInv_def,
          ← φ.map_simpleTorus, map_neg]
      commutator_ne hij := e_mul_f_sub_f_mul_e_ne hij
      serre_e hij := by rw [← φ.symmetrizer_eq, ← φ.serreLength_eq]; exact serre_e_eq_zero hij
      serre_f hij := by rw [← φ.symmetrizer_eq, ← φ.serreLength_eq]; exact serre_f_eq_zero hij }

@[simp] theorem map_e (φ : D.Hom D') {q : K} (i : ι) : map φ q (e D q i) = e D' q i := lift_e _ i
@[simp] theorem map_f (φ : D.Hom D') {q : K} (i : ι) : map φ q (f D q i) = f D' q i := lift_f _ i
@[simp] theorem map_k (φ : D.Hom D') {q : K} (y : Y) :
    map φ q (k D q y) = k D' q (φ.toLinearMap y) := lift_k _ y
@[simp] theorem map_simpleK (φ : D.Hom D') {q : K} (i : ι) :
    map φ q (simpleK D q i) = simpleK D' q i := by
  rw [simpleK_def, map_k, φ.map_simpleTorus, ← simpleK_def]
@[simp] theorem map_simpleKInv (φ : D.Hom D') {q : K} (i : ι) :
    map φ q (simpleKInv D q i) = simpleKInv D' q i := by
  rw [simpleKInv_def, map_k, map_neg, φ.map_simpleTorus, ← simpleKInv_def]
@[simp] theorem map_id (D : CartanDatum ι X Y) (q : K) :
    map (CartanDatum.Hom.id D) q = AlgHom.id K (QuantizedEnvelopingAlgebra D q) := by ext <;> simp
theorem map_comp {D'' : CartanDatum ι X'' Y''} (ψ : D'.Hom D'') (φ : D.Hom D') (q : K) :
    map (ψ.comp φ) q = (map ψ q).comp (map φ q) := by ext <;> simp

end Map

section Rescale

variable {ι X Y K : Type*} [AddCommGroup X] [AddCommGroup Y] [Field K]

/-- Rescaling `Eᵢ ↦ cᵢ • Eᵢ`, `Fᵢ ↦ cᵢ⁻¹ • Fᵢ`, and `K_y ↦ K_y` for `c : ι → Kˣ` defines an
endomorphism of `QuantizedEnvelopingAlgebra D q`. -/
def rescaleAlgHom (D : CartanDatum ι X Y) (q : K) (c : ι → Kˣ) :
    QuantizedEnvelopingAlgebra D q →ₐ[K] QuantizedEnvelopingAlgebra D q :=
  lift
    { e i := (c i : K) • e D q i, f i := ((c i : K))⁻¹ • f D q i, k y := k D q y,
      k_zero := k_zero, k_add := k_add,
      k_mul_e i y := by rw [mul_smul_comm, k_mul_e, smul_comm, smul_mul_assoc]
      k_mul_f i y := by rw [mul_smul_comm, k_mul_f, smul_comm, smul_mul_assoc]
      commutator_self i := by
        rw [smul_mul_smul_comm, smul_mul_smul_comm, mul_inv_cancel₀ (c i).ne_zero,
          inv_mul_cancel₀ (c i).ne_zero, one_smul, one_smul, e_mul_f_sub_f_mul_e_self,
          simpleK_def, simpleKInv_def]
      commutator_ne {i j} hij := by
        rw [smul_mul_smul_comm, smul_mul_smul_comm, mul_comm ((c j : K))⁻¹, ← smul_sub,
          e_mul_f_sub_f_mul_e_ne hij, smul_zero]
      serre_e hij := by rw [quantumSerre_smul, serre_e_eq_zero hij, smul_zero]
      serre_f hij := by rw [quantumSerre_smul, serre_f_eq_zero hij, smul_zero] }

variable {D : CartanDatum ι X Y} {q : K}

@[simp] theorem rescaleAlgHom_e (c : ι → Kˣ) (i : ι) :
    rescaleAlgHom D q c (e D q i) = (c i : K) • e D q i := lift_e _ i
@[simp] theorem rescaleAlgHom_f (c : ι → Kˣ) (i : ι) :
    rescaleAlgHom D q c (f D q i) = (c i : K)⁻¹ • f D q i := lift_f _ i
@[simp] theorem rescaleAlgHom_k (c : ι → Kˣ) (y : Y) :
    rescaleAlgHom D q c (k D q y) = k D q y := lift_k _ y
@[simp] theorem rescaleAlgHom_one :
    rescaleAlgHom D q 1 = AlgHom.id K (QuantizedEnvelopingAlgebra D q) := by ext <;> simp
theorem rescaleAlgHom_mul (c d : ι → Kˣ) :
    rescaleAlgHom D q (c * d) = (rescaleAlgHom D q c).comp (rescaleAlgHom D q d) := by
  ext <;> simp [smul_smul, mul_comm]

/-- The `K`-algebra automorphism rescaling `Eᵢ ↦ cᵢ • Eᵢ`, `Fᵢ ↦ cᵢ⁻¹ • Fᵢ`, and fixing `K_y`. -/
def rescaleAlgEquiv (D : CartanDatum ι X Y) (q : K) (c : ι → Kˣ) :
    QuantizedEnvelopingAlgebra D q ≃ₐ[K] QuantizedEnvelopingAlgebra D q :=
  AlgEquiv.ofAlgHom (rescaleAlgHom D q c) (rescaleAlgHom D q c⁻¹)
    (by rw [← rescaleAlgHom_mul, mul_inv_cancel, rescaleAlgHom_one])
    (by rw [← rescaleAlgHom_mul, inv_mul_cancel, rescaleAlgHom_one])

@[simp] theorem rescaleAlgEquiv_toAlgHom (c : ι → Kˣ) :
    (rescaleAlgEquiv D q c).toAlgHom = rescaleAlgHom D q c := (rfl)
@[simp] theorem rescaleAlgEquiv_e (c : ι → Kˣ) (i : ι) :
    rescaleAlgEquiv D q c (e D q i) = (c i : K) • e D q i := rescaleAlgHom_e c i
@[simp] theorem rescaleAlgEquiv_f (c : ι → Kˣ) (i : ι) :
    rescaleAlgEquiv D q c (f D q i) = (c i : K)⁻¹ • f D q i := rescaleAlgHom_f c i
@[simp] theorem rescaleAlgEquiv_k (c : ι → Kˣ) (y : Y) :
    rescaleAlgEquiv D q c (k D q y) = k D q y := rescaleAlgHom_k c y
@[simp] theorem rescaleAlgEquiv_symm (c : ι → Kˣ) :
    (rescaleAlgEquiv D q c).symm = rescaleAlgEquiv D q c⁻¹ := (rfl)

end Rescale
end QuantizedEnvelopingAlgebra
end TauCeti
