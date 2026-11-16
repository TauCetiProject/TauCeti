/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Subalgebra.Operations
public import Mathlib.Algebra.FreeAlgebra
public import Mathlib.Algebra.RingQuot
public import TauCeti.LinearAlgebra.Matrix.Cartan.Datum.Hom
public import TauCeti.QuantumGroups.QuantumInteger.Factorial

/-!
# The Drinfeld–Jimbo quantized enveloping algebra of a Cartan datum

This file defines the quantized enveloping algebra `TauCeti.QuantizedEnvelopingAlgebra D q` of a
symmetrizable Cartan datum `D : TauCeti.CartanDatum ι X Y` over a field `K` at parameter `q : K`.
It is the quotient of the free `K`-algebra on Chevalley generators `Eᵢ`, `Fᵢ` (`i : ι`) and full
coweight-lattice toral generators `K_y` (`y : Y`) by Lusztig's presentation:

* `K_0 = 1` and `K_y K_z = K_(y + z)`;
* `K_y Eᵢ = q^⟨αᵢ, y⟩ Eᵢ K_y` and `K_y Fᵢ = q^(-⟨αᵢ, y⟩) Fᵢ K_y`;
* `Eᵢ Fⱼ - Fⱼ Eᵢ = δᵢⱼ (Kᵢ - Kᵢ⁻¹) / (qᵢ - qᵢ⁻¹)`, where `qᵢ = q^(dᵢ)` and `Kᵢ = K_(dᵢ hᵢ)`;
* for `i ≠ j`, the divided-power quantum Serre relations
  `∑_{r + s = 1 - aᵢⱼ} (-1)^r Eᵢ^(r) Eⱼ Eᵢ^(s) = 0` and its `F` analogue.

No `[DecidableEq ι]`, `[Fintype ι]`, or genericity hypothesis on `q` is imposed on the type itself.

## Main definitions and results

* `TauCeti.QuantizedEnvelopingAlgebra D q`: the Drinfeld–Jimbo algebra of `D` at parameter `q`.
* `e`, `f`, `k`, `ki`, `kiInv`, `eDividedPower`, `fDividedPower`, `kUnit`: generators and units.
* `GeneratorTuple`, `lift`, `liftEquiv`, `hom_ext`, `adjoin_range_generator`, `induction`: the
  universal property and generation principle.
* `commute_e_e_of_cartan_eq_zero`, `commute_f_f_of_cartan_eq_zero`,
  `k_mem_center_of_pairing_root_eq_zero`: disconnected-node commutativity and central coweights.
* `map`, `chevalleyInvolution`: functoriality along `CartanDatum.Hom` and the Chevalley involution.

## References

* G. Lusztig, *Introduction to Quantum Groups*, Progress in Mathematics 110, Birkhäuser, 1993, §3.1.
* J. C. Jantzen, *Lectures on Quantum Groups*, GSM 6, AMS, 1996, Chapter 4.
-/

public section

open Finset

namespace TauCeti

namespace QuantizedEnvelopingAlgebra

/-- The presentation generators on index type `ι` and coweight lattice `Y`: raising `Eᵢ`,
lowering `Fᵢ`, and toral `K_y`. -/
inductive Generator (ι Y : Type*)
  | e (i : ι)
  | f (i : ι)
  | k (y : Y)
  deriving DecidableEq

section SerreLength

variable {ι X Y : Type*} [AddCommGroup X] [AddCommGroup Y] (D : CartanDatum ι X Y)

/-- The degree `1 - aᵢⱼ` (as a natural number) of the quantum Serre relation between distinct
nodes `i` and `j`; on the diagonal `aᵢᵢ = 2` it evaluates to `0`. -/
def serreLength (i j : ι) : ℕ := (1 - D.cartan i j).toNat

lemma serreLength_def (i j : ι) : serreLength D i j = (1 - D.cartan i j).toNat := (rfl)

@[simp]
lemma serreLength_self (i : ι) : serreLength D i i = 0 := by simp [serreLength_def]

lemma serreLength_pos {i j : ι} (hij : i ≠ j) : 0 < serreLength D i j := by
  have := D.cartan_nonpos hij; rw [serreLength_def]; omega

lemma serreLength_ne_zero {i j : ι} (hij : i ≠ j) : serreLength D i j ≠ 0 :=
  (serreLength_pos D hij).ne'

lemma natCast_serreLength {i j : ι} (hij : i ≠ j) :
    (serreLength D i j : ℤ) = 1 - D.cartan i j := by
  have := D.cartan_nonpos hij; rw [serreLength_def]; omega

lemma cartan_eq_one_sub_serreLength {i j : ι} (hij : i ≠ j) :
    D.cartan i j = 1 - serreLength D i j := by
  rw [natCast_serreLength D hij]; ring

@[simp]
lemma serreLength_eq_one_iff {i j : ι} (hij : i ≠ j) :
    serreLength D i j = 1 ↔ D.cartan i j = 0 := by
  have := D.cartan_nonpos hij; rw [serreLength_def]; omega

end SerreLength

/-- The defining relations of `QuantizedEnvelopingAlgebra D q` on the free algebra. -/
inductive Rel {K ι X Y : Type*} [Field K] [AddCommGroup X] [AddCommGroup Y]
    (D : CartanDatum ι X Y) (q : K) :
    FreeAlgebra K (Generator ι Y) → FreeAlgebra K (Generator ι Y) → Prop
  | k_zero : Rel D q (FreeAlgebra.ι K (.k 0)) 1
  | k_mul_k (y z : Y) :
      Rel D q (FreeAlgebra.ι K (.k y) * FreeAlgebra.ι K (.k z)) (FreeAlgebra.ι K (.k (y + z)))
  | k_mul_e (y : Y) (i : ι) :
      Rel D q (FreeAlgebra.ι K (.k y) * FreeAlgebra.ι K (.e i))
        (q ^ D.pairing (D.root i) y • (FreeAlgebra.ι K (.e i) * FreeAlgebra.ι K (.k y)))
  | k_mul_f (y : Y) (i : ι) :
      Rel D q (FreeAlgebra.ι K (.k y) * FreeAlgebra.ι K (.f i))
        (q ^ (-D.pairing (D.root i) y) • (FreeAlgebra.ι K (.f i) * FreeAlgebra.ι K (.k y)))
  | e_mul_f_sub_f_mul_e_self (i : ι) :
      Rel D q
        (FreeAlgebra.ι K (.e i) * FreeAlgebra.ι K (.f i) -
          FreeAlgebra.ι K (.f i) * FreeAlgebra.ι K (.e i))
        ((q ^ D.symmetrizer i - (q ^ D.symmetrizer i)⁻¹)⁻¹ •
          (FreeAlgebra.ι K (.k (D.simpleTorus i)) - FreeAlgebra.ι K (.k (-D.simpleTorus i))))
  | e_mul_f_sub_f_mul_e_of_ne {i j : ι} (hij : i ≠ j) :
      Rel D q
        (FreeAlgebra.ι K (.e i) * FreeAlgebra.ι K (.f j) -
          FreeAlgebra.ι K (.f j) * FreeAlgebra.ι K (.e i)) 0
  | serre_e {i j : ι} (hij : i ≠ j) :
      Rel D q (∑ r ∈ range (serreLength D i j + 1), (-1 : K) ^ r •
        (quantumDividedPower (q ^ D.symmetrizer i) (FreeAlgebra.ι K (.e i)) r *
          FreeAlgebra.ι K (.e j) *
          quantumDividedPower (q ^ D.symmetrizer i) (FreeAlgebra.ι K (.e i))
            (serreLength D i j - r))) 0
  | serre_f {i j : ι} (hij : i ≠ j) :
      Rel D q (∑ r ∈ range (serreLength D i j + 1), (-1 : K) ^ r •
        (quantumDividedPower (q ^ D.symmetrizer i) (FreeAlgebra.ι K (.f i)) r *
          FreeAlgebra.ι K (.f j) *
          quantumDividedPower (q ^ D.symmetrizer i) (FreeAlgebra.ι K (.f i))
            (serreLength D i j - r))) 0

end QuantizedEnvelopingAlgebra

/-- The **Drinfeld–Jimbo quantized enveloping algebra** `U_q(D)` of a symmetrizable Cartan datum
`D : CartanDatum ι X Y` over a field `K` at parameter `q : K`. -/
def QuantizedEnvelopingAlgebra {K ι X Y : Type*} [Field K] [AddCommGroup X] [AddCommGroup Y]
    (D : CartanDatum ι X Y) (q : K) : Type _ :=
  RingQuot (QuantizedEnvelopingAlgebra.Rel D q)

namespace QuantizedEnvelopingAlgebra

section Algebra

variable {K ι X Y : Type*} [Field K] [AddCommGroup X] [AddCommGroup Y]
  (D : CartanDatum ι X Y) (q : K)

noncomputable instance : Inhabited (QuantizedEnvelopingAlgebra D q) :=
  inferInstanceAs (Inhabited (RingQuot (Rel D q)))

noncomputable instance : Ring (QuantizedEnvelopingAlgebra D q) :=
  inferInstanceAs (Ring (RingQuot (Rel D q)))

noncomputable instance : Algebra K (QuantizedEnvelopingAlgebra D q) :=
  inferInstanceAs (Algebra K (RingQuot (Rel D q)))

/-- The quotient `K`-algebra map from `FreeAlgebra K (Generator ι Y)`. -/
noncomputable def mkAlgHom :
    FreeAlgebra K (Generator ι Y) →ₐ[K] QuantizedEnvelopingAlgebra D q :=
  RingQuot.mkAlgHom K (Rel D q)

/-- The image of a presentation generator in `QuantizedEnvelopingAlgebra D q`. -/
noncomputable def generator (g : Generator ι Y) : QuantizedEnvelopingAlgebra D q :=
  mkAlgHom D q (FreeAlgebra.ι K g)

@[simp]
theorem mkAlgHom_ι (g : Generator ι Y) :
    mkAlgHom D q (FreeAlgebra.ι K g) = generator D q g := (rfl)

/-- The raising Chevalley generator `Eᵢ` at node `i : ι`. -/
noncomputable def e (i : ι) : QuantizedEnvelopingAlgebra D q := generator D q (.e i)

/-- The lowering Chevalley generator `Fᵢ` at node `i : ι`. -/
noncomputable def f (i : ι) : QuantizedEnvelopingAlgebra D q := generator D q (.f i)

/-- The toral generator `K_y` attached to a coweight `y : Y`. -/
noncomputable def k (y : Y) : QuantizedEnvelopingAlgebra D q := generator D q (.k y)

@[simp] theorem generator_e (i : ι) : generator D q (.e i) = e D q i := (rfl)
@[simp] theorem generator_f (i : ι) : generator D q (.f i) = f D q i := (rfl)
@[simp] theorem generator_k (y : Y) : generator D q (.k y) = k D q y := (rfl)

/-- The simple toral generator `Kᵢ = K_(dᵢ hᵢ)` at node `i : ι`. -/
noncomputable abbrev ki (i : ι) : QuantizedEnvelopingAlgebra D q := k D q (D.simpleTorus i)

/-- The inverse simple toral generator `Kᵢ⁻¹ = K_(-dᵢ hᵢ)` at node `i : ι`. -/
noncomputable abbrev kiInv (i : ι) : QuantizedEnvelopingAlgebra D q := k D q (-D.simpleTorus i)

/-- The divided power `Eᵢ^(n) = [n]_(qᵢ)!⁻¹ • Eᵢ^n` with `qᵢ = q^(dᵢ)`. -/
noncomputable abbrev eDividedPower (i : ι) (n : ℕ) : QuantizedEnvelopingAlgebra D q :=
  quantumDividedPower (q ^ D.symmetrizer i) (e D q i) n

/-- The divided power `Fᵢ^(n) = [n]_(qᵢ)!⁻¹ • Fᵢ^n` with `qᵢ = q^(dᵢ)`. -/
noncomputable abbrev fDividedPower (i : ι) (n : ℕ) : QuantizedEnvelopingAlgebra D q :=
  quantumDividedPower (q ^ D.symmetrizer i) (f D q i) n

/-! ### Defining relations -/

variable {D q}

private theorem mkAlgHom_rel {a b : FreeAlgebra K (Generator ι Y)} (h : Rel D q a b) :
    mkAlgHom D q a = mkAlgHom D q b :=
  RingQuot.mkAlgHom_rel K h

@[simp]
theorem k_zero : k D q 0 = 1 := by
  simpa only [map_one, mkAlgHom_ι, generator_k] using mkAlgHom_rel (Rel.k_zero (D := D) (q := q))

theorem k_mul_k (y z : Y) : k D q y * k D q z = k D q (y + z) := by
  simpa only [map_mul, mkAlgHom_ι, generator_k] using
    mkAlgHom_rel (Rel.k_mul_k (D := D) (q := q) y z)

theorem k_mul_e (y : Y) (i : ι) :
    k D q y * e D q i = q ^ D.pairing (D.root i) y • (e D q i * k D q y) := by
  simpa only [map_mul, map_smul, mkAlgHom_ι, generator_k, generator_e] using
    mkAlgHom_rel (Rel.k_mul_e (D := D) (q := q) y i)

theorem k_mul_f (y : Y) (i : ι) :
    k D q y * f D q i = q ^ (-D.pairing (D.root i) y) • (f D q i * k D q y) := by
  simpa only [map_mul, map_smul, mkAlgHom_ι, generator_k, generator_f] using
    mkAlgHom_rel (Rel.k_mul_f (D := D) (q := q) y i)

/-- The diagonal `E`–`F` commutator: `Eᵢ Fᵢ - Fᵢ Eᵢ = (Kᵢ - Kᵢ⁻¹) / (qᵢ - qᵢ⁻¹)`. -/
theorem e_mul_f_sub_f_mul_e_self (i : ι) :
    e D q i * f D q i - f D q i * e D q i =
      (q ^ D.symmetrizer i - (q ^ D.symmetrizer i)⁻¹)⁻¹ • (ki D q i - kiInv D q i) := by
  simpa only [map_sub, map_mul, map_smul, mkAlgHom_ι, generator_e, generator_f, generator_k] using
    mkAlgHom_rel (Rel.e_mul_f_sub_f_mul_e_self (D := D) (q := q) i)

/-- The off-diagonal `E`–`F` commutator `Eᵢ Fⱼ - Fⱼ Eᵢ = 0` for `i ≠ j`. -/
theorem e_mul_f_sub_f_mul_e_of_ne {i j : ι} (hij : i ≠ j) :
    e D q i * f D q j - f D q j * e D q i = 0 := by
  simpa only [map_sub, map_mul, map_zero, mkAlgHom_ι, generator_e, generator_f] using
    mkAlgHom_rel (Rel.e_mul_f_sub_f_mul_e_of_ne (D := D) (q := q) hij)

theorem e_mul_f_of_ne {i j : ι} (hij : i ≠ j) : e D q i * f D q j = f D q j * e D q i :=
  sub_eq_zero.mp (e_mul_f_sub_f_mul_e_of_ne hij)

theorem commute_e_f_of_ne {i j : ι} (hij : i ≠ j) : Commute (e D q i) (f D q j) :=
  e_mul_f_of_ne hij

/-- The combined Kronecker-delta `E`–`F` commutator relation. -/
theorem e_mul_f_sub_f_mul_e [DecidableEq ι] (i j : ι) :
    e D q i * f D q j - f D q j * e D q i =
      if i = j then
        (q ^ D.symmetrizer i - (q ^ D.symmetrizer i)⁻¹)⁻¹ • (ki D q i - kiInv D q i)
      else 0 := by
  split_ifs with hij
  · subst hij; exact e_mul_f_sub_f_mul_e_self i
  · exact e_mul_f_sub_f_mul_e_of_ne hij

/-- The divided-power quantum Serre relation for `E` (`i ≠ j`). -/
theorem serre_e {i j : ι} (hij : i ≠ j) :
    ∑ r ∈ range (serreLength D i j + 1), (-1 : K) ^ r •
      (eDividedPower D q i r * e D q j * eDividedPower D q i (serreLength D i j - r)) = 0 := by
  simpa only [map_sum, map_smul, map_mul, map_quantumDividedPower, map_zero, mkAlgHom_ι,
    generator_e] using mkAlgHom_rel (Rel.serre_e (D := D) (q := q) hij)

/-- The divided-power quantum Serre relation for `F` (`i ≠ j`). -/
theorem serre_f {i j : ι} (hij : i ≠ j) :
    ∑ r ∈ range (serreLength D i j + 1), (-1 : K) ^ r •
      (fDividedPower D q i r * f D q j * fDividedPower D q i (serreLength D i j - r)) = 0 := by
  simpa only [map_sum, map_smul, map_mul, map_quantumDividedPower, map_zero, mkAlgHom_ι,
    generator_f] using mkAlgHom_rel (Rel.serre_f (D := D) (q := q) hij)

/-! ### Toral units and commutation rules -/

@[simp] theorem k_mul_k_neg (y : Y) : k D q y * k D q (-y) = 1 := by
  rw [k_mul_k, add_neg_cancel, k_zero]

@[simp] theorem k_neg_mul_k (y : Y) : k D q (-y) * k D q y = 1 := by
  rw [k_mul_k, neg_add_cancel, k_zero]

/-- The toral generator `K_y` packaged as a unit with inverse `K_(-y)`. -/
noncomputable def kUnit (D : CartanDatum ι X Y) (q : K) (y : Y) :
    (QuantizedEnvelopingAlgebra D q)ˣ where
  val := k D q y
  inv := k D q (-y)
  val_inv := k_mul_k_neg y
  inv_val := k_neg_mul_k y

@[simp] theorem kUnit_val (y : Y) :
    (kUnit D q y : QuantizedEnvelopingAlgebra D q) = k D q y := (rfl)
@[simp] theorem kUnit_inv (y : Y) : ↑(kUnit D q y)⁻¹ = k D q (-y) := (rfl)
@[simp] theorem kUnit_zero : kUnit D q 0 = 1 := Units.ext k_zero
theorem kUnit_add (y z : Y) : kUnit D q (y + z) = kUnit D q y * kUnit D q z :=
  Units.ext (k_mul_k y z).symm
@[simp] theorem kUnit_neg (y : Y) : kUnit D q (-y) = (kUnit D q y)⁻¹ := Units.ext (rfl)

@[simp] theorem k_mul_k_neg_mul (y : Y) (x : QuantizedEnvelopingAlgebra D q) :
    k D q y * (k D q (-y) * x) = x := Units.mul_inv_cancel_left (kUnit D q y) x

@[simp] theorem k_neg_mul_k_mul (y : Y) (x : QuantizedEnvelopingAlgebra D q) :
    k D q (-y) * (k D q y * x) = x := Units.inv_mul_cancel_left (kUnit D q y) x

theorem commute_k_k (y z : Y) : Commute (k D q y) (k D q z) := by
  rw [Commute, SemiconjBy, k_mul_k, k_mul_k, add_comm]

theorem k_pow (y : Y) (n : ℕ) : k D q y ^ n = k D q (n • y) := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, ih, k_mul_k, succ_nsmul]

@[simp] theorem e_zero (i : ι) : e D (0 : K) i = 0 := by
  rw [← k_neg_mul_k_mul (D.coroot i) (e D (0 : K) i), k_mul_e, D.pairing_root_coroot_self]; simp

@[simp] theorem f_zero (i : ι) : f D (0 : K) i = 0 := by
  rw [← k_mul_k_neg_mul (D.coroot i) (f D (0 : K) i), k_mul_f, map_neg, neg_neg,
    D.pairing_root_coroot_self]; simp

theorem k_mul_e_mul_k_neg (y : Y) (i : ι) :
    k D q y * e D q i * k D q (-y) = q ^ D.pairing (D.root i) y • e D q i := by
  rw [k_mul_e, smul_mul_assoc, mul_assoc, k_mul_k_neg, mul_one]

theorem k_mul_f_mul_k_neg (y : Y) (i : ι) :
    k D q y * f D q i * k D q (-y) = q ^ (-D.pairing (D.root i) y) • f D q i := by
  rw [k_mul_f, smul_mul_assoc, mul_assoc, k_mul_k_neg, mul_one]

private lemma mul_k_of_k_neg_mul {u : QuantizedEnvelopingAlgebra D q} {y : Y} {c : K}
    (h : k D q (-y) * u = c • (u * k D q (-y))) : u * k D q y = c • (k D q y * u) := by
  calc u * k D q y = k D q y * (k D q (-y) * u) * k D q y := by rw [k_mul_k_neg_mul]
    _ = c • (k D q y * u) := by
      rw [h, mul_smul_comm, smul_mul_assoc]; simp only [mul_assoc, k_neg_mul_k, mul_one]

theorem e_mul_k (y : Y) (i : ι) :
    e D q i * k D q y = q ^ (-D.pairing (D.root i) y) • (k D q y * e D q i) :=
  mul_k_of_k_neg_mul (by simpa only [map_neg] using k_mul_e (D := D) (q := q) (-y) i)

theorem f_mul_k (y : Y) (i : ι) :
    f D q i * k D q y = q ^ D.pairing (D.root i) y • (k D q y * f D q i) :=
  mul_k_of_k_neg_mul (by simpa only [map_neg, neg_neg] using k_mul_f (D := D) (q := q) (-y) i)

theorem k_mul_e_pow (y : Y) (i : ι) (n : ℕ) :
    k D q y * e D q i ^ n = q ^ ((n : ℤ) * D.pairing (D.root i) y) • (e D q i ^ n * k D q y) := by
  have h : SemiconjBy (k D q y) (e D q i) (q ^ D.pairing (D.root i) y • e D q i) := by
    rw [SemiconjBy, smul_mul_assoc, k_mul_e]
  rw [(h.pow_right n).eq, smul_pow, smul_mul_assoc, ← zpow_natCast (q ^ _), ← zpow_mul, mul_comm]

theorem e_pow_mul_k (y : Y) (i : ι) (n : ℕ) :
    e D q i ^ n * k D q y = q ^ (-(n : ℤ) * D.pairing (D.root i) y) • (k D q y * e D q i ^ n) :=
  mul_k_of_k_neg_mul (by
    simpa only [map_neg, mul_neg, neg_mul] using k_mul_e_pow (D := D) (q := q) (-y) i n)

theorem k_mul_f_pow (y : Y) (i : ι) (n : ℕ) :
    k D q y * f D q i ^ n = q ^ (-(n : ℤ) * D.pairing (D.root i) y) • (f D q i ^ n * k D q y) := by
  have h : SemiconjBy (k D q y) (f D q i) (q ^ (-D.pairing (D.root i) y) • f D q i) := by
    rw [SemiconjBy, smul_mul_assoc, k_mul_f]
  rw [(h.pow_right n).eq, smul_pow, smul_mul_assoc, ← zpow_natCast (q ^ _), ← zpow_mul]; ring_nf

theorem f_pow_mul_k (y : Y) (i : ι) (n : ℕ) :
    f D q i ^ n * k D q y = q ^ ((n : ℤ) * D.pairing (D.root i) y) • (k D q y * f D q i ^ n) :=
  mul_k_of_k_neg_mul (by
    simpa only [map_neg, mul_neg, neg_mul, neg_neg] using k_mul_f_pow (D := D) (q := q) (-y) i n)

theorem k_mul_eDividedPower (y : Y) (i : ι) (n : ℕ) :
    k D q y * eDividedPower D q i n =
      q ^ ((n : ℤ) * D.pairing (D.root i) y) • (eDividedPower D q i n * k D q y) := by
  rw [eDividedPower, quantumDividedPower_def, mul_smul_comm, k_mul_e_pow, smul_comm, smul_mul_assoc]

theorem eDividedPower_mul_k (y : Y) (i : ι) (n : ℕ) :
    eDividedPower D q i n * k D q y =
      q ^ (-(n : ℤ) * D.pairing (D.root i) y) • (k D q y * eDividedPower D q i n) := by
  rw [eDividedPower, quantumDividedPower_def, smul_mul_assoc, e_pow_mul_k, smul_comm, mul_smul_comm]

theorem k_mul_fDividedPower (y : Y) (i : ι) (n : ℕ) :
    k D q y * fDividedPower D q i n =
      q ^ (-(n : ℤ) * D.pairing (D.root i) y) • (fDividedPower D q i n * k D q y) := by
  rw [fDividedPower, quantumDividedPower_def, mul_smul_comm, k_mul_f_pow, smul_comm, smul_mul_assoc]

theorem fDividedPower_mul_k (y : Y) (i : ι) (n : ℕ) :
    fDividedPower D q i n * k D q y =
      q ^ ((n : ℤ) * D.pairing (D.root i) y) • (k D q y * fDividedPower D q i n) := by
  rw [fDividedPower, quantumDividedPower_def, smul_mul_assoc, f_pow_mul_k, smul_comm, mul_smul_comm]

theorem ki_mul_e (i j : ι) :
    ki D q i * e D q j = (q ^ D.symmetrizer i) ^ D.cartan i j • (e D q j * ki D q i) := by
  rw [k_mul_e, D.pairing_root_simpleTorus, D.symmetrizer_mul_cartan j i, zpow_mul, zpow_natCast]

theorem e_mul_ki (i j : ι) :
    e D q j * ki D q i = (q ^ D.symmetrizer i) ^ (-D.cartan i j) • (ki D q i * e D q j) := by
  rw [e_mul_k, D.pairing_root_simpleTorus, D.symmetrizer_mul_cartan j i, ← mul_neg, zpow_mul,
    zpow_natCast]

theorem ki_mul_f (i j : ι) :
    ki D q i * f D q j = (q ^ D.symmetrizer i) ^ (-D.cartan i j) • (f D q j * ki D q i) := by
  rw [k_mul_f, D.pairing_root_simpleTorus, D.symmetrizer_mul_cartan j i, ← mul_neg, zpow_mul,
    zpow_natCast]

theorem f_mul_ki (i j : ι) :
    f D q j * ki D q i = (q ^ D.symmetrizer i) ^ D.cartan i j • (ki D q i * f D q j) := by
  rw [f_mul_k, D.pairing_root_simpleTorus, D.symmetrizer_mul_cartan j i, zpow_mul, zpow_natCast]

theorem kiInv_mul_e (i j : ι) :
    kiInv D q i * e D q j = (q ^ D.symmetrizer i) ^ (-D.cartan i j) • (e D q j * kiInv D q i) := by
  rw [k_mul_e, map_neg, D.pairing_root_simpleTorus, D.symmetrizer_mul_cartan j i, ← mul_neg,
    zpow_mul, zpow_natCast]

theorem e_mul_kiInv (i j : ι) :
    e D q j * kiInv D q i = (q ^ D.symmetrizer i) ^ D.cartan i j • (kiInv D q i * e D q j) := by
  rw [e_mul_k, map_neg, neg_neg, D.pairing_root_simpleTorus, D.symmetrizer_mul_cartan j i,
    zpow_mul, zpow_natCast]

theorem kiInv_mul_f (i j : ι) :
    kiInv D q i * f D q j = (q ^ D.symmetrizer i) ^ D.cartan i j • (f D q j * kiInv D q i) := by
  rw [k_mul_f, map_neg, neg_neg, D.pairing_root_simpleTorus, D.symmetrizer_mul_cartan j i,
    zpow_mul, zpow_natCast]

theorem f_mul_kiInv (i j : ι) :
    f D q j * kiInv D q i = (q ^ D.symmetrizer i) ^ (-D.cartan i j) • (kiInv D q i * f D q j) := by
  rw [f_mul_k, map_neg, D.pairing_root_simpleTorus, D.symmetrizer_mul_cartan j i, ← mul_neg,
    zpow_mul, zpow_natCast]

/-! ### Universal property and generation -/

/-- A family `(e, f, k)` in a `K`-algebra `A` satisfying the defining relations of
`QuantizedEnvelopingAlgebra D q`. -/
@[ext]
structure GeneratorTuple (D : CartanDatum ι X Y) (q : K) (A : Type*) [Ring A] [Algebra K A] where
  /-- Images of the raising generators `Eᵢ`. -/
  e : ι → A
  /-- Images of the lowering generators `Fᵢ`. -/
  f : ι → A
  /-- Images of the toral generators `K_y`. -/
  k : Y → A
  /-- `K_0 = 1`. -/
  k_zero : k 0 = 1
  /-- `K_y K_z = K_(y + z)`. -/
  k_mul_k (y z : Y) : k y * k z = k (y + z)
  /-- `K_y Eᵢ = q^⟨αᵢ, y⟩ Eᵢ K_y`. -/
  k_mul_e (y : Y) (i : ι) : k y * e i = q ^ D.pairing (D.root i) y • (e i * k y)
  /-- `K_y Fᵢ = q^(-⟨αᵢ, y⟩) Fᵢ K_y`. -/
  k_mul_f (y : Y) (i : ι) : k y * f i = q ^ (-D.pairing (D.root i) y) • (f i * k y)
  /-- The diagonal `E`–`F` commutator relation. -/
  e_mul_f_sub_f_mul_e_self (i : ι) :
    e i * f i - f i * e i =
      (q ^ D.symmetrizer i - (q ^ D.symmetrizer i)⁻¹)⁻¹ •
        (k (D.simpleTorus i) - k (-D.simpleTorus i))
  /-- The off-diagonal `E`–`F` commutator relation. -/
  e_mul_f_sub_f_mul_e_of_ne {i j : ι} (hij : i ≠ j) : e i * f j - f j * e i = 0
  /-- The divided-power quantum Serre relation for `E`. -/
  serre_e {i j : ι} (hij : i ≠ j) :
    ∑ r ∈ range (serreLength D i j + 1), (-1 : K) ^ r •
      (quantumDividedPower (q ^ D.symmetrizer i) (e i) r * e j *
        quantumDividedPower (q ^ D.symmetrizer i) (e i) (serreLength D i j - r)) = 0
  /-- The divided-power quantum Serre relation for `F`. -/
  serre_f {i j : ι} (hij : i ≠ j) :
    ∑ r ∈ range (serreLength D i j + 1), (-1 : K) ^ r •
      (quantumDividedPower (q ^ D.symmetrizer i) (f i) r * f j *
        quantumDividedPower (q ^ D.symmetrizer i) (f i) (serreLength D i j - r)) = 0

/-- The function on presentation generator names underlying a `GeneratorTuple`. -/
def GeneratorTuple.toFun {A : Type*} [Ring A] [Algebra K A] (t : GeneratorTuple D q A) :
    Generator ι Y → A
  | .e i => t.e i
  | .f i => t.f i
  | .k y => t.k y

@[simp] theorem GeneratorTuple.toFun_e {A : Type*} [Ring A] [Algebra K A]
    (t : GeneratorTuple D q A) (i : ι) : t.toFun (.e i) = t.e i := (rfl)
@[simp] theorem GeneratorTuple.toFun_f {A : Type*} [Ring A] [Algebra K A]
    (t : GeneratorTuple D q A) (i : ι) : t.toFun (.f i) = t.f i := (rfl)
@[simp] theorem GeneratorTuple.toFun_k {A : Type*} [Ring A] [Algebra K A]
    (t : GeneratorTuple D q A) (y : Y) : t.toFun (.k y) = t.k y := (rfl)

section Lift

variable {A : Type*} [Ring A] [Algebra K A]

/-- The universal property of `QuantizedEnvelopingAlgebra D q`: any `GeneratorTuple` extends
uniquely to a `K`-algebra homomorphism. -/
noncomputable def lift (t : GeneratorTuple D q A) : QuantizedEnvelopingAlgebra D q →ₐ[K] A :=
  RingQuot.liftAlgHom K ⟨FreeAlgebra.lift K t.toFun, by
    intro a b h
    cases h with
    | k_zero =>
      simpa only [map_one, FreeAlgebra.lift_ι_apply, GeneratorTuple.toFun_k] using t.k_zero
    | k_mul_k y z =>
      simpa only [map_mul, FreeAlgebra.lift_ι_apply, GeneratorTuple.toFun_k] using t.k_mul_k y z
    | k_mul_e y i =>
      simpa only [map_mul, map_smul, FreeAlgebra.lift_ι_apply, GeneratorTuple.toFun_k,
        GeneratorTuple.toFun_e] using t.k_mul_e y i
    | k_mul_f y i =>
      simpa only [map_mul, map_smul, FreeAlgebra.lift_ι_apply, GeneratorTuple.toFun_k,
        GeneratorTuple.toFun_f] using t.k_mul_f y i
    | e_mul_f_sub_f_mul_e_self i =>
      simpa only [map_sub, map_mul, map_smul, FreeAlgebra.lift_ι_apply, GeneratorTuple.toFun_e,
        GeneratorTuple.toFun_f, GeneratorTuple.toFun_k] using t.e_mul_f_sub_f_mul_e_self i
    | e_mul_f_sub_f_mul_e_of_ne hij =>
      simpa only [map_sub, map_mul, map_zero, FreeAlgebra.lift_ι_apply, GeneratorTuple.toFun_e,
        GeneratorTuple.toFun_f] using t.e_mul_f_sub_f_mul_e_of_ne hij
    | serre_e hij =>
      simpa only [map_sum, map_smul, map_mul, map_quantumDividedPower, map_zero,
        FreeAlgebra.lift_ι_apply, GeneratorTuple.toFun_e] using t.serre_e hij
    | serre_f hij =>
      simpa only [map_sum, map_smul, map_mul, map_quantumDividedPower, map_zero,
        FreeAlgebra.lift_ι_apply, GeneratorTuple.toFun_f] using t.serre_f hij⟩

theorem lift_generator (t : GeneratorTuple D q A) (g : Generator ι Y) :
    lift t (generator D q g) = t.toFun g :=
  (RingQuot.liftAlgHom_mkAlgHom_apply K _ _ _).trans (FreeAlgebra.lift_ι_apply _ _)

@[simp] theorem lift_e (t : GeneratorTuple D q A) (i : ι) : lift t (e D q i) = t.e i :=
  lift_generator t (.e i)
@[simp] theorem lift_f (t : GeneratorTuple D q A) (i : ι) : lift t (f D q i) = t.f i :=
  lift_generator t (.f i)
@[simp] theorem lift_k (t : GeneratorTuple D q A) (y : Y) : lift t (k D q y) = t.k y :=
  lift_generator t (.k y)

/-- Two `K`-algebra maps out of `QuantizedEnvelopingAlgebra D q` agreeing on `Eᵢ`, `Fᵢ`, `K_y` are
equal. -/
@[ext high]
theorem hom_ext {φ ψ : QuantizedEnvelopingAlgebra D q →ₐ[K] A}
    (he : ∀ i, φ (e D q i) = ψ (e D q i))
    (hf : ∀ i, φ (f D q i) = ψ (f D q i))
    (hk : ∀ y, φ (k D q y) = ψ (k D q y)) : φ = ψ := by
  apply RingQuot.ringQuot_ext' K φ ψ
  apply FreeAlgebra.hom_ext
  funext g; cases g with | e i => exact he i | f i => exact hf i | k y => exact hk y

/-- `K`-algebra homomorphisms out of `QuantizedEnvelopingAlgebra D q` correspond bijectively to
`GeneratorTuple D q A`. -/
noncomputable def liftEquiv : (QuantizedEnvelopingAlgebra D q →ₐ[K] A) ≃ GeneratorTuple D q A where
  toFun φ :=
    { e i := φ (e D q i)
      f i := φ (f D q i)
      k y := φ (k D q y)
      k_zero := by rw [← map_one φ, ← k_zero]
      k_mul_k y z := by rw [← map_mul, k_mul_k]
      k_mul_e y i := by simpa only [map_mul, map_smul] using congrArg φ (k_mul_e y i)
      k_mul_f y i := by simpa only [map_mul, map_smul] using congrArg φ (k_mul_f y i)
      e_mul_f_sub_f_mul_e_self i := by
        simpa only [map_sub, map_mul, map_smul] using congrArg φ (e_mul_f_sub_f_mul_e_self i)
      e_mul_f_sub_f_mul_e_of_ne hij := by
        simpa only [map_sub, map_mul, map_zero] using congrArg φ (e_mul_f_sub_f_mul_e_of_ne hij)
      serre_e hij := by
        simpa only [map_sum, map_smul, map_mul, map_quantumDividedPower, map_zero] using
          congrArg φ (serre_e hij)
      serre_f hij := by
        simpa only [map_sum, map_smul, map_mul, map_quantumDividedPower, map_zero] using
          congrArg φ (serre_f hij) }
  invFun := lift
  left_inv _ := hom_ext (by simp) (by simp) (by simp)
  right_inv _ := by ext <;> simp

@[simp] theorem liftEquiv_apply_e (φ : QuantizedEnvelopingAlgebra D q →ₐ[K] A) (i : ι) :
    (liftEquiv φ).e i = φ (e D q i) := (rfl)
@[simp] theorem liftEquiv_apply_f (φ : QuantizedEnvelopingAlgebra D q →ₐ[K] A) (i : ι) :
    (liftEquiv φ).f i = φ (f D q i) := (rfl)
@[simp] theorem liftEquiv_apply_k (φ : QuantizedEnvelopingAlgebra D q →ₐ[K] A) (y : Y) :
    (liftEquiv φ).k y = φ (k D q y) := (rfl)
@[simp] theorem liftEquiv_symm_apply (t : GeneratorTuple D q A) : liftEquiv.symm t = lift t := (rfl)

end Lift

/-- The presentation generators generate `QuantizedEnvelopingAlgebra D q` as a `K`-algebra. -/
theorem adjoin_range_generator (D : CartanDatum ι X Y) (q : K) :
    Algebra.adjoin K (Set.range (generator D q)) = ⊤ := by
  rw [Algebra.adjoin_range_eq_range_freeAlgebra_lift,
    show FreeAlgebra.lift K (generator D q) = mkAlgHom D q from
      FreeAlgebra.hom_ext (funext fun g ↦ by simp),
    AlgHom.range_eq_top]
  exact RingQuot.mkAlgHom_surjective K (Rel D q)

/-- Induction principle on `QuantizedEnvelopingAlgebra D q` from scalars and generators. -/
@[elab_as_elim]
theorem induction {C : QuantizedEnvelopingAlgebra D q → Prop}
    (algebraMap : ∀ c : K, C (algebraMap K (QuantizedEnvelopingAlgebra D q) c))
    (e : ∀ i, C (e D q i)) (f : ∀ i, C (f D q i)) (k : ∀ y, C (k D q y))
    (mul : ∀ a b, C a → C b → C (a * b)) (add : ∀ a b, C a → C b → C (a + b))
    (x : QuantizedEnvelopingAlgebra D q) : C x := by
  have hx : x ∈ Algebra.adjoin K (Set.range (generator D q)) := by
    rw [adjoin_range_generator]; exact Algebra.mem_top
  induction hx using Algebra.adjoin_induction with
  | mem _ ha =>
    rcases ha with ⟨g, rfl⟩
    cases g with | e i => exact e i | f i => exact f i | k y => exact k y
  | algebraMap c => exact algebraMap c
  | add a b _ _ ha hb => exact add a b ha hb
  | mul a b _ _ ha hb => exact mul a b ha hb

theorem commute_of_commute_generators {z : QuantizedEnvelopingAlgebra D q}
    (he : ∀ i, Commute (e D q i) z) (hf : ∀ i, Commute (f D q i) z)
    (hk : ∀ y, Commute (k D q y) z) (x : QuantizedEnvelopingAlgebra D q) : Commute x z := by
  refine (Algebra.commute_of_mem_adjoin_of_forall_mem_commute (R := K)
    (s := Set.range (generator D q))
    (by rw [adjoin_range_generator]; exact Algebra.mem_top) ?_).symm
  rintro _ ⟨g, rfl⟩
  cases g with | e i => exact (he i).symm | f i => exact (hf i).symm | k y => exact (hk y).symm

/-- Scaling `x` by `c₁` and `y` by `c₂` preserves a divided-power Serre vanishing identity. -/
theorem serre_smul {A : Type*} [Ring A] [Algebra K A] {qi c₁ c₂ : K} {m : ℕ} {x y : A}
    (h : ∑ r ∈ range (m + 1), (-1 : K) ^ r •
      (quantumDividedPower qi x r * y * quantumDividedPower qi x (m - r)) = 0) :
    ∑ r ∈ range (m + 1), (-1 : K) ^ r •
      (quantumDividedPower qi (c₁ • x) r * (c₂ • y) *
        quantumDividedPower qi (c₁ • x) (m - r)) = 0 := by
  have hterm : ∀ r ∈ range (m + 1),
      (-1 : K) ^ r • (quantumDividedPower qi (c₁ • x) r * (c₂ • y) *
        quantumDividedPower qi (c₁ • x) (m - r)) =
      (c₁ ^ m * c₂) • ((-1 : K) ^ r •
        (quantumDividedPower qi x r * y * quantumDividedPower qi x (m - r))) := fun r hr ↦ by
    rw [quantumDividedPower_smul, quantumDividedPower_smul, smul_mul_smul_comm, smul_mul_smul_comm,
      smul_comm ((-1 : K) ^ r)]
    congr 1
    rw [mul_right_comm, ← pow_add, Nat.add_sub_of_le (Nat.lt_succ_iff.mp (mem_range.mp hr))]
  rw [sum_congr rfl hterm, ← smul_sum, h, smul_zero]

/-! ### Disconnected nodes, central coweights, functoriality, and Chevalley involution -/

/-- At disconnected nodes (`aᵢⱼ = 0`, `i ≠ j`), `Eᵢ` and `Eⱼ` commute when `qᵢ - qᵢ⁻¹ ≠ 0`. -/
theorem commute_e_e_of_cartan_eq_zero {i j : ι} (hij : i ≠ j) (hcart : D.cartan i j = 0)
    (hq : q ^ D.symmetrizer i - (q ^ D.symmetrizer i)⁻¹ ≠ 0) :
    Commute (e D q i) (e D q j) := by
  have hserre := serre_e (D := D) (q := q) hij
  rw [(serreLength_eq_one_iff D hij).mpr hcart, sum_range_succ, sum_range_one] at hserre
  simp only [pow_zero, one_smul, pow_one, neg_one_smul, Nat.sub_zero, tsub_self,
    quantumDividedPower_zero, quantumDividedPower_one hq, one_mul, mul_one,
    ← sub_eq_add_neg, sub_eq_zero] at hserre
  exact hserre.symm

/-- A coweight `c` annihilated by every simple root gives a central toral element `K_c`. -/
theorem commute_k_of_pairing_root_eq_zero {c : Y} (hc : ∀ i, D.pairing (D.root i) c = 0)
    (x : QuantizedEnvelopingAlgebra D q) : Commute (k D q c) x := by
  refine (commute_of_commute_generators ?_ ?_ (fun y ↦ commute_k_k y c) x).symm
  · intro i; rw [Commute, SemiconjBy, e_mul_k, hc i, neg_zero, zpow_zero, one_smul]
  · intro i; rw [Commute, SemiconjBy, f_mul_k, hc i, zpow_zero, one_smul]

theorem k_mem_center_of_pairing_root_eq_zero {c : Y} (hc : ∀ i, D.pairing (D.root i) c = 0) :
    k D q c ∈ Subalgebra.center K (QuantizedEnvelopingAlgebra D q) :=
  Subalgebra.mem_center_iff.mpr fun x ↦ (commute_k_of_pairing_root_eq_zero hc x).eq.symm

section Map

variable {X' Y' X'' Y'' : Type*} [AddCommGroup X'] [AddCommGroup Y']
  [AddCommGroup X''] [AddCommGroup Y''] {D' : CartanDatum ι X' Y'} {D'' : CartanDatum ι X'' Y''}

/-- Functoriality along a morphism `φ : CartanDatum.Hom D D'`: `Eᵢ ↦ Eᵢ`, `Fᵢ ↦ Fᵢ`,
`K_y ↦ K_(φ y)`. -/
noncomputable def map (φ : CartanDatum.Hom D D') :
    QuantizedEnvelopingAlgebra D q →ₐ[K] QuantizedEnvelopingAlgebra D' q :=
  have hlen (i j : ι) : serreLength D i j = serreLength D' i j := by
    rw [serreLength_def, serreLength_def, φ.cartan_eq]
  lift
    { e i := e D' q i
      f i := f D' q i
      k y := k D' q (φ.toLinearMap y)
      k_zero := by simp
      k_mul_k y z := by rw [map_add, k_mul_k]
      k_mul_e y i := by rw [k_mul_e, φ.pairing_root_map]
      k_mul_f y i := by rw [k_mul_f, φ.pairing_root_map]
      e_mul_f_sub_f_mul_e_self i := by
        rw [e_mul_f_sub_f_mul_e_self, ki, kiInv, φ.symmetrizer_eq, ← φ.map_simpleTorus, ← map_neg]
      e_mul_f_sub_f_mul_e_of_ne hij := e_mul_f_sub_f_mul_e_of_ne hij
      serre_e hij := by
        simpa only [eDividedPower, hlen, φ.symmetrizer_eq] using serre_e (D := D') (q := q) hij
      serre_f hij := by
        simpa only [fDividedPower, hlen, φ.symmetrizer_eq] using serre_f (D := D') (q := q) hij }

@[simp] theorem map_e (φ : CartanDatum.Hom D D') (i : ι) : map φ (e D q i) = e D' q i := lift_e _ i
@[simp] theorem map_f (φ : CartanDatum.Hom D D') (i : ι) : map φ (f D q i) = f D' q i := lift_f _ i
@[simp] theorem map_k (φ : CartanDatum.Hom D D') (y : Y) :
    map φ (k D q y) = k D' q (φ.toLinearMap y) := lift_k _ y
theorem map_ki (φ : CartanDatum.Hom D D') (i : ι) : map φ (ki D q i) = ki D' q i := by simp [ki]
theorem map_kiInv (φ : CartanDatum.Hom D D') (i : ι) : map φ (kiInv D q i) = kiInv D' q i := by
  simp [kiInv]
@[simp] theorem map_id :
    map (CartanDatum.Hom.id D) = AlgHom.id K (QuantizedEnvelopingAlgebra D q) := by ext <;> simp
theorem map_comp (ψ : CartanDatum.Hom D' D'') (φ : CartanDatum.Hom D D') :
    map (q := q) (ψ.comp φ) = (map ψ).comp (map φ) := by ext <;> simp

end Map

private noncomputable def chevalleyInvolutionAlgHom (D : CartanDatum ι X Y) (q : K) :
    QuantizedEnvelopingAlgebra D q →ₐ[K] QuantizedEnvelopingAlgebra D q :=
  lift
    { e i := f D q i
      f i := e D q i
      k y := k D q (-y)
      k_zero := by rw [neg_zero, k_zero]
      k_mul_k y z := by rw [k_mul_k, neg_add]
      k_mul_e y i := by rw [k_mul_f, map_neg, neg_neg]
      k_mul_f y i := by rw [k_mul_e, map_neg]
      e_mul_f_sub_f_mul_e_self i := by
        rw [neg_neg, ← neg_sub (e D q i * f D q i), e_mul_f_sub_f_mul_e_self, ← smul_neg, neg_sub]
      e_mul_f_sub_f_mul_e_of_ne hij := by
        rw [← neg_sub, e_mul_f_sub_f_mul_e_of_ne hij.symm, neg_zero]
      serre_e hij := serre_f hij
      serre_f hij := serre_e hij }

private theorem chevalleyInvolutionAlgHom_comp_self (D : CartanDatum ι X Y) (q : K) :
    (chevalleyInvolutionAlgHom D q).comp (chevalleyInvolutionAlgHom D q) =
      AlgHom.id K (QuantizedEnvelopingAlgebra D q) := by
  ext <;> simp [chevalleyInvolutionAlgHom]

/-- The Chevalley involution `ω`, swapping `Eᵢ` and `Fᵢ` and sending `K_y ↦ K_(-y)`. -/
noncomputable def chevalleyInvolution (D : CartanDatum ι X Y) (q : K) :
    QuantizedEnvelopingAlgebra D q ≃ₐ[K] QuantizedEnvelopingAlgebra D q :=
  AlgEquiv.ofAlgHom (chevalleyInvolutionAlgHom D q) (chevalleyInvolutionAlgHom D q)
    (chevalleyInvolutionAlgHom_comp_self D q) (chevalleyInvolutionAlgHom_comp_self D q)

@[simp] theorem chevalleyInvolution_e (i : ι) : chevalleyInvolution D q (e D q i) = f D q i :=
  lift_e _ i
@[simp] theorem chevalleyInvolution_f (i : ι) : chevalleyInvolution D q (f D q i) = e D q i :=
  lift_f _ i
@[simp] theorem chevalleyInvolution_k (y : Y) : chevalleyInvolution D q (k D q y) = k D q (-y) :=
  lift_k _ y
theorem chevalleyInvolution_ki (i : ι) : chevalleyInvolution D q (ki D q i) = kiInv D q i :=
  chevalleyInvolution_k (D.simpleTorus i)
theorem chevalleyInvolution_kiInv (i : ι) : chevalleyInvolution D q (kiInv D q i) = ki D q i := by
  rw [kiInv, chevalleyInvolution_k, neg_neg, ki]
theorem chevalleyInvolution_eDividedPower (i : ι) (n : ℕ) :
    chevalleyInvolution D q (eDividedPower D q i n) = fDividedPower D q i n := by
  simp [eDividedPower, fDividedPower]
theorem chevalleyInvolution_fDividedPower (i : ι) (n : ℕ) :
    chevalleyInvolution D q (fDividedPower D q i n) = eDividedPower D q i n := by
  simp [eDividedPower, fDividedPower]
@[simp] theorem chevalleyInvolution_symm :
    (chevalleyInvolution D q).symm = chevalleyInvolution D q := (rfl)
@[simp] theorem chevalleyInvolution_chevalleyInvolution (x : QuantizedEnvelopingAlgebra D q) :
    chevalleyInvolution D q (chevalleyInvolution D q x) = x :=
  (chevalleyInvolution D q).symm_apply_apply x

/-- At disconnected nodes (`aᵢⱼ = 0`, `i ≠ j`), `Fᵢ` and `Fⱼ` commute when `qᵢ - qᵢ⁻¹ ≠ 0`. -/
theorem commute_f_f_of_cartan_eq_zero {i j : ι} (hij : i ≠ j) (hcart : D.cartan i j = 0)
    (hq : q ^ D.symmetrizer i - (q ^ D.symmetrizer i)⁻¹ ≠ 0) :
    Commute (f D q i) (f D q j) := by
  simpa only [chevalleyInvolution_e] using
    (commute_e_e_of_cartan_eq_zero hij hcart hq).map (chevalleyInvolution D q)

end Algebra

end QuantizedEnvelopingAlgebra

end TauCeti
