/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.FreeAlgebra
public import Mathlib.Algebra.RingQuot
public import TauCeti.LinearAlgebra.Matrix.Cartan.Datum.Hom
public import TauCeti.QuantumGroups.QuantumInteger.DividedPower

import Mathlib.Tactic.Ring

/-!
# Drinfeld–Jimbo quantized enveloping algebras on full Cartan data

For a symmetrizable Cartan datum `D : CartanDatum ι X Y` on full weight and coweight lattices and
`q` in a field `K`, we define `QuantumEnvelopingAlgebra D q` by generators `Eᵢ`, `Fᵢ` (`i : ι`) and
`K_y` (`y : Y`) modulo the Lusztig–Drinfeld–Jimbo relations, with universal property `lift` /
`liftEquiv`, Chevalley involution `chevalleyEquiv`, and functoriality `map` along `CartanDatum.Hom`.

## References

* G. Lusztig, *Introduction to Quantum Groups*, Progress in Mathematics 110, Birkhäuser, 1993, §3.1.
* S. Lentner, *Quantum groups and Nichols algebras acting on conformal field theories*, Adv. Math.
  278 (2015), Definition 3.2.
* `Mathlib.LinearAlgebra.CliffordAlgebra.Basic` (`RingQuot` over `FreeAlgebra` quotient pattern).
-/

public section

namespace TauCeti

namespace QuantumEnvelopingAlgebra

/-- Generating symbols of `QuantumEnvelopingAlgebra D q`: raising `e i`, lowering `f i`, and
toral `k y` for coweights `y : Y`. -/
inductive Generator (ι Y : Type*)
  | e (i : ι)
  | f (i : ι)
  | k (y : Y)

section SerreLength

variable {ι X Y : Type*} [AddCommGroup X] [AddCommGroup Y] (D : CartanDatum ι X Y)

/-- The length `1 - aᵢⱼ` of the quantum Serre relation at `(i, j)`. -/
def serreLength (i j : ι) : ℕ := (1 - D.cartan i j).toNat

@[simp] theorem serreLength_self (i : ι) : serreLength D i i = 0 := by simp [serreLength]
theorem serreLength_pos {i j : ι} (hij : i ≠ j) : 0 < serreLength D i j := by
  have := D.cartan_nonpos hij; rw [serreLength]; omega
theorem natCast_serreLength {i j : ι} (hij : i ≠ j) :
    (serreLength D i j : ℤ) = 1 - D.cartan i j := by
  have := D.cartan_nonpos hij; rw [serreLength]; omega
theorem cartan_eq_one_sub_serreLength {i j : ι} (hij : i ≠ j) :
    D.cartan i j = 1 - serreLength D i j := by rw [natCast_serreLength D hij]; ring
theorem serreLength_of_cartan_eq_zero {i j : ι} (h : D.cartan i j = 0) :
    serreLength D i j = 1 := by simp [serreLength, h]
end SerreLength

/-- Defining relations of `QuantumEnvelopingAlgebra D q` on `FreeAlgebra K (Generator ι Y)`. -/
inductive Rel {ι X Y K : Type*} [AddCommGroup X] [AddCommGroup Y] [Field K]
    (D : CartanDatum ι X Y) (q : K) :
    FreeAlgebra K (Generator ι Y) → FreeAlgebra K (Generator ι Y) → Prop
  | torus_zero : Rel D q (FreeAlgebra.ι K (.k 0)) 1
  | torus_add (y₁ y₂ : Y) :
      Rel D q (FreeAlgebra.ι K (.k y₁) * FreeAlgebra.ι K (.k y₂)) (FreeAlgebra.ι K (.k (y₁ + y₂)))
  | k_mul_e (y : Y) (i : ι) :
      Rel D q (FreeAlgebra.ι K (.k y) * FreeAlgebra.ι K (.e i))
        (q ^ D.pairing (D.root i) y • (FreeAlgebra.ι K (.e i) * FreeAlgebra.ι K (.k y)))
  | k_mul_f (y : Y) (i : ι) :
      Rel D q (FreeAlgebra.ι K (.k y) * FreeAlgebra.ι K (.f i))
        (q ^ (-D.pairing (D.root i) y) • (FreeAlgebra.ι K (.f i) * FreeAlgebra.ι K (.k y)))
  | e_mul_f_sub_f_mul_e_self (i : ι) :
      Rel D q (FreeAlgebra.ι K (.e i) * FreeAlgebra.ι K (.f i) -
          FreeAlgebra.ι K (.f i) * FreeAlgebra.ι K (.e i))
        ((q ^ D.symmetrizer i - (q ^ D.symmetrizer i)⁻¹)⁻¹ •
          (FreeAlgebra.ι K (.k (D.simpleTorus i)) - FreeAlgebra.ι K (.k (-D.simpleTorus i))))
  | e_mul_f_of_ne {i j : ι} (hij : i ≠ j) :
      Rel D q (FreeAlgebra.ι K (.e i) * FreeAlgebra.ι K (.f j))
        (FreeAlgebra.ι K (.f j) * FreeAlgebra.ι K (.e i))
  | serre_e {i j : ι} (hij : i ≠ j) :
      Rel D q (serreElement (q ^ D.symmetrizer i) (serreLength D i j)
        (FreeAlgebra.ι K (.e i)) (FreeAlgebra.ι K (.e j))) 0
  | serre_f {i j : ι} (hij : i ≠ j) :
      Rel D q (serreElement (q ^ D.symmetrizer i) (serreLength D i j)
        (FreeAlgebra.ι K (.f i)) (FreeAlgebra.ι K (.f j))) 0

end QuantumEnvelopingAlgebra

/-- The Drinfeld–Jimbo quantized enveloping algebra `U_q(D)` of a symmetrizable Cartan datum `D`
at parameter `q : K`. -/
@[expose]
def QuantumEnvelopingAlgebra {ι X Y K : Type*} [AddCommGroup X] [AddCommGroup Y] [Field K]
    (D : CartanDatum ι X Y) (q : K) : Type _ :=
  RingQuot (QuantumEnvelopingAlgebra.Rel D q)

namespace QuantumEnvelopingAlgebra

variable {ι X Y K : Type*} [AddCommGroup X] [AddCommGroup Y] [Field K]

noncomputable instance (D : CartanDatum ι X Y) (q : K) : Ring (QuantumEnvelopingAlgebra D q) :=
  inferInstanceAs (Ring (RingQuot (Rel D q)))
noncomputable instance (D : CartanDatum ι X Y) (q : K) : Algebra K (QuantumEnvelopingAlgebra D q) :=
  inferInstanceAs (Algebra K (RingQuot (Rel D q)))

section Generators

variable (D : CartanDatum ι X Y) (q : K)

/-- The canonical quotient algebra homomorphism from the free algebra. -/
noncomputable def mkAlgHom : FreeAlgebra K (Generator ι Y) →ₐ[K] QuantumEnvelopingAlgebra D q :=
  RingQuot.mkAlgHom K (Rel D q)
/-- The image of a presentation symbol in `QuantumEnvelopingAlgebra D q`. -/
noncomputable def generator (g : Generator ι Y) : QuantumEnvelopingAlgebra D q :=
  mkAlgHom D q (FreeAlgebra.ι K g)
@[simp] theorem mkAlgHom_ι (g : Generator ι Y) :
    mkAlgHom D q (FreeAlgebra.ι K g) = generator D q g := (rfl)
/-- The raising Chevalley generator `Eᵢ`. -/
noncomputable abbrev e (i : ι) : QuantumEnvelopingAlgebra D q := generator D q (.e i)
/-- The lowering Chevalley generator `Fᵢ`. -/
noncomputable abbrev f (i : ι) : QuantumEnvelopingAlgebra D q := generator D q (.f i)
/-- The toral generator `K_y` attached to a coweight `y ∈ Y`. -/
noncomputable abbrev k (y : Y) : QuantumEnvelopingAlgebra D q := generator D q (.k y)
/-- The simple toral generator `Kᵢ = K_{dᵢ hᵢ}`. -/
noncomputable abbrev simpleK (i : ι) : QuantumEnvelopingAlgebra D q := k D q (D.simpleTorus i)
/-- The inverse simple toral generator `Kᵢ⁻¹ = K_{-dᵢ hᵢ}`. -/
noncomputable abbrev simpleKInv (i : ι) : QuantumEnvelopingAlgebra D q := k D q (-D.simpleTorus i)

end Generators

section Relations

variable {D : CartanDatum ι X Y} {q : K}

private theorem mkAlgHom_rel {a b : FreeAlgebra K (Generator ι Y)} (h : Rel D q a b) :
    mkAlgHom D q a = mkAlgHom D q b := RingQuot.mkAlgHom_rel K h

@[simp] theorem k_zero : k D q 0 = 1 := by
  simpa only [map_one, mkAlgHom_ι] using mkAlgHom_rel .torus_zero
@[simp] theorem k_mul_k (y₁ y₂ : Y) : k D q y₁ * k D q y₂ = k D q (y₁ + y₂) := by
  simpa only [map_mul, mkAlgHom_ι] using mkAlgHom_rel (.torus_add y₁ y₂)
@[simp] theorem k_mul_k_mul (y₁ y₂ : Y) (x : QuantumEnvelopingAlgebra D q) :
    k D q y₁ * (k D q y₂ * x) = k D q (y₁ + y₂) * x := by rw [← mul_assoc, k_mul_k]

theorem commute_k (y₁ y₂ : Y) : Commute (k D q y₁) (k D q y₂) := by
  rw [Commute, SemiconjBy, k_mul_k, k_mul_k, add_comm]
theorem k_mul_e (y : Y) (i : ι) :
    k D q y * e D q i = q ^ D.pairing (D.root i) y • (e D q i * k D q y) := by
  simpa only [map_mul, map_smul, mkAlgHom_ι] using mkAlgHom_rel (.k_mul_e y i)
theorem k_mul_f (y : Y) (i : ι) :
    k D q y * f D q i = q ^ (-D.pairing (D.root i) y) • (f D q i * k D q y) := by
  simpa only [map_mul, map_smul, mkAlgHom_ι] using mkAlgHom_rel (.k_mul_f y i)
theorem e_mul_f_sub_f_mul_e_self (i : ι) :
    e D q i * f D q i - f D q i * e D q i =
      (q ^ D.symmetrizer i - (q ^ D.symmetrizer i)⁻¹)⁻¹ • (simpleK D q i - simpleKInv D q i) := by
  simpa only [map_sub, map_mul, map_smul, mkAlgHom_ι] using
    mkAlgHom_rel (.e_mul_f_sub_f_mul_e_self i)
theorem e_mul_f_of_ne {i j : ι} (hij : i ≠ j) : e D q i * f D q j = f D q j * e D q i := by
  simpa only [map_mul, mkAlgHom_ι] using mkAlgHom_rel (.e_mul_f_of_ne hij)
theorem serre_e {i j : ι} (hij : i ≠ j) :
    serreElement (q ^ D.symmetrizer i) (serreLength D i j) (e D q i) (e D q j) = 0 := by
  simpa only [map_serreElement, map_zero, mkAlgHom_ι] using mkAlgHom_rel (.serre_e hij)
theorem serre_f {i j : ι} (hij : i ≠ j) :
    serreElement (q ^ D.symmetrizer i) (serreLength D i j) (f D q i) (f D q j) = 0 := by
  simpa only [map_serreElement, map_zero, mkAlgHom_ι] using mkAlgHom_rel (.serre_f hij)

/-- The group homomorphism sending a coweight `y ∈ Y` to the unit `K_y` with inverse `K_(-y)`. -/
noncomputable def kUnit (D : CartanDatum ι X Y) (q : K) :
    Multiplicative Y →* (QuantumEnvelopingAlgebra D q)ˣ where
  toFun y := ⟨k D q y.toAdd, k D q (-y.toAdd), by simp, by simp⟩
  map_one' := Units.ext k_zero
  map_mul' y₁ y₂ := Units.ext (k_mul_k y₁.toAdd y₂.toAdd).symm

@[simp] theorem kUnit_ofAdd_val (y : Y) :
    ((kUnit D q (.ofAdd y) : (QuantumEnvelopingAlgebra D q)ˣ) : QuantumEnvelopingAlgebra D q) =
      k D q y := (rfl)
@[simp] theorem kUnit_ofAdd_inv (y : Y) : ↑(kUnit D q (.ofAdd y))⁻¹ = k D q (-y) := (rfl)
theorem isUnit_k (y : Y) : IsUnit (k D q y) := (kUnit D q (.ofAdd y)).isUnit
theorem k_pow (y : Y) (n : ℕ) : k D q y ^ n = k D q (n • y) := by
  induction n with | zero => simp | succ n ih => rw [pow_succ, ih, k_mul_k, succ_nsmul]
theorem kUnit_zpow_val (y : Y) (m : ℤ) :
    ((kUnit D q (.ofAdd y) ^ m : (QuantumEnvelopingAlgebra D q)ˣ) : QuantumEnvelopingAlgebra D q) =
      k D q (m • y) := by rw [← map_zpow, ← ofAdd_zsmul, kUnit_ofAdd_val]

@[simp] theorem e_zero (i : ι) : e D (0 : K) i = 0 := by
  have h := k_mul_e (D := D) (q := (0 : K)) (D.coroot i) i; rw [D.pairing_root_coroot_self] at h
  calc e D (0 : K) i = k D 0 (-D.coroot i) * (k D 0 (D.coroot i) * e D 0 i) := by simp
    _ = 0 := by simp [h]
@[simp] theorem f_zero (i : ι) : f D (0 : K) i = 0 := by
  have h := k_mul_f (D := D) (q := (0 : K)) (-D.coroot i) i
  rw [map_neg, D.pairing_root_coroot_self, neg_neg] at h
  calc f D (0 : K) i = k D 0 (D.coroot i) * (k D 0 (-D.coroot i) * f D 0 i) := by simp
    _ = 0 := by simp [h]

private theorem mul_k_neg_of_k_mul {y : Y} {x : QuantumEnvelopingAlgebra D q} {c : K}
    (h : k D q y * x = c • (x * k D q y)) : x * k D q (-y) = c • (k D q (-y) * x) := by
  calc x * k D q (-y) = k D q (-y) * (k D q y * x) * k D q (-y) := by simp
    _ = c • (k D q (-y) * x) := by rw [h]; simp [mul_assoc]

private theorem smul_comm_pow {u a : QuantumEnvelopingAlgebra D q} {c : K}
    (h : u * a = c • (a * u)) (r : ℕ) : u * a ^ r = c ^ r • (a ^ r * u) := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [pow_succ, ← mul_assoc, ih, smul_mul_assoc, mul_assoc, h, mul_smul_comm, smul_smul,
      ← pow_succ, ← mul_assoc]

theorem e_mul_k_neg (y : Y) (i : ι) :
    e D q i * k D q (-y) = q ^ D.pairing (D.root i) y • (k D q (-y) * e D q i) :=
  mul_k_neg_of_k_mul (k_mul_e y i)
theorem e_mul_k (y : Y) (i : ι) :
    e D q i * k D q y = q ^ (-D.pairing (D.root i) y) • (k D q y * e D q i) := by
  simpa using e_mul_k_neg (D := D) (q := q) (-y) i
theorem f_mul_k_neg (y : Y) (i : ι) :
    f D q i * k D q (-y) = q ^ (-D.pairing (D.root i) y) • (k D q (-y) * f D q i) :=
  mul_k_neg_of_k_mul (k_mul_f y i)
theorem f_mul_k (y : Y) (i : ι) :
    f D q i * k D q y = q ^ D.pairing (D.root i) y • (k D q y * f D q i) := by
  simpa using f_mul_k_neg (D := D) (q := q) (-y) i
theorem k_mul_e_pow (y : Y) (i : ι) (r : ℕ) :
    k D q y * e D q i ^ r = q ^ ((r : ℤ) * D.pairing (D.root i) y) • (e D q i ^ r * k D q y) := by
  rw [smul_comm_pow (k_mul_e y i) r, ← zpow_natCast (q ^ _), ← zpow_mul, mul_comm]
theorem k_mul_quantumDividedPower_e (y : Y) (i : ι) (r : ℕ) :
    k D q y * quantumDividedPower (q ^ D.symmetrizer i) (e D q i) r =
      q ^ ((r : ℤ) * D.pairing (D.root i) y) •
        (quantumDividedPower (q ^ D.symmetrizer i) (e D q i) r * k D q y) := by
  rw [quantumDividedPower_def, mul_smul_comm, k_mul_e_pow, smul_comm, smul_mul_assoc]
theorem quantumDividedPower_e_mul_k (y : Y) (i : ι) (r : ℕ) :
    quantumDividedPower (q ^ D.symmetrizer i) (e D q i) r * k D q y =
      q ^ (-((r : ℤ) * D.pairing (D.root i) y)) •
        (k D q y * quantumDividedPower (q ^ D.symmetrizer i) (e D q i) r) := by
  simpa [mul_neg] using mul_k_neg_of_k_mul (k_mul_quantumDividedPower_e (D := D) (q := q) (-y) i r)
theorem simpleK_mul_e (i j : ι) :
    simpleK D q i * e D q j =
      (q ^ D.symmetrizer i) ^ D.cartan i j • (e D q j * simpleK D q i) := by
  rw [k_mul_e, D.pairing_root_simpleTorus, ← D.symmetrizer_mul_cartan, zpow_mul, zpow_natCast]
theorem simpleK_mul_e_self (i : ι) :
    simpleK D q i * e D q i = (q ^ D.symmetrizer i) ^ 2 • (e D q i * simpleK D q i) := by
  simpa using simpleK_mul_e (D := D) (q := q) i i
theorem e_mul_simpleKInv (i j : ι) :
    e D q j * simpleKInv D q i =
      (q ^ D.symmetrizer i) ^ D.cartan i j • (simpleKInv D q i * e D q j) := by
  rw [e_mul_k_neg, D.pairing_root_simpleTorus, ← D.symmetrizer_mul_cartan, zpow_mul, zpow_natCast]
theorem e_mul_simpleKInv_self (i : ι) :
    e D q i * simpleKInv D q i = (q ^ D.symmetrizer i) ^ 2 • (simpleKInv D q i * e D q i) := by
  simpa using e_mul_simpleKInv (D := D) (q := q) i i
theorem simpleK_mul_f (i j : ι) :
    simpleK D q i * f D q j =
      (q ^ D.symmetrizer i) ^ (-D.cartan i j) • (f D q j * simpleK D q i) := by
  rw [k_mul_f, D.pairing_root_simpleTorus, ← D.symmetrizer_mul_cartan, ← mul_neg, zpow_mul,
    zpow_natCast]
theorem simpleK_mul_f_self (i : ι) :
    simpleK D q i * f D q i = (q ^ D.symmetrizer i)⁻¹ ^ 2 • (f D q i * simpleK D q i) := by
  simpa [inv_pow] using simpleK_mul_f (D := D) (q := q) i i
theorem f_mul_simpleKInv (i j : ι) :
    f D q j * simpleKInv D q i =
      (q ^ D.symmetrizer i) ^ (-D.cartan i j) • (simpleKInv D q i * f D q j) := by
  rw [f_mul_k_neg, D.pairing_root_simpleTorus, ← D.symmetrizer_mul_cartan, ← mul_neg, zpow_mul,
    zpow_natCast]
theorem commute_e_of_cartan_eq_zero {i j : ι} (h : D.cartan i j = 0)
    (hq : q ^ D.symmetrizer i - (q ^ D.symmetrizer i)⁻¹ ≠ 0) : Commute (e D q i) (e D q j) := by
  have hij : i ≠ j := by rintro rfl; simp at h
  have hserre := serre_e (D := D) (q := q) hij
  rwa [serreLength_of_cartan_eq_zero D h, serreElement_one hq, sub_eq_zero, eq_comm] at hserre
theorem commute_f_of_cartan_eq_zero {i j : ι} (h : D.cartan i j = 0)
    (hq : q ^ D.symmetrizer i - (q ^ D.symmetrizer i)⁻¹ ≠ 0) : Commute (f D q i) (f D q j) := by
  have hij : i ≠ j := by rintro rfl; simp at h
  have hserre := serre_f (D := D) (q := q) hij
  rwa [serreLength_of_cartan_eq_zero D h, serreElement_one hq, sub_eq_zero, eq_comm] at hserre
end Relations

/-- A family of elements in a `K`-algebra `A` satisfying the defining relations of
`QuantumEnvelopingAlgebra D q`. -/
structure GeneratorTuple (D : CartanDatum ι X Y) (q : K) (A : Type*) [Ring A] [Algebra K A] where
  /-- Proposed images of `Eᵢ`. -/
  e : ι → A
  /-- Proposed images of `Fᵢ`. -/
  f : ι → A
  /-- Proposed images of `K_y`. -/
  k : Y → A
  k_zero : k 0 = 1
  k_mul_k (y₁ y₂ : Y) : k y₁ * k y₂ = k (y₁ + y₂)
  k_mul_e (y : Y) (i : ι) : k y * e i = q ^ D.pairing (D.root i) y • (e i * k y)
  k_mul_f (y : Y) (i : ι) : k y * f i = q ^ (-D.pairing (D.root i) y) • (f i * k y)
  e_mul_f_sub_f_mul_e_self (i : ι) : e i * f i - f i * e i =
    (q ^ D.symmetrizer i - (q ^ D.symmetrizer i)⁻¹)⁻¹ •
      (k (D.simpleTorus i) - k (-D.simpleTorus i))
  e_mul_f_of_ne {i j : ι} (hij : i ≠ j) : e i * f j = f j * e i
  serre_e {i j : ι} (hij : i ≠ j) :
    serreElement (q ^ D.symmetrizer i) (serreLength D i j) (e i) (e j) = 0
  serre_f {i j : ι} (hij : i ≠ j) :
    serreElement (q ^ D.symmetrizer i) (serreLength D i j) (f i) (f j) = 0

namespace GeneratorTuple

variable {D : CartanDatum ι X Y} {q : K} {A : Type*} [Ring A] [Algebra K A]

/-- Evaluation of a `GeneratorTuple` on `Generator ι Y`. -/
@[expose, simp] def toFun (t : GeneratorTuple D q A) : Generator ι Y → A
  | .e i => t.e i
  | .f i => t.f i
  | .k y => t.k y

@[ext] theorem ext {t₁ t₂ : GeneratorTuple D q A} (he : t₁.e = t₂.e) (hf : t₁.f = t₂.f)
    (hk : t₁.k = t₂.k) : t₁ = t₂ := by cases t₁; cases t₂; congr

end GeneratorTuple

section UniversalProperty

variable {D : CartanDatum ι X Y} {q : K} {A : Type*} [Ring A] [Algebra K A]

/-- Universal property of `QuantumEnvelopingAlgebra D q`. -/
noncomputable def lift (t : GeneratorTuple D q A) : QuantumEnvelopingAlgebra D q →ₐ[K] A :=
  RingQuot.liftAlgHom K ⟨FreeAlgebra.lift K t.toFun, by
    rintro _ _ (_ | ⟨y₁, y₂⟩ | ⟨y, i⟩ | ⟨y, i⟩ | ⟨i⟩ | @⟨_, _, hij⟩ | @⟨_, _, hij⟩ | @⟨_, _, hij⟩)
    · simpa using t.k_zero
    · simpa using t.k_mul_k y₁ y₂
    · simpa using t.k_mul_e y i
    · simpa using t.k_mul_f y i
    · simpa using t.e_mul_f_sub_f_mul_e_self i
    · simpa using t.e_mul_f_of_ne hij
    · simpa using t.serre_e hij
    · simpa using t.serre_f hij⟩

@[simp] theorem lift_generator (t : GeneratorTuple D q A) (g : Generator ι Y) :
    lift t (generator D q g) = t.toFun g :=
  (RingQuot.liftAlgHom_mkAlgHom_apply K _ _ _).trans (FreeAlgebra.lift_ι_apply _ _)

@[ext high]
theorem hom_ext {F G : QuantumEnvelopingAlgebra D q →ₐ[K] A}
    (he : ∀ i, F (e D q i) = G (e D q i)) (hf : ∀ i, F (f D q i) = G (f D q i))
    (hk : ∀ y, F (k D q y) = G (k D q y)) : F = G := by
  apply RingQuot.ringQuot_ext' K F G; apply FreeAlgebra.hom_ext; funext g
  cases g with | e i => exact he i | f i => exact hf i | k y => exact hk y

/-- Equivalence between `K`-algebra homomorphisms out of `U` and `GeneratorTuple`s in `A`. -/
noncomputable def liftEquiv : (QuantumEnvelopingAlgebra D q →ₐ[K] A) ≃ GeneratorTuple D q A where
  toFun F :=
    { e i := F (e D q i), f i := F (f D q i), k y := F (k D q y)
      k_zero := by rw [k_zero, map_one]
      k_mul_k y₁ y₂ := by rw [← map_mul, k_mul_k]
      k_mul_e y i := by simpa only [map_mul, map_smul] using congrArg F (k_mul_e y i)
      k_mul_f y i := by simpa only [map_mul, map_smul] using congrArg F (k_mul_f y i)
      e_mul_f_sub_f_mul_e_self i := by
        simpa only [map_sub, map_mul, map_smul] using congrArg F (e_mul_f_sub_f_mul_e_self i)
      e_mul_f_of_ne hij := by simpa only [map_mul] using congrArg F (e_mul_f_of_ne hij)
      serre_e hij := by simpa only [map_serreElement, map_zero] using congrArg F (serre_e hij)
      serre_f hij := by simpa only [map_serreElement, map_zero] using congrArg F (serre_f hij) }
  invFun := lift
  left_inv _ := by ext <;> simp
  right_inv _ := by ext <;> simp

@[simp] theorem liftEquiv_apply_e (F : QuantumEnvelopingAlgebra D q →ₐ[K] A) (i : ι) :
    (liftEquiv F).e i = F (e D q i) := (rfl)
@[simp] theorem liftEquiv_apply_f (F : QuantumEnvelopingAlgebra D q →ₐ[K] A) (i : ι) :
    (liftEquiv F).f i = F (f D q i) := (rfl)
@[simp] theorem liftEquiv_apply_k (F : QuantumEnvelopingAlgebra D q →ₐ[K] A) (y : Y) :
    (liftEquiv F).k y = F (k D q y) := (rfl)
@[simp] theorem liftEquiv_symm_apply (t : GeneratorTuple D q A) : liftEquiv.symm t = lift t := (rfl)

theorem adjoin_range_generator (D : CartanDatum ι X Y) (q : K) :
    Algebra.adjoin K (Set.range (generator D q)) = ⊤ := by
  rw [Algebra.adjoin_range_eq_range_freeAlgebra_lift]
  have h : FreeAlgebra.lift K (generator D q) = mkAlgHom D q := by
    apply FreeAlgebra.hom_ext; funext g; simp
  rw [h, AlgHom.range_eq_top]; exact RingQuot.mkAlgHom_surjective K (Rel D q)

@[elab_as_elim]
theorem induction {C : QuantumEnvelopingAlgebra D q → Prop}
    (algebraMap : ∀ c, C (algebraMap K (QuantumEnvelopingAlgebra D q) c))
    (e : ∀ i, C (e D q i)) (f : ∀ i, C (f D q i)) (k : ∀ y, C (k D q y))
    (mul : ∀ a b, C a → C b → C (a * b)) (add : ∀ a b, C a → C b → C (a + b))
    (a : QuantumEnvelopingAlgebra D q) : C a := by
  have ha : a ∈ Algebra.adjoin K (Set.range (generator D q)) := by
    rw [adjoin_range_generator]; exact Algebra.mem_top
  induction ha using Algebra.adjoin_induction with
  | mem _ hx =>
    rcases hx with ⟨g, rfl⟩
    cases g with | e i => exact e i | f i => exact f i | k y => exact k y
  | algebraMap c => exact algebraMap c
  | add x y _ _ hx hy => exact add x y hx hy
  | mul x y _ _ hx hy => exact mul x y hx hy

theorem commute_of_commute_generators {z : QuantumEnvelopingAlgebra D q}
    (he : ∀ i, Commute (e D q i) z) (hf : ∀ i, Commute (f D q i) z)
    (hk : ∀ y, Commute (k D q y) z) (a : QuantumEnvelopingAlgebra D q) : Commute a z := by
  refine (Algebra.commute_of_mem_adjoin_of_forall_mem_commute (R := K)
    (s := Set.range (generator D q)) ?_ ?_).symm
  · rw [adjoin_range_generator]; exact Algebra.mem_top
  · rintro _ ⟨g, rfl⟩
    cases g with | e i => exact (he i).symm | f i => exact (hf i).symm | k y => exact (hk y).symm

theorem commute_k_of_forall_pairing_root_eq_zero {y : Y}
    (hy : ∀ i, D.pairing (D.root i) y = 0) (a : QuantumEnvelopingAlgebra D q) :
    Commute a (k D q y) :=
  commute_of_commute_generators
    (fun i ↦ by rw [Commute, SemiconjBy, e_mul_k, hy i, neg_zero, zpow_zero, one_smul])
    (fun i ↦ by rw [Commute, SemiconjBy, f_mul_k, hy i, zpow_zero, one_smul])
    (fun z ↦ commute_k z y) a

theorem k_mem_center_of_forall_pairing_root_eq_zero {y : Y}
    (hy : ∀ i, D.pairing (D.root i) y = 0) :
    k D q y ∈ Subalgebra.center K (QuantumEnvelopingAlgebra D q) :=
  Subalgebra.mem_center_iff.mpr (commute_k_of_forall_pairing_root_eq_zero hy)

end UniversalProperty

section Symmetries

variable (D : CartanDatum ι X Y) (q : K)

private noncomputable def chevalleyTuple : GeneratorTuple D q (QuantumEnvelopingAlgebra D q) where
  e i := f D q i
  f i := e D q i
  k y := k D q (-y)
  k_zero := by simp
  k_mul_k y₁ y₂ := by rw [k_mul_k, neg_add_rev, add_comm]
  k_mul_e y i := by simpa [map_neg] using k_mul_f (D := D) (q := q) (-y) i
  k_mul_f y i := by simpa [map_neg] using k_mul_e (D := D) (q := q) (-y) i
  e_mul_f_sub_f_mul_e_self i := by
    rw [← neg_sub (e D q i * f D q i), e_mul_f_sub_f_mul_e_self, ← smul_neg, neg_sub, neg_neg]
  e_mul_f_of_ne hij := (e_mul_f_of_ne hij.symm).symm
  serre_e hij := serre_f hij
  serre_f hij := serre_e hij

/-- The **Chevalley involution** `ω`, swapping `Eᵢ ↔ Fᵢ` and sending `K_y ↦ K_(-y)`. -/
noncomputable def chevalleyEquiv :
    QuantumEnvelopingAlgebra D q ≃ₐ[K] QuantumEnvelopingAlgebra D q :=
  AlgEquiv.ofAlgHom (lift (chevalleyTuple D q)) (lift (chevalleyTuple D q))
    (by ext <;> simp [chevalleyTuple]) (by ext <;> simp [chevalleyTuple])

@[simp] theorem chevalleyEquiv_e (i : ι) : chevalleyEquiv D q (e D q i) = f D q i := by
  simp [chevalleyEquiv, chevalleyTuple]
@[simp] theorem chevalleyEquiv_f (i : ι) : chevalleyEquiv D q (f D q i) = e D q i := by
  simp [chevalleyEquiv, chevalleyTuple]
@[simp] theorem chevalleyEquiv_k (y : Y) : chevalleyEquiv D q (k D q y) = k D q (-y) := by
  simp [chevalleyEquiv, chevalleyTuple]
@[simp] theorem chevalleyEquiv_symm : (chevalleyEquiv D q).symm = chevalleyEquiv D q := (rfl)
@[simp] theorem chevalleyEquiv_chevalleyEquiv (x : QuantumEnvelopingAlgebra D q) :
    chevalleyEquiv D q (chevalleyEquiv D q x) = x := (chevalleyEquiv D q).symm_apply_apply x
end Symmetries

section Functoriality
variable {X' Y' X'' Y'' : Type*} [AddCommGroup X'] [AddCommGroup Y']
  [AddCommGroup X''] [AddCommGroup Y'']
  {D : CartanDatum ι X Y} {D' : CartanDatum ι X' Y'} {D'' : CartanDatum ι X'' Y''}

theorem serreLength_eq_of_hom (φ : CartanDatum.Hom D D') (i j : ι) :
    serreLength D i j = serreLength D' i j := by simp [serreLength, φ.cartan_eq]

/-- Functorial `K`-algebra homomorphism induced by `φ : CartanDatum.Hom D D'`. -/
noncomputable def map (φ : CartanDatum.Hom D D') (q : K) :
    QuantumEnvelopingAlgebra D q →ₐ[K] QuantumEnvelopingAlgebra D' q :=
  lift
    { e i := e D' q i, f i := f D' q i, k y := k D' q (φ.toLinearMap y)
      k_zero := by simp
      k_mul_k y₁ y₂ := by rw [k_mul_k, map_add]
      k_mul_e y i := by rw [k_mul_e, φ.pairing_root_map]
      k_mul_f y i := by rw [k_mul_f, φ.pairing_root_map]
      e_mul_f_sub_f_mul_e_self i := by
        rw [e_mul_f_sub_f_mul_e_self, φ.symmetrizer_eq, map_neg, φ.map_simpleTorus]
      e_mul_f_of_ne hij := e_mul_f_of_ne hij
      serre_e hij := by rw [← φ.symmetrizer_eq, serreLength_eq_of_hom φ]; exact serre_e hij
      serre_f hij := by rw [← φ.symmetrizer_eq, serreLength_eq_of_hom φ]; exact serre_f hij }

@[simp] theorem map_e (φ : CartanDatum.Hom D D') (q : K) (i : ι) :
    map φ q (e D q i) = e D' q i := by simp [map]
@[simp] theorem map_f (φ : CartanDatum.Hom D D') (q : K) (i : ι) :
    map φ q (f D q i) = f D' q i := by simp [map]
@[simp] theorem map_k (φ : CartanDatum.Hom D D') (q : K) (y : Y) :
    map φ q (k D q y) = k D' q (φ.toLinearMap y) := by simp [map]
@[simp] theorem map_id (D : CartanDatum ι X Y) (q : K) :
    map (CartanDatum.Hom.id D) q = AlgHom.id K (QuantumEnvelopingAlgebra D q) := by ext <;> simp
theorem map_comp (ψ : CartanDatum.Hom D' D'') (φ : CartanDatum.Hom D D') (q : K) :
    map (ψ.comp φ) q = (map ψ q).comp (map φ q) := by ext <;> simp
end Functoriality
end QuantumEnvelopingAlgebra
end TauCeti
