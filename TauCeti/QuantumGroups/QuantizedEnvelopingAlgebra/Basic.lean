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
generators `Eᵢ` (`i : ι`), `Fᵢ` (`i : ι`), and `K_y` (`y : Y`) subject to:

* `K_0 = 1` and `K_(y + z) = K_y K_z`,
* `K_y Eᵢ = q^⟨αᵢ, y⟩ Eᵢ K_y` and `K_y Fᵢ = q^(-⟨αᵢ, y⟩) Fᵢ K_y`,
* `Eᵢ Fᵢ - Fᵢ Eᵢ = (qᵢ - qᵢ⁻¹)⁻¹ • (Kᵢ - Kᵢ⁻¹)` and `Eᵢ Fⱼ - Fⱼ Eᵢ = 0` for `i ≠ j`, where
  `qᵢ = q^(dᵢ)` and `Kᵢ = K_(dᵢ hᵢ)`, and
* the divided-power quantum Serre relations
  `∑_{r = 0}^{1 - aᵢⱼ} (-1)^r Eᵢ^(r) Eⱼ Eᵢ^(1 - aᵢⱼ - r) = 0` and
  `∑_{r = 0}^{1 - aᵢⱼ} (-1)^r Fᵢ^(r) Fⱼ Fᵢ^(1 - aᵢⱼ - r) = 0` for `i ≠ j`.

Because toral generators are indexed by the full coweight lattice `Y`, central and intermediate
isogeny directions of `Y` are retained in the algebra. No finiteness or decidability of `ι`, and no
freeness or finite rank of `X` and `Y`, is assumed in the presentation. At `q = 0` the relations
`K_(hᵢ) Eᵢ = 0² • Eᵢ K_(hᵢ)` and `K_(-hᵢ) Fᵢ = 0² • Fᵢ K_(-hᵢ)` force `Eᵢ = Fᵢ = 0`, so all
presentation-level commutation, functoriality, and rescaling identities hold without assuming
`q ≠ 0`.

## Main definitions

* `TauCeti.CartanDatum.serreLength`: the Serre exponent `(1 - aᵢⱼ).toNat`.
* `TauCeti.QuantizedEnvelopingAlgebra D q`: the Drinfeld–Jimbo quotient `K`-algebra.
* `TauCeti.QuantizedEnvelopingAlgebra.e`, `f`, `k`, `simpleK`, `simpleKInv`: the raising,
  lowering, and toral generators, together with `Kᵢ = K_(dᵢ hᵢ)` and `Kᵢ⁻¹ = K_(-dᵢ hᵢ)`.
* `TauCeti.QuantizedEnvelopingAlgebra.GeneratorTuple` and `lift`: the universal property of the
  presentation, packaged as an equivalence `liftEquiv`.
* `TauCeti.QuantizedEnvelopingAlgebra.map`: functoriality along `CartanDatum.Hom`.
* `TauCeti.QuantizedEnvelopingAlgebra.rescaleAlgEquiv`: the `K`-algebra automorphism rescaling
  `Eᵢ ↦ cᵢ Eᵢ`, `Fᵢ ↦ cᵢ⁻¹ Fᵢ`, and fixing every `K_y`.

## Main results

* `TauCeti.QuantizedEnvelopingAlgebra.hom_ext` and `induction`: extensionality of algebra maps and
  generation by the presentation generators.
* `TauCeti.QuantizedEnvelopingAlgebra.e_mul_e_of_cartan_eq_zero` and
  `f_mul_f_of_cartan_eq_zero`: generators at disconnected Dynkin nodes commute when
  `(q^(dᵢ))² ≠ 1`.
* `TauCeti.QuantizedEnvelopingAlgebra.k_mem_center_of_pairing_root_eq_zero`: toral elements `K_c`
  for coweights `c` annihilated by all simple roots are central.

## References

* G. Lusztig, *Introduction to Quantum Groups*, Progress in Mathematics 110, Birkhäuser, 1993,
  §3.1.
* J. C. Jantzen, *Lectures on Quantum Groups*, Graduate Studies in Mathematics 6, American
  Mathematical Society, 1996, Chapter 4.
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
def serreLength (i j : ι) : ℕ :=
  (1 - D.cartan i j).toNat

/-- The defining formula for `CartanDatum.serreLength`. -/
lemma serreLength_def (i j : ι) : D.serreLength i j = (1 - D.cartan i j).toNat :=
  (rfl)

/-- On the diagonal `aᵢᵢ = 2`, the truncated Serre length is `0`. -/
@[simp]
lemma serreLength_self (i : ι) : D.serreLength i i = 0 := by
  simp [serreLength_def]

/-- For distinct nodes `i ≠ j`, `aᵢⱼ ≤ 0`, so `(serreLength i j : ℤ) = 1 - aᵢⱼ`. -/
lemma serreLength_cast_of_ne {i j : ι} (hij : i ≠ j) :
    (D.serreLength i j : ℤ) = 1 - D.cartan i j := by
  have h := D.cartan_nonpos hij
  rw [serreLength_def, Int.toNat_of_nonneg (by omega)]

/-- For distinct nodes `i ≠ j`, `serreLength i j` is strictly positive. -/
lemma serreLength_pos_of_ne {i j : ι} (hij : i ≠ j) : 0 < D.serreLength i j := by
  have h := D.cartan_nonpos hij
  have hc := D.serreLength_cast_of_ne hij
  omega

/-- For distinct nodes `i ≠ j`, `serreLength i j` is nonzero. -/
lemma serreLength_ne_zero_of_ne {i j : ι} (hij : i ≠ j) : D.serreLength i j ≠ 0 :=
  (D.serreLength_pos_of_ne hij).ne'

/-- Orthogonal nodes (`aᵢⱼ = 0`) have Serre length `1`. -/
lemma serreLength_of_cartan_eq_zero {i j : ι} (h : D.cartan i j = 0) : D.serreLength i j = 1 := by
  simp [serreLength_def, h]

/-- Morphisms of Cartan data preserve Serre lengths. -/
lemma Hom.serreLength_eq {X' Y' : Type*} [AddCommGroup X'] [AddCommGroup Y']
    {D : CartanDatum ι X Y} {D' : CartanDatum ι X' Y'} (φ : D.Hom D') (i j : ι) :
    D'.serreLength i j = D.serreLength i j := by
  simp [serreLength_def, φ.cartan_eq]

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
      Rel D q (FreeAlgebra.ι K (.k (y + z)))
        (FreeAlgebra.ι K (.k y) * FreeAlgebra.ι K (.k z))
  | k_mul_e (i : ι) (y : Y) :
      Rel D q (FreeAlgebra.ι K (.k y) * FreeAlgebra.ι K (.e i))
        (q ^ D.pairing (D.root i) y • (FreeAlgebra.ι K (.e i) * FreeAlgebra.ι K (.k y)))
  | k_mul_f (i : ι) (y : Y) :
      Rel D q (FreeAlgebra.ι K (.k y) * FreeAlgebra.ι K (.f i))
        (q ^ (-D.pairing (D.root i) y) • (FreeAlgebra.ι K (.f i) * FreeAlgebra.ι K (.k y)))
  | commutator_self (i : ι) :
      Rel D q
        (FreeAlgebra.ι K (.e i) * FreeAlgebra.ι K (.f i) -
          FreeAlgebra.ι K (.f i) * FreeAlgebra.ι K (.e i))
        ((q ^ D.symmetrizer i - (q ^ D.symmetrizer i)⁻¹)⁻¹ •
          (FreeAlgebra.ι K (.k (D.simpleTorus i)) - FreeAlgebra.ι K (.k (-D.simpleTorus i))))
  | commutator_ne {i j : ι} (hij : i ≠ j) :
      Rel D q
        (FreeAlgebra.ι K (.e i) * FreeAlgebra.ι K (.f j) -
          FreeAlgebra.ι K (.f j) * FreeAlgebra.ι K (.e i)) 0
  | serre_e {i j : ι} (hij : i ≠ j) :
      Rel D q
        (quantumSerre (q ^ D.symmetrizer i) (D.serreLength i j)
          (FreeAlgebra.ι K (.e i)) (FreeAlgebra.ι K (.e j))) 0
  | serre_f {i j : ι} (hij : i ≠ j) :
      Rel D q
        (quantumSerre (q ^ D.symmetrizer i) (D.serreLength i j)
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

instance (D : CartanDatum ι X Y) (q : K) : Inhabited (QuantizedEnvelopingAlgebra D q) :=
  ⟨0⟩

/-- The canonical quotient algebra homomorphism from the free algebra onto
`QuantizedEnvelopingAlgebra D q`. -/
def mkAlgHom (D : CartanDatum ι X Y) (q : K) :
    FreeAlgebra K (Generator ι Y) →ₐ[K] QuantizedEnvelopingAlgebra D q :=
  RingQuot.mkAlgHom K (Rel D q)

/-- The quotient map onto `QuantizedEnvelopingAlgebra D q` is surjective. -/
theorem mkAlgHom_surjective (D : CartanDatum ι X Y) (q : K) :
    Function.Surjective (mkAlgHom D q) :=
  RingQuot.mkAlgHom_surjective K (Rel D q)

/-- `mkAlgHom D q` identifies pairs related by `Rel D q`. -/
theorem mkAlgHom_rel {D : CartanDatum ι X Y} {q : K}
    {a b : FreeAlgebra K (Generator ι Y)} (h : Rel D q a b) :
    mkAlgHom D q a = mkAlgHom D q b :=
  RingQuot.mkAlgHom_rel K h

/-- The image of a formal generator in `QuantizedEnvelopingAlgebra D q`. -/
def generator (D : CartanDatum ι X Y) (q : K) (g : Generator ι Y) :
    QuantizedEnvelopingAlgebra D q :=
  mkAlgHom D q (FreeAlgebra.ι K g)

/-- `mkAlgHom` sends each free generator to the corresponding algebra generator. -/
@[simp]
theorem mkAlgHom_ι (D : CartanDatum ι X Y) (q : K) (g : Generator ι Y) :
    mkAlgHom D q (FreeAlgebra.ι K g) = generator D q g :=
  (rfl)

/-- The raising Chevalley generator `Eᵢ`. -/
def e (D : CartanDatum ι X Y) (q : K) (i : ι) : QuantizedEnvelopingAlgebra D q :=
  generator D q (.e i)

/-- The lowering Chevalley generator `Fᵢ`. -/
def f (D : CartanDatum ι X Y) (q : K) (i : ι) : QuantizedEnvelopingAlgebra D q :=
  generator D q (.f i)

/-- The toral generator `K_y` attached to a coweight `y ∈ Y`. -/
def k (D : CartanDatum ι X Y) (q : K) (y : Y) : QuantizedEnvelopingAlgebra D q :=
  generator D q (.k y)

/-- `generator` at `.e i` is `e D q i`. -/
@[simp]
theorem generator_e (D : CartanDatum ι X Y) (q : K) (i : ι) :
    generator D q (.e i) = e D q i :=
  (rfl)

/-- `generator` at `.f i` is `f D q i`. -/
@[simp]
theorem generator_f (D : CartanDatum ι X Y) (q : K) (i : ι) :
    generator D q (.f i) = f D q i :=
  (rfl)

/-- `generator` at `.k y` is `k D q y`. -/
@[simp]
theorem generator_k (D : CartanDatum ι X Y) (q : K) (y : Y) :
    generator D q (.k y) = k D q y :=
  (rfl)

/-- The simple toral generator `Kᵢ = K_(dᵢ hᵢ)`. -/
def simpleK (D : CartanDatum ι X Y) (q : K) (i : ι) : QuantizedEnvelopingAlgebra D q :=
  k D q (D.simpleTorus i)

/-- The defining formula `Kᵢ = K_(dᵢ hᵢ)`. -/
theorem simpleK_def (D : CartanDatum ι X Y) (q : K) (i : ι) :
    simpleK D q i = k D q (D.simpleTorus i) :=
  (rfl)

/-- The inverse simple toral generator `Kᵢ⁻¹ = K_(-dᵢ hᵢ)`. -/
def simpleKInv (D : CartanDatum ι X Y) (q : K) (i : ι) : QuantizedEnvelopingAlgebra D q :=
  k D q (-D.simpleTorus i)

/-- The defining formula `Kᵢ⁻¹ = K_(-dᵢ hᵢ)`. -/
theorem simpleKInv_def (D : CartanDatum ι X Y) (q : K) (i : ι) :
    simpleKInv D q i = k D q (-D.simpleTorus i) :=
  (rfl)

section

variable {D : CartanDatum ι X Y} {q : K}

/-! ### Toral relations and units -/

/-- `K_0 = 1`. -/
@[simp]
theorem k_zero : k D q 0 = 1 := by
  simpa only [map_one, mkAlgHom_ι, generator_k] using mkAlgHom_rel (Rel.k_zero (D := D) (q := q))

/-- `K_(y + z) = K_y * K_z`. -/
theorem k_add (y z : Y) : k D q (y + z) = k D q y * k D q z := by
  simpa only [map_mul, mkAlgHom_ι, generator_k] using mkAlgHom_rel (Rel.k_add (D := D) (q := q) y z)

/-- `K_y * K_(-y) = 1`. -/
@[simp]
theorem k_mul_k_neg (y : Y) : k D q y * k D q (-y) = 1 := by
  rw [← k_add, add_neg_cancel, k_zero]

/-- `K_(-y) * K_y = 1`. -/
@[simp]
theorem k_neg_mul_k (y : Y) : k D q (-y) * k D q y = 1 := by
  rw [← k_add, neg_add_cancel, k_zero]

end

/-- The toral generator `K_y` packaged as a unit with inverse `K_(-y)`. -/
def kUnit (D : CartanDatum ι X Y) (q : K) (y : Y) : (QuantizedEnvelopingAlgebra D q)ˣ where
  val := k D q y
  inv := k D q (-y)
  val_inv := k_mul_k_neg y
  inv_val := k_neg_mul_k y

variable {D : CartanDatum ι X Y} {q : K}

/-- The underlying element of `kUnit D q y` is `k D q y`. -/
@[simp]
theorem kUnit_val (y : Y) : (kUnit D q y : QuantizedEnvelopingAlgebra D q) = k D q y :=
  (rfl)

/-- The inverse of `kUnit D q y` has underlying element `k D q (-y)`. -/
@[simp]
theorem kUnit_inv (y : Y) : ↑(kUnit D q y)⁻¹ = k D q (-y) :=
  (rfl)

/-- Left multiplication by `K_y` cancels `K_(-y)`. -/
@[simp]
theorem k_mul_k_neg_mul (y : Y) (x : QuantizedEnvelopingAlgebra D q) :
    k D q y * (k D q (-y) * x) = x :=
  Units.mul_inv_cancel_left (kUnit D q y) x

/-- Left multiplication by `K_(-y)` cancels `K_y`. -/
@[simp]
theorem k_neg_mul_k_mul (y : Y) (x : QuantizedEnvelopingAlgebra D q) :
    k D q (-y) * (k D q y * x) = x :=
  Units.inv_mul_cancel_left (kUnit D q y) x

/-- `K_(n • y) = K_y ^ n` for natural multiples `n : ℕ`. -/
theorem k_nsmul (n : ℕ) (y : Y) : k D q (n • y) = k D q y ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [succ_nsmul, k_add, ih, pow_succ]

/-- `K_(m • y)` is the integer power `(kUnit D q y)^m` for `m : ℤ`. -/
theorem k_zsmul (m : ℤ) (y : Y) :
    k D q (m • y) = ((kUnit D q y ^ m : (QuantizedEnvelopingAlgebra D q)ˣ) :
      QuantizedEnvelopingAlgebra D q) := by
  cases m with
  | ofNat n =>
    rw [Int.ofNat_eq_natCast, natCast_zsmul, k_nsmul, zpow_natCast, Units.val_pow_eq_pow_val,
      kUnit_val]
  | negSucc n =>
    rw [negSucc_zsmul, zpow_negSucc, ← inv_pow, Units.val_pow_eq_pow_val, kUnit_inv, ← k_nsmul,
      ← smul_neg]

/-- `Kᵢ * Kᵢ⁻¹ = 1`. -/
@[simp]
theorem simpleK_mul_simpleKInv (i : ι) : simpleK D q i * simpleKInv D q i = 1 :=
  k_mul_k_neg (D.simpleTorus i)

/-- `Kᵢ⁻¹ * Kᵢ = 1`. -/
@[simp]
theorem simpleKInv_mul_simpleK (i : ι) : simpleKInv D q i * simpleK D q i = 1 :=
  k_neg_mul_k (D.simpleTorus i)

/-- Left multiplication by `Kᵢ` cancels `Kᵢ⁻¹`. -/
@[simp]
theorem simpleK_mul_simpleKInv_mul (i : ι) (x : QuantizedEnvelopingAlgebra D q) :
    simpleK D q i * (simpleKInv D q i * x) = x :=
  k_mul_k_neg_mul (D.simpleTorus i) x

/-- Left multiplication by `Kᵢ⁻¹` cancels `Kᵢ`. -/
@[simp]
theorem simpleKInv_mul_simpleK_mul (i : ι) (x : QuantizedEnvelopingAlgebra D q) :
    simpleKInv D q i * (simpleK D q i * x) = x :=
  k_neg_mul_k_mul (D.simpleTorus i) x

/-- `Kᵢ ^ n = K_(n • dᵢ hᵢ)`. -/
theorem simpleK_pow (i : ι) (n : ℕ) :
    simpleK D q i ^ n = k D q (n • D.simpleTorus i) :=
  (k_nsmul n (D.simpleTorus i)).symm

/-- `Kᵢ⁻¹ ^ n = K_(-(n • dᵢ hᵢ))`. -/
theorem simpleKInv_pow (i : ι) (n : ℕ) :
    simpleKInv D q i ^ n = k D q (-(n • D.simpleTorus i)) := by
  rw [simpleKInv_def, ← k_nsmul, smul_neg]

/-! ### Weight, commutator, and Serre relations -/

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

/-- Conjugating `Eᵢ` by `K_y` multiplies by `q^⟨αᵢ, y⟩`. -/
theorem k_mul_e_mul_k_neg (i : ι) (y : Y) :
    k D q y * e D q i * k D q (-y) = q ^ D.pairing (D.root i) y • e D q i := by
  rw [k_mul_e, smul_mul_assoc, mul_assoc, k_mul_k_neg, mul_one]

/-- Conjugating `Fᵢ` by `K_y` multiplies by `q^(-⟨αᵢ, y⟩)`. -/
theorem k_mul_f_mul_k_neg (i : ι) (y : Y) :
    k D q y * f D q i * k D q (-y) = q ^ (-D.pairing (D.root i) y) • f D q i := by
  rw [k_mul_f, smul_mul_assoc, mul_assoc, k_mul_k_neg, mul_one]

/-- Moving `K_y` to the left across `Eᵢ` multiplies by `q^(-⟨αᵢ, y⟩)`. -/
theorem e_mul_k (i : ι) (y : Y) :
    e D q i * k D q y = q ^ (-D.pairing (D.root i) y) • (k D q y * e D q i) := by
  calc
    e D q i * k D q y = k D q y * (k D q (-y) * e D q i) * k D q y := by
      rw [k_mul_k_neg_mul]
    _ = q ^ (-D.pairing (D.root i) y) • (k D q y * e D q i) := by
      rw [k_mul_e i (-y), map_neg, mul_smul_comm, smul_mul_assoc]
      simp only [mul_assoc, k_neg_mul_k, mul_one]

/-- Moving `K_y` to the left across `Fᵢ` multiplies by `q^⟨αᵢ, y⟩`. -/
theorem f_mul_k (i : ι) (y : Y) :
    f D q i * k D q y = q ^ D.pairing (D.root i) y • (k D q y * f D q i) := by
  calc
    f D q i * k D q y = k D q y * (k D q (-y) * f D q i) * k D q y := by
      rw [k_mul_k_neg_mul]
    _ = q ^ D.pairing (D.root i) y • (k D q y * f D q i) := by
      rw [k_mul_f i (-y), map_neg, neg_neg, mul_smul_comm, smul_mul_assoc]
      simp only [mul_assoc, k_neg_mul_k, mul_one]

/-- At `q = 0`, the raising generator `Eᵢ` vanishes. -/
@[simp]
theorem e_zero (i : ι) : e D (0 : K) i = 0 := by
  rw [← k_neg_mul_k_mul (D.coroot i) (e D (0 : K) i), k_mul_e, D.pairing_root_coroot_self]
  simp

/-- At `q = 0`, the lowering generator `Fᵢ` vanishes. -/
@[simp]
theorem f_zero (i : ι) : f D (0 : K) i = 0 := by
  rw [← k_mul_k_neg_mul (D.coroot i) (f D (0 : K) i), k_mul_f, map_neg, neg_neg,
    D.pairing_root_coroot_self]
  simp

/-- `Kᵢ * Eⱼ = qᵢ^(aᵢⱼ) • (Eⱼ * Kᵢ)`. -/
theorem simpleK_mul_e (i j : ι) :
    simpleK D q i * e D q j =
      (q ^ D.symmetrizer i) ^ D.cartan i j • (e D q j * simpleK D q i) := by
  rw [simpleK_def, k_mul_e, D.pairing_root_simpleTorus, ← D.symmetrizer_mul_cartan, zpow_mul,
    zpow_natCast]

/-- `Eⱼ * Kᵢ⁻¹ = qᵢ^(aᵢⱼ) • (Kᵢ⁻¹ * Eⱼ)`. -/
theorem e_mul_simpleKInv (i j : ι) :
    e D q j * simpleKInv D q i =
      (q ^ D.symmetrizer i) ^ D.cartan i j • (simpleKInv D q i * e D q j) := by
  rw [simpleKInv_def, e_mul_k, map_neg, neg_neg, D.pairing_root_simpleTorus,
    ← D.symmetrizer_mul_cartan, zpow_mul, zpow_natCast]

/-- `Kᵢ⁻¹ * Eⱼ = qᵢ^(-aᵢⱼ) • (Eⱼ * Kᵢ⁻¹)`. -/
theorem simpleKInv_mul_e (i j : ι) :
    simpleKInv D q i * e D q j =
      (q ^ D.symmetrizer i) ^ (-D.cartan i j) • (e D q j * simpleKInv D q i) := by
  rw [simpleKInv_def, k_mul_e, map_neg, D.pairing_root_simpleTorus, ← D.symmetrizer_mul_cartan,
    ← mul_neg, zpow_mul, zpow_natCast]

/-- `Kᵢ * Fⱼ = qᵢ^(-aᵢⱼ) • (Fⱼ * Kᵢ)`. -/
theorem simpleK_mul_f (i j : ι) :
    simpleK D q i * f D q j =
      (q ^ D.symmetrizer i) ^ (-D.cartan i j) • (f D q j * simpleK D q i) := by
  rw [simpleK_def, k_mul_f, D.pairing_root_simpleTorus, ← D.symmetrizer_mul_cartan, ← mul_neg,
    zpow_mul, zpow_natCast]

/-- `Kᵢ⁻¹ * Fⱼ = qᵢ^(aᵢⱼ) • (Fⱼ * Kᵢ⁻¹)`. -/
theorem simpleKInv_mul_f (i j : ι) :
    simpleKInv D q i * f D q j =
      (q ^ D.symmetrizer i) ^ D.cartan i j • (f D q j * simpleKInv D q i) := by
  rw [simpleKInv_def, k_mul_f, map_neg, neg_neg, D.pairing_root_simpleTorus,
    ← D.symmetrizer_mul_cartan, zpow_mul, zpow_natCast]

/-- `Fⱼ * Kᵢ = qᵢ^(aᵢⱼ) • (Kᵢ * Fⱼ)`. -/
theorem f_mul_simpleK (i j : ι) :
    f D q j * simpleK D q i =
      (q ^ D.symmetrizer i) ^ D.cartan i j • (simpleK D q i * f D q j) := by
  rw [simpleK_def, f_mul_k, D.pairing_root_simpleTorus, ← D.symmetrizer_mul_cartan, zpow_mul,
    zpow_natCast]

/-- The diagonal commutator relation `Eᵢ Fᵢ - Fᵢ Eᵢ = (qᵢ - qᵢ⁻¹)⁻¹ • (Kᵢ - Kᵢ⁻¹)`. -/
theorem e_mul_f_sub_f_mul_e_self (i : ι) :
    e D q i * f D q i - f D q i * e D q i =
      (q ^ D.symmetrizer i - (q ^ D.symmetrizer i)⁻¹)⁻¹ •
        (simpleK D q i - simpleKInv D q i) := by
  simpa only [map_sub, map_mul, map_smul, mkAlgHom_ι, generator_e, generator_f, generator_k,
    ← simpleK_def, ← simpleKInv_def] using mkAlgHom_rel (Rel.commutator_self (D := D) (q := q) i)

/-- Distinct raising and lowering generators commute: `Eᵢ Fⱼ - Fⱼ Eᵢ = 0` for `i ≠ j`. -/
theorem e_mul_f_sub_f_mul_e_ne {i j : ι} (hij : i ≠ j) :
    e D q i * f D q j - f D q j * e D q i = 0 := by
  simpa only [map_sub, map_mul, map_zero, mkAlgHom_ι, generator_e, generator_f] using
    mkAlgHom_rel (Rel.commutator_ne (D := D) (q := q) hij)

/-- For `i ≠ j`, `Eᵢ * Fⱼ = Fⱼ * Eᵢ`. -/
theorem e_mul_f_of_ne {i j : ι} (hij : i ≠ j) :
    e D q i * f D q j = f D q j * e D q i :=
  sub_eq_zero.mp (e_mul_f_sub_f_mul_e_ne hij)

/-- Combined Kronecker-delta form of the `[Eᵢ, Fⱼ]` commutator relation. -/
theorem e_mul_f_sub_f_mul_e [DecidableEq ι] (i j : ι) :
    e D q i * f D q j - f D q j * e D q i =
      if i = j then
        (q ^ D.symmetrizer i - (q ^ D.symmetrizer i)⁻¹)⁻¹ •
          (simpleK D q i - simpleKInv D q i)
      else 0 := by
  split_ifs with hij
  · subst hij
    exact e_mul_f_sub_f_mul_e_self i
  · exact e_mul_f_sub_f_mul_e_ne hij

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

/-- When `aᵢⱼ = 0` and `(q^(dᵢ))² ≠ 1`, the raising generators `Eᵢ` and `Eⱼ` commute. -/
theorem e_mul_e_of_cartan_eq_zero {i j : ι} (h : D.cartan i j = 0)
    (hq : (q ^ D.symmetrizer i) ^ 2 ≠ 1) :
    e D q i * e D q j = e D q j * e D q i := by
  rcases eq_or_ne q 0 with rfl | hq₀
  · simp
  have hij : i ≠ j := by rintro rfl; simp at h
  have hsub : q ^ D.symmetrizer i - (q ^ D.symmetrizer i)⁻¹ ≠ 0 := fun h0 => by
    have h := mul_inv_cancel₀ (pow_ne_zero (D.symmetrizer i) hq₀)
    exact hq (by rwa [← sub_eq_zero.mp h0, ← sq] at h)
  have hserre := serre_e_eq_zero (D := D) (q := q) hij
  rw [D.serreLength_of_cartan_eq_zero h, quantumSerre_one hsub] at hserre
  exact (sub_eq_zero.mp hserre).symm

/-- When `aᵢⱼ = 0` and `(q^(dᵢ))² ≠ 1`, the lowering generators `Fᵢ` and `Fⱼ` commute. -/
theorem f_mul_f_of_cartan_eq_zero {i j : ι} (h : D.cartan i j = 0)
    (hq : (q ^ D.symmetrizer i) ^ 2 ≠ 1) :
    f D q i * f D q j = f D q j * f D q i := by
  rcases eq_or_ne q 0 with rfl | hq₀
  · simp
  have hij : i ≠ j := by rintro rfl; simp at h
  have hsub : q ^ D.symmetrizer i - (q ^ D.symmetrizer i)⁻¹ ≠ 0 := fun h0 => by
    have h := mul_inv_cancel₀ (pow_ne_zero (D.symmetrizer i) hq₀)
    exact hq (by rwa [← sub_eq_zero.mp h0, ← sq] at h)
  have hserre := serre_f_eq_zero (D := D) (q := q) hij
  rw [D.serreLength_of_cartan_eq_zero h, quantumSerre_one hsub] at hserre
  exact (sub_eq_zero.mp hserre).symm

/-! ### Universal property and generation -/

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
  /-- `K_0 = 1`. -/
  k_zero : k 0 = 1
  /-- `K_(y + z) = K_y * K_z`. -/
  k_add (y z : Y) : k (y + z) = k y * k z
  /-- `K_y * Eᵢ = q^⟨αᵢ, y⟩ • (Eᵢ * K_y)`. -/
  k_mul_e (i : ι) (y : Y) : k y * e i = q ^ D.pairing (D.root i) y • (e i * k y)
  /-- `K_y * Fᵢ = q^(-⟨αᵢ, y⟩) • (Fᵢ * K_y)`. -/
  k_mul_f (i : ι) (y : Y) : k y * f i = q ^ (-D.pairing (D.root i) y) • (f i * k y)
  /-- Diagonal `[Eᵢ, Fᵢ]` commutator relation. -/
  commutator_self (i : ι) :
    e i * f i - f i * e i =
      (q ^ D.symmetrizer i - (q ^ D.symmetrizer i)⁻¹)⁻¹ •
        (k (D.simpleTorus i) - k (-D.simpleTorus i))
  /-- Off-diagonal `[Eᵢ, Fⱼ] = 0` commutator relation. -/
  commutator_ne {i j : ι} (hij : i ≠ j) : e i * f j - f j * e i = 0
  /-- Raising quantum Serre relation. -/
  serre_e {i j : ι} (hij : i ≠ j) :
    quantumSerre (q ^ D.symmetrizer i) (D.serreLength i j) (e i) (e j) = 0
  /-- Lowering quantum Serre relation. -/
  serre_f {i j : ι} (hij : i ≠ j) :
    quantumSerre (q ^ D.symmetrizer i) (D.serreLength i j) (f i) (f j) = 0

namespace GeneratorTuple

variable {D : CartanDatum ι X Y} {q : K} {A : Type*} [Ring A] [Algebra K A]

/-- Evaluation of a `GeneratorTuple` on formal generators. -/
def toFun (t : GeneratorTuple D q A) : Generator ι Y → A
  | .e i => t.e i
  | .f i => t.f i
  | .k y => t.k y

/-- `toFun` sends `.e i` to `t.e i`. -/
@[simp] theorem toFun_e (t : GeneratorTuple D q A) (i : ι) : t.toFun (.e i) = t.e i := (rfl)

/-- `toFun` sends `.f i` to `t.f i`. -/
@[simp] theorem toFun_f (t : GeneratorTuple D q A) (i : ι) : t.toFun (.f i) = t.f i := (rfl)

/-- `toFun` sends `.k y` to `t.k y`. -/
@[simp] theorem toFun_k (t : GeneratorTuple D q A) (y : Y) : t.toFun (.k y) = t.k y := (rfl)

/-- Two generator tuples with the same images on `Eᵢ`, `Fᵢ`, and `K_y` are equal. -/
@[ext]
theorem ext {s t : GeneratorTuple D q A}
    (he : ∀ i, s.e i = t.e i) (hf : ∀ i, s.f i = t.f i) (hk : ∀ y, s.k y = t.k y) : s = t := by
  cases s
  cases t
  simp only [mk.injEq]
  exact ⟨funext he, funext hf, funext hk⟩

end GeneratorTuple

section Lift

variable {D : CartanDatum ι X Y} {q : K} {A : Type*} [Ring A] [Algebra K A]

/-- The universal property of `QuantizedEnvelopingAlgebra D q`: a `GeneratorTuple` extends to a
`K`-algebra homomorphism. -/
def lift (t : GeneratorTuple D q A) : QuantizedEnvelopingAlgebra D q →ₐ[K] A :=
  RingQuot.liftAlgHom K ⟨FreeAlgebra.lift K t.toFun, by
    rintro a b (_ | ⟨y, z⟩ | ⟨i, y⟩ | ⟨i, y⟩ | ⟨i⟩ | @⟨i, j, hij⟩ | @⟨i, j, hij⟩ | @⟨i, j, hij⟩)
    · simpa only [map_one, FreeAlgebra.lift_ι_apply, GeneratorTuple.toFun_k] using t.k_zero
    · simpa only [map_mul, FreeAlgebra.lift_ι_apply, GeneratorTuple.toFun_k] using t.k_add y z
    · simpa only [map_mul, map_smul, FreeAlgebra.lift_ι_apply, GeneratorTuple.toFun_k,
        GeneratorTuple.toFun_e] using t.k_mul_e i y
    · simpa only [map_mul, map_smul, FreeAlgebra.lift_ι_apply, GeneratorTuple.toFun_k,
        GeneratorTuple.toFun_f] using t.k_mul_f i y
    · simpa only [map_sub, map_mul, map_smul, FreeAlgebra.lift_ι_apply, GeneratorTuple.toFun_e,
        GeneratorTuple.toFun_f, GeneratorTuple.toFun_k] using t.commutator_self i
    · simpa only [map_sub, map_mul, map_zero, FreeAlgebra.lift_ι_apply, GeneratorTuple.toFun_e,
        GeneratorTuple.toFun_f] using t.commutator_ne hij
    · simpa only [AlgHom.map_quantumSerre, map_zero, FreeAlgebra.lift_ι_apply,
        GeneratorTuple.toFun_e] using t.serre_e hij
    · simpa only [AlgHom.map_quantumSerre, map_zero, FreeAlgebra.lift_ι_apply,
        GeneratorTuple.toFun_f] using t.serre_f hij⟩

/-- `lift t` evaluates to `t.toFun g` on every formal generator `g`. -/
@[simp]
theorem lift_generator (t : GeneratorTuple D q A) (g : Generator ι Y) :
    lift t (generator D q g) = t.toFun g :=
  (RingQuot.liftAlgHom_mkAlgHom_apply K _ _ _).trans (FreeAlgebra.lift_ι_apply _ _)

/-- `lift t` sends `Eᵢ` to `t.e i`. -/
@[simp]
theorem lift_e (t : GeneratorTuple D q A) (i : ι) : lift t (e D q i) = t.e i :=
  lift_generator t (.e i)

/-- `lift t` sends `Fᵢ` to `t.f i`. -/
@[simp]
theorem lift_f (t : GeneratorTuple D q A) (i : ι) : lift t (f D q i) = t.f i :=
  lift_generator t (.f i)

/-- `lift t` sends `K_y` to `t.k y`. -/
@[simp]
theorem lift_k (t : GeneratorTuple D q A) (y : Y) : lift t (k D q y) = t.k y :=
  lift_generator t (.k y)

/-- `lift t` sends `Kᵢ` to `t.k (D.simpleTorus i)`. -/
@[simp]
theorem lift_simpleK (t : GeneratorTuple D q A) (i : ι) :
    lift t (simpleK D q i) = t.k (D.simpleTorus i) :=
  lift_k t (D.simpleTorus i)

/-- `lift t` sends `Kᵢ⁻¹` to `t.k (-D.simpleTorus i)`. -/
@[simp]
theorem lift_simpleKInv (t : GeneratorTuple D q A) (i : ι) :
    lift t (simpleKInv D q i) = t.k (-D.simpleTorus i) :=
  lift_k t (-D.simpleTorus i)

/-- Two `K`-algebra homomorphisms from `QuantizedEnvelopingAlgebra D q` agreeing on `Eᵢ`, `Fᵢ`,
and `K_y` are equal. -/
@[ext high]
theorem hom_ext {φ ψ : QuantizedEnvelopingAlgebra D q →ₐ[K] A}
    (he : ∀ i, φ (e D q i) = ψ (e D q i))
    (hf : ∀ i, φ (f D q i) = ψ (f D q i))
    (hk : ∀ y, φ (k D q y) = ψ (k D q y)) : φ = ψ := by
  apply RingQuot.ringQuot_ext' K φ ψ
  apply FreeAlgebra.hom_ext
  funext g
  cases g with
  | e i => exact he i
  | f i => exact hf i
  | k y => exact hk y

/-- `K`-algebra homomorphisms out of `QuantizedEnvelopingAlgebra D q` are equivalent to
`GeneratorTuple D q A`. -/
def liftEquiv : (QuantizedEnvelopingAlgebra D q →ₐ[K] A) ≃ GeneratorTuple D q A where
  toFun φ :=
    { e i := φ (e D q i)
      f i := φ (f D q i)
      k y := φ (k D q y)
      k_zero := by rw [k_zero, map_one]
      k_add y z := by rw [k_add, map_mul]
      k_mul_e i y := by
        simpa only [map_mul, map_smul] using congrArg φ (k_mul_e (D := D) (q := q) i y)
      k_mul_f i y := by
        simpa only [map_mul, map_smul] using congrArg φ (k_mul_f (D := D) (q := q) i y)
      commutator_self i := by
        simpa only [map_sub, map_mul, map_smul, simpleK_def, simpleKInv_def] using
          congrArg φ (e_mul_f_sub_f_mul_e_self (D := D) (q := q) i)
      commutator_ne hij := by
        simpa only [map_sub, map_mul, map_zero] using
          congrArg φ (e_mul_f_sub_f_mul_e_ne (D := D) (q := q) hij)
      serre_e hij := by
        simpa only [AlgHom.map_quantumSerre, map_zero] using
          congrArg φ (serre_e_eq_zero (D := D) (q := q) hij)
      serre_f hij := by
        simpa only [AlgHom.map_quantumSerre, map_zero] using
          congrArg φ (serre_f_eq_zero (D := D) (q := q) hij) }
  invFun := lift
  left_inv φ := hom_ext (by simp) (by simp) (by simp)
  right_inv t := by ext <;> simp

/-- `liftEquiv φ` records the value of `φ` on `Eᵢ`. -/
@[simp]
theorem liftEquiv_apply_e (φ : QuantizedEnvelopingAlgebra D q →ₐ[K] A) (i : ι) :
    (liftEquiv φ).e i = φ (e D q i) := (rfl)

/-- `liftEquiv φ` records the value of `φ` on `Fᵢ`. -/
@[simp]
theorem liftEquiv_apply_f (φ : QuantizedEnvelopingAlgebra D q →ₐ[K] A) (i : ι) :
    (liftEquiv φ).f i = φ (f D q i) := (rfl)

/-- `liftEquiv φ` records the value of `φ` on `K_y`. -/
@[simp]
theorem liftEquiv_apply_k (φ : QuantizedEnvelopingAlgebra D q →ₐ[K] A) (y : Y) :
    (liftEquiv φ).k y = φ (k D q y) := (rfl)

/-- The inverse of `liftEquiv` is `lift`. -/
@[simp]
theorem liftEquiv_symm_apply (t : GeneratorTuple D q A) :
    liftEquiv.symm t = lift t := (rfl)

end Lift

/-- The formal generators `Eᵢ`, `Fᵢ`, and `K_y` generate `QuantizedEnvelopingAlgebra D q` as a
`K`-algebra. -/
theorem adjoin_range_generator (D : CartanDatum ι X Y) (q : K) :
    Algebra.adjoin K (Set.range (generator D q)) = ⊤ := by
  rw [Algebra.adjoin_range_eq_range_freeAlgebra_lift]
  have h : FreeAlgebra.lift K (generator D q) = mkAlgHom D q := by
    apply FreeAlgebra.hom_ext
    funext g
    simp
  rw [h, AlgHom.range_eq_top]
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
    (mul : ∀ a b, P a → P b → P (a * b))
    (add : ∀ a b, P a → P b → P (a + b))
    (x : QuantizedEnvelopingAlgebra D q) : P x := by
  have hx : x ∈ Algebra.adjoin K (Set.range (generator D q)) := by
    rw [adjoin_range_generator]
    exact Algebra.mem_top
  induction hx using Algebra.adjoin_induction with
  | mem a ha =>
    obtain ⟨g, rfl⟩ := ha
    cases g with
    | e i => exact e i
    | f i => exact f i
    | k y => exact k y
  | algebraMap c => exact algebraMap c
  | add a b _ _ ha hb => exact add a b ha hb
  | mul a b _ _ ha hb => exact mul a b ha hb

/-- An element of `QuantizedEnvelopingAlgebra D q` commuting with every `Eᵢ`, `Fᵢ`, and `K_y`
commutes with the entire algebra. -/
theorem commute_of_commute_generators {z : QuantizedEnvelopingAlgebra D q}
    (he : ∀ i, Commute (e D q i) z)
    (hf : ∀ i, Commute (f D q i) z)
    (hk : ∀ y, Commute (k D q y) z)
    (a : QuantizedEnvelopingAlgebra D q) : Commute a z := by
  refine (Algebra.commute_of_mem_adjoin_of_forall_mem_commute (R := K)
    (s := Set.range (generator D q)) ?_ ?_).symm
  · rw [adjoin_range_generator]
    exact Algebra.mem_top
  · rintro _ ⟨g, rfl⟩
    cases g with
    | e i => exact (he i).symm
    | f i => exact (hf i).symm
    | k y => exact (hk y).symm

/-- For a coweight `c ∈ Y` annihilated by every simple root (`⟨αᵢ, c⟩ = 0` for all `i`), the toral
generator `K_c` lies in the center of `QuantizedEnvelopingAlgebra D q`. -/
theorem k_mem_center_of_pairing_root_eq_zero {c : Y}
    (hc : ∀ i, D.pairing (D.root i) c = 0) :
    k D q c ∈ Subalgebra.center K (QuantizedEnvelopingAlgebra D q) := by
  rw [Subalgebra.mem_center_iff]
  refine commute_of_commute_generators (fun i => ?_) (fun i => ?_) (fun y => ?_)
  · rw [Commute, SemiconjBy, k_mul_e, hc i, zpow_zero, one_smul]
  · rw [Commute, SemiconjBy, k_mul_f, hc i, neg_zero, zpow_zero, one_smul]
  · rw [Commute, SemiconjBy, ← k_add, ← k_add, add_comm]

end UniversalProperty

/-! ### Functoriality in the Cartan datum -/

section Map

variable {ι X Y X' Y' X'' Y'' K : Type*} [AddCommGroup X] [AddCommGroup Y]
  [AddCommGroup X'] [AddCommGroup Y'] [AddCommGroup X''] [AddCommGroup Y''] [Field K]

/-- A morphism of Cartan data `φ : D.Hom D'` induces a `K`-algebra homomorphism
`QuantizedEnvelopingAlgebra D q →ₐ[K] QuantizedEnvelopingAlgebra D' q` sending `Eᵢ ↦ Eᵢ`,
`Fᵢ ↦ Fᵢ`, and `K_y ↦ K_(φ y)`. -/
def map {D : CartanDatum ι X Y} {D' : CartanDatum ι X' Y'} (φ : D.Hom D') (q : K) :
    QuantizedEnvelopingAlgebra D q →ₐ[K] QuantizedEnvelopingAlgebra D' q :=
  lift
    { e i := e D' q i
      f i := f D' q i
      k y := k D' q (φ.toLinearMap y)
      k_zero := by simp
      k_add y z := by rw [map_add, k_add]
      k_mul_e i y := by rw [k_mul_e, φ.pairing_root_map]
      k_mul_f i y := by rw [k_mul_f, φ.pairing_root_map]
      commutator_self i := by
        rw [e_mul_f_sub_f_mul_e_self, φ.symmetrizer_eq, simpleK_def, simpleKInv_def,
          ← φ.map_simpleTorus, map_neg]
      commutator_ne hij := e_mul_f_sub_f_mul_e_ne hij
      serre_e hij := by
        rw [← φ.symmetrizer_eq, ← φ.serreLength_eq]
        exact serre_e_eq_zero hij
      serre_f hij := by
        rw [← φ.symmetrizer_eq, ← φ.serreLength_eq]
        exact serre_f_eq_zero hij }

/-- `map φ q` preserves `Eᵢ`. -/
@[simp]
theorem map_e {D : CartanDatum ι X Y} {D' : CartanDatum ι X' Y'} (φ : D.Hom D') {q : K} (i : ι) :
    map φ q (e D q i) = e D' q i :=
  lift_e _ i

/-- `map φ q` preserves `Fᵢ`. -/
@[simp]
theorem map_f {D : CartanDatum ι X Y} {D' : CartanDatum ι X' Y'} (φ : D.Hom D') {q : K} (i : ι) :
    map φ q (f D q i) = f D' q i :=
  lift_f _ i

/-- `map φ q` sends `K_y` to `K_(φ y)`. -/
@[simp]
theorem map_k {D : CartanDatum ι X Y} {D' : CartanDatum ι X' Y'} (φ : D.Hom D') {q : K} (y : Y) :
    map φ q (k D q y) = k D' q (φ.toLinearMap y) :=
  lift_k _ y

/-- `map φ q` preserves `Kᵢ`. -/
@[simp]
theorem map_simpleK {D : CartanDatum ι X Y} {D' : CartanDatum ι X' Y'} (φ : D.Hom D') {q : K}
    (i : ι) : map φ q (simpleK D q i) = simpleK D' q i := by
  rw [simpleK_def, map_k, φ.map_simpleTorus, ← simpleK_def]

/-- `map φ q` preserves `Kᵢ⁻¹`. -/
@[simp]
theorem map_simpleKInv {D : CartanDatum ι X Y} {D' : CartanDatum ι X' Y'} (φ : D.Hom D') {q : K}
    (i : ι) : map φ q (simpleKInv D q i) = simpleKInv D' q i := by
  rw [simpleKInv_def, map_k, map_neg, φ.map_simpleTorus, ← simpleKInv_def]

/-- `map` sends the identity Cartan datum morphism to the identity algebra homomorphism. -/
@[simp]
theorem map_id (D : CartanDatum ι X Y) (q : K) :
    map (CartanDatum.Hom.id D) q = AlgHom.id K (QuantizedEnvelopingAlgebra D q) := by
  ext <;> simp

/-- `map` preserves composition of Cartan datum morphisms. -/
theorem map_comp {D : CartanDatum ι X Y} {D' : CartanDatum ι X' Y'} {D'' : CartanDatum ι X'' Y''}
    (ψ : D'.Hom D'') (φ : D.Hom D') (q : K) :
    map (ψ.comp φ) q = (map ψ q).comp (map φ q) := by
  ext <;> simp

end Map

/-! ### Diagonal rescaling automorphisms -/

section Rescale

variable {ι X Y K : Type*} [AddCommGroup X] [AddCommGroup Y] [Field K]

/-- Rescaling `Eᵢ ↦ cᵢ • Eᵢ`, `Fᵢ ↦ cᵢ⁻¹ • Fᵢ`, and `K_y ↦ K_y` for a family of units
`c : ι → Kˣ` defines an endomorphism of `QuantizedEnvelopingAlgebra D q`. -/
def rescaleAlgHom (D : CartanDatum ι X Y) (q : K) (c : ι → Kˣ) :
    QuantizedEnvelopingAlgebra D q →ₐ[K] QuantizedEnvelopingAlgebra D q :=
  lift
    { e i := (c i : K) • e D q i
      f i := ((c i : K))⁻¹ • f D q i
      k y := k D q y
      k_zero := k_zero
      k_add := k_add
      k_mul_e i y := by rw [mul_smul_comm, k_mul_e, smul_comm, smul_mul_assoc]
      k_mul_f i y := by rw [mul_smul_comm, k_mul_f, smul_comm, smul_mul_assoc]
      commutator_self i := by
        rw [smul_mul_smul_comm, smul_mul_smul_comm, mul_inv_cancel₀ (c i).ne_zero,
          inv_mul_cancel₀ (c i).ne_zero, one_smul, one_smul, e_mul_f_sub_f_mul_e_self,
          simpleK_def, simpleKInv_def]
      commutator_ne {i j} hij := by
        rw [smul_mul_smul_comm, smul_mul_smul_comm, mul_comm ((c j : K))⁻¹, ← smul_sub,
          e_mul_f_sub_f_mul_e_ne hij, smul_zero]
      serre_e {i j} hij := by
        rw [quantumSerre_smul, serre_e_eq_zero hij, smul_zero]
      serre_f {i j} hij := by
        rw [quantumSerre_smul, serre_f_eq_zero hij, smul_zero] }

variable {D : CartanDatum ι X Y} {q : K}

/-- `rescaleAlgHom` scales `Eᵢ` by `cᵢ`. -/
@[simp]
theorem rescaleAlgHom_e (c : ι → Kˣ) (i : ι) :
    rescaleAlgHom D q c (e D q i) = (c i : K) • e D q i :=
  lift_e _ i

/-- `rescaleAlgHom` scales `Fᵢ` by `cᵢ⁻¹`. -/
@[simp]
theorem rescaleAlgHom_f (c : ι → Kˣ) (i : ι) :
    rescaleAlgHom D q c (f D q i) = (c i : K)⁻¹ • f D q i :=
  lift_f _ i

/-- `rescaleAlgHom` fixes every toral generator `K_y`. -/
@[simp]
theorem rescaleAlgHom_k (c : ι → Kˣ) (y : Y) :
    rescaleAlgHom D q c (k D q y) = k D q y :=
  lift_k _ y

/-- Rescaling by `1` is the identity endomorphism. -/
@[simp]
theorem rescaleAlgHom_one :
    rescaleAlgHom D q 1 = AlgHom.id K (QuantizedEnvelopingAlgebra D q) := by
  ext <;> simp

/-- Rescaling is a group action of `ι → Kˣ` by algebra endomorphisms. -/
theorem rescaleAlgHom_mul (c d : ι → Kˣ) :
    rescaleAlgHom D q (c * d) = (rescaleAlgHom D q c).comp (rescaleAlgHom D q d) := by
  ext i
  · simp [smul_smul, mul_comm]
  · simp [smul_smul]
  · simp

/-- The `K`-algebra automorphism rescaling `Eᵢ ↦ cᵢ • Eᵢ`, `Fᵢ ↦ cᵢ⁻¹ • Fᵢ`, and fixing `K_y`. -/
def rescaleAlgEquiv (D : CartanDatum ι X Y) (q : K) (c : ι → Kˣ) :
    QuantizedEnvelopingAlgebra D q ≃ₐ[K] QuantizedEnvelopingAlgebra D q :=
  AlgEquiv.ofAlgHom (rescaleAlgHom D q c) (rescaleAlgHom D q c⁻¹)
    (by rw [← rescaleAlgHom_mul, mul_inv_cancel, rescaleAlgHom_one])
    (by rw [← rescaleAlgHom_mul, inv_mul_cancel, rescaleAlgHom_one])

/-- Coercing `rescaleAlgEquiv` to an `AlgHom` recovers `rescaleAlgHom`. -/
@[simp]
theorem rescaleAlgEquiv_toAlgHom (c : ι → Kˣ) :
    (rescaleAlgEquiv D q c).toAlgHom = rescaleAlgHom D q c :=
  (rfl)

/-- `rescaleAlgEquiv` scales `Eᵢ` by `cᵢ`. -/
@[simp]
theorem rescaleAlgEquiv_e (c : ι → Kˣ) (i : ι) :
    rescaleAlgEquiv D q c (e D q i) = (c i : K) • e D q i :=
  rescaleAlgHom_e c i

/-- `rescaleAlgEquiv` scales `Fᵢ` by `cᵢ⁻¹`. -/
@[simp]
theorem rescaleAlgEquiv_f (c : ι → Kˣ) (i : ι) :
    rescaleAlgEquiv D q c (f D q i) = (c i : K)⁻¹ • f D q i :=
  rescaleAlgHom_f c i

/-- `rescaleAlgEquiv` fixes every toral generator `K_y`. -/
@[simp]
theorem rescaleAlgEquiv_k (c : ι → Kˣ) (y : Y) :
    rescaleAlgEquiv D q c (k D q y) = k D q y :=
  rescaleAlgHom_k c y

/-- The inverse of `rescaleAlgEquiv D q c` is `rescaleAlgEquiv D q c⁻¹`. -/
@[simp]
theorem rescaleAlgEquiv_symm (c : ι → Kˣ) :
    (rescaleAlgEquiv D q c).symm = rescaleAlgEquiv D q c⁻¹ :=
  (rfl)

end Rescale

end QuantizedEnvelopingAlgebra

end TauCeti
