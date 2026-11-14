/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.FreeAlgebra
public import Mathlib.Algebra.RingQuot
public import TauCeti.LinearAlgebra.Matrix.Cartan.Datum.Hom
public import TauCeti.QuantumGroups.QuantumInteger.Factorial

import Mathlib.Tactic

/-!
# The Drinfeld–Jimbo quantized enveloping algebra of a Cartan datum

Given a symmetrizable Cartan datum `D : CartanDatum ι X Y` (`TauCeti.CartanDatum`) and a scalar
parameter `q` in a field `K`, this file defines the Drinfeld–Jimbo quantized enveloping algebra
`TauCeti.QuantizedEnvelopingAlgebra D q` by generators `Eᵢ`, `Fᵢ` (`i : ι`) and `K_y` (`y : Y`)
subject to

* the toral group relations `K_0 = 1` and `K_y K_z = K_(y + z)`;
* the toral conjugation relations `K_y Eᵢ K_(-y) = q^⟨αᵢ, y⟩ Eᵢ` and
  `K_y Fᵢ K_(-y) = q^(-⟨αᵢ, y⟩) Fᵢ`;
* the commutator relations `Eᵢ Fⱼ - Fⱼ Eᵢ = δᵢⱼ (Kᵢ - Kᵢ⁻¹) / (qᵢ - qᵢ⁻¹)`, where
  `qᵢ = q^(dᵢ)` and `Kᵢ = K_(dᵢ hᵢ)`;
* for `i ≠ j`, the quantum Serre relations
  `∑_{r + s = 1 - aᵢⱼ} (-1)^r Eᵢ^(r) Eⱼ Eᵢ^(s) = 0` and
  `∑_{r + s = 1 - aᵢⱼ} (-1)^r Fᵢ^(r) Fⱼ Fᵢ^(s) = 0`, written with `qᵢ`-divided powers
  `x^(r) = [r]_(qᵢ)!⁻¹ • x^r` (`TauCeti.quantumDividedPower`).

Because a toral generator `K_y` is included for every coweight `y ∈ Y`, central directions
(`⟨αᵢ, c⟩ = 0` for all `i`) and intermediate lattices between the coroot lattice and its
saturation are retained in the presentation. No finiteness, decidable equality, or freeness
assumptions on `ι`, `X`, or `Y` are imposed, and the quotient is defined for every `q : K` (at
`q = 0`, the conjugation relations at `hᵢ` force `Eᵢ = Fᵢ = 0`).

## Main definitions

* `TauCeti.QuantizedEnvelopingAlgebra.Generator`: the free generator alphabet (`e i`, `f i`,
  `k y`).
* `TauCeti.QuantizedEnvelopingAlgebra.Rel`: the defining relation on the free algebra.
* `TauCeti.QuantizedEnvelopingAlgebra`: the quotient algebra `U_q(D)`.
* `TauCeti.QuantizedEnvelopingAlgebra.e`, `f`, `k`, `simpleK`, `simpleKInv`, `normalizedE`,
  `normalizedF`: the generators and normalized operators `Kᵢ⁻¹ Eᵢ` and `Fᵢ Kᵢ`.
* `TauCeti.QuantizedEnvelopingAlgebra.kUnitsHom`: the group homomorphism `Multiplicative Y →* Uˣ`
  packaging `K_y` with inverse `K_(-y)`.
* `TauCeti.QuantizedEnvelopingAlgebra.GeneratorTuple`, `lift`, `liftEquiv`: the universal property
  of the presentation.
* `TauCeti.QuantizedEnvelopingAlgebra.rescale`: the diagonal rescaling automorphisms
  `Eᵢ ↦ cᵢ • Eᵢ`, `Fᵢ ↦ cᵢ⁻¹ • Fᵢ`, `K_y ↦ K_y`.
* `TauCeti.QuantizedEnvelopingAlgebra.chevalleyInvolution`: the `K`-algebra involution
  `Eᵢ ↔ Fᵢ`, `K_y ↦ K_(-y)`.
* `TauCeti.QuantizedEnvelopingAlgebra.map`: functoriality along a morphism of Cartan data
  `CartanDatum.Hom D D'`.

## Main results

* `TauCeti.QuantizedEnvelopingAlgebra.hom_ext`, `adjoin_range_generator`, `induction`: morphism
  extensionality and generator induction on `U_q(D)`.
* `TauCeti.QuantizedEnvelopingAlgebra.commute_e_e_of_cartan_eq_zero` and
  `commute_f_f_of_cartan_eq_zero`: `Eᵢ` and `Eⱼ` (resp. `Fᵢ` and `Fⱼ`) commute when `i ≠ j`,
  `aᵢⱼ = 0`, and `qᵢ - qᵢ⁻¹ ≠ 0`.
* `TauCeti.QuantizedEnvelopingAlgebra.k_mem_center_of_pairing_root_eq_zero`: `K_c` lies in the
  center whenever `⟨αᵢ, c⟩ = 0` for every `i`.

## References

* G. Lusztig, *Introduction to Quantum Groups*, Progress in Mathematics 110, Birkhäuser, 1993,
  §3.1.
* J. C. Jantzen, *Lectures on Quantum Groups*, Graduate Studies in Mathematics 6, American
  Mathematical Society, 1996, Chapter 4.
* S. Lentner, *Quantum groups and Nichols algebras acting on conformal field theories*, Adv. Math.
  268 (2015), 247--316, Definition 3.2.
-/

public section

open Finset

namespace TauCeti

namespace QuantizedEnvelopingAlgebra

/-- The generator alphabet of a quantized enveloping algebra: raising generators `Eᵢ`, lowering
generators `Fᵢ`, and a toral generator `K_y` for every element `y` of the coweight lattice `Y`. -/
inductive Generator (ι Y : Type*)
  /-- The raising generator `Eᵢ` at node `i`. -/
  | e (i : ι)
  /-- The lowering generator `Fᵢ` at node `i`. -/
  | f (i : ι)
  /-- The toral generator `K_y` at coweight `y`. -/
  | k (y : Y)

section FreeAlgebra

variable {ι X Y : Type*}

/-- The raising generator `Eᵢ` in the free `K`-algebra on `Generator ι Y`. -/
def freeE (K : Type*) [Field K] (i : ι) : FreeAlgebra K (Generator ι Y) :=
  FreeAlgebra.ι K (.e i)

/-- The lowering generator `Fᵢ` in the free `K`-algebra on `Generator ι Y`. -/
def freeF (K : Type*) [Field K] (i : ι) : FreeAlgebra K (Generator ι Y) :=
  FreeAlgebra.ι K (.f i)

/-- The toral generator `K_y` in the free `K`-algebra on `Generator ι Y`. -/
def freeK (K : Type*) [Field K] (y : Y) : FreeAlgebra K (Generator ι Y) :=
  FreeAlgebra.ι K (.k y)

theorem freeE_def (K : Type*) [Field K] (i : ι) :
    freeE K (Y := Y) i = FreeAlgebra.ι K (.e i) := (rfl)

theorem freeF_def (K : Type*) [Field K] (i : ι) :
    freeF K (Y := Y) i = FreeAlgebra.ι K (.f i) := (rfl)

theorem freeK_def (K : Type*) [Field K] (y : Y) :
    freeK K (ι := ι) y = FreeAlgebra.ι K (.k y) := (rfl)

variable [AddCommGroup X] [AddCommGroup Y] {K : Type*} [Field K]

/-- Given candidate generator families `e`, `f` in a `K`-algebra `A`, the quantum Serre combination
`∑_{r = 0}^{1 - aᵢⱼ} (-1)^r eᵢ^(r) eⱼ eᵢ^(1 - aᵢⱼ - r)` formed with `qᵢ`-divided powers. -/
noncomputable def serreSum {A : Type*} [Semiring A] [Algebra K A]
    (D : CartanDatum ι X Y) (q : K) (x : ι → A) (i j : ι) : A :=
  ∑ r ∈ range (D.serreLength i j + 1),
    ((-1 : K) ^ r) •
      (quantumDividedPower (q ^ D.symmetrizer i) (x i) r * x j *
        quantumDividedPower (q ^ D.symmetrizer i) (x i) (D.serreLength i j - r))

theorem serreSum_def {A : Type*} [Semiring A] [Algebra K A]
    (D : CartanDatum ι X Y) (q : K) (x : ι → A) (i j : ι) :
    serreSum D q x i j =
      ∑ r ∈ range (D.serreLength i j + 1),
        ((-1 : K) ^ r) •
          (quantumDividedPower (q ^ D.symmetrizer i) (x i) r * x j *
            quantumDividedPower (q ^ D.symmetrizer i) (x i) (D.serreLength i j - r)) := (rfl)

/-- Algebra homomorphisms preserve `serreSum`. -/
@[simp]
theorem map_serreSum {A B F : Type*} [Semiring A] [Algebra K A] [Semiring B] [Algebra K B]
    [FunLike F A B] [AlgHomClass F K A B] (φ : F)
    (D : CartanDatum ι X Y) (q : K) (x : ι → A) (i j : ι) :
    φ (serreSum D q x i j) = serreSum D q (fun l => φ (x l)) i j := by
  simp [serreSum_def]

/-- Scaling the family `x` by `c` scales `serreSum D q x i j` by `cᵢ^(1 - aᵢⱼ) * cⱼ`. -/
theorem serreSum_smul {A : Type*} [Semiring A] [Algebra K A]
    (D : CartanDatum ι X Y) (q : K) (c : ι → K) (x : ι → A) (i j : ι) :
    serreSum D q (fun l => c l • x l) i j =
      (c i ^ D.serreLength i j * c j) • serreSum D q x i j := by
  rw [serreSum_def, serreSum_def, smul_sum]
  refine sum_congr rfl fun r hr => ?_
  have hrm : r ≤ D.serreLength i j := Nat.lt_succ_iff.mp (mem_range.mp hr)
  simp only [quantumDividedPower_smul, smul_mul_assoc, mul_smul_comm, smul_smul]
  congr 1
  calc
    (-1 : K) ^ r * (c i ^ (D.serreLength i j - r) * (c j * c i ^ r)) =
        (-1 : K) ^ r * (c i ^ (D.serreLength i j - r) * c i ^ r * c j) := by ring
    _ = (c i ^ D.serreLength i j * c j) * (-1 : K) ^ r := by
      rw [← pow_add, Nat.sub_add_cancel hrm]
      ring

/-- The positive quantum Serre element in the free algebra. -/
noncomputable def freeSerreE (D : CartanDatum ι X Y) (q : K) (i j : ι) :
    FreeAlgebra K (Generator ι Y) :=
  serreSum D q (freeE K) i j

/-- The negative quantum Serre element in the free algebra. -/
noncomputable def freeSerreF (D : CartanDatum ι X Y) (q : K) (i j : ι) :
    FreeAlgebra K (Generator ι Y) :=
  serreSum D q (freeF K) i j

theorem freeSerreE_def (D : CartanDatum ι X Y) (q : K) (i j : ι) :
    freeSerreE D q i j = serreSum D q (freeE K) i j := (rfl)

theorem freeSerreF_def (D : CartanDatum ι X Y) (q : K) (i j : ι) :
    freeSerreF D q i j = serreSum D q (freeF K) i j := (rfl)

/-- The defining relations of the Drinfeld–Jimbo quantized enveloping algebra on
`FreeAlgebra K (Generator ι Y)`. Splitting the diagonal and off-diagonal commutator relations
avoids requiring `DecidableEq ι`. -/
inductive Rel (D : CartanDatum ι X Y) (q : K) :
    FreeAlgebra K (Generator ι Y) → FreeAlgebra K (Generator ι Y) → Prop
  /-- `K_0 = 1`. -/
  | k_zero : Rel D q (freeK K 0) 1
  /-- `K_y K_z = K_(y + z)`. -/
  | k_mul_k (y z : Y) : Rel D q (freeK K y * freeK K z) (freeK K (y + z))
  /-- `K_y Eᵢ K_(-y) = q^⟨αᵢ, y⟩ Eᵢ`. -/
  | conjugate_e (y : Y) (i : ι) :
      Rel D q (freeK K y * freeE K i * freeK K (-y)) (q ^ D.pairing (D.root i) y • freeE K i)
  /-- `K_y Fᵢ K_(-y) = q^(-⟨αᵢ, y⟩) Fᵢ`. -/
  | conjugate_f (y : Y) (i : ι) :
      Rel D q (freeK K y * freeF K i * freeK K (-y)) (q ^ (-D.pairing (D.root i) y) • freeF K i)
  /-- `Eᵢ Fᵢ - Fᵢ Eᵢ = (Kᵢ - Kᵢ⁻¹) / (qᵢ - qᵢ⁻¹)`. -/
  | commutator_self (i : ι) :
      Rel D q (freeE K i * freeF K i - freeF K i * freeE K i)
        ((q ^ D.symmetrizer i - (q ^ D.symmetrizer i)⁻¹)⁻¹ •
          (freeK K (D.simpleTorus i) - freeK K (-D.simpleTorus i)))
  /-- `Eᵢ Fⱼ - Fⱼ Eᵢ = 0` for `i ≠ j`. -/
  | commutator_ne {i j : ι} (hij : i ≠ j) :
      Rel D q (freeE K i * freeF K j - freeF K j * freeE K i) 0
  /-- The positive quantum Serre relation for `i ≠ j`. -/
  | serre_e {i j : ι} (hij : i ≠ j) : Rel D q (freeSerreE D q i j) 0
  /-- The negative quantum Serre relation for `i ≠ j`. -/
  | serre_f {i j : ι} (hij : i ≠ j) : Rel D q (freeSerreF D q i j) 0

end FreeAlgebra

end QuantizedEnvelopingAlgebra

/-- The Drinfeld–Jimbo quantized enveloping algebra `U_q(D)` associated to a symmetrizable Cartan
datum `D : CartanDatum ι X Y` and parameter `q : K`, defined as `RingQuot` of the free algebra by
`QuantizedEnvelopingAlgebra.Rel D q`. -/
@[expose]
def QuantizedEnvelopingAlgebra {ι X Y K : Type*} [AddCommGroup X] [AddCommGroup Y] [Field K]
    (D : CartanDatum ι X Y) (q : K) : Type _ :=
  RingQuot (QuantizedEnvelopingAlgebra.Rel D q)

namespace QuantizedEnvelopingAlgebra

section Presentation

variable {ι X Y K : Type*} [AddCommGroup X] [AddCommGroup Y] [Field K]
  (D : CartanDatum ι X Y) (q : K)

noncomputable instance : Ring (QuantizedEnvelopingAlgebra D q) :=
  inferInstanceAs (Ring (RingQuot (Rel D q)))

noncomputable instance : Algebra K (QuantizedEnvelopingAlgebra D q) :=
  inferInstanceAs (Algebra K (RingQuot (Rel D q)))

noncomputable instance : Inhabited (QuantizedEnvelopingAlgebra D q) := ⟨0⟩

/-- The canonical quotient algebra map from the free algebra onto `QuantizedEnvelopingAlgebra D q`.
-/
noncomputable def mkAlgHom :
    FreeAlgebra K (Generator ι Y) →ₐ[K] QuantizedEnvelopingAlgebra D q :=
  RingQuot.mkAlgHom K (Rel D q)

/-- The quotient map onto `QuantizedEnvelopingAlgebra D q` is surjective. -/
theorem mkAlgHom_surjective : Function.Surjective (mkAlgHom D q) :=
  RingQuot.mkAlgHom_surjective K (Rel D q)

private theorem mkAlgHom_eq_of_rel {a b : FreeAlgebra K (Generator ι Y)} (h : Rel D q a b) :
    mkAlgHom D q a = mkAlgHom D q b :=
  RingQuot.mkAlgHom_rel K h

/-- The image in `QuantizedEnvelopingAlgebra D q` of a generator in `Generator ι Y`. -/
noncomputable def generator (g : Generator ι Y) : QuantizedEnvelopingAlgebra D q :=
  mkAlgHom D q (FreeAlgebra.ι K g)

/-- The quotient map takes a free generator to the corresponding generator of `U_q(D)`. -/
@[simp]
theorem mkAlgHom_ι (g : Generator ι Y) :
    mkAlgHom D q (FreeAlgebra.ι K g) = generator D q g := (rfl)

/-- The raising generator `Eᵢ` of `QuantizedEnvelopingAlgebra D q`. -/
noncomputable def e (i : ι) : QuantizedEnvelopingAlgebra D q :=
  generator D q (.e i)

/-- The lowering generator `Fᵢ` of `QuantizedEnvelopingAlgebra D q`. -/
noncomputable def f (i : ι) : QuantizedEnvelopingAlgebra D q :=
  generator D q (.f i)

/-- The toral generator `K_y` (`y ∈ Y`) of `QuantizedEnvelopingAlgebra D q`. -/
noncomputable def k (y : Y) : QuantizedEnvelopingAlgebra D q :=
  generator D q (.k y)

/-- The simple toral generator `Kᵢ = K_(dᵢ hᵢ)`. -/
noncomputable def simpleK (i : ι) : QuantizedEnvelopingAlgebra D q :=
  k D q (D.simpleTorus i)

/-- The inverse simple toral generator `Kᵢ⁻¹ = K_(-dᵢ hᵢ)`. -/
noncomputable def simpleKInv (i : ι) : QuantizedEnvelopingAlgebra D q :=
  k D q (-D.simpleTorus i)

/-- The normalized raising operator `eᵢ = Kᵢ⁻¹ Eᵢ`, satisfying `Δ(eᵢ) = eᵢ ⊗ Kᵢ⁻¹ + 1 ⊗ eᵢ`. -/
noncomputable def normalizedE (i : ι) : QuantizedEnvelopingAlgebra D q :=
  simpleKInv D q i * e D q i

/-- The normalized lowering operator `fᵢ = Fᵢ Kᵢ`, satisfying `Δ(fᵢ) = fᵢ ⊗ 1 + Kᵢ ⊗ fᵢ`. -/
noncomputable def normalizedF (i : ι) : QuantizedEnvelopingAlgebra D q :=
  f D q i * simpleK D q i

theorem e_def (i : ι) : e D q i = generator D q (.e i) := (rfl)

theorem f_def (i : ι) : f D q i = generator D q (.f i) := (rfl)

theorem k_def (y : Y) : k D q y = generator D q (.k y) := (rfl)

theorem simpleK_def (i : ι) : simpleK D q i = k D q (D.simpleTorus i) := (rfl)

theorem simpleKInv_def (i : ι) : simpleKInv D q i = k D q (-D.simpleTorus i) := (rfl)

theorem normalizedE_def (i : ι) : normalizedE D q i = simpleKInv D q i * e D q i := (rfl)

theorem normalizedF_def (i : ι) : normalizedF D q i = f D q i * simpleK D q i := (rfl)

@[simp]
theorem generator_e (i : ι) : generator D q (.e i) = e D q i := (rfl)

@[simp]
theorem generator_f (i : ι) : generator D q (.f i) = f D q i := (rfl)

@[simp]
theorem generator_k (y : Y) : generator D q (.k y) = k D q y := (rfl)

@[simp]
theorem mkAlgHom_freeE (i : ι) : mkAlgHom D q (freeE K i) = e D q i := (rfl)

@[simp]
theorem mkAlgHom_freeF (i : ι) : mkAlgHom D q (freeF K i) = f D q i := (rfl)

@[simp]
theorem mkAlgHom_freeK (y : Y) : mkAlgHom D q (freeK K y) = k D q y := (rfl)

/-! ### Toral group structure -/

/-- `K_0 = 1`. -/
@[simp]
theorem k_zero : k D q 0 = 1 := by
  simpa only [map_one, mkAlgHom_freeK] using mkAlgHom_eq_of_rel D q Rel.k_zero

/-- `K_y K_z = K_(y + z)`. -/
@[simp]
theorem k_mul_k (y z : Y) : k D q y * k D q z = k D q (y + z) := by
  simpa only [map_mul, mkAlgHom_freeK] using mkAlgHom_eq_of_rel D q (Rel.k_mul_k y z)

@[simp]
theorem k_mul_k_assoc (y z : Y) (x : QuantizedEnvelopingAlgebra D q) :
    k D q y * (k D q z * x) = k D q (y + z) * x := by
  rw [← mul_assoc, k_mul_k]

theorem k_add (y z : Y) : k D q (y + z) = k D q y * k D q z :=
  (k_mul_k D q y z).symm

theorem k_mul_k_neg (y : Y) : k D q y * k D q (-y) = 1 := by
  simp

theorem k_neg_mul_k (y : Y) : k D q (-y) * k D q y = 1 := by
  simp

/-- Any two toral generators commute. -/
theorem commute_k_k (y z : Y) : Commute (k D q y) (k D q z) := by
  rw [Commute, SemiconjBy, k_mul_k, k_mul_k, add_comm]

@[simp]
theorem simpleK_mul_simpleKInv (i : ι) : simpleK D q i * simpleKInv D q i = 1 := by
  simp [simpleK_def, simpleKInv_def]

@[simp]
theorem simpleKInv_mul_simpleK (i : ι) : simpleKInv D q i * simpleK D q i = 1 := by
  simp [simpleK_def, simpleKInv_def]

@[simp]
theorem simpleK_mul_simpleKInv_assoc (i : ι) (x : QuantizedEnvelopingAlgebra D q) :
    simpleK D q i * (simpleKInv D q i * x) = x := by
  rw [← mul_assoc, simpleK_mul_simpleKInv, one_mul]

@[simp]
theorem simpleKInv_mul_simpleK_assoc (i : ι) (x : QuantizedEnvelopingAlgebra D q) :
    simpleKInv D q i * (simpleK D q i * x) = x := by
  rw [← mul_assoc, simpleKInv_mul_simpleK, one_mul]

/-- The group homomorphism `Multiplicative Y →* (QuantizedEnvelopingAlgebra D q)ˣ` sending
`ofAdd y` to the unit `K_y` with inverse `K_(-y)`. -/
noncomputable def kUnitsHom : Multiplicative Y →* (QuantizedEnvelopingAlgebra D q)ˣ where
  toFun y := ⟨k D q y.toAdd, k D q (-y.toAdd), k_mul_k_neg D q y.toAdd, k_neg_mul_k D q y.toAdd⟩
  map_one' := Units.ext (k_zero D q)
  map_mul' y z := Units.ext (k_add D q y.toAdd z.toAdd)

@[simp]
theorem val_kUnitsHom (y : Y) :
    ((kUnitsHom D q (.ofAdd y) : (QuantizedEnvelopingAlgebra D q)ˣ) :
      QuantizedEnvelopingAlgebra D q) = k D q y := (rfl)

@[simp]
theorem val_inv_kUnitsHom (y : Y) :
    (((kUnitsHom D q (.ofAdd y))⁻¹ : (QuantizedEnvelopingAlgebra D q)ˣ) :
      QuantizedEnvelopingAlgebra D q) = k D q (-y) := (rfl)

/-- Every toral generator `K_y` is a unit in `QuantizedEnvelopingAlgebra D q`. -/
theorem isUnit_k (y : Y) : IsUnit (k D q y) :=
  ⟨kUnitsHom D q (.ofAdd y), rfl⟩

/-- Natural powers of `K_y` satisfy `(K_y)^n = K_(n • y)`. -/
@[simp]
theorem k_pow (y : Y) (n : ℕ) : k D q y ^ n = k D q (n • y) := by
  have h := congrArg Units.val ((kUnitsHom D q).map_pow (.ofAdd y) n)
  simpa only [Units.val_pow_eq_pow_val, val_kUnitsHom, ← ofAdd_nsmul] using h.symm

theorem simpleK_pow (i : ι) (n : ℕ) : simpleK D q i ^ n = k D q (n • D.simpleTorus i) := by
  rw [simpleK_def, k_pow]

theorem simpleKInv_pow (i : ι) (n : ℕ) :
    simpleKInv D q i ^ n = k D q (-(n • D.simpleTorus i)) := by
  rw [simpleKInv_def, k_pow, smul_neg]

/-! ### Toral conjugation and commutation -/

/-- `K_y Eᵢ K_(-y) = q^⟨αᵢ, y⟩ • Eᵢ`. -/
theorem k_mul_e_mul_k_neg (y : Y) (i : ι) :
    k D q y * e D q i * k D q (-y) = q ^ D.pairing (D.root i) y • e D q i := by
  simpa only [map_mul, map_smul, mkAlgHom_freeK, mkAlgHom_freeE] using
    mkAlgHom_eq_of_rel D q (Rel.conjugate_e y i)

/-- `K_y Fᵢ K_(-y) = q^(-⟨αᵢ, y⟩) • Fᵢ`. -/
theorem k_mul_f_mul_k_neg (y : Y) (i : ι) :
    k D q y * f D q i * k D q (-y) = q ^ (-D.pairing (D.root i) y) • f D q i := by
  simpa only [map_mul, map_smul, mkAlgHom_freeK, mkAlgHom_freeF] using
    mkAlgHom_eq_of_rel D q (Rel.conjugate_f y i)

/-- At `q = 0`, every raising generator `Eᵢ` vanishes: conjugating by `K_(hᵢ)` multiplies by
`0^2 = 0`. -/
@[simp]
theorem e_zero (i : ι) : e D (0 : K) i = 0 := by
  have h := k_mul_e_mul_k_neg D (0 : K) (D.coroot i) i
  rw [D.pairing_root_coroot_self, zpow_ofNat, zero_pow two_ne_zero, zero_smul] at h
  calc
    e D (0 : K) i =
        k D 0 (-D.coroot i) * (k D 0 (D.coroot i) * e D 0 i * k D 0 (-D.coroot i)) *
          k D 0 (D.coroot i) := by
      simp [mul_assoc]
    _ = 0 := by rw [h]; simp

/-- At `q = 0`, every lowering generator `Fᵢ` vanishes: conjugating by `K_(-hᵢ)` multiplies by
`0^2 = 0`. -/
@[simp]
theorem f_zero (i : ι) : f D (0 : K) i = 0 := by
  have h := k_mul_f_mul_k_neg D (0 : K) (-D.coroot i) i
  simp only [map_neg, D.pairing_root_coroot_self, neg_neg, zpow_ofNat, zero_pow two_ne_zero,
    zero_smul] at h
  calc
    f D (0 : K) i =
        k D 0 (D.coroot i) * (k D 0 (-D.coroot i) * f D 0 i * k D 0 (D.coroot i)) *
          k D 0 (-D.coroot i) := by
      simp [mul_assoc]
    _ = 0 := by rw [h]; simp

/-- `K_y Eᵢ = q^⟨αᵢ, y⟩ • (Eᵢ K_y)`. -/
theorem k_mul_e (y : Y) (i : ι) :
    k D q y * e D q i = q ^ D.pairing (D.root i) y • (e D q i * k D q y) := by
  calc
    k D q y * e D q i = (k D q y * e D q i * k D q (-y)) * k D q y := by simp [mul_assoc]
    _ = q ^ D.pairing (D.root i) y • (e D q i * k D q y) := by
      rw [k_mul_e_mul_k_neg, smul_mul_assoc]

/-- `K_y Fᵢ = q^(-⟨αᵢ, y⟩) • (Fᵢ K_y)`. -/
theorem k_mul_f (y : Y) (i : ι) :
    k D q y * f D q i = q ^ (-D.pairing (D.root i) y) • (f D q i * k D q y) := by
  calc
    k D q y * f D q i = (k D q y * f D q i * k D q (-y)) * k D q y := by simp [mul_assoc]
    _ = q ^ (-D.pairing (D.root i) y) • (f D q i * k D q y) := by
      rw [k_mul_f_mul_k_neg, smul_mul_assoc]

/-- `Eᵢ K_y = q^(-⟨αᵢ, y⟩) • (K_y Eᵢ)`. Holds unconditionally for every `q : K` (at `q = 0`,
`Eᵢ = 0`). -/
theorem e_mul_k (y : Y) (i : ι) :
    e D q i * k D q y = q ^ (-D.pairing (D.root i) y) • (k D q y * e D q i) := by
  rcases eq_or_ne q 0 with rfl | hq
  · simp
  · rw [k_mul_e, smul_smul, ← zpow_add₀ hq, neg_add_cancel, zpow_zero, one_smul]

/-- `Fᵢ K_y = q^⟨αᵢ, y⟩ • (K_y Fᵢ)`. Holds unconditionally for every `q : K` (at `q = 0`,
`Fᵢ = 0`). -/
theorem f_mul_k (y : Y) (i : ι) :
    f D q i * k D q y = q ^ D.pairing (D.root i) y • (k D q y * f D q i) := by
  rcases eq_or_ne q 0 with rfl | hq
  · simp
  · rw [k_mul_f, smul_smul, ← zpow_add₀ hq, add_neg_cancel, zpow_zero, one_smul]

/-- `Kᵢ Eⱼ = qᵢ^(aᵢⱼ) • (Eⱼ Kᵢ)`, where `qᵢ = q^(dᵢ)`. -/
theorem simpleK_mul_e (i j : ι) :
    simpleK D q i * e D q j =
      (q ^ D.symmetrizer i) ^ D.cartan i j • (e D q j * simpleK D q i) := by
  rw [simpleK_def, k_mul_e, D.pairing_root_simpleTorus, ← D.symmetrizer_mul_cartan, ← zpow_natCast,
    ← zpow_mul]

/-- `Kᵢ⁻¹ Eⱼ = qᵢ^(-aᵢⱼ) • (Eⱼ Kᵢ⁻¹)`, where `qᵢ = q^(dᵢ)`. -/
theorem simpleKInv_mul_e (i j : ι) :
    simpleKInv D q i * e D q j =
      (q ^ D.symmetrizer i) ^ (-D.cartan i j) • (e D q j * simpleKInv D q i) := by
  rw [simpleKInv_def, k_mul_e, map_neg, D.pairing_root_simpleTorus, ← D.symmetrizer_mul_cartan,
    ← mul_neg, ← zpow_natCast, ← zpow_mul]

/-- `Eⱼ Kᵢ = qᵢ^(-aᵢⱼ) • (Kᵢ Eⱼ)`. -/
theorem e_mul_simpleK (i j : ι) :
    e D q j * simpleK D q i =
      (q ^ D.symmetrizer i) ^ (-D.cartan i j) • (simpleK D q i * e D q j) := by
  rw [simpleK_def, e_mul_k, D.pairing_root_simpleTorus, ← D.symmetrizer_mul_cartan, ← mul_neg,
    ← zpow_natCast, ← zpow_mul]

/-- `Eⱼ Kᵢ⁻¹ = qᵢ^(aᵢⱼ) • (Kᵢ⁻¹ Eⱼ)`. -/
theorem e_mul_simpleKInv (i j : ι) :
    e D q j * simpleKInv D q i =
      (q ^ D.symmetrizer i) ^ D.cartan i j • (simpleKInv D q i * e D q j) := by
  rw [simpleKInv_def, e_mul_k, map_neg, neg_neg, D.pairing_root_simpleTorus,
    ← D.symmetrizer_mul_cartan, ← zpow_natCast, ← zpow_mul]

/-- `Kᵢ Fⱼ = qᵢ^(-aᵢⱼ) • (Fⱼ Kᵢ)`. -/
theorem simpleK_mul_f (i j : ι) :
    simpleK D q i * f D q j =
      (q ^ D.symmetrizer i) ^ (-D.cartan i j) • (f D q j * simpleK D q i) := by
  rw [simpleK_def, k_mul_f, D.pairing_root_simpleTorus, ← D.symmetrizer_mul_cartan, ← mul_neg,
    ← zpow_natCast, ← zpow_mul]

/-- `Kᵢ⁻¹ Fⱼ = qᵢ^(aᵢⱼ) • (Fⱼ Kᵢ⁻¹)`. -/
theorem simpleKInv_mul_f (i j : ι) :
    simpleKInv D q i * f D q j =
      (q ^ D.symmetrizer i) ^ D.cartan i j • (f D q j * simpleKInv D q i) := by
  rw [simpleKInv_def, k_mul_f, map_neg, neg_neg, D.pairing_root_simpleTorus,
    ← D.symmetrizer_mul_cartan, ← zpow_natCast, ← zpow_mul]

/-- `Fⱼ Kᵢ = qᵢ^(aᵢⱼ) • (Kᵢ Fⱼ)`. -/
theorem f_mul_simpleK (i j : ι) :
    f D q j * simpleK D q i =
      (q ^ D.symmetrizer i) ^ D.cartan i j • (simpleK D q i * f D q j) := by
  rw [simpleK_def, f_mul_k, D.pairing_root_simpleTorus, ← D.symmetrizer_mul_cartan,
    ← zpow_natCast, ← zpow_mul]

/-- `Fⱼ Kᵢ⁻¹ = qᵢ^(-aᵢⱼ) • (Kᵢ⁻¹ Fⱼ)`. -/
theorem f_mul_simpleKInv (i j : ι) :
    f D q j * simpleKInv D q i =
      (q ^ D.symmetrizer i) ^ (-D.cartan i j) • (simpleKInv D q i * f D q j) := by
  rw [simpleKInv_def, f_mul_k, map_neg, D.pairing_root_simpleTorus, ← D.symmetrizer_mul_cartan,
    ← mul_neg, ← zpow_natCast, ← zpow_mul]

/-- Commuting `K_y` past a quantum divided power of `Eᵢ`. -/
theorem k_mul_quantumDividedPower_e (q' : K) (y : Y) (i : ι) (n : ℕ) :
    k D q y * quantumDividedPower q' (e D q i) n =
      (q ^ D.pairing (D.root i) y) ^ n • (quantumDividedPower q' (e D q i) n * k D q y) :=
  mul_quantumDividedPower_of_mul_eq_smul_mul q' (k_mul_e D q y i) n

/-- Commuting `K_y` past a quantum divided power of `Fᵢ`. -/
theorem k_mul_quantumDividedPower_f (q' : K) (y : Y) (i : ι) (n : ℕ) :
    k D q y * quantumDividedPower q' (f D q i) n =
      (q ^ (-D.pairing (D.root i) y)) ^ n • (quantumDividedPower q' (f D q i) n * k D q y) :=
  mul_quantumDividedPower_of_mul_eq_smul_mul q' (k_mul_f D q y i) n

/-- All simple toral generators `Kᵢ` and `Kⱼ` commute. -/
theorem commute_simpleK_simpleK (i j : ι) : Commute (simpleK D q i) (simpleK D q j) :=
  commute_k_k D q (D.simpleTorus i) (D.simpleTorus j)

/-- Every `Kᵢ` commutes with every `Kⱼ⁻¹`. -/
theorem commute_simpleK_simpleKInv (i j : ι) : Commute (simpleK D q i) (simpleKInv D q j) :=
  commute_k_k D q (D.simpleTorus i) (-D.simpleTorus j)

/-- All inverse simple toral generators `Kᵢ⁻¹` and `Kⱼ⁻¹` commute. -/
theorem commute_simpleKInv_simpleKInv (i j : ι) :
    Commute (simpleKInv D q i) (simpleKInv D q j) :=
  commute_k_k D q (-D.simpleTorus i) (-D.simpleTorus j)

/-- `Kᵢ^n Eⱼ = qᵢ^(n aᵢⱼ) • (Eⱼ Kᵢ^n)`. -/
theorem simpleK_pow_mul_e (i j : ι) (n : ℕ) :
    simpleK D q i ^ n * e D q j =
      (q ^ D.symmetrizer i) ^ ((n : ℤ) * D.cartan i j) • (e D q j * simpleK D q i ^ n) := by
  rw [simpleK_pow, k_mul_e, map_nsmul, nsmul_eq_mul, D.pairing_root_simpleTorus,
    ← D.symmetrizer_mul_cartan, ← mul_assoc, mul_comm (n : ℤ), mul_assoc, zpow_mul, zpow_natCast]

/-- `Eⱼ Kᵢ⁻¹^n = qᵢ^(n aᵢⱼ) • (Kᵢ⁻¹^n Eⱼ)`. -/
theorem e_mul_simpleKInv_pow (i j : ι) (n : ℕ) :
    e D q j * simpleKInv D q i ^ n =
      (q ^ D.symmetrizer i) ^ ((n : ℤ) * D.cartan i j) •
        (simpleKInv D q i ^ n * e D q j) := by
  rw [simpleKInv_pow, e_mul_k, map_neg, map_nsmul, neg_neg, nsmul_eq_mul,
    D.pairing_root_simpleTorus, ← D.symmetrizer_mul_cartan, ← mul_assoc, mul_comm (n : ℤ),
    mul_assoc, zpow_mul, zpow_natCast]

/-- `Kᵢ^n Eⱼ^(m) = qᵢ^(n m aᵢⱼ) • (Eⱼ^(m) Kᵢ^n)`. -/
theorem simpleK_pow_mul_quantumDividedPower_e (q' : K) (i j : ι) (n m : ℕ) :
    simpleK D q i ^ n * quantumDividedPower q' (e D q j) m =
      (q ^ D.symmetrizer i) ^ ((n : ℤ) * (m : ℤ) * D.cartan i j) •
        (quantumDividedPower q' (e D q j) m * simpleK D q i ^ n) := by
  rw [mul_quantumDividedPower_of_mul_eq_smul_mul q' (simpleK_pow_mul_e D q i j n) m,
    ← zpow_natCast _ m, ← zpow_mul, mul_assoc (n : ℤ), mul_comm (D.cartan i j) (m : ℤ),
    ← mul_assoc]

/-- `Eⱼ^(m) Kᵢ⁻¹^n = qᵢ^(m n aᵢⱼ) • (Kᵢ⁻¹^n Eⱼ^(m))`. -/
theorem quantumDividedPower_e_mul_simpleKInv_pow (q' : K) (i j : ι) (m n : ℕ) :
    quantumDividedPower q' (e D q j) m * simpleKInv D q i ^ n =
      (q ^ D.symmetrizer i) ^ ((m : ℤ) * (n : ℤ) * D.cartan i j) •
        (simpleKInv D q i ^ n * quantumDividedPower q' (e D q j) m) := by
  rw [quantumDividedPower_mul_of_mul_eq_smul_mul q' (e_mul_simpleKInv_pow D q i j n) m,
    ← zpow_natCast _ m, ← zpow_mul, mul_comm ((n : ℤ) * D.cartan i j), ← mul_assoc]

/-! ### Commutator and quantum Serre relations -/

/-- The diagonal commutator relation `Eᵢ Fᵢ - Fᵢ Eᵢ = (Kᵢ - Kᵢ⁻¹) / (qᵢ - qᵢ⁻¹)`. -/
theorem e_mul_f_sub_f_mul_e_self (i : ι) :
    e D q i * f D q i - f D q i * e D q i =
      (q ^ D.symmetrizer i - (q ^ D.symmetrizer i)⁻¹)⁻¹ •
        (simpleK D q i - simpleKInv D q i) := by
  simpa only [map_sub, map_mul, map_smul, mkAlgHom_freeE, mkAlgHom_freeF, mkAlgHom_freeK,
    simpleK_def, simpleKInv_def] using mkAlgHom_eq_of_rel D q (Rel.commutator_self i)

/-- The off-diagonal commutator relation `Eᵢ Fⱼ - Fⱼ Eᵢ = 0` for `i ≠ j`. -/
theorem e_mul_f_sub_f_mul_e_of_ne {i j : ι} (hij : i ≠ j) :
    e D q i * f D q j - f D q j * e D q i = 0 := by
  simpa only [map_sub, map_mul, map_zero, mkAlgHom_freeE, mkAlgHom_freeF] using
    mkAlgHom_eq_of_rel D q (Rel.commutator_ne hij)

/-- `Eᵢ` and `Fⱼ` commute for `i ≠ j`. -/
theorem commute_e_f {i j : ι} (hij : i ≠ j) : Commute (e D q i) (f D q j) :=
  sub_eq_zero.mp (e_mul_f_sub_f_mul_e_of_ne D q hij)

/-- Combined `Eᵢ`--`Fⱼ` commutator formula under `DecidableEq ι`. -/
theorem e_mul_f_sub_f_mul_e [DecidableEq ι] (i j : ι) :
    e D q i * f D q j - f D q j * e D q i =
      if i = j then
        (q ^ D.symmetrizer i - (q ^ D.symmetrizer i)⁻¹)⁻¹ •
          (simpleK D q i - simpleKInv D q i)
      else 0 := by
  split_ifs with hij
  · subst hij
    exact e_mul_f_sub_f_mul_e_self D q i
  · exact e_mul_f_sub_f_mul_e_of_ne D q hij

/-- The positive quantum Serre relation in `QuantizedEnvelopingAlgebra D q` for `i ≠ j`. -/
theorem serreE_eq_zero {i j : ι} (hij : i ≠ j) :
    serreSum D q (e D q) i j = 0 := by
  simpa only [freeSerreE_def, map_serreSum, mkAlgHom_freeE, map_zero] using
    mkAlgHom_eq_of_rel D q (Rel.serre_e hij)

/-- The negative quantum Serre relation in `QuantizedEnvelopingAlgebra D q` for `i ≠ j`. -/
theorem serreF_eq_zero {i j : ι} (hij : i ≠ j) :
    serreSum D q (f D q) i j = 0 := by
  simpa only [freeSerreF_def, map_serreSum, mkAlgHom_freeF, map_zero] using
    mkAlgHom_eq_of_rel D q (Rel.serre_f hij)

/-- When `i ≠ j`, `aᵢⱼ = 0`, and `qᵢ - qᵢ⁻¹ ≠ 0`, the Serre relation has length `1` and reduces
to `Eᵢ Eⱼ = Eⱼ Eᵢ`. -/
theorem commute_e_e_of_cartan_eq_zero {i j : ι} (hij : i ≠ j) (hcartan : D.cartan i j = 0)
    (hq : q ^ D.symmetrizer i - (q ^ D.symmetrizer i)⁻¹ ≠ 0) :
    Commute (e D q i) (e D q j) := by
  have hserre := serreE_eq_zero D q hij
  rw [serreSum_def, D.serreLength_of_cartan_eq_zero hcartan, sum_range_succ,
    sum_range_one] at hserre
  simp only [pow_zero, pow_one, one_smul, neg_one_smul, Nat.sub_zero, Nat.sub_self,
    quantumDividedPower_zero, quantumDividedPower_one hq, one_mul, mul_one,
    ← sub_eq_add_neg] at hserre
  exact (sub_eq_zero.mp hserre).symm

/-- When `i ≠ j`, `aᵢⱼ = 0`, and `qᵢ - qᵢ⁻¹ ≠ 0`, the Serre relation has length `1` and reduces
to `Fᵢ Fⱼ = Fⱼ Fᵢ`. -/
theorem commute_f_f_of_cartan_eq_zero {i j : ι} (hij : i ≠ j) (hcartan : D.cartan i j = 0)
    (hq : q ^ D.symmetrizer i - (q ^ D.symmetrizer i)⁻¹ ≠ 0) :
    Commute (f D q i) (f D q j) := by
  have hserre := serreF_eq_zero D q hij
  rw [serreSum_def, D.serreLength_of_cartan_eq_zero hcartan, sum_range_succ,
    sum_range_one] at hserre
  simp only [pow_zero, pow_one, one_smul, neg_one_smul, Nat.sub_zero, Nat.sub_self,
    quantumDividedPower_zero, quantumDividedPower_one hq, one_mul, mul_one,
    ← sub_eq_add_neg] at hserre
  exact (sub_eq_zero.mp hserre).symm

/-! ### Universal property and generator induction -/

/-- A tuple of elements `(e, f, k)` in a `K`-algebra `A` satisfying the defining relations of
`QuantizedEnvelopingAlgebra D q`. Extensional on `(e, f, k)`. -/
@[ext]
structure GeneratorTuple (A : Type*) [Ring A] [Algebra K A] where
  /-- Proposed images of the raising generators `Eᵢ`. -/
  e : ι → A
  /-- Proposed images of the lowering generators `Fᵢ`. -/
  f : ι → A
  /-- Proposed images of the toral generators `K_y`. -/
  k : Y → A
  /-- `k 0 = 1`. -/
  k_zero : k 0 = 1
  /-- `k y * k z = k (y + z)`. -/
  k_mul_k : ∀ y z : Y, k y * k z = k (y + z)
  /-- `k y * e i * k (-y) = q^⟨αᵢ, y⟩ • e i`. -/
  conjugate_e : ∀ (y : Y) (i : ι), k y * e i * k (-y) = q ^ D.pairing (D.root i) y • e i
  /-- `k y * f i * k (-y) = q^(-⟨αᵢ, y⟩) • f i`. -/
  conjugate_f : ∀ (y : Y) (i : ι), k y * f i * k (-y) = q ^ (-D.pairing (D.root i) y) • f i
  /-- `e i * f i - f i * e i = (k (dᵢ hᵢ) - k (-dᵢ hᵢ)) / (qᵢ - qᵢ⁻¹)`. -/
  commutator_self : ∀ i : ι,
    e i * f i - f i * e i =
      (q ^ D.symmetrizer i - (q ^ D.symmetrizer i)⁻¹)⁻¹ •
        (k (D.simpleTorus i) - k (-D.simpleTorus i))
  /-- `e i * f j - f j * e i = 0` for `i ≠ j`. -/
  commutator_ne : ∀ {i j : ι}, i ≠ j → e i * f j - f j * e i = 0
  /-- Positive quantum Serre relation for `i ≠ j`. -/
  serre_e : ∀ {i j : ι}, i ≠ j → serreSum D q e i j = 0
  /-- Negative quantum Serre relation for `i ≠ j`. -/
  serre_f : ∀ {i j : ι}, i ≠ j → serreSum D q f i j = 0

namespace GeneratorTuple

variable {D q} {A : Type*} [Ring A] [Algebra K A]

/-- The function `Generator ι Y → A` underlying a `GeneratorTuple`. -/
def toFun (T : GeneratorTuple D q A) : Generator ι Y → A
  | .e i => T.e i
  | .f i => T.f i
  | .k y => T.k y

@[simp]
theorem toFun_e (T : GeneratorTuple D q A) (i : ι) : T.toFun (.e i) = T.e i := (rfl)

@[simp]
theorem toFun_f (T : GeneratorTuple D q A) (i : ι) : T.toFun (.f i) = T.f i := (rfl)

@[simp]
theorem toFun_k (T : GeneratorTuple D q A) (y : Y) : T.toFun (.k y) = T.k y := (rfl)

end GeneratorTuple

section Lift

variable {D q} {A : Type*} [Ring A] [Algebra K A]

/-- **Universal property of `QuantizedEnvelopingAlgebra`**: a `GeneratorTuple` in a `K`-algebra `A`
extends uniquely to a `K`-algebra homomorphism `QuantizedEnvelopingAlgebra D q →ₐ[K] A`. -/
noncomputable def lift (T : GeneratorTuple D q A) : QuantizedEnvelopingAlgebra D q →ₐ[K] A :=
  RingQuot.liftAlgHom K ⟨FreeAlgebra.lift K T.toFun, by
    intro a b h
    cases h with
    | k_zero =>
      simpa only [freeK_def, map_one, FreeAlgebra.lift_ι_apply, GeneratorTuple.toFun_k] using
        T.k_zero
    | k_mul_k y z =>
      simpa only [freeK_def, map_mul, FreeAlgebra.lift_ι_apply, GeneratorTuple.toFun_k] using
        T.k_mul_k y z
    | conjugate_e y i =>
      simpa only [freeK_def, freeE_def, map_mul, map_smul, FreeAlgebra.lift_ι_apply,
        GeneratorTuple.toFun_k, GeneratorTuple.toFun_e] using T.conjugate_e y i
    | conjugate_f y i =>
      simpa only [freeK_def, freeF_def, map_mul, map_smul, FreeAlgebra.lift_ι_apply,
        GeneratorTuple.toFun_k, GeneratorTuple.toFun_f] using T.conjugate_f y i
    | commutator_self i =>
      simpa only [freeE_def, freeF_def, freeK_def, map_sub, map_mul, map_smul,
        FreeAlgebra.lift_ι_apply, GeneratorTuple.toFun_e, GeneratorTuple.toFun_f,
        GeneratorTuple.toFun_k] using T.commutator_self i
    | commutator_ne hij =>
      simpa only [freeE_def, freeF_def, map_sub, map_mul, map_zero, FreeAlgebra.lift_ι_apply,
        GeneratorTuple.toFun_e, GeneratorTuple.toFun_f] using T.commutator_ne hij
    | serre_e hij =>
      simpa only [freeSerreE_def, map_serreSum, freeE_def, FreeAlgebra.lift_ι_apply,
        GeneratorTuple.toFun_e, map_zero] using T.serre_e hij
    | serre_f hij =>
      simpa only [freeSerreF_def, map_serreSum, freeF_def, FreeAlgebra.lift_ι_apply,
        GeneratorTuple.toFun_f, map_zero] using T.serre_f hij⟩

@[simp]
theorem lift_generator (T : GeneratorTuple D q A) (g : Generator ι Y) :
    lift T (generator D q g) = T.toFun g :=
  (RingQuot.liftAlgHom_mkAlgHom_apply K _ _ _).trans (FreeAlgebra.lift_ι_apply _ _)

@[simp]
theorem lift_e (T : GeneratorTuple D q A) (i : ι) : lift T (e D q i) = T.e i :=
  lift_generator T (.e i)

@[simp]
theorem lift_f (T : GeneratorTuple D q A) (i : ι) : lift T (f D q i) = T.f i :=
  lift_generator T (.f i)

@[simp]
theorem lift_k (T : GeneratorTuple D q A) (y : Y) : lift T (k D q y) = T.k y :=
  lift_generator T (.k y)

@[simp]
theorem lift_simpleK (T : GeneratorTuple D q A) (i : ι) :
    lift T (simpleK D q i) = T.k (D.simpleTorus i) :=
  lift_k T (D.simpleTorus i)

@[simp]
theorem lift_simpleKInv (T : GeneratorTuple D q A) (i : ι) :
    lift T (simpleKInv D q i) = T.k (-D.simpleTorus i) :=
  lift_k T (-D.simpleTorus i)

/-- Two `K`-algebra homomorphisms out of `QuantizedEnvelopingAlgebra D q` that agree on `e`, `f`,
and `k` are equal. -/
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

/-- Equivalence between `K`-algebra maps `QuantizedEnvelopingAlgebra D q →ₐ[K] A` and
`GeneratorTuple D q A`. -/
noncomputable def liftEquiv :
    (QuantizedEnvelopingAlgebra D q →ₐ[K] A) ≃ GeneratorTuple D q A where
  toFun φ :=
    { e := fun i => φ (e D q i)
      f := fun i => φ (f D q i)
      k := fun y => φ (k D q y)
      k_zero := by rw [← map_one φ, ← k_zero D q]
      k_mul_k := fun y z => by rw [← map_mul, k_mul_k]
      conjugate_e := fun y i => by
        simpa only [map_mul, map_smul] using congrArg φ (k_mul_e_mul_k_neg D q y i)
      conjugate_f := fun y i => by
        simpa only [map_mul, map_smul] using congrArg φ (k_mul_f_mul_k_neg D q y i)
      commutator_self := fun i => by
        simpa only [map_sub, map_mul, map_smul, simpleK_def, simpleKInv_def] using
          congrArg φ (e_mul_f_sub_f_mul_e_self D q i)
      commutator_ne := fun hij => by
        simpa only [map_sub, map_mul, map_zero] using congrArg φ (e_mul_f_sub_f_mul_e_of_ne D q hij)
      serre_e := fun hij => by
        simpa only [map_serreSum, map_zero] using congrArg φ (serreE_eq_zero D q hij)
      serre_f := fun hij => by
        simpa only [map_serreSum, map_zero] using congrArg φ (serreF_eq_zero D q hij) }
  invFun := lift
  left_inv φ := hom_ext (fun _ => lift_e _ _) (fun _ => lift_f _ _) (fun _ => lift_k _ _)
  right_inv T := by ext <;> simp

@[simp]
theorem liftEquiv_apply_e (φ : QuantizedEnvelopingAlgebra D q →ₐ[K] A) (i : ι) :
    (liftEquiv φ).e i = φ (e D q i) := (rfl)

@[simp]
theorem liftEquiv_apply_f (φ : QuantizedEnvelopingAlgebra D q →ₐ[K] A) (i : ι) :
    (liftEquiv φ).f i = φ (f D q i) := (rfl)

@[simp]
theorem liftEquiv_apply_k (φ : QuantizedEnvelopingAlgebra D q →ₐ[K] A) (y : Y) :
    (liftEquiv φ).k y = φ (k D q y) := (rfl)

@[simp]
theorem liftEquiv_symm_apply (T : GeneratorTuple D q A) : liftEquiv.symm T = lift T := (rfl)

end Lift

/-- The generators `Generator ι Y` generate `QuantizedEnvelopingAlgebra D q` as a `K`-algebra. -/
theorem adjoin_range_generator :
    Algebra.adjoin K (Set.range (generator D q)) = ⊤ := by
  rw [Algebra.adjoin_range_eq_range_freeAlgebra_lift]
  have h : FreeAlgebra.lift K (generator D q) = mkAlgHom D q := by
    apply FreeAlgebra.hom_ext
    funext g
    simp
  rw [h, AlgHom.range_eq_top]
  exact mkAlgHom_surjective D q

/-- Induction principle on `QuantizedEnvelopingAlgebra D q`: a predicate holding on scalars and on
all generators `e i`, `f i`, `k y`, and closed under addition and multiplication, holds everywhere.
-/
@[elab_as_elim]
theorem induction {P : QuantizedEnvelopingAlgebra D q → Prop}
    (algebraMap' : ∀ c : K, P (algebraMap K (QuantizedEnvelopingAlgebra D q) c))
    (e : ∀ i : ι, P (QuantizedEnvelopingAlgebra.e D q i))
    (f : ∀ i : ι, P (QuantizedEnvelopingAlgebra.f D q i))
    (k : ∀ y : Y, P (QuantizedEnvelopingAlgebra.k D q y))
    (add : ∀ a b, P a → P b → P (a + b))
    (mul : ∀ a b, P a → P b → P (a * b))
    (u : QuantizedEnvelopingAlgebra D q) : P u := by
  have hu : u ∈ Algebra.adjoin K (Set.range (generator D q)) := by
    rw [adjoin_range_generator]
    exact Algebra.mem_top
  induction hu using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨g, rfl⟩ := hx
    cases g with
    | e i => exact e i
    | f i => exact f i
    | k y => exact k y
  | algebraMap c => exact algebraMap' c
  | add a b _ _ ha hb => exact add a b ha hb
  | mul a b _ _ ha hb => exact mul a b ha hb

/-- An element commuting with all generators `e i`, `f i`, and `k y` commutes with every element of
`QuantizedEnvelopingAlgebra D q`. -/
theorem commute_of_commute_generators {z : QuantizedEnvelopingAlgebra D q}
    (he : ∀ i, Commute (e D q i) z)
    (hf : ∀ i, Commute (f D q i) z)
    (hk : ∀ y, Commute (k D q y) z)
    (u : QuantizedEnvelopingAlgebra D q) : Commute u z := by
  refine (Algebra.commute_of_mem_adjoin_of_forall_mem_commute (R := K)
    (s := Set.range (generator D q)) ?_ ?_).symm
  · rw [adjoin_range_generator]
    exact Algebra.mem_top
  · rintro _ ⟨g, rfl⟩
    cases g with
    | e i => exact (he i).symm
    | f i => exact (hf i).symm
    | k y => exact (hk y).symm

/-- For a root-annihilating coweight `c ∈ Y` (`⟨αᵢ, c⟩ = 0` for all `i`), `K_c` commutes with every
element of `QuantizedEnvelopingAlgebra D q`. -/
theorem commute_k_of_pairing_root_eq_zero {c : Y}
    (hc : ∀ i, D.pairing (D.root i) c = 0) (u : QuantizedEnvelopingAlgebra D q) :
    Commute u (k D q c) := by
  refine commute_of_commute_generators D q (fun i => ?_) (fun i => ?_)
    (fun y => commute_k_k D q y c) u
  · rw [Commute, SemiconjBy, e_mul_k, hc i, neg_zero, zpow_zero, one_smul]
  · rw [Commute, SemiconjBy, f_mul_k, hc i, zpow_zero, one_smul]

/-- For a root-annihilating coweight `c ∈ Y` (`⟨αᵢ, c⟩ = 0` for all `i`), `K_c` belongs to the
center of `QuantizedEnvelopingAlgebra D q`. -/
theorem k_mem_center_of_pairing_root_eq_zero {c : Y}
    (hc : ∀ i, D.pairing (D.root i) c = 0) :
    k D q c ∈ Subalgebra.center K (QuantizedEnvelopingAlgebra D q) := by
  rw [Subalgebra.mem_center_iff]
  exact commute_k_of_pairing_root_eq_zero D q hc

/-! ### Diagonal rescaling, Chevalley involution, and datum functoriality -/

/-- The generator tuple scaling `Eᵢ` by `cᵢ` and `Fᵢ` by `cᵢ⁻¹` while fixing `K_y`. -/
private noncomputable def rescaleTuple (c : ι → Kˣ) :
    GeneratorTuple D q (QuantizedEnvelopingAlgebra D q) where
  e i := (c i : K) • e D q i
  f i := (c i : K)⁻¹ • f D q i
  k y := k D q y
  k_zero := k_zero D q
  k_mul_k := k_mul_k D q
  conjugate_e y i := by
    rw [mul_smul_comm, smul_mul_assoc, k_mul_e_mul_k_neg, smul_comm]
  conjugate_f y i := by
    rw [mul_smul_comm, smul_mul_assoc, k_mul_f_mul_k_neg, smul_comm]
  commutator_self i := by
    rw [smul_mul_smul_comm, smul_mul_smul_comm, mul_inv_cancel₀ (c i).ne_zero,
      inv_mul_cancel₀ (c i).ne_zero, one_smul, one_smul, e_mul_f_sub_f_mul_e_self,
      simpleK_def, simpleKInv_def]
  commutator_ne {i j} hij := by
    rw [smul_mul_smul_comm, smul_mul_smul_comm, mul_comm ((c j : K)⁻¹) (c i : K), ← smul_sub,
      e_mul_f_sub_f_mul_e_of_ne D q hij, smul_zero]
  serre_e {i j} hij := by
    rw [serreSum_smul, serreE_eq_zero D q hij, smul_zero]
  serre_f {i j} hij := by
    rw [serreSum_smul, serreF_eq_zero D q hij, smul_zero]

/-- Diagonal rescaling automorphism of `QuantizedEnvelopingAlgebra D q`: for units `c : ι → Kˣ`,
sends `Eᵢ ↦ cᵢ • Eᵢ`, `Fᵢ ↦ cᵢ⁻¹ • Fᵢ`, and `K_y ↦ K_y`. -/
noncomputable def rescale (c : ι → Kˣ) :
    QuantizedEnvelopingAlgebra D q ≃ₐ[K] QuantizedEnvelopingAlgebra D q :=
  AlgEquiv.ofAlgHom (lift (rescaleTuple D q c)) (lift (rescaleTuple D q fun i => (c i)⁻¹))
    (by
      ext i
      · simp [rescaleTuple, smul_smul, (c i).ne_zero]
      · simp [rescaleTuple, smul_smul, (c i).ne_zero]
      · simp [rescaleTuple])
    (by
      ext i
      · simp [rescaleTuple, smul_smul, (c i).ne_zero]
      · simp [rescaleTuple, smul_smul, (c i).ne_zero]
      · simp [rescaleTuple])

@[simp]
theorem rescale_e (c : ι → Kˣ) (i : ι) :
    rescale D q c (e D q i) = (c i : K) • e D q i :=
  lift_e (rescaleTuple D q c) i

@[simp]
theorem rescale_f (c : ι → Kˣ) (i : ι) :
    rescale D q c (f D q i) = (c i : K)⁻¹ • f D q i :=
  lift_f (rescaleTuple D q c) i

@[simp]
theorem rescale_k (c : ι → Kˣ) (y : Y) :
    rescale D q c (k D q y) = k D q y :=
  lift_k (rescaleTuple D q c) y

@[simp]
theorem rescale_symm (c : ι → Kˣ) :
    (rescale D q c).symm = rescale D q (fun i => (c i)⁻¹) := by
  ext x
  rfl

/-- The generator tuple for the Chevalley involution `Eᵢ ↦ Fᵢ`, `Fᵢ ↦ Eᵢ`, `K_y ↦ K_(-y)`. -/
private noncomputable def chevalleyTuple :
    GeneratorTuple D q (QuantizedEnvelopingAlgebra D q) where
  e i := f D q i
  f i := e D q i
  k y := k D q (-y)
  k_zero := by simp
  k_mul_k y z := by rw [k_mul_k, neg_add_rev, add_comm]
  conjugate_e y i := by
    simpa only [map_neg, neg_neg] using k_mul_f_mul_k_neg D q (-y) i
  conjugate_f y i := by
    simpa only [map_neg] using k_mul_e_mul_k_neg D q (-y) i
  commutator_self i := by
    have h := congrArg Neg.neg (e_mul_f_sub_f_mul_e_self D q i)
    simpa only [neg_sub, ← smul_neg, simpleK_def, simpleKInv_def, neg_neg] using h
  commutator_ne {i j} hij := by
    have h := congrArg Neg.neg (e_mul_f_sub_f_mul_e_of_ne D q hij.symm)
    simpa only [neg_sub, neg_zero] using h
  serre_e {i j} hij := serreF_eq_zero D q hij
  serre_f {i j} hij := serreE_eq_zero D q hij

/-- The Chevalley `K`-algebra involution `ω` of `QuantizedEnvelopingAlgebra D q`, swapping
`Eᵢ ↔ Fᵢ` and sending `K_y ↦ K_(-y)`. -/
noncomputable def chevalleyInvolution :
    QuantizedEnvelopingAlgebra D q ≃ₐ[K] QuantizedEnvelopingAlgebra D q :=
  AlgEquiv.ofAlgHom (lift (chevalleyTuple D q)) (lift (chevalleyTuple D q))
    (by
      ext i
      · simp [chevalleyTuple]
      · simp [chevalleyTuple]
      · simp [chevalleyTuple])
    (by
      ext i
      · simp [chevalleyTuple]
      · simp [chevalleyTuple]
      · simp [chevalleyTuple])

@[simp]
theorem chevalleyInvolution_e (i : ι) :
    chevalleyInvolution D q (e D q i) = f D q i :=
  lift_e (chevalleyTuple D q) i

@[simp]
theorem chevalleyInvolution_f (i : ι) :
    chevalleyInvolution D q (f D q i) = e D q i :=
  lift_f (chevalleyTuple D q) i

@[simp]
theorem chevalleyInvolution_k (y : Y) :
    chevalleyInvolution D q (k D q y) = k D q (-y) :=
  lift_k (chevalleyTuple D q) y

@[simp]
theorem chevalleyInvolution_symm :
    (chevalleyInvolution D q).symm = chevalleyInvolution D q := by
  ext x
  rfl

@[simp]
theorem chevalleyInvolution_chevalleyInvolution (u : QuantizedEnvelopingAlgebra D q) :
    chevalleyInvolution D q (chevalleyInvolution D q u) = u :=
  (chevalleyInvolution D q).symm_apply_apply u

end Presentation

section Functoriality

variable {ι X Y X' Y' X'' Y'' K : Type*}
  [AddCommGroup X] [AddCommGroup Y] [AddCommGroup X'] [AddCommGroup Y']
  [AddCommGroup X''] [AddCommGroup Y''] [Field K]
  {D : CartanDatum ι X Y} {D' : CartanDatum ι X' Y'} {D'' : CartanDatum ι X'' Y''}

/-- A morphism of Cartan data `φ : CartanDatum.Hom D D'` induces a `K`-algebra homomorphism
`QuantizedEnvelopingAlgebra D q →ₐ[K] QuantizedEnvelopingAlgebra D' q` sending `Eᵢ ↦ Eᵢ`,
`Fᵢ ↦ Fᵢ`, and `K_y ↦ K_(φ y)`. -/
noncomputable def map (φ : CartanDatum.Hom D D') (q : K) :
    QuantizedEnvelopingAlgebra D q →ₐ[K] QuantizedEnvelopingAlgebra D' q :=
  lift
    { e := e D' q
      f := f D' q
      k := fun y => k D' q (φ.toLinearMap y)
      k_zero := by simp
      k_mul_k := fun y z => by rw [k_mul_k, map_add]
      conjugate_e := fun y i => by
        rw [map_neg, k_mul_e_mul_k_neg, φ.pairing_root_map]
      conjugate_f := fun y i => by
        rw [map_neg, k_mul_f_mul_k_neg, φ.pairing_root_map]
      commutator_self := fun i => by
        rw [e_mul_f_sub_f_mul_e_self, φ.symmetrizer_eq, map_neg, φ.map_simpleTorus,
          simpleK_def, simpleKInv_def]
      commutator_ne := fun hij => e_mul_f_sub_f_mul_e_of_ne D' q hij
      serre_e := fun {i j} hij => by
        have hlen := φ.serreLength_eq i j
        have hsym := φ.symmetrizer_eq
        simpa only [serreSum_def, hlen, hsym] using serreE_eq_zero D' q hij
      serre_f := fun {i j} hij => by
        have hlen := φ.serreLength_eq i j
        have hsym := φ.symmetrizer_eq
        simpa only [serreSum_def, hlen, hsym] using serreF_eq_zero D' q hij }

@[simp]
theorem map_e (φ : CartanDatum.Hom D D') (q : K) (i : ι) :
    map φ q (e D q i) = e D' q i :=
  lift_e _ i

@[simp]
theorem map_f (φ : CartanDatum.Hom D D') (q : K) (i : ι) :
    map φ q (f D q i) = f D' q i :=
  lift_f _ i

@[simp]
theorem map_k (φ : CartanDatum.Hom D D') (q : K) (y : Y) :
    map φ q (k D q y) = k D' q (φ.toLinearMap y) :=
  lift_k _ y

@[simp]
theorem map_simpleK (φ : CartanDatum.Hom D D') (q : K) (i : ι) :
    map φ q (simpleK D q i) = simpleK D' q i := by
  rw [simpleK_def, map_k, φ.map_simpleTorus, ← simpleK_def]

@[simp]
theorem map_simpleKInv (φ : CartanDatum.Hom D D') (q : K) (i : ι) :
    map φ q (simpleKInv D q i) = simpleKInv D' q i := by
  rw [simpleKInv_def, map_k, map_neg, φ.map_simpleTorus, ← simpleKInv_def]

@[simp]
theorem map_id (D : CartanDatum ι X Y) (q : K) :
    map (CartanDatum.Hom.id D) q = AlgHom.id K (QuantizedEnvelopingAlgebra D q) := by
  ext <;> simp

theorem map_comp (ψ : CartanDatum.Hom D' D'') (φ : CartanDatum.Hom D D') (q : K) :
    map (ψ.comp φ) q = (map ψ q).comp (map φ q) := by
  ext <;> simp

end Functoriality

end QuantizedEnvelopingAlgebra

end TauCeti
