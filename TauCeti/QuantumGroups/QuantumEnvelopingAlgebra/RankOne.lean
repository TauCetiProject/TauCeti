/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Bialgebra.Equiv
public import TauCeti.LinearAlgebra.Matrix.Cartan.Datum.Constructions
public import TauCeti.QuantumGroups.QuantumEnvelopingAlgebra.Hopf
public import TauCeti.QuantumGroups.UqSl2.Hopf

import TauCeti.QuantumGroups.UqSl2.Commutator
import TauCeti.QuantumGroups.UqSl2.Rescale

/-!
# Rank-one root embeddings and comparison with `UqSl2`

Every simple root `i` of a symmetrizable Cartan datum `D` determines a canonical `sl₂`-subalgebra
homomorphism `fromUqSl2 D q i : UqSl2 (q ^ D.symmetrizer i) →ₐ[ℂ] QuantumEnvelopingAlgebra D q`,
defined unconditionally for every complex parameter `q`, which upgrades to a bialgebra (hence Hopf
algebra) homomorphism `fromUqSl2BialgHom` whenever the source and target bialgebra structures are
defined (`q ^ dᵢ ≠ 0` and `IsSerreRegular D q`).

When `ι` has a unique index `i₀` and the simple toral element `D.simpleTorus i₀ = d_{i₀} h_{i₀}`
generates the coweight lattice `Y` over `ℤ`, this map is an isomorphism of algebras for every
`q : ℂ` (`uqSl2AlgEquivOfSurjective`) and of bialgebras (hence Hopf algebras) for every nonzero
`q : ℂ` (`uqSl2BialgEquivOfSurjective`). Specializing to `CartanDatum.sl2` identifies `UqSl2 q`
with `QuantumEnvelopingAlgebra CartanDatum.sl2 q` (`uqSl2AlgEquiv`, `uqSl2BialgEquiv`).

## Main definitions

* `TauCeti.QuantumEnvelopingAlgebra.fromUqSl2`: root-`i` algebra homomorphism
  `UqSl2 (q ^ D.symmetrizer i) →ₐ[ℂ] QuantumEnvelopingAlgebra D q`.
* `TauCeti.QuantumEnvelopingAlgebra.fromUqSl2BialgHom`: root-`i` bialgebra homomorphism
  `UqSl2 (q ^ D.symmetrizer i) →ₐc[ℂ] QuantumEnvelopingAlgebra D q`.
* `TauCeti.QuantumEnvelopingAlgebra.uqSl2AlgEquivOfSurjective`,
  `TauCeti.QuantumEnvelopingAlgebra.uqSl2BialgEquivOfSurjective`: algebra and bialgebra
  equivalences on any rank-one datum whose simple toral element generates `Y`.
* `TauCeti.QuantumEnvelopingAlgebra.uqSl2AlgEquiv`,
  `TauCeti.QuantumEnvelopingAlgebra.uqSl2BialgEquiv`: algebra and bialgebra equivalences
  `UqSl2 q ≃ QuantumEnvelopingAlgebra CartanDatum.sl2 q`.

## References

* G. Lusztig, *Introduction to Quantum Groups*, Progress in Mathematics 110, Birkhäuser, 1993,
  §3.1.
* A. Virelizier, *Quantum groups*, Graduate Studies in Mathematics, §2.3.
-/

public noncomputable section

namespace TauCeti.QuantumEnvelopingAlgebra

variable {ι X Y : Type*} [AddCommGroup X] [AddCommGroup Y]

/-! ### Root-`i` embeddings from `UqSl2` -/

private def fromUqSl2Tuple (D : CartanDatum ι X Y) (q : ℂ) (i : ι) :
    UqSl2.GeneratorTuple (q ^ D.symmetrizer i) (QuantumEnvelopingAlgebra D q) where
  e := e D q i
  f := f D q i
  k := simpleK D q i
  kInv := simpleKInv D q i
  k_mul_kInv := by simp
  kInv_mul_k := by simp
  k_mul_e := simpleK_mul_e_self i
  k_mul_f := simpleK_mul_f_self i
  e_mul_f_sub_f_mul_e := e_mul_f_sub_f_mul_e_self i

/-- The canonical rank-one algebra homomorphism `UqSl2 (q ^ dᵢ) →ₐ[ℂ] U(D, q)` attached to a
simple root `i`, valid unconditionally for every `q : ℂ`. -/
def fromUqSl2 (D : CartanDatum ι X Y) (q : ℂ) (i : ι) :
    UqSl2 (q ^ D.symmetrizer i) →ₐ[ℂ] QuantumEnvelopingAlgebra D q :=
  UqSl2.lift (fromUqSl2Tuple D q i)

@[simp]
theorem fromUqSl2_e (D : CartanDatum ι X Y) (q : ℂ) (i : ι) :
    fromUqSl2 D q i (UqSl2.e (q ^ D.symmetrizer i)) = e D q i := by
  simp [fromUqSl2, fromUqSl2Tuple]

@[simp]
theorem fromUqSl2_f (D : CartanDatum ι X Y) (q : ℂ) (i : ι) :
    fromUqSl2 D q i (UqSl2.f (q ^ D.symmetrizer i)) = f D q i := by
  simp [fromUqSl2, fromUqSl2Tuple]

@[simp]
theorem fromUqSl2_k (D : CartanDatum ι X Y) (q : ℂ) (i : ι) :
    fromUqSl2 D q i (UqSl2.k (q ^ D.symmetrizer i)) = simpleK D q i := by
  simp [fromUqSl2, fromUqSl2Tuple]

@[simp]
theorem fromUqSl2_kInv (D : CartanDatum ι X Y) (q : ℂ) (i : ι) :
    fromUqSl2 D q i (UqSl2.kInv (q ^ D.symmetrizer i)) = simpleKInv D q i := by
  simp [fromUqSl2, fromUqSl2Tuple]

/-- The root-`i` bialgebra (hence Hopf algebra, via `BialgHomClass.map_antipode`) homomorphism
`UqSl2 (q ^ dᵢ) →ₐc[ℂ] QuantumEnvelopingAlgebra D q`. -/
def fromUqSl2BialgHom (D : CartanDatum ι X Y) (q : ℂ) (i : ι)
    [Fact (q ^ D.symmetrizer i ≠ 0)] [IsSerreRegular D q] :
    UqSl2 (q ^ D.symmetrizer i) →ₐc[ℂ] QuantumEnvelopingAlgebra D q :=
  BialgHom.ofAlgHom (fromUqSl2 D q i)
    (by apply UqSl2.hom_ext <;> simp)
    (by apply UqSl2.hom_ext <;> simp)

@[simp]
theorem fromUqSl2BialgHom_toAlgHom (D : CartanDatum ι X Y) (q : ℂ) (i : ι)
    [Fact (q ^ D.symmetrizer i ≠ 0)] [IsSerreRegular D q] :
    (fromUqSl2BialgHom D q i :
        UqSl2 (q ^ D.symmetrizer i) →ₐ[ℂ] QuantumEnvelopingAlgebra D q) =
      fromUqSl2 D q i := (rfl)

@[simp]
theorem fromUqSl2BialgHom_apply (D : CartanDatum ι X Y) (q : ℂ) (i : ι)
    [Fact (q ^ D.symmetrizer i ≠ 0)] [IsSerreRegular D q]
    (x : UqSl2 (q ^ D.symmetrizer i)) :
    fromUqSl2BialgHom D q i x = fromUqSl2 D q i x := (rfl)

/-! ### Rank-one equivalence when `simpleTorus` generates `Y` -/

/-- The `ℤ`-multiples of any simple toral element `dᵢ hᵢ` are injective in `Y`. -/
theorem zsmul_simpleTorus_injective (D : CartanDatum ι X Y) (i : ι) :
    Function.Injective (fun n : ℤ ↦ n • D.simpleTorus i) := by
  intro m n hmn
  have h := congrArg (D.pairing (D.root i)) hmn
  simp only [map_zsmul, D.pairing_root_simpleTorus_self, zsmul_eq_mul] at h
  have hd : (0 : ℤ) < D.symmetrizer i := Nat.cast_pos.mpr (D.symmetrizer_pos i)
  exact mul_right_cancel₀ (by positivity) h

private theorem kUnit_zpow_mul_e (q : ℂ) (b : ℤ) :
    ((UqSl2.kUnit q ^ b : (UqSl2 q)ˣ) : UqSl2 q) * UqSl2.e q =
      (q ^ 2) ^ b • (UqSl2.e q * ((UqSl2.kUnit q ^ b : (UqSl2 q)ˣ) : UqSl2 q)) := by
  rcases eq_or_ne q 0 with rfl | hq
  · simp
  · have : Fact (q ≠ 0) := ⟨hq⟩
    calc ((UqSl2.kUnit q ^ b : (UqSl2 q)ˣ) : UqSl2 q) * UqSl2.e q
        = (((UqSl2.kUnit q ^ b : (UqSl2 q)ˣ) : UqSl2 q) * UqSl2.e q *
            ↑(UqSl2.kUnit q ^ b)⁻¹) *
            ((UqSl2.kUnit q ^ b : (UqSl2 q)ˣ) : UqSl2 q) := by
          rw [mul_assoc, Units.inv_mul, mul_one]
      _ = (q ^ 2) ^ b • (UqSl2.e q * ((UqSl2.kUnit q ^ b : (UqSl2 q)ˣ) : UqSl2 q)) := by
          rw [UqSl2.kUnit_zpow_mul_e_mul_inv, smul_mul_assoc, ← zpow_natCast, ← zpow_mul]
          rfl

private theorem kUnit_zpow_mul_f (q : ℂ) (b : ℤ) :
    ((UqSl2.kUnit q ^ b : (UqSl2 q)ˣ) : UqSl2 q) * UqSl2.f q =
      (q ^ 2) ^ (-b) • (UqSl2.f q * ((UqSl2.kUnit q ^ b : (UqSl2 q)ˣ) : UqSl2 q)) := by
  have h := UqSl2.f_mul_kUnit_zpow q (-b)
  rw [zpow_neg] at h
  calc ((UqSl2.kUnit q ^ b : (UqSl2 q)ˣ) : UqSl2 q) * UqSl2.f q
      = ((UqSl2.kUnit q ^ b : (UqSl2 q)ˣ) : UqSl2 q) *
          (UqSl2.f q * ↑(UqSl2.kUnit q ^ b)⁻¹) *
          ((UqSl2.kUnit q ^ b : (UqSl2 q)ˣ) : UqSl2 q) := by
        rw [mul_assoc, mul_assoc, Units.inv_mul, mul_one]
    _ = (q ^ 2) ^ (-b) • (UqSl2.f q * ((UqSl2.kUnit q ^ b : (UqSl2 q)ˣ) : UqSl2 q)) := by
        rw [h, mul_smul_comm, smul_mul_assoc, ← mul_assoc, Units.mul_inv, one_mul,
          ← zpow_natCast, ← zpow_mul]
        rfl

private theorem map_kUnit_zpow {A : Type*} [Ring A] [Algebra ℂ A] {q' : ℂ}
    (F : UqSl2 q' →ₐ[ℂ] A) (u : Aˣ) (hu : F (UqSl2.k q') = u) (n : ℤ) :
    F ((UqSl2.kUnit q' ^ n : (UqSl2 q')ˣ) : UqSl2 q') = ((u ^ n : Aˣ) : A) := by
  have hmap : Units.map F.toMonoidHom (UqSl2.kUnit q') = u := by
    ext
    simpa using hu
  rw [← hmap]
  exact congrArg (Units.val : Aˣ → A) ((Units.map F.toMonoidHom).map_zpow (UqSl2.kUnit q') n)

section Unique

variable [Unique ι]

private def torusCoord (D : CartanDatum ι X Y) (y : Y) : ℤ :=
  D.pairing (D.root default) y / (2 * (D.symmetrizer default : ℤ))

private theorem torusCoord_zsmul (D : CartanDatum ι X Y) (n : ℤ) :
    torusCoord D (n • D.simpleTorus default) = n := by
  have hd : (0 : ℤ) < D.symmetrizer default := Nat.cast_pos.mpr (D.symmetrizer_pos default)
  rw [torusCoord, map_zsmul, D.pairing_root_simpleTorus_self, zsmul_eq_mul]
  exact Int.mul_ediv_cancel n (by positivity)

private def toUqSl2Tuple (D : CartanDatum ι X Y) (q q' : ℂ) (hq' : q' = q ^ D.symmetrizer default)
    (hY : Function.Surjective (fun n : ℤ ↦ n • D.simpleTorus default)) :
    GeneratorTuple D q (UqSl2 q') :=
  have hadd : ∀ y₁ y₂ : Y, torusCoord D (y₁ + y₂) = torusCoord D y₁ + torusCoord D y₂ := by
    intro y₁ y₂
    obtain ⟨m, rfl⟩ := hY y₁
    obtain ⟨n, rfl⟩ := hY y₂
    rw [← add_zsmul, torusCoord_zsmul, torusCoord_zsmul, torusCoord_zsmul]
  have hpair : ∀ y : Y, D.pairing (D.root default) y =
      (D.symmetrizer default : ℤ) * (2 * torusCoord D y) := by
    intro y
    obtain ⟨n, rfl⟩ := hY y
    rw [torusCoord_zsmul, map_zsmul, D.pairing_root_simpleTorus_self, zsmul_eq_mul]
    push_cast
    ring
  { e := fun _ ↦ UqSl2.e q'
    f := fun _ ↦ UqSl2.f q'
    k := fun y ↦ ((UqSl2.kUnit q' ^ torusCoord D y : (UqSl2 q')ˣ) : UqSl2 q')
    k_zero := by simp [torusCoord]
    k_mul_k := fun y₁ y₂ ↦ by rw [hadd, zpow_add, Units.val_mul]
    k_mul_e := fun y i ↦ by
      rw [Unique.eq_default i, kUnit_zpow_mul_e, hq', hpair y, zpow_mul, zpow_natCast,
        ← zpow_natCast (q ^ D.symmetrizer default) 2, ← zpow_mul]
      rfl
    k_mul_f := fun y i ↦ by
      rw [Unique.eq_default i, kUnit_zpow_mul_f, hq', hpair y, ← mul_neg, zpow_mul,
        zpow_natCast, ← zpow_natCast (q ^ D.symmetrizer default) 2, ← zpow_mul, mul_neg]
      rfl
    e_mul_f_sub_f_mul_e_self := fun i ↦ by
      have h1 : torusCoord D (D.simpleTorus default) = 1 := by
        simpa using torusCoord_zsmul D 1
      have hm1 : torusCoord D (-D.simpleTorus default) = -1 := by
        simpa using torusCoord_zsmul D (-1)
      rw [Unique.eq_default i, ← hq', h1, hm1, zpow_one, zpow_neg_one,
        UqSl2.kUnit_val, UqSl2.kUnit_inv]
      exact UqSl2.e_mul_f_sub_f_mul_e
    e_mul_f_of_ne := fun hij ↦ (hij (Subsingleton.elim _ _)).elim
    serre_e := fun hij ↦ (hij (Subsingleton.elim _ _)).elim
    serre_f := fun hij ↦ (hij (Subsingleton.elim _ _)).elim }

/-- On any rank-one Cartan datum `[Unique ι]` whose simple toral element `d₀ h₀` generates `Y`
over `ℤ`, `fromUqSl2 D q default` is an algebra isomorphism
`UqSl2 (q ^ d₀) ≃ₐ[ℂ] QuantumEnvelopingAlgebra D q` for every `q : ℂ`. -/
def uqSl2AlgEquivOfSurjective (D : CartanDatum ι X Y) (q : ℂ)
    (hY : Function.Surjective (fun n : ℤ ↦ n • D.simpleTorus default)) :
    UqSl2 (q ^ D.symmetrizer default) ≃ₐ[ℂ] QuantumEnvelopingAlgebra D q :=
  let g := lift (toUqSl2Tuple D q (q ^ D.symmetrizer default) rfl hY)
  have h1 : torusCoord D (D.simpleTorus default) = 1 := by
    simpa using torusCoord_zsmul D 1
  AlgEquiv.ofAlgHom (fromUqSl2 D q default) g
    (by
      ext x
      · simp [g, toUqSl2Tuple, Unique.eq_default x]
      · simp [g, toUqSl2Tuple, Unique.eq_default x]
      · obtain ⟨n, rfl⟩ := hY x
        have hk := map_kUnit_zpow (fromUqSl2 D q default)
          (kUnit D q (.ofAdd (D.simpleTorus default))) (by simp) n
        rw [kUnit_zpow_val] at hk
        simpa [g, toUqSl2Tuple, torusCoord_zsmul] using hk)
    (by
      apply UqSl2.hom_ext
      · simp [g, toUqSl2Tuple]
      · simp [g, toUqSl2Tuple]
      · simp [g, toUqSl2Tuple, simpleK, h1])

@[simp]
theorem uqSl2AlgEquivOfSurjective_apply (D : CartanDatum ι X Y) (q : ℂ)
    (hY : Function.Surjective (fun n : ℤ ↦ n • D.simpleTorus default))
    (x : UqSl2 (q ^ D.symmetrizer default)) :
    uqSl2AlgEquivOfSurjective D q hY x = fromUqSl2 D q default x := (rfl)

/-- On any rank-one Cartan datum `[Unique ι]` whose simple toral element `d₀ h₀` generates `Y`
over `ℤ`, `fromUqSl2BialgHom D q default` is a bialgebra (hence Hopf algebra) isomorphism
`UqSl2 (q ^ d₀) ≃ₐc[ℂ] QuantumEnvelopingAlgebra D q` whenever `q ^ d₀ ≠ 0`. -/
def uqSl2BialgEquivOfSurjective (D : CartanDatum ι X Y) (q : ℂ)
    [Fact (q ^ D.symmetrizer default ≠ 0)]
    (hY : Function.Surjective (fun n : ℤ ↦ n • D.simpleTorus default)) :
    UqSl2 (q ^ D.symmetrizer default) ≃ₐc[ℂ] QuantumEnvelopingAlgebra D q :=
  BialgEquiv.ofAlgEquiv (uqSl2AlgEquivOfSurjective D q hY)
    (by apply UqSl2.hom_ext <;> simp)
    (by apply UqSl2.hom_ext <;> simp)

@[simp]
theorem uqSl2BialgEquivOfSurjective_apply (D : CartanDatum ι X Y) (q : ℂ)
    [Fact (q ^ D.symmetrizer default ≠ 0)]
    (hY : Function.Surjective (fun n : ℤ ↦ n • D.simpleTorus default))
    (x : UqSl2 (q ^ D.symmetrizer default)) :
    uqSl2BialgEquivOfSurjective D q hY x = fromUqSl2 D q default x := (rfl)

end Unique

/-! ### Identification with `UqSl2 q` on `CartanDatum.sl2` -/

private def fromUqSl2Sl2Tuple (q : ℂ) :
    UqSl2.GeneratorTuple q (QuantumEnvelopingAlgebra CartanDatum.sl2 q) where
  e := e CartanDatum.sl2 q ()
  f := f CartanDatum.sl2 q ()
  k := simpleK CartanDatum.sl2 q ()
  kInv := simpleKInv CartanDatum.sl2 q ()
  k_mul_kInv := by simp
  kInv_mul_k := by simp
  k_mul_e := by simpa using simpleK_mul_e_self (D := CartanDatum.sl2) (q := q) ()
  k_mul_f := by simpa using simpleK_mul_f_self (D := CartanDatum.sl2) (q := q) ()
  e_mul_f_sub_f_mul_e := by
    simpa using e_mul_f_sub_f_mul_e_self (D := CartanDatum.sl2) (q := q) ()

/-- Algebra isomorphism `UqSl2 q ≃ₐ[ℂ] QuantumEnvelopingAlgebra CartanDatum.sl2 q`, valid
unconditionally for every `q : ℂ`. -/
def uqSl2AlgEquiv (q : ℂ) :
    UqSl2 q ≃ₐ[ℂ] QuantumEnvelopingAlgebra CartanDatum.sl2 q :=
  have hY : Function.Surjective (fun n : ℤ ↦ n • CartanDatum.sl2.simpleTorus ()) := fun y ↦
    ⟨y, by simp⟩
  let f := UqSl2.lift (fromUqSl2Sl2Tuple q)
  let g := lift (toUqSl2Tuple CartanDatum.sl2 q q (by simp) hY)
  have heY : ∀ n : ℤ, torusCoord CartanDatum.sl2 n = n := fun n ↦ by
    simpa using torusCoord_zsmul CartanDatum.sl2 n
  AlgEquiv.ofAlgHom f g
    (by
      ext x
      · simp [f, g, fromUqSl2Sl2Tuple, toUqSl2Tuple]
      · simp [f, g, fromUqSl2Sl2Tuple, toUqSl2Tuple]
      · have hk := map_kUnit_zpow f (kUnit CartanDatum.sl2 q (.ofAdd 1))
          (by simp [f, fromUqSl2Sl2Tuple, simpleK]) x
        rw [kUnit_zpow_val, zsmul_one] at hk
        simpa [g, toUqSl2Tuple, heY x] using hk)
    (by
      apply UqSl2.hom_ext
      · simp [f, g, fromUqSl2Sl2Tuple, toUqSl2Tuple]
      · simp [f, g, fromUqSl2Sl2Tuple, toUqSl2Tuple]
      · simp [f, g, fromUqSl2Sl2Tuple, toUqSl2Tuple, simpleK, heY 1])

@[simp]
theorem uqSl2AlgEquiv_e (q : ℂ) :
    uqSl2AlgEquiv q (UqSl2.e q) = e CartanDatum.sl2 q () := by
  simp [uqSl2AlgEquiv, fromUqSl2Sl2Tuple]

@[simp]
theorem uqSl2AlgEquiv_f (q : ℂ) :
    uqSl2AlgEquiv q (UqSl2.f q) = f CartanDatum.sl2 q () := by
  simp [uqSl2AlgEquiv, fromUqSl2Sl2Tuple]

@[simp]
theorem uqSl2AlgEquiv_k (q : ℂ) :
    uqSl2AlgEquiv q (UqSl2.k q) = k CartanDatum.sl2 q 1 := by
  simp [uqSl2AlgEquiv, fromUqSl2Sl2Tuple, simpleK]

@[simp]
theorem uqSl2AlgEquiv_kInv (q : ℂ) :
    uqSl2AlgEquiv q (UqSl2.kInv q) = k CartanDatum.sl2 q (-1) := by
  simp [uqSl2AlgEquiv, fromUqSl2Sl2Tuple, simpleKInv]

@[simp]
theorem uqSl2AlgEquiv_symm_e (q : ℂ) :
    (uqSl2AlgEquiv q).symm (e CartanDatum.sl2 q ()) = UqSl2.e q :=
  (uqSl2AlgEquiv q).symm_apply_eq.mpr (uqSl2AlgEquiv_e q).symm

@[simp]
theorem uqSl2AlgEquiv_symm_f (q : ℂ) :
    (uqSl2AlgEquiv q).symm (f CartanDatum.sl2 q ()) = UqSl2.f q :=
  (uqSl2AlgEquiv q).symm_apply_eq.mpr (uqSl2AlgEquiv_f q).symm

@[simp]
theorem uqSl2AlgEquiv_symm_k (q : ℂ) (y : ℤ) :
    (uqSl2AlgEquiv q).symm (k CartanDatum.sl2 q y) =
      ((UqSl2.kUnit q ^ y : (UqSl2 q)ˣ) : UqSl2 q) := by
  rw [AlgEquiv.symm_apply_eq]
  have hk := map_kUnit_zpow (uqSl2AlgEquiv q).toAlgHom (kUnit CartanDatum.sl2 q (.ofAdd 1))
    (by simp) y
  rw [kUnit_zpow_val, zsmul_one] at hk
  exact hk.symm

/-- Bialgebra (hence Hopf algebra, via `BialgHomClass.map_antipode`) isomorphism
`UqSl2 q ≃ₐc[ℂ] QuantumEnvelopingAlgebra CartanDatum.sl2 q` for every nonzero `q : ℂ`. -/
def uqSl2BialgEquiv (q : ℂ) [Fact (q ≠ 0)] :
    UqSl2 q ≃ₐc[ℂ] QuantumEnvelopingAlgebra CartanDatum.sl2 q :=
  BialgEquiv.ofAlgEquiv (uqSl2AlgEquiv q)
    (by apply UqSl2.hom_ext <;> simp)
    (by apply UqSl2.hom_ext <;> simp [simpleK, simpleKInv])

@[simp]
theorem uqSl2BialgEquiv_toAlgEquiv (q : ℂ) [Fact (q ≠ 0)] :
    (uqSl2BialgEquiv q).toAlgEquiv = uqSl2AlgEquiv q := (rfl)

@[simp]
theorem uqSl2BialgEquiv_apply (q : ℂ) [Fact (q ≠ 0)] (x : UqSl2 q) :
    uqSl2BialgEquiv q x = uqSl2AlgEquiv q x := (rfl)

@[simp]
theorem uqSl2BialgEquiv_symm_apply (q : ℂ) [Fact (q ≠ 0)]
    (x : QuantumEnvelopingAlgebra CartanDatum.sl2 q) :
    (uqSl2BialgEquiv q).symm x = (uqSl2AlgEquiv q).symm x := (rfl)

end TauCeti.QuantumEnvelopingAlgebra
