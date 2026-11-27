/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Bialgebra.Equiv
public import TauCeti.LinearAlgebra.Matrix.Cartan.Datum.Constructions
public import TauCeti.QuantumGroups.QuantizedEnvelopingAlgebra.Hopf
public import TauCeti.QuantumGroups.UqSl2.Hopf

import TauCeti.QuantumGroups.UqSl2.Rescale

/-!
# Rank-one root homomorphisms and comparison with `UqSl2`

Every simple root `i` of a symmetrizable Cartan datum `D` induces a canonical `ℂ`-algebra
homomorphism `fromUqSl2 D q i : UqSl2 (q ^ D.symmetrizer i) →ₐ[ℂ] QuantizedEnvelopingAlgebra D q`
sending `E ↦ Eᵢ`, `F ↦ Fᵢ`, and `K^(±1) ↦ Kᵢ^(±1)`, upgrading to a bialgebra (hence Hopf algebra)
homomorphism `fromUqSl2BialgHom` whenever `q ^ D.symmetrizer i ≠ 0` and the Serre quantum
factorials of `D` are nonzero.

When `[Unique ι]` and `n ↦ n • D.simpleTorus default` surjects onto `Y`, `fromUqSl2` upgrades
unconditionally to an algebra isomorphism `uqSl2AlgEquivOfSurjective`, and for
`q ^ D.symmetrizer default ≠ 0` to a bialgebra isomorphism `uqSl2BialgEquivOfSurjective`; on
`CartanDatum.sl2` these specialize to `uqSl2AlgEquiv` (unconditional) and `uqSl2BialgEquiv` (for
`q ≠ 0`).

## Main definitions and results

* `TauCeti.QuantizedEnvelopingAlgebra.fromUqSl2`, `fromUqSl2BialgHom`: root-`i` algebra and
  bialgebra homomorphisms out of `UqSl2 (q ^ D.symmetrizer i)`.
* `TauCeti.QuantizedEnvelopingAlgebra.uqSl2AlgEquivOfSurjective`,
  `uqSl2BialgEquivOfSurjective`: rank-one algebra (unconditional) and bialgebra (for
  `q ^ d₀ ≠ 0`) isomorphisms when `d₀ h₀` generates `Y`.
* `TauCeti.QuantizedEnvelopingAlgebra.uqSl2AlgEquiv`, `uqSl2BialgEquiv`: the unconditional algebra
  isomorphism and (for `q ≠ 0`) bialgebra isomorphism
  `UqSl2 q ≃ QuantizedEnvelopingAlgebra CartanDatum.sl2 q`.

## References

* G. Lusztig, *Introduction to Quantum Groups*, Progress in Mathematics 110, Birkhäuser, 1993, §3.1.
* J. C. Jantzen, *Lectures on Quantum Groups*, Graduate Studies in Mathematics 6, AMS, 1996, §4.4.
* A. Virelizier, *Quantum groups*, §2.3.
-/

public noncomputable section

namespace TauCeti.QuantizedEnvelopingAlgebra

variable {ι X Y : Type*} [AddCommGroup X] [AddCommGroup Y]

private def fromUqSl2TupleAux (D : CartanDatum ι X Y) (q q' : ℂ) (i : ι)
    (hq' : q' = q ^ D.symmetrizer i) :
    UqSl2.GeneratorTuple q' (QuantizedEnvelopingAlgebra D q) where
  e := e D q i
  f := f D q i
  k := simpleK D q i
  kInv := simpleKInv D q i
  k_mul_kInv := simpleK_mul_simpleKInv D q i
  kInv_mul_k := simpleKInv_mul_simpleK D q i
  k_mul_e := by
    rw [hq', simpleK_mul_e, D.cartan_apply_self, zpow_ofNat]
  k_mul_f := by
    rw [hq', simpleK_mul_f, D.cartan_apply_self, zpow_neg, zpow_ofNat, inv_pow]
  e_mul_f_sub_f_mul_e := hq' ▸ e_mul_f_sub_f_mul_e_self D q i

section FromUqSl2

variable (D : CartanDatum ι X Y) (q : ℂ) (i : ι)

/-- The canonical rank-one `ℂ`-algebra homomorphism
`UqSl2 (q ^ dᵢ) →ₐ[ℂ] QuantizedEnvelopingAlgebra D q` attached to simple root `i`. -/
def fromUqSl2 : UqSl2 (q ^ D.symmetrizer i) →ₐ[ℂ] QuantizedEnvelopingAlgebra D q :=
  UqSl2.lift (fromUqSl2TupleAux D q _ i rfl)

@[simp] theorem fromUqSl2_e : fromUqSl2 D q i (UqSl2.e (q ^ D.symmetrizer i)) = e D q i := by
  simp [fromUqSl2, fromUqSl2TupleAux]
@[simp] theorem fromUqSl2_f : fromUqSl2 D q i (UqSl2.f (q ^ D.symmetrizer i)) = f D q i := by
  simp [fromUqSl2, fromUqSl2TupleAux]
@[simp] theorem fromUqSl2_k : fromUqSl2 D q i (UqSl2.k (q ^ D.symmetrizer i)) = simpleK D q i := by
  simp [fromUqSl2, fromUqSl2TupleAux]
@[simp] theorem fromUqSl2_kInv :
    fromUqSl2 D q i (UqSl2.kInv (q ^ D.symmetrizer i)) = simpleKInv D q i := by
  simp [fromUqSl2, fromUqSl2TupleAux]

/-- The root-`i` bialgebra (hence Hopf algebra) homomorphism
`UqSl2 (q ^ dᵢ) →ₐc[ℂ] QuantizedEnvelopingAlgebra D q`. -/
def fromUqSl2BialgHom
    (hserre : ∀ j l, j ≠ l → quantumFactorial (q ^ D.symmetrizer j) (D.serreLength j l) ≠ 0)
    [Fact (q ^ D.symmetrizer i ≠ 0)] :
    letI := bialgebra D q hserre
    UqSl2 (q ^ D.symmetrizer i) →ₐc[ℂ] QuantizedEnvelopingAlgebra D q :=
  letI := bialgebra D q hserre
  BialgHom.ofAlgHom (fromUqSl2 D q i)
    (by apply UqSl2.hom_ext <;> simp)
    (by apply UqSl2.hom_ext <;> simp)

@[simp] theorem fromUqSl2BialgHom_toAlgHom
    (hserre : ∀ j l, j ≠ l → quantumFactorial (q ^ D.symmetrizer j) (D.serreLength j l) ≠ 0)
    [Fact (q ^ D.symmetrizer i ≠ 0)] :
    letI := bialgebra D q hserre
    (fromUqSl2BialgHom D q i hserre :
      UqSl2 (q ^ D.symmetrizer i) →ₐ[ℂ] QuantizedEnvelopingAlgebra D q) =
      fromUqSl2 D q i := (rfl)

@[simp] theorem fromUqSl2BialgHom_apply
    (hserre : ∀ j l, j ≠ l → quantumFactorial (q ^ D.symmetrizer j) (D.serreLength j l) ≠ 0)
    [Fact (q ^ D.symmetrizer i ≠ 0)] (x : UqSl2 (q ^ D.symmetrizer i)) :
    letI := bialgebra D q hserre
    fromUqSl2BialgHom D q i hserre x = fromUqSl2 D q i x := (rfl)

end FromUqSl2

section Unique

variable [Unique ι]

private def torusCoord (D : CartanDatum ι X Y) (y : Y) : ℤ :=
  D.pairing (D.root default) y / (2 * (D.symmetrizer default : ℤ))

private theorem torusCoord_zsmul (D : CartanDatum ι X Y) (n : ℤ) :
    torusCoord D (n • D.simpleTorus default) = n := by
  have hd : (0 : ℤ) < D.symmetrizer default := Nat.cast_pos.mpr (D.symmetrizer_pos default)
  rw [torusCoord, map_zsmul, D.pairing_root_simpleTorus_self, zsmul_eq_mul]
  exact Int.mul_ediv_cancel n (by positivity)

private theorem torusCoord_simpleTorus (D : CartanDatum ι X Y) :
    torusCoord D (D.simpleTorus default) = 1 := by
  simpa using torusCoord_zsmul D 1

private def toUqSl2Tuple (D : CartanDatum ι X Y) (q q' : ℂ) (hq' : q' = q ^ D.symmetrizer default)
    (hY : Function.Surjective (fun n : ℤ => n • D.simpleTorus default)) :
    GeneratorTuple D q (UqSl2 q') :=
  have hadd : ∀ y₁ y₂ : Y, torusCoord D (y₁ + y₂) = torusCoord D y₁ + torusCoord D y₂ := by
    intro y₁ y₂
    obtain ⟨m, rfl⟩ := hY y₁
    obtain ⟨n, rfl⟩ := hY y₂
    rw [← add_zsmul, torusCoord_zsmul, torusCoord_zsmul, torusCoord_zsmul]
  have hneg : ∀ y : Y, torusCoord D (-y) = -torusCoord D y := by
    intro y
    obtain ⟨n, rfl⟩ := hY y
    rw [← neg_zsmul, torusCoord_zsmul, torusCoord_zsmul]
  have hpair : ∀ y : Y, D.pairing (D.root default) y =
      (D.symmetrizer default : ℤ) * (2 * torusCoord D y) := by
    intro y
    obtain ⟨n, rfl⟩ := hY y
    rw [torusCoord_zsmul, map_zsmul, D.pairing_root_simpleTorus_self, zsmul_eq_mul]
    push_cast; ring
  { e _ := UqSl2.e q'
    f _ := UqSl2.f q'
    k y := ((UqSl2.kUnit q' ^ torusCoord D y : (UqSl2 q')ˣ) : UqSl2 q')
    k_zero := by simp [torusCoord]
    k_mul_k y₁ y₂ := by rw [hadd, zpow_add, Units.val_mul]
    conjugate_e y i := by
      rw [Unique.eq_default i, hneg, zpow_neg, UqSl2.kUnit_zpow_mul_e_mul_inv, hq',
        ← zpow_natCast q, ← zpow_mul, hpair y]
    conjugate_f y i := by
      rw [Unique.eq_default i, hneg, zpow_neg, UqSl2.kUnit_zpow_mul_f_mul_inv, hq',
        ← zpow_natCast q, ← zpow_mul, mul_neg, hpair y]
    commutator_self i := by
      rw [Unique.eq_default i, ← hq', hneg, torusCoord_simpleTorus, zpow_one, zpow_neg_one,
        UqSl2.val_kUnit, UqSl2.val_inv_kUnit]
      exact UqSl2.e_mul_f_sub_f_mul_e
    commutator_ne hij := (hij (Subsingleton.elim _ _)).elim
    serre_e hij := (hij (Subsingleton.elim _ _)).elim
    serre_f hij := (hij (Subsingleton.elim _ _)).elim }

private def uqSl2AlgEquivAux (D : CartanDatum ι X Y) (q q' : ℂ)
    (hq' : q' = q ^ D.symmetrizer default)
    (hY : Function.Surjective (fun n : ℤ => n • D.simpleTorus default)) :
    UqSl2 q' ≃ₐ[ℂ] QuantizedEnvelopingAlgebra D q :=
  let f := UqSl2.lift (fromUqSl2TupleAux D q q' default hq')
  let g := lift (toUqSl2Tuple D q q' hq' hY)
  AlgEquiv.ofAlgHom f g
    (by
      ext x
      · simp [f, g, fromUqSl2TupleAux, toUqSl2Tuple, Unique.eq_default x]
      · simp [f, g, fromUqSl2TupleAux, toUqSl2Tuple, Unique.eq_default x]
      · obtain ⟨n, rfl⟩ := hY x
        simpa [g, toUqSl2Tuple, torusCoord_zsmul] using
          UqSl2.map_kUnit_zpow f (kUnitsHom D q (.ofAdd (D.simpleTorus default)))
            (by simp [f, fromUqSl2TupleAux, simpleK_def]) n)
    (by apply UqSl2.hom_ext <;>
      simp [f, g, fromUqSl2TupleAux, toUqSl2Tuple, simpleK_def, torusCoord_simpleTorus])

variable (D : CartanDatum ι X Y) (q : ℂ)

/-- Rank-one `ℂ`-algebra isomorphism `UqSl2 (q ^ d₀) ≃ₐ[ℂ] QuantizedEnvelopingAlgebra D q` when
`n ↦ n • D.simpleTorus default` surjects onto `Y`. -/
def uqSl2AlgEquivOfSurjective
    (hY : Function.Surjective (fun n : ℤ => n • D.simpleTorus default)) :
    UqSl2 (q ^ D.symmetrizer default) ≃ₐ[ℂ] QuantizedEnvelopingAlgebra D q :=
  uqSl2AlgEquivAux D q _ rfl hY

@[simp] theorem uqSl2AlgEquivOfSurjective_apply
    (hY : Function.Surjective (fun n : ℤ => n • D.simpleTorus default))
    (x : UqSl2 (q ^ D.symmetrizer default)) :
    uqSl2AlgEquivOfSurjective D q hY x = fromUqSl2 D q default x := (rfl)

/-- Rank-one bialgebra (hence Hopf algebra) isomorphism
`UqSl2 (q ^ d₀) ≃ₐc[ℂ] QuantizedEnvelopingAlgebra D q` when `d₀ h₀` generates `Y`. -/
def uqSl2BialgEquivOfSurjective [Fact (q ^ D.symmetrizer default ≠ 0)]
    (hY : Function.Surjective (fun n : ℤ => n • D.simpleTorus default)) :
    UqSl2 (q ^ D.symmetrizer default) ≃ₐc[ℂ] QuantizedEnvelopingAlgebra D q :=
  BialgEquiv.ofAlgEquiv (uqSl2AlgEquivOfSurjective D q hY)
    (by apply UqSl2.hom_ext <;> simp)
    (by apply UqSl2.hom_ext <;> simp)

@[simp] theorem uqSl2BialgEquivOfSurjective_toAlgEquiv [Fact (q ^ D.symmetrizer default ≠ 0)]
    (hY : Function.Surjective (fun n : ℤ => n • D.simpleTorus default)) :
    (uqSl2BialgEquivOfSurjective D q hY).toAlgEquiv = uqSl2AlgEquivOfSurjective D q hY := (rfl)

@[simp] theorem uqSl2BialgEquivOfSurjective_apply [Fact (q ^ D.symmetrizer default ≠ 0)]
    (hY : Function.Surjective (fun n : ℤ => n • D.simpleTorus default))
    (x : UqSl2 (q ^ D.symmetrizer default)) :
    uqSl2BialgEquivOfSurjective D q hY x = fromUqSl2 D q default x := (rfl)

end Unique

section Sl2

variable (q : ℂ)

/-- Unconditional `ℂ`-algebra isomorphism
`UqSl2 q ≃ₐ[ℂ] QuantizedEnvelopingAlgebra CartanDatum.sl2 q`. -/
def uqSl2AlgEquiv : UqSl2 q ≃ₐ[ℂ] QuantizedEnvelopingAlgebra CartanDatum.sl2 q :=
  uqSl2AlgEquivAux CartanDatum.sl2 q q (by simp) fun y => ⟨y, by simp⟩

@[simp] theorem uqSl2AlgEquiv_e : uqSl2AlgEquiv q (UqSl2.e q) = e CartanDatum.sl2 q () := by
  simp [uqSl2AlgEquiv, uqSl2AlgEquivAux, fromUqSl2TupleAux]
@[simp] theorem uqSl2AlgEquiv_f : uqSl2AlgEquiv q (UqSl2.f q) = f CartanDatum.sl2 q () := by
  simp [uqSl2AlgEquiv, uqSl2AlgEquivAux, fromUqSl2TupleAux]
@[simp] theorem uqSl2AlgEquiv_k : uqSl2AlgEquiv q (UqSl2.k q) = k CartanDatum.sl2 q 1 := by
  simp [uqSl2AlgEquiv, uqSl2AlgEquivAux, fromUqSl2TupleAux, simpleK_def]
@[simp] theorem uqSl2AlgEquiv_kInv :
    uqSl2AlgEquiv q (UqSl2.kInv q) = k CartanDatum.sl2 q (-1) := by
  simp [uqSl2AlgEquiv, uqSl2AlgEquivAux, fromUqSl2TupleAux, simpleKInv_def]
@[simp] theorem uqSl2AlgEquiv_symm_e :
    (uqSl2AlgEquiv q).symm (e CartanDatum.sl2 q ()) = UqSl2.e q :=
  (uqSl2AlgEquiv q).symm_apply_eq.mpr (uqSl2AlgEquiv_e q).symm
@[simp] theorem uqSl2AlgEquiv_symm_f :
    (uqSl2AlgEquiv q).symm (f CartanDatum.sl2 q ()) = UqSl2.f q :=
  (uqSl2AlgEquiv q).symm_apply_eq.mpr (uqSl2AlgEquiv_f q).symm
@[simp] theorem uqSl2AlgEquiv_symm_k (y : ℤ) :
    (uqSl2AlgEquiv q).symm (k CartanDatum.sl2 q y) = ↑(UqSl2.kUnit q ^ y) := by
  rw [AlgEquiv.symm_apply_eq]
  simpa using (UqSl2.map_kUnit_zpow (uqSl2AlgEquiv q)
    (kUnitsHom CartanDatum.sl2 q (.ofAdd 1)) (by simp) y).symm

/-- Bialgebra (hence Hopf algebra) isomorphism
`UqSl2 q ≃ₐc[ℂ] QuantizedEnvelopingAlgebra CartanDatum.sl2 q` for `q ≠ 0`. -/
def uqSl2BialgEquiv [Fact (q ≠ 0)] :
    UqSl2 q ≃ₐc[ℂ] QuantizedEnvelopingAlgebra CartanDatum.sl2 q :=
  BialgEquiv.ofAlgEquiv (uqSl2AlgEquiv q)
    (by apply UqSl2.hom_ext <;> simp)
    (by apply UqSl2.hom_ext <;> simp [simpleK_def, simpleKInv_def])

@[simp] theorem uqSl2BialgEquiv_toAlgEquiv [Fact (q ≠ 0)] :
    (uqSl2BialgEquiv q).toAlgEquiv = uqSl2AlgEquiv q := (rfl)
@[simp] theorem uqSl2BialgEquiv_apply [Fact (q ≠ 0)] (x : UqSl2 q) :
    uqSl2BialgEquiv q x = uqSl2AlgEquiv q x := (rfl)
@[simp] theorem uqSl2BialgEquiv_symm_apply [Fact (q ≠ 0)]
    (x : QuantizedEnvelopingAlgebra CartanDatum.sl2 q) :
    (uqSl2BialgEquiv q).symm x = (uqSl2AlgEquiv q).symm x := (rfl)

end Sl2

end TauCeti.QuantizedEnvelopingAlgebra
