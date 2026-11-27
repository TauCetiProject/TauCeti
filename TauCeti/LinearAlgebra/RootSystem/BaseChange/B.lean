/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.BaseChange.Pi
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.B.Datum
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import TauCeti.Algebra.Algebra.Pi
import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.NonSimplyLaced

/-!
# Entrywise base change of the simply connected root datum of type `Bₙ`

This file extends `typeBSimplyConnectedRootDatum n` and `typeBSimplyConnectedBase n` entrywise to
an arbitrary characteristic-zero field `K` via `TauCeti.rootPairingBaseChange`, producing the
reduced crystallographic root system `typeBBaseChangeRootSystem K n` on `Fin n → K`, its Bourbaki
base `typeBBaseChangeBase K n` of Cartan type `B n`, and simple-coroot evaluation rules.

## References
* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Plate II.
-/

public section

namespace TauCeti.DynkinType

variable (K : Type*) [Field K] [CharZero K]

/-- Entrywise base-changed root system of type `Bₙ` on `Fin n → K`. -/
def typeBBaseChangeRootSystem (n : ℕ) :
    RootPairing (Fin (2 * n ^ 2)) K (Fin n → K) (Fin n → K) :=
  rootPairingBaseChange K (typeBSimplyConnectedRootDatum n)
    (fun x y ↦ toLinearMap_typeBSimplyConnectedRootDatum x y)

/-- The Bourbaki-numbered base of `typeBBaseChangeRootSystem K n`. -/
def typeBBaseChangeBase (n : ℕ) : (typeBBaseChangeRootSystem K n).Base :=
  rootPairingBaseChangeBase K (typeBSimplyConnectedRootDatum n)
    (fun x y ↦ toLinearMap_typeBSimplyConnectedRootDatum x y) (typeBSimplyConnectedBase n)

/-- `typeBBaseChangeRootSystem K n` is crystallographic. -/
instance instIsCrystallographicTypeBBaseChangeRootSystem (n : ℕ) :
    (typeBBaseChangeRootSystem K n).IsCrystallographic :=
  isCrystallographic_rootPairingBaseChange ..

/-- `typeBBaseChangeRootSystem K n` is reduced. -/
instance instIsReducedTypeBBaseChangeRootSystem (n : ℕ) :
    (typeBBaseChangeRootSystem K n).IsReduced := isReduced_rootPairingBaseChange K _ _

/-- Over a characteristic-zero field, the roots and coroots of `typeBBaseChangeRootSystem K n`
span `Fin n → K`. -/
instance instIsRootSystemTypeBBaseChangeRootSystem (n : ℕ) :
    (typeBBaseChangeRootSystem K n).IsRootSystem where
  span_root_eq_top := top_le_iff.mp <| by
    have hcard : Fintype.card (typeBBaseChangeBase K n).support = Module.finrank K (Fin n → K) := by
      rw [Fintype.card_coe, Module.finrank_fin_fun, typeBBaseChangeBase,
        support_rootPairingBaseChangeBase,
        (hasCartanType_typeBSimplyConnectedRootDatum n).card_support, DynkinType.rank_B]
    rw [← (typeBBaseChangeBase K n).linearIndepOn_root.span_eq_top_of_card_eq_finrank' hcard]
    exact Submodule.span_mono fun _ ⟨i, hi⟩ ↦ hi ▸ Set.mem_range_self (i : Fin (2 * n ^ 2))
  span_coroot_eq_top := span_range_coroot_rootPairingBaseChange_eq_top K _ _
    (corootSpan_typeBSimplyConnectedRootDatum_eq_top n)

/-- `typeBBaseChangeBase K n` has Cartan type `B n`. -/
theorem hasCartanType_typeBBaseChangeBase (n : ℕ) :
    HasCartanType (typeBBaseChangeRootSystem K n) (typeBBaseChangeBase K n) (.B n) := by
  obtain ⟨e, he⟩ := (hasCartanType_iff _ _).mp (hasCartanType_typeBSimplyConnectedRootDatum n)
  exact (hasCartanType_iff _ _).mpr ⟨(supportEquivRootPairingBaseChangeBase K _ _ _).trans e,
    fun i j ↦ (cartanMatrix_rootPairingBaseChangeBase K _ _ _ i j).trans (he _ _)⟩

/-- The bilinear pairing of `typeBBaseChangeRootSystem K n` is `dotProduct`. -/
@[simp] theorem toLinearMap_typeBBaseChangeRootSystem (n : ℕ) (x y : Fin n → K) :
    (typeBBaseChangeRootSystem K n).toLinearMap x y = x ⬝ᵥ y :=
  toLinearMap_rootPairingBaseChange K (typeBSimplyConnectedRootDatum n) _ x y

/-- Each root of `typeBBaseChangeRootSystem K n` is the entrywise cast of the integral root. -/
@[simp] theorem root_typeBBaseChangeRootSystem (n : ℕ) (i : Fin (2 * n ^ 2)) :
    (typeBBaseChangeRootSystem K n).root i =
      Pi.algebraMap (Fin n) ℤ K ((typeBSimplyConnectedRootDatum n).root i) :=
  root_rootPairingBaseChange K (typeBSimplyConnectedRootDatum n) _ i

/-- Each coroot of `typeBBaseChangeRootSystem K n` is the entrywise cast of the integral coroot. -/
@[simp] theorem coroot_typeBBaseChangeRootSystem (n : ℕ) (i : Fin (2 * n ^ 2)) :
    (typeBBaseChangeRootSystem K n).coroot i =
      Pi.algebraMap (Fin n) ℤ K ((typeBSimplyConnectedRootDatum n).coroot i) :=
  coroot_rootPairingBaseChange K (typeBSimplyConnectedRootDatum n) _ i

/-- An entrywise cast vector is a root of `typeBBaseChangeRootSystem K n` iff the integral vector
is a root of `typeBSimplyConnectedRootDatum n`. -/
theorem piAlgebraMap_mem_range_root_typeBBaseChangeRootSystem_iff (n : ℕ) (x : Fin n → ℤ) :
    Pi.algebraMap (Fin n) ℤ K x ∈ Set.range (typeBBaseChangeRootSystem K n).root ↔
      x ∈ Set.range (typeBSimplyConnectedRootDatum n).root :=
  piAlgebraMap_mem_range_root_rootPairingBaseChange_iff K (typeBSimplyConnectedRootDatum n) _ x

/-- `m ∈ (typeBBaseChangeBase K n).support` iff `(m : ℕ) < n`. -/
@[simp] theorem mem_support_typeBBaseChangeBase_iff (n : ℕ) (m : Fin (2 * n ^ 2)) :
    m ∈ (typeBBaseChangeBase K n).support ↔ (m : ℕ) < n := by
  rw [typeBBaseChangeBase, support_rootPairingBaseChangeBase, mem_typeBSimplyConnectedBase_support]

-- Not `@[simp]`: `RootPairing.coroot'` is an `abbrev`, so `simp` unfolds the LHS via
-- `LinearMap.flip_apply`, `coroot_typeBBaseChangeRootSystem`, and
-- `coroot_typeBSimpleIndex` (`simpNF`).
/-- Evaluating the `k`-th simple coroot of `typeBBaseChangeRootSystem K n` on `y` gives `y k`. -/
theorem coroot'_typeBBaseChangeRootSystem_simpleIndex (n : ℕ) (k : Fin n) (y : Fin n → K) :
    (typeBBaseChangeRootSystem K n).coroot' (typeBSimpleIndex n k) y = y k := by
  rw [RootPairing.coroot', LinearMap.flip_apply, toLinearMap_typeBBaseChangeRootSystem,
    coroot_typeBBaseChangeRootSystem, coroot_typeBSimpleIndex]
  have hsingle : Pi.algebraMap (Fin n) ℤ K (Pi.single k 1) = Pi.single k (1 : K) := by
    ext j; rcases eq_or_ne j k with rfl | hjk <;> simp [piAlgebraMap_apply, *]
  rw [hsingle, dotProduct_single, mul_one]

end TauCeti.DynkinType
