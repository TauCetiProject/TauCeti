/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.BaseChange.Restrict.Base
public import TauCeti.LinearAlgebra.RootSystem.Chamber

/-!
# Regular weights and dominant chambers under scalar restriction

Under scalar restriction of a balanced root pairing `P` to a subfield `K` (and in particular for
`K = L`), weight regularity and membership in the closed and open dominant chambers in
`P.restrictScalars' K` agree with those in `P`.

## Main results

* `RootPairing.isRegularWeight_restrictScalars'_iff`,
  `RootPairing.mem_dominantChamber_restrictScalars'_iff_of_nonneg_iff`, and
  `RootPairing.mem_openDominantChamber_restrictScalars'_iff_of_pos_iff`: regularity and chamber
  membership in `P.restrictScalars' K` agree with those in `P`.
* `RootPairing.mem_dominantChamber_restrictScalars'_self_iff` and
  `RootPairing.mem_openDominantChamber_restrictScalars'_self_iff`: the `K = L` specialization.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Ch. VI, §1.
* M. Demazure, A. Grothendieck (eds.), *Schémas en groupes III* (SGA 3), Exposé XXI, §§1, 6.
-/

public section

namespace RootPairing

open Set Submodule TauCeti

section RestrictScalars

variable {ι L M N : Type*} [Field L] [AddCommGroup M] [AddCommGroup N] [Module L M] [Module L N]
  (P : RootPairing ι L M N) (K : Type*) [Field K] [Algebra K L]
  [Module K M] [Module K N] [IsScalarTower K L M] [IsScalarTower K L N]
  [P.IsBalanced] [P.IsValuedIn K]

/-- Weight regularity in `P.restrictScalars' K` agrees with weight regularity in `P`. -/
@[simp]
theorem isRegularWeight_restrictScalars'_iff (x : span K (range P.root)) :
    (P.restrictScalars' K).IsRegularWeight x ↔ P.IsRegularWeight (x : M) := by
  simp only [isRegularWeight_iff, ← P.algebraMap_restrictScalars'_coroot'_apply K, ne_eq,
    FaithfulSMul.algebraMap_eq_zero_iff]

/-- When `algebraMap K L` preserves and reflects nonnegativity (for example when `K` and `L` are
linearly ordered fields and `algebraMap K L` is order-preserving, or when `K = L`), membership in
the closed dominant chamber of `P.restrictScalars' K` agrees with that in `P`. -/
theorem mem_dominantChamber_restrictScalars'_iff_of_nonneg_iff [Preorder K] [Preorder L]
    (h : ∀ a : K, 0 ≤ algebraMap K L a ↔ 0 ≤ a) (b : P.Base) (x : span K (range P.root)) :
    x ∈ dominantChamber (P.restrictScalars' K) (b.restrictScalars' K) ↔
      (x : M) ∈ dominantChamber P b := by
  simp only [mem_dominantChamber, Base.support_restrictScalars',
    ← P.algebraMap_restrictScalars'_coroot'_apply K, h]

/-- When `algebraMap K L` preserves and reflects strict positivity, membership in the open dominant
chamber of `P.restrictScalars' K` agrees with that in `P`. -/
theorem mem_openDominantChamber_restrictScalars'_iff_of_pos_iff [Preorder K] [Preorder L]
    (h : ∀ a : K, 0 < algebraMap K L a ↔ 0 < a) (b : P.Base) (x : span K (range P.root)) :
    x ∈ openDominantChamber (P.restrictScalars' K) (b.restrictScalars' K) ↔
      (x : M) ∈ openDominantChamber P b := by
  simp only [mem_openDominantChamber, Base.support_restrictScalars',
    ← P.algebraMap_restrictScalars'_coroot'_apply K, h]

end RestrictScalars

section SelfRestrictScalars

variable {ι L M N : Type*} [Field L] [AddCommGroup M] [AddCommGroup N] [Module L M] [Module L N]
  (P : RootPairing ι L M N) [P.IsBalanced] (b : P.Base)

/-- Membership in the closed dominant chamber of `P.restrictScalars' L` agrees with that in `P`. -/
theorem mem_dominantChamber_restrictScalars'_self_iff [Preorder L] (x : span L (range P.root)) :
    x ∈ dominantChamber (P.restrictScalars' L) (b.restrictScalars' L) ↔
      (x : M) ∈ dominantChamber P b :=
  P.mem_dominantChamber_restrictScalars'_iff_of_nonneg_iff L (fun _ ↦ Iff.rfl) b x

/-- Membership in the open dominant chamber of `P.restrictScalars' L` agrees with that in `P`. -/
theorem mem_openDominantChamber_restrictScalars'_self_iff [Preorder L]
    (x : span L (range P.root)) :
    x ∈ openDominantChamber (P.restrictScalars' L) (b.restrictScalars' L) ↔
      (x : M) ∈ openDominantChamber P b :=
  P.mem_openDominantChamber_restrictScalars'_iff_of_pos_iff L (fun _ ↦ Iff.rfl) b x

end SelfRestrictScalars

end RootPairing
