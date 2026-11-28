/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LFunctions.Zeros.OneSidedBound.PlaceOfInt
public import TauCeti.NumberTheory.Padics.Coupling.SelectedExponents
import TauCeti.NumberTheory.Padics.Coupling.ShortOrbits

/-!
# Near-pair couplings in cyclotomic place coordinates

For odd `e`, the partner with label `-p^e` is the `e`-fold translate by the label of `-p`.
Sparsity of the large-weight places then identifies each near pair as the unique shortest
odd coupling into its target from the selected sources.

The application is `New.Data.isCouplingFamily_of_isNearPair` in
`grh/src/New/Derivatives/Sharpness/Cases.lean` of [grh-lean](https://github.com/lsernau/grh-lean)
at commit `72fead1`.
-/

public section

namespace TauCeti.OneSidedBound.Parameters

/-- Chosen short odd steps between large-weight place labels form a coupling family.
Sparsity forbids two short positive translates by the label of `-p` from a large-weight
place back into the set. In particular this applies when the steps are near pairs, whose
lengths are less than half the cutoff. -/
theorem isCouplingFamily_placeOfInt_neg_pow (P : Parameters) (s : ℕ) (p : ℤ)
    {A B : Set (ZMod (P.q₁ s))ˣ} (e : A → ℕ) (hA : A ⊆ B) (he : ∀ v, Odd (e v))
    (hlt : ∀ v, e v < l₀ s) (hend : ∀ v, P.placeOfInt s (-(p ^ e v)) * v.val ∈ B)
    (hsparse : ∀ v ∈ B, ∀ ⦃i j : ℕ⦄, 0 < i → i < j → j < l₀ s →
      P.placeOfInt s (-p) ^ i * v ∈ B → P.placeOfInt s (-p) ^ j * v ∉ B) :
    IsCouplingFamily {j | Odd j} (fun j v ↦ P.placeOfInt s (-(p ^ j)) * v.val) e := by
  have hstep {j : ℕ} (hj : Odd j) : P.placeOfInt s (-p) ^ j = P.placeOfInt s (-(p ^ j)) := by
    rw [← P.placeOfInt_pow, hj.neg_pow]
  have hend' (v : A) : P.placeOfInt s (-p) ^ e v * v.val ∈ B := by
    rw [hstep (he v)]
    exact hend v
  have hf := isCouplingFamily_of_short_returns (P.placeOfInt s (-p))
    (S := {j | Odd j}) (by simp) e hA he hlt hend' hsparse
  refine ⟨he, fun {i j k} hk hle h ↦ hf.eq_of_exponent_le hk hle ?_⟩
  simpa only [smul_eq_mul, hstep hk, hstep (he i)] using h

end TauCeti.OneSidedBound.Parameters
