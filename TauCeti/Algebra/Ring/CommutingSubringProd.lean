/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Ring.Subring.Basic
public import Mathlib.Data.Finset.Piecewise
public import Mathlib.Data.Fintype.Pi
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Group.Submonoid.BigOperators
import Mathlib.Algebra.Module.Submodule.Basic
import Mathlib.GroupTheory.NoncommPiCoprod
import Mathlib.LinearAlgebra.Multilinear.Basic

/-!
# Products in pairwise commuting subrings and first-order deformation coefficients

Let `R` be a ring and `𝒜 : J → Subring R` be a finite family of pairwise commuting subrings of `R`.
Using `MonoidHom.noncommPiCoprod`, we define the product map `commutingProd h𝒜 : (∀ j, 𝒜 j) →* R`
and prove that any single factor can be moved to the right (`commutingProd_update`), so the product
is multilinear over finite sums (`commutingProd_sum`).

For elements `Nm j, der j ∈ 𝒜 j`, we define `firstOrderFamilyCoeff h𝒜 Nm der S` to be the product
`∏_{j ∈ S} der j * ∏_{j ∉ S} Nm j`, the coefficient of `∏_{j ∈ S} α j` in `∏ (Nm j + α j ∂ j)`.
We show that it commutes with any element commuting with every `𝒜 j`, that at `S = ∅` it equals the
sum of `ρ` over a finite product group `∀ j, Γ j` when `Nm j = ∑_{g : Γ j} ρ (Pi.mulSingle j g)`,
and that inserting `j ∉ S` replaces a single factor `Nm j` by `der j`.

## Main definitions and results

* `TauCeti.commutingProd`: product of elements from pairwise commuting subrings `𝒜 j`.
* `TauCeti.commutingProd_update`: pulling one factor of `commutingProd` to the right.
* `TauCeti.commutingProd_sum`: multilinearity of `commutingProd` over finite sums.
* `TauCeti.firstOrderFamilyCoeff`: the square-free coefficient `∏_{j ∈ S} der j ∏_{j ∉ S} Nm j`.
* `TauCeti.firstOrderFamilyCoeff_empty`: `firstOrderFamilyCoeff` at `∅` is the full group norm.
* `TauCeti.exists_firstOrderFamilyCoeff_eq_mul`: inserting `j ∉ S` replaces `Nm j` by `der j`.

## Provenance

Adapted from `grh-lean` (`https://github.com/lsernau/grh-lean`, commit
`72fead102f663d5c7a407964a13dc0cf9d977207`), file
`src/New/Congruences/FirstOrder/OnePrime.lean` (`New.Patching.commutingProd`,
`New.Patching.commutingProd_update`, `New.Patching.commutingProd_sum`, `New.Patching.familyCoeff`,
`New.Patching.commute_familyCoeff`, `New.Patching.familyCoeff_empty`,
`New.Patching.exists_familyCoeff_eq_mul`).
-/

public section

open Finset

namespace TauCeti

variable {J R : Type*} [Ring R]

/-- The product `x ↦ ∏ j, x j` of elements `x j ∈ 𝒜 j` of pairwise commuting subrings of `R`. -/
noncomputable def commutingProd [Finite J] {𝒜 : J → Subring R}
    (h𝒜 : ∀ i j : J, i ≠ j → ∀ a ∈ 𝒜 i, ∀ b ∈ 𝒜 j, Commute a b) : (∀ j : J, 𝒜 j) →* R :=
  let _ : Fintype J := Fintype.ofFinite J
  MonoidHom.noncommPiCoprod (fun j ↦ (𝒜 j).subtype.toMonoidHom)
    fun i j hij a b ↦ h𝒜 i j hij a a.property b b.property

/-- In a product of elements of pairwise commuting subrings, any single factor can be written
last. -/
theorem commutingProd_update [Finite J] [DecidableEq J] {𝒜 : J → Subring R}
    (h𝒜 : ∀ i j : J, i ≠ j → ∀ a ∈ 𝒜 i, ∀ b ∈ 𝒜 j, Commute a b) (x : ∀ j : J, 𝒜 j) (j : J)
    (a : 𝒜 j) :
    commutingProd h𝒜 (Function.update x j a) = commutingProd h𝒜 (Function.update x j 1) * a := by
  have split : Function.update x j a = Function.update x j 1 * Pi.mulSingle j a := by
    simpa [← Pi.mulSingle.eq_1] using Function.update_mul x 1 j 1 a
  rw [split, map_mul]
  simp [commutingProd]

/-- A product of finite sums of elements of pairwise commuting subrings expands as a sum of
products: `∏_j ∑_i x j i = ∑_f ∏_j x j (f j)`. -/
theorem commutingProd_sum [Fintype J] [DecidableEq J] {𝒜 : J → Subring R}
    (h𝒜 : ∀ i j : J, i ≠ j → ∀ a ∈ 𝒜 i, ∀ b ∈ 𝒜 j, Commute a b) {ι : J → Type*}
    [∀ j : J, Fintype (ι j)] (x : ∀ j : J, ι j → 𝒜 j) :
    commutingProd h𝒜 (fun j : J ↦ ∑ i : ι j, x j i) =
      ∑ f : (j : J) → ι j, commutingProd h𝒜 fun j : J ↦ x j (f j) := by
  let Φ : (∀ j : J, 𝒜 j) →* R := commutingProd h𝒜
  have last (y : ∀ j : J, 𝒜 j) (j : J) (a : 𝒜 j) :
      Φ (Function.update y j a) = Φ (Function.update y j 1) * a := commutingProd_update h𝒜 y j a
  have Φ_add (y : ∀ j : J, 𝒜 j) (j : J) (a b : 𝒜 j) : Φ (Function.update y j (a + b)) =
      Φ (Function.update y j a) + Φ (Function.update y j b) := by
    rw [last y j (a + b), last y j a, last y j b, Subring.coe_add, mul_add]
  have Φ_smul (y : ∀ j : J, 𝒜 j) (j : J) (r : ℕ) (a : 𝒜 j) :
      Φ (Function.update y j (r • a)) = r • Φ (Function.update y j a) := by
    rw [last y j (r • a), last y j a, AddSubgroupClass.coe_nsmul, mul_smul_comm]
  let M : MultilinearMap (RingHom.id ℕ) (fun j : J ↦ 𝒜 j) R := .mk' Φ Φ_add Φ_smul
  exact M.map_sum x

/-- The coefficient `∏_{j ∈ S} der j * ∏_{j ∉ S} Nm j` of `∏_{j ∈ S} α j` in the first-order
deformation `∏ (Nm j + α j * der j)`, where `Nm j, der j ∈ 𝒜 j`. -/
noncomputable def firstOrderFamilyCoeff [Finite J] [DecidableEq J] {𝒜 : J → Subring R}
    (h𝒜 : ∀ i j : J, i ≠ j → ∀ a ∈ 𝒜 i, ∀ b ∈ 𝒜 j, Commute a b) (Nm der : ∀ j : J, 𝒜 j)
    (S : Finset J) : R :=
  commutingProd h𝒜 (S.piecewise der Nm)

/-- An element commuting with every subring `𝒜 j` commutes with `firstOrderFamilyCoeff h𝒜 Nm der S`
for every subset `S`. -/
theorem commute_firstOrderFamilyCoeff [Finite J] [DecidableEq J] {𝒜 : J → Subring R}
    (h𝒜 : ∀ i j : J, i ≠ j → ∀ a ∈ 𝒜 i, ∀ b ∈ 𝒜 j, Commute a b) (Nm der : ∀ j : J, 𝒜 j)
    {t : R} (ht : ∀ j : J, ∀ a ∈ 𝒜 j, Commute t a) (S : Finset J) :
    Commute t (firstOrderFamilyCoeff h𝒜 Nm der S) := by
  let _ : Fintype J := Fintype.ofFinite J
  unfold firstOrderFamilyCoeff commutingProd
  exact MonoidHom.commute_noncommPiCoprod _ (fun j (a : 𝒜 j) ↦ ht j a a.property)
    (S.piecewise der Nm)

/-- When `Nm j` is the sum of `ρ` over the `j`-th factor `Γ j` of a finite product group,
`firstOrderFamilyCoeff h𝒜 Nm der ∅` equals the sum of `ρ` over the entire product group. -/
theorem firstOrderFamilyCoeff_empty [Fintype J] [DecidableEq J] {Γ : J → Type*}
    [∀ j : J, Group (Γ j)] [∀ j : J, Fintype (Γ j)] (ρ : (∀ j : J, Γ j) →* R) {𝒜 : J → Subring R}
    (h𝒜 : ∀ i j : J, i ≠ j → ∀ a ∈ 𝒜 i, ∀ b ∈ 𝒜 j, Commute a b)
    (hρ : ∀ (j : J) (g : Γ j), ρ (Pi.mulSingle j g) ∈ 𝒜 j) {Nm : ∀ j : J, 𝒜 j}
    (h_norm : ∀ j : J, (Nm j : R) = ∑ g : Γ j, ρ (Pi.mulSingle j g)) (der : ∀ j : J, 𝒜 j) :
    firstOrderFamilyCoeff h𝒜 Nm der ∅ = ∑ g : (j : J) → Γ j, ρ g := by
  let r (j : J) (g : Γ j) : 𝒜 j := ⟨ρ (Pi.mulSingle j g), hρ j g⟩
  have norm_eq : Nm = fun j ↦ ∑ g : Γ j, r j g := funext fun j ↦ Subtype.ext (by simp [h_norm, r])
  have prod_single (g : ∀ j : J, Γ j) : commutingProd h𝒜 (fun j ↦ r j (g j)) = ρ g := by
    let _ : Fintype J := Fintype.ofFinite J
    exact DFunLike.congr_fun (MonoidHom.noncommPiCoprodEquiv.right_inv ρ) g
  calc firstOrderFamilyCoeff h𝒜 Nm der ∅ = commutingProd h𝒜 fun j ↦ ∑ g : Γ j, r j g := by
        rw [firstOrderFamilyCoeff, piecewise_empty, norm_eq]
    _ = ∑ g : (j : J) → Γ j, commutingProd h𝒜 fun j ↦ r j (g j) := commutingProd_sum h𝒜 r
    _ = ∑ g : (j : J) → Γ j, ρ g := sum_congr rfl fun g _ ↦ prod_single g

/-- For `j ∉ S`, `firstOrderFamilyCoeff` at `S` and `insert j S` share a common left factor `N'`,
differing only in their right factor (`Nm j` versus `der j`). -/
theorem exists_firstOrderFamilyCoeff_eq_mul [Finite J] [DecidableEq J] {𝒜 : J → Subring R}
    (h𝒜 : ∀ i j : J, i ≠ j → ∀ a ∈ 𝒜 i, ∀ b ∈ 𝒜 j, Commute a b) (Nm der : ∀ j : J, 𝒜 j)
    {j : J} {S : Finset J} (hj : j ∉ S) :
    ∃ N' : R,
      firstOrderFamilyCoeff h𝒜 Nm der S = N' * Nm j ∧
      firstOrderFamilyCoeff h𝒜 Nm der (insert j S) = N' * der j := by
  refine ⟨commutingProd h𝒜 (Function.update (S.piecewise der Nm) j 1), ?_, ?_⟩
  · rw [← commutingProd_update, ← piecewise_eq_of_notMem S der Nm hj, Function.update_eq_self,
      firstOrderFamilyCoeff]
  · rw [← commutingProd_update, firstOrderFamilyCoeff, piecewise_insert]

end TauCeti
