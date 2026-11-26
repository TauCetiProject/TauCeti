/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.CartanInvolution.RestrictedRoot.RootSystem
public import TauCeti.LinearAlgebra.RootSystem.Chamber
public import TauCeti.LinearAlgebra.RootSystem.Weyl.Bases
public import Mathlib.LinearAlgebra.RootSystem.BaseExists

/-!
# Positive restricted root systems, Weyl chambers, and simple restricted roots

Let `θ` be a Cartan involution of a real semisimple Lie algebra `𝔤₀` and `𝔞` a maximal
abelian subspace of its `-1`-eigenspace `𝔭`. Any element `H₀ ∈ 𝔞` avoiding every root
hyperplane `ker λ` (`λ ∈ Σ`) partitions the restricted roots `Σ` into positive roots
`Σ⁺(H₀) = {λ ∈ Σ | λ(H₀) > 0}` (`Submodule.positiveRestrictedRoots`) and negative roots
`-Σ⁺(H₀)`, and determines the positive restricted root space
`𝔫 = ⨁_{λ ∈ Σ⁺} 𝔤_λ` (`Submodule.positiveRestrictedRootSpace`).

Passing to the indivisible reduced subsystem `Σ_indiv` (`indivisibleRestrictedRootPairing`), the
open Weyl chambers of `Σ` in `𝔞` are the open dominant chambers
`(indivisibleRestrictedRootPairing).flip.openDominantChamber b.flip` indexed by bases `b` of
`Σ_indiv`. This file establishes:

* existence of regular elements in `𝔞` (`Submodule.exists_regular_restrictedRoots`) and hence of
  positive restricted root systems;
* the explicit bijection between positive restricted root systems `Σ⁺` and bases `b` of
  `Σ_indiv` (`LieEquiv.IsCartanInvolution.baseEquivPositiveRestrictedRootSystem`), with every `H₀`
  in the open dominant chamber of `b.flip` in `𝔞` inducing `Σ⁺(b)`;
* the basis of simple restricted roots `Π` (`RootPairing.Base.toWeightBasis`) such that every
  restricted root is an integer linear combination of `Π` with all coefficients `≥ 0` (when
  `λ ∈ Σ⁺`) or all coefficients `≤ 0` (when `-λ ∈ Σ⁺`);
* the transitive and simply transitive action of the restricted Weyl group `W(Σ)` on positive
  restricted root systems
  (`LieEquiv.IsCartanInvolution.existsUnique_weylGroup_smul_positiveRestrictedRoots`), obtained by
  transporting `RootPairing.Base.existsUnique_map_eq` along `restrictedWeylGroupEquiv`.

## Main definitions

* `Submodule.positiveRestrictedRoots`: the positive restricted roots `{λ ∈ Σ | 0 < λ(H₀)}`
  associated to `H₀ ∈ 𝔞`.
* `Submodule.positiveRestrictedRootSpace`: the sum `⨆ λ ∈ Σ⁺(H₀), 𝔤_λ` of the positive
  restricted root spaces.
* `Submodule.IsPositiveRestrictedRootSystem`: predicate that `S ⊆ Σ` arises from some regular
  element `H₀ ∈ 𝔞`.
* `LieEquiv.IsCartanInvolution.positiveRestrictedRootsOfBase`: the positive restricted root system
  `Σ ∩ posRootCone(b)` induced by a base `b` of `Σ_indiv`.
* `LieEquiv.IsCartanInvolution.baseEquivPositiveRestrictedRootSystem`: the equivalence between bases
  of `Σ_indiv` and positive restricted root systems.

## Main results

* `Submodule.exists_regular_restrictedRoots`: there exists `H₀ ∈ 𝔞` on which no restricted root
  vanishes.
* `positiveRestrictedRootsOfBase_eq_positiveRestrictedRoots_of_mem_openDominantChamber`: every
  `H₀` in the open dominant chamber of `b.flip` induces `Σ⁺(b)`.
* `LieEquiv.IsCartanInvolution.exists_int_nonneg_or_nonpos_of_mem_restrictedRoots`: every
  restricted root is a `ℤ`-linear combination of the simple restricted roots with all coefficients
  `≥ 0` or all `≤ 0`.
* `LieEquiv.IsCartanInvolution.existsUnique_weylGroup_smul_positiveRestrictedRoots`: `W(Σ)` acts
  simply transitively on the positive restricted root systems.

## References

* A. W. Knapp, *Lie Groups Beyond an Introduction*, 2nd ed., Chapter VI, §5.
* S. Helgason, *Differential Geometry, Lie Groups, and Symmetric Spaces*, Chapter VII, §2.
-/

public section

open LieAlgebra LieModule Module

namespace Submodule

section Positive

variable {R L : Type*} [CommRing R] [LT R] [LieRing L] [LieAlgebra R L]

/-- The **positive restricted roots** defined by `H₀ ∈ 𝔞`: those restricted roots `λ ∈ Σ`
with `0 < λ(H₀)`. -/
def positiveRestrictedRoots (𝔞 : Submodule R L) (H₀ : 𝔞) : Set (Dual R 𝔞) :=
  {μ ∈ 𝔞.restrictedRoots | 0 < μ H₀}

/-- The **positive restricted root space** defined by `H₀ ∈ 𝔞`: the sum
`⨆ λ ∈ Σ⁺(H₀), 𝔤_λ`. -/
def positiveRestrictedRootSpace (𝔞 : Submodule R L) (H₀ : 𝔞) : Submodule R L :=
  ⨆ μ ∈ 𝔞.positiveRestrictedRoots H₀, 𝔞.restrictedRootSpace μ

/-- Predicate that a subset `S ⊆ 𝔞*` is the system of **positive restricted roots** cut out by
some regular element `H₀ ∈ 𝔞`. -/
def IsPositiveRestrictedRootSystem (𝔞 : Submodule R L) (S : Set (Dual R 𝔞)) : Prop :=
  ∃ H₀ : 𝔞,
    (∀ μ ∈ 𝔞.restrictedRoots, μ H₀ ≠ 0) ∧ S = 𝔞.positiveRestrictedRoots H₀

variable {𝔞 : Submodule R L} {H₀ : 𝔞} {μ : Dual R 𝔞}

@[simp]
theorem mem_positiveRestrictedRoots :
    μ ∈ 𝔞.positiveRestrictedRoots H₀ ↔ μ ∈ 𝔞.restrictedRoots ∧ 0 < μ H₀ :=
  Iff.rfl

/-- Every positive restricted root is a restricted root. -/
theorem positiveRestrictedRoots_subset :
    𝔞.positiveRestrictedRoots H₀ ⊆ 𝔞.restrictedRoots :=
  fun _ h ↦ h.left

/-- A positive restricted root pairs positively with `H₀`. -/
theorem pos_of_mem_positiveRestrictedRoots (hμ : μ ∈ 𝔞.positiveRestrictedRoots H₀) :
    0 < μ H₀ :=
  hμ.right

/-- Every positive restricted root is nonzero. -/
theorem ne_zero_of_mem_positiveRestrictedRoots (hμ : μ ∈ 𝔞.positiveRestrictedRoots H₀) :
    μ ≠ 0 :=
  (mem_restrictedRoots.mp hμ.left).left

/-- If `R` is a domain and `L` is torsion-free and Noetherian over `R`, there are finitely many
positive restricted roots. -/
theorem finite_positiveRestrictedRoots [IsDomain R] [IsTorsionFree R L] [IsNoetherian R L] :
    (𝔞.positiveRestrictedRoots H₀).Finite :=
  finite_restrictedRoots.subset positiveRestrictedRoots_subset

/-- The zero subspace has no positive restricted roots. -/
@[simp]
theorem positiveRestrictedRoots_bot (H : (⊥ : Submodule R L)) :
    (⊥ : Submodule R L).positiveRestrictedRoots H = ∅ := by
  simp [positiveRestrictedRoots]

/-- Every positive restricted root space lies in `positiveRestrictedRootSpace`. -/
theorem restrictedRootSpace_le_positiveRestrictedRootSpace
    (hμ : μ ∈ 𝔞.positiveRestrictedRoots H₀) :
    𝔞.restrictedRootSpace μ ≤ 𝔞.positiveRestrictedRootSpace H₀ :=
  le_biSup (fun ν ↦ 𝔞.restrictedRootSpace ν) hμ

/-- Unfolding lemma for `positiveRestrictedRootSpace`. -/
theorem positiveRestrictedRootSpace_def :
    𝔞.positiveRestrictedRootSpace H₀ =
      ⨆ μ ∈ 𝔞.positiveRestrictedRoots H₀, 𝔞.restrictedRootSpace μ :=
  (rfl)

/-- `positiveRestrictedRootSpace` is bounded by `N` iff each positive restricted root space is
bounded by `N`. -/
theorem positiveRestrictedRootSpace_le_iff {N : Submodule R L} :
    𝔞.positiveRestrictedRootSpace H₀ ≤ N ↔
      ∀ μ ∈ 𝔞.positiveRestrictedRoots H₀, 𝔞.restrictedRootSpace μ ≤ N := by
  rw [positiveRestrictedRootSpace_def, iSup₂_le_iff]

theorem isPositiveRestrictedRootSystem_iff {S : Set (Dual R 𝔞)} :
    𝔞.IsPositiveRestrictedRootSystem S ↔
      ∃ H₀ : 𝔞,
        (∀ μ ∈ 𝔞.restrictedRoots, μ H₀ ≠ 0) ∧
          S = 𝔞.positiveRestrictedRoots H₀ :=
  Iff.rfl

/-- Every member of a positive restricted root system is a restricted root. -/
theorem IsPositiveRestrictedRootSystem.subset {S : Set (Dual R 𝔞)}
    (hS : 𝔞.IsPositiveRestrictedRootSystem S) :
    S ⊆ 𝔞.restrictedRoots := by
  obtain ⟨_, _, rfl⟩ := hS
  exact positiveRestrictedRoots_subset

/-- A positive restricted root system is finite under domain, torsion-free, and Noetherian
hypotheses. -/
theorem IsPositiveRestrictedRootSystem.finite [IsDomain R] [IsTorsionFree R L] [IsNoetherian R L]
    {S : Set (Dual R 𝔞)} (hS : 𝔞.IsPositiveRestrictedRootSystem S) : S.Finite :=
  finite_restrictedRoots.subset hS.subset

end Positive

section RegularExists

/-- **Existence of regular elements in `𝔞`**: over an infinite domain `R`, if `L` is
torsion-free and Noetherian over `R`, there exists `H₀ ∈ 𝔞` such that `λ(H₀) ≠ 0` for every
restricted root `λ ∈ Σ`. -/
theorem exists_regular_restrictedRoots {R L : Type*} [CommRing R] [IsDomain R] [Infinite R]
    [LieRing L] [LieAlgebra R L] [IsTorsionFree R L] [IsNoetherian R L] (𝔞 : Submodule R L) :
    ∃ H₀ : 𝔞, ∀ μ ∈ 𝔞.restrictedRoots, μ H₀ ≠ 0 := by
  classical
  have hex : ∀ s : Finset (Dual R 𝔞), (∀ μ ∈ s, μ ≠ 0) →
      ∃ H₀ : 𝔞, ∀ μ ∈ s, μ H₀ ≠ 0 := by
    intro s hs
    induction s using Finset.induction with
    | empty => exact ⟨0, fun _ h ↦ absurd h (Finset.notMem_empty _)⟩
    | insert μ s hμ ih =>
      obtain ⟨y, hy⟩ := ih fun ν hν ↦ hs ν (Finset.mem_insert_of_mem hν)
      obtain ⟨x, hx⟩ := DFunLike.ne_iff.mp (hs μ (Finset.mem_insert_self μ s))
      have hfin : (⋃ ν ∈ insert μ s, {t : R | ν (y + t • x) = 0}).Finite :=
        (insert μ s).finite_toSet.biUnion fun ν hν ↦
          Set.Subsingleton.finite fun t₁ ht₁ t₂ ht₂ ↦ by
            simp only [Set.mem_ofPred_eq, map_add, map_smul, smul_eq_mul] at ht₁ ht₂
            have hsub : (t₁ - t₂) * ν x = 0 := by linear_combination ht₁ - ht₂
            rcases mul_eq_zero.mp hsub with h | h
            · exact sub_eq_zero.mp h
            · exfalso
              rcases Finset.mem_insert.mp hν with rfl | hνs
              · exact hx h
              · exact hy ν hνs (by simpa [h] using ht₁)
      obtain ⟨t, _, ht⟩ := Set.infinite_univ.exists_notMem_finite hfin
      exact ⟨y + t • x, fun ν hν h0 ↦ ht (Set.mem_biUnion hν h0)⟩
  obtain ⟨H₀, hH₀⟩ := hex (finite_restrictedRoots (𝔞 := 𝔞)).toFinset fun μ hμ ↦
    (mem_restrictedRoots.mp ((finite_restrictedRoots (𝔞 := 𝔞)).mem_toFinset.mp hμ)).left
  exact ⟨H₀, fun μ hμ ↦ hH₀ μ ((finite_restrictedRoots (𝔞 := 𝔞)).mem_toFinset.mpr hμ)⟩

/-- Over an infinite ordered domain `R`, if `L` is torsion-free and Noetherian over `R`, there
exists at least one positive restricted root system for `𝔞`. -/
theorem exists_isPositiveRestrictedRootSystem {R L : Type*} [CommRing R] [IsDomain R]
    [Infinite R] [LT R] [LieRing L] [LieAlgebra R L] [IsTorsionFree R L] [IsNoetherian R L]
    (𝔞 : Submodule R L) :
    ∃ S : Set (Dual R 𝔞), 𝔞.IsPositiveRestrictedRootSystem S := by
  obtain ⟨H₀, hreg⟩ := 𝔞.exists_regular_restrictedRoots
  exact ⟨𝔞.positiveRestrictedRoots H₀, H₀, hreg, rfl⟩

end RegularExists

section Ordered

variable {R L : Type*} [CommRing R] [PartialOrder R] [IsOrderedAddMonoid R] [LieRing L]
  [LieAlgebra R L] {𝔞 : Submodule R L} {H₀ : 𝔞} {μ ν : Dual R 𝔞}

/-- Positive restricted roots are closed under sums that remain restricted roots. -/
theorem add_mem_positiveRestrictedRoots (hμ : μ ∈ 𝔞.positiveRestrictedRoots H₀)
    (hν : ν ∈ 𝔞.positiveRestrictedRoots H₀) (hadd : μ + ν ∈ 𝔞.restrictedRoots) :
    μ + ν ∈ 𝔞.positiveRestrictedRoots H₀ :=
  ⟨hadd, by simpa only [LinearMap.add_apply] using add_pos hμ.right hν.right⟩

/-- A positive restricted root system is closed under sums that remain restricted roots. -/
theorem IsPositiveRestrictedRootSystem.add_mem {S : Set (Dual R 𝔞)}
    (hS : 𝔞.IsPositiveRestrictedRootSystem S) (hμ : μ ∈ S) (hν : ν ∈ S)
    (hadd : μ + ν ∈ 𝔞.restrictedRoots) : μ + ν ∈ S := by
  obtain ⟨_, _, rfl⟩ := hS
  exact add_mem_positiveRestrictedRoots hμ hν hadd

/-- No positive restricted root system contains both `λ` and `-λ`. -/
theorem neg_notMem_positiveRestrictedRoots_of_mem
    (hμ : μ ∈ 𝔞.positiveRestrictedRoots H₀) :
    -μ ∉ 𝔞.positiveRestrictedRoots H₀ := by
  intro hneg
  exact hμ.right.not_gt (by simpa only [LinearMap.neg_apply, neg_pos] using hneg.right)

/-- A positive restricted root system cannot contain both `λ` and `-λ`. -/
theorem IsPositiveRestrictedRootSystem.neg_notMem_of_mem {S : Set (Dual R 𝔞)}
    (hS : 𝔞.IsPositiveRestrictedRootSystem S) (hμ : μ ∈ S) : -μ ∉ S := by
  obtain ⟨_, _, rfl⟩ := hS
  exact neg_notMem_positiveRestrictedRoots_of_mem hμ

/-- `Σ⁺(H₀)` and `-Σ⁺(H₀)` are disjoint. -/
theorem disjoint_positiveRestrictedRoots_neg :
    Disjoint (𝔞.positiveRestrictedRoots H₀)
      (Neg.neg '' 𝔞.positiveRestrictedRoots H₀) := by
  rw [Set.disjoint_left]
  rintro μ hμ ⟨ν, hν, rfl⟩
  exact neg_notMem_positiveRestrictedRoots_of_mem hν hμ

/-- A positive restricted root system is disjoint from its negative. -/
theorem IsPositiveRestrictedRootSystem.disjoint_neg {S : Set (Dual R 𝔞)}
    (hS : 𝔞.IsPositiveRestrictedRootSystem S) : Disjoint S (Neg.neg '' S) := by
  obtain ⟨_, _, rfl⟩ := hS
  exact disjoint_positiveRestrictedRoots_neg

end Ordered

section LinearOrdered

variable {R L : Type*} [CommRing R] [LinearOrder R] [IsOrderedAddMonoid R] [LieRing L]
  [LieAlgebra R L] {θ : L ≃ₗ⁅R⁆ L} {𝔞 : Submodule R L}

/-- For a regular `H₀ ∈ 𝔞` and `λ ∈ Σ`, `-λ ∈ Σ⁺(H₀)` iff
`λ ∉ Σ⁺(H₀)`. -/
theorem neg_mem_positiveRestrictedRoots_iff_notMem (h𝔞 : 𝔞 ≤ θ.cartanP) {H₀ : 𝔞}
    (hreg : ∀ μ ∈ 𝔞.restrictedRoots, μ H₀ ≠ 0) {μ : Dual R 𝔞}
    (hμ : μ ∈ 𝔞.restrictedRoots) :
    -μ ∈ 𝔞.positiveRestrictedRoots H₀ ↔ μ ∉ 𝔞.positiveRestrictedRoots H₀ := by
  have hneg : -μ ∈ 𝔞.restrictedRoots := (LieEquiv.neg_mem_restrictedRoots_iff h𝔞).mpr hμ
  simp only [mem_positiveRestrictedRoots, hμ, hneg, true_and, LinearMap.neg_apply, neg_pos]
  exact ⟨fun h hpos ↦ hpos.not_gt h, fun h ↦ lt_of_le_of_ne (not_lt.mp h) (hreg μ hμ)⟩

/-- For any positive restricted root system `S` and `λ ∈ Σ`, `-λ ∈ S` iff `λ ∉ S`. -/
theorem IsPositiveRestrictedRootSystem.neg_mem_iff_notMem (h𝔞 : 𝔞 ≤ θ.cartanP)
    {S : Set (Dual R 𝔞)} (hS : 𝔞.IsPositiveRestrictedRootSystem S) {μ : Dual R 𝔞}
    (hμ : μ ∈ 𝔞.restrictedRoots) :
    -μ ∈ S ↔ μ ∉ S := by
  obtain ⟨H₀, hreg, rfl⟩ := hS
  exact neg_mem_positiveRestrictedRoots_iff_notMem h𝔞 hreg hμ

/-- For any positive restricted root system `S` and `λ ∈ Σ`, either `λ ∈ S` or
`-λ ∈ S`. -/
theorem IsPositiveRestrictedRootSystem.mem_or_neg_mem (h𝔞 : 𝔞 ≤ θ.cartanP)
    {S : Set (Dual R 𝔞)} (hS : 𝔞.IsPositiveRestrictedRootSystem S) {μ : Dual R 𝔞}
    (hμ : μ ∈ 𝔞.restrictedRoots) :
    μ ∈ S ∨ -μ ∈ S := by
  rw [hS.neg_mem_iff_notMem h𝔞 hμ]
  exact em _

/-- For a regular `H₀ ∈ 𝔞`, `Σ⁺(H₀) ∪ (-Σ⁺(H₀)) = Σ`. -/
theorem positiveRestrictedRoots_union_neg (h𝔞 : 𝔞 ≤ θ.cartanP) {H₀ : 𝔞}
    (hreg : ∀ μ ∈ 𝔞.restrictedRoots, μ H₀ ≠ 0) :
    𝔞.positiveRestrictedRoots H₀ ∪ Neg.neg '' 𝔞.positiveRestrictedRoots H₀ =
      𝔞.restrictedRoots := by
  ext μ
  constructor
  · rintro (hμ | ⟨ν, hν, rfl⟩)
    · exact hμ.left
    · exact (LieEquiv.neg_mem_restrictedRoots_iff h𝔞).mpr hν.left
  · intro hμ
    by_cases hpos : μ ∈ 𝔞.positiveRestrictedRoots H₀
    · exact Or.inl hpos
    · refine Or.inr ⟨-μ, ?_, neg_neg μ⟩
      exact (neg_mem_positiveRestrictedRoots_iff_notMem h𝔞 hreg hμ).mpr hpos

/-- Every positive restricted root system partitions `Σ` as `S ∪ (-S)`. -/
theorem IsPositiveRestrictedRootSystem.union_neg (h𝔞 : 𝔞 ≤ θ.cartanP)
    {S : Set (Dual R 𝔞)} (hS : 𝔞.IsPositiveRestrictedRootSystem S) :
    S ∪ Neg.neg '' S = 𝔞.restrictedRoots := by
  obtain ⟨H₀, hreg, rfl⟩ := hS
  exact positiveRestrictedRoots_union_neg h𝔞 hreg

/-- Half the restricted roots are positive: `2 * |Σ⁺| = |Σ|`. -/
theorem IsPositiveRestrictedRootSystem.two_mul_ncard [IsDomain R] [IsTorsionFree R L]
    [IsNoetherian R L] (h𝔞 : 𝔞 ≤ θ.cartanP) {S : Set (Dual R 𝔞)}
    (hS : 𝔞.IsPositiveRestrictedRootSystem S) :
    2 * S.ncard = 𝔞.restrictedRoots.ncard := by
  have hfin : S.Finite := hS.finite
  have hneg_fin : (Neg.neg '' S).Finite := hfin.image _
  have hcard : (Neg.neg '' S).ncard = S.ncard :=
    Set.ncard_image_of_injective S neg_injective
  calc
    2 * S.ncard = S.ncard + S.ncard := two_mul _
    _ = S.ncard + (Neg.neg '' S).ncard := by rw [hcard]
    _ = (S ∪ Neg.neg '' S).ncard := (Set.ncard_union_eq hS.disjoint_neg hfin hneg_fin).symm
    _ = 𝔞.restrictedRoots.ncard := by rw [hS.union_neg h𝔞]

end LinearOrdered

end Submodule

namespace LieEquiv.IsCartanInvolution

open Submodule

section BasesAndChambers

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L] {θ : L ≃ₗ⁅ℝ⁆ L}
  {𝔞 : Submodule ℝ L} (hθ : θ.IsCartanInvolution) (h𝔞 : θ.IsMaximalAbelianInP 𝔞)

theorem isRegularWeight_flip_indivisible_iff (H : 𝔞) :
    (hθ.indivisibleRestrictedRootPairing h𝔞).flip.IsRegularWeight H ↔
      ∀ μ ∈ 𝔞.restrictedRoots, μ H ≠ 0 := by
  rw [RootPairing.isRegularWeight_iff]
  constructor
  · intro h μ hμ
    rcases hθ.mem_indivisibleRestrictedRoots_or_exists_eq_two_smul h𝔞 hμ with
      hindiv | ⟨γ, hγ, rfl⟩
    · simpa only [indivisibleRestrictedRootPairing_flip_coroot'_apply] using
        h ⟨μ, hindiv⟩
    · simpa only [indivisibleRestrictedRootPairing_flip_coroot'_apply, LinearMap.smul_apply,
        smul_eq_mul, mul_ne_zero_iff, OfNat.ofNat_ne_zero, ne_eq, not_false_eq_true,
        true_and] using h ⟨γ, hγ⟩
  · intro h γ
    rw [indivisibleRestrictedRootPairing_flip_coroot'_apply]
    exact h γ.val (mem_indivisibleRestrictedRoots.mp γ.property).left

/-- Membership in the open dominant chamber of `b.flip` inside `𝔞` means every simple
restricted root is strictly positive on `H`. -/
theorem mem_openDominantChamber_flip_indivisible_iff
    (b : (hθ.indivisibleRestrictedRootPairing h𝔞).Base) (H : 𝔞) :
    H ∈ (hθ.indivisibleRestrictedRootPairing h𝔞).flip.openDominantChamber b.flip ↔
      ∀ α ∈ b.support, 0 < (α : Dual ℝ 𝔞) H := by
  simp only [RootPairing.mem_openDominantChamber, RootPairing.Base.flip_support,
    indivisibleRestrictedRootPairing_flip_coroot'_apply]

/-- Membership in the closed dominant chamber of `b.flip` inside `𝔞` means every simple
restricted root is nonnegative on `H`. -/
theorem mem_dominantChamber_flip_indivisible_iff
    (b : (hθ.indivisibleRestrictedRootPairing h𝔞).Base) (H : 𝔞) :
    H ∈ (hθ.indivisibleRestrictedRootPairing h𝔞).flip.dominantChamber b.flip ↔
      ∀ α ∈ b.support, 0 ≤ (α : Dual ℝ 𝔞) H := by
  simp only [RootPairing.mem_dominantChamber, RootPairing.Base.flip_support,
    indivisibleRestrictedRootPairing_flip_coroot'_apply]

/-- The open Weyl chamber of every base of `Σ_indiv` is nonempty. -/
theorem exists_mem_openDominantChamber_flip_indivisible
    (b : (hθ.indivisibleRestrictedRootPairing h𝔞).Base) :
    ∃ H₀ : 𝔞,
      H₀ ∈ (hθ.indivisibleRestrictedRootPairing h𝔞).flip.openDominantChamber b.flip := by
  obtain ⟨H₀, hH₀⟩ := b.exists_forall_root'_eq fun _ ↦ (1 : ℝ)
  refine ⟨H₀,
    (hθ.mem_openDominantChamber_flip_indivisible_iff h𝔞 b H₀).mpr fun α hα ↦ ?_⟩
  have hval := hH₀ α hα
  rw [indivisibleRestrictedRootPairing_root'_apply] at hval
  rw [hval]
  exact zero_lt_one

/-- Every `H₀` in the open Weyl chamber of `b.flip` in `𝔞` is regular for `Σ`: no restricted root
vanishes at `H₀`. -/
theorem ne_zero_of_mem_openDominantChamber_flip_indivisible
    {b : (hθ.indivisibleRestrictedRootPairing h𝔞).Base} {H₀ : 𝔞}
    (hH₀ :
      H₀ ∈ (hθ.indivisibleRestrictedRootPairing h𝔞).flip.openDominantChamber b.flip)
    {μ : Dual ℝ 𝔞} (hμ : μ ∈ 𝔞.restrictedRoots) :
    μ H₀ ≠ 0 :=
  have := hθ.finite_indivisibleRestrictedRoots_subtype 𝔞
  (hθ.isRegularWeight_flip_indivisible_iff h𝔞 H₀).mp
    (RootPairing.isRegularWeight_of_mem_openDominantChamber _ b.flip hH₀) μ hμ

/-- An indivisible restricted root that pairs positively with an element of the open Weyl chamber
of `b.flip` is a positive root for `b`. -/
theorem isPos_of_pos_of_mem_openDominantChamber
    {b : (hθ.indivisibleRestrictedRootPairing h𝔞).Base} {H₀ : 𝔞}
    (hH₀ :
      H₀ ∈ (hθ.indivisibleRestrictedRootPairing h𝔞).flip.openDominantChamber b.flip)
    {γ : 𝔞.indivisibleRestrictedRoots} (hγ : 0 < (γ : Dual ℝ 𝔞) H₀) :
    b.IsPos γ := by
  have := hθ.finite_indivisibleRestrictedRoots_subtype 𝔞
  by_contra hnot
  have hpos : ∀ α ∈ b.support,
      0 < (hθ.indivisibleRestrictedRootPairing h𝔞).root' α H₀ := by
    intro α hα
    rw [indivisibleRestrictedRootPairing_root'_apply]
    exact (hθ.mem_openDominantChamber_flip_indivisible_iff h𝔞 b H₀).mp hH₀ α hα
  have hlt := RootPairing.root'_neg_of_not_isPos hpos hnot
  rw [indivisibleRestrictedRootPairing_root'_apply] at hlt
  exact hγ.not_gt hlt

/-- The **positive restricted roots determined by a base** `b` of `Σ_indiv`: the restricted
roots lying in the nonnegative integer cone `TauCeti.posRootCone` generated by `b`. -/
noncomputable def positiveRestrictedRootsOfBase
    (b : (hθ.indivisibleRestrictedRootPairing h𝔞).Base) : Set (Dual ℝ 𝔞) :=
  {μ ∈ 𝔞.restrictedRoots |
    μ ∈ TauCeti.posRootCone (hθ.indivisibleRestrictedRootPairing h𝔞) b}

@[simp]
theorem mem_positiveRestrictedRootsOfBase
    (b : (hθ.indivisibleRestrictedRootPairing h𝔞).Base) {μ : Dual ℝ 𝔞} :
    μ ∈ hθ.positiveRestrictedRootsOfBase h𝔞 b ↔
      μ ∈ 𝔞.restrictedRoots ∧
        μ ∈ TauCeti.posRootCone (hθ.indivisibleRestrictedRootPairing h𝔞) b :=
  Iff.rfl

theorem positiveRestrictedRootsOfBase_subset
    (b : (hθ.indivisibleRestrictedRootPairing h𝔞).Base) :
    hθ.positiveRestrictedRootsOfBase h𝔞 b ⊆ 𝔞.restrictedRoots :=
  fun _ h ↦ h.left

/-- An indivisible restricted root belongs to `Σ⁺(b)` iff it is positive for `b`. -/
theorem mem_positiveRestrictedRootsOfBase_iff_isPos
    (b : (hθ.indivisibleRestrictedRootPairing h𝔞).Base)
    (γ : 𝔞.indivisibleRestrictedRoots) :
    (γ : Dual ℝ 𝔞) ∈ hθ.positiveRestrictedRootsOfBase h𝔞 b ↔ b.IsPos γ := by
  rw [mem_positiveRestrictedRootsOfBase,
    and_iff_right (mem_indivisibleRestrictedRoots.mp γ.property).left,
    ← indivisibleRestrictedRootPairing_root_apply hθ h𝔞 γ,
    ← TauCeti.mem_posRoots_iff_root_mem_posRootCone, TauCeti.mem_posRoots]

/-- Every simple restricted root belongs to `Σ⁺(b)`. -/
theorem mem_positiveRestrictedRootsOfBase_of_mem_support
    (b : (hθ.indivisibleRestrictedRootPairing h𝔞).Base)
    {α : 𝔞.indivisibleRestrictedRoots} (hα : α ∈ b.support) :
    (α : Dual ℝ 𝔞) ∈ hθ.positiveRestrictedRootsOfBase h𝔞 b :=
  (hθ.mem_positiveRestrictedRootsOfBase_iff_isPos h𝔞 b α).mpr (b.isPos_of_mem_support hα)

/-- **Chamber characterization of positive systems.** Every `H₀` in the open Weyl chamber of
`b.flip` in `𝔞` cuts out `positiveRestrictedRootsOfBase hθ h𝔞 b`. -/
theorem positiveRestrictedRootsOfBase_eq_positiveRestrictedRoots_of_mem_openDominantChamber
    {b : (hθ.indivisibleRestrictedRootPairing h𝔞).Base} {H₀ : 𝔞}
    (hH₀ :
      H₀ ∈ (hθ.indivisibleRestrictedRootPairing h𝔞).flip.openDominantChamber b.flip) :
    hθ.positiveRestrictedRootsOfBase h𝔞 b = 𝔞.positiveRestrictedRoots H₀ := by
  have := hθ.finite_indivisibleRestrictedRoots_subtype 𝔞
  have hpos : ∀ α ∈ b.support,
      0 < (hθ.indivisibleRestrictedRootPairing h𝔞).root' α H₀ := by
    intro α hα
    rw [indivisibleRestrictedRootPairing_root'_apply]
    exact (hθ.mem_openDominantChamber_flip_indivisible_iff h𝔞 b H₀).mp hH₀ α hα
  ext μ
  simp only [mem_positiveRestrictedRootsOfBase, mem_positiveRestrictedRoots]
  refine ⟨fun ⟨hμ, hcone⟩ ↦ ⟨hμ, ?_⟩, fun ⟨hμ, hgt⟩ ↦ ⟨hμ, ?_⟩⟩
  · have hnonneg := RootPairing.toLinearMap_apply_nonneg_of_mem_posRootCone
      (fun α hα ↦ (hpos α hα).le) hcone
    rw [indivisibleRestrictedRootPairing_toLinearMap_apply] at hnonneg
    exact lt_of_le_of_ne hnonneg
      (Ne.symm (hθ.ne_zero_of_mem_openDominantChamber_flip_indivisible h𝔞 hH₀ hμ))
  · rcases hθ.mem_indivisibleRestrictedRoots_or_exists_eq_two_smul h𝔞 hμ with
      hindiv | ⟨γ, hγ, rfl⟩
    · have hγpos := hθ.isPos_of_pos_of_mem_openDominantChamber h𝔞 hH₀
        (γ := ⟨μ, hindiv⟩) hgt
      simpa only [indivisibleRestrictedRootPairing_root_apply] using
        TauCeti.root_mem_posRootCone_of_mem_posRoots (hθ.indivisibleRestrictedRootPairing h𝔞) b
          ((TauCeti.mem_posRoots _ b _).mpr hγpos)
    · have hγgt : 0 < γ H₀ := by
        simpa only [LinearMap.smul_apply, smul_eq_mul, Nat.ofNat_pos, mul_pos_iff_of_pos_left]
          using hgt
      have hγpos := hθ.isPos_of_pos_of_mem_openDominantChamber h𝔞 hH₀ (γ := ⟨γ, hγ⟩) hγgt
      have hmem := TauCeti.root_mem_posRootCone_of_mem_posRoots
        (hθ.indivisibleRestrictedRootPairing h𝔞) b ((TauCeti.mem_posRoots _ b _).mpr hγpos)
      simpa only [indivisibleRestrictedRootPairing_root_apply, two_smul] using
        AddSubmonoid.add_mem _ hmem hmem

/-- Every base `b` of `Σ_indiv` yields a positive restricted root system. -/
theorem isPositiveRestrictedRootSystem_positiveRestrictedRootsOfBase
    (b : (hθ.indivisibleRestrictedRootPairing h𝔞).Base) :
    𝔞.IsPositiveRestrictedRootSystem (hθ.positiveRestrictedRootsOfBase h𝔞 b) := by
  have := hθ.finite_indivisibleRestrictedRoots_subtype 𝔞
  obtain ⟨H₀, hH₀⟩ := hθ.exists_mem_openDominantChamber_flip_indivisible h𝔞 b
  exact ⟨H₀, fun _ hμ ↦ hθ.ne_zero_of_mem_openDominantChamber_flip_indivisible h𝔞 hH₀ hμ,
    hθ.positiveRestrictedRootsOfBase_eq_positiveRestrictedRoots_of_mem_openDominantChamber
      h𝔞 hH₀⟩

/-- Every positive restricted root system equals `positiveRestrictedRootsOfBase b` for some base `b`
of `Σ_indiv`. -/
theorem exists_base_positiveRestrictedRootsOfBase_eq {S : Set (Dual ℝ 𝔞)}
    (hS : 𝔞.IsPositiveRestrictedRootSystem S) :
    ∃ b : (hθ.indivisibleRestrictedRootPairing h𝔞).Base,
      hθ.positiveRestrictedRootsOfBase h𝔞 b = S := by
  have := hθ.finite_indivisibleRestrictedRoots_subtype 𝔞
  obtain ⟨H₀, hreg, rfl⟩ := hS
  obtain ⟨b₀⟩ := (hθ.indivisibleRestrictedRootPairing h𝔞).nonempty_base
  obtain ⟨u, hu⟩ := RootPairing.exists_mem_dominantChamber
    (hθ.indivisibleRestrictedRootPairing h𝔞).flip b₀.flip H₀
  have hu_reg : (hθ.indivisibleRestrictedRootPairing h𝔞).flip.IsRegularWeight (u • H₀) :=
    (RootPairing.isRegularWeight_smul _ u H₀).mpr
      ((hθ.isRegularWeight_flip_indivisible_iff h𝔞 H₀).mpr hreg)
  have hu_open := RootPairing.mem_openDominantChamber_of_isRegularWeight _ b₀.flip hu hu_reg
  have hH₀_open : H₀ ∈ (hθ.indivisibleRestrictedRootPairing h𝔞).flip.openDominantChamber
      (b₀.flip.map (u⁻¹ : (hθ.indivisibleRestrictedRootPairing h𝔞).flip.Aut)) := by
    rw [← RootPairing.smul_openDominantChamber]
    refine ⟨u • H₀, hu_open, ?_⟩
    simp only [← Subgroup.coe_inv, ← Subgroup.smul_def, inv_smul_smul]
  refine
    ⟨(b₀.flip.map (u⁻¹ : (hθ.indivisibleRestrictedRootPairing h𝔞).flip.Aut)).flip, ?_⟩
  exact
    hθ.positiveRestrictedRootsOfBase_eq_positiveRestrictedRoots_of_mem_openDominantChamber
      h𝔞 hH₀_open

/-- Different bases of `Σ_indiv` determine different positive restricted root systems. -/
theorem positiveRestrictedRootsOfBase_injective :
    Function.Injective (hθ.positiveRestrictedRootsOfBase h𝔞) := by
  have := hθ.finite_indivisibleRestrictedRoots_subtype 𝔞
  intro b₁ b₂ hEq
  have hpos :
      ∀ γ : 𝔞.indivisibleRestrictedRoots, b₁.IsPos γ ↔ b₂.IsPos γ := fun γ ↦ by
    have hmem : (γ : Dual ℝ 𝔞) ∈ hθ.positiveRestrictedRootsOfBase h𝔞 b₁ ↔
        (γ : Dual ℝ 𝔞) ∈ hθ.positiveRestrictedRootsOfBase h𝔞 b₂ := by
      rw [hEq]
    simpa only [mem_positiveRestrictedRootsOfBase_iff_isPos] using hmem
  ext γ
  simp only [TauCeti.mem_support_iff_isPos_and_forall_ne_add, hpos,
    indivisibleRestrictedRootPairing_root_apply]

/-- **Bijection between bases of `Σ_indiv` and positive restricted root systems.** -/
noncomputable def baseEquivPositiveRestrictedRootSystem :
    (hθ.indivisibleRestrictedRootPairing h𝔞).Base ≃
      {S : Set (Dual ℝ 𝔞) // 𝔞.IsPositiveRestrictedRootSystem S} :=
  Equiv.ofBijective
    (fun b ↦ ⟨hθ.positiveRestrictedRootsOfBase h𝔞 b,
      hθ.isPositiveRestrictedRootSystem_positiveRestrictedRootsOfBase h𝔞 b⟩)
    ⟨fun _ _ h ↦ hθ.positiveRestrictedRootsOfBase_injective h𝔞 (congrArg Subtype.val h),
      fun ⟨S, hS⟩ ↦ by
        obtain ⟨b, hb⟩ := hθ.exists_base_positiveRestrictedRootsOfBase_eq h𝔞 hS
        exact ⟨b, Subtype.ext hb⟩⟩

@[simp]
theorem baseEquivPositiveRestrictedRootSystem_apply
    (b : (hθ.indivisibleRestrictedRootPairing h𝔞).Base) :
    (hθ.baseEquivPositiveRestrictedRootSystem h𝔞 b : Set (Dual ℝ 𝔞)) =
      hθ.positiveRestrictedRootsOfBase h𝔞 b :=
  (rfl)

/-! ### Simple restricted roots and integer coordinates -/

/-- Every positive restricted root for `b` is a nonnegative integer combination of the simple
restricted roots of `b`. -/
theorem exists_nat_eq_sum_of_mem_positiveRestrictedRootsOfBase
    (b : (hθ.indivisibleRestrictedRootPairing h𝔞).Base) {μ : Dual ℝ 𝔞}
    (hμ : μ ∈ hθ.positiveRestrictedRootsOfBase h𝔞 b) :
    ∃ c : b.support → ℕ, μ = ∑ α : b.support, c α • (α.val : Dual ℝ 𝔞) := by
  obtain ⟨f, hf⟩ :=
    (TauCeti.mem_posRootCone (hθ.indivisibleRestrictedRootPairing h𝔞) b).mp hμ.right
  refine ⟨fun α ↦ f α.val, ?_⟩
  rw [hf, ← Finset.sum_coe_sort b.support]
  simp only [indivisibleRestrictedRootPairing_root_apply]

/-- Every restricted root outside `Σ⁺(b)` is a nonpositive integer combination of the simple
restricted roots of `b`. -/
theorem exists_int_nonpos_eq_sum_of_notMem_positiveRestrictedRootsOfBase
    (b : (hθ.indivisibleRestrictedRootPairing h𝔞).Base) {μ : Dual ℝ 𝔞}
    (hμ : μ ∈ 𝔞.restrictedRoots) (hnot : μ ∉ hθ.positiveRestrictedRootsOfBase h𝔞 b) :
    ∃ c : b.support → ℤ,
      (∀ α, c α ≤ 0) ∧ μ = ∑ α : b.support, c α • (α.val : Dual ℝ 𝔞) := by
  have hS := hθ.isPositiveRestrictedRootSystem_positiveRestrictedRootsOfBase h𝔞 b
  have hneg : -μ ∈ hθ.positiveRestrictedRootsOfBase h𝔞 b :=
    (hS.neg_mem_iff_notMem h𝔞.le_cartanP hμ).mpr hnot
  obtain ⟨f, hf⟩ := hθ.exists_nat_eq_sum_of_mem_positiveRestrictedRootsOfBase h𝔞 b hneg
  refine ⟨fun α ↦ -(f α : ℤ),
    fun α ↦ Int.neg_nonpos_of_nonneg (Int.natCast_nonneg _), ?_⟩
  calc
    μ = -(-μ) := (neg_neg μ).symm
    _ = -∑ α : b.support, f α • (α.val : Dual ℝ 𝔞) := by rw [hf]
    _ = ∑ α : b.support, (-(f α : ℤ)) • (α.val : Dual ℝ 𝔞) := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun α _ ↦ ?_
      rw [neg_smul, natCast_zsmul]

/-- **Integrality and sign of restricted root coordinates**: relative to a base `b` of `Σ_indiv`,
every restricted root is a `ℤ`-linear combination of `b.support` with all coefficients `≥ 0`
(when `λ ∈ Σ⁺(b)`) or all `≤ 0` (when `λ ∉ Σ⁺(b)`). -/
theorem exists_int_nonneg_or_nonpos_of_mem_restrictedRoots
    (b : (hθ.indivisibleRestrictedRootPairing h𝔞).Base) {μ : Dual ℝ 𝔞}
    (hμ : μ ∈ 𝔞.restrictedRoots) :
    (∃ c : b.support → ℤ,
        (∀ α, 0 ≤ c α) ∧ μ = ∑ α : b.support, c α • (α.val : Dual ℝ 𝔞)) ∨
      (∃ c : b.support → ℤ,
        (∀ α, c α ≤ 0) ∧ μ = ∑ α : b.support, c α • (α.val : Dual ℝ 𝔞)) := by
  by_cases hpos : μ ∈ hθ.positiveRestrictedRootsOfBase h𝔞 b
  · obtain ⟨f, hf⟩ := hθ.exists_nat_eq_sum_of_mem_positiveRestrictedRootsOfBase h𝔞 b hpos
    exact Or.inl ⟨fun α ↦ f α, fun α ↦ Int.natCast_nonneg _,
      by simpa only [natCast_zsmul] using hf⟩
  · exact Or.inr
      (hθ.exists_int_nonpos_eq_sum_of_notMem_positiveRestrictedRootsOfBase h𝔞 b hμ hpos)

/-! ### Weyl group action on positive restricted root systems -/

section WeylAction

open Pointwise

/-- A Weyl-group element `w ∈ W(Σ)` acts on `Σ⁺(H₀)` by sending it to
`Σ⁺(w⁻¹ • H₀)` (via the coweight action on `𝔞`). -/
theorem smul_positiveRestrictedRoots (w : (hθ.restrictedRootPairing h𝔞).weylGroup)
    (H₀ : 𝔞) :
    w • 𝔞.positiveRestrictedRoots H₀ =
      𝔞.positiveRestrictedRoots
        (((w⁻¹ : (hθ.restrictedRootPairing h𝔞).Aut)).coweightEquiv H₀) := by
  ext μ
  rw [Set.mem_smul_set_iff_inv_smul_mem, mem_positiveRestrictedRoots, mem_positiveRestrictedRoots,
    hθ.smul_mem_restrictedRoots_iff h𝔞 w⁻¹, ← Subgroup.coe_inv,
    hθ.restrictedRootPairing_weylGroup_smul_apply h𝔞]

/-- The Weyl group `W(Σ)` preserves the property of being a positive restricted root system. -/
theorem isPositiveRestrictedRootSystem_smul (w : (hθ.restrictedRootPairing h𝔞).weylGroup)
    {S : Set (Dual ℝ 𝔞)} (hS : 𝔞.IsPositiveRestrictedRootSystem S) :
    𝔞.IsPositiveRestrictedRootSystem (w • S) := by
  obtain ⟨H₀, hreg, rfl⟩ := hS
  refine ⟨((w⁻¹ : (hθ.restrictedRootPairing h𝔞).Aut)).coweightEquiv H₀,
    fun μ hμ ↦ ?_, hθ.smul_positiveRestrictedRoots h𝔞 w H₀⟩
  rw [← Subgroup.coe_inv, ← hθ.restrictedRootPairing_weylGroup_smul_apply h𝔞 w⁻¹]
  exact hreg _ ((hθ.smul_mem_restrictedRoots_iff h𝔞 w⁻¹).mpr hμ)

/-- The action of `W(Σ)` on positive restricted root systems matches the transport of bases of
`Σ_indiv` along `restrictedWeylGroupEquiv`. -/
theorem smul_positiveRestrictedRootsOfBase (w : (hθ.restrictedRootPairing h𝔞).weylGroup)
    (b : (hθ.indivisibleRestrictedRootPairing h𝔞).Base) :
    w • hθ.positiveRestrictedRootsOfBase h𝔞 b =
      hθ.positiveRestrictedRootsOfBase h𝔞
        (b.map (hθ.restrictedWeylGroupEquiv h𝔞 w :
          (hθ.indivisibleRestrictedRootPairing h𝔞).Aut)) := by
  classical
  let w' := hθ.restrictedWeylGroupEquiv h𝔞 w
  have hcone :
      TauCeti.posRootCone (hθ.indivisibleRestrictedRootPairing h𝔞)
          (b.map (w' : (hθ.indivisibleRestrictedRootPairing h𝔞).Aut)) =
        (TauCeti.posRootCone (hθ.indivisibleRestrictedRootPairing h𝔞) b).map
          (DistribSMul.toAddMonoidHom (Dual ℝ 𝔞) w') := by
    rw [TauCeti.posRootCone_def, TauCeti.posRootCone_def, AddMonoidHom.map_mclosure]
    congr 1
    ext ν
    rw [RootPairing.Base.support_map_eq]
    simp only [Set.mem_image, Finset.mem_coe, Finset.mem_image]
    constructor
    · rintro ⟨β, ⟨α, hα, rfl⟩, rfl⟩
      refine ⟨(hθ.indivisibleRestrictedRootPairing h𝔞).root α, ⟨α, hα, rfl⟩, ?_⟩
      rw [DistribSMul.toAddMonoidHom_apply, Subgroup.smul_def,
        RootPairing.Equiv.root_indexEquiv_eq_smul]
    · rintro ⟨_, ⟨α, hα, rfl⟩, rfl⟩
      refine ⟨(w' : (hθ.indivisibleRestrictedRootPairing h𝔞).Aut).indexEquiv α,
        ⟨α, hα, rfl⟩, ?_⟩
      rw [DistribSMul.toAddMonoidHom_apply, Subgroup.smul_def,
        RootPairing.Equiv.root_indexEquiv_eq_smul]
  ext μ
  rw [Set.mem_smul_set_iff_inv_smul_mem, mem_positiveRestrictedRootsOfBase,
    mem_positiveRestrictedRootsOfBase, hθ.smul_mem_restrictedRoots_iff h𝔞 w⁻¹, hcone]
  refine and_congr Iff.rfl ?_
  rw [AddSubmonoid.mem_map]
  constructor
  · intro hmem
    refine ⟨w⁻¹ • μ, hmem, ?_⟩
    rw [DistribSMul.toAddMonoidHom_apply, hθ.restrictedWeylGroupEquiv_smul, smul_inv_smul]
  · rintro ⟨ν, hν, rfl⟩
    rw [DistribSMul.toAddMonoidHom_apply, hθ.restrictedWeylGroupEquiv_smul, inv_smul_smul]
    exact hν

/-- **Simple transitivity of `W(Σ)` on positive restricted root systems.** For any two positive
restricted root systems `S₁` and `S₂`, there exists a unique `w ∈ W(Σ)` such that
`w • S₁ = S₂`. -/
theorem existsUnique_weylGroup_smul_positiveRestrictedRoots {S₁ S₂ : Set (Dual ℝ 𝔞)}
    (hS₁ : 𝔞.IsPositiveRestrictedRootSystem S₁)
    (hS₂ : 𝔞.IsPositiveRestrictedRootSystem S₂) :
    ∃! w : (hθ.restrictedRootPairing h𝔞).weylGroup, w • S₁ = S₂ := by
  have := hθ.finite_indivisibleRestrictedRoots_subtype 𝔞
  obtain ⟨b₁, rfl⟩ := hθ.exists_base_positiveRestrictedRootsOfBase_eq h𝔞 hS₁
  obtain ⟨b₂, rfl⟩ := hθ.exists_base_positiveRestrictedRootsOfBase_eq h𝔞 hS₂
  obtain ⟨w', hw', hw'_uniq⟩ := RootPairing.Base.existsUnique_map_eq b₁ b₂
  refine ⟨(hθ.restrictedWeylGroupEquiv h𝔞).symm w', ?_, fun v hv ↦ ?_⟩
  · dsimp only
    rw [hθ.smul_positiveRestrictedRootsOfBase h𝔞, MulEquiv.apply_symm_apply, hw']
  · dsimp only at hv
    rw [hθ.smul_positiveRestrictedRootsOfBase h𝔞] at hv
    have hmap : b₁.map (hθ.restrictedWeylGroupEquiv h𝔞 v :
        (hθ.indivisibleRestrictedRootPairing h𝔞).Aut) = b₂ :=
      hθ.positiveRestrictedRootsOfBase_injective h𝔞 hv
    exact (hθ.restrictedWeylGroupEquiv h𝔞).eq_symm_apply.mpr (hw'_uniq _ hmap)

/-- Every `H ∈ 𝔞` is conjugate by some `w ∈ W(Σ)` (via its coweight action) into the closed
dominant Weyl chamber of `b.flip`. -/
theorem exists_weylGroup_coweightEquiv_mem_dominantChamber
    (b : (hθ.indivisibleRestrictedRootPairing h𝔞).Base) (H : 𝔞) :
    ∃ w : (hθ.restrictedRootPairing h𝔞).weylGroup,
      (w : (hθ.restrictedRootPairing h𝔞).Aut).coweightEquiv H ∈
        (hθ.indivisibleRestrictedRootPairing h𝔞).flip.dominantChamber b.flip := by
  have := hθ.finite_indivisibleRestrictedRoots_subtype 𝔞
  obtain ⟨u, hu⟩ :=
    RootPairing.exists_mem_dominantChamber
      (hθ.indivisibleRestrictedRootPairing h𝔞).flip b.flip H
  obtain ⟨w', hw'⟩ := RootPairing.exists_weylGroup_coweightEquiv_eq_flip_smul _ u
  refine ⟨(hθ.restrictedWeylGroupEquiv h𝔞).symm w', ?_⟩
  rw [← hθ.coweightEquiv_restrictedWeylGroupEquiv h𝔞, MulEquiv.apply_symm_apply, hw']
  exact hu

end WeylAction

end BasesAndChambers

end LieEquiv.IsCartanInvolution
