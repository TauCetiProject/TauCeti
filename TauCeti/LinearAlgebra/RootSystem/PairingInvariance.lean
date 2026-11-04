/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.RootSystem.Chain
public import Mathlib.LinearAlgebra.RootSystem.Finite.Nondegenerate

/-!
# Invariance of crystallographic root relations under matching Cartan pairings

`TauCeti.LinearAlgebra.RootSystem.HomInvariance` shows that a homomorphism `f : P.Hom P₂` of root
pairings over a common base ring `R` with injective weight map preserves additive root relations,
reflections, pairwise linear independence, and root-string lengths.

When comparing a root datum `P : RootPairing ι ℤ X Y` over `ℤ` (possibly with a central torus in
`X` and `Y`) against the Killing root system of a semisimple Lie algebra over a field `K` of
characteristic zero, there is no `RootPairing.Hom` because the base rings `ℤ` and `K` differ and
the ambient modules have different ranks. Nevertheless, in any finite crystallographic root pairing
in characteristic zero, the canonical polarization on `P.rootSpan ℤ` is injective
(`RootPairing.exists_coroot_ne`), so an integer linear combination of roots vanishes if and only if
its pairing with every coroot vanishes.

Consequently, a bijection `e : ι ≃ ι₂` between the root indices of two finite crystallographic root
pairings `P` and `P₂` over characteristic-zero domains `R` and `S` satisfying
`P₂.pairingIn ℤ (e i) (e j) = P.pairingIn ℤ i j` preserves and reflects all integer linear
relations among roots, commutes with `RootPairing.reflectionPerm`, and preserves pairwise linear
independence, reducedness, and the root-string lengths `RootPairing.chainTopCoeff` and
`RootPairing.chainBotCoeff`.

## Main results

* `RootPairing.eq_zero_of_mem_rootSpan_of_forall_coroot'_eq_zero` and
  `RootPairing.eq_zero_of_mem_corootSpan_of_forall_root'_eq_zero`: an element of the integral root
  (or coroot) span paired to zero by every coroot (or root) vanishes, even when the ambient module
  contains extra toral directions.
* `RootPairing.sum_zsmul_root_eq_zero_iff`: an integer linear combination of roots vanishes if and
  only if its integer pairings with all coroots vanish.
* `RootPairing.sum_zsmul_root_eq_zero_iff_of_pairingIn`,
  `RootPairing.root_add_eq_zero_iff_of_pairingIn`, `RootPairing.root_eq_add_iff_of_pairingIn`,
  `RootPairing.root_add_add_eq_zero_iff_of_pairingIn`: matching integer Cartan pairings preserve
  and reflect integer linear relations among roots.
* `RootPairing.map_reflectionPerm_of_pairingIn`: matching integer Cartan pairings intertwine
  `RootPairing.reflectionPerm`.
* `RootPairing.linearIndependent_root_iff_of_pairingIn`, `RootPairing.isReduced_iff_of_pairingIn`,
  `RootPairing.chainTopCoeff_eq_of_pairingIn`, `RootPairing.chainBotCoeff_eq_of_pairingIn`:
  matching integer Cartan pairings preserve pairwise linear independence, reducedness, and
  root-string lengths.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Ch. VI, §1.
-/

public section

namespace RootPairing

open Function Set

section SinglePairing

variable {ι R M N : Type*} [CommRing R] [CharZero R] [IsDomain R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  (P : RootPairing ι R M N) [Finite ι] [P.IsCrystallographic]

/-- An element of the integral root span `P.rootSpan ℤ` annihilated by every coroot functional
vanishes, without assuming that the roots span `M`. -/
theorem eq_zero_of_mem_rootSpan_of_forall_coroot'_eq_zero {x : M} (hx : x ∈ P.rootSpan ℤ)
    (h : ∀ i, P.coroot' i x = 0) : x = 0 := by
  cases nonempty_fintype ι
  by_contra hx0
  obtain ⟨i, hi⟩ := P.exists_coroot_ne ℤ (x := ⟨x, hx⟩) (Subtype.coe_ne_coe.mp hx0)
  exact hi <| FaithfulSMul.algebraMap_injective ℤ R <| by
    rw [P.algebraMap_coroot'In_apply, map_zero, h i]

/-- An element of the integral coroot span `P.corootSpan ℤ` annihilated by every root functional
vanishes, without assuming that the coroots span `N`. -/
theorem eq_zero_of_mem_corootSpan_of_forall_root'_eq_zero {y : N} (hy : y ∈ P.corootSpan ℤ)
    (h : ∀ i, P.root' i y = 0) : y = 0 :=
  P.flip.eq_zero_of_mem_rootSpan_of_forall_coroot'_eq_zero hy h

/-- An integer linear combination of roots vanishes in `M` if and only if its integer Cartan
pairing with every coroot vanishes. -/
theorem sum_zsmul_root_eq_zero_iff {κ : Type*} [Fintype κ] (c : κ → ℤ) (idx : κ → ι) :
    ∑ a : κ, c a • P.root (idx a) = 0 ↔ ∀ s : ι, ∑ a : κ, c a * P.pairingIn ℤ (idx a) s = 0 := by
  have hmem : ∑ a : κ, c a • P.root (idx a) ∈ P.rootSpan ℤ :=
    Submodule.sum_mem _ fun a _ ↦ Submodule.smul_mem _ _ (Submodule.subset_span (mem_range_self _))
  have hpair (s : ι) :
      P.coroot' s (∑ a : κ, c a • P.root (idx a)) =
        ((∑ a : κ, c a * P.pairingIn ℤ (idx a) s : ℤ) : R) := by
    rw [map_sum, Int.cast_sum]
    refine Finset.sum_congr rfl fun a _ ↦ ?_
    rw [LinearMap.map_smul_of_tower, root_coroot'_eq_pairing, ← P.algebraMap_pairingIn ℤ]
    simp [zsmul_eq_mul]
  refine ⟨fun h0 s ↦ ?_,
    fun hs ↦ P.eq_zero_of_mem_rootSpan_of_forall_coroot'_eq_zero hmem fun s ↦ ?_⟩
  · have hs0 := hpair s
    rw [h0, map_zero, eq_comm, Int.cast_eq_zero] at hs0
    exact hs0
  · rw [hpair s, hs s, Int.cast_zero]

end SinglePairing

section TwoPairings

variable {ι ι₂ R S M N M₂ N₂ : Type*}
  [CommRing R] [CharZero R] [IsDomain R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  [CommRing S] [CharZero S] [IsDomain S] [AddCommGroup M₂] [Module S M₂]
  [AddCommGroup N₂] [Module S N₂]
  {P : RootPairing ι R M N} {P₂ : RootPairing ι₂ S M₂ N₂}
  [Finite ι] [P.IsCrystallographic] [P₂.IsCrystallographic]

/-- A bijection of root indices preserving integer Cartan pairings preserves and reflects all
integer linear relations among roots. -/
theorem sum_zsmul_root_eq_zero_iff_of_pairingIn (e : ι ≃ ι₂)
    (he : ∀ i j, P₂.pairingIn ℤ (e i) (e j) = P.pairingIn ℤ i j)
    {κ : Type*} [Fintype κ] (c : κ → ℤ) (idx : κ → ι) :
    ∑ a : κ, c a • P₂.root (e (idx a)) = 0 ↔ ∑ a : κ, c a • P.root (idx a) = 0 := by
  let _ : Finite ι₂ := Finite.of_equiv ι e
  rw [P₂.sum_zsmul_root_eq_zero_iff, P.sum_zsmul_root_eq_zero_iff]
  refine ⟨fun h s ↦ ?_, fun h s₂ ↦ ?_⟩
  · simpa [he] using h (e s)
  · obtain ⟨s, rfl⟩ := e.surjective s₂
    simpa [he] using h s

/-- Three-term integer linear relations among roots are preserved and reflected by any bijection of
root indices matching integer Cartan pairings. -/
theorem zsmul_add_zsmul_add_zsmul_root_eq_zero_iff_of_pairingIn (e : ι ≃ ι₂)
    (he : ∀ i j, P₂.pairingIn ℤ (e i) (e j) = P.pairingIn ℤ i j) (a b c : ℤ) (i j k : ι) :
    a • P₂.root (e i) + b • P₂.root (e j) + c • P₂.root (e k) = 0 ↔
      a • P.root i + b • P.root j + c • P.root k = 0 := by
  simpa [Fin.sum_univ_three, add_assoc] using
    sum_zsmul_root_eq_zero_iff_of_pairingIn e he ![a, b, c] ![i, j, k]

/-- Opposition of roots `α + β = 0` is preserved and reflected by a pairing-preserving bijection of
root indices. -/
theorem root_add_eq_zero_iff_of_pairingIn (e : ι ≃ ι₂)
    (he : ∀ i j, P₂.pairingIn ℤ (e i) (e j) = P.pairingIn ℤ i j) (i j : ι) :
    P₂.root (e i) + P₂.root (e j) = 0 ↔ P.root i + P.root j = 0 := by
  simpa using zsmul_add_zsmul_add_zsmul_root_eq_zero_iff_of_pairingIn e he 1 1 0 i j i

/-- Root-sum identities `γ = α + β` are preserved and reflected by a pairing-preserving bijection of
root indices. -/
theorem root_eq_add_iff_of_pairingIn (e : ι ≃ ι₂)
    (he : ∀ i j, P₂.pairingIn ℤ (e i) (e j) = P.pairingIn ℤ i j) (k i j : ι) :
    P₂.root (e k) = P₂.root (e i) + P₂.root (e j) ↔ P.root k = P.root i + P.root j := by
  rw [← sub_eq_zero, ← sub_eq_zero (a := P.root k)]
  simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using
    zsmul_add_zsmul_add_zsmul_root_eq_zero_iff_of_pairingIn e he (-1) (-1) 1 i j k

/-- Zero-sum root triples `α + β + γ = 0` are preserved and reflected by a pairing-preserving
bijection of root indices. -/
theorem root_add_add_eq_zero_iff_of_pairingIn (e : ι ≃ ι₂)
    (he : ∀ i j, P₂.pairingIn ℤ (e i) (e j) = P.pairingIn ℤ i j) (i j k : ι) :
    P₂.root (e i) + P₂.root (e j) + P₂.root (e k) = 0 ↔
      P.root i + P.root j + P.root k = 0 := by
  simpa using zsmul_add_zsmul_add_zsmul_root_eq_zero_iff_of_pairingIn e he 1 1 1 i j k

/-- Root-string step relations `γ = β + z • α` are preserved and reflected by a pairing-preserving
bijection of root indices. -/
theorem root_eq_add_zsmul_iff_of_pairingIn (e : ι ≃ ι₂)
    (he : ∀ i j, P₂.pairingIn ℤ (e i) (e j) = P.pairingIn ℤ i j) (k j i : ι) (z : ℤ) :
    P₂.root (e k) = P₂.root (e j) + z • P₂.root (e i) ↔
      P.root k = P.root j + z • P.root i := by
  rw [← sub_eq_zero, ← sub_eq_zero (a := P.root k)]
  simpa [sub_eq_add_neg, neg_smul, add_assoc, add_comm, add_left_comm] using
    zsmul_add_zsmul_add_zsmul_root_eq_zero_iff_of_pairingIn e he 1 (-1) (-z) k j i

/-- A bijection of root indices preserving integer Cartan pairings commutes with root
reflections. -/
theorem map_reflectionPerm_of_pairingIn (e : ι ≃ ι₂)
    (he : ∀ i j, P₂.pairingIn ℤ (e i) (e j) = P.pairingIn ℤ i j) (i j : ι) :
    e (P.reflectionPerm i j) = P₂.reflectionPerm (e i) (e j) := by
  apply P₂.root.injective
  have h1 : P.root (P.reflectionPerm i j) = P.root j + (-P.pairingIn ℤ j i) • P.root i := by
    rw [root_reflectionPerm, reflection_apply_root, ← P.algebraMap_pairingIn ℤ, neg_smul,
      sub_eq_add_neg, algebraMap_smul]
  have h2 := (root_eq_add_zsmul_iff_of_pairingIn e he (P.reflectionPerm i j) j i
    (-P.pairingIn ℤ j i)).mpr h1
  rw [h2, ← he j i, root_reflectionPerm, reflection_apply_root, ← P₂.algebraMap_pairingIn ℤ,
    neg_smul, sub_eq_add_neg, algebraMap_smul]

/-- A bijection of root indices preserving integer Cartan pairings preserves and reflects pairwise
linear independence of roots. -/
theorem linearIndependent_root_iff_of_pairingIn (e : ι ≃ ι₂)
    (he : ∀ i j, P₂.pairingIn ℤ (e i) (e j) = P.pairingIn ℤ i j) (i j : ι) :
    LinearIndependent S ![P₂.root (e i), P₂.root (e j)] ↔
      LinearIndependent R ![P.root i, P.root j] := by
  let _ : Finite ι₂ := Finite.of_equiv ι e
  have : Module.IsReflexive R M := .of_isPerfPair P.toLinearMap
  have : Module.IsReflexive S M₂ := .of_isPerfPair P₂.toLinearMap
  rw [P₂.linearIndependent_iff_coxeterWeightIn_ne_four ℤ,
    P.linearIndependent_iff_coxeterWeightIn_ne_four ℤ]
  simp only [coxeterWeightIn, he]

/-- Two finite crystallographic root pairings over characteristic-zero domains with matching
integer Cartan pairings are simultaneously reduced. -/
theorem isReduced_iff_of_pairingIn (e : ι ≃ ι₂)
    (he : ∀ i j, P₂.pairingIn ℤ (e i) (e j) = P.pairingIn ℤ i j) :
    P₂.IsReduced ↔ P.IsReduced := by
  let _ : Finite ι₂ := Finite.of_equiv ι e
  simp only [isReduced_iff', root_eq_neg_iff]
  refine ⟨fun h i j hij hdep ↦ ?_, fun h i₂ j₂ hij hdep ↦ ?_⟩
  · have hdep₂ := mt (linearIndependent_root_iff_of_pairingIn e he i j).mp hdep
    have h2 := h (e i) (e j) (e.injective.ne hij) hdep₂
    exact e.injective (h2.trans (map_reflectionPerm_of_pairingIn e he j j).symm)
  · obtain ⟨i, rfl⟩ := e.surjective i₂
    obtain ⟨j, rfl⟩ := e.surjective j₂
    have hdep₁ := mt (linearIndependent_root_iff_of_pairingIn e he i j).mpr hdep
    rw [← map_reflectionPerm_of_pairingIn e he j j]
    exact congrArg e (h i j (fun h' ↦ hij (congrArg e h')) hdep₁)

/-- A bijection of root indices preserving integer Cartan pairings preserves ascending root-string
lengths. -/
theorem chainTopCoeff_eq_of_pairingIn (e : ι ≃ ι₂)
    (he : ∀ i j, P₂.pairingIn ℤ (e i) (e j) = P.pairingIn ℤ i j) (i j : ι) :
    letI : Finite ι₂ := Finite.of_equiv ι e
    P₂.chainTopCoeff (e i) (e j) = P.chainTopCoeff i j := by
  let _ : Finite ι₂ := Finite.of_equiv ι e
  by_cases h : LinearIndependent R ![P.root i, P.root j]
  · have h₂ := (linearIndependent_root_iff_of_pairingIn e he i j).mpr h
    have hmem (n : ℕ) :
        P₂.root (e j) + n • P₂.root (e i) ∈ range P₂.root ↔
          P.root j + n • P.root i ∈ range P.root := by
      refine ⟨fun ⟨k₂, hk₂⟩ ↦ ?_, fun ⟨k, hk⟩ ↦ ⟨e k, ?_⟩⟩
      · obtain ⟨k, rfl⟩ := e.surjective k₂
        have hk₂' : P₂.root (e k) = P₂.root (e j) + (n : ℤ) • P₂.root (e i) := by
          simpa using hk₂
        exact ⟨k, by simpa using (root_eq_add_zsmul_iff_of_pairingIn e he k j i n).mp hk₂'⟩
      · have hk' : P.root k = P.root j + (n : ℤ) • P.root i := by simpa using hk
        simpa using (root_eq_add_zsmul_iff_of_pairingIn e he k j i n).mpr hk'
    refine le_antisymm ?_ ?_
    · rw [← P.root_add_nsmul_mem_range_iff_le_chainTopCoeff h, ← hmem]
      exact (P₂.root_add_nsmul_mem_range_iff_le_chainTopCoeff h₂).mpr le_rfl
    · rw [← P₂.root_add_nsmul_mem_range_iff_le_chainTopCoeff h₂, hmem]
      exact (P.root_add_nsmul_mem_range_iff_le_chainTopCoeff h).mpr le_rfl
  · have h₂ := mt (linearIndependent_root_iff_of_pairingIn e he i j).mp h
    rw [chainTopCoeff_of_not_linearIndependent h₂, chainTopCoeff_of_not_linearIndependent h]

/-- A bijection of root indices preserving integer Cartan pairings preserves descending root-string
lengths. -/
theorem chainBotCoeff_eq_of_pairingIn (e : ι ≃ ι₂)
    (he : ∀ i j, P₂.pairingIn ℤ (e i) (e j) = P.pairingIn ℤ i j) (i j : ι) :
    letI : Finite ι₂ := Finite.of_equiv ι e
    P₂.chainBotCoeff (e i) (e j) = P.chainBotCoeff i j := by
  let _ : Finite ι₂ := Finite.of_equiv ι e
  rw [← P₂.chainTopCoeff_reflectionPerm_left, ← P.chainTopCoeff_reflectionPerm_left,
    ← map_reflectionPerm_of_pairingIn e he, chainTopCoeff_eq_of_pairingIn e he]

end TwoPairings

end RootPairing
