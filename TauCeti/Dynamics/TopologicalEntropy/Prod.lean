/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Dynamics.TopologicalEntropy.NetEntropy
import TauCeti.Data.EReal.Quantale

/-!
# Topological entropy of products

For maps `S : X → X` and `T : Y → Y` of nonempty uniform spaces, the product map
`Prod.map S T` has topological entropy `coverEntropy S univ + coverEntropy T univ`
(`TauCeti.coverEntropy_prodMap`). No continuity or compactness is needed.

The product entourages `entourageProd U V` form a basis of the product uniformity, and two points
are `entourageProd U V`-close for `n` steps of `Prod.map S T` exactly when their coordinates are
`U`-close for `n` steps of `S` and `V`-close for `n` steps of `T`
(`TauCeti.dynEntourage_prodMap`). Products of dynamical covers are dynamical covers, which bounds
the minimal covers of the product by the product of the minimal covers
(`TauCeti.coverMincard_prodMap_le`); products of dynamical nets are dynamical nets, which bounds the
maximal nets of the product below (`TauCeti.netMaxcard_mul_le_netMaxcard_prodMap`). The upper
bound for the exponential growth rate of a product is the sum of the upper rates, and the lower
bound is the sum of an upper and a lower rate; Mathlib's `coverEntropyInf_eq_coverEntropy` shows
that the lower and upper entropies of a map on the whole space agree, so the bounds meet.

## Main results

* `TauCeti.dynEntourage_prodMap`: dynamical entourages of a product.
* `TauCeti.coverEntropy_prodMap_le`: `h(S × T) ≤ h(S) + h(T)`.
* `TauCeti.le_coverEntropy_prodMap`: `h(S) + h(T) ≤ h(S × T)`.
* `TauCeti.coverEntropy_prodMap`: `h(S × T) = h(S) + h(T)`.

## References

This is the product additivity of item 3 of §5.2 of the Tau Ceti roadmap `ClassicalErgodicTheory`.
-/

public section

namespace TauCeti

open Dynamics Set Filter ExpGrowth
open scoped Uniformity ENNReal

variable {X Y : Type*} {S : X → X} {T : Y → Y}

/-- Two points are `entourageProd U V`-close for `n` steps of `Prod.map S T` exactly when their
first coordinates are `U`-close for `n` steps of `S` and their second coordinates are `V`-close for
`n` steps of `T`. -/
theorem dynEntourage_prodMap (S : X → X) (T : Y → Y) (U : SetRel X X) (V : SetRel Y Y) (n : ℕ) :
    dynEntourage (Prod.map S T) (entourageProd U V) n =
      entourageProd (dynEntourage S U n) (dynEntourage T V n) := by
  ext ⟨⟨x, y⟩, ⟨x', y'⟩⟩
  simp only [mem_dynEntourage, Prod.map_iterate, Prod.map_apply, mem_entourageProd]
  exact ⟨fun h ↦ ⟨fun k hk ↦ (h k hk).1, fun k hk ↦ (h k hk).2⟩,
    fun h k hk ↦ ⟨h.1 k hk, h.2 k hk⟩⟩

/-- The product of two dynamical covers is a dynamical cover of the product map for the product
entourage. -/
theorem _root_.Dynamics.IsDynCoverOf.prodMap {U : SetRel X X} {V : SetRel Y Y} {n : ℕ}
    {s : Set X} {t : Set Y}
    (hs : IsDynCoverOf S univ U n s) (ht : IsDynCoverOf T univ V n t) :
    IsDynCoverOf (Prod.map S T) univ (entourageProd U V) n (s ×ˢ t) := by
  rintro ⟨x, y⟩ -
  obtain ⟨x', hx', hxx'⟩ := hs (mem_univ x)
  obtain ⟨y', hy', hyy'⟩ := ht (mem_univ y)
  refine ⟨(x', y'), mk_mem_prod hx' hy', ?_⟩
  change ((x, y), (x', y')) ∈ dynEntourage (Prod.map S T) (entourageProd U V) n
  rw [dynEntourage_prodMap]
  exact ⟨hxx', hyy'⟩

/-- The product of two dynamical nets is a dynamical net of the product map for the product
entourage. -/
theorem _root_.Dynamics.IsDynNetIn.prodMap {U : SetRel X X} {V : SetRel Y Y} {n : ℕ}
    {s : Set X} {t : Set Y}
    (hs : IsDynNetIn S univ U n s) (ht : IsDynNetIn T univ V n t) :
    IsDynNetIn (Prod.map S T) univ (entourageProd U V) n (s ×ˢ t) := by
  refine ⟨subset_univ _, fun p hp q hq hpq ↦ ?_⟩
  simp only [Function.onFun, dynEntourage_prodMap, inv_entourageProd, ball_entourageProd]
  rcases ne_or_eq p.1 q.1 with h | h
  · exact disjoint_prod.mpr (.inl (hs.2 hp.1 hq.1 h))
  · have h' : p.2 ≠ q.2 := fun h' ↦ hpq (Prod.ext h h')
    exact disjoint_prod.mpr (.inr (ht.2 hp.2 hq.2 h'))

/-- The minimal dynamical covers of a product map for a product entourage are at most the products
of the minimal dynamical covers of the factors. -/
theorem coverMincard_prodMap_le [Nonempty X] [Nonempty Y] (S : X → X) (T : Y → Y)
    (U : SetRel X X) (V : SetRel Y Y) (n : ℕ) :
    coverMincard (Prod.map S T) univ (entourageProd U V) n ≤
      coverMincard S univ U n * coverMincard T univ V n := by
  classical
  have hS1 := (one_le_coverMincard_iff S univ U n).mpr univ_nonempty
  have hT1 := (one_le_coverMincard_iff T univ V n).mpr univ_nonempty
  rcases eq_or_ne (coverMincard S univ U n) ⊤ with hS | hS
  · rw [hS, ENat.top_mul ((zero_lt_one.trans_le hT1).ne')]
    exact le_top
  · rcases eq_or_ne (coverMincard T univ V n) ⊤ with hT | hT
    · rw [hT, ENat.mul_top ((zero_lt_one.trans_le hS1).ne')]
      exact le_top
    · obtain ⟨s, hs, hs_card⟩ := (coverMincard_finite_iff S univ U n).mp (lt_top_iff_ne_top.mpr hS)
      obtain ⟨t, ht, ht_card⟩ := (coverMincard_finite_iff T univ V n).mp (lt_top_iff_ne_top.mpr hT)
      have hst : IsDynCoverOf (Prod.map S T) univ (entourageProd U V) n
          ((s ×ˢ t : Finset (X × Y)) : Set (X × Y)) := by
        rw [Finset.coe_product]
        exact hs.prodMap ht
      refine hst.coverMincard_le_card.trans ?_
      rw [Finset.card_product, ← hs_card, ← ht_card, Nat.cast_mul]

/-- The products of the maximal dynamical nets of the factors are at most the maximal dynamical
nets of the product map for the product entourage. -/
theorem netMaxcard_mul_le_netMaxcard_prodMap (S : X → X) (T : Y → Y) (U : SetRel X X)
    (V : SetRel Y Y) (n : ℕ) :
    netMaxcard S univ U n * netMaxcard T univ V n ≤
      netMaxcard (Prod.map S T) univ (entourageProd U V) n := by
  classical
  rw [netMaxcard, ENat.iSup_mul]
  refine iSup_le fun s ↦ ?_
  rw [ENat.iSup_mul]
  refine iSup_le fun hs ↦ ?_
  rw [netMaxcard, ENat.mul_iSup]
  refine iSup_le fun t ↦ ?_
  rw [ENat.mul_iSup]
  refine iSup_le fun ht ↦ ?_
  have hst : IsDynNetIn (Prod.map S T) univ (entourageProd U V) n
      ((s ×ˢ t : Finset (X × Y)) : Set (X × Y)) := by
    rw [Finset.coe_product]
    exact hs.prodMap ht
  refine le_trans ?_ (le_iSup₂ (f := fun (u : Finset (X × Y))
    (_ : IsDynNetIn (Prod.map S T) univ (entourageProd U V) n u) ↦ (u.card : ℕ∞)) _ hst)
  rw [Finset.card_product, Nat.cast_mul]

variable [UniformSpace X] [UniformSpace Y]

/-- The topological entropy of a product map is at most the sum of the entropies of the factors. -/
theorem coverEntropy_prodMap_le [Nonempty X] [Nonempty Y] (S : X → X) (T : Y → Y) :
    coverEntropy (Prod.map S T) univ ≤ coverEntropy S univ + coverEntropy T univ := by
  refine iSup₂_le fun W hW ↦ ?_
  obtain ⟨U, hU, V, hV, hUV⟩ := entourageProd_subset hW
  have hS0 := coverEntropyEntourage_nonneg S univ_nonempty U
  have hT0 := coverEntropyEntourage_nonneg T univ_nonempty V
  calc coverEntropyEntourage (Prod.map S T) univ W
      ≤ coverEntropyEntourage (Prod.map S T) univ (entourageProd U V) :=
        coverEntropyEntourage_antitone _ _ hUV
    _ ≤ expGrowthSup ((fun n ↦ (coverMincard S univ U n : ℝ≥0∞)) *
          fun n ↦ (coverMincard T univ V n : ℝ≥0∞)) :=
        expGrowthSup_monotone fun n ↦ by
          simp only [Pi.mul_apply, ← ENat.toENNReal_mul]
          exact ENat.toENNReal_mono (coverMincard_prodMap_le S T U V n)
    _ ≤ coverEntropyEntourage S univ U + coverEntropyEntourage T univ V :=
        expGrowthSup_mul_le (.inl (hS0.trans_lt' EReal.bot_lt_zero).ne')
          (.inr (hT0.trans_lt' EReal.bot_lt_zero).ne')
    _ ≤ coverEntropy S univ + coverEntropy T univ :=
        add_le_add (coverEntropyEntourage_le_coverEntropy S univ hU)
          (coverEntropyEntourage_le_coverEntropy T univ hV)

/-- The sum of the topological entropies of the factors is at most the entropy of the product
map. -/
theorem le_coverEntropy_prodMap (S : X → X) (T : Y → Y) :
    coverEntropy S univ + coverEntropy T univ ≤ coverEntropy (Prod.map S T) univ := by
  rw [← coverEntropyInf_eq_coverEntropy T (mapsTo_univ T univ),
    coverEntropy_eq_iSup_netEntropyEntourage, coverEntropyInf_eq_iSup_netEntropyInfEntourage,
    iSup_subtype', iSup_subtype', AddQuantale.iSup_add_distrib]
  refine iSup_le fun U ↦ ?_
  rw [AddQuantale.add_iSup_distrib]
  refine iSup_le fun V ↦ ?_
  refine le_trans ?_ (netEntropyEntourage_le_coverEntropy (Prod.map S T) univ
    (entourageProd_mem_uniformity U.property V.property))
  refine le_expGrowthSup_mul.trans (expGrowthSup_monotone fun n ↦ ?_)
  simp only [Pi.mul_apply, ← ENat.toENNReal_mul]
  exact ENat.toENNReal_mono (netMaxcard_mul_le_netMaxcard_prodMap S T U V n)

/-- **Product formula for topological entropy.** The topological entropy of the product of two
maps of nonempty uniform spaces is the sum of their entropies. -/
theorem coverEntropy_prodMap [Nonempty X] [Nonempty Y] (S : X → X) (T : Y → Y) :
    coverEntropy (Prod.map S T) univ = coverEntropy S univ + coverEntropy T univ :=
  (coverEntropy_prodMap_le S T).antisymm (le_coverEntropy_prodMap S T)

end TauCeti
