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

For maps `S : X → X` and `T : Y → Y` of uniform spaces and subsets `F : Set X`, `G : Set Y` with
`MapsTo T G G`, the product map `Prod.map S T` has topological entropy
`coverEntropy S F + coverEntropy T G` on `F ×ˢ G` (`TauCeti.coverEntropy_prodMap`); in particular
`h(S × T) = h(S) + h(T)` on the whole space (`TauCeti.coverEntropy_prodMap_univ`). No continuity
or compactness is needed.

The product entourages `entourageProd U V` form a basis of the product uniformity, and two points
are `entourageProd U V`-close for `n` steps of `Prod.map S T` exactly when their coordinates are
`U`-close for `n` steps of `S` and `V`-close for `n` steps of `T`
(`TauCeti.dynEntourage_prodMap`). Products of dynamical covers are dynamical covers, which bounds
the minimal cardinality of a dynamical cover of the product by the product of the minimal
cardinalities for the factors (`TauCeti.coverMincard_prodMap_le`); products of dynamical nets are
dynamical nets, which bounds the maximal cardinality of a dynamical net of the product below
(`TauCeti.netMaxcard_mul_le_netMaxcard_prodMap`). The upper bound for the exponential growth rate
of a product is the sum of the upper rates, and the lower bound is the sum of an upper and a lower
rate; Mathlib's `coverEntropyInf_eq_coverEntropy` shows that the lower and upper entropies of `T`
on an invariant set agree, so the bounds meet.

## Main results

* `TauCeti.dynEntourage_prodMap`: dynamical entourages of a product.
* `TauCeti.coverEntropy_prodMap_le`: `h(S × T) ≤ h(S) + h(T)`.
* `TauCeti.le_coverEntropy_prodMap`: `h(S) + h(T) ≤ h(S × T)`.
* `TauCeti.coverEntropy_prodMap`, `TauCeti.coverEntropy_prodMap_univ`: `h(S × T) = h(S) + h(T)`.

## References

* P. Walters, *An Introduction to Ergodic Theory*, Graduate Texts in Mathematics 79, Springer,
  1982, Theorem 7.10(iv). The upper bound follows the product of spanning sets and the lower bound
  the product of separated sets.
-/

public section

namespace TauCeti

open Dynamics Set Filter ExpGrowth
open scoped Uniformity ENNReal

variable {X Y : Type*} {S : X → X} {T : Y → Y}

/-- Two points are `entourageProd U V`-close for `n` steps of `Prod.map S T` exactly when their
first coordinates are `U`-close for `n` steps of `S` and their second coordinates are `V`-close for
`n` steps of `T`. -/
@[simp]
theorem dynEntourage_prodMap (S : X → X) (T : Y → Y) (U : SetRel X X) (V : SetRel Y Y) (n : ℕ) :
    dynEntourage (Prod.map S T) (entourageProd U V) n =
      entourageProd (dynEntourage S U n) (dynEntourage T V n) := by
  ext ⟨⟨x, y⟩, ⟨x', y'⟩⟩
  simp only [mem_dynEntourage, Prod.map_iterate, Prod.map_apply, mem_entourageProd]
  exact ⟨fun h ↦ ⟨fun k hk ↦ (h k hk).1, fun k hk ↦ (h k hk).2⟩,
    fun h k hk ↦ ⟨h.1 k hk, h.2 k hk⟩⟩

/-- The product of a dynamical cover of `F` and a dynamical cover of `G` is a dynamical cover of
`F ×ˢ G` for the product map and the product entourage. -/
theorem _root_.Dynamics.IsDynCoverOf.prodMap {F : Set X} {G : Set Y} {U : SetRel X X}
    {V : SetRel Y Y} {n : ℕ} {s : Set X} {t : Set Y}
    (hs : IsDynCoverOf S F U n s) (ht : IsDynCoverOf T G V n t) :
    IsDynCoverOf (Prod.map S T) (F ×ˢ G) (entourageProd U V) n (s ×ˢ t) := by
  rintro ⟨x, y⟩ ⟨hx, hy⟩
  obtain ⟨x', hx', hxx'⟩ := hs hx
  obtain ⟨y', hy', hyy'⟩ := ht hy
  refine ⟨(x', y'), mk_mem_prod hx' hy', ?_⟩
  rw [dynEntourage_prodMap]
  exact mem_entourageProd.mpr ⟨hxx', hyy'⟩

/-- The product of a dynamical net in `F` and a dynamical net in `G` is a dynamical net in
`F ×ˢ G` for the product map and the product entourage. -/
theorem _root_.Dynamics.IsDynNetIn.prodMap {F : Set X} {G : Set Y} {U : SetRel X X}
    {V : SetRel Y Y} {n : ℕ} {s : Set X} {t : Set Y}
    (hs : IsDynNetIn S F U n s) (ht : IsDynNetIn T G V n t) :
    IsDynNetIn (Prod.map S T) (F ×ˢ G) (entourageProd U V) n (s ×ˢ t) := by
  refine ⟨prod_mono hs.1 ht.1, fun p hp q hq hpq ↦ ?_⟩
  simp only [Function.onFun, dynEntourage_prodMap, inv_entourageProd, ball_entourageProd]
  rcases ne_or_eq p.1 q.1 with h | h
  · exact disjoint_prod.mpr (.inl (hs.2 hp.1 hq.1 h))
  · have h' : p.2 ≠ q.2 := fun h' ↦ hpq (Prod.ext h h')
    exact disjoint_prod.mpr (.inr (ht.2 hp.2 hq.2 h'))

/-- The minimal cardinality of a dynamical cover of `F ×ˢ G` for a product map and a product
entourage is at most the product of the minimal cardinalities of dynamical covers of `F` and `G`
for the factors. -/
theorem coverMincard_prodMap_le (S : X → X) (T : Y → Y) (F : Set X) (G : Set Y)
    (U : SetRel X X) (V : SetRel Y Y) (n : ℕ) :
    coverMincard (Prod.map S T) (F ×ˢ G) (entourageProd U V) n ≤
      coverMincard S F U n * coverMincard T G V n := by
  classical
  rcases F.eq_empty_or_nonempty with rfl | hF
  · simp [coverMincard_empty]
  rcases G.eq_empty_or_nonempty with rfl | hG
  · simp [coverMincard_empty]
  have hS1 := (one_le_coverMincard_iff S F U n).mpr hF
  have hT1 := (one_le_coverMincard_iff T G V n).mpr hG
  rcases eq_or_ne (coverMincard S F U n) ⊤ with hS | hS
  · rw [hS, ENat.top_mul ((zero_lt_one.trans_le hT1).ne')]
    exact le_top
  · rcases eq_or_ne (coverMincard T G V n) ⊤ with hT | hT
    · rw [hT, ENat.mul_top ((zero_lt_one.trans_le hS1).ne')]
      exact le_top
    · obtain ⟨s, hs, hs_card⟩ := (coverMincard_finite_iff S F U n).mp (lt_top_iff_ne_top.mpr hS)
      obtain ⟨t, ht, ht_card⟩ := (coverMincard_finite_iff T G V n).mp (lt_top_iff_ne_top.mpr hT)
      have hst : IsDynCoverOf (Prod.map S T) (F ×ˢ G) (entourageProd U V) n
          ((s ×ˢ t : Finset (X × Y)) : Set (X × Y)) := by
        rw [Finset.coe_product]
        exact hs.prodMap ht
      refine hst.coverMincard_le_card.trans ?_
      rw [Finset.card_product, ← hs_card, ← ht_card, Nat.cast_mul]

/-- The product of the maximal cardinalities of dynamical nets in `F` and in `G` for the factors is
at most the maximal cardinality of a dynamical net in `F ×ˢ G` for the product map and the product
entourage. -/
theorem netMaxcard_mul_le_netMaxcard_prodMap (S : X → X) (T : Y → Y) (F : Set X) (G : Set Y)
    (U : SetRel X X) (V : SetRel Y Y) (n : ℕ) :
    netMaxcard S F U n * netMaxcard T G V n ≤
      netMaxcard (Prod.map S T) (F ×ˢ G) (entourageProd U V) n := by
  classical
  rw [netMaxcard, ENat.iSup_mul]
  refine iSup_le fun s ↦ ?_
  rw [ENat.iSup_mul]
  refine iSup_le fun hs ↦ ?_
  rw [netMaxcard, ENat.mul_iSup]
  refine iSup_le fun t ↦ ?_
  rw [ENat.mul_iSup]
  refine iSup_le fun ht ↦ ?_
  have hst : IsDynNetIn (Prod.map S T) (F ×ˢ G) (entourageProd U V) n
      ((s ×ˢ t : Finset (X × Y)) : Set (X × Y)) := by
    rw [Finset.coe_product]
    exact hs.prodMap ht
  refine le_trans ?_ (le_iSup₂ (f := fun (u : Finset (X × Y))
    (_ : IsDynNetIn (Prod.map S T) (F ×ˢ G) (entourageProd U V) n u) ↦ (u.card : ℕ∞)) _ hst)
  rw [Finset.card_product, Nat.cast_mul]

variable [UniformSpace X] [UniformSpace Y]

/-- The topological entropy of a product map on `F ×ˢ G` is at most the sum of the entropies of the
factors on `F` and on `G`. -/
theorem coverEntropy_prodMap_le (S : X → X) (T : Y → Y) (F : Set X) (G : Set Y) :
    coverEntropy (Prod.map S T) (F ×ˢ G) ≤ coverEntropy S F + coverEntropy T G := by
  rcases F.eq_empty_or_nonempty with rfl | hF
  · simp
  rcases G.eq_empty_or_nonempty with rfl | hG
  · simp
  refine iSup₂_le fun W hW ↦ ?_
  obtain ⟨U, hU, V, hV, hUV⟩ := entourageProd_subset hW
  have hS0 := coverEntropyEntourage_nonneg S hF U
  have hT0 := coverEntropyEntourage_nonneg T hG V
  calc coverEntropyEntourage (Prod.map S T) (F ×ˢ G) W
      ≤ coverEntropyEntourage (Prod.map S T) (F ×ˢ G) (entourageProd U V) :=
        coverEntropyEntourage_antitone _ _ hUV
    _ ≤ expGrowthSup ((fun n ↦ (coverMincard S F U n : ℝ≥0∞)) *
          fun n ↦ (coverMincard T G V n : ℝ≥0∞)) :=
        expGrowthSup_monotone fun n ↦ by
          simp only [Pi.mul_apply, ← ENat.toENNReal_mul]
          exact ENat.toENNReal_mono (coverMincard_prodMap_le S T F G U V n)
    _ ≤ coverEntropyEntourage S F U + coverEntropyEntourage T G V :=
        expGrowthSup_mul_le (.inl (hS0.trans_lt' EReal.bot_lt_zero).ne')
          (.inr (hT0.trans_lt' EReal.bot_lt_zero).ne')
    _ ≤ coverEntropy S F + coverEntropy T G :=
        add_le_add (coverEntropyEntourage_le_coverEntropy S F hU)
          (coverEntropyEntourage_le_coverEntropy T G hV)

/-- If `T` maps `G` into itself, the sum of the topological entropies of `S` on `F` and of `T` on
`G` is at most the entropy of the product map on `F ×ˢ G`. -/
theorem le_coverEntropy_prodMap (S : X → X) {T : Y → Y} (F : Set X) {G : Set Y}
    (hG : MapsTo T G G) :
    coverEntropy S F + coverEntropy T G ≤ coverEntropy (Prod.map S T) (F ×ˢ G) := by
  rw [← coverEntropyInf_eq_coverEntropy T hG, coverEntropy_eq_iSup_netEntropyEntourage S F,
    coverEntropyInf_eq_iSup_netEntropyInfEntourage T G,
    iSup_subtype' (p := fun U : SetRel X X ↦ U ∈ 𝓤 X),
    iSup_subtype' (p := fun V : SetRel Y Y ↦ V ∈ 𝓤 Y), AddQuantale.iSup_add_distrib]
  refine iSup_le fun U ↦ ?_
  rw [AddQuantale.add_iSup_distrib]
  refine iSup_le fun V ↦ ?_
  refine le_trans ?_ (netEntropyEntourage_le_coverEntropy (Prod.map S T) (F ×ˢ G)
    (entourageProd_mem_uniformity U.property V.property))
  refine le_expGrowthSup_mul.trans (expGrowthSup_monotone fun n ↦ ?_)
  simp only [Pi.mul_apply, ← ENat.toENNReal_mul]
  exact ENat.toENNReal_mono (netMaxcard_mul_le_netMaxcard_prodMap S T F G U V n)

/-- **Product formula for topological entropy.** If `T` maps `G` into itself, the topological
entropy of the product map on `F ×ˢ G` is the sum of the entropies of `S` on `F` and of `T` on
`G`. -/
theorem coverEntropy_prodMap (S : X → X) {T : Y → Y} (F : Set X) {G : Set Y}
    (hG : MapsTo T G G) :
    coverEntropy (Prod.map S T) (F ×ˢ G) = coverEntropy S F + coverEntropy T G :=
  (coverEntropy_prodMap_le S T F G).antisymm (le_coverEntropy_prodMap S F hG)

/-- **Product formula for topological entropy** on the whole space: the topological entropy of the
product of two maps of uniform spaces is the sum of their entropies. -/
theorem coverEntropy_prodMap_univ (S : X → X) (T : Y → Y) :
    coverEntropy (Prod.map S T) univ = coverEntropy S univ + coverEntropy T univ := by
  rw [← univ_prod_univ]
  exact coverEntropy_prodMap S univ (mapsTo_univ T univ)

end TauCeti
