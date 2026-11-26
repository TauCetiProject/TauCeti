/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.SetTheory.Cardinal.Partition.EndHomogeneous
public import TauCeti.SetTheory.Cardinal.Partition.Pigeonhole
public import TauCeti.SetTheory.Cardinal.Beth
import TauCeti.Order.Fin.Tuple
import TauCeti.Order.Hom.Basic

/-!
# The Erdős–Rado theorem

For an infinite cardinal `κ`, write `ℶₙ(κ)` for the `n`-fold iterated exponential,
`ℶ₀(κ) = κ` and `ℶₙ₊₁(κ) = 2 ^ ℶₙ(κ)` (`Cardinal.iteratedTwoPow`, from
`TauCeti.SetTheory.Cardinal.Beth`). The Erdős–Rado theorem is the partition relation
`ℶₙ(κ)⁺ → (κ⁺)ⁿ⁺¹_κ`: every colouring of the increasing `(n + 1)`-tuples of a
linear order of cardinality `ℶₙ(κ)⁺` by at most `κ` colours has a homogeneous set of cardinality
`κ⁺`. At `n = 1` it is `(2 ^ κ)⁺ → (κ⁺)²_κ`.

Indexed by beth numbers, `ℶ_ (α + n) = ℶₙ(ℶ_ α)` (`Cardinal.iteratedTwoPow_beth`), the theorem
reads `ℶ_ (α + n)⁺ → (ℶ_ α⁺)ⁿ⁺¹_ℶ_α`; since `ℶ_ (α + n)⁺ ≤ ℶ_ (α + n + 1)`, it then also holds from
`ℶ_ (α + n + 1)` (`Cardinal.erdos_rado_beth_add_one`). This is the form in which Morley's proof
of the Hanf number bound for `Lω₁ω` applies it at every level `α`.

## Main results

* `Cardinal.erdos_rado`: `ℶₙ(κ)⁺ → (κ⁺)ⁿ⁺¹_κ` for infinite `κ`.
* `Cardinal.erdos_rado_beth`: `ℶ_ (α + n)⁺ → (ℶ_ α⁺)ⁿ⁺¹_ℶ_α`.
* `Cardinal.erdos_rado_beth_add_one`: `ℶ_ (α + n + 1) → (ℶ_ α⁺)ⁿ⁺¹_ℶ_α`.

## Implementation notes

The proof is by induction on `n`, starting from the pigeonhole principle `κ⁺ → (κ⁺)¹_κ`
(`Cardinal.partitionRel_succ_one`). For the step, a colouring of the increasing `(n + 2)`-tuples
of a well-order of cardinality `(2 ^ ℶₙ(κ))⁺` has an end-homogeneous set `H` of cardinality
`ℶₙ(κ)⁺` (`TauCeti.exists_isEndHomogeneousOn`). On the points of `H` below some other point of `H`,
the colour of an `(n + 2)`-tuple is a function of its first `n + 1` entries, and the induction
hypothesis applies to that induced colouring of `(n + 1)`-tuples.

## References

* P. Erdős and R. Rado, *A partition calculus in set theory*, Bull. Amer. Math. Soc. 62 (1956).
* D. Marker, *Lectures on Infinitary Model Theory*, Lecture Notes in Logic 46 (2016), Theorem 5.5
  and Corollary 5.6.
-/

public section

universe u

open Cardinal Set TauCeti

namespace Cardinal

/-- **From end-homogeneous to homogeneous sets.** Let `H` be end-homogeneous for a colouring `c`
of increasing `(n + 2)`-tuples, and `H'` the points of `H` below some other point of `H`. On `H'`
the colour of a tuple is determined by its first `n + 1` entries, so a partition relation for
`(n + 1)`-tuples on `H'` gives a homogeneous set for `c`. -/
private theorem exists_isHomogeneousOn_of_isEndHomogeneousOn {J D : Type u} [LinearOrder J]
    {n : ℕ} {c : (Fin (n + 2) ↪o J) → D} {H : Set J} (hc : IsEndHomogeneousOn c H)
    {lam μ : Cardinal.{u}} (h : PartitionRel #{x ∈ H | ∃ y ∈ H, x < y} lam (n + 1) μ)
    (hD : #D ≤ μ) : ∃ G : Set J, lam ≤ #G ∧ IsHomogeneousOn c G := by
  set H' := {x ∈ H | ∃ y ∈ H, x < y}
  choose! up hupH hup using fun x (hx : x ∈ H') ↦ hx.2
  -- Extend an increasing tuple from `H'` by a point of `H` above it.
  let ext (s : Fin (n + 1) ↪o H') : Fin (n + 2) ↪o J :=
    OrderEmbedding.snoc (s.trans (OrderEmbedding.subtype _)) (up (s (Fin.last n))) fun k ↦ by
      simpa using (Subtype.coe_le_coe.2 (s.monotone (Fin.le_last k))).trans_lt
        (hup _ (s (Fin.last n)).property)
  obtain ⟨G, hG, hd⟩ := partitionRel_def.1 h H' D rfl hD fun s ↦ c (ext s)
  -- The colour of a tuple from `G` is that of its first `n + 1` entries, extended by `ext`.
  have key (s : Fin (n + 2) ↪o J) (hs : ∀ k, s k ∈ Subtype.val '' G) :
      ∃ s₀ : Fin (n + 1) ↪o H', (∀ k, s₀ k ∈ G) ∧ c s = c (ext s₀) := by
    obtain ⟨s₀, hs₀G, hs₀⟩ := (OrderEmbedding.subtype (· ∈ H')).exists_trans_eq_of_forall_mem_image
      (Fin.castSuccOrderEmb.trans s) fun k ↦ hs k.castSucc
    have hsH (k : Fin (n + 2)) : s k ∈ H := by
      obtain ⟨x, -, hx⟩ := hs k
      exact hx ▸ x.property.1
    refine ⟨s₀, hs₀G, isEndHomogeneousOn_def.1 hc _ _ hsH (fun k ↦ ?_) ?_⟩
    · induction k using Fin.lastCases with
      | last => simpa [ext] using hupH _ (s₀ (Fin.last n)).property
      | cast k => simpa [ext] using (s₀ k).property.1
    · intro k
      simpa [ext] using (DFunLike.congr_fun hs₀ k).symm
  refine ⟨Subtype.val '' G, by rwa [mk_image_eq Subtype.val_injective],
    isHomogeneousOn_def.2 fun s t hs ht ↦ ?_⟩
  obtain ⟨s₀, hs₀G, hs₀⟩ := key s hs
  obtain ⟨t₀, ht₀G, ht₀⟩ := key t ht
  rw [hs₀, ht₀]
  exact isHomogeneousOn_def.1 hd s₀ t₀ hs₀G ht₀G

/-- **The Erdős–Rado theorem**, `ℶₙ(κ)⁺ → (κ⁺)ⁿ⁺¹_κ` for infinite `κ`: every colouring of the
increasing `(n + 1)`-tuples of a linear order of cardinality `ℶₙ(κ)⁺` by at most `κ` colours has a
homogeneous set of cardinality at least `κ⁺`. -/
theorem erdos_rado {κ : Cardinal.{u}} (hκ : ℵ₀ ≤ κ) :
    ∀ n : ℕ, PartitionRel (Order.succ (iteratedTwoPow κ n)) (Order.succ κ) (n + 1) κ
  | 0 => by simpa using partitionRel_succ_one hκ
  | n + 1 => by
    set lam := iteratedTwoPow κ n
    have hlam : ℵ₀ ≤ lam := hκ.trans (le_iteratedTwoPow κ n)
    rw [iteratedTwoPow_succ, partitionRel_iff_of_mk_eq _ (mk_ord_toType _)]
    intro D hD c
    obtain ⟨H, hH, hc⟩ := exists_isEndHomogeneousOn hlam (mk_ord_toType _).ge
      (hD.trans (le_iteratedTwoPow κ n)) c
    refine exists_isHomogeneousOn_of_isEndHomogeneousOn hc
      ((erdos_rado hκ n).mono ?_ le_rfl le_rfl) hD
    -- Removing the largest point of `H`, if any, leaves `lam⁺` points.
    have hsub : (H \ {x ∈ H | ∃ y ∈ H, x < y}).Subsingleton := by
      rintro a ⟨ha, ha'⟩ b ⟨hb, hb'⟩
      by_contra hab
      rcases lt_or_gt_of_ne hab with hlt | hlt
      · exact ha' ⟨ha, b, hb, hlt⟩
      · exact hb' ⟨hb, a, ha, hlt⟩
    by_contra! hlt
    have hle := (mk_sdiff_add_mk (sep_subset H _)).symm.trans_le
      (add_le_add (mk_le_one_iff_set_subsingleton.2 hsub) (Order.lt_succ_iff.1 hlt))
    rw [add_comm, add_one_eq hlam] at hle
    exact (Order.lt_succ lam).not_ge (hH.trans hle)

/-- **The Erdős–Rado theorem for beth numbers**, `ℶ_ (α + n)⁺ → (ℶ_ α⁺)ⁿ⁺¹_ℶ_α`. -/
theorem erdos_rado_beth (α : Ordinal.{u}) (n : ℕ) :
    PartitionRel (Order.succ (ℶ_ (α + n))) (Order.succ (ℶ_ α)) (n + 1) (ℶ_ α) := by
  simpa [iteratedTwoPow_beth] using erdos_rado (aleph0_le_beth α) n

/-- **The Erdős–Rado theorem for beth numbers**, from a set of cardinality at least
`ℶ_ (α + n + 1)`: `ℶ_ (α + n + 1) → (ℶ_ α⁺)ⁿ⁺¹_ℶ_α`. -/
theorem erdos_rado_beth_add_one (α : Ordinal.{u}) (n : ℕ) :
    PartitionRel (ℶ_ (α + n + 1)) (Order.succ (ℶ_ α)) (n + 1) (ℶ_ α) :=
  (erdos_rado_beth α n).mono (Order.succ_le_of_lt (beth_lt_beth.2 (lt_add_one _))) le_rfl le_rfl

end Cardinal
