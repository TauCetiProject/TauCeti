/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Order.Hom.PowersetCard
public import Mathlib.SetTheory.Cardinal.Order
import Mathlib.SetTheory.Cardinal.Arithmetic

/-!
# Homogeneous sets and the partition relation

This file sets up the vocabulary of the partition calculus of Erdős and Rado. A colouring of the
increasing `n`-tuples of a preorder `I` by a type `C` is a map `c : (Fin n ↪o I) → C`; in a linear
order increasing `n`-tuples are the same thing as `n`-element subsets
(`Set.powersetCard.ofFinEmbEquiv`).

* `TauCeti.IsHomogeneousOn c H`: all increasing tuples with entries in `H` have the same colour.
* `TauCeti.IsEndHomogeneousOn c H`: for a colouring of increasing `(n + 2)`-tuples, the colour of
  a tuple from `H` does not depend on its last entry.
* `Cardinal.PartitionRel κ lam n μ`, the relation `κ → (lam)ⁿ_μ`: every colouring of the
  increasing `n`-tuples of a linear order of cardinality `κ` by a type of cardinality at most `μ`
  has a homogeneous set of cardinality at least `lam`.

For `μ ≥ 1` the relation agrees with that of Erdős and Rado. At `μ = 0` it differs: a colour type
of cardinality `0` is allowed and every homogeneous set counts, so `0 → (0)¹_0` holds here,
whereas their formulation asks for a homogeneous set of a named colour.

## Main results

* `TauCeti.IsHomogeneousOn.mono`, `TauCeti.IsEndHomogeneousOn.mono`: both notions pass to subsets.
* `TauCeti.IsHomogeneousOn.isEndHomogeneousOn`: homogeneous sets are end-homogeneous.
* `TauCeti.isEndHomogeneousOn_of_encard_le`: a set with at most `n + 2` points is end-homogeneous
  for every colouring of increasing `(n + 2)`-tuples.
* `TauCeti.isHomogeneousOn_comp_trans_iff`, `TauCeti.isHomogeneousOn_comp_orderIso_iff`:
  homogeneous sets of a colouring restricted along an order embedding, or transported along an
  order isomorphism.
* `TauCeti.isHomogeneousOn_comp_ofFinEmbEquiv_iff`: homogeneity in a linear order is homogeneity
  for the induced colouring of `n`-element subsets.
* `Cardinal.PartitionRel.mono`: the relation is monotone in the source and antitone in the target
  and in the number of colours.
* `Cardinal.partitionRel_iff_powersetCard`, `Cardinal.partitionRel_iff_of_mk_eq`: the order-free
  form, stated with colourings of `n`-element subsets; consequently it suffices to test the
  relation on a single linear order of cardinality `κ`, for instance a well-order.
* `Cardinal.partitionRel_one_iff`: for `n = 1`, the relation is a statement about the fibres of
  maps into the colour type.

## References

* P. Erdős and R. Rado, *A partition calculus in set theory*, Bull. Amer. Math. Soc. 62 (1956).
* D. Marker, *Lectures on Infinitary Model Theory*, Lecture Notes in Logic 46 (2016), §5.1.
-/

public section

universe u

open Cardinal Set

namespace TauCeti

section Homogeneous

variable {I K C : Type*} {n : ℕ}

section Preorder

variable [Preorder I] [Preorder K]

/-- A set `H` is *homogeneous* for a colouring `c` of the increasing `n`-tuples of `I` if all
increasing `n`-tuples with entries in `H` get the same colour. -/
def IsHomogeneousOn (c : (Fin n ↪o I) → C) (H : Set I) : Prop :=
  ∀ s t : Fin n ↪o I, (∀ k, s k ∈ H) → (∀ k, t k ∈ H) → c s = c t

theorem isHomogeneousOn_def {c : (Fin n ↪o I) → C} {H : Set I} :
    IsHomogeneousOn c H ↔
      ∀ s t : Fin n ↪o I, (∀ k, s k ∈ H) → (∀ k, t k ∈ H) → c s = c t :=
  Iff.rfl

/-- A set `H` is *end-homogeneous* for a colouring `c` of the increasing `(n + 2)`-tuples of `I` if
two increasing tuples with entries in `H` that agree on their first `n + 1` entries get the same
colour. -/
def IsEndHomogeneousOn (c : (Fin (n + 2) ↪o I) → C) (H : Set I) : Prop :=
  ∀ s t : Fin (n + 2) ↪o I, (∀ k, s k ∈ H) → (∀ k, t k ∈ H) →
    (∀ k : Fin (n + 1), s k.castSucc = t k.castSucc) → c s = c t

theorem isEndHomogeneousOn_def {c : (Fin (n + 2) ↪o I) → C} {H : Set I} :
    IsEndHomogeneousOn c H ↔
      ∀ s t : Fin (n + 2) ↪o I, (∀ k, s k ∈ H) → (∀ k, t k ∈ H) →
        (∀ k : Fin (n + 1), s k.castSucc = t k.castSucc) → c s = c t :=
  Iff.rfl

theorem IsHomogeneousOn.mono {c : (Fin n ↪o I) → C} {H H' : Set I} (hH : H' ⊆ H)
    (h : IsHomogeneousOn c H) : IsHomogeneousOn c H' :=
  fun s t hs ht ↦ h s t (fun k ↦ hH (hs k)) (fun k ↦ hH (ht k))

theorem IsEndHomogeneousOn.mono {c : (Fin (n + 2) ↪o I) → C} {H H' : Set I} (hH : H' ⊆ H)
    (h : IsEndHomogeneousOn c H) : IsEndHomogeneousOn c H' :=
  fun s t hs ht ↦ h s t (fun k ↦ hH (hs k)) (fun k ↦ hH (ht k))

/-- A homogeneous set is end-homogeneous. -/
theorem IsHomogeneousOn.isEndHomogeneousOn {c : (Fin (n + 2) ↪o I) → C} {H : Set I}
    (h : IsHomogeneousOn c H) : IsEndHomogeneousOn c H :=
  fun s t hs ht _ ↦ h s t hs ht

/-- For `n = 0` every set is homogeneous: there is exactly one increasing `0`-tuple. -/
@[simp]
theorem isHomogeneousOn_zero (c : (Fin 0 ↪o I) → C) (H : Set I) : IsHomogeneousOn c H :=
  fun _ _ _ _ ↦ congrArg c <| RelEmbedding.ext fun k ↦ k.elim0

/-- The empty set is homogeneous for every colouring. -/
@[simp]
theorem isHomogeneousOn_empty (c : (Fin n ↪o I) → C) : IsHomogeneousOn c ∅ := by
  cases n with
  | zero => exact isHomogeneousOn_zero c ∅
  | succ n => exact fun s _ hs _ ↦ (hs 0).elim

/-- The empty set is end-homogeneous for every colouring. -/
@[simp]
theorem isEndHomogeneousOn_empty (c : (Fin (n + 2) ↪o I) → C) : IsEndHomogeneousOn c ∅ :=
  (isHomogeneousOn_empty c).isEndHomogeneousOn

/-- A set with at most `n + 2` points is end-homogeneous for every colouring of increasing
`(n + 2)`-tuples: two such tuples from it that agree on their first `n + 1` entries also agree on
their last entry. -/
theorem isEndHomogeneousOn_of_encard_le (c : (Fin (n + 2) ↪o I) → C) {H : Set I}
    (hH : H.encard ≤ n + 2) : IsEndHomogeneousOn c H := by
  intro s t hs ht hst
  set R := range fun k : Fin (n + 1) ↦ s k.castSucc
  have hRH : R ⊆ H := range_subset_iff.2 fun k ↦ hs _
  have hR : R.encard = n + 1 := by
    rw [Function.Injective.encard_range fun a b h ↦ Fin.castSucc_injective _ (s.injective h)]
    simp
  -- The last entries of `s` and `t` both lie in `H \ R`, which has at most one point.
  have hdiff : (H \ R).encard ≤ 1 := by
    refine (ENat.add_le_add_iff_right (k := n + 1) (by simp)).1 ?_
    rw [← hR, encard_sdiff_add_encard_of_subset hRH, hR, add_comm 1, add_assoc,
      one_add_one_eq_two]
    exact hH
  have hlast : s (Fin.last _) = t (Fin.last _) := by
    refine encard_le_one_iff.1 hdiff _ _ ⟨hs _, ?_⟩ ⟨ht _, ?_⟩
    · rintro ⟨k, hk⟩
      exact Fin.castSucc_ne_last k (s.injective hk)
    · rintro ⟨k, hk⟩
      exact Fin.castSucc_ne_last k (t.injective ((hst k).symm.trans hk))
  exact congrArg c <| RelEmbedding.ext <| Fin.lastCases hlast hst

/-- For `n = 1`, a set is homogeneous for the colouring of points by `f` exactly when `f` is
constant on it. -/
theorem isHomogeneousOn_one_iff {f : I → C} {H : Set I} :
    IsHomogeneousOn (fun s : Fin 1 ↪o I ↦ f (s 0)) H ↔ ∀ x ∈ H, ∀ y ∈ H, f x = f y := by
  refine ⟨fun h x hx y hy ↦ ?_, fun h s t hs ht ↦ h _ (hs 0) _ (ht 0)⟩
  exact h (.ofStrictMono _ (Subsingleton.strictMono _))
    (.ofStrictMono _ (Subsingleton.strictMono _)) (fun _ ↦ hx) (fun _ ↦ hy)

/-- **Restriction of a colouring along an order embedding.** The homogeneous sets of the
colouring `s ↦ c (s.trans e)` of increasing tuples of `K` are exactly the sets whose image under
`e` is homogeneous for `c`. -/
theorem isHomogeneousOn_comp_trans_iff (e : K ↪o I) {c : (Fin n ↪o I) → C} {H : Set K} :
    IsHomogeneousOn (fun s ↦ c (s.trans e)) H ↔ IsHomogeneousOn c (e '' H) := by
  refine ⟨fun h s t hs ht ↦ ?_, fun h s t hs ht ↦
    h _ _ (fun k ↦ mem_image_of_mem e (hs k)) (fun k ↦ mem_image_of_mem e (ht k))⟩
  -- An increasing tuple with entries in `e '' H` is the image of an increasing tuple in `H`.
  have lift (s : Fin n ↪o I) (hs : ∀ k, s k ∈ e '' H) :
      ∃ s' : Fin n ↪o K, (∀ k, s' k ∈ H) ∧ s'.trans e = s := by
    choose f hfH hf using hs
    refine ⟨.ofStrictMono f fun a b hab ↦ ?_, hfH, RelEmbedding.ext hf⟩
    rw [← e.lt_iff_lt, hf, hf]
    exact s.strictMono hab
  obtain ⟨s', hs', rfl⟩ := lift s hs
  obtain ⟨t', ht', rfl⟩ := lift t ht
  exact h s' t' hs' ht'

/-- **Transport of homogeneity along an order isomorphism.** -/
theorem isHomogeneousOn_comp_orderIso_iff (e : K ≃o I) {c : (Fin n ↪o I) → C} {H : Set I} :
    IsHomogeneousOn (fun s ↦ c (s.trans e.toOrderEmbedding)) (e ⁻¹' H) ↔ IsHomogeneousOn c H := by
  rw [isHomogeneousOn_comp_trans_iff, OrderIso.coe_toOrderEmbedding, e.image_preimage]

end Preorder

section LinearOrder

variable [LinearOrder I]

/-- **Homogeneity for colourings of `n`-element subsets.** In a linear order, a set `H` is
homogeneous for the colouring of increasing `n`-tuples induced by a colouring `d` of the
`n`-element subsets exactly when all `n`-element subsets of `H` get the same colour. -/
theorem isHomogeneousOn_comp_ofFinEmbEquiv_iff {d : powersetCard I n → C} {H : Set I} :
    IsHomogeneousOn (d ∘ powersetCard.ofFinEmbEquiv) H ↔
      ∀ s t : powersetCard I n, (s : Set I) ⊆ H → (t : Set I) ⊆ H → d s = d t := by
  have key (s : powersetCard I n) :
      (s : Set I) ⊆ H ↔ ∀ k, powersetCard.ofFinEmbEquiv.symm s k ∈ H := by
    rw [← range_subset_iff, show (s : Set I) = range (powersetCard.ofFinEmbEquiv.symm s) from
      ext fun x ↦ (powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem s x).symm]
  refine ⟨fun h s t hs ht ↦ ?_, fun h s t hs ht ↦ ?_⟩
  · simpa using h _ _ ((key s).1 hs) ((key t).1 ht)
  · simpa using h _ _ ((key _).2 (by simpa using hs)) ((key _).2 (by simpa using ht))

end LinearOrder

end Homogeneous

end TauCeti

namespace Cardinal

open TauCeti

/-- The *partition relation* `κ → (lam)ⁿ_μ`: for every linear order `J` of cardinality `κ`, every
colouring of the increasing `n`-tuples of `J` by a type of cardinality at most `μ` has a homogeneous
set of cardinality at least `lam`. By `Cardinal.partitionRel_iff_of_mk_eq` the relation does not
depend on the linear order chosen. -/
def PartitionRel (κ lam : Cardinal.{u}) (n : ℕ) (μ : Cardinal.{u}) : Prop :=
  ∀ (J : Type u) [LinearOrder J] (D : Type u), #J = κ → #D ≤ μ →
    ∀ c : (Fin n ↪o J) → D, ∃ H : Set J, lam ≤ #H ∧ IsHomogeneousOn c H

variable {κ κ' lam lam' μ μ' : Cardinal.{u}} {n : ℕ}

theorem partitionRel_def :
    PartitionRel κ lam n μ ↔
      ∀ (J : Type u) [LinearOrder J] (D : Type u), #J = κ → #D ≤ μ →
        ∀ c : (Fin n ↪o J) → D, ∃ H : Set J, lam ≤ #H ∧ IsHomogeneousOn c H :=
  Iff.rfl

/-- The partition relation `κ → (lam)ⁿ_μ` persists when the source `κ` grows and the target `lam`
and the number of colours `μ` shrink. -/
theorem PartitionRel.mono (h : PartitionRel κ lam n μ) (hκ : κ ≤ κ') (hlam : lam' ≤ lam)
    (hμ : μ' ≤ μ) : PartitionRel κ' lam' n μ' := by
  intro J _ D hJ hD c
  obtain ⟨S, hS⟩ := le_mk_iff_exists_set.1 (hκ.trans hJ.ge)
  obtain ⟨H, hH, hc⟩ := h S D hS (hD.trans hμ) fun s ↦ c (s.trans (OrderEmbedding.subtype _))
  refine ⟨OrderEmbedding.subtype _ '' H, ?_, (isHomogeneousOn_comp_trans_iff _).1 hc⟩
  rw [mk_image_eq (OrderEmbedding.subtype _).injective]
  exact hlam.trans hH

/-- **The order-free form of the partition relation.** `κ → (lam)ⁿ_μ` holds exactly when every
colouring of the `n`-element subsets of a type of cardinality `κ` by a type of cardinality at most
`μ` has a set of cardinality at least `lam` all of whose `n`-element subsets get the same
colour. -/
theorem partitionRel_iff_powersetCard :
    PartitionRel κ lam n μ ↔
      ∀ (X D : Type u), #X = κ → #D ≤ μ → ∀ c : powersetCard X n → D,
        ∃ H : Set X, lam ≤ #H ∧
          ∀ s t : powersetCard X n, (s : Set X) ⊆ H → (t : Set X) ⊆ H → c s = c t := by
  refine ⟨fun h X D hX hD c ↦ ?_, fun h J _ D hJ hD c ↦ ?_⟩
  · obtain ⟨_, _⟩ := exists_wellFoundedLT X
    obtain ⟨H, hH, hc⟩ := h X D hX hD (c ∘ powersetCard.ofFinEmbEquiv)
    exact ⟨H, hH, isHomogeneousOn_comp_ofFinEmbEquiv_iff.1 hc⟩
  · obtain ⟨H, hH, hc⟩ := h J D hJ hD (c ∘ powersetCard.ofFinEmbEquiv.symm)
    refine ⟨H, hH, ?_⟩
    simpa [Function.comp_assoc] using isHomogeneousOn_comp_ofFinEmbEquiv_iff.2 hc

/-- A colouring of the `n`-element subsets of `Y` and a bijection `g : X ≃ Y` give a colouring
of the `n`-element subsets of `X`; a set all of whose `n`-element subsets get the same colour for
it is carried by `g` to such a set for the original colouring. -/
private theorem homogeneous_image_of_map_equiv {X Y D : Type*} (g : X ≃ Y)
    {c : powersetCard Y n → D} {H : Set X}
    (hH : ∀ s t : powersetCard X n, (s : Set X) ⊆ H → (t : Set X) ⊆ H →
      c (powersetCard.map n g.toEmbedding s) = c (powersetCard.map n g.toEmbedding t)) :
    ∀ s t : powersetCard Y n, (s : Set Y) ⊆ g '' H → (t : Set Y) ⊆ g '' H → c s = c t := by
  have hmap (s : powersetCard Y n) :
      powersetCard.map n g.toEmbedding (powersetCard.map n g.symm.toEmbedding s) = s :=
    Subtype.ext <| by simp [Finset.map_map]
  have hsub (s : powersetCard Y n) (hs : (s : Set Y) ⊆ g '' H) :
      ((powersetCard.map n g.symm.toEmbedding s : powersetCard X n) : Set X) ⊆ H := by
    rw [powersetCard.coe_map, Equiv.coe_toEmbedding, ← g.symm_image_image H]
    exact image_mono hs
  intro s t hs ht
  rw [← hmap s, ← hmap t]
  exact hH _ _ (hsub s hs) (hsub t ht)

/-- **The partition relation does not depend on the linear order.** To verify `κ → (lam)ⁿ_μ` it
suffices to do so on a single linear order `J` of cardinality `κ`, for instance a well-order. -/
theorem partitionRel_iff_of_mk_eq (J : Type u) [LinearOrder J] (hJ : #J = κ) :
    PartitionRel κ lam n μ ↔
      ∀ (D : Type u), #D ≤ μ → ∀ c : (Fin n ↪o J) → D,
        ∃ H : Set J, lam ≤ #H ∧ IsHomogeneousOn c H := by
  refine ⟨fun h D hD c ↦ h J D hJ hD c, fun h ↦ partitionRel_iff_powersetCard.2 ?_⟩
  intro X D hX hD c
  obtain ⟨g⟩ := Cardinal.eq.1 (hJ.trans hX.symm)
  obtain ⟨H, hH, hc⟩ :=
    h D hD (c ∘ powersetCard.map n g.toEmbedding ∘ powersetCard.ofFinEmbEquiv)
  refine ⟨g '' H, by rwa [mk_image_eq g.injective], homogeneous_image_of_map_equiv g ?_⟩
  exact isHomogeneousOn_comp_ofFinEmbEquiv_iff.1 hc

/-- **The partition relation for `n = 1`.** `κ → (lam)¹_μ` holds exactly when every map from a
type of cardinality `κ` to a type of cardinality at most `μ` is constant on some set of
cardinality at least `lam`. -/
theorem partitionRel_one_iff :
    PartitionRel κ lam 1 μ ↔
      ∀ (X D : Type u), #X = κ → #D ≤ μ → ∀ f : X → D,
        ∃ H : Set X, lam ≤ #H ∧ ∀ x ∈ H, ∀ y ∈ H, f x = f y := by
  rw [partitionRel_iff_powersetCard]
  have hcoe {X : Type u} (x : X) : (powersetCard.ofSingleton x : Set X) = {x} :=
    ext fun _ ↦ Finset.mem_singleton
  refine ⟨fun h X D hX hD f ↦ ?_, fun h X D hX hD c ↦ ?_⟩
  · obtain ⟨H, hH, hc⟩ := h X D hX hD (f ∘ powersetCard.ofSingleton.symm)
    refine ⟨H, hH, fun x hx y hy ↦ ?_⟩
    simpa using hc (powersetCard.ofSingleton x) (powersetCard.ofSingleton y)
      (by simpa [hcoe] using hx) (by simpa [hcoe] using hy)
  · obtain ⟨H, hH, hc⟩ := h X D hX hD (c ∘ powersetCard.ofSingleton)
    refine ⟨H, hH, fun s t hs ht ↦ ?_⟩
    obtain ⟨x, rfl⟩ := powersetCard.ofSingleton.surjective s
    obtain ⟨y, rfl⟩ := powersetCard.ofSingleton.surjective t
    exact hc x (hs (by simp [hcoe])) y (ht (by simp [hcoe]))

end Cardinal
