/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.NoncrossingPartition.Comap
public import TauCeti.Probability.FreeProbability.Cumulant.Basic

/-!
# Free cumulants with products as arguments

Let `φ : A → R` be a function on a monoid, `a : α → A` a word indexed by a finite set `s` of
positions in a linear order, and `f : α → β` a map to a linear order that is monotone on `s`. The
fibres of `f` cut `s` into consecutive intervals; multiplying the letters of `a` along each fibre,
in increasing order, gives the grouped word `fiberProd a s f`, indexed by the image `f '' s`. Let
`σ_f ∈ NC(s)` be the partition of `s` into the fibres of `f`.

The free cumulants of the grouped word are sums of free cumulants of the original word: for every
noncrossing partition `ρ` of `f '' s`,
`κ_ρ(fiberProd a s f) = ∑_{π ∈ NC(s), π ⊔ σ_f = ρ̂} κ_π(a)`, where `ρ̂` is the pullback of `ρ`
along `f` and the join is taken in `NC(s)`. For `ρ` the partition into one part this is the
formula `κ_m(A₁, …, A_m) = ∑_{π ∈ NC(n), π ⊔ σ = 1_n} κ_π(a₁, …, aₙ)` for cumulants whose
arguments `A_j` are products of consecutive letters, the key step towards the characterisation of
freeness by the vanishing of mixed cumulants.

The proof identifies the block moments of `ρ̂` with those of `ρ`, so that both sides satisfy the
moment–cumulant formula on `NC(f '' s)`, and then uses that pulling back is an order isomorphism
of `NC(f '' s)` onto the upper interval `[σ_f, 1_s]` of `NC(s)`.

## Main definitions

* `TauCeti.fiberProd a s f` — the word indexed by `f '' s` whose letter at `y` is the product, in
  increasing order, of the letters of `a` at the positions of `s` over `y`.

## Main results

* `TauCeti.partitionMoment_comap` — the block moment of the pullback of a partition `P` of
  `f '' s` is the block moment of `P` for the grouped word.
* `TauCeti.partitionCumulant_fiberProd` — `κ_ρ(fiberProd a s f) = ∑_{π ⊔ σ_f = ρ̂} κ_π(a)`.
* `TauCeti.freeCumulant_fiberProd` and `TauCeti.freeCumulant_fiberProd_eq_sum_prod` — the free
  cumulant of the grouped word is `∑_{π ⊔ σ_f = 1_s} κ_π(a)`, and in multiplicative form
  `∑_{π ⊔ σ_f = 1_s} ∏_{B ∈ π} κ_B(a)`.

## References

* A. Nica, R. Speicher, *Lectures on the Combinatorics of Free Probability*, Theorem 11.12.
* M. Krawczyk, R. Speicher, *Combinatorics of free cumulants*, J. Combin. Theory Ser. A 90
  (2000), 267–292.
-/

public section

open Finset

namespace TauCeti

variable {R A α β : Type*} [LinearOrder α] [LinearOrder β] {s : Finset α} {f : α → β}

section Moment

variable [Monoid A]

/-- The word obtained from `a` by grouping along the fibres of `f`: its letter at `y` is the
product `a_{x₁} * ⋯ * a_{xₖ}` over the positions `x₁ < ⋯ < xₖ` of `s` with `f xᵢ = y`. When `f` is
monotone on `s` these positions are consecutive in `s`. -/
def fiberProd (a : α → A) (s : Finset α) (f : α → β) (y : β) : A :=
  ({x ∈ s | f x = y}.sort.map a).prod

/-- Unfolding of the word grouped along the fibres of `f`. -/
theorem fiberProd_def (a : α → A) (s : Finset α) (f : α → β) (y : β) :
    fiberProd a s f y = ({x ∈ s | f x = y}.sort.map a).prod := by
  rw [fiberProd]

/-- For `f` monotone on `s`, the product of a word along the positions of `s` over a set `C` is
the product of the word grouped along the fibres of `f` over the values of `f` at those
positions. -/
private theorem prod_map_sort_filter_eq (hf : MonotoneOn f s) (a : α → A) (C : Finset β) :
    ({x ∈ s | f x ∈ C}.sort.map a).prod =
      (({x ∈ s | f x ∈ C}.image f).sort.map (fiberProd a s f)).prod := by
  rw [← flatten_map_sort_filter_eq_sort (hf.mono (coe_subset.2 (filter_subset _ s))),
    List.map_flatten, List.prod_flatten, List.map_map, List.map_map]
  refine congrArg List.prod (List.map_congr_left fun y hy => ?_)
  obtain ⟨x, hx, rfl⟩ := mem_image.1 ((mem_sort _).1 hy)
  rw [Function.comp_apply, fiberProd_def, filter_filter,
    filter_congr (s := s) (q := fun z => f z = f x) fun z _ =>
      ⟨And.right, fun h => ⟨h ▸ (mem_filter.1 hx).2, h⟩⟩, Function.comp_apply]

variable [CommMonoid R]

/-- The block moment of the pullback along `f` of a partition `P` of `f '' s` is the block
moment of `P` for the word grouped along the fibres of `f`. -/
theorem partitionMoment_comap (φ : A → R) (a : α → A) (hf : MonotoneOn f s)
    (P : Finpartition (s.image f)) :
    partitionMoment φ a (P.comap f) = partitionMoment φ (fiberProd a s f) P := by
  rw [partitionMoment_def, partitionMoment_def, Finpartition.prod_parts_comap]
  refine prod_congr rfl fun C hC => ?_
  rw [prod_map_sort_filter_eq hf]
  congr 4
  ext y
  simp only [mem_image, mem_filter]
  refine ⟨fun ⟨x, ⟨_, hx⟩, hxy⟩ => hxy ▸ hx, fun hy => ?_⟩
  obtain ⟨x, hx, rfl⟩ := mem_image.1 (P.le hC hy)
  exact ⟨x, ⟨hx, hy⟩, rfl⟩

end Moment

section Cumulant

variable [CommRing R] [Monoid A] (φ : A → R) (a : α → A)

/-- *Free cumulants with products as arguments*: the free cumulant of a noncrossing partition `ρ`
of `f '' s` for the word grouped along the fibres of `f` is the sum of the free cumulants of the
noncrossing partitions `π` of `s` whose join with the partition `σ_f` of `s` into the fibres of `f`
is the pullback of `ρ`. -/
theorem partitionCumulant_fiberProd (hf : MonotoneOn f s)
    (ρ : NoncrossingPartition (s.image f)) :
    partitionCumulant φ (fiberProd a s f) ρ =
      ∑ π : NoncrossingPartition s with π ⊔ NoncrossingPartition.comap hf ⊥ =
        NoncrossingPartition.comap hf ρ, partitionCumulant φ a π := by
  set e := NoncrossingPartition.comap hf
  -- Both sides satisfy the moment–cumulant formula on `NC(f '' s)`.
  refine (congrFun (eq_partitionCumulant_of_forall_sum_Iic φ (fiberProd a s f)
    (fun ρ => ∑ π : NoncrossingPartition s with π ⊔ e ⊥ = e ρ, partitionCumulant φ a π)
    fun ρ => ?_) ρ).symm
  -- A partition `π` of `s` contributes to the term of `ρ' ≤ ρ` with `π ⊔ σ_f = ρ̂'` exactly when
  -- `π ≤ ρ̂`, and then `ρ'` is unique.
  rw [sum_comm' (t' := Iic (e ρ))
      (s' := fun π => {ρ' ∈ Iic ρ | π ⊔ e ⊥ = e ρ'}) fun ρ' π => by
    simp only [mem_filter, mem_univ, true_and, mem_Iic]
    exact ⟨fun ⟨h, hπ⟩ => ⟨⟨h, hπ⟩, le_sup_left.trans (hπ.trans_le (e.monotone h))⟩,
      fun ⟨h, _⟩ => h⟩]
  rw [← partitionMoment_comap φ a hf, ← NoncrossingPartition.coe_comap hf,
    ← sum_Iic_partitionCumulant]
  refine sum_congr rfl fun π hπ => ?_
  obtain ⟨ρ₀, hρ₀⟩ :=
    (NoncrossingPartition.exists_comap_eq_iff (hf := hf)).2 (le_sup_right (a := π))
  have hρ₀ρ : ρ₀ ≤ ρ :=
    e.le_iff_le.1 (hρ₀.trans_le (sup_le (mem_Iic.1 hπ) (e.monotone bot_le)))
  rw [show {ρ' ∈ Iic ρ | π ⊔ e ⊥ = e ρ'} = {ρ₀} by
      ext ρ'
      rw [mem_filter, mem_Iic, mem_singleton, ← hρ₀, e.injective.eq_iff]
      exact ⟨fun ⟨_, h⟩ => h.symm, fun h => ⟨h ▸ hρ₀ρ, h.symm⟩⟩,
    sum_singleton]

/-- *Free cumulants with products as arguments*: the free cumulant of the word grouped along the
fibres of `f` is the sum of the free cumulants of the noncrossing partitions `π` of `s` whose join
with the partition `σ_f` of `s` into the fibres of `f` is the partition into one part,
`κ(fiberProd a s f) = ∑_{π ⊔ σ_f = 1_s} κ_π(a)`. -/
theorem freeCumulant_fiberProd (hf : MonotoneOn f s) :
    freeCumulant φ (fiberProd a s f) (s.image f) =
      ∑ π : NoncrossingPartition s with π ⊔ NoncrossingPartition.comap hf ⊥ = ⊤,
        partitionCumulant φ a π := by
  rw [freeCumulant_def, partitionCumulant_fiberProd φ a hf, NoncrossingPartition.comap_top]

/-- *Free cumulants with products as arguments*, in multiplicative form:
`κ(fiberProd a s f) = ∑_{π ⊔ σ_f = 1_s} ∏_{B ∈ π} κ_B(a)`, where `σ_f` is the partition of `s`
into the fibres of `f`. -/
theorem freeCumulant_fiberProd_eq_sum_prod (hf : MonotoneOn f s) :
    freeCumulant φ (fiberProd a s f) (s.image f) =
      ∑ π : NoncrossingPartition s with π ⊔ NoncrossingPartition.comap hf ⊥ = ⊤,
        ∏ B ∈ π.1.parts, freeCumulant φ a B := by
  simp_rw [freeCumulant_fiberProd φ a hf, partitionCumulant_eq_prod_freeCumulant]

end Cumulant

end TauCeti
