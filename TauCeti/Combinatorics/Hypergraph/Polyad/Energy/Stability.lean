/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Hypergraph.Polyad.Coarsening
public import TauCeti.Combinatorics.Hypergraph.Polyad.Energy.Basic

/-!
# Stability of the polyad energy under moving few triples

The polyad energy of a coloring `H` does not decrease under refinement of the lower skeleton
(`Colored3Graph.polyadEnergy_mono_of_refines`). A regular lower skeleton, however, is usually
obtained by *recoloring* some pairs, which is not a refinement. This file shows that the energy
can then drop only by a multiple of the proportion of triples whose polyad changes.

Let `S` and `T` be lower skeletons and `M` a set of injective triples outside of which the polyad
over `S` is a function `f` of the polyad over `T`. Then
`H.polyadEnergy S ≤ H.polyadEnergy T + 2 |M| / |V|.descFactorial 3`
(`Colored3Graph.polyadEnergy_le_add_of_forall_notMem`). For each color `c`, the relative
densities over `T` minimize the squared distance to the indicator of `c` among all functions
constant on the polyads over `T`; the densities over `f` of those polyads form such a function
and agree with the densities over `S` outside `M`. Each triple of `M` costs at most `2`, since
the squared densities at a polyad sum to at most one.

When an injective map sends the polyad over `S` of every triple outside `M` to its polyad over
`T`, its left inverse is such a function (`Colored3Graph.polyadEnergy_le_add_of_injective`). In
particular, recoloring `|E|` ordered pairs of a skeleton without changing its vertex cells, along
an injective map of palettes, moves at most `3 |E| |V|` triples and lowers the energy by at most
`6 |E| |V| / |V|.descFactorial 3` (`Colored3Graph.polyadEnergy_le_add_of_vertexPart_eq`). This
is the energy bookkeeping of the regularity lemma for three-uniform hypergraphs, in which the
pair colors are regularized by editing few pairs between energy increments.

## Main results

* `TauCeti.Colored3Graph.polyadEnergy_le_add_of_forall_notMem`: the energy over `S` exceeds that
  over `T` by at most twice the proportion of triples where `S` is not determined by `T`.
* `TauCeti.Colored3Graph.polyadEnergy_le_add_of_injective`: the same bound for the triples moved
  by an injective map of polyads.
* `TauCeti.Colored3Graph.polyadEnergy_le_add_of_vertexPart_eq`: recoloring few pairs on the same
  vertex cells costs little energy.

## References

* V. Rödl and M. Schacht, *Regular partitions of hypergraphs: regularity lemmas*,
  Combin. Probab. Comput. 16 (2007), the index of a partition.
-/

public section

open Finset

namespace TauCeti.Colored3Graph

variable {κ κ₂ κ₂' V : Type*} [Fintype V] [DecidableEq V] [DecidableEq κ] [Fintype κ]
  (H : Colored3Graph κ V) {S : PairSkeleton3 κ₂ V} {T : PairSkeleton3 κ₂' V}

omit [Fintype κ] in
/-- For a single color `c`, the squared densities at the polyads over `S` sum to at most those
over `T` plus the squared distance, over the triples of `M`, from the indicator of `c` to the
densities at `f` of the polyads over `T`. -/
private theorem sum_sq_relativeDensity_le_add (M : Finset {x : Fin 3 → V // Function.Injective x})
    (f : Polyad3 T → Polyad3 S)
    (hf : ∀ x ∉ M, Polyad3.ofTriple S x = f (Polyad3.ofTriple T x)) (c : κ) :
    ∑ x, (H.relativeDensity c (Polyad3.ofTriple S x) : ℝ) ^ 2 ≤
      ∑ x, (H.relativeDensity c (Polyad3.ofTriple T x) : ℝ) ^ 2 +
        ∑ x ∈ M, ((if H.color (Set.powersetCard.ofFinEmb 3 V ⟨x.val, x.property⟩) = c then 1 else 0)
            -
          (H.relativeDensity c (f (Polyad3.ofTriple T x)) : ℝ)) ^ 2 := by
  set a : {x : Fin 3 → V // Function.Injective x} → ℝ :=
    fun x ↦ H.relativeDensity c (Polyad3.ofTriple S x)
  set b : {x : Fin 3 → V // Function.Injective x} → ℝ :=
    fun x ↦ H.relativeDensity c (Polyad3.ofTriple T x)
  set φ : {x : Fin 3 → V // Function.Injective x} → ℝ :=
    fun x ↦ H.relativeDensity c (f (Polyad3.ofTriple T x))
  set I : {x : Fin 3 → V // Function.Injective x} → ℝ :=
    fun x ↦ if H.color (Set.powersetCard.ofFinEmb 3 V ⟨x.val, x.property⟩) = c then 1 else 0
  -- Weighting by the indicator of `c` is weighting by the density, for functions constant on
  -- polyads.
  have hI (ψ : {x : Fin 3 → V // Function.Injective x} → ℝ) :
      ∑ x, I x * ψ x =
        ∑ x with H.color (Set.powersetCard.ofFinEmb 3 V ⟨x.val, x.property⟩) = c, ψ x := by
    simp only [I, ite_mul, one_mul, zero_mul, sum_ite, sum_const_zero, add_zero]
  have ha : ∑ x, a x * a x = ∑ x, I x * a x := by
    rw [hI, H.sum_relativeDensity_ofTriple_mul c _ fun x y hxy ↦ by simp only [a, hxy]]
  have hφ : ∑ x, b x * φ x = ∑ x, I x * φ x := by
    rw [hI, H.sum_relativeDensity_ofTriple_mul c _ fun x y hxy ↦ by simp only [φ, hxy]]
  -- Off `M` the two candidate densities agree.
  have hM : ∑ x, ((I x - φ x) ^ 2 - (I x - a x) ^ 2) ≤ ∑ x ∈ M, (I x - φ x) ^ 2 := by
    rw [← sum_subset (subset_univ M) fun x _ hx ↦ by simp [a, φ, hf x hx]]
    exact sum_le_sum fun x _ ↦ sub_le_self _ (sq_nonneg _)
  have hb : ∑ x, (2 * I x * φ x - φ x ^ 2) ≤ ∑ x, b x ^ 2 := by
    have : ∑ x, (2 * I x * φ x - φ x ^ 2) = ∑ x, (2 * b x * φ x - φ x ^ 2) := by
      simp only [sum_sub_distrib, mul_assoc, ← mul_sum, hφ]
    rw [this]
    exact sum_le_sum fun x _ ↦ by nlinarith [sq_nonneg (b x - φ x)]
  have hsplit : ∑ x, a x ^ 2 = ∑ x, ((I x - φ x) ^ 2 - (I x - a x) ^ 2) +
      ∑ x, (2 * I x * φ x - φ x ^ 2) := by
    rw [← sum_add_distrib]
    have : ∑ x, a x ^ 2 = ∑ x, (2 * I x * a x - a x ^ 2) := by
      simp only [sum_sub_distrib, mul_assoc, ← mul_sum, ← ha, sq]
      ring
    rw [this]
    exact sum_congr rfl fun x _ ↦ by ring
  linarith

/-- At each triple, the squared distance from the color indicators to the relative densities over
any polyad, summed over the colors, is at most `2`. -/
private theorem sum_sq_indicator_sub_relativeDensity_le_two
    (x : {x : Fin 3 → V // Function.Injective x}) (P : Polyad3 S) :
    ∑ c, ((if H.color (Set.powersetCard.ofFinEmb 3 V ⟨x.val, x.property⟩) = c then 1 else 0) -
      (H.relativeDensity c P : ℝ)) ^ 2 ≤ 2 := by
  set c₀ := H.color (Set.powersetCard.ofFinEmb 3 V ⟨x.val, x.property⟩)
  calc _ ≤ ∑ c, ((if c₀ = c then 1 else 0) + (H.relativeDensity c P : ℝ) ^ 2) := by
        refine sum_le_sum fun c _ ↦ ?_
        have h₀ : (0 : ℝ) ≤ H.relativeDensity c P := mod_cast H.relativeDensity_nonneg c P
        split_ifs <;> nlinarith
    _ ≤ 1 + 1 := by
        rw [sum_add_distrib, sum_ite_eq]
        simp only [mem_univ, ite_true]
        exact add_le_add_right (H.sum_sq_relativeDensity_le_one P) 1
    _ = 2 := by norm_num

/-- **Energy stability.** Let `M` be a set of injective triples outside of which the polyad over
`S` is determined by the polyad over `T` through a map `f`. Then the polyad energy over `S` exceeds
that over `T` by at most twice the proportion of the injective triples lying in `M`. -/
theorem polyadEnergy_le_add_of_forall_notMem (M : Finset {x : Fin 3 → V // Function.Injective x})
    (f : Polyad3 T → Polyad3 S)
    (hf : ∀ x ∉ M, Polyad3.ofTriple S x = f (Polyad3.ofTriple T x)) :
    H.polyadEnergy S ≤ H.polyadEnergy T + 2 * #M / (Fintype.card V).descFactorial 3 := by
  rw [polyadEnergy_def, polyadEnergy_def, ← add_div]
  refine div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg _)
  rw [sum_comm, sum_comm (s := univ) (t := univ)
    (f := fun x c ↦ (H.relativeDensity c (Polyad3.ofTriple T x) : ℝ) ^ 2)]
  calc _ ≤ ∑ c, (∑ x, (H.relativeDensity c (Polyad3.ofTriple T x) : ℝ) ^ 2 +
        ∑ x ∈ M, ((if H.color (Set.powersetCard.ofFinEmb 3 V ⟨x.val, x.property⟩) = c then 1 else 0)
            -
          (H.relativeDensity c (f (Polyad3.ofTriple T x)) : ℝ)) ^ 2) :=
        sum_le_sum fun c _ ↦ H.sum_sq_relativeDensity_le_add M f hf c
    _ ≤ _ := by
        rw [sum_add_distrib, sum_comm (s := univ) (t := M)]
        gcongr
        calc _ ≤ ∑ _x ∈ M, (2 : ℝ) := sum_le_sum fun x _ ↦
              H.sum_sq_indicator_sub_relativeDensity_le_two x _
          _ = 2 * #M := by rw [sum_const, nsmul_eq_mul, mul_comm]

/-- **Energy stability under an injective map of polyads.** If `g` maps polyads over `S`
injectively to polyads over `T`, the polyad energy over `S` exceeds that over `T` by at most twice
the proportion of the injective triples whose polyad over `T` is not the image under `g` of their
polyad over `S`. -/
theorem polyadEnergy_le_add_of_injective [DecidableEq κ₂'] (g : Polyad3 S → Polyad3 T)
    (hg : Function.Injective g) :
    H.polyadEnergy S ≤ H.polyadEnergy T +
      2 * #{x | Polyad3.ofTriple T x ≠ g (Polyad3.ofTriple S x)} /
        (Fintype.card V).descFactorial 3 := by
  obtain hS | hS := isEmpty_or_nonempty (Polyad3 S)
  · -- Without polyads there are no injective triples, and the energy over `S` vanishes.
    have : IsEmpty {x : Fin 3 → V // Function.Injective x} :=
      ⟨fun x ↦ hS.false (Polyad3.ofTriple S x)⟩
    rw [polyadEnergy_def, univ_eq_empty, sum_empty, zero_div]
    exact add_nonneg (H.polyadEnergy_nonneg T) (by positivity)
  refine H.polyadEnergy_le_add_of_forall_notMem _ (Function.invFun g) fun x hx ↦ ?_
  rw [mem_filter, not_and, not_not] at hx
  rw [hx (mem_univ x), Function.leftInverse_invFun hg]

/-- **Recoloring few pairs costs little energy.** Let `T` have the vertex cells of `S`, and let the
pair colors of `S` be those of `T` mapped by an injective map `g`, except on a set `E` of ordered
pairs. Then the polyad energy over `T` exceeds that over `S` by at most
`6 |E| |V| / |V|.descFactorial 3`. -/
theorem polyadEnergy_le_add_of_vertexPart_eq [DecidableEq κ₂] (hV : T.vertexPart = S.vertexPart)
    {g : κ₂' → κ₂} (hg : Function.Injective g) :
    H.polyadEnergy T ≤ H.polyadEnergy S +
      6 * #{p | S.pairColors.color p ≠ g (T.pairColors.color p)} * Fintype.card V /
        (Fintype.card V).descFactorial 3 := by
  refine (H.polyadEnergy_le_add_of_injective _ (Polyad3.coarsen_injective hV hg)).trans ?_
  refine add_le_add_right (div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg _)) _
  calc 2 * (#{x | Polyad3.ofTriple S x ≠ (Polyad3.ofTriple T x).coarsen hV.le g} : ℝ)
      ≤ 2 * ((3 * #{p | S.pairColors.color p ≠ g (T.pairColors.color p)} *
          Fintype.card V : ℕ) : ℝ) := by
        gcongr
        exact Polyad3.card_filter_ofTriple_ne_coarsen_ofTriple_le hV.le g
    _ = _ := by push_cast; ring

end TauCeti.Colored3Graph
