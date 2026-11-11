/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Chevalley.Root.Subgroup
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.LieAlgebra.Root.StructureConstant
import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.LieAlgebra.Root.Commutator.Basic

/-!
# The Chevalley commutator formula on the points of a Chevalley datum

For a Chevalley datum `D` and a commutative ring `A`, the root subgroups `x_α` of `D.points A`
satisfy Chevalley's commutator formula

```text
⁅x_α(u), x_β(v)⁆ = x_α(u) x_β(v) x_α(u)⁻¹ x_β(v)⁻¹ = ∏ x_{iα+jβ}(c_{ij} uⁱ vʲ),
```

the product over the roots `iα + jβ` with `i, j > 0` in increasing `i + j`. This file records it
on the points of `D`, with the coefficients given by the structure constants `N_{α,β}` of the
pinned Chevalley system, whenever at most two roots `iα + jβ` occur:

* if `α + β` is neither a root nor zero, `x_α(u)` and `x_β(v)` commute;
* if `α + β` is a root but `2α + β` and `α + 2β` are not,
  `⁅x_α(u), x_β(v)⁆ = x_{α+β}(N_{α,β} u v)`;
* if `α + β` and `2α + β` are roots but `3α + β` and `α + 2β` are not,
  `⁅x_α(u), x_β(v)⁆ = x_{α+β}(N_{α,β} u v) x_{2α+β}(M u² v)` with
  `M = N_{α,β} N_{α,α+β} / 2`, an exact division;
* if `α + β` and `α + 2β` are roots but `2α + β` and `α + 3β` are not,
  `⁅x_α(u), x_β(v)⁆ = x_{α+β}(N_{α,β} u v) x_{α+2β}(-M' u v²)` with
  `M' = N_{β,α} N_{β,α+β} / 2`, again an exact division.

These cover all pairs of roots `α ≠ -β` in the simply laced types and in the types `B`, `C`
and `F₄`; the remaining pairs of type `G₂` are treated in
`TauCeti.Algebra.AlgebraicGroup.Chevalley.Commutator.G2`. The formulas hold over every
commutative ring, including rings of characteristic two and three. They are the identities
`TauCeti.DynkinType.commute_chevalleyRootSubgroup`,
`TauCeti.DynkinType.commutatorElement_chevalleyRootSubgroup_of_root_eq_add` and
`TauCeti.DynkinType.commutatorElement_chevalleyRootSubgroup_of_root_eq_two_nsmul_add` on the
lattice of `D`, written in its weight basis; the last case is the third one for the pair
`β`, `α`, conjugated by `x_α(u)`.

## Main results

* `TauCeti.DynkinType.ChevalleyDatum.commute_rootSubgroup`: root subgroups of roots whose sum is
  neither a root nor zero commute.
* `TauCeti.DynkinType.ChevalleyDatum.commutatorElement_rootSubgroup_of_root_eq_add`: the
  one-factor commutator formula.
* `TauCeti.DynkinType.ChevalleyDatum.commutatorElement_rootSubgroup_of_root_eq_two_nsmul_add`:
  the two-factor commutator formula along the root string `β`, `α + β`, `2α + β`.
* `TauCeti.DynkinType.ChevalleyDatum.commutatorElement_rootSubgroup_of_root_eq_add_two_nsmul`:
  the two-factor commutator formula along the root string `α`, `α + β`, `α + 2β`.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, Chapter 3, Lemma 15.
* R. W. Carter, *Simple Groups of Lie Type*, Theorem 5.2.2.
-/

public section

open scoped commutatorElement

namespace TauCeti.DynkinType.ChevalleyDatum

universe v

variable {t : DynkinType} {ht : t.Valid} (D : ChevalleyDatum t ht) {α β γ δ : Fin t.numRoots}

/-- **Root subgroups commute when the roots do not sum to a root.** If `α + β` is neither a root
nor zero, then `x_α(u)` and `x_β(v)` commute in the points of `D` over every commutative ring. -/
theorem commute_rootSubgroup
    (h : (t.simplyConnectedRootDatum ht).root α + (t.simplyConnectedRootDatum ht).root β ∉
      Set.range (t.simplyConnectedRootDatum ht).root)
    (h₀ : (t.simplyConnectedRootDatum ht).root α + (t.simplyConnectedRootDatum ht).root β ≠ 0)
    (A : Type v) [CommRing A] (u v : A) :
    Commute (D.rootSubgroupPoints α A (Multiplicative.ofAdd u))
      (D.rootSubgroupPoints β A (Multiplicative.ofAdd v)) := by
  refine Commute.of_map (D.points A).subtype_injective ?_
  simp only [Subgroup.coe_subtype, coe_rootSubgroupPoints]
  exact (commute_chevalleyRootSubgroup D.representation D.lattice D.representation_mem_lattice
    D.isNilpotent_representation_rootGenerator h h₀ (CommAlgCat.of ℤ A) u v).map _

/-- **The one-factor Chevalley commutator formula.** If `γ = α + β` is a root while `2α + β` and
`α + 2β` are not, then `⁅x_α(u), x_β(v)⁆ = x_γ(N_{α,β} u v)` in the points of `D` over every
commutative ring. -/
theorem commutatorElement_rootSubgroup_of_root_eq_add
    (hγ : (t.simplyConnectedRootDatum ht).root γ =
      (t.simplyConnectedRootDatum ht).root α + (t.simplyConnectedRootDatum ht).root β)
    (hα : 2 • (t.simplyConnectedRootDatum ht).root α + (t.simplyConnectedRootDatum ht).root β ∉
      Set.range (t.simplyConnectedRootDatum ht).root)
    (hβ : (t.simplyConnectedRootDatum ht).root α + 2 • (t.simplyConnectedRootDatum ht).root β ∉
      Set.range (t.simplyConnectedRootDatum ht).root)
    (A : Type v) [CommRing A] (u v : A) :
    ⁅D.rootSubgroupPoints α A (Multiplicative.ofAdd u),
        D.rootSubgroupPoints β A (Multiplicative.ofAdd v)⁆ =
      D.rootSubgroupPoints γ A
        (Multiplicative.ofAdd ((t.structureConstant ht α β : A) * (u * v))) := by
  apply (D.points A).subtype_injective
  simp only [map_commutatorElement, Subgroup.coe_subtype, coe_rootSubgroupPoints]
  rw [← map_commutatorElement, commutatorElement_chevalleyRootSubgroup_of_root_eq_add
    D.representation D.lattice D.representation_mem_lattice
    D.isNilpotent_representation_rootGenerator hγ hα hβ (CommAlgCat.of ℤ A) u v]

/-- **The two-factor Chevalley commutator formula.** If `γ = α + β` and `δ = 2α + β` are roots
while `3α + β` and `α + 2β` are not, then in the points of `D` over every commutative ring

```text
⁅x_α(u), x_β(v)⁆ = x_γ(N_{α,β} u v) x_δ(M u² v),    M = N_{α,β} N_{α,γ} / 2,
```

where `M` is the integer with `(ad e_α)² e_β / 2 = M e_δ`; the division is exact. -/
theorem commutatorElement_rootSubgroup_of_root_eq_two_nsmul_add
    (hγ : (t.simplyConnectedRootDatum ht).root γ =
      (t.simplyConnectedRootDatum ht).root α + (t.simplyConnectedRootDatum ht).root β)
    (hδ : (t.simplyConnectedRootDatum ht).root δ =
      2 • (t.simplyConnectedRootDatum ht).root α + (t.simplyConnectedRootDatum ht).root β)
    (hα : 3 • (t.simplyConnectedRootDatum ht).root α + (t.simplyConnectedRootDatum ht).root β ∉
      Set.range (t.simplyConnectedRootDatum ht).root)
    (hβ : (t.simplyConnectedRootDatum ht).root α + 2 • (t.simplyConnectedRootDatum ht).root β ∉
      Set.range (t.simplyConnectedRootDatum ht).root)
    (A : Type v) [CommRing A] (u v : A) :
    ⁅D.rootSubgroupPoints α A (Multiplicative.ofAdd u),
        D.rootSubgroupPoints β A (Multiplicative.ofAdd v)⁆ =
      D.rootSubgroupPoints γ A (Multiplicative.ofAdd ((t.structureConstant ht α β : A) * (u * v))) *
        D.rootSubgroupPoints δ A
          (Multiplicative.ofAdd
            (((t.structureConstant ht α β * t.structureConstant ht α γ / 2 : ℤ) : A) *
              (u ^ 2 * v))) := by
  apply (D.points A).subtype_injective
  simp only [map_commutatorElement, map_mul, Subgroup.coe_subtype, coe_rootSubgroupPoints]
  rw [← map_commutatorElement, ← map_mul,
    commutatorElement_chevalleyRootSubgroup_of_root_eq_two_nsmul_add D.representation D.lattice
      D.representation_mem_lattice D.isNilpotent_representation_rootGenerator hγ hδ hα hβ
      (CommAlgCat.of ℤ A) u v]

/-- **The two-factor Chevalley commutator formula along the reversed string.** If `γ = α + β`
and `δ = α + 2β` are roots while `2α + β` and `α + 3β` are not, then in the points of `D` over
every commutative ring

```text
⁅x_α(u), x_β(v)⁆ = x_γ(N_{α,β} u v) x_δ(-M u v²),    M = N_{β,α} N_{β,γ} / 2,
```

where `M` is the integer with `(ad e_β)² e_α / 2 = M e_δ`; the division is exact. This is the
coefficient `c_{12} = -M_{β,α,2}`. -/
theorem commutatorElement_rootSubgroup_of_root_eq_add_two_nsmul
    (hγ : (t.simplyConnectedRootDatum ht).root γ =
      (t.simplyConnectedRootDatum ht).root α + (t.simplyConnectedRootDatum ht).root β)
    (hδ : (t.simplyConnectedRootDatum ht).root δ =
      (t.simplyConnectedRootDatum ht).root α + 2 • (t.simplyConnectedRootDatum ht).root β)
    (hα : 2 • (t.simplyConnectedRootDatum ht).root α + (t.simplyConnectedRootDatum ht).root β ∉
      Set.range (t.simplyConnectedRootDatum ht).root)
    (hβ : (t.simplyConnectedRootDatum ht).root α + 3 • (t.simplyConnectedRootDatum ht).root β ∉
      Set.range (t.simplyConnectedRootDatum ht).root)
    (A : Type v) [CommRing A] (u v : A) :
    ⁅D.rootSubgroupPoints α A (Multiplicative.ofAdd u),
        D.rootSubgroupPoints β A (Multiplicative.ofAdd v)⁆ =
      D.rootSubgroupPoints γ A (Multiplicative.ofAdd ((t.structureConstant ht α β : A) * (u * v))) *
        D.rootSubgroupPoints δ A
          (Multiplicative.ofAdd
            (-((t.structureConstant ht β α * t.structureConstant ht β γ / 2 : ℤ) : A) *
              (u * v ^ 2))) := by
  have := t.isReduced_simplyConnectedRootDatum ht
  let P := t.simplyConnectedRootDatum ht
  let x := fun (i : Fin t.numRoots) (w : A) => D.rootSubgroupPoints i A (Multiplicative.ofAdd w)
  -- The reversed string is the forward string of `β` along `α`, at the parameter `-u`.
  have h := D.commutatorElement_rootSubgroup_of_root_eq_two_nsmul_add (α := β) (β := α)
    (hγ.trans (add_comm _ _)) (hδ.trans (add_comm _ _)) (by rwa [add_comm])
    (by rwa [add_comm]) A v (-u)
  -- `x_α(u)` commutes with both factors, since `α + γ = 2α + β` and `α + δ = 2γ`.
  have hαγ : P.root α + P.root γ = 2 • P.root α + P.root β := by rw [hγ]; module
  have hαδ : P.root α + P.root δ = 2 • P.root γ := by rw [hδ, hγ]; module
  have hcomm (s s' : A) : Commute (x α u) (x γ s * x δ s') :=
    (D.commute_rootSubgroup (hαγ ▸ hα)
      (ne_zero_of_eq_nsmul_root_add_nsmul_root hγ (a := 2) (b := 1) two_ne_zero
        (by rw [hαγ, one_nsmul])) A u s).mul_right
    (D.commute_rootSubgroup (hαδ ▸ P.nsmul_notMem_range_root)
      (ne_zero_of_eq_nsmul_root_add_nsmul_root hγ (a := 2) (b := 2) two_ne_zero
        (by rw [hαδ, hγ]; module)) A u s')
  have hconj : ⁅x α u, x β v⁆ = x α u * ⁅x β v, x α (-u)⁆ * (x α u)⁻¹ := by
    simp only [x, commutatorElement_def, ofAdd_neg, map_inv, inv_inv]
    group
  have hN : (t.structureConstant ht β α : A) * (v * -u) =
      (t.structureConstant ht α β : A) * (u * v) := by
    rw [structureConstant_skew, Int.cast_neg]
    ring
  have hM (m : A) : m * (v ^ 2 * -u) = -m * (u * v ^ 2) := by ring
  rw [hconj, h, hN, hM, (hcomm _ _).eq, mul_inv_cancel_right]

end TauCeti.DynkinType.ChevalleyDatum
