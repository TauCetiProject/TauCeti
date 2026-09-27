/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Curves.StableReduction.NumericalType.GenusComparison
public import TauCeti.AlgebraicGeometry.Curves.StableReduction.NumericalType.MultiplicityBound
public import TauCeti.AlgebraicGeometry.Curves.StableReduction.Picard.Contraction
public import TauCeti.AlgebraicGeometry.Curves.StableReduction.Picard.Torsion.Bound

/-!
# Bounding prime torsion by the genus

Let `T` be a numerical type of genus `g ≥ 2` and `ℓ` a prime with `ℓ > 768g`. Then

`dim_{𝔽_ℓ} Pic(T)[ℓ] ≤ g`,

and if `T` is minimal, even `dim_{𝔽_ℓ} Pic(T)[ℓ] ≤ g_top ≤ g`, where `g_top` is the first Betti
number of the intersection graph
([Stacks, Proposition 55.7.4](https://stacks.math.columbia.edu/tag/0C9X)). In the proof of
semistable reduction this is the numerical input which, confronted with the `2g`-dimensional
`ℓ`-torsion of the Jacobian, forces the special fibre of a minimal regular model to be reduced
with nodal singularities.

The statements below only require `ℓ > 768g - 768`, which the bound on minimal types permits;
this contains the hypothesis `ℓ > 768g` of the Stacks Project.

## Main results

* `TauCeti.NumericalType.IsMinimal.finrank_torsion_le_topologicalGenus_of_lt`:
  `dim_{𝔽_ℓ} Pic(T)[ℓ] ≤ g_top` for a minimal type.
* `TauCeti.NumericalType.finrank_torsion_le_arithmeticGenus`: `dim_{𝔽_ℓ} Pic(T)[ℓ] ≤ g`.
-/

public section

namespace TauCeti

namespace NumericalType

universe u

variable {T : NumericalType.{u}}

namespace IsMinimal

/- For a minimal type, the bound `mᵢ|aᵢⱼ| ≤ 768g - 768` excludes prime divisors
`ℓ > 768g - 768` of the multiplicities and positive intersection numbers. This permits the
topological torsion bound; `g_top ≤ g` then gives the genus bound. For a nonminimal type,
contract a `(-1)`-index and induct on the number of components. -/
/-- **Prime torsion of a minimal numerical type.** In a minimal numerical type of genus `g ≥ 2`,
every prime `ℓ > 768g - 768` satisfies `dim_{𝔽_ℓ} Pic(T)[ℓ] ≤ g_top`, the first Betti number of
the intersection graph ([Stacks, Proposition 55.7.4](https://stacks.math.columbia.edu/tag/0C9X)).
-/
theorem finrank_torsion_le_topologicalGenus_of_lt (hT : T.IsMinimal)
    (hg : 2 ≤ T.arithmeticGenus) (ℓ : ℕ) [Fact ℓ.Prime]
    (hℓ : 768 * T.arithmeticGenus - 768 < ℓ) :
    (Module.finrank (ZMod ℓ) (T.torsion ℓ) : ℤ) ≤ T.topologicalGenus := by
  by_cases h : 1 < Fintype.card T.Component
  swap
  · rw [T.finrank_torsion_eq_zero_of_card_eq_one (le_antisymm (not_lt.mp h) Fintype.card_pos)]
    exact T.topologicalGenus_nonneg
  -- every multiplicity and every intersection number of meeting components is below `ℓ`
  refine T.finrank_torsion_le_topologicalGenus ℓ (fun i hdvd ↦ ?_) fun i j hij hdvd ↦ ?_
  · obtain ⟨j, hj⟩ := T.exists_adj h i
    have hpos := (T.adj_iff.mp hj).2
    have hbound := hT.multiplicity_mul_abs_intersection_le hg i j
    rw [abs_of_pos hpos] at hbound
    have hle : (T.multiplicity i : ℤ) ≤ T.multiplicity i * T.intersection i j :=
      le_mul_of_one_le_right (by positivity) hpos
    have := Nat.le_of_dvd (T.multiplicity i).pos hdvd
    omega
  · have hpos := (T.adj_iff.mp hij).2
    have hbound := hT.multiplicity_mul_abs_intersection_le hg i j
    rw [abs_of_pos hpos] at hbound
    have hle : T.intersection i j ≤ T.multiplicity i * T.intersection i j :=
      le_mul_of_one_le_left hpos.le (by exact_mod_cast (T.multiplicity i).pos)
    have := Int.le_of_dvd hpos hdvd
    omega

end IsMinimal

/-- A numerical type with `n` components and arithmetic genus `g ≥ 2` has prime
`ℓ`-torsion rank at most `g` whenever `ℓ > 768g - 768`. -/
private lemma finrank_torsion_le_arithmeticGenus_of_card_eq (ℓ : ℕ) [Fact ℓ.Prime] {n : ℕ} :
    ∀ T : NumericalType.{u}, Fintype.card T.Component = n → 2 ≤ T.arithmeticGenus →
      768 * T.arithmeticGenus - 768 < ℓ →
      (Module.finrank (ZMod ℓ) (T.torsion ℓ) : ℤ) ≤ T.arithmeticGenus := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro T hn hg hℓ
  by_cases hT : T.IsMinimal
  · by_cases h : 1 < Fintype.card T.Component
    · exact (hT.finrank_torsion_le_topologicalGenus_of_lt hg ℓ hℓ).trans
        (hT.topologicalGenus_le_arithmeticGenus h)
    · rw [T.finrank_torsion_eq_zero_of_card_eq_one (le_antisymm (not_lt.mp h) Fintype.card_pos)]
      omega
  -- contract a `(-1)`-index: the genus is unchanged and the torsion does not shrink
  obtain ⟨e, he⟩ : ∃ e, T.IsMinusOneIndex e := by
    simpa [isMinimal_iff] using hT
  have hcard : Fintype.card (T.contract he).Component < n := by
    rw [← hn]
    exact Fintype.card_subtype_lt (p := (· ≠ e)) (x := e) (by simp)
  have hgenus := arithmeticGenus_contract he
  have := ih _ hcard (T.contract he) rfl (hgenus ▸ hg) (hgenus ▸ hℓ)
  have hle : (Module.finrank (ZMod ℓ) (T.torsion ℓ) : ℤ) ≤
      Module.finrank (ZMod ℓ) ((T.contract he).torsion ℓ) :=
    Int.ofNat_le.mpr (T.finrank_torsion_le_contract he ℓ)
  omega

/-- **Prime torsion of a numerical type.** In a numerical type of genus `g ≥ 2`, every prime
`ℓ > 768g - 768` satisfies `dim_{𝔽_ℓ} Pic(T)[ℓ] ≤ g`. In particular this holds for every prime
`ℓ > 768g`, which is [Stacks, Proposition 55.7.4](https://stacks.math.columbia.edu/tag/0C9X). -/
theorem finrank_torsion_le_arithmeticGenus (hg : 2 ≤ T.arithmeticGenus) (ℓ : ℕ) [Fact ℓ.Prime]
    (hℓ : 768 * T.arithmeticGenus - 768 < ℓ) :
    (Module.finrank (ZMod ℓ) (T.torsion ℓ) : ℤ) ≤ T.arithmeticGenus :=
  finrank_torsion_le_arithmeticGenus_of_card_eq ℓ T rfl hg hℓ

end NumericalType

end TauCeti
