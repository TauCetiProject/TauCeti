/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.GroupTheory.SpecificGroups.CFSG.Suzuki.Basic

/-!
# Matrix equations for the Suzuki fixed points

For a validated Suzuki index with field order `q = 2^(2m+1)`, the fixed points of the
Steinberg map `τ^(2m+1)` are exactly the symplectic matrices satisfying

```text
τ(g) = g^[2^(m+1)],
```

where the right side raises each matrix entry to the indicated power. On the left, `τ(g)`
is the matrix of two-by-two minors on the four coordinate pairs
`(0,1), (0,3), (2,3), (1,2)`. Thus the criterion gives explicit polynomial equations,
without expanding the odd iterate of the special isogeny. Every solution has entries in
the recorded copy of `𝔽_q` inside the algebraic closure.

`mem_map_fixedSubgroup_steinberg_iff` reads this criterion in the general linear group,
including the symplectic equation. It supplies a matrix description with which a
generator-based construction can be compared. No generation theorem, derived-subgroup
calculation, or identification with another construction of the Suzuki group is asserted.

The explicit carrier is not identified with the pinned simply connected group scheme of
its diagram. Constructions on it transfer to that pinned group only along such an
identification, once one is proved.

The calculation uses the special-isogeny square relation already proved in
`TauCeti.Algebra.Lie.Symplectic.StandardCarrier.SpecialIsogeny` and the odd-power
construction in `TauCeti.GroupTheory.SpecificGroups.CFSG.Suzuki.Basic`.
-/

public section

open Matrix

namespace TauCeti.SuzukiLieIndex

variable (d : SuzukiLieIndex)

/-- A carrier point is fixed by the Suzuki Steinberg map exactly when the matrix of
its special isogeny equals its entrywise `2^(m+1)`-st power. -/
-- Not `@[simp]`: the generic equalizer membership lemma already simplifies this left side.
theorem mem_fixedSubgroup_steinberg_iff (g : d.toRankTwoBLieIndex.AmbientGroup) :
    g ∈ fixedSubgroup d.steinberg ↔
      ∀ i j : Fin 4,
        Matrix.symplecticSpecialIsogeny
          ((g : GL (Fin 4) d.1.Closure) : Matrix (Fin 4) (Fin 4) d.1.Closure) i j =
          ((g : GL (Fin 4) d.1.Closure) : Matrix (Fin 4) (Fin 4) d.1.Closure) i j ^
            (2 ^ (SuzukiReeIndex.halfExponent d.toSuzukiReeIndex + 1)) := by
  have hinj : Function.Injective d.halfFrobenius := by
    intro x y h
    have hsq := congrArg d.halfFrobenius h
    rw [halfFrobenius_halfFrobenius, halfFrobenius_halfFrobenius,
      RankTwoBLieIndex.primeFrobenius_def, SpStd.frobenius_eq_pointsMap] at hsq
    exact SpStd.pointsMap_injective 1 (RingHom.injective _) hsq
  rw [mem_fixedSubgroup, ← hinj.eq_iff, halfFrobenius_steinberg]
  constructor
  · intro h i j
    have hij := congrArg
      (fun x : d.toRankTwoBLieIndex.AmbientGroup =>
        ((x : GL (Fin 4) d.1.Closure) : Matrix (Fin 4) (Fin 4) d.1.Closure) i j) h
    simpa only [halfFrobenius_def, SpStd.coe_specialIsogeny,
      SpStd.coe_frobenius_apply, d.characteristic_eq_two] using hij.symm
  · intro h
    apply Subtype.ext
    apply Units.ext
    ext i j
    simpa only [halfFrobenius_def, SpStd.coe_specialIsogeny,
      SpStd.coe_frobenius_apply, d.characteristic_eq_two] using (h i j).symm

/-- The image of the Suzuki fixed subgroup in `GL₄` is cut out by the symplectic
equation and the special-isogeny minor equations. The alternating form uses the coordinate
pairs `(0,2)` and `(1,3)`, as in `JFin 2`. -/
theorem mem_map_fixedSubgroup_steinberg_iff
    (g : GL (Fin 4) d.1.Closure) :
    g ∈ (fixedSubgroup d.steinberg).map
        (SpStd.points 1 d.1.Closure).subtype ↔
      (g : Matrix (Fin 4) (Fin 4) d.1.Closure) * JFin 2 d.1.Closure *
          (g : Matrix (Fin 4) (Fin 4) d.1.Closure)ᵀ = JFin 2 d.1.Closure ∧
        ∀ i j : Fin 4,
          Matrix.symplecticSpecialIsogeny (g : Matrix (Fin 4) (Fin 4) d.1.Closure) i j =
            (g : Matrix (Fin 4) (Fin 4) d.1.Closure) i j ^
              (2 ^ (SuzukiReeIndex.halfExponent d.toSuzukiReeIndex + 1)) := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨?_, (d.mem_fixedSubgroup_steinberg_iff x).mp hx⟩
    exact GLSymplecticFin.mem_iff.mp
      ((SpStd.points_eq_GLSymplecticFin (K := d.1.Closure) 1) ▸ x.property)
  · rintro ⟨hg, h⟩
    have hmem : g ∈ SpStd.points 1 d.1.Closure := by
      rw [SpStd.points_eq_GLSymplecticFin]
      exact GLSymplecticFin.mem_iff.mpr hg
    exact ⟨⟨g, hmem⟩, (d.mem_fixedSubgroup_steinberg_iff ⟨g, hmem⟩).mpr h, rfl⟩

/-- Every matrix entry of a Suzuki Steinberg fixed point belongs to the recorded field
of order `2^(2m+1)`. -/
theorem coe_mem_fixedField_of_mem_fixedSubgroup_steinberg
    (g : d.toRankTwoBLieIndex.AmbientGroup) (hg : g ∈ fixedSubgroup d.steinberg)
    (i j : Fin 4) :
    ((g : GL (Fin 4) d.1.Closure) : Matrix (Fin 4) (Fin 4) d.1.Closure) i j ∈ d.1.fixedField := by
  apply (d.toRankTwoBLieIndex.mem_fixedSubgroup_frobenius_iff g).mp _ i j
  simpa only [mem_fixedSubgroup, mem_fixedSubgroup.mp hg] using
    (d.steinberg_steinberg g).symm

end TauCeti.SuzukiLieIndex
