/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.IntegralLattice.Rank24.TableRow.A5FourthD4.CyclicSymmetry

/-!
# Faithful action of the glue-pattern symmetries across all 23 rootful Niemeier rows

Every row `r` of the rootful rank-24 table is presented by glue patterns (`r.gluePatterns`), each
carrying an indicated symmetry group `p.symmetries`.  On the 22 rows other than `A₅⁴ D₄`, those
coordinate permutations preserve `r.glueSubgroup` directly and act on `r.lattice` via
`TauCeti.RootfulNiemeierType.patternIsometryHom`.  On `A₅⁴ D₄`, the cyclic pattern `[2(024)0]` acts
on `TauCeti.niemeierA5FourthD4` by coupling its marked-block rotation with `D₄` triality
(`TauCeti.RootfulNiemeierType.a5FourthD4CyclicSymmetryHom`).

This module combines both cases into a uniform action
`TauCeti.RootfulNiemeierType.coupledPatternIsometryHom` defined for every pattern of every rootful
Niemeier row without exception, and proves that every pattern symmetry group acts faithfully on its
row's lattice (`coupledPatternIsometryHom_injective`).

## Main declarations

* `TauCeti.RootfulNiemeierType.forall_mem_glueSymmetries_of_mem_symmetries_iff`:
  `r ≠ a5FourthD4` is the exact domain on which pattern symmetries are pure-position glue
  symmetries.
* `TauCeti.RootfulNiemeierType.coupledPatternIsometryHom`: action of `p.symmetries` on `r.lattice`
  for every `p ∈ r.gluePatterns` across all 23 rootful Niemeier rows.
* `TauCeti.RootfulNiemeierType.coupledPatternIsometryHom_eq_patternIsometryHom`,
  `TauCeti.RootfulNiemeierType.coupledPatternIsometryHom_a5FourthD4_cyclic`,
  `TauCeti.RootfulNiemeierType.coupledPatternIsometryHom_literal`: agreement with
  `patternIsometryHom` away from `A₅⁴ D₄`, with `a5FourthD4CyclicSymmetryHom` on `[2(024)0]`, and
  triviality on literal patterns.
* `TauCeti.RootfulNiemeierType.coupledPatternIsometryHom_injective`: every pattern symmetry group
  embeds faithfully into `Isometry r.lattice r.lattice`.

## References

* J. H. Conway and N. J. A. Sloane, *Sphere Packings, Lattices and Groups*, 3rd ed., Chapter 4
  §§3 and 7, and Chapter 16 §1, Table 16.1.
-/

public section

namespace TauCeti

namespace RootfulNiemeierType

open IntegralLattice

/-- **Exactness of `mem_glueSymmetries_of_mem_symmetries`**: every indicated pattern symmetry of a
row `r` is a pure-position glue symmetry of `r` if and only if `r ≠ a5FourthD4`. -/
theorem forall_mem_glueSymmetries_of_mem_symmetries_iff {r : RootfulNiemeierType} :
    (∀ {p : GluePattern} (hp : p ∈ r.gluePatterns) {g : Equiv.Perm (Fin p.length)},
      g ∈ p.symmetries →
        (finCongr (length_eq_of_mem_gluePatterns hp)).permCongr g ∈ r.glueSymmetries) ↔
      r ≠ a5FourthD4 := by
  refine ⟨fun h hr ↦ ?_, fun hr {p} hp {g} hg ↦ mem_glueSymmetries_of_mem_symmetries hr hp hg⟩
  subst hr
  have hp : GluePattern.cyclic [2] [0, 2, 4] [0] ∈ a5FourthD4.gluePatterns := by simp [gluePatterns]
  have hmem := h hp a5FourthD4BlockRot_mem_symmetries
  have heq : (finCongr (length_eq_of_mem_gluePatterns hp)).permCongr a5FourthD4BlockRot =
      (a5FourthD4BlockRot : Equiv.Perm (Fin a5FourthD4.components.length)) := by
    ext ⟨i, hi⟩
    rfl
  exact a5FourthD4BlockRot_notMem_glueSymmetries (heq ▸ hmem)

/-- **Every table pattern of every rootful Niemeier row acts on the lattice of its row**: by pure
component permutation (`patternIsometryHom`) on the 22 rows other than `A₅⁴ D₄`, and by the
coupled triality action (`a5FourthD4CyclicSymmetryHom`) on `A₅⁴ D₄`. -/
noncomputable def coupledPatternIsometryHom {r : RootfulNiemeierType} {p : GluePattern}
    (hp : p ∈ r.gluePatterns) :
    p.symmetries →* Isometry r.lattice r.lattice :=
  if hr : r = a5FourthD4 then
    match p, hp with
    | .literal _, _ => 1
    | .evenPermutations _, hp => by simp [hr, gluePatterns] at hp
    | .cyclic pre block post, hp => by
      have hp' : pre = [2] ∧ block = [0, 2, 4] ∧ post = [0] := by
        simpa [hr, gluePatterns] using hp
      rcases hp' with ⟨rfl, rfl, rfl⟩
      subst hr
      exact a5FourthD4CyclicSymmetryHom
  else
    patternIsometryHom hr hp

/-- On every row other than `A₅⁴ D₄`, `coupledPatternIsometryHom` agrees with
`patternIsometryHom`. -/
@[simp]
theorem coupledPatternIsometryHom_eq_patternIsometryHom {r : RootfulNiemeierType}
    (hr : r ≠ a5FourthD4) {p : GluePattern} (hp : p ∈ r.gluePatterns) :
    coupledPatternIsometryHom hp = patternIsometryHom hr hp := by
  simp [coupledPatternIsometryHom, hr]

/-- On the cyclic pattern `[2(024)0]` of `A₅⁴ D₄`, `coupledPatternIsometryHom` is
`a5FourthD4CyclicSymmetryHom`. -/
@[simp]
theorem coupledPatternIsometryHom_a5FourthD4_cyclic
    (hp : GluePattern.cyclic [2] [0, 2, 4] [0] ∈ a5FourthD4.gluePatterns) :
    coupledPatternIsometryHom hp = a5FourthD4CyclicSymmetryHom := by
  simp [coupledPatternIsometryHom]

/-- On any literal pattern of any row, `coupledPatternIsometryHom` is trivial. -/
@[simp]
theorem coupledPatternIsometryHom_literal {r : RootfulNiemeierType} (word : List ℕ)
    (hp : GluePattern.literal word ∈ r.gluePatterns) :
    coupledPatternIsometryHom hp = 1 := by
  ext g
  rw [Subsingleton.elim g 1, map_one, MonoidHom.one_apply]

/-- **Every pattern symmetry group across all 23 rootful Niemeier rows embeds faithfully into the
isometry group of its row's lattice.** -/
theorem coupledPatternIsometryHom_injective {r : RootfulNiemeierType} {p : GluePattern}
    (hp : p ∈ r.gluePatterns) :
    Function.Injective (coupledPatternIsometryHom hp) := by
  by_cases hr : r = a5FourthD4
  · subst hr
    rcases p with word | ⟨pre, block, post⟩ | @⟨n, word⟩
    · exact fun a b _ ↦ Subsingleton.elim a b
    · have hp' : pre = [2] ∧ block = [0, 2, 4] ∧ post = [0] := by
        simpa [gluePatterns] using hp
      rcases hp' with ⟨rfl, rfl, rfl⟩
      rw [coupledPatternIsometryHom_a5FourthD4_cyclic]
      exact a5FourthD4CyclicSymmetryHom_injective
    · simp [gluePatterns] at hp
  · rw [coupledPatternIsometryHom_eq_patternIsometryHom hr]
    exact patternIsometryHom_injective hr hp

end RootfulNiemeierType

end TauCeti
