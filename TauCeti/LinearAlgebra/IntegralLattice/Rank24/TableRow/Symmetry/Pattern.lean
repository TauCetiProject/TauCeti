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

* `TauCeti.RootfulNiemeierType.forall_permCongr_mem_glueSymmetries_iff`: the indicated pattern
  symmetries of a row are pure position glue symmetries if and only if the row is not `A₅⁴ D₄`.
* `TauCeti.RootfulNiemeierType.coupledPatternIsometryHom`: action of `p.symmetries` on `r.lattice`
  for every `p ∈ r.gluePatterns` across all 23 rootful Niemeier rows.
* `TauCeti.RootfulNiemeierType.coupledPatternIsometryHom_eq_patternIsometryHom`,
  `TauCeti.RootfulNiemeierType.coupledPatternIsometryHom_a5FourthD4_cyclic`,
  `TauCeti.RootfulNiemeierType.coupledPatternIsometryHom_literal`: agreement with
  `patternIsometryHom` away from `A₅⁴ D₄`, with `a5FourthD4CyclicSymmetryHom` on `[2(024)0]`, and
  triviality on literal patterns.
* `TauCeti.RootfulNiemeierType.exists_coupledPatternIsometryHom_a5FourthD4_eq_pow`,
  `TauCeti.RootfulNiemeierType.det_coupledPatternIsometryHom_a5FourthD4`: every pattern symmetry
  of `A₅⁴ D₄` acts as a power of `a5FourthD4TrialityRotation` and has determinant `1`.
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

/-- Classification of glue patterns of `A₅⁴ D₄`: each is either a literal word or `[2(024)0]`. -/
private def classifyA5FourthD4GluePattern {p : GluePattern}
    (hp : p ∈ a5FourthD4.gluePatterns) :
    PSum (Σ' word : List ℕ, p = .literal word) (p = .cyclic [2] [0, 2, 4] [0]) :=
  match p, hp with
  | .literal word, _ => PSum.inl ⟨word, rfl⟩
  | .evenPermutations _, hp => absurd hp (by simp [gluePatterns])
  | .cyclic pre block post, hp => by
    have hp' : pre = [2] ∧ block = [0, 2, 4] ∧ post = [0] := by
      simpa [gluePatterns] using hp
    rcases hp' with ⟨rfl, rfl, rfl⟩
    exact PSum.inr rfl

/-- Transporting a permutation of `[2(024)0]` along `length_eq_of_mem_gluePatterns` leaves it
unchanged on `Fin 5`. -/
private theorem permCongr_cyclic_a5FourthD4
    (hp : GluePattern.cyclic [2] [0, 2, 4] [0] ∈ a5FourthD4.gluePatterns)
    (σ : Equiv.Perm (Fin (GluePattern.cyclic [2] [0, 2, 4] [0]).length)) :
    (finCongr (length_eq_of_mem_gluePatterns hp)).permCongr σ =
      (σ : Equiv.Perm (Fin a5FourthD4.components.length)) := by
  ext i
  rw [Equiv.permCongr_apply, finCongr_apply, Fin.val_cast, finCongr_symm, finCongr_apply]
  exact congrArg (fun j : Fin 5 ↦ (σ j).val) (Fin.ext (Fin.val_cast _ _))

/-- **Every table pattern of every rootful Niemeier row acts on the lattice of its row**: by pure
component permutation (`patternIsometryHom`) on the 22 rows other than `A₅⁴ D₄`, and by the
coupled triality action (`a5FourthD4CyclicSymmetryHom`) on `A₅⁴ D₄`. -/
noncomputable def coupledPatternIsometryHom {r : RootfulNiemeierType} {p : GluePattern}
    (hp : p ∈ r.gluePatterns) :
    p.symmetries →* Isometry r.lattice r.lattice :=
  if hr : r = a5FourthD4 then by
    subst hr
    exact match classifyA5FourthD4GluePattern hp with
      | .inl ⟨_, hw⟩ => hw ▸ 1
      | .inr hw => hw ▸ a5FourthD4CyclicSymmetryHom
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
  rw [coupledPatternIsometryHom, dite_eq_left rfl]
  cases h : classifyA5FourthD4GluePattern hp with
  | inl h' => cases h'.2
  | inr h' => rfl

/-- On any literal pattern of any row, `coupledPatternIsometryHom` is trivial. -/
@[simp]
theorem coupledPatternIsometryHom_literal {r : RootfulNiemeierType} (word : List ℕ)
    (hp : GluePattern.literal word ∈ r.gluePatterns) :
    coupledPatternIsometryHom hp = 1 := by
  ext g
  rw [Subsingleton.elim g 1, map_one, MonoidHom.one_apply]

/-- **The indicated symmetries of all patterns of a row are pure position glue symmetries if and
only if the row is not `A₅⁴ D₄`.** -/
@[simp]
theorem forall_permCongr_mem_glueSymmetries_iff {r : RootfulNiemeierType} :
    (∀ p (hp : p ∈ r.gluePatterns), ∀ g ∈ p.symmetries,
      (finCongr (length_eq_of_mem_gluePatterns hp)).permCongr g ∈ r.glueSymmetries) ↔
      r ≠ a5FourthD4 := by
  refine ⟨fun h ↦ ?_, fun hr p hp g hg ↦ mem_glueSymmetries_of_mem_symmetries hr hp hg⟩
  rintro rfl
  refine a5FourthD4BlockRot_notMem_glueSymmetries ?_
  have hmem := h _ cyclic_mem_gluePatterns_a5FourthD4 a5FourthD4BlockRot
    a5FourthD4BlockRot_mem_symmetries
  exact (permCongr_cyclic_a5FourthD4 cyclic_mem_gluePatterns_a5FourthD4
    a5FourthD4BlockRot) ▸ hmem

/-- Every indicated pattern symmetry of `A₅⁴ D₄` acts on the component positions as a power
`a5FourthD4BlockRot ^ k` (`k < 3`) and on `niemeierA5FourthD4` as the matching power
`a5FourthD4TrialityRotation ^ k`. -/
theorem exists_coupledPatternIsometryHom_a5FourthD4_eq_pow {p : GluePattern}
    (hp : p ∈ a5FourthD4.gluePatterns) (g : p.symmetries) :
    ∃ k < 3,
      (finCongr (length_eq_of_mem_gluePatterns hp)).permCongr g.val = a5FourthD4BlockRot ^ k ∧
        coupledPatternIsometryHom hp g = a5FourthD4TrialityRotation ^ k := by
  cases classifyA5FourthD4GluePattern hp with
  | inl h =>
    rcases h with ⟨word, rfl⟩
    refine ⟨0, by decide, ?_, ?_⟩
    · rw [Subsingleton.elim g 1, Subgroup.coe_one, Equiv.Perm.one_def, Equiv.permCongr_refl]
      exact (pow_zero a5FourthD4BlockRot).symm
    · rw [coupledPatternIsometryHom_literal, MonoidHom.one_apply, pow_zero]
  | inr h =>
    rcases h with rfl
    obtain ⟨k, hk, hgk, hact⟩ := exists_a5FourthD4CyclicSymmetryHom_eq_pow g
    refine ⟨k, hk, ?_, ?_⟩
    · exact (permCongr_cyclic_a5FourthD4 hp g.val).trans hgk
    · rw [coupledPatternIsometryHom_a5FourthD4_cyclic, hact]

/-- Every pattern symmetry of `A₅⁴ D₄` acts on `niemeierA5FourthD4` with determinant `1`. -/
@[simp]
theorem det_coupledPatternIsometryHom_a5FourthD4 {p : GluePattern}
    (hp : p ∈ a5FourthD4.gluePatterns) (g : p.symmetries) :
    Isometry.det a5FourthD4.lattice (coupledPatternIsometryHom hp g) = 1 := by
  obtain ⟨k, -, -, hg⟩ := exists_coupledPatternIsometryHom_a5FourthD4_eq_pow hp g
  rw [hg, map_pow, det_a5FourthD4TrialityRotation, one_pow]

/-- **Every pattern symmetry group across all 23 rootful Niemeier rows embeds faithfully into the
isometry group of its row's lattice.** -/
theorem coupledPatternIsometryHom_injective {r : RootfulNiemeierType} {p : GluePattern}
    (hp : p ∈ r.gluePatterns) :
    Function.Injective (coupledPatternIsometryHom hp) := by
  by_cases hr : r = a5FourthD4
  · subst hr
    cases classifyA5FourthD4GluePattern hp with
    | inl h =>
      rcases h with ⟨word, rfl⟩
      exact fun a b _ ↦ Subsingleton.elim a b
    | inr h =>
      rcases h with rfl
      rw [coupledPatternIsometryHom_a5FourthD4_cyclic]
      exact a5FourthD4CyclicSymmetryHom_injective
  · rw [coupledPatternIsometryHom_eq_patternIsometryHom hr]
    exact patternIsometryHom_injective hr hp

end RootfulNiemeierType

end TauCeti
