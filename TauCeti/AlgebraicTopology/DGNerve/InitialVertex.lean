/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.DGNerve.Boundary
public import TauCeti.AlgebraicTopology.DGNerve.Quasicategory
public import TauCeti.AlgebraicTopology.Quasicategory.InitialVertex

/-!
# Initial vertices of the differential graded nerve

An object whose outgoing Hom complexes are exact in nonpositive cohomological degrees
is an initial vertex of the differential graded nerve. These degrees control the homotopy
groups of its outgoing mapping spaces. In particular, vanishing outgoing Hom complexes
suffice. Together with the terminal-vertex criterion, this constructs zero objects without
replacing mapping spaces by sets of homotopy classes.

The obstruction to extending a simplex boundary starting at `X` is a cycle in an outgoing
Hom complex of `X`. Exactness makes it a boundary, supplying the missing coherence. As in
the terminal-vertex criterion, the construction uses `DGNerve.exists_coherences_of_faces`
and `DGNerve.Coherences.exists_simplex_iff_of_boundary`.

## References

* J. Lurie, *Higher Algebra*, Construction 1.3.1.6 and Remark 1.3.1.12.
* J. Lurie, *Higher Topos Theory*, §1.2.12.
-/

public section

open CategoryTheory Limits Finset Simplicial SSet

namespace TauCeti.dgNerve

open DGNerve

universe v u

variable {R : Type v} [CommRing R] {C : Type u} [DGCategory R C]

/-- Exactness of every outgoing Hom complex in nonpositive degrees makes an object initial
in the dg nerve. No condition is imposed in positive cohomological degrees. -/
theorem isInitialVertex_of_exactAt {X : C}
    (h : ∀ (Y : C) (d : ℤ), d ≤ 0 → (dgHomComplex R X Y).ExactAt d) :
    (dgNerve R C).IsInitialVertex ((dgNerveEquiv R C).symm X) := by
  rw [SSet.isInitialVertex_iff]
  intro n σ₀ hσ₀
  have hX := congrArg (dgNerveEquiv R C) hσ₀
  rw [dgNerveEquiv_apply, Equiv.apply_symm_apply] at hX
  obtain _ | m := n
  · -- A one-dimensional boundary is filled by the zero closed map.
    let Y := Simplex.obj (R := R) (SSet.yonedaEquiv (boundary.ι 0 ≫ σ₀)) 0
    let e : (dgNerve R C) _⦋1⦌ := Simplex.edge (0 : dgCycles R X Y)
    refine ⟨SSet.yonedaEquiv.symm e, (boundary.eq_ι_comp_iff _ _).2 fun j ↦ ?_⟩
    rw [Equiv.apply_symm_apply]
    refine Simplex.ext_zero ?_
    fin_cases j
    · rfl
    · rw [dgNerve_δ]
      exact (obj_yonedaEquiv_ι_comp σ₀ 1 0).trans hX
  obtain ⟨f, hself, heq, hfaces⟩ := DGNerve.exists_coherences_of_faces (R := R) (fun _ ↦ True)
    (fun i ↦ Simplex.obj (R := R) (σ₀.app _ (boundary.vertex (m + 1) i)) 0)
    (fun l _ ↦ SSet.yonedaEquiv (boundary.ι l ≫ σ₀)) (fun l _ p ↦ obj_yonedaEquiv_ι_comp σ₀ l p)
    (fun _ _ _ _ hab ↦ map_yonedaEquiv_ι_comp σ₀ hab)
  have hself' := fun i ↦ hself i ((exists_ne i).imp fun _ hl ↦ ⟨trivial, hl⟩)
  have heq' : ∀ i j S d hij hS hd, (∃ l, l ≠ i ∧ l ≠ j ∧ l ∉ S) → _ :=
    fun i j S d hij hS hd hl ↦ heq i j S d hij hS hd (hl.imp fun _ hl ↦ ⟨trivial, hl⟩)
  have hd : (-(m + 1 : ℕ) : ℤ) + #(Ioo 0 (Fin.last (m + 2))) = 0 := by simp
  -- Only the top coherence is missing; its differential must be the boundary obstruction.
  have hexact := h (Simplex.obj (R := R)
    (σ₀.app _ (boundary.vertex (m + 1) (Fin.last (m + 2)))) 0) _
    (by omega : -(m + 1 : ℕ) + 1 ≤ (0 : ℤ))
  rw [← hX] at hexact
  obtain ⟨g, hg⟩ := (exactAt_iff_forall_exists_dgDifferential_eq R).1 hexact _
    (f.dgDifferential_boundary_eq_zero heq' hd)
  obtain ⟨x, hxobj, hxcoh⟩ := (f.exists_simplex_iff_of_boundary hself' heq' hd).2 ⟨g, hg⟩
  let x' : (dgNerve R C) _⦋m + 2⦌ := x
  refine ⟨SSet.yonedaEquiv.symm x', (boundary.eq_ι_comp_iff _ _).2 fun l ↦ ?_⟩
  rw [Equiv.apply_symm_apply, dgNerve_δ]
  exact (hfaces x hxobj (fun i j S d hij hS hd ⟨l, _, hl⟩ ↦ hxcoh i j S d hij hS hd ⟨l, hl⟩) l
    trivial).symm

/-- An object with zero outgoing Hom complexes is initial in the dg nerve. -/
theorem isInitialVertex_of_isZero {X : C} (h : ∀ Y : C, IsZero (dgHomComplex R X Y)) :
    (dgNerve R C).IsInitialVertex ((dgNerveEquiv R C).symm X) :=
  isInitialVertex_of_exactAt fun Y d _ ↦
    HomologicalComplex.ExactAt.of_isZero ((HomologicalComplex.eval _ _ d).map_isZero (h Y))

end TauCeti.dgNerve
