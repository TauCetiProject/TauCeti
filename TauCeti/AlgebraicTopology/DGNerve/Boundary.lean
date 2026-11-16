/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.DGNerve.Quasicategory
public import TauCeti.AlgebraicTopology.SimplicialSet.BoundaryColimits

/-!
# Maps out of a boundary into the differential graded nerve

The faces of a map `∂Δ[n + 2] ⟶ N_dg(C)` into the differential graded nerve of a dg category have
the objects of its vertices and agree on common faces. Conversely, coherences satisfying the dg
nerve equation on the boundary give a map out of it whose faces are
`TauCeti.DGNerve.Coherences.boundaryFace`.

## Main results

* `TauCeti.dgNerve.obj_yonedaEquiv_ι_comp` and `TauCeti.dgNerve.map_yonedaEquiv_ι_comp`: the faces
  of a map `∂Δ[n + 2] ⟶ N_dg(C)` have the objects of its vertices and agree on common faces.
* `TauCeti.dgNerve.exists_extension_of_exactAt`: exactness of the Hom complex between the
  endpoints kills the obstruction to extending a boundary.
* `TauCeti.DGNerve.Coherences.boundaryHom`: the map `∂Δ[n + 2] ⟶ N_dg(C)` with faces
  `TauCeti.DGNerve.Coherences.boundaryFace`, characterised by
  `TauCeti.DGNerve.Coherences.ι_boundaryHom`.

## References

* J. Lurie, *Higher Algebra*, Construction 1.3.1.6.
-/

public section

open CategoryTheory Finset Simplicial SSet

namespace TauCeti

open DGNerve

universe v u

namespace dgNerve

variable {R : Type v} [CommRing R] {C : Type u} [DGCategory R C] {n : ℕ}

/-- The objects of a face of a map `∂Δ[n + 1] ⟶ N_dg(C)` are its objects at the vertices other than
the omitted one. -/
theorem obj_yonedaEquiv_ι_comp (σ₀ : (∂Δ[n + 1] : SSet) ⟶ dgNerve R C) (l : Fin (n + 2))
    (p : Fin (n + 1)) :
    Simplex.obj (R := R) (SSet.yonedaEquiv (boundary.ι l ≫ σ₀)) p =
      Simplex.obj (R := R) (σ₀.app _ (boundary.vertex n (l.succAbove p))) 0 := by
  have h := NatTrans.naturality_apply σ₀ (SimplexCategory.const ⦋0⦌ ⦋n⦌ p).op
    (SSet.yonedaEquiv (boundary.ι l))
  rw [boundary.map_const_yonedaEquiv_ι] at h
  rw [SSet.yonedaEquiv_comp, h]
  -- A simplicial operator acts on objects by precomposition, by definition of `Simplex.map`.
  rfl

/-- The faces of a map `∂Δ[n + 2] ⟶ N_dg(C)` agree on their common faces. -/
theorem map_yonedaEquiv_ι_comp (σ₀ : (∂Δ[n + 2] : SSet) ⟶ dgNerve R C) {a b : Fin (n + 3)}
    (hab : a < b) :
    Simplex.map (SSet.yonedaEquiv (boundary.ι a ≫ σ₀))
        (SimplexCategory.δ (b.pred (Fin.ne_zero_of_lt hab))).toOrderHom =
      Simplex.map (SSet.yonedaEquiv (boundary.ι b ≫ σ₀))
        (SimplexCategory.δ (a.castPred (Fin.ne_last_of_lt hab))).toOrderHom := by
  have h := congrArg SSet.yonedaEquiv ((boundary.isCompatible_iff _).1
    (boundary.IsCompatible.of_hom σ₀) a b hab)
  rwa [stdSimplex.yonedaEquiv_δ_comp, stdSimplex.yonedaEquiv_δ_comp, dgNerve_δ, dgNerve_δ] at h

/-- A boundary in the dg nerve extends if the Hom complex from its first vertex to its last
vertex is exact in the degree of the boundary obstruction. A one-dimensional boundary always
extends, using the zero closed morphism. -/
theorem exists_extension_of_exactAt (σ₀ : (∂Δ[n + 1] : SSet) ⟶ dgNerve R C)
    (hexact : n ≠ 0 → (dgHomComplex R
      (Simplex.obj (R := R) (σ₀.app _ (boundary.vertex n 0)) 0)
      (Simplex.obj (R := R) (σ₀.app _ (boundary.vertex n (Fin.last (n + 1)))) 0)).ExactAt
        (-(n : ℤ) + 1)) :
    ∃ σ : Δ[n + 1] ⟶ dgNerve R C, σ₀ = ∂Δ[n + 1].ι ≫ σ := by
  obtain _ | m := n
  · let X₀ := Simplex.obj (R := R) (σ₀.app _ (boundary.vertex 0 0)) 0
    let Y := Simplex.obj (R := R) (σ₀.app _ (boundary.vertex 0 1)) 0
    let e : (dgNerve R C) _⦋1⦌ := Simplex.edge (0 : dgCycles R X₀ Y)
    refine ⟨SSet.yonedaEquiv.symm e, (boundary.eq_ι_comp_iff _ _).2 fun j ↦ ?_⟩
    rw [Equiv.apply_symm_apply]
    refine Simplex.ext_zero ?_
    fin_cases j
    · exact obj_yonedaEquiv_ι_comp σ₀ 0 0
    · rw [dgNerve_δ]
      exact obj_yonedaEquiv_ι_comp σ₀ 1 0
  obtain ⟨f, hself, heq, hfaces⟩ := DGNerve.exists_coherences_of_faces (R := R) (fun _ ↦ True)
    (fun i ↦ Simplex.obj (R := R) (σ₀.app _ (boundary.vertex (m + 1) i)) 0)
    (fun l _ ↦ SSet.yonedaEquiv (boundary.ι l ≫ σ₀)) (fun l _ p ↦ obj_yonedaEquiv_ι_comp σ₀ l p)
    (fun _ _ _ _ hab ↦ map_yonedaEquiv_ι_comp σ₀ hab)
  have hself' := fun i ↦ hself i ((exists_ne i).imp fun _ hl ↦ ⟨trivial, hl⟩)
  have heq' : ∀ i j S d hij hS hd, (∃ l, l ≠ i ∧ l ≠ j ∧ l ∉ S) → _ :=
    fun i j S d hij hS hd hl ↦ heq i j S d hij hS hd (hl.imp fun _ hl ↦ ⟨trivial, hl⟩)
  have hd : (-(m + 1 : ℕ) : ℤ) + #(Ioo 0 (Fin.last (m + 2))) = 0 := by simp
  obtain ⟨g, hg⟩ := (exactAt_iff_forall_exists_dgDifferential_eq R).1 (hexact (by omega)) _
    (f.dgDifferential_boundary_eq_zero heq' hd)
  obtain ⟨x, hxobj, hxcoh⟩ := (f.exists_simplex_iff_of_boundary hself' heq' hd).2 ⟨g, hg⟩
  let x' : (dgNerve R C) _⦋m + 2⦌ := x
  refine ⟨SSet.yonedaEquiv.symm x', (boundary.eq_ι_comp_iff _ _).2 fun l ↦ ?_⟩
  rw [Equiv.apply_symm_apply, dgNerve_δ]
  exact (hfaces x hxobj (fun i j S d hij hS hd ⟨l, _, hl⟩ ↦ hxcoh i j S d hij hS hd ⟨l, hl⟩) l
    trivial).symm

end dgNerve

namespace DGNerve

variable {R : Type v} [CommRing R] {C : Type u} [DGCategory R C] {n : ℕ} {Y : Fin (n + 3) → C}

/-- The faces `TauCeti.DGNerve.Coherences.boundaryFace` of coherences satisfying the dg nerve
equation on the boundary `∂Δ[n + 2]` form a compatible family of faces. -/
theorem Coherences.isCompatible_boundaryFace (f : Coherences R Y)
    (hself : ∀ i, f i i ∅ 0 le_rfl (empty_subset _) (by simp) = dgId R (Y i))
    (heq : ∀ i j S d hij hS hd, (∃ l, l ≠ i ∧ l ≠ j ∧ l ∉ S) →
      dgDifferential R d (f i j S d hij hS hd) = boundary R f i j S d hij hS hd) :
    boundary.IsCompatible fun l ↦
      (SSet.yonedaEquiv (X := dgNerve R C)).symm (f.boundaryFace hself heq l) := by
  rw [boundary.isCompatible_iff]
  intro a b hab
  -- The faces of a simplex of `N_dg(C)` are given by `Simplex.map` (`dgNerve_δ`).
  exact (stdSimplex.δ_comp_yonedaEquiv_symm _ _).trans ((congrArg SSet.yonedaEquiv.symm
    (f.boundaryFace_map_δ hself heq hab)).trans (stdSimplex.δ_comp_yonedaEquiv_symm _ _).symm)

/-- The map `∂Δ[n + 2] ⟶ N_dg(C)` glued from the faces `TauCeti.DGNerve.Coherences.boundaryFace`
of coherences satisfying the dg nerve equation on the boundary. -/
noncomputable def Coherences.boundaryHom (f : Coherences R Y)
    (hself : ∀ i, f i i ∅ 0 le_rfl (empty_subset _) (by simp) = dgId R (Y i))
    (heq : ∀ i j S d hij hS hd, (∃ l, l ≠ i ∧ l ≠ j ∧ l ∉ S) →
      dgDifferential R d (f i j S d hij hS hd) = boundary R f i j S d hij hS hd) :
    (∂Δ[n + 2] : SSet) ⟶ dgNerve R C :=
  (f.isCompatible_boundaryFace hself heq).desc

/-- The face of `TauCeti.DGNerve.Coherences.boundaryHom` opposite to `l` is
`TauCeti.DGNerve.Coherences.boundaryFace`. -/
@[simp]
theorem Coherences.ι_boundaryHom (f : Coherences R Y)
    (hself : ∀ i, f i i ∅ 0 le_rfl (empty_subset _) (by simp) = dgId R (Y i))
    (heq : ∀ i j S d hij hS hd, (∃ l, l ≠ i ∧ l ≠ j ∧ l ∉ S) →
      dgDifferential R d (f i j S d hij hS hd) = boundary R f i j S d hij hS hd)
    (l : Fin (n + 3)) :
    boundary.ι l ≫ f.boundaryHom hself heq =
      (SSet.yonedaEquiv (X := dgNerve R C)).symm (f.boundaryFace hself heq l) :=
  boundary.IsCompatible.ι_desc _ l

end DGNerve

end TauCeti
