/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.DGNerve.HornFilling
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
