/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.DGNerve.Functor
public import TauCeti.AlgebraicTopology.Quasicategory.FullyFaithful
public import TauCeti.CategoryTheory.DG.FullSubcategory

/-!
# Full subcategories of the differential graded nerve

The dg nerve commutes with restriction to a full dg subcategory. More precisely,
`TauCeti.DGFullSubcategory.dgNerveIso` identifies the nerve of the full dg subcategory
on `P` with the full enhanced subcategory of the ambient nerve on the vertices satisfying
`P`. The isomorphism intertwines the two inclusions. In particular the dg nerve of a full
dg inclusion is fully faithful on mapping spaces, not merely on homotopy categories.

A simplex lifts precisely when all its objects satisfy `P`: its coherences and their
identities are unchanged. This applies, for example, to the full dg subcategory of
K-injective complexes inside all cochain complexes. Recognizing its nerve as a full
subcategory allows limits and colimits constructed in the ambient enhancement to be
restricted once closure of the chosen objects has been established.

## References

* J. Lurie, *Higher Algebra*, Construction 1.3.1.6 and Definition 1.3.5.8.
* J. Lurie, *Higher Topos Theory*, §1.2.11.
-/

public section

open CategoryTheory Finset Opposite Simplicial

namespace TauCeti

universe v u

noncomputable section

variable {R : Type v} [CommRing R] {C : Type u} [DGCategory R C] {P : C → Prop}

namespace DGNerve.Simplex

/-- Lift a dg simplex to the full dg subcategory when each of its objects satisfies the
predicate. Its coherences are the original coherences. -/
-- The object field must reduce to identify the types of the original and lifted coherences.
@[expose]
def liftDGFullSubcategory {n : ℕ} (x : Simplex R C n) (hx : ∀ i, P (x.obj i)) :
    Simplex R (DGFullSubcategory P) n where
  obj i := ⟨x.obj i, hx i⟩
  coh := x.coh
  coh_self i := by simpa only [DGFullSubcategory.dgId_eq] using x.coh_self i
  dgDifferential_coh i j S d hij hS hd := by
    rw [DGFullSubcategory.dgDifferential_eq, boundary_def]
    simpa only [boundary_def, DGFullSubcategory.dgComp_eq] using
      x.dgDifferential_coh i j S d hij hS hd

/-- The objects of the lifted simplex are the original objects with their witnesses. -/
@[simp]
lemma liftDGFullSubcategory_obj {n : ℕ} (x : Simplex R C n) (hx : ∀ i, P (x.obj i))
    (i : Fin (n + 1)) :
    (x.liftDGFullSubcategory hx).obj i = ⟨x.obj i, hx i⟩ :=
  (rfl)

/-- Lifting to the full dg subcategory does not change a coherence. -/
@[simp]
lemma liftDGFullSubcategory_coh {n : ℕ} (x : Simplex R C n) (hx : ∀ i, P (x.obj i))
    (i j : Fin (n + 1)) (S : Finset (Fin (n + 1))) (d : ℤ) (hij : i ≤ j)
    (hS : S ⊆ Ioo i j) (hd : d + #S = 0) :
    (x.liftDGFullSubcategory hx).coh i j S d hij hS hd = x.coh i j S d hij hS hd :=
  (rfl)

/-- Forgetting a lift to a full dg subcategory recovers the original simplex. -/
@[simp]
lemma mapDGNerveSimplex_inclusion_liftDGFullSubcategory {n : ℕ} (x : Simplex R C n)
    (hx : ∀ i, P (x.obj i)) :
    (DGFullSubcategory.inclusion (R := R)).mapDGNerveSimplex
      (x.liftDGFullSubcategory hx) = x := by
  refine Simplex.ext (by ext i; simp) fun i j S d hij hS hd ↦ ?_
  exact DGFullSubcategory.inclusion_dgMap_heq R
    (X := (x.liftDGFullSubcategory hx).obj i) (Y := (x.liftDGFullSubcategory hx).obj j)
    (x.coh i j S d hij hS hd)

/-- Lifting the image of a simplex in a full dg subcategory recovers that simplex. -/
@[simp]
lemma liftDGFullSubcategory_mapDGNerveSimplex_inclusion {n : ℕ}
    (x : Simplex R (DGFullSubcategory P) n) :
    ((DGFullSubcategory.inclusion (R := R)).mapDGNerveSimplex x).liftDGFullSubcategory
      (fun i ↦ by simpa only [CategoryTheory.EnrichedFunctor.mapDGNerveSimplex_obj,
        DGFullSubcategory.inclusion_obj] using (x.obj i).property) = x := by
  refine Simplex.ext (by ext i; simp) fun i j S d hij hS hd ↦ ?_
  exact DGFullSubcategory.inclusion_dgMap_heq R (x.coh i j S d hij hS hd)

/-- Lifting a simplex to a full dg subcategory commutes with every simplicial operator. -/
lemma liftDGFullSubcategory_map {n m : ℕ} (x : Simplex R C n) (hx : ∀ i, P (x.obj i))
    (α : Fin (m + 1) →o Fin (n + 1)) :
    (x.map α).liftDGFullSubcategory
      (fun i ↦ by simpa only [map_obj, Function.comp_apply] using hx (α i)) =
      (x.liftDGFullSubcategory hx).map α := by
  refine Simplex.ext rfl fun i j S d hij hS hd ↦ heq_of_eq ?_
  rw [liftDGFullSubcategory_coh, map_coh, map_coh]
  by_cases h : #(S.image α) = #S ∧ S.image α ⊆ Ioo (α i) (α j)
  · rw [mapCoh_eq_coh _ _ h, mapCoh_eq_coh _ _ h]
    rfl
  · rw [mapCoh_eq_zero _ _ h, mapCoh_eq_zero _ _ h]
    rfl

end DGNerve.Simplex

namespace dgNerve

/-- A dg simplex belongs to the full enhanced subcategory on `P` exactly when all its
objects satisfy `P`. -/
@[simp]
lemma mem_fullEnhancedSubcategory_iff {n : ℕ} (x : (dgNerve R C) _⦋n⦌) :
    x ∈ ((dgNerve R C).fullEnhancedSubcategory (fun v ↦ P (v.obj 0))).obj
      (op ⦋n⦌) ↔ ∀ i, P (x.obj i) := by
  simp only [SSet.mem_fullEnhancedSubcategory_obj_iff_forall_fin, dgNerve_map_apply]
  rfl

end dgNerve

namespace DGFullSubcategory

variable (R P)

/-- The dg nerve of a full dg subcategory is the full enhanced subcategory of the ambient
dg nerve on the same objects. This is an isomorphism of simplicial sets in every degree. -/
def dgNerveIso :
    dgNerve R (DGFullSubcategory P) ≅
      ((dgNerve R C).fullEnhancedSubcategory (fun v ↦ P (v.obj 0)) : SSet) :=
  NatIso.ofComponents (fun n ↦ Equiv.toIso
    { toFun (x : (dgNerve R (DGFullSubcategory P)).obj n) :=
        ⟨(inclusion (R := R)).mapDGNerveSimplex x,
          (dgNerve.mem_fullEnhancedSubcategory_iff _).2 (fun i ↦ by
            -- At an arbitrary simplex-category object, reduce the exposed dg-nerve object
            -- wrapper to match the simplex-level object formula.
            erw [CategoryTheory.EnrichedFunctor.mapDGNerveSimplex_obj, inclusion_obj]
            exact (x.obj i).property)⟩
      invFun x := x.1.liftDGFullSubcategory
        ((dgNerve.mem_fullEnhancedSubcategory_iff x.1).1 x.2)
      left_inv x := x.liftDGFullSubcategory_mapDGNerveSimplex_inclusion
      right_inv x := Subtype.ext (x.1.mapDGNerveSimplex_inclusion_liftDGFullSubcategory _) })
    (fun {n m} α ↦ by
      ext x
      apply Subtype.ext
      exact (inclusion (R := R)).mapDGNerveSimplex_map x α.unop.toOrderHom)

/-- The comparison identifies the inclusion of the full enhanced subcategory with the
dg nerve of the enriched inclusion. -/
@[reassoc (attr := simp)]
lemma dgNerveIso_hom_ι :
    (dgNerveIso R P).hom ≫ SSet.Subcomplex.ι _ =
      (inclusion (R := R) (P := P)).mapDGNerve := by
  ext n x
  exact (CategoryTheory.EnrichedFunctor.mapDGNerve_app _ x).symm

/-- On simplices, the forward comparison applies the enriched inclusion. -/
@[simp]
lemma dgNerveIso_hom_app_coe (n : SimplexCategoryᵒᵖ)
    (x : (dgNerve R (DGFullSubcategory P)).obj n) :
    dsimp% ((dgNerveIso R P).hom.app n x).1 =
      (inclusion (R := R) (P := P)).mapDGNerveSimplex x :=
  (rfl)

/-- The inverse comparison lifts the objects and retains every coherence. -/
@[simp]
lemma dgNerveIso_inv_app (n : SimplexCategoryᵒᵖ)
    (x : ((dgNerve R C).fullEnhancedSubcategory
      (fun v ↦ P (v.obj 0))).obj n) :
    dsimp% (dgNerveIso R P).inv.app n x =
      x.1.liftDGFullSubcategory ((dgNerve.mem_fullEnhancedSubcategory_iff x.1).1 x.2) :=
  (rfl)

/-- The nerve of a full dg inclusion is fully faithful on right mapping spaces. -/
instance isFullyFaithful_mapDGNerve_inclusion :
    SSet.IsFullyFaithful (inclusion (R := R) (P := P)).mapDGNerve := by
  rw [← dgNerveIso_hom_ι R P]
  infer_instance

end DGFullSubcategory

end

end TauCeti
