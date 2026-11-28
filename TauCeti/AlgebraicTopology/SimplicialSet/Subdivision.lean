/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.Subdivision

/-!
# The last-vertex map of a simplicial set

The last-vertex map sends a chain of nonempty faces of a standard simplex to the
simplex of their largest vertices. It extends to arbitrary simplicial sets through
the left Kan extension defining Mathlib's subdivision functor. Its naturality
allows subdivision and last-vertex precomposition to be used on simplicial pairs.

The construction uses `SSet.stdSimplex.sdIso` and `SSet.stdSimplex.isoNerve` to
retain Mathlib's subdivision and standard-simplex conventions.

`TauCeti.SSet.lastVertexIter` gives the iterated maps. Naturality supplies face,
degeneracy and subcomplex restriction squares. Original vertices are fixed, and
the new vertex of the subdivided interval maps to its last endpoint.

## References

* J. F. Jardine, *Simplicial approximation*, Theory and Applications of Categories
  12 (2004), 34–72.
-/

public section

universe u

open CategoryTheory CategoryTheory.Functor Opposite Simplicial
open PartialOrder

namespace SimplexCategory

/-- The monotone map sending a nonempty face of a simplex to its largest vertex. -/
noncomputable def lastVertexOrderHom (n : SimplexCategory) :
    NonemptyFiniteChains (ULift.{u} (Fin (n.len + 1))) →o
      ULift.{u} (Fin (n.len + 1)) where
  toFun s := s.finset.max' s.nonempty
  monotone' _ _ h := Finset.max'_subset _ h

@[simp]
lemma lastVertexOrderHom_apply (n : SimplexCategory)
    (s : NonemptyFiniteChains (ULift.{u} (Fin (n.len + 1)))) :
    lastVertexOrderHom n s = s.finset.max' s.nonempty := (rfl)

/-- Taking the last vertex commutes with every simplex operator, including surjections. -/
lemma Hom.lastVertexOrderHom_map {n m : SimplexCategory} (f : n ⟶ m)
    (s : NonemptyFiniteChains (ULift.{u} (Fin (n.len + 1)))) :
    lastVertexOrderHom m (s.map (toPartOrd.map f).hom) =
      toPartOrd.map f (lastVertexOrderHom n s) := by
  classical
  -- Align finite-image equality with the decidable equality used by the maximum theorem.
  let : DecidableEq (ULift.{u} (Fin (m.len + 1))) := LinearOrder.toDecidableEq
  let g : ULift.{u} (Fin (n.len + 1)) →o ULift.{u} (Fin (m.len + 1)) :=
    { toFun := fun x ↦ ULift.up (f x.down)
      monotone' := fun _ _ h ↦ f.toOrderHom.monotone h }
  have hmap : (s.map (toPartOrd.map f).hom).finset = s.finset.image g := by
    exact Finset.ext fun x ↦
      (NonemptyFiniteChains.mem_map_iff s (toPartOrd.map f).hom x).trans
        (@Finset.mem_image _ _ this (⇑g) s.finset x).symm
  rw [lastVertexOrderHom_apply]
  calc
    _ = (s.finset.image g).max' (s.nonempty.image g) := by
      congr 1
    _ = _ := Finset.max'_image g.monotone s.finset (s.nonempty.image g)

private lemma sdLastVertexApp_apply (n : SimplexCategory) {d : ℕ}
    (s : (sd.obj n : SSet.{u}) _⦋d⦌) (i : Fin (d + 1)) :
    (nerveMap (lastVertexOrderHom n).monotone.functor ≫
      (SSet.stdSimplex.isoNerve n.len).inv).app _ s i =
      (lastVertexOrderHom n (s.obj i)).down := by
  dsimp only [NatTrans.comp_app]
  -- Evaluation of the nerve map is postcomposition with the maximum functor.
  exact SSet.stdSimplex.isoNerve_inv_app_apply
    ((nerveMap (lastVertexOrderHom n).monotone.functor).app _ s) i

end SimplexCategory

namespace TauCeti.SimplexCategory

open _root_.SimplexCategory

/-- The last-vertex map on the subdivisions of standard simplices. -/
noncomputable def sdLastVertex : sd.{u} ⟶ SSet.stdSimplex.{u} where
  app n := nerveMap (lastVertexOrderHom n).monotone.functor ≫
    (SSet.stdSimplex.isoNerve n.len).inv
  naturality {n m} f := by
    ext d s
    induction n using SimplexCategory.rec with | _ n
    induction m using SimplexCategory.rec with | _ m
    induction d using Opposite.rec with | _ d
    induction d using SimplexCategory.rec with | _ d
    apply SSet.stdSimplex.ext
    intro i
    -- Normalize the standard-simplex action and bundled chain types before using
    -- the coordinate formula; rewriting inside those dependent wrappers is ill-typed.
    change (nerveMap (lastVertexOrderHom ⦋m⦌).monotone.functor ≫
        (SSet.stdSimplex.isoNerve m).inv).app _ ((sd.map f).app _ s) i =
      f ((nerveMap (lastVertexOrderHom ⦋n⦌).monotone.functor ≫
        (SSet.stdSimplex.isoNerve n).inv).app _ s i)
    erw [sdLastVertexApp_apply ⦋m⦌, sdLastVertexApp_apply ⦋n⦌]
    exact congrArg (fun x : ULift.{u} (Fin (m + 1)) ↦ x.down)
      (f.lastVertexOrderHom_map (s.obj i))

/-- The i-th vertex of the image is the maximum of the i-th face in the input chain. -/
@[simp]
lemma sdLastVertex_app_apply {n d : ℕ}
    (s : (sd.obj ⦋n⦌ : SSet.{u}) _⦋d⦌) (i : Fin (d + 1)) :
    (sdLastVertex.app ⦋n⦌).app _ s i =
      (lastVertexOrderHom ⦋n⦌ (s.obj i)).down := by
  exact sdLastVertexApp_apply ⦋n⦌ s i

end TauCeti.SimplexCategory

namespace TauCeti.SSet

open _root_.SSet

/-- The natural last-vertex map from subdivision to the original simplicial set. -/
noncomputable def lastVertex : sd.{u} ⟶ 𝟭 SSet.{u} :=
  sd.descOfIsLeftKanExtension stdSimplex.sdIso.inv _
    (SimplexCategory.sdLastVertex ≫ (Functor.rightUnitor stdSimplex).inv)

end TauCeti.SSet

namespace SimplexCategory

open SSet TauCeti.SSet

/-- The last-vertex map restricts along the Kan-extension unit to the map on faces. -/
@[reassoc (attr := simp)]
lemma sdIso_inv_lastVertex (n : SimplexCategory) :
    stdSimplex.sdIso.{u}.inv.app n ≫ lastVertex.app (stdSimplex.obj n) =
      TauCeti.SimplexCategory.sdLastVertex.{u}.app n := by
  simpa only [lastVertex, NatTrans.comp_app, Functor.rightUnitor_inv_app,
    Category.comp_id] using
    _root_.SSet.sd.descOfIsLeftKanExtension_fac_app stdSimplex.sdIso.inv _
      (TauCeti.SimplexCategory.sdLastVertex.{u} ≫ (Functor.rightUnitor stdSimplex).inv) n

end SimplexCategory

namespace TauCeti.SSet

open _root_.SSet

/-- On a standard simplex, the last-vertex map is the nerve of the maximum map. -/
lemma lastVertex_stdSimplex (n : ℕ) :
    lastVertex.app (Δ[n] : SSet.{u}) = stdSimplex.sdIso.hom.app ⦋n⦌ ≫
      SimplexCategory.sdLastVertex.app ⦋n⦌ := by
  exact ((stdSimplex.sdIso.app ⦋n⦌).inv_comp_eq).mp
    (SimplexCategory.sdIso_inv_lastVertex ⦋n⦌)

/-- For any simplex x, including a degenerate one, its subdivided representing map
sends a chain of standard faces to the image under x of the simplex of their maxima. -/
@[reassoc]
lemma sdIso_inv_sd_map_lastVertex {X : SSet.{u}} {n : ℕ} (x : X _⦋n⦌) :
    stdSimplex.sdIso.inv.app ⦋n⦌ ≫ sd.map (yonedaEquiv.symm x) ≫ lastVertex.app X =
      SimplexCategory.sdLastVertex.app ⦋n⦌ ≫ yonedaEquiv.symm x := by
  rw [lastVertex.naturality, _root_.SimplexCategory.sdIso_inv_lastVertex_assoc, Functor.id_map]

/-- On an arbitrary simplex x, a chain maps to `X.map f.op x`, where f is the
simplex operator whose i-th value is the maximum of the i-th face, as computed by
`TauCeti.SimplexCategory.sdLastVertex_app_apply`. -/
@[simp]
lemma sdIso_inv_sd_map_lastVertex_apply {X : SSet.{u}} {n d : ℕ} (x : X _⦋n⦌)
    (s : (_root_.SimplexCategory.sd.obj ⦋n⦌ : SSet.{u}) _⦋d⦌) :
    dsimp% (lastVertex.app X).app _ ((sd.map (yonedaEquiv.symm x)).app _
      ((stdSimplex.sdIso.inv.app ⦋n⦌).app _ s)) =
        X.map (stdSimplex.objEquiv ((SimplexCategory.sdLastVertex.app ⦋n⦌).app _ s)).op x := by
  have h := congrArg (fun f : _root_.SimplexCategory.sd.obj ⦋n⦌ ⟶ X ↦
    f.app (op ⦋d⦌) s) (sdIso_inv_sd_map_lastVertex x)
  simpa only [NatTrans.comp_app, ConcreteCategory.comp_apply,
    _root_.SSet.yonedaEquiv_symm_app] using h

/-- In nerve coordinates, the image simplex lists the largest vertices of its faces. -/
@[simp]
lemma lastVertex_stdSimplex_apply {n d : ℕ}
    (s : (SimplexCategory.sd.obj ⦋n⦌ : SSet.{u}) _⦋d⦌) (i : Fin (d + 1)) :
    (dsimp% (lastVertex.app Δ[n]).app _ ((stdSimplex.sdIso.inv.app ⦋n⦌).app _ s)) i =
      (SimplexCategory.lastVertexOrderHom ⦋n⦌ (s.obj i)).down := by
  have h := congrArg (fun f : SimplexCategory.sd.obj ⦋n⦌ ⟶ Δ[n] ↦
    f.app (op ⦋d⦌) s) (_root_.SimplexCategory.sdIso_inv_lastVertex.{u} ⦋n⦌)
  simpa only [NatTrans.comp_app, types_comp_apply, SimplexCategory.sdLastVertex_app_apply]
    using congrArg (fun t : Δ[n] _⦋d⦌ ↦ t i) h

/-- The iterated subdivision functor, with the newest subdivision applied last.
The recursion is exposed so its object types compute in iterated-map signatures. -/
@[expose] noncomputable def sdIter : ℕ → SSet.{u} ⥤ SSet.{u}
  | 0 => 𝟭 _
  | r + 1 => sdIter r ⋙ sd

@[simp]
lemma sdIter_zero : sdIter.{u} 0 = 𝟭 SSet := (rfl)

@[simp]
lemma sdIter_succ (r : ℕ) : sdIter.{u} (r + 1) = sdIter r ⋙ sd := (rfl)

/-- The iterated last-vertex map, removing the newest subdivision first. -/
noncomputable def lastVertexIter : (r : ℕ) → sdIter.{u} r ⟶ 𝟭 SSet
  | 0 => 𝟙 _
  | r + 1 => whiskerLeft (sdIter r) lastVertex ≫
      (Functor.rightUnitor (sdIter r)).hom ≫ lastVertexIter r

end TauCeti.SSet

namespace SSet

open TauCeti.SSet

/-- At depth zero, the iterated last-vertex map is the identity. -/
@[simp]
lemma lastVertexIter_zero_app (X : SSet.{u}) : (lastVertexIter 0).app X = 𝟙 X := (rfl)

/-- Remove the outermost subdivision before applying the previous iterate. -/
@[simp]
lemma lastVertexIter_succ_app (X : SSet.{u}) (r : ℕ) :
    (lastVertexIter (r + 1)).app X =
      lastVertex.app ((sdIter r).obj X) ≫ (lastVertexIter r).app X := by
  dsimp only [lastVertexIter, NatTrans.comp_app, whiskerLeft_app,
    Functor.rightUnitor_hom_app]
  exact congrArg (lastVertex.app ((sdIter r).obj X) ≫ ·) (Category.id_comp _)

end SSet

namespace TauCeti.SSet

open _root_.SSet

/-- Split an iterated subdivision into two successive refinement depths. -/
noncomputable def sdIterAddIso (r : ℕ) : (s : ℕ) →
    sdIter.{u} (r + s) ≅ sdIter r ⋙ sdIter s
  | 0 => (Functor.rightUnitor (sdIter r)).symm
  | s + 1 => isoWhiskerRight (sdIterAddIso r s) sd ≪≫
      Functor.associator (sdIter r) (sdIter s) sd

end TauCeti.SSet

namespace SSet

open TauCeti.SSet

/-- At zero additional depth, the refinement comparison is the identity. -/
@[simp]
lemma sdIterAddIso_zero_hom_app (X : SSet.{u}) (r : ℕ) :
    (sdIterAddIso r 0).hom.app X = 𝟙 ((sdIter r).obj X) := (rfl)

/-- At successor depth, subdivision carries the preceding comparison. -/
@[simp]
lemma sdIterAddIso_succ_hom_app (X : SSet.{u}) (r s : ℕ) :
    (sdIterAddIso r (s + 1)).hom.app X = sd.map ((sdIterAddIso r s).hom.app X) := by
  dsimp only [sdIterAddIso, Iso.trans_hom, NatTrans.comp_app,
    isoWhiskerRight_hom, whiskerRight_app, Functor.associator_hom_app]
  exact Category.comp_id _

/-- Collapsing two successive refinements agrees with collapsing their total depth. -/
@[reassoc]
lemma sdIterAddIso_hom_app_lastVertexIter (X : SSet.{u}) (r s : ℕ) :
    (sdIterAddIso r s).hom.app X ≫
      (lastVertexIter s).app ((sdIter r).obj X) ≫ (lastVertexIter r).app X =
        (lastVertexIter (r + s)).app X := by
  induction s with
  | zero =>
    dsimp only [Nat.add_zero, sdIter, Functor.id_obj, Functor.comp_obj]
    simp only [sdIterAddIso_zero_hom_app, lastVertexIter_zero_app, Category.id_comp]
  | succ s ih =>
    dsimp only [Nat.add_succ, sdIter, Functor.comp_obj]
    rw [sdIterAddIso_succ_hom_app, lastVertexIter_succ_app, lastVertexIter_succ_app]
    simp only [Functor.comp_obj] at *
    rw [← Category.assoc, ← Category.assoc, lastVertex.naturality]
    simpa only [Functor.id_map, Category.assoc] using
      congrArg (lastVertex.app ((sdIter (r + s)).obj X) ≫ ·) ih

end SSet

namespace TauCeti.SSet.stdSimplex

open _root_.SSet

/-- Face coordinates for the vertices of a subdivided standard simplex. -/
noncomputable def sdVertex (n : ℕ) :
    NonemptyFiniteChains (ULift.{u} (Fin (n + 1))) ≃ (sd.obj Δ[n]) _⦋0⦌ :=
  nerveEquiv.symm.trans ((stdSimplex.sdIso.app ⦋n⦌).symm.app (op ⦋0⦌)).toEquiv

/-- Recover the nonempty face represented by a subdivision vertex. -/
lemma sdVertex_symm_apply (n : ℕ) (x : (sd.obj (Δ[n] : SSet.{u})) _⦋0⦌) :
    (sdVertex n).symm x =
      nerveEquiv ((stdSimplex.sdIso.hom.app ⦋n⦌).app (op ⦋0⦌) x) := (rfl)

end TauCeti.SSet.stdSimplex

namespace PartialOrder.NonemptyFiniteChains

open SSet TauCeti.SSet.stdSimplex TauCeti.SSet

lemma sdVertex_def {n : ℕ} (s : NonemptyFiniteChains (ULift.{u} (Fin (n + 1)))) :
    sdVertex n s = (stdSimplex.sdIso.inv.app ⦋n⦌).app (op ⦋0⦌)
      (ComposableArrows.mk₀ s) := (rfl)

/-- The vertex corresponding to a face maps to its largest vertex. -/
@[simp]
lemma lastVertex_sdVertex {n : ℕ} (s : NonemptyFiniteChains (ULift.{u} (Fin (n + 1)))) :
    dsimp% (lastVertex.app Δ[n]).app _ (sdVertex n s) =
      stdSimplex.const n (SimplexCategory.lastVertexOrderHom ⦋n⦌ s).down (op ⦋0⦌) := by
  rw [s.sdVertex_def]
  apply stdSimplex.obj₀Equiv.injective
  exact lastVertex_stdSimplex_apply (ComposableArrows.mk₀ s) 0

end PartialOrder.NonemptyFiniteChains

namespace TauCeti.SSet

open _root_.SSet

/-- Every vertex of an arbitrary simplicial set is fixed after subdivision of its
representing zero-simplex, regardless of the choice of subdivided vertex. -/
@[simp]
lemma lastVertex_sd_map_vertex {X : SSet.{u}} (x : X _⦋0⦌)
    (v : (sd.obj (Δ[0] : SSet.{u})) _⦋0⦌) :
    dsimp% (lastVertex.app X).app _ ((sd.map (const x)).app _ v) = x := by
  obtain ⟨s, rfl⟩ := (stdSimplex.sdVertex 0).surjective v
  rw [← yonedaEquiv_symm_zero, s.sdVertex_def]
  have hcomp := sdIso_inv_sd_map_lastVertex_apply x (ComposableArrows.mk₀ s)
  refine hcomp.trans ?_
  have h : _root_.SSet.stdSimplex.objEquiv
      ((SimplexCategory.sdLastVertex.app ⦋0⦌).app (op ⦋0⦌)
        (ComposableArrows.mk₀ s)) = 𝟙 ⦋0⦌ := Subsingleton.elim _ _
  rw [h, op_id, X.map_id]
  exact CategoryTheory.id_apply _

end TauCeti.SSet

namespace TauCeti.SSet.stdSimplex

open _root_.SSet
open PartialOrder.NonemptyFiniteChains

/-- Original vertices are fixed by the last-vertex map, in every dimension. -/
example {n : ℕ} (a : Fin (n + 1)) :
    dsimp% (lastVertex.app Δ[n]).app _
        (sdVertex n ⟨{ULift.up a}, Finset.singleton_nonempty _, fun i j ↦ le_total i j⟩) =
      stdSimplex.const n a (op ⦋0⦌) := by
  rw [lastVertex_sdVertex, SimplexCategory.lastVertexOrderHom_apply]
  simp

/-- The new vertex of the subdivided interval maps to the last endpoint. -/
example :
    (lastVertex.{u}.app Δ[1]).app _
        (sdVertex 1 ⟨{ULift.up (0 : Fin 2), ULift.up 1}, Finset.insert_nonempty _ _,
          fun i j ↦ le_total i j⟩) = stdSimplex.const 1 1 (op ⦋0⦌) := by
  have hmax : ({ULift.up (0 : Fin 2), ULift.up 1} : Finset (ULift.{u} (Fin 2))).max'
      (Finset.insert_nonempty _ _) = ULift.up 1 := by
    apply (Finset.max'_eq_iff _ _ _).mpr
    simp
  rw [lastVertex_sdVertex, SimplexCategory.lastVertexOrderHom_apply]
  exact congrArg (fun v : ULift.{u} (Fin 2) ↦ stdSimplex.const 1 v.down (op ⦋0⦌)) hmax

end TauCeti.SSet.stdSimplex
