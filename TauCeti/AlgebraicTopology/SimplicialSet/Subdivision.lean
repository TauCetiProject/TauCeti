/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.Subdivision
public import TauCeti.AlgebraicTopology.SimplicialComplex.Subdivision.Basic

/-!
# The last-vertex map of a simplicial set

The last-vertex map sends a chain of nonempty faces of a standard simplex to the
simplex of their largest vertices. It extends to arbitrary simplicial sets through
the left Kan extension defining Mathlib's subdivision functor. Its naturality
allows subdivision and last-vertex precomposition to be used on simplicial pairs.

The construction uses `SSet.stdSimplex.sdIso` and `SSet.stdSimplex.isoNerve` to
retain Mathlib's subdivision and standard-simplex conventions.

`SSet.lastVertexIter` gives the iterated maps, with face, degeneracy and subcomplex
restriction squares. Original vertices are fixed, and the new vertex of the
subdivided interval maps to its last endpoint. On the same face carrier, the
vertex computation agrees with `AbstractSimplicialComplex.lastVertexMap`.

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
lemma lastVertexOrderHom_map {n m : SimplexCategory} (f : n ⟶ m)
    (s : NonemptyFiniteChains (ULift.{u} (Fin (n.len + 1)))) :
    lastVertexOrderHom m (s.map (toPartOrd.map f).hom) =
      toPartOrd.map f (lastVertexOrderHom n s) := by
  classical
  -- Normalize the categorical coercions to the lifted monotone map on finite ordinals.
  dsimp [lastVertexOrderHom, NonemptyFiniteChains.map]
  have hf : Monotone (fun x : ULift.{u} (Fin (n.len + 1)) ↦
      (ULift.up (f x.down) : ULift.{u} (Fin (m.len + 1)))) :=
    fun _ _ h ↦ f.toOrderHom.monotone h
  refine (Finset.isGreatest_max' (α := ULift.{u} (Fin (m.len + 1)))
    (s.map (toPartOrd.map f).hom).finset (s.map (toPartOrd.map f).hom).nonempty).unique ?_
  convert! hf.map_isGreatest (Finset.isGreatest_max' s.finset s.nonempty) using 1
  · ext x
    exact NonemptyFiniteChains.mem_map_iff s (toPartOrd.map f).hom x

/-- The last-vertex map on the subdivisions of standard simplices. -/
noncomputable def sdLastVertex : sd.{u} ⟶ SSet.stdSimplex.{u} where
  app n := nerveMap (lastVertexOrderHom n).monotone.functor ≫
    (SSet.stdSimplex.isoNerve n.len).inv
  naturality {n m} f := by
    ext d s
    apply ULift.ext
    apply SimplexCategory.Hom.ext
    ext i
    exact congrArg (fun x : ULift.{u} (Fin (m.len + 1)) ↦ x.down.val)
      (lastVertexOrderHom_map f (s.obj i))

@[simp]
lemma sdLastVertex_app_apply {n d : ℕ}
    (s : (sd.obj ⦋n⦌ : SSet.{u}) _⦋d⦌) (i : Fin (d + 1)) :
    (sdLastVertex.app ⦋n⦌).app _ s i =
      (lastVertexOrderHom ⦋n⦌ (s.obj i)).down := (rfl)

end SimplexCategory

namespace SSet

/-- The natural last-vertex map from subdivision to the original simplicial set. -/
noncomputable def lastVertex : sd.{u} ⟶ 𝟭 SSet.{u} :=
  sd.descOfIsLeftKanExtension stdSimplex.sdIso.inv _
    (SimplexCategory.sdLastVertex ≫ (Functor.rightUnitor stdSimplex).inv)

/-- The last-vertex map restricts along the Kan-extension unit to the map on faces. -/
@[reassoc (attr := simp)]
lemma sdIso_inv_lastVertex (n : SimplexCategory) :
    stdSimplex.sdIso.inv.app n ≫ lastVertex.app (stdSimplex.obj n) =
      SimplexCategory.sdLastVertex.app n := by
  simpa only [lastVertex, NatTrans.comp_app, Functor.rightUnitor_inv_app,
    Category.comp_id] using
    sd.descOfIsLeftKanExtension_fac_app stdSimplex.sdIso.inv _
      (SimplexCategory.sdLastVertex ≫ (Functor.rightUnitor stdSimplex).inv) n

/-- On a standard simplex, the last-vertex map is the nerve of the maximum map. -/
lemma lastVertex_stdSimplex (n : ℕ) :
    lastVertex.app (Δ[n] : SSet.{u}) = stdSimplex.sdIso.hom.app ⦋n⦌ ≫
      SimplexCategory.sdLastVertex.app ⦋n⦌ := by
  calc
    _ = (stdSimplex.sdIso.hom.app ⦋n⦌ ≫ stdSimplex.sdIso.inv.app ⦋n⦌) ≫
        lastVertex.app Δ[n] := by simp
    _ = _ := by rw [Category.assoc, sdIso_inv_lastVertex]

/-- On every simplex of a simplicial set, the map is given by the last vertices
of its chain of faces. This also describes degenerate simplices. -/
@[reassoc]
lemma sdIso_inv_sd_map_lastVertex {X : SSet.{u}} {n : ℕ} (x : X _⦋n⦌) :
    stdSimplex.sdIso.inv.app ⦋n⦌ ≫ sd.map (yonedaEquiv.symm x) ≫ lastVertex.app X =
      SimplexCategory.sdLastVertex.app ⦋n⦌ ≫ yonedaEquiv.symm x := by
  rw [lastVertex.naturality, sdIso_inv_lastVertex_assoc, Functor.id_map]

/-- In nerve coordinates, the image simplex lists the largest vertices of its faces. -/
@[simp]
lemma lastVertex_stdSimplex_apply {n d : ℕ}
    (s : (SimplexCategory.sd.obj ⦋n⦌ : SSet.{u}) _⦋d⦌) (i : Fin (d + 1)) :
    (dsimp% (lastVertex.app Δ[n]).app _ ((stdSimplex.sdIso.inv.app ⦋n⦌).app _ s)) i =
      (SimplexCategory.lastVertexOrderHom ⦋n⦌ (s.obj i)).down := by
  have h := congrArg (fun f : SimplexCategory.sd.obj ⦋n⦌ ⟶ Δ[n] ↦
    f.app (op ⦋d⦌) s) (sdIso_inv_lastVertex.{u} ⦋n⦌)
  exact congrArg (fun t : Δ[n] _⦋d⦌ ↦ t i) h

/-- The iterated subdivision functor, with the newest subdivision applied last.
The recursion is exposed so its object types compute in iterated-map signatures. -/
@[expose] noncomputable def sdIter : ℕ → SSet.{u} ⥤ SSet.{u}
  | 0 => 𝟭 _
  | r + 1 => sdIter r ⋙ sd

@[simp]
lemma sdIter_zero : sdIter.{u} 0 = 𝟭 SSet := (rfl)

@[simp]
lemma sdIter_succ (r : ℕ) : sdIter.{u} (r + 1) = sdIter r ⋙ sd := (rfl)

/-- One iteration is Mathlib's subdivision functor. -/
lemma sdIter_one : sdIter.{u} 1 = sd := (rfl)

/-- The iterated last-vertex map, removing the newest subdivision first. -/
noncomputable def lastVertexIter : (r : ℕ) → sdIter.{u} r ⟶ 𝟭 SSet
  | 0 => 𝟙 _
  | r + 1 => whiskerLeft (sdIter r) lastVertex ≫
      (Functor.rightUnitor (sdIter r)).hom ≫ lastVertexIter r

@[simp]
lemma lastVertexIter_zero_app (X : SSet.{u}) : (lastVertexIter 0).app X = 𝟙 X := (rfl)

@[simp]
lemma lastVertexIter_succ_app (r : ℕ) (X : SSet.{u}) :
    (lastVertexIter (r + 1)).app X =
      lastVertex.app ((sdIter r).obj X) ≫ (lastVertexIter r).app X := by
  exact congrArg (fun f ↦ lastVertex.app ((sdIter r).obj X) ≫ f)
    (Category.id_comp ((lastVertexIter r).app X))

/-- One iteration of the last-vertex map is the original last-vertex map. -/
lemma lastVertexIter_one_app (X : SSet.{u}) : (lastVertexIter 1).app X = lastVertex.app X := by
  exact (lastVertexIter_succ_app 0 X).trans (Category.comp_id _)

namespace Subcomplex

/-- The last-vertex maps of a subcomplex and its ambient simplicial set form a
restriction square after any number of subdivisions. -/
lemma lastVertexIter_commSq {X : SSet.{u}} (A : X.Subcomplex) (r : ℕ) :
    CommSq ((sdIter r).map A.ι) ((lastVertexIter r).app A)
      ((lastVertexIter r).app X) A.ι :=
  ⟨(lastVertexIter r).naturality A.ι⟩

end Subcomplex

namespace stdSimplex

/-- A nonempty face, viewed as a vertex of the subdivision of a standard simplex. -/
noncomputable def sdVertex {n : ℕ}
    (s : NonemptyFiniteChains (ULift.{u} (Fin (n + 1)))) :
    (sd.obj Δ[n]) _⦋0⦌ :=
  (sdIso.inv.app ⦋n⦌).app _ (ComposableArrows.mk₀ s)

lemma sdVertex_def {n : ℕ} (s : NonemptyFiniteChains (ULift.{u} (Fin (n + 1)))) :
    sdVertex s = (sdIso.inv.app ⦋n⦌).app (op ⦋0⦌) (ComposableArrows.mk₀ s) := (rfl)

/-- The vertex corresponding to a face maps to its largest vertex. -/
@[simp]
lemma lastVertex_sdVertex {n : ℕ} (s : NonemptyFiniteChains (ULift.{u} (Fin (n + 1)))) :
    dsimp% (lastVertex.app Δ[n]).app _ (sdVertex s) =
      const n (SimplexCategory.lastVertexOrderHom ⦋n⦌ s).down (op ⦋0⦌) := by
  apply obj₀Equiv.injective
  exact lastVertex_stdSimplex_apply (ComposableArrows.mk₀ s) 0

/-- Original vertices are fixed by the last-vertex map, in every dimension. -/
lemma lastVertex_sdVertex_singleton {n : ℕ} (a : Fin (n + 1)) :
    dsimp% (lastVertex.app Δ[n]).app _
        (sdVertex ⟨{ULift.up a}, Finset.singleton_nonempty _, fun i j ↦ le_total i j⟩) =
      const n a (op ⦋0⦌) := by
  rw [lastVertex_sdVertex, SimplexCategory.lastVertexOrderHom_apply]
  simp

/-- The new vertex of the subdivided interval maps to the last endpoint. -/
lemma lastVertex_sdVertex_interval :
    (lastVertex.{u}.app Δ[1]).app _
        (sdVertex ⟨{ULift.up (0 : Fin 2), ULift.up 1}, Finset.insert_nonempty _ _,
          fun i j ↦ le_total i j⟩) = const 1 1 (op ⦋0⦌) := by
  rw [lastVertex_sdVertex, SimplexCategory.lastVertexOrderHom_apply]
  rfl

/-- Iterated last-vertex maps commute with the cofaces of standard simplices. -/
@[reassoc]
lemma lastVertexIter_δ (r n : ℕ) (i : Fin (n + 2)) :
    (sdIter r).map (stdSimplex.δ i) ≫ (lastVertexIter r).app Δ[n + 1] =
      (lastVertexIter r).app Δ[n] ≫ stdSimplex.δ i :=
  (lastVertexIter r).naturality (stdSimplex.δ i)

/-- Iterated last-vertex maps commute with the codegeneracies of standard simplices. -/
@[reassoc]
lemma lastVertexIter_σ (r n : ℕ) (i : Fin (n + 1)) :
    (sdIter r).map (stdSimplex.σ i) ≫ (lastVertexIter r).app Δ[n] =
      (lastVertexIter r).app Δ[n + 1] ≫ stdSimplex.σ i :=
  (lastVertexIter r).naturality (stdSimplex.σ i)

end stdSimplex

end SSet

namespace AbstractSimplicialComplex

/-- For a face on the lifted standard vertex set, the simplicial-set last-vertex map
agrees with the last-vertex map of the ordered abstract complex at its barycenter. -/
lemma lastVertex_sdVertex_eq_const_lastVertexMap {n : ℕ}
    (K : AbstractSimplicialComplex (ULift.{u} (Fin (n + 1))))
    (τ : TauCeti.SetLike.Face K) :
    (SSet.lastVertex.app Δ[n]).app _
        (SSet.stdSimplex.sdVertex ⟨τ.val, (K.isRelLowerSet_faces τ.property).1,
          fun i j ↦ le_total i j⟩) =
      SSet.stdSimplex.const n (lastVertexMap K (subdivisionBarycenter K τ)).down (op ⦋0⦌) := by
  rw [SSet.stdSimplex.lastVertex_sdVertex, lastVertexMap_subdivisionBarycenter]
  rfl

end AbstractSimplicialComplex
