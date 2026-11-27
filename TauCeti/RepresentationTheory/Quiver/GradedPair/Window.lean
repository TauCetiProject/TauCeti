/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Order.Interval.Basic
public import TauCeti.Combinatorics.Quiver.Embedding
public import TauCeti.Combinatorics.Quiver.Line
public import TauCeti.RepresentationTheory.Quiver.GradedPair.Basic
public import TauCeti.RepresentationTheory.Quiver.Representation.FiniteDimensional
import Mathlib.Algebra.DirectSum.Decomposition
import Mathlib.CategoryTheory.PathCategory.MorphismProperty

/-!
# Graded pairs on a finite interval and representations of a line quiver

Restricting a homogeneous operator of degree one or minus one to the consecutive graded pieces
of its carrier gives a representation of a linearly oriented type-A quiver. The vertices are
numbered in the direction of the operator, so the same line quiver models both directions. The
inverse assembles the vertex spaces and arrow maps into a graded operator with zero grades
outside the interval.

`GradedPair.InWindow.windowEquivalence` packages the two functors. Enlarging the window
adds zero vertex spaces and zero boundary arrows, and restriction back recovers the
original representation naturally in graded intertwiners.

## References

* H. Atobe, S. Kondo, S. Yasuda, *Local newforms for the general linear groups over a
  non-archimedean local field*, Forum of Mathematics, Pi 10 (2022), e24, §3.1.
-/

public noncomputable section

open CategoryTheory DirectSum
open scoped ModuleCat

namespace TauCeti

namespace StepDirection

/-- The vertices of the type-A quiver for the inclusive window `w`. -/
abbrev WindowVertex (w : NonemptyInterval ℤ) :=
  LineQuiver ((w.snd - w.fst).toNat + 1)

private abbrev vertexIndex {w : NonemptyInterval ℤ} (i : WindowVertex w) :
    Fin ((w.snd - w.fst).toNat + 1) :=
  (DoubledQuiver.OrientedQuiver.vertexEquiv _ _).symm i

/-- Number the degrees from the left for raising operators and from the right for lowering
operators, so an arrow always moves forward by one vertex. -/
def windowDegree (d : StepDirection) (w : NonemptyInterval ℤ) (i : WindowVertex w) : ℤ :=
  match d with
  | .up => w.fst + (vertexIndex i).val
  | .down => w.snd - (vertexIndex i).val

/-- For a raising operator, vertex indices are offsets from the lower endpoint. -/
@[simp]
theorem windowDegree_up_vertex (w : NonemptyInterval ℤ)
    (i : Fin ((w.snd - w.fst).toNat + 1)) :
    StepDirection.up.windowDegree w (DoubledQuiver.OrientedQuiver.vertex _ _ i) =
      w.fst + (i.val : ℤ) := by
  simp only [windowDegree, vertexIndex, DoubledQuiver.OrientedQuiver.vertexEquiv_symm_vertex]

/-- For a lowering operator, vertex indices are offsets from the upper endpoint. -/
@[simp]
theorem windowDegree_down_vertex (w : NonemptyInterval ℤ)
    (i : Fin ((w.snd - w.fst).toNat + 1)) :
    StepDirection.down.windowDegree w (DoubledQuiver.OrientedQuiver.vertex _ _ i) =
      w.snd - (i.val : ℤ) := by
  simp only [windowDegree, vertexIndex, DoubledQuiver.OrientedQuiver.vertexEquiv_symm_vertex]

/-- Each vertex of the line quiver is labelled by a degree in the window. -/
theorem windowDegree_mem (d : StepDirection) (w : NonemptyInterval ℤ) (i : WindowVertex w) :
    d.windowDegree w i ∈ w := by
  have hi := (vertexIndex i).isLt
  have hw := w.fst_le_snd
  rw [NonemptyInterval.mem_def]
  cases d <;> simp only [windowDegree] <;> omega

/-- Distinct vertices of the line quiver label distinct degrees. -/
theorem windowDegree_injective (d : StepDirection) (w : NonemptyInterval ℤ) :
    Function.Injective (d.windowDegree w) := by
  intro i j h
  apply (DoubledQuiver.OrientedQuiver.vertexEquiv _ _).symm.injective
  apply Fin.ext
  cases d <;> simp only [windowDegree, vertexIndex] at h <;> omega

/-- Every integer degree in the interval labels a vertex of the line quiver. -/
theorem mem_range_windowDegree_iff (d : StepDirection) (w : NonemptyInterval ℤ) {a : ℤ} :
    a ∈ Set.range (d.windowDegree w) ↔ a ∈ w := by
  refine ⟨fun ⟨i, hi⟩ ↦ hi ▸ d.windowDegree_mem w i, fun ha ↦ ?_⟩
  rw [NonemptyInterval.mem_def] at ha
  cases d with
  | up =>
    refine ⟨DoubledQuiver.OrientedQuiver.vertexEquiv _ _
      ⟨(a - w.fst).toNat, by omega⟩, ?_⟩
    simp only [windowDegree, vertexIndex, Equiv.symm_apply_apply]
    omega
  | down =>
    refine ⟨DoubledQuiver.OrientedQuiver.vertexEquiv _ _
      ⟨(w.snd - a).toNat, by omega⟩, ?_⟩
    simp only [windowDegree, vertexIndex, Equiv.symm_apply_apply]
    omega

/-- An arrow in the window moves by exactly the degree step of the operator. -/
theorem windowDegree_arrow (d : StepDirection) (w : NonemptyInterval ℤ)
    {i j : WindowVertex w} (e : i ⟶ j) :
    d.windowDegree w j = d.windowDegree w i + d.step := by
  have h : (vertexIndex i).val + 1 = (vertexIndex j).val := LineQuiver.index_add_one_eq e
  cases d <;> simp only [windowDegree, step_up, step_down] <;> omega

/-- Every consecutive pair of degrees in the direction of the operator has an arrow. -/
theorem nonempty_hom_iff_windowDegree_eq_add_step (d : StepDirection) (w : NonemptyInterval ℤ)
    (i j : WindowVertex w) :
    Nonempty (i ⟶ j) ↔ d.windowDegree w j = d.windowDegree w i + d.step := by
  rw [LineQuiver.nonempty_hom_iff]
  cases d <;> simp only [windowDegree, step_up, step_down, vertexIndex] <;> omega

end StepDirection

namespace GradedPair

/-- A coordinate graded pair with all its degrees in the closed interval `w`. -/
structure InWindow (w : NonemptyInterval ℤ) (d : StepDirection) where
  /-- The finite graded coordinate space. -/
  space : GradedCoordSpace
  /-- The homogeneous operator on the space. -/
  pair : GradedPair space d
  /-- Every basis coordinate has degree in the window. -/
  degree_mem (i : Fin space.n) : space.degree i ∈ w

namespace InWindow

variable {w : NonemptyInterval ℤ} {d : StepDirection}

/-- Morphisms of window pairs preserve every grade and intertwine the operators. -/
@[ext]
structure Hom (P Q : InWindow w d) where
  /-- The underlying complex linear map. -/
  toLinearMap : P.space.Carrier →ₗ[ℂ] Q.space.Carrier
  /-- The linear map preserves each grade. -/
  isHomogeneous : LinearMap.IsHomogeneous toLinearMap P.space.grade Q.space.grade 0
  /-- The linear map intertwines the operators. -/
  intertwines : ∀ x, toLinearMap (P.pair.operator x) = Q.pair.operator (toLinearMap x)

instance : Category (InWindow w d) where
  Hom := Hom
  id P := ⟨LinearMap.id, LinearMap.isHomogeneous_id _, fun _ ↦ rfl⟩
  comp f g := ⟨g.toLinearMap.comp f.toLinearMap,
    by simpa only [add_zero] using g.isHomogeneous.comp f.isHomogeneous,
    fun x ↦ by simp only [LinearMap.comp_apply, f.intertwines, g.intertwines]⟩
  id_comp f := Hom.ext (LinearMap.comp_id f.toLinearMap)
  comp_id f := Hom.ext (LinearMap.id_comp f.toLinearMap)
  assoc f g h := Hom.ext (LinearMap.comp_assoc _ _ _).symm

variable {P Q : InWindow w d}

@[simp]
theorem toLinearMap_id (P : InWindow w d) : ((𝟙 P) : Hom P P).toLinearMap = LinearMap.id :=
  (rfl)

@[simp]
theorem toLinearMap_comp {R : InWindow w d} (f : P ⟶ Q) (g : Q ⟶ R) :
    ((f ≫ g) : Hom P R).toLinearMap = g.toLinearMap.comp f.toLinearMap :=
  (rfl)

/-- Categorical isomorphisms of window pairs are exactly graded linear equivalences
intertwining their operators. -/
theorem nonempty_iso_iff (P Q : InWindow w d) :
    Nonempty (P ≅ Q) ↔ P.pair.Isomorphic Q.pair := by
  constructor
  · rintro ⟨i⟩
    let f := (i.hom : Hom P Q)
    let g := (i.inv : Hom Q P)
    have hfg : g.toLinearMap.comp f.toLinearMap = LinearMap.id :=
      congrArg Hom.toLinearMap i.hom_inv_id
    have hgf : f.toLinearMap.comp g.toLinearMap = LinearMap.id :=
      congrArg Hom.toLinearMap i.inv_hom_id
    apply GradedPairEquiv.isomorphic
    refine ⟨LinearEquiv.ofLinearMap f.toLinearMap g.toLinearMap hgf hfg, ?_, f.intertwines⟩
    intro a x
    constructor
    · intro hx
      simpa only [LinearEquiv.coe_ofLinearMap, add_zero] using f.isHomogeneous.map_mem hx
    · intro hx
      have hg := g.isHomogeneous.map_mem (p := a) hx
      rw [add_zero] at hg
      have hgfx : g.toLinearMap (f.toLinearMap x) = x := DFunLike.congr_fun hfg x
      exact hgfx ▸ hg
  · intro he
    obtain ⟨e⟩ := he.nonempty
    refine ⟨{ hom := ⟨e.toLinearEquiv.toLinearMap, LinearMap.isHomogeneous_def.2 ?_,
                    e.map_operator⟩
              inv := ⟨e.symm.toLinearEquiv.toLinearMap, LinearMap.isHomogeneous_def.2 ?_,
                    e.symm.map_operator⟩
              hom_inv_id := Hom.ext (LinearMap.ext e.symm_apply_apply)
              inv_hom_id := Hom.ext (LinearMap.ext e.apply_symm_apply) }⟩
    · intro a x hx
      rw [add_zero]
      exact (e.mem_grade_iff' a x).1 hx
    · intro a x hx
      rw [add_zero]
      exact (e.symm.mem_grade_iff' a x).1 hx

/-- Outside the window every graded piece vanishes. -/
@[simp]
theorem grade_eq_bot (P : InWindow w d) {a : ℤ} (ha : a ∉ w) : P.space.grade a = ⊥ :=
  (P.space.grade_eq_bot_iff a).2 fun i hi ↦ ha (hi ▸ P.degree_mem i)

/-- The arrow of a graded pair between two vertices of its window. -/
def arrowMap (P : InWindow w d) {i j : StepDirection.WindowVertex w} (e : i ⟶ j) :
    P.space.grade (d.windowDegree w i) →ₗ[ℂ] P.space.grade (d.windowDegree w j) :=
  P.pair.operator.restrict fun _ hx ↦ d.windowDegree_arrow w e ▸ P.pair.isHomogeneous.map_mem hx

@[simp]
theorem coe_arrowMap (P : InWindow w d) {i j : StepDirection.WindowVertex w} (e : i ⟶ j)
    (x : P.space.grade (d.windowDegree w i)) : (P.arrowMap e x : P.space.Carrier) =
      P.pair.operator x :=
  (rfl)

/-- Read the graded pieces and arrows of a window pair as a line-quiver representation. -/
@[expose]
def toRep (P : InWindow w d) : QuiverRep.{0, 0, 0, 0} ℂ (StepDirection.WindowVertex w) :=
  Paths.lift
    { obj := fun i ↦ ModuleCat.of ℂ (P.space.grade (d.windowDegree w i))
      map := fun e ↦ ModuleCat.ofHom (P.arrowMap e) }

@[simp]
theorem toRep_obj (P : InWindow w d) (i : Paths (StepDirection.WindowVertex w)) :
    P.toRep.obj i =
      ModuleCat.of ℂ (P.space.grade (d.windowDegree w i)) :=
  (rfl)

@[simp]
theorem toRep_map_arrow (P : InWindow w d) {i j : StepDirection.WindowVertex w} (e : i ⟶ j) :
    P.toRep.map e.toPath = ModuleCat.ofHom (P.arrowMap e) :=
  Paths.lift_toPath _ e

/-- Restrict a graded morphism to the vertex spaces of the window. -/
def toRepMap (f : P ⟶ Q) : P.toRep ⟶ Q.toRep :=
  Paths.liftNatTrans (fun i ↦ ModuleCat.ofHom (f.isHomogeneous.restrict (d.windowDegree w i)))
    (fun {i j} e ↦ by
      rw [toRep_map_arrow, toRep_map_arrow]
      apply ModuleCat.hom_ext
      -- Unbundle composition in the module category to use the ambient intertwining equation.
      change (f.isHomogeneous.restrict (d.windowDegree w j)).comp (P.arrowMap e) =
        (Q.arrowMap e).comp (f.isHomogeneous.restrict (d.windowDegree w i))
      exact LinearMap.ext fun x ↦ Subtype.ext (by simpa using f.intertwines x))

@[simp]
theorem toRepMap_app (f : P ⟶ Q) (i : Paths (StepDirection.WindowVertex w)) :
    (toRepMap f).app i =
      ModuleCat.ofHom (f.isHomogeneous.restrict (d.windowDegree w i)) :=
  (rfl)

/-- The full subcategory of the line-quiver representations with finite-dimensional vertex
spaces. -/
abbrev FiniteRep (w : NonemptyInterval ℤ) :=
  ObjectProperty.FullSubcategory (IsFinDim.{0, 0, 0, 0} ℂ (StepDirection.WindowVertex w))

/-- Restriction of a graded pair and its morphisms to the consecutive grades in the window.
The object projection reduces to `toRep`, so component morphisms can be typed on the grades. -/
@[expose, implicit_reducible]
def toRepFunctor (w : NonemptyInterval ℤ) (d : StepDirection) : InWindow w d ⥤ FiniteRep w where
  obj P := ⟨P.toRep, isFinDim_iff.2 fun i ↦
    inferInstanceAs (FiniteDimensional ℂ (P.space.grade (d.windowDegree w i)))⟩
  map f := ObjectProperty.homMk (toRepMap f)
  map_id P := by
    apply ObjectProperty.hom_ext
    apply NatTrans.ext
    funext i
    simp only [ObjectProperty.homMk_hom, ObjectProperty.FullSubcategory.id_hom, NatTrans.id_app,
      toRepMap_app]
    apply ModuleCat.hom_ext
    -- Identify the bundled identity with the linear identity on the grade.
    change ((𝟙 P : Hom P P).isHomogeneous.restrict (d.windowDegree w i)) = LinearMap.id
    exact LinearMap.IsHomogeneous.restrict_id _ _
  map_comp f g := by
    apply ObjectProperty.hom_ext
    apply NatTrans.ext
    funext i
    simp only [ObjectProperty.homMk_hom, ObjectProperty.FullSubcategory.comp_hom,
      NatTrans.comp_app, toRepMap_app]
    apply ModuleCat.hom_ext
    -- Unbundle the composite on the grade to apply the homogeneous restriction law.
    change (f ≫ g : Hom _ _).isHomogeneous.restrict (d.windowDegree w i) =
      (g.isHomogeneous.restrict _).comp (f.isHomogeneous.restrict _)
    exact LinearMap.IsHomogeneous.restrict_comp g.isHomogeneous f.isHomogeneous _
      (hcomp := (f ≫ g : Hom _ _).isHomogeneous)

/-- Forgetting finite dimensionality recovers the representation on the window grades. -/
@[simp]
theorem toRepFunctor_obj_obj (P : InWindow w d) :
    ((toRepFunctor w d).obj P).obj = P.toRep :=
  (rfl)

/-- The underlying representation morphism is the restriction to the window grades. -/
@[simp]
theorem toRepFunctor_map_hom (f : P ⟶ Q) :
    ((toRepFunctor w d).map f).hom = toRepMap f :=
  (rfl)

private theorem eq_zero_of_notMem (P : InWindow w d) {a : ℤ} (ha : a ∉ w)
    (x : P.space.grade a) : (x : P.space.Carrier) = 0 :=
  (Submodule.mem_bot ℂ).mp (P.grade_eq_bot ha ▸ x.property)

private theorem linearMap_ext_on_window {V : Type*} [AddCommMonoid V] [Module ℂ V]
    {f g : P.space.Carrier →ₗ[ℂ] V}
    (h : ∀ i : StepDirection.WindowVertex w, ∀ x : P.space.grade (d.windowDegree w i),
      f x = g x) : f = g := by
  let := P.space.isInternal_grade.chooseDecomposition
  apply decompose_lhom_ext P.space.grade
  intro a
  apply LinearMap.ext
  intro x
  by_cases ha : a ∈ w
  · obtain ⟨i, rfl⟩ := (d.mem_range_windowDegree_iff w).2 ha
    exact h i x
  · simp [P.eq_zero_of_notMem ha x]

private def assembleMap (f : ∀ a : ℤ, P.space.grade a →ₗ[ℂ] Q.space.grade a) :
    P.space.Carrier →ₗ[ℂ] Q.space.Carrier :=
  letI := P.space.isInternal_grade.chooseDecomposition
  (DirectSum.toModule ℂ ℤ Q.space.Carrier fun a ↦ (Q.space.grade a).subtype.comp (f a)).comp
    (decomposeLinearEquiv P.space.grade).toLinearMap

private theorem assembleMap_apply (f : ∀ a : ℤ, P.space.grade a →ₗ[ℂ] Q.space.grade a)
    (a : ℤ) (x : P.space.grade a) :
    assembleMap f x = (f a x : Q.space.Carrier) := by
  simp [assembleMap, decomposeLinearEquiv_apply_coe, DirectSum.toModule_lof]

open Classical in
private def repMapAt (f : P.toRep ⟶ Q.toRep) (a : ℤ) :
    P.space.grade a →ₗ[ℂ] Q.space.grade a :=
  if h : ∃ i, d.windowDegree w i = a then
    h.choose_spec ▸ (f.app (h.choose : Paths (StepDirection.WindowVertex w))).hom
  else 0

private theorem repMapAt_windowDegree (f : P.toRep ⟶ Q.toRep)
    (i : Paths (StepDirection.WindowVertex w)) :
    repMapAt f (d.windowDegree w i) = (f.app (i : Paths (StepDirection.WindowVertex w))).hom := by
  classical
  let h : ∃ j, d.windowDegree w j = d.windowDegree w i := ⟨i, rfl⟩
  rw [repMapAt, dite_eq_left h]
  have transport (j : StepDirection.WindowVertex w) (hj : d.windowDegree w j = d.windowDegree w i) :
      (hj ▸ (f.app (j : Paths (StepDirection.WindowVertex w))).hom :
          P.space.grade (d.windowDegree w i) →ₗ[ℂ] Q.space.grade (d.windowDegree w i)) =
        (f.app (i : Paths (StepDirection.WindowVertex w))).hom := by
    obtain rfl := d.windowDegree_injective w hj
    rfl
  exact transport h.choose h.choose_spec

private theorem repMapAt_arrow (f : P.toRep ⟶ Q.toRep)
    {i j : StepDirection.WindowVertex w} (e : i ⟶ j)
    (x : P.space.grade (d.windowDegree w i)) :
    repMapAt f (d.windowDegree w j) (P.arrowMap e x) =
      Q.arrowMap e (repMapAt f (d.windowDegree w i) x) := by
  have h := f.naturality e.toPath
  rw [P.toRep_map_arrow, Q.toRep_map_arrow] at h
  rw [repMapAt_windowDegree f (j : Paths _), repMapAt_windowDegree f (i : Paths _)]
  exact DFunLike.congr_fun (congrArg ModuleCat.Hom.hom h) x

/-- Assemble a representation morphism between the restrictions into an intertwiner of pairs. -/
def ofRepMap (f : P.toRep ⟶ Q.toRep) : Hom P Q where
  toLinearMap := assembleMap (repMapAt f)
  isHomogeneous := LinearMap.isHomogeneous_def.2 (by
    intro a x hx
    rw [add_zero, assembleMap_apply _ a ⟨x, hx⟩]
    exact (repMapAt f a ⟨x, hx⟩).property)
  intertwines := by
    suffices (assembleMap (repMapAt f)).comp P.pair.operator =
        Q.pair.operator.comp (assembleMap (repMapAt f)) from DFunLike.congr_fun this
    apply linearMap_ext_on_window
    intro i x
    simp only [LinearMap.comp_apply]
    by_cases hj : d.windowDegree w i + d.step ∈ w
    · obtain ⟨j, hj⟩ := (d.mem_range_windowDegree_iff w).2 hj
      obtain ⟨e⟩ := (d.nonempty_hom_iff_windowDegree_eq_add_step w i j).2 hj
      rw [← P.coe_arrowMap e x, assembleMap_apply, assembleMap_apply,
        repMapAt_arrow f e, Q.coe_arrowMap]
    · have hp := P.eq_zero_of_notMem hj ⟨P.pair.operator x, P.pair.isHomogeneous.map_mem x.property⟩
      have hq := Q.eq_zero_of_notMem hj
        ⟨Q.pair.operator (repMapAt f _ x), Q.pair.isHomogeneous.map_mem (repMapAt f _ x).property⟩
      calc
        _ = 0 := (congrArg (assembleMap (repMapAt f)) hp).trans (map_zero _)
        _ = _ := ((congrArg Q.pair.operator (assembleMap_apply (repMapAt f) _ x)).trans hq).symm

@[simp]
theorem ofRepMap_apply (f : P.toRep ⟶ Q.toRep) (i : Paths (StepDirection.WindowVertex w))
    (x : P.space.grade (d.windowDegree w i)) :
    (ofRepMap f).toLinearMap x =
      ((f.app i).hom x : Q.space.grade (d.windowDegree w i)).val := by
  rw [ofRepMap, assembleMap_apply]
  exact congrArg (fun g : P.space.grade (d.windowDegree w i) →ₗ[ℂ]
    Q.space.grade (d.windowDegree w i) ↦ (g x).val) (repMapAt_windowDegree f i)

/-- Restricting an assembled intertwiner recovers the original representation morphism. -/
@[simp]
theorem toRepMap_ofRepMap (f : P.toRep ⟶ Q.toRep) : toRepMap (ofRepMap f) = f := by
  apply NatTrans.ext
  funext i
  rw [toRepMap_app]
  apply ModuleCat.hom_ext
  -- Express the two bundled maps on the same grade before comparing their ambient values.
  change (ofRepMap f).isHomogeneous.restrict (d.windowDegree w i) = (f.app i).hom
  exact LinearMap.ext fun x ↦ Subtype.ext
    ((LinearMap.IsHomogeneous.coe_restrict_apply _ _ x).trans (ofRepMap_apply f i x))

/-- Assembling the restrictions of an intertwiner recovers the original graded morphism. -/
@[simp]
theorem ofRepMap_toRepMap (f : P ⟶ Q) : ofRepMap (toRepMap f) = f := by
  apply Hom.ext
  apply linearMap_ext_on_window
  intro i x
  exact (ofRepMap_apply (toRepMap f) i x).trans (by
    rw [toRepMap_app f (i : Paths _)]
    exact LinearMap.IsHomogeneous.coe_restrict_apply _ _ x)

/-- The window restriction functor is fully faithful. Every grade-preserving intertwiner can be
recovered uniquely from its maps on the window grades. -/
def fullyFaithfulToRepFunctor (w : NonemptyInterval ℤ) (d : StepDirection) :
    (toRepFunctor w d).FullyFaithful where
  preimage f := ofRepMap f.hom
  map_preimage f := ObjectProperty.hom_ext _ (toRepMap_ofRepMap f.hom)
  preimage_map f := ofRepMap_toRepMap f

section Extension

open StepDirection

private abbrev vertexSpace (M : FiniteRep w) (i : WindowVertex w) :=
  M.obj.obj (i : Paths (WindowVertex w))

private abbrev coordinates (M : FiniteRep w) :=
  Σ i : WindowVertex w, Fin (Module.finrank ℂ (vertexSpace M i))

private def coordinateIndex (M : FiniteRep w) :=
  Finite.equivFin (coordinates M)

private def repSpace (d : StepDirection) (M : FiniteRep w) : GradedCoordSpace :=
  ⟨_, fun k ↦ d.windowDegree w ((coordinateIndex M).symm k).1⟩

private def vertexBasis (M : FiniteRep w) (i : WindowVertex w) :
    Module.Basis (Fin (Module.finrank ℂ (vertexSpace M i))) ℂ (vertexSpace M i) :=
  letI := isFinDim_iff.1 M.property (i : Paths (WindowVertex w))
  Module.finBasis ℂ (vertexSpace M i)

private def coordinateEquiv (d : StepDirection) (M : FiniteRep w) :
    (∀ i, vertexSpace M i) ≃ₗ[ℂ] (repSpace d M).Carrier :=
  (LinearEquiv.piCongrRight fun i ↦ (vertexBasis M i).equivFun).trans
    ((LinearEquiv.piCurry ℂ (fun (i : WindowVertex w)
      (_ : Fin (Module.finrank ℂ (vertexSpace M i))) ↦ ℂ)).symm.trans
        (LinearEquiv.funCongrLeft ℂ ℂ (coordinateIndex M).symm))

private theorem coordinateEquiv_apply (M : FiniteRep w) (x : ∀ i, vertexSpace M i)
    (i : WindowVertex w) (k : Fin (Module.finrank ℂ (vertexSpace M i))) :
    coordinateEquiv d M x (coordinateIndex M ⟨i, k⟩) =
      (vertexBasis M i).equivFun (x i) k := by
  rw [coordinateEquiv, LinearEquiv.trans_apply, LinearEquiv.trans_apply]
  exact (congrFun (LinearEquiv.funCongrLeft_apply ℂ ℂ (coordinateIndex M).symm _)
    (coordinateIndex M ⟨i, k⟩)).trans (by
      rw [LinearMap.funLeft_apply, Equiv.symm_apply_apply, LinearEquiv.piCurry_symm_apply]
      rfl)

private theorem coordinateEquiv_mem_grade_iff (M : FiniteRep w)
    (x : ∀ i, vertexSpace M i) (a : ℤ) :
    coordinateEquiv d M x ∈ (repSpace d M).grade a ↔
      ∀ i, d.windowDegree w i ≠ a → x i = 0 := by
  rw [GradedCoordSpace.mem_grade_iff]
  constructor
  · intro hx i hi
    apply (vertexBasis M i).equivFun.injective
    ext k
    rw [map_zero, Pi.zero_apply, ← coordinateEquiv_apply (d := d)]
    apply hx
    simpa [repSpace] using hi
  · intro hx k hk
    obtain ⟨⟨i, j⟩, rfl⟩ := (coordinateIndex M).surjective k
    rw [coordinateEquiv_apply, hx i, map_zero, Pi.zero_apply]
    simpa [repSpace] using hk

open Classical in
private def repOperator (M : FiniteRep w) : Module.End ℂ (∀ i, vertexSpace M i) :=
  LinearMap.pi fun j ↦
    if h : ∃ i, Nonempty (i ⟶ j) then
      (M.obj.map h.choose_spec.some.toPath).hom.comp (LinearMap.proj h.choose)
    else 0

private theorem repOperator_apply_of_arrow (M : FiniteRep w) {i j : WindowVertex w}
    (e : i ⟶ j) (x : ∀ i, vertexSpace M i) :
    repOperator M x j = (M.obj.map e.toPath).hom (x i) := by
  classical
  rw [repOperator, LinearMap.pi_apply, dite_eq_left ⟨i, ⟨e⟩⟩]
  have same (i' : WindowVertex w) (e' : i' ⟶ j) :
      (M.obj.map e'.toPath).hom (x i') = (M.obj.map e.toPath).hom (x i) := by
    have h := (StepDirection.up.windowDegree_arrow w e').symm.trans
      (StepDirection.up.windowDegree_arrow w e)
    obtain rfl := StepDirection.up.windowDegree_injective w (add_right_cancel h)
    rw [Subsingleton.elim e' e]
  exact same _ _

private theorem repOperator_apply_of_no_arrow (M : FiniteRep w) (j : WindowVertex w)
    (h : ¬ ∃ i, Nonempty (i ⟶ j)) (x : ∀ i, vertexSpace M i) : repOperator M x j = 0 := by
  classical
  rw [repOperator, LinearMap.pi_apply, dite_eq_right h, LinearMap.zero_apply]

private theorem repOperator_mem_grade (M : FiniteRep w) (a : ℤ) (x : ∀ i, vertexSpace M i)
    (hx : coordinateEquiv d M x ∈ (repSpace d M).grade a) :
    coordinateEquiv d M (repOperator M x) ∈ (repSpace d M).grade (a + d.step) := by
  rw [coordinateEquiv_mem_grade_iff] at hx ⊢
  intro j hj
  by_cases h : ∃ i, Nonempty (i ⟶ j)
  · obtain ⟨i, ⟨e⟩⟩ := h
    have hi : d.windowDegree w i ≠ a := fun hi ↦ hj ((d.windowDegree_arrow w e).trans
      (congrArg (· + d.step) hi))
    rw [repOperator_apply_of_arrow M e, hx i hi, map_zero]
  · exact repOperator_apply_of_no_arrow M j h x

/-- Assemble a pointwise finite-dimensional representation into a graded pair supported in the
window. The operator is the sum of the arrow maps and kills the terminal vertex space. -/
def ofRep (d : StepDirection) (M : FiniteRep w) : InWindow w d where
  space := repSpace d M
  pair :=
    { operator := (coordinateEquiv d M).conj (repOperator M)
      isHomogeneous := LinearMap.isHomogeneous_def.2 (by
        intro a v hv
        rw [LinearEquiv.conj_apply_apply]
        exact repOperator_mem_grade (d := d) M a ((coordinateEquiv d M).symm v)
          (by simpa using hv)) }
  degree_mem k := d.windowDegree_mem w ((coordinateIndex M).symm k).1

private theorem ofRep_operator (M : FiniteRep w) (x : ∀ i, vertexSpace M i) :
    (ofRep d M).pair.operator (coordinateEquiv d M x) =
      coordinateEquiv d M (repOperator M x) := by
  exact (LinearEquiv.conj_apply_apply (coordinateEquiv d M) (repOperator M) _).trans
    (congrArg (fun u ↦ coordinateEquiv d M (repOperator M u))
      ((coordinateEquiv d M).symm_apply_apply x))

open Classical in
/-- The vertex space of a representation is linearly equivalent to the corresponding graded
piece of its assembled pair. -/
def ofRepGradeEquiv (d : StepDirection) (M : FiniteRep w) (i : WindowVertex w) :
    M.obj.obj (i : Paths (WindowVertex w)) ≃ₗ[ℂ]
      (ofRep d M).space.grade (d.windowDegree w i) where
  toFun x :=
    ⟨coordinateEquiv d M (Pi.single i x), (coordinateEquiv_mem_grade_iff _ _ _).2
      fun j hj ↦ by
        have hji : j ≠ i := fun h ↦ hj (congrArg (d.windowDegree w) h)
        rw [Pi.single_eq_of_ne hji]⟩
  invFun y := (coordinateEquiv d M).symm y.val i
  left_inv x := by simp
  right_inv y := by
    apply Subtype.ext
    apply (coordinateEquiv d M).symm.injective
    simp only [LinearEquiv.symm_apply_apply]
    funext j
    by_cases hj : j = i
    · subst j
      simp
    · have hy : y.val ∈ (repSpace d M).grade (d.windowDegree w i) := y.property
      let E := coordinateEquiv d M
      have h := (coordinateEquiv_mem_grade_iff (d := d) M (E.symm y.val) (d.windowDegree w i)).1
        ((E.apply_symm_apply (y.val : (repSpace d M).Carrier)).symm ▸ hy)
      rw [Pi.single_eq_of_ne hj, h j (fun e ↦ hj (d.windowDegree_injective w e))]
  map_add' x y := by
    apply Subtype.ext
    simp only [Submodule.coe_add, Pi.single_add, map_add]
    rfl
  map_smul' c x := by
    apply Subtype.ext
    simp only [Submodule.coe_smul, Pi.single_smul, map_smul, RingHom.id_apply]
    rfl

private theorem coe_ofRepGradeEquiv (M : FiniteRep w) (i : WindowVertex w)
    (x : M.obj.obj (i : Paths (WindowVertex w))) :
    (ofRepGradeEquiv d M i x).val = coordinateEquiv d M (Pi.single i x) :=
  rfl

private theorem repOperator_single (M : FiniteRep w) {i j : WindowVertex w}
    (e : i ⟶ j) (x : vertexSpace M i) :
    repOperator M (Pi.single i x) = Pi.single j ((M.obj.map e.toPath).hom x) := by
  classical
  funext k
  by_cases hk : k = j
  · subst k
    simp [repOperator_apply_of_arrow M e]
  · rw [Pi.single_eq_of_ne hk]
    by_cases h : ∃ l, Nonempty (l ⟶ k)
    · obtain ⟨l, ⟨f⟩⟩ := h
      have hi : l ≠ i := by
        rintro rfl
        exact hk (StepDirection.up.windowDegree_injective w
          ((StepDirection.up.windowDegree_arrow w f).trans
            (StepDirection.up.windowDegree_arrow w e).symm))
      rw [repOperator_apply_of_arrow M f, Pi.single_eq_of_ne hi, map_zero]
    · exact repOperator_apply_of_no_arrow M k h _

/-- The comparison with the assembled pair intertwines each arrow with the operator on its
source grade. -/
theorem ofRepGradeEquiv_arrow (M : FiniteRep w) {i j : WindowVertex w}
    (e : i ⟶ j) (x : M.obj.obj (i : Paths (WindowVertex w))) :
    (ofRep d M).arrowMap e (ofRepGradeEquiv d M i x) =
      ofRepGradeEquiv d M j ((M.obj.map e.toPath).hom x) := by
  apply Subtype.ext
  rw [coe_arrowMap, coe_ofRepGradeEquiv, ofRep_operator, repOperator_single M e,
    coe_ofRepGradeEquiv]

/-- Restricting the assembled graded pair recovers the original representation, by the
equivalences on its vertex spaces. -/
def ofRepIso (d : StepDirection) (M : FiniteRep w) :
    M ≅ (toRepFunctor w d).obj (ofRep d M) :=
  ObjectProperty.isoMk _ <| Paths.liftNatIso (F := M.obj) (G := (ofRep d M).toRep)
    (fun i ↦ (ofRepGradeEquiv d M i).toModuleIso) (fun {i j} e ↦ by
      rw [toRep_map_arrow]
      exact ModuleCat.hom_ext (LinearMap.ext fun x ↦ (ofRepGradeEquiv_arrow (d := d) M e x).symm))

/-- The forward component of the assembly isomorphism identifies a vertex space with its grade. -/
@[simp]
theorem ofRepIso_hom_app (M : FiniteRep w) (i : Paths (WindowVertex w)) :
    (ofRepIso d M).hom.hom.app i = (ofRepGradeEquiv d M i).toModuleIso.hom :=
  (rfl)

/-- The inverse component of the assembly isomorphism recovers the original vertex space. -/
@[simp]
theorem ofRepIso_inv_app (M : FiniteRep w) (i : Paths (WindowVertex w)) :
    (ofRepIso d M).inv.hom.app i = (ofRepGradeEquiv d M i).toModuleIso.inv :=
  (rfl)

end Extension

/-- Extend by zero outside the window and assemble the arrow maps. On morphisms, assemble
the component maps using the canonical isomorphisms on vertex spaces. The object projection
reduces to `ofRep`, so the map acts directly on the carrier of the assembled pair. -/
@[expose]
def ofRepFunctor (w : NonemptyInterval ℤ) (d : StepDirection) : FiniteRep w ⥤ InWindow w d where
  obj := ofRep d
  map {M N} f := (fullyFaithfulToRepFunctor w d).preimage
    ((ofRepIso d M).inv ≫ f ≫ (ofRepIso d N).hom)
  map_id M := by simp
  map_comp f g := by
    rw [← (fullyFaithfulToRepFunctor w d).preimage_comp]
    congr 1
    simp

/-- The object of the assembly functor is the assembled graded pair. -/
@[simp]
theorem ofRepFunctor_obj (M : FiniteRep w) : (ofRepFunctor w d).obj M = ofRep d M :=
  (rfl)

/-- On each assembled grade, the assembly functor acts by the original vertex map. -/
@[simp]
theorem ofRepFunctor_map_apply {M N : FiniteRep w} (f : M ⟶ N)
    (i : Paths (StepDirection.WindowVertex w)) (x : M.obj.obj i) :
    ((ofRepFunctor w d).map f).toLinearMap (ofRepGradeEquiv d M i x).val =
      (ofRepGradeEquiv d N i ((f.hom.app i).hom x)).val := by
  let g := (ofRepIso d M).inv ≫ f ≫ (ofRepIso d N).hom
  calc
    _ = ((g.hom.app i).hom (ofRepGradeEquiv d M i x)).val := ofRepMap_apply g.hom i _
    -- Composition of representation morphisms is pointwise on the vertex spaces.
    _ = (((ofRepIso d N).hom.hom.app i).hom
          ((f.hom.app i).hom (((ofRepIso d M).inv.hom.app i).hom
            (ofRepGradeEquiv d M i x)))).val := rfl
    _ = _ := by
      simp only [ofRepIso_hom_app, ofRepIso_inv_app]
      exact congrArg (fun y ↦ (ofRepGradeEquiv d N i ((f.hom.app i).hom y)).val)
        ((ofRepGradeEquiv d M i).symm_apply_apply x)

/-- Restricting to the window grades is an equivalence between coordinate graded pairs
supported in that window and pointwise finite-dimensional type-A representations. -/
def windowEquivalence (w : NonemptyInterval ℤ) (d : StepDirection) :
    InWindow w d ≌ FiniteRep w :=
  let ff := fullyFaithfulToRepFunctor w d
  CategoryTheory.Equivalence.mk (toRepFunctor w d) (ofRepFunctor w d)
    (NatIso.ofComponents (fun P ↦ ff.preimageIso (ofRepIso d ((toRepFunctor w d).obj P)))
      (fun f ↦ ff.map_injective (by simp [ofRepFunctor, ff])))
    (NatIso.ofComponents (fun M ↦ (ofRepIso d M).symm)
      (fun f ↦ by simp [ofRepFunctor]))

@[simp]
theorem windowEquivalence_functor (w : NonemptyInterval ℤ) (d : StepDirection) :
    (windowEquivalence w d).functor = toRepFunctor w d :=
  (rfl)

@[simp]
theorem windowEquivalence_inverse (w : NonemptyInterval ℤ) (d : StepDirection) :
    (windowEquivalence w d).inverse = ofRepFunctor w d :=
  (rfl)

-- The transports use the projection lemmas so the equations apply with the equivalence opaque.
/-- The counit recovers the original representation by inverting the assembly isomorphism. -/
@[simp]
theorem windowEquivalence_counitIso_hom_app (M : FiniteRep w) :
    (windowEquivalence w d).counitIso.hom.app M =
      eqToHom (by simp) ≫ (ofRepIso d M).inv := by
  erw [eqToHom_refl, Category.id_comp]
  rfl

/-- The inverse counit is the assembly isomorphism. -/
@[simp]
theorem windowEquivalence_counitIso_inv_app (M : FiniteRep w) :
    (windowEquivalence w d).counitIso.inv.app M =
      (ofRepIso d M).hom ≫ eqToHom (by simp) := by
  erw [eqToHom_refl, Category.comp_id]
  rfl

/-- The unit assembles the vertex maps of the assembly isomorphism for the restricted pair. -/
@[simp]
theorem windowEquivalence_unitIso_hom_app (P : InWindow w d) :
    (windowEquivalence w d).unitIso.hom.app P =
      ofRepMap (ofRepIso d ((toRepFunctor w d).obj P)).hom.hom ≫ eqToHom (by simp) := by
  erw [eqToHom_refl, Category.comp_id]
  let ff := fullyFaithfulToRepFunctor w d
  let e := windowEquivalence w d
  let i := ofRepIso d ((toRepFunctor w d).obj P)
  apply ff.map_injective
  exact (e.counitInv_app_functor P).symm.trans (ff.map_preimage i.hom).symm

/-- The inverse unit assembles the inverse vertex maps for the restricted pair. -/
@[simp]
theorem windowEquivalence_unitIso_inv_app (P : InWindow w d) :
    (windowEquivalence w d).unitIso.inv.app P =
      eqToHom (by simp) ≫ ofRepMap (ofRepIso d ((toRepFunctor w d).obj P)).inv.hom := by
  erw [eqToHom_refl, Category.id_comp]
  let ff := fullyFaithfulToRepFunctor w d
  let e := windowEquivalence w d
  let i := ofRepIso d ((toRepFunctor w d).obj P)
  apply ff.map_injective
  exact (e.counit_app_functor P).symm.trans (ff.map_preimage i.inv).symm

section Enlargement

open StepDirection

variable {W : NonemptyInterval ℤ}

/-- Include a window into a larger window by matching the integer degrees of its vertices and
sending each arrow to the corresponding consecutive-degree arrow. -/
@[implicit_reducible]
def windowEmbedding (d : StepDirection) (h : w ≤ W) :
    QuiverEmbedding (WindowVertex w) (WindowVertex W) :=
  let atDegree (i : WindowVertex w) := ((d.mem_range_windowDegree_iff W).2
    (NonemptyInterval.coe_subset_coe.mpr h (d.windowDegree_mem w i))).choose
  have atDegree_eq (i : WindowVertex w) : d.windowDegree W (atDegree i) = d.windowDegree w i :=
    ((d.mem_range_windowDegree_iff W).2
      (NonemptyInterval.coe_subset_coe.mpr h (d.windowDegree_mem w i))).choose_spec
  { obj := atDegree
    map := fun {i j} e ↦
      ((d.nonempty_hom_iff_windowDegree_eq_add_step W (atDegree i) (atDegree j)).2 (by
        rw [atDegree_eq i, atDegree_eq j]
        exact d.windowDegree_arrow w e)).some
    obj_injective := fun {i j} hij ↦ d.windowDegree_injective w <|
      (atDegree_eq i).symm.trans ((congrArg (d.windowDegree W) hij).trans (atDegree_eq j))
    map_injective := fun _ ↦ Subsingleton.elim _ _ }

@[simp]
theorem windowDegree_windowEmbedding_obj (d : StepDirection) (h : w ≤ W) (i : WindowVertex w) :
    d.windowDegree W ((windowEmbedding d h).obj i) = d.windowDegree w i := by
  exact ((d.mem_range_windowDegree_iff W).2
    (NonemptyInterval.coe_subset_coe.mpr h (d.windowDegree_mem w i))).choose_spec

/-- Include a graded pair supported in a smaller window into the category for the larger window.
The carrier is definitionally the same, so operators and intertwiners act on the original
coordinate spaces. -/
@[expose, implicit_reducible]
def enlargeFunctor (d : StepDirection) (h : w ≤ W) : InWindow w d ⥤ InWindow W d where
  obj P := ⟨P.space, P.pair, fun i ↦ NonemptyInterval.coe_subset_coe.mpr h (P.degree_mem i)⟩
  map f := ⟨f.toLinearMap, f.isHomogeneous, f.intertwines⟩
  map_id _ := Hom.ext rfl
  map_comp _ _ := Hom.ext rfl

/-- Enlarging the window preserves the graded coordinate space. -/
@[simp]
theorem enlargeFunctor_obj_space (h : w ≤ W) (P : InWindow w d) :
    ((enlargeFunctor d h).obj P).space = P.space :=
  (rfl)

/-- Enlarging the window preserves the homogeneous operator. -/
@[simp]
theorem enlargeFunctor_obj_pair_operator (h : w ≤ W) (P : InWindow w d) :
    ((enlargeFunctor d h).obj P).pair.operator = P.pair.operator :=
  (rfl)

/-- The enlargement of a morphism has the same underlying linear map. -/
@[simp]
theorem enlargeFunctor_map_toLinearMap (h : w ≤ W) (f : P ⟶ Q) :
    ((enlargeFunctor d h).map f).toLinearMap = f.toLinearMap :=
  (rfl)

/-- The new vertices of an enlarged window have zero space. -/
@[simp]
theorem enlargeFunctor_grade_eq_bot (h : w ≤ W) (P : InWindow w d) (j : WindowVertex W)
    (hj : d.windowDegree W j ∉ w) :
    ((enlargeFunctor d h).obj P).space.grade (d.windowDegree W j) = ⊥ :=
  P.grade_eq_bot hj

/-- An arrow incident to a newly added vertex is a zero map. -/
@[simp]
theorem enlargeFunctor_arrowMap_eq_zero (h : w ≤ W) (P : InWindow w d) {i j : WindowVertex W}
    (e : i ⟶ j) (he : d.windowDegree W i ∉ w ∨ d.windowDegree W j ∉ w) :
    ((enlargeFunctor d h).obj P).arrowMap e = 0 := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  rcases he with hi | hj
  · have hx : (x.val : P.space.Carrier) = 0 := P.eq_zero_of_notMem hi x
    rw [coe_arrowMap, hx, map_zero]
    rfl
  · exact P.eq_zero_of_notMem hj (((enlargeFunctor d h).obj P).arrowMap e x)

/-- Restrict representations along the inclusion of a smaller window. The vertex spaces reduce
to the original spaces at the included vertices, so the component maps have the original types. -/
@[expose, implicit_reducible]
def restrictRepFunctor (d : StepDirection) (h : w ≤ W) : FiniteRep W ⥤ FiniteRep w :=
  let F := Paths.lift ((windowEmbedding d h).toPrefunctor ⋙q Paths.of (WindowVertex W))
  let G := (Functor.whiskeringLeft (Paths (WindowVertex w)) (Paths (WindowVertex W))
    (ModuleCat ℂ)).obj F
  ObjectProperty.lift _ (ObjectProperty.ι (IsFinDim ℂ (WindowVertex W)) ⋙ G)
    (fun M ↦ isFinDim_iff.2 fun i ↦ isFinDim_iff.1 M.property (F.obj i))

/-- A vertex of the restriction has the space of its image in the larger window. -/
@[simp]
theorem restrictRepFunctor_obj_obj_obj (d : StepDirection) (h : w ≤ W) (M : FiniteRep W)
    (i : Paths (WindowVertex w)) :
    ((restrictRepFunctor d h).obj M).obj.obj i = M.obj.obj ((windowEmbedding d h).obj i) :=
  (rfl)

/-- The restriction sends an arrow to the map of its image in the larger window. -/
@[simp]
theorem restrictRepFunctor_obj_obj_map_arrow (d : StepDirection) (h : w ≤ W) (M : FiniteRep W)
    {i j : WindowVertex w} (e : i ⟶ j) :
    ((restrictRepFunctor d h).obj M).obj.map e.toPath =
      M.obj.map ((windowEmbedding d h).map e).toPath :=
  congrArg (fun p ↦ M.obj.map p)
    (Paths.lift_toPath ((windowEmbedding d h).toPrefunctor ⋙q Paths.of (WindowVertex W)) e)

/-- A restricted morphism acts by the original component at the image vertex. -/
@[simp]
theorem restrictRepFunctor_map_hom_app (d : StepDirection) (h : w ≤ W) {M N : FiniteRep W}
    (f : M ⟶ N) (i : Paths (WindowVertex w)) :
    ((restrictRepFunctor d h).map f).hom.app i = f.hom.app ((windowEmbedding d h).obj i) :=
  (rfl)

private def gradeIso (S : GradedCoordSpace) {a b : ℤ} (hab : a = b) :
    ModuleCat.of ℂ (S.grade a) ≅ ModuleCat.of ℂ (S.grade b) :=
  eqToIso (congrArg (fun c ↦ ModuleCat.of ℂ (S.grade c)) hab)

private theorem coe_gradeIso_hom (S : GradedCoordSpace) {a b : ℤ} (hab : a = b)
    (x : S.grade a) :
    ((gradeIso S hab).hom.hom x : S.Carrier) = x := by
  subst b
  rfl

private def enlargeRestrictRepIso (h : w ≤ W) (P : InWindow w d) :
    ((restrictRepFunctor d h).obj ((toRepFunctor W d).obj ((enlargeFunctor d h).obj P))).obj ≅
      P.toRep :=
  Paths.liftNatIso (fun i ↦ gradeIso P.space (windowDegree_windowEmbedding_obj d h i))
    (fun {i j} e ↦ by
      simp only [restrictRepFunctor_obj_obj_map_arrow, toRep_map_arrow]
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      apply Subtype.ext
      let X := (enlargeFunctor d h).obj P
      let e' := (windowEmbedding d h).map e
      let x' : X.space.grade (d.windowDegree W ((windowEmbedding d h).obj i)) := x
      let hi := windowDegree_windowEmbedding_obj d h i
      let hj := windowDegree_windowEmbedding_obj d h j
      calc
        _ = (X.arrowMap e' x').val := coe_gradeIso_hom P.space hj _
        _ = P.pair.operator x'.val := X.coe_arrowMap e' x'
        _ = P.pair.operator ((gradeIso P.space hi).hom.hom x').val :=
          (congrArg P.pair.operator (coe_gradeIso_hom P.space hi x')).symm
        _ = _ := (P.coe_arrowMap e _).symm)

/-- Enlarging a pair and then restricting its representation back to the smaller window
recovers the original representation naturally in graded intertwiners. -/
def enlargeRestrictIso (d : StepDirection) (h : w ≤ W) :
    enlargeFunctor d h ⋙ toRepFunctor W d ⋙ restrictRepFunctor d h ≅ toRepFunctor w d :=
  NatIso.ofComponents (fun P ↦ ObjectProperty.isoMk _ (enlargeRestrictRepIso h P))
    (fun {P Q} f ↦ by
      apply ObjectProperty.hom_ext
      apply NatTrans.ext
      funext i
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      apply Subtype.ext
      let j : WindowVertex w := i
      let a := d.windowDegree W ((windowEmbedding d h).obj j)
      let b := d.windowDegree w j
      let x' : P.space.grade a := x
      let hi : a = b := windowDegree_windowEmbedding_obj d h j
      calc
        _ = ((f.isHomogeneous.restrict a) x').val := coe_gradeIso_hom Q.space hi _
        _ = f.toLinearMap x'.val := f.isHomogeneous.coe_restrict_apply a x'
        _ = f.toLinearMap ((gradeIso P.space hi).hom.hom x').val :=
          (congrArg f.toLinearMap (coe_gradeIso_hom P.space hi x')).symm
        _ = _ := (f.isHomogeneous.coe_restrict_apply b _).symm)

-- Simplify these applications before `Functor.comp_obj` rewrites the dependent object arguments.
/-- The forward comparison preserves the underlying vector at each vertex of the smaller window. -/
@[simp↓]
theorem coe_enlargeRestrictIso_hom_app (h : w ≤ W) (P : InWindow w d)
    (i : Paths (WindowVertex w))
    (x : P.space.grade (d.windowDegree W ((windowEmbedding d h).obj i))) :
    (((((enlargeRestrictIso d h).hom.app P).hom.app i).hom x).val : P.space.Carrier) = x.val :=
  coe_gradeIso_hom P.space (windowDegree_windowEmbedding_obj d h i) x

/-- The inverse comparison preserves the underlying vector at each vertex of the smaller window. -/
@[simp↓]
theorem coe_enlargeRestrictIso_inv_app (h : w ≤ W) (P : InWindow w d)
    (i : Paths (WindowVertex w)) (x : P.space.grade (d.windowDegree w i)) :
    (((((enlargeRestrictIso d h).inv.app P).hom.app i).hom x).val : P.space.Carrier) = x.val :=
  coe_gradeIso_hom P.space (windowDegree_windowEmbedding_obj d h i).symm x

end Enlargement

end InWindow
end GradedPair
end TauCeti
