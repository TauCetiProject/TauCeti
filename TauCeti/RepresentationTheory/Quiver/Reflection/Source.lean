/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Quiver.Reflection.Representation
import Mathlib.CategoryTheory.PathCategory.MorphismProperty

/-!
# Reflecting a representation at a source

This file constructs the source-side Bernstein--Gelfand--Ponomarev reflection functor. For a
source `i`, the linear map

`Mᵢ → ∏_{a : i ⟶ b} M_b`

collects the actions of all arrows leaving `i`. The reflected representation agrees with `M` away
from `i`, replaces `Mᵢ` by the cokernel of this map, and lets a reversed arrow act by inserting
its coordinate and passing to the quotient. The construction is functorial because a morphism of
representations gives a commuting square of outgoing maps.

The target is the product over the arrows leaving `i`, not a direct sum: a linear map into a direct
sum must produce finitely supported families, which need not hold when infinitely many arrows leave
`i`, whereas the arrow actions always assemble into a map to the product. Over a finite quiver the
product and direct sum agree by `DirectSum.linearEquivFunOnFintype`, so `TauCeti.outgoingMap` is
then the direct-sum map `Mᵢ → ⨁_{a : i ⟶ b} M_b` of the BGP construction. The arrow-count and
dimension-vector results below therefore carry the relevant finiteness hypotheses.

When the outgoing map is injective, the quotient dimension is the simple reflection of the old
dimension vector. This is the dual of the surjectivity condition on `TauCeti.incomingSum` in the
sink-side construction.

## Main definitions

* `TauCeti.outgoingMap`: the map collecting all arrows out of a vertex.
* `TauCeti.sourceReflectRep`: reflection of a representation at a source.
* `TauCeti.sourceReflectionFunctor`: the BGP reflection functor at a source.

## Main results

* `TauCeti.sourceReflectRep_obj_self` and `TauCeti.sourceReflectRep_obj_of_ne` compute the vertex
  spaces.
* `TauCeti.sourceReflectRep_map_reflectArrowSource` computes the action of a reversed arrow.
* `TauCeti.sourceReflectionFunctor_map_app_self_mk` computes reflection on morphisms at the
  reflected vertex.
* `TauCeti.sourceReflectionFunctor_additive` records that source reflection is additive.
* `TauCeti.dimVector_sourceReflectRep` identifies the new dimension vector with the simple
  reflection when the outgoing map is injective.
* `TauCeti.finiteDimensional_sourceReflectRep_obj` shows that source reflection preserves
  finite-dimensional vertex spaces.

## References

See Bernstein--Gelfand--Ponomarev, *Coxeter functors and Gabriel's theorem*, and
Derksen--Weyman, *An Introduction to Quiver Representations*, Ch. 2. The formal template for this
dual construction is the sink-side API in
`TauCeti.RepresentationTheory.Quiver.Reflection.Representation`, especially `TauCeti.incomingSum`,
`TauCeti.reflectRep`, and `TauCeti.reflectionFunctor`.
-/

public section

namespace TauCeti

open CategoryTheory
open _root_.TauCeti.Quiver

universe u v w x

variable {k : Type u} {Q : Type v} [Field k] [Quiver.{w} Q]

/-! ### The outgoing map -/

section OutgoingMap

/-- **The map collecting the arrows out of a vertex.** Its coordinate at `e : i ⟶ b` is the
action of `e`, so this is the product of the arrow actions over the arrows leaving `i`; for a
finite quiver that product is the direct sum of the BGP construction. No hypothesis on `i` is
imposed: the map is defined at every vertex, and it is the reflection that needs `i` to be a
source. Its range is quotiented out in `TauCeti.sourceReflectRep`. -/
noncomputable def outgoingMap (M : QuiverRep.{u, v, w, max v w x} k Q) (i : Q) :
    M.obj i →ₗ[k] ((e : Σ b : Q, (i ⟶ b)) → M.obj e.1) :=
  LinearMap.pi fun e ↦ (M.map e.2.toPath).hom

/-- The coordinate of `TauCeti.outgoingMap` at an arrow is the action of that arrow. -/
@[simp]
theorem outgoingMap_apply (M : QuiverRep.{u, v, w, max v w x} k Q) (i : Q) (y : M.obj i)
    (e : Σ b : Q, (i ⟶ b)) :
    outgoingMap M i y e = (M.map e.2.toPath).hom y := by
  simp [outgoingMap]

variable [Fintype Q] [∀ a b : Q, Fintype (a ⟶ b)]

/-- The target of `TauCeti.outgoingMap` has dimension
`∑_b #(i ⟶ b) · dim M_b`. -/
theorem finrank_pi_outgoing (M : QuiverRep.{u, v, w, max v w x} k Q) (i : Q)
    (hM : ∀ e : Σ b : Q, (i ⟶ b), FiniteDimensional k (M.obj e.1)) :
    Module.finrank k ((e : Σ b : Q, (i ⟶ b)) → M.obj e.1)
      = ∑ b : Q, Fintype.card (i ⟶ b) * Module.finrank k (M.obj b) := by
  have key : ∀ g : Q → ℕ,
      (∑ e : Σ b : Q, (i ⟶ b), g e.1) = ∑ b : Q, Fintype.card (i ⟶ b) * g b := fun g ↦ by
    rw [Fintype.sum_sigma]
    exact Finset.sum_congr rfl fun b _ ↦ by simp
  rw [Module.finrank_pi_fintype]
  exact key fun b ↦ Module.finrank k (M.obj b)

end OutgoingMap

/-! ### The reflected representation and functor -/

section SourceReflectRep

open scoped Classical in
/-- The vertex spaces of source reflection: the quotient by the range of the outgoing map at `i`,
and the old vertex spaces elsewhere. -/
private noncomputable def sourceReflectRepObj
    (M : QuiverRep.{u, v, w, max v w x} k Q) (i j : Q) : ModuleCat.{max v w x} k :=
  if j = i then ModuleCat.of k
    (((e : Σ b : Q, (i ⟶ b)) → M.obj e.1) ⧸ LinearMap.range (outgoingMap M i)) else M.obj j

private theorem sourceReflectRepObj_self
    (M : QuiverRep.{u, v, w, max v w x} k Q) (i : Q) :
    sourceReflectRepObj M i i = ModuleCat.of k
      (((e : Σ b : Q, (i ⟶ b)) → M.obj e.1) ⧸ LinearMap.range (outgoingMap M i)) :=
  ite_eq_left rfl

private theorem sourceReflectRepObj_of_ne
    (M : QuiverRep.{u, v, w, max v w x} k Q) (i : Q) {j : Q} (h : j ≠ i) :
    sourceReflectRepObj M i j = M.obj j :=
  ite_eq_right h

open scoped Classical in
/-- The prefunctor underlying source reflection. A reversed arrow inserts one coordinate into the
product and passes to the quotient; an arrow away from `i` acts as before. -/
private noncomputable def sourceReflectPrefunctor
    (M : QuiverRep.{u, v, w, max v w x} k Q) {i : Q} (hi : IsSource i) :
    Reflect Q i ⥤q ModuleCat.{max v w x} k where
  obj j := sourceReflectRepObj M i j
  map {a b} e :=
    if hb : b = i then
      eqToHom (sourceReflectRepObj_of_ne M i (fun ha ↦
          (hi.isSink_reflect.isEmpty_hom b).elim
            (cast (congrArg (fun z ↦ @_root_.Quiver.Hom (Reflect Q i) _ z b) ha) e))) ≫
        ModuleCat.ofHom ((LinearMap.range (outgoingMap M i)).mkQ.comp
          (LinearMap.single k (fun e : Σ b : Q, (i ⟶ b) ↦ M.obj e.1)
            (⟨a, cast (((hom_reflect i a b).trans
              (congrArg (reflectHom i a) hb)).trans (reflectHom_right i a)) e⟩ :
              Σ b : Q, (i ⟶ b)))) ≫
        eqToHom ((congrArg (sourceReflectRepObj M i) hb).trans
          (sourceReflectRepObj_self M i)).symm
    else if ha : a = i then
      (hi.isSink_reflect.isEmpty_hom b).elim
        (cast (congrArg (fun z ↦ @_root_.Quiver.Hom (Reflect Q i) _ z b) ha) e)
    else
      eqToHom (sourceReflectRepObj_of_ne M i ha) ≫
        M.map (cast ((hom_reflect i a b).trans (reflectHom_of_ne_of_ne ha hb)) e).toPath ≫
        eqToHom (sourceReflectRepObj_of_ne M i hb).symm

/-- **The reflection of a representation at a source** `i`. It agrees with `M` away from `i` and
puts the cokernel of `TauCeti.outgoingMap M i` at `i`. -/
noncomputable def sourceReflectRep (M : QuiverRep.{u, v, w, max v w x} k Q) {i : Q}
    (hi : IsSource i) : QuiverRep k (Reflect Q i) :=
  Paths.lift (sourceReflectPrefunctor M hi)

variable (M : QuiverRep.{u, v, w, max v w x} k Q) {i : Q} (hi : IsSource i)

private theorem sourceReflectRep_obj (j : Reflect Q i) :
    (sourceReflectRep M hi).obj j = sourceReflectRepObj M i j :=
  rfl

private theorem sourceReflectRep_map_toPath {a b : Reflect Q i} (e : a ⟶ b) :
    (sourceReflectRep M hi).map e.toPath = (sourceReflectPrefunctor M hi).map e :=
  Paths.lift_toPath _ e

/-- At the reflected vertex, source reflection is the quotient by the outgoing map's range. -/
@[simp]
theorem sourceReflectRep_obj_self :
    (sourceReflectRep M hi).obj i = ModuleCat.of k
      (((e : Σ b : Q, (i ⟶ b)) → M.obj e.1) ⧸ LinearMap.range (outgoingMap M i)) :=
  (sourceReflectRep_obj M hi i).trans (sourceReflectRepObj_self M i)

/-- Away from the source, the reflected representation is unchanged. -/
@[simp]
theorem sourceReflectRep_obj_of_ne {j : Q} (h : j ≠ i) :
    (sourceReflectRep M hi).obj j = M.obj j :=
  (sourceReflectRep_obj M hi j).trans (sourceReflectRepObj_of_ne M i h)

open scoped Classical in
/-- **A source-side reversed arrow acts by insertion followed by the quotient map.** -/
@[simp]
theorem sourceReflectRep_map_reflectArrowSource {b : Q} (e : i ⟶ b) :
    (sourceReflectRep M hi).map (reflectArrowSource i e).toPath =
      eqToHom (sourceReflectRep_obj_of_ne M hi (hi.ne_of_hom e)) ≫
        ModuleCat.ofHom ((LinearMap.range (outgoingMap M i)).mkQ.comp
          (LinearMap.single k (fun e : Σ b : Q, (i ⟶ b) ↦ M.obj e.1) ⟨b, e⟩)) ≫
        eqToHom (sourceReflectRep_obj_self M hi).symm := by
  classical
  refine ((sourceReflectRep_map_toPath M hi (reflectArrowSource i e)).trans
    (dite_eq_left rfl)).trans ?_
  conv_lhs => rw [cast_reflectArrowSource]
  rfl

/-- An arrow away from the reflected vertex acts unchanged. -/
@[simp]
theorem sourceReflectRep_map_reflectArrowOfNeOfNe {a b : Q}
    (ha : a ≠ i) (hb : b ≠ i) (e : a ⟶ b) :
    (sourceReflectRep M hi).map (reflectArrowOfNeOfNe ha hb e).toPath =
      eqToHom (sourceReflectRep_obj_of_ne M hi ha) ≫ M.map e.toPath ≫
        eqToHom (sourceReflectRep_obj_of_ne M hi hb).symm := by
  classical
  refine ((sourceReflectRep_map_toPath (a := a) (b := b) M hi
    (reflectArrowOfNeOfNe ha hb e)).trans (dite_eq_right hb)).trans ?_
  refine (dite_eq_right ha).trans ?_
  conv_lhs => rw [cast_reflectArrowOfNeOfNe]
  rfl

/-- The coordinatewise map on the products indexed by arrows out of `i`. -/
private def outgoingCoordMap {M N : QuiverRep.{u, v, w, max v w x} k Q}
    (η : M ⟶ N) (i : Q) :
    ((e : Σ b : Q, (i ⟶ b)) → M.obj e.1) →ₗ[k]
      ((e : Σ b : Q, (i ⟶ b)) → N.obj e.1) where
  toFun f e := η.app e.1 (f e)
  map_add' f g := by ext e; simp
  map_smul' r f := by ext e; simp

private theorem outgoingCoordMap_id (M : QuiverRep.{u, v, w, max v w x} k Q) (i : Q) :
    outgoingCoordMap (𝟙 M) i = LinearMap.id := by
  ext f e
  rfl

private theorem outgoingCoordMap_comp
    {M N P : QuiverRep.{u, v, w, max v w x} k Q} (η : M ⟶ N) (θ : N ⟶ P) (i : Q) :
    outgoingCoordMap (η ≫ θ) i = (outgoingCoordMap θ i).comp (outgoingCoordMap η i) := by
  ext f e
  rfl

/-- The outgoing map is natural in the representation. -/
theorem outgoingMap_naturality {M N : QuiverRep.{u, v, w, max v w x} k Q}
    (η : M ⟶ N) (i : Q) (y : M.obj i) :
    (fun e ↦ η.app e.1 (outgoingMap M i y e)) = outgoingMap N i (η.app i y) := by
  ext e
  exact congrArg (fun f : M.obj i ⟶ N.obj e.1 ↦ f.hom y) (η.naturality e.2.toPath)

private theorem outgoingCoordMap_outgoingMap
    {M N : QuiverRep.{u, v, w, max v w x} k Q} (η : M ⟶ N) (i : Q) (y : M.obj i) :
    outgoingCoordMap η i (outgoingMap M i y) = outgoingMap N i (η.app i y) :=
  outgoingMap_naturality η i y

private theorem outgoingCoordMap_range_le
    {M N : QuiverRep.{u, v, w, max v w x} k Q} (η : M ⟶ N) (i : Q) :
    LinearMap.range (outgoingMap M i) ≤
      (LinearMap.range (outgoingMap N i)).comap (outgoingCoordMap η i) := by
  rintro _ ⟨y, rfl⟩
  rw [Submodule.mem_comap, outgoingCoordMap_outgoingMap]
  exact LinearMap.mem_range_self _ _

/-- The quotient map induced at the reflected vertex by a morphism of representations. -/
private noncomputable def outgoingQuotMap
    {M N : QuiverRep.{u, v, w, max v w x} k Q} (η : M ⟶ N) (i : Q) :
    (((e : Σ b : Q, (i ⟶ b)) → M.obj e.1) ⧸ LinearMap.range (outgoingMap M i)) →ₗ[k]
      (((e : Σ b : Q, (i ⟶ b)) → N.obj e.1) ⧸ LinearMap.range (outgoingMap N i)) :=
  (LinearMap.range (outgoingMap M i)).mapQ (LinearMap.range (outgoingMap N i))
    (outgoingCoordMap η i) (outgoingCoordMap_range_le η i)

@[simp]
private theorem outgoingQuotMap_mk
    {M N : QuiverRep.{u, v, w, max v w x} k Q} (η : M ⟶ N) (i : Q)
    (f : (e : Σ b : Q, (i ⟶ b)) → M.obj e.1) :
    outgoingQuotMap η i (Submodule.Quotient.mk f) =
      (LinearMap.range (outgoingMap N i)).mkQ (fun e ↦ η.app e.1 (f e)) := by
  unfold outgoingQuotMap
  exact LinearMap.congr_fun
    (Submodule.mapQ_mkQ (p := LinearMap.range (outgoingMap M i))
      (LinearMap.range (outgoingMap N i)) (outgoingCoordMap η i)
      (h := outgoingCoordMap_range_le η i)) f

@[simp]
private theorem outgoingQuotMap_id (M : QuiverRep.{u, v, w, max v w x} k Q) (i : Q) :
    outgoingQuotMap (𝟙 M) i = LinearMap.id := by
  unfold outgoingQuotMap
  cases outgoingCoordMap_id M i
  exact Submodule.mapQ_id (LinearMap.range (outgoingMap M i))

@[simp]
private theorem outgoingQuotMap_comp
    {M N P : QuiverRep.{u, v, w, max v w x} k Q} (η : M ⟶ N) (θ : N ⟶ P) (i : Q) :
    outgoingQuotMap (η ≫ θ) i = (outgoingQuotMap θ i).comp (outgoingQuotMap η i) := by
  unfold outgoingQuotMap
  cases outgoingCoordMap_comp η θ i
  exact Submodule.mapQ_comp (LinearMap.range (outgoingMap M i))
    (LinearMap.range (outgoingMap N i)) (LinearMap.range (outgoingMap P i))
    (outgoingCoordMap η i) (outgoingCoordMap θ i) (outgoingCoordMap_range_le η i)
    (outgoingCoordMap_range_le θ i)

open scoped Classical in
private theorem outgoingQuotMap_single
    {M N : QuiverRep.{u, v, w, max v w x} k Q} (η : M ⟶ N) (i : Q)
    {a : Q} (e : i ⟶ a) (y : M.obj a) :
    outgoingQuotMap η i
        (Submodule.Quotient.mk (Pi.single ⟨a, e⟩ y)) =
      (LinearMap.range (outgoingMap N i)).mkQ (Pi.single ⟨a, e⟩ (η.app a y)) := by
  rw [outgoingQuotMap_mk]
  congr 1
  ext c
  by_cases hc : c = ⟨a, e⟩
  · subst c
    simp
  · simp [Pi.single_eq_of_ne hc]

open scoped Classical in
private noncomputable def sourceReflectRepMapApp
    {M N : QuiverRep.{u, v, w, max v w x} k Q} (η : M ⟶ N) {i : Q} (hi : IsSource i)
    (j : Reflect Q i) : (sourceReflectRep M hi).obj j ⟶ (sourceReflectRep N hi).obj j :=
  if hj : j = i then
    eqToHom ((congrArg (sourceReflectRep M hi).obj hj).trans (sourceReflectRep_obj_self M hi)) ≫
      ModuleCat.ofHom (outgoingQuotMap η i) ≫
      eqToHom ((congrArg (sourceReflectRep N hi).obj hj).trans
        (sourceReflectRep_obj_self N hi)).symm
  else
    eqToHom (sourceReflectRep_obj_of_ne M hi hj) ≫ η.app j ≫
      eqToHom (sourceReflectRep_obj_of_ne N hi hj).symm

@[simp]
private theorem sourceReflectRepMapApp_self
    {M N : QuiverRep.{u, v, w, max v w x} k Q} (η : M ⟶ N) {i : Q} (hi : IsSource i) :
    sourceReflectRepMapApp η hi i =
      eqToHom (sourceReflectRep_obj_self M hi) ≫ ModuleCat.ofHom (outgoingQuotMap η i) ≫
        eqToHom (sourceReflectRep_obj_self N hi).symm := by
  classical
  unfold sourceReflectRepMapApp
  split
  · rfl
  · rename_i h
    exact (h rfl).elim

private theorem sourceReflectRepMapApp_of_ne
    {M N : QuiverRep.{u, v, w, max v w x} k Q} (η : M ⟶ N) {i : Q} (hi : IsSource i)
    {j : Reflect Q i} (hj : j ≠ i) :
    sourceReflectRepMapApp η hi j =
      eqToHom (sourceReflectRep_obj_of_ne M hi hj) ≫ η.app j ≫
        eqToHom (sourceReflectRep_obj_of_ne N hi hj).symm := by
  classical
  simp [sourceReflectRepMapApp, hj]

private theorem sourceReflectRepMapApp_naturality_arrow
    {M N : QuiverRep.{u, v, w, max v w x} k Q} (η : M ⟶ N) {i : Q} (hi : IsSource i)
    {a b : Reflect Q i} (e : a ⟶ b) :
    (sourceReflectRep M hi).map e.toPath ≫ sourceReflectRepMapApp η hi b =
      sourceReflectRepMapApp η hi a ≫ (sourceReflectRep N hi).map e.toPath := by
  classical
  by_cases hb : b = i
  · subst b
    let e' : @_root_.Quiver.Hom Q _ i a :=
      cast ((@hom_reflect Q _ i a i).trans (@reflectHom_right Q _ i a)) e
    have he : @reflectArrowSource Q _ i a e' = e := @reflectArrowSource_cast Q _ i a e _
    rw [← he, sourceReflectRep_map_reflectArrowSource M hi e',
      sourceReflectRep_map_reflectArrowSource N hi e']
    rw [sourceReflectRepMapApp_of_ne η hi (hi.ne_of_hom e'), sourceReflectRepMapApp_self η hi]
    refine (eqToHom_conjugate_square _ _ (sourceReflectRep_obj_self N hi)
      (sourceReflectRep_obj_of_ne N hi (hi.ne_of_hom e')) _ _ _ _).mpr ?_
    ext y
    exact outgoingQuotMap_single η i e' y
  · by_cases ha : a = i
    · subst a
      exact (hi.isSink_reflect.isEmpty_hom b).elim e
    · let e' : @_root_.Quiver.Hom Q _ a b :=
        cast ((@hom_reflect Q _ i a b).trans (@reflectHom_of_ne_of_ne Q _ i a b ha hb)) e
      have he : @reflectArrowOfNeOfNe Q _ i a b ha hb e' = e :=
        @reflectArrowOfNeOfNe_cast Q _ i a b ha hb e _
      rw [← he, sourceReflectRep_map_reflectArrowOfNeOfNe M hi ha hb e',
        sourceReflectRep_map_reflectArrowOfNeOfNe N hi ha hb e']
      rw [sourceReflectRepMapApp_of_ne η hi ha, sourceReflectRepMapApp_of_ne η hi hb]
      exact (eqToHom_conjugate_square _ _ (sourceReflectRep_obj_of_ne N hi hb) _ _ _ _ _).mpr
        (η.naturality e'.toPath)

private noncomputable def sourceReflectRepMap
    {M N : QuiverRep.{u, v, w, max v w x} k Q} (η : M ⟶ N) {i : Q} (hi : IsSource i) :
    sourceReflectRep M hi ⟶ sourceReflectRep N hi :=
  Paths.liftNatTrans (sourceReflectRepMapApp η hi) (sourceReflectRepMapApp_naturality_arrow η hi)

private theorem sourceEqToHom_conjugate_eq_id {C : Type*} [Category* C] {X Y : C}
    (h : X = Y) (f : Y ⟶ Y) (hf : f = 𝟙 Y) :
    eqToHom h ≫ f ≫ eqToHom h.symm = 𝟙 X := by
  subst h
  simp [hf]

private theorem sourceEqToHom_conjugate_eq_comp {C : Type*} [Category* C]
    {X X' Y Y' Z Z' : C} (hX : X = X') (hY : Y = Y') (hZ : Z = Z')
    (f : X' ⟶ Z') (g : X' ⟶ Y') (h : Y' ⟶ Z') (hf : f = g ≫ h) :
    eqToHom hX ≫ f ≫ eqToHom hZ.symm =
      (eqToHom hX ≫ g ≫ eqToHom hY.symm) ≫ eqToHom hY ≫ h ≫ eqToHom hZ.symm := by
  subst hX
  subst hY
  subst hZ
  simp [hf]

private theorem sourceEqToHom_conjugate_add {C : Type*} [Category* C] [Preadditive C]
    {X X' Y Y' : C} (hX : X = X') (hY : Y' = Y) {f g h : X' ⟶ Y'} (hf : f = g + h) :
    eqToHom hX ≫ f ≫ eqToHom hY =
      (eqToHom hX ≫ g ≫ eqToHom hY) + (eqToHom hX ≫ h ≫ eqToHom hY) := by
  subst hX
  subst hY
  simp [hf]

private theorem sourceReflectRepMap_id (M : QuiverRep.{u, v, w, max v w x} k Q)
    {i : Q} (hi : IsSource i) : sourceReflectRepMap (𝟙 M) hi = 𝟙 (sourceReflectRep M hi) := by
  apply NatTrans.ext
  funext j
  classical
  -- `Paths.liftNatTrans` has no propositional lemma exposing its `app`; this one definitional
  -- reduction is isolated here, before reasoning about the resulting categorical morphism.
  change sourceReflectRepMapApp (𝟙 M) hi j = 𝟙 _
  by_cases hj : j = i
  · subst j
    rw [sourceReflectRepMapApp_self, outgoingQuotMap_id, ModuleCat.ofHom_id]
    exact sourceEqToHom_conjugate_eq_id _ _ rfl
  · rw [sourceReflectRepMapApp_of_ne _ _ hj]
    exact sourceEqToHom_conjugate_eq_id _ _ rfl

private theorem sourceReflectRepMap_comp
    {M N P : QuiverRep.{u, v, w, max v w x} k Q} (η : M ⟶ N) (θ : N ⟶ P)
    {i : Q} (hi : IsSource i) :
    sourceReflectRepMap (η ≫ θ) hi = sourceReflectRepMap η hi ≫ sourceReflectRepMap θ hi := by
  apply NatTrans.ext
  funext j
  classical
  -- As above, this isolates the definitional `app` reduction for `Paths.liftNatTrans`.
  change sourceReflectRepMapApp (η ≫ θ) hi j =
    sourceReflectRepMapApp η hi j ≫ sourceReflectRepMapApp θ hi j
  by_cases hj : j = i
  · subst j
    rw [sourceReflectRepMapApp_self, sourceReflectRepMapApp_self,
      sourceReflectRepMapApp_self, outgoingQuotMap_comp, ModuleCat.ofHom_comp]
    exact sourceEqToHom_conjugate_eq_comp _ _ (sourceReflectRep_obj_self _ hi) _ _ _ rfl
  · rw [sourceReflectRepMapApp_of_ne _ _ hj, sourceReflectRepMapApp_of_ne _ _ hj,
      sourceReflectRepMapApp_of_ne _ _ hj]
    exact sourceEqToHom_conjugate_eq_comp _ _ (sourceReflectRep_obj_of_ne _ hi hj) _ _ _ rfl

/-- **The BGP reflection functor at a source.** It uses the quotient map induced by each morphism
at the reflected vertex and leaves all other components unchanged. -/
noncomputable def sourceReflectionFunctor (i : Q) (hi : IsSource i) :
    QuiverRep.{u, v, w, max v w x} k Q ⥤ QuiverRep k (Reflect Q i) where
  obj M := sourceReflectRep M hi
  map η := sourceReflectRepMap η hi
  map_id M := sourceReflectRepMap_id M hi
  map_comp η θ := sourceReflectRepMap_comp η θ hi

private theorem sourceReflectionFunctor_obj_def (i : Q) (hi : IsSource i)
    (M : QuiverRep.{u, v, w, max v w x} k Q) :
    (sourceReflectionFunctor i hi).obj M = sourceReflectRep M hi :=
  rfl

/-- The source reflection functor sends `M` to `TauCeti.sourceReflectRep M hi`. -/
@[simp]
theorem sourceReflectionFunctor_obj (i : Q) (hi : IsSource i)
    (M : QuiverRep.{u, v, w, max v w x} k Q) :
    (sourceReflectionFunctor i hi).obj M = sourceReflectRep M hi :=
  sourceReflectionFunctor_obj_def i hi M

private theorem sourceReflectionFunctor_map_app
    {M N : QuiverRep.{u, v, w, max v w x} k Q} (η : M ⟶ N) {i : Q} (hi : IsSource i)
    (j : Reflect Q i) :
    ((sourceReflectionFunctor i hi).map η).app j = sourceReflectRepMapApp η hi j :=
  rfl

private theorem outgoingQuotMap_add
    {M N : QuiverRep.{u, v, w, max v w x} k Q} (η θ : M ⟶ N) (i : Q) :
    outgoingQuotMap (η + θ) i = outgoingQuotMap η i + outgoingQuotMap θ i := by
  apply LinearMap.ext
  intro q
  induction q using Submodule.Quotient.induction_on with
  | _ f =>
    have h : (fun e ↦ (η + θ).app e.1 (f e)) =
        (fun e ↦ η.app e.1 (f e) + θ.app e.1 (f e)) := by
      ext e
      rfl
    rw [LinearMap.add_apply, outgoingQuotMap_mk, outgoingQuotMap_mk, outgoingQuotMap_mk]
    rw [h]
    exact map_add _ _ _

/-- **The source reflection functor is additive.** The map induced on the quotient is additive in
the original morphism, coordinate by coordinate. -/
instance sourceReflectionFunctor_additive (i : Q) (hi : IsSource i) :
    (sourceReflectionFunctor (k := k) i hi).Additive where
  map_add {M N η θ} := by
    apply NatTrans.ext
    funext j
    classical
    rw [NatTrans.app_add, sourceReflectionFunctor_map_app (η + θ) hi j,
      sourceReflectionFunctor_map_app η hi j, sourceReflectionFunctor_map_app θ hi j]
    by_cases hj : j = i
    · subst j
      rw [sourceReflectRepMapApp_self, sourceReflectRepMapApp_self,
        sourceReflectRepMapApp_self, outgoingQuotMap_add, ModuleCat.ofHom_add]
      exact sourceEqToHom_conjugate_add _ _ rfl
    · rw [sourceReflectRepMapApp_of_ne _ _ hj, sourceReflectRepMapApp_of_ne _ _ hj,
        sourceReflectRepMapApp_of_ne _ _ hj]
      exact sourceEqToHom_conjugate_add _ _ rfl

private theorem sourceReflectionFunctor_map_app_self
    {M N : QuiverRep.{u, v, w, max v w x} k Q} (η : M ⟶ N) {i : Q} (hi : IsSource i) :
    eqToHom (sourceReflectRep_obj_self M hi).symm ≫
        ((sourceReflectionFunctor i hi).map η).app i ≫
        eqToHom (sourceReflectRep_obj_self N hi) = ModuleCat.ofHom (outgoingQuotMap η i) := by
  rw [sourceReflectionFunctor_map_app η hi i, sourceReflectRepMapApp_self]
  exact eqToHom_conjugate_cancel _ _ _

/-- At the reflected vertex, source reflection sends a morphism to the induced map on quotient
classes, computed here on a representative. -/
@[simp]
theorem sourceReflectionFunctor_map_app_self_mk
    {M N : QuiverRep.{u, v, w, max v w x} k Q} (η : M ⟶ N) {i : Q} (hi : IsSource i)
    (f : (e : Σ b : Q, (i ⟶ b)) → M.obj e.1) :
    (eqToHom ((congrArg (fun R : QuiverRep k (Reflect Q i) ↦ R.obj i)
          (sourceReflectionFunctor_obj i hi N)).trans (sourceReflectRep_obj_self N hi))).hom
        ((((sourceReflectionFunctor i hi).map η).app i).hom
          ((eqToHom ((congrArg (fun R : QuiverRep k (Reflect Q i) ↦ R.obj i)
            (sourceReflectionFunctor_obj i hi M)).trans
              (sourceReflectRep_obj_self M hi)).symm).hom (Submodule.Quotient.mk f))) =
      (LinearMap.range (outgoingMap N i)).mkQ (fun e ↦ η.app e.1 (f e)) := by
  have hM : (congrArg (fun R : QuiverRep k (Reflect Q i) ↦ R.obj i)
      (sourceReflectionFunctor_obj i hi M)).trans (sourceReflectRep_obj_self M hi) =
      sourceReflectRep_obj_self M hi := Subsingleton.elim _ _
  have hN : (congrArg (fun R : QuiverRep k (Reflect Q i) ↦ R.obj i)
      (sourceReflectionFunctor_obj i hi N)).trans (sourceReflectRep_obj_self N hi) =
      sourceReflectRep_obj_self N hi := Subsingleton.elim _ _
  rw [hM, hN]
  exact congrArg (fun g : ModuleCat.of k
      (((e : Σ b : Q, (i ⟶ b)) → M.obj e.1) ⧸ LinearMap.range (outgoingMap M i)) ⟶
      ModuleCat.of k
        (((e : Σ b : Q, (i ⟶ b)) → N.obj e.1) ⧸ LinearMap.range (outgoingMap N i)) ↦
      g ((LinearMap.range (outgoingMap M i)).mkQ f))
    (sourceReflectionFunctor_map_app_self η hi)

/-- Away from the reflected vertex, source reflection leaves morphism components unchanged. -/
@[simp]
theorem sourceReflectionFunctor_map_app_of_ne
    {M N : QuiverRep.{u, v, w, max v w x} k Q} (η : M ⟶ N) {i : Q} (hi : IsSource i)
    {j : Q} (hj : j ≠ i) :
    ((sourceReflectionFunctor i hi).map η).app j =
      eqToHom ((congrArg (fun R : QuiverRep k (Reflect Q i) ↦ R.obj j)
          (sourceReflectionFunctor_obj i hi M)).trans (sourceReflectRep_obj_of_ne M hi hj)) ≫
        η.app j ≫
        eqToHom ((congrArg (fun R : QuiverRep k (Reflect Q i) ↦ R.obj j)
          (sourceReflectionFunctor_obj i hi N)).trans
            (sourceReflectRep_obj_of_ne N hi hj)).symm := by
  have hM : (congrArg (fun R : QuiverRep k (Reflect Q i) ↦ R.obj j)
      (sourceReflectionFunctor_obj i hi M)).trans (sourceReflectRep_obj_of_ne M hi hj) =
      sourceReflectRep_obj_of_ne M hi hj := Subsingleton.elim _ _
  have hN : (congrArg (fun R : QuiverRep k (Reflect Q i) ↦ R.obj j)
      (sourceReflectionFunctor_obj i hi N)).trans (sourceReflectRep_obj_of_ne N hi hj) =
      sourceReflectRep_obj_of_ne N hi hj := Subsingleton.elim _ _
  rw [hM, hN]
  rw [sourceReflectionFunctor_map_app η hi j]
  exact sourceReflectRepMapApp_of_ne η hi hj

end SourceReflectRep

/-! ### The dimension vector -/

section DimVector

variable [Fintype Q] [∀ a b : Q, Fintype (a ⟶ b)]
variable (M : QuiverRep.{u, v, w, max v w x} k Q) {i : Q} (hi : IsSource i)

omit [Fintype Q] [∀ a b : Q, Fintype (a ⟶ b)] in
/-- Away from the source, the dimension vector is unchanged. -/
@[simp]
theorem dimVector_sourceReflectRep_of_ne {j : Q} (h : j ≠ i) :
    dimVector (sourceReflectRep M hi) j = dimVector M j := by
  rw [dimVector_apply (M := sourceReflectRep M hi) (i := j), dimVector_apply]
  exact congrArg (fun X : ModuleCat.{max v w x} k ↦ Module.finrank k X)
    (sourceReflectRep_obj_of_ne M hi h)

/-- **The dimension of the reflected space at the source.** If the outgoing map is injective,
the dimension of its cokernel plus the old source dimension is the total dimension at the targets
of outgoing arrows. -/
theorem dimVector_sourceReflectRep_self_add
    (hM : ∀ e : Σ b : Q, (i ⟶ b), FiniteDimensional k (M.obj e.1))
    (hinj : Function.Injective (outgoingMap M i)) :
    dimVector (sourceReflectRep M hi) i + dimVector M i
      = ∑ b : Q, Fintype.card (i ⟶ b) * dimVector M b := by
  have hquot : dimVector (sourceReflectRep M hi) i =
      Module.finrank k
        (((e : Σ b : Q, (i ⟶ b)) → M.obj e.1) ⧸ LinearMap.range (outgoingMap M i)) := by
    rw [dimVector_apply (M := sourceReflectRep M hi) (i := i)]
    exact congrArg (fun X : ModuleCat.{max v w x} k ↦ Module.finrank k X)
      (sourceReflectRep_obj_self M hi)
  have hrange : Module.finrank k (LinearMap.range (outgoingMap M i)) = dimVector M i := by
    rw [← LinearEquiv.finrank_eq (LinearEquiv.ofInjective (outgoingMap M i) hinj)]
    exact (dimVector_apply M i).symm
  rw [hquot, ← hrange, Submodule.finrank_quotient_add_finrank,
    finrank_pi_outgoing M i hM]
  exact Finset.sum_congr rfl fun b _ ↦ congrArg (Fintype.card (i ⟶ b) * ·)
    (dimVector_apply M b).symm

/-- **Source reflection acts on dimension vectors by the simple reflection.** -/
theorem dimVector_sourceReflectRep [DecidableEq Q]
    (hM : ∀ e : Σ b : Q, (i ⟶ b), FiniteDimensional k (M.obj e.1))
    (hinj : Function.Injective (outgoingMap M i)) :
    (fun j : Q ↦ (dimVector (sourceReflectRep M hi) j : ℤ)) =
      vertexPreReflection Q i (fun j ↦ (dimVector M j : ℤ)) := by
  funext j
  rcases eq_or_ne j i with rfl | hj
  · have hzero : ∀ v : Q, Fintype.card (v ⟶ j) = 0 := fun v ↦
      Fintype.card_eq_zero_iff.mpr (hi.isEmpty_hom v)
    rw [vertexPreReflection_apply_self]
    have h := dimVector_sourceReflectRep_self_add M hi hM hinj
    have h' : ((dimVector (sourceReflectRep M hi) j : ℤ)) + (dimVector M j : ℤ) =
        ∑ b : Q, (Fintype.card (j ⟶ b) : ℤ) * (dimVector M b : ℤ) := by
      exact_mod_cast congrArg (fun n : ℕ ↦ (n : ℤ)) h
    have hsimp : ∑ v : Q,
        ((Fintype.card (j ⟶ v) : ℤ) + (Fintype.card (v ⟶ j) : ℤ)) *
          (dimVector M v : ℤ) =
        ∑ v : Q, (Fintype.card (j ⟶ v) : ℤ) * (dimVector M v : ℤ) :=
      Finset.sum_congr rfl fun v _ ↦ by simp [hzero v]
    rw [hsimp]
    linarith [h']
  · rw [vertexPreReflection_apply_of_ne Q i _ hj, dimVector_sourceReflectRep_of_ne M hi hj]

omit [Fintype Q] [∀ a b : Q, Fintype (a ⟶ b)] in
/-- **Source reflection preserves finite-dimensionality** of every vertex space. -/
theorem finiteDimensional_sourceReflectRep_obj
    [Finite (Σ b : Q, (i ⟶ b))]
    (h : ∀ a : Q, FiniteDimensional k (M.obj a)) (j : Q) :
    FiniteDimensional k ((sourceReflectRep M hi).obj j) := by
  rcases eq_or_ne j i with rfl | hj
  · have hpi : ∀ e : Σ b : Q, (j ⟶ b), FiniteDimensional k (M.obj e.1) := fun e ↦ h e.1
    rw [sourceReflectRep_obj_self M hi]
    exact FiniteDimensional.finiteDimensional_quotient _
  · rw [sourceReflectRep_obj_of_ne M hi hj]
    exact h j

end DimVector

end TauCeti
