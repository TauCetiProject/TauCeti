/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Polynomial.Laurent.AEval
public import TauCeti.Algebra.Polynomial.Laurent.Specialization
public import TauCeti.CategoryTheory.GrothendieckGroup.Graded

/-!
# The Laurent coefficient ring acting on graded triangulated `K₀`

A grading shift `{1}` of a pretriangulated category is a triangulated autoequivalence `e`.  It acts
on triangulated `K₀` by the automorphism `TauCeti.TriangulatedK0.mapEquiv e`, and iterating it
gives the `ℤ`-action `TauCeti.TriangulatedK0.shiftZPow e`.  Repackaging that action as a module
structure over `ℤ[q,q⁻¹] = LaurentPolynomial ℤ`, with `q` acting by the shift, makes graded
triangulated `K₀` a `ℤ[q,q⁻¹]`-module, as `TauCeti.LaurentK0` does for graded exact `K₀`.

`TauCeti.LaurentTriangulatedK0 C e` is triangulated `K₀` with this module structure, built as
`TauCeti.LaurentAEval` of the shift automorphism: no new group is constructed and no relation is
added.  The defining property is `TauCeti.LaurentTriangulatedK0.T_smul`, the normalization
`[M{n}] = qⁿ [M]`.  The suspension still acts by a sign, `[M⟦n⟧] = (-1)ⁿ [M]`, so the internal and
cohomological shifts enter as the Laurent variable and as a sign respectively.

The universal property `TauCeti.LaurentTriangulatedK0.liftEquiv` identifies the
`ℤ[q,q⁻¹]`-linear maps out of graded triangulated `K₀` into a `ℤ[q,q⁻¹]`-module `N` with the
triangle-additive invariants `a` satisfying `a(M{1}) = q · a(M)`, that is, the shift-compatible
invariants `TauCeti.TriangulatedK0.ShiftInvariant` for multiplication by `q`.  A triangulated
functor commuting with the grading shifts induces a `ℤ[q,q⁻¹]`-linear map, and a triangulated
equivalence commuting with them induces an isomorphism.

After specializing at `q = ε` for a unit `ε : ℤˣ`, the class of `M{1}` is `ε` times the class of
`M`.  Forgetting the grading along a triangulated functor `F` with `{1} ⋙ F ≅ F` factors through
the specialization at `q = 1`: this is `TauCeti.LaurentTriangulatedK0.forgetGrading`.  When the
grading shift is the suspension itself, `q` acts by `-1`.

## Main definitions

* `TauCeti.LaurentTriangulatedK0`: graded triangulated `K₀` as a `ℤ[q,q⁻¹]`-module.
* `TauCeti.LaurentTriangulatedK0.of`: the class `[M]` of an object.
* `TauCeti.LaurentTriangulatedK0.lift`: the `ℤ[q,q⁻¹]`-linear map induced by a shift-compatible
  invariant.
* `TauCeti.LaurentTriangulatedK0.map`: the `ℤ[q,q⁻¹]`-linear map induced by a triangulated functor
  commuting with the grading shifts.
* `TauCeti.LaurentTriangulatedK0.mapEquiv`: the isomorphism induced by such an equivalence.
* `TauCeti.LaurentTriangulatedK0.forgetGrading`: forgetting the grading, as a map out of graded
  triangulated `K₀` specialized at `q = 1`.

## Main results

* `TauCeti.LaurentTriangulatedK0.T_smul`: `qⁿ · [M] = [M{n}]`, with its generating cases
  `TauCeti.LaurentTriangulatedK0.T_one_smul_of` and
  `TauCeti.LaurentTriangulatedK0.T_neg_one_smul_of`.
* `TauCeti.LaurentTriangulatedK0.of_distTriang` and `TauCeti.LaurentTriangulatedK0.of_shift`: the
  triangle relation and the sign of the suspension.
* `TauCeti.LaurentTriangulatedK0.liftEquiv`: the universal property over the Laurent coefficient
  ring.
* `TauCeti.LaurentTriangulatedK0.hom_ext`: a `ℤ[q,q⁻¹]`-linear map out of graded triangulated `K₀`
  is determined by its values on object classes.
* `TauCeti.LaurentTriangulatedK0.mk_of_shift_functor_obj`: after specializing at `q = ε`, the
  class of `M{1}` is `ε` times the class of `M`.
* `TauCeti.LaurentTriangulatedK0.T_one_smul_of_iso_shiftFunctor`: a grading shift isomorphic to
  the suspension makes `q` act by `-1`.

## References

* Zsuzsanna Dancso and Anthony Licata, "Koszul algebras and flow lattices", *Journal of
  Combinatorial Theory, Series A* 185 (2022), Section 2.2, Definition 2.3, where graded `K₀` is a
  `ℤ[q,q⁻¹]`-module with `[M{1}] = q[M]`.
* Charles A. Weibel, *The K-book: An Introduction to Algebraic K-theory*, Chapter II,
  Exercise II.9.15, for triangulated `K₀`.
-/

public section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated ZeroObject
open LaurentPolynomial hiding C

universe w w' w'' v v' v'' u u' u''

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C] [EssentiallySmall.{w} C]

variable (C) in
/-- **Graded triangulated `K₀` over the Laurent coefficient ring.**  The underlying group is the
triangulated Grothendieck group of `C`, and the Laurent variable `q` acts by the automorphism
`[M] ↦ [M{1}]` induced by the grading shift `e`.  Use
`TauCeti.LaurentTriangulatedK0.ofTriangulatedK0` to move between the two views. -/
abbrev LaurentTriangulatedK0 (e : C ≌ C) [e.functor.CommShift ℤ] [e.functor.IsTriangulated] :=
  LaurentAEval (TriangulatedK0.mapEquiv e)

namespace LaurentTriangulatedK0

variable (e : C ≌ C) [e.functor.CommShift ℤ] [e.functor.IsTriangulated]

/-- **Graded triangulated `K₀` is triangulated `K₀`.**  Moving a class across this equivalence
changes nothing but which module structure is in scope. -/
noncomputable abbrev ofTriangulatedK0 : TriangulatedK0 C ≃+ LaurentTriangulatedK0 C e :=
  LaurentAEval.of (TriangulatedK0.mapEquiv e)

/-- **`qⁿ · [M] = [M{n}]`**: the Laurent variable acts on graded triangulated `K₀` by the grading
shift, and its `n`-th power by the `n`-fold shift. -/
-- Not `@[simp]`: `TauCeti.LaurentAEval.T_smul_of` and `TauCeti.TriangulatedK0.shiftZPow_apply`
-- already normalize both sides.
theorem T_smul (n : ℤ) (x : TriangulatedK0 C) :
    (T n : LaurentPolynomial ℤ) • ofTriangulatedK0 e x =
      ofTriangulatedK0 e (TriangulatedK0.shiftZPow e n x) := by
  rw [LaurentAEval.T_smul_of, TriangulatedK0.shiftZPow_apply]

/-- The class `[M]` of an object in graded triangulated `K₀`. -/
noncomputable def of (X : C) : LaurentTriangulatedK0 C e :=
  ofTriangulatedK0 e (TriangulatedK0.of X)

@[simp]
lemma ofTriangulatedK0_of (X : C) : ofTriangulatedK0 e (TriangulatedK0.of X) = of e X :=
  (rfl)

/-- Isomorphic objects have the same class. -/
theorem of_congr {X Y : C} (i : X ≅ Y) : of e X = of e Y := by
  rw [← ofTriangulatedK0_of, ← ofTriangulatedK0_of, TriangulatedK0.of_congr i]

/-- **The defining relation of graded triangulated `K₀`**: the class of the middle term of a
distinguished triangle is the sum of the classes of its outer terms. -/
theorem of_distTriang {T : Triangle C} (hT : T ∈ distTriang C) :
    of e T.obj₂ = of e T.obj₁ + of e T.obj₃ := by
  rw [← ofTriangulatedK0_of, TriangulatedK0.of_distTriang hT, map_add, ofTriangulatedK0_of,
    ofTriangulatedK0_of]

/-- The class of the zero object vanishes. -/
@[simp]
theorem of_zero : of e (0 : C) = 0 := by
  rw [← ofTriangulatedK0_of, TriangulatedK0.of_zero, map_zero]

/-- The class of an object which is zero vanishes. -/
@[simp]
theorem of_eq_zero_of_isZero {X : C} (hX : IsZero X) : of e X = 0 := by
  rw [← ofTriangulatedK0_of, TriangulatedK0.of_eq_zero_of_isZero hX, map_zero]

/-- The class of a biproduct is the sum of the classes. -/
@[simp]
theorem of_biprod (X Y : C) : of e (X ⊞ Y) = of e X + of e Y := by
  rw [← ofTriangulatedK0_of, TriangulatedK0.of_biprod, map_add, ofTriangulatedK0_of,
    ofTriangulatedK0_of]

/-- **The suspension acts by a sign**, `[M⟦n⟧] = (-1)ⁿ [M]`, independently of the Laurent action of
the grading shift. -/
@[simp]
theorem of_shift (n : ℤ) (X : C) : of e (X⟦n⟧) = (n.negOnePow : ℤ) • of e X := by
  rw [← ofTriangulatedK0_of, TriangulatedK0.of_shift, map_zsmul, ofTriangulatedK0_of]

/-- **`q · [M] = [M{1}]`.** -/
@[simp]
theorem T_one_smul_of (X : C) :
    (T 1 : LaurentPolynomial ℤ) • of e X = of e (e.functor.obj X) := by
  rw [← ofTriangulatedK0_of, LaurentAEval.T_one_smul_of, TriangulatedK0.mapEquiv_of,
    ofTriangulatedK0_of]

/-- **`q⁻¹ · [M] = [M{-1}]`.** -/
@[simp]
theorem T_neg_one_smul_of (X : C) :
    (T (-1) : LaurentPolynomial ℤ) • of e X = of e (e.inverse.obj X) := by
  rw [← ofTriangulatedK0_of, LaurentAEval.T_neg_one_smul_of, TriangulatedK0.mapEquiv_symm_of,
    ofTriangulatedK0_of]

/-- **A grading shift isomorphic to the suspension makes `q` act by `-1`.** -/
theorem T_one_smul_of_iso_shiftFunctor (h : e.functor ≅ shiftFunctor C (1 : ℤ))
    (x : LaurentTriangulatedK0 C e) : (T 1 : LaurentPolynomial ℤ) • x = -x := by
  obtain ⟨z, rfl⟩ := (ofTriangulatedK0 e).surjective x
  rw [LaurentAEval.T_one_smul_of, TriangulatedK0.mapEquiv_apply_of_iso_shiftFunctor e h, map_neg]

variable {e}
variable {N : Type*} [AddCommGroup N] [Module (LaurentPolynomial ℤ) N]

/-- **A `ℤ[q,q⁻¹]`-linear map out of graded triangulated `K₀` is determined by its values on
object classes.** -/
@[ext]
theorem hom_ext {f g : LaurentTriangulatedK0 C e →ₗ[LaurentPolynomial ℤ] N}
    (h : ∀ X : C, f (of e X) = g (of e X)) : f = g :=
  LaurentAEval.hom_ext <| TriangulatedK0.hom_ext fun X => by simpa using h X

section UniversalProperty

variable (e) in
/-- **The homomorphism out of graded triangulated `K₀` induced by a shift-compatible invariant**,
as a map of `ℤ[q,q⁻¹]`-modules.  The invariant is compared against multiplication by `q` on the
target. -/
noncomputable def lift (a : TriangulatedK0.ShiftInvariant C e (laurentTAut ℤ N)) :
    LaurentTriangulatedK0 C e →ₗ[LaurentPolynomial ℤ] N :=
  LaurentAEval.lift a.lift fun x => by simpa using a.lift_mapEquiv x

@[simp]
lemma lift_of (a : TriangulatedK0.ShiftInvariant C e (laurentTAut ℤ N)) (X : C) :
    lift e a (of e X) = a.obj X := by
  rw [lift, ← ofTriangulatedK0_of, LaurentAEval.lift_of,
    TriangulatedK0.ShiftInvariant.lift_of]

variable (e N) in
/-- **The universal property of graded triangulated `K₀` over the Laurent coefficient ring.**  For
a `ℤ[q,q⁻¹]`-module `N`, the `ℤ[q,q⁻¹]`-linear maps out of `LaurentTriangulatedK0 C e` correspond
bijectively to the triangle-additive invariants whose value on `M{1}` is `q` times the value
on `M`. -/
noncomputable def liftEquiv :
    TriangulatedK0.ShiftInvariant C e (laurentTAut ℤ N) ≃
      (LaurentTriangulatedK0 C e →ₗ[LaurentPolynomial ℤ] N) where
  toFun := lift e
  invFun g :=
    (TriangulatedK0.ShiftInvariant.liftEquiv e (laurentTAut ℤ N)).symm
      ⟨g.toAddMonoidHom.comp (ofTriangulatedK0 e).toAddMonoidHom, fun x => by
        simpa using map_smul g (T 1 : LaurentPolynomial ℤ) (ofTriangulatedK0 e x)⟩
  left_inv a := by
    ext X
    simp
  right_inv g := hom_ext fun X => by simp

@[simp]
lemma liftEquiv_apply (a : TriangulatedK0.ShiftInvariant C e (laurentTAut ℤ N)) :
    liftEquiv e N a = lift e a :=
  (rfl)

@[simp]
lemma liftEquiv_symm_apply_obj (g : LaurentTriangulatedK0 C e →ₗ[LaurentPolynomial ℤ] N) (X : C) :
    ((liftEquiv e N).symm g).obj X = g (of e X) := by
  simp [liftEquiv]

end UniversalProperty

section Functoriality

variable {D : Type u'} [Category.{v'} D] [Preadditive D] [HasZeroObject D] [HasShift D ℤ]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D] [EssentiallySmall.{w'} D]
  {e' : D ≌ D} [e'.functor.CommShift ℤ] [e'.functor.IsTriangulated]
  {F : C ⥤ D} [F.CommShift ℤ] [F.IsTriangulated]

/-- **A triangulated functor commuting with the grading shifts induces a `ℤ[q,q⁻¹]`-linear map**
of graded triangulated Grothendieck groups.  The underlying homomorphism is
`TauCeti.TriangulatedK0.map F`; the commutation isomorphism is what makes it `q`-linear. -/
noncomputable def map (comm : e.functor ⋙ F ≅ F ⋙ e'.functor) :
    LaurentTriangulatedK0 C e →ₗ[LaurentPolynomial ℤ] LaurentTriangulatedK0 D e' :=
  LaurentAEval.lift ((ofTriangulatedK0 e').toAddMonoidHom.comp (TriangulatedK0.map F)) fun x => by
    simp [TriangulatedK0.map_shiftEquiv comm]

/-- On the underlying triangulated Grothendieck groups, the induced map is the map induced by the
functor. -/
@[simp]
theorem map_ofTriangulatedK0 (comm : e.functor ⋙ F ≅ F ⋙ e'.functor) (x : TriangulatedK0 C) :
    map comm (ofTriangulatedK0 e x) = ofTriangulatedK0 e' (TriangulatedK0.map F x) := by
  rw [map, LaurentAEval.lift_of, AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom]

@[simp]
lemma map_of (comm : e.functor ⋙ F ≅ F ⋙ e'.functor) (X : C) :
    map comm (of e X) = of e' (F.obj X) := by
  rw [← ofTriangulatedK0_of, map_ofTriangulatedK0, TriangulatedK0.map_of, ofTriangulatedK0_of]

variable (e) in
/-- **The identity functor induces the identity map** of graded triangulated Grothendieck
groups. -/
@[simp]
theorem map_id (comm : e.functor ⋙ 𝟭 C ≅ 𝟭 C ⋙ e.functor) : map comm = LinearMap.id :=
  hom_ext fun X => by simp

/-- **`TauCeti.LaurentTriangulatedK0.map` is functorial**: a composite of triangulated functors
commuting with the grading shifts induces the composite `ℤ[q,q⁻¹]`-linear map.  The induced map
does not depend on the commutation isomorphism, so any one for the composite may be used. -/
theorem map_comp {K : Type u''} [Category.{v''} K] [Preadditive K] [HasZeroObject K]
    [HasShift K ℤ] [∀ n : ℤ, (shiftFunctor K n).Additive] [Pretriangulated K]
    [EssentiallySmall.{w''} K] {e'' : K ≌ K} [e''.functor.CommShift ℤ]
    [e''.functor.IsTriangulated] {H : D ⥤ K} [H.CommShift ℤ] [H.IsTriangulated]
    (comm : e.functor ⋙ F ≅ F ⋙ e'.functor) (comm' : e'.functor ⋙ H ≅ H ⋙ e''.functor)
    (comm'' : e.functor ⋙ F ⋙ H ≅ (F ⋙ H) ⋙ e''.functor) :
    map comm'' = (map comm').comp (map comm) :=
  hom_ext fun X => by simp

/-- **The induced map does not depend on the commutation isomorphism.** -/
theorem map_congr (comm comm' : e.functor ⋙ F ≅ F ⋙ e'.functor) : map comm = map comm' :=
  hom_ext fun X => by simp

end Functoriality

section Invariance

variable {D : Type u'} [Category.{v'} D] [Preadditive D] [HasZeroObject D] [HasShift D ℤ]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D] [EssentiallySmall.{w'} D]
  {e' : D ≌ D} [e'.functor.CommShift ℤ] [e'.functor.IsTriangulated]
  (E : C ≌ D) [E.functor.CommShift ℤ] [E.functor.IsTriangulated]

/-- **A triangulated equivalence commuting with the grading shifts induces an isomorphism of
`ℤ[q,q⁻¹]`-modules.**  Graded triangulated `K₀` over the Laurent coefficient ring is therefore an
invariant of the graded triangulated category.  The underlying additive isomorphism is
`TauCeti.TriangulatedK0.mapEquiv E`. -/
noncomputable def mapEquiv (comm : e.functor ⋙ E.functor ≅ E.functor ⋙ e'.functor) :
    LaurentTriangulatedK0 C e ≃ₗ[LaurentPolynomial ℤ] LaurentTriangulatedK0 D e' :=
  ((ofTriangulatedK0 e).symm.trans
      ((TriangulatedK0.mapEquiv E).trans (ofTriangulatedK0 e'))).toLinearEquiv fun p x => by
    obtain ⟨z, rfl⟩ := (ofTriangulatedK0 e).surjective x
    have key : ∀ y : LaurentTriangulatedK0 C e,
        ((ofTriangulatedK0 e).symm.trans
          ((TriangulatedK0.mapEquiv E).trans (ofTriangulatedK0 e'))) y = map comm y := fun y => by
      obtain ⟨y, rfl⟩ := (ofTriangulatedK0 e).surjective y
      rw [AddEquiv.trans_apply, AddEquiv.symm_apply_apply, AddEquiv.trans_apply,
        map_ofTriangulatedK0]
      exact congrArg (ofTriangulatedK0 e') (DFunLike.congr_fun
        (TriangulatedK0.mapEquiv_toAddMonoidHom E) y)
    rw [key, key, map_smul]

@[simp]
lemma mapEquiv_of (comm : e.functor ⋙ E.functor ≅ E.functor ⋙ e'.functor) (X : C) :
    mapEquiv E comm (of e X) = of e' (E.functor.obj X) := by
  simp [mapEquiv, ← ofTriangulatedK0_of]

@[simp]
lemma mapEquiv_symm_of (comm : e.functor ⋙ E.functor ≅ E.functor ⋙ e'.functor) (Y : D) :
    (mapEquiv E comm).symm (of e' Y) = of e (E.inverse.obj Y) := by
  simp [mapEquiv, ← ofTriangulatedK0_of]

end Invariance

section Specialization

variable (ε : ℤˣ)

/-- **The shift/sign formula of specialized graded triangulated `K₀`.**  After specializing at
`q = ε`, the class of `M{1}` is `ε` times the class of `M`: at `q = -1` a shift changes the sign
of a class, and at `q = 1` it does not change the class. -/
@[simp]
theorem mk_of_shift_functor_obj (X : C) :
    LaurentSpecialization.mk ε (of e (e.functor.obj X)) =
      (ε : ℤ) • LaurentSpecialization.mk ε (of e X) := by
  rw [← T_one_smul_of, map_smul, LaurentSpecialization.mk_smul, laurentEval_T_one]

end Specialization

section ForgetGrading

variable {D : Type u'} [Category.{v'} D] [Preadditive D] [HasZeroObject D] [HasShift D ℤ]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D] [EssentiallySmall.{w'} D]
  {F : C ⥤ D} [F.CommShift ℤ] [F.IsTriangulated]

/-- **Forgetting the grading, through the specialization at `q = 1`.**  A triangulated functor `F`
into an ungraded pretriangulated category with `{1} ⋙ F ≅ F` induces a map from graded
triangulated `K₀`, specialized at `q = 1`, to triangulated `K₀` of the target, sending the
specialized class of `M` to the class of `F M`.  It is not an isomorphism in general. -/
noncomputable def forgetGrading (comm : e.functor ⋙ F ≅ F) :
    LaurentSpecialization (1 : ℤˣ) (LaurentTriangulatedK0 C e) →ₗ[ℤ] TriangulatedK0 D :=
  LaurentSpecialization.lift 1
    ((TriangulatedK0.map F).comp (ofTriangulatedK0 e).symm.toAddMonoidHom).toIntLinearMap
      fun x => by
        obtain ⟨z, rfl⟩ := (ofTriangulatedK0 e).surjective x
        simp [TriangulatedK0.map_shiftEquiv_of_commShift comm]

/-- **The forgetful map factors the map induced by `F` through the specialization at
`q = 1`.** -/
@[simp]
theorem forgetGrading_mk_ofTriangulatedK0 (comm : e.functor ⋙ F ≅ F) (x : TriangulatedK0 C) :
    forgetGrading comm (LaurentSpecialization.mk 1 (ofTriangulatedK0 e x)) =
      TriangulatedK0.map F x := by
  simp [forgetGrading]

/-- Forgetting the grading sends the specialized class of `M` to the class of `F M`. -/
@[simp]
theorem forgetGrading_mk_of (comm : e.functor ⋙ F ≅ F) (X : C) :
    forgetGrading comm (LaurentSpecialization.mk 1 (of e X)) = TriangulatedK0.of (F.obj X) := by
  rw [← ofTriangulatedK0_of, forgetGrading_mk_ofTriangulatedK0, TriangulatedK0.map_of]

end ForgetGrading

end LaurentTriangulatedK0

end TauCeti
