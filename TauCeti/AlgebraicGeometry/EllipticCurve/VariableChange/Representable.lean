/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.Algebra.Category.Ring.Basic
public import Mathlib.CategoryTheory.Yoneda
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Algebra.Ring.ULift
public import Mathlib.AlgebraicGeometry.EllipticCurve.VariableChange

/-!
# The coordinate algebra of Weierstrass changes of variables

The group-valued functor `R ↦ WeierstrassCurve.VariableChange R` has underlying functor
corepresented by `ℤ[u,r,s,t][u⁻¹]`. The equivalence here uses the native change of variables,
including over rings with nilpotents and the zero ring; it is not a classification on field
points. This supplies the coordinate algebra for the group acting on Weierstrass equations.

`WeierstrassCurve.VariableChange.specialize` classifies a change of variables and
`Universal.change` is the universal one. Their two inverse laws, together with naturality,
give `pointsCorepresentableBy`.
The functor takes values in groups using Mathlib's `VariableChange.mapHom`, so its product
is the native, noncommutative product, not addition on three translation coordinates.

More generally, for a commutative ring `A`, `CoordinateRingOver A = A[u,r,s,t][u⁻¹]` represents
admissible changes of variables over `A`-algebras: `liftOver` identifies ring homomorphisms
`CoordinateRingOver A →+* R` with pairs of a ring homomorphism `A →+* R` and a `VariableChange R`,
specializing `universalChange`, and `mapCoordinateRingOver` makes `CoordinateRingOver` functorial
in `A`. Taking `A = ℤ` recovers `Universal.CoordinateRing`.

## References

* T. Bauer, *Computation of the homotopy of the spectrum tmf*, §3, for the
  Weierstrass coordinate-change group. The native multiplication convention is retained here.
-/

public section

noncomputable section

universe u

open WeierstrassCurve WeierstrassCurve.VariableChange

namespace TauCeti.WeierstrassChange

namespace Universal

open MvPolynomial

/-- The coordinate algebra `ℤ[u,r,s,t][u⁻¹]`, with indices `0,1,2,3` for `u,r,s,t`. -/
abbrev CoordinateRing := Localization.Away (X (0 : Fin 4) : MvPolynomial (Fin 4) ℤ)

/-- The four coordinate functions on the scheme of changes of variables. -/
def coordinate (i : Fin 4) : CoordinateRing :=
  algebraMap (MvPolynomial (Fin 4) ℤ) CoordinateRing (X i)

@[simp]
theorem algebraMap_X (i : Fin 4) :
    algebraMap (MvPolynomial (Fin 4) ℤ) CoordinateRing (X i) = coordinate i := (rfl)

/-- The scaling coordinate is invertible in the coordinate algebra. -/
theorem isUnit_coordinate_zero : IsUnit (coordinate 0) :=
  IsLocalization.Away.algebraMap_isUnit (X (0 : Fin 4) : MvPolynomial (Fin 4) ℤ)

/-- The universal admissible change of variables over `ℤ[u,r,s,t][u⁻¹]`. -/
def change : VariableChange CoordinateRing :=
  ⟨isUnit_coordinate_zero.unit, coordinate 1, coordinate 2, coordinate 3⟩

@[simp] theorem change_u : (change.u : CoordinateRing) = coordinate 0 :=
  isUnit_coordinate_zero.unit_spec

@[simp] theorem change_r : change.r = coordinate 1 := (rfl)

@[simp] theorem change_s : change.s = coordinate 2 := (rfl)

@[simp] theorem change_t : change.t = coordinate 3 := (rfl)

variable {R S : Type*} [CommRing R] [CommRing S]

/-- A map from the coordinate algebra is determined by the four coordinate functions;
the inverse of the scaling coordinate requires no extra datum. -/
@[ext]
theorem ringHom_ext {f g : CoordinateRing →+* R}
    (h : ∀ i, f (coordinate i) = g (coordinate i)) : f = g := by
  apply IsLocalization.ringHom_ext (.powers (X (0 : Fin 4) : MvPolynomial (Fin 4) ℤ))
  exact MvPolynomial.ringHom_ext' (RingHom.ext_int _ _) h

end Universal

end TauCeti.WeierstrassChange

namespace WeierstrassCurve.VariableChange

open MvPolynomial TauCeti.WeierstrassChange.Universal

variable {R S : Type*} [CommRing R] [CommRing S]

/-- The classifying homomorphism of a change of variables: send `u,r,s,t` to its coefficients. -/
def specialize (C : VariableChange R) : CoordinateRing →+* R :=
  IsLocalization.Away.lift (X (0 : Fin 4) : MvPolynomial (Fin 4) ℤ)
    (g := eval₂Hom (Int.castRingHom R) ![(C.u : R), C.r, C.s, C.t]) (by simp)

/-- Specialization evaluates the four coordinates at the four native coefficients. -/
@[simp]
theorem specialize_coordinate (C : VariableChange R) (i : Fin 4) :
    specialize C (coordinate i) = ![(C.u : R), C.r, C.s, C.t] i := by
  simp [specialize, coordinate, IsLocalization.Away.lift_eq, -algebraMap_X]

/-- Every change of variables is the image of the universal one under its classifying map. -/
@[simp]
theorem map_specialize (C : VariableChange R) : change.map (specialize C) = C := by
  ext <;> simp

/-- Classifying maps commute with coefficient extension. -/
@[simp]
theorem specialize_map (C : VariableChange R) (f : R →+* S) :
    specialize (C.map f) = f.comp (specialize C) := by
  apply TauCeti.WeierstrassChange.Universal.ringHom_ext
  intro i
  fin_cases i <;> simp

end WeierstrassCurve.VariableChange

namespace TauCeti.WeierstrassChange

namespace Universal

variable {R S : Type*} [CommRing R] [CommRing S]

/-- The universal change is classified by the identity on its coordinate algebra. -/
@[simp]
theorem specialize_change : specialize change = RingHom.id CoordinateRing := by
  apply ringHom_ext
  intro i
  fin_cases i <;> simp

/-- Ring homomorphisms from the coordinate algebra classify native changes of variables. -/
def ringHomEquiv (R : Type*) [CommRing R] : (CoordinateRing →+* R) ≃ VariableChange R where
  toFun f := change.map f
  invFun := specialize
  left_inv f := by simp
  right_inv := map_specialize

@[simp]
theorem ringHomEquiv_apply (f : CoordinateRing →+* R) : ringHomEquiv R f = change.map f := (rfl)

@[simp]
theorem ringHomEquiv_symm_apply (C : VariableChange R) :
    (ringHomEquiv R).symm C = specialize C := (rfl)

/-- The represented point associated to a composite is obtained by mapping the original
point along the second ring homomorphism. -/
theorem ringHomEquiv_comp (f : CoordinateRing →+* R) (g : R →+* S) :
    ringHomEquiv S (g.comp f) = (ringHomEquiv R f).map g :=
  (change.map_map f g).symm

end Universal

open CategoryTheory

/-- Changes of variables, with their native noncommutative group law, form a group-valued
functor of the coefficient ring. Its body is exposed so that its value types are the native
groups `VariableChange R`, without transporting points across object equalities. -/
@[expose] def pointsFunctor : CommRingCat.{u} ⥤ GrpCat.{u} where
  obj R := GrpCat.of (VariableChange R)
  map f := GrpCat.ofHom (mapHom f.hom)
  map_id _ := GrpCat.hom_ext (MonoidHom.ext fun C ↦ C.map_id)
  map_comp f g := GrpCat.hom_ext (MonoidHom.ext fun C ↦ (C.map_map f.hom g.hom).symm)

/-- The points functor acts by the native coefficient map. -/
@[simp]
theorem pointsFunctor_map_apply {R S : CommRingCat.{u}} (f : R ⟶ S)
    (C : VariableChange R) : pointsFunctor.map f C = C.map f.hom := (rfl)

/-- The underlying type-valued functor of Weierstrass changes of variables is corepresented
by `ℤ[u,r,s,t][u⁻¹]`. The group-scheme structure is not constructed here. -/
def pointsCorepresentableBy :
    (pointsFunctor.{u} ⋙ forget GrpCat).CorepresentableBy
      (CommRingCat.of (ULift.{u} Universal.CoordinateRing)) where
  homEquiv {R} := (ConcreteCategory.homEquiv (C := CommRingCat)).trans <|
    ({ toFun f := f.comp ULift.ringEquiv.symm.toRingHom
       invFun f := f.comp ULift.ringEquiv.toRingHom
       left_inv f := by ext x; rfl
       right_inv f := by ext x; rfl } :
      (ULift.{u} Universal.CoordinateRing →+* R) ≃ (Universal.CoordinateRing →+* R)).trans
        (Universal.ringHomEquiv R)
  homEquiv_comp g f := by
    -- Unwrap coefficient extension and use naturality of the ring-level classification.
    dsimp [ConcreteCategory.homEquiv, pointsFunctor]
    exact Universal.ringHomEquiv_comp (f.hom.comp ULift.ringEquiv.symm.toRingHom) g.hom

/-- The representing equivalence evaluates the universal change along the given ring map. -/
-- Not a simp lemma: the composite functor's object type is not in simp normal form.
theorem pointsCorepresentableBy_homEquiv {R : CommRingCat.{u}}
    (f : CommRingCat.of (ULift.{u} Universal.CoordinateRing) ⟶ R) :
    pointsCorepresentableBy.homEquiv f =
      Universal.change.map (f.hom.comp ULift.ringEquiv.symm.toRingHom) := (rfl)

/-- The inverse representing equivalence is the classifying homomorphism. -/
-- As above, the composite functor's object type prevents a simp-normal-form statement.
theorem pointsCorepresentableBy_homEquiv_symm {R : CommRingCat.{u}}
    (C : VariableChange R) :
    pointsCorepresentableBy.homEquiv.symm C =
      CommRingCat.ofHom (C.specialize.comp ULift.ringEquiv.toRingHom) := (rfl)

/-- The underlying functor of changes of variables is corepresentable by its coordinate
algebra; the representing equivalence is `pointsCorepresentableBy`. -/
instance : (pointsFunctor.{u} ⋙ forget GrpCat).IsCorepresentable :=
  pointsCorepresentableBy.isCorepresentable

section Relative

open MvPolynomial

variable {A B D R S : Type*} [CommRing A] [CommRing B] [CommRing D] [CommRing R] [CommRing S]

/-- The relative coordinate algebra `A[u,r,s,t][u⁻¹]` of admissible Weierstrass changes of
variables over `A`, with indices `0,1,2,3` for `u,r,s,t`. Taking `A = ℤ` gives
`Universal.CoordinateRing`. -/
abbrev CoordinateRingOver (A : Type*) [CommRing A] :=
  Localization.Away (X (0 : Fin 4) : MvPolynomial (Fin 4) A)

instance [IsDomain A] : IsDomain (CoordinateRingOver A) :=
  Localization.Away.isDomain (X_ne_zero (R := A) (0 : Fin 4))

/-- The four coordinate functions `u,r,s,t` in the relative coordinate algebra `A[u,r,s,t][u⁻¹]`. -/
def coordinateOver (i : Fin 4) : CoordinateRingOver A :=
  algebraMap (MvPolynomial (Fin 4) A) (CoordinateRingOver A) (X i)

/-- `coordinateOver i` is the image of the variable `X i` in the localization. -/
-- Not `@[simp]`: for `A = ℤ` this LHS already simplifies to `Universal.coordinate i` via
-- `Universal.algebraMap_X`.
theorem algebraMap_X_coordinateRingOver (i : Fin 4) :
    algebraMap (MvPolynomial (Fin 4) A) (CoordinateRingOver A) (X i) = coordinateOver i := (rfl)

/-- The scaling coordinate `u` is invertible in `A[u,r,s,t][u⁻¹]`. -/
theorem isUnit_coordinateOver_zero : IsUnit (coordinateOver (A := A) 0) :=
  IsLocalization.Away.algebraMap_isUnit (X (0 : Fin 4) : MvPolynomial (Fin 4) A)

/-- The universal admissible change of variables over `A[u,r,s,t][u⁻¹]`. -/
def universalChange : VariableChange (CoordinateRingOver A) :=
  ⟨isUnit_coordinateOver_zero.unit, coordinateOver 1, coordinateOver 2, coordinateOver 3⟩

@[simp]
theorem universalChange_u :
    ((universalChange (A := A)).u : CoordinateRingOver A) = coordinateOver 0 :=
  isUnit_coordinateOver_zero.unit_spec

@[simp]
theorem universalChange_r : (universalChange (A := A)).r = coordinateOver 1 := (rfl)

@[simp]
theorem universalChange_s : (universalChange (A := A)).s = coordinateOver 2 := (rfl)

@[simp]
theorem universalChange_t : (universalChange (A := A)).t = coordinateOver 3 := (rfl)

/-- Two ring homomorphisms out of `A[u,r,s,t][u⁻¹]` agree when they agree on `A` and on the four
coordinates `u,r,s,t`. -/
theorem coordinateRingOver_ringHom_ext {f g : CoordinateRingOver A →+* R}
    (hA : f.comp (algebraMap A (CoordinateRingOver A)) =
      g.comp (algebraMap A (CoordinateRingOver A)))
    (hX : ∀ i, f (coordinateOver i) = g (coordinateOver i)) : f = g := by
  apply IsLocalization.ringHom_ext (.powers (X (0 : Fin 4) : MvPolynomial (Fin 4) A))
  refine MvPolynomial.ringHom_ext' ?_ hX
  ext a
  exact RingHom.congr_fun hA a

/-- A ring homomorphism out of `A[u,r,s,t][u⁻¹]` is determined by its restriction to `A` and by
its base change of `universalChange`. -/
theorem ringHom_ext_universalChange {f g : CoordinateRingOver A →+* R}
    (hA : f.comp (algebraMap A (CoordinateRingOver A)) =
      g.comp (algebraMap A (CoordinateRingOver A)))
    (hC : universalChange.map f = universalChange.map g) : f = g := by
  refine coordinateRingOver_ringHom_ext hA fun i ↦ ?_
  fin_cases i
  · simpa using congrArg (fun C : VariableChange R ↦ (C.u : R)) hC
  · simpa using congrArg VariableChange.r hC
  · simpa using congrArg VariableChange.s hC
  · simpa using congrArg VariableChange.t hC

/-- **`A[u,r,s,t][u⁻¹]` represents admissible changes of variables over `A`-algebras**: pairs of
a ring homomorphism `A →+* R` and a change of variables `C : VariableChange R` correspond to ring
homomorphisms `CoordinateRingOver A →+* R`. -/
def liftOver : (A →+* R) × VariableChange R ≃ (CoordinateRingOver A →+* R) where
  toFun p := IsLocalization.Away.lift (X (0 : Fin 4) : MvPolynomial (Fin 4) A)
    (g := eval₂Hom p.1 ![(p.2.u : R), p.2.r, p.2.s, p.2.t]) (by simp)
  invFun f := (f.comp (algebraMap A (CoordinateRingOver A)), universalChange.map f)
  left_inv p := by
    refine Prod.ext (RingHom.ext fun a ↦ ?_) ?_
    · simp [IsScalarTower.algebraMap_apply A (MvPolynomial (Fin 4) A) (CoordinateRingOver A),
        IsLocalization.Away.lift_eq]
    · ext <;> simp [coordinateOver, IsLocalization.Away.lift_eq]
  right_inv f := by
    refine coordinateRingOver_ringHom_ext (RingHom.ext fun a ↦ ?_) fun i ↦ ?_
    · simp [IsScalarTower.algebraMap_apply A (MvPolynomial (Fin 4) A) (CoordinateRingOver A),
        IsLocalization.Away.lift_eq]
    · fin_cases i <;> simp [coordinateOver, IsLocalization.Away.lift_eq]

/-- The ring homomorphism out of `A` classified by `f : CoordinateRingOver A →+* R` is its
restriction along `algebraMap`. -/
@[simp]
theorem liftOver_symm_apply_fst (f : CoordinateRingOver A →+* R) :
    (liftOver.symm f).1 = f.comp (algebraMap A (CoordinateRingOver A)) := (rfl)

/-- The change of variables classified by `f : CoordinateRingOver A →+* R` is the base change of
`universalChange` along `f`. -/
@[simp]
theorem liftOver_symm_apply_snd (f : CoordinateRingOver A →+* R) :
    (liftOver.symm f).2 = universalChange.map f := (rfl)

/-- `liftOver (f, C)` restricts along `algebraMap` to `f`. -/
@[simp]
theorem liftOver_comp_algebraMap (p : (A →+* R) × VariableChange R) :
    (liftOver p).comp (algebraMap A (CoordinateRingOver A)) = p.1 :=
  congrArg Prod.fst (liftOver.left_inv p)

/-- `liftOver (f, C)` agrees with `f` on `A`. -/
@[simp]
theorem liftOver_algebraMap (p : (A →+* R) × VariableChange R) (a : A) :
    liftOver p (algebraMap A (CoordinateRingOver A) a) = p.1 a :=
  RingHom.congr_fun (liftOver_comp_algebraMap p) a

/-- `liftOver (f, C)` specializes `universalChange` to `C`. -/
@[simp]
theorem map_liftOver_universalChange (p : (A →+* R) × VariableChange R) :
    universalChange.map (liftOver p) = p.2 :=
  congrArg Prod.snd (liftOver.left_inv p)

/-- `liftOver (f, C)` evaluates the four coordinates `u,r,s,t` at the coefficients of `C`. -/
@[simp]
theorem liftOver_coordinateOver (p : (A →+* R) × VariableChange R) (i : Fin 4) :
    liftOver p (coordinateOver i) = ![(p.2.u : R), p.2.r, p.2.s, p.2.t] i := by
  simp [liftOver, coordinateOver, IsLocalization.Away.lift_eq]

/-- `liftOver (f, C)` sends the inverse scaling coordinate `u⁻¹` to `C.u⁻¹`. -/
@[simp]
theorem liftOver_universalChange_u_inv (p : (A →+* R) × VariableChange R) :
    liftOver p ↑(universalChange (A := A)).u⁻¹ = ↑p.2.u⁻¹ := by
  have h := congrArg (fun C : VariableChange R ↦ (C.u⁻¹ : Rˣ).val)
    (map_liftOver_universalChange p)
  simpa [VariableChange.map] using h

/-- The canonical pair `(algebraMap, universalChange)` is classified by the identity on
`CoordinateRingOver A`. -/
@[simp]
theorem liftOver_algebraMap_universalChange :
    liftOver (algebraMap A (CoordinateRingOver A), universalChange) =
      RingHom.id (CoordinateRingOver A) :=
  liftOver.right_inv (RingHom.id (CoordinateRingOver A))

/-- The structure map `A →+* CoordinateRingOver A` is injective for every commutative ring `A`, as
evaluating at the identity change of variables retracts it. -/
theorem algebraMap_coordinateRingOver_injective :
    Function.Injective (algebraMap A (CoordinateRingOver A)) :=
  Function.LeftInverse.injective (liftOver_algebraMap (RingHom.id A, 1))

instance [CharZero A] : CharZero (CoordinateRingOver A) :=
  charZero_of_inj_zero fun n hn ↦ by
    simpa using congrArg (liftOver (RingHom.id A, 1)) hn

/-- Naturality of `liftOver` in the target ring: post-composing `liftOver (f, C)` with `g` gives
`liftOver (g ∘ f, C.map g)`. -/
theorem comp_liftOver (g : R →+* S) (p : (A →+* R) × VariableChange R) :
    g.comp (liftOver p) = liftOver (g.comp p.1, p.2.map g) := by
  refine ringHom_ext_universalChange ?_ ?_
  · rw [RingHom.comp_assoc, liftOver_comp_algebraMap, liftOver_comp_algebraMap]
  · rw [← VariableChange.map_map, map_liftOver_universalChange, map_liftOver_universalChange]

/-- Over `ℤ`, `universalChange` coincides with `Universal.change`. -/
theorem universalChange_int : universalChange (A := ℤ) = Universal.change := (rfl)

/-- Over `ℤ`, `coordinateOver` coincides with `Universal.coordinate`. -/
theorem coordinateOver_int (i : Fin 4) : coordinateOver (A := ℤ) i = Universal.coordinate i := (rfl)

/-- Over `ℤ`, `liftOver` coincides with `VariableChange.specialize`. -/
theorem liftOver_intCastRingHom (C : VariableChange R) :
    liftOver (Int.castRingHom R, C) = C.specialize := by
  refine Universal.ringHom_ext fun i ↦ ?_
  rw [← coordinateOver_int, liftOver_coordinateOver, coordinateOver_int, C.specialize_coordinate]

/-- Functoriality of `CoordinateRingOver` in the base ring: a ring homomorphism `f : A →+* B`
induces `A[u,r,s,t][u⁻¹] →+* B[u,r,s,t][u⁻¹]` acting as `f` on `A` and preserving `u,r,s,t`. -/
def mapCoordinateRingOver (f : A →+* B) : CoordinateRingOver A →+* CoordinateRingOver B :=
  liftOver ((algebraMap B (CoordinateRingOver B)).comp f, universalChange)

/-- `mapCoordinateRingOver f` restricts to `algebraMap ∘ f` on `A`. -/
@[simp]
theorem mapCoordinateRingOver_comp_algebraMap (f : A →+* B) :
    (mapCoordinateRingOver f).comp (algebraMap A (CoordinateRingOver A)) =
      (algebraMap B (CoordinateRingOver B)).comp f :=
  liftOver_comp_algebraMap _

/-- `mapCoordinateRingOver f` acts by `f` on elements from `A`. -/
@[simp]
theorem mapCoordinateRingOver_algebraMap (f : A →+* B) (a : A) :
    mapCoordinateRingOver f (algebraMap A (CoordinateRingOver A) a) =
      algebraMap B (CoordinateRingOver B) (f a) :=
  liftOver_algebraMap _ a

/-- `mapCoordinateRingOver f` preserves the universal change of variables. -/
@[simp]
theorem map_mapCoordinateRingOver_universalChange (f : A →+* B) :
    universalChange.map (mapCoordinateRingOver f) = universalChange :=
  map_liftOver_universalChange _

/-- `mapCoordinateRingOver f` preserves each of the four coordinates `u,r,s,t`. -/
@[simp]
theorem mapCoordinateRingOver_coordinateOver (f : A →+* B) (i : Fin 4) :
    mapCoordinateRingOver f (coordinateOver i) = coordinateOver i := by
  fin_cases i <;> simp [mapCoordinateRingOver]

/-- `mapCoordinateRingOver` preserves identity homomorphisms. -/
@[simp]
theorem mapCoordinateRingOver_id :
    mapCoordinateRingOver (RingHom.id A) = RingHom.id (CoordinateRingOver A) :=
  liftOver_algebraMap_universalChange

/-- `mapCoordinateRingOver` preserves composition of ring homomorphisms. -/
@[simp]
theorem mapCoordinateRingOver_comp (g : B →+* D) (f : A →+* B) :
    (mapCoordinateRingOver g).comp (mapCoordinateRingOver f) =
      mapCoordinateRingOver (g.comp f) := by
  refine ringHom_ext_universalChange ?_ ?_
  · ext a
    simp
  · rw [← VariableChange.map_map, map_mapCoordinateRingOver_universalChange,
      map_mapCoordinateRingOver_universalChange, map_mapCoordinateRingOver_universalChange]

@[simp]
theorem mapCoordinateRingOver_mapCoordinateRingOver (g : B →+* D) (f : A →+* B)
    (x : CoordinateRingOver A) :
    mapCoordinateRingOver g (mapCoordinateRingOver f x) = mapCoordinateRingOver (g.comp f) x :=
  RingHom.congr_fun (mapCoordinateRingOver_comp g f) x

end Relative

end TauCeti.WeierstrassChange
