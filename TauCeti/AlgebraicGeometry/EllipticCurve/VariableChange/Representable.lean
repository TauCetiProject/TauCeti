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

More generally, over an arbitrary commutative coefficient ring `B`, the ring
`ChangeRing B = B[u, u⁻¹, r, s, t]` is the coordinate ring of `Spec B × G` for the group scheme `G`
of changes of variables: its homomorphisms classify pairs of a homomorphism out of `B` and a change
of variables (`ChangeRing.lift`, with universal change `ChangeRing.universalChange B`). The
coefficient extension `ChangeRing.map` is functorial (`ChangeRing.map_id`, `ChangeRing.map_comp`),
and `ChangeRing.pushoutLift` is the universal property of
`B'[u, u⁻¹, r, s, t] = B' ⊗_B B[u, u⁻¹, r, s, t]` as a pushout. For `B = ℤ` this is the
coordinate algebra `Universal.CoordinateRing`; for `B = ℤ[a₁, ⋯, a₆]` it is the ring of arrows of
the Weierstrass Hopf algebroid.

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

end TauCeti.WeierstrassChange

namespace TauCeti.WeierstrassChange

open MvPolynomial

variable {B B' R : Type*} [CommRing B] [CommRing B'] [CommRing R]

/-! ### The ring `B[u, u⁻¹, r, s, t]` -/

variable (B) in
/-- The ring `B[u, u⁻¹, r, s, t]`, the localization of `B[u, r, s, t]` away from `u`, with indices
`0, 1, 2, 3` for `u, r, s, t`. It is the coordinate ring of `Spec B × G`, for the group scheme `G`
of admissible changes of variables of Weierstrass curves. -/
abbrev ChangeRing : Type _ := Localization.Away (X 0 : MvPolynomial (Fin 4) B)

namespace ChangeRing

variable (B) in
/-- The universal change of variables `(u, r, s, t)` over `B[u, u⁻¹, r, s, t]`. -/
def universalChange : VariableChange (ChangeRing B) :=
  ⟨(IsLocalization.Away.algebraMap_isUnit (X 0 : MvPolynomial (Fin 4) B)).unit,
    algebraMap (MvPolynomial (Fin 4) B) _ (X 1), algebraMap (MvPolynomial (Fin 4) B) _ (X 2),
    algebraMap (MvPolynomial (Fin 4) B) _ (X 3)⟩

variable (B) in
@[simp]
theorem universalChange_u :
    ((universalChange B).u : ChangeRing B) = algebraMap (MvPolynomial (Fin 4) B) _ (X 0) :=
  IsUnit.unit_spec _

variable (B) in
@[simp]
theorem universalChange_r :
    (universalChange B).r = algebraMap (MvPolynomial (Fin 4) B) _ (X 1) :=
  (rfl)

variable (B) in
@[simp]
theorem universalChange_s :
    (universalChange B).s = algebraMap (MvPolynomial (Fin 4) B) _ (X 2) :=
  (rfl)

variable (B) in
@[simp]
theorem universalChange_t :
    (universalChange B).t = algebraMap (MvPolynomial (Fin 4) B) _ (X 3) :=
  (rfl)

/-- The homomorphism `B[u, r, s, t] →+* R` extending `f` and sending `u, r, s, t` to the
coefficients of `C`. -/
private def evalHom (f : B →+* R) (C : VariableChange R) : MvPolynomial (Fin 4) B →+* R :=
  eval₂Hom f ![(C.u : R), C.r, C.s, C.t]

private theorem isUnit_evalHom_X (f : B →+* R) (C : VariableChange R) :
    IsUnit (evalHom f C (X 0)) := by
  simp [evalHom]

/-- **Ring homomorphisms out of `B[u, u⁻¹, r, s, t]`** classify pairs of a ring homomorphism out
of `B` and a change of variables: a homomorphism `k` corresponds to its restriction to `B` and
to the base change of `universalChange B` along `k`. -/
def lift : (B →+* R) × VariableChange R ≃ (ChangeRing B →+* R) where
  toFun p := IsLocalization.Away.lift (X 0) (isUnit_evalHom_X p.1 p.2)
  invFun k := (k.comp (algebraMap B _), (universalChange B).map k)
  left_inv p := by
    refine Prod.ext (RingHom.ext fun b ↦ ?_) ?_
    · simp [IsScalarTower.algebraMap_apply B (MvPolynomial (Fin 4) B) (ChangeRing B),
        evalHom]
    · ext <;> simp [evalHom]
  right_inv k := by
    refine IsLocalization.ringHom_ext (.powers (X 0 : MvPolynomial (Fin 4) B)) ?_
    refine MvPolynomial.ringHom_ext (fun b ↦ ?_) fun i ↦ ?_
    · simp [evalHom,
        IsScalarTower.algebraMap_apply B (MvPolynomial (Fin 4) B) (ChangeRing B)]
    · fin_cases i <;> simp [evalHom]

/-- `lift p` restricts to `p.1` on `B`. -/
@[simp]
theorem lift_comp_algebraMap (p : (B →+* R) × VariableChange R) :
    (lift p).comp (algebraMap B _) = p.1 :=
  congrArg Prod.fst (lift.left_inv p)

/-- `lift p` agrees with `p.1` on `B`. -/
@[simp]
theorem lift_algebraMap (p : (B →+* R) × VariableChange R) (b : B) :
    lift p (algebraMap B _ b) = p.1 b :=
  RingHom.congr_fun (lift_comp_algebraMap p) b

/-- `lift p` carries the universal change of variables to `p.2`. -/
@[simp]
theorem map_lift (p : (B →+* R) × VariableChange R) :
    (universalChange B).map (lift p) = p.2 :=
  congrArg Prod.snd (lift.left_inv p)

@[simp]
theorem lift_symm_apply (k : ChangeRing B →+* R) :
    lift.symm k = (k.comp (algebraMap B _), (universalChange B).map k) :=
  (rfl)

/-- A ring homomorphism out of `B[u, u⁻¹, r, s, t]` is determined by its restriction to `B` and
the change of variables it classifies. -/
theorem ringHom_ext {k k' : ChangeRing B →+* R}
    (h₁ : k.comp (algebraMap B _) = k'.comp (algebraMap B _))
    (h₂ : (universalChange B).map k = (universalChange B).map k') : k = k' :=
  lift.symm.injective (Prod.ext h₁ h₂)

/-! ### Coefficient extension and the pushout `B' ⊗_B B[u, u⁻¹, r, s, t]` -/

/-- The coefficient extension `B[u, u⁻¹, r, s, t] →+* B'[u, u⁻¹, r, s, t]` of `f : B →+* B'`. -/
def map (f : B →+* B') : ChangeRing B →+* ChangeRing B' :=
  lift ((algebraMap B' _).comp f, universalChange B')

@[simp]
theorem map_comp_algebraMap (f : B →+* B') :
    (map f).comp (algebraMap B _) = (algebraMap B' _).comp f :=
  lift_comp_algebraMap _

@[simp]
theorem map_algebraMap (f : B →+* B') (b : B) :
    map f (algebraMap B _ b) = algebraMap B' _ (f b) :=
  lift_algebraMap _ b

@[simp]
theorem universalChange_map_map (f : B →+* B') :
    (universalChange B).map (map f) = universalChange B' :=
  map_lift _

variable (B) in
/-- Coefficient extension along the identity is the identity. -/
@[simp]
theorem map_id : map (RingHom.id B) = RingHom.id (ChangeRing B) :=
  ringHom_ext (by simp) (by simp)

/-- Coefficient extension is compatible with composition. -/
@[simp]
theorem map_comp {B'' : Type*} [CommRing B''] (g : B' →+* B'') (f : B →+* B') :
    map (g.comp f) = (map g).comp (map f) :=
  ringHom_ext (RingHom.ext fun b ↦ by simp) (by simp [← VariableChange.map_map])

/-- **The universal property of `B'[u, u⁻¹, r, s, t]` as the pushout `B' ⊗_B B[u, u⁻¹, r, s, t]`**
of `f : B →+* B'` and the inclusion `algebraMap`: ring homomorphisms out of it correspond to
pairs `(g, h)` of ring homomorphisms out of `B'` and out of `B[u, u⁻¹, r, s, t]` with
`g ∘ f = h ∘ algebraMap`, by restriction along `algebraMap` and along `map f`. -/
def pushoutLift (f : B →+* B') :
    {p : (B' →+* R) × (ChangeRing B →+* R) // p.1.comp f = p.2.comp (algebraMap B _)} ≃
      (ChangeRing B' →+* R) where
  toFun p := lift (p.1.1, (universalChange B).map p.1.2)
  invFun k := ⟨(k.comp (algebraMap B' _), k.comp (map f)), by
    rw [RingHom.comp_assoc, RingHom.comp_assoc, map_comp_algebraMap]⟩
  left_inv p := by
    refine Subtype.ext (Prod.ext (lift_comp_algebraMap _) (ringHom_ext ?_ ?_))
    · rw [RingHom.comp_assoc, map_comp_algebraMap, ← RingHom.comp_assoc, lift_comp_algebraMap,
        p.2]
    · rw [← VariableChange.map_map, universalChange_map_map, map_lift]
  right_inv k := ringHom_ext (lift_comp_algebraMap _) (by
    rw [map_lift]
    dsimp only
    rw [← VariableChange.map_map, universalChange_map_map])

variable (f : B →+* B')
  (p : {p : (B' →+* R) × (ChangeRing B →+* R) // p.1.comp f = p.2.comp (algebraMap B _)})

/-- `pushoutLift f (g, h)` restricts to `g` along `algebraMap`. -/
@[simp]
theorem pushoutLift_comp_algebraMap : (pushoutLift f p).comp (algebraMap B' _) = p.1.1 :=
  congrArg (fun q ↦ q.1.1) ((pushoutLift f).left_inv p)

/-- `pushoutLift f (g, h)` restricts to `h` along `map f`. -/
@[simp]
theorem pushoutLift_comp_map : (pushoutLift f p).comp (map f) = p.1.2 :=
  congrArg (fun q ↦ q.1.2) ((pushoutLift f).left_inv p)

@[simp]
theorem pushoutLift_algebraMap (b : B') : pushoutLift f p (algebraMap B' _ b) = p.1.1 b :=
  RingHom.congr_fun (pushoutLift_comp_algebraMap f p) b

@[simp]
theorem pushoutLift_map (x : ChangeRing B) : pushoutLift f p (map f x) = p.1.2 x :=
  RingHom.congr_fun (pushoutLift_comp_map f p) x

/-- `pushoutLift f (g, h)` carries the universal change of variables over `B'` to the change
classified by `h`. -/
@[simp]
theorem universalChange_map_pushoutLift :
    (universalChange B').map (pushoutLift f p) = (universalChange B).map p.1.2 :=
  map_lift _

end ChangeRing

end TauCeti.WeierstrassChange
