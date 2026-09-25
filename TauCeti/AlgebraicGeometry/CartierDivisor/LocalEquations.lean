/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.CartierDivisor.Basic
public import Mathlib.Topology.Sheaves.AddCommGrpCat
public import Mathlib.Topology.Sheaves.LocallySurjective

/-!
# Local equations for Cartier divisors

A Cartier divisor on an integral scheme is a section of the quotient sheaf
`𝒦_X^× / 𝒪_X^×`. This file extracts the local-equation description from that quotient:
every section is locally represented by a nonzero rational function, and two representatives
differ by a unique regular unit.

## Main declarations

* `Scheme.exists_local_equation` lifts a Cartier-divisor section to a rational unit on a
  neighbourhood of any chosen point;
* `Scheme.CartierDivisor.exists_local_equation_cover` chooses local equations on an open cover
  indexed by the points of the scheme;
* `Scheme.toCartierDivisorSheaf_app_eq_iff` characterizes equality of two representatives by
  their difference coming from a regular unit;
* `Scheme.CartierDivisor.existsUnique_transitionUnit` applies that characterization on the
  overlap of two local equations of a global Cartier divisor;
* `Scheme.rationalUnitClass_eq_rationalUnitClass_iff` restates it for nonzero rational functions:
  two of them have the same class over a nonempty open subset `U` exactly when they differ by a
  unit of `Γ(X, U)`;
* `Scheme.CartierDivisor.IsLocalEquationAt D x f`: `f` is a local equation of `D` at the point
  `x`; every point has one (`Scheme.CartierDivisor.exists_isLocalEquationAt`), two of them differ
  by a unit of the local ring `𝒪_{X,x}`
  (`Scheme.CartierDivisor.IsLocalEquationAt.exists_unit_mul_eq`), and they only depend on the
  divisor near `x` (`Scheme.CartierDivisor.isLocalEquationAt_congr`).

The sheaf `𝒪_X(D)` is built in `TauCeti/AlgebraicGeometry/CartierDivisor/Sheaf.lean` as the
subsheaf of `𝒦_X` cut out by the local equations, through
`Scheme.CartierDivisor.IsLocalEquationAt`. The transition units record how two local equations of
`D` change into one another on an overlap. The construction follows Hartshorne, *Algebraic
Geometry*, II.6, and the Stacks Project, *Divisors*, Tag 02AR. No formalization is vendored: local
lifting is Mathlib's
characterization of epimorphisms of sheaves as locally surjective maps, while the transition-unit
criterion uses left exactness of sections and the cokernel exact sequence.
-/

public section

open CategoryTheory Limits TopologicalSpace AlgebraicGeometry Opposite

namespace TauCeti

namespace AlgebraicGeometry

universe u

noncomputable section

namespace Scheme

variable (X : Scheme.{u}) [IsIntegral X]

/-- Every local Cartier-divisor section has a rational equation near each point of its domain.

The representative is a section of `𝒦_X^×` on a smaller open neighbourhood, and its image in
`𝒦_X^× / 𝒪_X^×` is the restriction of the given Cartier-divisor section. -/
theorem exists_local_equation {U : X.Opens}
    (D : ((cartierDivisorSheaf X).obj.obj (op U) : Type u)) (x : X) (hx : x ∈ U) :
    ∃ (V : X.Opens) (hVU : V ≤ U), x ∈ V ∧
      ∃ f : Additive (((rationalFunctionsRing X).presheaf.obj (op V))ˣ),
        ((toCartierDivisorSheaf X).hom.app (op V)).hom f = D |_ V := by
  have hlocal : TopCat.Presheaf.IsLocallySurjective (toCartierDivisorSheaf X).hom :=
    (TopCat.Sheaf.isLocallySurjective_iff_epi (toCartierDivisorSheaf X)).mpr inferInstance
  obtain ⟨V, hVU, ⟨f, hf⟩, hxV⟩ :=
    (TopCat.Presheaf.isLocallySurjective_iff (toCartierDivisorSheaf X).hom).mp hlocal
      U D x hx
  exact ⟨V, hVU, hxV, f, hf⟩

/-- Two rational-unit sections have the same image in the Cartier-divisor sheaf exactly when
their difference is the image of a regular unit.

The unit is unique by `toRationalUnitSheaf_app_injective`; the explicit existence-and-uniqueness
form is `existsUnique_regularUnit_sub_of_toCartierDivisorSheaf_app_eq`. Multiplication and
division of units are written as addition and subtraction because the unit sheaves are regarded
as sheaves of additive commutative groups. -/
theorem toCartierDivisorSheaf_app_eq_iff {U : X.Opens}
    (f g : Additive (((rationalFunctionsRing X).presheaf.obj (op U))ˣ)) :
    ((toCartierDivisorSheaf X).hom.app (op U)).hom f =
        ((toCartierDivisorSheaf X).hom.app (op U)).hom g ↔
      ∃ r : Additive (((X.presheaf.obj (op U)) : Type u)ˣ),
        ((toRationalUnitSheaf X).hom.app (op U)).hom r = f - g := by
  constructor
  · intro h
    let S : ShortComplex (TopCat.Sheaf AddCommGrpCat X) :=
      ShortComplex.mk (toRationalUnitSheaf X) (toCartierDivisorSheaf X)
        (toRationalUnitSheaf_comp_toCartierDivisorSheaf X)
    have hS : S.Exact := exact_toRationalUnitSheaf_toCartierDivisorSheaf X
    have hzero : ((toCartierDivisorSheaf X).hom.app (op U)).hom (f - g) = 0 :=
      (map_sub _ f g).trans (sub_eq_zero.mpr h)
    exact _root_.TopCat.Sheaf.sections_exact_of_left_exact hS (inferInstance : Mono S.f)
      (f - g) hzero
  · rintro ⟨r, hr⟩
    have hcomp := toRationalUnitSheaf_comp_toCartierDivisorSheaf X
    have happ := congrArg (fun k ↦ k.hom.app (op U)) hcomp
    have hrzero := ConcreteCategory.congr_hom happ r
    have hq_sub : ((toCartierDivisorSheaf X).hom.app (op U)).hom (f - g) = 0 :=
      (congrArg ((toCartierDivisorSheaf X).hom.app (op U)).hom hr.symm).trans hrzero
    apply sub_eq_zero.mp
    exact (map_sub _ f g).symm.trans hq_sub

/-- If two rational-unit sections represent the same Cartier divisor, there is a unique regular
unit whose image is their difference. In multiplicative notation, this says their ratio is a
unique regular unit. -/
theorem existsUnique_regularUnit_sub_of_toCartierDivisorSheaf_app_eq {U : X.Opens}
    (f g : Additive (((rationalFunctionsRing X).presheaf.obj (op U))ˣ))
    (h : ((toCartierDivisorSheaf X).hom.app (op U)).hom f =
      ((toCartierDivisorSheaf X).hom.app (op U)).hom g) :
    ∃! r : Additive (((X.presheaf.obj (op U)) : Type u)ˣ),
      ((toRationalUnitSheaf X).hom.app (op U)).hom r = f - g := by
  obtain ⟨r, hr⟩ := (toCartierDivisorSheaf_app_eq_iff X f g).mp h
  exact ⟨r, hr, fun s hs ↦ toRationalUnitSheaf_app_injective X U (hs.trans hr.symm)⟩

/-- Two nonzero rational functions have the same class in the Cartier-divisor sheaf over a
nonempty open subset `U` exactly when they differ by a unit of `Γ(X, U)`. -/
theorem rationalUnitClass_eq_rationalUnitClass_iff (U : X.Opens) [Nonempty U]
    (f g : X.functionFieldˣ) :
    rationalUnitClass X U (Additive.ofMul f) = rationalUnitClass X U (Additive.ofMul g) ↔
      ∃ r : Γ(X, U)ˣ, regularUnitToFunctionField X U r * g = f := by
  rw [rationalUnitClass_apply, rationalUnitClass_apply, toCartierDivisorSheaf_app_eq_iff]
  constructor
  · rintro ⟨r, hr⟩
    refine ⟨Additive.toMul r, Additive.ofMul.injective ?_⟩
    have h := (rationalUnitSectionsEquiv_toRationalUnitSheaf_app X U (Additive.toMul r)).symm.trans
      (congrArg (rationalUnitSectionsEquiv X U) hr)
    rw [map_sub, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply] at h
    rw [ofMul_mul, h, sub_add_cancel]
  · rintro ⟨r, hr⟩
    refine ⟨Additive.ofMul r, (rationalUnitSectionsEquiv X U).injective ?_⟩
    refine (rationalUnitSectionsEquiv_toRationalUnitSheaf_app X U r).trans ?_
    rw [map_sub, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply, ← hr, ofMul_mul,
      add_sub_cancel_right]

namespace CartierDivisor

/-- A global Cartier divisor admits an open cover carrying rational local equations.

The cover is indexed by the points of `X`, with the open indexed by `x` chosen to contain `x`.
The displayed supremum records that these opens cover the whole scheme. -/
theorem exists_local_equation_cover (D : CartierDivisor X) :
    ∃ (U : X → X.Opens)
      (f : ∀ x, Additive (((rationalFunctionsRing X).presheaf.obj (op (U x)))ˣ)),
      (∀ x, x ∈ U x) ∧ (⨆ x, U x) = ⊤ ∧ ∀ x,
        ((toCartierDivisorSheaf X).hom.app (op (U x))).hom (f x) = D |_ (U x) := by
  choose U _ hxU f hf using fun x ↦ exists_local_equation X D x (by simp)
  refine ⟨U, f, hxU, ?_, hf⟩
  apply top_unique
  intro x _
  exact Opens.mem_iSup.mpr ⟨x, hxU x⟩

/-- Two local equations of a global Cartier divisor determine a unique regular transition unit
on their overlap.

In multiplicative notation the displayed difference is the ratio `f / g`: the transition unit is
the regular unit by which the equation `g` must be multiplied to give `f` on `U ⊓ V`. -/
theorem existsUnique_transitionUnit (D : CartierDivisor X) {U V : X.Opens}
    (f : Additive (((rationalFunctionsRing X).presheaf.obj (op U))ˣ))
    (g : Additive (((rationalFunctionsRing X).presheaf.obj (op V))ˣ))
    (hf : ((toCartierDivisorSheaf X).hom.app (op U)).hom f = D |_ U)
    (hg : ((toCartierDivisorSheaf X).hom.app (op V)).hom g = D |_ V) :
    ∃! r : Additive (((X.presheaf.obj (op (U ⊓ V))) : Type u)ˣ),
      ((toRationalUnitSheaf X).hom.app (op (U ⊓ V))).hom r =
        f |_ (U ⊓ V) - g |_ (U ⊓ V) := by
  apply existsUnique_regularUnit_sub_of_toCartierDivisorSheaf_app_eq X
  calc
    _ = (((toCartierDivisorSheaf X).hom.app (op U)).hom f) |_ (U ⊓ V) :=
      TopCat.Presheaf.map_restrict (toCartierDivisorSheaf X).hom inf_le_left f
    _ = (D |_ U) |_ (U ⊓ V) := congrArg (fun s ↦ s |_ (U ⊓ V)) hf
    _ = D |_ (U ⊓ V) := TopCat.Presheaf.restrict_restrict _ _ _
    _ = (D |_ V) |_ (U ⊓ V) := (TopCat.Presheaf.restrict_restrict _ _ _).symm
    _ = (((toCartierDivisorSheaf X).hom.app (op V)).hom g) |_ (U ⊓ V) :=
      congrArg (fun s ↦ s |_ (U ⊓ V)) hg.symm
    _ = _ := (TopCat.Presheaf.map_restrict
      (toCartierDivisorSheaf X).hom inf_le_right g).symm

variable {X}

/-- A local equation over `V` restricts to a local equation over every nonempty open `W ≤ V`. -/
lemma rationalUnitClass_eq_of_le {D : CartierDivisor X} {V W : X.Opens} [Nonempty V]
    [Nonempty W] (hWV : W ≤ V) {f : X.functionFieldˣ}
    (hf : rationalUnitClass X V (Additive.ofMul f) = D |_ V) :
    rationalUnitClass X W (Additive.ofMul f) = D |_ W := by
  rw [← rationalUnitClass_restrict X hWV, hf, TopCat.Presheaf.restrict_restrict]

/-- A nonzero rational function `f` is a *local equation* of the Cartier divisor `D` at the point
`x` when `D` is the class of `f` over some open neighbourhood of `x`. -/
def IsLocalEquationAt (D : CartierDivisor X) (x : X) (f : X.functionFieldˣ) : Prop :=
  ∃ (V : X.Opens) (hx : x ∈ V),
    haveI : Nonempty V := ⟨⟨x, hx⟩⟩
    rationalUnitClass X V (Additive.ofMul f) = D |_ V

/-- Unfolding `IsLocalEquationAt`: `f` is a local equation of `D` at `x` exactly when `D` is the
class of `f` over some open neighbourhood of `x`. -/
lemma isLocalEquationAt_iff {D : CartierDivisor X} {x : X} {f : X.functionFieldˣ} :
    D.IsLocalEquationAt x f ↔ ∃ (V : X.Opens) (hx : x ∈ V),
      haveI : Nonempty V := ⟨⟨x, hx⟩⟩
      rationalUnitClass X V (Additive.ofMul f) = D |_ V :=
  Iff.rfl

/-- An equation of `D` over an open subset is a local equation at each of its points. -/
lemma isLocalEquationAt_of_rationalUnitClass_eq {D : CartierDivisor X} {V : X.Opens} [Nonempty V]
    {f : X.functionFieldˣ} (hf : rationalUnitClass X V (Additive.ofMul f) = D |_ V) {x : X}
    (hx : x ∈ V) : D.IsLocalEquationAt x f :=
  ⟨V, hx, hf⟩

/-- Every Cartier divisor has a local equation at every point. -/
theorem exists_isLocalEquationAt (D : CartierDivisor X) (x : X) :
    ∃ f : X.functionFieldˣ, D.IsLocalEquationAt x f := by
  obtain ⟨V, hVU, hx, f, hf⟩ := exists_local_equation X D x (Opens.mem_top x)
  have : Nonempty V := ⟨⟨x, hx⟩⟩
  refine ⟨Additive.toMul (rationalUnitSectionsEquiv X V f), V, hx, ?_⟩
  rw [rationalUnitClass_apply]
  exact ((congrArg _ ((rationalUnitSectionsEquiv X V).symm_apply_apply f)).trans hf)

/-- Two local equations of `D` at `x` differ by a unit of the local ring `𝒪_{X,x}`. -/
theorem IsLocalEquationAt.exists_unit_mul_eq {D : CartierDivisor X} {x : X}
    {f g : X.functionFieldˣ} (hf : D.IsLocalEquationAt x f) (hg : D.IsLocalEquationAt x g) :
    ∃ u : (X.presheaf.stalk x)ˣ,
      algebraMap (X.presheaf.stalk x) X.functionField u * g = f := by
  obtain ⟨V, hxV, hV⟩ := hf
  obtain ⟨W, hxW, hW⟩ := hg
  have : Nonempty V := ⟨⟨x, hxV⟩⟩
  have : Nonempty W := ⟨⟨x, hxW⟩⟩
  have hx : x ∈ V ⊓ W := ⟨hxV, hxW⟩
  have : Nonempty (V ⊓ W : X.Opens) := ⟨⟨x, hx⟩⟩
  obtain ⟨r, hr⟩ := (rationalUnitClass_eq_rationalUnitClass_iff X (V ⊓ W) f g).mp
    ((rationalUnitClass_eq_of_le inf_le_left hV).trans
      (rationalUnitClass_eq_of_le inf_le_right hW).symm)
  refine ⟨Units.map (X.presheaf.germ (V ⊓ W) x hx).hom.toMonoidHom r, ?_⟩
  rw [← hr, Units.val_mul, regularUnitToFunctionField_apply]
  exact congrArg (· * (g : X.functionField))
    (_root_.AlgebraicGeometry.Scheme.algebraMap_germ_eq_germToFunctionField X hx (r : Γ(X, V ⊓ W)))

/-- Whether `f * c` lies in the local ring at `x` does not depend on the choice of the local
equation `f` of `D` at `x`. -/
lemma IsLocalEquationAt.mul_mem_range_iff {D : CartierDivisor X} {x : X}
    {f g : X.functionFieldˣ} (hf : D.IsLocalEquationAt x f) (hg : D.IsLocalEquationAt x g)
    (c : X.functionField) :
    (f : X.functionField) * c ∈ (algebraMap (X.presheaf.stalk x) X.functionField).range ↔
      (g : X.functionField) * c ∈ (algebraMap (X.presheaf.stalk x) X.functionField).range := by
  obtain ⟨u, hu⟩ := hf.exists_unit_mul_eq hg
  have hu' : algebraMap (X.presheaf.stalk x) X.functionField ↑u⁻¹ * f = g := by
    rw [← hu, ← mul_assoc, ← map_mul, Units.inv_mul, map_one, one_mul]
  constructor
  · intro h
    rw [← hu', mul_assoc]
    exact Subring.mul_mem _ (RingHom.mem_range_self _ _) h
  · intro h
    rw [← hu, mul_assoc]
    exact Subring.mul_mem _ (RingHom.mem_range_self _ _) h

/-- Local equations only depend on the restriction of the divisor: divisors that agree on an open
subset `V` have the same local equations at the points of `V`. -/
lemma isLocalEquationAt_congr {D E : CartierDivisor X} {V : X.Opens} (h : D |_ V = E |_ V)
    {x : X} (hx : x ∈ V) (f : X.functionFieldˣ) :
    D.IsLocalEquationAt x f ↔ E.IsLocalEquationAt x f := by
  suffices key : ∀ {D E : CartierDivisor X}, D |_ V = E |_ V →
      D.IsLocalEquationAt x f → E.IsLocalEquationAt x f from ⟨key h, key h.symm⟩
  intro D E h ⟨W, hxW, hW⟩
  have : Nonempty W := ⟨⟨x, hxW⟩⟩
  have : Nonempty (W ⊓ V : X.Opens) := ⟨⟨x, hxW, hx⟩⟩
  refine isLocalEquationAt_of_rationalUnitClass_eq (V := W ⊓ V) ?_ ⟨hxW, hx⟩
  rw [rationalUnitClass_eq_of_le inf_le_left hW,
    ← TopCat.Presheaf.restrict_restrict (inf_le_right : W ⊓ V ≤ V) le_top D, h,
    TopCat.Presheaf.restrict_restrict]

end CartierDivisor

end Scheme

end

end AlgebraicGeometry

end TauCeti
