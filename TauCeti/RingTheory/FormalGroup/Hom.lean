/-
Copyright (c) 2026 Wenrong Zou and The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wenrong Zou, The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.FormalGroup.Basic
public import TauCeti.RingTheory.MvPowerSeries.Order
public import TauCeti.RingTheory.MvPowerSeries.Substitution
public import TauCeti.RingTheory.PowerSeries.Substitution
import TauCeti.RingTheory.PowerSeries.SubstInv

/-!
# Homomorphisms and isomorphisms of formal group laws

A homomorphism is a power series with zero constant term carrying one formal group law to
another. Composition is substitution. An isomorphism carries a specified inverse homomorphism;
it is strict when its linear coefficient is one. These maps act on the native power-series
points, including points with nilpotent, not necessarily zero, constant coefficient.

The homomorphism defect `f(F(X, Y)) - G(f(X), f(Y))` (`FormalGroup.homDefect`) of a power series
`f` measures how far `f` is from a homomorphism: it vanishes exactly for homomorphisms
(`TauCeti.FormalGroupHom.homDefect_toPowerSeries`, `TauCeti.FormalGroupHom.ofHomDefectEqZero`).
Towards the additive formal group law the defect is additive in `f`
(`FormalGroup.homDefect_𝔾ₐ_sub`), vanishes to the order of `f`
(`FormalGroup.le_order_homDefect_𝔾ₐ`), and for `f = c Xⁿ` has leading term
`c ((X + Y)ⁿ - Xⁿ - Yⁿ)` (`FormalGroup.homogeneousComponent_homDefect_𝔾ₐ_smul_X_pow`).

The bundles `TauCeti.FormalGroupHom`, `TauCeti.FormalGroupIso`, and
`TauCeti.FormalGroupIso.IsStrict` are adapted from Wenrong Zou's Mathlib PR #38213
(https://github.com/leanprover-community/mathlib4/pull/38213). The action on points here uses
Mathlib's native `FormalGroup.Point` carrier and formal substitution, not evaluation in an
arbitrary topological algebra.
-/

public section

open MvPowerSeries

namespace FormalGroup

variable {R : Type*} [CommRing R] (F G : FormalGroup R)

/-- The **homomorphism defect** `f(F(X, Y)) - G(f(X), f(Y))` of a power series `f` with respect to
formal group laws `F` and `G`. It vanishes exactly when `f` satisfies the homomorphism equation
(`FormalGroup.homDefect_eq_zero_iff`), and its order measures to which degree `f` is a
homomorphism from `F` to `G`. -/
noncomputable def homDefect (f : PowerSeries R) : MvPowerSeries (Fin 2) R :=
  PowerSeries.subst F.toPowerSeries f - subst (fun i ↦ f.toMvPowerSeries i) G.toPowerSeries

/-- Unfold the homomorphism defect. -/
theorem homDefect_def (f : PowerSeries R) :
    F.homDefect G f =
      PowerSeries.subst F.toPowerSeries f - subst (fun i ↦ f.toMvPowerSeries i) G.toPowerSeries :=
  (rfl)

/-- The homomorphism defect vanishes exactly when `f` satisfies the homomorphism equation. -/
theorem homDefect_eq_zero_iff {f : PowerSeries R} :
    F.homDefect G f = 0 ↔
      PowerSeries.subst F.toPowerSeries f = subst (fun i ↦ f.toMvPowerSeries i) G.toPowerSeries :=
  sub_eq_zero

/-- The homomorphism defect towards the additive formal group law is the additivity defect
`f(F(X, Y)) - f(X) - f(Y)`. -/
theorem homDefect_𝔾ₐ {f : PowerSeries R} (hf : PowerSeries.constantCoeff f = 0) :
    F.homDefect 𝔾ₐ f = PowerSeries.subst F.toPowerSeries f - PowerSeries.subst (X 0) f -
      PowerSeries.subst (X 1) f := by
  have hE := HasSubst.toMvPowerSeries (σ := Fin 2) hf
  rw [homDefect_def, 𝔾ₐ_toPowerSeries, subst_add hE, subst_X hE, subst_X hE]
  simp only [PowerSeries.toMvPowerSeries_eq_subst]
  ring

/-- The homomorphism defect towards the additive formal group law is additive in the series. -/
theorem homDefect_𝔾ₐ_sub {g h : PowerSeries R} (hg : PowerSeries.constantCoeff g = 0)
    (hh : PowerSeries.constantCoeff h = 0) :
    F.homDefect 𝔾ₐ (g - h) = F.homDefect 𝔾ₐ g - F.homDefect 𝔾ₐ h := by
  have hF := PowerSeries.HasSubst.of_constantCoeff_zero F.zero_constantCoeff
  rw [F.homDefect_𝔾ₐ (by rw [map_sub, hg, hh, sub_zero]), F.homDefect_𝔾ₐ hg, F.homDefect_𝔾ₐ hh]
  simp only [PowerSeries.subst_sub hF, PowerSeries.subst_sub (PowerSeries.HasSubst.X _)]
  ring

/-- The homomorphism defect of `g` towards the additive formal group law vanishes to the order
of `g`. -/
theorem le_order_homDefect_𝔾ₐ {g : PowerSeries R} (hg₀ : PowerSeries.constantCoeff g = 0)
    {n : ℕ} (hg : n ≤ g.order) : (n : ℕ∞) ≤ (F.homDefect 𝔾ₐ g).order := by
  have h {x : MvPowerSeries (Fin 2) R} (hx : constantCoeff x = 0) :
      (n : ℕ∞) ≤ (PowerSeries.subst x g).order :=
    hg.trans (PowerSeries.le_order_subst_left hx)
  rw [F.homDefect_𝔾ₐ hg₀]
  exact le_order_sub (le_order_sub (h F.zero_constantCoeff) (h (constantCoeff_X 0)))
    (h (constantCoeff_X 1))

/-- The lowest-degree part of the homomorphism defect of `c Xⁿ`, `n ≠ 0`, towards the additive
formal group law is `c ((X + Y)ⁿ - Xⁿ - Yⁿ)`. -/
theorem homogeneousComponent_homDefect_𝔾ₐ_smul_X_pow (c : R) {n : ℕ} (hn : n ≠ 0) :
    homogeneousComponent n (F.homDefect 𝔾ₐ (c • PowerSeries.X ^ n)) =
      ((c • ((MvPolynomial.X 0 + MvPolynomial.X 1) ^ n - MvPolynomial.X 0 ^ n -
        MvPolynomial.X 1 ^ n) : MvPolynomial (Fin 2) R) : MvPowerSeries (Fin 2) R) := by
  have hF := PowerSeries.HasSubst.of_constantCoeff_zero F.zero_constantCoeff
  have hX (i : Fin 2) := PowerSeries.HasSubst.X (S := R) i
  rw [F.homDefect_𝔾ₐ (by simp [hn])]
  simp only [PowerSeries.subst_smul hF, PowerSeries.subst_smul (hX _),
    PowerSeries.subst_pow hF, PowerSeries.subst_pow (hX _), PowerSeries.subst_X hF,
    PowerSeries.subst_X (hX _), map_sub, _root_.map_smul,
    homogeneousComponent_pow_of_constantCoeff_eq_zero F.zero_constantCoeff,
    homogeneousComponent_pow_of_constantCoeff_eq_zero (constantCoeff_X _),
    homogeneousComponent_one_X,
    homogeneousComponent_one_eq_X_add_X F.lin_coeff_X F.lin_coeff_Y]
  rw [MvPolynomial.smul_eq_C_mul, ← MvPolynomial.coeToMvPowerSeries.ringHom_apply]
  simp only [map_mul, map_sub, map_pow, map_add, MvPolynomial.coeToMvPowerSeries.ringHom_apply,
    MvPolynomial.coe_X, MvPolynomial.coe_C, MvPowerSeries.smul_eq_C_mul, mul_sub]

end FormalGroup

namespace TauCeti

variable {R : Type*} [CommRing R] {F G H K : FormalGroup R}

/-- A homomorphism of formal group laws is a series `f` with zero constant term such that
`f(F(X,Y)) = G(f(X),f(Y))`. -/
@[ext]
structure FormalGroupHom (F G : FormalGroup R) where
  /-- The underlying one-variable series. -/
  toPowerSeries : PowerSeries R
  /-- The homomorphism sends the origin to the origin. -/
  zero_constantCoeff : toPowerSeries.constantCoeff = 0
  /-- Compatibility with the formal group laws. -/
  hom : PowerSeries.subst F.toPowerSeries toPowerSeries =
    subst (fun i => toPowerSeries.toMvPowerSeries i) G.toPowerSeries

namespace FormalGroupHom

/-- Transport a homomorphism along an equality of source formal groups. -/
def ofSourceEq {F' : FormalGroup R} (e : F = F') (f : FormalGroupHom F G) :
    FormalGroupHom F' G := e ▸ f

@[simp]
theorem ofSourceEq_toPowerSeries {F' : FormalGroup R} (e : F = F')
    (f : FormalGroupHom F G) : (ofSourceEq e f).toPowerSeries = f.toPowerSeries := by
  subst F'
  rfl

/-- The series of a formal group homomorphism can be substituted. -/
theorem hasSubst (f : FormalGroupHom F G) : PowerSeries.HasSubst f.toPowerSeries :=
  .of_constantCoeff_zero' f.zero_constantCoeff

/-- The homomorphism equation after substituting any admissible coordinate family. -/
theorem hom_subst (f : FormalGroupHom F G) {σ : Type*}
    {a : Fin 2 → MvPowerSeries σ R} (ha : HasSubst a) :
    PowerSeries.subst (subst a F.toPowerSeries) f.toPowerSeries =
      subst (fun i => PowerSeries.subst (a i) f.toPowerSeries) G.toPowerSeries := by
  have h := congrArg (subst a) f.hom
  rw [subst_powerSeriesSubst ha (.of_constantCoeff_zero F.zero_constantCoeff),
    subst_comp_subst_apply (.toMvPowerSeries f.zero_constantCoeff) ha] at h
  simpa only [PowerSeries.subst_toMvPowerSeries ha] using h

/-- The homomorphism equation into the additive formal group is the additivity equation. -/
theorem hom_additive_iff {g : PowerSeries R} (hg : g.constantCoeff = 0) :
    (PowerSeries.subst F.toPowerSeries g =
      subst (fun i => g.toMvPowerSeries i) (FormalGroup.𝔾ₐ (R := R)).toPowerSeries) ↔
    PowerSeries.subst F.toPowerSeries g =
      PowerSeries.subst (X 0) g + PowerSeries.subst (X 1) g := by
  rw [FormalGroup.𝔾ₐ_toPowerSeries, subst_add (.toMvPowerSeries hg),
    subst_X (.toMvPowerSeries hg), subst_X (.toMvPowerSeries hg)]
  simp only [PowerSeries.toMvPowerSeries_eq_subst]

/-- A homomorphism of formal group laws has zero homomorphism defect. -/
@[simp]
theorem homDefect_toPowerSeries (f : FormalGroupHom F G) : F.homDefect G f.toPowerSeries = 0 :=
  (FormalGroup.homDefect_eq_zero_iff F G).mpr f.hom

/-- A power series without constant term whose homomorphism defect vanishes, as a homomorphism of
formal group laws. -/
def ofHomDefectEqZero {f : PowerSeries R} (hf : PowerSeries.constantCoeff f = 0)
    (h : F.homDefect G f = 0) : FormalGroupHom F G where
  toPowerSeries := f
  zero_constantCoeff := hf
  hom := (FormalGroup.homDefect_eq_zero_iff F G).mp h

@[simp]
theorem ofHomDefectEqZero_toPowerSeries {f : PowerSeries R}
    (hf : PowerSeries.constantCoeff f = 0) (h : F.homDefect G f = 0) :
    (ofHomDefectEqZero hf h).toPowerSeries = f := (rfl)

/-- A substitution inverse of a formal group homomorphism is a homomorphism. -/
noncomputable def ofInverse (f : FormalGroupHom F G) (g : PowerSeries R)
    (hg : g.constantCoeff = 0)
    (hfg : PowerSeries.subst g f.toPowerSeries = PowerSeries.X)
    (hgf : PowerSeries.subst f.toPowerSeries g = PowerSeries.X) : FormalGroupHom G F where
  toPowerSeries := g
  zero_constantCoeff := hg
  hom := by
    have hE := MvPowerSeries.HasSubst.toMvPowerSeries (σ := Fin 2) hg
    have hcoords (i : Fin 2) : PowerSeries.subst (g.toMvPowerSeries i) f.toPowerSeries =
        X i := by
      rw [PowerSeries.toMvPowerSeries_eq_subst,
        ← PowerSeries.subst_comp_subst_apply (.of_constantCoeff_zero' hg)
          (PowerSeries.HasSubst.X i), hfg, PowerSeries.subst_X (PowerSeries.HasSubst.X i)]
    have hF : PowerSeries.HasSubst (subst (fun i : Fin 2 => g.toMvPowerSeries i)
        F.toPowerSeries) := IsNilpotent_subst hE (F.zero_constantCoeff ▸ IsNilpotent.zero)
    have h := congrArg (fun a => PowerSeries.subst a g) (f.hom_subst hE)
    rw [← PowerSeries.subst_comp_subst_apply f.hasSubst hF, hgf,
      PowerSeries.subst_X hF] at h
    simpa only [hcoords, subst_self, id_eq] using h.symm

@[simp]
theorem ofInverse_toPowerSeries (f : FormalGroupHom F G) (g : PowerSeries R)
    (hg : g.constantCoeff = 0) (hfg : PowerSeries.subst g f.toPowerSeries = PowerSeries.X)
    (hgf : PowerSeries.subst f.toPowerSeries g = PowerSeries.X) :
    (f.ofInverse g hg hfg hgf).toPowerSeries = g := (rfl)

/-- The identity homomorphism has underlying series `X`. -/
noncomputable def id (F : FormalGroup R) : FormalGroupHom F F where
  toPowerSeries := PowerSeries.X
  zero_constantCoeff := PowerSeries.constantCoeff_X
  hom := by
    simp [PowerSeries.subst_X (.of_constantCoeff_zero F.zero_constantCoeff),
      PowerSeries.toMvPowerSeries_X, subst_self]

@[simp]
theorem id_toPowerSeries (F : FormalGroup R) : (id F).toPowerSeries = PowerSeries.X := (rfl)

/-- Composition of formal group homomorphisms, with the outer map first. -/
noncomputable def comp (g : FormalGroupHom G H) (f : FormalGroupHom F G) :
    FormalGroupHom F H where
  toPowerSeries := PowerSeries.subst f.toPowerSeries g.toPowerSeries
  zero_constantCoeff := PowerSeries.constantCoeff_subst_eq_zero f.zero_constantCoeff _
    g.zero_constantCoeff
  hom := by
    rw [PowerSeries.subst_comp_subst_apply f.hasSubst
      (.of_constantCoeff_zero F.zero_constantCoeff), f.hom]
    have hf := MvPowerSeries.HasSubst.toMvPowerSeries (σ := Fin 2) f.zero_constantCoeff
    have h := g.hom_subst hf
    rw [h]
    congr 1
    funext i
    simp only [PowerSeries.toMvPowerSeries_eq_subst,
      PowerSeries.subst_comp_subst_apply f.hasSubst (PowerSeries.HasSubst.X i)]

@[simp]
theorem comp_toPowerSeries (g : FormalGroupHom G H) (f : FormalGroupHom F G) :
    (g.comp f).toPowerSeries = PowerSeries.subst f.toPowerSeries g.toPowerSeries := (rfl)

@[simp]
theorem id_comp (f : FormalGroupHom F G) : (id G).comp f = f := by
  ext
  simp [PowerSeries.subst_X f.hasSubst]

@[simp]
theorem comp_id (f : FormalGroupHom F G) : f.comp (id F) = f := by
  ext
  simp [PowerSeries.X_subst]

/-- Composition of formal group homomorphisms is associative. -/
theorem comp_assoc (h : FormalGroupHom H K) (g : FormalGroupHom G H)
    (f : FormalGroupHom F G) : (h.comp g).comp f = h.comp (g.comp f) := by
  ext
  simp only [comp_toPowerSeries, PowerSeries.subst_comp_subst_apply g.hasSubst f.hasSubst]

/-- A left substitution inverse and a right substitution inverse of the same homomorphism agree. -/
theorem eq_of_subst_eq_X (f : FormalGroupHom F G) (g g' : FormalGroupHom G F)
    (hgf : PowerSeries.subst f.toPowerSeries g.toPowerSeries = PowerSeries.X)
    (hfg' : PowerSeries.subst g'.toPowerSeries f.toPowerSeries = PowerSeries.X) : g = g' := by
  apply FormalGroupHom.ext
  calc
    g.toPowerSeries = PowerSeries.subst
        (PowerSeries.subst g'.toPowerSeries f.toPowerSeries) g.toPowerSeries := by
      rw [hfg', PowerSeries.X_subst]
    _ = PowerSeries.subst g'.toPowerSeries
        (PowerSeries.subst f.toPowerSeries g.toPowerSeries) :=
      (PowerSeries.subst_comp_subst_apply f.hasSubst g'.hasSubst _).symm
    _ = g'.toPowerSeries := by rw [hgf, PowerSeries.subst_X g'.hasSubst]

/-- Linear coefficients multiply under composition. -/
theorem coeff_one_comp (g : FormalGroupHom G H) (f : FormalGroupHom F G) :
    PowerSeries.coeff 1 (g.comp f).toPowerSeries =
      PowerSeries.coeff 1 g.toPowerSeries * PowerSeries.coeff 1 f.toPowerSeries := by
  simp only [comp_toPowerSeries, PowerSeries.coeff_one_subst f.zero_constantCoeff,
    Algebra.algebraMap_self_apply]

/-- Apply a homomorphism to a native formal power-series point by substitution. -/
noncomputable def applyPoint (f : FormalGroupHom F G) {σ : Type*} (x : F.Point σ) : G.Point σ :=
  ⟨PowerSeries.subst x.val f.toPowerSeries, by
    simpa only [PowerSeries.coe_substAlgHom] using f.hasSubst.comp x.prop⟩

@[simp]
theorem applyPoint_val (f : FormalGroupHom F G) {σ : Type*} (x : F.Point σ) :
    (f.applyPoint x).val = PowerSeries.subst x.val f.toPowerSeries := (rfl)

@[simp]
theorem applyPoint_zero (f : FormalGroupHom F G) {σ : Type*} :
    f.applyPoint (0 : F.Point σ) = 0 := by
  apply Subtype.ext
  simp [PowerSeries.subst_zero_of_constantCoeff_zero f.zero_constantCoeff]

@[simp]
theorem applyPoint_add (f : FormalGroupHom F G) {σ : Type*} (x y : F.Point σ) :
    f.applyPoint (x + y) = f.applyPoint x + f.applyPoint y := by
  apply Subtype.ext
  have hxy : HasSubst ![x.val, y.val] := hasSubst_of_constantCoeff_nilpotent fun i => by
    fin_cases i
    · exact x.prop
    · exact y.prop
  simp only [applyPoint_val, FormalGroup.add_apply]
  convert f.hom_subst hxy using 2
  funext i
  fin_cases i <;> simp

/-- The induced additive map on native power-series points. -/
noncomputable def toAddMonoidHom (f : FormalGroupHom F G) (σ : Type*) :
    F.Point σ →+ G.Point σ where
  toFun := f.applyPoint
  map_zero' := f.applyPoint_zero
  map_add' := f.applyPoint_add

@[simp]
theorem toAddMonoidHom_apply (f : FormalGroupHom F G) {σ : Type*} (x : F.Point σ) :
    f.toAddMonoidHom σ x = f.applyPoint x := (rfl)

@[simp]
theorem id_applyPoint {σ : Type*} (x : F.Point σ) : (id F).applyPoint x = x := by
  apply Subtype.ext
  simp [PowerSeries.subst_X x.prop]

@[simp]
theorem comp_applyPoint (g : FormalGroupHom G H) (f : FormalGroupHom F G) {σ : Type*}
    (x : F.Point σ) : (g.comp f).applyPoint x = g.applyPoint (f.applyPoint x) := by
  apply Subtype.ext
  simp only [applyPoint_val, comp_toPowerSeries,
    PowerSeries.subst_comp_subst_apply f.hasSubst x.prop]

end FormalGroupHom

/-- An isomorphism of formal group laws with specified mutually inverse homomorphisms.
The inverse laws are equations of substitution operators on one-variable power series. -/
structure FormalGroupIso (F G : FormalGroup R) where
  /-- The forward homomorphism. -/
  toHom : FormalGroupHom F G
  /-- The inverse homomorphism. -/
  invHom : FormalGroupHom G F
  /-- Substitution by the forward series followed by the inverse is the identity. -/
  left_inv : PowerSeries.subst invHom.toPowerSeries ∘ PowerSeries.subst toHom.toPowerSeries =
    _root_.id
  /-- Substitution by the inverse series followed by the forward is the identity. -/
  right_inv : PowerSeries.subst toHom.toPowerSeries ∘ PowerSeries.subst invHom.toPowerSeries =
    _root_.id

namespace FormalGroupIso

/-- Construct an isomorphism from the two series substitution identities. -/
noncomputable def ofSubstEqX (f : FormalGroupHom F G) (g : FormalGroupHom G F)
    (hfg : PowerSeries.subst g.toPowerSeries f.toPowerSeries = PowerSeries.X)
    (hgf : PowerSeries.subst f.toPowerSeries g.toPowerSeries = PowerSeries.X) :
    FormalGroupIso F G where
  toHom := f
  invHom := g
  left_inv := by
    funext a
    simp only [Function.comp_apply, PowerSeries.subst_comp_subst_apply f.hasSubst g.hasSubst,
      hfg, PowerSeries.X_subst, id_eq]
  right_inv := by
    funext a
    simp only [Function.comp_apply, PowerSeries.subst_comp_subst_apply g.hasSubst f.hasSubst,
      hgf, PowerSeries.X_subst, id_eq]

@[simp]
theorem ofSubstEqX_toHom (f : FormalGroupHom F G) (g : FormalGroupHom G F)
    (hfg : PowerSeries.subst g.toPowerSeries f.toPowerSeries = PowerSeries.X)
    (hgf : PowerSeries.subst f.toPowerSeries g.toPowerSeries = PowerSeries.X) :
    (ofSubstEqX f g hfg hgf).toHom = f := (rfl)

@[simp]
theorem ofSubstEqX_invHom (f : FormalGroupHom F G) (g : FormalGroupHom G F)
    (hfg : PowerSeries.subst g.toPowerSeries f.toPowerSeries = PowerSeries.X)
    (hgf : PowerSeries.subst f.toPowerSeries g.toPowerSeries = PowerSeries.X) :
    (ofSubstEqX f g hfg hgf).invHom = g := (rfl)

/-- The forward series evaluated at the inverse series is `X`. -/
@[simp]
theorem subst_invHom_toHom (f : FormalGroupIso F G) :
    PowerSeries.subst f.invHom.toPowerSeries f.toHom.toPowerSeries = PowerSeries.X := by
  have h := congrFun f.left_inv PowerSeries.X
  simpa [PowerSeries.subst_X f.toHom.hasSubst] using h

/-- The inverse series evaluated at the forward series is `X`. -/
@[simp]
theorem subst_toHom_invHom (f : FormalGroupIso F G) :
    PowerSeries.subst f.toHom.toPowerSeries f.invHom.toPowerSeries = PowerSeries.X := by
  have h := congrFun f.right_inv PowerSeries.X
  simpa [PowerSeries.subst_X f.invHom.hasSubst] using h

/-- The linear coefficient of a formal group isomorphism is a unit. -/
theorem isUnit_coeff_one (f : FormalGroupIso F G) :
    IsUnit (PowerSeries.coeff 1 f.toHom.toPowerSeries) :=
  PowerSeries.isUnit_coeff_one_of_subst_eq_X f.toHom.hasSubst f.subst_toHom_invHom

/-- Over a nontrivial ring, the forward series of an isomorphism is nonzero: its linear
coefficient is invertible. -/
theorem toHom_toPowerSeries_ne_zero [Nontrivial R] (f : FormalGroupIso F G) :
    f.toHom.toPowerSeries ≠ 0 := by
  intro h0
  have h := congrArg (PowerSeries.coeff 1) f.subst_invHom_toHom
  simp [h0] at h

/-- A formal group isomorphism is determined by its forward homomorphism. -/
@[ext]
theorem ext {f g : FormalGroupIso F G} (h : f.toHom = g.toHom) : f = g := by
  have hinv : f.invHom = g.invHom :=
    FormalGroupHom.eq_of_subst_eq_X f.toHom f.invHom g.invHom
      f.subst_toHom_invHom (by rw [h]; exact g.subst_invHom_toHom)
  cases f
  cases g
  cases h
  cases hinv
  rfl

/-- A strict isomorphism has linear coefficient one. -/
class IsStrict (f : FormalGroupIso F G) : Prop where
  /-- The forward coordinate is tangent to the identity. -/
  coeff_one : PowerSeries.coeff 1 f.toHom.toPowerSeries = 1

/-- Reverse a formal group isomorphism. -/
def symm (f : FormalGroupIso F G) : FormalGroupIso G F where
  toHom := f.invHom
  invHom := f.toHom
  left_inv := f.right_inv
  right_inv := f.left_inv

@[simp]
theorem symm_toHom (f : FormalGroupIso F G) : f.symm.toHom = f.invHom := (rfl)

@[simp]
theorem symm_invHom (f : FormalGroupIso F G) : f.symm.invHom = f.toHom := (rfl)

@[simp]
theorem symm_symm (f : FormalGroupIso F G) : f.symm.symm = f := by
  ext
  rfl

/-- The identity formal group isomorphism. -/
noncomputable def refl (F : FormalGroup R) : FormalGroupIso F F :=
  .ofSubstEqX (.id F) (.id F) (by simp [PowerSeries.X_subst])
    (by simp [PowerSeries.X_subst])

@[simp]
theorem refl_toHom (F : FormalGroup R) : (refl F).toHom = FormalGroupHom.id F := (rfl)

@[simp]
theorem refl_invHom (F : FormalGroup R) : (refl F).invHom = FormalGroupHom.id F := (rfl)

/-- The inverse followed by the forward map is the identity homomorphism. -/
@[simp]
theorem toHom_comp_invHom (f : FormalGroupIso F G) :
    f.toHom.comp f.invHom = FormalGroupHom.id G := by
  apply FormalGroupHom.ext
  exact f.subst_invHom_toHom

/-- The forward map followed by the inverse is the identity homomorphism. -/
@[simp]
theorem invHom_comp_toHom (f : FormalGroupIso F G) :
    f.invHom.comp f.toHom = FormalGroupHom.id F := by
  apply FormalGroupHom.ext
  exact f.subst_toHom_invHom

/-- Compose formal group isomorphisms, applying the first argument first. -/
noncomputable def trans (f : FormalGroupIso F G) (g : FormalGroupIso G H) :
    FormalGroupIso F H :=
  .ofSubstEqX (g.toHom.comp f.toHom) (f.invHom.comp g.invHom)
    (by
      rw [← FormalGroupHom.comp_toPowerSeries, ← FormalGroupHom.comp_assoc,
        FormalGroupHom.comp_assoc g.toHom,
        toHom_comp_invHom, FormalGroupHom.comp_id, toHom_comp_invHom,
        FormalGroupHom.id_toPowerSeries])
    (by
      rw [← FormalGroupHom.comp_toPowerSeries, ← FormalGroupHom.comp_assoc,
        FormalGroupHom.comp_assoc f.invHom,
        invHom_comp_toHom, FormalGroupHom.comp_id, invHom_comp_toHom,
        FormalGroupHom.id_toPowerSeries])

@[simp]
theorem trans_toHom (f : FormalGroupIso F G) (g : FormalGroupIso G H) :
    (f.trans g).toHom = g.toHom.comp f.toHom := (rfl)

@[simp]
theorem trans_invHom (f : FormalGroupIso F G) (g : FormalGroupIso G H) :
    (f.trans g).invHom = f.invHom.comp g.invHom := (rfl)

@[simp]
theorem refl_trans (f : FormalGroupIso F G) : (refl F).trans f = f := by
  ext
  simp

@[simp]
theorem trans_refl (f : FormalGroupIso F G) : f.trans (refl G) = f := by
  ext
  simp

@[simp]
theorem self_trans_symm (f : FormalGroupIso F G) : f.trans f.symm = refl F := by
  ext
  simp

@[simp]
theorem symm_trans_self (f : FormalGroupIso F G) : f.symm.trans f = refl G := by
  ext
  simp

/-- Composition of formal group isomorphisms is associative. -/
theorem trans_assoc (f : FormalGroupIso F G) (g : FormalGroupIso G H)
    (h : FormalGroupIso H K) : (f.trans g).trans h = f.trans (g.trans h) := by
  ext
  simp only [trans_toHom, FormalGroupHom.comp_assoc]

instance (F : FormalGroup R) : (refl F).IsStrict where
  coeff_one := by simp

instance (f : FormalGroupIso F G) [f.IsStrict] : f.symm.IsStrict where
  coeff_one := by
    have h := congrArg (PowerSeries.coeff 1) f.subst_invHom_toHom
    simpa only [PowerSeries.coeff_one_subst f.invHom.zero_constantCoeff,
      Algebra.algebraMap_self_apply, IsStrict.coeff_one (f := f), one_mul,
      PowerSeries.coeff_X, ↓reduceIte, symm_toHom] using h

instance (f : FormalGroupIso F G) (g : FormalGroupIso G H) [f.IsStrict] [g.IsStrict] :
    (f.trans g).IsStrict where
  coeff_one := by
    simp only [trans_toHom, FormalGroupHom.coeff_one_comp,
      IsStrict.coeff_one (f := f), IsStrict.coeff_one (f := g), mul_one]

/-- The additive equivalence induced on native power-series points. -/
noncomputable def toAddEquiv (f : FormalGroupIso F G) (σ : Type*) : F.Point σ ≃+ G.Point σ where
  toFun := f.toHom.applyPoint
  invFun := f.invHom.applyPoint
  left_inv x := by
    rw [← FormalGroupHom.comp_applyPoint, invHom_comp_toHom, FormalGroupHom.id_applyPoint]
  right_inv x := by
    rw [← FormalGroupHom.comp_applyPoint, toHom_comp_invHom, FormalGroupHom.id_applyPoint]
  map_add' := f.toHom.applyPoint_add

@[simp]
theorem toAddEquiv_apply (f : FormalGroupIso F G) {σ : Type*} (x : F.Point σ) :
    f.toAddEquiv σ x = f.toHom.applyPoint x := (rfl)

@[simp]
theorem toAddEquiv_symm_apply (f : FormalGroupIso F G) {σ : Type*} (x : G.Point σ) :
    (f.toAddEquiv σ).symm x = f.invHom.applyPoint x := (rfl)

@[simp]
theorem toAddEquiv_refl (F : FormalGroup R) (σ : Type*) :
    (refl F).toAddEquiv σ = AddEquiv.refl (F.Point σ) := by
  ext x
  exact FormalGroupHom.id_applyPoint x

@[simp]
theorem toAddEquiv_trans (f : FormalGroupIso F G) (g : FormalGroupIso G H) (σ : Type*) :
    (f.trans g).toAddEquiv σ = (f.toAddEquiv σ).trans (g.toAddEquiv σ) := by
  ext x
  exact FormalGroupHom.comp_applyPoint g.toHom f.toHom x

@[simp]
theorem toAddEquiv_symm (f : FormalGroupIso F G) (σ : Type*) :
    f.symm.toAddEquiv σ = (f.toAddEquiv σ).symm := (rfl)

end FormalGroupIso

namespace FormalGroupHom

/-- A homomorphism with invertible linear coefficient is a formal group isomorphism. -/
noncomputable def toIso (f : FormalGroupHom F G)
    (hf : IsUnit (PowerSeries.coeff 1 f.toPowerSeries)) : FormalGroupIso F G :=
  .ofSubstEqX f
    (f.ofInverse (f.toPowerSeries.substInvOfIsUnit hf)
      (PowerSeries.constantCoeff_substInvOfIsUnit _ _)
      (PowerSeries.subst_substInvOfIsUnit_right _ f.zero_constantCoeff _)
      (PowerSeries.subst_substInvOfIsUnit_left _ f.zero_constantCoeff _))
    (PowerSeries.subst_substInvOfIsUnit_right _ f.zero_constantCoeff _)
    (PowerSeries.subst_substInvOfIsUnit_left _ f.zero_constantCoeff _)

@[simp]
theorem toIso_toHom (f : FormalGroupHom F G)
    (hf : IsUnit (PowerSeries.coeff 1 f.toPowerSeries)) : (f.toIso hf).toHom = f := (rfl)

@[simp]
theorem toIso_invHom_toPowerSeries (f : FormalGroupHom F G)
    (hf : IsUnit (PowerSeries.coeff 1 f.toPowerSeries)) :
    (f.toIso hf).invHom.toPowerSeries = f.toPowerSeries.substInvOfIsUnit hf := (rfl)

end FormalGroupHom

end TauCeti
