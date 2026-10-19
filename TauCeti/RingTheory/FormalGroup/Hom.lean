/-
Copyright (c) 2026 Wenrong Zou and The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wenrong Zou, The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.FormalGroup.Basic
public import TauCeti.RingTheory.MvPowerSeries.Substitution

/-!
# Homomorphisms and isomorphisms of formal group laws

A homomorphism is a power series with zero constant term carrying one formal group law to
another. Composition is substitution. An isomorphism carries a specified inverse homomorphism;
it is strict when its linear coefficient is one. These maps act on the native power-series
points, including points with nilpotent, not necessarily zero, constant coefficient.

The bundles `TauCeti.FormalGroupHom`, `TauCeti.FormalGroupIso`, and
`TauCeti.FormalGroupIso.IsStrict` are adapted from Wenrong Zou's Mathlib PR #38213
(https://github.com/leanprover-community/mathlib4/pull/38213). The action on points here uses
Mathlib's native `FormalGroup.Point` carrier and formal substitution, not evaluation in an
arbitrary topological algebra.
-/

public section

namespace TauCeti

open MvPowerSeries

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

/-- The series of a formal group homomorphism can be substituted. -/
theorem hasSubst (f : FormalGroupHom F G) : PowerSeries.HasSubst f.toPowerSeries :=
  .of_constantCoeff_zero' f.zero_constantCoeff

/-- The homomorphism equation at any two substitutable power series. -/
theorem hom_subst (f : FormalGroupHom F G) {σ : Type*} {a b : MvPowerSeries σ R}
    (ha : PowerSeries.HasSubst a) (hb : PowerSeries.HasSubst b) :
    PowerSeries.subst (subst ![a, b] F.toPowerSeries) f.toPowerSeries =
      subst ![PowerSeries.subst a f.toPowerSeries, PowerSeries.subst b f.toPowerSeries]
        G.toPowerSeries := by
  have hab : HasSubst ![a, b] := hasSubst_of_constantCoeff_nilpotent fun i => by
    fin_cases i <;> simpa
  have h := congrArg (subst ![a, b]) f.hom
  rw [subst_powerSeriesSubst hab (.of_constantCoeff_zero F.zero_constantCoeff),
    subst_comp_subst_apply (.toMvPowerSeries f.zero_constantCoeff) hab] at h
  simp only [PowerSeries.subst_toMvPowerSeries hab] at h
  convert h using 2
  funext i
  fin_cases i <;> rfl

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
    have h := congrArg (subst (fun i : Fin 2 => f.toPowerSeries.toMvPowerSeries i)) g.hom
    rw [subst_powerSeriesSubst hf (.of_constantCoeff_zero G.zero_constantCoeff),
      subst_comp_subst_apply (.toMvPowerSeries g.zero_constantCoeff) hf] at h
    rw [h]
    congr 1
    funext i
    rw [PowerSeries.subst_toMvPowerSeries hf]
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
  simpa only [applyPoint_val, FormalGroup.add_apply] using f.hom_subst x.prop y.prop

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

/-- The forward series evaluated at the inverse series is `X`. -/
@[simp]
theorem toHom_subst_invHom (f : FormalGroupIso F G) :
    PowerSeries.subst f.invHom.toPowerSeries f.toHom.toPowerSeries = PowerSeries.X := by
  have h := congrFun f.left_inv PowerSeries.X
  simpa [PowerSeries.subst_X f.toHom.hasSubst] using h

/-- The inverse series evaluated at the forward series is `X`. -/
@[simp]
theorem invHom_subst_toHom (f : FormalGroupIso F G) :
    PowerSeries.subst f.toHom.toPowerSeries f.invHom.toPowerSeries = PowerSeries.X := by
  have h := congrFun f.right_inv PowerSeries.X
  simpa [PowerSeries.subst_X f.invHom.hasSubst] using h

/-- A formal group isomorphism is determined by its forward homomorphism. -/
@[ext]
theorem ext {f g : FormalGroupIso F G} (h : f.toHom = g.toHom) : f = g := by
  have hinv : f.invHom = g.invHom := by
    apply FormalGroupHom.ext
    calc
      f.invHom.toPowerSeries = PowerSeries.subst
          (PowerSeries.subst g.invHom.toPowerSeries g.toHom.toPowerSeries)
          f.invHom.toPowerSeries := by
        rw [g.toHom_subst_invHom, PowerSeries.X_subst]
      _ = PowerSeries.subst g.invHom.toPowerSeries
          (PowerSeries.subst g.toHom.toPowerSeries f.invHom.toPowerSeries) :=
        (PowerSeries.subst_comp_subst_apply g.toHom.hasSubst g.invHom.hasSubst _).symm
      _ = g.invHom.toPowerSeries := by
        rw [← h, f.invHom_subst_toHom, PowerSeries.subst_X g.invHom.hasSubst]
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

/-- The additive equivalence induced on native power-series points. -/
noncomputable def toAddEquiv (f : FormalGroupIso F G) (σ : Type*) : F.Point σ ≃+ G.Point σ where
  toFun := f.toHom.applyPoint
  invFun := f.invHom.applyPoint
  left_inv x := by
    apply Subtype.ext
    simp only [FormalGroupHom.applyPoint_val,
      ← PowerSeries.subst_comp_subst_apply f.toHom.hasSubst x.prop,
      invHom_subst_toHom, PowerSeries.subst_X x.prop]
  right_inv x := by
    apply Subtype.ext
    simp only [FormalGroupHom.applyPoint_val,
      ← PowerSeries.subst_comp_subst_apply f.invHom.hasSubst x.prop,
      toHom_subst_invHom, PowerSeries.subst_X x.prop]
  map_add' := f.toHom.applyPoint_add

@[simp]
theorem toAddEquiv_apply (f : FormalGroupIso F G) {σ : Type*} (x : F.Point σ) :
    f.toAddEquiv σ x = f.toHom.applyPoint x := (rfl)

@[simp]
theorem toAddEquiv_symm_apply (f : FormalGroupIso F G) {σ : Type*} (x : G.Point σ) :
    (f.toAddEquiv σ).symm x = f.invHom.applyPoint x := (rfl)

end FormalGroupIso

end TauCeti
