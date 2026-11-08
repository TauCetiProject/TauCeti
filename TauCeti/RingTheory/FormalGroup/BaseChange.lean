/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.FormalGroup.Basic

/-!
# Base change of formal group laws

Mathlib constructs the base change `F.map f` of a formal group law by applying `f` to every
coefficient. This file supplies its basic functorial API: identity and composition laws,
preservation and reflection of commutativity, descent along injective coefficient maps, and
compatibility with the additive and multiplicative formal group laws.

## Main results

* `FormalGroup.map_id` and `FormalGroup.map_comp`: base change is functorial.
* `FormalGroup.map_injective`: base change along an injective homomorphism is injective.
* `FormalGroup.isComm_map` and `FormalGroup.isComm_of_map`: preservation and reflection of
  commutativity.
* `FormalGroup.ofMap`: descend a law whose coefficients lift along an injective map.
* `FormalGroup.map_𝔾ₐ` and `FormalGroup.map_𝔾ₘ`: the standard laws are stable under base change.
* `FormalGroup.subst_map_toPowerSeries_map`: a power series additive along `F` stays additive along
  `F` after base change.
-/

public section

open MvPowerSeries

namespace FormalGroup

variable {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]

/-- Base change along an injective coefficient homomorphism is injective. -/
theorem map_injective {f : R →+* S} (hf : Function.Injective f) :
    Function.Injective (fun F : FormalGroup R ↦ F.map f) := by
  intro F G h
  apply FormalGroup.ext
  ext1 d
  apply hf
  simpa only [map_toPowerSeries, coeff_map] using
    congrArg (fun K ↦ coeff d K.toPowerSeries) h

/-- Base-changing a formal group law along the identity homomorphism changes nothing. -/
@[simp]
theorem map_id (F : FormalGroup R) : F.map (RingHom.id R) = F := by
  ext
  simp

/-- Successive base changes of a formal group law agree with base change along the composite. -/
@[simp]
theorem map_comp (F : FormalGroup R) (f : R →+* S) (g : S →+* T) :
    (F.map f).map g = F.map (g.comp f) := by
  ext
  simp

/-- A base change of a commutative formal group law is commutative. -/
instance isComm_map (F : FormalGroup R) [F.IsComm] (f : R →+* S) : (F.map f).IsComm where
  comm := by
    have h := congrArg (MvPowerSeries.map f) (IsComm.comm (F := F))
    rw [MvPowerSeries.map_subst HasSubst.X_X] at h
    rw [map_toPowerSeries]
    calc
      _ = subst (fun i ↦ MvPowerSeries.map f (![X 1, X 0] i))
          (MvPowerSeries.map f F.toPowerSeries) := h
      _ = _ := by
        congr 1
        funext i
        fin_cases i <;> simp

/-- An injective coefficient map reflects commutativity. -/
theorem isComm_of_map {F : FormalGroup R} {f : R →+* S} (hf : Function.Injective f)
    [(F.map f).IsComm] : F.IsComm where
  comm := by
    ext d
    apply hf
    have h := congrArg (coeff d) (IsComm.comm (F := F.map f))
    rw [map_toPowerSeries] at h
    rw [← coeff_map, ← coeff_map, MvPowerSeries.map_subst HasSubst.X_X]
    convert h using 2
    congr 2
    funext i
    fin_cases i <;> simp

/-- Descend a formal group law along an injective coefficient map, given a power series
whose coefficient extension is that law. -/
def ofMap (f : R →+* S) (hf : Function.Injective f) (g : MvPowerSeries (Fin 2) R)
    (F : FormalGroup S) (hg : g.map f = F.toPowerSeries) : FormalGroup R where
  toPowerSeries := g
  zero_constantCoeff := hf (by rw [← constantCoeff_map, hg, F.zero_constantCoeff, map_zero])
  lin_coeff_X := hf (by rw [← coeff_map, hg, F.lin_coeff_X, map_one])
  lin_coeff_Y := hf (by rw [← coeff_map, hg, F.lin_coeff_Y, map_one])
  assoc := by
    have h₀ : constantCoeff g = 0 :=
      hf (by rw [← constantCoeff_map, hg, F.zero_constantCoeff, map_zero])
    have hv (a b : MvPowerSeries (Fin 3) R) :
        (fun i ↦ (![a, b] i).map f) = ![a.map f, b.map f] := by
      funext i
      fin_cases i <;> rfl
    have hmap : ((g.subst ![g.subst ![X 0, X 1], X 2]).map f :
        MvPowerSeries (Fin 3) S) = (g.subst ![X 0, g.subst ![X 1, X 2]]).map f := by
      simp only [MvPowerSeries.map_subst (HasSubst.cons_subst_zero_left (0 : Fin 3) 1 2 h₀),
        MvPowerSeries.map_subst (HasSubst.cons_subst_zero_right (0 : Fin 3) 1 2 h₀), hv,
        MvPowerSeries.map_subst HasSubst.X_X, map_X, hg, F.assoc]
    ext d
    apply hf
    simpa only [coeff_map] using congrArg (coeff d) hmap

/-- The underlying series of the descended formal group is the given series. -/
@[simp]
theorem ofMap_toPowerSeries (f : R →+* S) (hf : Function.Injective f)
    (g : MvPowerSeries (Fin 2) R) (F : FormalGroup S) (hg : g.map f = F.toPowerSeries) :
    (ofMap f hf g F hg).toPowerSeries = g := (rfl)

/-- Extending coefficients of the descended formal group recovers the original law. -/
@[simp]
theorem map_ofMap (f : R →+* S) (hf : Function.Injective f)
    (g : MvPowerSeries (Fin 2) R) (F : FormalGroup S) (hg : g.map f = F.toPowerSeries) :
    (ofMap f hf g F hg).map f = F := FormalGroup.ext hg

/-- The additive formal group law is unchanged by base change. -/
@[simp]
theorem map_𝔾ₐ (f : R →+* S) : (𝔾ₐ (R := R)).map f = 𝔾ₐ := by
  ext
  simp [FormalGroup.𝔾ₐ]

/-- The multiplicative formal group law is unchanged by base change. -/
@[simp]
theorem map_𝔾ₘ (f : R →+* S) : (𝔾ₘ (R := R)).map f = 𝔾ₘ := by
  ext
  simp [FormalGroup.𝔾ₘ]

/-- A power series additive along `F` stays additive along `F` after base change. -/
theorem subst_map_toPowerSeries_map (F : FormalGroup R) (f : R →+* S) {g : PowerSeries R}
    (hg : PowerSeries.subst F.toPowerSeries g =
      PowerSeries.subst (X 0) g + PowerSeries.subst (X 1) g) :
    PowerSeries.subst (F.map f).toPowerSeries (g.map f) =
      PowerSeries.subst (X 0) (g.map f) + PowerSeries.subst (X 1) (g.map f) := by
  have := congrArg (MvPowerSeries.map f) hg
  rwa [map_add, PowerSeries.map_subst (.of_constantCoeff_zero F.zero_constantCoeff),
    PowerSeries.map_subst (.X 0), PowerSeries.map_subst (.X 1), map_X, map_X,
    ← map_toPowerSeries] at this

end FormalGroup
