/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.FormalGroup.CoordinateChange.Basic
public import TauCeti.RingTheory.FormalGroup.ZSMul

/-!
# Naturality of the formal logarithm

Let `F` be a formal group law over a `ℚ`-algebra `R`, with logarithm `log_F` and exponential
`exp_F` (`FormalGroup.log`, `FormalGroup.exp`). This file records how they transform under the
operations on formal group laws in scope.

* **Base change.** For a ring homomorphism `f : R →+* S` of `ℚ`-algebras, applying `f` to the
  coefficients of `log_F` and `exp_F` gives the logarithm and exponential of `F.map f`.
* **Homomorphisms.** A homomorphism `f : F → G` satisfies `log_G(f(X)) = f'(0) · log_F(X)`, so
  `f(X) = exp_G(f'(0) · log_F(X))`. Over a `ℚ`-algebra a homomorphism is therefore determined by
  its linear coefficient, and a strict isomorphism `f` satisfies `log_G(f(X)) = log_F(X)`. Dually
  `f(exp_F(X)) = exp_G(f'(0) · X)`.
* **Change of coordinate.** For a formal coordinate `φ = u X + ⋯`, the transported law `φ • F` has
  logarithm `u · log_F(φ⁻¹(X))`.
* **Multiplication series.** `log_F([n]_F(X)) = n · log_F(X)` and `[n]_F(X) = exp_F(n · log_F(X))`
  for every integer `n`, without commutativity of `F`.

## Main results

* `FormalGroup.map_log`, `FormalGroup.map_exp`: the logarithm and exponential commute with base
  change.
* `TauCeti.FormalGroupHom.subst_toPowerSeries_log`: `log_G(f(X)) = f'(0) · log_F(X)`.
* `TauCeti.FormalGroupHom.toPowerSeries_eq_subst_exp`: `f(X) = exp_G(f'(0) · log_F(X))`.
* `TauCeti.FormalGroupHom.coeff_one_injective`: over a `ℚ`-algebra, a homomorphism of formal group
  laws is determined by its linear coefficient.
* `TauCeti.FormalGroupHom.subst_exp_toPowerSeries`: `f(exp_F(X)) = exp_G(f'(0) · X)`.
* `TauCeti.FormalGroupIso.trans_logIso`: a strict isomorphism `f : F ≅ G` composed with `log_G`
  is `log_F`.
* `FormalGroup.log_smul`: the logarithm of `φ • F` is `u · log_F(φ⁻¹(X))`.
* `FormalGroup.subst_zsmulSeries_log`, `FormalGroup.zsmulSeries_eq_subst_exp`: the logarithm
  linearises integer multiplication, `[n]_F(X) = exp_F(n · log_F(X))`.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], IV.5.
* [M. Hazewinkel, *Formal Groups and Applications*][hazewinkel1978], I §5.
-/

public section

open MvPowerSeries TauCeti

namespace FormalGroup

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra ℚ R] [Algebra ℚ S] (F : FormalGroup R)

/-! ### Base change -/

/-- **The logarithm commutes with base change**: applying a ring homomorphism `f : R →+* S` of
`ℚ`-algebras to the coefficients of `log_F` gives the logarithm of `F.map f`. -/
@[simp]
theorem map_log (f : R →+* S) : F.log.map f = (F.map f).log := by
  ext n
  rw [PowerSeries.coeff_map, coeff_log, coeff_log, map_rat_smul, ← PowerSeries.coeff_map,
    F.map_invariantDifferential f]

/-- **The exponential commutes with base change**: applying a ring homomorphism `f : R →+* S` of
`ℚ`-algebras to the coefficients of `exp_F` gives the exponential of `F.map f`. -/
@[simp]
theorem map_exp (f : R →+* S) : F.exp.map f = (F.map f).exp := by
  have hE : PowerSeries.HasSubst (F.exp.map f) := .of_constantCoeff_zero' (by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map,
      PowerSeries.coeff_zero_eq_constantCoeff_apply, constantCoeff_exp, map_zero])
  -- `log_{F.map f}(exp_F.map f) = (log_F(exp_F)).map f = X`
  have h : PowerSeries.subst (F.exp.map f) (F.map f).log = PowerSeries.X := by
    have h := PowerSeries.map_subst (h := f)
      (PowerSeries.HasSubst.of_constantCoeff_zero' F.constantCoeff_exp) F.log
    -- `PowerSeries.map_subst` states its result with `MvPowerSeries.map` on the unit index type,
    -- which is `PowerSeries.map` by definition
    change PowerSeries.map f (PowerSeries.subst F.exp F.log) =
      PowerSeries.subst (F.exp.map f) (F.log.map f) at h
    rw [subst_exp_log, PowerSeries.map_X, map_log] at h
    exact h.symm
  have := (F.map f).subst_subst_log_exp hE
  rwa [h, PowerSeries.X_subst, eq_comm] at this

end FormalGroup

namespace TauCeti.FormalGroupHom

variable {R : Type*} [CommRing R] [Algebra ℚ R] {F G : FormalGroup R}

/-- **Naturality of the logarithm**: a homomorphism `f : F → G` of formal group laws over a
`ℚ`-algebra satisfies `log_G(f(X)) = f'(0) · log_F(X)`. -/
theorem subst_toPowerSeries_log (f : FormalGroupHom F G) :
    PowerSeries.subst f.toPowerSeries G.log = PowerSeries.coeff 1 f.toPowerSeries • F.log := by
  have h := F.toPowerSeries_eq_coeff_one_smul_log (G.logHom.comp f)
  rwa [coeff_one_comp, FormalGroup.logHom_toPowerSeries, FormalGroup.coeff_one_log, one_mul,
    comp_toPowerSeries, FormalGroup.logHom_toPowerSeries] at h

/-- Over a `ℚ`-algebra, a homomorphism `f : F → G` of formal group laws is
`f(X) = exp_G(f'(0) · log_F(X))`. -/
theorem toPowerSeries_eq_subst_exp (f : FormalGroupHom F G) :
    f.toPowerSeries =
      PowerSeries.subst (PowerSeries.coeff 1 f.toPowerSeries • F.log) G.exp := by
  rw [← f.subst_toPowerSeries_log, G.subst_subst_log_exp f.hasSubst]

/-- **Naturality of the exponential**: a homomorphism `f : F → G` of formal group laws over a
`ℚ`-algebra satisfies `f(exp_F(X)) = exp_G(f'(0) · X)`. -/
theorem subst_exp_toPowerSeries (f : FormalGroupHom F G) :
    PowerSeries.subst F.exp f.toPowerSeries =
      PowerSeries.subst (PowerSeries.coeff 1 f.toPowerSeries • PowerSeries.X) G.exp := by
  have hexp := PowerSeries.HasSubst.of_constantCoeff_zero' F.constantCoeff_exp
  conv_lhs => rw [f.toPowerSeries_eq_subst_exp]
  rw [PowerSeries.subst_comp_subst_apply
      (.smul' _ (.of_constantCoeff_zero' F.constantCoeff_log)) hexp,
    PowerSeries.subst_smul hexp, FormalGroup.subst_exp_log]

/-- Over a `ℚ`-algebra, a homomorphism of formal group laws is determined by its linear
coefficient. -/
theorem coeff_one_injective :
    Function.Injective fun f : FormalGroupHom F G ↦ PowerSeries.coeff 1 f.toPowerSeries := by
  intro f g h
  ext : 1
  rw [f.toPowerSeries_eq_subst_exp, g.toPowerSeries_eq_subst_exp]
  exact congrArg (fun c ↦ PowerSeries.subst (c • F.log) G.exp) h

end TauCeti.FormalGroupHom

namespace TauCeti.FormalGroupIso

variable {R : Type*} [CommRing R] [Algebra ℚ R] {F G : FormalGroup R}

/-- A strict isomorphism `f : F ≅ G` over a `ℚ`-algebra, followed by the logarithm of `G`, is the
logarithm of `F`. -/
@[simp]
theorem trans_logIso (f : FormalGroupIso F G) [f.IsStrict] : f.trans G.logIso = F.logIso :=
  F.eq_logIso _

end TauCeti.FormalGroupIso

namespace FormalGroup

variable {R : Type*} [CommRing R] [Algebra ℚ R] (F : FormalGroup R)

/-! ### Change of coordinate -/

/-- **The logarithm after a change of coordinate**: for a formal coordinate `φ = u X + ⋯`, the
logarithm of `φ • F` is `u · log_F(φ⁻¹(X))`. -/
theorem log_smul (φ : FormalCoordinate R) :
    (φ • F).log =
      (FormalCoordinate.linearCoeff φ : R) • PowerSeries.subst φ⁻¹.toPowerSeries F.log := by
  have h := (smulIso φ F).invHom.subst_toPowerSeries_log
  rw [smulIso_invHom_toPowerSeries, ← FormalCoordinate.val_linearCoeff, map_inv] at h
  rw [h, smul_smul, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_smul]

/-! ### Multiplication series -/

/-- **The logarithm linearises integer multiplication**: `log_F([n]_F(X)) = n · log_F(X)`. -/
@[simp]
theorem subst_zsmulSeries_log (n : ℤ) :
    PowerSeries.subst (F.zsmulSeries n) F.log = n • F.log := by
  have h := F.logHom.subst_zsmulSeries n
  rw [logHom_toPowerSeries] at h
  have hlog := PowerSeries.HasSubst.of_constantCoeff_zero' F.constantCoeff_log
  rw [h, zsmulSeries_𝔾ₐ, ← zsmul_eq_mul, ← PowerSeries.coe_substAlgHom hlog, map_zsmul,
    PowerSeries.coe_substAlgHom, PowerSeries.subst_X hlog]

/-- **The logarithm linearises multiplication by `n`**: `log_F([n]_F(X)) = n · log_F(X)`. -/
@[simp]
theorem subst_nsmulSeries_log (n : ℕ) :
    PowerSeries.subst (F.nsmulSeries n) F.log = n • F.log := by
  simpa using F.subst_zsmulSeries_log n

/-- Integer multiplication on a formal group law over a `ℚ`-algebra is
`[n]_F(X) = exp_F(n · log_F(X))`. -/
theorem zsmulSeries_eq_subst_exp (n : ℤ) :
    F.zsmulSeries n = PowerSeries.subst (n • F.log) F.exp := by
  rw [← F.subst_zsmulSeries_log, F.subst_subst_log_exp (F.hasSubst_zsmulSeries n)]

/-- Multiplication by `n` on a formal group law over a `ℚ`-algebra is
`[n]_F(X) = exp_F(n · log_F(X))`. -/
theorem nsmulSeries_eq_subst_exp (n : ℕ) :
    F.nsmulSeries n = PowerSeries.subst (n • F.log) F.exp := by
  simpa using F.zsmulSeries_eq_subst_exp n

end FormalGroup
