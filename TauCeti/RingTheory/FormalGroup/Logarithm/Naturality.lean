/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.FormalGroup.CoordinateChange.Basic
public import TauCeti.RingTheory.FormalGroup.Logarithm.Basic

/-!
# Naturality of the formal logarithm

Over a `ℚ`-algebra `R`, every formal group law `F` has a logarithm `log_F`, the unique power series
`X + ⋯` that is additive along `F`, with compositional inverse `exp_F` (see
`TauCeti.RingTheory.FormalGroup.Logarithm.Basic`, which also proves the base-change laws
`FormalGroup.map_log` and `FormalGroup.map_exp`). This file compares the logarithms of formal group
laws related by homomorphisms and by changes of coordinate.

* **Homomorphisms.** If `f : F → G` is a homomorphism of formal group laws, then `log_G ∘ f` is
  additive along `F` with linear coefficient `f'(0)`, so `log_G(f(X)) = f'(0) · log_F(X)` and
  `f(X) = exp_G(f'(0) · log_F(X))`. Consequently a homomorphism is determined by its linear
  coefficient, and every `c : R` is the linear coefficient of exactly one homomorphism `F → G`:
  over a `ℚ`-algebra, `Hom(F, G) ≃ R`. A strict isomorphism followed by `log_G` is `log_F`.
* **Coordinate change.** For a formal coordinate `φ = u X + ⋯`, the formal group law `φ • F`
  has logarithm `u · log_F(φ⁻¹(X))` and exponential `φ(exp_F(u⁻¹ X))`.

## Main results

* `TauCeti.FormalGroupHom.subst_log`: `log_G(f(X)) = f'(0) · log_F(X)`.
* `TauCeti.FormalGroupHom.toPowerSeries_eq_subst_exp`: `f(X) = exp_G(f'(0) · log_F(X))`.
* `TauCeti.FormalGroupHom.coeffOneEquiv`: homomorphisms `F → G` correspond to their linear
  coefficients.
* `TauCeti.FormalGroupIso.trans_logIso`: for a strict isomorphism `f : F ≅ G`,
  `log_G ∘ f = log_F` as strict isomorphisms to the additive formal group law.
* `FormalGroup.log_smul` and `FormalGroup.exp_smul`: the logarithm and exponential after a change
  of coordinate.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], IV.5.
* M. Hazewinkel, *Formal Groups and Applications*, Academic Press (1978).
-/

public section

open TauCeti

namespace TauCeti.FormalGroupHom

variable {R : Type*} [CommRing R] [Algebra ℚ R] {F G : FormalGroup R}

/-- **The logarithm is natural along homomorphisms**: for a homomorphism `f : F → G`,
`log_G(f(X)) = f'(0) · log_F(X)`. -/
theorem subst_log (f : FormalGroupHom F G) :
    PowerSeries.subst f.toPowerSeries G.log = PowerSeries.coeff 1 f.toPowerSeries • F.log := by
  have h := (G.logHom.comp f).toPowerSeries_eq_coeff_one_smul_log
  rw [coeff_one_comp, FormalGroup.logHom_toPowerSeries, FormalGroup.coeff_one_log, one_mul] at h
  simpa only [comp_toPowerSeries, FormalGroup.logHom_toPowerSeries] using h

/-- **Every homomorphism is an exponential of a multiple of the logarithm**: a homomorphism
`f : F → G` is `f(X) = exp_G(f'(0) · log_F(X))`. -/
theorem toPowerSeries_eq_subst_exp (f : FormalGroupHom F G) :
    f.toPowerSeries =
      PowerSeries.subst (PowerSeries.coeff 1 f.toPowerSeries • F.log) G.exp := by
  rw [← f.subst_log, ← PowerSeries.subst_comp_subst_apply
    (.of_constantCoeff_zero' G.constantCoeff_log) f.hasSubst, G.subst_log_exp,
    PowerSeries.subst_X f.hasSubst]

/-- Over a `ℚ`-algebra, a homomorphism of formal group laws is determined by its linear
coefficient. -/
theorem coeff_one_injective :
    Function.Injective fun f : FormalGroupHom F G ↦ PowerSeries.coeff 1 f.toPowerSeries :=
  fun f g h ↦ FormalGroupHom.ext <| by
    rw [f.toPowerSeries_eq_subst_exp, g.toPowerSeries_eq_subst_exp]
    exact congrArg (fun c ↦ PowerSeries.subst (c • F.log) G.exp) h

variable (F G) in
/-- The homomorphism `exp_G(c · log_F(X))` from `F` to `G`, with linear coefficient `c`. -/
noncomputable def ofCoeffOne (c : R) : FormalGroupHom F G :=
  G.expHom.comp
    { toPowerSeries := c • F.log
      zero_constantCoeff := by simp
      hom := (hom_additive_iff (by simp)).mpr (F.subst_toPowerSeries_eq_add_iff.mpr ⟨c, rfl⟩) }

/-- The series of `ofCoeffOne F G c` is `exp_G(c · log_F(X))`. -/
theorem ofCoeffOne_toPowerSeries (c : R) :
    (ofCoeffOne F G c).toPowerSeries = PowerSeries.subst (c • F.log) G.exp := by
  simp [ofCoeffOne]

/-- `ofCoeffOne F G c` has linear coefficient `c`. -/
@[simp]
theorem coeff_one_ofCoeffOne (c : R) :
    PowerSeries.coeff 1 (ofCoeffOne F G c).toPowerSeries = c := by
  rw [ofCoeffOne_toPowerSeries, PowerSeries.coeff_one_subst (by simp)]
  simp

variable (F G) in
/-- **Homomorphisms over a `ℚ`-algebra are classified by their linear coefficient**: `f ↦ f'(0)`
is a bijection from the homomorphisms `F → G` to `R`, with inverse `c ↦ exp_G(c · log_F(X))`. -/
noncomputable def coeffOneEquiv : FormalGroupHom F G ≃ R where
  toFun f := PowerSeries.coeff 1 f.toPowerSeries
  invFun := ofCoeffOne F G
  left_inv _ := coeff_one_injective (coeff_one_ofCoeffOne _)
  right_inv := coeff_one_ofCoeffOne

@[simp]
theorem coeffOneEquiv_apply (f : FormalGroupHom F G) :
    coeffOneEquiv F G f = PowerSeries.coeff 1 f.toPowerSeries := (rfl)

@[simp]
theorem coeffOneEquiv_symm_apply (c : R) : (coeffOneEquiv F G).symm c = ofCoeffOne F G c := (rfl)

end TauCeti.FormalGroupHom

namespace TauCeti.FormalGroupIso

variable {R : Type*} [CommRing R] [Algebra ℚ R] {F G : FormalGroup R}

/-- A strict isomorphism `f : F ≅ G` followed by the logarithm of `G` is the logarithm of `F`. -/
@[simp]
theorem trans_logIso (f : FormalGroupIso F G) [f.IsStrict] : f.trans G.logIso = F.logIso :=
  F.eq_logIso _

end TauCeti.FormalGroupIso

namespace FormalGroup

variable {R : Type*} [CommRing R] [Algebra ℚ R] (F : FormalGroup R)

/-- **The logarithm after a change of coordinate**: for a formal coordinate `φ = u X + ⋯`, the
logarithm of `φ • F` is `u · log_F(φ⁻¹(X))`. -/
theorem log_smul (φ : FormalCoordinate R) :
    (φ • F).log =
      (FormalCoordinate.linearCoeff φ : R) • PowerSeries.subst φ⁻¹.toPowerSeries F.log := by
  rw [← smulIso_invHom_toPowerSeries φ F, (smulIso φ F).invHom.subst_log,
    smulIso_invHom_toPowerSeries, ← FormalCoordinate.val_linearCoeff, map_inv, smul_smul,
    Units.mul_inv, one_smul]

/-- **The exponential after a change of coordinate**: for a formal coordinate `φ = u X + ⋯`, the
exponential of `φ • F` is `φ(exp_F(u⁻¹ X))`. -/
theorem exp_smul (φ : FormalCoordinate R) :
    (φ • F).exp = PowerSeries.subst
      (PowerSeries.rescale ((FormalCoordinate.linearCoeff φ)⁻¹ : Rˣ).val F.exp)
      φ.toPowerSeries := by
  set v : R := ((FormalCoordinate.linearCoeff φ)⁻¹ : Rˣ).val
  have hv : PowerSeries.HasSubst (v • PowerSeries.X : PowerSeries R) :=
    .of_constantCoeff_zero' (by simp)
  have hE : PowerSeries.HasSubst (PowerSeries.rescale v F.exp) :=
    .of_constantCoeff_zero' (by
      rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_rescale]
      simp)
  refine ((φ • F).eq_exp_of_subst_log_eq_X (φ.hasSubst_subst hE) ?_).symm
  -- `u · log_F(φ⁻¹(φ(exp_F(u⁻¹ X)))) = u · log_F(exp_F(u⁻¹ X)) = u · u⁻¹ X = X`
  rw [log_smul, PowerSeries.subst_smul (φ.hasSubst_subst hE),
    PowerSeries.subst_comp_subst_apply φ⁻¹.hasSubst (φ.hasSubst_subst hE),
    φ.subst_inv_subst hE, PowerSeries.rescale_eq_subst,
    ← PowerSeries.subst_comp_subst_apply (.of_constantCoeff_zero' F.constantCoeff_exp) hv,
    subst_exp_log, PowerSeries.subst_X hv, smul_smul, Units.mul_inv, one_smul]

end FormalGroup
