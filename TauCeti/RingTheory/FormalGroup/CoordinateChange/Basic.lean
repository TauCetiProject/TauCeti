/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.FormalGroup.Basic
public import TauCeti.RingTheory.PowerSeries.Coordinate.Basic
import TauCeti.RingTheory.FormalGroup.AddInv
import TauCeti.RingTheory.MvPowerSeries.Substitution

/-!
# Changing the coordinate of a formal group law

A formal group law `F(X, Y)` over a commutative ring `R` is the group law of the formal group
written in one particular formal parameter. Changing the parameter by a formal coordinate
`φ = u X + ⋯` (`u` a unit, `TauCeti.FormalCoordinate R`) transports `F` to the formal group law

  `(φ • F)(X, Y) = φ(F(φ⁻¹(X), φ⁻¹(Y)))`,

for which `φ` is a homomorphism from `F`: `(φ • F)(φ(X), φ(Y)) = φ(F(X, Y))`. As `φ` has the
compositional inverse `φ⁻¹`, it is an isomorphism of formal group laws from `F` to `φ • F`, strict
when `u = 1`. The construction is a left action of the group of formal coordinates on formal group
laws, compatible with commutativity and with base change of the coefficient ring.

The universal instance of this action, a strict coordinate with indeterminate coefficients acting
on the universal formal group law, is what makes strict isomorphisms of formal group laws
representable by a polynomial ring over the Lazard ring.

## Main definitions

* `FormalGroup.changeCoordinate`: the formal group law `φ(F(φ⁻¹(X), φ⁻¹(Y)))`, written `φ • F`.
* `FormalGroup.instMulActionFormalCoordinate`: the action `φ • F` of formal coordinates on formal
  group laws.

## Main results

* `FormalGroup.subst_smul_toPowerSeries`: `(φ • F)(x, y) = φ(F(φ⁻¹(x), φ⁻¹(y)))` for all
  substitutable `x, y`.
* `FormalGroup.subst_toPowerSeries_eq_subst_smul_toPowerSeries`: `φ` is a homomorphism from `F`
  to `φ • F`, that is `φ(F(X, Y)) = (φ • F)(φ(X), φ(Y))`.
* `FormalGroup.instIsCommSMul`: changing coordinates preserves commutativity.
* `FormalGroup.map_smul`: changing coordinates commutes with base change.

## References

* [M. Hazewinkel, *Formal Groups and Applications*][hazewinkel1978], I §1.
* D. C. Ravenel, *Complex Cobordism and Stable Homotopy Groups of Spheres*, Appendix A2.1.
-/

public section

open MvPowerSeries TauCeti

namespace FormalGroup

variable {R S : Type*} [CommRing R] [CommRing S] {σ : Type*}

section Series

variable (φ : FormalCoordinate R) (F : FormalGroup R)

/-- The series `φ(F(φ⁻¹(X), φ⁻¹(Y)))` underlying `φ • F`. -/
private noncomputable def coordinateChangeSeries : MvPowerSeries (Fin 2) R :=
  PowerSeries.subst
    (F.toPowerSeries.subst
      ![PowerSeries.subst (X 0 : MvPowerSeries (Fin 2) R) φ⁻¹.toPowerSeries,
        PowerSeries.subst (X 1 : MvPowerSeries (Fin 2) R) φ⁻¹.toPowerSeries])
    φ.toPowerSeries

private theorem subst_coordinateChangeSeries {x y : MvPowerSeries σ R}
    (hx : PowerSeries.HasSubst x) (hy : PowerSeries.HasSubst y) :
    (coordinateChangeSeries φ F).subst ![x, y] =
      PowerSeries.subst
        (F.toPowerSeries.subst
          ![PowerSeries.subst x φ⁻¹.toPowerSeries, PowerSeries.subst y φ⁻¹.toPowerSeries])
        φ.toPowerSeries := by
  have hxy := hasSubst_finTwo hx hy
  have hX (i : Fin 2) := PowerSeries.HasSubst.X (S := R) i
  rw [coordinateChangeSeries, subst_powerSeriesSubst hxy
      (F.hasSubst_subst_pair (φ⁻¹.hasSubst_subst (hX 0)) (φ⁻¹.hasSubst_subst (hX 1))),
    subst_comp_subst_apply (hasSubst_finTwo (φ⁻¹.hasSubst_subst (hX 0))
      (φ⁻¹.hasSubst_subst (hX 1))) hxy]
  congr 2
  funext s
  fin_cases s <;> simp [subst_powerSeriesSubst hxy (hX _), subst_X hxy]

end Series

/-- The **change of coordinate** of a formal group law: the formal group law
`φ(F(φ⁻¹(X), φ⁻¹(Y)))` obtained by transporting `F` along the formal coordinate `φ`. It is
written `φ • F` (`FormalGroup.instMulActionFormalCoordinate`), and its API is stated for `φ • F`. -/
noncomputable def changeCoordinate (F : FormalGroup R) (φ : FormalCoordinate R) :
    FormalGroup R where
  toPowerSeries := coordinateChangeSeries φ F
  zero_constantCoeff :=
    PowerSeries.constantCoeff_subst_eq_zero
      (constantCoeff_subst_eq_zero
        (hasSubst_finTwo (φ⁻¹.hasSubst_subst (PowerSeries.HasSubst.X 0))
          (φ⁻¹.hasSubst_subst (PowerSeries.HasSubst.X 1)))
        (fun s ↦ by
          fin_cases s <;>
            exact PowerSeries.constantCoeff_subst_eq_zero (constantCoeff_X _) _
              φ⁻¹.constantCoeff_toPowerSeries)
        F.zero_constantCoeff)
      _ φ.constantCoeff_toPowerSeries
  lin_coeff_X := by
    rw [← coeff_subst_X_zero, subst_coordinateChangeSeries φ F PowerSeries.HasSubst.X'
      PowerSeries.HasSubst.zero, PowerSeries.subst_zero_of_constantCoeff_zero
      φ⁻¹.constantCoeff_toPowerSeries,
      F.add_zero (φ⁻¹.hasSubst_subst PowerSeries.HasSubst.X'),
      φ.subst_subst_inv PowerSeries.HasSubst.X', PowerSeries.coeff_one_X]
  lin_coeff_Y := by
    rw [← coeff_subst_zero_X, subst_coordinateChangeSeries φ F PowerSeries.HasSubst.zero
      PowerSeries.HasSubst.X', PowerSeries.subst_zero_of_constantCoeff_zero
      φ⁻¹.constantCoeff_toPowerSeries,
      F.zero_add (φ⁻¹.hasSubst_subst PowerSeries.HasSubst.X'),
      φ.subst_subst_inv PowerSeries.HasSubst.X', PowerSeries.coeff_one_X]
  assoc := by
    have hY (i : Fin 3) := PowerSeries.HasSubst.X (S := R) i
    have hψ (i : Fin 3) := φ⁻¹.hasSubst_subst (hY i)
    -- both sides are `φ(F(F(φ⁻¹(Y₀), φ⁻¹(Y₁)), φ⁻¹(Y₂)))`, as `φ⁻¹ ∘ φ` cancels inside
    rw [subst_coordinateChangeSeries φ F (hY 0) (hY 1),
      subst_coordinateChangeSeries φ F (hY 1) (hY 2),
      subst_coordinateChangeSeries φ F
        (φ.hasSubst_subst (F.hasSubst_subst_pair (hψ 0) (hψ 1))) (hY 2),
      subst_coordinateChangeSeries φ F (hY 0)
        (φ.hasSubst_subst (F.hasSubst_subst_pair (hψ 1) (hψ 2))),
      φ.subst_inv_subst (F.hasSubst_subst_pair (hψ 0) (hψ 1)),
      φ.subst_inv_subst (F.hasSubst_subst_pair (hψ 1) (hψ 2)), F.assoc' (hψ 0) (hψ 1) (hψ 2)]

/-- Formal coordinates act on formal group laws by change of coordinate,
`φ • F = φ(F(φ⁻¹(X), φ⁻¹(Y)))`. -/
noncomputable instance instSMulFormalCoordinate : SMul (FormalCoordinate R) (FormalGroup R) :=
  ⟨fun φ F ↦ F.changeCoordinate φ⟩

/-- `F.changeCoordinate φ` is the action `φ • F`. -/
@[simp]
theorem changeCoordinate_eq_smul (F : FormalGroup R) (φ : FormalCoordinate R) :
    F.changeCoordinate φ = φ • F :=
  (rfl)

/-- The series of `φ • F` is `φ(F(φ⁻¹(X), φ⁻¹(Y)))`. -/
theorem smul_toPowerSeries (φ : FormalCoordinate R) (F : FormalGroup R) :
    (φ • F).toPowerSeries =
      PowerSeries.subst
        (F.toPowerSeries.subst
          ![PowerSeries.subst (X 0 : MvPowerSeries (Fin 2) R) φ⁻¹.toPowerSeries,
            PowerSeries.subst (X 1 : MvPowerSeries (Fin 2) R) φ⁻¹.toPowerSeries])
        φ.toPowerSeries :=
  (rfl)

/-- The formal group law `φ • F` at substitutable `x, y` is `φ(F(φ⁻¹(x), φ⁻¹(y)))`. -/
theorem subst_smul_toPowerSeries (φ : FormalCoordinate R) (F : FormalGroup R)
    {x y : MvPowerSeries σ R} (hx : PowerSeries.HasSubst x) (hy : PowerSeries.HasSubst y) :
    (φ • F).toPowerSeries.subst ![x, y] =
      PowerSeries.subst
        (F.toPowerSeries.subst
          ![PowerSeries.subst x φ⁻¹.toPowerSeries, PowerSeries.subst y φ⁻¹.toPowerSeries])
        φ.toPowerSeries :=
  subst_coordinateChangeSeries φ F hx hy

/-- A change of coordinate `φ` is additive from `F` to `φ • F` on substitutable series:
`(φ • F)(φ(x), φ(y)) = φ(F(x, y))`. -/
theorem subst_smul_toPowerSeries_subst (φ : FormalCoordinate R) (F : FormalGroup R)
    {x y : MvPowerSeries σ R} (hx : PowerSeries.HasSubst x) (hy : PowerSeries.HasSubst y) :
    (φ • F).toPowerSeries.subst
        ![PowerSeries.subst x φ.toPowerSeries, PowerSeries.subst y φ.toPowerSeries] =
      PowerSeries.subst (F.toPowerSeries.subst ![x, y]) φ.toPowerSeries := by
  rw [subst_smul_toPowerSeries φ F (φ.hasSubst_subst hx) (φ.hasSubst_subst hy),
    φ.subst_inv_subst hx, φ.subst_inv_subst hy]

/-- **A change of coordinate `φ` is a homomorphism from `F` to `φ • F`**:
`φ(F(X, Y)) = (φ • F)(φ(X), φ(Y))`. -/
theorem subst_toPowerSeries_eq_subst_smul_toPowerSeries (φ : FormalCoordinate R)
    (F : FormalGroup R) :
    PowerSeries.subst F.toPowerSeries φ.toPowerSeries =
      (φ • F).toPowerSeries.subst
        ![PowerSeries.subst (X 0 : MvPowerSeries (Fin 2) R) φ.toPowerSeries,
          PowerSeries.subst (X 1 : MvPowerSeries (Fin 2) R) φ.toPowerSeries] := by
  rw [subst_smul_toPowerSeries_subst φ F (PowerSeries.HasSubst.X 0) (PowerSeries.HasSubst.X 1),
    finTwo_X_eq_X, subst_self, id]

/-- Formal coordinates act on formal group laws: `1 • F = F` and `(φ * ψ) • F = φ • (ψ • F)`. -/
noncomputable instance instMulActionFormalCoordinate :
    MulAction (FormalCoordinate R) (FormalGroup R) where
  one_smul F := FormalGroup.ext <| by
    rw [smul_toPowerSeries, inv_one, FormalCoordinate.toPowerSeries_one,
      PowerSeries.subst_X (PowerSeries.HasSubst.X 0),
      PowerSeries.subst_X (PowerSeries.HasSubst.X 1),
      finTwo_X_eq_X, subst_self, id,
      PowerSeries.subst_X (PowerSeries.HasSubst.of_constantCoeff_zero F.zero_constantCoeff)]
  mul_smul φ ψ F := FormalGroup.ext <| by
    have hX (i : Fin 2) := PowerSeries.HasSubst.X (S := R) i
    have hφ (i : Fin 2) := φ⁻¹.hasSubst_subst (hX i)
    rw [smul_toPowerSeries, smul_toPowerSeries φ, subst_smul_toPowerSeries ψ F (hφ 0) (hφ 1),
      mul_inv_rev, FormalCoordinate.subst_toPowerSeries_mul _ _ (hX 0),
      FormalCoordinate.subst_toPowerSeries_mul _ _ (hX 1),
      FormalCoordinate.subst_toPowerSeries_mul _ _
        (F.hasSubst_subst_pair (ψ⁻¹.hasSubst_subst (hφ 0)) (ψ⁻¹.hasSubst_subst (hφ 1)))]

/-- **Changing coordinates preserves commutativity.** -/
instance instIsCommSMul (φ : FormalCoordinate R) (F : FormalGroup R) [F.IsComm] :
    (φ • F).IsComm where
  comm := by
    have hX (i : Fin 2) := PowerSeries.HasSubst.X (S := R) i
    have hφ (i : Fin 2) := φ⁻¹.hasSubst_subst (hX i)
    rw [subst_smul_toPowerSeries φ F (hX 1) (hX 0),
      F.comm' (hφ 1) (hφ 0), smul_toPowerSeries]

/-- **Changing coordinates commutes with base change**: for `f : R →+* S`, the base change of
`φ • F` is the base change of `φ` acting on the base change of `F`. -/
theorem map_smul (f : R →+* S) (φ : FormalCoordinate R) (F : FormalGroup R) :
    (φ • F).map f = FormalCoordinate.map f φ • F.map f := FormalGroup.ext <| by
  have hX (i : Fin 2) := PowerSeries.HasSubst.X (S := R) i
  have hφ (i : Fin 2) := φ⁻¹.hasSubst_subst (hX i)
  rw [map_toPowerSeries, smul_toPowerSeries, smul_toPowerSeries, ← map_inv,
    PowerSeries.map_subst (F.hasSubst_subst_pair (hφ 0) (hφ 1)),
    MvPowerSeries.map_subst (hasSubst_finTwo (hφ 0) (hφ 1)), map_toPowerSeries,
    FormalCoordinate.toPowerSeries_map, FormalCoordinate.toPowerSeries_map]
  congr 2
  funext s
  fin_cases s <;> simp [PowerSeries.map_subst (hX _)]

end FormalGroup
