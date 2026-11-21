/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.Prod
public import TauCeti.Algebra.Lie.Equiv
public import TauCeti.Algebra.Lie.Solvable.Equiv
import Mathlib.LinearAlgebra.Projection
import TauCeti.Algebra.Lie.Prod

/-!
# Centre/derived assembly of Lie algebra equivalences

When `IsCompl (center R L) (derivedSeries R L 1)`, addition yields `Z(L) × [L, L] ≃ₗ⁅R⁆ L`
(`LieEquiv.prodCenterDerivedEquiv`), and automorphisms of `Z(L)` and `[L, L]` assemble into
`LieEquiv.ofCenterDerived`, reconstructing any automorphism
(`LieEquiv.ofCenterDerived_restrictCenter_restrictDerivedSeries`) and giving uniqueness from the two
restrictions (`LieEquiv.eq_of_restrictCenter_eq_of_restrictDerivedSeries_eq`).

## Main definitions and results

* `LieEquiv.prodCenterDerivedEquiv`, `LieEquiv.ofCenterDerived`,
  `LieEquiv.eq_of_restrictCenter_eq_of_restrictDerivedSeries_eq`,
  `LieEquiv.ofCenterDerived_restrictCenter_restrictDerivedSeries`.
-/

public section

open LieAlgebra

namespace LieEquiv

variable {R L M : Type*} [CommRing R] [LieRing L] [LieAlgebra R L] [LieRing M] [LieAlgebra R M]

/-- When the centre and derived ideal of `L` are complementary, addition gives a Lie algebra
equivalence `Z(L) × [L, L] ≃ₗ⁅R⁆ L`. -/
noncomputable def prodCenterDerivedEquiv
    (hcompl : IsCompl (center R L) (derivedSeries R L 1)) :
    (center R L × derivedSeries R L 1) ≃ₗ⁅R⁆ L where
  __ := Submodule.prodEquivOfIsCompl (center R L).toSubmodule (derivedSeries R L 1).toSubmodule
    (LieSubmodule.isCompl_toSubmodule.mpr hcompl)
  map_lie' {p q} := by
    have hz (z : center R L) (y : L) : ⁅y, (z : L)⁆ = 0 :=
      (LieModule.mem_maxTrivSubmodule R L L z).mp z.property y
    have hzl (z : center R L) (y : L) : ⁅(z : L), y⁆ = 0 := by
      rw [← lie_skew, hz z y, neg_zero]
    simp only [LinearEquiv.toFun_eq_coe, Submodule.coe_prodEquivOfIsCompl',
      LieAlgebra.Prod.bracket_apply, LieIdeal.coe_bracket_of_module, LieSubmodule.coe_bracket,
      lie_add, add_lie, hz, hzl, zero_add]

@[simp, grind =]
theorem prodCenterDerivedEquiv_apply
    (hcompl : IsCompl (center R L) (derivedSeries R L 1))
    (p : center R L × derivedSeries R L 1) :
    prodCenterDerivedEquiv hcompl p = (p.1 : L) + p.2 := (rfl)

@[simp]
theorem prodCenterDerivedEquiv_symm_center
    (hcompl : IsCompl (center R L) (derivedSeries R L 1)) (z : center R L) :
    (prodCenterDerivedEquiv hcompl).symm (z : L) = (z, 0) :=
  (prodCenterDerivedEquiv hcompl).injective (by simp)

@[simp]
theorem prodCenterDerivedEquiv_symm_derivedSeries
    (hcompl : IsCompl (center R L) (derivedSeries R L 1)) (d : derivedSeries R L 1) :
    (prodCenterDerivedEquiv hcompl).symm (d : L) = (0, d) :=
  (prodCenterDerivedEquiv hcompl).injective (by simp)

/-- Assemble automorphisms of `Z(L)` and `[L, L]` into an automorphism of `L` when the centre and
derived ideal are complementary. -/
noncomputable def ofCenterDerived
    (hcompl : IsCompl (center R L) (derivedSeries R L 1))
    (θZ : center R L ≃ₗ⁅R⁆ center R L)
    (θD : derivedSeries R L 1 ≃ₗ⁅R⁆ derivedSeries R L 1) : L ≃ₗ⁅R⁆ L :=
  (prodCenterDerivedEquiv hcompl).symm.trans
    ((LieEquiv.prodCongr θZ θD).trans (prodCenterDerivedEquiv hcompl))

@[simp]
theorem ofCenterDerived_apply_center
    (hcompl : IsCompl (center R L) (derivedSeries R L 1))
    (θZ : center R L ≃ₗ⁅R⁆ center R L) (θD : derivedSeries R L 1 ≃ₗ⁅R⁆ derivedSeries R L 1)
    (z : center R L) : ofCenterDerived hcompl θZ θD (z : L) = θZ z := by simp [ofCenterDerived]

@[simp]
theorem ofCenterDerived_apply_derivedSeries
    (hcompl : IsCompl (center R L) (derivedSeries R L 1))
    (θZ : center R L ≃ₗ⁅R⁆ center R L) (θD : derivedSeries R L 1 ≃ₗ⁅R⁆ derivedSeries R L 1)
    (d : derivedSeries R L 1) : ofCenterDerived hcompl θZ θD (d : L) = θD d := by
  simp [ofCenterDerived]

@[simp]
theorem restrictCenter_ofCenterDerived
    (hcompl : IsCompl (center R L) (derivedSeries R L 1))
    (θZ : center R L ≃ₗ⁅R⁆ center R L) (θD : derivedSeries R L 1 ≃ₗ⁅R⁆ derivedSeries R L 1) :
    (ofCenterDerived hcompl θZ θD).restrictCenter = θZ := by ext z; simp

@[simp]
theorem restrictDerivedSeries_ofCenterDerived
    (hcompl : IsCompl (center R L) (derivedSeries R L 1))
    (θZ : center R L ≃ₗ⁅R⁆ center R L) (θD : derivedSeries R L 1 ≃ₗ⁅R⁆ derivedSeries R L 1) :
    (ofCenterDerived hcompl θZ θD).restrictDerivedSeries 1 = θD := by ext d; simp

/-- Two Lie algebra equivalences out of a Lie algebra with `L = Z(L) ⊕ [L, L]` are equal if they
have the same restrictions to the centre and to the derived ideal. -/
theorem eq_of_restrictCenter_eq_of_restrictDerivedSeries_eq
    (hcompl : IsCompl (center R L) (derivedSeries R L 1)) {e₁ e₂ : L ≃ₗ⁅R⁆ M}
    (hZ : e₁.restrictCenter = e₂.restrictCenter)
    (hD : e₁.restrictDerivedSeries 1 = e₂.restrictDerivedSeries 1) : e₁ = e₂ := by
  ext x
  obtain ⟨⟨z, d⟩, rfl⟩ := (prodCenterDerivedEquiv hcompl).surjective x
  have hz : e₁ z = e₂ z := by
    simpa only [coe_restrictCenter] using
      congrArg (fun f : center R L ≃ₗ⁅R⁆ center R M ↦ (f z : M)) hZ
  have hd : e₁ d = e₂ d := by
    simpa only [coe_restrictDerivedSeries] using
      congrArg (fun f : derivedSeries R L 1 ≃ₗ⁅R⁆ derivedSeries R M 1 ↦ (f d : M)) hD
  simp [map_add, hz, hd]

/-- Every Lie algebra automorphism is reconstructed from its restrictions to `Z(L)` and `[L, L]`
when the centre and derived ideal are complementary. -/
@[simp]
theorem ofCenterDerived_restrictCenter_restrictDerivedSeries
    (hcompl : IsCompl (center R L) (derivedSeries R L 1)) (θ : L ≃ₗ⁅R⁆ L) :
    ofCenterDerived hcompl θ.restrictCenter (θ.restrictDerivedSeries 1) = θ :=
  eq_of_restrictCenter_eq_of_restrictDerivedSeries_eq hcompl
    (restrictCenter_ofCenterDerived hcompl _ _)
    (restrictDerivedSeries_ofCenterDerived hcompl _ _)

@[simp]
theorem ofCenterDerived_refl (hcompl : IsCompl (center R L) (derivedSeries R L 1)) :
    ofCenterDerived hcompl LieEquiv.refl LieEquiv.refl = LieEquiv.refl :=
  eq_of_restrictCenter_eq_of_restrictDerivedSeries_eq hcompl (by simp) (by simp)

@[simp]
theorem ofCenterDerived_symm
    (hcompl : IsCompl (center R L) (derivedSeries R L 1))
    (θZ : center R L ≃ₗ⁅R⁆ center R L) (θD : derivedSeries R L 1 ≃ₗ⁅R⁆ derivedSeries R L 1) :
    (ofCenterDerived hcompl θZ θD).symm = ofCenterDerived hcompl θZ.symm θD.symm :=
  eq_of_restrictCenter_eq_of_restrictDerivedSeries_eq hcompl (by simp) (by simp)

theorem ofCenterDerived_trans
    (hcompl : IsCompl (center R L) (derivedSeries R L 1))
    (θZ₁ θZ₂ : center R L ≃ₗ⁅R⁆ center R L)
    (θD₁ θD₂ : derivedSeries R L 1 ≃ₗ⁅R⁆ derivedSeries R L 1) :
    (ofCenterDerived hcompl θZ₁ θD₁).trans (ofCenterDerived hcompl θZ₂ θD₂) =
      ofCenterDerived hcompl (θZ₁.trans θZ₂) (θD₁.trans θD₂) :=
  eq_of_restrictCenter_eq_of_restrictDerivedSeries_eq hcompl (by simp) (by simp)

end LieEquiv
