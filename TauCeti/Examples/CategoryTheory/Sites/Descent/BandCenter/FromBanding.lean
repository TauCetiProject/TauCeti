/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Sites.Descent.BandCenter.FromBanding

/-!
# Checks for the coefficients of a banding as intrinsic central sections

For a gerbe `F` with an `A`-banding `b`:

* the local coefficient of the unit section is zero on every arrow;
* the local coefficient of `c_b(U)(a)` at `f` is the restriction of `a` along `f`;
* two families of local objects on the same sieve give the same local coefficients, with no
  isomorphisms between the chosen objects;
* the inverse of `c_b(U)` sends the unit section to the unit, `c_b(U)(a)` to `a` and `z⁻¹` to the
  inverse coefficient; `c_b(U)` of the inverse of `z` is `z`; the inverse of a restricted section is
  the restricted coefficient; a section other than the unit has a coefficient other than the unit.
-/

public section

namespace TauCeti.Examples.BandCenterFromBanding

open CategoryTheory CategoryTheory.Pseudofunctor Opposite Bicategory
open IntrinsicBandSections AbelianBanding

variable {C : Type*} [Category* C] {F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat}
  {J : GrothendieckTopology C} [F.IsGerbe J] {A : Sheaf J AddCommGrpCat}
  (b : F.AbelianBanding J A) {U : C} (R : Sieve U)
  (xs : ∀ ⦃V : C⦄ (f : V ⟶ U), R f → F.obj (.mk (op V)))

/-- The local coefficient of the unit section is zero on every arrow. -/
example {V : C} (f : V ⟶ U) (hf : R f) : b.localCoefficient R xs 1 f hf = 0 := by
  rw [localCoefficient_apply, map_one, map_one, toAdd_one]
  rfl

/-- The local coefficient of `c_b(U)(a)` at `f` is the restriction of `a` along `f`. -/
example (a : Multiplicative (A.obj.obj (op U))) {V : C} (f : V ⟶ U) (hf : R f) :
    b.localCoefficient R xs (b.centerFromBanding U a) f hf = A.obj.map f.op a.toAdd := by
  rw [localCoefficient_apply, evaluation_centerFromBanding, MulEquiv.symm_apply_apply,
    toAdd_ofAdd]

/-- Two families of local objects give the same local coefficients. -/
example (ys : ∀ ⦃V : C⦄ (f : V ⟶ U), R f → F.obj (.mk (op V))) (z : IntrinsicBandSections F U)
    {V : C} (f : V ⟶ U) (hf : R f) :
    b.localCoefficient R xs z f hf = b.localCoefficient R ys z f hf := by
  refine Multiplicative.ofAdd.injective (b.centerFromBanding_injective V ?_)
  rw [centerFromBanding_localCoefficient, centerFromBanding_localCoefficient]

/-- The inverse sends the unit section to the unit coefficient. -/
example : (b.centerFromBandingEquiv U).symm 1 = 1 :=
  map_one _

/-- The inverse of `c_b(U)(a)` is `a`, and `c_b(U)` of the inverse of `z` is `z`. -/
example (a : Multiplicative (A.obj.obj (op U))) (z : IntrinsicBandSections F U) :
    (b.centerFromBandingEquiv U).symm (b.centerFromBanding U a) = a ∧
      b.centerFromBanding U ((b.centerFromBandingEquiv U).symm z) = z :=
  ⟨centerFromBandingEquiv_symm_centerFromBanding b U a,
    centerFromBanding_centerFromBandingEquiv_symm b U z⟩

/-- The inverse respects inversion of central sections. -/
example (z : IntrinsicBandSections F U) :
    (b.centerFromBandingEquiv U).symm z⁻¹ = ((b.centerFromBandingEquiv U).symm z)⁻¹ :=
  map_inv _ z

/-- The inverse on a restricted section is the restricted coefficient. -/
example {V : C} (f : V ⟶ U) (z : IntrinsicBandSections F U) :
    (b.centerFromBandingEquiv V).symm (restrict f z) =
      Multiplicative.ofAdd (A.obj.map f.op ((b.centerFromBandingEquiv U).symm z).toAdd) :=
  centerFromBandingEquiv_symm_restrict b f z

/-- A section other than the unit has a coefficient other than the unit, so the inverse is not the
constant unit map. -/
example (z : IntrinsicBandSections F U) (hz : z ≠ 1) : (b.centerFromBandingEquiv U).symm z ≠ 1 :=
  fun h ↦ hz (by rw [← centerFromBanding_centerFromBandingEquiv_symm b U z, h, map_one])

end TauCeti.Examples.BandCenterFromBanding
