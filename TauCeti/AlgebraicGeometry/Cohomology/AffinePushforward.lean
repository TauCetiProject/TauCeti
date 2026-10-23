/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Cohomology.SectionsQuotient.Linear
public import TauCeti.AlgebraicGeometry.Cohomology.Module.Base
public import TauCeti.AlgebraicGeometry.Cohomology.OpenImmersion
public import TauCeti.AlgebraicGeometry.Modules.Quasicoherent.Pushforward.Affine

/-!
# Cohomology comparison through an affine morphism

For a morphism `f : X ⟶ Y` over a ring `R`, zeroth cohomology of `f_* M` is finite
exactly when that of `M` is finite. If `f` is affine and `Y` is locally Noetherian with a cover
by two affine opens, the same holds in degree one for quasicoherent `M` when `X` is locally
Noetherian. Both first cohomology groups are computed
by the same sections on the overlap modulo differences of restrictions. These results allow
cohomological finiteness on the projective line to be transported to finite covers.

## References

* R. Hartshorne, *Algebraic Geometry*, III, Proposition 8.1 and Section 4.
-/

public section

open CategoryTheory AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.Modules
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme.Modules

universe u

noncomputable section

namespace AlgebraicGeometry.Scheme.Hom

/-- The difference of restrictions for a pushforward is the difference on the preimage opens.
The overlap section types agree because preimages preserve intersections. -/
lemma mayerVietorisSectionsDifferenceLinear_pushforward {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M : X.Modules) (U V : Y.Opens) (a : Γ((pushforward f).obj M, U))
    (b : Γ((pushforward f).obj M, V)) :
    mayerVietorisSectionsDifferenceLinear ((pushforward f).obj M) U V (a, b) =
      mayerVietorisSectionsDifferenceLinear M (f ⁻¹ᵁ U) (f ⁻¹ᵁ V) (a, b) := by
  let N := (pushforward f).obj M
  have hres : N.presheaf.map (homOfLE inf_le_left).op a -
      N.presheaf.map (homOfLE inf_le_right).op b =
        M.presheaf.map (homOfLE inf_le_left).op a -
          M.presheaf.map (homOfLE inf_le_right).op b := by
    simp only [N, pushforward_obj_presheaf_map]
    -- Preimages of inclusions are the same morphisms in the opens poset.
    rfl
  -- Compose the public formulas explicitly: their section types agree at default
  -- transparency, but type inference for rewriting does not unfold pushforward objects.
  exact (mayerVietorisSectionsDifferenceLinear_apply N U V a b).trans
    ((mayerVietorisSectionsDifference_apply N U V a b).trans
      (hres.trans ((mayerVietorisSectionsDifference_apply M _ _ a b).symm.trans
        (mayerVietorisSectionsDifferenceLinear_apply M _ _ a b).symm)))

/-- An overlap section has zero boundary for a pushforward exactly when it has zero boundary
on the preimage cover. Pushforward sections over `U ⊓ V` are definitionally sections over
`f ⁻¹ᵁ (U ⊓ V)`, which is definitionally `f ⁻¹ᵁ U ⊓ f ⁻¹ᵁ V` by `f.preimage_inf`.
No affineness or acyclicity is needed for this kernel comparison. -/
lemma mayerVietorisBoundaryLinear_pushforward_eq_zero_iff {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M : X.Modules) (U V : Y.Opens) (hUV : U ⊔ V = ⊤)
    (s : Γ((pushforward f).obj M, U ⊓ V)) :
    mayerVietorisBoundaryLinear ((pushforward f).obj M) U V hUV s = 0 ↔
      mayerVietorisBoundaryLinear M (f ⁻¹ᵁ U) (f ⁻¹ᵁ V)
        (f.preimage_sup_eq_top hUV) s = 0 := by
  have hpre := f.preimage_sup_eq_top hUV
  have hY := SetLike.ext_iff.mp
    (ker_mayerVietorisBoundaryLinear ((pushforward f).obj M) U V hUV) s
  have hX := SetLike.ext_iff.mp
    (ker_mayerVietorisBoundaryLinear M (f ⁻¹ᵁ U) (f ⁻¹ᵁ V) hpre) s
  refine hY.trans (Iff.trans ?_ hX.symm)
  constructor <;> rintro ⟨⟨a, b⟩, h⟩
  · exact ⟨(a, b), (f.mayerVietorisSectionsDifferenceLinear_pushforward M U V a b).symm.trans h⟩
  · exact ⟨(a, b), (f.mayerVietorisSectionsDifferenceLinear_pushforward M U V a b).trans h⟩

variable {R : Type u} [CommRing R] {X Y : Scheme.{u}}
  [X.Over (Spec (.of R))] [Y.Over (Spec (.of R))]
  (f : X ⟶ Y) [f.IsOver (Spec (.of R))]

/-- Zeroth cohomology of a pushforward agrees with that of the original sheaf as a module
over the base ring, with no condition on the morphism. -/
def cohomologyZeroPushforwardBaseLinearEquiv (M : X.Modules) :
    Cohomology ((pushforward f).obj M) 0 ≃ₗ[R] Cohomology M 0 := by
  -- Local sections use `baseRingToStructurePresheaf`, whereas global sections use
  -- `baseRingToGlobalSections`; identify these scalar maps at the top open.
  -- Both syntactic presentations of the top preimage have the same module structure;
  -- instance search needs each presentation, as for intersections below.
  let : Module Γ(X, f ⁻¹ᵁ ⊤) Γ((pushforward f).obj M, ⊤) :=
    inferInstanceAs (Module Γ(X, f ⁻¹ᵁ ⊤) Γ(M, f ⁻¹ᵁ ⊤))
  let : Module Γ(X, ⊤) Γ((pushforward f).obj M, ⊤) :=
    inferInstanceAs (Module Γ(X, ⊤) Γ(M, ⊤))
  let e : Γ((pushforward f).obj M, ⊤) ≃ₗ[R] Γ(M, ⊤) :=
    { toFun := id
      invFun := id
      left_inv _ := rfl
      right_inv _ := rfl
      map_add' _ _ := rfl
      map_smul' r s := by
        -- Pushforward global sections restrict scalars along `f.app ⊤`; compare the
        -- two base-ring maps through their structure-presheaf components at the top open.
        change f.app ⊤ (baseRingToGlobalSections R Y r) • (s : Γ(M, ⊤)) =
          baseRingToGlobalSections R X r • (s : Γ(M, ⊤))
        have h := app_baseRingToStructurePresheaf R f ⊤ r
        simp only [f.preimage_top, Scheme.baseRingToStructurePresheaf_app_top,
          CommRingCat.hom_ofHom] at h
        exact congrArg (fun a : Γ(X, ⊤) ↦ a • (s : Γ(M, ⊤))) h }
  exact (cohomologyZeroBaseLinearEquiv R Y ((pushforward f).obj M)).trans
    (e.trans (cohomologyZeroBaseLinearEquiv R X M).symm)

/-- The degree-zero comparison identifies the same global section on source and target. -/
@[simp]
lemma cohomologyZeroPushforwardBaseLinearEquiv_apply (M : X.Modules)
    (x : Cohomology ((pushforward f).obj M) 0) :
    f.cohomologyZeroPushforwardBaseLinearEquiv (R := R) M x =
      (cohomologyZeroBaseLinearEquiv R X M).symm
        (cohomologyZeroBaseLinearEquiv R Y ((pushforward f).obj M) x) := by
  rfl

/-- Zeroth cohomology of a pushforward is finite over the base ring exactly when the original
zeroth cohomology is finite, with no condition on the morphism. -/
@[simp]
theorem moduleFinite_cohomology_zero_pushforward_iff (M : X.Modules) :
    Module.Finite R (Cohomology ((pushforward f).obj M) 0) ↔
      Module.Finite R (Cohomology M 0) :=
  Module.Finite.equiv_iff (f.cohomologyZeroPushforwardBaseLinearEquiv (R := R) M)

/-- On a locally Noetherian target covered by two affine opens, first cohomology of an affine
pushforward agrees with that on the locally Noetherian source as a module over the base ring. -/
def cohomologyOnePushforwardBaseLinearEquiv [IsAffineHom f]
    [IsLocallyNoetherian Y] [IsLocallyNoetherian X] (M : X.Modules) [M.IsQuasicoherent]
    (U V : Y.Opens) (hU : IsAffineOpen U) (hV : IsAffineOpen V) (hUV : U ⊔ V = ⊤) :
    Cohomology ((pushforward f).obj M) 1 ≃ₗ[R] Cohomology M 1 := by
  -- Restrict the two Mayer–Vietoris boundaries to the common scalar ring `R`.
  let N := (pushforward f).obj M
  let : Algebra R Γ(Y, ⊤) := ((Y.baseRingToStructurePresheaf R).app (op ⊤)).hom.toAlgebra
  let : Algebra R Γ(X, ⊤) := ((X.baseRingToStructurePresheaf R).app (op ⊤)).hom.toAlgebra
  let : Module R Γ(N, U ⊓ V) :=
    Module.compHom _ ((Y.baseRingToStructurePresheaf R).app (op (U ⊓ V))).hom
  -- `f.preimage_inf` is `rfl`: the preimage of the overlap and the overlap of preimages
  -- are definitionally equal. The two local instances below present the same scalar action
  -- in each syntactic form, since instance search does not unfold preimages here.
  let : Module R Γ(M, f ⁻¹ᵁ U ⊓ f ⁻¹ᵁ V) :=
    Module.compHom _ ((X.baseRingToStructurePresheaf R).app (op (f ⁻¹ᵁ U ⊓ f ⁻¹ᵁ V))).hom
  have := isScalarTower_sections R N (U ⊓ V)
  have := isScalarTower_sections R M (f ⁻¹ᵁ U ⊓ f ⁻¹ᵁ V)
  have := isScalarTower_cohomology R Y N 1
  have := isScalarTower_cohomology R X M 1
  have hpre := f.preimage_sup_eq_top hUV
  have : IsNoetherianRing Γ(Y, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  have : IsNoetherianRing Γ(Y, V) := IsLocallyNoetherian.component_noetherian ⟨V, hV⟩
  have : IsNoetherianRing Γ(X, f ⁻¹ᵁ U) :=
    IsLocallyNoetherian.component_noetherian ⟨_, hU.preimage f⟩
  have : IsNoetherianRing Γ(X, f ⁻¹ᵁ V) :=
    IsLocallyNoetherian.component_noetherian ⟨_, hV.preimage f⟩
  let : Module R Γ(M, f ⁻¹ᵁ (U ⊓ V)) :=
    Module.compHom _ ((X.baseRingToStructurePresheaf R).app (op (f ⁻¹ᵁ (U ⊓ V)))).hom
  let e := pushforwardSectionsBaseLinearEquiv (R := R) f M (U ⊓ V)
  let bY := (mayerVietorisBoundaryLinear N U V hUV).restrictScalars R
  let bX := ((mayerVietorisBoundaryLinear M (f ⁻¹ᵁ U) (f ⁻¹ᵁ V) hpre).restrictScalars R).comp
    e.toLinearMap
  have hbY : Function.Surjective bY := by
    exact mayerVietorisBoundaryLinear_surjective N U V hUV
      (subsingleton_cohomologyOn_succ_of_isAffineOpen N hU 0)
      (subsingleton_cohomologyOn_succ_of_isAffineOpen N hV 0)
  have hbX : Function.Surjective bX := by
    exact (mayerVietorisBoundaryLinear_surjective M _ _ hpre
      (subsingleton_cohomologyOn_succ_of_isAffineOpen M (hU.preimage f) 0)
      (subsingleton_cohomologyOn_succ_of_isAffineOpen M (hV.preimage f) 0)).comp
        e.surjective
  -- The compatibility of restriction differences identifies the two boundary kernels.
  have hker : LinearMap.ker bY = LinearMap.ker bX := by
    ext s
    simp only [LinearMap.mem_ker]
    have he : e s = s := pushforwardSectionsBaseLinearEquiv_apply R f M (U ⊓ V) s
    have hx : bX s = mayerVietorisBoundaryLinear M (f ⁻¹ᵁ U) (f ⁻¹ᵁ V) hpre s := by
      exact congrArg (mayerVietorisBoundaryLinear M (f ⁻¹ᵁ U) (f ⁻¹ᵁ V) hpre) he
    rw [hx]
    exact f.mayerVietorisBoundaryLinear_pushforward_eq_zero_iff M U V hUV s
  -- Both cohomology modules are the quotient of the common overlap by this kernel.
  exact (bY.quotKerEquivOfSurjective hbY).symm.trans
    ((Submodule.quotEquivOfEq _ _ hker).trans (bX.quotKerEquivOfSurjective hbX))

/-- The degree-one comparison carries the boundary of an overlap section to its boundary
on the preimage cover. The section types are identified by pushforward and `f.preimage_inf`. -/
@[simp]
lemma cohomologyOnePushforwardBaseLinearEquiv_boundary [IsAffineHom f]
    [IsLocallyNoetherian Y] [IsLocallyNoetherian X] (M : X.Modules) [M.IsQuasicoherent]
    (U V : Y.Opens) (hU : IsAffineOpen U) (hV : IsAffineOpen V) (hUV : U ⊔ V = ⊤)
    (s : Γ((pushforward f).obj M, U ⊓ V)) :
    dsimp% only [pushforward_obj_obj]
      (f.cohomologyOnePushforwardBaseLinearEquiv (R := R) M U V hU hV hUV
        (mayerVietorisBoundaryLinear ((pushforward f).obj M) U V hUV s)) =
      mayerVietorisBoundaryLinear M (f ⁻¹ᵁ U) (f ⁻¹ᵁ V) (f.preimage_sup_eq_top hUV) s := by
  let : Module R Γ((pushforward f).obj M, U ⊓ V) :=
    Module.compHom _ ((Y.baseRingToStructurePresheaf R).app (op (U ⊓ V))).hom
  let : Module R Γ(M, f ⁻¹ᵁ (U ⊓ V)) :=
    Module.compHom _ ((X.baseRingToStructurePresheaf R).app (op (f ⁻¹ᵁ (U ⊓ V)))).hom
  rw [cohomologyOnePushforwardBaseLinearEquiv, LinearEquiv.trans_apply]
  -- The boundary's scalar restriction is definitionally the same function; `erw`
  -- unfolds it when matching the first-isomorphism-theorem formulas.
  erw [LinearMap.quotKerEquivOfSurjective_symm_apply, LinearEquiv.trans_apply,
    Submodule.quotEquivOfEq_mk, LinearMap.quotKerEquivOfSurjective_apply_mk]
  exact congrArg (mayerVietorisBoundaryLinear M (f ⁻¹ᵁ U) (f ⁻¹ᵁ V)
    (f.preimage_sup_eq_top hUV)) (pushforwardSectionsBaseLinearEquiv_apply R f M (U ⊓ V) s)

/-- On a locally Noetherian target covered by two affine opens, first cohomology of an affine
pushforward is finite exactly when first cohomology on the locally Noetherian source is finite. -/
theorem moduleFinite_cohomology_one_pushforward_iff_of_two_affine_opens [IsAffineHom f]
    [IsLocallyNoetherian Y] [IsLocallyNoetherian X] (M : X.Modules) [M.IsQuasicoherent]
    (U V : Y.Opens) (hU : IsAffineOpen U) (hV : IsAffineOpen V) (hUV : U ⊔ V = ⊤) :
    Module.Finite R (Cohomology ((pushforward f).obj M) 1) ↔
      Module.Finite R (Cohomology M 1) :=
  Module.Finite.equiv_iff (f.cohomologyOnePushforwardBaseLinearEquiv (R := R) M U V hU hV hUV)

end AlgebraicGeometry.Scheme.Hom
