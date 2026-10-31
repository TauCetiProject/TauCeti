/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Cohomology.SectionsQuotient.Linear
public import TauCeti.AlgebraicGeometry.Cohomology.Module.Base
public import TauCeti.AlgebraicGeometry.Cohomology.Affine
public import TauCeti.AlgebraicGeometry.Modules.Quasicoherent.Pushforward.QuasiSeparated
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import TauCeti.AlgebraicGeometry.Scheme.Opens
public import TauCeti.LinearAlgebra.Submodule.Quotient

/-!
# Cohomology comparison through an affine morphism

For a morphism `f : X ⟶ Y` over a ring `R`, zeroth cohomology of `f_* M` is finite
exactly when that of `M` is finite. If `f` is affine and `Y` has a cover by two affine opens, the
same holds in degree one for quasicoherent `M`. Both first cohomology groups are computed by the
same sections on the overlap modulo differences of restrictions. These results allow
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
  -- Instantiate the preimage formulas explicitly: their pair type is only definitionally
  -- that of the pushforward sections.
  simp only [mayerVietorisSectionsDifferenceLinear_apply M (f ⁻¹ᵁ U) (f ⁻¹ᵁ V) a b,
    mayerVietorisSectionsDifference_apply M (f ⁻¹ᵁ U) (f ⁻¹ᵁ V) a b,
    mayerVietorisSectionsDifferenceLinear_apply, mayerVietorisSectionsDifference_apply]
  -- Pushforward restriction maps are restrictions along preimages of the inclusions.
  rfl

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
  -- Global sections carry the action through `baseRingToGlobalSections`, which is only
  -- propositionally the action through `baseRingToStructurePresheaf` used by
  -- `pushforwardSectionsBaseLinearEquiv`, so that equivalence cannot be reused at `⊤`.
  let e : Γ((pushforward f).obj M, ⊤) ≃ₗ[R] Γ(M, ⊤) :=
    { toFun := id
      invFun := id
      left_inv _ := rfl
      right_inv _ := rfl
      map_add' _ _ := rfl
      map_smul' r s := by
        rw [base_smul_globalSections_eq_baseRingToStructurePresheaf_smul]
        exact (pushforward_baseRingToStructurePresheaf_smul R f M ⊤ r s).trans
          (base_smul_globalSections_eq_baseRingToStructurePresheaf_smul R X M r s).symm }
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

/-- The inverse degree-zero comparison identifies the same global section on target and
source. -/
@[simp]
lemma cohomologyZeroPushforwardBaseLinearEquiv_symm_apply (M : X.Modules)
    (x : Cohomology M 0) :
    (f.cohomologyZeroPushforwardBaseLinearEquiv (R := R) M).symm x =
      (cohomologyZeroBaseLinearEquiv R Y ((pushforward f).obj M)).symm
        (cohomologyZeroBaseLinearEquiv R X M x) := by
  rfl

/-- Zeroth cohomology of a pushforward is finite over the base ring exactly when the original
zeroth cohomology is finite, with no condition on the morphism. -/
@[simp]
theorem moduleFinite_cohomology_zero_pushforward_iff (M : X.Modules) :
    Module.Finite R (Cohomology ((pushforward f).obj M) 0) ↔
      Module.Finite R (Cohomology M 0) :=
  Module.Finite.equiv_iff (f.cohomologyZeroPushforwardBaseLinearEquiv (R := R) M)

/-- On a target covered by two affine opens, first cohomology of an affine pushforward agrees with
that on the source as a module over the base ring. -/
def cohomologyOnePushforwardBaseLinearEquiv [IsAffineHom f]
    (M : X.Modules) [M.IsQuasicoherent]
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
  exact bY.equivOfSurjectiveOfKerEq bX hbY hbX hker

/-- The degree-one comparison carries the boundary of an overlap section to its boundary
on the preimage cover. The section types are identified by pushforward and `f.preimage_inf`. -/
@[simp]
lemma cohomologyOnePushforwardBaseLinearEquiv_boundary [IsAffineHom f]
    (M : X.Modules) [M.IsQuasicoherent]
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
  -- The comparison sends the boundary of `s` to the boundary of its image under the
  -- section comparison, which is `s` itself.
  exact (LinearMap.equivOfSurjectiveOfKerEq_apply _ _ _ _ _ s).trans (congrArg
    (mayerVietorisBoundaryLinear M (f ⁻¹ᵁ U) (f ⁻¹ᵁ V) (f.preimage_sup_eq_top hUV))
    (pushforwardSectionsBaseLinearEquiv_apply R f M (U ⊓ V) s))

/-- The inverse degree-one comparison carries the boundary of a section over the overlap of
the preimage cover to the boundary of the same section on the target cover. -/
@[simp]
lemma cohomologyOnePushforwardBaseLinearEquiv_symm_boundary [IsAffineHom f]
    (M : X.Modules) [M.IsQuasicoherent]
    (U V : Y.Opens) (hU : IsAffineOpen U) (hV : IsAffineOpen V) (hUV : U ⊔ V = ⊤)
    (s : Γ(M, f ⁻¹ᵁ U ⊓ f ⁻¹ᵁ V)) :
    (f.cohomologyOnePushforwardBaseLinearEquiv (R := R) M U V hU hV hUV).symm
        (mayerVietorisBoundaryLinear M (f ⁻¹ᵁ U) (f ⁻¹ᵁ V) (f.preimage_sup_eq_top hUV) s) =
      mayerVietorisBoundaryLinear ((pushforward f).obj M) U V hUV s :=
  (LinearEquiv.symm_apply_eq _).mpr
    (f.cohomologyOnePushforwardBaseLinearEquiv_boundary M U V hU hV hUV s).symm

/-- On a target covered by two affine opens, first cohomology of an affine pushforward is finite
exactly when first cohomology on the source is finite. -/
theorem moduleFinite_cohomology_one_pushforward_iff_of_two_affine_opens [IsAffineHom f]
    (M : X.Modules) [M.IsQuasicoherent]
    (U V : Y.Opens) (hU : IsAffineOpen U) (hV : IsAffineOpen V) (hUV : U ⊔ V = ⊤) :
    Module.Finite R (Cohomology ((pushforward f).obj M) 1) ↔
      Module.Finite R (Cohomology M 1) :=
  Module.Finite.equiv_iff (f.cohomologyOnePushforwardBaseLinearEquiv (R := R) M U V hU hV hUV)

end AlgebraicGeometry.Scheme.Hom
