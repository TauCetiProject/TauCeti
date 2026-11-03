/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors, Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
public import Mathlib.RingTheory.Unramified.LocalStructure
public import TauCeti.AlgebraicGeometry.Morphisms.Dominant
public import TauCeti.AlgebraicGeometry.Scheme.Normal
public import TauCeti.RingTheory.QuasiFinite.Height

import TauCeti.Topology.KrullDimension.Basic

/-!
# Locally quasi-finite morphisms

Formal unramifiedness together with local finite type implies local quasi-finiteness.

A locally quasi-finite morphism is strictly monotone for the specialization order on points
(`x ≤ y` when `y` generizes `x`): it preserves specializations because it is continuous, and two
distinct points of one fibre never specialize to each other because the fibres are discrete. This
is incomparability for quasi-finite morphisms. Consequently the codimension of a point is at most
the codimension of its image, and the dimension of the source is at most that of the target.

## Main results

* `AlgebraicGeometry.LocallyQuasiFinite.of_formallyUnramified`: a formally unramified morphism
  locally of finite type is locally quasi-finite.
* `AlgebraicGeometry.Scheme.Hom.strictMono`: a locally quasi-finite morphism
  is strictly monotone for the specialization order.
* `AlgebraicGeometry.Scheme.Hom.coheight_le_coheight_apply`: under a locally quasi-finite morphism
  the coheight of a point is at most the coheight of its image.
* `AlgebraicGeometry.Scheme.Hom.topologicalKrullDim_le`: the source of a locally quasi-finite
  morphism has dimension at most that of its target.
* `AlgebraicGeometry.Scheme.Hom.ringKrullDim_stalk_eq_of_quasiFiniteAt`: a dominant morphism of
  integral schemes, locally of finite type, which is quasi-finite at `x` with integrally closed
  local ring at `f x`, preserves the dimension of the local ring at `x`;
  `AlgebraicGeometry.Scheme.Hom.ringKrullDim_stalk_eq_of_locallyQuasiFinite` is the form for a
  locally quasi-finite morphism onto a normal scheme. Over a normal base the inequality between
  coheights becomes an equality; the ring-level input is
  `Ideal.height_eq_height_of_quasiFiniteAt`.

## References

* The strict monotonicity is a scheme form of `Pcf.height_eq_one_of_liesOver_heightOne` in
  T. Dupuy, T. Tucker and Z. Wang,
  [pcfawd-formalization](https://github.com/tdupu/pcfawd-formalization) at commit
  `9a20b3f351446d64e6015d704198bc71c7002008` (Apache-2.0), `lean/Pcf/Bounding/Divisors.lean`,
  whose incomparability step is proved there for integral extensions of rings.
-/

public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry

/-- A formally unramified morphism that is locally of finite type is locally quasi-finite. -/
instance (priority := low) LocallyQuasiFinite.of_formallyUnramified {X Y : Scheme.{u}}
    (f : X ⟶ Y) [hform : FormallyUnramified f] [htype : LocallyOfFiniteType f] :
    LocallyQuasiFinite f := by
  rw [locallyQuasiFinite_iff]
  intro U hU V hV e
  have hform := hform.formallyUnramified_appLE hU hV e
  have htype := htype.finiteType_appLE hU hV e
  algebraize [(f.appLE U V e).hom]
  exact RingHom.quasiFinite_algebraMap.mpr inferInstance

/-- A locally quasi-finite morphism is strictly monotone for the specialization order. -/
theorem Scheme.Hom.strictMono {X Y : Scheme.{u}} (f : X ⟶ Y)
    [LocallyQuasiFinite f] : StrictMono f := by
  -- `f` preserves specializations, and two points of one fibre that specialize to each other are
  -- equal because the fibre is discrete.
  intro x y hxy
  have hle : f x ≤ f y := (le_iff_specializes.mp hxy.le).map f.continuous
  refine lt_of_le_not_ge hle fun hge ↦ hxy.not_ge ?_
  have hfxy : f x = f y :=
    (inseparable_iff_specializes_and.mpr ⟨le_iff_specializes.mp hge,
      le_iff_specializes.mp hle⟩).eq
  have hxy_eq : y = x :=
    (f.isDiscrete_preimage_singleton (f x)).eq_of_specializes (le_iff_specializes.mp hxy.le)
      hfxy.symm rfl
  exact hxy_eq ▸ le_rfl

/-- Under a locally quasi-finite morphism the coheight of a point is at most the coheight of its
image. -/
theorem Scheme.Hom.coheight_le_coheight_apply {X Y : Scheme.{u}} (f : X ⟶ Y)
    [LocallyQuasiFinite f] (x : X) : Order.coheight x ≤ Order.coheight (f x) :=
  Order.coheight_le_coheight_apply_of_strictMono _ f.strictMono x

/-- The source of a locally quasi-finite morphism has dimension at most that of its target: the
dimension of a scheme is the supremum of the coheights of its points. -/
theorem Scheme.Hom.topologicalKrullDim_le {X Y : Scheme.{u}} (f : X ⟶ Y)
    [LocallyQuasiFinite f] : topologicalKrullDim X ≤ topologicalKrullDim Y := by
  rw [TauCeti.topologicalKrullDim_eq_iSup_coheight, TauCeti.topologicalKrullDim_eq_iSup_coheight]
  exact iSup_le fun x ↦ (WithBot.coe_le_coe.mpr (f.coheight_le_coheight_apply x)).trans
    (le_iSup (fun y : Y ↦ (Order.coheight y : WithBot ℕ∞)) (f x))

/-- **Quasi-finite morphisms over a normal base preserve the dimension of local rings.** Let
`f : X ⟶ Y` be a dominant morphism of integral schemes, locally of finite type. If `f` is
quasi-finite at `x` and the local ring of `Y` at `f x` is integrally closed, then the local rings
at `x` and at `f x` have the same dimension. -/
theorem Scheme.Hom.ringKrullDim_stalk_eq_of_quasiFiniteAt {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsIntegral X] [IsIntegral Y] [IsDominant f] [LocallyOfFiniteType f] {x : X}
    (hx : f.QuasiFiniteAt x) [IsIntegrallyClosed (Y.presheaf.stalk (f x))] :
    ringKrullDim (X.presheaf.stalk x) = ringKrullDim (Y.presheaf.stalk (f x)) := by
  -- Choose affine opens `U ∋ f x` and `V ∋ x` with `V ⊆ f⁻¹ U`. The two local rings are the
  -- localizations of `Γ(Y, U) ⟶ Γ(X, V)` at the primes of `f x` and `x`, and the ring-level
  -- `Ideal.height_eq_height_of_quasiFiniteAt` compares their heights.
  obtain ⟨U, hU, hxU, -⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp Y.isBasis_affineOpens
    (U := ⊤) (x := f x) trivial
  obtain ⟨V, hV, hxV, e⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens
    (U := f ⁻¹ᵁ U) (x := x) hxU
  have : Nonempty V := ⟨⟨x, hxV⟩⟩
  have hft := LocallyOfFiniteType.finiteType_appLE (f := f) hU hV e
  have hqf := hx.quasiFiniteAt hV hU e hxV
  algebraize [(f.appLE U V e).hom]
  have : FaithfulSMul Γ(Y, U) Γ(X, V) := (faithfulSMul_iff_algebraMap_injective _ _).mpr
    (f.appLE_injective_of_isDominant U V e)
  set q := (hV.primeIdealOf ⟨x, hxV⟩).asIdeal
  have hq : q.under Γ(Y, U) = (hU.primeIdealOf ⟨f x, e hxV⟩).asIdeal :=
    congrArg PrimeSpectrum.asIdeal (IsAffineOpen.comap_primeIdealOf_appLE U hU V hV e hxV)
  have : q.LiesOver (hU.primeIdealOf ⟨f x, e hxV⟩).asIdeal := ⟨hq.symm⟩
  let := X.presheaf.algebra_section_stalk ⟨x, hxV⟩
  let := Y.presheaf.algebra_section_stalk ⟨f x, e hxV⟩
  have := hV.isLocalization_stalk ⟨x, hxV⟩
  have := hU.isLocalization_stalk ⟨f x, e hxV⟩
  have : IsIntegrallyClosed (Localization.AtPrime (hU.primeIdealOf ⟨f x, e hxV⟩).asIdeal) :=
    .of_equiv (IsLocalization.algEquiv (hU.primeIdealOf ⟨f x, e hxV⟩).asIdeal.primeCompl
      (Y.presheaf.stalk (f x)) _).toRingEquiv
  rw [IsLocalization.AtPrime.ringKrullDim_eq_height q,
    IsLocalization.AtPrime.ringKrullDim_eq_height (hU.primeIdealOf ⟨f x, e hxV⟩).asIdeal,
    Ideal.height_eq_height_of_quasiFiniteAt (hU.primeIdealOf ⟨f x, e hxV⟩).asIdeal q]

/-- A locally quasi-finite dominant morphism `f : X ⟶ Y` of integral schemes, locally of finite
type, onto a normal scheme preserves the dimension of every local ring:
`dim 𝒪_{X,x} = dim 𝒪_{Y,f x}` for all `x`. Normality of `X` is not needed. -/
theorem Scheme.Hom.ringKrullDim_stalk_eq_of_locallyQuasiFinite {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsIntegral X] [IsIntegral Y] [IsDominant f] [LocallyOfFiniteType f] [LocallyQuasiFinite f]
    [TauCeti.AlgebraicGeometry.IsNormalScheme Y] (x : X) :
    ringKrullDim (X.presheaf.stalk x) = ringKrullDim (Y.presheaf.stalk (f x)) :=
  f.ringKrullDim_stalk_eq_of_quasiFiniteAt (f.quasiFiniteAt x)

end AlgebraicGeometry
