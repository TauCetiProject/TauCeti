/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
public import Mathlib.RingTheory.IntegralClosure.GoingDown
public import TauCeti.AlgebraicGeometry.Morphisms.Flat.Dominant
public import TauCeti.AlgebraicGeometry.Morphisms.RamificationIdx
public import TauCeti.AlgebraicGeometry.Scheme.Normal
public import TauCeti.RingTheory.KrullDimension.GoingDown
public import TauCeti.RingTheory.RamificationInertia.DiscreteValuationRing

/-!
# Codimension and ramification over a normal target

Let `f : X ⟶ Y` be a finite dominant morphism of integral schemes with `Y` locally Noetherian and
normal. On affine charts `f` is a finite injective extension `A → B` of domains with `A`
integrally closed, which satisfies going down (Stacks, Proposition 10.38.7 (00H8)); with
incomparability this gives `ht (𝔮 ∩ A) = ht 𝔮` for every prime `𝔮` of `B`
(`Ideal.height_under_eq_of_isIntegral`). Hence `f` preserves the codimension of every point, and
in particular sends points of codimension one to points of codimension one, which is the input
`hf` of `TauCeti.NormalSchemes.codimensionOneMap`. Without normality of `Y` this fails (Stacks,
Section 110.19 (02JE)).

At a point `x` of `X` whose image has codimension one on a locally Noetherian normal `Y`, the local
ring `𝒪_{Y,f(x)}` is a discrete valuation ring, so the stalk map of a dominant `f` from an
integral scheme is flat (`AlgebraicGeometry.Scheme.Hom.flat_stalkMap_of_isDominant`), and
Mathlib's `Ideal.ramificationIdx_tower` then makes ramification indices multiply along a composite.
When both local rings are discrete valuation rings, `ramificationIdxAt f x` is the exponent `e`
with `𝔪_{f(x)} 𝒪_{X,x} = 𝔪_x ^ e`, the ramification index of the extension of discrete valuation
rings (Stacks, Definition 15.113.1 (09E4)).

## Main results

* `TauCeti.NormalSchemes.coheight_apply_eq_coheight`: a finite dominant morphism of integral
  schemes with locally Noetherian normal target preserves the coheight of every point.
* `TauCeti.NormalSchemes.coheight_apply_eq_one_of_isNormalScheme`: in particular it sends points of
  coheight one to points of coheight one.
* `TauCeti.NormalSchemes.ramificationIdxAt_comp`: `e_x(f ≫ g) = e_x(f) e_{f(x)}(g)` when `f` is a
  dominant morphism from an integral scheme and `f x` has coheight one on a locally Noetherian
  normal scheme.
* `TauCeti.NormalSchemes.ramificationIdxAt_eq_dvr`: at a point of coheight one of a locally
  Noetherian normal integral scheme over a point of coheight one, `𝔪_{f(x)} 𝒪_{X,x} = 𝔪_x ^ e`
  with `e = ramificationIdxAt f x`.

## References

* [Stacks Project, Proposition 10.38.7](https://stacks.math.columbia.edu/tag/00H8) and
  [Definition 15.113.1](https://stacks.math.columbia.edu/tag/09E4).
* Ported from T. Dupuy, T. Tucker and Z. Wang,
  [pcfawd-formalization](https://github.com/tdupu/pcfawd-formalization) at commit
  `9a20b3f351446d64e6015d704198bc71c7002008` (Apache-2.0), `lean/Pcf/Bounding/SchemeDynamics.lean`:
  `coheight_apply_eq_coheight` is its `Pcf.coheight_apply_eq_of_finite_dominant_normal`, and
  `ramificationIdxAt_comp` is its `Pcf.schemeDivisorRamificationIdx_comp` (there with `f` finite
  and `x` of coheight one); `ramificationIdxAt_eq_dvr` is the scheme form of its
  `Pcf.heightOneRamificationIdx_eq_dvrExponent` (`lean/Pcf/Bounding/Divisors.lean`).
-/

public section

open CategoryTheory AlgebraicGeometry Order IsLocalRing TauCeti.AlgebraicGeometry

namespace TauCeti.NormalSchemes

universe u

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- A finite dominant morphism of integral schemes with locally Noetherian normal target preserves
the coheight of every point: on affine charts it is a finite injective extension of Noetherian
domains with integrally closed base, which satisfies going down. -/
theorem coheight_apply_eq_coheight [IsFinite f] [IsDominant f] [IsIntegral X] [IsIntegral Y]
    [IsLocallyNoetherian Y] [IsNormalScheme Y] (x : X) : coheight (f x) = coheight x := by
  obtain ⟨U, hU, hxU, -⟩ := exists_isAffineOpen_mem_and_subset (x := f x) (U := ⊤) trivial
  have hV : IsAffineOpen (f ⁻¹ᵁ U) := hU.preimage f
  have : Nonempty U := ⟨⟨f x, hxU⟩⟩
  have : Nonempty (f ⁻¹ᵁ U) := ⟨⟨x, hxU⟩⟩
  let := (f.app U).hom.toAlgebra
  have : Module.Finite Γ(Y, U) Γ(X, f ⁻¹ᵁ U) := f.finite_app U hU
  have : IsSchemeTheoreticallyDominant f := .of_isDominant f
  have : FaithfulSMul Γ(Y, U) Γ(X, f ⁻¹ᵁ U) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr (f.app_injective U)
  have : IsNoetherianRing Γ(Y, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  have : IsNoetherianRing Γ(X, f ⁻¹ᵁ U) := .of_finite Γ(Y, U) _
  have : IsIntegrallyClosed Γ(Y, U) := IsNormalScheme.isIntegrallyClosed_of_isAffineOpen hU
  -- The prime of `x` contracts to the prime of `f x`, and heights are coheights on both charts.
  have hcontract : (hV.primeIdealOf ⟨x, hxU⟩).asIdeal.under Γ(Y, U) =
      (hU.primeIdealOf ⟨f x, hxU⟩).asIdeal := by
    have h := IsAffineOpen.comap_primeIdealOf_appLE U hU (f ⁻¹ᵁ U) hV le_rfl hxU
    rw [Scheme.Hom.appLE_eq_app] at h
    exact congrArg PrimeSpectrum.asIdeal h
  let q : Spec Γ(Y, U) := hU.primeIdealOf ⟨f x, hxU⟩
  let Q : Spec Γ(X, f ⁻¹ᵁ U) := hV.primeIdealOf ⟨x, hxU⟩
  have htarget : coheight (f x) = coheight q := by
    rw [← coheight_eq_of_isOpenImmersion hU.fromSpec, hU.fromSpec_primeIdealOf]
  have hsource : coheight x = coheight Q := by
    rw [← coheight_eq_of_isOpenImmersion hV.fromSpec, hV.fromSpec_primeIdealOf]
  rw [htarget, hsource, ← idealHeight_eq_coheight, ← idealHeight_eq_coheight, ← hcontract]
  exact Ideal.height_under_eq_of_isIntegral _

/-- A finite dominant morphism of integral schemes with locally Noetherian normal target sends
points of coheight one to points of coheight one (going down, Stacks, Proposition 10.38.7
(00H8)). -/
theorem coheight_apply_eq_one_of_isNormalScheme [IsLocallyNoetherian Y] [IsNormalScheme Y]
    [IsFinite f] [IsDominant f] [IsIntegral X] [IsIntegral Y]
    (x : X) (hx : coheight x = 1) : coheight (f x) = 1 :=
  (coheight_apply_eq_coheight f x).trans hx

/-- **Ramification indices multiply in towers.** For a dominant morphism `f : X ⟶ Y` from an
integral scheme and a point `x` whose image has coheight one on the locally Noetherian normal
scheme `Y`, `e_x(f ≫ g) = e_x(f) e_{f(x)}(g)` for every `g : Y ⟶ Z`. The local ring of `Y` at
`f x` is a discrete valuation ring, over which the stalk map of `f` is flat. -/
theorem ramificationIdxAt_comp {Z : Scheme.{u}} (g : Y ⟶ Z) [IsDominant f] [IsIntegral X]
    [IsLocallyNoetherian Y] [IsNormalScheme Y] (x : X)
    (hfx : coheight (f x) = 1) :
    ramificationIdxAt (f ≫ g) x = ramificationIdxAt f x * ramificationIdxAt g (f x) := by
  let R := Z.presheaf.stalk (g (f x))
  let S := Y.presheaf.stalk (f x)
  let T := X.presheaf.stalk x
  let : Algebra R S := (g.stalkMap (f x)).hom.toAlgebra
  let : Algebra S T := (f.stalkMap x).hom.toAlgebra
  let : Algebra R T := ((f ≫ g).stalkMap x).hom.toAlgebra
  have hcomp : ((f ≫ g).stalkMap x).hom = (f.stalkMap x).hom.comp (g.stalkMap (f x)).hom := by
    rw [Scheme.Hom.stalkMap_comp]
    rfl
  have : IsScalarTower R S T := .of_algebraMap_eq' hcomp
  have : IsLocalHom (algebraMap S T) := inferInstanceAs (IsLocalHom (f.stalkMap x).hom)
  have : IsDiscreteValuationRing S := IsNormalScheme.isDiscreteValuationRing_stalk Y (f x) hfx
  have : Module.Flat S T := RingHom.flat_algebraMap_iff.mp (f.flat_stalkMap_of_isDominant x)
  rw [ramificationIdxAt_def, ramificationIdxAt_def, ramificationIdxAt_def, mul_comm]
  exact Ideal.ramificationIdx_tower (R := R) (maximalIdeal S) (maximalIdeal T)

/-- **The ramification index of an extension of discrete valuation rings.** At a point `x` of
coheight one of a locally Noetherian normal integral scheme `X`, over a point `f x` of coheight
one of an integral scheme, for `f` dominant, the local rings are discrete valuation rings and
`𝔪_{f(x)} 𝒪_{X,x} = 𝔪_x ^ e` with `e = ramificationIdxAt f x`: the ramification index of the
extension `𝒪_{Y,f(x)} → 𝒪_{X,x}` of Stacks, Definition 15.113.1 (09E4). -/
@[stacks 09E4 "the ramification index of the stalk extension"]
theorem ramificationIdxAt_eq_dvr [IsDominant f] [IsIntegral X] [IsIntegral Y]
    [IsLocallyNoetherian X] [IsNormalScheme X] (x : X) (hx : coheight x = 1)
    (hfx : coheight (f x) = 1) :
    (maximalIdeal (Y.presheaf.stalk (f x))).map (f.stalkMap x).hom =
      maximalIdeal (X.presheaf.stalk x) ^ ramificationIdxAt f x := by
  let := (f.stalkMap x).hom.toAlgebra
  have : IsLocalHom (algebraMap (Y.presheaf.stalk (f x)) (X.presheaf.stalk x)) :=
    inferInstanceAs (IsLocalHom (f.stalkMap x).hom)
  have : IsDiscreteValuationRing (X.presheaf.stalk x) :=
    IsNormalScheme.isDiscreteValuationRing_stalk X x hx
  -- The maximal ideal of `𝒪_{Y,f(x)}` is nonzero, as this local ring has dimension one, and the
  -- stalk map is injective.
  have hne : maximalIdeal (Y.presheaf.stalk (f x)) ≠ ⊥ := by
    intro hbot
    have hfield : IsField (Y.presheaf.stalk (f x)) :=
      isField_iff_maximalIdeal_eq.mpr hbot
    have hdim := ringKrullDim_stalk_eq_coheight (f x)
    rw [ringKrullDim_eq_zero_of_isField hfield, hfx] at hdim
    exact zero_ne_one (WithBot.coe_injective hdim)
  have hmap : (maximalIdeal (Y.presheaf.stalk (f x))).map
      (algebraMap (Y.presheaf.stalk (f x)) (X.presheaf.stalk x)) ≠ ⊥ := by
    have hinj : Function.Injective
        (algebraMap (Y.presheaf.stalk (f x)) (X.presheaf.stalk x)) :=
      f.stalkMap_injective_of_isDominant x
    rw [Ne, Ideal.map_eq_bot_iff_le_ker, (RingHom.injective_iff_ker_eq_bot _).mp hinj, le_bot_iff]
    exact hne
  rw [ramificationIdxAt_def]
  exact IsDiscreteValuationRing.map_maximalIdeal_eq_pow_ramificationIdx hmap

end TauCeti.NormalSchemes
