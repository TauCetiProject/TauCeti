/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
public import Mathlib.RingTheory.IntegralClosure.GoingDown
public import TauCeti.AlgebraicGeometry.Morphisms.CodimensionOne.Basic
public import TauCeti.AlgebraicGeometry.Scheme.Normal
public import TauCeti.RingTheory.KrullDimension.Fiber

/-!
# Codimension of points under finite morphisms to a normal scheme

Let `f : X ⟶ Y` be a finite dominant morphism of integral schemes with `Y` locally Noetherian and
normal. Then `f` preserves the codimension of every point, and in particular sends points of
codimension one to points of codimension one. This supplies the input `hf` of
`AlgebraicGeometry.Scheme.Hom.codimensionOneMap`. Without normality of `Y` this fails
(Stacks, Section 110.19 (02JE)).
Normality makes the target reduced, so dominance implies scheme-theoretic dominance.

## Main results

* `AlgebraicGeometry.Scheme.Hom.coheight_apply_eq_coheight`: a finite dominant morphism of integral
  schemes with locally Noetherian normal target preserves the coheight of every point.
* `AlgebraicGeometry.Scheme.Hom.coheight_apply_eq_one_of_coheight_eq_one`: in particular it sends
  points of coheight one to points of coheight one.

## References

* [Stacks Project, Proposition 10.38.7](https://stacks.math.columbia.edu/tag/00H8) and
  [Section 110.19](https://stacks.math.columbia.edu/tag/02JE).
* Ported from T. Dupuy, T. Tucker and Z. Wang,
  [pcfawd-formalization](https://github.com/tdupu/pcfawd-formalization) at commit
  `9a20b3f351446d64e6015d704198bc71c7002008` (Apache-2.0), `lean/Pcf/Bounding/SchemeDynamics.lean`:
  `coheight_apply_eq_coheight` is its `Pcf.coheight_apply_eq_of_finite_dominant_normal`, whose
  ring-level step is its `Pcf.height_under_eq_of_finite_of_normal`
  (`lean/Pcf/Bounding/Divisors.lean`).
-/

public section

open CategoryTheory AlgebraicGeometry Order TauCeti.AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Hom

universe u

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- A finite dominant morphism of integral schemes with locally Noetherian normal target preserves
the coheight of every point. -/
@[simp] theorem coheight_apply_eq_coheight [IsFinite f] [IsDominant f]
    [IsIntegral X] [IsLocallyNoetherian Y] [IsNormalScheme Y] (x : X) :
    coheight (f x) = coheight x := by
  have : IsSchemeTheoreticallyDominant f := .of_isDominant f
  have himage : IsIrreducible (Set.range f) := by
    simpa only [Set.image_univ] using
      (IrreducibleSpace.isIrreducible_univ X).image f f.continuous.continuousOn
  have : IrreducibleSpace Y := by
    apply (irreducibleSpace_def Y).mpr
    simpa only [Set.top_eq_univ, f.denseRange.closure_eq] using himage.closure
  have : IsIntegral Y := isIntegral_of_irreducibleSpace_of_isReduced Y
  obtain ⟨U, hU, hxU, -⟩ := exists_isAffineOpen_mem_and_subset (x := f x) (U := ⊤) trivial
  have hV : IsAffineOpen (f ⁻¹ᵁ U) := hU.preimage f
  have : Nonempty U := ⟨⟨f x, hxU⟩⟩
  have : Nonempty (f ⁻¹ᵁ U) := ⟨⟨x, hxU⟩⟩
  let := (f.app U).hom.toAlgebra
  have : Module.Finite Γ(Y, U) Γ(X, f ⁻¹ᵁ U) := f.finite_app U hU
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
  have : IsDomain Γ(X, f ⁻¹ᵁ U) := inferInstance
  exact (Ideal.height_eq_height_under_of_quasiFinite _).symm

/-- A finite dominant morphism of integral schemes with locally Noetherian normal target sends
points of coheight one to points of coheight one (going down, Stacks, Proposition 10.38.7
(00H8)). This is the scheme-theoretic codimension consequence of going down, rather than
the ring-theoretic existence statement of that tag. -/
@[stacks 00H8 "codimension-one consequence for finite dominant morphisms to normal schemes"]
theorem coheight_apply_eq_one_of_coheight_eq_one [IsLocallyNoetherian Y] [IsNormalScheme Y]
    [IsFinite f] [IsDominant f] [IsIntegral X]
    (x : X) (hx : coheight x = 1) : coheight (f x) = 1 :=
  (coheight_apply_eq_coheight f x).trans hx

end AlgebraicGeometry.Scheme.Hom
