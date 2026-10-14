/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.Invertible

/-!
# Effective Cartier divisors and invertible ideal sheaves

A closed subscheme of an arbitrary scheme is an effective Cartier divisor exactly when its
ideal sheaf, regarded as a module over the structure sheaf, is invertible. The forward implication
is the trivialization by a local nonzerodivisor. For the converse, a basis section of the ideal
sheaf gives a regular function via its inclusion into the structure sheaf. That function is a
nonzerodivisor, since the inclusion is injective, and generates the ideal on every affine open
inside the trivializing neighbourhood.

This characterization lets constructions of divisors use local rank-one module trivializations
instead of first choosing equations. It requires no reducedness, integrality or Noetherian
hypothesis, so it applies to divisors in families over nonreduced bases as well.

## Main results

* `Scheme.IdealSheafData.isSMulRegular_trivializationGenerator`: a local basis of an ideal sheaf
  is a nonzerodivisor in the structure sheaf.
* `Scheme.IdealSheafData.ideal_eq_span_trivializationGenerator`: that basis generates the ideal
  on each affine open inside the trivialization.
* `Scheme.IdealSheafData.isEffectiveCartier_iff_isInvertible_sheaf`: the characterization of
  effective Cartier divisors by invertible ideal sheaves.

## References

* The Stacks Project, *Divisors*, Section *Effective Cartier divisors*, Tag 01WQ.
-/

public section

open CategoryTheory Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData

noncomputable section

variable {X : Scheme.{u}} (I : X.IdealSheafData) {V : X.Opens}
  (t : SheafOfModules.free (R := X.ringCatSheaf.over V) PUnit ≅ I.sheaf.over V)

/-- A basis section of the ideal sheaf, restricted to any open subset of its trivializing
neighbourhood, maps to a nonzerodivisor in the structure sheaf. -/
theorem isSMulRegular_trivializationGenerator {W : X.Opens} (i : W ⟶ V) :
    IsSMulRegular (R := Γ(X, W)) Γ(X, W)
      (Scheme.Modules.Hom.app I.sheafι W
        (I.sheaf.presheaf.map i.op (Scheme.Modules.trivializationGenerator I.sheaf t)) :
          Γ(X, W)) := by
  intro r s h
  have h' :
      r • I.sheaf.presheaf.map i.op (Scheme.Modules.trivializationGenerator I.sheaf t) =
        s • I.sheaf.presheaf.map i.op (Scheme.Modules.trivializationGenerator I.sheaf t) := by
    apply I.sheafι_app_injective W
    -- The sections of the unit module are regular functions, but its module instance is
    -- elaborated through the sheaf category; `erw` matches the scalar-linearity lemma there.
    erw [Scheme.Modules.Hom.app_smul, Scheme.Modules.Hom.app_smul]
    exact (mul_comm _ _).trans (h.trans (mul_comm _ _))
  have hc := congrArg (Scheme.Modules.trivializationCoordinate I.sheaf t i) h'
  simpa only [LinearEquiv.map_smul,
    Scheme.Modules.trivializationCoordinate_map_trivializationGenerator, smul_eq_mul,
    mul_one] using hc

/-- On an affine open inside a rank-one trivialization of an ideal sheaf, its ideal is generated
by the regular function given by the restricted basis section. -/
theorem ideal_eq_span_trivializationGenerator (U : X.affineOpens) (hUV : U.1 ≤ V) :
    I.ideal U = Ideal.span (α := Γ(X, U))
      {(Scheme.Modules.Hom.app I.sheafι U.1
        (I.sheaf.presheaf.map (homOfLE hUV).op
          (Scheme.Modules.trivializationGenerator I.sheaf t)) : Γ(X, U))} := by
  ext a
  rw [← I.sections_eq_ideal U]
  -- As above, the ideal's generator is read through the unit module of the structure sheaf.
  erw [Ideal.mem_span_singleton]
  constructor
  · intro ha
    let s := I.sectionMk a ha
    let b : Γ(X, U) := Scheme.Modules.Hom.app I.sheafι U.1
      (I.sheaf.presheaf.map (homOfLE hUV).op
        (Scheme.Modules.trivializationGenerator I.sheaf t))
    have hs := congrArg (Scheme.Modules.Hom.app I.sheafι U.1)
      (Scheme.Modules.eq_trivializationCoordinate_smul_map_trivializationGenerator
        I.sheaf t (homOfLE hUV) s)
    refine ⟨Scheme.Modules.trivializationCoordinate I.sheaf t (homOfLE hUV) s, ?_⟩
    erw [Scheme.Modules.Hom.app_smul] at hs
    dsimp only [s] at hs
    erw [sheafι_app_sectionMk] at hs
    -- Read scalar multiplication in the unit module as multiplication of regular functions.
    have hs' : a = Scheme.Modules.trivializationCoordinate I.sheaf t (homOfLE hUV) s * b := hs
    exact hs'.trans (mul_comm _ _)
  · rintro ⟨r, rfl⟩
    exact (I.sections U.1).mul_mem_right r (I.sheafι_app_mem U.1 _)

/-- A closed subscheme whose ideal sheaf is invertible is an effective Cartier divisor.
The local equation is the image of a basis section under the inclusion into the structure sheaf.
No condition on the ambient scheme is needed. -/
theorem isEffectiveCartier_of_isInvertible_sheaf
    [TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible X I.sheaf] : I.IsEffectiveCartier := by
  rw [isEffectiveCartier_iff]
  intro x
  obtain ⟨V, t, hxV⟩ := Scheme.Modules.exists_mem_trivialization I.sheaf x
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, hUV⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hxV V.isOpen
  exact ⟨⟨U, hU⟩, hxU, _, I.isSMulRegular_trivializationGenerator t (homOfLE hUV),
    I.ideal_eq_span_trivializationGenerator t ⟨U, hU⟩ hUV⟩

/-- Effective Cartier divisors on an arbitrary scheme are exactly the closed subschemes with
invertible ideal sheaf. -/
theorem isEffectiveCartier_iff_isInvertible_sheaf :
    I.IsEffectiveCartier ↔ TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible X I.sheaf := by
  constructor
  · exact IsEffectiveCartier.isInvertible_sheaf
  · intro hI
    let := hI
    exact I.isEffectiveCartier_of_isInvertible_sheaf

end

end AlgebraicGeometry.Scheme.IdealSheafData
