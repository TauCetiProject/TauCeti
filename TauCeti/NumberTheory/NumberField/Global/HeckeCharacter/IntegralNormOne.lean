/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.Global.HeckeCharacter.Tame
public import TauCeti.NumberTheory.NumberField.Global.Ideles.Norm.Integral

/-!
# Local prescriptions on integral norm-one ideles

A weight and finitely many residue characters give a continuous character of the integral
norm-one subgroup: take the integer powers of the infinite coordinates and multiply by the
residue character values. This is the local prescription to be extended when constructing an
automorphic character with given weight and tame part.

The prescription is the local product in `New.AutChar.exists_hasWeight_of_prod_eq_one` in
lsernau/grh-lean (`72fead1`), following the prescribed-restriction construction for Hecke
characters (A. Raghuram, *Notes on the arithmetic of Hecke L-functions*, §4).
-/

public section

open NumberField IsDedekindDomain

namespace TauCeti.GlobalNumberFields

variable {L : Type*} [Field L] [NumberField L] [IsCMField L]

/-- The continuous character on integral norm-one ideles prescribed by an integer weight at
infinity (using `InfinitePlace.embedding`) and residue characters at a finite set of places. -/
noncomputable def integralNormOneCharacter (e : InfinitePlace L → ℤ)
    (S : Finset (HeightOneSpectrum (𝓞 L)))
    (ψ : ∀ w : S, (IsLocalRing.ResidueField (w.val.adicCompletionIntegers L))ˣ →* Circle) :
    integralNormOne (maximalRealSubfield L) L →ₜ* Circle where
  toFun u := (∏ w, w.normOneInfiniteCoord u.val ^ e w) *
    ∏ w : S, ψ w (w.val.integralUnitsReduction (integralNormOneToFinite u))
  map_one' := by simp
  map_mul' u v := by
    simp only [MulMemClass.coe_mul, map_mul, mul_zpow, Finset.prod_mul_distrib]
    ac_rfl
  continuous_toFun := by
    apply Continuous.mul
    · exact continuous_finsetProd _ fun w _ ↦
        (w.normOneInfiniteCoord.continuous.comp continuous_subtypeVal).zpow (e w)
    · exact continuous_finsetProd _ fun w _ ↦
        (w.val.continuous_comp_integralUnitsReduction (ψ w)).comp integralNormOneToFinite.continuous

/-- Evaluate the prescription as a product of the archimedean and tame parts. -/
theorem integralNormOneCharacter_apply (e : InfinitePlace L → ℤ)
    (S : Finset (HeightOneSpectrum (𝓞 L)))
    (ψ : ∀ w : S, (IsLocalRing.ResidueField (w.val.adicCompletionIntegers L))ˣ →* Circle)
    (u : integralNormOne (maximalRealSubfield L) L) :
    integralNormOneCharacter e S ψ u =
      (∏ w, w.normOneInfiniteCoord u.val ^ e w) *
        ∏ w : S, ψ w (w.val.integralUnitsReduction (integralNormOneToFinite u)) := (rfl)

/-- A weight-zero tame character restricts to the local prescription with zero infinite weight. -/
theorem NormOneTameCharacter.apply_integralNormOne {S : Finset (HeightOneSpectrum (𝓞 L))}
    (ξ : NormOneTameCharacter (maximalRealSubfield L) L S)
    (u : integralNormOne (maximalRealSubfield L) L) :
    ξ.toContinuousMonoidHom u.val = integralNormOneCharacter 0 S ξ.residueCharacter u := by
  rw [ξ.apply_integral u.val ((mem_integralNormOne_iff u.val).mp u.property),
    integralNormOneCharacter_apply]
  have hfinite : integralNormOneToFinite u =
      ⟨_, (mem_integralNormOne_iff u.val).mp u.property⟩ :=
    Subtype.ext (coe_integralNormOneToFinite u)
  simp only [Pi.zero_apply, zpow_zero, Finset.prod_const_one, one_mul, hfinite]

end TauCeti.GlobalNumberFields
