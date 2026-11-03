/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.ThetaSeries.Inversion
public import TauCeti.NumberTheory.ModularForms.ThetaSeries.Translation
public import TauCeti.NumberTheory.ModularForms.ThetaSeries.Cusp
public import Mathlib.NumberTheory.ModularForms.BoundedAtCusp
import Mathlib.LinearAlgebra.Matrix.FixedDetMatrices

/-!
# Boundedness of lattice theta series at rational cusps

For an even full lattice of rank `2k`, every coset theta series with offset in the dual lattice
is bounded at every rational cusp in weight `k`. This supplies the cusp-growth condition for
bundling these functions as modular forms, independently of their congruence transformation laws.

The translation law sends each coset series to a scalar multiple of itself, and the inversion
law sends it to a finite linear combination of coset series. Mathlib's
`FixedDetMatrices.induction_on` propagates boundedness under these two operations to every
matrix in `SL(2, ℤ)`. Each constituent is bounded at infinity by
`ZLattice.isBoundedAtImInfty_thetaCoset`. No linear independence of the coset series is needed
or asserted; in particular the relations `θ_γ = θ_{-γ}` cause no difficulty.

## Main statements

* `ZLattice.IsEven.isBoundedAtImInfty_thetaCoset_slash`: every integral modular-group slash of
  a dual-coset theta series is bounded at infinity.
* `ZLattice.IsEven.isBoundedAt_thetaCoset`: boundedness at every cusp of `SL(2, ℤ)`.
* `ZLattice.IsEven.isBoundedAt_thetaSeries`: the lattice's own theta series has the same property.

## References

* W. Ebeling, *Lattices and Codes*, 3rd ed., Chapter 2.
-/

public section

open Module UpperHalfPlane
open scoped ModularForm UpperHalfPlane MatrixGroups

namespace ZLattice.IsEven

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] {L : Submodule ℤ E} [DiscreteTopology L] [IsZLattice ℝ L]
  {k : ℕ}

/-- Every weight-`k` slash of a dual-coset theta series by an integral modular-group matrix
is bounded at infinity, for an even full lattice of rank `2k`. -/
theorem isBoundedAtImInfty_thetaCoset_slash (hL : IsEven L)
    (hk : finrank ℝ E = 2 * k) {γ : E} (hγ : γ ∈ dual L) (A : SL(2, ℤ)) :
    IsBoundedAtImInfty (thetaCoset L γ ∣[(k : ℤ)] A) := by
  classical
  -- Borel volume is only used internally by the inversion formula.
  borelize E
  let := hL.isIntegral.finite_discriminantGroup
  let := Fintype.ofFinite (DiscriminantGroup L)
  suffices h : ∀ γ : dual L, IsBoundedAtImInfty (thetaCoset L γ ∣[(k : ℤ)] A) from h ⟨γ, hγ⟩
  induction A using (FixedDetMatrices.induction_on one_ne_zero) with
  | h0 A ha hc _ hd =>
    rw [FixedDetMatrices.reps_one_id A ha hc hd]
    intro γ
    simpa using isBoundedAtImInfty_thetaCoset L (γ : E)
  | hS B ih =>
    -- The induction principle uses `FixedDetMatrix _ _ 1`; name the same subtype as
    -- `SL(2, ℤ)` so rewriting can find its multiplication and slash-action instances.
    change SL(2, ℤ) at B
    intro γ
    change IsBoundedAtImInfty (thetaCoset L γ ∣[(k : ℤ)] (ModularGroup.S * B))
    rw [SlashAction.slash_mul, hL.isIntegral.thetaCoset_slash_S hk,
      ModularForm.SL_smul_slash, SlashAction.sum_slash]
    apply (Filter.boundedFilterSubmodule ℂ atImInfty).smul_mem
    apply (Filter.boundedFilterSubmodule ℂ atImInfty).sum_mem
    intro δ _
    rw [ModularForm.SL_smul_slash]
    apply (Filter.boundedFilterSubmodule ℂ atImInfty).smul_mem
    have hδ := ih (Quotient.out δ)
    simpa only [← thetaCosetClass_mk, Submodule.Quotient.mk_out] using! hδ
  | hT B ih =>
    -- As in the `S` case, use the special-linear name of the fixed-determinant subtype.
    change SL(2, ℤ) at B
    intro γ
    change IsBoundedAtImInfty (thetaCoset L γ ∣[(k : ℤ)] (ModularGroup.T * B))
    rw [SlashAction.slash_mul, hL.thetaCoset_slash_T γ.2,
      ModularForm.SL_smul_slash]
    exact (Filter.boundedFilterSubmodule ℂ atImInfty).smul_mem _ (ih γ)

/-- Every integral modular-group slash of the theta series of an even full lattice of rank
`2k` is bounded at infinity in weight `k`. -/
theorem isBoundedAtImInfty_thetaSeries_slash (hL : IsEven L)
    (hk : finrank ℝ E = 2 * k) (A : SL(2, ℤ)) :
    IsBoundedAtImInfty (thetaSeries L ∣[(k : ℤ)] A) := by
  simpa using hL.isBoundedAtImInfty_thetaCoset_slash hk (zero_mem (dual L)) A

/-- The theta series of a coset with offset in the dual of an even full lattice of rank `2k`
is bounded at every rational cusp in weight `k`. -/
theorem isBoundedAt_thetaCoset (hL : IsEven L) (hk : finrank ℝ E = 2 * k)
    {γ : E} (hγ : γ ∈ dual L) {c : OnePoint ℝ} (hc : IsCusp c 𝒮ℒ) :
    c.IsBoundedAt (thetaCoset L γ) k := by
  apply (OnePoint.isBoundedAt_iff_forall_SL2Z hc).mpr
  intro A _
  exact hL.isBoundedAtImInfty_thetaCoset_slash hk hγ A

/-- The theta series of an even full lattice of rank `2k` is bounded at every rational cusp
in weight `k`. -/
theorem isBoundedAt_thetaSeries (hL : IsEven L) (hk : finrank ℝ E = 2 * k)
    {c : OnePoint ℝ} (hc : IsCusp c 𝒮ℒ) : c.IsBoundedAt (thetaSeries L) k := by
  simpa using hL.isBoundedAt_thetaCoset hk (zero_mem (dual L)) hc

end ZLattice.IsEven
