/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ClassFieldTheory.Brauer.OpenSubgroup
public import TauCeti.FieldTheory.GaloisCohomology.BrauerTorsion
import TauCeti.RepresentationTheory.Homological.ContCohomology.Corestriction.Naturality

/-!
# Corestriction on local roots-of-unity cohomology

For a nonarchimedean local field `K`, an exponent `n` invertible in `K`, and an open subgroup
`U` of `G_K`, corestriction `H²(U, μₙ) → H²(G_K, μₙ)` is bijective. This is the coefficient
corestriction needed to transport the local Tate-duality pairing through Shapiro's lemma.

The Kummer inclusion identifies both groups with the `n`-torsion in the corresponding Brauer
cohomology groups. Corestriction commutes with that inclusion and is an isomorphism on Brauer
cohomology (`explicitCor2_unitsCoeff_bijective`), so its restriction to `n`-torsion is an
isomorphism too. No coprimality with the subgroup index or the residue characteristic is needed.

The statement uses the explicit low-degree model and the single ambient coefficient module
`KummerCoeff K n`, matching the generic duality and Shapiro API.

## Main result

* `TauCeti.ClassFieldTheory.explicitCor2_kummerCoeff_bijective`: degree-two corestriction on
  roots-of-unity coefficients is bijective for every open subgroup of a local `G_K`.

## References

* J.-P. Serre, *Galois Cohomology*, Chapter II, §5.2, Theorem 2 and its proof.
* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, second edition,
  (6.2.1) and (7.2.6).
-/

public noncomputable section

namespace TauCeti.ClassFieldTheory

open ContCohomology

variable (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] {n : ℕ} (hn : IsUnit (n : K))
  (U : Subgroup (AbsoluteGaloisGroup K)) [U.FiniteIndex]
  (hU : IsOpen (U : Set (AbsoluteGaloisGroup K)))

include hn

/-- Corestriction on local `H²` with roots-of-unity coefficients is bijective for every open
subgroup, for any exponent invertible in the field. This includes all nonzero exponents in
characteristic zero, even when they divide the subgroup index or the residue characteristic. -/
theorem explicitCor2_kummerCoeff_bijective :
    Function.Bijective (explicitCor2 (AbsoluteGaloisGroup K) (KummerCoeff K n) U hU) := by
  let S := kummerShortExact K n hn
  let i := explicitCoeff2 (AbsoluteGaloisGroup K) (KummerCoeff K n)
    S.inclDistribMulActionHom continuous_of_discreteTopology
  let j := explicitCoeff2 U (KummerCoeff K n)
    (S.restrict U).inclDistribMulActionHom continuous_of_discreteTopology
  let c := explicitCor2 (AbsoluteGaloisGroup K) (UnitsCoeff K) U hU
  let d := explicitCor2 (AbsoluteGaloisGroup K) (KummerCoeff K n) U hU
  have hi : Function.Injective i := explicitCoeff2_kummerShortExact_incl_injective K hn
  have hj : Function.Injective j :=
    explicitCoeff2_kummerShortExact_restrict_incl_injective K hn U (U.isClosed_of_isOpen hU)
  have hc : Function.Bijective c := explicitCor2_unitsCoeff_bijective K U hU
  have hcomm (x : H2 U (KummerCoeff K n)) : c (j x) = i (d x) := by
    have hi' : (S.inclDistribMulActionHom : KummerCoeff K n →+ UnitsCoeff K) = S.incl := by
      apply AddMonoidHom.ext
      intro m
      exact DiscreteShortExact.inclDistribMulActionHom_apply S m
    have hj' : ((S.restrict U).inclDistribMulActionHom :
        KummerCoeff K n →+ UnitsCoeff K) = S.incl := by
      apply AddMonoidHom.ext
      intro m
      -- Retype evaluation through the additive-hom coercion so the public restriction lemmas
      -- apply; the short exact sequence itself remains opaque.
      change (S.restrict U).inclDistribMulActionHom m = S.incl m
      rw [DiscreteShortExact.inclDistribMulActionHom_apply, DiscreteShortExact.restrict_incl]
    simp only [c, j, i, d, explicitCoeff2_eq_explicitMap2, hi', hj']
    exact explicitCor2_explicitMap2_id (AbsoluteGaloisGroup K) (KummerCoeff K n) U hU
      S.incl continuous_of_discreteTopology S.incl_equivariant x
  refine ⟨fun x y h => hj (hc.1 (by rw [hcomm, hcomm, h])), fun y => ?_⟩
  obtain ⟨z, hz⟩ := hc.2 (i y)
  have hny : n • i y = 0 :=
    (mem_range_explicitCoeff2_kummerShortExact_incl_iff K hn (i y)).1 ⟨y, rfl⟩
  have hnz : n • z = 0 := hc.1 (by rw [map_nsmul, hz, hny, map_zero])
  obtain ⟨x, hx⟩ :=
    (mem_range_explicitCoeff2_kummerShortExact_restrict_incl_iff K hn U z).2 hnz
  exact ⟨x, hi (by rw [← hcomm, hx, hz])⟩

end TauCeti.ClassFieldTheory
