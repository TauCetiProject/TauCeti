/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.GaloisCohomology.WeilPairing.Cardinality
public import TauCeti.AlgebraicGeometry.EllipticCurve.GaloisCohomology.WeilPairing.Orthogonality
public import TauCeti.RingTheory.DedekindDomain.AdicValuation.ValuativeRel
import TauCeti.Algebra.Module.ZMod.Annihilator
import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Point.Index.Isogeny.Basic
import TauCeti.NumberTheory.LocalField.IntegerRing.Padic

/-!
# The local Kummer images of an isogeny and its dual are exact annihilators

Let `F_u` be the completion of the fraction field of a Dedekind domain at a height-one prime `u`
with finite residue field, and suppose that `F_u` is a finite extension of `ℚ_p`. For an isogeny
`φ : E₁ → E₂` of elliptic curves over `F_u`, with dual `φ̂`, the local Kummer images
`H¹_φ(F_u) ⊆ H¹(F_u, E₁[φ])` and `H¹_φ̂(F_u) ⊆ H¹(F_u, E₂[φ̂])` are exact annihilators of each
other under the local Tate pairing `TauCeti.Isogeny.localTateKerWeilPairing`. This holds also
when `p` divides `deg φ`.

These are the local conditions of the Selmer groups `Sel_φ` and `Sel_φ̂` at `u`, so the result
says that the two Selmer structures are dual at every finite place, which is the local input to
Cassels' comparison of `#Sel_φ` with `#Sel_φ̂`.

The images are orthogonal by
`TauCeti.Isogeny.localTateKerWeilPairing_eq_zero_of_mem_range_kummerMap` and the pairing is
perfect by `TauCeti.Isogeny.localTateKerWeilPairing_bijective`, so by the counting criterion
`AddMonoidHom.eq_ker_compl₂_subtype_iff_forall_eq_zero_and_natCard_mul_eq_zmod` exactness
amounts to `#H¹_φ(F_u) · #H¹_φ̂(F_u) = #H¹(F_u, E₁[φ])`. With `n = deg φ`, the left side is
`#E₁(F_u)[φ] · #E₂(F_u)[φ̂] · #(O_u ⧸ n O_u)` by
`TauCeti.Isogeny.Hom.index_range_mul_index_range_dual_eq_card_ker_mul_card_ker_dual_mul`, and
Tate's local Euler characteristic formula gives the right side as
`#E₁(F_u)[φ] · #E₂(F_u)[φ̂] · p ^ ([F_u : ℚ_p] · v_p(n))`
(`TauCeti.Isogeny.natCard_H1_kerCoeff`). The last factors agree by
`TauCeti.natCard_integerRing_quotient_span_natCast`.

## Main results

All in the namespace `TauCeti.Isogeny`:

* `natCard_range_kummerMap_mul_dual_eq_natCard_H1_adicCompletion`:
  `#H¹_φ(F_u) · #H¹_φ̂(F_u) = #H¹(F_u, E₁[φ])`.
* `ker_explicitCoeff1_kerCoeffIncl_eq_ker_compl₂_localTateKerWeilPairing_dual_subtype`:
  the local condition of `Sel_φ` at `u` is the exact annihilator of that of `Sel_φ̂`.
* `range_kummerMap_eq_ker_compl₂_localTateKerWeilPairing_dual_subtype`:
  the local Kummer image of `φ` is the exact annihilator of that of `φ̂`.

## References

* J. S. Milne, *Arithmetic Duality Theorems*, 2nd ed., I, Theorems 2.1 and 2.8.
* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], X.4.
* J. W. S. Cassels, *Arithmetic on curves of genus 1. VIII. On conjectures of Birch and
  Swinnerton-Dyer*, J. reine angew. Math. 217 (1965), 180–199.
-/

public section

noncomputable section

namespace TauCeti.Isogeny

open IsDedekindDomain WeierstrassCurve TauCeti.ContCohomology TauCeti.ClassFieldTheory
open Hom (ofIsogeny)

variable {A : Type*} [CommRing A] [IsDedekindDomain A] {F : Type} [Field F] [Algebra A F]
  [IsFractionRing A F] {u : HeightOneSpectrum A} [Finite (A ⧸ u.asIdeal)]
  (p : ℕ) [Fact p.Prime] [FinitePadicExtension (u.adicCompletion F) p]
  {W₁ W₂ : WeierstrassCurve (u.adicCompletion F)} [W₁.IsElliptic] [W₂.IsElliptic]
  (φ : Isogeny W₁.toAffine W₂.toAffine)

/-- **The orders of the local Kummer images of `φ` and `φ̂` multiply to `#H¹(F_u, E₁[φ])`**
over a completion `F_u` that is a finite extension of `ℚ_p`, including when `p` divides
`deg φ`. -/
theorem natCard_range_kummerMap_mul_dual_eq_natCard_H1_adicCompletion
    [DecidableEq (u.adicCompletion F)] :
    letI := FinitePadicExtension.charZero (u.adicCompletion F) p
    Nat.card φ.kummerMap.range * Nat.card φ.dual.kummerMap.range =
      Nat.card (H1 (AbsoluteGaloisGroup (u.adicCompletion F)) (ofIsogeny φ).KerCoeff) := by
  have := FinitePadicExtension.charZero (u.adicCompletion F) p
  have hA : (φ.degree : A) ≠ 0 := fun h ↦ φ.degree_ne_zero <| Nat.cast_eq_zero.mp <| by
    rw [← map_natCast (algebraMap A (u.adicCompletion F)), h, map_zero]
  rw [natCard_range_kummerMap, natCard_range_kummerMap, ← Hom.dual_ofIsogeny,
    Hom.index_range_mul_index_range_dual_eq_card_ker_mul_card_ker_dual_mul u
      (by rwa [Hom.degree_ofIsogeny]),
    φ.natCard_H1_kerCoeff p, Hom.dual_ofIsogeny, Hom.degree_ofIsogeny,
    ← natCard_integerRing_quotient_span_natCast p φ.degree_ne_zero]
  -- `O_u` is the ring of integers of the valuative relation on `F_u`.
  exact congrArg _ (Nat.card_congr (Ideal.quotientEquiv _ _
    u.integerEquivAdicCompletionIntegers.symm
    (by rw [Ideal.map_span, Set.image_singleton, map_natCast])).toEquiv)

include p in
/-- A subgroup of `H¹(F_u, E₁[φ])` orthogonal to a subgroup `H` of `H¹(F_u, E₂[φ̂])` is the exact
annihilator of `H` once their orders multiply to `#H¹(F_u, E₁[φ])`. -/
private theorem eq_ker_compl₂_localTateKerWeilPairing_subtype
    (hn : IsUnit (φ.degree : u.adicCompletion F))
    (U : AddSubgroup (H1 (AbsoluteGaloisGroup (u.adicCompletion F)) (ofIsogeny φ).KerCoeff))
    (H : AddSubgroup (H1 (AbsoluteGaloisGroup (u.adicCompletion F)) (ofIsogeny φ.dual).KerCoeff))
    (horth : ∀ a ∈ U, ∀ b ∈ H, φ.localTateKerWeilPairing hn a b = 0)
    (hcard : Nat.card U * Nat.card H =
      Nat.card (H1 (AbsoluteGaloisGroup (u.adicCompletion F)) (ofIsogeny φ).KerCoeff)) :
    U = ((φ.localTateKerWeilPairing hn).compl₂ H.subtype).ker := by
  have := FinitePadicExtension.charZero (u.adicCompletion F) p
  -- `H¹(F_u, E₂[φ̂])` is finite, by the local Euler characteristic formula.
  have hfin : Nat.card (H1 (AbsoluteGaloisGroup (u.adicCompletion F))
      (ofIsogeny φ.dual).KerCoeff) ≠ 0 := by
    classical
    have := (ofIsogeny φ.dual).finite_ker_pointMapHom (Hom.ofIsogeny_ne_zero φ.dual)
    have := (ofIsogeny φ.dual.dual).finite_ker_pointMapHom (Hom.ofIsogeny_ne_zero φ.dual.dual)
    rw [φ.dual.natCard_H1_kerCoeff p]
    exact mul_ne_zero (mul_ne_zero Nat.card_pos.ne' Nat.card_pos.ne')
      (pow_ne_zero _ (Fact.out : p.Prime).ne_zero)
  have := Nat.finite_of_card_ne_zero hfin
  have hkill (Q : (ofIsogeny φ.dual).KerCoeff) : φ.degree • Q = 0 := by
    simpa only [degree_dual] using φ.dual.degree_nsmul_kerCoeff_eq_zero Q
  exact (AddMonoidHom.eq_ker_compl₂_subtype_iff_forall_eq_zero_and_natCard_mul_eq_zmod _
    (φ.localTateKerWeilPairing_bijective hn) (nsmul_H1_eq_zero hkill) U H).mpr ⟨horth, hcard⟩

include p in
/-- **The local condition of `Sel_φ` at a finite place is the exact annihilator of that of
`Sel_φ̂`** under local Tate duality, over a completion `F_u` that is a finite extension of `ℚ_p`.
The residue characteristic `p` may divide `deg φ`. -/
theorem ker_explicitCoeff1_kerCoeffIncl_eq_ker_compl₂_localTateKerWeilPairing_dual_subtype
    (hn : IsUnit (φ.degree : u.adicCompletion F)) :
    (explicitCoeff1 _ _ (ofIsogeny φ).kerCoeffIncl continuous_of_discreteTopology).ker =
      ((φ.localTateKerWeilPairing hn).compl₂
        (explicitCoeff1 _ _ (ofIsogeny φ.dual).kerCoeffIncl
          continuous_of_discreteTopology).ker.subtype).ker := by
  classical
  have := FinitePadicExtension.charZero (u.adicCompletion F) p
  refine φ.eq_ker_compl₂_localTateKerWeilPairing_subtype p hn _ _
    (fun _ ha _ hb ↦ ?_) ?_
  · rw [localTateKerWeilPairing_apply, φ.kerH1WeilPairing_eq_zero_of_mem_ker hn ha hb, map_zero,
      map_zero]
  · rw [← φ.range_kummerMap, ← φ.dual.range_kummerMap,
      φ.natCard_range_kummerMap_mul_dual_eq_natCard_H1_adicCompletion p]

/-- **The local Kummer image of `φ` is the exact annihilator of the local Kummer image of `φ̂`**
under local Tate duality, over a completion `F_u` that is a finite extension of `ℚ_p`. The
residue characteristic `p` may divide `deg φ`. -/
theorem range_kummerMap_eq_ker_compl₂_localTateKerWeilPairing_dual_subtype
    [DecidableEq (u.adicCompletion F)] (hn : IsUnit (φ.degree : u.adicCompletion F)) :
    letI := FinitePadicExtension.charZero (u.adicCompletion F) p
    φ.kummerMap.range =
      ((φ.localTateKerWeilPairing hn).compl₂ φ.dual.kummerMap.range.subtype).ker :=
  letI := FinitePadicExtension.charZero (u.adicCompletion F) p
  φ.eq_ker_compl₂_localTateKerWeilPairing_subtype p hn _ _
    (fun _ ha _ hb ↦ φ.localTateKerWeilPairing_eq_zero_of_mem_range_kummerMap hn ha hb)
    (φ.natCard_range_kummerMap_mul_dual_eq_natCard_H1_adicCompletion p)

end TauCeti.Isogeny
