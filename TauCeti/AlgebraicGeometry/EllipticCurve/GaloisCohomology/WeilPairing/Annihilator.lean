/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.GaloisCohomology.WeilPairing.Local
public import TauCeti.RingTheory.DedekindDomain.AdicValuation.ValuativeRel

import TauCeti.Algebra.Module.ZMod.Annihilator
import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Point.Index.Isogeny.Basic
import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Point.Index.NSmul
import TauCeti.AlgebraicGeometry.EllipticCurve.GaloisCohomology.WeilPairing.Cardinality
import TauCeti.AlgebraicGeometry.EllipticCurve.GaloisCohomology.WeilPairing.Orthogonality
import TauCeti.RingTheory.DedekindDomain.AdicValuation.Padic

/-!
# Exact annihilators of local Kummer images under local Tate duality

Let `E` be an elliptic curve over the completion `F_u` of the fraction field `F` of a Dedekind
domain `A` at a height-one prime `u` with finite residue field, assuming `F` has characteristic
zero. Local Tate duality gives perfect pairings `H¹(F_u, E[m]) × H¹(F_u, E[m]) → ℤ/m`
(`WeierstrassCurve.localTateWeilPairing_bijective`,
`WeierstrassCurve.localTateWeilPairing_flip_bijective`) and, for an isogeny `φ : E₁ → E₂` of degree
`n`, `H¹(F_u, E₁[φ]) × H¹(F_u, E₂[φ̂]) → ℤ/n` (`TauCeti.Isogeny.localTateKerWeilPairing_bijective`,
`TauCeti.Isogeny.localTateKerWeilPairing_flip_bijective`).

This file proves that:

* the image of the `[m]`-Kummer map `E(F_u) → H¹(F_u, E[m])` satisfies
  `#(im δ_m)² = #H¹(F_u, E[m])` and is its own exact annihilator under `localTateWeilPairing`,
  including at places `u` dividing `m`;
* for any isogeny `φ : E₁ → E₂` over `F_u`, the Kummer images of `φ` and of its dual `φ̂` satisfy
  `#(im δ_φ) · #(im δ_φ̂) = #H¹(F_u, E₁[φ])` and are exact mutual annihilators under
  `localTateKerWeilPairing`, including at places `u` dividing `deg φ`;
* the same exact-annihilator identities hold without `DecidableEq` on `F_u` for the kernels of
  `H¹(F_u, E[m]) → H¹(F_u, E)` and `H¹(F_u, E₁[φ]) → H¹(F_u, E₁)`, which define the local
  conditions of the `m`-Selmer and `φ`-Selmer structures;
* the local obstruction quotients `H¹(F_u, E[m]) ⧸ im δ_m` and `H¹(F_u, E₁[φ]) ⧸ im δ_φ` have
  orders `#(im δ_m)` and `#(im δ_φ̂)`, respectively.

The proof combines isotropy and orthogonality of the local Kummer images
(`WeierstrassCurve.localTateWeilPairing_kummerMap_kummerMap_eq_zero`,
`TauCeti.Isogeny.localTateKerWeilPairing_eq_zero_of_mem_range_kummerMap`), the formal-group index
identities (`WeierstrassCurve.index_range_nsmul_eq_natCard_torsionBy_mul`,
`TauCeti.Isogeny.Hom.index_range_mul_index_range_dual_eq_card_ker_mul_card_ker_dual_mul`), the
`p`-adic quotient count `#(O_u ⧸ n O_u) = p ^ ([F_u : ℚ_p] v_p(n))` from
`TauCeti.RingTheory.DedekindDomain.AdicValuation.Padic`,
the local Euler characteristic formulas (`WeierstrassCurve.natCard_H1_torsionCoeff`,
`TauCeti.Isogeny.natCard_H1_kerCoeff`), and the `ℤ/n`-annihilator counting criterion
(`AddMonoidHom.eq_ker_compl₂_subtype_iff_forall_eq_zero_and_natCard_mul_eq_zmod`).

## Main results

* `WeierstrassCurve.natCard_range_kummerMap_adicCompletion`,
  `WeierstrassCurve.natCard_range_kummerMap_sq_eq_natCard_H1`,
  `WeierstrassCurve.range_kummerMap_eq_ker_compl₂_localTateWeilPairing`,
  `WeierstrassCurve.ker_explicitCoeff1_torsionCoeffIncl_eq_ker_compl₂_localTateWeilPairing`,
  `WeierstrassCurve.natCard_quotient_range_kummerMap_eq_natCard_range_kummerMap`:
  order, Lagrangian self-annihilator property, and quotient order of the local `[m]`-Kummer image
  and `[m]`-Selmer local condition at every finite place.
* `TauCeti.Isogeny.natCard_range_kummerMap_mul_dual_eq_natCard_H1`,
  `TauCeti.Isogeny.range_kummerMap_eq_ker_compl₂_localTateKerWeilPairing`,
  `TauCeti.Isogeny.range_kummerMap_dual_eq_ker_compl₂_flip_localTateKerWeilPairing`,
  `TauCeti.Isogeny.ker_explicitCoeff1_kerCoeffIncl_eq_ker_compl₂_localTateKerWeilPairing`,
  `TauCeti.Isogeny.ker_explicitCoeff1_kerCoeffIncl_dual_eq_ker_compl₂_flip_localTateKerWeilPairing`,
  `TauCeti.Isogeny.natCard_quotient_range_kummerMap_eq_natCard_range_kummerMap_dual`:
  order product, exact mutual annihilator property, and quotient order for the local `φ`- and
  `φ̂`-Kummer images and Selmer local conditions at every finite place.

## References

* J. S. Milne, *Arithmetic Duality Theorems*, 2nd ed., I, Theorem 2.1 and Proposition 3.8.
* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], X.1 and X.4.
* J. W. S. Cassels, *Arithmetic on curves of genus 1. VIII. On conjectures of Birch and
  Swinnerton-Dyer*, J. reine angew. Math. 217 (1965), 180–199, Lemma 3.1.
-/

public section

noncomputable section

open IsDedekindDomain TauCeti TauCeti.ContCohomology TauCeti.ClassFieldTheory

/-! ### Exact annihilators of the `[m]`-Kummer image at a finite place -/

namespace WeierstrassCurve

section AdicKummerCard

variable {A F : Type*} [CommRing A] [IsDedekindDomain A] [Field F] [Algebra A F]
  [IsFractionRing A F] (u : HeightOneSpectrum A) [Finite (A ⧸ u.asIdeal)]
  (W : WeierstrassCurve (u.adicCompletion F)) [W.IsElliptic] [DecidableEq (u.adicCompletion F)]
  (m : ℕ) (hm : IsUnit (m : u.adicCompletion F))

/-- **Order of the local `[m]`-Kummer image**: over the completion `F_u` at a height-one prime `u`
with finite residue field, `#(im δ_m) = #E(F_u)[m] · #(O_u ⧸ m O_u)` whenever `m` is invertible in
`F_u`. -/
theorem natCard_range_kummerMap_adicCompletion :
    Nat.card (W.kummerMap m hm).range =
      Nat.card (AddSubgroup.torsionBy W.toAffine.Point m) *
        Nat.card (u.adicCompletionIntegers F ⧸
          Ideal.span {(m : u.adicCompletionIntegers F)}) := by
  have hmA : (m : A) ≠ 0 := fun h ↦
    hm.ne_zero (by rw [← map_natCast (algebraMap A (u.adicCompletion F)), h, map_zero])
  rw [W.natCard_range_kummerMap m hm, W.index_range_nsmul_eq_natCard_torsionBy_mul u hmA]
  rfl

/-- The local `[m]`-Kummer image in `H¹(F_u, E[m])` is finite whenever `m` is invertible in
`F_u`. -/
theorem finite_range_kummerMap_adicCompletion :
    Finite (W.kummerMap m hm).range := by
  have hmA : (m : A) ≠ 0 := fun h ↦
    hm.ne_zero (by rw [← map_natCast (algebraMap A (u.adicCompletion F)), h, map_zero])
  exact (W.finite_range_kummerMap_iff m hm).2 (W.finiteIndex_range_nsmul u hmA)

end AdicKummerCard

section AdicAnnihilator

variable {A : Type*} {F : Type} [CommRing A] [IsDedekindDomain A] [Field F] [CharZero F]
  [Algebra A F] [IsFractionRing A F] (u : HeightOneSpectrum A) [Finite (A ⧸ u.asIdeal)]
  (W : WeierstrassCurve (u.adicCompletion F)) [W.IsElliptic]
  (m : ℕ) (hm : IsUnit (m : u.adicCompletion F))

/-- **Square of the local `[m]`-Kummer order**: in mixed characteristic, the square of the order of
the `[m]`-Kummer image in `H¹(F_u, E[m])` equals `#H¹(F_u, E[m])`, including when `u` divides
`m`. -/
theorem natCard_range_kummerMap_sq_eq_natCard_H1 [DecidableEq (u.adicCompletion F)] :
    Nat.card (W.kummerMap m hm).range ^ 2 =
      Nat.card (H1 (AbsoluteGaloisGroup (u.adicCompletion F)) (W.TorsionCoeff m)) := by
  open scoped AdicCompletionPadic in
  let p := ringChar (A ⧸ u.asIdeal)
  have : Fact p.Prime := ⟨u.prime_ringChar_quotient⟩
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact hm.ne_zero Nat.cast_zero
  rw [W.natCard_range_kummerMap_adicCompletion u m hm,
    u.natCard_quotient_span_natCast_adicCompletionIntegers_eq_pow_finrank p hm0,
    (W.natCard_H1_torsionCoeff hm0 p).symm]

/-- **The local `[m]`-Kummer image is its own exact annihilator under local Tate duality**, at
every finite place `u` (including places dividing `m`). That is, the Kummer image is a maximal
isotropic (Lagrangian) subgroup of `H¹(F_u, E[m])`. -/
theorem range_kummerMap_eq_ker_compl₂_localTateWeilPairing [DecidableEq (u.adicCompletion F)] :
    (W.kummerMap m hm).range =
      ((W.localTateWeilPairing m hm).compl₂ (W.kummerMap m hm).range.subtype).ker := by
  have := hm.neZero_natCast
  have := W.finite_H1_torsionCoeff m hm
  rw [(W.localTateWeilPairing m hm).eq_ker_compl₂_subtype_iff_forall_eq_zero_and_natCard_mul_eq_zmod
    (W.localTateWeilPairing_bijective m hm)
    (nsmul_H1_eq_zero fun P ↦ AddSubgroup.torsionBy.nsmul P)]
  refine ⟨?_, by rw [← sq, W.natCard_range_kummerMap_sq_eq_natCard_H1 u m hm]⟩
  rintro _ ⟨P, rfl⟩ _ ⟨Q, rfl⟩
  exact W.localTateWeilPairing_kummerMap_kummerMap_eq_zero m hm P Q

/-- **The `[m]`-Selmer local condition is its own exact annihilator under local Tate duality**,
stated without `DecidableEq` on `F_u` for the kernel of `H¹(F_u, E[m]) → H¹(F_u, E)`. -/
theorem ker_explicitCoeff1_torsionCoeffIncl_eq_ker_compl₂_localTateWeilPairing :
    (explicitCoeff1 (AbsoluteGaloisGroup (u.adicCompletion F)) (W.TorsionCoeff m)
        (W.torsionCoeffIncl m) continuous_of_discreteTopology).ker =
      ((W.localTateWeilPairing m hm).compl₂
        (explicitCoeff1 (AbsoluteGaloisGroup (u.adicCompletion F)) (W.TorsionCoeff m)
          (W.torsionCoeffIncl m) continuous_of_discreteTopology).ker.subtype).ker := by
  classical
  rw [← W.range_kummerMap m hm]
  exact W.range_kummerMap_eq_ker_compl₂_localTateWeilPairing u m hm

/-- The local obstruction quotient `H¹(F_u, E[m]) ⧸ im δ_m` has the same order as the local
`[m]`-Kummer image `im δ_m`. -/
theorem natCard_quotient_range_kummerMap_eq_natCard_range_kummerMap
    [DecidableEq (u.adicCompletion F)] :
    Nat.card (H1 (AbsoluteGaloisGroup (u.adicCompletion F)) (W.TorsionCoeff m) ⧸
        (W.kummerMap m hm).range) =
      Nat.card (W.kummerMap m hm).range := by
  have := hm.neZero_natCast
  rw [← AddSubgroup.index_eq_card,
    ← (W.localTateWeilPairing m hm).natCard_ker_compl₂_subtype_eq_index_zmod
      (W.localTateWeilPairing_bijective m hm)
      (nsmul_H1_eq_zero fun P ↦ AddSubgroup.torsionBy.nsmul P),
    ← W.range_kummerMap_eq_ker_compl₂_localTateWeilPairing u m hm]

end AdicAnnihilator

end WeierstrassCurve

/-! ### Exact mutual annihilators of the `φ`- and `φ̂`-Kummer images at a finite place -/

namespace TauCeti.Isogeny

open WeierstrassCurve Hom

variable {A : Type*} {F : Type} [CommRing A] [IsDedekindDomain A] [Field F] [CharZero F]
  [Algebra A F] [IsFractionRing A F] (u : HeightOneSpectrum A) [Finite (A ⧸ u.asIdeal)]
  {W₁ W₂ : WeierstrassCurve (u.adicCompletion F)} [W₁.IsElliptic] [W₂.IsElliptic]
  (φ : Isogeny W₁.toAffine W₂.toAffine)

/-- **Order product of the local `φ`- and `φ̂`-Kummer images**: at every finite place `u` in mixed
characteristic (including places dividing `deg φ`), the orders of the local Kummer images of `φ`
and of its dual `φ̂` multiply to `#H¹(F_u, E₁[φ])`. -/
theorem natCard_range_kummerMap_mul_dual_eq_natCard_H1 [DecidableEq (u.adicCompletion F)] :
    Nat.card φ.kummerMap.range * Nat.card φ.dual.kummerMap.range =
      Nat.card (H1 (AbsoluteGaloisGroup (u.adicCompletion F)) (ofIsogeny φ).KerCoeff) := by
  open scoped AdicCompletionPadic in
  let p := ringChar (A ⧸ u.asIdeal)
  have : Fact p.Prime := ⟨u.prime_ringChar_quotient⟩
  have : CharZero A := (algebraMap A F).charZero
  have hnA : ((ofIsogeny φ).degree : A) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Hom.degree_ofIsogeny φ ▸ φ.degree_pos.ne')
  rw [φ.natCard_range_kummerMap, φ.dual.natCard_range_kummerMap, ← Hom.dual_ofIsogeny,
    Hom.index_range_mul_index_range_dual_eq_card_ker_mul_card_ker_dual_mul u hnA,
    Hom.dual_ofIsogeny, Hom.degree_ofIsogeny,
    u.natCard_quotient_span_natCast_adicCompletionIntegers_eq_pow_finrank p φ.degree_pos.ne',
    (φ.natCard_H1_kerCoeff p).symm]

/-- **The local `φ`-Kummer image is the exact annihilator of the local `φ̂`-Kummer image** under
local Tate duality, at every finite place `u` (including places dividing `deg φ`). -/
theorem range_kummerMap_eq_ker_compl₂_localTateKerWeilPairing [DecidableEq (u.adicCompletion F)]
    (hn : IsUnit (φ.degree : u.adicCompletion F)) :
    φ.kummerMap.range =
      ((φ.localTateKerWeilPairing hn).compl₂ φ.dual.kummerMap.range.subtype).ker := by
  have := hn.neZero_natCast
  have : Finite (H1 (AbsoluteGaloisGroup (u.adicCompletion F)) (ofIsogeny φ.dual).KerCoeff) :=
    φ.dual.finite_H1_kerCoeff (φ.degree_dual.symm ▸ hn)
  have hiff :=
    (φ.localTateKerWeilPairing hn).eq_ker_compl₂_subtype_iff_forall_eq_zero_and_natCard_mul_eq_zmod
      (φ.localTateKerWeilPairing_bijective hn)
      (φ.degree_dual ▸ nsmul_H1_eq_zero φ.dual.degree_nsmul_kerCoeff_eq_zero)
  rw [hiff]
  exact ⟨fun _ ha _ hb ↦ φ.localTateKerWeilPairing_eq_zero_of_mem_range_kummerMap hn ha hb,
    φ.natCard_range_kummerMap_mul_dual_eq_natCard_H1 u⟩

/-- **The local `φ̂`-Kummer image is the exact annihilator of the local `φ`-Kummer image** under
the transposed local Tate pairing, at every finite place `u` (including places dividing
`deg φ`). -/
theorem range_kummerMap_dual_eq_ker_compl₂_flip_localTateKerWeilPairing
    [DecidableEq (u.adicCompletion F)] (hn : IsUnit (φ.degree : u.adicCompletion F)) :
    φ.dual.kummerMap.range =
      ((φ.localTateKerWeilPairing hn).flip.compl₂ φ.kummerMap.range.subtype).ker := by
  have := hn.neZero_natCast
  have := φ.finite_H1_kerCoeff hn
  have hiff := (φ.localTateKerWeilPairing
    hn).flip.eq_ker_compl₂_subtype_iff_forall_eq_zero_and_natCard_mul_eq_zmod
    (φ.localTateKerWeilPairing_flip_bijective hn)
    (nsmul_H1_eq_zero φ.degree_nsmul_kerCoeff_eq_zero)
  rw [hiff]
  refine ⟨fun _ hb _ ha ↦ φ.localTateKerWeilPairing_eq_zero_of_mem_range_kummerMap hn ha hb, ?_⟩
  rw [mul_comm, φ.natCard_range_kummerMap_mul_dual_eq_natCard_H1 u,
    φ.natCard_H1_kerCoeff_eq_dual hn]

/-- **The `φ`-Selmer local condition is the exact annihilator of the `φ̂`-Selmer local condition**
under local Tate duality, stated without `DecidableEq` on `F_u` for the kernels of the maps to
point-coefficient cohomology. -/
theorem ker_explicitCoeff1_kerCoeffIncl_eq_ker_compl₂_localTateKerWeilPairing
    (hn : IsUnit (φ.degree : u.adicCompletion F)) :
    (explicitCoeff1 (AbsoluteGaloisGroup (u.adicCompletion F)) (ofIsogeny φ).KerCoeff
        (ofIsogeny φ).kerCoeffIncl continuous_of_discreteTopology).ker =
      ((φ.localTateKerWeilPairing hn).compl₂
        (explicitCoeff1 (AbsoluteGaloisGroup (u.adicCompletion F)) (ofIsogeny φ.dual).KerCoeff
          (ofIsogeny φ.dual).kerCoeffIncl continuous_of_discreteTopology).ker.subtype).ker := by
  classical
  have := (φ.isSeparable_dual_and_self_iff.mpr hn.ne_zero).2
  have := (φ.isSeparable_dual_and_self_iff.mpr hn.ne_zero).1
  exact φ.range_kummerMap.symm.trans <|
    (φ.range_kummerMap_eq_ker_compl₂_localTateKerWeilPairing u hn).trans <|
      congrArg (fun H : AddSubgroup _ ↦ ((φ.localTateKerWeilPairing hn).compl₂ H.subtype).ker)
        φ.dual.range_kummerMap

/-- **The `φ̂`-Selmer local condition is the exact annihilator of the `φ`-Selmer local condition**
under the transposed local Tate pairing, stated without `DecidableEq` on `F_u`. -/
theorem ker_explicitCoeff1_kerCoeffIncl_dual_eq_ker_compl₂_flip_localTateKerWeilPairing
    (hn : IsUnit (φ.degree : u.adicCompletion F)) :
    (explicitCoeff1 (AbsoluteGaloisGroup (u.adicCompletion F)) (ofIsogeny φ.dual).KerCoeff
        (ofIsogeny φ.dual).kerCoeffIncl continuous_of_discreteTopology).ker =
      ((φ.localTateKerWeilPairing hn).flip.compl₂
        (explicitCoeff1 (AbsoluteGaloisGroup (u.adicCompletion F)) (ofIsogeny φ).KerCoeff
          (ofIsogeny φ).kerCoeffIncl continuous_of_discreteTopology).ker.subtype).ker := by
  classical
  have := (φ.isSeparable_dual_and_self_iff.mpr hn.ne_zero).2
  have := (φ.isSeparable_dual_and_self_iff.mpr hn.ne_zero).1
  exact φ.dual.range_kummerMap.symm.trans <|
    (φ.range_kummerMap_dual_eq_ker_compl₂_flip_localTateKerWeilPairing u hn).trans <|
      congrArg (fun H : AddSubgroup _ ↦ ((φ.localTateKerWeilPairing hn).flip.compl₂ H.subtype).ker)
        φ.range_kummerMap

/-- **Order of the local isogeny obstruction quotient**: at every finite place `u` in mixed
characteristic (including places dividing `deg φ`), `H¹(F_u, E₁[φ]) ⧸ im δ_φ` has the same finite
order as the dual Kummer image `im δ_φ̂`. -/
theorem natCard_quotient_range_kummerMap_eq_natCard_range_kummerMap_dual
    [DecidableEq (u.adicCompletion F)] :
    Nat.card (H1 (AbsoluteGaloisGroup (u.adicCompletion F)) (ofIsogeny φ).KerCoeff ⧸
        φ.kummerMap.range) =
      Nat.card φ.dual.kummerMap.range := by
  have := u.adicCompletion_charZero (K := F)
  have hn : IsUnit (φ.degree : u.adicCompletion F) :=
    isUnit_iff_ne_zero.mpr (Nat.cast_ne_zero.mpr φ.degree_pos.ne')
  have := hn.neZero_natCast
  rw [← AddSubgroup.index_eq_card,
    ← (φ.localTateKerWeilPairing hn).flip.natCard_ker_compl₂_subtype_eq_index_zmod
      (φ.localTateKerWeilPairing_flip_bijective hn)
      (nsmul_H1_eq_zero φ.degree_nsmul_kerCoeff_eq_zero),
    ← φ.range_kummerMap_dual_eq_ker_compl₂_flip_localTateKerWeilPairing u hn]

end TauCeti.Isogeny

end
