/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.GaloisCohomology.WeilPairing.Local
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Dual.Separability
public import TauCeti.NumberTheory.LocalField.AbsoluteRamificationIndex
public import TauCeti.RingTheory.DedekindDomain.AdicValuation.ValuativeRel
import TauCeti.Algebra.Module.ZMod.Annihilator
import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Point.Index.LocalField
import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Point.Index.NSmul
import TauCeti.AlgebraicGeometry.EllipticCurve.GaloisCohomology.WeilPairing.Cardinality
import TauCeti.AlgebraicGeometry.EllipticCurve.GaloisCohomology.WeilPairing.Orthogonality
import TauCeti.RingTheory.DedekindDomain.AdicValuation.Padic

/-!
# Exact annihilators of local Kummer images under local Tate duality

Let `K` be a finite compatible extension of `ℚ_p`, or more concretely the completion `F_u` of the
fraction field `F` of a Dedekind domain `A` at a height-one prime `u` with finite residue field in
characteristic zero. Local Tate duality gives perfect pairings `H¹(K, E[m]) × H¹(K, E[m]) → ℤ/m`
(`WeierstrassCurve.localTateWeilPairing_bijective`,
`WeierstrassCurve.localTateWeilPairing_flip_bijective`) and, for an isogeny `φ : E₁ → E₂` of degree
`n`, `H¹(K, E₁[φ]) × H¹(K, E₂[φ̂]) → ℤ/n` (`TauCeti.Isogeny.localTateKerWeilPairing_bijective`,
`TauCeti.Isogeny.localTateKerWeilPairing_flip_bijective`).

This file proves, both over any `FinitePadicExtension K p` and unconditionally at every finite
place `u : HeightOneSpectrum A` with finite residue field in characteristic zero (via the
`AdicCompletionPadic` structure of `TauCeti.RingTheory.DedekindDomain.AdicValuation.Padic`):

* the image of the `[m]`-Kummer map `E(K) → H¹(K, E[m])` satisfies `#(im δ_m)² = #H¹(K, E[m])` and
  is its own exact annihilator under `localTateWeilPairing` (including when `p ∣ m`), and the same
  holds without `DecidableEq` for the `[m]`-Selmer local condition `ker(H¹(K, E[m]) → H¹(K, E))`;
* for any isogeny `φ : E₁ → E₂`, the local conditions and Kummer images of `φ` and of its dual `φ̂`
  satisfy `#H¹_φ(K) · #H¹_φ̂(K) = #H¹(K, E₁[φ])` and are exact mutual annihilators under
  `localTateKerWeilPairing` and its transpose (including when `p ∣ deg φ`);
* the local obstruction quotients `H¹(K, E[m]) ⧸ im δ_m` and `H¹(K, E₁[φ]) ⧸ im δ_φ` have orders
  `#(im δ_m)` and `#(im δ_φ̂)`, respectively.

The proofs combine isotropy and orthogonality of the local Kummer images
(`WeierstrassCurve.localTateWeilPairing_kummerMap_kummerMap_eq_zero`,
`TauCeti.Isogeny.localTateKerWeilPairing_eq_zero_of_mem_range_kummerMap`), the formal-group index
identities (`WeierstrassCurve.index_range_nsmul_eq_natCard_torsionBy_mul_of_localField`, and
`index_range_mul_index_range_dual_eq_card_ker_mul_card_ker_dual_mul_of_localField` in
`TauCeti.Isogeny.Hom`),
the `p`-adic quotient count `#(𝒪[K] ⧸ n 𝒪[K]) = p ^ ([K : ℚ_p] · v_p(n))`
(`TauCeti.natCard_quotient_span_natCast_eq_pow_finrank_mul_padicValNat`), Tate's local Euler
characteristic formulas (`WeierstrassCurve.natCard_H1_torsionCoeff`,
`TauCeti.Isogeny.natCard_H1_kerCoeff`), and the `ℤ/n`-annihilator counting criterion
(`AddMonoidHom.eq_ker_compl₂_subtype_iff_forall_eq_zero_and_natCard_mul_eq_zmod`).

Together with the archimedean case (`WeilPairing.Archimedean`) and global reciprocity
(`WeilPairing.Reciprocity`), these are the local inputs of Cassels' formula for the ratio of the
orders of `Sel_φ` and `Sel_φ̂`.

## Main results

* `WeierstrassCurve.natCard_range_kummerMap_sq_eq_natCard_H1`,
  `WeierstrassCurve.ker_explicitCoeff1_torsionCoeffIncl_eq_ker_compl₂_localTateWeilPairing_subtype`,
  `WeierstrassCurve.range_kummerMap_eq_ker_compl₂_localTateWeilPairing_subtype`,
  `WeierstrassCurve.natCard_quotient_range_kummerMap_eq_natCard_range_kummerMap`, and their
  `_adicCompletion` counterparts (together with
  `WeierstrassCurve.natCard_range_kummerMap_adicCompletion` and
  `WeierstrassCurve.finite_range_kummerMap_adicCompletion`): order, Lagrangian self-annihilation,
  and obstruction-quotient order of the local `[m]`-Kummer image and `[m]`-Selmer local condition.
* `TauCeti.Isogeny.natCard_localKummerCondition_mul_dual_eq_natCard_H1`,
  `TauCeti.Isogeny.natCard_range_kummerMap_mul_dual_eq_natCard_H1`,
  `TauCeti.Isogeny.localKummerCondition_eq_ker_compl₂_localTateKerWeilPairing_dual_subtype`,
  `TauCeti.Isogeny.range_kummerMap_eq_ker_compl₂_localTateKerWeilPairing_dual_subtype`,
  `TauCeti.Isogeny.localKummerCondition_dual_eq_ker_compl₂_flip_localTateKerWeilPairing_subtype`,
  `TauCeti.Isogeny.range_kummerMap_dual_eq_ker_compl₂_flip_localTateKerWeilPairing_subtype`,
  `TauCeti.Isogeny.natCard_quotient_range_kummerMap_eq_natCard_range_kummerMap_dual`, and their
  `_adicCompletion` counterparts: complementary orders, exact mutual annihilation on both sides, and
  obstruction-quotient order for `φ` and `φ̂`.

## References

* J. S. Milne, *Arithmetic Duality Theorems*, 2nd ed., I, Theorems 2.1 and 2.8 and Proposition 3.8.
* J. W. S. Cassels, *Arithmetic on curves of genus 1. VIII. On conjectures of Birch and
  Swinnerton-Dyer*, J. reine angew. Math. 217 (1965), 180–199, Lemma 3.1.
* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], X.1 and X.4.
-/

public section

noncomputable section

open IsDedekindDomain TauCeti TauCeti.ContCohomology

/-! ### Exact annihilators of the `[m]`-Kummer image -/

namespace WeierstrassCurve

section FinitePadicExtension

variable {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] (p : ℕ) [Fact p.Prime] [FinitePadicExtension K p]
  (W : WeierstrassCurve K) [W.IsElliptic] (m : ℕ) (hm : IsUnit (m : K))

include p in
/-- **Square of the local `[m]`-Kummer order**: over a finite extension `K` of `ℚ_p`, the square of
the order of the `[m]`-Kummer image in `H¹(K, E[m])` equals `#H¹(K, E[m])`, including when `p`
divides `m`. -/
theorem natCard_range_kummerMap_sq_eq_natCard_H1 [DecidableEq K] :
    Nat.card (W.kummerMap m hm).range ^ 2 =
      Nat.card (H1 (AbsoluteGaloisGroup K) (W.TorsionCoeff m)) := by
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact hm.ne_zero Nat.cast_zero
  -- `AddSubgroup.torsionBy` is `@[reducible]` for `(Submodule.torsionBy ℤ _ _).toAddSubgroup`.
  rw [W.natCard_range_kummerMap m hm,
    W.index_range_nsmul_eq_natCard_torsionBy_mul_of_localField hm.ne_zero,
    natCard_quotient_span_natCast_eq_pow_finrank_mul_padicValNat K p m hm0,
    W.natCard_H1_torsionCoeff hm0 p, ← SetLike.coe_sort_coe (AddSubgroup.torsionBy _ _),
    Submodule.coe_toAddSubgroup, SetLike.coe_sort_coe]

include p in
/-- **The local `[m]`-Kummer image is its own exact annihilator under local Tate duality**: over a
finite extension `K` of `ℚ_p`, the Kummer image is a Lagrangian subgroup of `H¹(K, E[m])`, including
when `p` divides `m`. -/
theorem range_kummerMap_eq_ker_compl₂_localTateWeilPairing_subtype [DecidableEq K] :
    (W.kummerMap m hm).range =
      ((W.localTateWeilPairing m hm).compl₂ (W.kummerMap m hm).range.subtype).ker := by
  have := hm.neZero_natCast
  have := W.finite_H1_torsionCoeff m hm
  rw [(W.localTateWeilPairing m hm).eq_ker_compl₂_subtype_iff_forall_eq_zero_and_natCard_mul_eq_zmod
    (W.localTateWeilPairing_bijective m hm)
    (nsmul_H1_eq_zero fun P ↦ AddSubgroup.torsionBy.nsmul P)]
  refine ⟨?_, by rw [← sq, W.natCard_range_kummerMap_sq_eq_natCard_H1 p m hm]⟩
  rintro _ ⟨P, rfl⟩ _ ⟨Q, rfl⟩
  exact W.localTateWeilPairing_kummerMap_kummerMap_eq_zero m hm P Q

include p in
/-- **The `[m]`-Selmer local condition is its own exact annihilator under local Tate duality**,
stated without `DecidableEq` on `K` for the kernel of `H¹(K, E[m]) → H¹(K, E)`. -/
theorem ker_explicitCoeff1_torsionCoeffIncl_eq_ker_compl₂_localTateWeilPairing_subtype :
    (explicitCoeff1 (AbsoluteGaloisGroup K) (W.TorsionCoeff m)
        (W.torsionCoeffIncl m) continuous_of_discreteTopology).ker =
      ((W.localTateWeilPairing m hm).compl₂
        (explicitCoeff1 (AbsoluteGaloisGroup K) (W.TorsionCoeff m)
          (W.torsionCoeffIncl m) continuous_of_discreteTopology).ker.subtype).ker := by
  classical
  rw [← W.range_kummerMap m hm]
  exact W.range_kummerMap_eq_ker_compl₂_localTateWeilPairing_subtype p m hm

include p in
/-- Over a finite extension `K` of `ℚ_p`, the local obstruction quotient `H¹(K, E[m]) ⧸ im δ_m` has
the same order as the local `[m]`-Kummer image `im δ_m`. -/
theorem natCard_quotient_range_kummerMap_eq_natCard_range_kummerMap [DecidableEq K] :
    Nat.card (H1 (AbsoluteGaloisGroup K) (W.TorsionCoeff m) ⧸ (W.kummerMap m hm).range) =
      Nat.card (W.kummerMap m hm).range := by
  have := hm.neZero_natCast
  rw [← AddSubgroup.index_eq_card,
    ← (W.localTateWeilPairing m hm).natCard_ker_compl₂_subtype_eq_index_zmod
      (W.localTateWeilPairing_bijective m hm)
      (nsmul_H1_eq_zero fun P ↦ AddSubgroup.torsionBy.nsmul P),
    ← W.range_kummerMap_eq_ker_compl₂_localTateWeilPairing_subtype p m hm]

end FinitePadicExtension

private theorem natCast_ne_zero_of_isUnit_adicCompletion {A F : Type*} [CommRing A]
    [IsDedekindDomain A] [Field F] [Algebra A F] [IsFractionRing A F] (u : HeightOneSpectrum A)
    {m : ℕ} (hm : IsUnit (m : u.adicCompletion F)) : (m : A) ≠ 0 := fun h ↦
  hm.ne_zero (by rw [← map_natCast (algebraMap A (u.adicCompletion F)), h, map_zero])

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
  rw [W.natCard_range_kummerMap m hm,
    W.index_range_nsmul_eq_natCard_torsionBy_mul u (natCast_ne_zero_of_isUnit_adicCompletion u hm),
    ← SetLike.coe_sort_coe (AddSubgroup.torsionBy _ _), Submodule.coe_toAddSubgroup,
    SetLike.coe_sort_coe]

/-- The local `[m]`-Kummer image in `H¹(F_u, E[m])` is finite whenever `m` is invertible in
`F_u`. -/
theorem finite_range_kummerMap_adicCompletion :
    Finite (W.kummerMap m hm).range :=
  (W.finite_range_kummerMap_iff m hm).2
    (W.finiteIndex_range_nsmul u (natCast_ne_zero_of_isUnit_adicCompletion u hm))

end AdicKummerCard

section AdicAnnihilator

open scoped AdicCompletionPadic

variable {A : Type*} {F : Type} [CommRing A] [IsDedekindDomain A] [Field F] [CharZero F]
  [Algebra A F] [IsFractionRing A F] (u : HeightOneSpectrum A) [Finite (A ⧸ u.asIdeal)]
  (W : WeierstrassCurve (u.adicCompletion F)) [W.IsElliptic]
  (m : ℕ) (hm : IsUnit (m : u.adicCompletion F))

/-- **Square of the local `[m]`-Kummer order at a finite place**: in mixed characteristic, the
square of the order of the `[m]`-Kummer image in `H¹(F_u, E[m])` equals `#H¹(F_u, E[m])`, including
when `u` divides `m`. -/
theorem natCard_range_kummerMap_sq_eq_natCard_H1_adicCompletion
    [DecidableEq (u.adicCompletion F)] :
    Nat.card (W.kummerMap m hm).range ^ 2 =
      Nat.card (H1 (AbsoluteGaloisGroup (u.adicCompletion F)) (W.TorsionCoeff m)) :=
  W.natCard_range_kummerMap_sq_eq_natCard_H1 (ringChar (A ⧸ u.asIdeal)) m hm

/-- **The local `[m]`-Kummer image at a finite place `u` is its own exact annihilator** under local
Tate duality (including when `u` divides `m`). -/
theorem range_kummerMap_eq_ker_compl₂_localTateWeilPairing_adicCompletion
    [DecidableEq (u.adicCompletion F)] :
    (W.kummerMap m hm).range =
      ((W.localTateWeilPairing m hm).compl₂ (W.kummerMap m hm).range.subtype).ker :=
  W.range_kummerMap_eq_ker_compl₂_localTateWeilPairing_subtype (ringChar (A ⧸ u.asIdeal)) m hm

/-- **The `[m]`-Selmer local condition at a finite place `u` is its own exact annihilator** under
local Tate duality, stated without `DecidableEq` on `F_u`. -/
theorem ker_explicitCoeff1_torsionCoeffIncl_eq_ker_compl₂_localTateWeilPairing_adicCompletion :
    (explicitCoeff1 (AbsoluteGaloisGroup (u.adicCompletion F)) (W.TorsionCoeff m)
        (W.torsionCoeffIncl m) continuous_of_discreteTopology).ker =
      ((W.localTateWeilPairing m hm).compl₂
        (explicitCoeff1 (AbsoluteGaloisGroup (u.adicCompletion F)) (W.TorsionCoeff m)
          (W.torsionCoeffIncl m) continuous_of_discreteTopology).ker.subtype).ker :=
  W.ker_explicitCoeff1_torsionCoeffIncl_eq_ker_compl₂_localTateWeilPairing_subtype
    (ringChar (A ⧸ u.asIdeal)) m hm

/-- At every finite place `u` in mixed characteristic, the local obstruction quotient
`H¹(F_u, E[m]) ⧸ im δ_m` has the same order as the local `[m]`-Kummer image `im δ_m`. -/
theorem natCard_quotient_range_kummerMap_eq_natCard_range_kummerMap_adicCompletion
    [DecidableEq (u.adicCompletion F)] :
    Nat.card (H1 (AbsoluteGaloisGroup (u.adicCompletion F)) (W.TorsionCoeff m) ⧸
        (W.kummerMap m hm).range) =
      Nat.card (W.kummerMap m hm).range :=
  W.natCard_quotient_range_kummerMap_eq_natCard_range_kummerMap (ringChar (A ⧸ u.asIdeal)) m hm

end AdicAnnihilator

end WeierstrassCurve

/-! ### Exact mutual annihilators of the `φ`- and `φ̂`-Kummer images -/

namespace TauCeti.Isogeny

open WeierstrassCurve Hom

section FinitePadicExtension

variable {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] (p : ℕ) [Fact p.Prime] [FinitePadicExtension K p]
  {W₁ W₂ : WeierstrassCurve K} [W₁.IsElliptic] [W₂.IsElliptic]
  (φ : Isogeny W₁.toAffine W₂.toAffine)

include p

/-- **The local conditions of an isogeny and of its dual have complementary orders**: over a
finite extension `K` of `ℚ_p`, the local conditions `H¹_φ(K) ⊆ H¹(K, E₁[φ])` and
`H¹_φ̂(K) ⊆ H¹(K, E₂[φ̂])`, the kernels of the maps to `H¹(K, E₁)` and `H¹(K, E₂)`, satisfy

`#H¹_φ(K) · #H¹_φ̂(K) = #H¹(K, E₁[φ])`.

The residue characteristic `p` may divide `deg φ`. -/
theorem natCard_localKummerCondition_mul_dual_eq_natCard_H1 :
    Nat.card φ.localKummerCondition *
      Nat.card φ.dual.localKummerCondition =
      Nat.card (H1 (AbsoluteGaloisGroup K) (ofIsogeny φ).KerCoeff) := by
  classical
  have := FinitePadicExtension.charZero K p
  have hn : (φ.degree : K) ≠ 0 := Nat.cast_ne_zero.mpr φ.degree_ne_zero
  obtain ⟨_, _⟩ := φ.isSeparable_dual_and_self_iff.mpr hn
  have h := (ofIsogeny φ
    ).index_range_mul_index_range_dual_eq_card_ker_mul_card_ker_dual_mul_of_localField
    (by rwa [degree_ofIsogeny])
  rw [dual_ofIsogeny, degree_ofIsogeny,
    natCard_quotient_span_natCast_eq_pow_finrank_mul_padicValNat K p _ φ.degree_ne_zero] at h
  rw [← φ.range_kummerMap,
    ← φ.dual.range_kummerMap, natCard_range_kummerMap,
    natCard_range_kummerMap, h, φ.natCard_H1_kerCoeff p]

/-- **The Kummer images of an isogeny and of its dual have complementary orders** over a finite
extension `K` of `ℚ_p`, including when `p` divides `deg φ`. -/
theorem natCard_range_kummerMap_mul_dual_eq_natCard_H1 [DecidableEq K] :
    haveI := FinitePadicExtension.charZero K p
    letI := (φ.isSeparable_dual_and_self_iff.mpr (Nat.cast_ne_zero.mpr φ.degree_ne_zero)).2
    letI := (φ.isSeparable_dual_and_self_iff.mpr (Nat.cast_ne_zero.mpr φ.degree_ne_zero)).1
    Nat.card φ.kummerMap.range * Nat.card φ.dual.kummerMap.range =
      Nat.card (H1 (AbsoluteGaloisGroup K) (ofIsogeny φ).KerCoeff) := by
  have := FinitePadicExtension.charZero K p
  obtain ⟨_, _⟩ := φ.isSeparable_dual_and_self_iff.mpr (Nat.cast_ne_zero.mpr φ.degree_ne_zero)
  rw [φ.range_kummerMap, φ.dual.range_kummerMap]
  exact φ.natCard_localKummerCondition_mul_dual_eq_natCard_H1 p

/-- **The local condition of an isogeny is the exact annihilator of that of its dual**: over a
finite extension `K` of `ℚ_p`, a class in `H¹(K, E₁[φ])` lies in the local condition of `φ`, the
kernel of the map to `H¹(K, E₁)`, exactly when its local Tate pairing with every class in the local
condition of `φ̂` vanishes. The residue characteristic `p` may divide `deg φ`. -/
theorem localKummerCondition_eq_ker_compl₂_localTateKerWeilPairing_dual_subtype :
    haveI := FinitePadicExtension.charZero K p
    φ.localKummerCondition =
      ((φ.localTateKerWeilPairing (Nat.cast_ne_zero.mpr φ.degree_ne_zero).isUnit).compl₂
        φ.dual.localKummerCondition.subtype).ker := by
  classical
  have := FinitePadicExtension.charZero K p
  have hn : IsUnit (φ.degree : K) := (Nat.cast_ne_zero.mpr φ.degree_ne_zero).isUnit
  have := hn.neZero_natCast
  obtain ⟨_, _⟩ := φ.isSeparable_dual_and_self_iff.mpr hn.ne_zero
  have hcard := φ.natCard_localKummerCondition_mul_dual_eq_natCard_H1 p
  have : Finite (H1 (AbsoluteGaloisGroup K) (ofIsogeny φ.dual).KerCoeff) :=
    φ.dual.finite_H1_kerCoeff (φ.degree_dual.symm ▸ hn)
  have hkill (Q : (ofIsogeny φ.dual).KerCoeff) : φ.degree • Q = 0 := by
    simpa only [degree_dual] using φ.dual.degree_nsmul_kerCoeff_eq_zero Q
  refine ((φ.localTateKerWeilPairing hn
    ).eq_ker_compl₂_subtype_iff_forall_eq_zero_and_natCard_mul_eq_zmod
    (φ.localTateKerWeilPairing_bijective hn) (nsmul_H1_eq_zero hkill) _ _).mpr ⟨?_, hcard⟩
  intro a ha b hb
  rw [← φ.range_kummerMap] at ha
  rw [← φ.dual.range_kummerMap] at hb
  exact φ.localTateKerWeilPairing_eq_zero_of_mem_range_kummerMap hn ha hb

/-- **The Kummer image of an isogeny is the exact annihilator of that of its dual**: over a finite
extension `K` of `ℚ_p`, the image of `E₂(K)` in `H¹(K, E₁[φ])` consists of the classes whose local
Tate pairing with the image of `E₁(K)` in `H¹(K, E₂[φ̂])` vanishes. The residue characteristic `p`
may divide `deg φ`. -/
theorem range_kummerMap_eq_ker_compl₂_localTateKerWeilPairing_dual_subtype [DecidableEq K] :
    haveI := FinitePadicExtension.charZero K p
    letI := (φ.isSeparable_dual_and_self_iff.mpr (Nat.cast_ne_zero.mpr φ.degree_ne_zero)).2
    letI := (φ.isSeparable_dual_and_self_iff.mpr (Nat.cast_ne_zero.mpr φ.degree_ne_zero)).1
    φ.kummerMap.range =
      ((φ.localTateKerWeilPairing (Nat.cast_ne_zero.mpr φ.degree_ne_zero).isUnit).compl₂
        φ.dual.kummerMap.range.subtype).ker := by
  have := FinitePadicExtension.charZero K p
  obtain ⟨_, _⟩ := φ.isSeparable_dual_and_self_iff.mpr (Nat.cast_ne_zero.mpr φ.degree_ne_zero)
  rw [φ.range_kummerMap, φ.dual.range_kummerMap]
  exact φ.localKummerCondition_eq_ker_compl₂_localTateKerWeilPairing_dual_subtype p

/-- **The local condition of the dual isogeny `φ̂` is the exact annihilator of that of `φ`** under
the transposed local Tate pairing, over a finite extension `K` of `ℚ_p` (including when `p` divides
`deg φ`). -/
theorem localKummerCondition_dual_eq_ker_compl₂_flip_localTateKerWeilPairing_subtype :
    haveI := FinitePadicExtension.charZero K p
    φ.dual.localKummerCondition =
      ((φ.localTateKerWeilPairing (Nat.cast_ne_zero.mpr φ.degree_ne_zero).isUnit).flip.compl₂
        φ.localKummerCondition.subtype).ker := by
  classical
  have := FinitePadicExtension.charZero K p
  have hn : IsUnit (φ.degree : K) := (Nat.cast_ne_zero.mpr φ.degree_ne_zero).isUnit
  have := hn.neZero_natCast
  obtain ⟨_, _⟩ := φ.isSeparable_dual_and_self_iff.mpr hn.ne_zero
  have := φ.finite_H1_kerCoeff hn
  refine ((φ.localTateKerWeilPairing hn
    ).flip.eq_ker_compl₂_subtype_iff_forall_eq_zero_and_natCard_mul_eq_zmod
    (φ.localTateKerWeilPairing_flip_bijective hn)
    (nsmul_H1_eq_zero φ.degree_nsmul_kerCoeff_eq_zero) _ _).mpr ⟨?_, ?_⟩
  · intro b hb a ha
    rw [← φ.range_kummerMap] at ha
    rw [← φ.dual.range_kummerMap] at hb
    exact φ.localTateKerWeilPairing_eq_zero_of_mem_range_kummerMap hn ha hb
  · rw [mul_comm, φ.natCard_localKummerCondition_mul_dual_eq_natCard_H1 p,
      φ.natCard_H1_kerCoeff_eq_dual hn]

/-- **The Kummer image of the dual isogeny `φ̂` is the exact annihilator of that of `φ`** under the
transposed local Tate pairing, over a finite extension `K` of `ℚ_p` (including when `p` divides
`deg φ`). -/
theorem range_kummerMap_dual_eq_ker_compl₂_flip_localTateKerWeilPairing_subtype [DecidableEq K] :
    haveI := FinitePadicExtension.charZero K p
    letI := (φ.isSeparable_dual_and_self_iff.mpr (Nat.cast_ne_zero.mpr φ.degree_ne_zero)).2
    letI := (φ.isSeparable_dual_and_self_iff.mpr (Nat.cast_ne_zero.mpr φ.degree_ne_zero)).1
    φ.dual.kummerMap.range =
      ((φ.localTateKerWeilPairing (Nat.cast_ne_zero.mpr φ.degree_ne_zero).isUnit).flip.compl₂
        φ.kummerMap.range.subtype).ker := by
  have := FinitePadicExtension.charZero K p
  obtain ⟨_, _⟩ := φ.isSeparable_dual_and_self_iff.mpr (Nat.cast_ne_zero.mpr φ.degree_ne_zero)
  rw [φ.range_kummerMap, φ.dual.range_kummerMap]
  exact φ.localKummerCondition_dual_eq_ker_compl₂_flip_localTateKerWeilPairing_subtype p

/-- **Order of the local isogeny obstruction quotient**: over a finite extension `K` of `ℚ_p`
(including when `p` divides `deg φ`), `H¹(K, E₁[φ]) ⧸ im δ_φ` has the same finite order as the dual
Kummer image `im δ_φ̂`. -/
theorem natCard_quotient_range_kummerMap_eq_natCard_range_kummerMap_dual [DecidableEq K] :
    haveI := FinitePadicExtension.charZero K p
    letI := (φ.isSeparable_dual_and_self_iff.mpr (Nat.cast_ne_zero.mpr φ.degree_ne_zero)).2
    letI := (φ.isSeparable_dual_and_self_iff.mpr (Nat.cast_ne_zero.mpr φ.degree_ne_zero)).1
    Nat.card (H1 (AbsoluteGaloisGroup K) (ofIsogeny φ).KerCoeff ⧸ φ.kummerMap.range) =
      Nat.card φ.dual.kummerMap.range := by
  have := FinitePadicExtension.charZero K p
  have hn : IsUnit (φ.degree : K) := (Nat.cast_ne_zero.mpr φ.degree_ne_zero).isUnit
  have := hn.neZero_natCast
  obtain ⟨_, _⟩ := φ.isSeparable_dual_and_self_iff.mpr hn.ne_zero
  rw [← AddSubgroup.index_eq_card,
    ← (φ.localTateKerWeilPairing hn).flip.natCard_ker_compl₂_subtype_eq_index_zmod
      (φ.localTateKerWeilPairing_flip_bijective hn)
      (nsmul_H1_eq_zero φ.degree_nsmul_kerCoeff_eq_zero),
    ← φ.range_kummerMap_dual_eq_ker_compl₂_flip_localTateKerWeilPairing_subtype p]

end FinitePadicExtension

section AdicAnnihilator

open scoped AdicCompletionPadic

variable {A : Type*} {F : Type} [CommRing A] [IsDedekindDomain A] [Field F] [CharZero F]
  [Algebra A F] [IsFractionRing A F] (u : HeightOneSpectrum A) [Finite (A ⧸ u.asIdeal)]
  {W₁ W₂ : WeierstrassCurve (u.adicCompletion F)} [W₁.IsElliptic] [W₂.IsElliptic]
  (φ : Isogeny W₁.toAffine W₂.toAffine)

/-- **Complementary orders of the local conditions of `φ` and `φ̂` at a finite place**: at every
finite place `u` in mixed characteristic (including places dividing `deg φ`),
`#H¹_φ(F_u) · #H¹_φ̂(F_u) = #H¹(F_u, E₁[φ])`. -/
theorem natCard_localKummerCondition_mul_dual_eq_natCard_H1_adicCompletion :
    Nat.card φ.localKummerCondition * Nat.card φ.dual.localKummerCondition =
      Nat.card (H1 (AbsoluteGaloisGroup (u.adicCompletion F)) (ofIsogeny φ).KerCoeff) :=
  φ.natCard_localKummerCondition_mul_dual_eq_natCard_H1 (ringChar (A ⧸ u.asIdeal))

/-- **Order product of the local `φ`- and `φ̂`-Kummer images at a finite place**: at every finite
place `u` in mixed characteristic (including places dividing `deg φ`), the orders of the local
Kummer images of `φ` and of its dual `φ̂` multiply to `#H¹(F_u, E₁[φ])`. -/
theorem natCard_range_kummerMap_mul_dual_eq_natCard_H1_adicCompletion
    [DecidableEq (u.adicCompletion F)] :
    Nat.card φ.kummerMap.range * Nat.card φ.dual.kummerMap.range =
      Nat.card (H1 (AbsoluteGaloisGroup (u.adicCompletion F)) (ofIsogeny φ).KerCoeff) :=
  φ.natCard_range_kummerMap_mul_dual_eq_natCard_H1 (ringChar (A ⧸ u.asIdeal))

/-- **The `φ`-Selmer local condition at a finite place `u` is the exact annihilator of the
`φ̂`-Selmer local condition** under local Tate duality, stated without `DecidableEq` on `F_u`. -/
theorem localKummerCondition_eq_ker_compl₂_localTateKerWeilPairing_dual_subtype_adicCompletion
    (hn : IsUnit (φ.degree : u.adicCompletion F)) :
    φ.localKummerCondition =
      ((φ.localTateKerWeilPairing hn).compl₂ φ.dual.localKummerCondition.subtype).ker :=
  φ.localKummerCondition_eq_ker_compl₂_localTateKerWeilPairing_dual_subtype
    (ringChar (A ⧸ u.asIdeal))

/-- **The local `φ`-Kummer image at a finite place `u` is the exact annihilator of the local
`φ̂`-Kummer image** under local Tate duality (including when `u` divides `deg φ`). -/
theorem range_kummerMap_eq_ker_compl₂_localTateKerWeilPairing_dual_subtype_adicCompletion
    [DecidableEq (u.adicCompletion F)] (hn : IsUnit (φ.degree : u.adicCompletion F)) :
    φ.kummerMap.range =
      ((φ.localTateKerWeilPairing hn).compl₂ φ.dual.kummerMap.range.subtype).ker :=
  φ.range_kummerMap_eq_ker_compl₂_localTateKerWeilPairing_dual_subtype
    (ringChar (A ⧸ u.asIdeal))

/-- **The `φ̂`-Selmer local condition at a finite place `u` is the exact annihilator of the
`φ`-Selmer local condition** under the transposed local Tate pairing, stated without `DecidableEq`
on `F_u`. -/
theorem localKummerCondition_dual_eq_ker_compl₂_flip_localTateKerWeilPairing_subtype_adicCompletion
    (hn : IsUnit (φ.degree : u.adicCompletion F)) :
    φ.dual.localKummerCondition =
      ((φ.localTateKerWeilPairing hn).flip.compl₂ φ.localKummerCondition.subtype).ker :=
  φ.localKummerCondition_dual_eq_ker_compl₂_flip_localTateKerWeilPairing_subtype
    (ringChar (A ⧸ u.asIdeal))

/-- **The local `φ̂`-Kummer image at a finite place `u` is the exact annihilator of the local
`φ`-Kummer image** under the transposed local Tate pairing (including when `u` divides
`deg φ`). -/
theorem range_kummerMap_dual_eq_ker_compl₂_flip_localTateKerWeilPairing_subtype_adicCompletion
    [DecidableEq (u.adicCompletion F)] (hn : IsUnit (φ.degree : u.adicCompletion F)) :
    φ.dual.kummerMap.range =
      ((φ.localTateKerWeilPairing hn).flip.compl₂ φ.kummerMap.range.subtype).ker :=
  φ.range_kummerMap_dual_eq_ker_compl₂_flip_localTateKerWeilPairing_subtype
    (ringChar (A ⧸ u.asIdeal))

/-- **Order of the local isogeny obstruction quotient at a finite place**: at every finite place `u`
in mixed characteristic (including places dividing `deg φ`), `H¹(F_u, E₁[φ]) ⧸ im δ_φ` has the same
finite order as the dual Kummer image `im δ_φ̂`. -/
theorem natCard_quotient_range_kummerMap_eq_natCard_range_kummerMap_dual_adicCompletion
    [DecidableEq (u.adicCompletion F)] :
    Nat.card (H1 (AbsoluteGaloisGroup (u.adicCompletion F)) (ofIsogeny φ).KerCoeff ⧸
        φ.kummerMap.range) =
      Nat.card φ.dual.kummerMap.range :=
  φ.natCard_quotient_range_kummerMap_eq_natCard_range_kummerMap_dual (ringChar (A ⧸ u.asIdeal))

end AdicAnnihilator

end TauCeti.Isogeny

end
