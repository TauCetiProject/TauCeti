/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.GaloisCohomology.WeilPairing.Local
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Dual.Separability
public import TauCeti.NumberTheory.LocalField.AbsoluteRamificationIndex
import TauCeti.Algebra.Module.ZMod.Annihilator
import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Point.Index.LocalField
import TauCeti.AlgebraicGeometry.EllipticCurve.GaloisCohomology.Isogeny.Finiteness
import TauCeti.AlgebraicGeometry.EllipticCurve.GaloisCohomology.WeilPairing.Cardinality
import TauCeti.AlgebraicGeometry.EllipticCurve.GaloisCohomology.WeilPairing.Orthogonality

/-!
# Exact local annihilation of the Kummer images of an isogeny and its dual

Let `K` be a finite extension of `ℚ_p` and `φ : E₁ → E₂` an isogeny of elliptic curves over `K`,
with dual `φ̂`. The images of the local Kummer maps

`E₂(K) → H¹(K, E₁[φ])`,   `E₁(K) → H¹(K, E₂[φ̂])`

are the local conditions of the Selmer groups `Sel_φ` and `Sel_φ̂`. Under the perfect local Tate
pairing `H¹(K, E₁[φ]) × H¹(K, E₂[φ̂]) → ℤ/deg φ` (`TauCeti.Isogeny.localTateKerWeilPairing`) they
are orthogonal (`TauCeti.Isogeny.localTateKerWeilPairing_eq_zero_of_mem_range_kummerMap`). This file
shows that each is the **exact annihilator** of the other: the Kummer image of `φ` is the set of
classes pairing to zero with the Kummer image of `φ̂`. This holds at every place of residue
characteristic `p`, including when `p` divides `deg φ`.

By the counting criterion for perfect pairings into `ℤ/n`
(`AddMonoidHom.eq_ker_compl₂_subtype_iff_forall_eq_zero_and_natCard_mul_eq_zmod`), orthogonality
upgrades to exact annihilation once the orders of the two Kummer images multiply to the order of
`H¹(K, E₁[φ])`. With `n = deg φ`, the image of the Kummer map of `φ` has order
`[E₂(K) : φ E₁(K)]`, and over a nonarchimedean local field

`[E₂(K) : φ E₁(K)] · [E₁(K) : φ̂ E₂(K)] = #E₁(K)[φ] · #E₂(K)[φ̂] · #(𝒪[K] ⧸ n 𝒪[K])`

(`index_range_mul_index_range_dual_eq_card_ker_mul_card_ker_dual_mul_of_localField` in the
namespace `TauCeti.Isogeny.Hom`), where the last factor is `p ^ ([K : ℚ_p] · v_p(n))`. Tate's
local Euler characteristic formula and local duality give the same value for `#H¹(K, E₁[φ])`
(`TauCeti.Isogeny.natCard_H1_kerCoeff`).

Together with the archimedean case (`WeilPairing.Archimedean`) and global reciprocity
(`WeilPairing.Reciprocity`), these are the local inputs of Cassels' formula for the ratio of the
orders of `Sel_φ` and `Sel_φ̂`.

## Main results

All in the namespace `TauCeti.Isogeny`:

* `natCard_localKummerCondition_mul_dual_eq_natCard_H1`: the local conditions of `φ`
  and `φ̂` have orders multiplying to `#H¹(K, E₁[φ])`.
* `localKummerCondition_eq_ker_compl₂_localTateKerWeilPairing_dual_subtype`: the local
  condition of `φ` is the exact annihilator of that of `φ̂`.
* `range_kummerMap_eq_ker_compl₂_localTateKerWeilPairing_dual_subtype`: the same for the Kummer
  images.

## References

* J. S. Milne, *Arithmetic Duality Theorems*, 2nd ed., I, Theorems 2.1 and 2.8.
* J. W. S. Cassels, *Arithmetic on curves of genus 1. VIII. On conjectures of Birch and
  Swinnerton-Dyer*, J. reine angew. Math. 217 (1965), 180–199.
* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], X.4.
-/

public section

noncomputable section

namespace TauCeti.Isogeny

open WeierstrassCurve TauCeti.ContCohomology Hom

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
  have := (ofIsogeny φ.dual).finite_H1_kerCoeff_of_isTopologicallyFinitelyGenerated
    (ofIsogeny_ne_zero φ.dual) (isTopologicallyFinitelyGenerated_absoluteGaloisGroup p K)
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

end TauCeti.Isogeny
