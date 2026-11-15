/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.GaloisCohomology.WeilPairing.Local
public import TauCeti.RingTheory.DedekindDomain.AdicValuation.ValuativeRel

import TauCeti.Algebra.Module.ZMod.Annihilator
import TauCeti.Algebra.Module.ZMod.Dual
import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Point.Index.Isogeny.Basic
import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Point.Index.NSmul
import TauCeti.AlgebraicGeometry.EllipticCurve.GaloisCohomology.Isogeny.Cardinality
import TauCeti.AlgebraicGeometry.EllipticCurve.GaloisCohomology.WeilPairing.Cardinality
import TauCeti.AlgebraicGeometry.EllipticCurve.GaloisCohomology.WeilPairing.Orthogonality
import TauCeti.NumberTheory.ClassFieldTheory.FiniteCohomology.Basic
import TauCeti.RepresentationTheory.Homological.ContCohomology.NatCardComparison
import TauCeti.RingTheory.DedekindDomain.AdicValuation.Padic

/-!
# Exact annihilators of local Kummer images under local Tate duality

Let `E` be an elliptic curve over a nonarchimedean local field `K` and `m` a natural number
invertible in `K`. Local Tate duality gives a pairing `H¹(K, E[m]) × H¹(K, E[m]) → ℤ/m` whose
left adjoint is bijective (`WeierstrassCurve.localTateWeilPairing_bijective`), and similarly for
an isogeny `φ : E₁ → E₂` of degree `n` invertible in `K` a pairing
`H¹(K, E₁[φ]) × H¹(K, E₂[φ̂]) → ℤ/n` (`TauCeti.Isogeny.localTateKerWeilPairing_bijective`).

This file first establishes finiteness of `H¹(K, E[m])` and `H¹(K, E₁[φ])` over any
nonarchimedean local field `K` in which the exponent is invertible, and deduces that the transposed
adjoints `(W.localTateWeilPairing m hm).flip` and `(φ.localTateKerWeilPairing hn).flip` are also
bijective, so that `H¹(K, E₁[φ])` and `H¹(K, E₂[φ̂])` have the same finite order.

Over the completion `F_u` of the fraction field `F` of a Dedekind domain `A` at a height-one prime
`u` with finite residue field, assuming `F` has characteristic zero, this file then proves that:

* the image of the `[m]`-Kummer map `E(F_u) → H¹(F_u, E[m])` satisfies
  `#(im δ_m)² = #H¹(F_u, E[m])` and is its own exact annihilator under `localTateWeilPairing`,
  including at places `u` dividing `m`;
* for any isogeny `φ : E₁ → E₂` over `F_u`, the Kummer images of `φ` and of its dual `φ̂` satisfy
  `#(im δ_φ) · #(im δ_φ̂) = #H¹(F_u, E₁[φ])` and are exact mutual annihilators under
  `localTateKerWeilPairing`, including at places `u` dividing `deg φ`;
* the same exact-annihilator identities hold without `DecidableEq` on `F_u` for the kernels of
  `H¹(F_u, E[m]) → H¹(F_u, E)` and `H¹(F_u, E₁[φ]) → H¹(F_u, E₁)`, which define the local
  conditions of the `m`-Selmer and `φ`-Selmer structures;
* the local obstruction quotient `H¹(F_u, E₁[φ]) ⧸ im δ_φ` has order `#(im δ_φ̂)`.

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

* `WeierstrassCurve.finite_H1_torsionCoeff`, `TauCeti.Isogeny.finite_H1_kerCoeff`: finiteness of
  `H¹(K, E[m])` and `H¹(K, E₁[φ])` over any nonarchimedean local field.
* `WeierstrassCurve.localTateWeilPairing_flip_bijective`,
  `TauCeti.Isogeny.localTateKerWeilPairing_flip_bijective`: bijectivity of the right adjoints of
  the local Tate pairings, and `TauCeti.Isogeny.natCard_H1_kerCoeff_eq_dual`.
* `WeierstrassCurve.natCard_range_kummerMap_adicCompletion`,
  `WeierstrassCurve.natCard_range_kummerMap_sq_eq_natCard_H1`,
  `WeierstrassCurve.range_kummerMap_eq_ker_compl₂_localTateWeilPairing`,
  `WeierstrassCurve.ker_explicitCoeff1_torsionCoeffIncl_eq_ker_compl₂_localTateWeilPairing`:
  order and Lagrangian self-annihilator property of the local `[m]`-Kummer image and `[m]`-Selmer
  local condition at every finite place.
* `TauCeti.Isogeny.natCard_range_kummerMap_mul_dual_eq_natCard_H1`,
  `TauCeti.Isogeny.range_kummerMap_eq_ker_compl₂_localTateKerWeilPairing`,
  `TauCeti.Isogeny.range_kummerMap_dual_eq_ker_flip_compl₂_localTateKerWeilPairing`,
  `TauCeti.Isogeny.ker_explicitCoeff1_kerCoeffIncl_eq_ker_compl₂_localTateKerWeilPairing`,
  `TauCeti.Isogeny.ker_explicitCoeff1_kerCoeffIncl_dual_eq_ker_flip_compl₂_localTateKerWeilPairing`,
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

/-! ### Finiteness and two-sided perfection over a nonarchimedean local field -/

section LocalField

/-- Unbundled degree-one Galois cohomology of a finite discrete `G_K`-module killed by `n` is
finite over any nonarchimedean local field `K` in which `n` is nonzero. -/
private theorem finite_H1_of_nsmul_eq_zero {K : Type} [Field K] [ValuativeRel K]
    [TopologicalSpace K] [IsNonarchimedeanLocalField K] {n : ℕ} (hn : (n : K) ≠ 0)
    (M : Type) [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
    [DistribMulAction (AbsoluteGaloisGroup K) M] [ContinuousSMul (AbsoluteGaloisGroup K) M]
    [Finite M] (hM : ∀ x : M, n • x = 0) :
    Finite (H1 (AbsoluteGaloisGroup K) M) := by
  let _ := AddCommGroup.zmodModule hM
  let A := ofDiscreteModule (ZMod n) (AbsoluteGaloisGroup K) M
  let r := absoluteGaloisGroupRestrictEquiv K
  let X : GalRep n K :=
    TopRep.res ((r : Field.absoluteGaloisGroup K →ₜ* AbsoluteGaloisGroup K) :
      Field.absoluteGaloisGroup K →* AbsoluteGaloisGroup K) A
  have hX : IsSmoothDiscrete (ZMod n) X :=
    (ofDiscreteModule_isSmoothDiscrete _ _ _).res r.continuous
  have hA : IsSmoothDiscrete (ZMod n) A := ofDiscreteModule_isSmoothDiscrete _ _ _
  let _ := TopRep.distribMulAction A
  have : Finite X.V := ‹Finite M›
  have := r.symm.toHomeomorph.isOpenEmbedding.locallyCompactSpace
  have : Finite (continuousCohomology 1 X) :=
    finite_continuousCohomology_of_le_one hn X hX le_rfl
  -- Supply the discrete topology and action continuity explicitly on the bundled carrier.
  have hc₁ := @TopRep.natCard_H1_eq_natCard_continuousCohomology
    _ _ _ _ _ _ _ A hA.discreteTopology hA.continuousSMul
  exact Nat.finite_of_card_ne_zero
    ((hc₁.trans (r.natCard_continuousCohomology_res A 1).symm) ▸ Nat.card_pos.ne')

/-- For a biadditive pairing `M × N → ZMod n` with `N` finite and killed by `n ≠ 0`, bijectivity
of the left adjoint `M → (N →+ ZMod n)` implies bijectivity of the right adjoint
`N → (M →+ ZMod n)`. -/
private theorem bijective_flip_of_bijective_zmod {n : ℕ} [NeZero n] {M N : Type*}
    [AddCommGroup M] [AddCommGroup N] [Finite N] (hN : ∀ y : N, n • y = 0)
    (e : M →+ N →+ ZMod n) (he : Function.Bijective e) :
    Function.Bijective e.flip := by
  obtain ⟨hsep, hrep⟩ := forall_eq_zero_and_exists_eq_of_bijective_flip hN e.flip he
  refine ⟨(injective_iff_map_eq_zero e.flip).2 fun y hy ↦ hsep y fun x ↦ ?_, fun φ ↦ ?_⟩
  · exact DFunLike.congr_fun hy x
  · obtain ⟨y, hy⟩ := hrep φ
    exact ⟨y, AddMonoidHom.ext hy⟩

namespace WeierstrassCurve

variable {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] (W : WeierstrassCurve K) [W.IsElliptic]
  (m : ℕ) (hm : IsUnit (m : K))

include hm in
/-- `H¹(K, E[m])` is finite when `m` is invertible in the nonarchimedean local field `K`. -/
theorem finite_H1_torsionCoeff :
    Finite (H1 (AbsoluteGaloisGroup K) (W.TorsionCoeff m)) := by
  have := hm.neZero_natCast
  exact finite_H1_of_nsmul_eq_zero hm.ne_zero (W.TorsionCoeff m)
    fun P ↦ AddSubgroup.torsionBy.nsmul P

/-- **Two-sided perfection of local Tate duality for `E[m]`.** Pairing in the second variable gives
a bijection from `H¹(K, E[m])` to its additive characters with values in `ℤ/m`. -/
theorem localTateWeilPairing_flip_bijective :
    Function.Bijective (W.localTateWeilPairing m hm).flip := by
  have := hm.neZero_natCast
  have := W.finite_H1_torsionCoeff m hm
  exact bijective_flip_of_bijective_zmod (nsmul_H1_eq_zero fun P ↦ AddSubgroup.torsionBy.nsmul P)
    (W.localTateWeilPairing m hm) (W.localTateWeilPairing_bijective m hm)

end WeierstrassCurve

namespace TauCeti.Isogeny

open WeierstrassCurve Hom

variable {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] {W₁ W₂ : WeierstrassCurve K} [W₁.IsElliptic] [W₂.IsElliptic]
  (φ : Isogeny W₁.toAffine W₂.toAffine) (hn : IsUnit (φ.degree : K))

include hn in
/-- `H¹(K, E₁[φ])` is finite when `deg φ` is invertible in the nonarchimedean local field `K`. -/
theorem finite_H1_kerCoeff :
    Finite (H1 (AbsoluteGaloisGroup K) (ofIsogeny φ).KerCoeff) := by
  have := (φ.isSeparable_dual_and_self_iff.mpr hn.ne_zero).2
  have : Finite (ofIsogeny φ).KerCoeff :=
    Nat.finite_of_card_ne_zero (φ.natCard_kerCoeff_eq_degree ▸ φ.degree_pos.ne')
  exact finite_H1_of_nsmul_eq_zero hn.ne_zero (ofIsogeny φ).KerCoeff
    φ.degree_nsmul_kerCoeff_eq_zero

/-- **Dual perfect local Tate duality for an isogeny.** Pairing in the second variable gives a
bijection from `H¹(K, E₂[φ̂])` to the additive characters of `H¹(K, E₁[φ])` with values in
`ℤ/deg φ`. -/
theorem localTateKerWeilPairing_flip_bijective :
    Function.Bijective (φ.localTateKerWeilPairing hn).flip := by
  have := hn.neZero_natCast
  have : Finite (H1 (AbsoluteGaloisGroup K) (ofIsogeny φ.dual).KerCoeff) :=
    φ.dual.finite_H1_kerCoeff (φ.degree_dual.symm ▸ hn)
  exact bijective_flip_of_bijective_zmod
    (φ.degree_dual ▸ nsmul_H1_eq_zero φ.dual.degree_nsmul_kerCoeff_eq_zero)
    (φ.localTateKerWeilPairing hn) (φ.localTateKerWeilPairing_bijective hn)

include hn in
/-- Over any nonarchimedean local field in which `deg φ` is invertible, `H¹(K, E₁[φ])` and
`H¹(K, E₂[φ̂])` have the same finite order by local Tate duality. -/
theorem natCard_H1_kerCoeff_eq_dual :
    Nat.card (H1 (AbsoluteGaloisGroup K) (ofIsogeny φ).KerCoeff) =
      Nat.card (H1 (AbsoluteGaloisGroup K) (ofIsogeny φ.dual).KerCoeff) := by
  have := hn.neZero_natCast
  rw [Nat.card_congr (Equiv.ofBijective _ (φ.localTateKerWeilPairing_bijective hn)),
    TauCeti.natCard_addMonoidHom_zmod
      (φ.degree_dual ▸ nsmul_H1_eq_zero φ.dual.degree_nsmul_kerCoeff_eq_zero)]

end TauCeti.Isogeny

end LocalField

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

variable {A F : Type} [CommRing A] [IsDedekindDomain A] [Field F] [CharZero F] [Algebra A F]
  [IsFractionRing A F] (u : HeightOneSpectrum A) [Finite (A ⧸ u.asIdeal)]
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
  have := W.finite_range_kummerMap_adicCompletion u m hm
  have hmul :
      Nat.card (H1 (AbsoluteGaloisGroup (u.adicCompletion F)) (W.TorsionCoeff m) ⧸
          (W.kummerMap m hm).range) *
        Nat.card (W.kummerMap m hm).range =
      Nat.card (W.kummerMap m hm).range * Nat.card (W.kummerMap m hm).range := by
    calc Nat.card (H1 (AbsoluteGaloisGroup (u.adicCompletion F)) (W.TorsionCoeff m) ⧸
            (W.kummerMap m hm).range) *
          Nat.card (W.kummerMap m hm).range
        = Nat.card (H1 (AbsoluteGaloisGroup (u.adicCompletion F)) (W.TorsionCoeff m)) :=
          (W.kummerMap m hm).range.index_mul_card
      _ = Nat.card (W.kummerMap m hm).range ^ 2 :=
          (W.natCard_range_kummerMap_sq_eq_natCard_H1 u m hm).symm
      _ = Nat.card (W.kummerMap m hm).range * Nat.card (W.kummerMap m hm).range := sq _
  exact Nat.mul_right_cancel Nat.card_pos hmul

end AdicAnnihilator

end WeierstrassCurve

/-! ### Exact mutual annihilators of the `φ`- and `φ̂`-Kummer images at a finite place -/

namespace TauCeti.Isogeny

open WeierstrassCurve Hom

variable {A F : Type} [CommRing A] [IsDedekindDomain A] [Field F] [CharZero F] [Algebra A F]
  [IsFractionRing A F] (u : HeightOneSpectrum A) [Finite (A ⧸ u.asIdeal)]
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
  have hnA : ((ofIsogeny φ).degree : A) ≠ 0 := fun h ↦
    (Nat.cast_ne_zero.mpr φ.degree_pos.ne' : (φ.degree : F) ≠ 0) <| by
      rw [← Hom.degree_ofIsogeny, ← map_natCast (algebraMap A F), h, map_zero]
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
theorem range_kummerMap_dual_eq_ker_flip_compl₂_localTateKerWeilPairing
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
theorem ker_explicitCoeff1_kerCoeffIncl_dual_eq_ker_flip_compl₂_localTateKerWeilPairing
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
    (φ.range_kummerMap_dual_eq_ker_flip_compl₂_localTateKerWeilPairing u hn).trans <|
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
  have hnA : ((ofIsogeny φ).degree : A) ≠ 0 := fun h ↦
    (Nat.cast_ne_zero.mpr φ.degree_pos.ne' : (φ.degree : F) ≠ 0) <| by
      rw [← Hom.degree_ofIsogeny, ← map_natCast (algebraMap A F), h, map_zero]
  have : Finite φ.kummerMap.range :=
    φ.finite_range_kummerMap_iff.2 (Hom.finiteIndex_range_pointMapHom_of_degree_ne_zero u hnA)
  have hmul :
      Nat.card (H1 (AbsoluteGaloisGroup (u.adicCompletion F)) (ofIsogeny φ).KerCoeff ⧸
          φ.kummerMap.range) *
        Nat.card φ.kummerMap.range =
      Nat.card φ.dual.kummerMap.range * Nat.card φ.kummerMap.range := by
    calc Nat.card (H1 (AbsoluteGaloisGroup (u.adicCompletion F)) (ofIsogeny φ).KerCoeff ⧸
            φ.kummerMap.range) *
          Nat.card φ.kummerMap.range
        = Nat.card (H1 (AbsoluteGaloisGroup (u.adicCompletion F)) (ofIsogeny φ).KerCoeff) :=
          φ.kummerMap.range.index_mul_card
      _ = Nat.card φ.kummerMap.range * Nat.card φ.dual.kummerMap.range :=
          (φ.natCard_range_kummerMap_mul_dual_eq_natCard_H1 u).symm
      _ = Nat.card φ.dual.kummerMap.range * Nat.card φ.kummerMap.range := mul_comm _ _
  exact Nat.mul_right_cancel Nat.card_pos hmul

end TauCeti.Isogeny

end
