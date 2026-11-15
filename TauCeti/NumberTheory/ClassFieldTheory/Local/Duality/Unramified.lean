/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ClassFieldTheory.Local.Duality.Cardinality
public import TauCeti.NumberTheory.ClassFieldTheory.Local.EulerCharacteristic.Theorem
public import TauCeti.NumberTheory.LocalField.Unramified.Cohomology

import TauCeti.Algebra.Module.ZMod.Annihilator
import TauCeti.RepresentationTheory.Homological.ContCohomology.NatCardComparison

/-!
# Unramified local Tate duality

Let `K` be a nonarchimedean local field, `M` a finite discrete `G_K`-module killed by `n`, and
`M' = Hom(M, μₙ)` its Kummer dual
(`TauCeti.InternalHom (AbsoluteGaloisGroup K) M (KummerCoeff K n)`). Over any nonarchimedean local
field and for any `n ≠ 0`, the unramified subgroups `H¹_ur(G_K, M)` and `H¹_ur(G_K, M')` are
orthogonal under Tate's degree-one duality pairing `TauCeti.ContCohomology.dualityMap1`: their cup
product inflates from `H²(G_K ⧸ I_K, μₙ^{I_K}) = 0`
(`TauCeti.ClassFieldTheory.dualityMap1_kummerCoeff_eq_zero_of_mem_unramifiedCohomology`).

When `K` is a finite extension of `ℚ_p` (`TauCeti.FinitePadicExtension K p`) and `p ∤ n`, Tate's
local Euler characteristic formula (`TauCeti.ClassFieldTheory.eulerCharacteristic_mixed`) gives
`#H¹(G_K, M) = #H⁰(G_K, M) · #H²(G_K, M)`. Combining the procyclic unramified count
`#H¹_ur(G_K, X) = #H⁰(G_K, X)` (`TauCeti.natCard_unramifiedCohomology_eq_natCard_H0`) for `M` and
`M'` with `#H²(G_K, M) = #H⁰(G_K, M')`
(`TauCeti.ClassFieldTheory.natCard_H2_eq_natCard_H0_internalHom`) yields

```text
#H¹_ur(G_K, M) · #H¹_ur(G_K, M') = #H¹(G_K, M),
```

which upgrades orthogonality to **Milne's unramified local duality theorem**: `H¹_ur(G_K, M)` and
`H¹_ur(G_K, M')` are exact mutual annihilators under local Tate duality.

## Main results

* `TauCeti.ClassFieldTheory.dualityMap1_kummerCoeff_eq_zero_of_mem_unramifiedCohomology`:
  unramified classes in `H¹(G_K, M)` and `H¹(G_K, Hom(M, μₙ))` pair to zero over any
  nonarchimedean local field.
* `TauCeti.ClassFieldTheory.finite_H1_of_nsmul_eq_zero`: `H¹(G_K, M)` is finite for any finite
  discrete `G_K`-module killed by `n` invertible in `K`.
* `TauCeti.ClassFieldTheory.natCard_H1_eq_natCard_H0_mul_natCard_H2_mul_pow`,
  `natCard_H1_eq_natCard_H0_mul_natCard_H2_of_not_dvd`, and
  `natCard_H1_eq_natCard_H0_mul_natCard_H2_of_not_dvd_exponent`: explicit-cohomology forms of
  Tate's local Euler characteristic formula over a finite extension of `ℚ_p`.
* `TauCeti.ClassFieldTheory.natCard_unramifiedCohomology_mul_internalHom_eq_natCard_H1`:
  `#H¹_ur(G_K, M) · #H¹_ur(G_K, Hom(M, μₙ)) = #H¹(G_K, M)` when `p ∤ n`.
* `TauCeti.ClassFieldTheory.unramifiedCohomology_eq_ker_compl₂_dualityMap1`,
  `unramifiedCohomology_internalHom_eq_ker_flip_compl₂_dualityMap1`,
  `mem_unramifiedCohomology_iff_forall_dualityMap1_eq_zero`, and
  `mem_unramifiedCohomology_internalHom_iff_forall_dualityMap1_eq_zero`: `H¹_ur(G_K, M)` and
  `H¹_ur(G_K, Hom(M, μₙ))` are exact mutual annihilators under `dualityMap1` when `p ∤ n`.

## References

* J. S. Milne, *Arithmetic Duality Theorems*, 2nd ed., Chapter I, Theorem 2.6.
* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., (7.2.15).
-/

public noncomputable section

namespace TauCeti.ClassFieldTheory

open ContCohomology

/-! ### Private bridge from unbundled `G_K`-modules to `GalRep n K` -/

section GalRepBridge

attribute [local instance] TopRep.distribMulAction

variable (K : Type) [Field K]
  {n : ℕ} (M : Type) [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
  [DistribMulAction (AbsoluteGaloisGroup K) M] [ContinuousSMul (AbsoluteGaloisGroup K) M]

/-- Bundle a discrete `G_K`-module killed by `n` as an object of `GalRep n K` by restricting along
`absoluteGaloisGroupRestrictEquiv K`. -/
private def toGalRep (hM : ∀ x : M, n • x = 0) : GalRep n K :=
  letI : Module (ZMod n) M := AddCommGroup.zmodModule hM
  haveI : ContinuousSMul (ZMod n) M := ⟨continuous_of_discreteTopology⟩
  TopRep.res
    (absoluteGaloisGroupRestrictEquiv K : Field.absoluteGaloisGroup K →* AbsoluteGaloisGroup K)
    (ofDiscreteModule (ZMod n) (AbsoluteGaloisGroup K) M)

/-- `toGalRep K M hM` is smooth and discrete. -/
private theorem isSmoothDiscrete_toGalRep (hM : ∀ x : M, n • x = 0) :
    IsSmoothDiscrete (ZMod n) (toGalRep K M hM) := by
  let _ : Module (ZMod n) M := AddCommGroup.zmodModule hM
  have : ContinuousSMul (ZMod n) M := ⟨continuous_of_discreteTopology⟩
  exact (ofDiscreteModule_isSmoothDiscrete (ZMod n) (AbsoluteGaloisGroup K) M).res
    (absoluteGaloisGroupRestrictEquiv K).continuous

/-- Discrete topology on the carrier of `toGalRep K M hM`. -/
private instance instDiscreteTopologyToGalRep (hM : ∀ x : M, n • x = 0) :
    DiscreteTopology (toGalRep K M hM).V :=
  (isSmoothDiscrete_toGalRep K M hM).discreteTopology

/-- `Fact` wrapper for `isSmoothDiscrete_toGalRep`. -/
private instance instFactIsSmoothDiscreteToGalRep (hM : ∀ x : M, n • x = 0) :
    Fact (IsSmoothDiscrete (ZMod n) (toGalRep K M hM)) :=
  ⟨isSmoothDiscrete_toGalRep K M hM⟩

/-- Continuous action of `Field.absoluteGaloisGroup K` on `toGalRep K M hM`. -/
private instance instContinuousSMulToGalRep (hM : ∀ x : M, n • x = 0) :
    ContinuousSMul (Field.absoluteGaloisGroup K) (toGalRep K M hM).V :=
  (isSmoothDiscrete_toGalRep K M hM).continuousSMul

/-- Underlying additive equivalence `M ≃+ (toGalRep K M hM).V`. -/
private def toGalRepAddEquiv (hM : ∀ x : M, n • x = 0) : M ≃+ (toGalRep K M hM).V :=
  AddEquiv.refl M

/-- Finiteness of `(toGalRep K M hM).V` when `M` is finite. -/
private instance instFiniteToGalRep [Finite M] (hM : ∀ x : M, n • x = 0) :
    Finite (toGalRep K M hM).V :=
  Finite.of_equiv M (toGalRepAddEquiv K M hM).toEquiv

omit [ContinuousSMul (AbsoluteGaloisGroup K) M] in
/-- Semilinearity of `toGalRepAddEquiv` along `absoluteGaloisGroupRestrictEquiv K`. -/
private theorem toGalRepAddEquiv_smul (hM : ∀ x : M, n • x = 0)
    (g : Field.absoluteGaloisGroup K) (x : M) :
    toGalRepAddEquiv K M hM (absoluteGaloisGroupRestrictEquiv K g • x) =
      g • toGalRepAddEquiv K M hM x := by
  let _ : Module (ZMod n) M := AddCommGroup.zmodModule hM
  have : ContinuousSMul (ZMod n) M := ⟨continuous_of_discreteTopology⟩
  exact (((ofDiscreteModule_ρ_apply_apply (R := ZMod n)
      (absoluteGaloisGroupRestrictEquiv K g) x).symm.trans
    (ContRepresentation.restrict_apply_apply
      (ofDiscreteModule (ZMod n) (AbsoluteGaloisGroup K) M).ρ
      (absoluteGaloisGroupRestrictEquiv K :
        Field.absoluteGaloisGroup K →* AbsoluteGaloisGroup K) g x).symm).trans
    (TopRep.distribMulAction_smul (toGalRep K M hM) g (toGalRepAddEquiv K M hM x)).symm)

/-- Equivalence between explicit `H¹(G_K, M)` and categorical `continuousCohomology 1`. -/
private def h1EquivToGalRep (hM : ∀ x : M, n • x = 0) :
    H1 (AbsoluteGaloisGroup K) M ≃+ continuousCohomology 1 (toGalRep K M hM) :=
  (explicitMap1Equiv (AbsoluteGaloisGroup K) M (Field.absoluteGaloisGroup K) (toGalRep K M hM).V
    (absoluteGaloisGroupRestrictEquiv K) (toGalRepAddEquiv K M hM)
    continuous_of_discreteTopology continuous_of_discreteTopology
    (toGalRepAddEquiv_smul K M hM)).trans
    (toGalRep K M hM).explicitH1AddEquivContinuousCohomologyOfDiscrete

end GalRepBridge

/-! ### Orthogonality and finiteness over a general nonarchimedean local field -/

section General

variable {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {n : ℕ}

/-- **Orthogonality of unramified cohomology under local Tate duality.** Over any nonarchimedean
local field `K` and for any `n ≠ 0`, unramified classes in `H¹(G_K, M)` and
`H¹(G_K, Hom(M, μₙ))` pair to zero under `dualityMap1`. No assumption that `n` is invertible in
`K` or its residue field is needed. -/
theorem dualityMap1_kummerCoeff_eq_zero_of_mem_unramifiedCohomology [NeZero n]
    {M : Type} [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
    [DistribMulAction (AbsoluteGaloisGroup K) M] [ContinuousSMul (AbsoluteGaloisGroup K) M]
    [Finite M]
    {x : H1 (AbsoluteGaloisGroup K) M} (hx : x ∈ unramifiedCohomology K M)
    {y : H1 (AbsoluteGaloisGroup K)
      (InternalHom (AbsoluteGaloisGroup K) M (KummerCoeff K n))}
    (hy : y ∈ unramifiedCohomology K
      (InternalHom (AbsoluteGaloisGroup K) M (KummerCoeff K n))) :
    dualityMap1 (AbsoluteGaloisGroup K) M (KummerCoeff K n) x y = 0 := by
  rw [dualityMap1_eq_neg_explicitDualityPairing11, explicitDualityPairing11_def,
    explicitCup11_eq_zero_of_mem_unramifiedCohomology _ _ _ hy hx, neg_zero]

/-- **Finiteness of explicit `H¹`** for a finite discrete `G_K`-module killed by an integer `n`
invertible in `K`. -/
theorem finite_H1_of_nsmul_eq_zero (hn : IsUnit (n : K))
    (M : Type) [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
    [DistribMulAction (AbsoluteGaloisGroup K) M] [ContinuousSMul (AbsoluteGaloisGroup K) M]
    [Finite M] (hM : ∀ x : M, n • x = 0) :
    Finite (H1 (AbsoluteGaloisGroup K) M) := by
  have : Finite (continuousCohomology 1 (toGalRep K M hM)) :=
    finite_H hn.ne_zero (toGalRep K M hM) Fact.out (by omega)
  exact Finite.of_equiv _ (h1EquivToGalRep K M hM).symm.toEquiv

end General

/-! ### Explicit local Euler characteristic and unramified exact annihilators -/

section Padic

variable (p : ℕ) [Fact p.Prime]
  {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [FinitePadicExtension K p]
  {n : ℕ}

/-- **Tate's local Euler characteristic formula on explicit cohomology.** For a finite discrete
`G_K`-module `M` over a finite extension `K` of `ℚ_p`, killed by `n ≠ 0`,
`#H¹(G_K, M) = #H⁰(G_K, M) · #H²(G_K, M) · p ^ ([K : ℚ_p] · v_p(#M))`. -/
theorem natCard_H1_eq_natCard_H0_mul_natCard_H2_mul_pow (hn : n ≠ 0)
    (M : Type) [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
    [DistribMulAction (AbsoluteGaloisGroup K) M] [ContinuousSMul (AbsoluteGaloisGroup K) M]
    [Finite M] (hM : ∀ x : M, n • x = 0) :
    Nat.card (H1 (AbsoluteGaloisGroup K) M) =
      Nat.card (H0 (AbsoluteGaloisGroup K) M) * Nat.card (H2 (AbsoluteGaloisGroup K) M) *
        p ^ (Module.finrank ℚ_[p] K * padicValNat p (Nat.card M)) := by
  let A := toGalRep K M hM
  have : DiscreteTopology A.V := inferInstanceAs (DiscreteTopology (toGalRep K M hM).V)
  let _ : DistribMulAction (Field.absoluteGaloisGroup K) A.V := TopRep.distribMulAction A
  have : ContinuousSMul (Field.absoluteGaloisGroup K) A.V :=
    inferInstanceAs (ContinuousSMul (Field.absoluteGaloisGroup K) (toGalRep K M hM).V)
  have h0 : Nat.card (H0 (AbsoluteGaloisGroup K) M) = Nat.card (continuousCohomology 0 A) :=
    (Nat.card_congr (Equiv.ofBijective _ (explicitMap0_bijective (AbsoluteGaloisGroup K) M
      (absoluteGaloisGroupRestrictEquiv K : Field.absoluteGaloisGroup K →* AbsoluteGaloisGroup K)
      (absoluteGaloisGroupRestrictEquiv K).surjective (toGalRepAddEquiv K M hM).toAddMonoidHom
      (toGalRepAddEquiv K M hM).bijective (toGalRepAddEquiv_smul K M hM)))).trans
      A.natCard_H0_eq_natCard_continuousCohomology
  have h1 : Nat.card (H1 (AbsoluteGaloisGroup K) M) = Nat.card (continuousCohomology 1 A) :=
    Nat.card_congr (h1EquivToGalRep K M hM).toEquiv
  have h2 : Nat.card (H2 (AbsoluteGaloisGroup K) M) = Nat.card (continuousCohomology 2 A) :=
    (Nat.card_congr (explicitMap2Equiv (AbsoluteGaloisGroup K) M (Field.absoluteGaloisGroup K) A.V
      (absoluteGaloisGroupRestrictEquiv K) (toGalRepAddEquiv K M hM)
      continuous_of_discreteTopology continuous_of_discreteTopology
      (toGalRepAddEquiv_smul K M hM)).toEquiv).trans A.natCard_H2_eq_natCard_continuousCohomology
  have hcard : Nat.card A.V = Nat.card M := Nat.card_congr (toGalRepAddEquiv K M hM).symm.toEquiv
  rw [h0, h1, h2, ← hcard]
  exact eulerCharacteristic_mixed p K n hn A inferInstance

/-- **Prime-to-`p` local Euler characteristic on explicit cohomology (by order).** If `p ∤ #M`,
then `#H¹(G_K, M) = #H⁰(G_K, M) · #H²(G_K, M)`. -/
theorem natCard_H1_eq_natCard_H0_mul_natCard_H2_of_not_dvd (hn : n ≠ 0)
    (M : Type) [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
    [DistribMulAction (AbsoluteGaloisGroup K) M] [ContinuousSMul (AbsoluteGaloisGroup K) M]
    [Finite M] (hM : ∀ x : M, n • x = 0) (hpM : ¬ p ∣ Nat.card M) :
    Nat.card (H1 (AbsoluteGaloisGroup K) M) =
      Nat.card (H0 (AbsoluteGaloisGroup K) M) * Nat.card (H2 (AbsoluteGaloisGroup K) M) := by
  rw [natCard_H1_eq_natCard_H0_mul_natCard_H2_mul_pow p hn M hM, Nat.padicValNat_def,
    multiplicity_eq_zero_of_not_dvd hpM, mul_zero, pow_zero, mul_one]

/-- **Prime-to-`p` local Euler characteristic on explicit cohomology (by exponent).** If `M` is
killed by `n` with `p ∤ n`, then `#H¹(G_K, M) = #H⁰(G_K, M) · #H²(G_K, M)`. -/
theorem natCard_H1_eq_natCard_H0_mul_natCard_H2_of_not_dvd_exponent (hpn : ¬ p ∣ n)
    (M : Type) [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
    [DistribMulAction (AbsoluteGaloisGroup K) M] [ContinuousSMul (AbsoluteGaloisGroup K) M]
    [Finite M] (hM : ∀ x : M, n • x = 0) :
    Nat.card (H1 (AbsoluteGaloisGroup K) M) =
      Nat.card (H0 (AbsoluteGaloisGroup K) M) * Nat.card (H2 (AbsoluteGaloisGroup K) M) := by
  have hn : n ≠ 0 := by rintro rfl; exact hpn (dvd_zero p)
  refine natCard_H1_eq_natCard_H0_mul_natCard_H2_of_not_dvd p hn M hM fun hpM ↦ ?_
  obtain ⟨x, hx⟩ := exists_prime_addOrderOf_dvd_card' p hpM
  exact hpn (hx ▸ addOrderOf_dvd_of_nsmul_eq_zero (hM x))

/-- **Order product of unramified `H¹` and its Kummer dual.** For a finite discrete `G_K`-module
`M` over a finite extension `K` of `ℚ_p`, killed by `n` with `p ∤ n`,
`#H¹_ur(G_K, M) · #H¹_ur(G_K, Hom(M, μₙ)) = #H¹(G_K, M)`. -/
theorem natCard_unramifiedCohomology_mul_internalHom_eq_natCard_H1 (hpn : ¬ p ∣ n)
    (M : Type) [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
    [DistribMulAction (AbsoluteGaloisGroup K) M] [ContinuousSMul (AbsoluteGaloisGroup K) M]
    [Finite M] (hM : ∀ x : M, n • x = 0) :
    Nat.card (unramifiedCohomology K M) *
        Nat.card (unramifiedCohomology K
          (InternalHom (AbsoluteGaloisGroup K) M (KummerCoeff K n))) =
      Nat.card (H1 (AbsoluteGaloisGroup K) M) := by
  have hn0 : n ≠ 0 := by rintro rfl; exact hpn (dvd_zero p)
  have : NeZero n := ⟨hn0⟩
  have := FinitePadicExtension.charZero K p
  have hn : IsUnit (n : K) := (Nat.cast_ne_zero.mpr hn0).isUnit
  rw [natCard_unramifiedCohomology_eq_natCard_H0, natCard_unramifiedCohomology_eq_natCard_H0,
    ← natCard_H2_eq_natCard_H0_internalHom hn M hM,
    natCard_H1_eq_natCard_H0_mul_natCard_H2_of_not_dvd_exponent p hpn M hM]

/-- **Unramified local Tate duality (Milne, *ADT* I, Theorem 2.6; NSW (7.2.15)).** Let `K` be a
finite extension of `ℚ_p` and `M` a finite discrete `G_K`-module killed by `n` with `p ∤ n`. Then
`H¹_ur(G_K, M)` is the exact left annihilator of `H¹_ur(G_K, Hom(M, μₙ))` under `dualityMap1`. -/
theorem unramifiedCohomology_eq_ker_compl₂_dualityMap1 (hpn : ¬ p ∣ n)
    (M : Type) [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
    [DistribMulAction (AbsoluteGaloisGroup K) M] [ContinuousSMul (AbsoluteGaloisGroup K) M]
    [Finite M] (hM : ∀ x : M, n • x = 0) :
    unramifiedCohomology K M =
      ((dualityMap1 (AbsoluteGaloisGroup K) M (KummerCoeff K n)).compl₂
        (unramifiedCohomology K
          (InternalHom (AbsoluteGaloisGroup K) M (KummerCoeff K n))).subtype).ker := by
  have hn0 : n ≠ 0 := by rintro rfl; exact hpn (dvd_zero p)
  have : NeZero n := ⟨hn0⟩
  have := FinitePadicExtension.charZero K p
  have hn : IsUnit (n : K) := (Nat.cast_ne_zero.mpr hn0).isUnit
  have hM' : ∀ φ : InternalHom (AbsoluteGaloisGroup K) M (KummerCoeff K n), n • φ = 0 :=
    InternalHom.nsmul_eq_zero_of_domain hM
  have : Finite (H1 (AbsoluteGaloisGroup K)
      (InternalHom (AbsoluteGaloisGroup K) M (KummerCoeff K n))) :=
    finite_H1_of_nsmul_eq_zero hn _ hM'
  rw [(dualityMap1 (AbsoluteGaloisGroup K) M (KummerCoeff K n)
    ).eq_ker_compl₂_subtype_iff_forall_eq_zero_and_natCard_mul_eq_of_addEquiv_zmod
      ((muNRepH2Equiv n K).trans (h2MuEquivZMod K hn))
      (dualityMap1_kummerCoeff_bijective hn M hM)
      (nsmul_H1_eq_zero (G := AbsoluteGaloisGroup K) hM')]
  exact ⟨fun _ hx _ hy ↦ dualityMap1_kummerCoeff_eq_zero_of_mem_unramifiedCohomology hx hy,
    natCard_unramifiedCohomology_mul_internalHom_eq_natCard_H1 p hpn M hM⟩

/-- **Dual form of unramified local Tate duality.** Over a finite extension `K` of `ℚ_p`, for a
finite discrete `G_K`-module `M` killed by `n` with `p ∤ n`, `H¹_ur(G_K, Hom(M, μₙ))` is the exact
right annihilator of `H¹_ur(G_K, M)` under `dualityMap1`. -/
theorem unramifiedCohomology_internalHom_eq_ker_flip_compl₂_dualityMap1 (hpn : ¬ p ∣ n)
    (M : Type) [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
    [DistribMulAction (AbsoluteGaloisGroup K) M] [ContinuousSMul (AbsoluteGaloisGroup K) M]
    [Finite M] (hM : ∀ x : M, n • x = 0) :
    unramifiedCohomology K (InternalHom (AbsoluteGaloisGroup K) M (KummerCoeff K n)) =
      ((dualityMap1 (AbsoluteGaloisGroup K) M (KummerCoeff K n)).flip.compl₂
        (unramifiedCohomology K M).subtype).ker := by
  have hn0 : n ≠ 0 := by rintro rfl; exact hpn (dvd_zero p)
  have : NeZero n := ⟨hn0⟩
  have := FinitePadicExtension.charZero K p
  have hn : IsUnit (n : K) := (Nat.cast_ne_zero.mpr hn0).isUnit
  have hM' : ∀ φ : InternalHom (AbsoluteGaloisGroup K) M (KummerCoeff K n), n • φ = 0 :=
    InternalHom.nsmul_eq_zero_of_domain hM
  have : Finite (H1 (AbsoluteGaloisGroup K)
      (InternalHom (AbsoluteGaloisGroup K) M (KummerCoeff K n))) :=
    finite_H1_of_nsmul_eq_zero hn _ hM'
  rw [unramifiedCohomology_eq_ker_compl₂_dualityMap1 p hpn M hM,
    (dualityMap1 (AbsoluteGaloisGroup K) M (KummerCoeff K n)
      ).ker_flip_compl₂_subtype_ker_compl₂_subtype_of_addEquiv_zmod
      ((muNRepH2Equiv n K).trans (h2MuEquivZMod K hn))
      (dualityMap1_kummerCoeff_bijective hn M hM)
      (nsmul_H1_eq_zero (G := AbsoluteGaloisGroup K) hM')]

/-- **Pointwise criterion for unramified classes in `H¹(G_K, M)`.** Over a finite extension `K` of
`ℚ_p`, for `M` finite discrete and killed by `n` with `p ∤ n`, a class in `H¹(G_K, M)` is
unramified if and only if it pairs to zero with every unramified class in `H¹(G_K, Hom(M, μₙ))`. -/
theorem mem_unramifiedCohomology_iff_forall_dualityMap1_eq_zero (hpn : ¬ p ∣ n)
    {M : Type} [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
    [DistribMulAction (AbsoluteGaloisGroup K) M] [ContinuousSMul (AbsoluteGaloisGroup K) M]
    [Finite M] (hM : ∀ x : M, n • x = 0) (x : H1 (AbsoluteGaloisGroup K) M) :
    x ∈ unramifiedCohomology K M ↔
      ∀ y ∈ unramifiedCohomology K (InternalHom (AbsoluteGaloisGroup K) M (KummerCoeff K n)),
        dualityMap1 (AbsoluteGaloisGroup K) M (KummerCoeff K n) x y = 0 := by
  conv_lhs => rw [unramifiedCohomology_eq_ker_compl₂_dualityMap1 p hpn M hM]
  simp only [AddMonoidHom.mem_ker, AddMonoidHom.ext_iff, AddMonoidHom.compl₂_apply,
    AddMonoidHom.zero_apply, Subtype.forall, AddSubgroup.subtype_apply]

/-- **Pointwise criterion for unramified classes in `H¹(G_K, Hom(M, μₙ))`.** Over a finite
extension `K` of `ℚ_p`, for `M` finite discrete and killed by `n` with `p ∤ n`, a class in
`H¹(G_K, Hom(M, μₙ))` is unramified if and only if every unramified class in `H¹(G_K, M)` pairs to
zero with it. -/
theorem mem_unramifiedCohomology_internalHom_iff_forall_dualityMap1_eq_zero (hpn : ¬ p ∣ n)
    {M : Type} [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
    [DistribMulAction (AbsoluteGaloisGroup K) M] [ContinuousSMul (AbsoluteGaloisGroup K) M]
    [Finite M] (hM : ∀ x : M, n • x = 0)
    (y : H1 (AbsoluteGaloisGroup K) (InternalHom (AbsoluteGaloisGroup K) M (KummerCoeff K n))) :
    y ∈ unramifiedCohomology K (InternalHom (AbsoluteGaloisGroup K) M (KummerCoeff K n)) ↔
      ∀ x ∈ unramifiedCohomology K M,
        dualityMap1 (AbsoluteGaloisGroup K) M (KummerCoeff K n) x y = 0 := by
  conv_lhs => rw [unramifiedCohomology_internalHom_eq_ker_flip_compl₂_dualityMap1 p hpn M hM]
  simp only [AddMonoidHom.mem_ker, AddMonoidHom.ext_iff, AddMonoidHom.compl₂_apply,
    AddMonoidHom.zero_apply, AddMonoidHom.flip_apply, Subtype.forall, AddSubgroup.subtype_apply]

end Padic

end TauCeti.ClassFieldTheory
