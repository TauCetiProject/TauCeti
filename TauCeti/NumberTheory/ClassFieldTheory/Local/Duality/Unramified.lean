/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ClassFieldTheory.Local.Duality.Cardinality
public import TauCeti.NumberTheory.LocalField.AbsoluteRamificationIndex
public import TauCeti.NumberTheory.LocalField.Unramified.Cohomology

import TauCeti.Algebra.Algebra.NatCast
import TauCeti.Algebra.Group.Subgroup.Ker
import TauCeti.Algebra.Module.ZMod.Annihilator
import TauCeti.Data.Nat.Cast.IsUnit
import TauCeti.NumberTheory.ClassFieldTheory.FiniteCohomology.Basic
import TauCeti.NumberTheory.ClassFieldTheory.Local.EulerCharacteristic.Theorem

/-!
# Unramified local Tate duality

Let `K` be a nonarchimedean local field, `M` a finite discrete `G_K`-module killed by `n`, and
`M' = Hom(M, μₙ)` its Kummer dual
(`TauCeti.InternalHom (AbsoluteGaloisGroup K) M (KummerCoeff K n)`). Over any nonarchimedean local
field and for any `n ≠ 0`, the unramified subgroups `unramifiedH1 K M` and `unramifiedH1 K M'` are
orthogonal under the degree-one cup-product map `TauCeti.ContCohomology.dualityMap1`: their cup
product inflates from `H²(G_K ⧸ I_K, μₙ^{I_K}) = 0`
(`TauCeti.ClassFieldTheory.dualityMap1_kummerCoeff_eq_zero_of_mem_unramifiedH1`). Full local Tate
duality (perfection of `dualityMap1`) holds whenever `n` is invertible in `K`, even if the residue
characteristic divides `n`; the prime-to-`p` hypothesis below is needed only for exact annihilation
of the unramified subgroups (when `char K ∣ n`, `dualityMap1` itself need not be nondegenerate).

When `K` is a finite extension of `ℚ_p` (`TauCeti.FinitePadicExtension K p`) and `p ∤ n`, Tate's
local Euler characteristic formula
(`TauCeti.ClassFieldTheory.natCard_H1_eq_natCard_H0_mul_natCard_H2_of_not_dvd_of_nsmul_eq_zero`)
gives `#H¹(G_K, M) = #H⁰(G_K, M) · #H²(G_K, M)`. Combining the procyclic unramified count
`#unramifiedH1 K X = #H⁰(G_K, X)` (`TauCeti.natCard_unramifiedH1_eq_natCard_H0`) for `M` and `M'`
with `#H²(G_K, M) = #H⁰(G_K, M')`
(`TauCeti.ClassFieldTheory.natCard_H2_eq_natCard_H0_internalHom`) yields

```text
#unramifiedH1 K M · #unramifiedH1 K M' = #H¹(G_K, M),
```

which upgrades orthogonality to **Milne's unramified local duality theorem**: `unramifiedH1 K M` and
`unramifiedH1 K M'` are exact mutual annihilators under local Tate duality.

## Main results

* `TauCeti.ClassFieldTheory.dualityMap1_kummerCoeff_eq_zero_of_mem_unramifiedH1`:
  unramified classes in `H¹(G_K, M)` and `H¹(G_K, Hom(M, μₙ))` pair to zero under `dualityMap1`
  over any nonarchimedean local field.
* `natCard_unramifiedH1_mul_natCard_unramifiedH1_internalHom_eq_natCard_H1`:
  `#unramifiedH1 K M · #unramifiedH1 K (Hom(M, μₙ)) = #H¹(G_K, M)` when `p ∤ n`.
* `TauCeti.ClassFieldTheory.unramifiedH1_eq_ker_compl₂_dualityMap1`,
  `unramifiedH1_internalHom_eq_ker_flip_compl₂_dualityMap1`,
  `mem_unramifiedH1_iff_forall_dualityMap1_eq_zero`, and
  `mem_unramifiedH1_internalHom_iff_forall_dualityMap1_eq_zero`: `unramifiedH1 K M` and
  `unramifiedH1 K (Hom(M, μₙ))` are exact mutual annihilators under `dualityMap1` when `p ∤ n`.
* `TauCeti.ClassFieldTheory.mem_unramifiedH1_iff_forall_pairing_eq_zero` and
  `TauCeti.ClassFieldTheory.mem_unramifiedH1_right_iff_forall_pairing_eq_zero`: over a finite
  extension `K` of `ℚ_p`, for a finite discrete `G_K`-module `M` killed by `n` with `p ∤ n`,
  transport of the left and right pointwise exact-annihilation criteria along an equivariant
  duality isomorphism `N ≃+[G_K] Hom(M, μₙ)` and an injective target homomorphism
  `H²(G_K, μₙ) →+ C`.

## References

* J. S. Milne, *Arithmetic Duality Theorems*, 2nd ed., Chapter I, Theorem 2.6.
* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., (7.2.15).
-/

public noncomputable section

namespace TauCeti.ClassFieldTheory

open ContCohomology

/-! ### Orthogonality over a general nonarchimedean local field -/

section General

variable {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {n : ℕ}

/-- **Cup-product orthogonality of unramified cohomology.** Over any nonarchimedean local field
`K` and for any `n ≠ 0`, unramified classes in `H¹(G_K, M)` and `H¹(G_K, Hom(M, μₙ))` pair to
zero under the cup-product map `dualityMap1`. No assumption that `n` is invertible in `K` or prime
to the residue characteristic is needed (full local Tate duality holds whenever `n` is invertible in
`K`, whereas exact annihilation of the unramified subgroups below additionally requires `p ∤ n`;
when `char K ∣ n`, `dualityMap1` itself need not be nondegenerate). -/
theorem dualityMap1_kummerCoeff_eq_zero_of_mem_unramifiedH1 [NeZero n]
    {M : Type} [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
    [DistribMulAction (AbsoluteGaloisGroup K) M] [ContinuousSMul (AbsoluteGaloisGroup K) M]
    [Finite M]
    {x : H1 (AbsoluteGaloisGroup K) M} (hx : x ∈ unramifiedH1 K M)
    {y : H1 (AbsoluteGaloisGroup K)
      (InternalHom (AbsoluteGaloisGroup K) M (KummerCoeff K n))}
    (hy : y ∈ unramifiedH1 K
      (InternalHom (AbsoluteGaloisGroup K) M (KummerCoeff K n))) :
    dualityMap1 (AbsoluteGaloisGroup K) M (KummerCoeff K n) x y = 0 := by
  rw [dualityMap1_eq_neg_explicitDualityPairing11, explicitDualityPairing11_def,
    AddMonoidHom.explicitCup11_eq_zero_of_mem_unramifiedH1 _ _ _ hy hx, neg_zero]

end General

/-! ### Unramified exact annihilators over finite extensions of `ℚ_p` -/

section Padic

variable (p : ℕ) [Fact p.Prime]
  {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [FinitePadicExtension K p]
  {n : ℕ}

/-- **Order product of unramified `H¹` and its Kummer dual.** For a finite discrete `G_K`-module
`M` over a finite extension `K` of `ℚ_p`, killed by `n` with `p ∤ n`,
`#H¹_ur(G_K, M) · #H¹_ur(G_K, Hom(M, μₙ)) = #H¹(G_K, M)`. -/
theorem natCard_unramifiedH1_mul_natCard_unramifiedH1_internalHom_eq_natCard_H1 (hpn : ¬ p ∣ n)
    (M : Type) [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
    [DistribMulAction (AbsoluteGaloisGroup K) M] [ContinuousSMul (AbsoluteGaloisGroup K) M]
    [Finite M] (hM : ∀ x : M, n • x = 0) :
    Nat.card (unramifiedH1 K M) *
        Nat.card (unramifiedH1 K
          (InternalHom (AbsoluteGaloisGroup K) M (KummerCoeff K n))) =
      Nat.card (H1 (AbsoluteGaloisGroup K) M) := by
  have := FinitePadicExtension.charZero K p
  have hn := TauCeti.isUnit_natCast_of_not_dvd_of_charZero (K := K) hpn
  have : NeZero n := hn.neZero_natCast
  rw [natCard_unramifiedH1_eq_natCard_H0, natCard_unramifiedH1_eq_natCard_H0,
    ← natCard_H2_eq_natCard_H0_internalHom hn M hM,
    natCard_H1_eq_natCard_H0_mul_natCard_H2_of_not_dvd_of_nsmul_eq_zero p hpn M hM]

/-- **Unramified local Tate duality (Milne, *ADT* I, Theorem 2.6; NSW (7.2.15)).** Let `K` be a
finite extension of `ℚ_p` and `M` a finite discrete `G_K`-module killed by `n` with `p ∤ n`. Then
`H¹_ur(G_K, M)` is the exact left annihilator of `H¹_ur(G_K, Hom(M, μₙ))` under `dualityMap1`. -/
theorem unramifiedH1_eq_ker_compl₂_dualityMap1 (hpn : ¬ p ∣ n)
    (M : Type) [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
    [DistribMulAction (AbsoluteGaloisGroup K) M] [ContinuousSMul (AbsoluteGaloisGroup K) M]
    [Finite M] (hM : ∀ x : M, n • x = 0) :
    unramifiedH1 K M =
      ((dualityMap1 (AbsoluteGaloisGroup K) M (KummerCoeff K n)).compl₂
        (unramifiedH1 K
          (InternalHom (AbsoluteGaloisGroup K) M (KummerCoeff K n))).subtype).ker := by
  have := FinitePadicExtension.charZero K p
  have hn := TauCeti.isUnit_natCast_of_not_dvd_of_charZero (K := K) hpn
  have : NeZero n := hn.neZero_natCast
  have : Finite (H1 (AbsoluteGaloisGroup K)
      (InternalHom (AbsoluteGaloisGroup K) M (KummerCoeff K n))) :=
    finite_H1_of_nsmul_eq_zero hn.ne_zero _ (InternalHom.nsmul_eq_zero_of_domain hM)
  rw [(dualityMap1 (AbsoluteGaloisGroup K) M (KummerCoeff K n)
    ).eq_ker_compl₂_subtype_iff_forall_eq_zero_and_natCard_mul_eq_of_addEquiv_zmod
      (explicitH2MuEquivZMod K hn)
      (dualityMap1_kummerCoeff_bijective hn M hM)
      (nsmul_H1_eq_zero (G := AbsoluteGaloisGroup K) (InternalHom.nsmul_eq_zero_of_domain hM))]
  exact ⟨fun _ hx _ hy ↦ dualityMap1_kummerCoeff_eq_zero_of_mem_unramifiedH1 hx hy,
    natCard_unramifiedH1_mul_natCard_unramifiedH1_internalHom_eq_natCard_H1 p hpn M hM⟩

/-- **Dual form of unramified local Tate duality.** Over a finite extension `K` of `ℚ_p`, for a
finite discrete `G_K`-module `M` killed by `n` with `p ∤ n`, `H¹_ur(G_K, Hom(M, μₙ))` is the exact
right annihilator of `H¹_ur(G_K, M)` under `dualityMap1`. -/
theorem unramifiedH1_internalHom_eq_ker_flip_compl₂_dualityMap1 (hpn : ¬ p ∣ n)
    (M : Type) [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
    [DistribMulAction (AbsoluteGaloisGroup K) M] [ContinuousSMul (AbsoluteGaloisGroup K) M]
    [Finite M] (hM : ∀ x : M, n • x = 0) :
    unramifiedH1 K (InternalHom (AbsoluteGaloisGroup K) M (KummerCoeff K n)) =
      ((dualityMap1 (AbsoluteGaloisGroup K) M (KummerCoeff K n)).flip.compl₂
        (unramifiedH1 K M).subtype).ker := by
  have := FinitePadicExtension.charZero K p
  have hn := TauCeti.isUnit_natCast_of_not_dvd_of_charZero (K := K) hpn
  have : NeZero n := hn.neZero_natCast
  have : Finite (H1 (AbsoluteGaloisGroup K)
      (InternalHom (AbsoluteGaloisGroup K) M (KummerCoeff K n))) :=
    finite_H1_of_nsmul_eq_zero hn.ne_zero _ (InternalHom.nsmul_eq_zero_of_domain hM)
  rw [unramifiedH1_eq_ker_compl₂_dualityMap1 p hpn M hM,
    (dualityMap1 (AbsoluteGaloisGroup K) M (KummerCoeff K n)
      ).ker_flip_compl₂_subtype_ker_compl₂_subtype_of_addEquiv_zmod
      (explicitH2MuEquivZMod K hn)
      (dualityMap1_kummerCoeff_bijective hn M hM)
      (nsmul_H1_eq_zero (G := AbsoluteGaloisGroup K) (InternalHom.nsmul_eq_zero_of_domain hM))]

/-- **Pointwise criterion for unramified classes in `H¹(G_K, M)`.** Over a finite extension `K` of
`ℚ_p`, for `M` finite discrete and killed by `n` with `p ∤ n`, a class in `H¹(G_K, M)` is
unramified if and only if it pairs to zero with every unramified class in `H¹(G_K, Hom(M, μₙ))`. -/
theorem mem_unramifiedH1_iff_forall_dualityMap1_eq_zero (hpn : ¬ p ∣ n)
    {M : Type} [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
    [DistribMulAction (AbsoluteGaloisGroup K) M] [ContinuousSMul (AbsoluteGaloisGroup K) M]
    [Finite M] (hM : ∀ x : M, n • x = 0) (x : H1 (AbsoluteGaloisGroup K) M) :
    x ∈ unramifiedH1 K M ↔
      ∀ y ∈ unramifiedH1 K (InternalHom (AbsoluteGaloisGroup K) M (KummerCoeff K n)),
        dualityMap1 (AbsoluteGaloisGroup K) M (KummerCoeff K n) x y = 0 := by
  conv_lhs => rw [unramifiedH1_eq_ker_compl₂_dualityMap1 p hpn M hM]
  exact AddMonoidHom.mem_ker_compl₂_subtype_iff _ _

/-- **Pointwise criterion for unramified classes in `H¹(G_K, Hom(M, μₙ))`.** Over a finite
extension `K` of `ℚ_p`, for `M` finite discrete and killed by `n` with `p ∤ n`, a class in
`H¹(G_K, Hom(M, μₙ))` is unramified if and only if every unramified class in `H¹(G_K, M)` pairs to
zero with it. -/
theorem mem_unramifiedH1_internalHom_iff_forall_dualityMap1_eq_zero (hpn : ¬ p ∣ n)
    {M : Type} [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
    [DistribMulAction (AbsoluteGaloisGroup K) M] [ContinuousSMul (AbsoluteGaloisGroup K) M]
    [Finite M] (hM : ∀ x : M, n • x = 0)
    (y : H1 (AbsoluteGaloisGroup K) (InternalHom (AbsoluteGaloisGroup K) M (KummerCoeff K n))) :
    y ∈ unramifiedH1 K (InternalHom (AbsoluteGaloisGroup K) M (KummerCoeff K n)) ↔
      ∀ x ∈ unramifiedH1 K M,
        dualityMap1 (AbsoluteGaloisGroup K) M (KummerCoeff K n) x y = 0 := by
  conv_lhs => rw [unramifiedH1_internalHom_eq_ker_flip_compl₂_dualityMap1 p hpn M hM]
  simp only [AddMonoidHom.mem_ker_compl₂_subtype_iff, AddMonoidHom.flip_apply]

/-- **Transported left-hand pointwise criterion for unramified cohomology.** Over a finite
extension `K` of `ℚ_p`, for a finite discrete `G_K`-module `M` killed by `n` with `p ∤ n`, given a
bijective `G_K`-equivariant duality map `d : N →+[G_K] Hom(M, μₙ)` and a pairing
`P : H¹(G_K, M) →+ H¹(G_K, N) →+ C` factoring through `dualityMap1` via an injective additive
homomorphism `iC : H²(G_K, μₙ) →+ C`, a class in `H¹(G_K, M)` is unramified if and only if it
pairs to zero with every unramified class in `H¹(G_K, N)`. -/
theorem mem_unramifiedH1_iff_forall_pairing_eq_zero (hpn : ¬ p ∣ n)
    {M N C : Type} [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
    [DistribMulAction (AbsoluteGaloisGroup K) M] [ContinuousSMul (AbsoluteGaloisGroup K) M]
    [Finite M] (hM : ∀ x : M, n • x = 0)
    [AddCommGroup N] [TopologicalSpace N] [DiscreteTopology N]
    [DistribMulAction (AbsoluteGaloisGroup K) N] [ContinuousSMul (AbsoluteGaloisGroup K) N]
    [AddCommGroup C]
    (d : N →+[AbsoluteGaloisGroup K] InternalHom (AbsoluteGaloisGroup K) M (KummerCoeff K n))
    (hd : Function.Bijective d)
    (iC : H2 (AbsoluteGaloisGroup K) (KummerCoeff K n) →+ C) (hiC : Function.Injective iC)
    (P : H1 (AbsoluteGaloisGroup K) M →+ H1 (AbsoluteGaloisGroup K) N →+ C)
    (hP : ∀ a b, P a b =
      iC (dualityMap1 (AbsoluteGaloisGroup K) M (KummerCoeff K n) a
        (explicitCoeff1 (AbsoluteGaloisGroup K) N d continuous_of_discreteTopology b)))
    (a : H1 (AbsoluteGaloisGroup K) M) :
    a ∈ unramifiedH1 K M ↔ ∀ b ∈ unramifiedH1 K N, P a b = 0 := by
  rw [mem_unramifiedH1_iff_forall_dualityMap1_eq_zero p hpn hM a,
    (explicitCoeff1_bijective (AbsoluteGaloisGroup K) N hd).surjective.forall]
  refine forall_congr' fun b ↦ ?_
  rw [d.explicitCoeff1_mem_unramifiedH1_iff hd, hP a b, map_eq_zero_iff iC hiC]

/-- **Transported right-hand pointwise criterion for unramified cohomology.** Over a finite
extension `K` of `ℚ_p`, for a finite discrete `G_K`-module `M` killed by `n` with `p ∤ n`, under
the same duality dictionary `d` and injective target homomorphism `iC`, a class in `H¹(G_K, N)` is
unramified if and only if every unramified class in `H¹(G_K, M)` pairs to zero with it. -/
theorem mem_unramifiedH1_right_iff_forall_pairing_eq_zero (hpn : ¬ p ∣ n)
    {M N C : Type} [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
    [DistribMulAction (AbsoluteGaloisGroup K) M] [ContinuousSMul (AbsoluteGaloisGroup K) M]
    [Finite M] (hM : ∀ x : M, n • x = 0)
    [AddCommGroup N] [TopologicalSpace N] [DiscreteTopology N]
    [DistribMulAction (AbsoluteGaloisGroup K) N] [ContinuousSMul (AbsoluteGaloisGroup K) N]
    [AddCommGroup C]
    (d : N →+[AbsoluteGaloisGroup K] InternalHom (AbsoluteGaloisGroup K) M (KummerCoeff K n))
    (hd : Function.Bijective d)
    (iC : H2 (AbsoluteGaloisGroup K) (KummerCoeff K n) →+ C) (hiC : Function.Injective iC)
    (P : H1 (AbsoluteGaloisGroup K) M →+ H1 (AbsoluteGaloisGroup K) N →+ C)
    (hP : ∀ a b, P a b =
      iC (dualityMap1 (AbsoluteGaloisGroup K) M (KummerCoeff K n) a
        (explicitCoeff1 (AbsoluteGaloisGroup K) N d continuous_of_discreteTopology b)))
    (b : H1 (AbsoluteGaloisGroup K) N) :
    b ∈ unramifiedH1 K N ↔ ∀ a ∈ unramifiedH1 K M, P a b = 0 := by
  rw [← d.explicitCoeff1_mem_unramifiedH1_iff hd (c := b),
    mem_unramifiedH1_internalHom_iff_forall_dualityMap1_eq_zero p hpn hM _]
  refine forall₂_congr fun a _ ↦ ?_
  rw [hP a b, map_eq_zero_iff iC hiC]

end Padic

end TauCeti.ClassFieldTheory
