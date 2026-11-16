/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Torsion
public import TauCeti.NumberTheory.LocalField.Unramified.Inertia.SeparableClosure
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Cup.Product
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Inflation.Basic
import TauCeti.RepresentationTheory.Homological.ContCohomology.Cup.Inflation
import TauCeti.Topology.Algebra.Group.Profinite.ZHat.Coinvariants
import TauCeti.Topology.Algebra.Group.Profinite.ZHat.Extension

/-!
# Unramified Galois cohomology over a nonarchimedean local field

Let `K` be a nonarchimedean local field, `G_K = AbsoluteGaloisGroup K` the Galois group of its
separable closure `Kˢ`, and `I_K` the image of `TauCeti.inertiaSubgroup K` in `G_K` under
`TauCeti.absoluteGaloisGroupRestrictEquiv K`. For a topological `G_K`-module `M`, the subgroup of
**unramified degree-one Galois cohomology classes**

```text
unramifiedH1 K M ≤ H¹(G_K, M)
```

is the kernel of restriction to `I_K`. This file develops the local cohomological properties of
`unramifiedH1 K M` that supply the local input for Tate orthogonality of unramified subgroups and
the identification and finiteness of Selmer local conditions at good places.

Inflation-restriction (`TauCeti.ContCohomology.explicitInfRes_exact` and
`TauCeti.ContCohomology.explicitInfl1_injective`) identifies `H¹(G_K ⧸ I_K, M^{I_K})` with
`unramifiedH1 K M` (`TauCeti.quotientH1AddEquivUnramifiedH1`) whenever the quotient action on
`M^{I_K}` is continuous — in particular for every discrete `G_K`-module `M`. Transporting along the
topological group isomorphism `G_K ⧸ I_K ≃ₜ* zHat` (`TauCeti.quotientMapInertiaSubgroupEquivZHat`),
which carries `TauCeti.unramifiedQuotientFrobenius K` to `zHat.gen`, the coinvariant computation
for `zHat` (`TauCeti.zHat.h1AddEquivCoinvariants`) gives

```text
unramifiedH1 K M ≃+ M^{I_K} ⧸ (Frob_K - 1) M^{I_K}
```

whenever `M` is discrete and `M^{I_K}` is torsion (`TauCeti.unramifiedH1AddEquivCoinvariants`).

When `M` is discrete and `M^{I_K}` is finite (in particular for every finite discrete `G_K`-module
`M`, with no unramifiedness or residue-characteristic assumption on `M`), transporting the `zHat`
order identity `TauCeti.zHat.natCard_H1_eq_natCard_H0` yields the **Frobenius order formula**
(`TauCeti.natCard_unramifiedH1_eq_natCard_H0`):

```text
#unramifiedH1 K M = #H⁰(G_K, M).
```

Finally, since `H²(zHat, N)` vanishes for every profinite `zHat`-module `N`
(`TauCeti.zHat.subsingleton_H2_additive`), `H²(G_K ⧸ I_K, N)` vanishes as well
(`TauCeti.subsingleton_H2_quotient_inertiaSubgroup`). Because inflation commutes with explicit
`(1, 1)` cup products (`TauCeti.ContCohomology.explicitInfl2_explicitCup11`), **the cup product of
any two unramified degree-one classes vanishes in `H²(G_K, P)`** along any continuous
`G_K`-equivariant biadditive pairing `A × B → P` whenever `G_K ⧸ I_K` acts continuously on the
inertia-fixed subgroups and `H²(G_K ⧸ I_K, P^{I_K})` vanishes — in particular when `A`, `B`, `P`
are discrete and `P^{I_K}` is finite (`AddMonoidHom.explicitCup11_eq_zero_of_mem_unramifiedH1`).

## Main definitions

* `TauCeti.frobeniusSubId`: the endomorphism `m ↦ unramifiedQuotientFrobenius K • m - m` of
  `M^{I_K}`.
* `TauCeti.unramifiedH1`: the subgroup `ker(H¹(G_K, M) → H¹(I_K, M))` of unramified classes.
* `TauCeti.quotientH1AddEquivUnramifiedH1`: inflation as
  `H¹(G_K ⧸ I_K, M^{I_K}) ≃+ unramifiedH1 K M`.
* `TauCeti.unramifiedH1AddEquivCoinvariants`: the isomorphism
  `unramifiedH1 K M ≃+ M^{I_K} ⧸ (Frob_K - 1) M^{I_K}` for discrete `M` with torsion `M^{I_K}`.

## Main results

* `DistribMulActionHom.explicitCoeff1_mem_unramifiedH1`, `AlgHom.explicitMap1_mem_unramifiedH1`:
  functoriality of `unramifiedH1` in the coefficient module and along valuative extensions of local
  fields.
* `TauCeti.ker_frobeniusSubId_eq_fixedPoints`, `TauCeti.natCard_unramifiedH1_eq_natCard_H0`:
  `ker(Frob_K - 1 | M^{I_K}) = (M^{I_K})^{G_K ⧸ I_K}`, and `#unramifiedH1 K M = #H⁰(G_K, M)` for
  discrete `M` with finite `M^{I_K}`.
* `TauCeti.subsingleton_H2_quotient_inertiaSubgroup`: `H²(G_K ⧸ I_K, N) = 0` for profinite `N`.
* `AddMonoidHom.explicitCup11_eq_zero_of_mem_unramifiedH1`: two unramified classes cup to `0` in
  `H²(G_K, P)` whenever `H²(G_K ⧸ I_K, P^{I_K}) = 0` (in particular for discrete `A`, `B`, `P` with
  finite `P^{I_K}`).

## References

* J. S. Milne, *Arithmetic Duality Theorems*, 2nd ed., Chapter I, Lemma 2.7 and Theorem 2.6.
* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., Proposition 7.2.14.
* K. Rubin, *Euler Systems*, Annals of Mathematics Studies 147, Lemma I.3.2(i).
-/

public noncomputable section

namespace TauCeti

open ContCohomology _root_.ValuativeRel

universe u v w

section FrobeniusSubId

variable (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

/-- **The Frobenius-minus-identity endomorphism `Frob_K - 1`** on the inertia invariants `M^{I_K}`
of an `AbsoluteGaloisGroup K`-module `M`. -/
def frobeniusSubId (M : Type v) [AddCommGroup M] [DistribMulAction (AbsoluteGaloisGroup K) M] :
    FixedPoints.addSubgroup
        ((inertiaSubgroup K).map
          ((absoluteGaloisGroupRestrictEquiv K :
              Field.absoluteGaloisGroup K ≃* AbsoluteGaloisGroup K) :
            Field.absoluteGaloisGroup K →* AbsoluteGaloisGroup K)) M →+
      FixedPoints.addSubgroup
        ((inertiaSubgroup K).map
          ((absoluteGaloisGroupRestrictEquiv K :
              Field.absoluteGaloisGroup K ≃* AbsoluteGaloisGroup K) :
            Field.absoluteGaloisGroup K →* AbsoluteGaloisGroup K)) M where
  toFun m := unramifiedQuotientFrobenius K • m - m
  map_zero' := by rw [smul_zero, sub_self]
  map_add' a b := by
    rw [smul_add]
    abel

/-- `frobeniusSubId K M` sends `m ∈ M^{I_K}` to `unramifiedQuotientFrobenius K • m - m`. -/
@[simp]
theorem frobeniusSubId_apply {M : Type v} [AddCommGroup M]
    [DistribMulAction (AbsoluteGaloisGroup K) M]
    (m : FixedPoints.addSubgroup
      ((inertiaSubgroup K).map
        ((absoluteGaloisGroupRestrictEquiv K :
            Field.absoluteGaloisGroup K ≃* AbsoluteGaloisGroup K) :
          Field.absoluteGaloisGroup K →* AbsoluteGaloisGroup K)) M) :
    frobeniusSubId K M m = unramifiedQuotientFrobenius K • m - m :=
  (rfl)

/-- Under the `zHat`-action transported along `(quotientMapInertiaSubgroupEquivZHat K).symm`,
scalar multiplication by `z : zHat` is scalar multiplication by
`(quotientMapInertiaSubgroupEquivZHat K).symm z`. -/
private theorem compHom_symm_smul {N : Type v} [AddCommGroup N]
    [DistribMulAction
      (AbsoluteGaloisGroup K ⧸
        (inertiaSubgroup K).map
          ((absoluteGaloisGroupRestrictEquiv K :
              Field.absoluteGaloisGroup K ≃* AbsoluteGaloisGroup K) :
            Field.absoluteGaloisGroup K →* AbsoluteGaloisGroup K)) N]
    (z : zHat.{u}) (m : N) :
    letI : DistribMulAction zHat.{u} N :=
      DistribMulAction.compHom N (quotientMapInertiaSubgroupEquivZHat K).symm.toMonoidHom
    z • m = (quotientMapInertiaSubgroupEquivZHat K).symm z • m := by
  let _ : DistribMulAction zHat.{u} N :=
    DistribMulAction.compHom N (quotientMapInertiaSubgroupEquivZHat K).symm.toMonoidHom
  rw [MulAction.compHom_smul_def, MulEquiv.coe_toMonoidHom]
  rfl

/-- Under the `zHat`-action transported along `(quotientMapInertiaSubgroupEquivZHat K).symm`,
`zHat.genSubId` on `M^{I_K}` coincides with `frobeniusSubId K M`. -/
private theorem genSubId_eq_frobeniusSubId (M : Type v) [AddCommGroup M]
    [DistribMulAction (AbsoluteGaloisGroup K) M] :
    letI : DistribMulAction zHat.{u}
        (FixedPoints.addSubgroup
          ((inertiaSubgroup K).map
            ((absoluteGaloisGroupRestrictEquiv K :
                Field.absoluteGaloisGroup K ≃* AbsoluteGaloisGroup K) :
              Field.absoluteGaloisGroup K →* AbsoluteGaloisGroup K)) M) :=
      DistribMulAction.compHom _ (quotientMapInertiaSubgroupEquivZHat K).symm.toMonoidHom
    zHat.genSubId.{u}
        (FixedPoints.addSubgroup
          ((inertiaSubgroup K).map
            ((absoluteGaloisGroupRestrictEquiv K :
                Field.absoluteGaloisGroup K ≃* AbsoluteGaloisGroup K) :
              Field.absoluteGaloisGroup K →* AbsoluteGaloisGroup K)) M) =
      frobeniusSubId K M := by
  let _ : DistribMulAction zHat.{u}
      (FixedPoints.addSubgroup
        ((inertiaSubgroup K).map
          ((absoluteGaloisGroupRestrictEquiv K :
              Field.absoluteGaloisGroup K ≃* AbsoluteGaloisGroup K) :
            Field.absoluteGaloisGroup K →* AbsoluteGaloisGroup K)) M) :=
    DistribMulAction.compHom _ (quotientMapInertiaSubgroupEquivZHat K).symm.toMonoidHom
  refine AddMonoidHom.ext fun m ↦ ?_
  rw [zHat.genSubId_apply, frobeniusSubId_apply, compHom_symm_smul,
    quotientMapInertiaSubgroupEquivZHat_symm_gen]

/-- **An inertia-invariant element of a `T₁` `G_K`-module fixed by `unramifiedQuotientFrobenius K`
is fixed by the entire unramified quotient `G_K ⧸ I_K`** (whenever the quotient action on `M^{I_K}`
is continuous, for instance when `M` is discrete). -/
theorem ker_frobeniusSubId_eq_fixedPoints (M : Type v) [AddCommGroup M] [TopologicalSpace M]
    [T1Space M] [DistribMulAction (AbsoluteGaloisGroup K) M]
    [ContinuousSMul
      (AbsoluteGaloisGroup K ⧸
        (inertiaSubgroup K).map
          ((absoluteGaloisGroupRestrictEquiv K :
              Field.absoluteGaloisGroup K ≃* AbsoluteGaloisGroup K) :
            Field.absoluteGaloisGroup K →* AbsoluteGaloisGroup K))
      (FixedPoints.addSubgroup
        ((inertiaSubgroup K).map
          ((absoluteGaloisGroupRestrictEquiv K :
              Field.absoluteGaloisGroup K ≃* AbsoluteGaloisGroup K) :
            Field.absoluteGaloisGroup K →* AbsoluteGaloisGroup K)) M)] :
    (frobeniusSubId K M).ker =
      FixedPoints.addSubgroup
        (AbsoluteGaloisGroup K ⧸
          (inertiaSubgroup K).map
            ((absoluteGaloisGroupRestrictEquiv K :
                Field.absoluteGaloisGroup K ≃* AbsoluteGaloisGroup K) :
              Field.absoluteGaloisGroup K →* AbsoluteGaloisGroup K))
        (FixedPoints.addSubgroup
          ((inertiaSubgroup K).map
            ((absoluteGaloisGroupRestrictEquiv K :
                Field.absoluteGaloisGroup K ≃* AbsoluteGaloisGroup K) :
              Field.absoluteGaloisGroup K →* AbsoluteGaloisGroup K)) M) := by
  let I := (inertiaSubgroup K).map
    ((absoluteGaloisGroupRestrictEquiv K :
        Field.absoluteGaloisGroup K ≃* AbsoluteGaloisGroup K) :
      Field.absoluteGaloisGroup K →* AbsoluteGaloisGroup K)
  let N := FixedPoints.addSubgroup I M
  let e := quotientMapInertiaSubgroupEquivZHat K
  let _ : DistribMulAction zHat.{u} N := DistribMulAction.compHom N e.symm.toMonoidHom
  have _ : ContinuousSMul zHat.{u} N := MulAction.continuousSMul_compHom e.symm.continuous
  rw [← genSubId_eq_frobeniusSubId K M, zHat.ker_genSubId_eq_fixedPoints]
  ext x
  rw [FixedPoints.mem_addSubgroup, FixedPoints.mem_addSubgroup]
  simp_rw [compHom_symm_smul K]
  exact ⟨fun h q ↦ by rw [← e.symm_apply_apply q]; exact h (e q), fun h z ↦ h (e.symm z)⟩

end FrobeniusSubId

section UnramifiedH1

variable (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  (M : Type v) [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]
  [DistribMulAction (AbsoluteGaloisGroup K) M] [ContinuousSMul (AbsoluteGaloisGroup K) M]

/-- **Unramified first Galois cohomology `H¹_ur(K, M)`**: the subgroup of `H¹(G_K, M)` consisting of
classes whose restriction to the inertia subgroup `I_K` vanishes. -/
def unramifiedH1 : AddSubgroup (H1 (AbsoluteGaloisGroup K) M) :=
  (explicitRes1 (AbsoluteGaloisGroup K) M
    ((inertiaSubgroup K).map
      ((absoluteGaloisGroupRestrictEquiv K :
          Field.absoluteGaloisGroup K ≃* AbsoluteGaloisGroup K) :
        Field.absoluteGaloisGroup K →* AbsoluteGaloisGroup K))).ker

/-- `unramifiedH1 K M` is the kernel of restriction to inertia in `AbsoluteGaloisGroup K`. -/
theorem unramifiedH1_def :
    unramifiedH1 K M =
      (explicitRes1 (AbsoluteGaloisGroup K) M
        ((inertiaSubgroup K).map
          ((absoluteGaloisGroupRestrictEquiv K :
              Field.absoluteGaloisGroup K ≃* AbsoluteGaloisGroup K) :
            Field.absoluteGaloisGroup K →* AbsoluteGaloisGroup K))).ker :=
  (rfl)

variable {K M}

/-- A class in `H¹(G_K, M)` is unramified if and only if its restriction to inertia vanishes. -/
@[simp]
theorem mem_unramifiedH1_iff {c : H1 (AbsoluteGaloisGroup K) M} :
    c ∈ unramifiedH1 K M ↔
      explicitRes1 (AbsoluteGaloisGroup K) M
        ((inertiaSubgroup K).map
          ((absoluteGaloisGroupRestrictEquiv K :
              Field.absoluteGaloisGroup K ≃* AbsoluteGaloisGroup K) :
            Field.absoluteGaloisGroup K →* AbsoluteGaloisGroup K)) c = 0 :=
  (Iff.rfl)

/-- **Functoriality of `unramifiedH1` in the coefficient module.** A continuous `G_K`-equivariant
homomorphism `f : M →+[G_K] N` carries unramified classes in `H¹(G_K, M)` to unramified classes in
`H¹(G_K, N)`. -/
theorem _root_.DistribMulActionHom.explicitCoeff1_mem_unramifiedH1 {N : Type w} [AddCommGroup N]
    [TopologicalSpace N] [IsTopologicalAddGroup N] [DistribMulAction (AbsoluteGaloisGroup K) N]
    [ContinuousSMul (AbsoluteGaloisGroup K) N]
    (f : M →+[AbsoluteGaloisGroup K] N) (hf : Continuous f)
    {c : H1 (AbsoluteGaloisGroup K) M} (hc : c ∈ unramifiedH1 K M) :
    explicitCoeff1 (AbsoluteGaloisGroup K) M f hf c ∈ unramifiedH1 K N := by
  rw [mem_unramifiedH1_iff, explicitCoeff1_eq_explicitMap1]
  exact (ContinuousMonoidHom.id _).explicitRes1_explicitMap1_eq_zero_of_map_le _ _ _
    (by rintro _ ⟨g, hg, rfl⟩; exact hg) (mem_unramifiedH1_iff.mp hc)

/-- **Functoriality of `unramifiedH1` along an extension of local fields.** For a valuative
extension `L/K` of nonarchimedean local fields, a `K`-embedding `τ : Kˢ →ₐ[K] Lˢ` of separable
closures, and a continuous homomorphism `f : M →+ N` equivariant along `absoluteGaloisGroupMap τ`,
pullback `H¹(G_K, M) → H¹(G_L, N)` carries unramified classes to unramified classes. -/
theorem _root_.AlgHom.explicitMap1_mem_unramifiedH1 {L : Type*} [Field L] [ValuativeRel L]
    [TopologicalSpace L] [IsNonarchimedeanLocalField L] [Algebra K L] [ValuativeExtension K L]
    {N : Type w} [AddCommGroup N] [TopologicalSpace N] [IsTopologicalAddGroup N]
    [DistribMulAction (AbsoluteGaloisGroup L) N] [ContinuousSMul (AbsoluteGaloisGroup L) N]
    (τ : SeparableClosure K →ₐ[K] SeparableClosure L) (f : M →+ N) (hf : Continuous f)
    (hequiv : ∀ (g : AbsoluteGaloisGroup L) (m : M), f (absoluteGaloisGroupMap τ g • m) = g • f m)
    {c : H1 (AbsoluteGaloisGroup K) M} (hc : c ∈ unramifiedH1 K M) :
    explicitMap1 (AbsoluteGaloisGroup K) M (AbsoluteGaloisGroup L) N
      (absoluteGaloisGroupMap τ) f hf hequiv c ∈ unramifiedH1 L N := by
  rw [mem_unramifiedH1_iff]
  exact (absoluteGaloisGroupMap τ).explicitRes1_explicitMap1_eq_zero_of_map_le f hf hequiv
    τ.map_absoluteGaloisGroupMap_inertiaSubgroup_le hc

section Inflation

variable (K M)
  [ContinuousSMul
    (AbsoluteGaloisGroup K ⧸
      (inertiaSubgroup K).map
        ((absoluteGaloisGroupRestrictEquiv K :
            Field.absoluteGaloisGroup K ≃* AbsoluteGaloisGroup K) :
          Field.absoluteGaloisGroup K →* AbsoluteGaloisGroup K))
    (FixedPoints.addSubgroup
      ((inertiaSubgroup K).map
        ((absoluteGaloisGroupRestrictEquiv K :
            Field.absoluteGaloisGroup K ≃* AbsoluteGaloisGroup K) :
          Field.absoluteGaloisGroup K →* AbsoluteGaloisGroup K)) M)]

/-- **The unramified subgroup of `H¹(G_K, M)` is the image of inflation from `G_K ⧸ I_K`.** -/
theorem range_explicitInfl1_eq_unramifiedH1 :
    (explicitInfl1 (AbsoluteGaloisGroup K) M
      ((inertiaSubgroup K).map
        ((absoluteGaloisGroupRestrictEquiv K :
            Field.absoluteGaloisGroup K ≃* AbsoluteGaloisGroup K) :
          Field.absoluteGaloisGroup K →* AbsoluteGaloisGroup K))).range =
      unramifiedH1 K M :=
  explicitInfRes_exact (AbsoluteGaloisGroup K) M _

variable {K M} in
/-- Every class inflated from `H¹(G_K ⧸ I_K, M^{I_K})` is unramified. -/
theorem explicitInfl1_mem_unramifiedH1
    (x : H1 (AbsoluteGaloisGroup K ⧸
        (inertiaSubgroup K).map
          ((absoluteGaloisGroupRestrictEquiv K :
              Field.absoluteGaloisGroup K ≃* AbsoluteGaloisGroup K) :
            Field.absoluteGaloisGroup K →* AbsoluteGaloisGroup K))
      (FixedPoints.addSubgroup
        ((inertiaSubgroup K).map
          ((absoluteGaloisGroupRestrictEquiv K :
              Field.absoluteGaloisGroup K ≃* AbsoluteGaloisGroup K) :
            Field.absoluteGaloisGroup K →* AbsoluteGaloisGroup K)) M)) :
    explicitInfl1 (AbsoluteGaloisGroup K) M
      ((inertiaSubgroup K).map
        ((absoluteGaloisGroupRestrictEquiv K :
            Field.absoluteGaloisGroup K ≃* AbsoluteGaloisGroup K) :
          Field.absoluteGaloisGroup K →* AbsoluteGaloisGroup K)) x ∈
      unramifiedH1 K M := by
  rw [← range_explicitInfl1_eq_unramifiedH1]
  exact ⟨x, rfl⟩

private theorem bijective_codRestrict_explicitInfl1 :
    Function.Bijective
      ((explicitInfl1 (AbsoluteGaloisGroup K) M
        ((inertiaSubgroup K).map
          ((absoluteGaloisGroupRestrictEquiv K :
              Field.absoluteGaloisGroup K ≃* AbsoluteGaloisGroup K) :
            Field.absoluteGaloisGroup K →* AbsoluteGaloisGroup K))).codRestrict
          (unramifiedH1 K M) explicitInfl1_mem_unramifiedH1) := by
  let I := (inertiaSubgroup K).map
    ((absoluteGaloisGroupRestrictEquiv K :
        Field.absoluteGaloisGroup K ≃* AbsoluteGaloisGroup K) :
      Field.absoluteGaloisGroup K →* AbsoluteGaloisGroup K)
  refine ⟨fun a b h ↦ explicitInfl1_injective (AbsoluteGaloisGroup K) M I (congrArg Subtype.val h),
    fun y ↦ ?_⟩
  have hy : y.1 ∈ (explicitInfl1 (AbsoluteGaloisGroup K) M I).range := by
    rw [range_explicitInfl1_eq_unramifiedH1]
    exact y.2
  obtain ⟨x, hx⟩ := hy
  exact ⟨x, Subtype.ext hx⟩

/-- **Inflation identifies `H¹(G_K ⧸ I_K, M^{I_K})` with `unramifiedH1 K M`.** -/
def quotientH1AddEquivUnramifiedH1 :
    H1 (AbsoluteGaloisGroup K ⧸
        (inertiaSubgroup K).map
          ((absoluteGaloisGroupRestrictEquiv K :
              Field.absoluteGaloisGroup K ≃* AbsoluteGaloisGroup K) :
            Field.absoluteGaloisGroup K →* AbsoluteGaloisGroup K))
      (FixedPoints.addSubgroup
        ((inertiaSubgroup K).map
          ((absoluteGaloisGroupRestrictEquiv K :
              Field.absoluteGaloisGroup K ≃* AbsoluteGaloisGroup K) :
            Field.absoluteGaloisGroup K →* AbsoluteGaloisGroup K)) M) ≃+
      unramifiedH1 K M :=
  AddEquiv.ofBijective
    ((explicitInfl1 (AbsoluteGaloisGroup K) M
      ((inertiaSubgroup K).map
        ((absoluteGaloisGroupRestrictEquiv K :
            Field.absoluteGaloisGroup K ≃* AbsoluteGaloisGroup K) :
          Field.absoluteGaloisGroup K →* AbsoluteGaloisGroup K))).codRestrict
        (unramifiedH1 K M) explicitInfl1_mem_unramifiedH1)
    (bijective_codRestrict_explicitInfl1 K M)

/-- `quotientH1AddEquivUnramifiedH1` acts as `explicitInfl1` into `H¹(G_K, M)`. -/
@[simp]
theorem coe_quotientH1AddEquivUnramifiedH1_apply
    (x : H1 (AbsoluteGaloisGroup K ⧸
        (inertiaSubgroup K).map
          ((absoluteGaloisGroupRestrictEquiv K :
              Field.absoluteGaloisGroup K ≃* AbsoluteGaloisGroup K) :
            Field.absoluteGaloisGroup K →* AbsoluteGaloisGroup K))
      (FixedPoints.addSubgroup
        ((inertiaSubgroup K).map
          ((absoluteGaloisGroupRestrictEquiv K :
              Field.absoluteGaloisGroup K ≃* AbsoluteGaloisGroup K) :
            Field.absoluteGaloisGroup K →* AbsoluteGaloisGroup K)) M)) :
    (quotientH1AddEquivUnramifiedH1 K M x : H1 (AbsoluteGaloisGroup K) M) =
      explicitInfl1 (AbsoluteGaloisGroup K) M
        ((inertiaSubgroup K).map
          ((absoluteGaloisGroupRestrictEquiv K :
              Field.absoluteGaloisGroup K ≃* AbsoluteGaloisGroup K) :
            Field.absoluteGaloisGroup K →* AbsoluteGaloisGroup K)) x :=
  (rfl)

/-- Inflating the preimage of an unramified class under `quotientH1AddEquivUnramifiedH1` recovers
the underlying class in `H¹(G_K, M)`. -/
@[simp]
theorem explicitInfl1_quotientH1AddEquivUnramifiedH1_symm (c : unramifiedH1 K M) :
    explicitInfl1 (AbsoluteGaloisGroup K) M
        ((inertiaSubgroup K).map
          ((absoluteGaloisGroupRestrictEquiv K :
              Field.absoluteGaloisGroup K ≃* AbsoluteGaloisGroup K) :
            Field.absoluteGaloisGroup K →* AbsoluteGaloisGroup K))
        ((quotientH1AddEquivUnramifiedH1 K M).symm c) =
      (c : H1 (AbsoluteGaloisGroup K) M) := by
  rw [← coe_quotientH1AddEquivUnramifiedH1_apply, AddEquiv.apply_symm_apply]

end Inflation

end UnramifiedH1

section CoinvariantsAndCardinality

variable (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  (M : Type v) [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
  [DistribMulAction (AbsoluteGaloisGroup K) M] [ContinuousSMul (AbsoluteGaloisGroup K) M]

private local instance : DistribMulAction zHat.{u}
    (FixedPoints.addSubgroup
      ((inertiaSubgroup K).map
        ((absoluteGaloisGroupRestrictEquiv K :
            Field.absoluteGaloisGroup K ≃* AbsoluteGaloisGroup K) :
          Field.absoluteGaloisGroup K →* AbsoluteGaloisGroup K)) M) :=
  DistribMulAction.compHom _ (quotientMapInertiaSubgroupEquivZHat K).symm.toMonoidHom

private local instance : ContinuousSMul zHat.{u}
    (FixedPoints.addSubgroup
      ((inertiaSubgroup K).map
        ((absoluteGaloisGroupRestrictEquiv K :
            Field.absoluteGaloisGroup K ≃* AbsoluteGaloisGroup K) :
          Field.absoluteGaloisGroup K →* AbsoluteGaloisGroup K)) M) :=
  MulAction.continuousSMul_compHom (quotientMapInertiaSubgroupEquivZHat K).symm.continuous

/-- Transporting `H¹(G_K ⧸ I_K, M^{I_K})` to `H¹(zHat, M^{I_K})` along
`(quotientMapInertiaSubgroupEquivZHat K).symm`. -/
private def quotientH1AddEquivZHatH1 :
    H1 (AbsoluteGaloisGroup K ⧸
        (inertiaSubgroup K).map
          ((absoluteGaloisGroupRestrictEquiv K :
              Field.absoluteGaloisGroup K ≃* AbsoluteGaloisGroup K) :
            Field.absoluteGaloisGroup K →* AbsoluteGaloisGroup K))
      (FixedPoints.addSubgroup
        ((inertiaSubgroup K).map
          ((absoluteGaloisGroupRestrictEquiv K :
              Field.absoluteGaloisGroup K ≃* AbsoluteGaloisGroup K) :
            Field.absoluteGaloisGroup K →* AbsoluteGaloisGroup K)) M) ≃+
      H1 zHat.{u}
        (FixedPoints.addSubgroup
          ((inertiaSubgroup K).map
            ((absoluteGaloisGroupRestrictEquiv K :
                Field.absoluteGaloisGroup K ≃* AbsoluteGaloisGroup K) :
              Field.absoluteGaloisGroup K →* AbsoluteGaloisGroup K)) M) :=
  explicitMap1Equiv _ _ zHat.{u} _
    (quotientMapInertiaSubgroupEquivZHat K).symm (AddEquiv.refl _)
    continuous_of_discreteTopology continuous_of_discreteTopology fun z m ↦ by
      rw [AddEquiv.refl_apply, AddEquiv.refl_apply]
      exact (compHom_symm_smul K z m).symm

/-- Transporting `unramifiedH1 K M` to `H¹(zHat, M^{I_K})` along
`(quotientMapInertiaSubgroupEquivZHat K).symm`. -/
private def unramifiedH1AddEquivZHatH1 :
    unramifiedH1 K M ≃+
      H1 zHat.{u}
        (FixedPoints.addSubgroup
          ((inertiaSubgroup K).map
            ((absoluteGaloisGroupRestrictEquiv K :
                Field.absoluteGaloisGroup K ≃* AbsoluteGaloisGroup K) :
              Field.absoluteGaloisGroup K →* AbsoluteGaloisGroup K)) M) :=
  (quotientH1AddEquivUnramifiedH1 K M).symm.trans (quotientH1AddEquivZHatH1 K M)

/-- On a `1`-cocycle `f` of `G_K ⧸ I_K`, `unramifiedH1AddEquivZHatH1` pulls `f` back along
`(quotientMapInertiaSubgroupEquivZHat K).symm`. -/
private theorem unramifiedH1AddEquivZHatH1_quotientH1AddEquivUnramifiedH1_mk
    (f : Z1
      (AbsoluteGaloisGroup K ⧸
        (inertiaSubgroup K).map
          ((absoluteGaloisGroupRestrictEquiv K :
              Field.absoluteGaloisGroup K ≃* AbsoluteGaloisGroup K) :
            Field.absoluteGaloisGroup K →* AbsoluteGaloisGroup K))
      (FixedPoints.addSubgroup
        ((inertiaSubgroup K).map
          ((absoluteGaloisGroupRestrictEquiv K :
              Field.absoluteGaloisGroup K ≃* AbsoluteGaloisGroup K) :
            Field.absoluteGaloisGroup K →* AbsoluteGaloisGroup K)) M)) :
    unramifiedH1AddEquivZHatH1 K M (quotientH1AddEquivUnramifiedH1 K M (f : H1 _ _)) =
      (cocyclesMap1 _ _ zHat.{u} _ (quotientMapInertiaSubgroupEquivZHat K).symm
        (AddEquiv.refl _).toAddMonoidHom continuous_of_discreteTopology
        (fun z m ↦ by
          rw [AddEquiv.coe_toAddMonoidHom, AddEquiv.refl_apply, AddEquiv.refl_apply,
            ContinuousMonoidHom.coe_coe]
          exact (compHom_symm_smul K z m).symm) f : H1 _ _) := by
  let I := (inertiaSubgroup K).map
    ((absoluteGaloisGroupRestrictEquiv K :
        Field.absoluteGaloisGroup K ≃* AbsoluteGaloisGroup K) :
      Field.absoluteGaloisGroup K →* AbsoluteGaloisGroup K)
  let N := FixedPoints.addSubgroup I M
  have hequiv : ∀ (z : zHat.{u}) (m : N),
      AddEquiv.refl N ((quotientMapInertiaSubgroupEquivZHat K).symm z • m) =
        z • AddEquiv.refl N m := fun z m ↦ by
    rw [AddEquiv.refl_apply, AddEquiv.refl_apply]
    exact (compHom_symm_smul K z m).symm
  exact (congrArg (quotientH1AddEquivZHatH1 K M)
      ((quotientH1AddEquivUnramifiedH1 K M).symm_apply_apply (f : H1 _ _))).trans <|
    (explicitMap1Equiv_apply (AbsoluteGaloisGroup K ⧸ I) N zHat.{u} N
      (quotientMapInertiaSubgroupEquivZHat K).symm (AddEquiv.refl N)
      continuous_of_discreteTopology continuous_of_discreteTopology hequiv (f : H1 _ _)).trans
      (explicitMap1_mk (AbsoluteGaloisGroup K ⧸ I) N zHat.{u} N
        (quotientMapInertiaSubgroupEquivZHat K).symm (AddEquiv.refl N).toAddMonoidHom
        continuous_of_discreteTopology hequiv f)

/-- Transporting `H⁰(G_K, M)` to `H⁰(zHat, M^{I_K})` along `explicitInfl0Equiv` and
`(quotientMapInertiaSubgroupEquivZHat K).symm`. -/
private def h0AddEquivZHatH0 :
    H0 (AbsoluteGaloisGroup K) M ≃+
      H0 zHat.{u}
        (FixedPoints.addSubgroup
          ((inertiaSubgroup K).map
            ((absoluteGaloisGroupRestrictEquiv K :
                Field.absoluteGaloisGroup K ≃* AbsoluteGaloisGroup K) :
              Field.absoluteGaloisGroup K →* AbsoluteGaloisGroup K)) M) :=
  let I := (inertiaSubgroup K).map
    ((absoluteGaloisGroupRestrictEquiv K :
        Field.absoluteGaloisGroup K ≃* AbsoluteGaloisGroup K) :
      Field.absoluteGaloisGroup K →* AbsoluteGaloisGroup K)
  let N := FixedPoints.addSubgroup I M
  let e := quotientMapInertiaSubgroupEquivZHat K
  have hequiv0 : ∀ (z : zHat.{u}) (m : N),
      AddMonoidHom.id N (e.symm.toMonoidHom z • m) = z • AddMonoidHom.id N m := fun z m ↦ by
    rw [AddMonoidHom.id_apply, AddMonoidHom.id_apply]
    exact (MulAction.compHom_smul_def e.symm.toMonoidHom z m).symm
  (explicitInfl0Equiv (AbsoluteGaloisGroup K) M I).symm.trans <|
    AddEquiv.ofBijective
      (explicitMap0 (AbsoluteGaloisGroup K ⧸ I) N e.symm.toMonoidHom (AddMonoidHom.id N) hequiv0)
      (explicitMap0_bijective (AbsoluteGaloisGroup K ⧸ I) N e.symm.toMonoidHom e.symm.surjective
        (AddMonoidHom.id N) Function.bijective_id hequiv0)

omit [TopologicalSpace M] [DiscreteTopology M] [ContinuousSMul (AbsoluteGaloisGroup K) M] in
/-- Specialization of `genSubId_eq_frobeniusSubId` using the local `zHat`-action instance. -/
private theorem genSubId_eq_frobeniusSubId_local :
    zHat.genSubId.{u}
        (FixedPoints.addSubgroup
          ((inertiaSubgroup K).map
            ((absoluteGaloisGroupRestrictEquiv K :
                Field.absoluteGaloisGroup K ≃* AbsoluteGaloisGroup K) :
              Field.absoluteGaloisGroup K →* AbsoluteGaloisGroup K)) M) =
      frobeniusSubId K M :=
  genSubId_eq_frobeniusSubId K M

/-- **Unramified `H¹` is the Frobenius coinvariant quotient of `M^{I_K}`**: for a discrete
`G_K`-module `M` whose inertia-fixed subgroup `M^{I_K}` is torsion,
`unramifiedH1 K M ≃+ M^{I_K} ⧸ (Frob_K - 1) M^{I_K}`. -/
def unramifiedH1AddEquivCoinvariants
    (hM : IsAddTorsion (FixedPoints.addSubgroup
      ((inertiaSubgroup K).map
        ((absoluteGaloisGroupRestrictEquiv K :
            Field.absoluteGaloisGroup K ≃* AbsoluteGaloisGroup K) :
          Field.absoluteGaloisGroup K →* AbsoluteGaloisGroup K)) M)) :
    unramifiedH1 K M ≃+
      FixedPoints.addSubgroup
        ((inertiaSubgroup K).map
          ((absoluteGaloisGroupRestrictEquiv K :
              Field.absoluteGaloisGroup K ≃* AbsoluteGaloisGroup K) :
            Field.absoluteGaloisGroup K →* AbsoluteGaloisGroup K)) M ⧸
        (frobeniusSubId K M).range :=
  (unramifiedH1AddEquivZHatH1 K M).trans <|
    (zHat.h1AddEquivCoinvariants.{u} _ hM).trans
      (QuotientAddGroup.quotientAddEquivOfEq
        (congrArg AddMonoidHom.range (genSubId_eq_frobeniusSubId_local K M)))

/-- On a `1`-cocycle `f` of `G_K ⧸ I_K` with values in `M^{I_K}`,
`unramifiedH1AddEquivCoinvariants` sends its inflated unramified class to the coinvariant class of
`f (unramifiedQuotientFrobenius K)`. -/
@[simp]
theorem unramifiedH1AddEquivCoinvariants_quotientH1AddEquivUnramifiedH1_mk
    (hM : IsAddTorsion (FixedPoints.addSubgroup
      ((inertiaSubgroup K).map
        ((absoluteGaloisGroupRestrictEquiv K :
            Field.absoluteGaloisGroup K ≃* AbsoluteGaloisGroup K) :
          Field.absoluteGaloisGroup K →* AbsoluteGaloisGroup K)) M))
    (f : Z1
      (AbsoluteGaloisGroup K ⧸
        (inertiaSubgroup K).map
          ((absoluteGaloisGroupRestrictEquiv K :
              Field.absoluteGaloisGroup K ≃* AbsoluteGaloisGroup K) :
            Field.absoluteGaloisGroup K →* AbsoluteGaloisGroup K))
      (FixedPoints.addSubgroup
        ((inertiaSubgroup K).map
          ((absoluteGaloisGroupRestrictEquiv K :
              Field.absoluteGaloisGroup K ≃* AbsoluteGaloisGroup K) :
            Field.absoluteGaloisGroup K →* AbsoluteGaloisGroup K)) M)) :
    unramifiedH1AddEquivCoinvariants K M hM
        (quotientH1AddEquivUnramifiedH1 K M (f : H1 _ _)) =
      QuotientAddGroup.mk (f.val (unramifiedQuotientFrobenius K)) := by
  dsimp only [unramifiedH1AddEquivCoinvariants]
  rw [AddEquiv.trans_apply, AddEquiv.trans_apply,
    unramifiedH1AddEquivZHatH1_quotientH1AddEquivUnramifiedH1_mk,
    zHat.h1AddEquivCoinvariants_apply, zHat.evalGen_mk, QuotientAddGroup.quotientAddEquivOfEq_mk,
    cocyclesMap1_apply, AddEquiv.coe_toAddMonoidHom, AddEquiv.refl_apply,
    ContinuousMonoidHom.coe_coe, quotientMapInertiaSubgroupEquivZHat_symm_gen]

/-- **Frobenius order formula for unramified cohomology.** For any discrete `G_K`-module `M` whose
inertia-fixed subgroup `M^{I_K}` is finite (in particular for every finite discrete `G_K`-module
`M`, with no unramifiedness or residue-characteristic assumption),
`#unramifiedH1 K M = #H⁰(G_K, M)`. -/
theorem natCard_unramifiedH1_eq_natCard_H0
    [Finite (FixedPoints.addSubgroup
      ((inertiaSubgroup K).map
        ((absoluteGaloisGroupRestrictEquiv K :
            Field.absoluteGaloisGroup K ≃* AbsoluteGaloisGroup K) :
          Field.absoluteGaloisGroup K →* AbsoluteGaloisGroup K)) M)] :
    Nat.card (unramifiedH1 K M) = Nat.card (H0 (AbsoluteGaloisGroup K) M) :=
  calc
    Nat.card (unramifiedH1 K M) = Nat.card (H1 zHat.{u} _) :=
      Nat.card_congr (unramifiedH1AddEquivZHatH1 K M).toEquiv
    _ = Nat.card (H0 zHat.{u} _) := zHat.natCard_H1_eq_natCard_H0.{u} _
    _ = Nat.card (H0 (AbsoluteGaloisGroup K) M) :=
      Nat.card_congr (h0AddEquivZHatH0 K M).symm.toEquiv

/-- **Unramified `H¹` is finite** for every discrete `G_K`-module `M` whose inertia-fixed subgroup
`M^{I_K}` is finite (in particular for every finite discrete `G_K`-module `M`). -/
instance finite_unramifiedH1
    [Finite (FixedPoints.addSubgroup
      ((inertiaSubgroup K).map
        ((absoluteGaloisGroupRestrictEquiv K :
            Field.absoluteGaloisGroup K ≃* AbsoluteGaloisGroup K) :
          Field.absoluteGaloisGroup K →* AbsoluteGaloisGroup K)) M)] :
    Finite (unramifiedH1 K M) := by
  have : Finite (H0 (AbsoluteGaloisGroup K) M) :=
    Finite.of_equiv _ (explicitInfl0Equiv (AbsoluteGaloisGroup K) M
      ((inertiaSubgroup K).map
        ((absoluteGaloisGroupRestrictEquiv K :
            Field.absoluteGaloisGroup K ≃* AbsoluteGaloisGroup K) :
          Field.absoluteGaloisGroup K →* AbsoluteGaloisGroup K))).toEquiv
  exact Nat.finite_of_card_ne_zero
    ((natCard_unramifiedH1_eq_natCard_H0 K M).trans_ne Nat.card_pos.ne')

/-- **If a discrete `G_K`-module with finite `M^{I_K}` has trivial `G_K`-invariants, its unramified
`H¹` vanishes.** -/
theorem subsingleton_unramifiedH1_of_subsingleton_H0
    [Finite (FixedPoints.addSubgroup
      ((inertiaSubgroup K).map
        ((absoluteGaloisGroupRestrictEquiv K :
            Field.absoluteGaloisGroup K ≃* AbsoluteGaloisGroup K) :
          Field.absoluteGaloisGroup K →* AbsoluteGaloisGroup K)) M)]
    [Subsingleton (H0 (AbsoluteGaloisGroup K) M)] :
    Subsingleton (unramifiedH1 K M) := by
  let N := FixedPoints.addSubgroup
    ((inertiaSubgroup K).map
      ((absoluteGaloisGroupRestrictEquiv K :
          Field.absoluteGaloisGroup K ≃* AbsoluteGaloisGroup K) :
        Field.absoluteGaloisGroup K →* AbsoluteGaloisGroup K)) M
  have _ : Subsingleton (H0 zHat.{u} N) := (h0AddEquivZHatH0 K M).symm.toEquiv.subsingleton
  have _ : Subsingleton (H1 zHat.{u} N) := zHat.subsingleton_H1_of_subsingleton_H0.{u} N
  exact (unramifiedH1AddEquivZHatH1 K M).toEquiv.subsingleton

end CoinvariantsAndCardinality

section CupProduct

variable {K : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

/-- **`H²(G_K ⧸ I_K, N)` vanishes** for every profinite abelian group `N` with a continuous action
of the unramified quotient `G_K ⧸ I_K`, since `G_K ⧸ I_K ≃ₜ* zHat`. -/
instance subsingleton_H2_quotient_inertiaSubgroup {N : Type v} [AddCommGroup N]
    [TopologicalSpace N] [IsTopologicalAddGroup N] [CompactSpace N] [TotallyDisconnectedSpace N]
    [DistribMulAction
      (AbsoluteGaloisGroup K ⧸
        (inertiaSubgroup K).map
          ((absoluteGaloisGroupRestrictEquiv K :
              Field.absoluteGaloisGroup K ≃* AbsoluteGaloisGroup K) :
            Field.absoluteGaloisGroup K →* AbsoluteGaloisGroup K)) N]
    [ContinuousSMul
      (AbsoluteGaloisGroup K ⧸
        (inertiaSubgroup K).map
          ((absoluteGaloisGroupRestrictEquiv K :
              Field.absoluteGaloisGroup K ≃* AbsoluteGaloisGroup K) :
            Field.absoluteGaloisGroup K →* AbsoluteGaloisGroup K)) N] :
    Subsingleton (H2
      (AbsoluteGaloisGroup K ⧸
        (inertiaSubgroup K).map
          ((absoluteGaloisGroupRestrictEquiv K :
              Field.absoluteGaloisGroup K ≃* AbsoluteGaloisGroup K) :
            Field.absoluteGaloisGroup K →* AbsoluteGaloisGroup K)) N) := by
  let I := (inertiaSubgroup K).map
    ((absoluteGaloisGroupRestrictEquiv K :
        Field.absoluteGaloisGroup K ≃* AbsoluteGaloisGroup K) :
      Field.absoluteGaloisGroup K →* AbsoluteGaloisGroup K)
  let e := quotientMapInertiaSubgroupEquivZHat K
  let _ : DistribMulAction zHat.{u} N := DistribMulAction.compHom N e.symm.toMonoidHom
  have _ : ContinuousSMul zHat.{u} N := MulAction.continuousSMul_compHom e.symm.continuous
  exact (explicitMap2Equiv (AbsoluteGaloisGroup K ⧸ I) N zHat.{u} N e.symm (AddEquiv.refl N)
    continuous_id continuous_id fun z m ↦ by
      rw [AddEquiv.refl_apply, AddEquiv.refl_apply]
      exact (compHom_symm_smul K z m).symm).toEquiv.subsingleton

/-- **Cup-product orthogonality of unramified degree-one classes.** Let `μ : A →+ B →+ P` be a
continuous `G_K`-equivariant biadditive pairing of topological `G_K`-modules such that `G_K ⧸ I_K`
acts continuously on the inertia-fixed subgroups and `H²(G_K ⧸ I_K, P^{I_K})` vanishes (for instance
when `A`, `B`, `P` are discrete and `P^{I_K}` is finite, or when `P^{I_K}` is profinite). Then any
two unramified classes `a ∈ unramifiedH1 K A` and `b ∈ unramifiedH1 K B` satisfy `a ⌣ b = 0` in
`H²(G_K, P)`. -/
theorem _root_.AddMonoidHom.explicitCup11_eq_zero_of_mem_unramifiedH1
    {A B P : Type*} [AddCommGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A]
    [DistribMulAction (AbsoluteGaloisGroup K) A] [ContinuousSMul (AbsoluteGaloisGroup K) A]
    [AddCommGroup B] [TopologicalSpace B] [IsTopologicalAddGroup B]
    [DistribMulAction (AbsoluteGaloisGroup K) B] [ContinuousSMul (AbsoluteGaloisGroup K) B]
    [AddCommGroup P] [TopologicalSpace P] [IsTopologicalAddGroup P]
    [DistribMulAction (AbsoluteGaloisGroup K) P] [ContinuousSMul (AbsoluteGaloisGroup K) P]
    [ContinuousSMul
      (AbsoluteGaloisGroup K ⧸
        (inertiaSubgroup K).map
          ((absoluteGaloisGroupRestrictEquiv K :
              Field.absoluteGaloisGroup K ≃* AbsoluteGaloisGroup K) :
            Field.absoluteGaloisGroup K →* AbsoluteGaloisGroup K))
      (FixedPoints.addSubgroup
        ((inertiaSubgroup K).map
          ((absoluteGaloisGroupRestrictEquiv K :
              Field.absoluteGaloisGroup K ≃* AbsoluteGaloisGroup K) :
            Field.absoluteGaloisGroup K →* AbsoluteGaloisGroup K)) A)]
    [ContinuousSMul
      (AbsoluteGaloisGroup K ⧸
        (inertiaSubgroup K).map
          ((absoluteGaloisGroupRestrictEquiv K :
              Field.absoluteGaloisGroup K ≃* AbsoluteGaloisGroup K) :
            Field.absoluteGaloisGroup K →* AbsoluteGaloisGroup K))
      (FixedPoints.addSubgroup
        ((inertiaSubgroup K).map
          ((absoluteGaloisGroupRestrictEquiv K :
              Field.absoluteGaloisGroup K ≃* AbsoluteGaloisGroup K) :
            Field.absoluteGaloisGroup K →* AbsoluteGaloisGroup K)) B)]
    [ContinuousSMul
      (AbsoluteGaloisGroup K ⧸
        (inertiaSubgroup K).map
          ((absoluteGaloisGroupRestrictEquiv K :
              Field.absoluteGaloisGroup K ≃* AbsoluteGaloisGroup K) :
            Field.absoluteGaloisGroup K →* AbsoluteGaloisGroup K))
      (FixedPoints.addSubgroup
        ((inertiaSubgroup K).map
          ((absoluteGaloisGroupRestrictEquiv K :
              Field.absoluteGaloisGroup K ≃* AbsoluteGaloisGroup K) :
            Field.absoluteGaloisGroup K →* AbsoluteGaloisGroup K)) P)]
    [Subsingleton (H2
      (AbsoluteGaloisGroup K ⧸
        (inertiaSubgroup K).map
          ((absoluteGaloisGroupRestrictEquiv K :
              Field.absoluteGaloisGroup K ≃* AbsoluteGaloisGroup K) :
            Field.absoluteGaloisGroup K →* AbsoluteGaloisGroup K))
      (FixedPoints.addSubgroup
        ((inertiaSubgroup K).map
          ((absoluteGaloisGroupRestrictEquiv K :
              Field.absoluteGaloisGroup K ≃* AbsoluteGaloisGroup K) :
            Field.absoluteGaloisGroup K →* AbsoluteGaloisGroup K)) P))]
    (μ : A →+ B →+ P) (hμ : Continuous fun p : A × B ↦ μ p.1 p.2)
    (hequiv : ∀ (g : AbsoluteGaloisGroup K) (x : A) (y : B), μ (g • x) (g • y) = g • μ x y)
    {a : H1 (AbsoluteGaloisGroup K) A} {b : H1 (AbsoluteGaloisGroup K) B}
    (ha : a ∈ unramifiedH1 K A) (hb : b ∈ unramifiedH1 K B) :
    explicitCup11 (AbsoluteGaloisGroup K) A B P μ hμ hequiv a b = 0 := by
  let I := (inertiaSubgroup K).map
    ((absoluteGaloisGroupRestrictEquiv K :
        Field.absoluteGaloisGroup K ≃* AbsoluteGaloisGroup K) :
      Field.absoluteGaloisGroup K →* AbsoluteGaloisGroup K)
  have ha' : a ∈ (explicitInfl1 (AbsoluteGaloisGroup K) A I).range := by
    rwa [range_explicitInfl1_eq_unramifiedH1]
  have hb' : b ∈ (explicitInfl1 (AbsoluteGaloisGroup K) B I).range := by
    rwa [range_explicitInfl1_eq_unramifiedH1]
  obtain ⟨a₀, rfl⟩ := ha'
  obtain ⟨b₀, rfl⟩ := hb'
  rw [← explicitInfl2_explicitCup11 (AbsoluteGaloisGroup K) A B P I μ hμ hequiv a₀ b₀]
  rw [Subsingleton.elim (explicitCup11 _ _ _ _ _ _ _ a₀ b₀) 0, map_zero]

end CupProduct

end TauCeti
