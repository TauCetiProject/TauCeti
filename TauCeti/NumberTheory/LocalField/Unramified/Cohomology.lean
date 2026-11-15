/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Torsion
public import TauCeti.NumberTheory.LocalField.Unramified.Inertia.SeparableClosure
public import TauCeti.NumberTheory.LocalField.Unramified.ZHat
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

is the kernel of restriction to `I_K`.

Inflation-restriction (`TauCeti.ContCohomology.explicitInfRes_exact` and
`TauCeti.ContCohomology.explicitInfl1_injective`) identifies `unramifiedH1 K M` with
`H¹(G_K ⧸ I_K, M^{I_K})` whenever the quotient action on `M^{I_K}` is continuous — in particular for
every discrete `G_K`-module `M`. Transporting along the topological group isomorphism
`G_K ⧸ I_K ≃ₜ* Gal(Kᵘʳ/K) ≃ₜ* zHat` (`TauCeti.quotientMapInertiaSubgroupEquivZHat`) carries the
class `TauCeti.frobQuotient K` of arithmetic Frobenius to `zHat.gen`, so the coinvariant computation
for `zHat` (`TauCeti.zHat.h1AddEquivCoinvariants`) gives

```text
unramifiedH1 K M ≃+ M^{I_K} ⧸ (Frob_K - 1) M^{I_K}
```

whenever `M` is discrete and `M^{I_K}` is torsion (`TauCeti.unramifiedH1AddEquivCoinvariants`).

When `M` is discrete and `M^{I_K}` is finite (in particular for every finite discrete `G_K`-module
`M`, with no unramifiedness or residue-characteristic assumption on `M`), comparing the kernel and
cokernel of `Frob_K - 1` on `M^{I_K}` yields the **Frobenius order formula**
(`TauCeti.natCard_unramifiedH1_eq_natCard_H0`):

```text
#unramifiedH1 K M = #H⁰(G_K, M).
```

Finally, since `H²(zHat, N)` vanishes for every profinite `zHat`-module `N`
(`TauCeti.zHat.subsingleton_H2_additive`), `H²(G_K ⧸ I_K, N)` vanishes as well
(`TauCeti.subsingleton_H2_quotient_inertiaSubgroup`). Because inflation commutes with explicit
`(1, 1)` cup products (`TauCeti.ContCohomology.explicitInfl2_explicitCup11`), **the cup product of
any two unramified degree-one classes vanishes in `H²(G_K, P)`** along any `G_K`-equivariant
biadditive pairing `A × B → P` of discrete `G_K`-modules whose inertia-fixed target `P^{I_K}` is
finite (`TauCeti.explicitCup11_eq_zero_of_mem_unramifiedH1`).

## Main definitions

* `TauCeti.quotientMapInertiaSubgroupEquivZHat`: the topological group isomorphism
  `G_K ⧸ I_K ≃ₜ* zHat` sending arithmetic Frobenius to `zHat.gen`.
* `TauCeti.frobQuotient`: the image of arithmetic Frobenius in `G_K ⧸ I_K`.
* `TauCeti.frobSubId`: the endomorphism `m ↦ frobQuotient K • m - m` of `M^{I_K}`.
* `TauCeti.unramifiedH1`: the subgroup `ker(H¹(G_K, M) → H¹(I_K, M))` of unramified classes.
* `TauCeti.unramifiedH1AddEquivQuotient`: inflation as `H¹(G_K ⧸ I_K, M^{I_K}) ≃+ unramifiedH1 K M`.
* `TauCeti.unramifiedH1AddEquivCoinvariants`: the isomorphism
  `unramifiedH1 K M ≃+ M^{I_K} ⧸ (Frob_K - 1) M^{I_K}` for discrete `M` with torsion `M^{I_K}`.

## Main results

* `TauCeti.explicitCoeff1_mem_unramifiedH1`, `TauCeti.explicitMap1_mem_unramifiedH1`: functoriality
  of `unramifiedH1` in the coefficient module and along valuative extensions of local fields.
* `TauCeti.ker_frobSubId_eq_fixedPoints`, `TauCeti.natCard_unramifiedH1_eq_natCard_H0`:
  `ker(Frob_K - 1 | M^{I_K}) = (M^{I_K})^{G_K ⧸ I_K}`, and `#unramifiedH1 K M = #H⁰(G_K, M)` for
  discrete `M` with finite `M^{I_K}`.
* `TauCeti.subsingleton_H2_quotient_inertiaSubgroup`: `H²(G_K ⧸ I_K, N) = 0` for profinite `N`.
* `TauCeti.explicitCup11_eq_zero_of_mem_unramifiedH1`: two unramified classes cup to `0` in
  `H²(G_K, P)` whenever `P^{I_K}` is finite.

## References

* J. S. Milne, *Arithmetic Duality Theorems*, 2nd ed., Chapter I, Lemma 2.7 and Theorem 2.6.
* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., Proposition 7.2.14.
* K. Rubin, *Euler Systems*, Annals of Mathematics Studies 147, Lemma I.3.2(i).
-/

public noncomputable section

namespace TauCeti

open ContCohomology _root_.ValuativeRel

universe u v w

section QuotientZHat

variable (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

/-- **Inertia in `AbsoluteGaloisGroup K` is normal**, as the image of `inertiaSubgroup K` under the
surjective isomorphism `absoluteGaloisGroupRestrictEquiv K`. -/
instance normal_map_inertiaSubgroup_absoluteGaloisGroupRestrictEquiv :
    ((inertiaSubgroup K).map (absoluteGaloisGroupRestrictEquiv K).toMonoidHom).Normal :=
  Subgroup.Normal.map (inertiaSubgroup_normal K) _ (absoluteGaloisGroupRestrictEquiv K).surjective

/-- **The unramified quotient of `AbsoluteGaloisGroup K` is `zHat`.** Transporting from
`Field.absoluteGaloisGroup K ⧸ inertiaSubgroup K` through
`TauCeti.absoluteGaloisGroupQuotientEquivOfEq` and
`TauCeti.maximalUnramifiedGaloisGroupEquivZHat` sends arithmetic Frobenius lifts to
`zHat.gen`. -/
def quotientMapInertiaSubgroupEquivZHat :
    (AbsoluteGaloisGroup K ⧸
      (inertiaSubgroup K).map (absoluteGaloisGroupRestrictEquiv K).toMonoidHom) ≃ₜ* zHat.{u} :=
  ((absoluteGaloisGroupRestrictEquiv K).quotientCongr (inertiaSubgroup K)
      ((inertiaSubgroup K).map (absoluteGaloisGroupRestrictEquiv K).toMonoidHom) rfl).symm.trans
    ((absoluteGaloisGroupQuotientEquivOfEq (inertiaSubgroup_def K)).trans
      (maximalUnramifiedGaloisGroupEquivZHat K (AlgebraicClosure K)))

/-- `quotientMapInertiaSubgroupEquivZHat K` evaluates on the coset of `σ` via restriction to the
maximal unramified extension and `maximalUnramifiedGaloisGroupEquivZHat`. -/
theorem quotientMapInertiaSubgroupEquivZHat_mk (σ : Field.absoluteGaloisGroup K) :
    quotientMapInertiaSubgroupEquivZHat K
        (absoluteGaloisGroupRestrictEquiv K σ :
          AbsoluteGaloisGroup K ⧸
            (inertiaSubgroup K).map (absoluteGaloisGroupRestrictEquiv K).toMonoidHom) =
      maximalUnramifiedGaloisGroupEquivZHat K (AlgebraicClosure K)
        (restrictMaximalUnramifiedHom K σ) := by
  let I := (inertiaSubgroup K).map (absoluteGaloisGroupRestrictEquiv K).toMonoidHom
  rw [quotientMapInertiaSubgroupEquivZHat, ContinuousMulEquiv.trans_apply,
    ContinuousMulEquiv.trans_apply]
  have hsymm : ((absoluteGaloisGroupRestrictEquiv K).quotientCongr (inertiaSubgroup K) I rfl).symm
      (absoluteGaloisGroupRestrictEquiv K σ : AbsoluteGaloisGroup K ⧸ I) =
      (σ : Field.absoluteGaloisGroup K ⧸ inertiaSubgroup K) := by
    apply ((absoluteGaloisGroupRestrictEquiv K).quotientCongr (inertiaSubgroup K) I rfl).injective
    rw [ContinuousMulEquiv.apply_symm_apply]
    exact (ContinuousMulEquiv.quotientCongr_mk
      (absoluteGaloisGroupRestrictEquiv K) (inertiaSubgroup K) I rfl σ).symm
  have hres : AlgEquiv.restrictNormalHom (maximalUnramifiedExtension K (AlgebraicClosure K)) σ =
      restrictMaximalUnramifiedHom K σ := by
    ext x
    exact (AlgEquiv.restrictNormal_commutes _ _ x).trans
      (restrictMaximalUnramifiedHom_coe_apply σ x).symm
  rw [hsymm, absoluteGaloisGroupQuotientEquivOfEq_mk, hres]

variable {K} in
/-- **An arithmetic Frobenius lift maps to `zHat.gen` in the unramified quotient.** -/
theorem quotientMapInertiaSubgroupEquivZHat_mk_of_isArithFrobeniusLift
    {σ : Field.absoluteGaloisGroup K} (hσ : IsArithFrobeniusLift K σ) :
    quotientMapInertiaSubgroupEquivZHat K
        (absoluteGaloisGroupRestrictEquiv K σ :
          AbsoluteGaloisGroup K ⧸
            (inertiaSubgroup K).map (absoluteGaloisGroupRestrictEquiv K).toMonoidHom) =
      zHat.gen := by
  rw [quotientMapInertiaSubgroupEquivZHat_mk, isArithFrobeniusLift_def.mp hσ,
    maximalUnramifiedGaloisGroupEquivZHat_apply_frobenius]

/-- **The arithmetic Frobenius element of the unramified quotient** of `AbsoluteGaloisGroup K`,
corresponding to `zHat.gen` under `quotientMapInertiaSubgroupEquivZHat K`. -/
def frobQuotient :
    AbsoluteGaloisGroup K ⧸
      (inertiaSubgroup K).map (absoluteGaloisGroupRestrictEquiv K).toMonoidHom :=
  (quotientMapInertiaSubgroupEquivZHat K).symm zHat.gen

/-- `frobQuotient K` is the preimage of `zHat.gen` under `quotientMapInertiaSubgroupEquivZHat K`. -/
theorem frobQuotient_def :
    frobQuotient K = (quotientMapInertiaSubgroupEquivZHat K).symm zHat.gen :=
  (rfl)

/-- `quotientMapInertiaSubgroupEquivZHat K` sends `frobQuotient K` to `zHat.gen`. -/
theorem quotientMapInertiaSubgroupEquivZHat_frobQuotient :
    quotientMapInertiaSubgroupEquivZHat K (frobQuotient K) = zHat.gen :=
  (quotientMapInertiaSubgroupEquivZHat K).apply_symm_apply zHat.gen

variable {K} in
/-- `frobQuotient K` is the coset of the restriction to `Kˢ` of any arithmetic Frobenius lift. -/
theorem frobQuotient_eq_mk_of_isArithFrobeniusLift {σ : Field.absoluteGaloisGroup K}
    (hσ : IsArithFrobeniusLift K σ) :
    frobQuotient K =
      (absoluteGaloisGroupRestrictEquiv K σ :
        AbsoluteGaloisGroup K ⧸
          (inertiaSubgroup K).map (absoluteGaloisGroupRestrictEquiv K).toMonoidHom) := by
  apply (quotientMapInertiaSubgroupEquivZHat K).injective
  rw [quotientMapInertiaSubgroupEquivZHat_frobQuotient,
    quotientMapInertiaSubgroupEquivZHat_mk_of_isArithFrobeniusLift hσ]

/-- **The Frobenius-minus-identity endomorphism `Frob_K - 1`** on the inertia invariants `M^{I_K}`
of an `AbsoluteGaloisGroup K`-module `M`. -/
def frobSubId (M : Type v) [AddCommGroup M] [DistribMulAction (AbsoluteGaloisGroup K) M] :
    FixedPoints.addSubgroup
        ((inertiaSubgroup K).map (absoluteGaloisGroupRestrictEquiv K).toMonoidHom) M →+
      FixedPoints.addSubgroup
        ((inertiaSubgroup K).map (absoluteGaloisGroupRestrictEquiv K).toMonoidHom) M where
  toFun m := frobQuotient K • m - m
  map_zero' := by rw [smul_zero, sub_self]
  map_add' a b := by
    rw [smul_add]
    abel

/-- `frobSubId K M` sends `m ∈ M^{I_K}` to `frobQuotient K • m - m`. -/
theorem frobSubId_apply {M : Type v} [AddCommGroup M] [DistribMulAction (AbsoluteGaloisGroup K) M]
    (m : FixedPoints.addSubgroup
      ((inertiaSubgroup K).map (absoluteGaloisGroupRestrictEquiv K).toMonoidHom) M) :
    frobSubId K M m = frobQuotient K • m - m :=
  (rfl)

/-- Transport a continuous action of the unramified quotient `G_K ⧸ I_K` to `zHat` along
`(quotientMapInertiaSubgroupEquivZHat K).symm`. -/
private theorem continuousSMul_zHat_of_quotient {N : Type v} [AddCommGroup N] [TopologicalSpace N]
    [DistribMulAction
      (AbsoluteGaloisGroup K ⧸
        (inertiaSubgroup K).map (absoluteGaloisGroupRestrictEquiv K).toMonoidHom) N]
    [ContinuousSMul
      (AbsoluteGaloisGroup K ⧸
        (inertiaSubgroup K).map (absoluteGaloisGroupRestrictEquiv K).toMonoidHom) N] :
    letI : DistribMulAction zHat.{u} N :=
      DistribMulAction.compHom N (quotientMapInertiaSubgroupEquivZHat K).symm.toMonoidHom
    ContinuousSMul zHat.{u} N := by
  let I := (inertiaSubgroup K).map (absoluteGaloisGroupRestrictEquiv K).toMonoidHom
  have hsmul : Continuous fun p : (AbsoluteGaloisGroup K ⧸ I) × N ↦ p.1 • p.2 := continuous_smul
  let _ : DistribMulAction zHat.{u} N :=
    DistribMulAction.compHom N (quotientMapInertiaSubgroupEquivZHat K).symm.toMonoidHom
  exact ⟨hsmul.comp ((quotientMapInertiaSubgroupEquivZHat K).symm.continuous.prodMap continuous_id)⟩

/-- **An inertia-invariant element of a Hausdorff `G_K`-module fixed by `frobQuotient K` is fixed
by the entire unramified quotient `G_K ⧸ I_K`** (whenever the quotient action on `M^{I_K}` is
continuous, for instance when `M` is discrete). -/
theorem ker_frobSubId_eq_fixedPoints (M : Type v) [AddCommGroup M] [TopologicalSpace M] [T2Space M]
    [DistribMulAction (AbsoluteGaloisGroup K) M]
    [ContinuousSMul
      (AbsoluteGaloisGroup K ⧸
        (inertiaSubgroup K).map (absoluteGaloisGroupRestrictEquiv K).toMonoidHom)
      (FixedPoints.addSubgroup
        ((inertiaSubgroup K).map (absoluteGaloisGroupRestrictEquiv K).toMonoidHom) M)] :
    (frobSubId K M).ker =
      FixedPoints.addSubgroup
        (AbsoluteGaloisGroup K ⧸
          (inertiaSubgroup K).map (absoluteGaloisGroupRestrictEquiv K).toMonoidHom)
        (FixedPoints.addSubgroup
          ((inertiaSubgroup K).map (absoluteGaloisGroupRestrictEquiv K).toMonoidHom) M) := by
  let I := (inertiaSubgroup K).map (absoluteGaloisGroupRestrictEquiv K).toMonoidHom
  let N := FixedPoints.addSubgroup I M
  let e := quotientMapInertiaSubgroupEquivZHat K
  let _ : DistribMulAction zHat.{u} N := DistribMulAction.compHom N e.symm.toMonoidHom
  have _ : ContinuousSMul zHat.{u} N := continuousSMul_zHat_of_quotient K
  have hhom : frobSubId K M = zHat.genSubId.{u} N := by
    ext m
    rw [frobSubId_apply, zHat.genSubId_apply]
    rfl
  rw [hhom, zHat.ker_genSubId_eq_fixedPoints]
  ext x
  rw [FixedPoints.mem_addSubgroup, FixedPoints.mem_addSubgroup]
  refine ⟨fun h q ↦ ?_, fun h z ↦ h (e.symm z)⟩
  have hq : (e.symm (e q)) • x = x := h (e q)
  rwa [e.symm_apply_apply] at hq

end QuotientZHat

section UnramifiedH1

variable (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  (M : Type v) [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]
  [DistribMulAction (AbsoluteGaloisGroup K) M] [ContinuousSMul (AbsoluteGaloisGroup K) M]

/-- **Unramified first Galois cohomology `H¹_ur(K, M)`**: the subgroup of `H¹(G_K, M)` consisting of
classes whose restriction to the inertia subgroup `I_K` vanishes. -/
def unramifiedH1 : AddSubgroup (H1 (AbsoluteGaloisGroup K) M) :=
  (explicitRes1 (AbsoluteGaloisGroup K) M
    ((inertiaSubgroup K).map (absoluteGaloisGroupRestrictEquiv K).toMonoidHom)).ker

/-- `unramifiedH1 K M` is the kernel of restriction to inertia in `AbsoluteGaloisGroup K`. -/
theorem unramifiedH1_def :
    unramifiedH1 K M =
      (explicitRes1 (AbsoluteGaloisGroup K) M
        ((inertiaSubgroup K).map (absoluteGaloisGroupRestrictEquiv K).toMonoidHom)).ker :=
  (rfl)

variable {K M}

/-- A class in `H¹(G_K, M)` is unramified if and only if its restriction to inertia vanishes. -/
@[simp]
theorem mem_unramifiedH1_iff {c : H1 (AbsoluteGaloisGroup K) M} :
    c ∈ unramifiedH1 K M ↔
      explicitRes1 (AbsoluteGaloisGroup K) M
        ((inertiaSubgroup K).map (absoluteGaloisGroupRestrictEquiv K).toMonoidHom) c = 0 :=
  (Iff.rfl)

/-- **Functoriality of `unramifiedH1` in the coefficient module.** A continuous `G_K`-equivariant
homomorphism `f : M →+[G_K] N` carries unramified classes in `H¹(G_K, M)` to unramified classes in
`H¹(G_K, N)`. -/
theorem explicitCoeff1_mem_unramifiedH1 {N : Type w} [AddCommGroup N] [TopologicalSpace N]
    [IsTopologicalAddGroup N] [DistribMulAction (AbsoluteGaloisGroup K) N]
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
theorem explicitMap1_mem_unramifiedH1 {L : Type*} [Field L] [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L] [Algebra K L] [ValuativeExtension K L]
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
      (inertiaSubgroup K).map (absoluteGaloisGroupRestrictEquiv K).toMonoidHom)
    (FixedPoints.addSubgroup
      ((inertiaSubgroup K).map (absoluteGaloisGroupRestrictEquiv K).toMonoidHom) M)]

/-- **The unramified subgroup of `H¹(G_K, M)` is the image of inflation from `G_K ⧸ I_K`.** -/
theorem range_explicitInfl1_eq_unramifiedH1 :
    (explicitInfl1 (AbsoluteGaloisGroup K) M
      ((inertiaSubgroup K).map (absoluteGaloisGroupRestrictEquiv K).toMonoidHom)).range =
      unramifiedH1 K M :=
  explicitInfRes_exact (AbsoluteGaloisGroup K) M _

variable {K M} in
/-- Every class inflated from `H¹(G_K ⧸ I_K, M^{I_K})` is unramified. -/
theorem explicitInfl1_mem_unramifiedH1
    (x : H1 (AbsoluteGaloisGroup K ⧸
        (inertiaSubgroup K).map (absoluteGaloisGroupRestrictEquiv K).toMonoidHom)
      (FixedPoints.addSubgroup
        ((inertiaSubgroup K).map (absoluteGaloisGroupRestrictEquiv K).toMonoidHom) M)) :
    explicitInfl1 (AbsoluteGaloisGroup K) M
      ((inertiaSubgroup K).map (absoluteGaloisGroupRestrictEquiv K).toMonoidHom) x ∈
      unramifiedH1 K M := by
  rw [← range_explicitInfl1_eq_unramifiedH1]
  exact ⟨x, rfl⟩

private theorem bijective_codRestrict_explicitInfl1 :
    Function.Bijective
      ((explicitInfl1 (AbsoluteGaloisGroup K) M
        ((inertiaSubgroup K).map (absoluteGaloisGroupRestrictEquiv K).toMonoidHom)).codRestrict
          (unramifiedH1 K M) explicitInfl1_mem_unramifiedH1) := by
  let I := (inertiaSubgroup K).map (absoluteGaloisGroupRestrictEquiv K).toMonoidHom
  refine ⟨fun a b h ↦ explicitInfl1_injective (AbsoluteGaloisGroup K) M I (congrArg Subtype.val h),
    fun y ↦ ?_⟩
  have hy : y.1 ∈ (explicitInfl1 (AbsoluteGaloisGroup K) M I).range := by
    rw [range_explicitInfl1_eq_unramifiedH1]
    exact y.2
  obtain ⟨x, hx⟩ := hy
  exact ⟨x, Subtype.ext hx⟩

/-- **Inflation identifies `H¹(G_K ⧸ I_K, M^{I_K})` with `unramifiedH1 K M`.** -/
def unramifiedH1AddEquivQuotient :
    H1 (AbsoluteGaloisGroup K ⧸
        (inertiaSubgroup K).map (absoluteGaloisGroupRestrictEquiv K).toMonoidHom)
      (FixedPoints.addSubgroup
        ((inertiaSubgroup K).map (absoluteGaloisGroupRestrictEquiv K).toMonoidHom) M) ≃+
      unramifiedH1 K M :=
  AddEquiv.ofBijective
    ((explicitInfl1 (AbsoluteGaloisGroup K) M
      ((inertiaSubgroup K).map (absoluteGaloisGroupRestrictEquiv K).toMonoidHom)).codRestrict
        (unramifiedH1 K M) explicitInfl1_mem_unramifiedH1)
    (bijective_codRestrict_explicitInfl1 K M)

/-- `unramifiedH1AddEquivQuotient` acts as `explicitInfl1` into `H¹(G_K, M)`. -/
theorem coe_unramifiedH1AddEquivQuotient_apply
    (x : H1 (AbsoluteGaloisGroup K ⧸
        (inertiaSubgroup K).map (absoluteGaloisGroupRestrictEquiv K).toMonoidHom)
      (FixedPoints.addSubgroup
        ((inertiaSubgroup K).map (absoluteGaloisGroupRestrictEquiv K).toMonoidHom) M)) :
    (unramifiedH1AddEquivQuotient K M x : H1 (AbsoluteGaloisGroup K) M) =
      explicitInfl1 (AbsoluteGaloisGroup K) M
        ((inertiaSubgroup K).map (absoluteGaloisGroupRestrictEquiv K).toMonoidHom) x :=
  (rfl)

end Inflation

end UnramifiedH1

section CoinvariantsAndCardinality

variable (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  (M : Type v) [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
  [DistribMulAction (AbsoluteGaloisGroup K) M] [ContinuousSMul (AbsoluteGaloisGroup K) M]

omit [TopologicalSpace M] [DiscreteTopology M] [ContinuousSMul (AbsoluteGaloisGroup K) M] in
private theorem range_genSubId_eq_range_frobSubId :
    letI : DistribMulAction zHat.{u}
        (FixedPoints.addSubgroup
          ((inertiaSubgroup K).map (absoluteGaloisGroupRestrictEquiv K).toMonoidHom) M) :=
      DistribMulAction.compHom _ (quotientMapInertiaSubgroupEquivZHat K).symm.toMonoidHom
    (zHat.genSubId.{u}
        (FixedPoints.addSubgroup
          ((inertiaSubgroup K).map (absoluteGaloisGroupRestrictEquiv K).toMonoidHom) M)).range =
      (frobSubId K M).range := by
  let _ : DistribMulAction zHat.{u}
      (FixedPoints.addSubgroup
        ((inertiaSubgroup K).map (absoluteGaloisGroupRestrictEquiv K).toMonoidHom) M) :=
    DistribMulAction.compHom _ (quotientMapInertiaSubgroupEquivZHat K).symm.toMonoidHom
  congr 1
  ext m
  rw [zHat.genSubId_apply, frobSubId_apply]
  rfl

/-- **Unramified `H¹` is the Frobenius coinvariant quotient of `M^{I_K}`**: for a discrete
`G_K`-module `M` whose inertia-fixed subgroup `M^{I_K}` is torsion,
`unramifiedH1 K M ≃+ M^{I_K} ⧸ (Frob_K - 1) M^{I_K}`. -/
def unramifiedH1AddEquivCoinvariants
    (hM : IsAddTorsion (FixedPoints.addSubgroup
      ((inertiaSubgroup K).map (absoluteGaloisGroupRestrictEquiv K).toMonoidHom) M)) :
    unramifiedH1 K M ≃+
      FixedPoints.addSubgroup
        ((inertiaSubgroup K).map (absoluteGaloisGroupRestrictEquiv K).toMonoidHom) M ⧸
        (frobSubId K M).range :=
  let I := (inertiaSubgroup K).map (absoluteGaloisGroupRestrictEquiv K).toMonoidHom
  let N := FixedPoints.addSubgroup I M
  letI : DistribMulAction zHat.{u} N :=
    DistribMulAction.compHom N (quotientMapInertiaSubgroupEquivZHat K).symm.toMonoidHom
  haveI : ContinuousSMul zHat.{u} N := continuousSMul_zHat_of_quotient K
  (unramifiedH1AddEquivQuotient K M).symm.trans <|
    (explicitMap1Equiv (AbsoluteGaloisGroup K ⧸ I) N zHat.{u} N
      (quotientMapInertiaSubgroupEquivZHat K).symm (AddEquiv.refl N)
      continuous_of_discreteTopology continuous_of_discreteTopology fun _ _ ↦ rfl).trans <|
      (zHat.h1AddEquivCoinvariants.{u} N hM).trans
        (QuotientAddGroup.quotientAddEquivOfEq (range_genSubId_eq_range_frobSubId K M))

/-- On a `1`-cocycle `f` of `G_K ⧸ I_K` with values in `M^{I_K}`,
`unramifiedH1AddEquivCoinvariants` sends its inflated unramified class to the coinvariant class of
`f (frobQuotient K)`. -/
theorem unramifiedH1AddEquivCoinvariants_unramifiedH1AddEquivQuotient_mk
    (hM : IsAddTorsion (FixedPoints.addSubgroup
      ((inertiaSubgroup K).map (absoluteGaloisGroupRestrictEquiv K).toMonoidHom) M))
    (f : Z1
      (AbsoluteGaloisGroup K ⧸
        (inertiaSubgroup K).map (absoluteGaloisGroupRestrictEquiv K).toMonoidHom)
      (FixedPoints.addSubgroup
        ((inertiaSubgroup K).map (absoluteGaloisGroupRestrictEquiv K).toMonoidHom) M)) :
    unramifiedH1AddEquivCoinvariants K M hM
        (unramifiedH1AddEquivQuotient K M (f : H1 _ _)) =
      QuotientAddGroup.mk (f.val (frobQuotient K)) := by
  let I := (inertiaSubgroup K).map (absoluteGaloisGroupRestrictEquiv K).toMonoidHom
  let N := FixedPoints.addSubgroup I M
  let _ : DistribMulAction zHat.{u} N :=
    DistribMulAction.compHom N (quotientMapInertiaSubgroupEquivZHat K).symm.toMonoidHom
  have _ : ContinuousSMul zHat.{u} N := continuousSMul_zHat_of_quotient K
  let c1 := cocyclesMap1 (AbsoluteGaloisGroup K ⧸ I) N zHat.{u} N
    (quotientMapInertiaSubgroupEquivZHat K).symm (AddEquiv.refl N).toAddMonoidHom
    continuous_of_discreteTopology (fun _ _ ↦ rfl) f
  refine (AddEquiv.trans_apply _ _ _).trans ?_
  refine (congrArg _ ((unramifiedH1AddEquivQuotient K M).symm_apply_apply (f : H1 _ _))).trans ?_
  refine (AddEquiv.trans_apply _ _ _).trans ?_
  refine (congrArg _ ((explicitMap1Equiv_apply _ _ _ _ _ _ _ _ _ _).trans
    (explicitMap1_mk _ _ _ _ _ _ _ _ f))).trans ?_
  refine (AddEquiv.trans_apply _ _ _).trans ?_
  refine (congrArg _ ((zHat.h1AddEquivCoinvariants_apply hM _).trans
    (zHat.evalGen_mk N c1))).trans ?_
  exact (QuotientAddGroup.quotientAddEquivOfEq_mk _ _).trans
    (congrArg QuotientAddGroup.mk (cocyclesMap1_apply _ _ _ _ _ _ _ _ f zHat.gen))

/-- **Frobenius order formula for unramified cohomology.** For any discrete `G_K`-module `M` whose
inertia-fixed subgroup `M^{I_K}` is finite (in particular for every finite discrete `G_K`-module
`M`, with no unramifiedness or residue-characteristic assumption),
`#unramifiedH1 K M = #H⁰(G_K, M)`. -/
theorem natCard_unramifiedH1_eq_natCard_H0
    [Finite (FixedPoints.addSubgroup
      ((inertiaSubgroup K).map (absoluteGaloisGroupRestrictEquiv K).toMonoidHom) M)] :
    Nat.card (unramifiedH1 K M) = Nat.card (H0 (AbsoluteGaloisGroup K) M) := by
  let I := (inertiaSubgroup K).map (absoluteGaloisGroupRestrictEquiv K).toMonoidHom
  let N := FixedPoints.addSubgroup I M
  have hidx : Nat.card (frobSubId K M).range * Nat.card (N ⧸ (frobSubId K M).range) =
      Nat.card N := by
    rw [mul_comm]
    exact (frobSubId K M).range.index_mul_card
  have hker := AddSubgroup.card_ker_mul_card_range (frobSubId K M)
  rw [ker_frobSubId_eq_fixedPoints K M, mul_comm] at hker
  have hquot : Nat.card (N ⧸ (frobSubId K M).range) =
      Nat.card (H0 (AbsoluteGaloisGroup K ⧸ I) N) :=
    Nat.eq_of_mul_eq_mul_left Nat.card_pos (hidx.trans hker.symm)
  exact (Nat.card_congr (unramifiedH1AddEquivCoinvariants K M isAddTorsion_of_finite).toEquiv).trans
    (hquot.trans (Nat.card_congr (explicitInfl0Equiv (AbsoluteGaloisGroup K) M I).toEquiv))

/-- **Unramified `H¹` is finite** whenever the inertia-fixed subgroup `M^{I_K}` is finite (in
particular for every finite discrete `G_K`-module `M`). -/
instance finite_unramifiedH1
    [Finite (FixedPoints.addSubgroup
      ((inertiaSubgroup K).map (absoluteGaloisGroupRestrictEquiv K).toMonoidHom) M)] :
    Finite (unramifiedH1 K M) := by
  have : Finite (H0 (AbsoluteGaloisGroup K) M) :=
    Finite.of_equiv _ (explicitInfl0Equiv (AbsoluteGaloisGroup K) M
      ((inertiaSubgroup K).map (absoluteGaloisGroupRestrictEquiv K).toMonoidHom)).toEquiv
  exact Nat.finite_of_card_ne_zero
    ((natCard_unramifiedH1_eq_natCard_H0 K M).trans_ne Nat.card_pos.ne')

/-- **If a discrete `G_K`-module with finite `M^{I_K}` has trivial `G_K`-invariants, its unramified
`H¹` vanishes.** -/
theorem subsingleton_unramifiedH1_of_subsingleton_H0
    [Finite (FixedPoints.addSubgroup
      ((inertiaSubgroup K).map (absoluteGaloisGroupRestrictEquiv K).toMonoidHom) M)]
    [Subsingleton (H0 (AbsoluteGaloisGroup K) M)] :
    Subsingleton (unramifiedH1 K M) := by
  have hcard : Nat.card (unramifiedH1 K M) = 1 :=
    (natCard_unramifiedH1_eq_natCard_H0 K M).trans
      (Nat.card_unique (α := H0 (AbsoluteGaloisGroup K) M))
  exact (Nat.card_eq_one_iff_unique.mp hcard).1

end CoinvariantsAndCardinality

section CupProduct

variable {K : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

/-- **`H²(G_K ⧸ I_K, N)` vanishes** for every profinite abelian group `N` with a continuous action
of the unramified quotient `G_K ⧸ I_K`, since `G_K ⧸ I_K ≃ₜ* zHat`. -/
instance subsingleton_H2_quotient_inertiaSubgroup {N : Type v} [AddCommGroup N]
    [TopologicalSpace N] [IsTopologicalAddGroup N] [CompactSpace N] [TotallyDisconnectedSpace N]
    [DistribMulAction
      (AbsoluteGaloisGroup K ⧸
        (inertiaSubgroup K).map (absoluteGaloisGroupRestrictEquiv K).toMonoidHom) N]
    [ContinuousSMul
      (AbsoluteGaloisGroup K ⧸
        (inertiaSubgroup K).map (absoluteGaloisGroupRestrictEquiv K).toMonoidHom) N] :
    Subsingleton (H2
      (AbsoluteGaloisGroup K ⧸
        (inertiaSubgroup K).map (absoluteGaloisGroupRestrictEquiv K).toMonoidHom) N) := by
  let I := (inertiaSubgroup K).map (absoluteGaloisGroupRestrictEquiv K).toMonoidHom
  let _ : DistribMulAction zHat.{u} N :=
    DistribMulAction.compHom N (quotientMapInertiaSubgroupEquivZHat K).symm.toMonoidHom
  have _ : ContinuousSMul zHat.{u} N := continuousSMul_zHat_of_quotient K
  exact (explicitMap2Equiv (AbsoluteGaloisGroup K ⧸ I) N zHat.{u} N
    (quotientMapInertiaSubgroupEquivZHat K).symm (AddEquiv.refl N)
    continuous_id continuous_id fun _ _ ↦ rfl).toEquiv.subsingleton

/-- **Cup-product orthogonality of unramified degree-one classes.** Let `μ : A →+ B →+ P` be a
`G_K`-equivariant biadditive pairing of discrete `G_K`-modules. If `P^{I_K}` is finite (in
particular if `P` is finite), then any two unramified classes `a ∈ unramifiedH1 K A` and
`b ∈ unramifiedH1 K B` satisfy `a ⌣ b = 0` in `H²(G_K, P)`. -/
theorem explicitCup11_eq_zero_of_mem_unramifiedH1
    {A B P : Type*} [AddCommGroup A] [TopologicalSpace A] [DiscreteTopology A]
    [DistribMulAction (AbsoluteGaloisGroup K) A] [ContinuousSMul (AbsoluteGaloisGroup K) A]
    [AddCommGroup B] [TopologicalSpace B] [DiscreteTopology B]
    [DistribMulAction (AbsoluteGaloisGroup K) B] [ContinuousSMul (AbsoluteGaloisGroup K) B]
    [AddCommGroup P] [TopologicalSpace P] [DiscreteTopology P]
    [DistribMulAction (AbsoluteGaloisGroup K) P] [ContinuousSMul (AbsoluteGaloisGroup K) P]
    [Finite (FixedPoints.addSubgroup
      ((inertiaSubgroup K).map (absoluteGaloisGroupRestrictEquiv K).toMonoidHom) P)]
    (μ : A →+ B →+ P)
    (hequiv : ∀ (g : AbsoluteGaloisGroup K) (x : A) (y : B), μ (g • x) (g • y) = g • μ x y)
    {a : H1 (AbsoluteGaloisGroup K) A} {b : H1 (AbsoluteGaloisGroup K) B}
    (ha : a ∈ unramifiedH1 K A) (hb : b ∈ unramifiedH1 K B) :
    explicitCup11 (AbsoluteGaloisGroup K) A B P μ
      continuous_of_discreteTopology hequiv a b = 0 := by
  let I := (inertiaSubgroup K).map (absoluteGaloisGroupRestrictEquiv K).toMonoidHom
  have ha' : a ∈ (explicitInfl1 (AbsoluteGaloisGroup K) A I).range := by
    rwa [range_explicitInfl1_eq_unramifiedH1]
  have hb' : b ∈ (explicitInfl1 (AbsoluteGaloisGroup K) B I).range := by
    rwa [range_explicitInfl1_eq_unramifiedH1]
  obtain ⟨a₀, rfl⟩ := ha'
  obtain ⟨b₀, rfl⟩ := hb'
  rw [← explicitInfl2_explicitCup11 (AbsoluteGaloisGroup K) A B P I μ
    continuous_of_discreteTopology hequiv a₀ b₀]
  rw [Subsingleton.elim (explicitCup11 _ _ _ _ _ _ _ a₀ b₀) 0, map_zero]

end CupProduct

end TauCeti
