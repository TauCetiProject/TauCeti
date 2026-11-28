/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Torsion
public import TauCeti.NumberTheory.LocalField.Unramified.Inertia.SeparableClosure
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Cup.Product.Basic
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Inflation.Basic
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Unramified
import TauCeti.RepresentationTheory.Homological.ContCohomology.Cup.Inflation
import TauCeti.Topology.Algebra.Group.Profinite.ZHat.Coinvariants.Basic
import TauCeti.Topology.Algebra.Group.Profinite.ZHat.Extension

/-!
# Unramified Galois cohomology over a nonarchimedean local field

Let `K` be a nonarchimedean local field, `G_K = AbsoluteGaloisGroup K` the Galois group of its
separable closure `Kˢ`, and `I_K = TauCeti.separableClosureInertiaSubgroup K` its inertia subgroup.
For a topological `G_K`-module `M`, the subgroup `unramifiedH1 K M ≤ H¹(G_K, M)` of **unramified
degree-one Galois cohomology classes** is the kernel of restriction to `I_K`. This file develops
its local cohomological properties, supplying the local input for Tate orthogonality of unramified
subgroups and the identification and finiteness of Selmer local conditions at good places.

Inflation-restriction (`TauCeti.ContCohomology.explicitInfRes_exact` and
`TauCeti.ContCohomology.explicitInfl1_injective`) identifies `H¹(G_K ⧸ I_K, M^{I_K})` with
`unramifiedH1 K M` (`TauCeti.quotientH1AddEquivUnramifiedH1`) whenever `G_K ⧸ I_K` acts
continuously on `M^{I_K}` (in particular whenever `M^{I_K}` is discrete). Transporting along
`G_K ⧸ I_K ≃ₜ* zHat` (`TauCeti.quotientSeparableClosureInertiaSubgroupEquivZHat`), which carries
`TauCeti.unramifiedQuotientFrobenius K` to `zHat.gen`, yields
`unramifiedH1 K M ≃+ M^{I_K} ⧸ (Frob_K - 1) M^{I_K}` (`TauCeti.unramifiedH1AddEquivCoinvariants`)
when `M^{I_K}` is discrete and torsion, and the **Frobenius order formula**
`#unramifiedH1 K M = #H⁰(G_K, M)` (`TauCeti.natCard_unramifiedH1_eq_natCard_H0`) when `M^{I_K}` is
discrete and finite (with no unramifiedness or residue-characteristic assumption on `M`).

Finally, since `H²(zHat, N) = 0` for every profinite `zHat`-module `N`
(`TauCeti.zHat.subsingleton_H2_additive`), `H²(G_K ⧸ I_K, N) = 0` as well
(`TauCeti.subsingleton_H2_quotient_separableClosureInertiaSubgroup`). Because inflation commutes
with explicit `(1, 1)` cup products (`TauCeti.ContCohomology.explicitInfl2_explicitCup11`), any two
unramified classes cup to `0` in `H²(G_K, P)` whenever `G_K ⧸ I_K` acts continuously on the
inertia-fixed subgroups and `H²(G_K ⧸ I_K, P^{I_K}) = 0` — in particular for discrete `A`, `B`, `P`
with finite `P^{I_K}` (`AddMonoidHom.explicitCup11_eq_zero_of_mem_unramifiedH1`).

## Main definitions

* `TauCeti.frobeniusSubId`: the endomorphism `m ↦ unramifiedQuotientFrobenius K • m - m` of
  `M^{I_K}`.
* `TauCeti.unramifiedH1`: the subgroup `ker(H¹(G_K, M) → H¹(I_K, M))` of unramified classes.
* `TauCeti.quotientH1AddEquivUnramifiedH1`: inflation `H¹(G_K ⧸ I_K, M^{I_K}) ≃+ unramifiedH1 K M`.
* `TauCeti.unramifiedH1AddEquivCoinvariants`: `unramifiedH1 K M ≃+ M^{I_K} ⧸ (Frob_K - 1) M^{I_K}`
  when `M^{I_K}` is discrete and torsion.

## Main results

* `TauCeti.mk_mem_unramifiedH1_of_forall_mem_separableClosureInertiaSubgroup`,
  `TauCeti.mk_mem_unramifiedH1_of_forall_mem_inertiaSubgroup`: a continuous `1`-cocycle vanishing
  on inertia represents an unramified class.
* `DistribMulActionHom.explicitCoeff1_mem_unramifiedH1`,
  `AddEquiv.unramifiedH1_comap_explicitCoeff1Equiv`,
  `DistribMulActionHom.unramifiedH1_comap_explicitCoeff1`,
  `AlgHom.explicitMap1_mem_unramifiedH1`: functoriality of `unramifiedH1` in the coefficient
  module and along valuative extensions of local fields.
* `DistribMulActionHom.comap_unramifiedH1_of_injective_of_smul_eq_self`: an injective coefficient
  map between unramified modules pulls the target unramified condition back to the source one.
* `TauCeti.ker_frobeniusSubId_eq_fixedPoints`, `TauCeti.natCard_unramifiedH1_eq_natCard_H0`:
  `ker(Frob_K - 1 | M^{I_K}) = (M^{I_K})^{G_K ⧸ I_K}`, and `#unramifiedH1 K M = #H⁰(G_K, M)` when
  `M^{I_K}` is discrete and finite.
* `TauCeti.exists_apply_unramifiedQuotientFrobenius_eq_of_isOfFinAddOrder`,
  `TauCeti.unramifiedH1AddEquivCoinvariants_mk_of_isArithFrobeniusLift`: realization of torsion
  inertia invariants as Frobenius values of continuous `1`-cocycles and evaluation of
  `unramifiedH1AddEquivCoinvariants` on unramified `G_K`-cocycles at arithmetic Frobenius lifts.
* `TauCeti.subsingleton_H2_quotient_separableClosureInertiaSubgroup`: `H²(G_K ⧸ I_K, N) = 0` for
  profinite `N`.
* `AddMonoidHom.explicitCup11_eq_zero_of_mem_unramifiedH1`: two unramified classes cup to `0` in
  `H²(G_K, P)` whenever `H²(G_K ⧸ I_K, P^{I_K}) = 0`.

## References

* J. S. Milne, *Arithmetic Duality Theorems*, 2nd ed., Chapter I, Lemma 2.7 and Theorem 2.6.
* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., Proposition 7.2.14.
* K. Rubin, *Euler Systems*, Annals of Mathematics Studies 147, Lemma I.3.2(i).
* B. Mazur and K. Rubin, *Kolyvagin systems*, Mem. Amer. Math. Soc. 168 (2004), no. 799,
  Lemma 1.1.9 (cartesianity of the unramified local condition).
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
    FixedPoints.addSubgroup (separableClosureInertiaSubgroup K) M →+
      FixedPoints.addSubgroup (separableClosureInertiaSubgroup K) M where
  toFun m := unramifiedQuotientFrobenius K • m - m
  map_zero' := by rw [smul_zero, sub_self]
  map_add' a b := by
    rw [smul_add]
    abel

/-- `frobeniusSubId K M` sends `m ∈ M^{I_K}` to `unramifiedQuotientFrobenius K • m - m`. -/
@[simp]
theorem frobeniusSubId_apply {M : Type v} [AddCommGroup M]
    [DistribMulAction (AbsoluteGaloisGroup K) M]
    (m : FixedPoints.addSubgroup (separableClosureInertiaSubgroup K) M) :
    frobeniusSubId K M m = unramifiedQuotientFrobenius K • m - m :=
  (rfl)

/-- Under the `zHat`-action transported along
`(quotientSeparableClosureInertiaSubgroupEquivZHat K).symm`, `zHat.genSubId` on `M^{I_K}` coincides
with `frobeniusSubId K M`. -/
private theorem genSubId_eq_frobeniusSubId (M : Type v) [AddCommGroup M]
    [DistribMulAction (AbsoluteGaloisGroup K) M] :
    letI : DistribMulAction zHat.{u}
        (FixedPoints.addSubgroup (separableClosureInertiaSubgroup K) M) :=
      DistribMulAction.compHom _
        (quotientSeparableClosureInertiaSubgroupEquivZHat K).symm.toMonoidHom
    zHat.genSubId.{u} (FixedPoints.addSubgroup (separableClosureInertiaSubgroup K) M) =
      frobeniusSubId K M := by
  let N := FixedPoints.addSubgroup (separableClosureInertiaSubgroup K) M
  let e := quotientSeparableClosureInertiaSubgroupEquivZHat K
  let _ : DistribMulAction zHat.{u} N := DistribMulAction.compHom N e.symm.toMonoidHom
  refine AddMonoidHom.ext fun m ↦ ?_
  rw [zHat.genSubId_apply, frobeniusSubId_apply, MulAction.compHom_smul_def e.symm.toMonoidHom,
    MulEquiv.coe_toMonoidHom]
  exact congrArg (· • m - m) (quotientSeparableClosureInertiaSubgroupEquivZHat_symm_gen K)

/-- **An inertia-invariant element of a `T₁` `G_K`-module fixed by `unramifiedQuotientFrobenius K`
is fixed by the entire unramified quotient `G_K ⧸ I_K`** (whenever the quotient action on `M^{I_K}`
is continuous, for instance when `M^{I_K}` is discrete). -/
theorem ker_frobeniusSubId_eq_fixedPoints (M : Type v) [AddCommGroup M] [TopologicalSpace M]
    [T1Space M] [DistribMulAction (AbsoluteGaloisGroup K) M]
    [ContinuousSMul (AbsoluteGaloisGroup K ⧸ separableClosureInertiaSubgroup K)
      (FixedPoints.addSubgroup (separableClosureInertiaSubgroup K) M)] :
    (frobeniusSubId K M).ker =
      FixedPoints.addSubgroup (AbsoluteGaloisGroup K ⧸ separableClosureInertiaSubgroup K)
        (FixedPoints.addSubgroup (separableClosureInertiaSubgroup K) M) := by
  let N := FixedPoints.addSubgroup (separableClosureInertiaSubgroup K) M
  let e := quotientSeparableClosureInertiaSubgroupEquivZHat K
  let _ : DistribMulAction zHat.{u} N := DistribMulAction.compHom N e.symm.toMonoidHom
  have _ : ContinuousSMul zHat.{u} N := MulAction.continuousSMul_compHom e.symm.continuous
  rw [← genSubId_eq_frobeniusSubId K M, zHat.ker_genSubId_eq_fixedPoints]
  ext x
  rw [FixedPoints.mem_addSubgroup, FixedPoints.mem_addSubgroup]
  simp_rw [MulAction.compHom_smul_def e.symm.toMonoidHom, MulEquiv.coe_toMonoidHom]
  exact ⟨fun h q ↦ by rw [← e.symm_apply_apply q]; exact h (e q), fun h z ↦ h (e.symm z)⟩

end FrobeniusSubId

section UnramifiedH1

variable (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  (M : Type v) [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]
  [DistribMulAction (AbsoluteGaloisGroup K) M] [ContinuousSMul (AbsoluteGaloisGroup K) M]

/-- **Unramified first Galois cohomology `H¹_ur(K, M)`**: the subgroup of `H¹(G_K, M)` consisting of
classes whose restriction to `separableClosureInertiaSubgroup K` vanishes. -/
def unramifiedH1 : AddSubgroup (H1 (AbsoluteGaloisGroup K) M) :=
  (explicitRes1 (AbsoluteGaloisGroup K) M (separableClosureInertiaSubgroup K)).ker

/-- `unramifiedH1 K M` is the kernel of restriction to `separableClosureInertiaSubgroup K`. -/
theorem unramifiedH1_def :
    unramifiedH1 K M =
      (explicitRes1 (AbsoluteGaloisGroup K) M (separableClosureInertiaSubgroup K)).ker :=
  (rfl)

variable {K M}

/-- A class in `H¹(G_K, M)` is unramified if and only if its restriction to
`separableClosureInertiaSubgroup K` vanishes. -/
@[simp]
theorem mem_unramifiedH1_iff {c : H1 (AbsoluteGaloisGroup K) M} :
    c ∈ unramifiedH1 K M ↔
      explicitRes1 (AbsoluteGaloisGroup K) M (separableClosureInertiaSubgroup K) c = 0 :=
  (Iff.rfl)

omit [ContinuousSMul (AbsoluteGaloisGroup K) M] in
/-- A continuous `1`-cocycle of `AbsoluteGaloisGroup K` that vanishes on
`separableClosureInertiaSubgroup K` takes values in the inertia-fixed subgroup `M^{I_K}`. -/
theorem apply_mem_fixedPoints_of_forall_mem_separableClosureInertiaSubgroup
    {f : Z1 (AbsoluteGaloisGroup K) M}
    (hf : ∀ ⦃τ : AbsoluteGaloisGroup K⦄, τ ∈ separableClosureInertiaSubgroup K → f.val τ = 0)
    (g : AbsoluteGaloisGroup K) :
    f.val g ∈ FixedPoints.addSubgroup (separableClosureInertiaSubgroup K) M :=
  coe_descendZ1_apply_mk f (fun τ ↦ hf τ.property) g ▸
    ((descendZ1 f (fun τ ↦ hf τ.property)).val (g : AbsoluteGaloisGroup K ⧸ _)).property

/-- A continuous `1`-cocycle of `AbsoluteGaloisGroup K` that vanishes on
`separableClosureInertiaSubgroup K` represents an unramified cohomology class. -/
theorem mk_mem_unramifiedH1_of_forall_mem_separableClosureInertiaSubgroup
    {f : Z1 (AbsoluteGaloisGroup K) M}
    (hf : ∀ ⦃τ : AbsoluteGaloisGroup K⦄, τ ∈ separableClosureInertiaSubgroup K → f.val τ = 0) :
    (f : H1 (AbsoluteGaloisGroup K) M) ∈ unramifiedH1 K M := by
  rw [mem_unramifiedH1_iff, explicitRes1_mk, H1pi_eq_zero_iff, mem_B1_iff]
  refine ⟨0, fun τ ↦ ?_⟩
  rw [smul_zero, sub_zero, cocyclesMap1_apply, AddMonoidHom.id_apply,
    ContinuousMonoidHom.subgroupSubtype_apply]
  exact (hf τ.property).symm

/-- A continuous `1`-cocycle of `AbsoluteGaloisGroup K` that vanishes on the restriction of
`inertiaSubgroup K` represents an unramified cohomology class. -/
theorem mk_mem_unramifiedH1_of_forall_mem_inertiaSubgroup
    {f : Z1 (AbsoluteGaloisGroup K) M}
    (hf : ∀ ⦃σ : Field.absoluteGaloisGroup K⦄, σ ∈ inertiaSubgroup K →
      f.val (absoluteGaloisGroupRestrictEquiv K σ) = 0) :
    (f : H1 (AbsoluteGaloisGroup K) M) ∈ unramifiedH1 K M := by
  refine mk_mem_unramifiedH1_of_forall_mem_separableClosureInertiaSubgroup fun τ hτ ↦ ?_
  obtain ⟨σ, rfl⟩ := (absoluteGaloisGroupRestrictEquiv K).surjective τ
  exact hf (absoluteGaloisGroupRestrictEquiv_mem_separableClosureInertiaSubgroup_iff.mp hτ)

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

/-- An equivariant additive homeomorphism of topological `G_K`-modules preserves and reflects
unramified first cohomology classes. -/
theorem _root_.AddEquiv.explicitCoeff1Equiv_mem_unramifiedH1_iff {N : Type w} [AddCommGroup N]
    [TopologicalSpace N] [IsTopologicalAddGroup N]
    [DistribMulAction (AbsoluteGaloisGroup K) N] [ContinuousSMul (AbsoluteGaloisGroup K) N]
    (e : M ≃+ N) (he : Continuous e) (he' : Continuous e.symm)
    (hequiv : ∀ (g : AbsoluteGaloisGroup K) (m : M), e (g • m) = g • e m)
    {c : H1 (AbsoluteGaloisGroup K) M} :
    explicitCoeff1Equiv (AbsoluteGaloisGroup K) M e he he' hequiv c ∈ unramifiedH1 K N ↔
      c ∈ unramifiedH1 K M := by
  refine ⟨fun hc ↦ ?_, fun hc ↦ ?_⟩
  · have hc' := DistribMulActionHom.explicitCoeff1_mem_unramifiedH1
      { e.symm.toAddMonoidHom with map_smul' := AddEquiv.symm_map_smul_of_map_smul e hequiv } he' hc
    rwa [← explicitCoeff1Equiv_symm_apply (G := AbsoluteGaloisGroup K) (M := M) e he he' hequiv,
      AddEquiv.symm_apply_apply] at hc'
  · rw [explicitCoeff1Equiv_apply]
    exact DistribMulActionHom.explicitCoeff1_mem_unramifiedH1
      { e.toAddMonoidHom with map_smul' := hequiv } he hc

/-- Pulling `unramifiedH1 K N` back along `explicitCoeff1Equiv` for an equivariant additive
homeomorphism of topological `G_K`-modules recovers `unramifiedH1 K M`. -/
theorem _root_.AddEquiv.unramifiedH1_comap_explicitCoeff1Equiv {N : Type w} [AddCommGroup N]
    [TopologicalSpace N] [IsTopologicalAddGroup N]
    [DistribMulAction (AbsoluteGaloisGroup K) N] [ContinuousSMul (AbsoluteGaloisGroup K) N]
    (e : M ≃+ N) (he : Continuous e) (he' : Continuous e.symm)
    (hequiv : ∀ (g : AbsoluteGaloisGroup K) (m : M), e (g • m) = g • e m) :
    (unramifiedH1 K N).comap
        (explicitCoeff1Equiv (AbsoluteGaloisGroup K) M e he he' hequiv).toAddMonoidHom =
      unramifiedH1 K M := by
  ext c
  exact e.explicitCoeff1Equiv_mem_unramifiedH1_iff he he' hequiv

/-- A bijective equivariant homomorphism of discrete `G_K`-modules preserves and reflects
unramified first cohomology classes. -/
@[simp high]
theorem _root_.DistribMulActionHom.explicitCoeff1_mem_unramifiedH1_iff
    [DiscreteTopology M] {N : Type w} [AddCommGroup N] [TopologicalSpace N] [DiscreteTopology N]
    [DistribMulAction (AbsoluteGaloisGroup K) N] [ContinuousSMul (AbsoluteGaloisGroup K) N]
    (f : M →+[AbsoluteGaloisGroup K] N) (hf : Function.Bijective f)
    {c : H1 (AbsoluteGaloisGroup K) M} :
    explicitCoeff1 (AbsoluteGaloisGroup K) M f continuous_of_discreteTopology c ∈
        unramifiedH1 K N ↔
      c ∈ unramifiedH1 K M := by
  rw [← explicitCoeff1Equiv_ofBijective_apply (AbsoluteGaloisGroup K) M hf c]
  exact (AddEquiv.ofBijective f hf).explicitCoeff1Equiv_mem_unramifiedH1_iff
    continuous_of_discreteTopology continuous_of_discreteTopology (AddEquiv.ofBijective_smul hf)

/-- Pulling `unramifiedH1 K N` back along `explicitCoeff1` for a bijective equivariant homomorphism
of discrete `G_K`-modules recovers `unramifiedH1 K M`. -/
@[simp]
theorem _root_.DistribMulActionHom.unramifiedH1_comap_explicitCoeff1
    [DiscreteTopology M] {N : Type w} [AddCommGroup N] [TopologicalSpace N] [DiscreteTopology N]
    [DistribMulAction (AbsoluteGaloisGroup K) N] [ContinuousSMul (AbsoluteGaloisGroup K) N]
    (f : M →+[AbsoluteGaloisGroup K] N) (hf : Function.Bijective f) :
    (unramifiedH1 K N).comap
        (explicitCoeff1 (AbsoluteGaloisGroup K) M f continuous_of_discreteTopology) =
      unramifiedH1 K M := by
  ext c
  exact f.explicitCoeff1_mem_unramifiedH1_iff hf

/-- **The unramified local condition is cartesian on unramified coefficients.** For a continuous
injective equivariant coefficient map whose target has trivial inertia action, the inverse image
of the target unramified subgroup is exactly the source unramified subgroup. Equivariance and
injectivity also force inertia to act trivially on the source. -/
theorem _root_.DistribMulActionHom.comap_unramifiedH1_of_injective_of_smul_eq_self
    {N : Type w} [AddCommGroup N] [TopologicalSpace N] [IsTopologicalAddGroup N]
    [DistribMulAction (AbsoluteGaloisGroup K) N] [ContinuousSMul (AbsoluteGaloisGroup K) N]
    (f : M →+[AbsoluteGaloisGroup K] N) (hf : Continuous f) (hinj : Function.Injective f)
    (hI : ∀ (g : separableClosureInertiaSubgroup K) (n : N),
      (g : AbsoluteGaloisGroup K) • n = n) :
    (unramifiedH1 K N).comap (explicitCoeff1 (AbsoluteGaloisGroup K) M f hf) =
      unramifiedH1 K M := by
  rw [unramifiedH1_def, unramifiedH1_def]
  exact (separableClosureInertiaSubgroup K).comap_ker_explicitRes1_of_injective_of_smul_eq_self
    f hf hinj hI

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
    τ.map_absoluteGaloisGroupMap_separableClosureInertiaSubgroup_le (mem_unramifiedH1_iff.mp hc)

section Inflation

variable (K M)
  [ContinuousSMul (AbsoluteGaloisGroup K ⧸ separableClosureInertiaSubgroup K)
    (FixedPoints.addSubgroup (separableClosureInertiaSubgroup K) M)]

/-- **The unramified subgroup of `H¹(G_K, M)` is the image of inflation from `G_K ⧸ I_K`.** -/
theorem range_explicitInfl1_eq_unramifiedH1 :
    (explicitInfl1 (AbsoluteGaloisGroup K) M (separableClosureInertiaSubgroup K)).range =
      unramifiedH1 K M := by
  rw [unramifiedH1_def]
  exact explicitInfRes_exact (AbsoluteGaloisGroup K) M _

variable {K M} in
/-- Every class inflated from `H¹(G_K ⧸ I_K, M^{I_K})` is unramified. -/
theorem explicitInfl1_mem_unramifiedH1
    (x : H1 (AbsoluteGaloisGroup K ⧸ separableClosureInertiaSubgroup K)
      (FixedPoints.addSubgroup (separableClosureInertiaSubgroup K) M)) :
    explicitInfl1 (AbsoluteGaloisGroup K) M (separableClosureInertiaSubgroup K) x ∈
      unramifiedH1 K M := by
  rw [← range_explicitInfl1_eq_unramifiedH1]
  exact ⟨x, rfl⟩

/-- **Inflation identifies `H¹(G_K ⧸ I_K, M^{I_K})` with `unramifiedH1 K M`.** -/
def quotientH1AddEquivUnramifiedH1 :
    H1 (AbsoluteGaloisGroup K ⧸ separableClosureInertiaSubgroup K)
        (FixedPoints.addSubgroup (separableClosureInertiaSubgroup K) M) ≃+
      unramifiedH1 K M :=
  (AddMonoidHom.ofInjective
    (explicitInfl1_injective (AbsoluteGaloisGroup K) M (separableClosureInertiaSubgroup K))).trans
    (AddEquiv.addSubgroupCongr (range_explicitInfl1_eq_unramifiedH1 K M))

/-- `quotientH1AddEquivUnramifiedH1` acts as `explicitInfl1` into `H¹(G_K, M)`. -/
@[simp]
theorem coe_quotientH1AddEquivUnramifiedH1_apply
    (x : H1 (AbsoluteGaloisGroup K ⧸ separableClosureInertiaSubgroup K)
      (FixedPoints.addSubgroup (separableClosureInertiaSubgroup K) M)) :
    (quotientH1AddEquivUnramifiedH1 K M x : H1 (AbsoluteGaloisGroup K) M) =
      explicitInfl1 (AbsoluteGaloisGroup K) M (separableClosureInertiaSubgroup K) x :=
  (rfl)

/-- Inflating the preimage of an unramified class under `quotientH1AddEquivUnramifiedH1` recovers
the underlying class in `H¹(G_K, M)`. -/
@[simp]
theorem explicitInfl1_quotientH1AddEquivUnramifiedH1_symm (c : unramifiedH1 K M) :
    explicitInfl1 (AbsoluteGaloisGroup K) M (separableClosureInertiaSubgroup K)
        ((quotientH1AddEquivUnramifiedH1 K M).symm c) =
      (c : H1 (AbsoluteGaloisGroup K) M) := by
  rw [← coe_quotientH1AddEquivUnramifiedH1_apply, AddEquiv.apply_symm_apply]

/-- The inverse of `quotientH1AddEquivUnramifiedH1` recovers a quotient cohomology class from its
inflated unramified class. -/
@[simp]
theorem quotientH1AddEquivUnramifiedH1_symm_mk
    (x : H1 (AbsoluteGaloisGroup K ⧸ separableClosureInertiaSubgroup K)
      (FixedPoints.addSubgroup (separableClosureInertiaSubgroup K) M))
    {hx : explicitInfl1 (AbsoluteGaloisGroup K) M (separableClosureInertiaSubgroup K) x ∈
      unramifiedH1 K M} :
    (quotientH1AddEquivUnramifiedH1 K M).symm ⟨_, hx⟩ = x := by
  apply (quotientH1AddEquivUnramifiedH1 K M).injective
  apply Subtype.ext
  rw [AddEquiv.apply_symm_apply, coe_quotientH1AddEquivUnramifiedH1_apply]

end Inflation

end UnramifiedH1

section CoinvariantsAndCardinality

variable (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  (M : Type v) [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]
  [DistribMulAction (AbsoluteGaloisGroup K) M] [ContinuousSMul (AbsoluteGaloisGroup K) M]
  [DiscreteTopology (FixedPoints.addSubgroup (separableClosureInertiaSubgroup K) M)]

private local instance :
    DistribMulAction zHat.{u} (FixedPoints.addSubgroup (separableClosureInertiaSubgroup K) M) :=
  DistribMulAction.compHom _ (quotientSeparableClosureInertiaSubgroupEquivZHat K).symm.toMonoidHom

private local instance :
    ContinuousSMul zHat.{u} (FixedPoints.addSubgroup (separableClosureInertiaSubgroup K) M) :=
  MulAction.continuousSMul_compHom
    (quotientSeparableClosureInertiaSubgroupEquivZHat K).symm.continuous

/-- Transporting `H¹(G_K ⧸ I_K, M^{I_K})` to `H¹(zHat, M^{I_K})` along
`(quotientSeparableClosureInertiaSubgroupEquivZHat K).symm`. -/
private def quotientH1AddEquivZHatH1 :
    H1 (AbsoluteGaloisGroup K ⧸ separableClosureInertiaSubgroup K)
        (FixedPoints.addSubgroup (separableClosureInertiaSubgroup K) M) ≃+
      H1 zHat.{u} (FixedPoints.addSubgroup (separableClosureInertiaSubgroup K) M) :=
  explicitMap1Equiv _ _ zHat.{u} _
    (quotientSeparableClosureInertiaSubgroupEquivZHat K).symm (AddEquiv.refl _)
    continuous_of_discreteTopology continuous_of_discreteTopology fun z m ↦ by
      rw [AddEquiv.refl_apply, AddEquiv.refl_apply,
        MulAction.compHom_smul_def
          (quotientSeparableClosureInertiaSubgroupEquivZHat K).symm.toMonoidHom]
      rfl

/-- Transporting `unramifiedH1 K M` to `H¹(zHat, M^{I_K})` along
`(quotientSeparableClosureInertiaSubgroupEquivZHat K).symm`. -/
private def unramifiedH1AddEquivZHatH1 :
    unramifiedH1 K M ≃+
      H1 zHat.{u} (FixedPoints.addSubgroup (separableClosureInertiaSubgroup K) M) :=
  (quotientH1AddEquivUnramifiedH1 K M).symm.trans (quotientH1AddEquivZHatH1 K M)

/-- Transporting `H⁰(G_K, M)` to `H⁰(zHat, M^{I_K})` along `explicitInfl0Equiv` and
`(quotientSeparableClosureInertiaSubgroupEquivZHat K).symm`. -/
private def h0AddEquivZHatH0 :
    H0 (AbsoluteGaloisGroup K) M ≃+
      H0 zHat.{u} (FixedPoints.addSubgroup (separableClosureInertiaSubgroup K) M) :=
  let N := FixedPoints.addSubgroup (separableClosureInertiaSubgroup K) M
  let e := quotientSeparableClosureInertiaSubgroupEquivZHat K
  have hequiv0 : ∀ (z : zHat.{u}) (m : N),
      AddMonoidHom.id N (e.symm.toMonoidHom z • m) = z • AddMonoidHom.id N m := fun z m ↦ by
    rw [AddMonoidHom.id_apply, AddMonoidHom.id_apply]
    exact (MulAction.compHom_smul_def e.symm.toMonoidHom z m).symm
  (explicitInfl0Equiv (AbsoluteGaloisGroup K) M (separableClosureInertiaSubgroup K)).symm.trans <|
    AddEquiv.ofBijective
      (explicitMap0 (AbsoluteGaloisGroup K ⧸ separableClosureInertiaSubgroup K) N
        e.symm.toMonoidHom (AddMonoidHom.id N) hequiv0)
      (explicitMap0_bijective (AbsoluteGaloisGroup K ⧸ separableClosureInertiaSubgroup K) N
        e.symm.toMonoidHom e.symm.surjective (AddMonoidHom.id N) Function.bijective_id hequiv0)

/-- **Every torsion inertia-invariant element of `M` is the value at
`unramifiedQuotientFrobenius K` of a continuous `1`-cocycle of `G_K ⧸ I_K`** (whenever `M^{I_K}`
is discrete). -/
theorem exists_apply_unramifiedQuotientFrobenius_eq_of_isOfFinAddOrder
    {m : FixedPoints.addSubgroup (separableClosureInertiaSubgroup K) M} (hm : IsOfFinAddOrder m) :
    ∃ f : Z1 (AbsoluteGaloisGroup K ⧸ separableClosureInertiaSubgroup K)
        (FixedPoints.addSubgroup (separableClosureInertiaSubgroup K) M),
      f.val (unramifiedQuotientFrobenius K) = m := by
  let e := quotientSeparableClosureInertiaSubgroupEquivZHat K
  obtain ⟨f, hf⟩ := zHat.exists_apply_gen_eq_of_isOfFinAddOrder.{u} hm
  refine ⟨cocyclesMap1 zHat.{u} _ _ _ e (AddMonoidHom.id _) continuous_id (fun q x ↦ ?_) f, ?_⟩
  · rw [AddMonoidHom.id_apply, AddMonoidHom.id_apply, ContinuousMonoidHom.coe_coe,
      MulAction.compHom_smul_def e.symm.toMonoidHom]
    exact congrArg (· • x) (e.symm_apply_apply q)
  · rw [cocyclesMap1_apply, AddMonoidHom.id_apply, ContinuousMonoidHom.coe_coe,
      quotientSeparableClosureInertiaSubgroupEquivZHat_unramifiedQuotientFrobenius, hf]

/-- **Unramified `H¹` is the Frobenius coinvariant quotient of `M^{I_K}`**: for a topological
`G_K`-module `M` whose inertia-fixed subgroup `M^{I_K}` is discrete and torsion,
`unramifiedH1 K M ≃+ M^{I_K} ⧸ (Frob_K - 1) M^{I_K}`. -/
def unramifiedH1AddEquivCoinvariants
    (hM : IsAddTorsion (FixedPoints.addSubgroup (separableClosureInertiaSubgroup K) M)) :
    unramifiedH1 K M ≃+
      FixedPoints.addSubgroup (separableClosureInertiaSubgroup K) M ⧸ (frobeniusSubId K M).range :=
  (unramifiedH1AddEquivZHatH1 K M).trans <|
    (zHat.h1AddEquivCoinvariants.{u} _ hM).trans
      (QuotientAddGroup.quotientAddEquivOfEq
        (congrArg AddMonoidHom.range (genSubId_eq_frobeniusSubId K M)))

/-- On a `1`-cocycle `f` of `G_K ⧸ I_K` with values in `M^{I_K}`,
`unramifiedH1AddEquivCoinvariants` sends its inflated unramified class to the coinvariant class of
`f (unramifiedQuotientFrobenius K)`. -/
@[simp]
theorem unramifiedH1AddEquivCoinvariants_quotientH1AddEquivUnramifiedH1_mk
    (hM : IsAddTorsion (FixedPoints.addSubgroup (separableClosureInertiaSubgroup K) M))
    (f : Z1 (AbsoluteGaloisGroup K ⧸ separableClosureInertiaSubgroup K)
      (FixedPoints.addSubgroup (separableClosureInertiaSubgroup K) M)) :
    unramifiedH1AddEquivCoinvariants K M hM
        (quotientH1AddEquivUnramifiedH1 K M (f : H1 _ _)) =
      QuotientAddGroup.mk (f.val (unramifiedQuotientFrobenius K)) := by
  dsimp only [unramifiedH1AddEquivCoinvariants, unramifiedH1AddEquivZHatH1,
    quotientH1AddEquivZHatH1]
  rw [AddEquiv.trans_apply, AddEquiv.trans_apply, AddEquiv.trans_apply,
    AddEquiv.symm_apply_apply, explicitMap1Equiv_apply, zHat.h1AddEquivCoinvariants_apply]
  refine (congrArg (fun x ↦ QuotientAddGroup.quotientAddEquivOfEq _ (zHat.evalGen.{u} _ x))
    (explicitMap1_mk (AbsoluteGaloisGroup K ⧸ separableClosureInertiaSubgroup K) _ zHat.{u} _
      (quotientSeparableClosureInertiaSubgroupEquivZHat K).symm (AddEquiv.refl _).toAddMonoidHom
      continuous_of_discreteTopology _ f)).trans ?_
  rw [zHat.evalGen_mk, QuotientAddGroup.quotientAddEquivOfEq_mk]
  refine congrArg QuotientAddGroup.mk <| (cocyclesMap1_apply _ _ zHat.{u} _
    (quotientSeparableClosureInertiaSubgroupEquivZHat K).symm (AddEquiv.refl _).toAddMonoidHom
    continuous_of_discreteTopology _ f zHat.gen).trans ?_
  rw [AddEquiv.coe_toAddMonoidHom, AddEquiv.refl_apply, ContinuousMonoidHom.coe_coe,
    quotientSeparableClosureInertiaSubgroupEquivZHat_symm_gen]

/-- On the coinvariant class of the Frobenius value of a `1`-cocycle `f` of `G_K ⧸ I_K`,
`(unramifiedH1AddEquivCoinvariants K M hM).symm` recovers the inflated unramified class of `f`. -/
@[simp]
theorem unramifiedH1AddEquivCoinvariants_symm_mk
    (hM : IsAddTorsion (FixedPoints.addSubgroup (separableClosureInertiaSubgroup K) M))
    (f : Z1 (AbsoluteGaloisGroup K ⧸ separableClosureInertiaSubgroup K)
      (FixedPoints.addSubgroup (separableClosureInertiaSubgroup K) M)) :
    (unramifiedH1AddEquivCoinvariants K M hM).symm
        (QuotientAddGroup.mk (f.val (unramifiedQuotientFrobenius K))) =
      quotientH1AddEquivUnramifiedH1 K M (f : H1 _ _) := by
  rw [← unramifiedH1AddEquivCoinvariants_quotientH1AddEquivUnramifiedH1_mk K M hM f,
    AddEquiv.symm_apply_apply]

/-- On a continuous `1`-cocycle `f` of `AbsoluteGaloisGroup K` vanishing on inertia,
`unramifiedH1AddEquivCoinvariants` sends its class to the coinvariant class of
`f (absoluteGaloisGroupRestrictEquiv K σ)` for any arithmetic Frobenius lift `σ`. -/
theorem unramifiedH1AddEquivCoinvariants_mk_of_isArithFrobeniusLift
    (hM : IsAddTorsion (FixedPoints.addSubgroup (separableClosureInertiaSubgroup K) M))
    {f : Z1 (AbsoluteGaloisGroup K) M}
    (hf : ∀ ⦃τ : AbsoluteGaloisGroup K⦄, τ ∈ separableClosureInertiaSubgroup K → f.val τ = 0)
    {hc : (f : H1 (AbsoluteGaloisGroup K) M) ∈ unramifiedH1 K M}
    {σ : Field.absoluteGaloisGroup K} (hσ : IsArithFrobeniusLift K σ) :
    unramifiedH1AddEquivCoinvariants K M hM ⟨(f : H1 (AbsoluteGaloisGroup K) M), hc⟩ =
      QuotientAddGroup.mk
        ⟨f.val (absoluteGaloisGroupRestrictEquiv K σ),
          apply_mem_fixedPoints_of_forall_mem_separableClosureInertiaSubgroup hf _⟩ := by
  have hdesc : (⟨(f : H1 (AbsoluteGaloisGroup K) M), hc⟩ : unramifiedH1 K M) =
      quotientH1AddEquivUnramifiedH1 K M (descendZ1 f (fun τ ↦ hf τ.property) : H1 _ _) := by
    apply Subtype.ext
    rw [coe_quotientH1AddEquivUnramifiedH1_apply, explicitInfl1_descendZ1]
  rw [hdesc, unramifiedH1AddEquivCoinvariants_quotientH1AddEquivUnramifiedH1_mk,
    unramifiedQuotientFrobenius_eq_mk_of_isArithFrobeniusLift hσ]
  congr 1
  exact Subtype.ext
    (coe_descendZ1_apply_mk f (fun τ ↦ hf τ.property) (absoluteGaloisGroupRestrictEquiv K σ))

/-- On the coinvariant class of `f (absoluteGaloisGroupRestrictEquiv K σ)` for an arithmetic
Frobenius lift `σ` and a continuous `1`-cocycle `f` vanishing on inertia,
`(unramifiedH1AddEquivCoinvariants K M hM).symm` recovers the unramified class of `f`. -/
theorem unramifiedH1AddEquivCoinvariants_symm_mk_of_isArithFrobeniusLift
    (hM : IsAddTorsion (FixedPoints.addSubgroup (separableClosureInertiaSubgroup K) M))
    {f : Z1 (AbsoluteGaloisGroup K) M}
    (hf : ∀ ⦃τ : AbsoluteGaloisGroup K⦄, τ ∈ separableClosureInertiaSubgroup K → f.val τ = 0)
    {hc : (f : H1 (AbsoluteGaloisGroup K) M) ∈ unramifiedH1 K M}
    {σ : Field.absoluteGaloisGroup K} (hσ : IsArithFrobeniusLift K σ) :
    (unramifiedH1AddEquivCoinvariants K M hM).symm
        (QuotientAddGroup.mk
          ⟨f.val (absoluteGaloisGroupRestrictEquiv K σ),
            apply_mem_fixedPoints_of_forall_mem_separableClosureInertiaSubgroup hf _⟩) =
      ⟨(f : H1 (AbsoluteGaloisGroup K) M), hc⟩ := by
  rw [← unramifiedH1AddEquivCoinvariants_mk_of_isArithFrobeniusLift K M hM hf (hc := hc) hσ,
    AddEquiv.symm_apply_apply]

/-- **Frobenius order formula for unramified cohomology.** For any topological `G_K`-module `M`
whose inertia-fixed subgroup `M^{I_K}` is discrete and finite (in particular for every finite
discrete `G_K`-module `M`, or every `T₁` `G_K`-module with finite `M^{I_K}`, with no
unramifiedness or residue-characteristic assumption), `#unramifiedH1 K M = #H⁰(G_K, M)`. -/
theorem natCard_unramifiedH1_eq_natCard_H0
    [Finite (FixedPoints.addSubgroup (separableClosureInertiaSubgroup K) M)] :
    Nat.card (unramifiedH1 K M) = Nat.card (H0 (AbsoluteGaloisGroup K) M) :=
  calc
    Nat.card (unramifiedH1 K M) = Nat.card (H1 zHat.{u} _) :=
      Nat.card_congr (unramifiedH1AddEquivZHatH1 K M).toEquiv
    _ = Nat.card (H0 zHat.{u} _) := zHat.natCard_H1_eq_natCard_H0.{u} _
    _ = Nat.card (H0 (AbsoluteGaloisGroup K) M) :=
      Nat.card_congr (h0AddEquivZHatH0 K M).symm.toEquiv

/-- **Unramified `H¹` is finite** for every topological `G_K`-module `M` whose inertia-fixed
subgroup `M^{I_K}` is discrete and finite (in particular for every finite discrete `G_K`-module
`M`). -/
instance finite_unramifiedH1
    [Finite (FixedPoints.addSubgroup (separableClosureInertiaSubgroup K) M)] :
    Finite (unramifiedH1 K M) := by
  have : Finite (H0 (AbsoluteGaloisGroup K) M) :=
    Finite.of_equiv _
      (explicitInfl0Equiv (AbsoluteGaloisGroup K) M (separableClosureInertiaSubgroup K)).toEquiv
  exact Nat.finite_of_card_ne_zero
    ((natCard_unramifiedH1_eq_natCard_H0 K M).trans_ne Nat.card_pos.ne')

/-- **If a topological `G_K`-module with discrete finite `M^{I_K}` has trivial `G_K`-invariants,
its unramified `H¹` vanishes.** -/
theorem subsingleton_unramifiedH1_of_subsingleton_H0
    [Finite (FixedPoints.addSubgroup (separableClosureInertiaSubgroup K) M)]
    [Subsingleton (H0 (AbsoluteGaloisGroup K) M)] :
    Subsingleton (unramifiedH1 K M) := by
  let N := FixedPoints.addSubgroup (separableClosureInertiaSubgroup K) M
  have _ : Subsingleton (H0 zHat.{u} N) := (h0AddEquivZHatH0 K M).symm.toEquiv.subsingleton
  have _ : Subsingleton (H1 zHat.{u} N) := zHat.subsingleton_H1_of_subsingleton_H0.{u} N
  exact (unramifiedH1AddEquivZHatH1 K M).toEquiv.subsingleton

end CoinvariantsAndCardinality

section CupProduct

variable {K : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

/-- **`H²(G_K ⧸ I_K, N)` vanishes** for every profinite abelian group `N` with a continuous action
of the unramified quotient `G_K ⧸ I_K`, since `G_K ⧸ I_K ≃ₜ* zHat`. -/
instance subsingleton_H2_quotient_separableClosureInertiaSubgroup {N : Type v} [AddCommGroup N]
    [TopologicalSpace N] [IsTopologicalAddGroup N] [CompactSpace N] [TotallyDisconnectedSpace N]
    [DistribMulAction (AbsoluteGaloisGroup K ⧸ separableClosureInertiaSubgroup K) N]
    [ContinuousSMul (AbsoluteGaloisGroup K ⧸ separableClosureInertiaSubgroup K) N] :
    Subsingleton (H2 (AbsoluteGaloisGroup K ⧸ separableClosureInertiaSubgroup K) N) := by
  let e := quotientSeparableClosureInertiaSubgroupEquivZHat K
  let _ : DistribMulAction zHat.{u} N := DistribMulAction.compHom N e.symm.toMonoidHom
  have _ : ContinuousSMul zHat.{u} N := MulAction.continuousSMul_compHom e.symm.continuous
  exact (explicitMap2Equiv (AbsoluteGaloisGroup K ⧸ separableClosureInertiaSubgroup K) N zHat.{u} N
    e.symm (AddEquiv.refl N) continuous_id continuous_id fun z m ↦ by
      rw [AddEquiv.refl_apply, AddEquiv.refl_apply, MulAction.compHom_smul_def e.symm.toMonoidHom]
      rfl).toEquiv.subsingleton

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
    [ContinuousSMul (AbsoluteGaloisGroup K ⧸ separableClosureInertiaSubgroup K)
      (FixedPoints.addSubgroup (separableClosureInertiaSubgroup K) A)]
    [ContinuousSMul (AbsoluteGaloisGroup K ⧸ separableClosureInertiaSubgroup K)
      (FixedPoints.addSubgroup (separableClosureInertiaSubgroup K) B)]
    [ContinuousSMul (AbsoluteGaloisGroup K ⧸ separableClosureInertiaSubgroup K)
      (FixedPoints.addSubgroup (separableClosureInertiaSubgroup K) P)]
    [Subsingleton (H2 (AbsoluteGaloisGroup K ⧸ separableClosureInertiaSubgroup K)
      (FixedPoints.addSubgroup (separableClosureInertiaSubgroup K) P))]
    (μ : A →+ B →+ P) (hμ : Continuous fun p : A × B ↦ μ p.1 p.2)
    (hequiv : ∀ (g : AbsoluteGaloisGroup K) (x : A) (y : B), μ (g • x) (g • y) = g • μ x y)
    {a : H1 (AbsoluteGaloisGroup K) A} {b : H1 (AbsoluteGaloisGroup K) B}
    (ha : a ∈ unramifiedH1 K A) (hb : b ∈ unramifiedH1 K B) :
    explicitCup11 (AbsoluteGaloisGroup K) A B P μ hμ hequiv a b = 0 := by
  obtain ⟨a₀, rfl⟩ := (range_explicitInfl1_eq_unramifiedH1 K A).symm ▸ ha
  obtain ⟨b₀, rfl⟩ := (range_explicitInfl1_eq_unramifiedH1 K B).symm ▸ hb
  rw [← explicitInfl2_explicitCup11 _ A B P (separableClosureInertiaSubgroup K) μ hμ hequiv a₀ b₀,
    Subsingleton.elim (explicitCup11 _ _ _ _ _ _ _ a₀ b₀) 0, map_zero]

end CupProduct

/-- **A continuous 1-cocycle vanishing on inertia and at a Frobenius lift vanishes identically.**
No torsion or wild-inertia hypothesis is needed; only `T₁` on the coefficient module. -/
theorem eq_zero_of_apply_inertiaSubgroup_eq_zero_of_isArithFrobeniusLift {K : Type} [Field K]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] {M : Type*}
    [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M] [T1Space M]
    [DistribMulAction (Field.absoluteGaloisGroup K) M]
    (c : Z1 (Field.absoluteGaloisGroup K) M) {σ : Field.absoluteGaloisGroup K}
    (hσ : IsArithFrobeniusLift K σ)
    (hI : ∀ g ∈ inertiaSubgroup K, (c : Field.absoluteGaloisGroup K → M) g = 0)
    (hσ0 : (c : Field.absoluteGaloisGroup K → M) σ = 0) :
    c = 0 := by
  have hc := mem_Z1_iff.1 c.property
  have htop : (Subgroup.closure ({σ} ∪ (inertiaSubgroup K : Set _))).topologicalClosure = ⊤ := by
    rw [Subgroup.closure_union, ← Subgroup.zpowers_eq_closure, Subgroup.closure_eq]
    exact hσ.topologicalClosure_zpowers_sup_inertiaSubgroup
  refine Subtype.ext (groupCohomology.eq_zero_of_eqOn_zero_of_topologicalClosure_closure_eq_top
    hc.2 hc.1 htop ?_)
  rintro g (rfl | hg)
  · exact hσ0
  · exact hI g hg

end TauCeti
