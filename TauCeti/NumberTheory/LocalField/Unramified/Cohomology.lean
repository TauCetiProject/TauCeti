/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.Unramified.Inertia.SeparableClosure
public import TauCeti.NumberTheory.LocalField.Unramified.ZHat
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Cup.Inflation
import TauCeti.Topology.Algebra.Group.Profinite.ZHat.FirstCohomology

/-!
# Unramified Galois cohomology of a nonarchimedean local field

Let `K` be a nonarchimedean local field with absolute Galois group
`G_K = TauCeti.AbsoluteGaloisGroup K = Gal(Kˢ/K)` and inertia subgroup `I_K`, transported from
`Gal(K^{alg}/K)` along `TauCeti.absoluteGaloisGroupRestrictEquiv K`. For a continuous `G_K`-module
`M`, the **unramified first cohomology** `TauCeti.unramifiedCohomology K M ≤ H¹(G_K, M)` is the
kernel of restriction to inertia.

By exactness of the inflation-restriction sequence in degree one
(`TauCeti.ContCohomology.explicitInfRes_exact`), inflation identifies `H¹(G_K ⧸ I_K, M^{I_K})`
with `unramifiedCohomology K M` whenever `M` is discrete (`TauCeti.unramifiedCohomologyEquiv`).
Since the unramified quotient `G_K ⧸ I_K` is topologically isomorphic to the profinite integers
`ℤ̂` (`TauCeti.quotientInertiaSepClosureEquivZHat`), the procyclic cohomology calculations of
`TauCeti.Topology.Algebra.Group.Profinite.ZHat.FirstCohomology` yield two fundamental arithmetic
consequences whenever the inertia invariants `M^{I_K}` (or `P^{I_K}`) are finite:

1. **Cardinality of unramified `H¹`** (`TauCeti.natCard_unramifiedCohomology_eq_natCard_H0`):
   `#H¹_ur(G_K, M) = #H⁰(G_K, M)`.
2. **Isotropy of the cup product on unramified classes**
   (`TauCeti.explicitCup11_eq_zero_of_mem_unramifiedCohomology`): for any `G_K`-equivariant
   biadditive pairing `M × A → P` of discrete `G_K`-modules with `P^{I_K}` finite, the cup product
   of two unramified classes vanishes in `H²(G_K, P)`, because it inflates from
   `H²(G_K ⧸ I_K, P^{I_K}) = 0`.

## Main definitions

* `TauCeti.quotientInertiaSepClosureEquivZHat`: the isomorphism of topological groups
  `G_K ⧸ I_K ≃ₜ* ℤ̂` at the separable closure.
* `TauCeti.unramifiedCohomology`: the subgroup `ker(res : H¹(G_K, M) → H¹(I_K, M))` of unramified
  cohomology classes.
* `TauCeti.unramifiedCohomologyEquiv`: inflation as an additive equivalence
  `H¹(G_K ⧸ I_K, M^{I_K}) ≃+ unramifiedCohomology K M` for discrete `M`.

## Main results

* `TauCeti.explicitMap1_mem_unramifiedCohomology`,
  `TauCeti.explicitCoeff1_mem_unramifiedCohomology`: functoriality of unramified classes along
  extensions of local fields and equivariant coefficient maps.
* `TauCeti.finite_unramifiedCohomology`, `TauCeti.natCard_unramifiedCohomology_eq_natCard_H0`:
  `H¹_ur(G_K, M)` is finite of cardinality `#H⁰(G_K, M)` whenever `M^{I_K}` is finite.
* `TauCeti.explicitCup11_eq_zero_of_mem_unramifiedCohomology`: the `(1, 1)` cup product vanishes on
  pairs of unramified classes whenever `P^{I_K}` is finite.

## References

* J. S. Milne, *Arithmetic Duality Theorems*, 2nd ed., Chapter I, Lemma 2.5 and proof of
  Theorem 2.6.
* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., (7.2.14)–(7.2.15).
-/

public section

noncomputable section

namespace TauCeti

open ContCohomology

universe u v w

/-! ### The unramified quotient at the separable closure -/

section Quotient

variable (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

/-- The image of the inertia subgroup in `AbsoluteGaloisGroup K = Gal(Kˢ/K)` is normal. -/
instance inertiaSubgroup_map_normal :
    ((inertiaSubgroup K).map (absoluteGaloisGroupRestrictEquiv K).toMonoidHom).Normal :=
  Subgroup.Normal.map (inertiaSubgroup_normal K) _ (absoluteGaloisGroupRestrictEquiv K).surjective

/-- **The unramified quotient of `AbsoluteGaloisGroup K` is `ℤ̂`.** Transporting the inertia
subgroup from `Gal(K^{alg}/K)` to `Gal(Kˢ/K)` and composing with restriction to `K^{ur}` gives a
continuous multiplicative equivalence with the profinite integers. -/
def quotientInertiaSepClosureEquivZHat :
    AbsoluteGaloisGroup K ⧸
        ((inertiaSubgroup K).map (absoluteGaloisGroupRestrictEquiv K).toMonoidHom) ≃ₜ*
      zHat.{u} :=
  ((absoluteGaloisGroupRestrictEquiv K).quotientCongr (inertiaSubgroup K)
    ((inertiaSubgroup K).map (absoluteGaloisGroupRestrictEquiv K).toMonoidHom) rfl).symm.trans
    ((quotientInertiaSubgroupEquiv K).trans
      (maximalUnramifiedGaloisGroupEquivZHat K (AlgebraicClosure K)))

end Quotient

/-! ### Unramified first cohomology and its functoriality -/

section Basic

variable (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  (M : Type v) [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]
  [DistribMulAction (AbsoluteGaloisGroup K) M] [ContinuousSMul (AbsoluteGaloisGroup K) M]

/-- **Unramified first Galois cohomology** `H¹_ur(G_K, M)` of a nonarchimedean local field `K`:
the kernel of restriction from `AbsoluteGaloisGroup K` to its inertia subgroup. -/
def unramifiedCohomology : AddSubgroup (H1 (AbsoluteGaloisGroup K) M) :=
  (explicitRes1 (AbsoluteGaloisGroup K) M
    ((inertiaSubgroup K).map (absoluteGaloisGroupRestrictEquiv K).toMonoidHom)).ker

variable {K M}

/-- A class in `H¹(G_K, M)` is unramified if and only if its restriction to inertia vanishes. -/
@[simp]
theorem mem_unramifiedCohomology_iff {c : H1 (AbsoluteGaloisGroup K) M} :
    c ∈ unramifiedCohomology K M ↔
      explicitRes1 (AbsoluteGaloisGroup K) M
        ((inertiaSubgroup K).map (absoluteGaloisGroupRestrictEquiv K).toMonoidHom) c = 0 :=
  (Iff.rfl)

/-- **Unramified classes pull back to unramified classes** along an extension `L/K` of
nonarchimedean local fields, an embedding `τ : Kˢ →ₐ[K] Lˢ`, and a compatible continuous
coefficient homomorphism `f : M →+ N`. -/
theorem explicitMap1_mem_unramifiedCohomology
    {L : Type w} [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra K L] [ValuativeExtension K L] (τ : SeparableClosure K →ₐ[K] SeparableClosure L)
    {N : Type*} [AddCommGroup N] [TopologicalSpace N] [IsTopologicalAddGroup N]
    [DistribMulAction (AbsoluteGaloisGroup L) N] [ContinuousSMul (AbsoluteGaloisGroup L) N]
    (f : M →+ N) (hf : Continuous f)
    (hequiv : ∀ (g : AbsoluteGaloisGroup L) (m : M), f (absoluteGaloisGroupMap τ g • m) = g • f m)
    {c : H1 (AbsoluteGaloisGroup K) M} (hc : c ∈ unramifiedCohomology K M) :
    explicitMap1 (AbsoluteGaloisGroup K) M (AbsoluteGaloisGroup L) N
      (absoluteGaloisGroupMap τ) f hf hequiv c ∈ unramifiedCohomology L N :=
  (absoluteGaloisGroupMap τ).explicitRes1_explicitMap1_eq_zero_of_map_le f hf hequiv
    τ.map_absoluteGaloisGroupMap_inertiaSubgroup_le hc

/-- Continuous `G_K`-equivariant coefficient maps preserve unramified cohomology classes. -/
theorem explicitCoeff1_mem_unramifiedCohomology
    {N : Type*} [AddCommGroup N] [TopologicalSpace N] [IsTopologicalAddGroup N]
    [DistribMulAction (AbsoluteGaloisGroup K) N] [ContinuousSMul (AbsoluteGaloisGroup K) N]
    (f : M →+[AbsoluteGaloisGroup K] N) (hf : Continuous f)
    {c : H1 (AbsoluteGaloisGroup K) M} (hc : c ∈ unramifiedCohomology K M) :
    explicitCoeff1 (AbsoluteGaloisGroup K) M f hf c ∈ unramifiedCohomology K N := by
  rw [mem_unramifiedCohomology_iff, explicitCoeff1_eq_explicitMap1]
  exact (ContinuousMonoidHom.id _).explicitRes1_explicitMap1_eq_zero_of_map_le _ _ _
    (fun _ ⟨_, hg, h⟩ ↦ h ▸ hg) hc

/-- A bijective equivariant map of discrete `G_K`-modules preserves and reflects unramified
first cohomology classes. -/
theorem explicitCoeff1_mem_unramifiedCohomology_iff_of_bijective [DiscreteTopology M]
    {N : Type*} [AddCommGroup N] [TopologicalSpace N] [DiscreteTopology N]
    [DistribMulAction (AbsoluteGaloisGroup K) N] [ContinuousSMul (AbsoluteGaloisGroup K) N]
    (f : M →+[AbsoluteGaloisGroup K] N) (hf : Function.Bijective f)
    {c : H1 (AbsoluteGaloisGroup K) M} :
    explicitCoeff1 (AbsoluteGaloisGroup K) M f continuous_of_discreteTopology c ∈
      unramifiedCohomology K N ↔ c ∈ unramifiedCohomology K M := by
  refine ⟨fun hc ↦ ?_, explicitCoeff1_mem_unramifiedCohomology f continuous_of_discreteTopology⟩
  let e := AddEquiv.ofBijective f hf
  let fInv : N →+[AbsoluteGaloisGroup K] M :=
    { toFun := e.symm
      map_zero' := map_zero e.symm
      map_add' := map_add e.symm
      map_smul' := fun g y ↦ e.injective <| by
        rw [e.apply_symm_apply, MonoidHom.id_apply, AddEquiv.ofBijective_apply, map_smul]
        exact congrArg (g • ·)
          ((e.apply_symm_apply y).symm.trans (AddEquiv.ofBijective_apply f hf _)) }
  have hcomp : fInv.comp f = DistribMulActionHom.id _ :=
    DistribMulActionHom.ext fun x ↦ e.symm_apply_apply x
  have hc' := explicitCoeff1_mem_unramifiedCohomology fInv continuous_of_discreteTopology hc
  rwa [← AddMonoidHom.comp_apply,
    ← explicitCoeff1_comp (AbsoluteGaloisGroup K) M f fInv
      continuous_of_discreteTopology continuous_of_discreteTopology,
    congrArg (fun g ↦ explicitCoeff1 (AbsoluteGaloisGroup K) M g continuous_of_discreteTopology)
      hcomp,
    explicitCoeff1_id, AddMonoidHom.id_apply] at hc'

end Basic

/-! ### Inflation equivalence, cardinality, and cup-product vanishing -/

section Discrete

variable (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  (M : Type v) [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
  [DistribMulAction (AbsoluteGaloisGroup K) M] [ContinuousSMul (AbsoluteGaloisGroup K) M]

/-- For a discrete `G_K`-module `M`, the unramified subgroup of `H¹(G_K, M)` is the image of
inflation from `G_K ⧸ I_K` with coefficients in `M^{I_K}`. -/
theorem range_explicitInfl1_eq_unramifiedCohomology :
    (explicitInfl1 (AbsoluteGaloisGroup K) M
      ((inertiaSubgroup K).map (absoluteGaloisGroupRestrictEquiv K).toMonoidHom)).range =
      unramifiedCohomology K M :=
  explicitInfRes_exact (AbsoluteGaloisGroup K) M _

/-- **Inflation identifies `H¹(G_K ⧸ I_K, M^{I_K})` with `unramifiedCohomology K M`** for every
discrete `G_K`-module `M`. -/
def unramifiedCohomologyEquiv :
    H1 (AbsoluteGaloisGroup K ⧸
        ((inertiaSubgroup K).map (absoluteGaloisGroupRestrictEquiv K).toMonoidHom))
      (FixedPoints.addSubgroup
        ((inertiaSubgroup K).map (absoluteGaloisGroupRestrictEquiv K).toMonoidHom) M) ≃+
      unramifiedCohomology K M :=
  AddEquiv.ofBijective
    ((explicitInfl1 (AbsoluteGaloisGroup K) M
        ((inertiaSubgroup K).map (absoluteGaloisGroupRestrictEquiv K).toMonoidHom)).codRestrict
      (unramifiedCohomology K M) fun x ↦
        range_explicitInfl1_eq_unramifiedCohomology K M ▸ ⟨x, rfl⟩)
    ⟨fun _ _ h ↦ explicitInfl1_injective (AbsoluteGaloisGroup K) M _ (congrArg Subtype.val h),
     fun ⟨_, hy⟩ ↦ by
      obtain ⟨x, hx⟩ := (range_explicitInfl1_eq_unramifiedCohomology K M).symm ▸ hy
      exact ⟨x, Subtype.ext hx⟩⟩

/-- `unramifiedCohomologyEquiv` acts by degree-one inflation into `H¹(G_K, M)`. -/
theorem coe_unramifiedCohomologyEquiv_apply
    (x : H1 (AbsoluteGaloisGroup K ⧸
        ((inertiaSubgroup K).map (absoluteGaloisGroupRestrictEquiv K).toMonoidHom))
      (FixedPoints.addSubgroup
        ((inertiaSubgroup K).map (absoluteGaloisGroupRestrictEquiv K).toMonoidHom) M)) :
    (unramifiedCohomologyEquiv K M x : H1 (AbsoluteGaloisGroup K) M) =
      explicitInfl1 (AbsoluteGaloisGroup K) M
        ((inertiaSubgroup K).map (absoluteGaloisGroupRestrictEquiv K).toMonoidHom) x :=
  (rfl)

/-- **Finiteness of unramified `H¹`.** For any discrete `G_K`-module `M` whose inertia invariants
`M^{I_K}` are finite (in particular for any finite discrete `M`), `unramifiedCohomology K M` is
finite. -/
instance finite_unramifiedCohomology
    [Finite (FixedPoints.addSubgroup
      ((inertiaSubgroup K).map (absoluteGaloisGroupRestrictEquiv K).toMonoidHom) M)] :
    Finite (unramifiedCohomology K M) := by
  have := zHat.finite_H1_of_continuousMulEquiv
    (FixedPoints.addSubgroup
      ((inertiaSubgroup K).map (absoluteGaloisGroupRestrictEquiv K).toMonoidHom) M)
    (quotientInertiaSepClosureEquivZHat K)
  exact Finite.of_equiv _ (unramifiedCohomologyEquiv K M).toEquiv

/-- **Order of unramified `H¹` (Milne, *ADT* I, Lemma 2.5; NSW (7.2.14)).** For any discrete
`G_K`-module `M` whose inertia invariants `M^{I_K}` are finite (in particular for any finite
discrete `M`), `#H¹_ur(G_K, M) = #H⁰(G_K, M)`. -/
theorem natCard_unramifiedCohomology_eq_natCard_H0
    [Finite (FixedPoints.addSubgroup
      ((inertiaSubgroup K).map (absoluteGaloisGroupRestrictEquiv K).toMonoidHom) M)] :
    Nat.card (unramifiedCohomology K M) = Nat.card (H0 (AbsoluteGaloisGroup K) M) := by
  rw [← Nat.card_congr (unramifiedCohomologyEquiv K M).toEquiv,
    zHat.natCard_H1_eq_natCard_H0_of_continuousMulEquiv
      (FixedPoints.addSubgroup
        ((inertiaSubgroup K).map (absoluteGaloisGroupRestrictEquiv K).toMonoidHom) M)
      (quotientInertiaSepClosureEquivZHat K)]
  exact Nat.card_congr (explicitInfl0Equiv (AbsoluteGaloisGroup K) M _).toEquiv

variable {K M}

/-- **Cup products of unramified classes vanish.** Let `M × A → P` be a `G_K`-equivariant
biadditive pairing of discrete `G_K`-modules whose target has finite inertia invariants `P^{I_K}`
(for instance when `P` is finite). For any `x ∈ H¹_ur(G_K, M)` and `y ∈ H¹_ur(G_K, A)`, the cup
product `x ⌣ y ∈ H²(G_K, P)` vanishes because it inflates from `H²(G_K ⧸ I_K, P^{I_K}) = 0`. -/
theorem explicitCup11_eq_zero_of_mem_unramifiedCohomology
    {A : Type*} [AddCommGroup A] [TopologicalSpace A] [DiscreteTopology A]
    [DistribMulAction (AbsoluteGaloisGroup K) A] [ContinuousSMul (AbsoluteGaloisGroup K) A]
    {P : Type*} [AddCommGroup P] [TopologicalSpace P] [DiscreteTopology P]
    [DistribMulAction (AbsoluteGaloisGroup K) P] [ContinuousSMul (AbsoluteGaloisGroup K) P]
    [Finite (FixedPoints.addSubgroup
      ((inertiaSubgroup K).map (absoluteGaloisGroupRestrictEquiv K).toMonoidHom) P)]
    (μ : M →+ A →+ P) (hμ : Continuous fun p : M × A => μ p.1 p.2)
    (hequiv : ∀ (g : AbsoluteGaloisGroup K) (m : M) (a : A), μ (g • m) (g • a) = g • μ m a)
    {x : H1 (AbsoluteGaloisGroup K) M} (hx : x ∈ unramifiedCohomology K M)
    {y : H1 (AbsoluteGaloisGroup K) A} (hy : y ∈ unramifiedCohomology K A) :
    explicitCup11 (AbsoluteGaloisGroup K) M A P μ hμ hequiv x y = 0 := by
  obtain ⟨x₀, rfl⟩ := (range_explicitInfl1_eq_unramifiedCohomology K M).symm ▸ hx
  obtain ⟨y₀, rfl⟩ := (range_explicitInfl1_eq_unramifiedCohomology K A).symm ▸ hy
  rw [← explicitInfl2_explicitCup11]
  have : Subsingleton
      (H2 (AbsoluteGaloisGroup K ⧸
          ((inertiaSubgroup K).map (absoluteGaloisGroupRestrictEquiv K).toMonoidHom))
        (FixedPoints.addSubgroup
          ((inertiaSubgroup K).map (absoluteGaloisGroupRestrictEquiv K).toMonoidHom) P)) :=
    zHat.subsingleton_H2_of_continuousMulEquiv _ (quotientInertiaSepClosureEquivZHat K)
  exact (congrArg _ (Subsingleton.elim _ 0)).trans (map_zero _)

end Discrete

end TauCeti
