/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck, The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.GroupAction.ConjAct
public import Mathlib.MeasureTheory.Group.FundamentalDomain
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure

/-!
# Fundamental domains for subgroups by coset tiling

If `s` is a fundamental domain for a group `G` acting on `α`, a subgroup `H ≤ G` with
countable coset space has the `[G : H]`-fold tiling `⋃ q : G ⧸ H, (q.out)⁻¹ • s` as a
fundamental domain. This is how a fundamental domain for a finite-index subgroup (a
congruence subgroup, say) is manufactured from a fundamental domain of the ambient group;
countability of `G ⧸ H` — automatic at finite index — is what makes the tiling a countable
union.

In the other direction, a set whose translates tile the space with disjoint interiors, overlapping
only along a null frontier, is itself a fundamental domain.

## Main results

* `MeasureTheory.IsFundamentalDomain.iUnion_smul_of_transversal`: for any family `r : ι → G`
  with `i ↦ ⟦(r i)⁻¹⟧` bijective onto `G ⧸ H`, the tiling `⋃ i, r i • s` is an
  `H`-fundamental domain.
* `MeasureTheory.IsFundamentalDomain.subgroup_iUnion_out_inv_smul`: the special case of the
  canonical representatives, `⋃ q : G ⧸ H, (q.out)⁻¹ • s`.
* `MeasureTheory.IsFundamentalDomain.smul_of_eq_conjAct_pointwise_smul`: an `H₁`-fundamental domain
  translates to a `g H₁ g⁻¹`-fundamental domain under `g`.
* `MeasureTheory.isFundamentalDomain_subgroupOf_iff`: a fundamental domain for `H.subgroupOf K`
  is the same as one for `H ⊓ K`, the two subgroups being the same elements acting the same way.
* `MeasureTheory.IsFundamentalDomain.iUnion_mul_smul_of_transversal`: the **double-coset
  tiling**, at an arbitrary transversal — for any `r : ι → Γ₂` with `i ↦ ⟦(r i)⁻¹⟧` bijective
  onto `Γ₂ ⧸ (δ⁻¹Γ₁δ ⊓ Γ₂)`, the translates `⋃ i, (δ · r i) • s` tile a fundamental domain for
  `Γ₁ ⊓ δΓ₂δ⁻¹`.
* `MeasureTheory.IsFundamentalDomain.iUnion_mul_out_inv_smul`: the same at the canonical
  `Quotient.out` representatives, `⋃ᵥ (δ σᵥ⁻¹) • s` over `Γ₂ ⧸ (δ⁻¹Γ₁δ ⊓ Γ₂)`. A Hecke operator
  supplies its own representatives rather than `Quotient.out`'s, so it is the transversal form
  above that applies there.
* `MeasureTheory.IsFundamentalDomain.aedisjoint_smul_of_inv_mul_mem`: translates `g₁ • D`,
  `g₂ • D` of an `H`-fundamental domain are a.e. disjoint whenever `g₁ ≠ g₂` and
  `g₁⁻¹ * g₂ ∈ H` (needing only quasi-measure-preservation of the one translation).
* `MeasureTheory.IsFundamentalDomain.of_disjoint_smul_interior`: a null-measurable set with null
  translated frontiers, whose translates cover almost everything and have pairwise disjoint
  interiors, is a fundamental domain. This is how a closed tile of a tessellation, such
  as a fundamental polygon, becomes a measurable fundamental domain.
* `MeasureTheory.IsFundamentalDomain.congr_set`: a set a.e. equal to a fundamental domain is one.
* `MeasureTheory.IsFundamentalDomain.measure_le_of_aedisjoint_smul`: a set a.e. disjoint from its
  nonidentity translates has measure at most that of a fundamental domain.
* `MeasureTheory.IsFundamentalDomain.measure_le_of_subset_iUnion_smul`: a fundamental domain has
  measure at most that of any set whose translates cover it.
* `MeasureTheory.IsFundamentalDomain.hasSum_setIntegral_of_ac`,
  `MeasureTheory.IsFundamentalDomain.hasSum_setIntegral`,
  `MeasureTheory.IsFundamentalDomain.hasSum_setIntegral_smul`: `HasSum` decomposition of Bochner
  integrals over the translates of a fundamental domain, upgrading Mathlib's `integral_eq_tsum`
  family.
* `MeasureTheory.covolume_pos`, `MeasureTheory.covolume_conjAct_smul`,
  `MeasureTheory.covolume_eq_card_mul_covolume`: for an invariant measure the covolume is
  positive, invariant under conjugation, and multiplied by the index on passing to a subgroup.
* `MeasureTheory.covolume_eq_index_mul_covolume`: the same multiplicativity at finite index, with
  the index as a natural number.
* `MeasureTheory.covolume_smul_measure`: for an invariant measure, scaling the measure by `c`
  scales the covolume by `c`.

Ported from the
[AINTLIB `LeanModularForms` project](https://github.com/CBirkbeck/AINTLIB/tree/main/projects/LeanModularForms),
`projects/LeanModularForms/Modularforms/PeterssonLevelN.lean` (measure-theory section), as a
prerequisite for fundamental domains of congruence subgroups.
-/

public section

namespace MeasureTheory

open Measure Set

open scoped ENNReal Pointwise

/-- **Transversal coset tiling of a fundamental domain.** If `s` is a fundamental domain
for a group `G` acting on `α`, `H ≤ G` a subgroup, and `r : ι → G` a family such that
`i ↦ ⟦(r i)⁻¹⟧` enumerates the left cosets `G ⧸ H` bijectively, then `⋃ i, r i • s` is a
fundamental domain for the restricted `H`-action. The inverses make `r` a *right*
transversal: each `x ∈ G` factors as `h * r i` with `h ∈ H` for exactly one `i`.

The index type must be countable (`[Countable ι]`), so that the tiling is a countable union.
Beyond that, the *only* measure-theoretic hypothesis is null-measurability of the individual
translates `r i • s`: measurability and invariance of the whole ambient action are not needed.
`subgroup_iUnion_out_inv_smul` is the convenience form that supplies `hnull` from
`[MeasurableConstSMul G α]` and `[SMulInvariantMeasure G α μ]`. -/
@[to_additive /-- **Transversal coset tiling of a fundamental domain.** If `s` is a fundamental
domain for an additive group `G` acting on `α`, `H ≤ G` a subgroup, and `r : ι → G` a family
over a **countable** index type (`[Countable ι]`) such that `i ↦ ⟦-(r i)⟧` enumerates the
cosets `G ⧸ H` bijectively, then `⋃ i, r i +ᵥ s` is a fundamental domain for the restricted
`H`-action. Beyond countability the only measure-theoretic hypothesis is null-measurability
of the individual translates `r i +ᵥ s`. -/]
theorem IsFundamentalDomain.iUnion_smul_of_transversal
    {G α ι : Type*} [Group G] [MeasurableSpace α] [MulAction G α] [Countable ι]
    {μ : Measure α}
    {H : Subgroup G} {s : Set α} (hs : IsFundamentalDomain G s μ)
    {r : ι → G} (hnull : ∀ i, NullMeasurableSet (r i • s) μ)
    (hr : Function.Bijective fun i ↦ (QuotientGroup.mk ((r i)⁻¹) : G ⧸ H)) :
    IsFundamentalDomain H (⋃ i, r i • s) μ := by
  refine ⟨.iUnion hnull, ?_, ?_⟩
  · filter_upwards [hs.ae_covers] with τ ⟨g, hg⟩
    -- `g` lies in the coset of some `(r i)⁻¹`, so `r i * g ∈ H` carries `τ` into `r i • s`
    obtain ⟨i, hi⟩ := hr.surjective g
    refine ⟨⟨r i * g, by simpa using QuotientGroup.eq.1 hi⟩, mem_iUnion.2 ⟨i, ?_⟩⟩
    rw [Submonoid.mk_smul, mul_smul]
    exact smul_mem_smul_set hg
  · intro h₁ h₂ hne
    simp only [Function.onFun, MulAction.subgroup_smul_def, smul_set_iUnion,
      AEDisjoint.iUnion_left_iff, AEDisjoint.iUnion_right_iff, ← mul_smul]
    refine fun i j ↦ hs.aedisjoint fun heq ↦ hne ?_
    -- `h₁ * r j = h₂ * r i` puts `(r j)⁻¹` and `(r i)⁻¹` in one left coset of `H`, so `j = i`
    have hji : r j * (r i)⁻¹ = (h₁ : G)⁻¹ * h₂ := by
      rw [mul_inv_eq_iff_eq_mul, mul_assoc, ← heq, inv_mul_cancel_left]
    obtain rfl : j = i := hr.injective <| QuotientGroup.eq.2 <| by
      simpa [hji] using H.mul_mem (H.inv_mem h₁.property) h₂.property
    exact Subtype.ext (mul_right_cancel heq)

/-- **Subgroup coset tiling of a fundamental domain.** If `s` is a fundamental
domain for a group `G` acting on `α`, then for any subgroup `H ≤ G`, the union of
`[G : H]`-many translates `(q.out)⁻¹ • s` (for `q ∈ G ⧸ H`) is a fundamental
domain for the restricted `H`-action on `α`: the inverses `(q.out)⁻¹` of the canonical
representatives form the right transversal. The coset space must be countable
(`[Countable (G ⧸ H)]`) — in particular this covers every finite-index subgroup. This is
`IsFundamentalDomain.iUnion_smul_of_transversal` at `r q = (q.out)⁻¹`. -/
@[to_additive /-- **Subgroup coset tiling of a fundamental domain.** If `s` is a fundamental
domain for an additive group `G` acting on `α`, then for any subgroup `H ≤ G` whose coset
space is **countable** (`[Countable (G ⧸ H)]`, automatic at finite index), the union of the
translates `-q.out +ᵥ s` (for `q ∈ G ⧸ H`) is a fundamental domain for the restricted
`H`-action on `α`. -/]
theorem IsFundamentalDomain.subgroup_iUnion_out_inv_smul
    {G α : Type*} [Group G] [MeasurableSpace α] [MulAction G α]
    [MeasurableConstSMul G α] {μ : Measure α} [SMulInvariantMeasure G α μ]
    (H : Subgroup G) [Countable (G ⧸ H)] {s : Set α}
    (hs : IsFundamentalDomain G s μ) :
    IsFundamentalDomain H (⋃ q : G ⧸ H, ((q.out : G))⁻¹ • s) μ :=
  hs.iUnion_smul_of_transversal (r := fun q : G ⧸ H ↦ (q.out : G)⁻¹)
      (fun q ↦ hs.nullMeasurableSet_smul _) <| by
    simpa only [inv_inv, QuotientGroup.out_eq', Function.id_def] using Function.bijective_id

/-- **Conjugation-shift of a fundamental domain.** If `s` is an `H₁`-fundamental
domain (where `H₁ ≤ G`) and `H₂` is the pointwise conjugate `g · H₁ · g⁻¹`
(in `Subgroup` pointwise smul form, via the `ConjAct G`-action), then
`g • s` is an `H₂`-fundamental domain. Only quasi-measure-preservation of the single
translation `x ↦ g⁻¹ • x` is required, not invariance under the whole group. -/
theorem IsFundamentalDomain.smul_of_eq_conjAct_pointwise_smul
    {G α : Type*} [Group G] [MeasurableSpace α] [MulAction G α]
    {μ : Measure α}
    {H₁ H₂ : Subgroup G} {s : Set α} (hs : IsFundamentalDomain H₁ s μ)
    {g : G} (hg : QuasiMeasurePreserving (fun x : α ↦ g⁻¹ • x) μ μ)
    (hgH : H₂ = ConjAct.toConjAct g • H₁) :
    IsFundamentalDomain H₂ (g • s) μ := by
  subst hgH
  -- `Subgroup.pointwise_smul_def` is `rfl`, and the `ConjAct` monoid endomorphism at `g` is
  -- definitionally `MulAut.conj g`; naming the target form here (rather than letting the
  -- lemma leave it as `toMonoidEnd …`) is what lets `MulEquiv.subgroupMap_symm_apply`
  -- rewrite below, since simp matches the subgroup index syntactically.
  rw [show ConjAct.toConjAct g • H₁ = H₁.map (MulAut.conj g : G ≃* G) from
    Subgroup.pointwise_smul_def _]
  refine hs.image_of_equiv (MulAction.toPerm g) hg
    ((MulAut.conj g).subgroupMap H₁).symm.toEquiv fun h₂ x ↦ ?_
  -- `MulEquiv.subgroupMap` sends `h₁` to `g * h₁ * g⁻¹`, so its inverse sends `h₂` to
  -- `g⁻¹ * h₂ * g`; `MulAction.subgroup_smul_def` restricts the subtype action to the
  -- ambient one on each side.
  simp only [MulEquiv.toEquiv_eq_coe, MulEquiv.coe_toEquiv, MulEquiv.subgroupMap_symm_apply,
    MulAut.conj_symm_apply, MulAction.subgroup_smul_def, MulAction.toPerm_apply, smul_smul,
    mul_inv_cancel_left, mul_assoc]

/-- **AE-disjointness of arbitrary `G`-translates related by an `H`-element.**
Let `D` be a fundamental domain for a subgroup `H ≤ G` acting on `α` with a measure `μ`.
For any distinct pair `g₁, g₂ ∈ G` whose relative
position `g₁⁻¹ * g₂` lies in `H`, the translates `g₁ • D` and `g₂ • D` are
`AE`-disjoint with respect to `μ` — needing only quasi-measure-preservation of the single
translation `x ↦ g₁⁻¹ • x`, not invariance under the whole group. -/
@[to_additive /-- **AE-disjointness of arbitrary `G`-translates related by an `H`-element.**
Let `D` be a fundamental domain for a subgroup `H ≤ G` of an additive group acting on `α`
with a measure `μ`. For any distinct pair `g₁, g₂ ∈ G` with `-g₁ + g₂ ∈ H`, the translates
`g₁ +ᵥ D` and `g₂ +ᵥ D` are `AE`-disjoint, given quasi-measure-preservation of the single
translation `x ↦ -g₁ +ᵥ x`. -/]
theorem IsFundamentalDomain.aedisjoint_smul_of_inv_mul_mem
    {G α : Type*} [Group G] [MeasurableSpace α] [MulAction G α]
    {μ : Measure α}
    {H : Subgroup G} {D : Set α} (hD : IsFundamentalDomain H D μ)
    {g₁ g₂ : G} (hg₁ : QuasiMeasurePreserving (fun x : α ↦ g₁⁻¹ • x) μ μ)
    (h_mem : g₁⁻¹ * g₂ ∈ H) (h_ne : g₁ ≠ g₂) :
    AEDisjoint μ (g₁ • D) (g₂ • D) := by
  have h_ne' : g₁⁻¹ * g₂ ≠ 1 := fun h ↦ h_ne (inv_mul_eq_one.mp h)
  have h_core : AEDisjoint μ ((1 : H) • D) ((⟨g₁⁻¹ * g₂, h_mem⟩ : H) • D) :=
    hD.aedisjoint fun heq ↦ h_ne' <| by
      simpa [Subgroup.coe_one, eq_comm] using congr_arg (Subtype.val : H → G) heq
  rw [one_smul, MulAction.subgroup_smul_def] at h_core
  -- Pull the disjointness back along `x ↦ g₁⁻¹ • x`; the two preimages are the stated translates.
  simpa [Set.preimage_smul_inv, smul_smul] using h_core.preimage hg₁

/-- **A fundamental domain for a subgroup, read through a larger group it sits inside.** `s` is a
fundamental domain for `H.subgroupOf K` acting through `K` if and only if it is one for `H ⊓ K`
acting through the ambient group: the two subgroups are the same set of elements and act the same
way, so only the packaging differs. -/
theorem isFundamentalDomain_subgroupOf_iff {G α : Type*} [Group G] [MeasurableSpace α]
    [MulAction G α] {μ : Measure α} {H K : Subgroup G} {s : Set α} :
    IsFundamentalDomain (H.subgroupOf K) s μ ↔ IsFundamentalDomain (H ⊓ K : Subgroup G) s μ := by
  -- `K.subtype` carries `H.subgroupOf K` onto `H ⊓ K`, and each element acts the same either way
  let e : H.subgroupOf K ≃* (H ⊓ K : Subgroup G) :=
    ((H.subgroupOf K).equivMapOfInjective K.subtype K.subtype_injective).trans
      (MulEquiv.subgroupCongr (H.subgroupOf_map_subtype K))
  have he (g : H.subgroupOf K) : Function.Semiconj (id : α → α) (e g • ·) (g • ·) := fun x ↦ by
    simp [e, Subgroup.smul_def]
  refine ⟨fun hs ↦ ?_, fun hs ↦ ?_⟩
  · simpa only [Set.preimage_id] using hs.preimage_of_equiv (.id μ) e.bijective he
  · simpa only [Equiv.coe_refl, Set.image_id] using hs.image_of_equiv (.refl α) (.id μ) e.toEquiv he

/-- **The double-coset tiling of a fundamental domain, at an arbitrary transversal.** Let `s` be
a fundamental domain for `Γ₂` and let `δ` be any element acting quasi-measure-preservingly. If
`r : ι → Γ₂` is a family with `i ↦ ⟦(r i)⁻¹⟧` a bijection onto `Γ₂ ⧸ (δ⁻¹Γ₁δ ⊓ Γ₂)`, then the
translates `(δ · r i) • s` tile a fundamental domain for `Γ₁ ⊓ δΓ₂δ⁻¹`.

`iUnion_mul_out_inv_smul` below is this at `r v = σᵥ⁻¹` for the canonical representatives, and is
the statement to reach for when the family is not already fixed. **The transversal form is what a
Hecke operator needs**, because the elements it sums over are supplied by the double-coset
machinery rather than chosen by `Quotient.out`: two transversals of the same coset space give
different translates, so a tiling stated only at `Quotient.out` does not transfer to them. That
is the same reason `iUnion_smul_of_transversal` sits under `subgroup_iUnion_out_inv_smul` above.

Note the hypotheses this does *not* take: no measurability of the ambient action and no
invariance of `μ` under it, only the null-measurability of the individual translates and
quasi-measure-preservation of the single translation by `δ⁻¹`. -/
theorem IsFundamentalDomain.iUnion_mul_smul_of_transversal {G α ι : Type*} [Group G]
    [MeasurableSpace α] [MulAction G α] [Countable ι] {μ : Measure α} {Γ₁ Γ₂ : Subgroup G}
    (δ : G) {s : Set α} (hs : IsFundamentalDomain Γ₂ s μ)
    (hδ : QuasiMeasurePreserving (fun x : α ↦ δ⁻¹ • x) μ μ)
    {r : ι → Γ₂} (hnull : ∀ i, NullMeasurableSet (((r i : Γ₂) : G) • s) μ)
    (hr : Function.Bijective fun i ↦
      (QuotientGroup.mk (r i)⁻¹ : Γ₂ ⧸ (ConjAct.toConjAct δ⁻¹ • Γ₁).subgroupOf Γ₂)) :
    IsFundamentalDomain (Γ₁ ⊓ ConjAct.toConjAct δ • Γ₂ : Subgroup G)
      (⋃ i, (δ * ((r i : Γ₂) : G)) • s) μ := by
  -- Tile `s` inside `Γ₂` along the transversal, then carry the tiling along `δ`. Only `hδ` is
  -- needed for the second step, which is why no measurability of the ambient action appears.
  have htile := isFundamentalDomain_subgroupOf_iff.1 <| hs.iUnion_smul_of_transversal
    (H := (ConjAct.toConjAct δ⁻¹ • Γ₁).subgroupOf Γ₂) hnull hr
  have hconj := htile.smul_of_eq_conjAct_pointwise_smul (g := δ) hδ (H₂ :=
    ConjAct.toConjAct δ • ((ConjAct.toConjAct δ⁻¹ • Γ₁) ⊓ Γ₂ : Subgroup G)) rfl
  have hgrp : ConjAct.toConjAct δ • ((ConjAct.toConjAct δ⁻¹ • Γ₁) ⊓ Γ₂ : Subgroup G) =
      (Γ₁ ⊓ ConjAct.toConjAct δ • Γ₂ : Subgroup G) := by
    rw [Subgroup.smul_inf, map_inv, smul_inv_smul]
  -- the `Γ₂`-action on `α` is the ambient one by definition, so the two spellings of each
  -- translate are the same set and the outer `δ` composes with them
  have hset : ∀ i, δ • ((r i) • s) = (δ * ((r i : Γ₂) : G)) • s := fun i ↦ by
    rw [show ((r i) • s : Set α) = (((r i : Γ₂) : G)) • s from rfl, smul_smul]
  rw [hgrp, Set.smul_set_iUnion] at hconj
  exact (Set.iUnion_congr hset) ▸ hconj

/-- **The double-coset tiling of a fundamental domain.** Let `s` be a fundamental domain for
`Γ₂`, and let `δ` be any element acting quasi-measure-preservingly. The translates
`(δ · σᵥ⁻¹) • s`, taken over the canonical representatives `σᵥ` of `Γ₂ ⧸ (δ⁻¹Γ₁δ ⊓ Γ₂)`, tile a
fundamental domain for `Γ₁ ⊓ δΓ₂δ⁻¹`.

The index type is `DoubleCoset.DecompQuotient Γ₂ Γ₁ δ⁻¹`, the one a Hecke decomposition
`Γ₁ δ Γ₂ = ⊔ᵥ Γ₁ (δ σᵥ⁻¹)` is indexed by — but `σᵥ` here is `Quotient.out`'s choice, and a Hecke
operator's `σᵥ` comes from the double-coset machinery instead. **Two transversals of the same
coset space give different translates**, so this statement does not transfer to them;
`iUnion_mul_smul_of_transversal` is the form that does.

Ported from AINTLIB (github.com/CBirkbeck/AINTLIB @ `6d87d596a5372d5b122c47b7082d4c3afa9b7c3b`,
Apache-2.0), `projects/LeanModularForms/LeanModularForms/HeckeRIngs/GL2/AdjointTheory/
FDTransport.lean`, which proves this for `Γ₁(N)` and a concrete `α`. -/
theorem IsFundamentalDomain.iUnion_mul_out_inv_smul {G α : Type*} [Group G] [MeasurableSpace α]
    [MulAction G α] {μ : Measure α} {Γ₁ Γ₂ : Subgroup G}
    [MeasurableConstSMul Γ₂ α] [SMulInvariantMeasure Γ₂ α μ]
    (δ : G) {s : Set α} (hs : IsFundamentalDomain Γ₂ s μ)
    (hδ : QuasiMeasurePreserving (fun x : α ↦ δ⁻¹ • x) μ μ)
    [Countable (Γ₂ ⧸ (ConjAct.toConjAct δ⁻¹ • Γ₁).subgroupOf Γ₂)] :
    IsFundamentalDomain (Γ₁ ⊓ ConjAct.toConjAct δ • Γ₂ : Subgroup G)
      (⋃ v : Γ₂ ⧸ (ConjAct.toConjAct δ⁻¹ • Γ₁).subgroupOf Γ₂,
        (δ * ((v.out : Γ₂) : G)⁻¹) • s) μ :=
  hs.iUnion_mul_smul_of_transversal δ hδ
    (r := fun v : Γ₂ ⧸ (ConjAct.toConjAct δ⁻¹ • Γ₁).subgroupOf Γ₂ ↦ (v.out)⁻¹)
    (fun v ↦ hs.nullMeasurableSet_smul _) <| by
      simpa only [inv_inv, QuotientGroup.out_eq', Function.id_def] using Function.bijective_id

/-- **A tile with disjoint interiors and null frontier is a fundamental domain.** Let `s` be a
null-measurable set whose translates cover almost every point, all of whose translated frontiers
are null, and whose interior is disjoint from its translates by nonidentity elements. Then `s` is
a fundamental domain. Neither invariance of the measure nor continuity of the action is needed;
for an invariant measure the frontier hypothesis follows from `μ (frontier s) = 0` by
`measure_smul_null`. -/
@[to_additive /-- **A tile with disjoint interiors and null frontier is an additive fundamental
domain.** Let `s` be a null-measurable set whose translates cover almost every point, all of whose
translated frontiers are null, and whose interior is disjoint from its translates by nonzero
elements. Then `s` is an additive fundamental domain. -/]
theorem IsFundamentalDomain.of_disjoint_smul_interior {G α : Type*} [Group G] [MulAction G α]
    [TopologicalSpace α] [MeasurableSpace α] {μ : Measure α}
    {s : Set α} (h_meas : NullMeasurableSet s μ) (h_ae_covers : ∀ᵐ x ∂μ, ∃ g : G, g • x ∈ s)
    (h_frontier : ∀ g : G, μ (g • frontier s) = 0)
    (h_disj : ∀ g : G, g ≠ 1 → Disjoint (g • interior s) (interior s)) :
    IsFundamentalDomain G s μ where
  nullMeasurableSet := h_meas
  ae_covers := h_ae_covers
  aedisjoint g h hgh := by
    -- a point of `s` off its frontier lies in its interior
    have hint {y : α} (hy : y ∈ s) (hy' : y ∉ frontier s) : y ∈ interior s :=
      ((closure_eq_interior_union_frontier s).subset (subset_closure hy)).resolve_right hy'
    -- a common point of two distinct translates lies on the frontier of one of them
    have hsub : g • s ∩ h • s ⊆ g • frontier s ∪ h • frontier s := by
      rintro x ⟨hxg, hxh⟩
      rw [mem_smul_set_iff_inv_smul_mem] at hxg hxh
      by_contra hx
      rw [mem_union, mem_smul_set_iff_inv_smul_mem, mem_smul_set_iff_inv_smul_mem,
        not_or] at hx
      refine disjoint_left.1 (h_disj (h⁻¹ * g) fun h1 ↦ hgh (inv_mul_eq_one.1 h1).symm)
        ?_ (hint hxh hx.2)
      rw [mem_smul_set_iff_inv_smul_mem, mul_inv_rev, inv_inv, mul_smul, smul_inv_smul]
      exact hint hxg hx.1
    exact measure_mono_null hsub (measure_union_null (h_frontier g) (h_frontier h))

/-- **A set a.e. equal to a fundamental domain is a fundamental domain.** Fundamental domains are
determined only up to null sets: changing `s` on a null set, for instance by choosing which
boundary points of a polygon to keep, gives another fundamental domain, provided the translations
are quasi-measure-preserving and the group is countable. -/
@[to_additive /-- **A set a.e. equal to an additive fundamental domain is an additive fundamental
domain**, for a countable group acting by quasi-measure-preserving translations. -/]
theorem IsFundamentalDomain.congr_set {G α : Type*} [Group G] [MulAction G α]
    [MeasurableSpace α] [Countable G] {μ : Measure α} {s t : Set α}
    (h : IsFundamentalDomain G s μ) (hst : s =ᵐ[μ] t)
    (h_qmp : ∀ g : G, QuasiMeasurePreserving (g • · : α → α) μ μ) :
    IsFundamentalDomain G t μ where
  nullMeasurableSet := h.nullMeasurableSet.congr hst
  ae_covers := by
    have hmem : ∀ᵐ x ∂μ, ∀ g : G, (g • x ∈ s ↔ g • x ∈ t) :=
      ae_all_iff.2 fun g ↦ ((h_qmp g).preimage_ae_eq hst).mem_iff
    filter_upwards [h.ae_covers, hmem] with x ⟨g, hg⟩ hx
    exact ⟨g, (hx g).1 hg⟩
  aedisjoint g g' hne := by
    have key (g : G) : g • t =ᵐ[μ] g • s := by
      simpa only [preimage_smul_inv] using (h_qmp g⁻¹).preimage_ae_eq hst.symm
    exact (h.aedisjoint hne).congr (key g) (key g')

/-- **A set a.e. disjoint from its translates is no larger than a fundamental domain.** If a
null-measurable set `t` is a.e. disjoint from each of its translates by nonidentity elements, so
that it embeds in the orbit space up to a null set, then its measure is at most that of any
fundamental domain. -/
@[to_additive /-- **A set a.e. disjoint from its translates is no larger than a fundamental
domain.** If a null-measurable set `t` is a.e. disjoint from each of its translates by nonzero
elements, then its measure is at most that of any fundamental domain. -/]
theorem IsFundamentalDomain.measure_le_of_aedisjoint_smul {G α : Type*} [Group G]
    [MulAction G α] [MeasurableSpace α] [Countable G] [MeasurableConstSMul G α] {μ : Measure α}
    [SMulInvariantMeasure G α μ] {s t : Set α} (hs : IsFundamentalDomain G s μ)
    (ht : NullMeasurableSet t μ) (hd : ∀ g : G, g ≠ 1 → AEDisjoint μ (g • t) t) : μ t ≤ μ s :=
  hs.measure_le_of_pairwise_disjoint ht <| (pairwise_aedisjoint_of_aedisjoint_forall_ne_one hd
    fun g ↦ (measurePreserving_smul g μ).quasiMeasurePreserving).mono fun _ _ h ↦
      h.mono inter_subset_left inter_subset_left

/-- **A fundamental domain is no larger than a set whose translates cover it.** If the translates
of `t` cover a fundamental domain `s`, for instance because they cover the whole space, then
`μ s ≤ μ t`. -/
@[to_additive /-- **A fundamental domain is no larger than a set whose translates cover it.** If
the translates of `t` cover an additive fundamental domain `s`, then `μ s ≤ μ t`. -/]
theorem IsFundamentalDomain.measure_le_of_subset_iUnion_smul {G α : Type*} [Group G]
    [MulAction G α] [MeasurableSpace α] [Countable G] [MeasurableConstSMul G α] {μ : Measure α}
    [SMulInvariantMeasure G α μ] {s t : Set α} (hs : IsFundamentalDomain G s μ)
    (hst : s ⊆ ⋃ g : G, g • t) : μ s ≤ μ t :=
  calc μ s ≤ μ (⋃ g : G, g • t ∩ s) := measure_mono <| by
        rw [← iUnion_inter]; exact subset_inter hst subset_rfl
    _ ≤ ∑' g : G, μ (g • t ∩ s) := measure_iUnion_le _
    _ = μ t := (hs.measure_eq_tsum t).symm

/-- **Covolume is positive**: a countable group acting with a fundamental domain for a nonzero
invariant measure has positive covolume. -/
theorem covolume_pos {G α : Type*} [Group G] [MulAction G α] [MeasurableSpace α] [Countable G]
    [MeasurableConstSMul G α] {μ : Measure α} [SMulInvariantMeasure G α μ]
    [HasFundamentalDomain G α μ] (hμ : μ ≠ 0) : 0 < covolume G α μ := by
  obtain ⟨s, hs⟩ := HasFundamentalDomain.ExistsIsFundamentalDomain (G := G) (ν := μ)
  rw [hs.covolume_eq_volume]
  exact pos_iff_ne_zero.mpr (hs.measure_ne_zero hμ)

/-- **Covolume is a conjugacy invariant**: for an invariant measure, a countable subgroup `Γ`
with a fundamental domain and its conjugate `g Γ g⁻¹` have the same covolume. -/
@[simp]
theorem covolume_conjAct_smul {G α : Type*} [Group G] [MulAction G α] [MeasurableSpace α]
    [MeasurableConstSMul G α] {μ : Measure α} [SMulInvariantMeasure G α μ] (Γ : Subgroup G)
    [Countable Γ] [HasFundamentalDomain Γ α μ] (g : G) :
    covolume (ConjAct.toConjAct g • Γ : Subgroup G) α μ = covolume Γ α μ := by
  have : Countable (ConjAct.toConjAct g • Γ : Subgroup G) :=
    (Subgroup.equivSMul (ConjAct.toConjAct g) Γ).symm.injective.countable
  obtain ⟨s, hs⟩ := HasFundamentalDomain.ExistsIsFundamentalDomain (G := Γ) (ν := μ)
  rw [hs.covolume_eq_volume, (hs.smul_of_eq_conjAct_pointwise_smul
    (measurePreserving_smul g⁻¹ μ).quasiMeasurePreserving rfl).covolume_eq_volume,
    measure_smul]

/-- **Covolume is multiplicative in the index**: for a measure invariant under subgroups `Δ ≤ Γ`
with `Γ` countable and having a fundamental domain, the covolume of `Δ` is the index `[Γ : Δ]`,
counted in `ℕ∞`, times the covolume of `Γ`. -/
theorem covolume_eq_card_mul_covolume {G α : Type*} [Group G] [MulAction G α]
    [MeasurableSpace α] {μ : Measure α} {Γ Δ : Subgroup G} [MeasurableConstSMul Γ α]
    [SMulInvariantMeasure Γ α μ] [Countable Γ] [HasFundamentalDomain Γ α μ] (h : Δ ≤ Γ) :
    covolume Δ α μ = ENat.card (Γ ⧸ Δ.subgroupOf Γ) * covolume Γ α μ := by
  have : MeasurableConstSMul Δ α := ⟨fun d ↦ measurable_const_smul (⟨d, h d.property⟩ : Γ)⟩
  have : SMulInvariantMeasure Δ α μ :=
    ⟨fun d ↦ SMulInvariantMeasure.measure_preimage_smul (⟨d, h d.property⟩ : Γ)⟩
  have : Countable Δ := (Subgroup.inclusion_injective h).countable
  have : Countable (Γ ⧸ Δ.subgroupOf Γ) := QuotientGroup.mk_surjective.countable
  obtain ⟨s, hs⟩ := HasFundamentalDomain.ExistsIsFundamentalDomain (G := Γ) (ν := μ)
  have ht := isFundamentalDomain_subgroupOf_iff.1 (hs.subgroup_iUnion_out_inv_smul (Δ.subgroupOf Γ))
  rw [inf_of_le_left h] at ht
  rw [ht.covolume_eq_volume, hs.covolume_eq_volume, measure_iUnion₀ ?_
    fun q ↦ hs.nullMeasurableSet_smul _]
  · simp_rw [measure_smul]
    exact ENNReal.tsum_const _
  · intro q q' hqq'
    refine hs.aedisjoint fun heq ↦ hqq' ?_
    rw [← q.out_eq', ← q'.out_eq', inv_inj.mp heq]

/-- **Covolume is multiplicative in a finite index**: the form of
`MeasureTheory.covolume_eq_card_mul_covolume` for `Δ` of finite index in `Γ`, with the index
`[Γ : Δ]` as a natural number. -/
theorem covolume_eq_index_mul_covolume {G α : Type*} [Group G] [MulAction G α]
    [MeasurableSpace α] {μ : Measure α} {Γ Δ : Subgroup G} [MeasurableConstSMul Γ α]
    [SMulInvariantMeasure Γ α μ] [Countable Γ] [HasFundamentalDomain Γ α μ] (h : Δ ≤ Γ)
    [Δ.IsFiniteRelIndex Γ] :
    covolume Δ α μ = (Δ.subgroupOf Γ).index * covolume Γ α μ := by
  rw [covolume_eq_card_mul_covolume h, ENat.card_eq_coe_natCard, ENat.toENNReal_coe,
    Subgroup.index]

/-- For `ν ≪ μ`, a fundamental domain `s` whose translates `g • s` are `ν`-null-measurable,
and a `ν`-integrable function `f`, the set integrals of `f` over `g • s` have sum `∫ x, f x ∂ν`.
This upgrades `MeasureTheory.IsFundamentalDomain.integral_eq_tsum_of_ac` from `tsum` equality to
`HasSum` without requiring measure invariance. -/
@[to_additive /-- For `ν ≪ μ`, an additive fundamental domain `s` whose translates `g +ᵥ s` are
`ν`-null-measurable, and a `ν`-integrable function `f`, the set integrals of `f` over `g +ᵥ s`
have sum `∫ x, f x ∂ν`. This upgrades
`MeasureTheory.IsAddFundamentalDomain.integral_eq_tsum_of_ac` from `tsum` equality to `HasSum`
without requiring measure invariance. -/]
theorem IsFundamentalDomain.hasSum_setIntegral_of_ac {G α E : Type*} [Group G] [Countable G]
    [MulAction G α] [MeasurableSpace α] {μ ν : Measure α}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {s : Set α}
    (h : IsFundamentalDomain G s μ) (hν : ν ≪ μ)
    (hnull : ∀ g : G, NullMeasurableSet (g • s) ν) {f : α → E} (hf : Integrable f ν) :
    HasSum (fun g : G ↦ ∫ x in g • s, f x ∂ν) (∫ x, f x ∂ν) := by
  have hsum_m : (Measure.sum fun g : G ↦ ν.restrict (g • s)) = ν := by
    rw [← restrict_iUnion_ae (h.aedisjoint.mono fun _ _ hij ↦ hν hij) hnull,
      restrict_congr_set (hν h.iUnion_smul_ae_eq), restrict_univ]
  have hsum := hasSum_integral_measure (μ := fun g : G ↦ ν.restrict (g • s))
    (by rwa [hsum_m])
  rwa [hsum_m] at hsum

/-- For a fundamental domain `s` whose translates `g • s` are `μ`-null-measurable and a
`μ`-integrable function `f`, the set integrals of `f` over `g • s` have sum `∫ x, f x ∂μ`. This
upgrades `MeasureTheory.IsFundamentalDomain.integral_eq_tsum` from `tsum` equality to `HasSum`
without requiring measure invariance. -/
@[to_additive /-- For an additive fundamental domain `s` whose translates `g +ᵥ s` are
`μ`-null-measurable and a `μ`-integrable function `f`, the set integrals of `f` over `g +ᵥ s` have
sum `∫ x, f x ∂μ`. This upgrades `MeasureTheory.IsAddFundamentalDomain.integral_eq_tsum` from
`tsum` equality to `HasSum` without requiring measure invariance. -/]
theorem IsFundamentalDomain.hasSum_setIntegral {G α E : Type*} [Group G] [Countable G]
    [MulAction G α] [MeasurableSpace α] {μ : Measure α}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {s : Set α}
    (h : IsFundamentalDomain G s μ) (hnull : ∀ g : G, NullMeasurableSet (g • s) μ)
    {f : α → E} (hf : Integrable f μ) :
    HasSum (fun g : G ↦ ∫ x in g • s, f x ∂μ) (∫ x, f x ∂μ) :=
  h.hasSum_setIntegral_of_ac Measure.AbsolutelyContinuous.rfl hnull hf

/-- For a `μ`-integrable function `f`, the set integrals `∫ x in s, f (g • x) ∂μ` over a
fundamental domain `s` have sum `∫ x, f x ∂μ`. This upgrades
`MeasureTheory.IsFundamentalDomain.integral_eq_tsum''` from `tsum` equality to `HasSum`. -/
@[to_additive /-- For a `μ`-integrable function `f`, the set integrals `∫ x in s, f (g +ᵥ x) ∂μ`
over an additive fundamental domain `s` have sum `∫ x, f x ∂μ`. This upgrades
`MeasureTheory.IsAddFundamentalDomain.integral_eq_tsum''` from `tsum` equality to `HasSum`. -/]
theorem IsFundamentalDomain.hasSum_setIntegral_smul {G α E : Type*} [Group G] [Countable G]
    [MulAction G α] [MeasurableSpace α] [MeasurableConstSMul G α] {μ : Measure α}
    [SMulInvariantMeasure G α μ] [NormedAddCommGroup E] [NormedSpace ℝ E] {s : Set α}
    (h : IsFundamentalDomain G s μ) {f : α → E} (hf : Integrable f μ) :
    HasSum (fun g : G ↦ ∫ x in s, f (g • x) ∂μ) (∫ x, f x ∂μ) := by
  refine (h.hasSum_setIntegral h.nullMeasurableSet_smul hf).congr_fun fun g ↦ ?_
  rw [← Set.image_smul]
  exact ((measurePreserving_smul g μ).setIntegral_image_emb
    (measurableEmbedding_const_smul g) f s).symm

/-- **Covolume scales with the measure**: multiplying the measure by `c` multiplies the covolume
by `c`. -/
@[to_additive (attr := simp) addCovolume_smul_measure /-- **Covolume scales with the measure**:
multiplying the measure by `c` multiplies the additive covolume by `c`. -/]
theorem covolume_smul_measure {G α : Type*} [Group G] [MulAction G α] [MeasurableSpace α]
    [Countable G] [MeasurableConstSMul G α] {μ : Measure α} [SMulInvariantMeasure G α μ]
    (c : ℝ≥0∞) : covolume G α (c • μ) = c * covolume G α μ := by
  rcases eq_or_ne c 0 with rfl | hc
  · simp only [zero_smul, zero_mul]
    unfold covolume
    split_ifs <;> simp
  by_cases h : HasFundamentalDomain G α μ
  · obtain ⟨s, hs⟩ := h.ExistsIsFundamentalDomain
    rw [(hs.mono smul_absolutelyContinuous).covolume_eq_volume, hs.covolume_eq_volume,
      smul_apply, smul_eq_mul]
  · have h' : ¬HasFundamentalDomain G α (c • μ) := fun ⟨⟨s, hs⟩⟩ =>
      h ⟨⟨s, hs.mono (absolutelyContinuous_smul hc)⟩⟩
    simp [covolume, h, h']

end MeasureTheory
