/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Group.Tannery
public import TauCeti.Dynamics.Ergodic.Action.Factor
public import TauCeti.MeasureTheory.Group.Action
public import TauCeti.MeasureTheory.Group.Arithmetic
public import TauCeti.MeasureTheory.Measure.Real

/-!
# Mixing of measure-preserving actions along a filter

Let `M` act on a measurable space `X` carrying a measure `μ`, and let `l` be a filter on
`M`. The action is *mixing along `l`* (`TauCeti.MixingAlong M X μ l`) if the correlations
`μ(A ∩ (m • ·)⁻¹' B)` of any two measurable sets tend to `μ(A) μ(B)` along `l`, the measures being
read as real numbers. A single map `T` is mixing exactly when the action of its iterates
(`IterateMulAct T`) is mixing along the image of `atTop`
(`TauCeti.mixingAlong_iterateMulAct_iff`); an action of an infinite discrete group is mixing when
it is mixing along `cofinite`. The definition accepts any filter: along `⊥` it is vacuous
(`TauCeti.mixingAlong_bot`), so the theorems deducing ergodicity assume `l.NeBot`.

The action is *weakly mixing* (`TauCeti.WeakMixingSMul M X μ`) if the diagonal action on
`(X × X, μ × μ)` is ergodic.

Measure preservation is not part of the definition of mixing; the theorems that need it carry
`SMulInvariantMeasure M X μ` as a separate hypothesis.

## Main results

* `TauCeti.MixingAlong.of_isPiSystem`: for a probability measure invariant under a measurable
  action, mixing may be checked on a π-system generating the σ-algebra.
* `TauCeti.MixingAlong.prod`: the diagonal action on a product of two actions mixing along the same
  filter is mixing along it.
* `TauCeti.MixingAlong.measureReal_eq_zero_or_one`, `TauCeti.MixingAlong.ergodicSMul`: an action
  mixing along a nontrivial filter is ergodic.
* `TauCeti.MixingAlong.weakMixingSMul`: an action mixing along a nontrivial filter is weakly
  mixing.
* `TauCeti.WeakMixingSMul.ergodicSMul`: a weakly mixing action is ergodic.
* `TauCeti.IsFactorMapSMul.mixingAlong`, `TauCeti.IsFactorMapSMul.weakMixingSMul`: mixing and weak
  mixing pass to factors; `MeasureTheory.MeasurePreserving.mixingAlong_iff` and
  `MeasureTheory.MeasurePreserving.weakMixingSMul_iff` give their invariance under equivariant
  measure-preserving measurable equivalences.
* `TauCeti.MixingAlong.mono`, `TauCeti.mixingAlong_map_iff`: mixing along a filter implies mixing
  along every finer filter, and mixing along the image of a filter under a reparameterization of
  the action is mixing of the reparameterized action.

Every definition and theorem except `TauCeti.mixingAlong_iterateMulAct_iff` has an additive
version (`TauCeti.AddMixingAlong`, `TauCeti.WeakMixingVAdd`), for instance for flows.

## References

* M. Einsiedler and T. Ward, *Ergodic Theory with a view towards Number Theory*, Springer, 2011,
  §2.7 (mixing and weak mixing).
-/

public section

open Filter MeasureTheory Set Topology

namespace TauCeti

variable {M N X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y] {μ : Measure X}
  {ν : Measure Y} {l l' : Filter M}

/-- The action of `M` on `(X, μ)` is *mixing along* the filter `l` on `M` if for all measurable
`A` and `B` the correlations `μ(A ∩ (m • ·)⁻¹' B)` tend to `μ(A) μ(B)` along `l`, the measures
being read as real numbers. -/
@[to_additive AddMixingAlong /-- The additive action of `M` on `(X, μ)` is *mixing along* the
filter `l` on `M` if for all measurable `A` and `B` the correlations `μ(A ∩ (m +ᵥ ·)⁻¹' B)` tend to
`μ(A) μ(B)` along `l`, the measures being read as real numbers. -/]
def MixingAlong (M X : Type*) [SMul M X] [MeasurableSpace X] (μ : Measure X) (l : Filter M) :
    Prop :=
  ∀ ⦃A B : Set X⦄, MeasurableSet A → MeasurableSet B →
    Tendsto (fun m : M ↦ μ.real (A ∩ (m • ·) ⁻¹' B)) l (𝓝 (μ.real A * μ.real B))

/-- The action of `M` on `(X, μ)` is *weakly mixing* if the diagonal action on `(X × X, μ × μ)` is
ergodic. In particular `μ × μ` is invariant under the diagonal action. -/
@[to_additive /-- The additive action of `M` on `(X, μ)` is *weakly mixing* if the diagonal action
on `(X × X, μ × μ)` is ergodic. In particular `μ × μ` is invariant under the diagonal action. -/]
def WeakMixingSMul (M X : Type*) [SMul M X] [MeasurableSpace X] (μ : Measure X) : Prop :=
  ErgodicSMul M (X × X) (μ.prod μ)

section SMul

variable [SMul M X] [SMul M Y]

@[to_additive addMixingAlong_iff]
theorem mixingAlong_iff : MixingAlong M X μ l ↔ ∀ ⦃A B : Set X⦄, MeasurableSet A →
    MeasurableSet B →
      Tendsto (fun m : M ↦ μ.real (A ∩ (m • ·) ⁻¹' B)) l (𝓝 (μ.real A * μ.real B)) :=
  Iff.rfl

/-- The correlations of an action mixing along `l` tend to the product of the measures. -/
@[to_additive /-- The correlations of an additive action mixing along `l`
tend to the product of the measures. -/]
theorem MixingAlong.tendsto (h : MixingAlong M X μ l) {A B : Set X} (hA : MeasurableSet A)
    (hB : MeasurableSet B) :
    Tendsto (fun m : M ↦ μ.real (A ∩ (m • ·) ⁻¹' B)) l (𝓝 (μ.real A * μ.real B)) :=
  h hA hB

@[to_additive]
theorem weakMixingSMul_iff : WeakMixingSMul M X μ ↔ ErgodicSMul M (X × X) (μ.prod μ) :=
  Iff.rfl

/-- Every action is mixing along the trivial filter `⊥`. -/
@[to_additive (attr := simp) addMixingAlong_bot /-- Every additive action is mixing along the
trivial filter `⊥`. -/]
theorem mixingAlong_bot : MixingAlong M X μ ⊥ :=
  fun _ _ _ _ ↦ tendsto_bot

/-- Mixing along a filter implies mixing along every finer filter. -/
@[to_additive /-- Mixing along a filter implies mixing along every finer filter.
-/]
theorem MixingAlong.mono (h : MixingAlong M X μ l) (hl : l' ≤ l) : MixingAlong M X μ l' :=
  fun _ _ hA hB ↦ (h hA hB).mono_left hl

/-- **Reparameterization.** If `f : N → M` reparameterizes the action, `f n • x = n • x`, for
instance a monoid homomorphism defining the `N`-action, then the `M`-action is mixing along the
image `map f l` of a filter `l` on `N` exactly when the `N`-action is mixing along `l`. -/
@[to_additive addMixingAlong_map_iff /-- **Reparameterization.** If `f : N → M` reparameterizes the
additive action, `f n +ᵥ x = n +ᵥ x`, then the `M`-action is mixing along the image `map f l` of a
filter `l` on `N` exactly when the `N`-action is mixing along `l`. -/]
theorem mixingAlong_map_iff [SMul N X] {f : N → M} (hf : ∀ (n : N) (x : X), f n • x = n • x)
    {l : Filter N} : MixingAlong M X μ (map f l) ↔ MixingAlong N X μ l := by
  simp only [mixingAlong_iff, tendsto_map'_iff, Function.comp_def, hf]

/-- **The zero-one law of mixing.** If an action is mixing along a nontrivial filter and a
measurable set `s` is almost everywhere equal to its preimage under every parameter, then
`μ.real s` is `0` or `1`. -/
@[to_additive AddMixingAlong.measureReal_eq_zero_or_one /-- **The zero-one law of mixing.** If an
additive action is mixing along a nontrivial filter and a measurable set `s` is almost everywhere
equal to its preimage under every parameter, then `μ.real s` is `0` or `1`. -/]
theorem MixingAlong.measureReal_eq_zero_or_one [l.NeBot] (h : MixingAlong M X μ l) {s : Set X}
    (hs : MeasurableSet s) (hinv : ∀ m : M, (m • ·) ⁻¹' s =ᵐ[μ] s) :
    μ.real s = 0 ∨ μ.real s = 1 := by
  have hconst : ∀ m : M, μ.real (s ∩ (m • ·) ⁻¹' s) = μ.real s := fun m ↦ by
    rw [measureReal_congr (ae_eq_set_inter .rfl (hinv m)), inter_self]
  have h0 := h hs hs
  simp only [hconst] at h0
  exact eq_zero_or_one_of_sq_eq_self (pow_two (μ.real s) ▸ tendsto_nhds_unique h0
    tendsto_const_nhds)

/-- **Mixing implies ergodicity.** An action mixing along a nontrivial filter, preserving a
probability measure, is ergodic. -/
@[to_additive /-- **Mixing implies ergodicity.** An additive action
mixing along a nontrivial filter, preserving a probability measure, is ergodic. -/]
theorem MixingAlong.ergodicSMul [l.NeBot] [IsProbabilityMeasure μ] [SMulInvariantMeasure M X μ]
    (h : MixingAlong M X μ l) : ErgodicSMul M X μ where
  aeconst_of_forall_preimage_smul_ae_eq {s} hs hinv := by
    rw [eventuallyEmptyOrUniv_iff', ae_eq_empty, ae_eq_univ, prob_compl_eq_zero_iff hs]
    rcases h.measureReal_eq_zero_or_one hs hinv with h1 | h1
    · exact .inl ((measureReal_eq_zero_iff).1 h1)
    · rw [measureReal_def] at h1
      exact .inr ((ENNReal.toReal_eq_one_iff _).1 h1)

/-- **Weak mixing implies ergodicity.** A weakly mixing measurable action on a probability space is
ergodic. -/
@[to_additive /-- **Weak mixing implies ergodicity.** A weakly mixing measurable additive action
on a probability space is ergodic. -/]
theorem WeakMixingSMul.ergodicSMul [IsProbabilityMeasure μ] [MeasurableConstSMul M X]
    (h : WeakMixingSMul M X μ) : ErgodicSMul M X μ :=
  have : ErgodicSMul M (X × X) (μ.prod μ) := h
  (IsFactorMapSMul.fst (M := M) (μ := μ) (μ' := μ)).ergodicSMul

/-- **Mixing passes to factors.** If `π` is a factor map of actions, the target action is
measurable and the source action is mixing along `l`, then the target action is mixing along
`l`. -/
@[to_additive IsFactorMapVAdd.addMixingAlong /-- **Mixing passes to factors.** If `π` is a factor
map of additive actions, the target action is measurable and the source action is mixing along `l`,
then the target action is mixing along `l`. -/]
theorem IsFactorMapSMul.mixingAlong [MeasurableConstSMul M Y] {π : X → Y}
    (hπ : IsFactorMapSMul M π μ ν) (h : MixingAlong M X μ l) : MixingAlong M Y ν l := by
  intro A B hA hB
  have hmp := hπ.measurePreserving
  have hcorr : ∀ m : M, ν.real (A ∩ (m • ·) ⁻¹' B) = μ.real (π ⁻¹' A ∩ (m • ·) ⁻¹' (π ⁻¹' B)) :=
    fun m ↦ by
      rw [← hmp.measureReal_preimage
        (hA.inter (hB.preimage (measurable_const_smul m))).nullMeasurableSet, preimage_inter]
      exact measureReal_congr (ae_eq_set_inter .rfl ((hπ.comp_smul_ae_eq m).preimage B).symm)
  simp only [hcorr, ← hmp.measureReal_preimage hA.nullMeasurableSet,
    ← hmp.measureReal_preimage hB.nullMeasurableSet]
  exact h (hA.preimage hmp.measurable) (hB.preimage hmp.measurable)

/-- **Weak mixing passes to factors.** If `π` is a factor map of actions, the target action is
measurable and the source action on an s-finite measure space is weakly mixing, then the target
action is weakly mixing. -/
@[to_additive /-- **Weak mixing passes to factors.** If `π` is a factor map of additive actions,
the target action is measurable and the source action on an s-finite measure space is weakly
mixing, then the target action is weakly mixing. -/]
theorem IsFactorMapSMul.weakMixingSMul [SFinite μ] [MeasurableConstSMul M Y] {π : X → Y}
    (hπ : IsFactorMapSMul M π μ ν) (h : WeakMixingSMul M X μ) : WeakMixingSMul M Y ν :=
  have : ErgodicSMul M (X × X) (μ.prod μ) := h
  (hπ.prodMap hπ).ergodicSMul

end SMul

section PiSystem

variable [SMul M X] [MeasurableConstSMul M X] [IsProbabilityMeasure μ]
  [SMulInvariantMeasure M X μ]

/-- First half of the π-system test: if the correlations of `A` and `B` converge to `μ(A) μ(B)`
for every `A` in a generating π-system `p`, then they do for every measurable `A`. -/
@[to_additive tendsto_of_isPiSystem_left_vadd]
private theorem tendsto_of_isPiSystem_left {p : Set (Set X)}
    (hgen : ‹MeasurableSpace X› = .generateFrom p) (hp : IsPiSystem p) {B : Set X}
    (hB : MeasurableSet B)
    (h : ∀ A ∈ p, Tendsto (fun m : M ↦ μ.real (A ∩ (m • ·) ⁻¹' B)) l (𝓝 (μ.real A * μ.real B)))
    {A : Set X} (hA : MeasurableSet A) :
    Tendsto (fun m : M ↦ μ.real (A ∩ (m • ·) ⁻¹' B)) l (𝓝 (μ.real A * μ.real B)) := by
  have hB' (m : M) : MeasurableSet ((m • ·) ⁻¹' B) := hB.preimage (measurable_const_smul m)
  induction A, hA using MeasurableSpace.induction_on_inter hgen hp with
  | empty => simpa using tendsto_const_nhds
  | basic t ht => exact h t ht
  | compl t ht iht =>
    have hcorr (m : M) : μ.real (tᶜ ∩ (m • ·) ⁻¹' B) = μ.real B - μ.real (t ∩ (m • ·) ⁻¹' B) := by
      have := measureReal_inter_add_sdiff (μ := μ) (s := (m • ·) ⁻¹' B) ht
      rw [(measurePreserving_smul m μ).measureReal_preimage hB.nullMeasurableSet,
        sdiff_eq_compl_inter, inter_comm ((m • ·) ⁻¹' B) t] at this
      linarith
    simp only [hcorr, measureReal_compl ht, probReal_univ, sub_mul, one_mul]
    exact tendsto_const_nhds.sub iht
  | iUnion f hd hf ihf =>
    have hcorr (m : M) : μ.real ((⋃ i, f i) ∩ (m • ·) ⁻¹' B) =
        ∑' i, μ.real (f i ∩ (m • ·) ⁻¹' B) := by
      rw [iUnion_inter, measureReal_iUnion (μ := μ)
        (hd.mono fun _ _ h ↦ h.mono inter_subset_left inter_subset_left)
        (fun i ↦ (hf i).inter (hB' m))]
    simp only [hcorr, measureReal_iUnion (μ := μ) hd hf, ← tsum_mul_right]
    refine tendsto_tsum_of_dominated_convergence (summable_measure_toReal (μ := μ) hf hd) ihf
      (.of_forall fun m i ↦ ?_)
    rw [Real.norm_of_nonneg measureReal_nonneg]
    exact measureReal_mono inter_subset_left

/-- **The π-system test for mixing.** For a probability measure invariant under a measurable
action, if the correlations of any two sets of a π-system `p` generating the σ-algebra converge
to the product of their measures along `l`, then the action is mixing along `l`. -/
@[to_additive /-- **The π-system test for mixing.** For a probability
measure invariant under a measurable additive action, if the correlations of any two sets of a
π-system `p` generating the σ-algebra converge to the product of their measures along `l`, then the
action is mixing along `l`. -/]
theorem MixingAlong.of_isPiSystem {p : Set (Set X)} (hgen : ‹MeasurableSpace X› = .generateFrom p)
    (hp : IsPiSystem p)
    (h : ∀ A ∈ p, ∀ B ∈ p,
      Tendsto (fun m : M ↦ μ.real (A ∩ (m • ·) ⁻¹' B)) l (𝓝 (μ.real A * μ.real B))) :
    MixingAlong M X μ l := by
  intro A B hA hB
  induction B, hB using MeasurableSpace.induction_on_inter hgen hp with
  | empty => simpa using tendsto_const_nhds
  | basic t ht =>
    exact tendsto_of_isPiSystem_left hgen hp (hgen ▸ .basic t ht) (fun A hA ↦ h A hA t ht) hA
  | compl t ht iht =>
    have hcorr (m : M) : μ.real (A ∩ (m • ·) ⁻¹' tᶜ) = μ.real A - μ.real (A ∩ (m • ·) ⁻¹' t) := by
      have := measureReal_inter_add_sdiff (μ := μ) (s := A) (ht.preimage (measurable_const_smul m))
      rw [sdiff_eq] at this
      rw [preimage_compl]
      linarith
    simp only [hcorr, measureReal_compl ht, probReal_univ, mul_sub, mul_one]
    exact tendsto_const_nhds.sub iht
  | iUnion f hd hf ihf =>
    have hf' (m : M) (i : ℕ) : MeasurableSet ((m • ·) ⁻¹' f i) :=
      (hf i).preimage (measurable_const_smul m)
    have hcorr (m : M) : μ.real (A ∩ (m • ·) ⁻¹' ⋃ i, f i) =
        ∑' i, μ.real (A ∩ (m • ·) ⁻¹' f i) := by
      rw [preimage_iUnion, inter_iUnion, measureReal_iUnion (μ := μ)
        (hd.mono fun _ _ h ↦ (h.preimage _).mono inter_subset_right inter_subset_right)
        (fun i ↦ hA.inter (hf' m i))]
    simp only [hcorr, measureReal_iUnion (μ := μ) hd hf, ← tsum_mul_left]
    refine tendsto_tsum_of_dominated_convergence (summable_measure_toReal (μ := μ) hf hd) ihf
      (.of_forall fun m i ↦ ?_)
    rw [Real.norm_of_nonneg measureReal_nonneg,
      ← (measurePreserving_smul m μ).measureReal_preimage (hf i).nullMeasurableSet]
    exact measureReal_mono inter_subset_right

end PiSystem

section Prod

variable [SMul M X] [SMul M Y] [MeasurableConstSMul M X] [MeasurableConstSMul M Y]
  [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] [SMulInvariantMeasure M X μ]
  [SMulInvariantMeasure M Y ν]

/-- **Mixing of products.** If two actions preserving probability measures are mixing along the
same filter, so is the diagonal action on the product. -/
@[to_additive AddMixingAlong.prod /-- **Mixing of products.** If two additive actions preserving
probability measures are mixing along the same filter, so is the diagonal action on the
product. -/]
theorem MixingAlong.prod (hX : MixingAlong M X μ l) (hY : MixingAlong M Y ν l) :
    MixingAlong M (X × Y) (μ.prod ν) l := by
  refine .of_isPiSystem generateFrom_prod.symm isPiSystem_prod ?_
  rintro _ ⟨A₁, hA₁, A₂, hA₂, rfl⟩ _ ⟨B₁, hB₁, B₂, hB₂, rfl⟩
  have hcorr (m : M) : (A₁ ×ˢ A₂) ∩ (m • ·) ⁻¹' (B₁ ×ˢ B₂) =
      (A₁ ∩ (m • ·) ⁻¹' B₁) ×ˢ (A₂ ∩ (m • ·) ⁻¹' B₂) := by
    ext ⟨x, y⟩
    simp only [mem_inter_iff, mem_prod, mem_preimage, Prod.smul_mk]
    tauto
  simp only [hcorr, measureReal_prod_prod]
  convert (hX hA₁ hB₁).mul (hY hA₂ hB₂) using 2
  ring

/-- **Mixing implies weak mixing.** An action mixing along a nontrivial filter, preserving a
probability measure, is weakly mixing. -/
@[to_additive /-- **Mixing implies weak mixing.** An additive action
mixing along a nontrivial filter, preserving a probability measure, is weakly mixing. -/]
theorem MixingAlong.weakMixingSMul [l.NeBot] (h : MixingAlong M X μ l) : WeakMixingSMul M X μ :=
  (h.prod h).ergodicSMul

end Prod

/-- **Mixing of a single map.** A map `T` is mixing for `μ`, in the sense that the correlations
`μ(A ∩ T^[n]⁻¹' B)` tend to `μ(A) μ(B)` as `n → ∞`, exactly when the action of its iterates is
mixing along the image of `atTop`. -/
theorem mixingAlong_iterateMulAct_iff {T : X → X} :
    MixingAlong (IterateMulAct T) X μ (map IterateMulAct.mk atTop) ↔
      ∀ ⦃A B : Set X⦄, MeasurableSet A → MeasurableSet B →
        Tendsto (fun n : ℕ ↦ μ.real (A ∩ T^[n] ⁻¹' B)) atTop (𝓝 (μ.real A * μ.real B)) := by
  simp only [mixingAlong_iff, tendsto_map'_iff, Function.comp_def, IterateMulAct.mk_smul]

end TauCeti

namespace MeasureTheory.MeasurePreserving

open TauCeti

variable {M X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y] [SMul M X] [SMul M Y]
  [MeasurableConstSMul M X] [MeasurableConstSMul M Y] {μ : Measure X} {ν : Measure Y}
  {e : X ≃ᵐ Y}

/-- **Mixing is invariant under isomorphism.** Along an equivariant measure-preserving measurable
equivalence, the target action is mixing along `l` exactly when the source action is. -/
@[to_additive addMixingAlong_iff /-- **Mixing is invariant under isomorphism.** Along an equivariant
measure-preserving measurable equivalence, the target additive action is mixing along `l` exactly
when the source action is. -/]
theorem mixingAlong_iff (he : MeasurePreserving e μ ν) (h : ∀ (m : M) (x : X), e (m • x) = m • e x)
    {l : Filter M} : MixingAlong M Y ν l ↔ MixingAlong M X μ l :=
  ⟨(IsFactorMapSMul.of_measurableEquiv_symm he h).mixingAlong,
    (IsFactorMapSMul.of_map_smul he h).mixingAlong⟩

/-- **Weak mixing is invariant under isomorphism.** Along an equivariant measure-preserving
measurable equivalence of s-finite measure spaces, the target action is weakly mixing exactly when
the source action is. -/
@[to_additive /-- **Weak mixing is invariant under isomorphism.** Along an equivariant
measure-preserving measurable equivalence of s-finite measure spaces, the target additive action is
weakly mixing exactly when the source action is. -/]
theorem weakMixingSMul_iff [SFinite μ] [SFinite ν] (he : MeasurePreserving e μ ν)
    (h : ∀ (m : M) (x : X), e (m • x) = m • e x) : WeakMixingSMul M Y ν ↔ WeakMixingSMul M X μ :=
  ⟨(IsFactorMapSMul.of_measurableEquiv_symm he h).weakMixingSMul,
    (IsFactorMapSMul.of_map_smul he h).weakMixingSMul⟩

end MeasureTheory.MeasurePreserving
