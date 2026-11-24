/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Colimit.CommonStage
public import TauCeti.RingTheory.Huber.LocalizationTopology.Away
public import TauCeti.RingTheory.Huber.Pair
public import TauCeti.RingTheory.IntegralClosure.DirectLimit

/-!
# Directed colimits of Tate pairs

Let `(Aᵢ, tᵢⱼ)` be a directed system of topological rings with continuous transition maps, and
let `φᵢ : Aᵢ → L` be compatible ring homomorphisms exhibiting `L` as its colimit. Let `A₀ᵢ ⊆ Aᵢ`
be open subrings (for instance compatible rings of definition), `L₀ ⊆ L` the union of their
images, and `ϖ'` the image of a pseudouniformiser `ϖ` of some stage. This file makes `L` a Tate
ring and the colimit of plus rings a ring of integral elements.

* `L` is the localisation `L₀[1/ϖ']` (`TauCeti.Huber.DirectLimit.isLocalization_away`), so it
  carries the `ϖ'`-adic topology `TauCeti.Huber.awayTopology`, whose neighbourhoods of zero have
  basis `ϖ'ⁿ L₀`. For it `L` is a Tate ring (`TauCeti.Huber.isTateRing_of_hasBasis`) and
  `(L₀, ϖ' L₀)` is a pair of definition (`TauCeti.Huber.PairOfDefinition.ofIsPseudoUniformizer`).
* For every group topology on `L` with this basis the maps `φᵢ` are continuous
  (`TauCeti.Huber.DirectLimit.continuous_of_hasBasis`), and the union `L⁺` of the images of plus
  rings `Aᵢ⁺ ⊇ A₀ᵢ` is a ring of integral elements
  (`TauCeti.Huber.DirectLimit.isRingOfIntegralElements_of_hasBasis`). So `(L, L⁺)` is a Huber
  pair and the `φᵢ` are continuous ring homomorphisms carrying `Aᵢ⁺` into `L⁺`; when the stages
  are Huber rings, they are morphisms of Huber pairs `(Aᵢ, Aᵢ⁺) → (L, L⁺)`.
* An ideal of definition contained in `ϖ L₀` consists of images of topologically nilpotent
  elements of the stages
  (`TauCeti.Huber.exists_isTopologicallyNilpotent_eq_of_mem_idealOfDefinition`): an element `ϖ c`
  with `c` coming from `A₀ⱼ` is the image of a product of a power-bounded and a topologically
  nilpotent element of a later stage.

The last item is the condition under which continuity of a valuation on `L`, and hence membership
in the adic spectrum of `L`, can be tested on the stages; see
`TauCeti/AlgebraicGeometry/AdicSpace/Spa/DirectLimit.lean`, where these results identify the adic
spectrum of a colimit of Tate pairs with the inverse limit of the adic spectra.

## Main results

* `TauCeti.Huber.exists_isTopologicallyNilpotent_eq_of_mem_idealOfDefinition`: an ideal of
  definition contained in `ϖ L₀` of a colimit of Tate rings consists of images of topologically
  nilpotent elements of the stages.
* `TauCeti.Huber.DirectLimit.isLocalization_away`: the colimit is `L₀[1/ϖ']`.
* `TauCeti.Huber.DirectLimit.continuous_of_hasBasis`: the maps into the colimit are continuous for
  the `ϖ'`-adic topology.
* `TauCeti.Huber.DirectLimit.isRingOfIntegralElements_of_hasBasis`: the colimit of the plus rings
  is a ring of integral elements.
* `TauCeti.Huber.DirectLimit.isTateRing_of_hasBasis`: the colimit Tate-ring instance.
* `TauCeti.Huber.DirectLimit.pair`, `TauCeti.Huber.DirectLimit.pairHom`: the bundled colimit
  Huber pair and the morphisms into it from stage Huber pairs.

## References

* K. S. Kedlaya, R. Liu, *Relative p-adic Hodge theory: foundations*, Astérisque 371 (2015),
  §2.6, Remark 2.6.3.
* P. Scholze, *Perfectoid spaces*, Publ. Math. IHÉS 116 (2012), §6, proof of Lemma 6.13(ii).
-/

public section

namespace TauCeti.Huber

variable {ι : Type*} [Preorder ι] [IsDirectedOrder ι] {A : ι → Type*} [∀ i, CommRing (A i)]
  [∀ i, TopologicalSpace (A i)] {t : ∀ i j, i ≤ j → A i →+* A j}
  {L : Type*} [CommRing L] [TopologicalSpace L] {φ : ∀ i, A i →+* L}
  (hφt : ∀ i j (h : i ≤ j) a, φ j (t i j h a) = φ i a)

include hφt in
/-- **The ideal of definition of a colimit of Tate rings consists of images of topologically
nilpotent elements.** Let `Qᵢ ⊆ Aᵢ` be subrings of power-bounded elements preserved by the
transition maps (for instance compatible rings of definition `A_{i,0}`), and let `(L₀, I)` be a
pair of definition of `L` with `L₀` contained in the union of the images of the `Qᵢ` and
`I ⊆ ϖ L₀` for the image of a topologically nilpotent `ϖ ∈ A_{i₀}`. Then every element of `I` is
the image of a topologically nilpotent element of some stage. -/
theorem exists_isTopologicallyNilpotent_eq_of_mem_idealOfDefinition
    (ht : ∀ i j (h : i ≤ j), Continuous (t i j h)) (Q : ∀ i, Subring (A i))
    (hQ : ∀ i, ∀ c ∈ Q i, IsPowerBounded c)
    (htQ : ∀ i j (h : i ≤ j), ∀ c ∈ Q i, t i j h c ∈ Q j)
    (P : PairOfDefinition L) (hP : ∀ c ∈ P.ringOfDefinition, ∃ i, ∃ c' ∈ Q i, φ i c' = c)
    {i₀ : ι} {ϖ : A i₀} (hϖ : IsTopologicallyNilpotent ϖ)
    (hI : ∀ a ∈ P.idealOfDefinition, ∃ c ∈ P.ringOfDefinition, φ i₀ ϖ * c = a)
    {a : P.ringOfDefinition} (ha : a ∈ P.idealOfDefinition) :
    ∃ i, ∃ y : A i, IsTopologicallyNilpotent y ∧ φ i y = a := by
  obtain ⟨c, hc, hca⟩ := hI a ha
  -- `ϖ c` with `c` the image of `c' ∈ Qⱼ` is the image of the product of the power-bounded `c'`
  -- and the topologically nilpotent `ϖ` at a stage above `i₀` and `j`
  obtain ⟨j, c', hc', rfl⟩ := hP c hc
  obtain ⟨k, hjk, hi₀k⟩ := directed_of (· ≤ ·) j i₀
  refine ⟨k, t j k hjk c' * t i₀ k hi₀k ϖ,
    (hQ k _ (htQ j k hjk c' hc')).isTopologicallyNilpotent_mul (hϖ.map (ht i₀ k hi₀k)), ?_⟩
  rw [map_mul, hφt, hφt, mul_comm, hca]

namespace DirectLimit

open Topology

/-! ### The colimit of Tate pairs

Let `A₀ᵢ ⊆ Aᵢ` be open subrings, `L₀ ⊆ L` a subring containing their images and `ϖ` a
pseudouniformiser of a stage `A_{i₀}`, with image `ϖ' ∈ L₀`. The topology on `L` is any group
topology whose neighbourhoods of zero have basis `ϖ'ⁿ L₀`, such as `TauCeti.Huber.awayTopology`. -/

section Tate

variable [∀ i, IsTopologicalRing (A i)] (ht : ∀ i j (h : i ≤ j), Continuous (t i j h))
  (A₀ : ∀ i, Subring (A i)) (hA₀ : ∀ i, IsOpen (A₀ i : Set (A i)))
  {L₀ : Subring L} (hφA₀ : ∀ i, ∀ a ∈ A₀ i, φ i a ∈ L₀)
  {i₀ : ι} {ϖ : A i₀} (hϖ : IsPseudoUniformizer ϖ) {ϖ' : L₀} (hϖ' : (ϖ' : L) = φ i₀ ϖ)

omit [TopologicalSpace L] in
include hφt ht hA₀ hφA₀ hϖ hϖ' in
/-- Every element of a stage `Aᵢ` is mapped into `L₀` after multiplication by a power of `ϖ'`. -/
private theorem exists_pow_mul_map_mem (i : ι) (a : A i) : ∃ n, (ϖ' : L) ^ n * φ i a ∈ L₀ := by
  -- at a stage `j` above `i` and `i₀`, the powers of the image of `ϖ` times the image of `a`
  -- tend to zero, so they eventually lie in the open subring `A₀ⱼ`
  obtain ⟨j, hij, hi₀j⟩ := directed_of (· ≤ ·) i i₀
  have hlim := ((hϖ.isTopologicallyNilpotent.map (ht i₀ j hi₀j)).mul_const (t i j hij a))
  rw [zero_mul] at hlim
  obtain ⟨n, hn⟩ := (hlim.eventually ((hA₀ j).mem_nhds (A₀ j).zero_mem)).exists
  refine ⟨n, ?_⟩
  simpa only [map_mul, map_pow, hφt, hϖ'] using hφA₀ j _ hn

omit [TopologicalSpace L] in
include hφt ht hA₀ hφA₀ hϖ hϖ' in
/-- **The colimit is `L₀[1/ϖ']`.** If every element of `L` comes from a stage, then `L` is the
localisation of any subring `L₀` containing the images of the `A₀ᵢ` away from the image `ϖ'` of
the pseudouniformiser `ϖ`. In particular `L` carries the `ϖ'`-adic topology
`TauCeti.Huber.awayTopology ϖ' L`. -/
theorem isLocalization_away (hcover : ∀ x : L, ∃ i a, φ i a = x) :
    IsLocalization.Away ϖ' L := by
  refine .mk ϖ' ?_ (fun x ↦ ?_) fun a b hab ↦ ⟨0, by simp [Subtype.ext hab]⟩
  · simpa [Algebra.algebraMap_ofSubsemiring_apply, hϖ'] using hϖ.isUnit.map (φ i₀)
  · obtain ⟨i, a, rfl⟩ := hcover x
    obtain ⟨n, hn⟩ := exists_pow_mul_map_mem hφt ht A₀ hA₀ hφA₀ hϖ hϖ' i a
    refine ⟨n, ⟨_, hn⟩, ?_⟩
    simp only [Algebra.algebraMap_ofSubsemiring_apply, mul_comm]

variable
  (h : (𝓝 (0 : L)).HasBasis (fun _ : ℕ ↦ True) fun n ↦ (awayNhd ϖ' L n : Set L))

include hφt ht hA₀ hφA₀ hϖ hϖ' h in
/-- **The maps into the colimit are continuous** for any group topology on `L` whose
neighbourhoods of zero have basis `ϖ'ⁿ L₀`: a neighbourhood `ϖ'ⁿ L₀` pulls back, at a stage `j`
above `i` and `i₀`, to the preimage of the open subgroup `ϖⁿ A₀ⱼ`. -/
theorem continuous_of_hasBasis [IsTopologicalAddGroup L] (i : ι) : Continuous (φ i) := by
  refine continuous_of_continuousAt_zero (φ i) ?_
  rw [ContinuousAt, map_zero, h.tendsto_right_iff]
  intro n _
  -- `a ↦ ϖⱼ⁻ⁿ tᵢⱼ(a)` is continuous, so it lands in the open `A₀ⱼ` near zero
  obtain ⟨j, hij, hi₀j⟩ := directed_of (· ≤ ·) i i₀
  obtain ⟨u, hu⟩ := (hϖ.isUnit.map (t i₀ j hi₀j)).pow n
  have hcont : Continuous fun a ↦ (↑u⁻¹ : A j) * t i j hij a := (ht i j hij).const_mul _
  filter_upwards [hcont.continuousAt.preimage_mem_nhds (by
    simpa using (hA₀ j).mem_nhds (A₀ j).zero_mem)] with a ha
  refine mem_awayNhd.mpr ⟨⟨_, hφA₀ j _ ha⟩, ?_⟩
  have hu' : (ϖ' : L) ^ n = φ j u := by rw [hu, map_pow, hφt, hϖ']
  rw [Algebra.algebraMap_ofSubsemiring_apply, Subring.coe_mul, SubmonoidClass.coe_pow, hu',
    ← map_mul, Units.mul_inv_cancel_left, hφt]

include hφt ht hA₀ hφA₀ hϖ hϖ' h in
/-- The image of a power-bounded element of a stage above `i₀` is power-bounded: some power of
`ϖ'` carries all its powers into the bounded subring `L₀`. -/
private theorem isPowerBounded_map [IsTopologicalRing L] {j : ι} (hi₀j : i₀ ≤ j) {a : A j}
    (ha : IsPowerBounded a) : IsPowerBounded (φ j a) := by
  have hU : φ j ⁻¹' L₀ ∈ 𝓝 (0 : A j) :=
    (continuous_of_hasBasis hφt ht A₀ hA₀ hφA₀ hϖ hϖ' h j).continuousAt.preimage_mem_nhds
      (by simpa using (isOpen_subring_of_hasBasis h).mem_nhds L₀.zero_mem)
  obtain ⟨V, hV, hVU⟩ := isBounded_iff.mp (isPowerBounded_iff.mp ha) _ hU
  obtain ⟨k, hk⟩ := ((hϖ.isTopologicallyNilpotent.map (ht i₀ j hi₀j)).eventually_mem hV).exists
  obtain ⟨u, hu⟩ := (hϖ.isUnit.map (φ i₀)).pow k
  have hmem (n : ℕ) : (u : L) * φ j a ^ n ∈ L₀ := by
    simpa [hu, hφt] using hVU (Set.mul_mem_mul hk ⟨n, rfl⟩)
  refine isPowerBounded_iff.mpr
    (((isBounded_singleton (↑u⁻¹ : L)).mul (isBounded_subring_of_hasBasis h)).subset ?_)
  rintro _ ⟨n, rfl⟩
  exact Set.mem_mul.mpr ⟨_, Set.mem_singleton _, _, hmem n, by simp⟩

include hφt ht hA₀ hφA₀ hϖ hϖ' h in
/-- **The colimit of plus rings is a ring of integral elements.** Let `Aᵢ⁺ ⊆ Aᵢ` be subrings
integrally closed in `Aᵢ`, consisting of power-bounded elements, containing `A₀ᵢ` and preserved by
the transition maps, and let `L⁺ ⊆ L` be the union of their images. If `L` is the colimit of the
`Aᵢ` and `L₀` the union of the images of the `A₀ᵢ`, then `L⁺` is a ring of integral elements of
`L` for the `ϖ'`-adic topology. So `(L, L⁺)` is a Huber pair, and the maps `φᵢ`, which are
continuous by `continuous_of_hasBasis` and carry `Aᵢ⁺` into `L⁺`, are morphisms of Huber pairs
`(Aᵢ, Aᵢ⁺) → (L, L⁺)` whenever the stages are Huber rings. -/
theorem isRingOfIntegralElements_of_hasBasis [NonarchimedeanRing L]
    (hcover : ∀ x : L, ∃ i a, φ i a = x)
    (hker : ∀ i (a b : A i), φ i a = φ i b → ∃ j, ∃ h : i ≤ j, t i j h a = t i j h b)
    (hL₀ : ∀ x ∈ L₀, ∃ i, ∃ a ∈ A₀ i, φ i a = x) (Aplus : ∀ i, Subring (A i))
    [∀ i, IsIntegrallyClosedIn (Aplus i) (A i)] (hAplus : ∀ i, ∀ a ∈ Aplus i, IsPowerBounded a)
    (hA₀plus : ∀ i, A₀ i ≤ Aplus i) (htplus : ∀ i j (h : i ≤ j), ∀ a ∈ Aplus i, t i j h a ∈ Aplus j)
    {Lplus : Subring L} (hφplus : ∀ i, ∀ a ∈ Aplus i, φ i a ∈ Lplus)
    (hLplus : ∀ x ∈ Lplus, ∃ i, ∃ a ∈ Aplus i, φ i a = x) :
    IsRingOfIntegralElements Lplus where
  isOpen := AddSubgroup.isOpen_mono (H₁ := L₀.toAddSubgroup) (H₂ := Lplus.toAddSubgroup)
    (fun x hx ↦ by
      obtain ⟨i, a, ha, rfl⟩ := hL₀ x hx
      exact hφplus i a (hA₀plus i ha))
    (isOpen_subring_of_hasBasis h)
  isIntegrallyClosedIn :=
    TauCeti.DirectLimit.isIntegrallyClosedIn hφt hcover hker Aplus htplus hφplus hLplus
  le_powerBoundedSubring x hx := by
    obtain ⟨i, a, ha, rfl⟩ := hLplus x hx
    obtain ⟨j, hij, hi₀j⟩ := directed_of (· ≤ ·) i i₀
    rw [← hφt i j hij]
    exact mem_powerBoundedSubring.mpr (isPowerBounded_map hφt ht A₀ hA₀ hφA₀ hϖ hϖ' h hi₀j
      (hAplus j _ (htplus i j hij a ha)))

include hφt ht hA₀ hφA₀ hϖ hϖ' h in
/-- The colimit is a Tate ring for the topology with basis `ϖ'ⁿ L₀`. This supplies the
ambient instance for the bundled colimit pair and its morphisms. -/
theorem isTateRing_of_hasBasis [IsTopologicalRing L] (hcover : ∀ x : L, ∃ i a, φ i a = x) :
    IsTateRing L := by
  let := isLocalization_away hφt ht A₀ hA₀ hφA₀ hϖ hϖ' hcover
  exact TauCeti.Huber.isTateRing_of_hasBasis h

section Bundled

variable [IsTopologicalRing L] (hcover : ∀ x : L, ∃ i a, φ i a = x)
  (hker : ∀ i (a b : A i), φ i a = φ i b → ∃ j, ∃ h : i ≤ j, t i j h a = t i j h b)
  (hL₀ : ∀ x ∈ L₀, ∃ i, ∃ a ∈ A₀ i, φ i a = x) (Aplus : ∀ i, Subring (A i))
  [∀ i, IsIntegrallyClosedIn (Aplus i) (A i)] (hAplus : ∀ i, ∀ a ∈ Aplus i, IsPowerBounded a)
  (hA₀plus : ∀ i, A₀ i ≤ Aplus i) (htplus : ∀ i j (h : i ≤ j), ∀ a ∈ Aplus i, t i j h a ∈ Aplus j)
  {Lplus : Subring L} (hφplus : ∀ i, ∀ a ∈ Aplus i, φ i a ∈ Lplus)
  (hLplus : ∀ x ∈ Lplus, ∃ i, ∃ a ∈ Aplus i, φ i a = x)

/-- The colimit Huber pair for the topology with basis `ϖ'ⁿ L₀`, with plus ring the union
of the images of the stage plus rings. Its Huber structure is supplied by
`isTateRing_of_hasBasis`. -/
def pair :
    letI := isTateRing_of_hasBasis hφt ht A₀ hA₀ hφA₀ hϖ hϖ' h hcover
    Pair L :=
  letI := isTateRing_of_hasBasis hφt ht A₀ hA₀ hφA₀ hϖ hϖ' h hcover
  { plus := Lplus
    isRingOfIntegralElements := isRingOfIntegralElements_of_hasBasis hφt ht A₀ hA₀ hφA₀ hϖ hϖ' h
      hcover hker hL₀ Aplus hAplus hA₀plus htplus hφplus hLplus }

/-- The plus ring of the colimit pair is `Lplus`. -/
@[simp]
theorem pair_plus :
    letI := isTateRing_of_hasBasis hφt ht A₀ hA₀ hφA₀ hϖ hϖ' h hcover
    (pair hφt ht A₀ hA₀ hφA₀ hϖ hϖ' h hcover hker hL₀ Aplus hAplus hA₀plus htplus
      hφplus hLplus).plus = Lplus := (rfl)

/-- The map from a stage Huber pair to the colimit pair. The source may have any ring of
integral elements contained in the chosen stage plus ring. -/
def pairHom (i : ι) [IsHuberRing (A i)] (S : Pair (A i)) (hS : S.plus ≤ Aplus i) :
    letI := isTateRing_of_hasBasis hφt ht A₀ hA₀ hφA₀ hϖ hϖ' h hcover
    Pair.Hom S (pair hφt ht A₀ hA₀ hφA₀ hϖ hϖ' h hcover hker hL₀ Aplus hAplus hA₀plus htplus
      hφplus hLplus) :=
  letI := isTateRing_of_hasBasis hφt ht A₀ hA₀ hφA₀ hϖ hϖ' h hcover
  { toRingHom := φ i
    continuous_toRingHom := continuous_of_hasBasis hφt ht A₀ hA₀ hφA₀ hϖ hϖ' h i
    map_mem_plus a ha := hφplus i a (hS ha) }

/-- The underlying ring homomorphism of the stage morphism is `φ i`. -/
@[simp]
theorem pairHom_toRingHom (i : ι) [IsHuberRing (A i)] (S : Pair (A i)) (hS : S.plus ≤ Aplus i) :
    letI := isTateRing_of_hasBasis hφt ht A₀ hA₀ hφA₀ hϖ hϖ' h hcover
    (pairHom hφt ht A₀ hA₀ hφA₀ hϖ hϖ' h hcover hker hL₀ Aplus hAplus hA₀plus htplus
      hφplus hLplus i S hS).toRingHom = φ i := (rfl)

end Bundled

end Tate

end DirectLimit

end TauCeti.Huber
