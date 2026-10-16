/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.LocalHomology.MayerVietoris

/-!
# Local homology of finite unions of convex sets in a chart

Let `M` be a Hausdorff space and `φ : M → E` an open partial homeomorphism to a real normed space
of finite dimension `n`, such as a chart of a topological `n`-manifold. This file proves the
finite-union case of Hatcher's Lemma 3.27: if `L = φ.symm '' (K₁ ∪ ⋯ ∪ Kₘ)` for compact convex
sets `Kᵢ ⊆ φ.target`, then

* the local homology `Hₖ(M, M ∖ L)` vanishes for `k > n`
  (`TauCeti.isZero_localHomology_symm_image_iUnion`), and
* a morphism into `Hₙ(M, M ∖ L)` is determined by its composites with the restrictions to the
  local homology groups `Hₙ(M, M ∖ {x})` at the points `x ∈ L`
  (`TauCeti.localHomology_symm_image_iUnion_hom_ext`).

With coefficients in a module, the second statement says that a class of `Hₙ(M, M ∖ L)` vanishes
when its images in all `Hₙ(M, M ∖ {x})`, `x ∈ L`, vanish. These are the properties from which the
fundamental class of a closed manifold is assembled.

The proof is Hatcher's induction on the number of convex pieces. For a single convex piece
containing `φ x`, the restriction to `x` is an isomorphism
(`TauCeti.isIso_localHomologyRestriction_symm_image`). The induction step applies the relative
Mayer–Vietoris sequence of the complements of two closed sets `A` and `B`,
`⋯ ⟶ Hₖ₊₁(M, M ∖ (A ∩ B)) ⟶ Hₖ(M, M ∖ (A ∪ B)) ⟶ Hₖ(M, M ∖ A) ⊞ Hₖ(M, M ∖ B) ⟶ ⋯`,
to `A = L₁ ∪ ⋯ ∪ Lₘ₋₁` and `B = Lₘ`, where `A ∩ B` is again a union of `m - 1` convex pieces of
the same chart. The two consequences of that sequence used in the step hold for any closed sets:
`TauCeti.isZero_localHomology_union` and `TauCeti.localHomology_hom_ext_of_union`.

## References

* A. Hatcher, *Algebraic Topology*, Section 3.3, Lemma 3.27, steps (1) and (2) of its proof.
-/

public section

noncomputable section

open CategoryTheory Limits Set Module

universe w v u

namespace TauCeti

variable {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Abelian C] (R : C)

section Chart

variable {M : Type w} [TopologicalSpace M] [T2Space M] {E : Type w} [NormedAddCommGroup E]
  [NormedSpace ℝ E] [FiniteDimensional ℝ E] (φ : OpenPartialHomeomorph M E) {n : ℕ}

/-- The two conclusions of Hatcher's Lemma 3.27 for a set `L` in an `n`-manifold: local homology
along `L` vanishes above degree `n`, and in degree `n` it is detected by the restrictions to the
points of `L`. -/
private def Detected (n : ℕ) (L : Set M) : Prop :=
  (∀ k, n < k → IsZero (localHomology R L k)) ∧
    ∀ ⦃T : C⦄ (g₁ g₂ : T ⟶ localHomology R L n),
      (∀ x (hx : x ∈ L), g₁ ≫ localHomologyRestriction R (singleton_subset_iff.2 hx) n =
        g₂ ≫ localHomologyRestriction R (singleton_subset_iff.2 hx) n) → g₁ = g₂

omit [T2Space M] in
private lemma detected_empty : Detected R n (∅ : Set M) :=
  ⟨fun k _ ↦ isZero_localHomology_empty R k,
    fun _ _ _ _ ↦ (isZero_localHomology_empty R n).eq_of_tgt _ _⟩

omit [T2Space M] in
private lemma Detected.union {A B : Set M} (hA : IsClosed A) (hB : IsClosed B)
    (dA : Detected R n A) (dB : Detected R n B) (dAB : Detected R n (A ∩ B)) :
    Detected R n (A ∪ B) := by
  refine ⟨fun k hk ↦ isZero_localHomology_union hA hB (dA.1 k hk) (dB.1 k hk)
    (dAB.1 (k + 1) (by lia)), fun T g₁ g₂ h ↦ ?_⟩
  refine localHomology_hom_ext_of_union hA hB (dAB.1 (n + 1) (by lia))
    (dA.2 _ _ fun x hx ↦ ?_) (dB.2 _ _ fun x hx ↦ ?_)
  · simpa only [Category.assoc, localHomologyRestriction_comp] using h x (subset_union_left hx)
  · simpa only [Category.assoc, localHomologyRestriction_comp] using h x (subset_union_right hx)

/-- Lemma 3.27 for one compact convex set `K` in a chart: local homology along `φ.symm '' K`
vanishes above degree `n` and is detected at points in degree `n`. Detection follows by choosing a
point `x` of `φ.symm '' K`: the restriction to `x` is an isomorphism, hence a monomorphism. -/
private lemma detected_symm_image_of_convex (hn : finrank ℝ E = n) {K : Set E}
    (hK : Convex ℝ K) (hKk : IsCompact K) (hKφ : K ⊆ φ.target) :
    Detected R n (φ.symm '' K) := by
  rcases K.eq_empty_or_nonempty with rfl | ⟨y, hy⟩
  · rw [image_empty]
    exact detected_empty R
  have hx : φ.symm y ∈ φ.source := φ.map_target (hKφ hy)
  have hxK : φ (φ.symm y) ∈ K := (φ.right_inv (hKφ hy)).symm ▸ hy
  have := isIso_localHomologyRestriction_symm_image R φ (hK.starConvex hxK) hKk hKφ hx hxK n
  refine ⟨fun k hk ↦ isZero_singularHomology_compl_symm_image_of_ne R φ hx (hK.starConvex hxK)
    hxK hKk.isBounded hKk.isClosed (φ.isClosed_image_symm_of_isCompact hKk hKφ) hKφ hn
    (by lia),
    fun T g₁ g₂ h ↦ ?_⟩
  exact (cancel_mono (localHomologyRestriction R
    (singleton_subset_iff.2 ⟨φ (φ.symm y), hxK, φ.left_inv hx⟩ : {φ.symm y} ⊆ φ.symm '' K) n)).1
    (h _ ⟨φ (φ.symm y), hxK, φ.left_inv hx⟩)

/-- Lemma 3.27 for a union of compact convex sets of a chart indexed by a finset, by induction on
the finset. The intersection of the new piece with the union of the others is again such a union,
indexed by the smaller finset, which is why the statement is quantified over all families. -/
private lemma detected_symm_image_biUnion (hn : finrank ℝ E = n) {ι : Type*} (s : Finset ι) :
    ∀ K : ι → Set E, (∀ i ∈ s, Convex ℝ (K i) ∧ IsCompact (K i) ∧ K i ⊆ φ.target) →
      Detected R n (φ.symm '' ⋃ i ∈ s, K i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro K _
    simpa using detected_empty R
  | insert a s _ ih =>
    intro K hK
    obtain ⟨hKa, hKak, hKaφ⟩ := hK a (Finset.mem_insert_self a s)
    have hKs (i : ι) (hi : i ∈ s) := hK i (Finset.mem_insert_of_mem hi)
    have hsφ : ⋃ i ∈ s, K i ⊆ φ.target := iUnion₂_subset fun i hi ↦ (hKs i hi).2.2
    have hsk : IsCompact (⋃ i ∈ s, K i) := s.isCompact_biUnion fun i hi ↦ (hKs i hi).2.1
    rw [Finset.set_biUnion_insert, image_union]
    refine (detected_symm_image_of_convex R φ hn hKa hKak hKaφ).union R
      (φ.isClosed_image_symm_of_isCompact hKak hKaφ)
      (φ.isClosed_image_symm_of_isCompact hsk hsφ)
      (ih K hKs) ?_
    -- The intersection of the new piece with the others is the union of the convex sets
    -- `K a ∩ K i`, since `φ.symm` is injective on `φ.target`.
    rw [← φ.symm.injOn.image_inter hKaφ hsφ, inter_iUnion₂]
    exact ih (fun i ↦ K a ∩ K i) fun i hi ↦ ⟨hKa.inter (hKs i hi).1,
      hKak.inter_right (hKs i hi).2.1.isClosed, inter_subset_left.trans hKaφ⟩

variable {ι : Type*} [Finite ι] {K : ι → Set E}

private lemma detected_symm_image_iUnion (hn : finrank ℝ E = n) (hK : ∀ i, Convex ℝ (K i))
    (hKk : ∀ i, IsCompact (K i)) (hKφ : ∀ i, K i ⊆ φ.target) :
    Detected R n (φ.symm '' ⋃ i, K i) := by
  have := Fintype.ofFinite ι
  simpa using detected_symm_image_biUnion R φ hn Finset.univ K fun i _ ↦ ⟨hK i, hKk i, hKφ i⟩

/-- **Local homology of a finite union of convex sets vanishes above the dimension** (Hatcher,
Lemma 3.27, finite-union case). Let `φ : M → E` be an open partial homeomorphism from a Hausdorff
space to a real normed space of finite dimension `n`, and let `L = φ.symm '' ⋃ i, K i` for finitely
many compact convex sets `K i ⊆ φ.target`. Then `Hₖ(M, M ∖ L)` vanishes for `k > n`. -/
theorem isZero_localHomology_symm_image_iUnion (hn : finrank ℝ E = n) (hK : ∀ i, Convex ℝ (K i))
    (hKk : ∀ i, IsCompact (K i)) (hKφ : ∀ i, K i ⊆ φ.target) {k : ℕ} (hk : n < k) :
    IsZero (localHomology R (φ.symm '' ⋃ i, K i) k) :=
  (detected_symm_image_iUnion R φ hn hK hKk hKφ).1 k hk

/-- **Local homology of a finite union of convex sets is detected at points** (Hatcher,
Lemma 3.27, finite-union case). Let `φ : M → E` be an open partial homeomorphism from a Hausdorff
space to a real normed space of finite dimension `n`, and let `L = φ.symm '' ⋃ i, K i` for finitely
many compact convex sets `K i ⊆ φ.target`. Then a morphism into `Hₙ(M, M ∖ L)` is determined by
its composites with the restrictions to `Hₙ(M, M ∖ {x})` for `x ∈ L`. -/
theorem localHomology_symm_image_iUnion_hom_ext (hn : finrank ℝ E = n)
    (hK : ∀ i, Convex ℝ (K i)) (hKk : ∀ i, IsCompact (K i)) (hKφ : ∀ i, K i ⊆ φ.target) {T : C}
    {g₁ g₂ : T ⟶ localHomology R (φ.symm '' ⋃ i, K i) n}
    (h : ∀ x (hx : x ∈ φ.symm '' ⋃ i, K i),
      g₁ ≫ localHomologyRestriction R (singleton_subset_iff.2 hx) n =
        g₂ ≫ localHomologyRestriction R (singleton_subset_iff.2 hx) n) :
    g₁ = g₂ :=
  (detected_symm_image_iUnion R φ hn hK hKk hKφ).2 g₁ g₂ h

end Chart

end TauCeti
