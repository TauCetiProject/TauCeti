/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Homotopy.Relative.CellDimension
public import TauCeti.AlgebraicTopology.Singular.Triple
public import TauCeti.Geometry.Manifold.Morse.Cell.Homology
public import TauCeti.Geometry.Manifold.Morse.Exhaustion
public import TauCeti.Geometry.Manifold.Morse.OpenEmbedding

import TauCeti.Topology.Homotopy.DeformationRetract

/-!
# Low-degree connectivity across Morse bands and compactified pairs

Let `X` be a Hausdorff space, `F : X → ℝ` a continuous function, and `j : M → X` an open embedding
of a boundaryless manifold on which `F ∘ j` is Morse. Across a compact band `F⁻¹[a, b]` with
`F < a` outside `range j`, where `a ≤ b` are regular values of `F ∘ j` and every critical point of
`F ∘ j` in the band has Morse index at least `n`, only cells of dimension at least `n` are attached:

* in homotopy, the sublevel pair `({F ≤ b}, {F ≤ a})` has trivial relative homotopy sets in degrees
  `1 ≤ k < n` (`TauCeti.IsMorse.subsingleton_relHomotopyGroup_sublevelPair_of_isOpenEmbedding`), and
  the inclusion `{F ≤ a} ↪ {F ≤ b}` induces surjections `π_k({F ≤ a}, x₀) → π_k({F ≤ b}, x₀)` for
  `k < n` and bijections for `k + 1 < n`;
* in homology, the relative singular homology `H_k({F ≤ b}, {F ≤ a}; R)` vanishes for `k < n` in
  every abelian category with coproducts
  (`TauCeti.IsMorse.isZero_singularHomology_sublevelPair_of_isOpenEmbedding`), so
  `{F ≤ a} ↪ {F ≤ b}` induces epimorphisms on `H_k` for `k < n` and isomorphisms for `k + 1 < n`.

Taking `j = id` specializes these statements to a Morse function on `M` itself.

Now suppose `A ⊆ X` lies in `{F ≤ 0}`, `F ≤ 0` outside `range j`, `F` is bounded above, every
positive band `F⁻¹[a, b]` is compact, and `A` sits inside a subset `W ⊆ X` containing some positive
sublevel `{F ≤ δ}` (`δ > 0`) such that the inclusion `A ↪ W` is a weak homotopy equivalence (or
induces homology isomorphisms in the relevant degrees, for instance when `W` deformation retracts
onto `A`). Choosing a regular value `0 < a < δ` sandwiches `{F ≤ a}` into `A ↪ {F ≤ a} ↪ W ↪ X`:
the composite `A ↪ W` is an equivalence while `{F ≤ a} ↪ X` has the low-degree connectivity above,
forcing the inclusion `A ↪ X` to inherit the same low-degree homotopy and homology connectivity
without any smoothness assumption on `X` along `A`.

## Main results

* `TauCeti.IsMorse.subsingleton_relHomotopyGroup_sublevelPair_of_isOpenEmbedding`,
  `TauCeti.IsMorse.surjective_homotopyGroupMap_sublevelInclusion_of_isOpenEmbedding`,
  `TauCeti.IsMorse.bijective_homotopyGroupMap_sublevelInclusion_of_isOpenEmbedding`: homotopy
  connectivity across a compact band on a space with an open manifold part (and their manifold
  specializations without `_of_isOpenEmbedding`).
* `TauCeti.IsMorse.isZero_singularHomology_sublevelPair_of_isOpenEmbedding`,
  `TauCeti.IsMorse.epi_homologyMap_sublevelInclusion_of_isOpenEmbedding`,
  `TauCeti.IsMorse.isIso_homologyMap_sublevelInclusion_of_isOpenEmbedding`: low-degree homology
  vanishing and inclusion-induced epimorphisms/isomorphisms across a compact band (and their
  manifold specializations without `_of_isOpenEmbedding`).
* `TauCeti.IsMorse.subsingleton_relHomotopyGroup_ofSubset_of_isOpenEmbedding`,
  `TauCeti.IsMorse.surjective_homotopyGroupMap_subtypeVal_of_isOpenEmbedding`,
  `TauCeti.IsMorse.bijective_homotopyGroupMap_subtypeVal_of_isOpenEmbedding`,
  `TauCeti.IsMorse.isZero_singularHomology_ofSubset_of_isOpenEmbedding`: homotopy and homology
  connectivity of `(X, A)` when `A` has a weak-equivalence / degreewise homology-isomorphic
  neighbourhood containing a positive sublevel of `F`.

## References

* J. Milnor, *Morse Theory*, Annals of Mathematics Studies 51, Princeton University Press, 1963,
  Theorems 3.1 and 3.2, and Section 7 (Theorem 7.4).
* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 4.1, Corollary 4.12.
-/

public section

noncomputable section

open CategoryTheory Limits Function Set Topology Topology.RelCWComplex
open scoped ContDiff ContinuousMap Manifold Topology.Homotopy

universe u v w

namespace TauCeti

section BandInduction

variable {E H : Type*} {M X : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [FiniteDimensional ℝ E]
  [I.Boundaryless] [IsManifold I ∞ M] [T2Space M] [TopologicalSpace X]
  {j : M → X} {F : X → ℝ} {n : ℕ}

/-- Induction across the finitely many critical levels in a compact band `F⁻¹[a, b]` between regular
values of `F ∘ j` whose critical points all have Morse index at least `n`, supplying the strong
deformation retraction on regular bands and the finite high-index relative CW complex across each
critical level via `IsMorse.band_induction`. -/
private theorem IsMorse.sublevelBand_induction (hj : IsOpenEmbedding j) (hF : Continuous F)
    (hf : IsMorse I (F ∘ j)) {a b : ℝ} (hab : a ≤ b) (hcompact : IsCompact (F ⁻¹' Icc a b))
    (hA : ∀ x ∉ range j, F x < a) (ha : IsRegularValue I 𝓘(ℝ) (F ∘ j) a)
    (hb : IsRegularValue I 𝓘(ℝ) (F ∘ j) b)
    (hindex : ∀ p ∈ criticalPoints I (F ∘ j) ∩ (F ∘ j) ⁻¹' Icc a b,
      n ≤ manifoldMorseIndex I (F ∘ j) p)
    {P : ∀ s t : ℝ, s ≤ t → Prop}
    (hreg : ∀ {s t : ℝ} (hst : s ≤ t) (r : C({x | F x ≤ t}, {x | F x ≤ s})),
      LeftInverse r (ContinuousMap.inclusion (sublevel_mono F hst)) →
      (((ContinuousMap.inclusion (sublevel_mono F hst)).comp r).HomotopyRel
        (ContinuousMap.id _) {x | (x : X) ∈ {x | F x ≤ s}}) →
      P s t hst)
    (hcell : ∀ {c ε : ℝ} (hε : 0 < ε) (C' : Set X) [RelCWComplex C' {x | F x ≤ c - ε}]
      [RelCWComplex.Finite C'] (hC' : C' ⊆ {x | F x ≤ c + ε}),
      (∀ m < n, IsEmpty (cell C' m)) →
      ∀ (r : C({x | F x ≤ c + ε}, C')), LeftInverse r (ContinuousMap.inclusion hC') →
      (((ContinuousMap.inclusion hC').comp r).HomotopyRel
        (ContinuousMap.id _) {y | (y : X) ∈ C'}) →
      P (c - ε) (c + ε) (by linarith))
    (htrans : ∀ {s m t : ℝ} (hsm : s ≤ m) (hmt : m ≤ t),
      P s m hsm → P m t hmt → P s t (hsm.trans hmt)) :
    P a b hab := by
  have hcompact_sub {s t : ℝ} (hs : a ≤ s) (ht : t ≤ b) : IsCompact (F ⁻¹' Icc s t) :=
    hcompact.of_isClosed_subset (isClosed_Icc.preimage hF) (preimage_mono (Icc_subset_Icc hs ht))
  refine hf.band_induction (P := fun s t hst ↦ a ≤ s → t ≤ b → P s t hst) hab
    (hj.isInducing.isCompact_comp_preimage_Icc hA hcompact) ha hb
    (fun s t hst _ hcrit hs ht ↦ ?_)
    (fun p _ hac hcb δ hδ _ ↦ ?_)
    (fun s m t hsm hmt _ h₁ h₂ hs ht ↦
      htrans hsm hmt (h₁ hs (hmt.trans ht)) (h₂ (hs.trans hsm) ht))
    le_rfl le_rfl
  · obtain ⟨r, hri, ⟨G⟩⟩ := exists_sublevelDeformation_of_isOpenEmbedding hj hF hf.contMDiff hst
      (hcompact_sub hs ht)
      (fun p hsp hpt hp ↦ hcrit p (mem_criticalPoints_iff_mfderiv_eq_zero.2 hp) ⟨hsp, hpt⟩)
      fun x hx ↦ (hA x hx).trans_le hs
    rw [sublevelInclusion_eq_inclusion] at hri G
    exact hreg hst r hri G
  · set δ₀ : ℝ := min δ (min (F (j p) - a) (b - F (j p)) / 2) with hδ₀_def
    have hδ₀ : 0 < δ₀ := lt_min hδ (half_pos (lt_min (sub_pos.2 hac) (sub_pos.2 hcb)))
    have hδ₀a : a < F (j p) - δ₀ := by
      linarith [hδ₀_def, min_le_right δ (min (F (j p) - a) (b - F (j p)) / 2),
        min_le_left (F (j p) - a) (b - F (j p))]
    have hδ₀b : F (j p) + δ₀ < b := by
      linarith [hδ₀_def, min_le_right δ (min (F (j p) - a) (b - F (j p)) / 2),
        min_le_right (F (j p) - a) (b - F (j p))]
    obtain ⟨ε, hε, hεδ₀, C', _, _, hC', hcell', r, hri, ⟨G⟩⟩ :=
      hf.exists_relCWComplex_sublevel_of_isOpenEmbedding hj hF hδ₀ (hcompact_sub hδ₀a.le hδ₀b.le)
        fun x hx ↦ (hA x hx).trans hδ₀a
    refine ⟨ε, hε, hεδ₀.trans (min_le_left _ _), fun _ _ ↦ hcell hε C' hC' (fun m hm ↦ ?_) r hri G⟩
    refine (hcell' m).some.isEmpty_congr.2 ⟨fun ⟨⟨q, hq, hqc⟩, hqm⟩ ↦ ?_⟩
    have hqc' : F (j q) = F (j p) := hqc
    have := hindex q ⟨hq, by
      simp only [mem_preimage, mem_Icc, Function.comp_apply]
      constructor <;> linarith⟩
    dsimp only at hqm
    omega

end BandInduction

section SublevelHomotopy

variable {E H : Type*} {M X : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [FiniteDimensional ℝ E]
  [I.Boundaryless] [IsManifold I ∞ M] [T2Space M] [TopologicalSpace X] [T2Space X]
  {j : M → X} {F : X → ℝ} {n : ℕ}

/-- Low-degree homotopy connectivity of `{F ≤ a} ↪ {F ≤ b}`, indexed by `Fin k` so that it
contains no universe parameter. -/
private structure SublevelBandConnected (F : X → ℝ) (n : ℕ) (a b : ℝ) (hab : a ≤ b) : Prop where
  exists_joined (hn : 0 < n) (y : {x | F x ≤ b}) :
    ∃ x, Joined (ContinuousMap.inclusion (sublevel_mono F hab) x) y
  surjective {k : ℕ} (hk : k < n) (x : {x | F x ≤ a}) :
    Surjective (HomotopyGroup.map (N := Fin k) (ContinuousMap.inclusion (sublevel_mono F hab))
      (rfl : ContinuousMap.inclusion (sublevel_mono F hab) x =
        ContinuousMap.inclusion (sublevel_mono F hab) x))
  injective {k : ℕ} (hk : k + 1 < n) (x : {x | F x ≤ a}) :
    Injective (HomotopyGroup.map (N := Fin k) (ContinuousMap.inclusion (sublevel_mono F hab))
      (rfl : ContinuousMap.inclusion (sublevel_mono F hab) x =
        ContinuousMap.inclusion (sublevel_mono F hab) x))

omit [T2Space X] in
private theorem SublevelBandConnected.trans {a m b : ℝ} {ham : a ≤ m} {hmb : m ≤ b}
    (h₁ : SublevelBandConnected F n a m ham) (h₂ : SublevelBandConnected F n m b hmb) :
    SublevelBandConnected F n a b (ham.trans hmb) := by
  have hcomp (k : ℕ) (x : {x | F x ≤ a}) :
      HomotopyGroup.map (N := Fin k) (ContinuousMap.inclusion (sublevel_mono F hmb)) rfl ∘
        HomotopyGroup.map (ContinuousMap.inclusion (sublevel_mono F ham))
          (rfl : _ = ContinuousMap.inclusion (sublevel_mono F ham) x) =
      HomotopyGroup.map (ContinuousMap.inclusion (sublevel_mono F (ham.trans hmb))) rfl :=
    HomotopyGroup.map_comp_map_of_comp_eq (ContinuousMap.ext fun _ ↦ rfl) rfl rfl rfl
  refine ⟨fun hn y ↦ ?_, fun hk x ↦ hcomp _ x ▸ (h₂.surjective hk _).comp (h₁.surjective hk x),
    fun hk x ↦ hcomp _ x ▸ (h₂.injective hk _).comp (h₁.injective hk x)⟩
  obtain ⟨z, hz⟩ := h₂.exists_joined hn y
  obtain ⟨x, hx⟩ := h₁.exists_joined hn z
  exact ⟨x, (hx.map (ContinuousMap.inclusion (sublevel_mono F hmb)).continuous).trans hz⟩

private theorem sublevelBandConnected_of_isOpenEmbedding (hj : IsOpenEmbedding j)
    (hF : Continuous F) (hf : IsMorse I (F ∘ j)) {a b : ℝ} (hab : a ≤ b)
    (hcompact : IsCompact (F ⁻¹' Icc a b)) (hA : ∀ x ∉ range j, F x < a)
    (ha : IsRegularValue I 𝓘(ℝ) (F ∘ j) a) (hb : IsRegularValue I 𝓘(ℝ) (F ∘ j) b)
    (hindex : ∀ p ∈ criticalPoints I (F ∘ j) ∩ (F ∘ j) ⁻¹' Icc a b,
      n ≤ manifoldMorseIndex I (F ∘ j) p) :
    SublevelBandConnected F n a b hab := by
  refine hf.sublevelBand_induction hj hF hab hcompact hA ha hb hindex
    (P := SublevelBandConnected F n) (fun hst r hri G ↦ ?_)
    (fun {c ε} hε C' _ _ hC' hempty r hri G ↦ ?_) (fun _ _ h₁ h₂ ↦ h₁.trans h₂)
  · have he := (ContinuousMap.HomotopyEquiv.ofDeformationRetraction
        (ContinuousMap.inclusion (sublevel_mono F hst)) r hri
        ⟨G.toHomotopy⟩).isWeakHomotopyEquivalence
    exact ⟨fun _ ↦ he.exists_joined, fun _ x ↦ (he.bijective _ x).surjective,
      fun _ x ↦ (he.bijective _ x).injective⟩
  · have hg := (ContinuousMap.HomotopyEquiv.ofDeformationRetraction
      (ContinuousMap.inclusion hC') r hri ⟨G.toHomotopy⟩).isWeakHomotopyEquivalence
    have hgf : (ContinuousMap.inclusion hC').comp (ContinuousMap.inclusion base_subset_complex) =
        (ContinuousMap.inclusion (sublevel_mono F (a := c - ε) (b := c + ε) (by linarith))).comp
          (ContinuousMap.id _) :=
      ContinuousMap.ext fun _ ↦ rfl
    exact ⟨fun hn ↦ exists_joined_of_isEmpty_cell_of_comp_eq hempty hn .id hg hgf,
      fun hk ↦ surjective_homotopyGroupMap_of_isEmpty_cell_of_comp_eq hempty
        (by simpa using hk) .id hg hgf,
      fun hk ↦ injective_homotopyGroupMap_of_isEmpty_cell_of_comp_eq hempty
        (by simpa using hk) .id hg hgf⟩

/-- **Path connectivity across a Morse band with indices at least `1`.** Across a compact band
`F⁻¹[a, b]` between regular values of `F ∘ j` with `F < a` outside `range j`, if `0 < n` and every
critical point in the band has index at least `n`, every point of `{F ≤ b}` is joined by a path in
`{F ≤ b}` to `{F ≤ a}`. -/
theorem IsMorse.exists_joined_sublevelInclusion_of_isOpenEmbedding (hj : IsOpenEmbedding j)
    (hF : Continuous F) (hf : IsMorse I (F ∘ j)) {a b : ℝ} (hab : a ≤ b)
    (hcompact : IsCompact (F ⁻¹' Icc a b)) (hA : ∀ x ∉ range j, F x < a)
    (ha : IsRegularValue I 𝓘(ℝ) (F ∘ j) a) (hb : IsRegularValue I 𝓘(ℝ) (F ∘ j) b)
    (hindex : ∀ p ∈ criticalPoints I (F ∘ j) ∩ (F ∘ j) ⁻¹' Icc a b,
      n ≤ manifoldMorseIndex I (F ∘ j) p)
    (hn : 0 < n) (y : {x | F x ≤ b}) :
    ∃ x, Joined (sublevelInclusion F a b hab x) y := by
  rw [sublevelInclusion_eq_inclusion]
  exact (sublevelBandConnected_of_isOpenEmbedding hj hF hf hab hcompact hA ha hb
    hindex).exists_joined hn y

/-- **Surjectivity on `π_k` for `k < n` across a Morse band.** Across a compact band `F⁻¹[a, b]`
between regular values of `F ∘ j` with `F < a` outside `range j`, if every critical point in the
band has index at least `n`, then `{F ≤ a} ↪ {F ≤ b}` induces surjections on `π_k` for `k < n`. -/
theorem IsMorse.surjective_homotopyGroupMap_sublevelInclusion_of_isOpenEmbedding
    {N : Type v} [Finite N] (hj : IsOpenEmbedding j) (hF : Continuous F) (hf : IsMorse I (F ∘ j))
    {a b : ℝ} (hab : a ≤ b) (hcompact : IsCompact (F ⁻¹' Icc a b)) (hA : ∀ x ∉ range j, F x < a)
    (ha : IsRegularValue I 𝓘(ℝ) (F ∘ j) a) (hb : IsRegularValue I 𝓘(ℝ) (F ∘ j) b)
    (hindex : ∀ p ∈ criticalPoints I (F ∘ j) ∩ (F ∘ j) ⁻¹' Icc a b,
      n ≤ manifoldMorseIndex I (F ∘ j) p)
    (hN : Nat.card N < n) (x : {x | F x ≤ a}) :
    Surjective (HomotopyGroup.map (N := N) (sublevelInclusion F a b hab)
      (rfl : sublevelInclusion F a b hab x = sublevelInclusion F a b hab x)) := by
  rw [HomotopyGroup.surjective_map_congr (sublevelInclusion_eq_inclusion F hab) rfl rfl,
    ← HomotopyGroup.congrEquiv_symm_comp_map_comp_congrEquiv _ rfl (Finite.equivFin N)]
  exact (Equiv.surjective _).comp
    (((sublevelBandConnected_of_isOpenEmbedding hj hF hf hab hcompact hA ha hb
      hindex).surjective hN x).comp (Equiv.surjective _))

/-- **Injectivity on `π_k` for `k + 1 < n` across a Morse band.** Across a compact band `F⁻¹[a, b]`
between regular values of `F ∘ j` with `F < a` outside `range j`, if every critical point in the
band has index at least `n`, then `{F ≤ a} ↪ {F ≤ b}` induces injections on `π_k` for
`k + 1 < n`. -/
theorem IsMorse.injective_homotopyGroupMap_sublevelInclusion_of_isOpenEmbedding
    {N : Type v} [Finite N] (hj : IsOpenEmbedding j) (hF : Continuous F) (hf : IsMorse I (F ∘ j))
    {a b : ℝ} (hab : a ≤ b) (hcompact : IsCompact (F ⁻¹' Icc a b)) (hA : ∀ x ∉ range j, F x < a)
    (ha : IsRegularValue I 𝓘(ℝ) (F ∘ j) a) (hb : IsRegularValue I 𝓘(ℝ) (F ∘ j) b)
    (hindex : ∀ p ∈ criticalPoints I (F ∘ j) ∩ (F ∘ j) ⁻¹' Icc a b,
      n ≤ manifoldMorseIndex I (F ∘ j) p)
    (hN : Nat.card N + 1 < n) (x : {x | F x ≤ a}) :
    Injective (HomotopyGroup.map (N := N) (sublevelInclusion F a b hab)
      (rfl : sublevelInclusion F a b hab x = sublevelInclusion F a b hab x)) := by
  rw [HomotopyGroup.injective_map_congr (sublevelInclusion_eq_inclusion F hab) rfl rfl,
    ← HomotopyGroup.congrEquiv_symm_comp_map_comp_congrEquiv _ rfl (Finite.equivFin N)]
  exact (Equiv.injective _).comp
    (((sublevelBandConnected_of_isOpenEmbedding hj hF hf hab hcompact hA ha hb
      hindex).injective hN x).comp (Equiv.injective _))

/-- **Bijectivity on `π_k` for `k + 1 < n` across a Morse band.** -/
theorem IsMorse.bijective_homotopyGroupMap_sublevelInclusion_of_isOpenEmbedding
    {N : Type v} [Finite N] (hj : IsOpenEmbedding j) (hF : Continuous F) (hf : IsMorse I (F ∘ j))
    {a b : ℝ} (hab : a ≤ b) (hcompact : IsCompact (F ⁻¹' Icc a b)) (hA : ∀ x ∉ range j, F x < a)
    (ha : IsRegularValue I 𝓘(ℝ) (F ∘ j) a) (hb : IsRegularValue I 𝓘(ℝ) (F ∘ j) b)
    (hindex : ∀ p ∈ criticalPoints I (F ∘ j) ∩ (F ∘ j) ⁻¹' Icc a b,
      n ≤ manifoldMorseIndex I (F ∘ j) p)
    (hN : Nat.card N + 1 < n) (x : {x | F x ≤ a}) :
    Bijective (HomotopyGroup.map (N := N) (sublevelInclusion F a b hab)
      (rfl : sublevelInclusion F a b hab x = sublevelInclusion F a b hab x)) :=
  ⟨hf.injective_homotopyGroupMap_sublevelInclusion_of_isOpenEmbedding hj hF hab hcompact hA ha hb
      hindex hN x,
    hf.surjective_homotopyGroupMap_sublevelInclusion_of_isOpenEmbedding hj hF hab hcompact hA ha hb
      hindex (by omega) x⟩

/-- **Relative homotopy vanishing below the Morse index bound across a compact band.** Across a
compact band `F⁻¹[a, b]` between regular values of `F ∘ j` with `F < a` outside `range j`, if every
critical point in the band has index at least `n`, then `π_{k+1}({F ≤ b}, {F ≤ a}, x₀)` is trivial
for `k + 1 < n` and every `x₀ ∈ {F ≤ a}`. -/
theorem IsMorse.subsingleton_relHomotopyGroup_sublevelPair_of_isOpenEmbedding
    {N : Type v} [Finite N] (hj : IsOpenEmbedding j) (hF : Continuous F) (hf : IsMorse I (F ∘ j))
    {a b : ℝ} (hab : a ≤ b) (hcompact : IsCompact (F ⁻¹' Icc a b)) (hA : ∀ x ∉ range j, F x < a)
    (ha : IsRegularValue I 𝓘(ℝ) (F ∘ j) a) (hb : IsRegularValue I 𝓘(ℝ) (F ∘ j) b)
    (hindex : ∀ p ∈ criticalPoints I (F ∘ j) ∩ (F ∘ j) ⁻¹' Icc a b,
      n ≤ manifoldMorseIndex I (F ∘ j) p)
    (hN : Nat.card N + 1 < n) (x : {x | F x ≤ a}) :
    Subsingleton (RelHomotopyGroup N ⟨sublevelPair F hab, x⟩) :=
  RelHomotopyGroup.subsingleton_of_injective_of_surjective
    ((HomotopyGroup.injective_map_congr (sublevelInclusion_eq_inclusion F hab) rfl rfl).1
      (hf.injective_homotopyGroupMap_sublevelInclusion_of_isOpenEmbedding hj hF hab hcompact hA ha
        hb hindex hN x))
    ((HomotopyGroup.surjective_map_congr (sublevelInclusion_eq_inclusion F hab) rfl rfl).1
      (hf.surjective_homotopyGroupMap_sublevelInclusion_of_isOpenEmbedding hj hF hab hcompact hA ha
        hb hindex (by rw [_root_.Finite.card_option]; exact hN) x))

/-- **Path connectivity across a Morse band with indices at least `1` on a manifold.** -/
theorem IsMorse.exists_joined_sublevelInclusion {f : M → ℝ} (hf : IsMorse I f) {a b : ℝ}
    (hab : a ≤ b) (hcompact : IsCompact (f ⁻¹' Icc a b))
    (ha : IsRegularValue I 𝓘(ℝ) f a) (hb : IsRegularValue I 𝓘(ℝ) f b)
    (hindex : ∀ p ∈ criticalPoints I f ∩ f ⁻¹' Icc a b, n ≤ manifoldMorseIndex I f p)
    (hn : 0 < n) (y : {x | f x ≤ b}) :
    ∃ x, Joined (sublevelInclusion f a b hab x) y :=
  hf.exists_joined_sublevelInclusion_of_isOpenEmbedding .id hf.contMDiff.continuous hab hcompact
    (fun _ h ↦ (h (mem_range_self _)).elim) ha hb hindex hn y

/-- **Relative homotopy vanishing below the Morse index bound on a manifold.** -/
theorem IsMorse.subsingleton_relHomotopyGroup_sublevelPair {f : M → ℝ} {N : Type v} [Finite N]
    (hf : IsMorse I f) {a b : ℝ} (hab : a ≤ b) (hcompact : IsCompact (f ⁻¹' Icc a b))
    (ha : IsRegularValue I 𝓘(ℝ) f a) (hb : IsRegularValue I 𝓘(ℝ) f b)
    (hindex : ∀ p ∈ criticalPoints I f ∩ f ⁻¹' Icc a b, n ≤ manifoldMorseIndex I f p)
    (hN : Nat.card N + 1 < n) (x : {x | f x ≤ a}) :
    Subsingleton (RelHomotopyGroup N ⟨sublevelPair f hab, x⟩) :=
  hf.subsingleton_relHomotopyGroup_sublevelPair_of_isOpenEmbedding .id hf.contMDiff.continuous hab
    hcompact (fun _ h ↦ (h (mem_range_self _)).elim) ha hb hindex hN x

/-- **Surjectivity on `π_k` for `k < n` across a Morse band on a manifold.** -/
theorem IsMorse.surjective_homotopyGroupMap_sublevelInclusion {f : M → ℝ} {N : Type v} [Finite N]
    (hf : IsMorse I f) {a b : ℝ} (hab : a ≤ b) (hcompact : IsCompact (f ⁻¹' Icc a b))
    (ha : IsRegularValue I 𝓘(ℝ) f a) (hb : IsRegularValue I 𝓘(ℝ) f b)
    (hindex : ∀ p ∈ criticalPoints I f ∩ f ⁻¹' Icc a b, n ≤ manifoldMorseIndex I f p)
    (hN : Nat.card N < n) (x : {x | f x ≤ a}) :
    Surjective (HomotopyGroup.map (N := N) (sublevelInclusion f a b hab)
      (rfl : sublevelInclusion f a b hab x = sublevelInclusion f a b hab x)) :=
  hf.surjective_homotopyGroupMap_sublevelInclusion_of_isOpenEmbedding .id hf.contMDiff.continuous
    hab hcompact (fun _ h ↦ (h (mem_range_self _)).elim) ha hb hindex hN x

/-- **Injectivity on `π_k` for `k + 1 < n` across a Morse band on a manifold.** -/
theorem IsMorse.injective_homotopyGroupMap_sublevelInclusion {f : M → ℝ} {N : Type v} [Finite N]
    (hf : IsMorse I f) {a b : ℝ} (hab : a ≤ b) (hcompact : IsCompact (f ⁻¹' Icc a b))
    (ha : IsRegularValue I 𝓘(ℝ) f a) (hb : IsRegularValue I 𝓘(ℝ) f b)
    (hindex : ∀ p ∈ criticalPoints I f ∩ f ⁻¹' Icc a b, n ≤ manifoldMorseIndex I f p)
    (hN : Nat.card N + 1 < n) (x : {x | f x ≤ a}) :
    Injective (HomotopyGroup.map (N := N) (sublevelInclusion f a b hab)
      (rfl : sublevelInclusion f a b hab x = sublevelInclusion f a b hab x)) :=
  hf.injective_homotopyGroupMap_sublevelInclusion_of_isOpenEmbedding .id hf.contMDiff.continuous
    hab hcompact (fun _ h ↦ (h (mem_range_self _)).elim) ha hb hindex hN x

/-- **Bijectivity on `π_k` for `k + 1 < n` across a Morse band on a manifold.** -/
theorem IsMorse.bijective_homotopyGroupMap_sublevelInclusion {f : M → ℝ} {N : Type v} [Finite N]
    (hf : IsMorse I f) {a b : ℝ} (hab : a ≤ b) (hcompact : IsCompact (f ⁻¹' Icc a b))
    (ha : IsRegularValue I 𝓘(ℝ) f a) (hb : IsRegularValue I 𝓘(ℝ) f b)
    (hindex : ∀ p ∈ criticalPoints I f ∩ f ⁻¹' Icc a b, n ≤ manifoldMorseIndex I f p)
    (hN : Nat.card N + 1 < n) (x : {x | f x ≤ a}) :
    Bijective (HomotopyGroup.map (N := N) (sublevelInclusion f a b hab)
      (rfl : sublevelInclusion f a b hab x = sublevelInclusion f a b hab x)) :=
  hf.bijective_homotopyGroupMap_sublevelInclusion_of_isOpenEmbedding .id hf.contMDiff.continuous hab
    hcompact (fun _ h ↦ (h (mem_range_self _)).elim) ha hb hindex hN x

end SublevelHomotopy

section SublevelHomology

variable {E H : Type*} {M X : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [FiniteDimensional ℝ E]
  [I.Boundaryless] [IsManifold I ∞ M] [T2Space M] [TopologicalSpace X] [T2Space X]
  {j : M → X} {F : X → ℝ} {n : ℕ}
  {A_cat : Type v} [Category.{w} A_cat] [Abelian A_cat] [HasCoproducts.{u} A_cat]

/-- **Relative singular homology vanishes below the Morse index bound across a compact band.** Let
`F⁻¹[a, b]` be a compact band between regular values of `F ∘ j` with `F < a` outside `range j`. If
every critical point of `F ∘ j` in the band has Morse index at least `n`, then
`H_k({F ≤ b}, {F ≤ a}; R)` vanishes for every `k < n`. -/
theorem IsMorse.isZero_singularHomology_sublevelPair_of_isOpenEmbedding (hj : IsOpenEmbedding j)
    (hF : Continuous F) (hf : IsMorse I (F ∘ j)) {a b : ℝ} (hab : a ≤ b)
    (hcompact : IsCompact (F ⁻¹' Icc a b)) (hA : ∀ x ∉ range j, F x < a)
    (ha : IsRegularValue I 𝓘(ℝ) (F ∘ j) a) (hb : IsRegularValue I 𝓘(ℝ) (F ∘ j) b)
    (hindex : ∀ p ∈ criticalPoints I (F ∘ j) ∩ (F ∘ j) ⁻¹' Icc a b,
      n ≤ manifoldMorseIndex I (F ∘ j) p)
    (R : A_cat) {k : ℕ} (hk : k < n) :
    IsZero ((sublevelPair F hab).singularHomology R k) := by
  refine hf.sublevelBand_induction hj hF hab hcompact hA ha hb hindex
    (P := fun s t hst ↦ IsZero ((sublevelPair F hst).singularHomology R k))
    (fun hst r _ G ↦ TopPair.isZero_singularHomology_ofInclusion_of_homotopyRel
      (X := TopCat.of X) (sublevel_mono F hst) r G R k)
    (fun _ C' _ _ hC' hempty r _ G ↦ ?_)
    fun hsm hmt h₁ h₂ ↦ (TopTriple.ofInclusions (X := TopCat.of X) (sublevel_mono F hsm)
      (sublevel_mono F hmt)).isZero_singularHomology_totalPair R k h₁ h₂
  have : IsEmpty (cell C' k) := hempty k hk
  have : ∀ m, HasExactColimitsOfShape (Discrete (cell C' m)) A_cat := fun m ↦
    have : _root_.Finite (cell C' m) := FiniteType.finite_cell m
    @hasExactColimitsOfShape_discrete_finite A_cat _ _ Abelian.hasFiniteBiproducts _ _
  have hzero := isZero_singularHomology_complexBasePair_of_isEmpty_cell C' R k
  rw [complexBasePair_eq_ofInclusion] at hzero
  have hiso := TopPair.isIso_singularHomologyMap_ofInclusionMap_inclusion_of_homotopyRel
    (X := TopCat.of X) base_subset_complex hC' r G R k
  exact hzero.of_iso (@asIso _ _ _ _ _ hiso).symm

/-- **Epimorphism on `H_k` for `k < n` across a Morse band.** -/
theorem IsMorse.epi_homologyMap_sublevelInclusion_of_isOpenEmbedding (hj : IsOpenEmbedding j)
    (hF : Continuous F) (hf : IsMorse I (F ∘ j)) {a b : ℝ} (hab : a ≤ b)
    (hcompact : IsCompact (F ⁻¹' Icc a b)) (hA : ∀ x ∉ range j, F x < a)
    (ha : IsRegularValue I 𝓘(ℝ) (F ∘ j) a) (hb : IsRegularValue I 𝓘(ℝ) (F ∘ j) b)
    (hindex : ∀ p ∈ criticalPoints I (F ∘ j) ∩ (F ∘ j) ⁻¹' Icc a b,
      n ≤ manifoldMorseIndex I (F ∘ j) p)
    (R : A_cat) {k : ℕ} (hk : k < n) :
    Epi (SSet.homologyMap
      (TopCat.toSSet.map (TopCat.ofHom (sublevelInclusion F a b hab))) R k) := by
  rw [sublevelInclusion_eq_inclusion]
  exact (sublevelPair F hab).epi_homologyMap_map_of_isZero R
    (hf.isZero_singularHomology_sublevelPair_of_isOpenEmbedding hj hF hab hcompact hA ha hb hindex
      R hk)

/-- **Isomorphism on `H_k` for `k + 1 < n` across a Morse band.** -/
theorem IsMorse.isIso_homologyMap_sublevelInclusion_of_isOpenEmbedding (hj : IsOpenEmbedding j)
    (hF : Continuous F) (hf : IsMorse I (F ∘ j)) {a b : ℝ} (hab : a ≤ b)
    (hcompact : IsCompact (F ⁻¹' Icc a b)) (hA : ∀ x ∉ range j, F x < a)
    (ha : IsRegularValue I 𝓘(ℝ) (F ∘ j) a) (hb : IsRegularValue I 𝓘(ℝ) (F ∘ j) b)
    (hindex : ∀ p ∈ criticalPoints I (F ∘ j) ∩ (F ∘ j) ⁻¹' Icc a b,
      n ≤ manifoldMorseIndex I (F ∘ j) p)
    (R : A_cat) {k : ℕ} (hk : k + 1 < n) :
    IsIso (SSet.homologyMap
      (TopCat.toSSet.map (TopCat.ofHom (sublevelInclusion F a b hab))) R k) := by
  rw [sublevelInclusion_eq_inclusion]
  exact (sublevelPair F hab).isIso_homologyMap_map_of_isZero R
    (hf.isZero_singularHomology_sublevelPair_of_isOpenEmbedding hj hF hab hcompact hA ha hb hindex
      R hk)
    (hf.isZero_singularHomology_sublevelPair_of_isOpenEmbedding hj hF hab hcompact hA ha hb hindex
      R (by omega))

/-- **Relative singular homology vanishes below the Morse index bound on a manifold.** -/
theorem IsMorse.isZero_singularHomology_sublevelPair {f : M → ℝ}
    (hf : IsMorse I f) {a b : ℝ} (hab : a ≤ b) (hcompact : IsCompact (f ⁻¹' Icc a b))
    (ha : IsRegularValue I 𝓘(ℝ) f a) (hb : IsRegularValue I 𝓘(ℝ) f b)
    (hindex : ∀ p ∈ criticalPoints I f ∩ f ⁻¹' Icc a b, n ≤ manifoldMorseIndex I f p)
    (R : A_cat) {k : ℕ} (hk : k < n) :
    IsZero ((sublevelPair f hab).singularHomology R k) :=
  hf.isZero_singularHomology_sublevelPair_of_isOpenEmbedding .id hf.contMDiff.continuous hab
    hcompact (fun _ h ↦ (h (mem_range_self _)).elim) ha hb hindex R hk

/-- **Epimorphism on `H_k` for `k < n` across a Morse band on a manifold.** -/
theorem IsMorse.epi_homologyMap_sublevelInclusion {f : M → ℝ}
    (hf : IsMorse I f) {a b : ℝ} (hab : a ≤ b) (hcompact : IsCompact (f ⁻¹' Icc a b))
    (ha : IsRegularValue I 𝓘(ℝ) f a) (hb : IsRegularValue I 𝓘(ℝ) f b)
    (hindex : ∀ p ∈ criticalPoints I f ∩ f ⁻¹' Icc a b, n ≤ manifoldMorseIndex I f p)
    (R : A_cat) {k : ℕ} (hk : k < n) :
    Epi (SSet.homologyMap
      (TopCat.toSSet.map (TopCat.ofHom (sublevelInclusion f a b hab))) R k) :=
  hf.epi_homologyMap_sublevelInclusion_of_isOpenEmbedding .id hf.contMDiff.continuous hab hcompact
    (fun _ h ↦ (h (mem_range_self _)).elim) ha hb hindex R hk

/-- **Isomorphism on `H_k` for `k + 1 < n` across a Morse band on a manifold.** -/
theorem IsMorse.isIso_homologyMap_sublevelInclusion {f : M → ℝ}
    (hf : IsMorse I f) {a b : ℝ} (hab : a ≤ b) (hcompact : IsCompact (f ⁻¹' Icc a b))
    (ha : IsRegularValue I 𝓘(ℝ) f a) (hb : IsRegularValue I 𝓘(ℝ) f b)
    (hindex : ∀ p ∈ criticalPoints I f ∩ f ⁻¹' Icc a b, n ≤ manifoldMorseIndex I f p)
    (R : A_cat) {k : ℕ} (hk : k + 1 < n) :
    IsIso (SSet.homologyMap
      (TopCat.toSSet.map (TopCat.ofHom (sublevelInclusion f a b hab))) R k) :=
  hf.isIso_homologyMap_sublevelInclusion_of_isOpenEmbedding .id hf.contMDiff.continuous hab hcompact
    (fun _ h ↦ (h (mem_range_self _)).elim) ha hb hindex R hk

end SublevelHomology

section PairConnectivity

private theorem surjective_homotopyGroupMap_subtypeVal_sublevel_iff
    {X : Type u} [TopologicalSpace X] {N : Type v} [Finite N] {F : X → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hFb : ∀ x, F x ≤ b) (y : {x | F x ≤ a}) :
    Surjective (HomotopyGroup.map (N := N) (x := y)
        (ContinuousMap.subtypeVal {x | F x ≤ a}) rfl) ↔
      Surjective (HomotopyGroup.map (N := N) (x := y) (sublevelInclusion F a b hab) rfl) :=
  (ContinuousMap.HomotopyEquiv.refl _).isWeakHomotopyEquivalence.surjective_map_iff_of_comp_eq
    (sublevelHomeomorphUniv hFb).toHomotopyEquiv.isWeakHomotopyEquivalence
    (ContinuousMap.ext fun x ↦ by simp) N y

private theorem injective_homotopyGroupMap_subtypeVal_sublevel_iff
    {X : Type u} [TopologicalSpace X] {N : Type v} [Finite N] {F : X → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hFb : ∀ x, F x ≤ b) (y : {x | F x ≤ a}) :
    Injective (HomotopyGroup.map (N := N) (x := y)
        (ContinuousMap.subtypeVal {x | F x ≤ a}) rfl) ↔
      Injective (HomotopyGroup.map (N := N) (x := y) (sublevelInclusion F a b hab) rfl) :=
  (ContinuousMap.HomotopyEquiv.refl _).isWeakHomotopyEquivalence.injective_map_iff_of_comp_eq
    (sublevelHomeomorphUniv hFb).toHomotopyEquiv.isWeakHomotopyEquivalence
    (ContinuousMap.ext fun x ↦ by simp) N y

private theorem sublevelInclusion_comp_sublevelHomeomorphUniv
    {X : Type u} [TopologicalSpace X] {F : X → ℝ} {a b : ℝ} (hab : a ≤ b) (hFb : ∀ x, F x ≤ b) :
    TopCat.ofHom (sublevelInclusion F a b hab) ≫
        (TopCat.isoOfHomeo (X := TopCat.of ↥{x | F x ≤ b}) (Y := TopCat.of X)
          (sublevelHomeomorphUniv hFb)).hom =
      TopCat.ofHom (ContinuousMap.subtypeVal {x | F x ≤ a}) := by
  ext x
  simp

variable {E H : Type*} {M X : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [FiniteDimensional ℝ E]
  [I.Boundaryless] [IsManifold I ∞ M] [T2Space M] [TopologicalSpace X] [T2Space X]
  {j : M → X} {F : X → ℝ} {A W : Set X} {n : ℕ}

omit [FiniteDimensional ℝ E] [T2Space M] [T2Space X] in
/-- Choose a regular value `0 < a < δ` of `F ∘ j` and an upper bound `b > F` so `{F ≤ a} ⊆ W` and
`{F ≤ b} = univ`. -/
private theorem IsMorse.exists_sandwich_levels (hj : IsOpenEmbedding j)
    (hf : IsMorse I (F ∘ j)) (hbdd : BddAbove (range F)) (hA : ∀ x ∉ range j, F x ≤ 0)
    (hAF : ∀ x ∈ A, F x ≤ 0) (hcompact : ∀ a b, 0 < a → a ≤ b → IsCompact (F ⁻¹' Icc a b))
    (hδ : ∃ δ > 0, {x | F x ≤ δ} ⊆ W) :
    ∃ (a b : ℝ) (_ : a ≤ b),
      0 < a ∧ A ⊆ {x | F x ≤ a} ∧ {x | F x ≤ a} ⊆ W ∧ (∀ x ∉ range j, F x < a) ∧
      (∀ x, F x < b) ∧ IsRegularValue I 𝓘(ℝ) (F ∘ j) a ∧ IsRegularValue I 𝓘(ℝ) (F ∘ j) b ∧
      IsCompact (F ⁻¹' Icc a b) := by
  obtain ⟨δ, hδ_pos, hδW⟩ := hδ
  obtain ⟨M₀, hM₀⟩ := hbdd
  have hA_third (x : X) (hx : x ∉ range j) : F x < δ / 3 := (hA x hx).trans_lt (by linarith)
  obtain ⟨a, ⟨ha₁, ha₂⟩, ha_reg⟩ := hf.exists_isRegularValue_mem_Ioo
    (a := δ / 3) (b := 2 * δ / 3) (by linarith)
    (hj.isInducing.isCompact_comp_preimage_Icc hA_third
      (hcompact _ _ (by linarith) (by linarith)))
  have ha_pos : 0 < a := by linarith
  let b : ℝ := max a M₀ + 1
  have hab : a ≤ b := by linarith [le_max_left a M₀]
  have hFb (x : X) : F x < b :=
    (hM₀ (mem_range_self x)).trans_lt (by linarith [le_max_right a M₀])
  refine ⟨a, b, hab, ha_pos, fun x hx ↦ (hAF x hx).trans ha_pos.le,
    fun x hx ↦ hδW (hx.out.trans (by linarith)), fun x hx ↦ (hA x hx).trans_lt ha_pos, hFb,
    ha_reg, isRegularValue_iff_notMem_image_criticalPoints.2 fun ⟨p, _, hp⟩ ↦ (hFb (j p)).ne hp,
    hcompact a b ha_pos hab⟩

/-- **Path connectivity of `(X, A)` from a high-index Morse function on the open manifold part.**
If `0 < n`, every critical point of `F ∘ j` has index at least `n`, and `A ↪ W` is a weak homotopy
equivalence on a set `W` containing a positive sublevel `{F ≤ δ}`, then every point of `X` is
joined by a path in `X` to a point of `A`. -/
theorem IsMorse.exists_joined_of_isOpenEmbedding (hj : IsOpenEmbedding j) (hF : Continuous F)
    (hf : IsMorse I (F ∘ j)) (hbdd : BddAbove (range F)) (hA : ∀ x ∉ range j, F x ≤ 0)
    (hAF : ∀ x ∈ A, F x ≤ 0) (hcompact : ∀ a b, 0 < a → a ≤ b → IsCompact (F ⁻¹' Icc a b))
    (hindex : ∀ p ∈ criticalPoints I (F ∘ j), n ≤ manifoldMorseIndex I (F ∘ j) p)
    {hAW : A ⊆ W} (hW : (ContinuousMap.inclusion hAW).IsWeakHomotopyEquivalence)
    (hδ : ∃ δ > 0, {x | F x ≤ δ} ⊆ W) (hn : 0 < n) (x : X) :
    ∃ a : A, Joined (a : X) x := by
  obtain ⟨a, b, hab, -, -, haW, hA_lt, hFb, ha_reg, hb_reg, hcpt⟩ :=
    hf.exists_sandwich_levels hj hbdd hA hAF hcompact hδ
  obtain ⟨y, hy⟩ := hf.exists_joined_sublevelInclusion_of_isOpenEmbedding hj hF hab hcpt hA_lt
    ha_reg hb_reg (fun p hp ↦ hindex p hp.1) hn ⟨x, (hFb x).le⟩
  rw [sublevelInclusion_eq_inclusion] at hy
  obtain ⟨a₀, ha₀⟩ := hW.exists_joined (ContinuousMap.inclusion haW y)
  exact ⟨a₀, (ha₀.map continuous_subtype_val).trans (hy.map continuous_subtype_val)⟩

/-- **Surjectivity of `π_k(A, a₀) → π_k(X, a₀)` for `k < n` on a compactified pair.** -/
theorem IsMorse.surjective_homotopyGroupMap_subtypeVal_of_isOpenEmbedding
    {N : Type v} [Finite N] (hj : IsOpenEmbedding j) (hF : Continuous F)
    (hf : IsMorse I (F ∘ j)) (hbdd : BddAbove (range F)) (hA : ∀ x ∉ range j, F x ≤ 0)
    (hAF : ∀ x ∈ A, F x ≤ 0) (hcompact : ∀ a b, 0 < a → a ≤ b → IsCompact (F ⁻¹' Icc a b))
    (hindex : ∀ p ∈ criticalPoints I (F ∘ j), n ≤ manifoldMorseIndex I (F ∘ j) p)
    {hAW : A ⊆ W} (hW : (ContinuousMap.inclusion hAW).IsWeakHomotopyEquivalence)
    (hδ : ∃ δ > 0, {x | F x ≤ δ} ⊆ W) (hN : Nat.card N < n) (a₀ : A) :
    Surjective (HomotopyGroup.map (N := N) (x := a₀)
      (ContinuousMap.subtypeVal A) (rfl : (a₀ : X) = (a₀ : X))) := by
  obtain ⟨a, b, hab, -, hAa, haW, hA_lt, hFb, ha_reg, hb_reg, hcpt⟩ :=
    hf.exists_sandwich_levels hj hbdd hA hAF hcompact hδ
  let y : {x | F x ≤ a} := ContinuousMap.inclusion hAa a₀
  have hsurj_sub : Surjective (HomotopyGroup.map (N := N) (x := y)
      (ContinuousMap.subtypeVal {x | F x ≤ a}) rfl) :=
    (surjective_homotopyGroupMap_subtypeVal_sublevel_iff hab (fun x ↦ (hFb x).le) y).2
      (hf.surjective_homotopyGroupMap_sublevelInclusion_of_isOpenEmbedding hj hF hab hcpt hA_lt
        ha_reg hb_reg (fun p hp ↦ hindex p hp.1) hN y)
  have hsurj_W : Surjective (HomotopyGroup.map (N := N) (x := ContinuousMap.inclusion haW y)
      (ContinuousMap.subtypeVal W) rfl) :=
    ((HomotopyGroup.map_comp_map_of_comp_eq (ContinuousMap.subtypeVal_comp_inclusion haW)
      rfl rfl rfl).symm ▸ hsurj_sub).of_comp
  exact (HomotopyGroup.map_comp_map_of_comp_eq (ContinuousMap.subtypeVal_comp_inclusion hAW)
    rfl rfl rfl) ▸ hsurj_W.comp (hW.map_bijective N a₀).surjective

/-- **Injectivity of `π_k(A, a₀) → π_k(X, a₀)` for `k + 1 < n` on a compactified pair.** -/
theorem IsMorse.injective_homotopyGroupMap_subtypeVal_of_isOpenEmbedding
    {N : Type v} [Finite N] (hj : IsOpenEmbedding j) (hF : Continuous F)
    (hf : IsMorse I (F ∘ j)) (hbdd : BddAbove (range F)) (hA : ∀ x ∉ range j, F x ≤ 0)
    (hAF : ∀ x ∈ A, F x ≤ 0) (hcompact : ∀ a b, 0 < a → a ≤ b → IsCompact (F ⁻¹' Icc a b))
    (hindex : ∀ p ∈ criticalPoints I (F ∘ j), n ≤ manifoldMorseIndex I (F ∘ j) p)
    {hAW : A ⊆ W} (hW : (ContinuousMap.inclusion hAW).IsWeakHomotopyEquivalence)
    (hδ : ∃ δ > 0, {x | F x ≤ δ} ⊆ W) (hN : Nat.card N + 1 < n) (a₀ : A) :
    Injective (HomotopyGroup.map (N := N) (x := a₀)
      (ContinuousMap.subtypeVal A) (rfl : (a₀ : X) = (a₀ : X))) := by
  obtain ⟨a, b, hab, -, hAa, haW, hA_lt, hFb, ha_reg, hb_reg, hcpt⟩ :=
    hf.exists_sandwich_levels hj hbdd hA hAF hcompact hδ
  let y : {x | F x ≤ a} := ContinuousMap.inclusion hAa a₀
  have hinj_sub : Injective (HomotopyGroup.map (N := N) (x := y)
      (ContinuousMap.subtypeVal {x | F x ≤ a}) rfl) :=
    (injective_homotopyGroupMap_subtypeVal_sublevel_iff hab (fun x ↦ (hFb x).le) y).2
      (hf.injective_homotopyGroupMap_sublevelInclusion_of_isOpenEmbedding hj hF hab hcpt hA_lt
        ha_reg hb_reg (fun p hp ↦ hindex p hp.1) hN y)
  have hinj_α : Injective (HomotopyGroup.map (N := N) (x := a₀)
      (ContinuousMap.inclusion hAa) rfl) :=
    ((HomotopyGroup.map_comp_map_of_comp_eq (ContinuousMap.inclusion_comp_inclusion haW hAa)
      rfl rfl rfl).symm ▸ (hW.map_bijective N a₀).injective).of_comp
  exact (HomotopyGroup.map_comp_map_of_comp_eq (ContinuousMap.subtypeVal_comp_inclusion hAa)
    rfl rfl rfl) ▸ hinj_sub.comp hinj_α

/-- **Bijectivity of `π_k(A, a₀) → π_k(X, a₀)` for `k + 1 < n` on a compactified pair.** -/
theorem IsMorse.bijective_homotopyGroupMap_subtypeVal_of_isOpenEmbedding
    {N : Type v} [Finite N] (hj : IsOpenEmbedding j) (hF : Continuous F)
    (hf : IsMorse I (F ∘ j)) (hbdd : BddAbove (range F)) (hA : ∀ x ∉ range j, F x ≤ 0)
    (hAF : ∀ x ∈ A, F x ≤ 0) (hcompact : ∀ a b, 0 < a → a ≤ b → IsCompact (F ⁻¹' Icc a b))
    (hindex : ∀ p ∈ criticalPoints I (F ∘ j), n ≤ manifoldMorseIndex I (F ∘ j) p)
    {hAW : A ⊆ W} (hW : (ContinuousMap.inclusion hAW).IsWeakHomotopyEquivalence)
    (hδ : ∃ δ > 0, {x | F x ≤ δ} ⊆ W) (hN : Nat.card N + 1 < n) (a₀ : A) :
    Bijective (HomotopyGroup.map (N := N) (x := a₀)
      (ContinuousMap.subtypeVal A) (rfl : (a₀ : X) = (a₀ : X))) :=
  ⟨hf.injective_homotopyGroupMap_subtypeVal_of_isOpenEmbedding hj hF hbdd hA hAF hcompact hindex hW
      hδ hN a₀,
    hf.surjective_homotopyGroupMap_subtypeVal_of_isOpenEmbedding hj hF hbdd hA hAF hcompact hindex
      hW hδ (by omega) a₀⟩

/-- **Injectivity on path components of `A ↪ X` when `1 < n`.** -/
theorem IsMorse.joined_subtypeVal_iff_of_isOpenEmbedding (hj : IsOpenEmbedding j)
    (hF : Continuous F) (hf : IsMorse I (F ∘ j)) (hbdd : BddAbove (range F))
    (hA : ∀ x ∉ range j, F x ≤ 0) (hAF : ∀ x ∈ A, F x ≤ 0)
    (hcompact : ∀ a b, 0 < a → a ≤ b → IsCompact (F ⁻¹' Icc a b))
    (hindex : ∀ p ∈ criticalPoints I (F ∘ j), n ≤ manifoldMorseIndex I (F ∘ j) p)
    {hAW : A ⊆ W} (hW : (ContinuousMap.inclusion hAW).IsWeakHomotopyEquivalence)
    (hδ : ∃ δ > 0, {x | F x ≤ δ} ⊆ W) (hn : 1 < n) {a₀ a₁ : A} :
    Joined (a₀ : X) (a₁ : X) ↔ Joined a₀ a₁ :=
  ContinuousMap.joined_iff_of_injective_homotopyGroupMap (ContinuousMap.subtypeVal A)
    (hf.injective_homotopyGroupMap_subtypeVal_of_isOpenEmbedding (N := Fin 0) hj hF hbdd hA hAF
      hcompact hindex hW hδ (by simpa using hn) a₀)

/-- **Relative homotopy vanishing `π_{k+1}(X, A, a₀) = 0` for `k + 1 < n` on a compactified
pair.** -/
theorem IsMorse.subsingleton_relHomotopyGroup_ofSubset_of_isOpenEmbedding
    {N : Type v} [Finite N] (hj : IsOpenEmbedding j) (hF : Continuous F)
    (hf : IsMorse I (F ∘ j)) (hbdd : BddAbove (range F)) (hA : ∀ x ∉ range j, F x ≤ 0)
    (hAF : ∀ x ∈ A, F x ≤ 0) (hcompact : ∀ a b, 0 < a → a ≤ b → IsCompact (F ⁻¹' Icc a b))
    (hindex : ∀ p ∈ criticalPoints I (F ∘ j), n ≤ manifoldMorseIndex I (F ∘ j) p)
    {hAW : A ⊆ W} (hW : (ContinuousMap.inclusion hAW).IsWeakHomotopyEquivalence)
    (hδ : ∃ δ > 0, {x | F x ≤ δ} ⊆ W) (hN : Nat.card N + 1 < n) (a₀ : A) :
    Subsingleton (RelHomotopyGroup N ⟨TopPair.ofSubset (X := TopCat.of X) A, a₀⟩) :=
  RelHomotopyGroup.subsingleton_of_injective_of_surjective
    (hf.injective_homotopyGroupMap_subtypeVal_of_isOpenEmbedding hj hF hbdd hA hAF hcompact hindex
      hW hδ hN a₀)
    (hf.surjective_homotopyGroupMap_subtypeVal_of_isOpenEmbedding hj hF hbdd hA hAF hcompact hindex
      hW hδ (by rw [_root_.Finite.card_option]; exact hN) a₀)

section Homology

variable {A_cat : Type v} [Category.{w} A_cat] [Abelian A_cat] [HasCoproducts.{u} A_cat]

/-- **Epimorphism `H_k(A; R) ⟶ H_k(X; R)` for `k < n` on a compactified pair.** If `A ↪ W` induces
a singular homology isomorphism in degree `k` on a set `W` containing a positive sublevel `{F ≤ δ}`,
then `A ↪ X` induces an epimorphism `H_k(A; R) ⟶ H_k(X; R)` for `k < n`. -/
theorem IsMorse.epi_homologyMap_subtypeVal_of_isOpenEmbedding (hj : IsOpenEmbedding j)
    (hF : Continuous F) (hf : IsMorse I (F ∘ j)) (hbdd : BddAbove (range F))
    (hA : ∀ x ∉ range j, F x ≤ 0) (hAF : ∀ x ∈ A, F x ≤ 0)
    (hcompact : ∀ a b, 0 < a → a ≤ b → IsCompact (F ⁻¹' Icc a b))
    (hindex : ∀ p ∈ criticalPoints I (F ∘ j), n ≤ manifoldMorseIndex I (F ∘ j) p)
    (R : A_cat) {k : ℕ} {hAW : A ⊆ W}
    (hW : IsIso (SSet.homologyMap (TopCat.toSSet.map
      (TopCat.ofHom (ContinuousMap.inclusion hAW))) R k))
    (hδ : ∃ δ > 0, {x | F x ≤ δ} ⊆ W) (hk : k < n) :
    Epi (SSet.homologyMap (TopCat.toSSet.map
      (TopCat.ofHom (ContinuousMap.subtypeVal A))) R k) := by
  obtain ⟨a, b, hab, -, -, haW, hA_lt, hFb, ha_reg, hb_reg, hcpt⟩ :=
    hf.exists_sandwich_levels hj hbdd hA hAF hcompact hδ
  let H := (AlgebraicTopology.singularHomologyFunctor A_cat k).obj R
  have : Epi (H.map (TopCat.ofHom (sublevelInclusion F a b hab))) := by
    rw [singularHomologyFunctor_obj_map]
    exact hf.epi_homologyMap_sublevelInclusion_of_isOpenEmbedding hj hF hab hcpt hA_lt ha_reg hb_reg
      (fun p hp ↦ hindex p hp.1) R hk
  have hepi_sub : Epi (H.map (TopCat.ofHom (ContinuousMap.subtypeVal {x | F x ≤ a}))) := by
    rw [← sublevelInclusion_comp_sublevelHomeomorphUniv hab fun x ↦ (hFb x).le, H.map_comp]
    exact epi_comp _ _
  have : Epi (H.map (TopCat.ofHom (ContinuousMap.inclusion haW)) ≫
      H.map (TopCat.ofHom (ContinuousMap.subtypeVal W))) := by
    rwa [← H.map_comp, ← TopCat.ofHom_comp, ContinuousMap.subtypeVal_comp_inclusion]
  have : Epi (H.map (TopCat.ofHom (ContinuousMap.subtypeVal W))) :=
    epi_of_epi (H.map (TopCat.ofHom (ContinuousMap.inclusion haW))) _
  have : IsIso (H.map (TopCat.ofHom (ContinuousMap.inclusion hAW))) := by
    rwa [singularHomologyFunctor_obj_map]
  have hepi : Epi (H.map (TopCat.ofHom (ContinuousMap.inclusion hAW)) ≫
      H.map (TopCat.ofHom (ContinuousMap.subtypeVal W))) := epi_comp _ _
  rw [← H.map_comp, ← TopCat.ofHom_comp, ContinuousMap.subtypeVal_comp_inclusion] at hepi
  dsimp only [H] at hepi
  rwa [singularHomologyFunctor_obj_map] at hepi

/-- **Monomorphism `H_k(A; R) ⟶ H_k(X; R)` for `k + 1 < n` on a compactified pair.** If `A ↪ W`
induces a singular homology isomorphism in degree `k` on a set `W` containing a positive sublevel
`{F ≤ δ}`, then `A ↪ X` induces a monomorphism `H_k(A; R) ⟶ H_k(X; R)` for `k + 1 < n`. -/
theorem IsMorse.mono_homologyMap_subtypeVal_of_isOpenEmbedding (hj : IsOpenEmbedding j)
    (hF : Continuous F) (hf : IsMorse I (F ∘ j)) (hbdd : BddAbove (range F))
    (hA : ∀ x ∉ range j, F x ≤ 0) (hAF : ∀ x ∈ A, F x ≤ 0)
    (hcompact : ∀ a b, 0 < a → a ≤ b → IsCompact (F ⁻¹' Icc a b))
    (hindex : ∀ p ∈ criticalPoints I (F ∘ j), n ≤ manifoldMorseIndex I (F ∘ j) p)
    (R : A_cat) {k : ℕ} {hAW : A ⊆ W}
    (hW : IsIso (SSet.homologyMap (TopCat.toSSet.map
      (TopCat.ofHom (ContinuousMap.inclusion hAW))) R k))
    (hδ : ∃ δ > 0, {x | F x ≤ δ} ⊆ W) (hk : k + 1 < n) :
    Mono (SSet.homologyMap (TopCat.toSSet.map
      (TopCat.ofHom (ContinuousMap.subtypeVal A))) R k) := by
  obtain ⟨a, b, hab, -, hAa, haW, hA_lt, hFb, ha_reg, hb_reg, hcpt⟩ :=
    hf.exists_sandwich_levels hj hbdd hA hAF hcompact hδ
  let H := (AlgebraicTopology.singularHomologyFunctor A_cat k).obj R
  have : IsIso (H.map (TopCat.ofHom (ContinuousMap.inclusion hAW))) := by
    rwa [singularHomologyFunctor_obj_map]
  have : Mono (H.map (TopCat.ofHom (ContinuousMap.inclusion hAa)) ≫
      H.map (TopCat.ofHom (ContinuousMap.inclusion haW))) := by
    rw [← H.map_comp, ← TopCat.ofHom_comp, ContinuousMap.inclusion_comp_inclusion]
    infer_instance
  have : Mono (H.map (TopCat.ofHom (ContinuousMap.inclusion hAa))) :=
    mono_of_mono _ (H.map (TopCat.ofHom (ContinuousMap.inclusion haW)))
  have : IsIso (H.map (TopCat.ofHom (sublevelInclusion F a b hab))) := by
    rw [singularHomologyFunctor_obj_map]
    exact hf.isIso_homologyMap_sublevelInclusion_of_isOpenEmbedding hj hF hab hcpt hA_lt ha_reg
      hb_reg (fun p hp ↦ hindex p hp.1) R hk
  have : Mono (H.map (TopCat.ofHom (ContinuousMap.subtypeVal {x | F x ≤ a}))) := by
    rw [← sublevelInclusion_comp_sublevelHomeomorphUniv hab fun x ↦ (hFb x).le, H.map_comp]
    exact mono_comp _ _
  have hmono : Mono (H.map (TopCat.ofHom (ContinuousMap.inclusion hAa)) ≫
      H.map (TopCat.ofHom (ContinuousMap.subtypeVal {x | F x ≤ a}))) := mono_comp _ _
  rw [← H.map_comp, ← TopCat.ofHom_comp, ContinuousMap.subtypeVal_comp_inclusion] at hmono
  dsimp only [H] at hmono
  rwa [singularHomologyFunctor_obj_map] at hmono

/-- **Isomorphism `H_k(A; R) ≅ H_k(X; R)` for `k + 1 < n` on a compactified pair.** If `A ↪ W`
induces a singular homology isomorphism in degree `k` on a set `W` containing a positive sublevel
`{F ≤ δ}`, then `A ↪ X` induces an isomorphism `H_k(A; R) ≅ H_k(X; R)` for `k + 1 < n`. -/
theorem IsMorse.isIso_homologyMap_subtypeVal_of_isOpenEmbedding (hj : IsOpenEmbedding j)
    (hF : Continuous F) (hf : IsMorse I (F ∘ j)) (hbdd : BddAbove (range F))
    (hA : ∀ x ∉ range j, F x ≤ 0) (hAF : ∀ x ∈ A, F x ≤ 0)
    (hcompact : ∀ a b, 0 < a → a ≤ b → IsCompact (F ⁻¹' Icc a b))
    (hindex : ∀ p ∈ criticalPoints I (F ∘ j), n ≤ manifoldMorseIndex I (F ∘ j) p)
    (R : A_cat) {k : ℕ} {hAW : A ⊆ W}
    (hW : IsIso (SSet.homologyMap (TopCat.toSSet.map
      (TopCat.ofHom (ContinuousMap.inclusion hAW))) R k))
    (hδ : ∃ δ > 0, {x | F x ≤ δ} ⊆ W) (hk : k + 1 < n) :
    IsIso (SSet.homologyMap (TopCat.toSSet.map
      (TopCat.ofHom (ContinuousMap.subtypeVal A))) R k) := by
  let f : TopCat.of A ⟶ TopCat.of X := TopCat.ofHom (ContinuousMap.subtypeVal A)
  have : Mono (SSet.homologyMap (TopCat.toSSet.map f) R k) :=
    hf.mono_homologyMap_subtypeVal_of_isOpenEmbedding hj hF hbdd hA hAF hcompact hindex R hW hδ hk
  have : Epi (SSet.homologyMap (TopCat.toSSet.map f) R k) :=
    hf.epi_homologyMap_subtypeVal_of_isOpenEmbedding hj hF hbdd hA hAF hcompact hindex R hW hδ
      (by omega)
  exact isIso_of_mono_of_epi (SSet.homologyMap (TopCat.toSSet.map f) R k)

/-- **Relative singular homology vanishing `H_k(X, A; R) = 0` for `k < n` on a compactified
pair.** If `A ↪ W` induces singular homology isomorphisms in degree `k` and (when `k > 0`) degree
`k - 1` on a set `W` containing a positive sublevel `{F ≤ δ}`, then `H_k(X, A; R) = 0` for
`k < n`. -/
theorem IsMorse.isZero_singularHomology_ofSubset_of_isOpenEmbedding (hj : IsOpenEmbedding j)
    (hF : Continuous F) (hf : IsMorse I (F ∘ j)) (hbdd : BddAbove (range F))
    (hA : ∀ x ∉ range j, F x ≤ 0) (hAF : ∀ x ∈ A, F x ≤ 0)
    (hcompact : ∀ a b, 0 < a → a ≤ b → IsCompact (F ⁻¹' Icc a b))
    (hindex : ∀ p ∈ criticalPoints I (F ∘ j), n ≤ manifoldMorseIndex I (F ∘ j) p)
    (R : A_cat) {k : ℕ} {hAW : A ⊆ W}
    (hW : ∀ m, m = k ∨ m + 1 = k → IsIso (SSet.homologyMap (TopCat.toSSet.map
      (TopCat.ofHom (ContinuousMap.inclusion hAW))) R m))
    (hδ : ∃ δ > 0, {x | F x ≤ δ} ⊆ W) (hk : k < n) :
    IsZero ((TopPair.ofSubset (X := TopCat.of X) A).singularHomology R k) := by
  let P := TopPair.ofSubset (X := TopCat.of X) A
  have hepi : Epi (SSet.homologyMap (TopCat.toSSet.map P.map) R k) :=
    hf.epi_homologyMap_subtypeVal_of_isOpenEmbedding hj hF hbdd hA hAF hcompact hindex R
      (hW k (.inl rfl)) hδ hk
  have hπ : P.singularHomologyπ R k = 0 :=
    (cancel_epi (SSet.homologyMap (TopCat.toSSet.map P.map) R k)).1
      ((P.homologyMap_comp_singularHomologyπ R k).trans comp_zero.symm)
  rcases k with _ | k
  · exact (IsZero.iff_id_eq_zero _).2 <| (cancel_epi (P.singularHomologyπ R 0)).1 <|
      (Category.comp_id _).trans (hπ.trans comp_zero.symm)
  · have hmono : Mono (SSet.homologyMap (TopCat.toSSet.map P.map) R k) :=
      hf.mono_homologyMap_subtypeVal_of_isOpenEmbedding hj hF hbdd hA hAF hcompact hindex R
        (hW k (.inr rfl)) hδ hk
    have hδ₀ : P.singularHomologyδ R (k + 1) k rfl = 0 :=
      (cancel_mono (SSet.homologyMap (TopCat.toSSet.map P.map) R k)).1
        ((P.singularHomologyδ_comp R (k + 1) k rfl).trans zero_comp.symm)
    exact (P.singularHomology_exact_relative R (k + 1) k rfl).isZero_X₂ hπ hδ₀

end Homology

end PairConnectivity

end TauCeti
