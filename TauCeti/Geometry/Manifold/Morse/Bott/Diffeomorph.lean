/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.Bott.Count
import Mathlib.Topology.Homeomorph.Lemmas
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Composition
import TauCeti.Geometry.Manifold.Morse.LocalDiffeomorph
import TauCeti.Geometry.Manifold.Morse.Submersion

/-!
# Morse–Bott functions under diffeomorphisms

The Morse–Bott property is natural: composing with a diffeomorphism carries critical
submanifolds, their nondegeneracy, the Morse–Bott families exhibiting a function and the indices
of their pieces from one manifold to the other. These are the Morse–Bott counterparts of the
invariance of critical bands (`TauCeti.IsCriticalBandCut.comp_diffeomorph`) and of the spectral
sequence of a sublevel filtration (`TauCeti.filteredSpaceSpectralSequenceSublevelCompIso`) under
diffeomorphisms.

Let `π : M → M'` be a map between boundaryless manifolds, possibly with different models, let
`f : M' → ℝ`, and let `i : S → M` and `i' : S → M'` be smooth embeddings with `i' = π ∘ i`. If `π`
is a `C²` local diffeomorphism at each point of `i`, then

* `i` is a critical submanifold of `f ∘ π` exactly when `i'` is a critical submanifold of `f`
  (`TauCeti.SmoothEmbedding.isCriticalSubmanifold_comp_iff_of_isLocalDiffeomorphAt`);
* `i` is a Morse–Bott critical submanifold of `f ∘ π` exactly when `i'` is one of `f`
  (`TauCeti.SmoothEmbedding.isNondegenerateCriticalSubmanifold_comp_iff_of_isLocalDiffeomorphAt`).

Indeed, `dπ` carries the kernel of the critical Hessian of `f ∘ π` at `i s` onto that of `f` at
`i' s`, and the tangent space of `i` onto that of `i'`. This applies for instance to a covering map
`π`: a lift `i` of a submanifold `i'` along `π`, embedded in the cover, is a Morse–Bott critical
submanifold of `f ∘ π` exactly when `i'` is one of `f`.

For a smooth diffeomorphism `σ : M → M'` the global conditions of a Morse–Bott family, which
concern the connected components of the critical set and the local finiteness of the pieces, are
carried along too, since `σ` is a homeomorphism matching the critical sets
(`IsLocalDiffeomorph.criticalPoints_comp`). So a family `i'` exhibits `f` as a Morse–Bott
function exactly when the family `i = σ⁻¹ ∘ i'`, with the same pieces, exhibits `f ∘ σ` as one
(`TauCeti.isMorseBottFamily_comp_diffeomorph_iff`); then each piece keeps its index
(`TauCeti.IsMorseBottFamily.index_comp_diffeomorph`), and the Morse–Bott counts of the two
families agree (`TauCeti.IsMorseBottFamily.morseBottCount_comp_diffeomorph`).

## Main results

* `TauCeti.SmoothEmbedding.isCriticalSubmanifold_comp_iff_of_isLocalDiffeomorphAt`: critical
  submanifolds under a local diffeomorphism.
* `TauCeti.SmoothEmbedding.isNondegenerateCriticalSubmanifold_comp_iff_of_isLocalDiffeomorphAt`:
  Morse–Bott critical submanifolds under a local diffeomorphism.
* `TauCeti.IsMorseBottFamily.comp_diffeomorph`: a Morse–Bott family of `f` pulls back to a
  Morse–Bott family of `f ∘ σ`.
* `TauCeti.isMorseBottFamily_comp_diffeomorph_iff`: the two families are Morse–Bott together.
* `TauCeti.IsMorseBottFamily.index_comp_diffeomorph`: the pieces keep their indices.
* `TauCeti.IsMorseBottFamily.morseBottCount_comp_diffeomorph`: the Morse–Bott counts agree.

## References

* R. Bott, *Nondegenerate critical manifolds*, Annals of Mathematics 60 (1954), 248–261.
-/

public section

open Function Set
open scoped ContDiff Manifold

universe u

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  {E' H' M' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  {I' : ModelWithCorners ℝ E' H'} [TopologicalSpace M'] [ChartedSpace H' M']
  {f : M' → ℝ} {m : ℕ∞ω}

/-! ### Critical submanifolds under a local diffeomorphism -/

namespace SmoothEmbedding

variable {F G S : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace G]
  {J : ModelWithCorners ℝ F G} [TopologicalSpace S] [ChartedSpace G S] {n n' : ℕ∞ω}
  {i : SmoothEmbedding J I n S M} {i' : SmoothEmbedding J I' n' S M'} {π : M → M'}

/-- **Critical submanifolds under a local diffeomorphism.** Let `i : S → M` and `i' : S → M'` be
smooth embeddings with `i' = π ∘ i`, where `π` is a `C^m` local diffeomorphism, `2 ≤ m`, at each
point of `i`. Then `i` is a critical submanifold of `f ∘ π` exactly when `i'` is a critical
submanifold of `f`. -/
theorem isCriticalSubmanifold_comp_iff_of_isLocalDiffeomorphAt
    (hπ : ∀ s, IsLocalDiffeomorphAt I I' m π (i s)) (hm : 2 ≤ m) (hi : ⇑i' = π ∘ i) :
    i.IsCriticalSubmanifold (f ∘ π) ↔ i'.IsCriticalSubmanifold f := by
  have hC (s : S) : ContMDiffAt I 𝓘(ℝ) 2 (f ∘ π) (i s) ↔ ContMDiffAt I' 𝓘(ℝ) 2 f (i' s) := by
    rw [hi]
    exact (hπ s).contMDiffAt_comp_iff hm
  have hcrit (s : S) : i s ∈ criticalPoints I (f ∘ π) ↔ i' s ∈ criticalPoints I' f := by
    rw [hi]
    exact (hπ s).mem_criticalPoints_comp_iff (one_le_two.trans hm)
  exact ⟨fun h ↦ ⟨fun s ↦ (hC s).1 (h.contMDiffAt s), fun s ↦ (hcrit s).1 (h.mem_criticalPoints s)⟩,
    fun h ↦ ⟨fun s ↦ (hC s).2 (h.contMDiffAt s), fun s ↦ (hcrit s).2 (h.mem_criticalPoints s)⟩⟩

variable [I.Boundaryless] [I'.Boundaryless]

/-- Along a critical submanifold `i'` of `f` with `i' = π ∘ i`, where `π` is a `C²` local
diffeomorphism at `i s`, the kernel of the critical Hessian of `f ∘ π` at `i s` lies in the tangent
space of `i` exactly when the kernel of the critical Hessian of `f` at `i' s` lies in the tangent
space of `i'`: the invertible map `dπ` carries the first pair of subspaces onto the second. -/
private theorem ker_criticalHessian_comp_le_iff {s : S} (hπ : IsLocalDiffeomorphAt I I' m π (i s))
    (hm : 2 ≤ m) (hn : n ≠ 0) (hi : ⇑i' = π ∘ i) (h : i'.IsCriticalSubmanifold f) :
    (criticalHessian I (f ∘ π) (i s)).ker ≤ (mfderiv J I i s).toLinearMap.range ↔
      (criticalHessian I' f (i' s)).ker ≤ (mfderiv J I' i' s).toLinearMap.range := by
  have hm0 : m ≠ 0 := (two_pos.trans_le hm).ne'
  have hD := hπ.isInvertible_mfderiv hm0
  have his : i' s = π (i s) := congrFun hi s
  have hf : ContMDiffAt I' 𝓘(ℝ) 2 f (π (i s)) := his ▸ h.contMDiffAt s
  have hcrit : π (i s) ∈ criticalPoints I' f := his ▸ h.mem_criticalPoints s
  -- The tangent space of `i'` is the image under `dπ` of that of `i`.
  have hrange : (mfderiv J I' i' s).toLinearMap.range =
      (mfderiv J I i s).toLinearMap.range.map (mfderiv I I' π (i s)).toLinearMap := by
    rw [hi, mfderiv_comp s (hπ.mdifferentiableAt hm0) ((i.contMDiff s).mdifferentiableAt hn),
      ContinuousLinearMap.toLinearMap_comp, LinearMap.range_comp]
  -- The kernel of the Hessian of `f` is the image under `dπ` of that of `f ∘ π`.
  rw [(isRegularPoint_iff.2 hD.surjective).ker_criticalHessian_comp hf
      (hπ.contMDiffAt.of_le hm) hcrit, hrange, his,
    ← Submodule.map_le_map_iff_of_injective hD.injective,
    Submodule.map_comap_eq_of_surjective hD.surjective]

/-- **Morse–Bott critical submanifolds under a local diffeomorphism.** Let `i : S → M` and
`i' : S → M'` be smooth embeddings with `i' = π ∘ i` between boundaryless manifolds, where `π` is a
`C^m` local diffeomorphism, `2 ≤ m`, at each point of `i`. Then `i` is a Morse–Bott critical
submanifold of `f ∘ π` exactly when `i'` is a Morse–Bott critical submanifold of `f`. -/
theorem isNondegenerateCriticalSubmanifold_comp_iff_of_isLocalDiffeomorphAt
    (hπ : ∀ s, IsLocalDiffeomorphAt I I' m π (i s)) (hm : 2 ≤ m) (hn : n ≠ 0)
    (hi : ⇑i' = π ∘ i) :
    i.IsNondegenerateCriticalSubmanifold (f ∘ π) ↔ i'.IsNondegenerateCriticalSubmanifold f := by
  have hC := isCriticalSubmanifold_comp_iff_of_isLocalDiffeomorphAt (f := f) hπ hm hi
  refine ⟨fun h ↦ ⟨hC.1 h.toIsCriticalSubmanifold, fun s ↦ ?_⟩,
    fun h ↦ ⟨hC.2 h.toIsCriticalSubmanifold, fun s ↦ ?_⟩⟩
  · exact (ker_criticalHessian_comp_le_iff (hπ s) hm hn hi
      (hC.1 h.toIsCriticalSubmanifold)).1 (h.ker_criticalHessian_le s)
  · exact (ker_criticalHessian_comp_le_iff (hπ s) hm hn hi
      h.toIsCriticalSubmanifold).2 (h.ker_criticalHessian_le s)

end SmoothEmbedding

/-! ### Morse–Bott families under a diffeomorphism -/

section Family

variable {ι : Type*} {F : ι → Type*} [∀ a, NormedAddCommGroup (F a)] [∀ a, NormedSpace ℝ (F a)]
  {G : ι → Type*} [∀ a, TopologicalSpace (G a)] {J : ∀ a, ModelWithCorners ℝ (F a) (G a)}
  {S : ι → Type*} [∀ a, TopologicalSpace (S a)] [∀ a, ChartedSpace (G a) (S a)] {n n' : ℕ∞ω}
  {i : ∀ a, SmoothEmbedding (J a) I n (S a) M} {i' : ∀ a, SmoothEmbedding (J a) I' n' (S a) M'}
  [I.Boundaryless] [I'.Boundaryless]

/-- **Morse–Bott functions pull back along diffeomorphisms.** Let `σ : M → M'` be a smooth
diffeomorphism between boundaryless manifolds and let the family `i'` exhibit `f` as a Morse–Bott
function. Then a family `i` of embeddings of the same pieces with `i' a = σ ∘ i a`, that is,
`i a = σ⁻¹ ∘ i' a`, exhibits `f ∘ σ` as a Morse–Bott function. -/
theorem IsMorseBottFamily.comp_diffeomorph (h : IsMorseBottFamily i' f)
    (σ : M ≃ₘ^m⟮I, I'⟯ M') (hm : ∞ ≤ m) (hn : n ≠ 0) (hi : ∀ a, ⇑(i' a) = σ ∘ i a) :
    IsMorseBottFamily i (f ∘ σ) := by
  have hm2 : 2 ≤ m := le_trans (by simp) hm
  have hrange (a : ι) : range (i a) = σ ⁻¹' range (i' a) := by
    rw [hi, range_comp, preimage_image_eq _ (EquivLike.injective σ)]
  have hcrit : criticalPoints I (f ∘ σ) = σ ⁻¹' criticalPoints I' f :=
    σ.isLocalDiffeomorph.criticalPoints_comp (one_le_two.trans hm2)
  refine
    { contMDiff := h.contMDiff.comp (σ.contMDiff.of_le hm)
      isNondegenerateCriticalSubmanifold := fun a ↦
        (SmoothEmbedding.isNondegenerateCriticalSubmanifold_comp_iff_of_isLocalDiffeomorphAt
          (fun s ↦ σ.isLocalDiffeomorph (i a s)) hm2 hn (hi a)).2
          (h.isNondegenerateCriticalSubmanifold a)
      nonempty := h.nonempty
      boundarylessManifold := h.boundarylessManifold
      range_eq_connectedComponentIn := fun a s ↦ ?_
      range_injective := fun a b hab ↦ h.range_injective <|
        preimage_injective.2 (EquivLike.surjective σ) <| by simpa only [hrange] using hab
      criticalPoints_subset_iUnion_range := ?_
      locallyFinite_range := ?_ }
  · -- `σ⁻¹` carries the connected component of the critical set of `f` through `i' a s` onto the
    -- connected component of the critical set of `f ∘ σ` through `i a s`.
    have hs : i' a s ∈ criticalPoints I' f := h.range_subset_criticalPoints a (mem_range_self s)
    have := σ.toHomeomorph.symm.image_connectedComponentIn hs
    rw [Diffeomorph.coe_toHomeomorph_symm, σ.symm_image_eq_preimage,
      σ.symm_image_eq_preimage, hi a, comp_apply, σ.symm_apply_apply] at this
    rw [hrange, hcrit, h.range_eq_connectedComponentIn a s, hi a, comp_apply, this]
  · rw [hcrit]
    simp_rw [hrange, ← preimage_iUnion]
    exact preimage_mono h.criticalPoints_subset_iUnion_range
  · simp_rw [hrange]
    exact h.locallyFinite_range.preimage_continuous σ.continuous

/-- **The Morse–Bott property is invariant under diffeomorphisms.** Let `σ : M → M'` be a smooth
diffeomorphism between boundaryless manifolds, and let `i` and `i'` be families of embeddings of
the same pieces into `M` and `M'` with `i' a = σ ∘ i a`. Then `i` exhibits `f ∘ σ` as a Morse–Bott
function exactly when `i'` exhibits `f` as one. -/
theorem isMorseBottFamily_comp_diffeomorph_iff (σ : M ≃ₘ^m⟮I, I'⟯ M') (hm : ∞ ≤ m) (hn : n ≠ 0)
    (hn' : n' ≠ 0) (hi : ∀ a, ⇑(i' a) = σ ∘ i a) :
    IsMorseBottFamily i (f ∘ σ) ↔ IsMorseBottFamily i' f := by
  refine ⟨fun h ↦ ?_, fun h ↦ h.comp_diffeomorph σ hm hn hi⟩
  have hi' (a : ι) : ⇑(i a) = σ.symm ∘ i' a := by
    funext s
    rw [hi, comp_apply, comp_apply, σ.symm_apply_apply]
  have hf : (f ∘ σ) ∘ σ.symm = f := by
    funext x
    rw [comp_apply, comp_apply, σ.apply_symm_apply]
  simpa only [hf] using h.comp_diffeomorph σ.symm hm hn' hi'

variable [FiniteDimensional ℝ E]

/-- **The pieces keep their indices under a diffeomorphism.** For the Morse–Bott family
`IsMorseBottFamily.comp_diffeomorph` of `f ∘ σ` obtained from one of `f`, each piece has the same
Morse index for `f ∘ σ` as for `f`. -/
theorem IsMorseBottFamily.index_comp_diffeomorph (h : IsMorseBottFamily i' f)
    (σ : M ≃ₘ^m⟮I, I'⟯ M') (hm : ∞ ≤ m) (hn : n ≠ 0) (hi : ∀ a, ⇑(i' a) = σ ∘ i a) (a : ι) :
    (h.comp_diffeomorph σ hm hn hi).index a = h.index a := by
  have hm2 : 2 ≤ m := le_trans (by simp) hm
  have hσ : IsRegularPoint I I' σ (i a (h.nonempty a).some) :=
    isRegularPoint_iff.2 (σ.isInvertible_mfderiv (two_pos.trans_le hm2).ne').surjective
  have hs : σ (i a (h.nonempty a).some) = i' a (h.nonempty a).some := by rw [hi a, comp_apply]
  rw [index_def, index_def, ← hs]
  exact hσ.manifoldMorseIndex_comp (h.contMDiff.contMDiffAt.of_le (by simp))
    (σ.contMDiffAt.of_le hm2) (hs ▸ h.range_subset_criticalPoints a (mem_range_self _))

/-- **The Morse–Bott counts are invariant under diffeomorphisms.** For the Morse–Bott family
`IsMorseBottFamily.comp_diffeomorph` of `f ∘ σ` obtained from one of `f`, the Morse–Bott counts
agree in every degree and over every ring: the two families have the same pieces with the same
indices. -/
theorem IsMorseBottFamily.morseBottCount_comp_diffeomorph {S : ι → Type u}
    [∀ a, TopologicalSpace (S a)] [∀ a, ChartedSpace (G a) (S a)]
    {i : ∀ a, SmoothEmbedding (J a) I n (S a) M} {i' : ∀ a, SmoothEmbedding (J a) I' n' (S a) M'}
    (h : IsMorseBottFamily i' f) (σ : M ≃ₘ^m⟮I, I'⟯ M') (hm : ∞ ≤ m) (hn : n ≠ 0)
    (hi : ∀ a, ⇑(i' a) = σ ∘ i a) (k : Type u) [Ring k] (j : ℕ) :
    (h.comp_diffeomorph σ hm hn hi).morseBottCount k j = h.morseBottCount k j := by
  have hindex : (h.comp_diffeomorph σ hm hn hi).index = h.index :=
    funext (h.index_comp_diffeomorph σ hm hn hi)
  rw [morseBottCount_def, morseBottCount_def, hindex]

end Family

end TauCeti
