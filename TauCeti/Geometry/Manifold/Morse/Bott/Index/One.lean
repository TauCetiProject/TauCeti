/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.Bott.Thom.Pair
public import TauCeti.Topology.VectorBundle.Thom.LineBundle
import TauCeti.Geometry.Manifold.Morse.Bott.Thom.DiscSpherePair

/-!
# Crossing the level of a Morse–Bott submanifold of index one

Let `i : S → M` be a nondegenerate critical submanifold of a smooth function `f` on the level
`f = c`, along which the Morse index of `f` is `1`, and let `g` be a fibre metric on its normal
bundle. The negative normal spaces relative to `g` then form a real line bundle `ν⁻ → S`, the
negative normal bundle, which need not be orientable. Bott's theorem identifies the relative
homology across the level with the homology of `S` shifted by the index and twisted by the
orientation local system `o(ν⁻)` (`TauCeti.VectorBundleOrientationCover.signLocalSystem`). This
file proves that identification in index one, in every degree and over every ring `R`, for
instance `ℤ`, with no orientation of `ν⁻`:

* for `ε > 0` the negative disc bundle `D_ε`, relative to the negative sphere bundle `S_ε`, has
  `Hₙ₊₁(D_ε, S_ε; R) ≅ Hₙ(S; o(ν⁻))`
  (`nonempty_singularHomology_negativeDiscSpherePair_succ_iso_twistedHomology`, in the namespace
  `TauCeti.SmoothEmbedding.IsCriticalSubmanifold`);
* if `a < c < b`, the band `f⁻¹[a, b]` is compact and all its critical points lie on `i`, then
  `Hₙ₊₁({f ≤ b}, {f ≤ a}; R) ≅ Hₙ(S; o(ν⁻))`
  (`nonempty_singularHomology_sublevelPair_succ_iso_twistedHomology`, in the namespace
  `TauCeti.SmoothEmbedding.IsNondegenerateCriticalSubmanifold`).

In degree `0` the relative homology vanishes, as it does below the index in every rank
(`isZero_singularHomology_sublevelPair_of_lt`, in the namespace
`TauCeti.SmoothEmbedding.IsNondegenerateCriticalSubmanifold`), so these statements compute the
relative homology across the level in all degrees. With a Thom class of `ν⁻`, for instance over
`ZMod 2` or for an orientable `ν⁻`, the twist can be dropped
(`nonempty_singularHomology_sublevelPair_iso_singularHomology_of_isThomClass`, in the namespace
`TauCeti.SmoothEmbedding.IsNondegenerateCriticalSubmanifold`); over `ℤ` and for a non-orientable
`ν⁻` it cannot. For a critical circle whose negative normal bundle is a Möbius line,
`H₁({f ≤ b}, {f ≤ a}; ℤ)` is `H₀(S¹; o(ν⁻)) ≅ ℤ/2` rather than `H₀(S¹; ℤ) ≅ ℤ`.

The proof equips `ν⁻` with the norm of the inner product `-½ Hessₛ`
(`TauCeti.SmoothEmbedding.IsCriticalSubmanifold.negativeNormalNorm`), which is continuous on the
total space and whose unit disc and sphere bundles are `D_1` and `S_1`. The pair `(D_ε, S_ε)` has
the homology of the Thom pair `(ν⁻, ν⁻₀)`
(`TauCeti.SmoothEmbedding.IsCriticalSubmanifold.isIso_singularHomologyMap_negativeDiscThomPairMap`),
and the Thom isomorphism of a line bundle with orientation coefficients,
`Hₙ₊₁(ν⁻, ν⁻₀; R) ≅ Hₙ(S; o(ν⁻))`
(`TauCeti.thomPairSingularHomologySuccIsoOrientationTwistedHomology`), computes it from the double
cover `S_1 → S`. The band has the homology of `(D_ε, S_ε)` for small `ε`
(`nonempty_singularHomology_sublevelPair_iso_negativeDiscSpherePair`, in the namespace
`TauCeti.SmoothEmbedding.IsNondegenerateCriticalSubmanifold`).

## References

* R. Bott, *Nondegenerate critical manifolds*, Annals of Mathematics 60 (1954), 248–261.
* R. L. Cohen, K. Iga and P. Norbury, *Topics in Morse theory: lecture notes*, 2006,
  Theorem 15.4.
* A. Hatcher, *Algebraic Topology*, Section 3.H (local coefficients and the local system of a
  covering space).
-/

public section

noncomputable section

open Bundle CategoryTheory Module Set Topology
open TauCeti.VectorBundleOrientationCover TauCeti.LocalCoefficientSystem
open scoped ContDiff Manifold

universe u

namespace TauCeti.SmoothEmbedding

/-! ### The negative disc-sphere pair -/

namespace IsCriticalSubmanifold

variable {E S : Type u} {H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M]
  [ChartedSpace H M] {E' H' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  [FiniteDimensional ℝ E'] [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'}
  [TopologicalSpace S] [ChartedSpace H' S] [IsManifold J 1 S] {f : M → ℝ} {n : ℕ∞ω}
  {i : SmoothEmbedding J I n S M} (hn : n ≠ 0) [I.Boundaryless] [IsManifold I 2 M]
  (h : i.IsCriticalSubmanifold f) {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [FiniteDimensional ℝ P] (g : RiemannianMetric fun s ↦ i.isImmersion.NormalSpace s hn) {ε : ℝ}
  (hdim : finrank ℝ P = finrank ℝ E - finrank ℝ E')

/-- **The homology of the negative disc bundle of a negative normal line bundle.** Let `i` be a
critical submanifold of `f`, let `g` be a fibre metric on its normal bundle, and suppose that the
negative normal spaces have continuous local frames of size one, so that they form a real line
bundle `ν⁻`. Then for `ε > 0` the negative disc bundle `D_ε`, relative to the negative sphere bundle
`S_ε`, has the homology of `S` with coefficients in the orientation local system `o(ν⁻)`, shifted
by one: `Hₖ₊₁(D_ε, S_ε; R) ≅ Hₖ(S; o(ν⁻))` for every ring `R` and every degree `k`. No orientation
of `ν⁻` is assumed. -/
theorem nonempty_singularHomology_negativeDiscSpherePair_succ_iso_twistedHomology
    (hV : letI := i.normalSpaceFiberBundle hn hdim
      HasLocalSubbundleFrames P (Fin 1) (h.negativeNormalSpace hn g))
    (hε : 0 < ε) (R : Type u) [Ring R] (k : ℕ) :
    letI := i.normalSpaceFiberBundle hn hdim
    haveI := i.normalSpaceVectorBundle hn hdim
    letI := subbundleTopology P (F' := Fin 1 → ℝ) (h.negativeNormalSpace hn g)
    letI := hV.fiberBundle
    haveI := hV.vectorBundle
    Nonempty ((h.negativeDiscSpherePair hn P g ε).singularHomology (ModuleCat.of R R) (k + 1) ≅
      (signLocalSystem (Fin 1 → ℝ) (fun s ↦ h.negativeNormalSpace hn g s) R
        ((Fintype.card_fin 1).trans (finrank_fin_fun ℝ).symm)).twistedHomology k) := by
  let := i.normalSpaceFiberBundle hn hdim
  have := i.normalSpaceVectorBundle hn hdim
  let := subbundleTopology P (F' := Fin 1 → ℝ) (h.negativeNormalSpace hn g)
  let := hV.fiberBundle
  have := hV.vectorBundle
  have := h.isIso_singularHomologyMap_negativeDiscThomPairMap hn g 1 hdim hV hε
    (ModuleCat.of R R) (k + 1)
  -- The Thom isomorphism of a line bundle needs a continuous fibre norm: take the norm of the inner
  -- product `-½ Hessₛ`.
  let := h.negativeNormalNorm hn g one_pos
  let _ (s : S) := (h.negativeNormalInnerProductSpace hn g one_pos s).toNormedSpace
  exact ⟨asIso (TopPair.singularHomologyMap (h.negativeDiscThomPairMap hn P g 1 hε)
      (ModuleCat.of R R) (k + 1)) ≪≫
    thomPairSingularHomologySuccIsoOrientationTwistedHomology
      (h.continuous_norm_negativeNormalNorm hn g 1 hdim one_pos) (finrank_fin_fun ℝ) R k⟩

end IsCriticalSubmanifold

/-! ### The homology of a critical band -/

namespace IsNondegenerateCriticalSubmanifold

variable {E M S : Type u} {H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [SecondCountableTopology M] {E' H' P : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  [FiniteDimensional ℝ E'] [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'} [J.Boundaryless]
  [TopologicalSpace S] [ChartedSpace H' S] [IsManifold J ∞ S] [NormedAddCommGroup P]
  [NormedSpace ℝ P] [FiniteDimensional ℝ P] {f : M → ℝ} {i : SmoothEmbedding J I ∞ S M}
  (hn : (∞ : ℕ∞ω) ≠ 0) (h : i.IsNondegenerateCriticalSubmanifold f)
  (hfs : ContMDiff I 𝓘(ℝ) ∞ f) {a b c : ℝ} (hc : ∀ s, f (i s) = c) (hac : a < c) (hcb : c < b)
  (hcompact : IsCompact (f ⁻¹' Icc a b)) (hcrit : criticalPoints I f ∩ f ⁻¹' Icc a b ⊆ range i)
  (hdim : finrank ℝ P = finrank ℝ E - finrank ℝ E')
  (g : letI := i.normalSpaceFiberBundle hn hdim
    letI := i.normalSpaceVectorBundle hn hdim
    ContMDiffRiemannianMetric J ∞ P fun s ↦ i.isImmersion.NormalSpace s hn)

include h hfs hc hac hcb hcompact hcrit in
/-- **Across a Morse–Bott level of index one, the relative homology is the homology of the
critical submanifold with orientation coefficients, shifted by one.** Let `i : S → M` be a
nondegenerate critical submanifold of a smooth function `f` on a Hausdorff, second-countable,
finite-dimensional, boundaryless manifold, with `f = c` along `i`, and let `g` be a smooth fibre
metric on its normal bundle. Let `a < c < b` be such that the band `f⁻¹[a, b]` is compact and all
its critical points lie on `i`. Suppose that the negative normal spaces relative to `g` have
continuous local frames of size one, so that they form the negative normal bundle `ν⁻`, a real line
bundle; the Morse index of `f` along `i` is then `1`, and conversely such frames exist when the
Morse index is `1` at every point of `i`
(`IsNondegenerateCriticalSubmanifold.hasLocalContMDiffSubbundleFrames_negativeNormalSpace`). Then
`Hₖ₊₁({f ≤ b}, {f ≤ a}; R) ≅ Hₖ(S; o(ν⁻))` for every ring `R`, for instance `ℤ`, and every degree
`k`, where `o(ν⁻)` is the orientation local system of `ν⁻`. No orientation of `ν⁻` is assumed. -/
theorem nonempty_singularHomology_sublevelPair_succ_iso_twistedHomology
    (hV : letI := i.normalSpaceFiberBundle hn hdim
      letI := i.normalSpaceVectorBundle hn hdim
      HasLocalSubbundleFrames P (Fin 1) (h.negativeNormalSpace hn g.toRiemannianMetric))
    (R : Type u) [Ring R] (k : ℕ) :
    letI := i.normalSpaceFiberBundle hn hdim
    letI := i.normalSpaceVectorBundle hn hdim
    letI := subbundleTopology P (F' := Fin 1 → ℝ) (h.negativeNormalSpace hn g.toRiemannianMetric)
    letI := hV.fiberBundle
    haveI := hV.vectorBundle
    Nonempty ((sublevelPair f (hac.trans hcb).le).singularHomology (ModuleCat.of R R) (k + 1) ≅
      (signLocalSystem (Fin 1 → ℝ) (fun s ↦ h.negativeNormalSpace hn g.toRiemannianMetric s) R
        ((Fintype.card_fin 1).trans (finrank_fin_fun ℝ).symm)).twistedHomology k) := by
  let := i.normalSpaceFiberBundle hn hdim
  let := i.normalSpaceVectorBundle hn hdim
  let := subbundleTopology P (F' := Fin 1 → ℝ) (h.negativeNormalSpace hn g.toRiemannianMetric)
  let := hV.fiberBundle
  have := hV.vectorBundle
  cases isEmpty_or_nonempty S with
  | inl _ =>
    -- Over an empty critical submanifold the band has no critical points, and both groups vanish.
    have : IsEmpty (TopCat.of S) := inferInstanceAs (IsEmpty S)
    exact ⟨(isZero_singularHomology_sublevelPair_of_isEmpty hfs (hac.trans hcb).le hcompact hcrit
      _ _).iso (isZero_twistedHomology_of_isEmpty _ k)⟩
  | inr _ =>
    -- The band has the homology of `(D_ε, S_ε)` for small `ε`, which the Thom isomorphism of the
    -- line bundle `ν⁻` computes.
    obtain ⟨ε₀, hε₀, hband⟩ :=
      h.nonempty_singularHomology_sublevelPair_iso_negativeDiscSpherePair hn hfs hc hac hcb hcompact
        hcrit hdim g hV
    have hε : ε₀ / 2 ∈ Ioo 0 ε₀ := ⟨half_pos hε₀, half_lt_self hε₀⟩
    obtain ⟨e₁⟩ := hband (ε₀ / 2) hε (ModuleCat.of R R) (k + 1)
    have h' := h.toIsCriticalSubmanifold
    obtain ⟨e₂⟩ := h'.nonempty_singularHomology_negativeDiscSpherePair_succ_iso_twistedHomology hn
      g.toRiemannianMetric hdim hV hε.1 R k
    exact ⟨e₁ ≪≫ e₂⟩

end IsNondegenerateCriticalSubmanifold

end TauCeti.SmoothEmbedding
