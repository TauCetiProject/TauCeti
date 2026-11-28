/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Sublevel
public import TauCeti.Geometry.Manifold.Morse.Bott.Family
public import TauCeti.Geometry.Manifold.Morse.Bott.Thom.TwistedHomology
public import TauCeti.Geometry.Manifold.Morse.CriticalPoints

/-!
# Vanishing of homology from a Morse–Bott function over any ring

Let the family `i j : S j → M` exhibit `f` as a Morse–Bott function, and let the negative normal
bundle `ν⁻ j` of the piece `S j` have rank `r j`, the index of the piece. Crossing a critical level
`c` changes the homology of the sublevels by the twisted homology of the pieces on that level,
shifted by their indices: over every commutative ring `K`, `ℤ` included,

`Hₙ({f ≤ b}, {f ≤ a}; K) ≅ ⨁_{r j ≤ n} H_{n - r j}(S j; o(ν⁻ j) ⊗ K)`

when `c` is the only critical value in the compact band `f⁻¹[a, b]` and `a < c < b`
(`TauCeti.IsMorseBottFamily.nonempty_singularHomology_sublevelPair_iso_sigma_twistedHomology`).
This file draws the qualitative consequence over any ring: the homology of `M` vanishes in every
degree `n` in which all the pieces contribute nothing.

* Along a critical-band cut `a : ℤ → ℝ`, `Hₙ({f ≤ a q'}, {f ≤ a q}; K) = 0` as soon as
  `H_{n - r j}(S j; o(ν⁻ j) ⊗ K) = 0` for every piece with values in `(a q, a q']` and of index
  `r j ≤ n` (in the namespace `TauCeti.IsMorseBottFamily`,
  `isZero_singularHomology_sublevelPair_of_forall_isZero_twistedHomology`).
* On a compact manifold, `Hₙ(M; K) = 0` as soon as `H_{n - r j}(S j; o(ν⁻ j) ⊗ K) = 0` for every
  piece of index `r j ≤ n`
  (`TauCeti.IsMorseBottFamily.isZero_singularHomology_of_forall_isZero_twistedHomology`).

These are the Morse–Bott counterparts of the vanishing of `Hₙ(M; R)` for a Morse function without
critical points of index `n` (`TauCeti.IsMorse.isZero_singularHomology_of_criticalCount_eq_zero`).
Over a field they follow from the weak Morse–Bott inequalities
(`TauCeti.IsMorseBottFamily.bettiNumber_le_sum_twistedBettiNumber`); over `ℤ` dimensions are not
available and the twist matters. For a critical circle of index one whose negative normal bundle is
a Möbius line, `H₀(S¹; o(ν⁻)) ≅ ℤ/2` is not zero, so the circle may contribute to `H₁(M; ℤ)` even
though `H₀(S¹; o(ν⁻) ⊗ ℚ) = 0`.

The proof cuts the values of `f` into critical bands and adds one band at a time, through the long
exact sequences of the triples of sublevels
(`Monotone.isZero_singularHomology_ofInclusion_of_forall_mem_Ico`).

## Main results

In the namespace `TauCeti.IsMorseBottFamily`:

* `isZero_singularHomology_sublevelPair_of_forall_isZero_twistedHomology`: vanishing of the
  relative homology of two sublevels of a critical-band cut.
* `isZero_singularHomology_of_forall_isZero_twistedHomology`: vanishing of the homology of a
  compact manifold.

## References

* R. Bott, *Nondegenerate critical manifolds*, Annals of Mathematics 60 (1954), 248–261.
* R. L. Cohen, K. Iga and P. Norbury, *Topics in Morse theory: lecture notes*, 2006,
  Theorems 15.4 and 15.7.
-/

public section

noncomputable section

open AlgebraicTopology Bundle CategoryTheory Limits Module Set
open TauCeti.LocalCoefficientSystem TauCeti.VectorBundleOrientationCover
open scoped ContDiff Manifold

namespace TauCeti.IsMorseBottFamily

universe u

variable {E M : Type u} {H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [SecondCountableTopology M] {ι : Type*} {E' H' P : ι → Type*} {S : ι → Type u}
  [∀ j, NormedAddCommGroup (E' j)] [∀ j, NormedSpace ℝ (E' j)] [∀ j, FiniteDimensional ℝ (E' j)]
  [∀ j, TopologicalSpace (H' j)] {J : ∀ j, ModelWithCorners ℝ (E' j) (H' j)}
  [∀ j, (J j).Boundaryless] [∀ j, TopologicalSpace (S j)] [∀ j, ChartedSpace (H' j) (S j)]
  [∀ j, IsManifold (J j) ∞ (S j)] [∀ j, NormedAddCommGroup (P j)] [∀ j, NormedSpace ℝ (P j)]
  [∀ j, FiniteDimensional ℝ (P j)] {f : M → ℝ} {i : ∀ j, SmoothEmbedding (J j) I ∞ (S j) M}
  (hn : (∞ : ℕ∞ω) ≠ 0) (h : IsMorseBottFamily i f)
  (hdim : ∀ j, finrank ℝ (P j) = finrank ℝ E - finrank ℝ (E' j))
  (g : letI : ∀ j, FiberBundle (P j) fun s ↦ (i j).isImmersion.NormalSpace s hn :=
      fun j ↦ (i j).normalSpaceFiberBundle hn (hdim j)
    letI : ∀ j, VectorBundle ℝ (P j) fun s ↦ (i j).isImmersion.NormalSpace s hn :=
      fun j ↦ (i j).normalSpaceVectorBundle hn (hdim j)
    ∀ j, ContMDiffRiemannianMetric (J j) ∞ (P j) fun s ↦ (i j).isImmersion.NormalSpace s hn)
  {κ : ι → Type u} [∀ j, Fintype (κ j)]
  (hV : letI : ∀ j, FiberBundle (P j) fun s ↦ (i j).isImmersion.NormalSpace s hn :=
      fun j ↦ (i j).normalSpaceFiberBundle hn (hdim j)
    letI : ∀ j, VectorBundle ℝ (P j) fun s ↦ (i j).isImmersion.NormalSpace s hn :=
      fun j ↦ (i j).normalSpaceVectorBundle hn (hdim j)
    ∀ j, HasLocalSubbundleFrames (P j) (κ j)
      ((h.isNondegenerateCriticalSubmanifold j).negativeNormalSpace hn (g j).toRiemannianMetric))
  (K : Type u) [CommRing K]

/-- **Vanishing across critical bands over any ring.** Let the family `i j : S j → M` exhibit `f`
as a Morse–Bott function on a Hausdorff second-countable boundaryless manifold, with pieces
modelled on boundaryless models, let `g j` be smooth fibre metrics on the normal bundles of the
pieces, and let the negative normal spaces relative to `g j` have continuous local frames indexed
by a finite type `κ j`, so that they form the negative normal bundle `ν⁻ j` of rank `|κ j|`, the
index of the piece. Let `K` be a commutative ring, for instance `ℤ`, let `a : ℤ → ℝ` be a
critical-band cut of `f` and let `q ≤ q'`. If `H_{n - |κ j|}(S j; o(ν⁻ j) ⊗ K) = 0` for every
piece with values in `(a q, a q']` and of index `|κ j| ≤ n`, then
`Hₙ({f ≤ a q'}, {f ≤ a q}; K) = 0`. No orientation of the bundles `ν⁻ j` is assumed. -/
theorem isZero_singularHomology_sublevelPair_of_forall_isZero_twistedHomology {a : ℤ → ℝ}
    (ha : IsCriticalBandCut I f a) {q q' : ℤ} (hqq' : q ≤ q') (n : ℕ)
    (hz : letI : ∀ j, FiberBundle (P j) fun s ↦ (i j).isImmersion.NormalSpace s hn :=
        fun j ↦ (i j).normalSpaceFiberBundle hn (hdim j)
      letI : ∀ j, VectorBundle ℝ (P j) fun s ↦ (i j).isImmersion.NormalSpace s hn :=
        fun j ↦ (i j).normalSpaceVectorBundle hn (hdim j)
      letI : ∀ j, TopologicalSpace (TotalSpace (κ j → ℝ)
          fun s ↦ (h.isNondegenerateCriticalSubmanifold j).negativeNormalSpace hn
            (g j).toRiemannianMetric s) :=
        fun j ↦ subbundleTopology (P j)
          ((h.isNondegenerateCriticalSubmanifold j).negativeNormalSpace hn
            (g j).toRiemannianMetric)
      letI : ∀ j, FiberBundle (κ j → ℝ) fun s ↦
          (h.isNondegenerateCriticalSubmanifold j).negativeNormalSpace hn
            (g j).toRiemannianMetric s :=
        fun j ↦ (hV j).fiberBundle
      haveI : ∀ j, VectorBundle ℝ (κ j → ℝ) fun s ↦
          (h.isNondegenerateCriticalSubmanifold j).negativeNormalSpace hn
            (g j).toRiemannianMetric s :=
        fun j ↦ (hV j).vectorBundle
      ∀ j, (∀ s, f (i j s) ∈ Ioc (a q) (a q')) → Fintype.card (κ j) ≤ n →
        IsZero (twistedHomology (signLocalSystem (κ j → ℝ)
          (fun s ↦ (h.isNondegenerateCriticalSubmanifold j).negativeNormalSpace hn
            (g j).toRiemannianMetric s) K
          ((Fintype.card_fin _).trans (finrank_fintype_fun_eq_card ℝ).symm))
          (n - Fintype.card (κ j)))) :
    IsZero ((sublevelPair f (ha.monotone hqq')).singularHomology (ModuleCat.of K K) n) := by
  -- Add the critical bands `f⁻¹[a p, a (p + 1)]`, `q ≤ p < q'`, one at a time.
  refine Monotone.isZero_singularHomology_ofInclusion_of_forall_mem_Ico (Y := TopCat.of M)
    (X := fun q ↦ {x | f x ≤ a q}) ((sublevel_mono f).comp ha.monotone) (ModuleCat.of K K) hqq' n
    fun p hp ↦ ?_
  obtain ⟨hqp, hpq'⟩ := Finset.mem_Ico.1 hp
  obtain ⟨c, hc, hcrit⟩ := (ha.isCriticalBand p).exists_mem_Ioo_forall_eq
  -- The band homology is the sum of the twisted homologies of the pieces on its critical level,
  -- each of which vanishes.
  obtain ⟨e⟩ := h.nonempty_singularHomology_sublevelPair_iso_sigma_twistedHomology hn hc.1 hc.2
    (ha.isCriticalBand p).isCompact hcrit hdim g hV K n
  have : Finite {j // (∀ s, f (i j s) = c) ∧ Fintype.card (κ j) ≤ n} :=
    h.finite_subtype_of_forall_apply_eq (ha.isCriticalBand p).isCompact (Ioo_subset_Icc_self hc)
      fun _ ↦ And.left
  refine IsZero.of_iso ((IsZero.iff_id_eq_zero _).2 (Sigma.hom_ext _ _ fun j ↦ ?_)) e
  refine (hz j.val (fun s ↦ ?_) j.property.2).eq_of_src _ _
  rw [j.property.1 s]
  exact ⟨(ha.monotone hqp).trans_lt hc.1, hc.2.le.trans (ha.monotone (Int.add_one_le_iff.2 hpq'))⟩

/-- **Vanishing of the homology of a compact manifold over any ring.** Let the family
`i j : S j → M` exhibit `f` as a Morse–Bott function on a compact Hausdorff boundaryless manifold,
with pieces modelled on boundaryless models, let `g j` be smooth fibre metrics on the normal
bundles of the pieces, and let the negative normal spaces relative to `g j` have continuous local
frames indexed by a finite type `κ j`, so that they form the negative normal bundle `ν⁻ j` of rank
`|κ j|`, the index of the piece. Let `K` be a commutative ring, for instance `ℤ`. If
`H_{n - |κ j|}(S j; o(ν⁻ j) ⊗ K) = 0` for every piece of index `|κ j| ≤ n`, then `Hₙ(M; K) = 0`.
No orientation of the bundles `ν⁻ j` is assumed. -/
theorem isZero_singularHomology_of_forall_isZero_twistedHomology [CompactSpace M] (n : ℕ)
    (hz : letI : ∀ j, FiberBundle (P j) fun s ↦ (i j).isImmersion.NormalSpace s hn :=
        fun j ↦ (i j).normalSpaceFiberBundle hn (hdim j)
      letI : ∀ j, VectorBundle ℝ (P j) fun s ↦ (i j).isImmersion.NormalSpace s hn :=
        fun j ↦ (i j).normalSpaceVectorBundle hn (hdim j)
      letI : ∀ j, TopologicalSpace (TotalSpace (κ j → ℝ)
          fun s ↦ (h.isNondegenerateCriticalSubmanifold j).negativeNormalSpace hn
            (g j).toRiemannianMetric s) :=
        fun j ↦ subbundleTopology (P j)
          ((h.isNondegenerateCriticalSubmanifold j).negativeNormalSpace hn
            (g j).toRiemannianMetric)
      letI : ∀ j, FiberBundle (κ j → ℝ) fun s ↦
          (h.isNondegenerateCriticalSubmanifold j).negativeNormalSpace hn
            (g j).toRiemannianMetric s :=
        fun j ↦ (hV j).fiberBundle
      haveI : ∀ j, VectorBundle ℝ (κ j → ℝ) fun s ↦
          (h.isNondegenerateCriticalSubmanifold j).negativeNormalSpace hn
            (g j).toRiemannianMetric s :=
        fun j ↦ (hV j).vectorBundle
      ∀ j, Fintype.card (κ j) ≤ n →
        IsZero (twistedHomology (signLocalSystem (κ j → ℝ)
          (fun s ↦ (h.isNondegenerateCriticalSubmanifold j).negativeNormalSpace hn
            (g j).toRiemannianMetric s) K
          ((Fintype.card_fin _).trans (finrank_fintype_fun_eq_card ℝ).symm))
          (n - Fintype.card (κ j)))) :
    IsZero (((singularHomologyFunctor (ModuleCat.{u} K) n).obj (ModuleCat.of K K)).obj
      (TopCat.of M)) := by
  -- Cut the finitely many critical values of `f` by a critical-band cut running from below to
  -- above all values of `f`; then `M` is the relative sublevel pair `({f ≤ a q₁}, {f ≤ a q₀})`.
  obtain ⟨a, ha, ⟨q₀, hq₀⟩, q₁, hq₁⟩ := exists_isCriticalBandCut_of_finite_image_criticalPoints
    (I := I) h.contMDiff.continuous (h.finite_image_criticalPoints hn)
  have hq₁' (x : M) : f x ≤ a (max q₀ q₁) := (hq₁ x).trans (ha.monotone (le_max_right _ _))
  exact (h.isZero_singularHomology_sublevelPair_of_forall_isZero_twistedHomology hn hdim g hV K ha
    (le_max_left q₀ q₁) n fun j _ ↦ hz j).of_iso
    (singularHomologyIsoSublevelPair (ha.monotone (le_max_left _ _)) hq₀ hq₁' _ n)

end TauCeti.IsMorseBottFamily
