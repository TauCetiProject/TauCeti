/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Wkp.Embedding
public import TauCeti.Analysis.Sobolev.Wkp.FiniteCover
public import TauCeti.Geometry.Manifold.VectorBundle.Sobolev.Exponent
public import TauCeti.Geometry.Manifold.VectorBundle.Sobolev.Transfer

/-!
# The Sobolev embedding for Sobolev sections of a vector bundle

Let `M` be a smooth Hausdorff manifold without boundary modelled on a real inner product space `E`
of finite dimension `n`, let `V → M` be a smooth real vector bundle with finite-dimensional model
fibre `F`, and let `A` be a finite bundle atlas, so that `M` is compact. For `1 ≤ p` and the
Sobolev conjugate exponent `p⋆`, `1/p⋆ = 1/p - 1/n`, with `p⋆ < ∞` (that is, `p < n`), the
Sobolev space `W^{k+1,p}(V)` of `TauCeti.SobolevSection` embeds continuously into `W^{k,p⋆}(V)`
for every order `k`, and the embedding keeps the underlying section
(`TauCeti.SobolevSection.exists_sobolevEmbeddingL`). Iterating, `W^{k+r,p}(V)` embeds into
`W^{k,q}(V)` for `1/q = 1/p - r/n`, `q < ∞`
(`TauCeti.SobolevSection.exists_sobolevEmbeddingL_of_inv_add_eq`), and into `W^{k,q'}(V)` for
`1 ≤ q' ≤ q` (`TauCeti.SobolevSection.exists_sobolevEmbeddingL_of_inv_add_eq_of_le`).
In particular `W^{1,1}(V) ⊆ L^{n/(n-1)}(V)` for `n ≥ 2`.

The local input is the interior embedding `W^{k+1,p}(Ω) → W^{k,p⋆}(Q)` for `Q` with compact closure
inside `Ω` (`TauCeti.Wkp.exists_sobolevEmbeddingL_of_isCompact_closure`). As for Rellich's theorem
(`TauCeti.SobolevSection.isCompactOperator_lowerOrderL`), it does not apply to the chart images
`A.image j` themselves, whose boundaries are not controlled. The chart image `A.image j` is covered
by finitely many pieces `P i j` (`TauCeti.FiniteBundleAtlas.exists_transfer_cover`), on which the
chart-`j` data are transferred (`TauCeti.FiniteBundleAtlas.transferL`) from the chart-`i` data
on a set `Q i` with compact closure inside `A.image i`. Transferring the interior embeddings of the
chart-`i` data gives, on each piece, an element of `W^{k,p⋆}(P i j)` with the values of the
chart-`j` data. These glue over the finite cover
(`TauCeti.Wkp.exists_continuousLinearMap_value_ae_eq`) to an element of `W^{k,p⋆}(A.image j)`, and
the resulting tuples are again the components of the same section
(`TauCeti.SectionChartData.exists_continuousLinearMap_chartValueL_ae_eq`).

## Main results

* `TauCeti.SobolevSection.exists_sobolevEmbeddingL`: **the Sobolev embedding**
  `W^{k+1,p}(V) → W^{k,p⋆}(V)` for Sobolev sections.
* `TauCeti.SobolevSection.exists_sobolevEmbeddingL_of_inv_add_eq`: its iterate
  `W^{k+r,p}(V) → W^{k,q}(V)` for `1/q + r/n = 1/p`, `q < ∞`.
* `TauCeti.SobolevSection.exists_sobolevEmbeddingL_of_inv_add_eq_of_le`: the embeddings
  `W^{k+r,p}(V) → W^{k,q'}(V)` for `1 ≤ q' ≤ q`; for `p = 1` these are `1 ≤ q' ≤ n/(n-r)`.
* `TauCeti.SobolevSection.sobolevEmbeddingL`: the Sobolev embedding as a chosen continuous linear
  map `W^{k+1,p}(V) →L[ℝ] W^{k,p⋆}(V)`.
* `TauCeti.SobolevSection.value_sobolevEmbeddingL_ae`,
  `TauCeti.SobolevSection.chartValueL_sobolevEmbeddingL_ae`: it keeps the chart components and the
  chart data, hence the section; these determine it
  (`TauCeti.SobolevSection.sobolevEmbeddingL_eq_iff`).
* `TauCeti.SobolevSection.sobolevEmbeddingL_injective`: it is injective.
* `TauCeti.SobolevSection.lowerOrderL_sobolevEmbeddingL`: it commutes with forgetting the highest
  weak derivative.

## References

* R. A. Adams and J. J. F. Fournier, *Sobolev Spaces*, 2nd ed., Academic Press (2003),
  Theorem 4.12, Part I, Case B.
* T. Aubin, *Some Nonlinear Problems in Riemannian Geometry*, Springer (1998), Theorem 2.21
  (the Sobolev embedding on compact manifolds).
-/

public section

noncomputable section

open Bundle Filter MeasureTheory Module Set TopologicalSpace
open scoped Manifold ContDiff ENNReal Topology

universe u

namespace TauCeti

section Sobolev

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {M : Type*}
  [TopologicalSpace M] [ChartedSpace E M] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)] [∀ x, TopologicalSpace (V x)]
  [FiberBundle F V] (A : FiniteBundleAtlas E M F V)

variable [IsManifold 𝓘(ℝ, E) ∞ M]

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)] [VectorBundle ℝ F V]

variable (μ : Measure E) [μ.IsAddHaarMeasure]

variable [FiniteDimensional ℝ F] [ContMDiffVectorBundle ∞ F V 𝓘(ℝ, E)] {p : ℝ≥0∞} [Fact (1 ≤ p)]

namespace SobolevSection

/-- **The Sobolev embedding for Sobolev sections.** Let `M` be a compact manifold without boundary,
given by a finite bundle atlas of a Hausdorff manifold, of dimension `n`, let `1 ≤ p` and let
`1/p⋆ + 1/n = 1/p` with `p⋆ < ∞`. Then for every order `k` there is a continuous linear map
`W^{k+1,p}(V) → W^{k,p⋆}(V)` keeping the underlying section: its chart data are those of the
original Sobolev section. -/
theorem exists_sobolevEmbeddingL [T2Space M] {pstar : ℝ≥0∞} (hpstar : pstar ≠ ⊤)
    (hexp : pstar⁻¹ + (finrank ℝ E : ℝ≥0∞)⁻¹ = p⁻¹) (k : ℕ) :
    letI := Fact.mk (one_le_of_inv_add_eq_inv hexp)
    ∃ T : SobolevSection A μ p (k + 1) →L[ℝ] SobolevSection A μ pstar k,
      ∀ w i, A.sectionChartData.chartValueL μ pstar k i (T w) =ᵐ[μ.restrict (A.image i)]
        A.sectionChartData.chartValueL μ p (k + 1) i w := by
  let _ := Fact.mk (one_le_of_inv_add_eq_inv hexp)
  obtain ⟨P, Q, hP, hPc, hPD, hQc, hQ, hPQ, hcov⟩ := A.exists_transfer_cover
  have hPj (i j : Fin A.n) : P i j ≤ A.image j :=
    SetLike.coe_subset_coe.1 ((hP i j).trans (A.overlap_subset_image i j))
  have hQi (i : Fin A.n) : Q i ≤ A.image i :=
    SetLike.coe_subset_coe.1 (subset_closure.trans (hQ i))
  -- The chart-`i` components of a section, embedded on `Q i`.
  choose Emb hEmb using fun i ↦ Wkp.exists_sobolevEmbeddingL_of_isCompact_closure (mu := μ)
    hpstar hexp (hQc i) (hQ i) k
  let D (i : Fin A.n) :
      SobolevSection A μ p (k + 1) →L[ℝ] (Fin (finrank ℝ F) → Wkp μ (Q i) pstar k) :=
    ContinuousLinearMap.pi fun l ↦ (Emb i).comp ((ContinuousLinearMap.proj l).comp
      ((ContinuousLinearMap.proj (R := ℝ) (φ := fun i : Fin A.sectionChartData.n ↦
          ∀ _ : Fin (finrank ℝ F), Wkp μ (A.sectionChartData.image i) p (k + 1)) i).comp
        (A.sectionChartData.sobolevSections μ p (k + 1)).subtypeL))
  -- The inclusion followed by the two projections evaluates `w` at `i` and `l`. This holds by
  -- definition only, unfolding `pi`, `proj`, `comp` and `subtypeL`, as the index type
  -- `Fin A.sectionChartData.n` of the projection unfolds to `Fin A.n`.
  have hD (w : SobolevSection A μ p (k + 1)) (i : Fin A.n) (l : Fin (finrank ℝ F)) :
      D i w l = Emb i ((w : A.sectionChartData.SobolevData μ p (k + 1)) i l) :=
    (rfl)
  -- On the piece `P i j`, the transfer of the embedded chart-`i` components.
  let f (j : Fin A.n) (m : Fin (finrank ℝ F)) (i : Fin A.n) :
      SobolevSection A μ p (k + 1) →L[ℝ] Wkp μ (P i j) pstar k :=
    (ContinuousLinearMap.proj m).comp
      ((A.transferL μ pstar k i j (hPc i j) (hPD i j) (hPQ i j)).comp (D i))
  have hf (j : Fin A.n) (m : Fin (finrank ℝ F)) (i : Fin A.n) (w : SobolevSection A μ p (k + 1)) :
      (Wkp.value k (f j m i w) : E → ℝ) =ᵐ[μ.restrict (P i j)]
        Wkp.value (k + 1) ((w : A.sectionChartData.SobolevData μ p (k + 1)) j m) := by
    set u := (w : A.sectionChartData.SobolevData μ p (k + 1))
    -- The transfer only sees the values of the embedded chart-`i` components, which are those of
    -- the chart-`i` components themselves; by `restrictL_eq_transferL` these transfer to the
    -- chart-`j` components.
    refine (A.value_transferL_ae_congr (hPc i j) (hPD i j) (hPQ i j) (D i w)
      (fun l ↦ Wkp.restrictL (hQi i) (k + 1) (u i l))
      (fun l ↦ by
        rw [hD]
        exact (hEmb i (u i l)).trans (Wkp.value_restrictL_ae (hQi i) (k + 1) (u i l)).symm)
      m).trans ?_
    rw [← A.restrictL_eq_transferL μ p (k + 1) w.property (hP i j) (hPc i j) (hPD i j) (hQi i)
      (hPQ i j) m]
    exact Wkp.value_restrictL_ae (hPj i j) (k + 1) (u j m)
  choose Φ hΦ using fun j m ↦ Wkp.exists_continuousLinearMap_value_ae_eq (fun i ↦ hPj i j)
    (hcov j) (f j m) _ (hf j m)
  exact A.sectionChartData.exists_continuousLinearMap_chartValueL_ae_eq Φ hΦ

/-- **Iterated Sobolev embedding for Sobolev sections.** On a compact manifold without boundary of
dimension `n`, given by a finite bundle atlas of a Hausdorff manifold, let `1 ≤ p` and
`1/q + r/n = 1/p` with `q < ∞`. Then for every order `k` there is a continuous linear map
`W^{k+r,p}(V) → W^{k,q}(V)` keeping the underlying section. For `p = 1`, `r = 1` and `k = 0`
this is `W^{1,1}(V) ⊆ L^{n/(n-1)}(V)`, `n ≥ 2`. -/
theorem exists_sobolevEmbeddingL_of_inv_add_eq [T2Space M] (k : ℕ) :
    ∀ (r : ℕ) {p q : ℝ≥0∞} [Fact (1 ≤ p)] (_ : q ≠ ⊤)
      (hexp : q⁻¹ + r * (finrank ℝ E : ℝ≥0∞)⁻¹ = p⁻¹),
      letI := Fact.mk (one_le_of_inv_add_eq_inv hexp)
      ∃ T : SobolevSection A μ p (k + r) →L[ℝ] SobolevSection A μ q k,
        ∀ w i, A.sectionChartData.chartValueL μ q k i (T w) =ᵐ[μ.restrict (A.image i)]
          A.sectionChartData.chartValueL μ p (k + r) i w
  | 0, p, q, _, _, hexp => by
    obtain rfl : q = p := by simpa using hexp
    exact ⟨ContinuousLinearMap.id ℝ _, fun w i ↦ .rfl⟩
  | r + 1, p, q, _, hq, hexp => by
    -- First lose one derivative from `p` to the intermediate exponent `s`, then `r` more.
    obtain ⟨s, hs, hsinv⟩ := exists_inv_eq_inv_add_of_ne_top hq (r * (finrank ℝ E : ℝ≥0∞)⁻¹)
    have hsexp : s⁻¹ + (finrank ℝ E : ℝ≥0∞)⁻¹ = p⁻¹ := by
      rw [hsinv, ← hexp]
      push_cast
      ring
    have : Fact (1 ≤ s) := ⟨one_le_of_inv_add_eq_inv hsexp⟩
    obtain ⟨T₁, hT₁⟩ := exists_sobolevEmbeddingL A μ hs hsexp (k + r)
    obtain ⟨T₂, hT₂⟩ := exists_sobolevEmbeddingL_of_inv_add_eq k r hq hsinv.symm
    exact ⟨T₂.comp T₁, fun w i ↦ (hT₂ (T₁ w) i).trans (hT₁ w i)⟩

/-- **Sobolev embeddings below the critical exponent.** On a compact manifold without boundary of
dimension `n`, given by a finite bundle atlas of a Hausdorff manifold, let `1 ≤ p`, let
`1/q + r/n = 1/p` with `q < ∞`, and let `1 ≤ q' ≤ q`. Then for every order `k` there is a
continuous linear map `W^{k+r,p}(V) → W^{k,q'}(V)` keeping the underlying section. For `p = 1` this
is `W^{k+r,1}(V) ⊆ W^{k,q'}(V)` for `1 ≤ q' ≤ n/(n-r)`, `r < n`. -/
theorem exists_sobolevEmbeddingL_of_inv_add_eq_of_le [T2Space M] (k r : ℕ) {q q' : ℝ≥0∞}
    [Fact (1 ≤ q')] (hq : q ≠ ⊤) (hexp : q⁻¹ + r * (finrank ℝ E : ℝ≥0∞)⁻¹ = p⁻¹)
    (hq' : q' ≤ q) :
    ∃ T : SobolevSection A μ p (k + r) →L[ℝ] SobolevSection A μ q' k,
      ∀ w i, A.sectionChartData.chartValueL μ q' k i (T w) =ᵐ[μ.restrict (A.image i)]
        A.sectionChartData.chartValueL μ p (k + r) i w := by
  let _ := Fact.mk (one_le_of_inv_add_eq_inv hexp)
  obtain ⟨T, hT⟩ := exists_sobolevEmbeddingL_of_inv_add_eq A μ k r hq hexp
  refine ⟨(A.sectionChartData.ofExponentLEL μ k hq').comp T, fun w i ↦ ?_⟩
  rw [ContinuousLinearMap.comp_apply, SectionChartData.chartValueL_ofExponentLEL,
    Lp.coeFn_ofExponentLEL]
  exact hT w i

variable [T2Space M] {pstar : ℝ≥0∞} [Fact (1 ≤ pstar)]

/-- **The Sobolev embedding for Sobolev sections**, as a continuous linear map. On a compact
manifold without boundary, given by a finite bundle atlas of a Hausdorff manifold of dimension `n`,
if `1 ≤ p` and `1/p⋆ + 1/n = 1/p` with `p⋆ < ∞`, this is the inclusion
`W^{k+1,p}(V) → W^{k,p⋆}(V)`, chosen by `TauCeti.SobolevSection.exists_sobolevEmbeddingL`. It keeps
the chart data (`TauCeti.SobolevSection.chartValueL_sobolevEmbeddingL_ae`), hence the section, and
the chart components (`TauCeti.SobolevSection.value_sobolevEmbeddingL_ae`). At `p = 1` it is the
endpoint embedding `W^{k+1,1}(V) → W^{k,n/(n-1)}(V)`. -/
def sobolevEmbeddingL (k : ℕ) (hpstar : pstar ≠ ⊤)
    (hexp : pstar⁻¹ + (finrank ℝ E : ℝ≥0∞)⁻¹ = p⁻¹) :
    SobolevSection A μ p (k + 1) →L[ℝ] SobolevSection A μ pstar k :=
  (exists_sobolevEmbeddingL A μ hpstar hexp k).choose

variable {A μ} {k : ℕ}

/-- The Sobolev embedding keeps the chart data of a Sobolev section, hence the section whose
coordinates they are. -/
theorem chartValueL_sobolevEmbeddingL_ae (hpstar : pstar ≠ ⊤)
    (hexp : pstar⁻¹ + (finrank ℝ E : ℝ≥0∞)⁻¹ = p⁻¹) (w : SobolevSection A μ p (k + 1))
    (i : Fin A.n) :
    A.sectionChartData.chartValueL μ pstar k i (sobolevEmbeddingL A μ k hpstar hexp w)
      =ᵐ[μ.restrict (A.image i)] A.sectionChartData.chartValueL μ p (k + 1) i w :=
  (exists_sobolevEmbeddingL A μ hpstar hexp k).choose_spec w i

/-- The Sobolev embedding keeps the chart components of a Sobolev section. -/
theorem value_sobolevEmbeddingL_ae (hpstar : pstar ≠ ⊤)
    (hexp : pstar⁻¹ + (finrank ℝ E : ℝ≥0∞)⁻¹ = p⁻¹) (w : SobolevSection A μ p (k + 1))
    (i : Fin A.n) (m : Fin (finrank ℝ F)) :
    (Wkp.value k ((sobolevEmbeddingL A μ k hpstar hexp w :
        A.sectionChartData.SobolevData μ pstar k) i m) : E → ℝ) =ᵐ[μ.restrict (A.image i)]
      Wkp.value (k + 1) ((w : A.sectionChartData.SobolevData μ p (k + 1)) i m) := by
  -- Both are the `m`th coordinate of the reading in chart `i` of the section underlying `w`.
  obtain ⟨s, hs⟩ := A.sectionChartData.exists_section μ p (k + 1) w
  exact (SectionChartData.value_ae_eq_repr_coord
    ((chartValueL_sobolevEmbeddingL_ae hpstar hexp w i).trans (hs i)) m).trans
      (SectionChartData.value_ae_eq_repr_coord (hs i) m).symm

/-- **Characterization of the Sobolev embedding.** An element of `W^{k,p⋆}(V)` is the image of
`w ∈ W^{k+1,p}(V)` exactly when its chart components have the values of those of `w`. -/
theorem sobolevEmbeddingL_eq_iff (hpstar : pstar ≠ ⊤)
    (hexp : pstar⁻¹ + (finrank ℝ E : ℝ≥0∞)⁻¹ = p⁻¹) (w : SobolevSection A μ p (k + 1))
    (v : SobolevSection A μ pstar k) :
    sobolevEmbeddingL A μ k hpstar hexp w = v ↔ ∀ i m,
      (Wkp.value k ((v : A.sectionChartData.SobolevData μ pstar k) i m) : E → ℝ)
        =ᵐ[μ.restrict (A.image i)]
          Wkp.value (k + 1) ((w : A.sectionChartData.SobolevData μ p (k + 1)) i m) := by
  refine ⟨fun h i m ↦ h ▸ value_sobolevEmbeddingL_ae hpstar hexp w i m, fun h ↦ ?_⟩
  exact A.sectionChartData.sobolevSections_ext μ pstar k fun i m ↦ Lp.ext <|
    (value_sobolevEmbeddingL_ae hpstar hexp w i m).trans (h i m).symm

/-- The Sobolev embedding is injective. -/
theorem sobolevEmbeddingL_injective (hpstar : pstar ≠ ⊤)
    (hexp : pstar⁻¹ + (finrank ℝ E : ℝ≥0∞)⁻¹ = p⁻¹) :
    Function.Injective (sobolevEmbeddingL A μ k hpstar hexp) := fun w w' h ↦
  A.sectionChartData.sobolevSections_ext μ p (k + 1) fun i m ↦ Lp.ext <|
    (value_sobolevEmbeddingL_ae hpstar hexp w i m).symm.trans <| by
      rw [h]
      exact value_sobolevEmbeddingL_ae hpstar hexp w' i m

/-- The Sobolev embedding commutes with forgetting the highest weak derivative. -/
theorem lowerOrderL_sobolevEmbeddingL (hpstar : pstar ≠ ⊤)
    (hexp : pstar⁻¹ + (finrank ℝ E : ℝ≥0∞)⁻¹ = p⁻¹) (w : SobolevSection A μ p (k + 2)) :
    A.sectionChartData.lowerOrderL μ pstar k (sobolevEmbeddingL A μ (k + 1) hpstar hexp w) =
      sobolevEmbeddingL A μ k hpstar hexp (A.sectionChartData.lowerOrderL μ p (k + 1) w) := by
  refine ((sobolevEmbeddingL_eq_iff hpstar hexp _ _).2 fun i m ↦ ?_).symm
  rw [SectionChartData.lowerOrderL_apply, SectionChartData.lowerOrderL_apply, ← Wkp.value_succ,
    ← Wkp.value_succ]
  exact value_sobolevEmbeddingL_ae hpstar hexp w i m

end SobolevSection

end Sobolev

end TauCeti
