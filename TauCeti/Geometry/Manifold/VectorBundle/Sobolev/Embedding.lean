/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Wkp.Embedding
public import TauCeti.Analysis.Sobolev.Wkp.FiniteCover
public import TauCeti.Geometry.Manifold.VectorBundle.Sobolev.Transfer

/-!
# The Sobolev embedding for sections of a vector bundle

Let `M` be a smooth Hausdorff manifold without boundary modelled on a real inner product space `E`
of finite dimension `n`, let `V → M` be a smooth real vector bundle with finite-dimensional model
fibre `F`, and let `A` be a finite bundle atlas, so that `M` is compact. For `1 ≤ p` and the Sobolev
conjugate `p⋆` with `1/p⋆ + 1/n = 1/p` and `p⋆ < ∞`, that is `p < n`, the inclusion
`W^{k+1,p}(V) → W^{k,p⋆}(V)` of the Sobolev spaces `TauCeti.SobolevSection` is a continuous linear
map for every order `k` (`TauCeti.SobolevSection.sobolevEmbeddingL`). It keeps the section: the
chart data of the image are those of the input
(`TauCeti.SobolevSection.chartValueL_sobolevEmbeddingL_ae`).

At `p = 1` this is the endpoint embedding `W^{k+1,1}(V) → W^{k,n/(n-1)}(V)` for `n ≥ 2`. Iterating
gives `W^{k+r,p}(V) → W^{k,q}(V)` for `1/q + r/n = 1/p` with `q < ∞`, the integer Sobolev embeddings
below the critical exponent.

The local input is the interior Sobolev embedding
`TauCeti.Wkp.exists_sobolevEmbeddingL_of_isCompact_closure`, which needs a subdomain with compact
closure inside the chart image, as no boundary regularity of the chart images is available. As for
Rellich compactness (`TauCeti.SobolevSection.isCompactOperator_lowerOrderL`), the chart image
`A.image j` is covered by finitely many pieces `P i j` on which the chart-`j` data are transferred
from the chart-`i` data on a set `Q i` with compact closure in `A.image i`
(`TauCeti.FiniteBundleAtlas.exists_transfer_cover`, `TauCeti.FiniteBundleAtlas.transferL`). The
interior embedding on `Q i`, followed by the transfer at the exponent `p⋆`, gives the data on
`P i j` in `W^{k,p⋆}`. These pieces agree on overlaps, since all of them have the values of the
original chart-`j` data, so they glue to an element of `W^{k,p⋆}(A.image j)`
(`TauCeti.Wkp.exists_continuousLinearMap_value_ae_eq`).

## Main results

* `TauCeti.SobolevSection.sobolevEmbeddingL`: the Sobolev embedding
  `W^{k+1,p}(V) →L[ℝ] W^{k,p⋆}(V)`.
* `TauCeti.SobolevSection.value_sobolevEmbeddingL_ae`,
  `TauCeti.SobolevSection.chartValueL_sobolevEmbeddingL_ae`: it keeps the chart components and the
  chart data, hence the section; these determine it
  (`TauCeti.SobolevSection.sobolevEmbeddingL_eq_iff`).
* `TauCeti.SobolevSection.sobolevEmbeddingL_injective`: it is injective.
* `TauCeti.SobolevSection.lowerOrderL_sobolevEmbeddingL`: it commutes with forgetting the highest
  weak derivative.
* `TauCeti.SobolevSection.exists_sobolevEmbeddingL_of_inv_add_mul_inv_eq`: the iterated embedding
  `W^{k+r,p}(V) → W^{k,q}(V)` for `1/q + r/n = 1/p` and `q < ∞`.

## References

* T. Aubin, *Some Nonlinear Problems in Riemannian Geometry*, Springer (1998), Chapter 2.
* E. Hebey, *Nonlinear Analysis on Manifolds: Sobolev Spaces and Inequalities*, Courant Lecture
  Notes 5 (2000), Chapter 3.
* L. C. Evans, *Partial Differential Equations*, 2nd ed., §5.6.1, for the Euclidean input.
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

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ F]
  [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)] [VectorBundle ℝ F V]
  [ContMDiffVectorBundle ∞ F V 𝓘(ℝ, E)]

variable (μ : Measure E) [μ.IsAddHaarMeasure] {p pstar : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ pstar)]
  (k : ℕ)

namespace SobolevSection

variable {A μ k} in
/-- **The local pieces of the embedding.** On a piece `P` of the image of chart `j` whose
chart-`j` data are transferred from the chart-`i` data on `Q`, the transfer at the exponent `p⋆`
of the interior embedding `T` on `Q` of the chart-`i` components of a Sobolev section has the
values of its chart-`j` components. -/
private theorem value_transferL_ae_value (hp : p ≠ ⊤) (hpstar : pstar ≠ ⊤)
    {w : SobolevSection A μ p (k + 1)} {i j : Fin A.n} {P Q : Opens E}
    (hP : (P : Set E) ⊆ A.overlap i j) (hPc : IsCompact (closure (P : Set E)))
    (hPD : closure (P : Set E) ⊆ A.transferDomain i j) (hQ : Q ≤ A.image i)
    (hPQ : MapsTo ((A.chart j).symm ≫ₕ A.chart i) P Q)
    (T : Wkp μ (A.image i) p (k + 1) →L[ℝ] Wkp μ Q pstar k)
    (hT : ∀ u, (Wkp.value k (T u) : E → ℝ) =ᵐ[μ.restrict Q] Wkp.value (k + 1) u)
    (m : Fin (finrank ℝ F)) :
    (Wkp.value k (A.transferL μ pstar k hpstar i j hPc hPD hPQ
        (fun l ↦ T ((w : A.sectionChartData.SobolevData μ p (k + 1)) i l)) m) : E → ℝ)
      =ᵐ[μ.restrict P]
        Wkp.value (k + 1) ((w : A.sectionChartData.SobolevData μ p (k + 1)) j m) := by
  have hPj : P ≤ A.image j := SetLike.coe_subset_coe.1 (hP.trans (A.overlap_subset_image i j))
  have hres := A.restrictL_eq_transferL μ p (k + 1) hp w.2 hP hPc hPD hQ hPQ m
  refine (A.value_transferL_ae_congr hPc hPD hPQ hpstar hp _
    (fun l ↦ Wkp.restrictL hQ (k + 1) ((w : A.sectionChartData.SobolevData μ p (k + 1)) i l))
    (fun l ↦ (hT _).trans (Wkp.value_restrictL_ae hQ (k + 1) _).symm) m).trans ?_
  rw [← hres]
  exact Wkp.value_restrictL_ae hPj (k + 1) _

variable [T2Space M]

/-- **The Sobolev embedding for sections of a vector bundle**, as an existence statement: a
continuous linear map `W^{k+1,p}(V) → W^{k,p⋆}(V)` keeping all the chart components. -/
private theorem exists_sobolevEmbeddingL (hpstar : pstar ≠ ⊤)
    (hexp : pstar⁻¹ + (finrank ℝ E : ℝ≥0∞)⁻¹ = p⁻¹) :
    ∃ T : SobolevSection A μ p (k + 1) →L[ℝ] SobolevSection A μ pstar k,
      ∀ w i m, (Wkp.value k ((T w : A.sectionChartData.SobolevData μ pstar k) i m) : E → ℝ)
        =ᵐ[μ.restrict (A.image i)]
          Wkp.value (k + 1) ((w : A.sectionChartData.SobolevData μ p (k + 1)) i m) := by
  -- The source exponent is finite, since `1/p ≥ 1/n > 0`.
  have hp : p ≠ ⊤ := fun hp ↦ by
    rw [hp, ENNReal.inv_top, add_eq_zero] at hexp
    exact ENNReal.natCast_ne_top _ (ENNReal.inv_eq_zero.1 hexp.2)
  obtain ⟨P, Q, hP, hPc, hPD, hQc, hQ, hPQ, hcov⟩ := A.exists_transfer_cover
  have hPj (i j : Fin A.n) : P i j ≤ A.image j :=
    SetLike.coe_subset_coe.1 ((hP i j).trans (A.overlap_subset_image i j))
  -- The interior Sobolev embedding on `Q i`.
  choose I hI using fun i : Fin A.n ↦ Wkp.exists_sobolevEmbeddingL_of_isCompact_closure
    (mu := μ) (Omega := A.image i) (U := Q i) hpstar hexp (hQc i) (hQ i) k
  -- The chart-`j` component `m` on the piece `P i j`, transferred from chart `i`, has the values
  -- of the original component; gluing the pieces over the cover of `A.image j` gives the
  -- chart-`j` component `m` of the embedding.
  choose G hG using fun (j : Fin A.n) (m : Fin (finrank ℝ F)) ↦
    Wkp.exists_continuousLinearMap_value_ae_eq (fun i ↦ hPj i j) (hcov j)
      (fun i ↦ ((ContinuousLinearMap.proj m).comp
        (A.transferL μ pstar k hpstar i j (hPc i j) (hPD i j) (hPQ i j))).comp
        ((ContinuousLinearMap.piMap fun _ ↦ I i).comp ((ContinuousLinearMap.proj (R := ℝ)
          (φ := fun i : Fin A.sectionChartData.n ↦
            ∀ _ : Fin (finrank ℝ F), Wkp μ (A.sectionChartData.image i) p (k + 1)) i).comp
          (A.sectionChartData.sobolevSections μ p (k + 1)).subtypeL)))
      (fun w ↦ Wkp.value (k + 1) ((w : A.sectionChartData.SobolevData μ p (k + 1)) j m))
      fun i w ↦ value_transferL_ae_value hp hpstar (hP i j) (hPc i j) (hPD i j)
        (SetLike.coe_subset_coe.1 (subset_closure.trans (hQ i))) (hPQ i j) (I i) (hI i) m
  -- The glued components are the components of the same section.
  let D : SobolevSection A μ p (k + 1) →L[ℝ] A.sectionChartData.SobolevData μ pstar k :=
    ContinuousLinearMap.pi fun j ↦ ContinuousLinearMap.pi fun m ↦ G j m
  -- The components of `D w` have the values of those of `w`: this is `hG`, as the chart indices
  -- and images of `A.sectionChartData` are those of `A` by definition.
  have hD (w : SobolevSection A μ p (k + 1)) (j : Fin A.n) (m : Fin (finrank ℝ F)) :
      (Wkp.value k (D w j m) : E → ℝ) =ᵐ[μ.restrict (A.image j)]
        Wkp.value (k + 1) ((w : A.sectionChartData.SobolevData μ p (k + 1)) j m) :=
    hG j m w
  refine ⟨D.codRestrict _ fun w ↦ ?_, fun w i m ↦ by
    rw [ContinuousLinearMap.coe_codRestrict_apply]
    exact hD w i m⟩
  obtain ⟨s, hs⟩ := A.sectionChartData.exists_section μ p (k + 1) w
  refine (A.sectionChartData.mem_sobolevSections_iff μ pstar k).2 ⟨s, fun i ↦ ?_⟩
  filter_upwards [A.sectionChartData.chartValueL_apply_ae μ pstar k i (D w),
    A.sectionChartData.chartValueL_apply_ae μ p (k + 1) i w,
    ae_all_iff.2 fun m ↦ hD w i m, hs i] with y h₁ h₂ h₃ h₄
  rw [h₁, ← h₄, h₂]
  exact Finset.sum_congr rfl fun m _ ↦ by rw [h₃ m]

/-- **The Sobolev embedding for sections of a vector bundle.** On a compact manifold without
boundary, given by a finite bundle atlas of a Hausdorff manifold of dimension `n`, if `1 ≤ p` and
`1/p⋆ + 1/n = 1/p` with `p⋆ < ∞`, the inclusion `W^{k+1,p}(V) → W^{k,p⋆}(V)` as a continuous
linear map, for every order `k`. It keeps the chart components
(`TauCeti.SobolevSection.value_sobolevEmbeddingL_ae`), hence the section
(`TauCeti.SobolevSection.chartValueL_sobolevEmbeddingL_ae`). At `p = 1` it is the endpoint
embedding `W^{k+1,1}(V) → W^{k,n/(n-1)}(V)`. -/
def sobolevEmbeddingL (hpstar : pstar ≠ ⊤) (hexp : pstar⁻¹ + (finrank ℝ E : ℝ≥0∞)⁻¹ = p⁻¹) :
    SobolevSection A μ p (k + 1) →L[ℝ] SobolevSection A μ pstar k :=
  (exists_sobolevEmbeddingL A μ k hpstar hexp).choose

variable {A μ k}

/-- The Sobolev embedding keeps the chart components of a Sobolev section. -/
theorem value_sobolevEmbeddingL_ae (hpstar : pstar ≠ ⊤)
    (hexp : pstar⁻¹ + (finrank ℝ E : ℝ≥0∞)⁻¹ = p⁻¹) (w : SobolevSection A μ p (k + 1))
    (i : Fin A.n) (m : Fin (finrank ℝ F)) :
    (Wkp.value k ((sobolevEmbeddingL A μ k hpstar hexp w :
        A.sectionChartData.SobolevData μ pstar k) i m) : E → ℝ) =ᵐ[μ.restrict (A.image i)]
      Wkp.value (k + 1) ((w : A.sectionChartData.SobolevData μ p (k + 1)) i m) :=
  (exists_sobolevEmbeddingL A μ k hpstar hexp).choose_spec w i m

/-- The Sobolev embedding keeps the chart data of a Sobolev section, hence the section whose
coordinates they are. -/
theorem chartValueL_sobolevEmbeddingL_ae (hpstar : pstar ≠ ⊤)
    (hexp : pstar⁻¹ + (finrank ℝ E : ℝ≥0∞)⁻¹ = p⁻¹) (w : SobolevSection A μ p (k + 1))
    (i : Fin A.n) :
    A.sectionChartData.chartValueL μ pstar k i (sobolevEmbeddingL A μ k hpstar hexp w)
      =ᵐ[μ.restrict (A.image i)] A.sectionChartData.chartValueL μ p (k + 1) i w := by
  filter_upwards [A.sectionChartData.chartValueL_apply_ae μ pstar k i
      (sobolevEmbeddingL A μ k hpstar hexp w),
    A.sectionChartData.chartValueL_apply_ae μ p (k + 1) i w,
    ae_all_iff.2 fun m ↦ value_sobolevEmbeddingL_ae hpstar hexp w i m] with y h₁ h₂ h₃
  rw [h₁, h₂]
  exact Finset.sum_congr rfl fun m _ ↦ by rw [h₃ m]

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
    Function.Injective (sobolevEmbeddingL A μ k (pstar := pstar) hpstar hexp) := fun w w' h ↦
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

/-- **Iterated Sobolev embedding for sections of a vector bundle.** On a compact manifold without
boundary of dimension `n`, if `1 ≤ p` and `1/q + r/n = 1/p` with `q < ∞`, that is `r p < n`, there
is a continuous linear map `W^{k+r,p}(V) → W^{k,q}(V)` keeping all the chart components of a Sobolev
section, for every order `k`. It is the composite of `r` first-order embeddings
`TauCeti.SobolevSection.sobolevEmbeddingL`. Lowering the exponent of the target
(`TauCeti.SectionChartData.ofExponentLEL`) then gives `W^{k+r,p}(V) → W^{k,s}(V)` for every
`1 ≤ s ≤ q`. -/
theorem exists_sobolevEmbeddingL_of_inv_add_mul_inv_eq (r : ℕ) {q : ℝ≥0∞} [Fact (1 ≤ q)]
    (hq : q ≠ ⊤) (hexp : q⁻¹ + r * (finrank ℝ E : ℝ≥0∞)⁻¹ = p⁻¹) :
    ∃ T : SobolevSection A μ p (k + r) →L[ℝ] SobolevSection A μ q k,
      ∀ w i m, (Wkp.value k ((T w : A.sectionChartData.SobolevData μ q k) i m) : E → ℝ)
        =ᵐ[μ.restrict (A.image i)]
          Wkp.value (k + r) ((w : A.sectionChartData.SobolevData μ p (k + r)) i m) := by
  induction r generalizing p with
  | zero =>
    obtain rfl : q = p := by simpa using hexp
    exact ⟨ContinuousLinearMap.id ℝ _, fun _ _ _ ↦ ae_eq_refl _⟩
  | succ r ih =>
    -- The intermediate exponent `p₁` with `1/p₁ = 1/q + r/n` and `1/p₁ + 1/n = 1/p`.
    set p₁ : ℝ≥0∞ := (q⁻¹ + r * (finrank ℝ E : ℝ≥0∞)⁻¹)⁻¹
    have hp₁ : p₁⁻¹ = q⁻¹ + r * (finrank ℝ E : ℝ≥0∞)⁻¹ := inv_inv _
    have hexp₁ : p₁⁻¹ + (finrank ℝ E : ℝ≥0∞)⁻¹ = p⁻¹ := by
      rw [hp₁, ← hexp, Nat.cast_succ, add_mul, one_mul, add_assoc]
    have hp₁top : p₁ ≠ ⊤ := by
      rw [← ENNReal.inv_ne_zero, hp₁]
      exact fun h ↦ ENNReal.inv_ne_zero.2 hq (add_eq_zero.1 h).1
    have : Fact (1 ≤ p₁) := ⟨(Fact.out : 1 ≤ p).trans
      (ENNReal.inv_le_inv.1 (hexp₁ ▸ le_add_right le_rfl))⟩
    obtain ⟨T, hT⟩ := ih (p := p₁) hp₁.symm
    refine ⟨T.comp (sobolevEmbeddingL A μ (k + r) hp₁top hexp₁), fun w i m ↦ ?_⟩
    exact (hT _ i m).trans (value_sobolevEmbeddingL_ae hp₁top hexp₁ w i m)

end SobolevSection

end Sobolev

end TauCeti
