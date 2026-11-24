/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.ContinuousMap.ZeroAtInfty
public import TauCeti.Geometry.Manifold.VectorBundle.FiniteBundleAtlas.AEEq
public import TauCeti.Geometry.Manifold.VectorBundle.Sobolev.Basic
import TauCeti.Analysis.Sobolev.Wkp.ContDiffRepresentative
import TauCeti.Analysis.Sobolev.Wkp.CriticalEmbedding

/-!
# The critical Sobolev embedding for Sobolev sections of a vector bundle

Let `M` be a manifold without boundary modelled on a real inner product space `E` of finite
dimension `n`, let `V → M` be a real vector bundle with finite-dimensional model fibre `F`, and let
`A` be a finite bundle atlas. This file proves the critical case `p = 1` of the embedding of the
Sobolev sections `W^{k,p}(V)` (`TauCeti.SobolevSection`) into continuous sections: for `k ≥ n`
every element `w` of `W^{k,1}(V)` has a unique continuous representative, a continuous section of
`V` whose chart expressions agree almost everywhere with the chart data of `w`
(`TauCeti.SobolevSection.existsUnique_continuous_ae_eq_coord_of_finrank_le`). For
`w ∈ W^{n+j,1}(V)` the chart expressions of this representative are moreover `Cʲ` on the chart
images (`TauCeti.SobolevSection.exists_continuous_contDiffOn_coord_ae_eq_of_finrank_le`).

Both statements are instances of general ones for any finite exponent `p`: if every element of the
whole-space space `W^{k,p}(E)` has a continuous representative vanishing at infinity, then every
element of `W^{k+j,p}(V)` has a continuous representative with `Cʲ` chart expressions
(`TauCeti.SobolevSection.exists_continuous_contDiffOn_coord_ae_eq_of_forall_zeroAtInfty`), and it is
unique (`TauCeti.SobolevSection.existsUnique_continuous_ae_eq_coord_of_forall_zeroAtInfty`). The
critical case uses the whole-space embedding `TauCeti.Wkp.toZeroAtInftyOne` (`p = 1`, `k ≥ n`).

The proof is local in each chart. The chart-`i` data of `w` are scalar Sobolev functions in
`W^{k+j,p}(A.image i)`, which have representatives that are `Cʲ` on the open chart image by the
interior localization principle (`TauCeti.Wkp.exists_contDiffOn_ae_eq_of_forall_zeroAtInfty`).
Since chart transitions preserve null sets, these representatives satisfy the cocycle relation of
the chart expressions of a section almost everywhere, hence everywhere, and they glue to a
continuous section (`TauCeti.FiniteBundleAtlas.exists_continuous_coord_eqOn_of_ae_eq`). Uniqueness
holds because two continuous sections whose chart expressions agree almost everywhere are equal
(`TauCeti.FiniteBundleAtlas.eq_of_continuous_of_coord_ae_eq`).

## Main results

* `TauCeti.SobolevSection.exists_continuous_contDiffOn_coord_ae_eq_of_forall_zeroAtInfty`,
  `TauCeti.SobolevSection.existsUnique_continuous_ae_eq_coord_of_forall_zeroAtInfty`: the general
  statements for a finite exponent `p` under a whole-space embedding hypothesis.
* `TauCeti.SobolevSection.exists_continuous_contDiffOn_coord_ae_eq_of_finrank_le`: for `k ≥ n`,
  an element of `W^{k+j,1}(V)` is represented by a continuous section whose chart expressions are
  `Cʲ`.
* `TauCeti.SobolevSection.existsUnique_continuous_ae_eq_coord_of_finrank_le`: for `k ≥ n`, an
  element of `W^{k,1}(V)` has exactly one continuous representative.

## References

* R. A. Adams, J. J. F. Fournier, *Sobolev Spaces*, 2nd ed., Academic Press (2003),
  Theorem 4.12, Part I, Case A, for `p = 1` and `m = n`.
* T. Aubin, *Some Nonlinear Problems in Riemannian Geometry*, Springer (1998), Theorem 2.21
  (the Sobolev embeddings on compact manifolds).
-/

public section

open Bundle MeasureTheory Module Set
open scoped Manifold ContDiff ENNReal ZeroAtInfty

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) 1 M] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F] {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)] [∀ x, TopologicalSpace (V x)] [FiberBundle F V]
  [VectorBundle ℝ F V] {A : FiniteBundleAtlas E M F V} {k : ℕ}

namespace SobolevSection

/-- **Sobolev sections with `Cʲ` representatives from a whole-space embedding.** Let `p < ∞`. If
every element of the whole-space space `W^{k,p}(E)` agrees almost everywhere with a continuous
function vanishing at infinity, then every element `w` of `W^{k+j,p}(V)` is
represented by a continuous section `s` of `V` whose chart expression `A.coord i s` is `Cʲ` on the
chart image `A.image i` and agrees almost everywhere there with the chart-`i` data of `w`, for every
chart `i`. -/
theorem exists_continuous_contDiffOn_coord_ae_eq_of_forall_zeroAtInfty {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤)
    (h : ∀ w : Wkp (volume : Measure E) ⊤ p k, ∃ g : C₀(E, ℝ), Wkp.value k w =ᵐ[volume] g)
    (j : ℕ) (w : SobolevSection A volume p (k + j)) :
    ∃ s : ∀ x, V x, Continuous (fun x ↦ TotalSpace.mk' F x (s x)) ∧
      ∀ i, ContDiffOn ℝ j (A.coord i s) (A.image i) ∧
        A.sectionChartData.chartValueL volume p (k + j) i w
          =ᵐ[volume.restrict (A.image i)] A.coord i s := by
  obtain ⟨s, hs⟩ := A.sectionChartData.exists_section volume p (k + j) w
  -- The chart-`i` components of `w` have representatives that are `Cʲ` on `A.image i`.
  choose G hG hGae using fun (i : Fin A.n) (l : Fin (finrank ℝ F)) ↦
    Wkp.exists_contDiffOn_ae_eq_of_forall_zeroAtInfty (Omega := A.image i) hp h j
      ((w : A.sectionChartData.SobolevData volume p (k + j)) i l)
  let g (i : Fin A.n) (y : E) : F := ∑ l, G i l y • finBasis ℝ F l
  have hg (i : Fin A.n) : ContDiffOn ℝ j (g i) (A.image i) :=
    ContDiffOn.sum fun l _ ↦ (hG i l).smul contDiffOn_const
  have hwg (i : Fin A.n) : A.sectionChartData.chartValueL volume p (k + j) i w
      =ᵐ[volume.restrict (A.image i)] g i := by
    filter_upwards [A.sectionChartData.chartValueL_apply_ae volume p (k + j) i w,
      ae_all_iff.2 (hGae i)] with y hy hl
    rw [hy]
    exact Finset.sum_congr rfl fun l _ ↦ congrArg (· • finBasis ℝ F l) (hl l)
  -- They glue to a continuous section, since the chart data of `w` are the chart expressions of
  -- the section `s` almost everywhere.
  obtain ⟨t, ht, hte⟩ := A.exists_continuous_coord_eqOn_of_ae_eq (μ := volume)
    (fun i ↦ (hg i).continuousOn)
    fun i ↦ ((hs i).trans (A.sectionChartData_coord_ae_eq volume i s)).symm.trans (hwg i)
  refine ⟨t, ht, fun i ↦ ⟨(hg i).congr (hte i), (hwg i).trans ?_⟩⟩
  filter_upwards [ae_restrict_mem (A.image i).isOpen.measurableSet] with y hy
  exact (hte i hy).symm

/-- **Unique continuous representatives of Sobolev sections from a whole-space embedding.** Let
`p < ∞`. If every element of the whole-space space `W^{k,p}(E)` agrees almost everywhere with a
continuous function vanishing at infinity, then every element `w` of `W^{k,p}(V)` has exactly one
continuous representative: there is a unique continuous section `s` of `V` whose chart expression
`A.coord i s` agrees, for every chart `i`, almost everywhere on `A.image i` with the chart-`i` data
of `w`. -/
theorem existsUnique_continuous_ae_eq_coord_of_forall_zeroAtInfty {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤)
    (h : ∀ w : Wkp (volume : Measure E) ⊤ p k, ∃ g : C₀(E, ℝ), Wkp.value k w =ᵐ[volume] g)
    (w : SobolevSection A volume p k) :
    ∃! s : ∀ x, V x, Continuous (fun x ↦ TotalSpace.mk' F x (s x)) ∧
      ∀ i, A.sectionChartData.chartValueL volume p k i w
        =ᵐ[volume.restrict (A.image i)] A.coord i s := by
  obtain ⟨s, hs, hsw⟩ := exists_continuous_contDiffOn_coord_ae_eq_of_forall_zeroAtInfty hp h 0 w
  exact ⟨s, ⟨hs, fun i ↦ (hsw i).2⟩, fun t ht ↦ A.eq_of_continuous_of_coord_ae_eq
    (μ := volume) ht.1 hs fun i ↦ (ht.2 i).symm.trans (hsw i).2⟩

/-- **The critical Sobolev embedding for Sobolev sections, with derivatives.** Let `M` have
dimension `n ≤ k`. Every element `w` of `W^{k+j,1}(V)` is represented by a continuous section `s`
of `V` whose chart expression `A.coord i s` is `Cʲ` on the chart image `A.image i` and agrees almost
everywhere there with the chart-`i` data of `w`, for every chart `i`. -/
theorem exists_continuous_contDiffOn_coord_ae_eq_of_finrank_le (hk : finrank ℝ E ≤ k) (j : ℕ)
    (w : SobolevSection A volume 1 (k + j)) :
    ∃ s : ∀ x, V x, Continuous (fun x ↦ TotalSpace.mk' F x (s x)) ∧
      ∀ i, ContDiffOn ℝ j (A.coord i s) (A.image i) ∧
        A.sectionChartData.chartValueL volume 1 (k + j) i w
          =ᵐ[volume.restrict (A.image i)] A.coord i s :=
  exists_continuous_contDiffOn_coord_ae_eq_of_forall_zeroAtInfty ENNReal.one_ne_top
    (fun w ↦ ⟨Wkp.toZeroAtInftyOne hk w, Wkp.value_ae_eq_toZeroAtInftyOne hk w⟩) j w

/-- **The critical Sobolev embedding for Sobolev sections.** Let `M` have dimension `n ≤ k`. Every
element `w` of `W^{k,1}(V)` has exactly one continuous representative: there is a unique continuous
section `s` of `V` whose chart expression `A.coord i s` agrees, for every chart `i`, almost
everywhere on `A.image i` with the chart-`i` data of `w`. -/
theorem existsUnique_continuous_ae_eq_coord_of_finrank_le (hk : finrank ℝ E ≤ k)
    (w : SobolevSection A volume 1 k) :
    ∃! s : ∀ x, V x, Continuous (fun x ↦ TotalSpace.mk' F x (s x)) ∧
      ∀ i, A.sectionChartData.chartValueL volume 1 k i w
        =ᵐ[volume.restrict (A.image i)] A.coord i s :=
  existsUnique_continuous_ae_eq_coord_of_forall_zeroAtInfty ENNReal.one_ne_top
    (fun w ↦ ⟨Wkp.toZeroAtInftyOne hk w, Wkp.value_ae_eq_toZeroAtInftyOne hk w⟩) w

end SobolevSection

end TauCeti
