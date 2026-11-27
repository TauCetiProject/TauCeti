/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Holder.Inclusion
public import TauCeti.Analysis.Sobolev.Local.Morrey
public import TauCeti.Analysis.Sobolev.W1p.InteriorMorrey
public import TauCeti.Geometry.Manifold.VectorBundle.FiniteBundleAtlas.AEEq
public import TauCeti.Geometry.Manifold.VectorBundle.Sobolev.ContMDiffSection
public import TauCeti.Geometry.Manifold.VectorBundle.Sobolev.Exponent
public import TauCeti.Geometry.Manifold.VectorBundle.Sobolev.Local
import TauCeti.Analysis.Sobolev.Local.SobolevEmbedding
import TauCeti.Analysis.Sobolev.W1p.PreciseRepresentative
import TauCeti.MeasureTheory.Measure.OpenPos
import TauCeti.Topology.MetricSpace.Holder

/-!
# Morrey's embedding for Sobolev sections

Let `M` be a `C¹` manifold without boundary modelled on a finite-dimensional real inner product
space `E` of dimension `n`, let `V → M` be a real vector bundle with finite-dimensional model fibre
`F`, let `A` be a finite bundle atlas and let `μ` be an additive Haar measure on `E`. This file
proves Morrey's embedding for the Sobolev spaces `W^{k,p}(V)` of `TauCeti.SobolevSection A μ p k`.

A continuous representative of an element `w` of `W^{k,p}(V)` is a continuous section `s` of `V`
whose coordinates in every chart `i` of `A` agree almost everywhere on `A.image i` with the chart
data of `w`. There is at most one, and `TauCeti.SobolevSection.toSection w` is it whenever it
exists. The proposition `TauCeti.SobolevSection.HasContinuousRepresentatives A μ p k` says that
every element of `W^{k,p}(V)` has one; under it `toSection` is linear and injective, and it is
continuous: its chart expressions are bounded on compact subsets of the chart images by a multiple
of the Sobolev norm (`TauCeti.SobolevSection.exists_norm_coord_toSection_le`), point evaluation is
a continuous linear map (`TauCeti.SobolevSection.evalL`), and so is
`TauCeti.SobolevSection.toSectionL`. The representative does not change when the order or the
exponent is lowered, nor along any map between Sobolev spaces keeping the chart data, such as a
Sobolev embedding; continuous representatives transfer back along such maps
(`TauCeti.SobolevSection.HasContinuousRepresentatives.of_chartValueL_ae_eq`). Hölder bounds
`C ‖w‖` on the chart expressions over a compact subset `K` of a chart image give a continuous
linear map into the Hölder space `C^{0,α}(K; F)` (`TauCeti.SobolevSection.coordHolderL`). Continuous
representatives exist in two regimes treated here; every order in every dimension, for `k p > n`
and `1 < p`, is `TauCeti.SobolevSection.HasContinuousRepresentatives.of_finrank_lt_mul`.

* **Order one in every dimension.** For `n < p ≤ ∞` every element of `W^{1,p}(V)` has a continuous
  representative (`TauCeti.SobolevSection.HasContinuousRepresentatives.of_finrank_lt`), with
  exponent `α = 1 - n / p`. On every compact subset `K` of a chart image the chart expression of
  the continuous representative is `α`-Hölder with constant `C ‖w‖`, where `C` depends on `K` but
  not on `w`. Restriction to `K` is therefore a continuous linear map
  `TauCeti.SobolevSection.morreyEmbedding` from `W^{1,p}(V)` to the Banach space `C^{0,α}(K; F)`
  of `TauCeti.HolderSpace`. At `p = ∞` the exponent is `1` and the chart expressions are
  Lipschitz. The embedding is compact into every `C^{0,β}(K; F)` with `β < α`
  (`TauCeti.SobolevSection.isCompactOperator_inclusionL_comp_morreyEmbedding`), by the
  Arzelà–Ascoli compactness of the Hölder inclusion `C^{0,α} → C^{0,β}`.
* **Every order over surfaces.** For `E = ℂ`, Lebesgue measure, `1 ≤ p ≤ ∞` and `2 < k p`, every
  element of `W^{k,p}(V)` has a continuous representative
  (`TauCeti.SobolevSection.HasContinuousRepresentatives.of_two_lt_mul`), and for `p > 2` its chart
  expressions are `(1 - 2 / p)`-Hölder on compact subsets of the chart images
  (`TauCeti.SobolevSection.exists_holderOnWith_coord_toSection`). For `k ≥ 2` this covers
  exponents `p ≤ 2`, where `W^{1,p}` functions need not be continuous.

The proofs are local. In chart `i` the chart data of `w` have, in either regime, precise
representatives `gᵢ` continuous on `A.image i` that agree with the chart data there almost
everywhere: at order one the components of `w` in the basis `Module.finBasis ℝ F` are scalar
Sobolev functions `w i j ∈ W^{1,p}(A.image i)`, whose precise representatives are continuous by the
interior Morrey embedding (`TauCeti.W1p.continuousOn_preciseRepresentative`); over surfaces the
chart expressions lie in `MemWkpLoc p (A.image i) k` and the planar Morrey embedding for `kp > 2`
applies (`TauCeti.MemWkpLoc.continuousOn_preciseRepresentative_of_two_lt_mul`). The coordinates of
a section with chart data `w` in two charts are related by the coordinate change of the bundle at
every point of the overlap; since chart transitions preserve null sets, the functions `gᵢ` satisfy
the same relation almost everywhere, and hence everywhere, both sides being continuous on the open
overlap and the Haar measure charging every nonempty open set. Therefore they glue to a continuous
section with chart expression `gᵢ` on `A.image i` for every chart `i`
(`TauCeti.FiniteBundleAtlas.exists_continuous_coord_eqOn_of_ae_eq`). Uniqueness holds because two
continuous sections whose chart expressions agree almost everywhere agree everywhere
(`TauCeti.FiniteBundleAtlas.eq_of_continuous_of_coord_ae_eq`). The sup bound is the closed graph
theorem for the map to continuous functions on a compact neighbourhood of the compact set. The
uniform Hölder bounds at order one come from the uniform interior bounds for the scalar
components, `TauCeti.W1p.exists_forall_holderOnWith_preciseRepresentative_of_isCompact`, since
every component of `w` has norm at most `‖w‖` (`TauCeti.SectionChartData.norm_component_le`).

For `n ≥ 2` the hypothesis `n < p` cannot be weakened to `p = n`: `W^{1,n}` contains unbounded
functions, such as `log (log (e / ‖x‖))` near the origin. Likewise `2 < k p` cannot be dropped
over surfaces.

## Main results

* `TauCeti.SobolevSection.toSection`: the continuous representative, and
  `TauCeti.SobolevSection.HasContinuousRepresentatives`: every element has one.
* `TauCeti.SobolevSection.existsUnique_continuous_ae_eq_coord`: the continuous representative is
  unique.
* `TauCeti.SobolevSection.toSection_injective`: distinct elements have distinct continuous
  representatives, and `TauCeti.SobolevSection.toSection_ofContMDiffSection`: a `Cᵏ` section is
  its own continuous representative.
* `TauCeti.SobolevSection.toSection_lowerOrderL`, `TauCeti.SobolevSection.toSection_ofExponentLEL`:
  the continuous representative does not change when the order or the exponent is lowered, and
  `TauCeti.SobolevSection.toSection_eq_of_chartValueL_ae_eq`: nor between any two Sobolev
  sections with the same chart data.
* `TauCeti.SobolevSection.HasContinuousRepresentatives.of_chartValueL_ae_eq`: continuous
  representatives transfer back along maps keeping the chart data, and
  `TauCeti.SobolevSection.HasContinuousRepresentatives.mono`: to higher orders and exponents.
* `TauCeti.SobolevSection.exists_forall_holderOnWith_coord_toSection_of_chartValueL_ae_eq`: Hölder
  bounds in a chart transfer back along bounded linear maps keeping the chart data.
* `TauCeti.SobolevSection.coordHolderL`: Hölder bounds in a chart give a bounded operator into
  `C^{0,α}(K; F)`, and `TauCeti.SobolevSection.isCompactOperator_inclusionL_comp_coordHolderL`:
  it is compact into `C^{0,β}(K; F)` for `β < α`.
* `TauCeti.SobolevSection.exists_norm_coord_toSection_le`: the sup bound of the chart expressions
  on compact subsets of the chart images, `TauCeti.SobolevSection.evalL`: evaluation of the
  continuous representative at a point is a continuous linear map to the fibre, and
  `TauCeti.SobolevSection.toSectionL`: the continuous representative as a continuous linear map to
  sections with the topology of pointwise convergence.
* `TauCeti.SobolevSection.HasContinuousRepresentatives.of_finrank_lt`: continuous representatives
  in `W^{1,p}(V)` for `p` above the dimension.
* `TauCeti.SobolevSection.repr_coord_toSection`: at order one, in chart `i`, the components of the
  continuous representative are the precise representatives of the chart-`i` components of `w`.
* `TauCeti.SobolevSection.exists_forall_holderOnWith_coord_toSection` and
  `TauCeti.SobolevSection.exists_forall_lipschitzOnWith_coord_toSection`: at order one the chart
  expressions are `α`-Hölder, Lipschitz at `p = ∞`, on compact subsets of the chart images, with
  constants `C ‖w‖`.
* `TauCeti.SobolevSection.morreyEmbedding`: the bounded operator `W^{1,p}(V) → C^{0,α}(K; F)`,
  the case of `TauCeti.SobolevSection.coordHolderL` at order one.
* `TauCeti.SobolevSection.isCompactOperator_inclusionL_comp_morreyEmbedding`: it is compact into
  `C^{0,β}(K; F)` for `β < α`.
* `TauCeti.SobolevSection.HasContinuousRepresentatives.of_two_lt_mul`: continuous representatives
  in `W^{k,p}(V)` over surfaces for `2 < k p`, and
  `TauCeti.SobolevSection.exists_holderOnWith_coord_toSection`: their chart expressions are
  `(1 - 2 / p)`-Hölder for `p > 2`.

## References

* C. B. Morrey, *Multiple Integrals in the Calculus of Variations*, Theorem 3.5.2.
* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Theorem 7.17.
* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Appendix B.1 (Sobolev spaces of sections and the Sobolev embedding theorem).
* R. S. Palais, *Foundations of Global Non-linear Analysis*, Benjamin (1968), §9.
-/

public section

noncomputable section

open Bundle Filter MeasureTheory Module Set TopologicalSpace TauCeti.MeasureTheory
open scoped Manifold ENNReal NNReal Topology

namespace TauCeti

section General

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)] [∀ x, AddCommGroup (V x)]
  [∀ x, Module ℝ (V x)] [∀ x, TopologicalSpace (V x)] [FiberBundle F V] [VectorBundle ℝ F V]
  {A : FiniteBundleAtlas E M F V} {p : ℝ≥0∞} [Fact (1 ≤ p)] {k : ℕ}

namespace SobolevSection

open FiniteBundleAtlas

/-- **Continuous representatives.** Every element `w` of `W^{k,p}(V)` has a continuous
representative: a continuous section `s` of `V` whose chart expression `A.coord i s` agrees, for
every chart `i`, almost everywhere on `A.image i` with the chart data of `w`. It holds at order one
for `p` above the dimension
(`TauCeti.SobolevSection.HasContinuousRepresentatives.of_finrank_lt`), over surfaces for
`2 < k p` (`TauCeti.SobolevSection.HasContinuousRepresentatives.of_two_lt_mul`), and on compact
smooth manifolds for `1 < p` and `n < k p`
(`TauCeti.SobolevSection.HasContinuousRepresentatives.of_finrank_lt_mul`). -/
def HasContinuousRepresentatives (A : FiniteBundleAtlas E M F V) (μ : Measure E)
    [μ.IsAddHaarMeasure] (p : ℝ≥0∞) [Fact (1 ≤ p)] (k : ℕ) : Prop :=
  ∀ w : SobolevSection A μ p k, ∃ s : ∀ x, V x, Continuous (fun x ↦ TotalSpace.mk' F x (s x)) ∧
    ∀ i, A.sectionChartData.chartValueL μ p k i w =ᵐ[μ.restrict (A.image i)] A.coord i s

/-- The continuous representative of an element of `W^{k,p}(V)`: a continuous section whose chart
expressions agree almost everywhere with the chart data, whenever there is one. It is then unique
(`TauCeti.SobolevSection.eq_toSection`). -/
def toSection (w : SobolevSection A μ p k) : ∀ x, V x :=
  Classical.epsilon fun s : ∀ x, V x ↦ Continuous (fun x ↦ TotalSpace.mk' F x (s x)) ∧
    ∀ i, A.sectionChartData.chartValueL μ p k i w =ᵐ[μ.restrict (A.image i)] A.coord i s

/-- If `w` has a continuous representative, then `TauCeti.SobolevSection.toSection w` is one. -/
private theorem toSection_spec {w : SobolevSection A μ p k}
    (hw : ∃ s : ∀ x, V x, Continuous (fun x ↦ TotalSpace.mk' F x (s x)) ∧
      ∀ i, A.sectionChartData.chartValueL μ p k i w =ᵐ[μ.restrict (A.image i)] A.coord i s) :
    Continuous (fun x ↦ TotalSpace.mk' F x (toSection w x)) ∧
      ∀ i, A.sectionChartData.chartValueL μ p k i w
        =ᵐ[μ.restrict (A.image i)] A.coord i (toSection w) :=
  Classical.epsilon_spec hw

/-- The continuous representative is a continuous section. -/
theorem continuous_toSection (h : HasContinuousRepresentatives A μ p k)
    (w : SobolevSection A μ p k) : Continuous fun x ↦ TotalSpace.mk' F x (toSection w x) :=
  (toSection_spec (h w)).1

/-- The chart data of an element of `W^{k,p}(V)` are the chart expressions of its continuous
representative, almost everywhere. -/
theorem chartValueL_ae_eq_coord_toSection (h : HasContinuousRepresentatives A μ p k)
    (w : SobolevSection A μ p k) (i : Fin A.n) :
    A.sectionChartData.chartValueL μ p k i w
      =ᵐ[μ.restrict (A.image i)] A.coord i (toSection w) :=
  (toSection_spec (h w)).2 i

/-- **Uniqueness of the continuous representative.** A continuous section whose chart
expressions agree almost everywhere with the chart data of `w` is the continuous representative
of `w`. -/
theorem eq_toSection {w : SobolevSection A μ p k} {s : ∀ x, V x}
    (hs : Continuous fun x ↦ TotalSpace.mk' F x (s x))
    (hw : ∀ i, A.sectionChartData.chartValueL μ p k i w
      =ᵐ[μ.restrict (A.image i)] A.coord i s) :
    s = toSection w :=
  have h := toSection_spec ⟨s, hs, hw⟩
  A.eq_of_continuous_of_coord_ae_eq (μ := μ) hs h.1 fun i ↦ (hw i).symm.trans (h.2 i)

/-- **Morrey's embedding for Sobolev sections: continuous representatives.** When every element of
`W^{k,p}(V)` has a continuous representative, it is unique: there is exactly one continuous section
`s` of `V` whose chart expression `A.coord i s` agrees, for every chart `i`, almost everywhere on
`A.image i` with the chart data of `w`. -/
theorem existsUnique_continuous_ae_eq_coord (h : HasContinuousRepresentatives A μ p k)
    (w : SobolevSection A μ p k) :
    ∃! s : ∀ x, V x, Continuous (fun x ↦ TotalSpace.mk' F x (s x)) ∧
      ∀ i, A.sectionChartData.chartValueL μ p k i w
        =ᵐ[μ.restrict (A.image i)] A.coord i s :=
  ⟨toSection w, toSection_spec (h w), fun _ hs ↦ eq_toSection hs.1 hs.2⟩

/-- **Injectivity.** Distinct elements of `W^{k,p}(V)` have distinct continuous
representatives. -/
theorem toSection_injective (h : HasContinuousRepresentatives A μ p k) :
    Function.Injective (toSection : SobolevSection A μ p k → ∀ x, V x) :=
  fun w w' hww' ↦ eq_of_ae_eq_coord (chartValueL_ae_eq_coord_toSection h w)
    (hww' ▸ chartValueL_ae_eq_coord_toSection h w')

/-- Forgetting the highest derivative keeps the chart data. -/
theorem chartValueL_lowerOrderL_ae_eq (w : SobolevSection A μ p (k + 1)) (i) :
    A.sectionChartData.chartValueL μ p k i (A.sectionChartData.lowerOrderL μ p k w)
      =ᵐ[μ.restrict (A.image i)] A.sectionChartData.chartValueL μ p (k + 1) i w := by
  rw [SectionChartData.chartValueL_coe_lowerOrderL]

/-- Lowering the exponent keeps the chart data. -/
theorem chartValueL_ofExponentLEL_ae_eq {q : ℝ≥0∞} [Fact (1 ≤ q)] (hpq : p ≤ q)
    (w : SobolevSection A μ q k) (i) :
    A.sectionChartData.chartValueL μ p k i (A.sectionChartData.ofExponentLEL μ k hpq w)
      =ᵐ[μ.restrict (A.image i)] A.sectionChartData.chartValueL μ q k i w :=
  .of_eq (SectionChartData.coeFn_chartValueL_ofExponentLEL hpq w i)

/-- Two Sobolev sections, possibly of different orders and exponents, with the same chart data have
the same continuous representative. -/
theorem toSection_eq_of_chartValueL_ae_eq {q : ℝ≥0∞} [Fact (1 ≤ q)] {l : ℕ}
    (h : HasContinuousRepresentatives A μ q l) {v : SobolevSection A μ q l}
    {w : SobolevSection A μ p k}
    (hvw : ∀ i, A.sectionChartData.chartValueL μ q l i v
      =ᵐ[μ.restrict (A.image i)] A.sectionChartData.chartValueL μ p k i w) :
    toSection v = toSection w :=
  eq_toSection (continuous_toSection h v) fun i ↦
    (hvw i).symm.trans (chartValueL_ae_eq_coord_toSection h v i)

/-- Forgetting the highest derivative does not change the continuous representative. -/
@[simp]
theorem toSection_lowerOrderL (h : HasContinuousRepresentatives A μ p (k + 1))
    (w : SobolevSection A μ p (k + 1)) :
    toSection (A.sectionChartData.lowerOrderL μ p k w) = toSection w :=
  (toSection_eq_of_chartValueL_ae_eq h fun i ↦ (chartValueL_lowerOrderL_ae_eq w i).symm).symm

/-- Lowering the exponent does not change the continuous representative. -/
@[simp]
theorem toSection_ofExponentLEL {q : ℝ≥0∞} [Fact (1 ≤ q)] (hpq : p ≤ q)
    (h : HasContinuousRepresentatives A μ q k) (w : SobolevSection A μ q k) :
    toSection (A.sectionChartData.ofExponentLEL μ k hpq w) = toSection w :=
  (toSection_eq_of_chartValueL_ae_eq h fun i ↦ (chartValueL_ofExponentLEL_ae_eq hpq w i).symm).symm

/-- **Transfer of continuous representatives.** If a map `T` from `W^{k,p}(V)` to `W^{l,q}(V)` keeps
the chart data and every element of `W^{l,q}(V)` has a continuous representative, then so does every
element of `W^{k,p}(V)`. Typical maps `T` are Sobolev embeddings. -/
theorem HasContinuousRepresentatives.of_chartValueL_ae_eq {q : ℝ≥0∞} [Fact (1 ≤ q)] {l : ℕ}
    (h : HasContinuousRepresentatives A μ q l)
    (T : SobolevSection A μ p k → SobolevSection A μ q l)
    (hT : ∀ w i, A.sectionChartData.chartValueL μ q l i (T w)
      =ᵐ[μ.restrict (A.image i)] A.sectionChartData.chartValueL μ p k i w) :
    HasContinuousRepresentatives A μ p k := fun w ↦
  ⟨toSection (T w), continuous_toSection h (T w),
    fun i ↦ (hT w i).symm.trans (chartValueL_ae_eq_coord_toSection h (T w) i)⟩

/-- **Transfer of Hölder bounds.** If a bounded linear map `T` from `W^{k,p}(V)` to `W^{l,q}(V)`
keeps the chart data and the chart expressions of the continuous representatives of `W^{l,q}(V)`
are `α`-Hölder on `K` with constant `C ‖v‖`, then those of `W^{k,p}(V)` are `α`-Hölder on `K` with
constant `C ‖T‖ ‖w‖`. -/
theorem exists_forall_holderOnWith_coord_toSection_of_chartValueL_ae_eq {q : ℝ≥0∞} [Fact (1 ≤ q)]
    {l : ℕ} (h : HasContinuousRepresentatives A μ q l)
    (T : SobolevSection A μ p k →L[ℝ] SobolevSection A μ q l)
    (hT : ∀ w i, A.sectionChartData.chartValueL μ q l i (T w)
      =ᵐ[μ.restrict (A.image i)] A.sectionChartData.chartValueL μ p k i w)
    {i : Fin A.n} {K : Set E} {α : ℝ≥0}
    (hC : ∃ C : ℝ≥0, ∀ v : SobolevSection A μ q l,
      HolderOnWith (C * ‖v‖₊) α (A.coord i (toSection v)) K) :
    ∃ C : ℝ≥0, ∀ w : SobolevSection A μ p k,
      HolderOnWith (C * ‖w‖₊) α (A.coord i (toSection w)) K := by
  obtain ⟨C, hC⟩ := hC
  refine ⟨C * ‖T‖₊, fun w ↦ ?_⟩
  rw [← toSection_eq_of_chartValueL_ae_eq h (hT w)]
  refine (hC (T w)).mono_const ?_
  rw [mul_assoc]
  gcongr
  exact T.le_opNNNorm w

/-- **Monotonicity of continuous representatives.** If the elements of `W^{k,p}(V)` have continuous
representatives, so do those of `W^{l,q}(V)` for `k ≤ l` and `p ≤ q`. -/
theorem HasContinuousRepresentatives.mono {q : ℝ≥0∞} [Fact (1 ≤ q)] {l : ℕ}
    (h : HasContinuousRepresentatives A μ p k) (hpq : p ≤ q) (hkl : k ≤ l) :
    HasContinuousRepresentatives A μ q l := by
  have hp : HasContinuousRepresentatives A μ p l := by
    induction l, hkl using Nat.le_induction with
    | base => exact h
    | succ l _ ih =>
      exact ih.of_chartValueL_ae_eq _ chartValueL_lowerOrderL_ae_eq
  exact hp.of_chartValueL_ae_eq _ (chartValueL_ofExponentLEL_ae_eq hpq)

/-- The continuous representative of a `Cᵏ` section, viewed as an element of `W^{k,p}(V)`, is the
section itself. -/
@[simp]
theorem toSection_ofContMDiffSection [IsManifold 𝓘(ℝ, E) k M]
    [ContMDiffVectorBundle k F V 𝓘(ℝ, E)] (s : Cₛ^k⟮𝓘(ℝ, E); F, V⟯) :
    toSection (ofContMDiffSection A μ p k s) = s :=
  (eq_toSection s.contMDiff.continuous (chartValueL_ofContMDiffSection_ae A μ p k s)).symm

/-- Taking continuous representatives is additive. -/
@[simp]
theorem toSection_add (h : HasContinuousRepresentatives A μ p k)
    (w v : SobolevSection A μ p k) : toSection (w + v) = toSection w + toSection v := by
  refine (eq_toSection ?_ fun i ↦ ?_).symm
  · exact contMDiff_zero_iff.1 (ContMDiff.add_section (I := 𝓘(ℝ, E))
      (contMDiff_zero_iff.2 (continuous_toSection h w))
      (contMDiff_zero_iff.2 (continuous_toSection h v)))
  · exact chartValueL_add_ae_coord (chartValueL_ae_eq_coord_toSection h w i)
      (chartValueL_ae_eq_coord_toSection h v i)

/-- Taking continuous representatives commutes with real scalar multiplication. -/
@[simp]
theorem toSection_smul (h : HasContinuousRepresentatives A μ p k) (c : ℝ)
    (w : SobolevSection A μ p k) : toSection (c • w) = c • toSection w := by
  refine (eq_toSection ?_ fun i ↦ ?_).symm
  · exact contMDiff_zero_iff.1 (ContMDiff.const_smul_section (I := 𝓘(ℝ, E)) (a := c)
      (contMDiff_zero_iff.2 (continuous_toSection h w)))
  · exact chartValueL_smul_ae_coord c (chartValueL_ae_eq_coord_toSection h w i)

/-- The combination of the basis vectors of the model fibre with the precise representatives of the
chart-`i` components of an element of `W^{1,p}(V)`. -/
private def chartRep (w : SobolevSection A μ p 1) (i : Fin A.n) (y : E) : F :=
  ∑ j, preciseRepresentative μ
    (W1p.value ((w : A.sectionChartData.SobolevData μ p 1) i j)) y • finBasis ℝ F j

/-- For `p` above the dimension, `chartRep w i` is continuous on the image of chart `i`. -/
private theorem continuousOn_chartRep (hp : (finrank ℝ E : ℝ≥0∞) < p)
    (w : SobolevSection A μ p 1) (i : Fin A.n) : ContinuousOn (chartRep w i) (A.image i) :=
  continuousOn_finsetSum _ fun _ _ ↦
    (W1p.continuousOn_preciseRepresentative hp _).smul continuousOn_const

/-- The chart data of `w` agree with `chartRep w i` almost everywhere on the image of chart `i`. -/
private theorem chartValueL_ae_eq_chartRep (w : SobolevSection A μ p 1) (i : Fin A.n) :
    A.sectionChartData.chartValueL μ p 1 i w =ᵐ[μ.restrict (A.image i)] chartRep w i := by
  filter_upwards [A.sectionChartData.chartValueL_apply_ae μ p 1 i w,
    ae_all_iff.2 fun j ↦ W1p.ae_eq_preciseRepresentative
      ((w : A.sectionChartData.SobolevData μ p 1) i j)] with y hy hj
  rw [hy]
  exact Finset.sum_congr rfl fun j _ ↦ by rw [Wkp.value_one, hj j]

/-- The chart expression in chart `i` of the continuous representative, restricted to a subset
`L` of the chart image, as a linear map into the continuous functions on `L`. -/
private def coordRestrictₗ (h : HasContinuousRepresentatives A μ p k) (i : Fin A.n) {L : Set E}
    (hLi : L ⊆ A.image i) : SobolevSection A μ p k →ₗ[ℝ] C(L, F) where
  toFun w := ⟨fun y ↦ A.coord i (toSection w) y,
    ((A.continuousOn_coord (continuous_toSection h w) i).mono hLi).domRestrict⟩
  map_add' w v := by
    ext y
    simp only [toSection_add h, ContinuousMap.add_apply, ContinuousMap.coe_mk]
    exact A.coord_add i _ _ (hLi y.property)
  map_smul' c w := by
    ext y
    simp only [toSection_smul h, ContinuousMap.smul_apply, ContinuousMap.coe_mk]
    exact A.coord_smul i _ _ (hLi y.property)

private theorem coordRestrictₗ_apply (h : HasContinuousRepresentatives A μ p k) (i : Fin A.n)
    {L : Set E} (hLi : L ⊆ A.image i) (w : SobolevSection A μ p k) (y : L) :
    coordRestrictₗ h i hLi w y = A.coord i (toSection w) y :=
  rfl

variable [IsManifold 𝓘(ℝ, E) 1 M]

/-- On the closure of an open set with compact closure inside the chart image, the chart
expression of the continuous representative depends continuously on the element of
`W^{k,p}(V)`, by the closed graph theorem: limits in `W^{k,p}(V)` give limits of the chart data in
`Lᵖ`, hence almost everywhere along a subsequence. -/
private theorem continuous_coordRestrictₗ (h : HasContinuousRepresentatives A μ p k) (i : Fin A.n)
    {U : Opens E} (hUi : closure (U : Set E) ⊆ A.image i) (hUc : IsCompact (closure (U : Set E))) :
    Continuous (coordRestrictₗ h i hUi) := by
  set L := closure (U : Set E)
  have : CompactSpace L := isCompact_iff_compactSpace.1 hUc
  refine (coordRestrictₗ h i hUi).continuous_of_seq_closed_graph fun w w₀ g hw hg ↦ ?_
  -- Along a subsequence the chart data converge almost everywhere.
  have hval : Tendsto (fun n ↦ A.sectionChartData.chartValueL μ p k i (w n)) atTop
      (𝓝 (A.sectionChartData.chartValueL μ p k i w₀)) :=
    ((A.sectionChartData.chartValueL μ p k i).continuous.comp
      continuous_subtypeVal).continuousAt.tendsto.comp hw
  obtain ⟨ns, hns_mono, hns⟩ := (tendstoInMeasure_of_tendsto_Lp hval).exists_seq_tendsto_ae
  have hae : ∀ᵐ y ∂μ.restrict (A.image i), Tendsto
      (fun n ↦ A.coord i (toSection (w (ns n))) y) atTop
      (𝓝 (A.coord i (toSection w₀) y)) := by
    filter_upwards [hns, ae_all_iff.2 fun n ↦ chartValueL_ae_eq_coord_toSection h (w (ns n)) i,
      chartValueL_ae_eq_coord_toSection h w₀ i] with y hy hn h₀
    simpa only [hn, h₀] using hy
  -- The limit `g` agrees with the chart expression of the representative of the limit almost
  -- everywhere on `U`, hence on its closure.
  refine DFunLike.coe_injective (U.isOpen.ext_closure_of_ae_eq (μ := μ) g.continuous
    (coordRestrictₗ h i hUi w₀).continuous ?_)
  filter_upwards [(ae_restrict_iff' (A.image i).isOpen.measurableSet).1 hae] with y hy hyU
  exact tendsto_nhds_unique (((continuous_eval_const (⟨y, subset_closure hyU⟩ : L)).tendsto g).comp
    (hg.comp hns_mono.tendsto_atTop)) (hy (hUi (subset_closure hyU)))

/-- **Morrey's embedding for Sobolev sections: the sup bound.** When every element of
`W^{k,p}(V)` has a continuous representative, the chart expression of the continuous
representative is bounded on every compact subset `K` of the chart image by a constant multiple
of the Sobolev norm, the constant depending on `K` but not on the element. -/
theorem exists_norm_coord_toSection_le (h : HasContinuousRepresentatives A μ p k) (i : Fin A.n)
    {K : Set E} (hK : IsCompact K) (hKi : K ⊆ A.image i) :
    ∃ C : ℝ≥0, ∀ w : SobolevSection A μ p k, ∀ y ∈ K,
      ‖A.coord i (toSection w) y‖ ≤ C * ‖w‖ := by
  obtain ⟨U, hKU, hUi, hUc⟩ := Opens.exists_between_and_isCompact_closure hK hKi
  have : CompactSpace (closure (U : Set E)) := isCompact_iff_compactSpace.1 hUc
  let Ψ : SobolevSection A μ p k →L[ℝ] C(closure (U : Set E), F) :=
    ⟨coordRestrictₗ h i hUi, continuous_coordRestrictₗ h i hUi hUc⟩
  refine ⟨‖Ψ‖₊, fun w y hy ↦ ?_⟩
  have hyL : y ∈ closure (U : Set E) := subset_closure (hKU hy)
  calc ‖A.coord i (toSection w) y‖ = ‖Ψ w ⟨y, hyL⟩‖ := by
        rw [ContinuousLinearMap.coe_mk', coordRestrictₗ_apply]
    _ ≤ ‖Ψ w‖ := (Ψ w).norm_coe_le_norm _
    _ ≤ ‖Ψ‖ * ‖w‖ := Ψ.le_opNorm w

/-- **Morrey's embedding for Sobolev sections: point evaluation.** When every element of
`W^{k,p}(V)` has a continuous representative, evaluating the continuous representative at a point
`x` is a continuous real-linear map from `W^{k,p}(V)` to the fibre `V x`. -/
def evalL (h : HasContinuousRepresentatives A μ p k) (x : M) :
    SobolevSection A μ p k →L[ℝ] V x where
  toFun w := toSection w x
  map_add' w v := by simp [toSection_add h]
  map_smul' c w := by simp [toSection_smul h]
  cont := by
    obtain ⟨i, hx⟩ := A.exists_mem_dom x
    have hxi : A.chart i x ∈ A.image i := A.mem_image.2 ⟨x, hx, rfl⟩
    obtain ⟨U, hxU, hUi, hUc⟩ := Opens.exists_between_and_isCompact_closure isCompact_singleton
      (singleton_subset_iff.2 hxi)
    -- The chart expression at `A.chart i x` determines the value at `x`.
    refine (((A.triv i).symmL ℝ x).continuous.comp
      ((continuous_eval_const (⟨A.chart i x, subset_closure (hxU rfl)⟩ :
        closure (U : Set E))).comp (continuous_coordRestrictₗ h i hUi hUc))).congr fun w ↦ ?_
    simp [coordRestrictₗ_apply, (A.triv i).symmL_apply (A.dom_subset_baseSet i hx),
      A.coord_chart _ hx, (A.triv i).symm_apply_apply_mk (A.dom_subset_baseSet i hx)]

@[simp]
theorem evalL_apply (h : HasContinuousRepresentatives A μ p k) (x : M)
    (w : SobolevSection A μ p k) : evalL h x w = toSection w x :=
  (rfl)

/-- Taking continuous representatives, as a continuous real-linear map from `W^{k,p}(V)` to
sections, with the topology of pointwise convergence. -/
def toSectionL (h : HasContinuousRepresentatives A μ p k) :
    SobolevSection A μ p k →L[ℝ] ∀ x, V x :=
  ContinuousLinearMap.pi (evalL h)

@[simp]
theorem toSectionL_apply (h : HasContinuousRepresentatives A μ p k)
    (w : SobolevSection A μ p k) : toSectionL h w = toSection w :=
  (rfl)

/-- The continuous representative of `0` is the zero section. -/
@[simp]
theorem toSection_zero (h : HasContinuousRepresentatives A μ p k) :
    toSection (0 : SobolevSection A μ p k) = 0 :=
  map_zero (toSectionL h)

/-- Taking continuous representatives commutes with negation. -/
@[simp]
theorem toSection_neg (h : HasContinuousRepresentatives A μ p k) (w : SobolevSection A μ p k) :
    toSection (-w) = -toSection w :=
  map_neg (toSectionL h) w

/-- Taking continuous representatives commutes with subtraction. -/
@[simp]
theorem toSection_sub (h : HasContinuousRepresentatives A μ p k)
    (w v : SobolevSection A μ p k) : toSection (w - v) = toSection w - toSection v :=
  map_sub (toSectionL h) w v

/-- The restriction to a compact subset `K` of the image of chart `i` of the chart expression of the
continuous representative, as an element of the Hölder space `C^{0,α}(K; F)`, given a Hölder bound
with constant `C ‖w‖`. -/
private def coordHolder (h : HasContinuousRepresentatives A μ p k) (i : Fin A.n) (K : Set E)
    (hKi : K ⊆ A.image i) [CompactSpace K] {α : ℝ≥0}
    (hα : ∃ C : ℝ≥0, ∀ w : SobolevSection A μ p k,
      HolderOnWith (C * ‖w‖₊) α (A.coord i (toSection w)) K)
    (w : SobolevSection A μ p k) : HolderSpace α K F :=
  HolderSpace.ofBoundedContinuousFunction
    (BoundedContinuousFunction.mkOfCompact ⟨K.domRestrict (A.coord i (toSection w)),
      ((A.continuousOn_coord (continuous_toSection h w) i).mono hKi).domRestrict⟩)
    (let ⟨_, hC⟩ := hα
    ⟨_, (hC w).holderWith⟩)

omit [IsManifold 𝓘(ℝ, E) 1 M] in
private theorem coe_coordHolder (h : HasContinuousRepresentatives A μ p k) (i : Fin A.n)
    (K : Set E) (hKi : K ⊆ A.image i) [CompactSpace K] {α : ℝ≥0}
    (hα : ∃ C : ℝ≥0, ∀ w : SobolevSection A μ p k,
      HolderOnWith (C * ‖w‖₊) α (A.coord i (toSection w)) K)
    (w : SobolevSection A μ p k) :
    ⇑(coordHolder h i K hKi hα w) = K.domRestrict (A.coord i (toSection w)) := by
  ext y
  simp [coordHolder, HolderSpace.ofBoundedContinuousFunction_apply]

/-- **Sobolev sections in a Hölder space.** When every element `w` of `W^{k,p}(V)` has a continuous
representative whose chart expression in chart `i` is `α`-Hölder on a compact subset `K` of the
chart image with constant `C ‖w‖`, restricting that chart expression to `K` is a continuous linear
map from `W^{k,p}(V)` to the Banach space `C^{0,α}(K; F)` of `TauCeti.HolderSpace`. At order one
for `p` above the dimension this is `TauCeti.SobolevSection.morreyEmbedding`. -/
def coordHolderL (h : HasContinuousRepresentatives A μ p k) (i : Fin A.n) (K : Set E)
    [CompactSpace K] (hKi : K ⊆ A.image i) {α : ℝ≥0}
    (hα : ∃ C : ℝ≥0, ∀ w : SobolevSection A μ p k,
      HolderOnWith (C * ‖w‖₊) α (A.coord i (toSection w)) K) :
    SobolevSection A μ p k →L[ℝ] HolderSpace α K F :=
  LinearMap.mkContinuousOfExistsBound
    { toFun := coordHolder h i K hKi hα
      map_add' w v := HolderSpace.ext fun y ↦ by
        rw [HolderSpace.add_apply, coe_coordHolder, coe_coordHolder, coe_coordHolder]
        simp only [Set.domRestrict_apply]
        rw [toSection_add h, A.coord_add i _ _ (hKi y.property)]
      map_smul' c w := HolderSpace.ext fun y ↦ by
        rw [RingHom.id_apply, HolderSpace.smul_apply, coe_coordHolder, coe_coordHolder]
        simp only [Set.domRestrict_apply]
        rw [toSection_smul h, A.coord_smul i _ _ (hKi y.property)] }
    (by
      obtain ⟨C₁, h₁⟩ := exists_norm_coord_toSection_le h i (isCompact_iff_compactSpace.2 ‹_›) hKi
      obtain ⟨C₂, h₂⟩ := hα
      refine ⟨(C₁ : ℝ) + C₂, fun w ↦ ?_⟩
      have hsup (y : K) : ‖coordHolder h i K hKi ⟨C₂, h₂⟩ w y‖ ≤ C₁ * ‖w‖ := by
        rw [coe_coordHolder, Set.domRestrict_apply]
        exact h₁ w y y.property
      have hhol : HolderWith (C₂ * ‖w‖₊) α (coordHolder h i K hKi ⟨C₂, h₂⟩ w) := by
        rw [coe_coordHolder]
        exact (h₂ w).holderWith
      refine (HolderSpace.norm_le_of_norm_le_of_holderWith (by positivity) hsup hhol).trans_eq ?_
      rw [NNReal.coe_mul, coe_nnNorm]
      ring)

@[simp]
theorem coordHolderL_apply_apply (h : HasContinuousRepresentatives A μ p k) (i : Fin A.n)
    (K : Set E) [CompactSpace K] (hKi : K ⊆ A.image i) {α : ℝ≥0}
    (hα : ∃ C : ℝ≥0, ∀ w : SobolevSection A μ p k,
      HolderOnWith (C * ‖w‖₊) α (A.coord i (toSection w)) K)
    (w : SobolevSection A μ p k) (y : K) :
    coordHolderL h i K hKi hα w y = A.coord i (toSection w) y := by
  simp [coordHolderL, coe_coordHolder]

/-- **Compactness into Hölder spaces of smaller exponent.** For `β < α`, the map
`TauCeti.SobolevSection.coordHolderL` into `C^{0,α}(K; F)` followed by the inclusion into
`C^{0,β}(K; F)` is a compact operator, by the compactness of that inclusion
(`TauCeti.HolderSpace.isCompactOperator_inclusionL`). -/
theorem isCompactOperator_inclusionL_comp_coordHolderL (h : HasContinuousRepresentatives A μ p k)
    (i : Fin A.n) (K : Set E) [CompactSpace K] (hKi : K ⊆ A.image i) {α β : ℝ≥0}
    (hα : ∃ C : ℝ≥0, ∀ w : SobolevSection A μ p k,
      HolderOnWith (C * ‖w‖₊) α (A.coord i (toSection w)) K) (hβ : β < α) :
    IsCompactOperator ((HolderSpace.inclusionL (X := K) (Y := F) hβ.le).comp
      (coordHolderL h i K hKi hα)) :=
  (HolderSpace.isCompactOperator_inclusionL hβ).comp_clm _

/-! ### Order one in every dimension -/

/-- **Morrey's embedding for Sobolev sections: continuous representatives at order one.** For `p`
above the dimension `n` of the model space, `n < p ≤ ∞`, every element `w` of `W^{1,p}(V)` has a
continuous representative: a continuous section `s` of `V` whose chart expression `A.coord i s`
agrees, for every chart `i`, almost everywhere on `A.image i` with the chart data of `w`. -/
theorem HasContinuousRepresentatives.of_finrank_lt (hp : (finrank ℝ E : ℝ≥0∞) < p) :
    HasContinuousRepresentatives A μ p 1 := by
  intro w
  obtain ⟨s, hs⟩ := exists_ae_eq_coord w
  -- The functions `chartRep w i` glue to a continuous section.
  obtain ⟨t, ht, hts⟩ := exists_continuous_coord_eqOn_of_ae_eq (μ := μ)
    (continuousOn_chartRep hp w) fun i ↦ (hs i).symm.trans (chartValueL_ae_eq_chartRep w i)
  refine ⟨t, ht, fun i ↦ ?_⟩
  filter_upwards [chartValueL_ae_eq_chartRep w i,
    ae_restrict_mem (A.image i).isOpen.measurableSet] with y hy hyU
  rw [hy, hts i hyU]

/-- On the image of chart `i`, the chart expression of the continuous representative is
`chartRep w i`. -/
private theorem eqOn_coord_toSection_chartRep (hp : (finrank ℝ E : ℝ≥0∞) < p)
    (w : SobolevSection A μ p 1) (i : Fin A.n) :
    EqOn (A.coord i (toSection w)) (chartRep w i) (A.image i) :=
  Measure.eqOn_open_of_ae_eq (μ := μ)
    ((chartValueL_ae_eq_coord_toSection (.of_finrank_lt hp) w i).symm.trans
      (chartValueL_ae_eq_chartRep w i))
    (A.image i).isOpen
    (A.continuousOn_coord (continuous_toSection (.of_finrank_lt hp) w) i)
    (continuousOn_chartRep hp w i)

/-- **The chart components of the continuous representative.** On the image of chart `i`, the
`j`th component in the basis `Module.finBasis ℝ F` of the chart expression of the continuous
representative of `w ∈ W^{1,p}(V)`, for `p` above the dimension, is the precise representative of
the chart-`i` component `w i j`, a scalar Sobolev function on the chart image. -/
theorem repr_coord_toSection (hp : (finrank ℝ E : ℝ≥0∞) < p) (w : SobolevSection A μ p 1)
    {i : Fin A.n} {y : E} (hy : y ∈ A.image i) (j : Fin (finrank ℝ F)) :
    (finBasis ℝ F).repr (A.coord i (toSection w) y) j =
      preciseRepresentative μ (W1p.value ((w : A.sectionChartData.SobolevData μ p 1) i j)) y := by
  rw [eqOn_coord_toSection_chartRep hp w i hy, chartRep, (finBasis ℝ F).repr_sum_self]

/-- **Morrey's embedding for Sobolev sections: Hölder continuity in charts.** For `n < p ≤ ∞`,
where `n` is the dimension, on every compact subset `K` of the image of chart `i` the chart
expression of the continuous representative of `w ∈ W^{1,p}(V)` is Hölder continuous with exponent
`1 - n / p` and constant `C ‖w‖`, where `C` depends on `K` but not on `w`. -/
theorem exists_forall_holderOnWith_coord_toSection (hp : (finrank ℝ E : ℝ≥0∞) < p)
    (i : Fin A.n) {K : Set E} (hK : IsCompact K) (hKi : K ⊆ A.image i) :
    ∃ C : ℝ≥0, ∀ w : SobolevSection A μ p 1, HolderOnWith (C * ‖w‖₊)
      ((1 : ℝ≥0∞) - finrank ℝ E / p).toNNReal (A.coord i (toSection w)) K := by
  set α := ((1 : ℝ≥0∞) - finrank ℝ E / p).toNNReal
  obtain ⟨C, hC⟩ :=
    W1p.exists_forall_holderOnWith_preciseRepresentative_of_isCompact (mu := μ) hp hK hKi
  refine ⟨C * ∑ j, ‖finBasis ℝ F j‖₊, fun w ↦ HolderOnWith.of_dist_le fun x hx y hy ↦ ?_⟩
  set f : Fin (finrank ℝ F) → E → ℝ := fun j ↦ preciseRepresentative μ
    (W1p.value ((w : A.sectionChartData.SobolevData μ p 1) i j))
  rw [eqOn_coord_toSection_chartRep hp w i (hKi hx), eqOn_coord_toSection_chartRep hp w i (hKi hy),
    chartRep, chartRep, dist_eq_norm, ← Finset.sum_sub_distrib]
  calc ‖∑ j, (f j x • finBasis ℝ F j - f j y • finBasis ℝ F j)‖
      ≤ ∑ j, dist (f j x) (f j y) * ‖finBasis ℝ F j‖ := by
        refine (norm_sum_le _ _).trans_eq (Finset.sum_congr rfl fun j _ ↦ ?_)
        rw [← sub_smul, norm_smul, Real.norm_eq_abs, Real.dist_eq]
    _ ≤ ∑ j, C * ‖w‖ * dist x y ^ (α : ℝ) * ‖finBasis ℝ F j‖ := by
        gcongr with j
        refine ((hC _).dist_le hx hy).trans (mul_le_mul_of_nonneg_right ?_ (by positivity))
        have h : ((C * ‖(w : A.sectionChartData.SobolevData μ p 1) i j‖₊ : ℝ≥0) : ℝ) ≤
            C * ‖w‖ := by
          rw [NNReal.coe_mul, coe_nnNorm]
          exact mul_le_mul_of_nonneg_left (SectionChartData.norm_component_le w i j) C.coe_nonneg
        exact h
    _ = ↑((C * ∑ j, ‖finBasis ℝ F j‖₊) * ‖w‖₊) * dist x y ^ (α : ℝ) := by
        simp only [NNReal.coe_mul, NNReal.coe_sum, coe_nnNorm, Finset.mul_sum, Finset.sum_mul]
        exact Finset.sum_congr rfl fun j _ ↦ by ring

/-- **`W^{1,∞}` sections are Lipschitz in charts.** At the endpoint `p = ∞` the Morrey exponent
`1 - n / p` is `1`: on every compact subset `K` of the image of chart `i` the chart expression of
the continuous representative of `w ∈ W^{1,∞}(V)` is Lipschitz with constant `C ‖w‖`, where `C`
depends on `K` but not on `w`. -/
theorem exists_forall_lipschitzOnWith_coord_toSection (i : Fin A.n) {K : Set E}
    (hK : IsCompact K) (hKi : K ⊆ A.image i) :
    ∃ C : ℝ≥0, ∀ w : SobolevSection A μ ∞ 1,
      LipschitzOnWith (C * ‖w‖₊) (A.coord i (toSection w)) K := by
  obtain ⟨C, hC⟩ :=
    exists_forall_holderOnWith_coord_toSection (μ := μ) (ENNReal.natCast_lt_top _) i hK hKi
  refine ⟨C, fun w ↦ holderOnWith_one.1 ?_⟩
  simpa only [ENNReal.div_top, tsub_zero, ENNReal.toNNReal_one] using hC w

/-- **Morrey's embedding for Sobolev sections, as a bounded operator into a Hölder space.** For
`n < p ≤ ∞`, where `n` is the dimension, and a compact subset `K` of the image of chart `i`,
restricting to `K` the chart expression of the continuous representative is a continuous linear map
from `W^{1,p}(V)` to the Banach space `C^{0,α}(K; F)` of `α`-Hölder functions, `α = 1 - n / p`,
with its supremum-plus-Hölder norm (`TauCeti.HolderSpace`). -/
def morreyEmbedding (hp : (finrank ℝ E : ℝ≥0∞) < p) (i : Fin A.n) (K : Set E) [CompactSpace K]
    (hKi : K ⊆ A.image i) :
    SobolevSection A μ p 1 →L[ℝ] HolderSpace ((1 : ℝ≥0∞) - finrank ℝ E / p).toNNReal K F :=
  coordHolderL (.of_finrank_lt hp) i K hKi
    (exists_forall_holderOnWith_coord_toSection hp i (isCompact_iff_compactSpace.2 ‹_›) hKi)

@[simp]
theorem morreyEmbedding_apply_apply (hp : (finrank ℝ E : ℝ≥0∞) < p) (i : Fin A.n) (K : Set E)
    [CompactSpace K] (hKi : K ⊆ A.image i) (w : SobolevSection A μ p 1) (y : K) :
    morreyEmbedding hp i K hKi w y = A.coord i (toSection w) y :=
  coordHolderL_apply_apply _ i K hKi _ w y

/-- **Compactness of Morrey's embedding.** For `n < p ≤ ∞`, where `n` is the dimension, and every
exponent `β < 1 - n / p`, the embedding of `W^{1,p}(V)` into the Hölder space `C^{0,β}(K; F)` on a
compact subset `K` of the image of chart `i` is a compact operator: it is
`TauCeti.SobolevSection.morreyEmbedding` followed by the compact inclusion
`C^{0,α}(K; F) → C^{0,β}(K; F)` of `TauCeti.HolderSpace.isCompactOperator_inclusionL`. -/
theorem isCompactOperator_inclusionL_comp_morreyEmbedding (hp : (finrank ℝ E : ℝ≥0∞) < p)
    (i : Fin A.n) (K : Set E) [CompactSpace K] (hKi : K ⊆ A.image i) {β : ℝ≥0}
    (hβ : β < ((1 : ℝ≥0∞) - finrank ℝ E / p).toNNReal) :
    IsCompactOperator ((HolderSpace.inclusionL (X := K) (Y := F) hβ.le).comp
      (morreyEmbedding (μ := μ) hp i K hKi)) :=
  isCompactOperator_inclusionL_comp_coordHolderL _ i K hKi _ hβ

end SobolevSection

end General

/-! ### Every order over surfaces -/

section Surface

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M] [IsManifold 𝓘(ℝ, ℂ) 1 M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)] [∀ x, AddCommGroup (V x)]
  [∀ x, Module ℝ (V x)] [∀ x, TopologicalSpace (V x)] [FiberBundle F V] [VectorBundle ℝ F V]
  {A : FiniteBundleAtlas ℂ M F V} {p : ℝ≥0∞} [Fact (1 ≤ p)] {k : ℕ}

namespace SobolevSection

open FiniteBundleAtlas

/-- **Morrey's embedding for Sobolev sections over surfaces: continuous representatives.** For
`1 ≤ p ≤ ∞` and `2 < k p`, every element `w` of `W^{k,p}(V)` has a continuous representative: a
continuous section `s` of `V` whose chart expression `A.coord i s` agrees, for every chart `i`,
almost everywhere on `A.image i` with the chart data of `w`. -/
theorem HasContinuousRepresentatives.of_two_lt_mul (hkp : 2 < (k : ℝ≥0∞) * p) :
    HasContinuousRepresentatives A volume p k := by
  intro w
  obtain ⟨s, hs⟩ := exists_ae_eq_coord w
  -- The precise representatives of the chart expressions glue to a continuous section.
  obtain ⟨t, ht, hts⟩ := exists_continuous_coord_eqOn_of_ae_eq (μ := volume)
    (fun i ↦ (memWkpLoc_coord w hs i).continuousOn_preciseRepresentative_of_two_lt_mul
      Fact.out hkp)
    fun i ↦ (memWkpLoc_coord w hs i).memLpLoc.ae_eq_preciseRepresentative Fact.out
  refine ⟨t, ht, fun i ↦ ?_⟩
  filter_upwards [hs i, (memWkpLoc_coord w hs i).memLpLoc.ae_eq_preciseRepresentative Fact.out,
    ae_restrict_mem (A.image i).isOpen.measurableSet] with y hy hy' hyU
  rw [hy, hy', hts i hyU]

/-- The chart expressions of the continuous representative are, on the chart images, the precise
representatives of the chart expressions of any section whose coordinates are the chart data. -/
theorem eqOn_coord_toSection (hkp : 2 < (k : ℝ≥0∞) * p) {w : SobolevSection A volume p k}
    {s : ∀ x, V x}
    (hs : ∀ i, A.sectionChartData.chartValueL volume p k i w
      =ᵐ[volume.restrict (A.image i)] A.coord i s)
    (i : Fin A.n) :
    EqOn (A.coord i (toSection w)) (preciseRepresentative volume (A.coord i s))
      (A.image i) := by
  have hu := memWkpLoc_coord w hs i
  refine (eqOn_preciseRepresentative_of_continuousOn (A.image i).isOpen
    (hu.memLpLoc.locallyIntegrableOn Fact.out (A.image i).isOpen.isLocallyClosed) ?_
    (A.continuousOn_coord (continuous_toSection (.of_two_lt_mul hkp) w) i)).symm
  exact (hs i).symm.trans (chartValueL_ae_eq_coord_toSection (.of_two_lt_mul hkp) w i)

/-- **Morrey's embedding for Sobolev sections over surfaces: Hölder continuity in charts.** For
`2 < p ≤ ∞` and `2 < k p`, the chart expression of the continuous representative of an element of
`W^{k,p}(V)` is Hölder continuous with exponent `1 - 2 / p` on every compact subset of the chart
image. -/
theorem exists_holderOnWith_coord_toSection (hkp : 2 < (k : ℝ≥0∞) * p) (hp : 2 < p)
    (w : SobolevSection A volume p k) (i : Fin A.n) {K : Set ℂ} (hK : IsCompact K)
    (hKi : K ⊆ A.image i) :
    ∃ C : ℝ≥0, HolderOnWith C ((1 : ℝ≥0∞) - 2 / p).toNNReal (A.coord i (toSection w)) K := by
  have hk : 1 ≤ k := Nat.one_le_iff_ne_zero.2 fun hk ↦ by simp [hk] at hkp
  obtain ⟨s, hs⟩ := exists_ae_eq_coord w
  obtain ⟨C, hC⟩ := ((memWkpLoc_coord w hs i).of_le
    hk).exists_holderOnWith_preciseRepresentative_of_isCompact hp hK hKi
  refine ⟨C, fun x hx y hy ↦ ?_⟩
  rw [eqOn_coord_toSection hkp hs i (hKi hx), eqOn_coord_toSection hkp hs i (hKi hy)]
  exact hC x hx y hy

/-- **Check.** `W^{2,3/2}(V)` lies below the exponent `2` of `W^{1,p}`, but `2 · 3/2 = 3 > 2`, so
its elements have continuous representatives. -/
example [Fact (1 ≤ (3 / 2 : ℝ≥0∞))] (w : SobolevSection A volume (3 / 2) 2) :
    Continuous fun x ↦ TotalSpace.mk' F x (toSection w x) :=
  continuous_toSection (.of_two_lt_mul (by
    rw [Nat.cast_ofNat, ENNReal.mul_div_cancel two_ne_zero ENNReal.ofNat_ne_top]
    norm_num)) w

end SobolevSection

end Surface

end TauCeti
