/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.BumpFunction.Normed
public import TauCeti.Analysis.Distribution.WaveFrontSet.Basic
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Haar.Unique
import TauCeti.Analysis.Calculus.BumpFunction.Normed
import TauCeti.Analysis.Calculus.FDeriv.Submodule
import TauCeti.Analysis.InnerProductSpace.ProdL2
import TauCeti.MeasureTheory.Constructions.BorelSpace.Basic

/-!
# Measures on subspaces fail the pullback criterion

A distribution `T` on an open set of `E'` has a pullback along a smooth map `f` when its wave
front set misses the *normal set* of `f`, the covectors `(f x, η)` with `η ≠ 0` and
`Df(x)ᵀ η = 0` (`Distribution.pullback`; for the inclusion of `E × {0}`,
`Distribution.pullbackInl`). This file shows that the criterion genuinely excludes the
restriction of a measure on a subspace to that subspace.

If `f` maps a neighbourhood of `x` into a subspace `V`, then `Df(x)ᵀ` vanishes on `Vᗮ`
(`TauCeti.adjoint_fderiv_apply_eq_zero_of_eventually_mem`), so the normal set of `f` at `x`
contains every nonzero covector conormal to `V`. The surface measure of `V` has exactly these
covectors as its wave front set over `V` (`Distribution.waveFrontSet_ofFun_one_map_subtype`). So,
for a proper subspace `V`, the criterion fails at every point for every map into `V`
(`Distribution.not_forall_adjoint_fderiv_apply_ne_zero_ofFun_one_map_subtype`).

The basic instance is `δ(x - y)`, the distribution `φ ↦ ∫ φ (x, x) dx` on `E × E` carried by the
diagonal. Its wave front set consists of the covectors `((x, x), (η, -η))` with `η ≠ 0`, conormal
to the diagonal (`Distribution.waveFrontSet_ofFun_one_map_diagonal`), and the transpose of the
derivative of the diagonal map `x ↦ (x, x)` is `(ξ, η) ↦ ξ + η`, which sends each of them to `0`
(`Distribution.mem_waveFrontSet_ofFun_one_map_diagonal_and_adjoint_fderiv_apply_eq_zero`).
So the pullback criterion does not allow `δ(x - y)` to be restricted to the diagonal.

Without the criterion the limit defining the pullback need not exist. For the surface measure
`T = 1 ⊗ δ₀` of `E × {0}`, the values `T (ψ ⊗ ρ) = (∫ ψ) ρ 0` on the test functions
`(x, y) ↦ ψ x ρ y` are unbounded as normalized bumps `ρ` concentrate at `0` and `∫ ψ ≠ 0`
(`Distribution.tendsto_norm_ofFun_one_map_inl_atTop`), whereas under the criterion they converge
to the pullback (`Distribution.tendsto_pullbackInl`). Any value assigned to such a restriction
is therefore a choice, a renormalization, not a limit of these approximations.

## Main results

* `Distribution.exists_mem_waveFrontSet_ofFun_one_map_subtype_and_adjoint_fderiv_apply_eq_zero`,
  `Distribution.not_forall_adjoint_fderiv_apply_ne_zero_ofFun_one_map_subtype`: the surface
  measure of a proper subspace fails the pullback criterion along every map into it.
* `Distribution.waveFrontSet_ofFun_one_map_diagonal`: the wave front set of `δ(x - y)`.
* `Distribution.mem_waveFrontSet_ofFun_one_map_diagonal_and_adjoint_fderiv_apply_eq_zero`:
  `δ(x - y)` fails the pullback criterion along the diagonal map at every covector over the
  diagonal.
* `Distribution.tendsto_norm_ofFun_one_map_inl_atTop`: the approximations of the restriction of
  `1 ⊗ δ₀` to `E × {0}` are unbounded.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators I*, second edition,
  Springer, 1990, Theorem 8.2.4 (the pullback criterion).
* C. Brouder, N. V. Dang, F. Hélein, *Continuity of the fundamental operations on distributions
  having a specified wave front set*, arXiv:1409.7662v2, Proposition 5.1.
-/

public section

noncomputable section

open Filter Function MeasureTheory Set TopologicalSpace WithLp
open scoped Distributions Topology RealInnerProductSpace ContDiff

namespace Distribution

variable {E E' : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup E'] [InnerProductSpace ℝ E']

/-! ### Maps into a subspace -/

section Subspace

variable [CompleteSpace E] [FiniteDimensional ℝ E'] [MeasurableSpace E'] [BorelSpace E']

/-- **The surface measure of a subspace fails the pullback criterion along maps into it.** Let
`V` be a proper subspace of `E'`, and `f` a map sending a neighbourhood of `x` into `V`, with
`f x` in the open set `Ω'`. Then some covector of the wave front set of the surface measure of
`V` on `Ω'` over `f x` lies in the normal set of `f`: the transpose of `Df(x)` sends it to `0`. -/
theorem exists_mem_waveFrontSet_ofFun_one_map_subtype_and_adjoint_fderiv_apply_eq_zero
    {V : Submodule ℝ E'} (hV : V ≠ ⊤) {Ω' : Opens E'} {f : E → E'} {x : E}
    (hf : ∀ᶠ y in 𝓝 x, f y ∈ V) (hx : f x ∈ Ω') :
    ∃ η, (f x, η) ∈ (ofFun Ω' 1 (volume.map ((↑) : V → E')) ⊤).waveFrontSet ∧
      (fderiv ℝ f x).adjoint η = 0 := by
  obtain ⟨η, hη, hη0⟩ :=
    Submodule.exists_mem_ne_zero_of_ne_bot (Submodule.orthogonal_eq_bot_iff.not.2 hV)
  refine ⟨η, ?_, TauCeti.adjoint_fderiv_apply_eq_zero_of_eventually_mem hf hη⟩
  rw [waveFrontSet_ofFun_one_map_subtype]
  exact ⟨⟨hx, hf.self_of_nhds⟩, hη, hη0⟩

/-- **The pullback criterion fails for the surface measure of a subspace.** For a proper subspace
`V` of `E'` and a map `f` sending a nonempty open set `Ω` into `V ∩ Ω'`, the wave front set of the
surface measure of `V` on `Ω'` meets the normal set of `f`: the hypothesis of
`Distribution.pullback` fails. -/
theorem not_forall_adjoint_fderiv_apply_ne_zero_ofFun_one_map_subtype {V : Submodule ℝ E'}
    (hV : V ≠ ⊤) {Ω : Opens E} {Ω' : Opens E'} {f : E → E'} (hfΩ : MapsTo f Ω Ω')
    (hfV : MapsTo f Ω V) (hΩ : (Ω : Set E).Nonempty) :
    ¬ ∀ x ∈ Ω, ∀ η, (f x, η) ∈ (ofFun Ω' 1 (volume.map ((↑) : V → E')) ⊤).waveFrontSet →
      (fderiv ℝ f x).adjoint η ≠ 0 := by
  obtain ⟨x, hx⟩ := hΩ
  obtain ⟨η, hη, h0⟩ :=
    exists_mem_waveFrontSet_ofFun_one_map_subtype_and_adjoint_fderiv_apply_eq_zero hV
      (mem_of_superset (Ω.isOpen.mem_nhds hx) hfV) (hfΩ hx)
  exact fun h ↦ h x hx η hη h0

end Subspace

/-! ### The diagonal delta `δ(x - y)` -/

section Diagonal

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [MeasurableSpace (WithLp 2 (E × E))] [BorelSpace (WithLp 2 (E × E))]

/-- `δ(x - y)` is a nonzero multiple of the surface measure of the diagonal: Lebesgue measure of
`E` pushed forward along `x ↦ (x, x)` is a positive multiple of the surface measure of the
diagonal, by uniqueness of Haar measure on the diagonal. -/
private theorem exists_ofFun_one_map_diagonal_eq_smul (Ω : Opens (WithLp 2 (E × E))) :
    ∃ c : ℂ, c ≠ 0 ∧ ofFun Ω (1 : WithLp 2 (E × E) → ℂ) (volume.map fun x : E ↦ toLp 2 (x, x)) ⊤ =
      c • ofFun Ω 1 (volume.map ((↑) : diagonal 2 ℝ E → WithLp 2 (E × E))) ⊤ := by
  set e := diagonalEquiv 2 ℝ E
  have hd : (fun x : E ↦ toLp 2 (x, x)) = ((↑) : diagonal 2 ℝ E → WithLp 2 (E × E)) ∘ e := by
    funext x
    simp [e]
  set c := Measure.addHaarScalarFactor (volume.map e) volume
  have hμ : volume.map (fun x : E ↦ toLp 2 (x, x)) =
      c • volume.map ((↑) : diagonal 2 ℝ E → WithLp 2 (E × E)) := by
    rw [hd, ← Measure.map_map measurable_subtypeVal e.continuous.measurable,
      congrArg (Measure.map _) (Measure.isAddLeftInvariant_eq_smul (volume.map e) volume),
      Measure.map_smul]
    exact measurable_subtypeVal.aemeasurable
  have hce : Topology.IsClosedEmbedding ((↑) : diagonal 2 ℝ E → WithLp 2 (E × E)) :=
    (diagonal 2 ℝ E).isClosedEmbedding_subtype (diagonal 2 ℝ E).isClosed_of_finiteDimensional
  have := Measure.isFiniteMeasureOnCompacts_map_of_isProperMap volume hce.isProperMap
  refine ⟨((c : ℝ) : ℂ), by exact_mod_cast
    (Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure (volume.map e) volume).ne', ?_⟩
  ext φ
  rw [hμ, ofFun_apply (f := 1) ((locallyIntegrable_const 1).locallyIntegrableOn _), smul_apply,
    ofFun_apply (f := 1) ((locallyIntegrable_const 1).locallyIntegrableOn _)]
  simp [integral_smul_nnreal_measure, NNReal.smul_def]

/-- **The wave front set of `δ(x - y)`.** The distribution `φ ↦ ∫ φ (x, x) dx` on an open set `Ω`
of `E × E`, carried by the diagonal, is singular exactly at the points `(x, x)` of the diagonal in
`Ω`, and there exactly in the nonzero directions `(η, -η)`, conormal to the diagonal. -/
theorem waveFrontSet_ofFun_one_map_diagonal (Ω : Opens (WithLp 2 (E × E))) :
    (ofFun Ω 1 (volume.map fun x : E ↦ toLp 2 (x, x)) ⊤).waveFrontSet =
      {q | q.1 ∈ Ω ∧ q.1.fst = q.1.snd ∧ q.2 ≠ 0 ∧ q.2.snd = -q.2.fst} := by
  obtain ⟨c, hc, h⟩ := exists_ofFun_one_map_diagonal_eq_smul (E := E) Ω
  rw [h, waveFrontSet_smul hc, waveFrontSet_ofFun_one_map_subtype]
  ext ⟨p, ζ⟩
  simp only [mem_prod, mem_inter_iff, SetLike.mem_coe, Set.mem_sdiff, mem_singleton_iff,
    WithLp.mem_diagonal_iff, mem_orthogonal_diagonal_iff, mem_ofPred_eq]
  tauto

/-- **`δ(x - y)` fails the pullback criterion along the diagonal.** At every point `(x, x)` of
the diagonal in `Ω` and for every `η ≠ 0`, the covector `(η, -η)` lies in the wave front set of
`δ(x - y)`, and the transpose `(ξ, ζ) ↦ ξ + ζ` of the derivative of the diagonal map `x ↦ (x, x)`
sends it to `0`. So the wave front set of `δ(x - y)` meets the normal set of the diagonal map at
every point of the diagonal, and the hypothesis of `Distribution.pullback` fails. -/
theorem mem_waveFrontSet_ofFun_one_map_diagonal_and_adjoint_fderiv_apply_eq_zero
    {Ω : Opens (WithLp 2 (E × E))} {x : E} (hx : toLp 2 (x, x) ∈ Ω) {η : E} (hη : η ≠ 0) :
    (toLp 2 (x, x), toLp 2 (η, -η)) ∈
        (ofFun Ω 1 (volume.map fun x : E ↦ toLp 2 (x, x)) ⊤).waveFrontSet ∧
      (fderiv ℝ (fun x : E ↦ toLp 2 (x, x)) x).adjoint (toLp 2 (η, -η)) = 0 := by
  refine ⟨?_, TauCeti.adjoint_fderiv_apply_eq_zero_of_eventually_mem (V := diagonal 2 ℝ E)
    (Eventually.of_forall fun y ↦ WithLp.mem_diagonal_iff.2 rfl)
    (mem_orthogonal_diagonal_iff.2 rfl)⟩
  rw [waveFrontSet_ofFun_one_map_diagonal]
  exact ⟨hx, rfl, fun h ↦ hη (by simpa using congrArg WithLp.fst h), rfl⟩

end Diagonal

/-! ### Divergence of the approximations without the criterion -/

section Divergence

variable [FiniteDimensional ℝ E] {D : Type*} [NormedAddCommGroup D] [InnerProductSpace ℝ D]
  [FiniteDimensional ℝ D] [MeasurableSpace E] [BorelSpace E] [MeasurableSpace D] [BorelSpace D]
  [MeasurableSpace (WithLp 2 (E × D))] [BorelSpace (WithLp 2 (E × D))]

/-- **Without the wave front hypothesis the restriction to `E × {0}` need not exist.** Let `T` be
the measure `φ ↦ ∫ φ (x, 0) dx` of `E × {0}`, that is `1 ⊗ δ₀`, on an open set `W` of `E × D` with
`D` nontrivial. If `∫ ψ ≠ 0` and `f i` are the test functions `(x, y) ↦ ψ x ρ i y` for normalized
bumps `ρ i` centred at `0` whose radii tend to zero, then `T (f i) = (∫ ψ) ρ i 0` is unbounded. So,
unlike `Distribution.tendsto_pullbackInl` under the wave front hypothesis, these approximations of
the restriction of `T` to `E × {0}` have no limit. Such families exist for every test function `ψ`
on an open set `U` with `U × {0} ⊆ W` (`Distribution.exists_seq_tensor_mollifier`). -/
theorem tendsto_norm_ofFun_one_map_inl_atTop [Nontrivial D] {W : Opens (WithLp 2 (E × D))}
    {ψ : E → ℝ} (hψ : ∫ x, ψ x ≠ 0) {ι : Type*} {l : Filter ι} {σ : ι → ContDiffBump (0 : D)}
    (hσ : Tendsto (fun i ↦ (σ i).rOut) l (𝓝 0)) {f : ι → 𝓓(W, ℝ)}
    (hf : ∀ i p, f i p = ψ p.fst * (σ i).normed volume p.snd) :
    Tendsto (fun i ↦ ‖ofFun W (1 : WithLp 2 (E × D) → ℂ)
      (volume.map fun x : E ↦ toLp 2 (x, (0 : D))) ⊤ (f i)‖) l atTop := by
  set g : E → WithLp 2 (E × D) := fun x ↦ toLp 2 (x, 0)
  have hg : Topology.IsClosedEmbedding g :=
    (show LeftInverse WithLp.fst g from fun _ ↦ rfl).isClosedEmbedding
      (WithLp.continuous_fst 2 E D) (by fun_prop)
  have := Measure.isFiniteMeasureOnCompacts_map_of_isProperMap volume hg.isProperMap
  have hval (i : ι) : ‖ofFun W (1 : WithLp 2 (E × D) → ℂ) (volume.map g) ⊤ (f i)‖ =
      (σ i).normed volume 0 * |∫ x, ψ x| := by
    rw [ofFun_apply (f := 1) ((locallyIntegrable_const 1).locallyIntegrableOn _),
      hg.measurableEmbedding.integral_map]
    simp [g, hf, integral_complex_ofReal, integral_mul_const,
      abs_of_nonneg ((σ i).nonneg_normed 0), mul_comm]
  simp_rw [hval]
  exact (ContDiffBump.tendsto_normed_center_atTop volume hσ).atTop_mul_const (abs_pos.2 hψ)

end Divergence

end Distribution
