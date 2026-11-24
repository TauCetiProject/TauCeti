/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.MetricSpace.Holder
public import TauCeti.Analysis.Complex.Wirtinger.InteriorEstimate
import TauCeti.Analysis.Complex.Wirtinger.Precompact
import TauCeti.Analysis.Sobolev.Morrey.Basic
import TauCeti.Topology.ContinuousMap.Ascoli

/-!
# Hölder bounds and compactness from `Lᵖ` bounds on `\bar∂`, `p > 2`

Let `2 < p < ∞` and let `U ⊆ ℂ` be open. For a map `u` smooth on `U` with values in a complex
Hilbert space, the interior Calderón–Zygmund estimate
(`TauCeti.exists_eLpNorm_fderiv_le_eLpNorm_conjWirtingerDeriv_add_eLpNorm`) bounds the `Lᵖ` norm
of the derivative of `u` on a compact subset of `U` by the `Lᵖ(U)` norms of `\bar∂u` and `u`, and
Morrey's inequality (`TauCeti.exists_edist_le_of_contDiffOn_cthickening_of_two_lt`) turns an
`Lᵖ` bound on the derivative, `p > 2`, into a Hölder bound of exponent `1 - 2 / p`. Together they
give a local Hölder estimate controlled by `\bar∂u` and `u` alone
(`TauCeti.exists_edist_le_eLpNorm_conjWirtingerDeriv_add_eLpNorm`): for `K ⊆ U` compact there are
`C` and `δ > 0` with

`‖u x - u y‖ ≤ C (‖\bar∂u‖_{Lᵖ(U)} + ‖u‖_{Lᵖ(U)}) |x - y| ^ (1 - 2 / p)`

for all `x ∈ K` and `|x - y| < δ`.

A family of maps that is bounded on compact subsets of `U`, and whose `\bar∂` is bounded in `Lᵖ`
on compact subsets of `U`, is Hölder continuous of exponent `1 - 2 / p` on each compact subset
with a common constant (`TauCeti.exists_holderOnWith_of_eLpNorm_conjWirtingerDeriv_le`): apply
`TauCeti.exists_holderOnWith_of_norm_conjWirtingerDeriv_sub_le` on a thickening of that subset.
By the Arzelà–Ascoli theorem for locally Hölder families
(`TauCeti.exists_subseq_tendstoLocallyUniformlyOn_of_holderOnWith`) a sequence of such maps, with
values in a proper space, has a subsequence converging locally uniformly on `U`; the limit is
continuous on `U` and Hölder of the same exponent on each compact subset
(`TauCeti.exists_subseq_tendstoLocallyUniformlyOn_of_eLpNorm_conjWirtingerDeriv_le`).

The bounds here are only required on compact subsets of `U`. Families bounded on all of `U`, with
`\bar∂u` bounded in `Lᵖ(U)` up to a bounded error, as in
`TauCeti.Analysis.Complex.Wirtinger.Precompact`, are a special case
(`TauCeti.exists_strictMono_tendstoLocallyUniformlyOn_of_norm_conjWirtingerDeriv_sub_le`).

This is the compactness step for functions solving a scalar Cauchy–Riemann equation with an `Lᵖ`
forcing, such as `\bar∂b = -ν b + f` with `ν` bounded and `f` bounded in `Lᵖ`. For `p = 2 + 2 / m`
the Hölder exponent `1 - 2 / p` is `1 / (m + 1)`. This is the exponent that arises if the symmetric
coefficients of the local branches of Seiberg–Witten solutions concentrating along a
pseudoholomorphic curve, the setting of Taubes's *SW ⇒ Gr*, satisfy such equations with that `p`;
no such equation is proved here.

## Main results

* `TauCeti.exists_edist_le_eLpNorm_conjWirtingerDeriv_add_eLpNorm`: the local Hölder estimate.
* `TauCeti.exists_holderOnWith_of_eLpNorm_conjWirtingerDeriv_le`: a common Hölder constant on each
  compact subset for a family with locally bounded values and locally `Lᵖ`-bounded `\bar∂`.
* `TauCeti.exists_subseq_tendstoLocallyUniformlyOn_of_eLpNorm_conjWirtingerDeriv_le`: a sequence
  of such maps has a locally uniformly convergent subsequence with a locally Hölder limit.
* `TauCeti.exists_strictMono_tendstoLocallyUniformlyOn_of_norm_conjWirtingerDeriv_sub_le`: the
  same conclusion for families bounded on `U` with `\bar∂` bounded in `Lᵖ(U)` up to a bounded
  error.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Appendix B (the Calderón–Zygmund inequality and its use with Morrey's embedding).
* C. H. Taubes, *SW ⇒ Gr: from the Seiberg–Witten equations to pseudo-holomorphic curves*,
  J. Amer. Math. Soc. 9 (1996), 845–918.
-/

public section

open MeasureTheory Metric Set Filter Topology
open scoped ENNReal NNReal ContDiff

namespace TauCeti

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- **Local Hölder estimate from the Cauchy–Riemann operator.** Let `2 < p < ∞`, let `U ⊆ ℂ` be
open and let `K ⊆ U` be compact. There are a constant `C` and a radius `δ > 0` such that every map
`u` smooth on `U`, with values in a complex Hilbert space, satisfies

`‖u x - u y‖ ≤ C (‖\bar∂u‖_{Lᵖ(U)} + ‖u‖_{Lᵖ(U)}) |x - y| ^ (1 - 2 / p)`

for all `x ∈ K` and all `y` with `|x - y| < δ`. -/
theorem exists_edist_le_eLpNorm_conjWirtingerDeriv_add_eLpNorm {p : ℝ≥0} (hp : 2 < p)
    {U K : Set ℂ} (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U) :
    ∃ C : ℝ≥0, ∃ δ : ℝ≥0, 0 < δ ∧ ∀ u : ℂ → F, ContDiffOn ℝ ∞ u U → ∀ x ∈ K, ∀ y,
      dist x y < δ → edist (u x) (u y) ≤
        C * (eLpNorm (fun z ↦ conjWirtingerDeriv u z 1) p (volume.restrict U) +
          eLpNorm u p (volume.restrict U)) * edist x y ^ ((1 - 2 / p : ℝ≥0) : ℝ) := by
  obtain ⟨δ₀, hδ₀, hδ₀U⟩ := hK.exists_cthickening_subset_open hU hKU
  have hp₁ : (1 : ℝ≥0∞) < p := by exact_mod_cast one_lt_two.trans hp
  obtain ⟨C₁, hC₁⟩ := exists_eLpNorm_fderiv_le_eLpNorm_conjWirtingerDeriv_add_eLpNorm (F := F)
    hp₁ ENNReal.coe_ne_top hU hK.cthickening hδ₀U
  obtain ⟨M, hM⟩ := exists_edist_le_of_contDiffOn_cthickening_of_two_lt (F := F) hp
  refine ⟨M * C₁, (δ₀ / 2).toNNReal, by simpa using hδ₀, fun u hu x hx y hxy ↦ ?_⟩
  have hxy' : 2 * dist x y ≤ δ₀ := by
    rw [Real.coe_toNNReal _ (half_pos hδ₀).le] at hxy
    linarith
  -- Morrey's inequality on the `δ₀`-thickening of `K`, then the interior estimate there.
  calc edist (u x) (u y)
    _ ≤ M * edist x y ^ ((1 - 2 / p : ℝ≥0) : ℝ) *
          eLpNorm (fderiv ℝ u) p (volume.restrict (cthickening δ₀ K)) :=
      hM ((hu.mono hδ₀U).of_le (by exact_mod_cast le_top)) hx hxy'
    _ ≤ M * edist x y ^ ((1 - 2 / p : ℝ≥0) : ℝ) *
          (C₁ * (eLpNorm (fun z ↦ conjWirtingerDeriv u z 1) p (volume.restrict U) +
            eLpNorm u p (volume.restrict U))) := by
      gcongr
      exact hC₁ u hu
    _ = _ := by
      rw [ENNReal.coe_mul]
      ring

/-- **A common Hölder constant on compact sets.** Let `2 < p < ∞` and let `U ⊆ ℂ` be open. Let
`u i` be maps smooth on `U`, with values in a complex Hilbert space, that are bounded on each
compact subset of `U` uniformly in `i`, and whose conjugate Wirtinger derivatives `\bar∂(u i)` are
bounded in `Lᵖ` on each compact subset of `U` uniformly in `i`. Then on each compact `K ⊆ U` the
maps `u i` are Hölder continuous of exponent `1 - 2 / p` with a common constant. -/
theorem exists_holderOnWith_of_eLpNorm_conjWirtingerDeriv_le {ι : Type*} {p : ℝ≥0} (hp : 2 < p)
    {U : Set ℂ} (hU : IsOpen U) {u : ι → ℂ → F} (hu : ∀ i, ContDiffOn ℝ ∞ (u i) U)
    (hbdd : ∀ K ⊆ U, IsCompact K → ∃ B : ℝ, ∀ i, ∀ z ∈ K, ‖u i z‖ ≤ B)
    (hdbar : ∀ K ⊆ U, IsCompact K → ∃ A : ℝ≥0∞, A ≠ (∞ : ℝ≥0∞) ∧
      ∀ i, eLpNorm (fun z ↦ conjWirtingerDeriv (u i) z 1) p (volume.restrict K) ≤ A)
    {K : Set ℂ} (hK : IsCompact K) (hKU : K ⊆ U) :
    ∃ C : ℝ≥0, ∀ i, HolderOnWith C (1 - 2 / p) (u i) K := by
  -- Apply the uniform Hölder bound on the open `δ₀`-thickening `V` of `K`, whose closure is a
  -- compact subset of `U`, with `g = \bar∂(u i)` and no error term.
  obtain ⟨δ₀, hδ₀, hδ₀U⟩ := hK.exists_cthickening_subset_open hU hKU
  have hVK' : thickening δ₀ K ⊆ cthickening δ₀ K := thickening_subset_cthickening δ₀ K
  obtain ⟨A, hA, hAle⟩ := hdbar _ hδ₀U hK.cthickening
  obtain ⟨B, hB⟩ := hbdd _ hδ₀U hK.cthickening
  obtain ⟨C, hC⟩ := exists_holderOnWith_of_norm_conjWirtingerDeriv_sub_le (F := F) hp
    isOpen_thickening hK (self_subset_thickening hδ₀ K) B.toNNReal 0 A.toNNReal
  refine ⟨C, fun i ↦ hC (u i) (fun z ↦ conjWirtingerDeriv (u i) z 1)
    ((hu i).mono (hVK'.trans hδ₀U)) (fun z hz ↦ (hB i z (hVK' hz)).trans B.le_coe_toNNReal)
    (fun z _ ↦ by simp) ?_⟩
  rw [ENNReal.coe_toNNReal hA]
  exact (eLpNorm_mono_measure _ (Measure.restrict_mono hVK' le_rfl)).trans (hAle i)

/-- **Compactness from `Lᵖ` bounds on `\bar∂`, `p > 2`.** Let `2 < p < ∞`, let `U ⊆ ℂ` be open,
and let `u n` be maps smooth on `U`, with values in a proper complex Hilbert space, that are bounded
on each compact subset of `U` uniformly in `n`, and whose conjugate Wirtinger derivatives
`\bar∂(u n)` are bounded in `Lᵖ` on each compact subset of `U` uniformly in `n`. Then a subsequence
of the `u n` converges locally uniformly on `U` to a map `v` that is continuous on `U` and Hölder
continuous of exponent `1 - 2 / p` on each compact subset of `U`. -/
theorem exists_subseq_tendstoLocallyUniformlyOn_of_eLpNorm_conjWirtingerDeriv_le [ProperSpace F]
    {p : ℝ≥0} (hp : 2 < p) {U : Set ℂ} (hU : IsOpen U) {u : ℕ → ℂ → F}
    (hu : ∀ n, ContDiffOn ℝ ∞ (u n) U)
    (hbdd : ∀ K ⊆ U, IsCompact K → ∃ B : ℝ, ∀ n, ∀ z ∈ K, ‖u n z‖ ≤ B)
    (hdbar : ∀ K ⊆ U, IsCompact K → ∃ A : ℝ≥0∞, A ≠ (∞ : ℝ≥0∞) ∧
      ∀ n, eLpNorm (fun z ↦ conjWirtingerDeriv (u n) z 1) p (volume.restrict K) ≤ A) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ v : ℂ → F, ContinuousOn v U ∧
      TendstoLocallyUniformlyOn (fun n ↦ u (φ n)) v atTop U ∧
      ∀ K ⊆ U, IsCompact K → ∃ C : ℝ≥0, HolderOnWith C (1 - 2 / p) v K := by
  have hholder := fun K (hKU : K ⊆ U) (hK : IsCompact K) ↦
    exists_holderOnWith_of_eLpNorm_conjWirtingerDeriv_le hp hU hu hbdd hdbar hK hKU
  -- At each point the values lie in a closed ball, which is compact since `F` is proper.
  have hpt (x : ℂ) (hx : x ∈ U) : ∃ Q, IsCompact Q ∧ ∀ n, u n x ∈ Q := by
    obtain ⟨B, hB⟩ := hbdd {x} (singleton_subset_iff.2 hx) isCompact_singleton
    exact ⟨closedBall 0 B, isCompact_closedBall _ _,
      fun n ↦ mem_closedBall_zero_iff.2 (hB n x rfl)⟩
  obtain ⟨φ, hφ, v, hv, hconv, hlim⟩ := exists_subseq_tendstoLocallyUniformlyOn_of_holderOnWith hU
    (tsub_pos_of_lt ((div_lt_one (two_pos.trans hp)).2 hp)) hholder hpt
  refine ⟨φ, hφ, v, hv, hconv, fun K hKU hK ↦ ?_⟩
  obtain ⟨C, hC⟩ := hholder K hKU hK
  exact ⟨C, hlim K hKU C hC⟩

/-- **Locally uniformly convergent subsequences under global bounds.** Let `2 < p < ∞`, let
`U ⊆ ℂ` be open and let `u n` be maps smooth on `U` into a proper complex Hilbert space, with
`‖u n‖ ≤ A` on `U` and `‖\bar∂(u n) - g n‖ ≤ M` on `U` for some `g n` with `‖g n‖_{Lᵖ(U)} ≤ B`.
Then a subsequence of `u n` converges locally uniformly on `U` to a map `v` that is continuous on
`U` and Hölder continuous of exponent `1 - 2 / p` on each compact subset of `U`. -/
theorem exists_strictMono_tendstoLocallyUniformlyOn_of_norm_conjWirtingerDeriv_sub_le
    [ProperSpace F] {p : ℝ≥0} (hp : 2 < p) {U : Set ℂ} (hU : IsOpen U) {A M B : ℝ≥0}
    {u g : ℕ → ℂ → F} (hu : ∀ n, ContDiffOn ℝ ∞ (u n) U) (hA : ∀ n, ∀ z ∈ U, ‖u n z‖ ≤ A)
    (hM : ∀ n, ∀ z ∈ U, ‖conjWirtingerDeriv (u n) z 1 - g n z‖ ≤ M)
    (hB : ∀ n, eLpNorm (g n) p (volume.restrict U) ≤ B) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ v : ℂ → F, ContinuousOn v U ∧
      TendstoLocallyUniformlyOn (fun n ↦ u (φ n)) v atTop U ∧
      ∀ K ⊆ U, IsCompact K → ∃ C : ℝ≥0, HolderOnWith C (1 - 2 / p) v K := by
  refine exists_subseq_tendstoLocallyUniformlyOn_of_eLpNorm_conjWirtingerDeriv_le hp hU hu
    (fun _ hKU _ ↦ ⟨A, fun n z hz ↦ hA n z (hKU hz)⟩) fun K hKU hK ↦
      ⟨volume K ^ (p : ℝ≥0∞).toReal⁻¹ * ENNReal.ofReal M + B, ?_, fun n ↦ ?_⟩
  · simp [ENNReal.mul_ne_top, hK.measure_lt_top.ne]
  -- Split `\bar∂(u n)` on `K` as the bounded `\bar∂(u n) - g n` plus `g n`.
  exact eLpNorm_conjWirtingerDeriv_restrict_le_of_norm_sub_le
    (by exact_mod_cast (one_lt_two.trans hp).le) hU hK.measurableSet hKU (hu n)
    (fun z hz ↦ hM n z (hKU hz))
    ((eLpNorm_mono_measure _ (Measure.restrict_mono hKU le_rfl)).trans (hB n))

end TauCeti
