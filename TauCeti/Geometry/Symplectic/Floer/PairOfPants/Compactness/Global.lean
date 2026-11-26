/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.Compactness.Basic
public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.Compactness.Closed
public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.Compactness.End
import TauCeti.Data.ENNReal.NatCastDiv
import TauCeti.Geometry.Symplectic.Floer.Tameness
import TauCeti.MeasureTheory.Integral.Bochner.Basic
import TauCeti.MeasureTheory.Measure.BubblingSet
import TauCeti.Topology.Compactness.Compact
import TauCeti.Topology.UniformSpace.LocallyUniformConvergence

/-!
# Compactness of Floer pairs of pants on the whole domain

Let `K_H` be the pair-of-pants perturbation `TauCeti.Floer.pairOfPantsPerturbation` of
period-one `C³` Hamiltonians `H_q` with `|H_q| ≤ B_q` on the three ends of `S = ℂ ∖ {0, 1}`, with
values in a symplectic vector space `(V, ω)`, and let `J(z, x)` be a `C²` family of `ω`-tame
almost complex structures on `S × V` which is cylindrical on the ends: beyond some height `T₀` on
the end `q` it is `J_q(t, x)` in the end coordinates, for a `C²` family `J_q` of `ω`-tame
structures.

Gromov–Floer compactness off finitely many bubbling points is known on one compact window of `S`
at a time, and on the translates of one window of an end in its positive end chart, with a
threshold that does not depend on the translation; in the namespace `TauCeti.SymplecticForm`,
these are `exists_pos_forall_tendstoLocallyUniformlyOn_subseq_off_finset_pairOfPantsPerturbation`
and `exists_pos_forall_tendstoLocallyUniformlyOn_subseq_off_finset_comp_positiveEndChart`. This
file assembles them into the statement on all of `S`, in the same namespace,
`exists_pos_forall_tendstoLocallyUniformlyOn_subseq_off_finset_thricePuncturedSphereReal`:
there is a threshold `δ > 0` such that every sequence of Floer solutions `uₖ : S → K`, for a
compact `K ⊆ V`, with action differences `aₖ(0) + aₖ(1) - aₖ(∞) ≤ A` has a subsequence converging
locally uniformly on `S \ Z` for a finite set `Z ⊆ S` with `#Z * δ ≤ A + B_0 + B_1 + B_∞`, and
every disc about a point of `Z` eventually carries energy at least `δ`.

The domain `S` is covered by countably many windows: the core `{z ∈ S | ±s_q(z) < T + 2 for
every end q}`, inside the compact truncation `S_{T + 2}`, where `T = max T₀ 2`, and on each end
`q` the images under `z ↦ φ'_q(z + (m, 0))`, for `m ∈ ℕ`, of the two windows
`(T + 1, T + 3) × (-2/5, 2/5)` and `(T + 1, T + 3) × (1/10, 9/10)` of the positive end chart
`φ'_q` (`TauCeti.Floer.positiveEndChart`). Since `φ'_q` is an open map, injective on bands of
angular width one, locally uniform convergence of `uₖ ∘ φ'_q` on a window is locally uniform
convergence of `uₖ` on its image (`TendstoLocallyUniformlyOn.image_of_isOpenMap`), and the energy
of `uₖ ∘ φ'_q` over a part of a window is the energy of `uₖ` over its image
(`TauCeti.SymplecticForm.setLIntegral_floerEnergyDensity_comp_positiveEndChart_add_eq`). The
thresholds of the windows are bounded below, since on each end the windows are translates of two
fixed windows, so the diagonal argument of
`TauCeti.exists_tendstoLocallyUniformlyOn_subseq_off_finset_iUnion` applies with the energy
measures of the `uₖ` on `S`.

**A closed manifold target.** The same holds for solutions `uₖ : S → M` in a closed manifold `M`
with a nondegenerate two-form `ω`, such as a closed symplectic manifold, with no condition on
where they take their values. In the namespace `TauCeti.SmoothTwoForm.IsNondegenerate` this is
`exists_pos_forall_tendstoLocallyUniformlyOn_comp_subseq_off_finset_thricePuncturedSphereReal`,
for solutions of topological energy `∫_S uₖ^*ω + ∑ q, ±∫₀¹ H_q(t, xₖ(q)(t)) dt ≤ A`. As in
`TauCeti.Geometry.Symplectic.Floer.PairOfPants.Compactness.Closed`, whose theorems on the core
window and on the translated end windows replace those of a vector space, sizes in `M` are measured
through an injective `C¹` map `e : M → F` into a normed space, such as the Whitney embedding. The
constants those theorems take are derived here. The pushforwards through `e` of the Hamiltonian
vector fields of the perturbation are bounded on the compact core
(`exists_forall_norm_mvfderiv_hamiltonianVectorField_pairOfPantsPerturbation_le`) and on the ends,
by compactness of `M` and periodicity of the `H_q`. Beyond `T₀` the structures are those of the
circle `t ↦ φ_q(±T, t)` of `S`, so they are `C²` in the charts of `M`, and one constant `c > 0`
with `c ‖d e v‖² ≤ ω(v, J v)` serves the core and these circles, which form a compact part of `S`
(`TauCeti.SmoothTwoForm.IsNondegenerate.exists_pos_forall_mul_norm_mvfderiv_sq_le`). The diagonal
argument runs with the readings `e ∘ uₖ`, whose energy on a window of an end is the energy of `uₖ`
on its image
(`TauCeti.SmoothTwoForm.setLIntegral_floerEnergyDensity_comp_positiveEndChart_add_eq`), and the
limit is read back in `M` through `e` (`IsCompact.exists_tendsto_of_tendsto_comp`): the solutions
converge locally uniformly after applying `e`, and pointwise in `M`.

Energy that escapes along the ends is not seen by the limit: this is the breaking of Floer
cylinders off the ends, which is not treated here, nor are the regularity of the limit and the
bubbles at the points of `Z`.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., Section 4.6
  (bubbling off finitely many points on a noncompact domain).
* M. Schwarz, *Cohomology operations from S¹-cobordisms in Floer homology*, PhD thesis,
  ETH Zürich (1995), on the compactness of the moduli spaces of the pair-of-pants product.
-/

public section

open Complex Filter Function MeasureTheory Metric Set Topology TauCeti.ThricePuncturedSphere
open scoped Manifold

namespace TauCeti.SymplecticForm

open Floer

/-- The points of `S` whose signed longitudinal coordinate on every end is below `c` form an open
set. -/
private theorem isOpen_setOf_forall_fst_positiveEndCoord_lt (c : ℝ) :
    IsOpen {z | z ∈ thricePuncturedSphereReal ∧ ∀ q, (positiveEndCoord q z).1 < c} := by
  refine isOpen_iff_mem_nhds.2 fun z ⟨hzS, hz⟩ ↦ ?_
  refine (isOpen_thricePuncturedSphereReal.eventually_mem hzS).and (eventually_all.2 fun q ↦ ?_)
  exact (continuousAt_fst_positiveEndCoord q (Puncture.ne_endCenter
    (mem_thricePuncturedSphereReal_iff.1 hzS) q)).eventually_lt continuousAt_const (hz q)

/-- The end windows `(T + 1, T + 3) × (c - 2/5, c + 2/5)` of a positive end chart, with `c = 0`
for `b = false` and `c = 1/2` for `b = true`. -/
private noncomputable def endWindow (T : ℝ) (b : Bool) : Set (ℝ × ℝ) :=
  Ioo (T + 1) (T + 3) ×ˢ
    Ioo ((bif b then 1 / 2 else 0) - 2 / 5) ((bif b then 1 / 2 else 0) + 2 / 5)

/-- The translates by `(m, 0)`, `m ≥ 0`, of the closed end windows lie beyond `T ≥ 0` in a band of
angular width one. -/
private theorem add_mem_Ioi_prod_Ioo {T : ℝ} (hT : 0 ≤ T) {m : ℝ} (hm : 0 ≤ m) {b : Bool}
    {y : ℝ × ℝ} (hy : y ∈ Icc (T + 1) (T + 3) ×ˢ
      Icc ((bif b then (1 / 2 : ℝ) else 0) - 2 / 5) ((bif b then 1 / 2 else 0) + 2 / 5)) :
    y + (m, 0) ∈ Ioi (max T 0) ×ˢ
      Ioo ((bif b then 1 / 2 else 0) - 1 / 2) ((bif b then 1 / 2 else 0) - 1 / 2 + 1) := by
  obtain ⟨⟨hs, -⟩, ht₁, ht₂⟩ := hy
  refine ⟨?_, ?_, ?_⟩
  · rw [Prod.fst_add, mem_Ioi, max_eq_left hT]; linarith
  · rw [Prod.snd_add, add_zero]; linarith
  · rw [Prod.snd_add, add_zero]; linarith

/-- A point at least `T + 2` out along the end `q` lies in the image of an end window under
`y ↦ φ'_q(y + (m, 0))` for some `m ∈ ℕ`. -/
private theorem exists_mem_image_positiveEndChart_add {q : Puncture} {z : ℝ × ℝ}
    (hz : equivRealProdCLM.symm z ≠ q.endCenter) {T : ℝ}
    (hT : T + 2 ≤ (positiveEndCoord q z).1) :
    ∃ (m : ℕ) (b : Bool),
      z ∈ (fun y ↦ positiveEndChart q (y + ((m : ℝ), 0))) '' endWindow T b := by
  set s := (positiveEndCoord q z).1
  set t := (positiveEndCoord q z).2
  have hzc : positiveEndChart q (s, t) = z := positiveEndChart_positiveEndCoord q hz
  -- Translate by the integer part of `s - (T + 2)`.
  set m := ⌊s - (T + 2)⌋₊
  have hm₁ : (m : ℝ) ≤ s - (T + 2) := Nat.floor_le (by linarith)
  have hm₂ : s - (T + 2) < m + 1 := Nat.lt_floor_add_one _
  -- Shift the angular coordinate by an integer into one of the two windows.
  have hper : Periodic (fun t ↦ positiveEndChart q (s, t)) 1 := positiveEndChart_add_one q s
  have hk (k : ℤ) : positiveEndChart q (s, t - k) = z := by
    simpa [hzc] using hper.sub_int_mul_eq k (x := t)
  have hy (b : Bool) (k : ℤ) (h₁ : (bif b then 1 / 2 else 0) - 2 / 5 < t - k)
      (h₂ : t - k < (bif b then 1 / 2 else 0) + 2 / 5) : ∃ (m : ℕ) (b : Bool),
        z ∈ (fun y ↦ positiveEndChart q (y + ((m : ℝ), 0))) '' endWindow T b :=
    ⟨m, b, (s - m, t - k), ⟨⟨by linarith, by linarith⟩, h₁, h₂⟩, by simpa using hk k⟩
  have hf₀ : 0 ≤ t - ⌊t⌋ := Int.self_sub_floor t ▸ Int.fract_nonneg t
  have hf₁ : t - ⌊t⌋ < 1 := Int.self_sub_floor t ▸ Int.fract_lt_one t
  by_cases h₁ : t - ⌊t⌋ < 2 / 5
  · exact hy false ⌊t⌋ (by simp only [Bool.cond_false]; linarith)
      (by simp only [Bool.cond_false]; linarith)
  by_cases h₂ : t - ⌊t⌋ < 9 / 10
  · exact hy true ⌊t⌋ (by simp only [Bool.cond_true]; linarith)
      (by simp only [Bool.cond_true]; linarith)
  · exact hy false (⌊t⌋ + 1) (by push_cast; simp only [Bool.cond_false]; linarith)
      (by push_cast; simp only [Bool.cond_false]; linarith)

/-- The windows covering `S`: the core, where the signed longitudinal coordinate of every end is
below `T + 2`, and on each end `q` the images of the end windows under `y ↦ φ'_q(y + (m, 0))`,
for `m ∈ ℕ`. -/
private noncomputable def window (T : ℝ) : Option (Puncture × ℕ × Bool) → Set (ℝ × ℝ)
  | none => {z | z ∈ thricePuncturedSphereReal ∧ ∀ q, (positiveEndCoord q z).1 < T + 2}
  | some (q, m, b) => (fun y ↦ positiveEndChart q (y + ((m : ℝ), 0))) '' endWindow T b

/-- The end windows are mapped into `S`. -/
private theorem positiveEndChart_add_mem {T : ℝ} (hT : 0 ≤ T) (q : Puncture) (m : ℕ) {b : Bool}
    {y : ℝ × ℝ} (hy : y ∈ endWindow T b) :
    positiveEndChart q (y + ((m : ℝ), 0)) ∈ thricePuncturedSphereReal :=
  positiveEndChart_mem_thricePuncturedSphereReal <| (le_max_right _ _).trans_lt
    (add_mem_Ioi_prod_Ioo hT (Nat.cast_nonneg m)
      (prod_mono Ioo_subset_Icc_self Ioo_subset_Icc_self hy)).1

/-- The windows are open, since the positive end charts are open maps. -/
private theorem isOpen_window (T : ℝ) (i : Option (Puncture × ℕ × Bool)) :
    IsOpen (window T i) := by
  rcases i with _ | ⟨q, m, b⟩
  · exact isOpen_setOf_forall_fst_positiveEndCoord_lt _
  · exact (isOpenMap_positiveEndChart q).comp (Homeomorph.addRight ((m : ℝ), (0 : ℝ))).isOpenMap
      _ (isOpen_Ioo.prod isOpen_Ioo)

/-- The core window lies in the compact truncation `S_{T + 2}`. -/
private theorem window_none_subset (T : ℝ) :
    window T none ⊆ equivRealProdCLM.symm ⁻¹' truncation (T + 2) :=
  subset_preimage_truncation_of_isOpen (isOpen_window T none) fun _ hz q ↦ (hz.2 q).le

/-- The windows cover `S`. -/
private theorem iUnion_window {T : ℝ} (hT : 0 ≤ T) :
    ⋃ i, window T i = thricePuncturedSphereReal := by
  refine subset_antisymm (iUnion_subset fun i ↦ ?_) fun z hz ↦ ?_
  · rcases i with _ | ⟨q, m, b⟩
    · exact fun z hz ↦ hz.1
    · rintro _ ⟨y, hy, rfl⟩
      exact positiveEndChart_add_mem hT q m hy
  · by_cases hc : ∀ q, (positiveEndCoord q z).1 < T + 2
    · exact mem_iUnion.2 ⟨none, hz, hc⟩
    · obtain ⟨q, hq⟩ := not_forall.1 hc
      obtain ⟨m, b, hzm⟩ :=
        exists_mem_image_positiveEndChart_add
          (Puncture.ne_endCenter (mem_thricePuncturedSphereReal_iff.1 hz) q) (not_lt.1 hq)
      exact mem_iUnion.2 ⟨some (q, m, b), hzm⟩

/-- **Convergence on a window of an end, read on `S`.** Let `g(y) = φ'_q(y + (m, 0))` be the
translated positive end chart of the end `q`, and let `Ω` be an open window whose translate by
`(m, 0)` lies in a band of angular width one beyond `0`. If the readings `fₙ ∘ g` converge locally
uniformly on `Ω \ Z`, then the `fₙ` converge locally uniformly on `g(Ω) \ g(Z)`. -/
private theorem exists_tendstoLocallyUniformlyOn_image_positiveEndChart_add {α : Type*}
    [UniformSpace α] {q : Puncture} {m : ℕ} {T t₀ : ℝ} {Ω : Set (ℝ × ℝ)} (hΩ : IsOpen Ω)
    (hΩT : ∀ z ∈ Ω, z + ((m : ℝ), 0) ∈ Ioi (max T 0) ×ˢ Ioo t₀ (t₀ + 1)) {Z : Finset (ℝ × ℝ)}
    (hZ : ↑Z ⊆ Ω) {f : ℕ → ℝ × ℝ → α} {v : ℝ × ℝ → α}
    (hv : TendstoLocallyUniformlyOn (fun n z ↦ f n (positiveEndChart q (z + ((m : ℝ), 0)))) v
      atTop (Ω \ ↑Z)) :
    ∃ v' : ℝ × ℝ → α, TendstoLocallyUniformlyOn f v' atTop
      ((fun y ↦ positiveEndChart q (y + ((m : ℝ), 0))) '' Ω \
        (fun y ↦ positiveEndChart q (y + ((m : ℝ), 0))) '' ↑Z) := by
  have hinj : InjOn (fun y ↦ positiveEndChart q (y + ((m : ℝ), 0))) Ω := fun a ha b hb hab ↦
    add_right_cancel (injOn_positiveEndChart q t₀ ⟨mem_univ _, Ioo_subset_Ico_self (hΩT a ha).2⟩
      ⟨mem_univ _, Ioo_subset_Ico_self (hΩT b hb).2⟩ hab)
  rw [← hinj.image_sdiff_subset hZ]
  exact ⟨_, hv.image_of_isOpenMap (hΩ.sdiff Z.finite_toSet.isClosed)
    ((isOpenMap_positiveEndChart q).comp (Homeomorph.addRight _).isOpenMap)
    (hinj.mono sdiff_subset)⟩

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {H : Puncture → ℝ → V → ℝ}

/-- **Bubbling points on a window of an end, read on `S`.** Let `g(y) = φ'_q(y + (m, 0))` be the
translated positive end chart of the end `q`, and let `Ω` be an open window whose translate by
`(m, 0)` lies beyond `max T 0`, for `T ≥ 2`, in a band of angular width one. If the end readings
`uₖ ∘ g` converge locally uniformly on `Ω \ Z` along `φ`, and the energy `δ` concentrates in every
disc about a point of `Z ⊆ Ω`, then `uₖ` converges locally uniformly on `g(Ω) \ g(Z)` along `φ`,
and every neighbourhood of a point of `g(Z)` eventually carries energy at least `δ` for the energy
measure of `uₖ` on `S`. -/
private theorem concentration_and_tendstoLocallyUniformlyOn_image_positiveEndChart_add
    (ω : SymplecticForm V) (hH : ∀ q, Periodic (H q) 1) (hHd : ∀ q t, Differentiable ℝ (H q t))
    {u : ℕ → ℝ × ℝ → V} (hu : ∀ k, DifferentiableOn ℝ (u k) thricePuncturedSphereReal)
    {q : Puncture} {m : ℕ} {T t₀ : ℝ} (hT : 2 ≤ T) {Ω : Set (ℝ × ℝ)} (hΩ : IsOpen Ω)
    (hΩT : ∀ z ∈ Ω, z + ((m : ℝ), 0) ∈ Ioi (max T 0) ×ˢ Ioo t₀ (t₀ + 1)) {δ : ℝ} {φ : ℕ → ℕ}
    {Z : Finset (ℝ × ℝ)} (hZ : ↑Z ⊆ Ω) {v : ℝ × ℝ → V}
    (hconc : ∀ z ∈ Z, ∀ ε > 0, ∀ᶠ n in atTop, δ ≤ ∫ y in ball z ε ∩ Ω, ω.floerEnergyDensity
      (fun _ _ ↦ 0) (fun w ↦ positiveEndHamiltonian H q w.2)
      (fun z ↦ u (φ n) (positiveEndChart q (z + ((m : ℝ), 0)))) y)
    (hv : TendstoLocallyUniformlyOn (fun n z ↦ u (φ n) (positiveEndChart q (z + ((m : ℝ), 0)))) v
      atTop (Ω \ ↑Z)) :
    (∀ z ∈ (fun y ↦ positiveEndChart q (y + ((m : ℝ), 0))) '' ↑Z, ∀ N ∈ 𝓝 z,
      ∀ᶠ n in atTop, ENNReal.ofReal δ ≤ (volume.restrict thricePuncturedSphereReal).withDensity
        (fun y ↦ ENNReal.ofReal (ω.floerEnergyDensity
          (fun z x ↦ pairOfPantsPerturbation H (equivRealProdCLM.symm z) x 1)
          (fun z x ↦ pairOfPantsPerturbation H (equivRealProdCLM.symm z) x I) (u (φ n)) y)) N) ∧
      ∃ v' : ℝ × ℝ → V, TendstoLocallyUniformlyOn (fun n ↦ u (φ n)) v' atTop
        ((fun y ↦ positiveEndChart q (y + ((m : ℝ), 0))) '' Ω \
          (fun y ↦ positiveEndChart q (y + ((m : ℝ), 0))) '' ↑Z) := by
  set g : ℝ × ℝ → ℝ × ℝ := fun y ↦ positiveEndChart q (y + ((m : ℝ), 0))
  have hg : Continuous g :=
    (contDiff_positiveEndChart q 0).continuous.comp (continuous_id.add continuous_const)
  have hgS (y : ℝ × ℝ) (hy : y ∈ Ω) : g y ∈ thricePuncturedSphereReal :=
    positiveEndChart_mem_thricePuncturedSphereReal ((le_max_right _ _).trans_lt (hΩT y hy).1)
  have hgo : IsOpenMap g := (isOpenMap_positiveEndChart q).comp (Homeomorph.addRight _).isOpenMap
  have hKH (r : Puncture) (w : ℂ) (x : V) (hw : T ≤ r.endSign * (r.endCoord w).re) :
      pairOfPantsPerturbation H w x = H r (r.endCoord w).im x • r.endAngularForm w :=
    pairOfPantsPerturbation_eq_smul_endAngularForm (hT.trans hw) x
  refine ⟨?_, exists_tendstoLocallyUniformlyOn_image_positiveEndChart_add hΩ hΩT hZ hv⟩
  · rintro _ ⟨z, hz, rfl⟩ N hN
    obtain ⟨ε, hε, hεN⟩ := Metric.mem_nhds_iff.1 (hg.continuousAt.preimage_mem_nhds hN)
    filter_upwards [hconc z hz ε hε] with n hn
    have hs : MeasurableSet (ball z ε ∩ Ω) := measurableSet_ball.inter hΩ.measurableSet
    -- The image of the disc is open, so measurable, and lies in `S ∩ N`.
    have hgs : MeasurableSet (g '' (ball z ε ∩ Ω)) := (hgo _ (isOpen_ball.inter hΩ)).measurableSet
    have hgsS : g '' (ball z ε ∩ Ω) ⊆ thricePuncturedSphereReal := by
      rintro _ ⟨y, hy, rfl⟩
      exact hgS y hy.2
    refine TauCeti.MeasureTheory.le_withDensity_of_le_setLIntegral hgs hgsS
      (image_subset_iff.2 (inter_subset_left.trans hεN)) ?_
    rw [← setLIntegral_floerEnergyDensity_comp_positiveEndChart_add_eq hKH hH hHd (hu _) q m hs
      fun y hy ↦ hΩT y hy.2]
    exact (ENNReal.ofReal_le_ofReal hn).trans
      TauCeti.MeasureTheory.ofReal_integral_le_lintegral_ofReal

/-- The energy of a Floer pair of pants whose action difference is at most `A` is at most
`A + B_0 + B_1 + B_∞`, which is nonnegative. -/
private theorem nonneg_and_lintegral_floerEnergyDensity_le (ω : SymplecticForm V)
    (hH : ∀ q, Periodic (H q) 1) (hHs : ∀ q, ContDiff ℝ 3 (uncurry (H q))) {B : Puncture → ℝ}
    (hB : ∀ q t x, |H q t x| ≤ B q) {J : ℝ × ℝ → V → AlmostComplexStructure V}
    (hJt : ∀ z ∈ thricePuncturedSphereReal, ∀ x, ω.Tames (J z x)) {u : ℝ × ℝ → V}
    (hu : ContDiffOn ℝ 3 u thricePuncturedSphereReal)
    (hfl : ∀ z ∈ thricePuncturedSphereReal,
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z (u z))
        (ω.perturbedFDeriv
          (fun z x ↦ pairOfPantsPerturbation H (equivRealProdCLM.symm z) x 1)
          (fun z x ↦ pairOfPantsPerturbation H (equivRealProdCLM.symm z) x I)
          u z : ℝ × ℝ →ₗ[ℝ] V)) {a : Puncture → ℝ}
    (ha : ∀ q, Tendsto (fun R ↦ ω.hamiltonianAction (H q) (fun t ↦ u (equivRealProdCLM
      (q.cylindricalEndLift (↑(q.endSign * R) + ↑t * I))))) atTop (𝓝 (a q)))
    {A : ℝ} (hA : a .zero + a .one - a .inf ≤ A) :
    0 ≤ A + ∑ q, B q ∧ ∫⁻ z in thricePuncturedSphereReal, ENNReal.ofReal (ω.floerEnergyDensity
      (fun z x ↦ pairOfPantsPerturbation H (equivRealProdCLM.symm z) x 1)
      (fun z x ↦ pairOfPantsPerturbation H (equivRealProdCLM.symm z) x I) u z) ≤
        ENNReal.ofReal (A + ∑ q, B q) := by
  have hHs' (q : Puncture) : ContDiff ℝ 1 (uncurry (H q)) := (hHs q).of_le (by norm_num)
  have h := le_add_add_sum_of_tendsto_hamiltonianAction ω hH hHs' hB (hu.of_le (by norm_num))
    (fun z hz ↦ hJt z hz _) hfl ha
  refine ⟨by linarith, (lintegral_floerEnergyDensity_pairOfPantsPerturbation_le ω hH hHs' hB
    (hu.of_le (by norm_num)) (fun z hz ↦ hJt z hz _) hfl ha).trans <|
      ENNReal.ofReal_le_ofReal ?_⟩
  simp only [Puncture.sum_univ, Puncture.endSign_zero, Puncture.endSign_one,
    Puncture.endSign_inf]
  linarith

/-- **The windows of the pair of pants, with one threshold.** Under the hypotheses of the main
theorem below, there is a threshold `δ > 0` such that on every window, every subsequence of a
sequence of solutions has a further subsequence converging off a set at each point of which the
energy measure of every neighbourhood is eventually at least `δ`. -/
private theorem exists_pos_forall_window (ω : SymplecticForm V) (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContDiff ℝ 3 (uncurry (H q))) {B : Puncture → ℝ} (hB : ∀ q t x, |H q t x| ≤ B q)
    {J : ℝ × ℝ → V → AlmostComplexStructure V}
    (hJ : ContDiffOn ℝ 2
      (fun p : (ℝ × ℝ) × V ↦ (J p.1 p.2).toLinearMap.toContinuousLinearMap)
      (thricePuncturedSphereReal ×ˢ univ))
    (hJt : ∀ z ∈ thricePuncturedSphereReal, ∀ x, ω.Tames (J z x)) {T₀ : ℝ}
    {Jq : Puncture → ℝ → V → AlmostComplexStructure V} (hJqt : ∀ q t x, ω.Tames (Jq q t x))
    (hJq : ∀ q, ContDiff ℝ 2 fun p : ℝ × V ↦ (Jq q p.1 p.2).toLinearMap.toContinuousLinearMap)
    (hJe : ∀ q s t x, T₀ ≤ s → J (endChart q (q.endSign * s, t)) x = Jq q t x)
    {K : Set V} (hK : IsCompact K) :
    ∃ δ > 0, ∀ ⦃u : ℕ → ℝ × ℝ → V⦄ ⦃a : ℕ → Puncture → ℝ⦄ ⦃A : ℝ⦄,
      (∀ k, ContDiffOn ℝ 3 (u k) thricePuncturedSphereReal) →
      (∀ k, ∀ z ∈ thricePuncturedSphereReal,
        IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z (u k z))
          (ω.perturbedFDeriv
            (fun z x ↦ pairOfPantsPerturbation H (equivRealProdCLM.symm z) x 1)
            (fun z x ↦ pairOfPantsPerturbation H (equivRealProdCLM.symm z) x I)
            (u k) z : ℝ × ℝ →ₗ[ℝ] V)) →
      (∀ k q, Tendsto (fun R ↦ ω.hamiltonianAction (H q) (fun t ↦ u k (equivRealProdCLM
        (q.cylindricalEndLift (↑(q.endSign * R) + ↑t * I))))) atTop (𝓝 (a k q))) →
      (∀ k, a k .zero + a k .one - a k .inf ≤ A) →
      (∀ k, MapsTo (u k) thricePuncturedSphereReal K) →
      ∀ i ⦃ψ : ℕ → ℕ⦄, StrictMono ψ → ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ Z : Set (ℝ × ℝ),
        (∀ z ∈ Z, ∀ N ∈ 𝓝 z, ∀ᶠ n in atTop, ENNReal.ofReal δ ≤
          (volume.restrict thricePuncturedSphereReal).withDensity (fun y ↦ ENNReal.ofReal
            (ω.floerEnergyDensity
              (fun z x ↦ pairOfPantsPerturbation H (equivRealProdCLM.symm z) x 1)
              (fun z x ↦ pairOfPantsPerturbation H (equivRealProdCLM.symm z) x I)
              (u (ψ (φ n))) y)) N) ∧
        ∃ v : ℝ × ℝ → V, TendstoLocallyUniformlyOn (fun n ↦ u (ψ (φ n))) v atTop
          (window (max T₀ 2) i \ Z) := by
  have hT : 2 ≤ max T₀ 2 := le_max_right _ _
  have hHd (q : Puncture) (t : ℝ) : Differentiable ℝ (H q t) :=
    ((hHs q).differentiable (by norm_num)).comp ((differentiable_const t).prodMk differentiable_id)
  -- The thresholds of the two windows of each end, uniform in the translation, and of the core.
  choose δe hδe hconve using fun q b ↦
    ω.exists_pos_forall_tendstoLocallyUniformlyOn_subseq_off_finset_comp_positiveEndChart (H := H)
      (fun r w x hw ↦ pairOfPantsPerturbation_eq_smul_endAngularForm (hT.trans hw) x) hH hHd
      (hHs q) (hJqt q) (hJq q) (fun s t x hs ↦ hJe q s t x ((le_max_left _ _).trans hs))
      (D := Icc (max T₀ 2 + 1) (max T₀ 2 + 3) ×ˢ Icc ((bif b then (1 / 2 : ℝ) else 0) - 2 / 5)
        ((bif b then 1 / 2 else 0) + 2 / 5)) (isCompact_Icc.prod isCompact_Icc)
      (t₀ := (bif b then 1 / 2 else 0) - 1 / 2) (fun y hy ↦ by
        have h := add_mem_Ioi_prod_Ioo (m := 0) (by linarith) le_rfl hy
        rwa [Prod.mk_zero_zero, add_zero] at h) hK
  obtain ⟨δc, hδc, hconvc⟩ :=
    exists_pos_forall_tendstoLocallyUniformlyOn_subseq_off_finset_pairOfPantsPerturbation ω hH
      hHs hB hJ hJt (isCompact_preimage_truncation (max T₀ 2 + 2))
      (preimage_truncation_subset_thricePuncturedSphereReal _) hK
  refine ⟨min δc (Finset.univ.inf' ⟨(.zero, false), Finset.mem_univ _⟩
    fun p : Puncture × Bool ↦ δe p.1 p.2), lt_min hδc ((Finset.lt_inf'_iff _).2 fun p _ ↦
      hδe p.1 p.2), fun u a A hu hfl ha hA huK i ψ _ ↦ ?_⟩
  rcases i with _ | ⟨q, m, b⟩
  · obtain ⟨φ, Z, v, hφ, -, -, hc, -, -, -, hv⟩ := hconvc (u := u ∘ ψ) (a := a ∘ ψ)
      (isOpen_window _ none) (window_none_subset _) (fun k ↦ hu _) (fun k ↦ hfl _)
      (fun k ↦ ha _) (fun k ↦ hA _) (fun k ↦ (huK _).mono_left fun z hz ↦ hz.1)
    exact ⟨φ, hφ, ↑Z, fun z hz ↦
      eventually_ofReal_le_withDensity_of_forall_eventually_le_setIntegral_ball
        (isOpen_window _ none).measurableSet (fun y hy ↦ hy.1)
        fun ε hε ↦ (hc z hz ε hε).mono fun n hn ↦ (min_le_left _ _).trans hn, v, hv⟩
  · obtain ⟨φ, Z, v, hφ, hZΩ, -, hc, -, -, -, hv⟩ := hconve q b (Ω := endWindow (max T₀ 2) b)
      (u := u ∘ ψ) (R := fun _ ↦ (m : ℝ)) (isOpen_Ioo.prod isOpen_Ioo)
      (prod_mono Ioo_subset_Icc_self Ioo_subset_Icc_self) (fun _ ↦ Nat.cast_nonneg m)
      (fun k ↦ hu _) (fun k ↦ hfl _)
      (nonneg_and_lintegral_floerEnergyDensity_le ω hH hHs hB hJt (hu 0) (hfl 0) (ha 0) (hA 0)).1
      (fun k ↦ (nonneg_and_lintegral_floerEnergyDensity_le ω hH hHs hB hJt (hu _) (hfl _) (ha _)
        (hA _)).2) (fun k y hy ↦ huK _ (positiveEndChart_add_mem (by linarith) q m hy))
    obtain ⟨hc', v', hv'⟩ :=
      concentration_and_tendstoLocallyUniformlyOn_image_positiveEndChart_add ω hH hHd
        (fun k ↦ (hu (ψ k)).differentiableOn (by norm_num)) hT (isOpen_Ioo.prod isOpen_Ioo)
        (fun y hy ↦ add_mem_Ioi_prod_Ioo (by linarith) (Nat.cast_nonneg m)
          (prod_mono Ioo_subset_Icc_self Ioo_subset_Icc_self hy)) hZΩ
        (fun z hz ε hε ↦ (hc z hz ε hε).mono fun n hn ↦ ((min_le_right _ _).trans
          (Finset.inf'_le (fun p : Puncture × Bool ↦ δe p.1 p.2) (Finset.mem_univ (q, b)))).trans
            hn) hv
    exact ⟨φ, hφ, _, hc', v', hv'⟩

/-- **Floer pairs of pants with bounded end actions converge off finitely many bubbling points on
the whole domain.** Let `K_H` be the pair-of-pants perturbation of period-one `C³` Hamiltonians
`H_q` with `|H_q| ≤ B_q`, and let `J(z, x)` be a `C²` family of `ω`-tame structures on `S × V`,
where `S = ℂ ∖ {0, 1}` is read in real coordinates, which beyond `T₀` on each end `q` is a `C²`
family `J_q(t, x)` of `ω`-tame structures in the end coordinates. Fix a compact `K ⊆ V`. There is a
threshold `δ > 0` with the following property. Let `uₖ : S → K` be `C³` solutions of
`(du - X_{K_H})^{0,1} = 0` on `S` for `J(z, u)`, with limiting end actions `aₖ(q)` satisfying
`aₖ(0) + aₖ(1) - aₖ(∞) ≤ A`. Then there are a subsequence `φ`, a finite set `Z ⊆ S` with
`#Z * δ ≤ A + B_0 + B_1 + B_∞`, and a continuous `v : S \ Z → K` such that along `φ` every disc
about a point of `Z` eventually carries energy at least `δ`, and `u_{φ n} → v` locally uniformly
on `S \ Z`. -/
theorem exists_pos_forall_tendstoLocallyUniformlyOn_subseq_off_finset_thricePuncturedSphereReal
    (ω : SymplecticForm V) (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContDiff ℝ 3 (uncurry (H q))) {B : Puncture → ℝ} (hB : ∀ q t x, |H q t x| ≤ B q)
    {J : ℝ × ℝ → V → AlmostComplexStructure V}
    (hJ : ContDiffOn ℝ 2
      (fun p : (ℝ × ℝ) × V ↦ (J p.1 p.2).toLinearMap.toContinuousLinearMap)
      (thricePuncturedSphereReal ×ˢ univ))
    (hJt : ∀ z ∈ thricePuncturedSphereReal, ∀ x, ω.Tames (J z x)) {T₀ : ℝ}
    {Jq : Puncture → ℝ → V → AlmostComplexStructure V} (hJqt : ∀ q t x, ω.Tames (Jq q t x))
    (hJq : ∀ q, ContDiff ℝ 2 fun p : ℝ × V ↦ (Jq q p.1 p.2).toLinearMap.toContinuousLinearMap)
    (hJe : ∀ q s t x, T₀ ≤ s → J (endChart q (q.endSign * s, t)) x = Jq q t x)
    {K : Set V} (hK : IsCompact K) :
    ∃ δ > 0, ∀ ⦃u : ℕ → ℝ × ℝ → V⦄ ⦃a : ℕ → Puncture → ℝ⦄ ⦃A : ℝ⦄,
      (∀ k, ContDiffOn ℝ 3 (u k) thricePuncturedSphereReal) →
      (∀ k, ∀ z ∈ thricePuncturedSphereReal,
        IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z (u k z))
          (ω.perturbedFDeriv
            (fun z x ↦ pairOfPantsPerturbation H (equivRealProdCLM.symm z) x 1)
            (fun z x ↦ pairOfPantsPerturbation H (equivRealProdCLM.symm z) x I)
            (u k) z : ℝ × ℝ →ₗ[ℝ] V)) →
      (∀ k q, Tendsto (fun R ↦ ω.hamiltonianAction (H q) (fun t ↦ u k (equivRealProdCLM
        (q.cylindricalEndLift (↑(q.endSign * R) + ↑t * I))))) atTop (𝓝 (a k q))) →
      (∀ k, a k .zero + a k .one - a k .inf ≤ A) →
      (∀ k, MapsTo (u k) thricePuncturedSphereReal K) →
      ∃ (φ : ℕ → ℕ) (Z : Finset (ℝ × ℝ)) (v : ℝ × ℝ → V), StrictMono φ ∧
        ↑Z ⊆ thricePuncturedSphereReal ∧ Z.card * δ ≤ A + ∑ q, B q ∧
        (∀ z ∈ Z, ∀ ε > 0, ∀ᶠ n in atTop, δ ≤ ∫ y in ball z ε ∩ thricePuncturedSphereReal,
          ω.floerEnergyDensity
            (fun z x ↦ pairOfPantsPerturbation H (equivRealProdCLM.symm z) x 1)
            (fun z x ↦ pairOfPantsPerturbation H (equivRealProdCLM.symm z) x I) (u (φ n)) y) ∧
        ContinuousOn v (thricePuncturedSphereReal \ ↑Z) ∧
        MapsTo v (thricePuncturedSphereReal \ ↑Z) K ∧
        TendstoLocallyUniformlyOn (fun n ↦ u (φ n)) v atTop
          (thricePuncturedSphereReal \ ↑Z) := by
  obtain ⟨δ, hδ, hwin⟩ := exists_pos_forall_window ω hH hHs hB hJ hJt hJqt hJq hJe hK
  refine ⟨δ, hδ, fun u a A hu hfl ha hA huK ↦ ?_⟩
  have hE (k : ℕ) :=
    nonneg_and_lintegral_floerEnergyDensity_le ω hH hHs hB hJt (hu k) (hfl k) (ha k) (hA k)
  -- Assemble the windows by the diagonal argument, for the energy measures of the `uₖ` on `S`.
  obtain ⟨φ, Z, v, hφ, hZ, hcard, hconc, hconv⟩ :=
    exists_tendstoLocallyUniformlyOn_subseq_off_finset_iUnion (isOpen_window (max T₀ 2))
      (F := u) (ENNReal.ofReal_pos.2 hδ).ne' ENNReal.ofReal_ne_top
      (fun k ↦ (measure_mono (subset_univ _)).trans (by
        rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]; exact (hE k).2))
      (hwin hu hfl ha hA huK)
  rw [iUnion_window (by positivity)] at hZ hconv
  refine ⟨φ, Z, v, hφ, hZ, ?_, fun z hz ε hε ↦ ?_, ?_, ?_, hconv⟩
  · exact (ENNReal.natCast_mul_ofReal_le_ofReal_iff (hE 0).1).1 hcard
  · -- The energy measure of a disc is the energy over its part in `S`.
    filter_upwards [hconc z hz _ (ball_mem_nhds z hε)] with n hn
    have h0 (y : ℝ × ℝ) (hy : y ∈ ball z ε ∩ thricePuncturedSphereReal) :=
      ω.floerEnergyDensity_nonneg (hJt y hy.2 _) (hfl (φ n) y hy.2)
    exact TauCeti.MeasureTheory.le_setIntegral_of_ofReal_le_withDensity measurableSet_ball
      isOpen_thricePuncturedSphereReal.measurableSet
      (ω.integrableOn_and_setIntegral_floerEnergyDensity_le isOpen_thricePuncturedSphereReal
        (measurableSet_ball.inter isOpen_thricePuncturedSphereReal.measurableSet)
        inter_subset_right ((hu _).of_le (by norm_num))
        (contDiffOn_uncurry_pairOfPantsPerturbation hH (fun q ↦ (hHs q).of_le (by norm_num)) 1)
        (contDiffOn_uncurry_pairOfPantsPerturbation hH (fun q ↦ (hHs q).of_le (by norm_num)) I)
        h0 (hE 0).1
        (hE _).2).1 h0 hn
  · exact hconv.continuousOn (Eventually.of_forall fun n ↦
      ((hu (φ n)).continuousOn).mono sdiff_subset).frequently
  · exact fun z hz ↦ hK.isClosed.mem_of_tendsto (hconv.tendsto_at hz)
      (Eventually.of_forall fun n ↦ huK _ hz.1)

end TauCeti.SymplecticForm

/-! ### A closed manifold target -/

namespace TauCeti.SmoothTwoForm.IsNondegenerate

open Floer SymplecticForm

variable {E G M F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace G] {I : ModelWithCorners ℝ E G} [I.Boundaryless] [TopologicalSpace M]
  [ChartedSpace G M] [IsManifold I ⊤ M] [CompactSpace M] [NormedAddCommGroup F]
  [NormedSpace ℝ F] {ω : SmoothTwoForm I M} {H : Puncture → ℝ → M → ℝ}
  {J : ℝ × ℝ → (x : M) → AlmostComplexStructure (TangentSpace I x)} {e : M → F}

omit [FiniteDimensional ℝ E] [I.Boundaryless] [CompactSpace M] in
/-- **Energy concentration on a window of an end, read on `S`.** Let `g(y) = φ'_q(y + (m, 0))` be
the translated positive end chart of the end `q`, and let `Ω` be an open window whose translate by
`(m, 0)` lies beyond `max T 0`, for `T ≥ 2`, in a band of angular width one. If the energy `δ` of
the end readings `uₖ ∘ g` concentrates in every disc about a point of `Z ⊆ Ω`, then every
neighbourhood of a point of `g(Z)` eventually carries energy at least `δ` for the energy measure
of `uₖ` on `S`. -/
private theorem eventually_ofReal_le_withDensity_image_positiveEndChart_add
    (hH : ∀ q, Periodic (H q) 1) (hHd : ∀ q t, MDifferentiable I 𝓘(ℝ) (H q t))
    {u : ℕ → ℝ × ℝ → M} (hu : ∀ k, MDifferentiableOn 𝓘(ℝ, ℝ × ℝ) I (u k) thricePuncturedSphereReal)
    {q : Puncture} {m : ℕ} {T t₀ : ℝ} (hT : 2 ≤ T) {Ω : Set (ℝ × ℝ)} (hΩ : IsOpen Ω)
    (hΩT : ∀ z ∈ Ω, z + ((m : ℝ), 0) ∈ Ioi (max T 0) ×ˢ Ioo t₀ (t₀ + 1)) {δ : ℝ} {φ : ℕ → ℕ}
    {Z : Finset (ℝ × ℝ)}
    (hconc : ∀ z ∈ Z, ∀ ε > 0, ∀ᶠ n in atTop, δ ≤ ∫ y in ball z ε ∩ Ω, ω.floerEnergyDensity
      (fun _ _ ↦ 0) (fun w ↦ positiveEndHamiltonian H q w.2)
      (fun z ↦ u (φ n) (positiveEndChart q (z + ((m : ℝ), 0)))) y) :
    ∀ z ∈ (fun y ↦ positiveEndChart q (y + ((m : ℝ), 0))) '' ↑Z, ∀ N ∈ 𝓝 z,
      ∀ᶠ n in atTop, ENNReal.ofReal δ ≤ (volume.restrict thricePuncturedSphereReal).withDensity
        (fun y ↦ ENNReal.ofReal (ω.floerEnergyDensity
          (fun z x ↦ pairOfPantsPerturbation H (equivRealProdCLM.symm z) x 1)
          (fun z x ↦ pairOfPantsPerturbation H (equivRealProdCLM.symm z) x Complex.I)
          (u (φ n)) y)) N := by
  set g : ℝ × ℝ → ℝ × ℝ := fun y ↦ positiveEndChart q (y + ((m : ℝ), 0))
  have hg : Continuous g :=
    (contDiff_positiveEndChart q 0).continuous.comp (continuous_id.add continuous_const)
  have hgo : IsOpenMap g := (isOpenMap_positiveEndChart q).comp (Homeomorph.addRight _).isOpenMap
  rintro _ ⟨z, hz, rfl⟩ N hN
  obtain ⟨ε, hε, hεN⟩ := Metric.mem_nhds_iff.1 (hg.continuousAt.preimage_mem_nhds hN)
  filter_upwards [hconc z hz ε hε] with n hn
  -- The image of the disc is open, so measurable, and lies in `S ∩ N`.
  have hs : MeasurableSet (ball z ε ∩ Ω) := measurableSet_ball.inter hΩ.measurableSet
  have hgsS : g '' (ball z ε ∩ Ω) ⊆ thricePuncturedSphereReal := by
    rintro _ ⟨y, hy, rfl⟩
    exact positiveEndChart_mem_thricePuncturedSphereReal
      ((le_max_right _ _).trans_lt (hΩT y hy.2).1)
  refine TauCeti.MeasureTheory.le_withDensity_of_le_setLIntegral
    (hgo _ (isOpen_ball.inter hΩ)).measurableSet hgsS
    (image_subset_iff.2 (inter_subset_left.trans hεN)) ?_
  rw [← SmoothTwoForm.setLIntegral_floerEnergyDensity_comp_positiveEndChart_add_eq q
    (fun w x hw ↦ pairOfPantsPerturbation_eq_smul_endAngularForm (hT.trans hw) x) (hH q) (hHd q)
    (hu _) m hs fun y hy ↦ hΩT y hy.2]
  exact (ENNReal.ofReal_le_ofReal hn).trans
    TauCeti.MeasureTheory.ofReal_integral_le_lintegral_ofReal


omit [I.Boundaryless] [CompactSpace M] in
/-- The energy of a Floer pair of pants in a manifold whose topological energy is at most `A` is
at most `A + B_0 + B_1 + B_∞`, which is nonnegative. -/
private theorem nonneg_and_lintegral_floerEnergyDensity_le (hω : ω.IsNondegenerate)
    (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (H q)))
    {B : Puncture → ℝ} (hB : ∀ q t x, |H q t x| ≤ B q)
    (hJt : ∀ z ∈ thricePuncturedSphereReal, ∀ x, (hω.symplecticFormAt x).Tames (J z x))
    {u : ℝ × ℝ → M} (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u thricePuncturedSphereReal)
    (hfl : ∀ z ∈ thricePuncturedSphereReal,
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z (u z))
        (ω.perturbedMFDeriv
          (fun z x ↦ pairOfPantsPerturbation H (equivRealProdCLM.symm z) x 1)
          (fun z x ↦ pairOfPantsPerturbation H (equivRealProdCLM.symm z) x Complex.I)
          u z).toLinearMap)
    {x : Puncture → ℝ → M}
    (hx : ∀ q t, Tendsto (fun R : ℝ ↦ u (equivRealProdCLM
      (q.cylindricalEndLift (↑(q.endSign * R) + ↑t * Complex.I)))) atTop (𝓝 (x q t)))
    (hE : IntegrableOn (ω.floerEnergyDensity
      (fun z x ↦ pairOfPantsPerturbation H (equivRealProdCLM.symm z) x 1)
      (fun z x ↦ pairOfPantsPerturbation H (equivRealProdCLM.symm z) x Complex.I) u)
      thricePuncturedSphereReal)
    (hA : IntegrableOn (fun z ↦ (SmoothBundleForm.eval₂ ω (u z)
      (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
      (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ)) thricePuncturedSphereReal)
    {A : ℝ} (htop : (∫ z in thricePuncturedSphereReal, (SmoothBundleForm.eval₂ ω (u z)
        (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
        (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ)) +
      ∑ q, q.endSign * ∫ t in (0 : ℝ)..1, H q t (x q t) ≤ A) :
    0 ≤ A + ∑ q, B q ∧ ∫⁻ z in thricePuncturedSphereReal, ENNReal.ofReal (ω.floerEnergyDensity
      (fun z x ↦ pairOfPantsPerturbation H (equivRealProdCLM.symm z) x 1)
      (fun z x ↦ pairOfPantsPerturbation H (equivRealProdCLM.symm z) x Complex.I) u z) ≤
        ENNReal.ofReal (A + ∑ q, B q) := by
  have hS := isOpen_thricePuncturedSphereReal.measurableSet
  have h0 (z : ℝ × ℝ) (hz : z ∈ thricePuncturedSphereReal) :=
    floerEnergyDensity_nonneg hω (hJt z hz _) (hfl z hz)
  have h := hω.setIntegral_floerEnergyDensity_pairOfPantsPerturbation_le hH hHs hB hu hx hE hA
    (J := fun z ↦ J z (u z)) (fun z hz ↦ hJt z hz _) hfl subset_rfl
  have hpos := setIntegral_nonneg (μ := volume) hS h0
  refine ⟨by linarith, ?_⟩
  rw [← ofReal_integral_eq_lintegral_ofReal hE (ae_restrict_of_forall_mem hS h0)]
  exact ENNReal.ofReal_le_ofReal (by linarith)

omit [I.Boundaryless] in
/-- **The data of the windows.** Under the hypotheses of the main theorem below, with
`T = max T₀ 2`, there are constants `c > 0` and `L` such that on the core truncation `S_{T + 2}`
the structures are uniformly tame with respect to `e`, `c ‖d e v‖² ≤ ω(v, J v)`, and the
pushforwards through `e` of the Hamiltonian vector fields of the perturbation are at most `L`, and
such that on each end `q` the structures `J_q` are `C²` in the charts of `M`, tame, and uniformly
tame with the same constant `c`, and the pushforwards of the Hamiltonian vector fields of the end
Hamiltonian `H'_q` are bounded. -/
private theorem exists_pos_window_data (hω : ω.IsNondegenerate) (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (H q)))
    (hJ : ∀ α, ContDiffOn ℝ 2 (almostComplexInChartAt I α J)
      (thricePuncturedSphereReal ×ˢ (extChartAt I α).target))
    (hJt : ∀ z ∈ thricePuncturedSphereReal, ∀ x, (hω.symplecticFormAt x).Tames (J z x))
    {T₀ : ℝ} {Jq : Puncture → ℝ → (x : M) → AlmostComplexStructure (TangentSpace I x)}
    (hJe : ∀ q s t x, T₀ ≤ s → J (endChart q (q.endSign * s, t)) x = Jq q t x)
    (he : ContMDiff I 𝓘(ℝ, F) 1 e) :
    ∃ c > 0, ∃ L,
      (∀ z ∈ equivRealProdCLM.symm ⁻¹' truncation (max T₀ 2 + 2), ∀ x v,
        c * ‖mvfderiv I e x v‖ ^ 2 ≤ hω.symplecticFormAt x v (J z x v)) ∧
      (∀ z ∈ equivRealProdCLM.symm ⁻¹' truncation (max T₀ 2 + 2), ∀ x,
        ‖mvfderiv I e x (ω.hamiltonianVectorField
          (fun y ↦ pairOfPantsPerturbation H (equivRealProdCLM.symm z) y 1) x)‖ ≤ L ∧
        ‖mvfderiv I e x (ω.hamiltonianVectorField
          (fun y ↦ pairOfPantsPerturbation H (equivRealProdCLM.symm z) y Complex.I) x)‖ ≤ L) ∧
      ∀ q, (∀ α, ContDiffOn ℝ 2 (almostComplexInChartAt I α (Jq q))
          (univ ×ˢ (extChartAt I α).target)) ∧
        (∀ t x, (hω.symplecticFormAt x).Tames (Jq q t x)) ∧
        (∀ t x v, c * ‖mvfderiv I e x v‖ ^ 2 ≤ hω.symplecticFormAt x v (Jq q t x v)) ∧
        ∃ L', ∀ t x,
          ‖mvfderiv I e x (ω.hamiltonianVectorField (positiveEndHamiltonian H q t) x)‖ ≤ L' := by
  set T := max T₀ 2
  have hT : 2 ≤ T := le_max_right _ _
  -- On the end `q` the structures are those on the circle `φ_q(±T, t)` of `S`.
  have hmem (q : Puncture) (t : ℝ) : endChart q (q.endSign * T, t) ∈ thricePuncturedSphereReal :=
    endChart_mem_thricePuncturedSphereReal (by rw [Puncture.endSign_mul_endSign_mul]; linarith)
  have hJq (q : Puncture) : Jq q = fun t ↦ J (endChart q (q.endSign * T, t)) :=
    funext fun t ↦ funext fun x ↦ (hJe q T t x (le_max_left _ _)).symm
  have hJqs (q : Puncture) (α : M) : ContDiffOn ℝ 2 (almostComplexInChartAt I α (Jq q))
      (univ ×ˢ (extChartAt I α).target) := by
    rw [hJq, funext (almostComplexInChartAt_comp (I := I) (α := α) (J := J)
      fun t ↦ endChart q (q.endSign * T, t))]
    refine (hJ α).comp (s := univ ×ˢ (extChartAt I α).target)
      (f := fun p : ℝ × E ↦ (endChart q (q.endSign * T, p.1), p.2)) ?_
      fun p hp ↦ ⟨hmem q p.1, hp.2⟩
    exact (((contDiff_endChart q 2).comp (contDiff_const.prodMk contDiff_fst)).prodMk
      contDiff_snd).contDiffOn
  have hJqt (q : Puncture) (t : ℝ) (x : M) : (hω.symplecticFormAt x).Tames (Jq q t x) := by
    rw [hJq]
    exact hJt _ (hmem q t) x
  -- One tameness constant serves the core truncation and the circles `φ_q(±T, t)`, `0 ≤ t ≤ 1`.
  set Dt : Set (ℝ × ℝ) := equivRealProdCLM.symm ⁻¹' truncation (T + 2) ∪
    ⋃ q, (fun t ↦ endChart q (q.endSign * T, t)) '' Icc 0 1
  have hDtS : Dt ⊆ thricePuncturedSphereReal :=
    union_subset (preimage_truncation_subset_thricePuncturedSphereReal _)
      (iUnion_subset fun q ↦ by rintro _ ⟨t, -, rfl⟩; exact hmem q t)
  obtain ⟨c, hc, hJc⟩ := hω.exists_pos_forall_mul_norm_mvfderiv_sq_le
    ((isCompact_preimage_truncation _).union (isCompact_iUnion fun q ↦ isCompact_Icc.image
      ((contDiff_endChart q 0).continuous.comp (continuous_const.prodMk continuous_id))))
    isCompact_univ (fun α _ ↦ (hJ α).continuousOn.mono (prod_mono hDtS subset_rfl))
    (fun z hz x _ ↦ hJt z (hDtS hz) x) he
  have hJqc (q : Puncture) (t : ℝ) (x : M) (v : TangentSpace I x) :
      c * ‖mvfderiv I e x v‖ ^ 2 ≤ hω.symplecticFormAt x v (Jq q t x v) := by
    -- The end chart is `1`-periodic in `t`, so `φ_q(±T, t)` lies on the circle over `[0, 1)`.
    obtain ⟨t', ht', heq⟩ := (periodic_comp_endChart q id (q.endSign * T)).exists_mem_Ico₀ one_pos t
    have h : c * ‖mvfderiv I e x v‖ ^ 2 ≤
        hω.symplecticFormAt x v (J (endChart q (q.endSign * T, t')) x v) :=
      hJc _ (Or.inr (mem_iUnion.2 ⟨q, t', Ico_subset_Icc_self ht', rfl⟩)) x (mem_univ x) v
    rw [hJq]
    rwa [← show endChart q (q.endSign * T, t) = endChart q (q.endSign * T, t') from heq] at h
  have hD := isCompact_preimage_truncation (T + 2)
  have hDS := preimage_truncation_subset_thricePuncturedSphereReal (T + 2)
  obtain ⟨Ls, hLs⟩ := exists_forall_norm_mvfderiv_hamiltonianVectorField_pairOfPantsPerturbation_le
    hω hH hHs he hD hDS 1
  obtain ⟨Lt, hLt⟩ := exists_forall_norm_mvfderiv_hamiltonianVectorField_pairOfPantsPerturbation_le
    hω hH hHs he hD hDS Complex.I
  exact ⟨c, hc, max Ls Lt, fun z hz x ↦ hJc z (Or.inl hz) x (mem_univ x), fun z hz x ↦
    ⟨(hLs z hz x).trans (le_max_left _ _), (hLt z hz x).trans (le_max_right _ _)⟩,
    fun q ↦ ⟨hJqs q, hJqt q, hJqc q, hω.exists_forall_norm_mvfderiv_hamiltonianVectorField_le
      (contMDiff_uncurry_positiveEndHamiltonian (hHs q)) (periodic_positiveEndHamiltonian (hH q))
      he⟩⟩

/-- **The windows of a pair of pants in a closed manifold, with one threshold.** Under the
hypotheses of the main theorem below, there is a threshold `δ > 0` such that on every window, every
subsequence of a sequence of solutions has a further subsequence along which the solutions read
through `e` converge off a set at each point of which the energy measure of every neighbourhood
is eventually at least `δ`. -/
private theorem exists_pos_forall_window
    (hω : ω.IsNondegenerate) (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 3 (uncurry (H q)))
    {B : Puncture → ℝ} (hB : ∀ q t x, |H q t x| ≤ B q)
    (hJ : ∀ α, ContDiffOn ℝ 2 (almostComplexInChartAt I α J)
      (thricePuncturedSphereReal ×ˢ (extChartAt I α).target))
    (hJt : ∀ z ∈ thricePuncturedSphereReal, ∀ x, (hω.symplecticFormAt x).Tames (J z x))
    {T₀ : ℝ} {Jq : Puncture → ℝ → (x : M) → AlmostComplexStructure (TangentSpace I x)}
    (hJe : ∀ q s t x, T₀ ≤ s → J (endChart q (q.endSign * s, t)) x = Jq q t x)
    (he : ContMDiff I 𝓘(ℝ, F) 1 e) (he_inj : Injective e) :
    ∃ δ > 0, ∀ ⦃u : ℕ → ℝ × ℝ → M⦄ ⦃x : ℕ → Puncture → ℝ → M⦄ ⦃A : ℝ⦄,
      (∀ k, ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 3 (u k) thricePuncturedSphereReal) →
      (∀ k, ∀ z ∈ thricePuncturedSphereReal,
        IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z (u k z))
          (ω.perturbedMFDeriv
            (fun z x ↦ pairOfPantsPerturbation H (equivRealProdCLM.symm z) x 1)
            (fun z x ↦ pairOfPantsPerturbation H (equivRealProdCLM.symm z) x Complex.I)
            (u k) z).toLinearMap) →
      (∀ k q t, Tendsto (fun R : ℝ ↦ u k (equivRealProdCLM
        (q.cylindricalEndLift (↑(q.endSign * R) + ↑t * Complex.I)))) atTop (𝓝 (x k q t))) →
      (∀ k, IntegrableOn (ω.floerEnergyDensity
        (fun z x ↦ pairOfPantsPerturbation H (equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation H (equivRealProdCLM.symm z) x Complex.I) (u k))
        thricePuncturedSphereReal) →
      (∀ k, IntegrableOn (fun z ↦ (SmoothBundleForm.eval₂ ω (u k z)
        (mfderiv 𝓘(ℝ, ℝ × ℝ) I (u k) z stdComplexLineReal)
        (mfderiv 𝓘(ℝ, ℝ × ℝ) I (u k) z stdComplexLineImag) : ℝ)) thricePuncturedSphereReal) →
      (∀ k, (∫ z in thricePuncturedSphereReal, (SmoothBundleForm.eval₂ ω (u k z)
          (mfderiv 𝓘(ℝ, ℝ × ℝ) I (u k) z stdComplexLineReal)
          (mfderiv 𝓘(ℝ, ℝ × ℝ) I (u k) z stdComplexLineImag) : ℝ)) +
        ∑ q, q.endSign * ∫ t in (0 : ℝ)..1, H q t (x k q t) ≤ A) →
      ∀ i ⦃ψ : ℕ → ℕ⦄, StrictMono ψ → ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ Z : Set (ℝ × ℝ),
        (∀ z ∈ Z, ∀ N ∈ 𝓝 z, ∀ᶠ n in atTop, ENNReal.ofReal δ ≤
          (volume.restrict thricePuncturedSphereReal).withDensity (fun y ↦ ENNReal.ofReal
            (ω.floerEnergyDensity
              (fun z x ↦ pairOfPantsPerturbation H (equivRealProdCLM.symm z) x 1)
              (fun z x ↦ pairOfPantsPerturbation H (equivRealProdCLM.symm z) x Complex.I)
              (u (ψ (φ n))) y)) N) ∧
        ∃ v : ℝ × ℝ → F, TendstoLocallyUniformlyOn (fun n ↦ e ∘ u (ψ (φ n))) v atTop
          (window (max T₀ 2) i \ Z) := by
  set T := max T₀ 2
  have hT : 2 ≤ T := le_max_right _ _
  have hed : ∀ x, MDifferentiableAt I 𝓘(ℝ, F) e x := he.mdifferentiable one_ne_zero
  obtain ⟨c, hc, L, hJc, hL, hq⟩ := exists_pos_window_data hω hH
    (fun q ↦ (hHs q).of_le (by norm_num)) hJ hJt hJe he
  -- The thresholds of the two windows of each end, uniform in the translation, and of the core.
  choose δe hδe hconve using fun q b ↦
    hω.exists_pos_forall_tendstoLocallyUniformlyOn_comp_subseq_off_finset_comp_positiveEndChart
      (K := pairOfPantsPerturbation H) (T₀ := T)
      (fun w x hw ↦ pairOfPantsPerturbation_eq_smul_endAngularForm (hT.trans hw) x) (hH q)
      (hHs q) (fun s t x hs ↦ hJe q s t x ((le_max_left _ _).trans hs)) (hq q).1 (hq q).2.1 hed
      he_inj hc (hq q).2.2.1 (hq q).2.2.2.choose_spec
      (D := Icc (T + 1) (T + 3) ×ˢ Icc ((bif b then (1 / 2 : ℝ) else 0) - 2 / 5)
        ((bif b then 1 / 2 else 0) + 2 / 5)) (isCompact_Icc.prod isCompact_Icc)
      (t₀ := (bif b then 1 / 2 else 0) - 1 / 2) (fun y hy ↦ by
        have h := add_mem_Ioi_prod_Ioo (m := 0) (by linarith) le_rfl hy
        rwa [Prod.mk_zero_zero, add_zero] at h)
  obtain ⟨δc, hδc, hconvc⟩ :=
    hω.exists_pos_forall_tendstoLocallyUniformlyOn_comp_subseq_off_finset_pairOfPantsPerturbation
      hH hHs hB hJ hJt hed he_inj (isCompact_preimage_truncation (T + 2))
      (preimage_truncation_subset_thricePuncturedSphereReal (T + 2)) hc hJc
      (fun z hz x ↦ (hL z hz x).1) fun z hz x ↦ (hL z hz x).2
  refine ⟨min δc (Finset.univ.inf' ⟨(.zero, false), Finset.mem_univ _⟩
    fun p : Puncture × Bool ↦ δe p.1 p.2), lt_min hδc ((Finset.lt_inf'_iff _).2 fun p _ ↦
      hδe p.1 p.2), fun u x A hu hfl hx hE hA htop i ψ _ ↦ ?_⟩
  rcases i with _ | ⟨q, m, b⟩
  · obtain ⟨φ, hφ, Z, -, -, hc, -, v, -, hv, -⟩ := hconvc (u := u ∘ ψ) (x := x ∘ ψ)
      (isOpen_window _ none) (window_none_subset _) (fun k ↦ hu _) (fun k ↦ hfl _)
      (fun k ↦ hx _) (fun k ↦ hE _) (fun k ↦ hA _) (fun k ↦ htop _)
    exact ⟨φ, hφ, ↑Z, fun z hz ↦
      eventually_ofReal_le_withDensity_of_forall_eventually_le_setIntegral_ball
        (isOpen_window _ none).measurableSet (fun y hy ↦ hy.1)
        fun ε hε ↦ (hc z hz ε hε).mono fun n hn ↦ (min_le_left _ _).trans hn, e ∘ v, hv⟩
  · have hEb (k : ℕ) := nonneg_and_lintegral_floerEnergyDensity_le hω hH
      (fun q ↦ (hHs q).of_le (by norm_num)) hB hJt ((hu k).of_le (by norm_num)) (hfl k) (hx k)
      (hE k) (hA k) (htop k)
    have hΩT (y : ℝ × ℝ) (hy : y ∈ endWindow T b) :=
      add_mem_Ioi_prod_Ioo (by linarith) (Nat.cast_nonneg m)
        (prod_mono Ioo_subset_Icc_self Ioo_subset_Icc_self hy)
    obtain ⟨φ, hφ, Z, hZΩ, -, hc, -, v, -, hv, -⟩ := hconve q b (Ω := endWindow T b)
      (u := u ∘ ψ) (R := fun _ ↦ (m : ℝ)) (isOpen_Ioo.prod isOpen_Ioo)
      (prod_mono Ioo_subset_Icc_self Ioo_subset_Icc_self) (fun _ ↦ Nat.cast_nonneg m)
      (fun k ↦ hu _) (fun k ↦ hfl _) (hEb 0).1 fun k ↦ (hEb _).2
    exact ⟨φ, hφ, _, eventually_ofReal_le_withDensity_image_positiveEndChart_add hH
      (fun q t ↦ ((hHs q).comp (contMDiff_const.prodMk contMDiff_id)).mdifferentiable (by norm_num))
      (fun k ↦ (hu (ψ k)).mdifferentiableOn (by norm_num)) hT (isOpen_Ioo.prod isOpen_Ioo) hΩT
      (fun z hz ε hε ↦ (hc z hz ε hε).mono fun n hn ↦ ((min_le_right _ _).trans
        (Finset.inf'_le (fun p : Puncture × Bool ↦ δe p.1 p.2) (Finset.mem_univ (q, b)))).trans
          hn),
      exists_tendstoLocallyUniformlyOn_image_positiveEndChart_add (isOpen_Ioo.prod isOpen_Ioo)
        hΩT hZΩ (f := fun n ↦ e ∘ u (ψ (φ n))) hv⟩

/-- **Floer pairs of pants in a closed manifold converge off finitely many bubbling points on the
whole domain.** Let `ω` be a nondegenerate two-form on a closed manifold `M`, such as a closed
symplectic manifold, let `K` be the pair-of-pants perturbation of period-one `C³` Hamiltonians
`H_q` with `|H_q| ≤ B_q`, and let `J(z, x)` be structures on the tangent spaces of `M`, tamed by `ω`
for `z ∈ S = ℂ ∖ {0, 1}` (read in real coordinates) and `C²` read in the chart at every point of
`M`, which beyond `T₀` on each end `q` are structures `J_q(t, x)` in the end coordinates. Let
`e : M → F` be an injective `C¹` map into a normed space, such as the Whitney embedding. There is a
threshold `δ > 0` with the following property. Let `uₖ` be `C³` solutions of
`(du - X_K)^{0,1} = 0` on `S` for `J(z, u)`, whose end loops `t ↦ uₖ(φ_q(±R + i t))` converge
pointwise to loops `xₖ(q)` as `R → ∞`, with integrable energy and area densities and topological
energy `∫_S uₖ^*ω + ∑ q, ±∫₀¹ H_q(t, xₖ(q)(t)) dt ≤ A`. Then there are a subsequence `φ`, a finite
set `Z ⊆ S` with `#Z * δ ≤ A + B_0 + B_1 + B_∞` and a map `v : S \ Z → M`, continuous, such that
along `φ` every disc about a point of `Z` eventually carries energy at least `δ`, and the
solutions converge to `v` on `S \ Z`, locally uniformly after applying `e` and pointwise in `M`. -/
theorem exists_pos_forall_tendstoLocallyUniformlyOn_comp_subseq_off_finset_thricePuncturedSphereReal
    (hω : ω.IsNondegenerate) (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 3 (uncurry (H q)))
    {B : Puncture → ℝ} (hB : ∀ q t x, |H q t x| ≤ B q)
    (hJ : ∀ α, ContDiffOn ℝ 2 (almostComplexInChartAt I α J)
      (thricePuncturedSphereReal ×ˢ (extChartAt I α).target))
    (hJt : ∀ z ∈ thricePuncturedSphereReal, ∀ x, (hω.symplecticFormAt x).Tames (J z x))
    {T₀ : ℝ} {Jq : Puncture → ℝ → (x : M) → AlmostComplexStructure (TangentSpace I x)}
    (hJe : ∀ q s t x, T₀ ≤ s → J (endChart q (q.endSign * s, t)) x = Jq q t x)
    (he : ContMDiff I 𝓘(ℝ, F) 1 e) (he_inj : Injective e) :
    ∃ δ > 0, ∀ ⦃u : ℕ → ℝ × ℝ → M⦄ ⦃x : ℕ → Puncture → ℝ → M⦄ ⦃A : ℝ⦄,
      (∀ k, ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 3 (u k) thricePuncturedSphereReal) →
      (∀ k, ∀ z ∈ thricePuncturedSphereReal,
        IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z (u k z))
          (ω.perturbedMFDeriv
            (fun z x ↦ pairOfPantsPerturbation H (equivRealProdCLM.symm z) x 1)
            (fun z x ↦ pairOfPantsPerturbation H (equivRealProdCLM.symm z) x Complex.I)
            (u k) z).toLinearMap) →
      (∀ k q t, Tendsto (fun R : ℝ ↦ u k (equivRealProdCLM
        (q.cylindricalEndLift (↑(q.endSign * R) + ↑t * Complex.I)))) atTop (𝓝 (x k q t))) →
      (∀ k, IntegrableOn (ω.floerEnergyDensity
        (fun z x ↦ pairOfPantsPerturbation H (equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation H (equivRealProdCLM.symm z) x Complex.I) (u k))
        thricePuncturedSphereReal) →
      (∀ k, IntegrableOn (fun z ↦ (SmoothBundleForm.eval₂ ω (u k z)
        (mfderiv 𝓘(ℝ, ℝ × ℝ) I (u k) z stdComplexLineReal)
        (mfderiv 𝓘(ℝ, ℝ × ℝ) I (u k) z stdComplexLineImag) : ℝ)) thricePuncturedSphereReal) →
      (∀ k, (∫ z in thricePuncturedSphereReal, (SmoothBundleForm.eval₂ ω (u k z)
          (mfderiv 𝓘(ℝ, ℝ × ℝ) I (u k) z stdComplexLineReal)
          (mfderiv 𝓘(ℝ, ℝ × ℝ) I (u k) z stdComplexLineImag) : ℝ)) +
        ∑ q, q.endSign * ∫ t in (0 : ℝ)..1, H q t (x k q t) ≤ A) →
      ∃ (φ : ℕ → ℕ) (Z : Finset (ℝ × ℝ)) (v : ℝ × ℝ → M), StrictMono φ ∧
        ↑Z ⊆ thricePuncturedSphereReal ∧ Z.card * δ ≤ A + ∑ q, B q ∧
        (∀ z ∈ Z, ∀ ε > 0, ∀ᶠ n in atTop, δ ≤ ∫ y in ball z ε ∩ thricePuncturedSphereReal,
          ω.floerEnergyDensity
            (fun z x ↦ pairOfPantsPerturbation H (equivRealProdCLM.symm z) x 1)
            (fun z x ↦ pairOfPantsPerturbation H (equivRealProdCLM.symm z) x Complex.I)
            (u (φ n)) y) ∧
        ContinuousOn v (thricePuncturedSphereReal \ ↑Z) ∧
        TendstoLocallyUniformlyOn (fun n ↦ e ∘ u (φ n)) (e ∘ v) atTop
          (thricePuncturedSphereReal \ ↑Z) ∧
        ∀ z ∈ thricePuncturedSphereReal \ ↑Z, Tendsto (fun n ↦ u (φ n) z) atTop (𝓝 (v z)) := by
  obtain ⟨δ, hδ, hwin⟩ := exists_pos_forall_window hω hH hHs hB hJ hJt hJe he he_inj
  refine ⟨δ, hδ, fun u x A hu hfl hx hE hA htop ↦ ?_⟩
  have hEb (k : ℕ) := nonneg_and_lintegral_floerEnergyDensity_le hω hH
    (fun q ↦ (hHs q).of_le (by norm_num)) hB hJt ((hu k).of_le (by norm_num)) (hfl k) (hx k)
    (hE k) (hA k) (htop k)
  -- Assemble the windows by the diagonal argument, for the energy measures of the `uₖ` on `S`.
  obtain ⟨φ, Z, g, hφ, hZ, hcard, hconc, hconv⟩ :=
    exists_tendstoLocallyUniformlyOn_subseq_off_finset_iUnion (isOpen_window (max T₀ 2))
      (F := fun k ↦ e ∘ u k) (ENNReal.ofReal_pos.2 hδ).ne' ENNReal.ofReal_ne_top
      (fun k ↦ (measure_mono (subset_univ _)).trans (by
        rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]; exact (hEb k).2))
      (hwin hu hfl hx hE hA htop)
  rw [iUnion_window (by positivity)] at hZ hconv
  -- The limit is continuous, and it is read back in `M` through the embedding `e`.
  have hg : ContinuousOn g (thricePuncturedSphereReal \ ↑Z) :=
    hconv.continuousOn (Eventually.of_forall fun n ↦
      (he.continuous.comp_continuousOn (hu (φ n)).continuousOn).mono sdiff_subset).frequently
  obtain ⟨v, hv, -, hev, hpt⟩ := isCompact_univ.exists_tendsto_of_tendsto_comp
    he.continuous.continuousOn he_inj.injOn (fun _ _ ↦ .of_forall fun _ ↦ mem_univ _) hg
    fun z hz ↦ hconv.tendsto_at hz
  refine ⟨φ, Z, v, hφ, hZ, (ENNReal.natCast_mul_ofReal_le_ofReal_iff (hEb 0).1).1 hcard,
    fun z hz ε hε ↦ ?_, hv, hconv.congr_right hev.symm, hpt⟩
  -- The energy measure of a disc is the energy over its part in `S`.
  filter_upwards [hconc z hz _ (ball_mem_nhds z hε)] with n hn
  exact TauCeti.MeasureTheory.le_setIntegral_of_ofReal_le_withDensity measurableSet_ball
    isOpen_thricePuncturedSphereReal.measurableSet ((hE _).mono_set inter_subset_right)
    (fun y hy ↦ floerEnergyDensity_nonneg hω (hJt y hy.2 _) (hfl (φ n) y hy.2)) hn

end TauCeti.SmoothTwoForm.IsNondegenerate
