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
import TauCeti.Geometry.Symplectic.Floer.Compactness.EndWindow
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
where they take their values, and for families. In the namespace
`TauCeti.SmoothTwoForm.IsNondegenerate`,
`exists_pos_forall_tendsto_tendstoLocallyUniformlyOn_comp_subseq_off_finset_of_cylindrical` treats
perturbations `K_p` and structures `J_p` depending on a parameter `p` in a compact window `C` of a
finite-dimensional space, `C²` in the charts of `M` jointly in `(p, z)`, which are cylindrical on
the ends with data independent of `p`: beyond `T₀` on the end `q`, `K_p = H_q(t) dt` and
`J_p = J_q(t)`. Solutions for parameters `pₖ ∈ C` of energy at most `E` have a subsequence whose
parameters converge in `C` and which converges on `S` off a finite set `Z` with `#Z * δ ≤ E`. This
is the form of compactness that the families of the pair-of-pants product take on `S` over a
compact window of parameters, for instance the continuation family with bounded neck positions.
The pair of pants itself is the case of a one-point parameter space,
`exists_pos_forall_tendstoLocallyUniformlyOn_comp_subseq_off_finset_thricePuncturedSphereReal`, for
solutions of topological energy `∫_S uₖ^*ω + ∑ q, ±∫₀¹ H_q(t, xₖ(q)(t)) dt ≤ A`.

As in `TauCeti.Geometry.Symplectic.Floer.PairOfPants.Compactness.Closed`, whose theorems on the core
window and on the translated end windows replace those of a vector space, sizes in `M` are measured
through an injective `C¹` map `e : M → F` into a normed space, such as the Whitney embedding. On
the core the family theorem takes uniform tameness with respect to `e` and bounds on the
pushforwards through `e` of the Hamiltonian vector fields as hypotheses over compact parts of `S`;
for the pair of pants they hold by compactness
(`TauCeti.SmoothTwoForm.IsNondegenerate.exists_pos_forall_mul_norm_mvfderiv_sq_le`,
`exists_forall_norm_mvfderiv_hamiltonianVectorField_pairOfPantsPerturbation_le`). On the ends the
constants are derived: the end Hamiltonians are periodic on a compact manifold, and beyond `T₀` the
structures are those of the circle `t ↦ φ_q(±T, t)` of `S` for any parameter, so they are `C²` in
the charts of `M` and one constant `c > 0` with `c ‖d e v‖² ≤ ω(v, J v)` serves the core and these
circles, which form a compact part of `S`. The threshold of the end windows depends only on the end
data (`exists_pos_forall_tendstoLocallyUniformlyOn_comp_subseq_off_finset_comp_positiveEndChart`),
so it does not change along the family. The diagonal argument runs with the readings `e ∘ uₖ`,
whose energy on a window of an end is the energy of `uₖ` on its image
(`TauCeti.SmoothTwoForm.setLIntegral_floerEnergyDensity_comp_positiveEndChart_add_eq`), and the
limit is read back in `M` through `e` (`IsCompact.exists_tendsto_of_tendsto_comp`): the solutions
converge locally uniformly after applying `e`, and pointwise in `M`. The windows also give bounds
on the energy densities near every point off their bubbling points; read on `S` through the
Jacobian of the end chart
(`TauCeti.SmoothTwoForm.floerEnergyDensity_comp_positiveEndChart`), they pass through the diagonal
argument (`TauCeti.exists_tendstoLocallyUniformlyOn_subseq_off_finset_iUnion_of_le`), so the energy
densities are eventually bounded near every point of `S \ Z`. These bounds make the limit a
`C¹` Floer solution on `S \ Z`, in
`TauCeti.Geometry.Symplectic.Floer.PairOfPants.Compactness.Regularity`.

Energy that escapes along the ends is not seen by the limit: this is the breaking of Floer
cylinders off the ends, which is not treated here, nor are the bubbles at the points of `Z`.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., Section 4.6
  (bubbling off finitely many points on a noncompact domain).
* M. Schwarz, *Cohomology operations from S¹-cobordisms in Floer homology*, PhD thesis,
  ETH Zürich (1995), on the compactness of the moduli spaces of the pair-of-pants product.
-/

public section

open Complex Filter Function MeasureTheory Metric Set Topology TauCeti.ThricePuncturedSphere
open scoped Manifold

namespace TauCeti.SmoothTwoForm

open Floer

variable {E G M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace G]
  {I : ModelWithCorners ℝ E G} [TopologicalSpace M] [ChartedSpace G M]
  [IsManifold I (⊤ : ℕ∞) M] {ω : SmoothTwoForm I M} {H : Puncture → ℝ → M → ℝ}

/-- **Energy concentration on a window of an end, read on `S`.** Let `Kₖ` be perturbations equal
to `H_q(t) dt` beyond `T₀` on the end `q`, let `g(y) = φ'_q(y + (m, 0))` be the translated positive
end chart of the end `q`, and let `Ω` be an open window whose translate by `(m, 0)` lies beyond
`max T 0`, for `T ≥ T₀`, in a band of angular width one. If the energy `δ` of the end readings
`uₖ ∘ g` concentrates in every disc about a point of `Z ⊆ Ω`, then every neighbourhood of a point
of `g(Z)` eventually carries energy at least `δ` for the energy measure of `uₖ` on `S`. -/
private theorem eventually_ofReal_le_withDensity_image_positiveEndChart_add
    {K : ℕ → ℂ → M → ℂ →L[ℝ] ℝ} {T₀ : ℝ}
    (hKH : ∀ k q w x, T₀ ≤ q.endSign * (q.endCoord w).re →
      K k w x = H q (q.endCoord w).im x • q.endAngularForm w)
    (hH : ∀ q, Periodic (H q) 1) (hHd : ∀ q t, MDifferentiable I 𝓘(ℝ) (H q t))
    {u : ℕ → ℝ × ℝ → M} (hu : ∀ k, MDifferentiableOn 𝓘(ℝ, ℝ × ℝ) I (u k) thricePuncturedSphereReal)
    {q : Puncture} {m : ℕ} {T t₀ : ℝ} (hT : T₀ ≤ T) {Ω : Set (ℝ × ℝ)} (hΩ : IsOpen Ω)
    (hΩT : ∀ z ∈ Ω, z + ((m : ℝ), 0) ∈ Ioi (max T 0) ×ˢ Ioo t₀ (t₀ + 1)) {δ : ℝ} {φ : ℕ → ℕ}
    {Z : Finset (ℝ × ℝ)}
    (hconc : ∀ z ∈ Z, ∀ ε > 0, ∀ᶠ n in atTop, δ ≤ ∫ y in ball z ε ∩ Ω, ω.floerEnergyDensity
      (fun _ _ ↦ 0) (fun w ↦ positiveEndHamiltonian H q w.2)
      (fun z ↦ u (φ n) (positiveEndChart q (z + ((m : ℝ), 0)))) y) :
    ∀ z ∈ (fun y ↦ positiveEndChart q (y + ((m : ℝ), 0))) '' ↑Z, ∀ N ∈ 𝓝 z,
      ∀ᶠ n in atTop, ENNReal.ofReal δ ≤ (volume.restrict thricePuncturedSphereReal).withDensity
        (fun y ↦ ENNReal.ofReal (ω.floerEnergyDensity
          (fun z x ↦ K (φ n) (equivRealProdCLM.symm z) x 1)
          (fun z x ↦ K (φ n) (equivRealProdCLM.symm z) x Complex.I)
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
    (T₀ := T) (fun w x hw ↦ hKH (φ n) q w x (hT.trans hw)) (hH q) (hHd q)
    (hu _) m hs fun y hy ↦ hΩT y hy.2]
  exact (ENNReal.ofReal_le_ofReal hn).trans
    TauCeti.MeasureTheory.ofReal_integral_le_lintegral_ofReal

/-- **Bounds on the energy densities on a window of an end, read on `S`.** Let `Kₖ` be
perturbations equal to `H_q(t) dt` beyond `T₀` on the end `q`, let `g(y) = φ'_q(y + (m, 0))` be the
translated positive end chart of the end `q`, and let `Ω` be an open window whose translate by
`(m, 0)` lies beyond `max T 0`, for `T ≥ T₀`, in a band of angular width one. If along `φ` the
energy densities of the end readings `uₖ ∘ g` are uniformly bounded on every compact subset of
`Ω \ Z`, then the energy densities of the `uₖ` are uniformly bounded near every point of
`g(Ω) \ g(Z)`, since the energy density of `uₖ ∘ g` is that of `uₖ` times the Jacobian of `g`. -/
private theorem exists_mem_nhds_forall_floerEnergyDensity_le_image_positiveEndChart_add
    {K : ℕ → ℂ → M → ℂ →L[ℝ] ℝ} {T₀ : ℝ}
    (hKH : ∀ k q w x, T₀ ≤ q.endSign * (q.endCoord w).re →
      K k w x = H q (q.endCoord w).im x • q.endAngularForm w)
    (hH : ∀ q, Periodic (H q) 1) (hHd : ∀ q t, MDifferentiable I 𝓘(ℝ) (H q t))
    {u : ℕ → ℝ × ℝ → M} (hu : ∀ k, MDifferentiableOn 𝓘(ℝ, ℝ × ℝ) I (u k) thricePuncturedSphereReal)
    {q : Puncture} {m : ℕ} {T t₀ : ℝ} (hT : T₀ ≤ T) {Ω : Set (ℝ × ℝ)} (hΩ : IsOpen Ω)
    (hΩT : ∀ z ∈ Ω, z + ((m : ℝ), 0) ∈ Ioi (max T 0) ×ˢ Ioo t₀ (t₀ + 1)) {φ : ℕ → ℕ}
    {Z : Finset (ℝ × ℝ)}
    (hbd : ∀ C, IsCompact C → C ⊆ Ω \ ↑Z → ∃ A, ∀ n, ∀ y ∈ C, ω.floerEnergyDensity
      (fun _ _ ↦ 0) (fun w ↦ positiveEndHamiltonian H q w.2)
      (fun z ↦ u (φ n) (positiveEndChart q (z + ((m : ℝ), 0)))) y ≤ A) :
    ∀ y ∈ (fun y ↦ positiveEndChart q (y + ((m : ℝ), 0))) '' Ω \
        (fun y ↦ positiveEndChart q (y + ((m : ℝ), 0))) '' ↑Z, ∃ N ∈ 𝓝 y, ∃ A,
      ∀ᶠ n in atTop, ∀ x ∈ N, ω.floerEnergyDensity
        (fun z x ↦ K (φ n) (equivRealProdCLM.symm z) x 1)
        (fun z x ↦ K (φ n) (equivRealProdCLM.symm z) x Complex.I) (u (φ n)) x ≤ A := by
  set g : ℝ × ℝ → ℝ × ℝ := fun y ↦ positiveEndChart q (y + ((m : ℝ), 0))
  have hgo : IsOpenMap g := (isOpenMap_positiveEndChart q).comp (Homeomorph.addRight _).isOpenMap
  rintro _ ⟨⟨ζ, hζ, rfl⟩, hζZ⟩
  -- A compact neighbourhood of `ζ` off the bubbling points, on which the end readings are bounded.
  obtain ⟨L, hL, hLΩ, hLc⟩ := local_compact_nhds
    ((hΩ.sdiff Z.finite_toSet.isClosed).mem_nhds ⟨hζ, fun h ↦ hζZ ⟨ζ, h, rfl⟩⟩)
  obtain ⟨A, hA⟩ := hbd L hLc hLΩ
  -- The Jacobian of the translated end chart is bounded below on it by some `c > 0`.
  have hdet : Continuous fun y : ℝ × ℝ ↦ (fderiv ℝ (positiveEndChart q) (y + ((m : ℝ), 0))).det :=
    ContinuousLinearMap.continuous_det.comp
      (((contDiff_positiveEndChart q 1).continuous_fderiv one_ne_zero).comp
        (continuous_id.add continuous_const))
  obtain ⟨c, hc, hcL⟩ : ∃ c > 0, ∀ y ∈ L,
      c ≤ (fderiv ℝ (positiveEndChart q) (y + ((m : ℝ), 0))).det := by
    obtain ⟨y₀, -, hmin⟩ := hLc.exists_isMinOn ⟨ζ, mem_of_mem_nhds hL⟩ hdet.continuousOn
    exact ⟨_, det_fderiv_positiveEndChart_pos q _, fun y hy ↦ hmin hy⟩
  refine ⟨g '' L, mem_of_superset ((hgo _ isOpen_interior).mem_nhds
    (mem_image_of_mem g (mem_interior_iff_mem_nhds.2 hL))) (image_mono interior_subset),
    max A 0 / c, .of_forall fun n ↦ ?_⟩
  rintro _ ⟨y, hy, rfl⟩
  have hyΩ := hΩT y (hLΩ hy).1
  have hyS : g y ∈ thricePuncturedSphereReal :=
    positiveEndChart_mem_thricePuncturedSphereReal ((le_max_right _ _).trans_lt hyΩ.1)
  -- The energy density of the end reading is the Jacobian times that of `u`.
  have h := SmoothTwoForm.floerEnergyDensity_comp_positiveEndChart (ω := ω) (T₀ := T)
    (fun w x hw ↦ hKH (φ n) q w x (hT.trans hw)) (hH q) (hHd q) (u := u (φ n))
    ((le_max_left _ _).trans hyΩ.1.le)
    ((hu _ _ hyS).mdifferentiableAt (isOpen_thricePuncturedSphereReal.mem_nhds hyS))
  rw [← ω.floerEnergyDensity_cylindrical_comp_add_right] at h
  have hAy : (fderiv ℝ (positiveEndChart q) (y + ((m : ℝ), 0))).det * ω.floerEnergyDensity
      (fun z x ↦ K (φ n) (equivRealProdCLM.symm z) x 1)
      (fun z x ↦ K (φ n) (equivRealProdCLM.symm z) x Complex.I) (u (φ n)) (g y) ≤ max A 0 :=
    h ▸ (hA n y hy).trans (le_max_left _ _)
  rcases lt_or_ge (ω.floerEnergyDensity (fun z x ↦ K (φ n) (equivRealProdCLM.symm z) x 1)
      (fun z x ↦ K (φ n) (equivRealProdCLM.symm z) x Complex.I) (u (φ n)) (g y)) 0 with h0 | h0
  · exact h0.le.trans (div_nonneg (le_max_right _ _) hc.le)
  · rw [le_div_iff₀ hc, mul_comm]
    exact (mul_le_mul_of_nonneg_right (hcL y hy) h0).trans hAy

end TauCeti.SmoothTwoForm

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
  -- Translate `(s, t)` into an end window, using that `φ'_q` has period one in `t`.
  obtain ⟨m, k, b, hy⟩ := exists_sub_mem_endWindow (by linarith : T + 1 < s) t
  have hper : Periodic (fun t ↦ positiveEndChart q (s, t)) 1 := positiveEndChart_add_one q s
  exact ⟨m, b, (s - m, t - k), hy, by simpa [hzc] using hper.sub_int_mul_eq k (x := t)⟩

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
  positiveEndChart_mem_thricePuncturedSphereReal <| hT.trans_lt
    (endWindow_add_mem_Ioi_prod_Ioo le_rfl (Nat.cast_nonneg m) hy).1

/-- The windows are open, since the positive end charts are open maps. -/
private theorem isOpen_window (T : ℝ) (i : Option (Puncture × ℕ × Bool)) :
    IsOpen (window T i) := by
  rcases i with _ | ⟨q, m, b⟩
  · exact isOpen_setOf_forall_fst_positiveEndCoord_lt _
  · exact (isOpenMap_positiveEndChart q).comp (Homeomorph.addRight ((m : ℝ), (0 : ℝ))).isOpenMap
      _ (isOpen_endWindow T b)

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
  refine ⟨?_, exists_tendstoLocallyUniformlyOn_image_positiveEndChart_add hΩ hΩT hZ hv⟩
  -- The concentration is the manifold statement for the constant form.
  simpa only [floerEnergyDensity_constSmooth] using
    SmoothTwoForm.eventually_ofReal_le_withDensity_image_positiveEndChart_add
      (ω := ω.constSmooth) (K := fun _ ↦ pairOfPantsPerturbation H)
      (fun _ q w x hw ↦ pairOfPantsPerturbation_eq_smul_endAngularForm hw x) hH
      (fun q t ↦ (hHd q t).mdifferentiable)
      (fun k ↦ (hu k).mdifferentiableOn) hT hΩ hΩT
      (by simpa only [floerEnergyDensity_constSmooth] using hconc)

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
      (t₀ := (bif b then 1 / 2 else 0) - 1 / 2)
      (endWindow_closed_subset_Ioi_prod_Ioo (max_le le_rfl (by linarith)) b)
      hK
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
      (u := u ∘ ψ) (R := fun _ ↦ (m : ℝ)) (isOpen_endWindow _ b)
      (endWindow_subset_Icc_prod_Icc _ b) (fun _ ↦ Nat.cast_nonneg m)
      (fun k ↦ hu _) (fun k ↦ hfl _)
      (nonneg_and_lintegral_floerEnergyDensity_le ω hH hHs hB hJt (hu 0) (hfl 0) (ha 0) (hA 0)).1
      (fun k ↦ (nonneg_and_lintegral_floerEnergyDensity_le ω hH hHs hB hJt (hu _) (hfl _) (ha _)
        (hA _)).2) (fun k y hy ↦ huK _ (positiveEndChart_add_mem (by linarith) q m hy))
    obtain ⟨hc', v', hv'⟩ :=
      concentration_and_tendstoLocallyUniformlyOn_image_positiveEndChart_add ω hH hHd
        (fun k ↦ (hu (ψ k)).differentiableOn (by norm_num)) hT (isOpen_endWindow _ b)
        (fun y hy ↦
          endWindow_add_mem_Ioi_prod_Ioo (max_le le_rfl (by linarith)) (Nat.cast_nonneg m) hy)
        hZΩ
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

variable {E G M F P : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace G] {I : ModelWithCorners ℝ E G} [I.Boundaryless] [TopologicalSpace M]
  [ChartedSpace G M] [IsManifold I ⊤ M] [CompactSpace M] [NormedAddCommGroup F]
  [NormedSpace ℝ F] [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  {ω : SmoothTwoForm I M} {H : Puncture → ℝ → M → ℝ} {e : M → F}

omit [I.Boundaryless] [FiniteDimensional ℝ P] in
/-- **The data of the windows of a family.** Under the hypotheses of the main theorem below, with
`T = max T₀ 2` and a parameter `p₀ ∈ C`, there is a constant `c > 0` such that on the core
truncation `S_{T + 2}` the structures `J_p`, `p ∈ C`, are uniformly tame with respect to `e`,
`c ‖d e v‖² ≤ ω(v, J_p v)`, and such that on each end `q` the structures `J_q` are `C²` in the
charts of `M`, tame, and uniformly tame with the same constant `c`, and the pushforwards of the
Hamiltonian vector fields of the end Hamiltonian `H'_q` are bounded. Beyond `T₀` every `J_p` is
`J_q` on the end `q`, so these are properties of `J_{p₀}` on the circles `φ_q(±T, t)`. -/
private theorem exists_pos_family_window_data (hω : ω.IsNondegenerate)
    (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (H q)))
    {J : P → ℝ × ℝ → (x : M) → AlmostComplexStructure (TangentSpace I x)}
    {W : Set (P × (ℝ × ℝ))} {C : Set P} (hCW : C ×ˢ thricePuncturedSphereReal ⊆ W)
    (hJ : ∀ α, ContDiffOn ℝ 2 (almostComplexInChartAt I α (uncurry J))
      (W ×ˢ (extChartAt I α).target))
    (hJt : ∀ p ∈ C, ∀ z ∈ thricePuncturedSphereReal, ∀ x,
      (hω.symplecticFormAt x).Tames (J p z x))
    (hJc : ∀ D, IsCompact D → D ⊆ thricePuncturedSphereReal → ∃ c > 0, ∀ p ∈ C, ∀ z ∈ D,
      ∀ x v, c * ‖mvfderiv I e x v‖ ^ 2 ≤ hω.symplecticFormAt x v (J p z x v))
    {T₀ : ℝ} {Jq : Puncture → ℝ → (x : M) → AlmostComplexStructure (TangentSpace I x)}
    (hJe : ∀ p ∈ C, ∀ q s t x, T₀ ≤ s → J p (endChart q (q.endSign * s, t)) x = Jq q t x)
    (he : ContMDiff I 𝓘(ℝ, F) 1 e) {p₀ : P} (hp₀ : p₀ ∈ C) :
    ∃ c > 0,
      (∀ p ∈ C, ∀ z ∈ equivRealProdCLM.symm ⁻¹' truncation (max T₀ 2 + 2), ∀ x v,
        c * ‖mvfderiv I e x v‖ ^ 2 ≤ hω.symplecticFormAt x v (J p z x v)) ∧
      ∀ q, (∀ α, ContDiffOn ℝ 2 (almostComplexInChartAt I α (Jq q))
          (univ ×ˢ (extChartAt I α).target)) ∧
        (∀ t x, (hω.symplecticFormAt x).Tames (Jq q t x)) ∧
        (∀ t x v, c * ‖mvfderiv I e x v‖ ^ 2 ≤ hω.symplecticFormAt x v (Jq q t x v)) ∧
        ∃ L', ∀ t x,
          ‖mvfderiv I e x (ω.hamiltonianVectorField (positiveEndHamiltonian H q t) x)‖ ≤ L' := by
  set T := max T₀ 2
  have hT : 2 ≤ T := le_max_right _ _
  -- On the end `q` the structures are those of `J_{p₀}` on the circle `φ_q(±T, t)` of `S`.
  have hmem (q : Puncture) (t : ℝ) : endChart q (q.endSign * T, t) ∈ thricePuncturedSphereReal :=
    endChart_mem_thricePuncturedSphereReal (by rw [Puncture.endSign_mul_endSign_mul]; linarith)
  have hJq (q : Puncture) : Jq q = fun t ↦ J p₀ (endChart q (q.endSign * T, t)) :=
    funext fun t ↦ funext fun x ↦ (hJe p₀ hp₀ q T t x (le_max_left _ _)).symm
  have hJqs (q : Puncture) (α : M) : ContDiffOn ℝ 2 (almostComplexInChartAt I α (Jq q))
      (univ ×ˢ (extChartAt I α).target) := by
    have h := (hJ α).comp (s := univ ×ˢ (extChartAt I α).target)
      (f := fun p : ℝ × E ↦ ((p₀, endChart q (q.endSign * T, p.1)), p.2))
      ((contDiff_const.prodMk ((contDiff_endChart q 2).comp
        (contDiff_const.prodMk contDiff_fst))).prodMk contDiff_snd).contDiffOn
      fun p hp ↦ ⟨hCW ⟨hp₀, hmem q p.1⟩, hp.2⟩
    rw [hJq]
    exact h.congr fun p _ ↦ almostComplexInChartAt_comp (J := uncurry J)
      (fun t ↦ (p₀, endChart q (q.endSign * T, t))) p
  have hJqt (q : Puncture) (t : ℝ) (x : M) : (hω.symplecticFormAt x).Tames (Jq q t x) := by
    rw [hJq]
    exact hJt p₀ hp₀ _ (hmem q t) x
  -- One tameness constant serves the core truncation and the circles `φ_q(±T, t)`, `0 ≤ t ≤ 1`.
  set Dt : Set (ℝ × ℝ) := equivRealProdCLM.symm ⁻¹' truncation (T + 2) ∪
    ⋃ q, (fun t ↦ endChart q (q.endSign * T, t)) '' Icc 0 1
  have hDtS : Dt ⊆ thricePuncturedSphereReal :=
    union_subset (preimage_truncation_subset_thricePuncturedSphereReal _)
      (iUnion_subset fun q ↦ by rintro _ ⟨t, -, rfl⟩; exact hmem q t)
  obtain ⟨c, hc, hJcD⟩ := hJc Dt ((isCompact_preimage_truncation _).union
    (isCompact_iUnion fun q ↦ isCompact_Icc.image
      ((contDiff_endChart q 0).continuous.comp (continuous_const.prodMk continuous_id)))) hDtS
  have hJqc (q : Puncture) (t : ℝ) (x : M) (v : TangentSpace I x) :
      c * ‖mvfderiv I e x v‖ ^ 2 ≤ hω.symplecticFormAt x v (Jq q t x v) := by
    -- The end chart is `1`-periodic in `t`, so `φ_q(±T, t)` lies on the circle over `[0, 1)`.
    obtain ⟨t', ht', heq⟩ := (periodic_comp_endChart q id (q.endSign * T)).exists_mem_Ico₀ one_pos t
    simp only [id_comp] at heq
    have h : c * ‖mvfderiv I e x v‖ ^ 2 ≤
        hω.symplecticFormAt x v (J p₀ (endChart q (q.endSign * T, t')) x v) :=
      hJcD p₀ hp₀ _ (Or.inr (mem_iUnion.2 ⟨q, t', Ico_subset_Icc_self ht', rfl⟩)) x v
    simpa only [hJq, heq] using h
  exact ⟨c, hc, fun p hp z hz x v ↦ hJcD p hp z (Or.inl hz) x v,
    fun q ↦ ⟨hJqs q, hJqt q, hJqc q, hω.exists_forall_norm_mvfderiv_hamiltonianVectorField_le
      (contMDiff_uncurry_positiveEndHamiltonian (hHs q)) (periodic_positiveEndHamiltonian (hH q))
      he⟩⟩

omit [FiniteDimensional ℝ E] [I.Boundaryless] [CompactSpace M] [NormedSpace ℝ F] in
/-- **An end window of a family, read on `S`.** Let `Kₖ` be perturbations equal to `H_q(t) dt`
beyond `T₀` on the end `q`, let `g(y) = φ'_q(y + (m, 0))` be the translated positive end chart and
`T ≥ max T₀ 0`. If along `φ` the end readings `uₖ ∘ g`, read through `e`, converge locally
uniformly on the end window off a finite set `Z`, at each point of which the energy `δ` of the end
readings concentrates, and their energy densities are uniformly bounded on every compact subset of
the end window off `Z`, then the solutions read through `e` converge locally uniformly on the
window `g(endWindow)` of `S` off `g(Z)`, every neighbourhood of a point of `g(Z)` eventually
carries energy at least `δ` for the energy measure of `uₖ` on `S`, and the energy densities of the
`uₖ` are uniformly bounded near every point of the window off `g(Z)`. -/
private theorem concentration_and_tendstoLocallyUniformlyOn_window_some
    {K : ℕ → ℂ → M → ℂ →L[ℝ] ℝ} {T₀ : ℝ}
    (hKH : ∀ k q w x, T₀ ≤ q.endSign * (q.endCoord w).re →
      K k w x = H q (q.endCoord w).im x • q.endAngularForm w)
    (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (H q)))
    {u : ℕ → ℝ × ℝ → M} (hu : ∀ k, MDifferentiableOn 𝓘(ℝ, ℝ × ℝ) I (u k) thricePuncturedSphereReal)
    {T : ℝ} (hT₀ : T₀ ≤ T) (hT : 0 ≤ T) (q : Puncture) (m : ℕ) (b : Bool) {δ : ℝ} {φ : ℕ → ℕ}
    {Z : Finset (ℝ × ℝ)} (hZ : ↑Z ⊆ endWindow T b)
    (hconc : ∀ z ∈ Z, ∀ ε > 0, ∀ᶠ n in atTop, δ ≤ ∫ y in ball z ε ∩ endWindow T b,
      ω.floerEnergyDensity (fun _ _ ↦ 0) (fun w ↦ positiveEndHamiltonian H q w.2)
        (fun z ↦ u (φ n) (positiveEndChart q (z + ((m : ℝ), 0)))) y)
    (hbd : ∀ C, IsCompact C → C ⊆ endWindow T b \ ↑Z → ∃ A, ∀ n, ∀ y ∈ C, ω.floerEnergyDensity
      (fun _ _ ↦ 0) (fun w ↦ positiveEndHamiltonian H q w.2)
      (fun z ↦ u (φ n) (positiveEndChart q (z + ((m : ℝ), 0)))) y ≤ A)
    {v : ℝ × ℝ → F}
    (hv : TendstoLocallyUniformlyOn
      (fun n z ↦ e (u (φ n) (positiveEndChart q (z + ((m : ℝ), 0))))) v atTop
      (endWindow T b \ ↑Z)) :
    (∀ z ∈ (fun y ↦ positiveEndChart q (y + ((m : ℝ), 0))) '' ↑Z, ∀ N ∈ 𝓝 z,
      ∀ᶠ n in atTop, ENNReal.ofReal δ ≤ (volume.restrict thricePuncturedSphereReal).withDensity
        (fun y ↦ ENNReal.ofReal (ω.floerEnergyDensity
          (fun z x ↦ K (φ n) (equivRealProdCLM.symm z) x 1)
          (fun z x ↦ K (φ n) (equivRealProdCLM.symm z) x Complex.I) (u (φ n)) y)) N) ∧
      (∀ y ∈ window T (some (q, m, b)) \ (fun y ↦ positiveEndChart q (y + ((m : ℝ), 0))) '' ↑Z,
        ∃ N ∈ 𝓝 y, ∃ A, ∀ᶠ n in atTop, ∀ x ∈ N, ω.floerEnergyDensity
          (fun z x ↦ K (φ n) (equivRealProdCLM.symm z) x 1)
          (fun z x ↦ K (φ n) (equivRealProdCLM.symm z) x Complex.I) (u (φ n)) x ≤ A) ∧
      ∃ v' : ℝ × ℝ → F, TendstoLocallyUniformlyOn (fun n ↦ e ∘ u (φ n)) v' atTop
        (window T (some (q, m, b)) \ (fun y ↦ positiveEndChart q (y + ((m : ℝ), 0))) '' ↑Z) := by
  have hΩT (y : ℝ × ℝ) (hy : y ∈ endWindow T b) :=
    endWindow_add_mem_Ioi_prod_Ioo (max_le le_rfl hT) (Nat.cast_nonneg m) hy
  have hHd (q : Puncture) (t : ℝ) : MDifferentiable I 𝓘(ℝ) (H q t) :=
    ((hHs q).comp (contMDiff_const.prodMk contMDiff_id)).mdifferentiable one_ne_zero
  exact ⟨eventually_ofReal_le_withDensity_image_positiveEndChart_add hKH hH hHd hu hT₀
    (isOpen_endWindow T b) hΩT hconc,
    exists_mem_nhds_forall_floerEnergyDensity_le_image_positiveEndChart_add hKH hH hHd hu hT₀
      (isOpen_endWindow T b) hΩT hbd,
    exists_tendstoLocallyUniformlyOn_image_positiveEndChart_add (isOpen_endWindow T b)
      hΩT hZ (f := fun n ↦ e ∘ u (φ n)) hv⟩

/-- **The windows of a family, with one threshold.** Under the hypotheses of the main theorem
below, for a parameter `p₀ ∈ C`, there is a threshold `δ > 0` such that on every window, every
subsequence of a sequence of solutions for parameters in `C`, with energy at most `E` over `S`, has
a further subsequence along which the solutions read through `e` converge off a set at each point
of which the energy measure of every neighbourhood is eventually at least `δ`, and near every other
point of the window the energy densities are eventually bounded. -/
private theorem exists_pos_forall_family_window (hω : ω.IsNondegenerate)
    {K : P → ℂ → M → ℂ →L[ℝ] ℝ}
    {J : P → ℝ × ℝ → (x : M) → AlmostComplexStructure (TangentSpace I x)}
    {W : Set (P × (ℝ × ℝ))} {C : Set P} (hW : IsOpen W) (hC : IsCompact C)
    (hCW : C ×ˢ thricePuncturedSphereReal ⊆ W)
    (hJ : ∀ α, ContDiffOn ℝ 2 (almostComplexInChartAt I α (uncurry J))
      (W ×ˢ (extChartAt I α).target))
    (hXs : ∀ α, ContDiffOn ℝ 2 (ω.hamiltonianVectorFieldInChartAt α
      (uncurry fun p z x ↦ K p (equivRealProdCLM.symm z) x 1)) (W ×ˢ (extChartAt I α).target))
    (hXt : ∀ α, ContDiffOn ℝ 2 (ω.hamiltonianVectorFieldInChartAt α
      (uncurry fun p z x ↦ K p (equivRealProdCLM.symm z) x Complex.I))
      (W ×ˢ (extChartAt I α).target))
    (hJt : ∀ p ∈ C, ∀ z ∈ thricePuncturedSphereReal, ∀ x,
      (hω.symplecticFormAt x).Tames (J p z x))
    (hJc : ∀ D, IsCompact D → D ⊆ thricePuncturedSphereReal → ∃ c > 0, ∀ p ∈ C, ∀ z ∈ D,
      ∀ x v, c * ‖mvfderiv I e x v‖ ^ 2 ≤ hω.symplecticFormAt x v (J p z x v))
    (hB : ∀ D, IsCompact D → D ⊆ thricePuncturedSphereReal → ∃ B, ∀ p ∈ C, ∀ z ∈ D, ∀ x,
      ‖mvfderiv I e x (ω.hamiltonianVectorField
        (fun y ↦ K p (equivRealProdCLM.symm z) y 1) x)‖ ≤ B ∧
      ‖mvfderiv I e x (ω.hamiltonianVectorField
        (fun y ↦ K p (equivRealProdCLM.symm z) y Complex.I) x)‖ ≤ B)
    {T₀ : ℝ} (hKH : ∀ p ∈ C, ∀ q w x, T₀ ≤ q.endSign * (q.endCoord w).re →
      K p w x = H q (q.endCoord w).im x • q.endAngularForm w)
    (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 3 (uncurry (H q)))
    {Jq : Puncture → ℝ → (x : M) → AlmostComplexStructure (TangentSpace I x)}
    (hJe : ∀ p ∈ C, ∀ q s t x, T₀ ≤ s → J p (endChart q (q.endSign * s, t)) x = Jq q t x)
    (he : ContMDiff I 𝓘(ℝ, F) 1 e) (he_inj : Injective e) {p₀ : P} (hp₀ : p₀ ∈ C) :
    ∃ δ > 0, ∀ ⦃p : ℕ → P⦄ ⦃u : ℕ → ℝ × ℝ → M⦄ ⦃E : ℝ⦄, (∀ k, p k ∈ C) →
      (∀ k, ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 3 (u k) thricePuncturedSphereReal) →
      (∀ k, ∀ z ∈ thricePuncturedSphereReal,
        IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J (p k) z (u k z))
          (ω.perturbedMFDeriv (fun z x ↦ K (p k) (equivRealProdCLM.symm z) x 1)
            (fun z x ↦ K (p k) (equivRealProdCLM.symm z) x Complex.I) (u k) z).toLinearMap) →
      (∀ k, IntegrableOn (ω.floerEnergyDensity (fun z x ↦ K (p k) (equivRealProdCLM.symm z) x 1)
        (fun z x ↦ K (p k) (equivRealProdCLM.symm z) x Complex.I) (u k))
        thricePuncturedSphereReal) →
      0 ≤ E →
      (∀ k, ∫⁻ z in thricePuncturedSphereReal, ENNReal.ofReal (ω.floerEnergyDensity
        (fun z x ↦ K (p k) (equivRealProdCLM.symm z) x 1)
        (fun z x ↦ K (p k) (equivRealProdCLM.symm z) x Complex.I) (u k) z) ≤ ENNReal.ofReal E) →
      (∀ k, ∫ z in window (max T₀ 2) none, ω.floerEnergyDensity
        (fun z x ↦ K (p k) (equivRealProdCLM.symm z) x 1)
        (fun z x ↦ K (p k) (equivRealProdCLM.symm z) x Complex.I) (u k) z ≤ E) →
      ∀ i ⦃ψ : ℕ → ℕ⦄, StrictMono ψ → ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ Z : Set (ℝ × ℝ),
        (∀ z ∈ Z, ∀ N ∈ 𝓝 z, ∀ᶠ n in atTop, ENNReal.ofReal δ ≤
          (volume.restrict thricePuncturedSphereReal).withDensity (fun y ↦ ENNReal.ofReal
            (ω.floerEnergyDensity (fun z x ↦ K (p (ψ (φ n))) (equivRealProdCLM.symm z) x 1)
              (fun z x ↦ K (p (ψ (φ n))) (equivRealProdCLM.symm z) x Complex.I)
              (u (ψ (φ n))) y)) N) ∧
        (∀ y ∈ window (max T₀ 2) i \ Z, ∃ N ∈ 𝓝 y, ∃ A, ∀ᶠ n in atTop, ∀ x ∈ N,
          ω.floerEnergyDensity (fun z x ↦ K (p (ψ (φ n))) (equivRealProdCLM.symm z) x 1)
            (fun z x ↦ K (p (ψ (φ n))) (equivRealProdCLM.symm z) x Complex.I) (u (ψ (φ n))) x ≤
              A) ∧
        ∃ v : ℝ × ℝ → F, TendstoLocallyUniformlyOn (fun n ↦ e ∘ u (ψ (φ n))) v atTop
          (window (max T₀ 2) i \ Z) := by
  set T := max T₀ 2
  have hT : 2 ≤ T := le_max_right _ _
  have hed : ∀ x, MDifferentiableAt I 𝓘(ℝ, F) e x := he.mdifferentiable one_ne_zero
  have hDS := preimage_truncation_subset_thricePuncturedSphereReal (T + 2)
  obtain ⟨c, hc, hJcc, hq⟩ := exists_pos_family_window_data hω hH
    (fun q ↦ (hHs q).of_le (by norm_num)) hCW hJ hJt hJc hJe he hp₀
  obtain ⟨B, hBD⟩ := hB _ (isCompact_preimage_truncation (T + 2)) hDS
  -- The thresholds of the two windows of each end, uniform in the translation, and of the core.
  choose δe hδe hconve using fun q b ↦
    hω.exists_pos_forall_tendstoLocallyUniformlyOn_comp_subseq_off_finset_comp_positiveEndChart
      (T₀ := T) (hH q) (hHs q) (hq q).1 (hq q).2.1 hed he_inj hc (hq q).2.2.1
      (hq q).2.2.2.choose_spec
      (D := Icc (T + 1) (T + 3) ×ˢ Icc ((bif b then (1 / 2 : ℝ) else 0) - 2 / 5)
        ((bif b then 1 / 2 else 0) + 2 / 5)) (isCompact_Icc.prod isCompact_Icc)
      (t₀ := (bif b then 1 / 2 else 0) - 1 / 2)
      (endWindow_closed_subset_Ioi_prod_Ioo (max_le le_rfl (by linarith)) b)
  obtain ⟨δc, hδc, hconvc⟩ :=
    hω.exists_pos_forall_tendsto_tendstoLocallyUniformlyOn_comp_subseq_off_finset hed he_inj hW hC
      (isCompact_preimage_truncation (T + 2)) ((prod_mono subset_rfl hDS).trans hCW) hJ hXs hXt
      (fun p hp z hz x ↦ hJt p hp z (hDS hz) x) hc hJcc (fun p hp z hz x ↦ (hBD p hp z hz x).1)
      fun p hp z hz x ↦ (hBD p hp z hz x).2
  refine ⟨min δc (Finset.univ.inf' ⟨(.zero, false), Finset.mem_univ _⟩
    fun p : Puncture × Bool ↦ δe p.1 p.2), lt_min hδc ((Finset.lt_inf'_iff _).2 fun p _ ↦
      hδe p.1 p.2), fun p u E hpC hu hfl hint hE0 hEl hEc i ψ _ ↦ ?_⟩
  rcases i with _ | ⟨q, m, b⟩
  · have hΩS : window T none ⊆ thricePuncturedSphereReal := fun y hy ↦ hy.1
    obtain ⟨φ, hφ, -, -, -, Z, -, -, hc, hbd, v, -, hv, -⟩ := hconvc (p := p ∘ ψ) (u := u ∘ ψ)
      (isOpen_window _ none) (window_none_subset _) (fun k ↦ hpC _) (fun k ↦ (hu _).mono hΩS)
      (fun k z hz ↦ hfl _ z (hΩS hz)) (fun k ↦ (hint _).mono_set hΩS) fun k ↦ hEc _
    exact ⟨φ, hφ, ↑Z, fun z hz ↦
      eventually_ofReal_le_withDensity_of_forall_eventually_le_setIntegral_ball
        (isOpen_window _ none).measurableSet hΩS
        fun ε hε ↦ (hc z hz ε hε).mono fun n hn ↦ (min_le_left _ _).trans hn,
      -- A compact neighbourhood of a point off the bubbling points carries a bound.
      fun y hy ↦ (local_compact_nhds (((isOpen_window _ none).sdiff
        Z.finite_toSet.isClosed).mem_nhds hy)).elim fun L ⟨hL, hLΩ, hLc⟩ ↦
          ⟨L, hL, (hbd L hLc hLΩ).imp fun _ hA ↦ .of_forall hA⟩, e ∘ v, hv⟩
  · obtain ⟨φ, hφ, Z, hZΩ, -, hc, hbd, v, -, hv, -⟩ := hconve q b
      (K := fun k ↦ K (p (ψ k))) (J := fun k ↦ J (p (ψ k))) (Ω := endWindow T b) (u := u ∘ ψ)
      (R := fun _ ↦ (m : ℝ)) (fun k w x hw ↦ hKH _ (hpC _) q w x ((le_max_left _ _).trans hw))
      (fun k s t x hs ↦ hJe _ (hpC _) q s t x ((le_max_left _ _).trans hs))
      (isOpen_endWindow _ b) (endWindow_subset_Icc_prod_Icc _ b)
      (fun _ ↦ Nat.cast_nonneg m) (fun k ↦ hu _) (fun k ↦ hfl _) hE0 fun k ↦ hEl _
    exact ⟨φ, hφ, _, concentration_and_tendstoLocallyUniformlyOn_window_some
      (K := fun k ↦ K (p (ψ k))) (fun k ↦ hKH _ (hpC _)) hH (fun q ↦ (hHs q).of_le (by norm_num))
      (fun k ↦ (hu (ψ k)).mdifferentiableOn (by norm_num)) (le_max_left _ _) (by positivity)
      q m b hZΩ (fun z hz ε hε ↦ (hc z hz ε hε).mono fun n hn ↦ ((min_le_right _ _).trans
        (Finset.inf'_le (fun p : Puncture × Bool ↦ δe p.1 p.2) (Finset.mem_univ (q, b)))).trans
          hn) hbd hv⟩

/-- **Families of Floer pairs of pants in a closed manifold converge off finitely many bubbling
points on the whole domain.** Let `ω` be a nondegenerate two-form on a closed manifold `M`, such as
a closed symplectic manifold, and let `K_p` and `J_p(z, x)` be perturbations on
`S = ℂ ∖ {0, 1}` and structures on the tangent spaces of `M`, depending on a parameter `p` in a
finite-dimensional real normed space `P`, with `J_p` tamed by `ω` over `S` (read in real
coordinates) for `p` in a compact window `C ⊆ P`. Suppose that, read in the chart at every point
of `M`, the structures and the Hamiltonian vector fields of the two components of `K_p` are `C²`
jointly in `(p, z, y)` on `W × (chart target)` for an open `W ⊇ C × S`, and that they are
cylindrical on the ends with data independent of `p`: beyond `T₀` on the end `q`, `K_p` is
`H_q(t) dt` for a period-one `C³` Hamiltonian `H_q` and `J_p` is `J_q(t, x)` in the end
coordinates, for every `p ∈ C`. Let `e : M → F` be an injective `C¹` map into a normed space, such
as the Whitney embedding, and over every compact `D ⊆ S` let the structures `J_p`, `p ∈ C`, be
uniformly tame with respect to `e` and the pushforwards through `e` of the Hamiltonian vector
fields of `K_p` be bounded. There is a threshold `δ > 0` with the following property. Let `uₖ` be
`C³` solutions of `(du - X_{K_{pₖ}})^{0,1} = 0` on `S` for `J_{pₖ}(z, u)`, with `pₖ ∈ C`, with
integrable energy density and Floer energy at most `E` over `S`. Then there are a
subsequence `φ`, a limit `p₀ ∈ C` of the parameters `p_{φ n}`, a finite set `Z ⊆ S` with
`#Z * δ ≤ E` and a map `v : S \ Z → M`, continuous, such that along `φ` every disc about a point of
`Z` eventually carries energy at least `δ`, the energy densities are eventually bounded near every
point of `S \ Z`, and the solutions converge to `v` on `S \ Z`, locally uniformly after applying
`e` and pointwise in `M`. -/
theorem exists_pos_forall_tendsto_tendstoLocallyUniformlyOn_comp_subseq_off_finset_of_cylindrical
    (hω : ω.IsNondegenerate) {K : P → ℂ → M → ℂ →L[ℝ] ℝ}
    {J : P → ℝ × ℝ → (x : M) → AlmostComplexStructure (TangentSpace I x)}
    {W : Set (P × (ℝ × ℝ))} {C : Set P} (hW : IsOpen W) (hC : IsCompact C)
    (hCW : C ×ˢ thricePuncturedSphereReal ⊆ W)
    (hJ : ∀ α, ContDiffOn ℝ 2 (almostComplexInChartAt I α (uncurry J))
      (W ×ˢ (extChartAt I α).target))
    (hXs : ∀ α, ContDiffOn ℝ 2 (ω.hamiltonianVectorFieldInChartAt α
      (uncurry fun p z x ↦ K p (equivRealProdCLM.symm z) x 1)) (W ×ˢ (extChartAt I α).target))
    (hXt : ∀ α, ContDiffOn ℝ 2 (ω.hamiltonianVectorFieldInChartAt α
      (uncurry fun p z x ↦ K p (equivRealProdCLM.symm z) x Complex.I))
      (W ×ˢ (extChartAt I α).target))
    (hJt : ∀ p ∈ C, ∀ z ∈ thricePuncturedSphereReal, ∀ x,
      (hω.symplecticFormAt x).Tames (J p z x))
    (hJc : ∀ D, IsCompact D → D ⊆ thricePuncturedSphereReal → ∃ c > 0, ∀ p ∈ C, ∀ z ∈ D,
      ∀ x v, c * ‖mvfderiv I e x v‖ ^ 2 ≤ hω.symplecticFormAt x v (J p z x v))
    (hB : ∀ D, IsCompact D → D ⊆ thricePuncturedSphereReal → ∃ B, ∀ p ∈ C, ∀ z ∈ D, ∀ x,
      ‖mvfderiv I e x (ω.hamiltonianVectorField
        (fun y ↦ K p (equivRealProdCLM.symm z) y 1) x)‖ ≤ B ∧
      ‖mvfderiv I e x (ω.hamiltonianVectorField
        (fun y ↦ K p (equivRealProdCLM.symm z) y Complex.I) x)‖ ≤ B)
    {T₀ : ℝ} (hKH : ∀ p ∈ C, ∀ q w x, T₀ ≤ q.endSign * (q.endCoord w).re →
      K p w x = H q (q.endCoord w).im x • q.endAngularForm w)
    (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 3 (uncurry (H q)))
    {Jq : Puncture → ℝ → (x : M) → AlmostComplexStructure (TangentSpace I x)}
    (hJe : ∀ p ∈ C, ∀ q s t x, T₀ ≤ s → J p (endChart q (q.endSign * s, t)) x = Jq q t x)
    (he : ContMDiff I 𝓘(ℝ, F) 1 e) (he_inj : Injective e) :
    ∃ δ > 0, ∀ ⦃p : ℕ → P⦄ ⦃u : ℕ → ℝ × ℝ → M⦄ ⦃E : ℝ⦄, (∀ k, p k ∈ C) →
      (∀ k, ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 3 (u k) thricePuncturedSphereReal) →
      (∀ k, ∀ z ∈ thricePuncturedSphereReal,
        IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J (p k) z (u k z))
          (ω.perturbedMFDeriv (fun z x ↦ K (p k) (equivRealProdCLM.symm z) x 1)
            (fun z x ↦ K (p k) (equivRealProdCLM.symm z) x Complex.I) (u k) z).toLinearMap) →
      (∀ k, IntegrableOn (ω.floerEnergyDensity (fun z x ↦ K (p k) (equivRealProdCLM.symm z) x 1)
        (fun z x ↦ K (p k) (equivRealProdCLM.symm z) x Complex.I) (u k))
        thricePuncturedSphereReal) →
      (∀ k, ∫ z in thricePuncturedSphereReal, ω.floerEnergyDensity
        (fun z x ↦ K (p k) (equivRealProdCLM.symm z) x 1)
        (fun z x ↦ K (p k) (equivRealProdCLM.symm z) x Complex.I) (u k) z ≤ E) →
      ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ p₀ ∈ C, Tendsto (fun n ↦ p (φ n)) atTop (𝓝 p₀) ∧
        ∃ (Z : Finset (ℝ × ℝ)) (v : ℝ × ℝ → M), ↑Z ⊆ thricePuncturedSphereReal ∧
        Z.card * δ ≤ E ∧
        (∀ z ∈ Z, ∀ ε > 0, ∀ᶠ n in atTop, δ ≤ ∫ y in ball z ε ∩ thricePuncturedSphereReal,
          ω.floerEnergyDensity (fun z x ↦ K (p (φ n)) (equivRealProdCLM.symm z) x 1)
            (fun z x ↦ K (p (φ n)) (equivRealProdCLM.symm z) x Complex.I) (u (φ n)) y) ∧
        (∀ y ∈ thricePuncturedSphereReal \ ↑Z, ∃ N ∈ 𝓝 y, ∃ A, ∀ᶠ n in atTop, ∀ w ∈ N,
          ω.floerEnergyDensity (fun z x ↦ K (p (φ n)) (equivRealProdCLM.symm z) x 1)
            (fun z x ↦ K (p (φ n)) (equivRealProdCLM.symm z) x Complex.I) (u (φ n)) w ≤ A) ∧
        ContinuousOn v (thricePuncturedSphereReal \ ↑Z) ∧
        TendstoLocallyUniformlyOn (fun n ↦ e ∘ u (φ n)) (e ∘ v) atTop
          (thricePuncturedSphereReal \ ↑Z) ∧
        ∀ z ∈ thricePuncturedSphereReal \ ↑Z, Tendsto (fun n ↦ u (φ n) z) atTop (𝓝 (v z)) := by
  -- Without parameters there are no sequences of solutions.
  rcases C.eq_empty_or_nonempty with rfl | ⟨p₁, hp₁⟩
  · exact ⟨1, one_pos, fun p _ _ hpC ↦ absurd (hpC 0) (notMem_empty _)⟩
  obtain ⟨δ, hδ, hwin⟩ := exists_pos_forall_family_window hω hW hC hCW hJ hXs hXt hJt hJc hB hKH
    hH hHs hJe he he_inj hp₁
  refine ⟨δ, hδ, fun p u E hpC hu hfl hint hE ↦ ?_⟩
  have hS := isOpen_thricePuncturedSphereReal.measurableSet
  have h0 (k : ℕ) (z : ℝ × ℝ) (hz : z ∈ thricePuncturedSphereReal) :=
    floerEnergyDensity_nonneg hω (hJt _ (hpC k) z hz _) (hfl k z hz)
  -- The energy is nonnegative, so it bounds the energy measure of `S` and the energy over parts.
  have hE0 : 0 ≤ E := (setIntegral_nonneg hS (h0 0)).trans (hE 0)
  have hEl (k : ℕ) : ∫⁻ z in thricePuncturedSphereReal, ENNReal.ofReal (ω.floerEnergyDensity
      (fun z x ↦ K (p k) (equivRealProdCLM.symm z) x 1)
      (fun z x ↦ K (p k) (equivRealProdCLM.symm z) x Complex.I) (u k) z) ≤ ENNReal.ofReal E := by
    rw [← ofReal_integral_eq_lintegral_ofReal (hint k) (ae_restrict_of_forall_mem hS (h0 k))]
    exact ENNReal.ofReal_le_ofReal (hE k)
  -- First make the parameters converge.
  obtain ⟨p₀, hp₀, ψ, hψ, hpψ⟩ := hC.tendsto_subseq hpC
  -- Assemble the windows by the diagonal argument, for the energy measures of the `uₖ` on `S`.
  obtain ⟨φ, Z, g, hφ, hZ, hcard, hconc, hbd, hconv⟩ :=
    exists_tendstoLocallyUniformlyOn_subseq_off_finset_iUnion_of_le (isOpen_window (max T₀ 2))
      (F := fun k ↦ e ∘ u (ψ k)) (G := fun k ↦ ω.floerEnergyDensity
        (fun z x ↦ K (p (ψ k)) (equivRealProdCLM.symm z) x 1)
        (fun z x ↦ K (p (ψ k)) (equivRealProdCLM.symm z) x Complex.I) (u (ψ k)))
      (ENNReal.ofReal_pos.2 hδ).ne' ENNReal.ofReal_ne_top
      (fun k ↦ (measure_mono (subset_univ _)).trans (by
        rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
        exact hEl (ψ k)))
      (hwin (p := p ∘ ψ) (u := u ∘ ψ) (fun k ↦ hpC _) (fun k ↦ hu _) (fun k ↦ hfl _)
        (fun k ↦ hint _) hE0 (fun k ↦ hEl _) fun k ↦ (setIntegral_mono_set
          (s := window (max T₀ 2) none) (hint _)
          (ae_restrict_of_forall_mem hS (h0 _))
          (ae_of_all _ fun _ hy ↦ hy.1)).trans
            (hE _))
  rw [iUnion_window (by positivity)] at hZ hbd hconv
  -- The limit is continuous, and it is read back in `M` through the embedding `e`.
  have hg : ContinuousOn g (thricePuncturedSphereReal \ ↑Z) :=
    hconv.continuousOn (Eventually.of_forall fun n ↦
      (he.continuous.comp_continuousOn (hu (ψ (φ n))).continuousOn).mono sdiff_subset).frequently
  obtain ⟨v, hv, -, hev, hpt⟩ := isCompact_univ.exists_tendsto_of_tendsto_comp
    he.continuous.continuousOn he_inj.injOn (fun _ _ ↦ .of_forall fun _ ↦ mem_univ _) hg
    fun z hz ↦ hconv.tendsto_at hz
  refine ⟨ψ ∘ φ, hψ.comp hφ, p₀, hp₀, hpψ.comp hφ.tendsto_atTop, Z, v, hZ,
    (ENNReal.natCast_mul_ofReal_le_ofReal_iff hE0).1 hcard, fun z hz ε hε ↦ ?_, hbd, hv,
    hconv.congr_right hev.symm, hpt⟩
  -- The energy measure of a disc is the energy over its part in `S`.
  filter_upwards [hconc z hz _ (ball_mem_nhds z hε)] with n hn
  exact TauCeti.MeasureTheory.le_setIntegral_of_ofReal_le_withDensity measurableSet_ball
    isOpen_thricePuncturedSphereReal.measurableSet ((hint _).mono_set inter_subset_right)
    (fun y hy ↦ h0 _ y hy.2) hn

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
along `φ` every disc about a point of `Z` eventually carries energy at least `δ`, the energy
densities are eventually bounded near every point of `S \ Z`, and the solutions converge to `v`
on `S \ Z`, locally uniformly after applying `e` and pointwise in `M`.
This is the case of a one-point parameter space in
`exists_pos_forall_tendsto_tendstoLocallyUniformlyOn_comp_subseq_off_finset_of_cylindrical`. -/
theorem exists_pos_forall_tendstoLocallyUniformlyOn_comp_subseq_off_finset_thricePuncturedSphereReal
    (hω : ω.IsNondegenerate) (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 3 (uncurry (H q)))
    {B : Puncture → ℝ} (hB : ∀ q t x, |H q t x| ≤ B q)
    {J : ℝ × ℝ → (x : M) → AlmostComplexStructure (TangentSpace I x)}
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
        (∀ y ∈ thricePuncturedSphereReal \ ↑Z, ∃ N ∈ 𝓝 y, ∃ A', ∀ᶠ n in atTop, ∀ w ∈ N,
          ω.floerEnergyDensity
            (fun z x ↦ pairOfPantsPerturbation H (equivRealProdCLM.symm z) x 1)
            (fun z x ↦ pairOfPantsPerturbation H (equivRealProdCLM.symm z) x Complex.I)
            (u (φ n)) w ≤ A') ∧
        ContinuousOn v (thricePuncturedSphereReal \ ↑Z) ∧
        TendstoLocallyUniformlyOn (fun n ↦ e ∘ u (φ n)) (e ∘ v) atTop
          (thricePuncturedSphereReal \ ↑Z) ∧
        ∀ z ∈ thricePuncturedSphereReal \ ↑Z, Tendsto (fun n ↦ u (φ n) z) atTop (𝓝 (v z)) := by
  have hS := isOpen_thricePuncturedSphereReal
  -- The constant family over the one-point parameter space `Unit`, on `W = univ × S`.
  have hπ (α : M) : MapsTo (fun q : (Unit × (ℝ × ℝ)) × E ↦ (q.1.2, q.2))
      ((univ ×ˢ thricePuncturedSphereReal) ×ˢ (extChartAt I α).target)
      (thricePuncturedSphereReal ×ˢ (extChartAt I α).target) :=
    fun q hq ↦ ⟨hq.1.2, hq.2⟩
  have hX (v : ℂ) (α : M) := contDiffOn_hamiltonianVectorFieldInChartAt_uncurry_const (R := Unit)
    (hω.contDiffOn_hamiltonianVectorFieldInChartAt_pairOfPantsPerturbation hH hHs v α) (hπ α)
  -- Over a compact part of `S` the structure is uniformly tame and the Hamiltonian vector fields
  -- of the perturbation are bounded.
  have hJc (D : Set (ℝ × ℝ)) (hD : IsCompact D) (hDS : D ⊆ thricePuncturedSphereReal) :=
    have ⟨c, hc, h⟩ := hω.exists_pos_forall_mul_norm_mvfderiv_sq_le hD isCompact_univ
      (fun α _ ↦ (hJ α).continuousOn.mono (prod_mono hDS subset_rfl))
      (fun z hz x _ ↦ hJt z (hDS hz) x) he
    (⟨c, hc, fun _ _ z hz x v ↦ h z hz x (mem_univ x) v⟩ : ∃ c > 0, ∀ p ∈ (univ : Set Unit),
      ∀ z ∈ D, ∀ x v, c * ‖mvfderiv I e x v‖ ^ 2 ≤ hω.symplecticFormAt x v (J z x v))
  have hBD (D : Set (ℝ × ℝ)) (hD : IsCompact D) (hDS : D ⊆ thricePuncturedSphereReal) :=
    have ⟨Ls, hLs⟩ := exists_forall_norm_mvfderiv_hamiltonianVectorField_pairOfPantsPerturbation_le
      hω hH (fun q ↦ (hHs q).of_le (by norm_num)) he hD hDS 1
    have ⟨Lt, hLt⟩ := exists_forall_norm_mvfderiv_hamiltonianVectorField_pairOfPantsPerturbation_le
      hω hH (fun q ↦ (hHs q).of_le (by norm_num)) he hD hDS Complex.I
    (⟨max Ls Lt, fun _ _ z hz x ↦ ⟨(hLs z hz x).trans (le_max_left _ _),
      (hLt z hz x).trans (le_max_right _ _)⟩⟩ : ∃ B, ∀ p ∈ (univ : Set Unit), ∀ z ∈ D, ∀ x,
        ‖mvfderiv I e x (ω.hamiltonianVectorField
          (fun y ↦ pairOfPantsPerturbation H (equivRealProdCLM.symm z) y 1) x)‖ ≤ B ∧
        ‖mvfderiv I e x (ω.hamiltonianVectorField
          (fun y ↦ pairOfPantsPerturbation H (equivRealProdCLM.symm z) y Complex.I) x)‖ ≤ B)
  obtain ⟨δ, hδ, hconv⟩ :=
    hω.exists_pos_forall_tendsto_tendstoLocallyUniformlyOn_comp_subseq_off_finset_of_cylindrical
      (K := fun (_ : Unit) ↦ pairOfPantsPerturbation H) (J := fun (_ : Unit) ↦ J)
      (isOpen_univ.prod hS) isCompact_univ subset_rfl
      (fun α ↦ contDiffOn_almostComplexInChartAt_uncurry_const (hJ α) (hπ α)) (hX 1) (hX Complex.I)
      (fun _ _ ↦ hJt) hJc hBD (T₀ := max T₀ 2)
      (fun _ _ q w x hw ↦ pairOfPantsPerturbation_eq_smul_endAngularForm
        ((le_max_right _ _).trans hw) x) hH hHs
      (fun _ _ q s t x hs ↦ hJe q s t x ((le_max_left _ _).trans hs)) he he_inj
  refine ⟨δ, hδ, fun u x A hu hfl hx hE hA htop ↦ ?_⟩
  -- The energy over `S` is at most the topological energy plus `B₀ + B₁ + B_∞`.
  have hEb (k : ℕ) := hω.setIntegral_floerEnergyDensity_pairOfPantsPerturbation_le hH
    (fun q ↦ (hHs q).of_le (by norm_num)) hB ((hu k).of_le (by norm_num)) (hx k) (hE k) (hA k)
    (J := fun z ↦ J z (u k z)) (fun z hz ↦ hJt z hz _) (hfl k) subset_rfl
  obtain ⟨φ, hφ, -, -, -, Z, v, hZ, hcard, hconc, hbd, hv, hlim, hpt⟩ :=
    hconv (p := fun _ ↦ ()) (E := A + ∑ q, B q) (fun _ ↦ mem_univ _) hu hfl hE
      fun k ↦ by linarith [htop k, hEb k]
  exact ⟨φ, Z, v, hφ, hZ, hcard, hconc, hbd, hv, hlim, hpt⟩

end TauCeti.SmoothTwoForm.IsNondegenerate
