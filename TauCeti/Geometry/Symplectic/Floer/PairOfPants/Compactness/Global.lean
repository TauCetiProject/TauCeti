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
import TauCeti.Geometry.Symplectic.Floer.Manifold.Translation
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

Some families move their output end: the input-exchange family behind graded commutativity is
cylindrical beyond `T₀` in the end chart of the output end recentred at the parameter `c`, not in
the end chart at `∞`. The family theorem above is the case `a = 0` of
`exists_pos_forall_tendsto_tendstoLocallyUniformlyOn_comp_subseq_off_finset_of_recentered`, in
which the output end is recentred at a point `a(p)` of the real axis depending continuously on the
parameter: beyond `T₀` on the output end, `w ↦ K_p(w + a(p))` is `H_∞(t) dt` and `J_p` is
`J_∞(t)` in the end chart moved by `a(p)`. The centres are bounded on `C`, so beyond a height `T`
that only depends on that bound the moved end charts stay in `S`. Once the parameters converge to
`p₀`, the windows of the output end are taken in the end chart moved by `a(p₀)`, and the core is
the rest of `S` near the input ends and within a fixed distance of `a(p₀)`, inside a compact
truncation of `S` that does not depend on `p₀`. On an end window the solutions are read through
the translates `w ↦ uₖ(w + a(pₖ))`, which are defined on `S - a(pₖ)` and solve the cylindrical
equation of the end (the end theorems apply to solutions on any open set containing the end), and
then moved back: locally uniform convergence to a continuous limit survives the converging
translations (`TendstoLocallyUniformlyOn.comp_sub_of_tendsto`), and so does the concentration of
energy at the bubbling points.

As in `TauCeti.Geometry.Symplectic.Floer.PairOfPants.Compactness.Closed`, whose theorems on the core
window and on the translated end windows replace those of a vector space, sizes in `M` are measured
through an injective `C¹` map `e : M → F` into a normed space, such as the Whitney embedding. On
the core the family theorem takes uniform tameness with respect to `e` and bounds on the
pushforwards through `e` of the Hamiltonian vector fields as hypotheses over compact parts of `S`;
for the pair of pants they hold by compactness
(`TauCeti.SmoothTwoForm.IsNondegenerate.exists_pos_forall_mul_norm_mvfderiv_sq_le`,
`exists_forall_norm_mvfderiv_hamiltonianVectorField_pairOfPantsPerturbation_le`). On the ends the
constants are derived: the end Hamiltonians are periodic on a compact manifold, and beyond `T₀` the
structures are those of the circle `t ↦ φ_q(±T, t)` of `S`, moved by `a(p)` on the output end,
for any parameter `p`, so they are `C²` in
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
densities are eventually bounded near every point of `S \ Z`. For smooth solutions of the
pair-of-pants theorem, these bounds make the limit a `C¹` Floer solution on `S \ Z`, in
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

namespace TauCeti.SymplecticForm

open Floer

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

/-- The offset of the end `q` in a family whose output end is recentred at `a ∈ ℝ`: the translation
`(a, 0)` on the output end, and `0` on the two input ends. -/
private def endOffset (a : ℝ) (q : Puncture) : ℝ × ℝ := if q = .inf then (a, 0) else 0

private theorem endOffset_inf (a : ℝ) : endOffset a .inf = (a, 0) := by simp [endOffset]

private theorem endOffset_of_ne {a : ℝ} {q : Puncture} (hq : q ≠ .inf) : endOffset a q = 0 := by
  simp [endOffset, hq]

private theorem endOffset_zero (q : Puncture) : endOffset 0 q = 0 := by
  unfold endOffset
  split_ifs <;> rfl

/-- The points of `S` whose signed longitudinal coordinate on each input end is below `c` and which
lie in the open disc of radius `2 exp (2πc)` about `a` form an open set. -/
private theorem isOpen_setOf_forall_fst_positiveEndCoord_lt_and_norm_sub_lt (c a : ℝ) :
    IsOpen {z | z ∈ thricePuncturedSphereReal ∧
      (∀ q, q ≠ .inf → (positiveEndCoord q z).1 < c) ∧
        ‖equivRealProdCLM.symm z - a‖ < 2 * Real.exp (2 * Real.pi * c)} := by
  refine isOpen_iff_mem_nhds.2 fun z ⟨hzS, hz, hza⟩ ↦ ?_
  refine (isOpen_thricePuncturedSphereReal.eventually_mem hzS).and
    ((eventually_all.2 fun q ↦ ?_).and ?_)
  · by_cases hq : q = .inf
    · exact .of_forall fun _ h ↦ absurd hq h
    · exact ((continuousAt_fst_positiveEndCoord q (Puncture.ne_endCenter
        (mem_thricePuncturedSphereReal_iff.1 hzS) q)).eventually_lt continuousAt_const
          (hz q hq)).mono fun _ h _ ↦ h
  · exact ((equivRealProdCLM.symm.continuous.sub continuous_const).norm.continuousAt).eventually_lt
      continuousAt_const hza

/-- Beyond `T ≥ |a|` on the end `q`, the positive end chart moved by the offset of `q` for the
output end recentred at `a` maps into `S`. -/
private theorem positiveEndChart_add_endOffset_mem {T a : ℝ} (hT : 0 ≤ T) (ha : |a| ≤ T)
    (q : Puncture) {ζ : ℝ × ℝ} (hζ : T < ζ.1) :
    positiveEndChart q ζ + endOffset a q ∈ thricePuncturedSphereReal := by
  by_cases hq : q = .inf
  · subst hq
    refine mem_thricePuncturedSphereReal_of_two_le_norm ?_
    rw [endOffset_inf, TauCeti.Complex.equivRealProdCLM_symm_add_prodMk_zero,
      positiveEndChart_mk, equivRealProdCLM_symm_endChart]
    have hφ := Puncture.two_mul_exp_le_norm_cylindricalEndLift_inf (R := ζ.1)
      (z := equivRealProdCLM.symm (Puncture.endSign .inf * ζ.1, Puncture.endSign .inf * ζ.2))
      (by simp)
    have hexp := Real.add_one_le_exp (2 * Real.pi * ζ.1)
    have hn := norm_sub_norm_le (Puncture.inf.cylindricalEndLift
      (equivRealProdCLM.symm (Puncture.endSign .inf * ζ.1, Puncture.endSign .inf * ζ.2)))
      (-(a : ℂ))
    rw [sub_neg_eq_add, norm_neg, Complex.norm_real, Real.norm_eq_abs] at hn
    nlinarith [Real.two_le_pi]
  · rw [endOffset_of_ne hq, add_zero]
    exact positiveEndChart_mem_thricePuncturedSphereReal (hT.trans_lt hζ)

/-- The windows covering `S` for an output end recentred at `a ∈ ℝ`: the core, the points of `S`
whose signed longitudinal coordinate on each input end is below `T + 2` and which lie in the open
disc of radius `2 exp (2π (T + 2))` about `a`, and on each end `q` the images of the end windows
under `y ↦ φ'_q(y + (m, 0))`, for `m ∈ ℕ`, moved by the offset of `q`. For `a = 0` the core is the
set of points of `S` whose signed longitudinal coordinate on every end is below `T + 2`. -/
private noncomputable def window (T a : ℝ) : Option (Puncture × ℕ × Bool) → Set (ℝ × ℝ)
  | none => {z | z ∈ thricePuncturedSphereReal ∧
      (∀ q, q ≠ .inf → (positiveEndCoord q z).1 < T + 2) ∧
        ‖equivRealProdCLM.symm z - a‖ < 2 * Real.exp (2 * Real.pi * (T + 2))}
  | some (q, m, b) =>
    (fun y ↦ positiveEndChart q (y + ((m : ℝ), 0)) + endOffset a q) '' endWindow T b

/-- An end window is the image of an end window of the cylinder under the positive end chart
moved by the offset of the end. -/
private theorem window_some (T a : ℝ) (q : Puncture) (m : ℕ) (b : Bool) :
    window T a (some (q, m, b)) =
      (fun y ↦ positiveEndChart q (y + ((m : ℝ), 0)) + endOffset a q) '' endWindow T b :=
  (rfl)

/-- The end windows are mapped into `S`. -/
private theorem positiveEndChart_add_mem {T : ℝ} (hT : 0 ≤ T) (q : Puncture) (m : ℕ) {b : Bool}
    {y : ℝ × ℝ} (hy : y ∈ endWindow T b) :
    positiveEndChart q (y + ((m : ℝ), 0)) ∈ thricePuncturedSphereReal :=
  positiveEndChart_mem_thricePuncturedSphereReal <| hT.trans_lt
    (endWindow_add_mem_Ioi_prod_Ioo le_rfl (Nat.cast_nonneg m) hy).1

/-- For an output end that is not recentred, the end windows are the images of the end windows
under `y ↦ φ'_q(y + (m, 0))`. -/
private theorem window_zero_some (T : ℝ) (q : Puncture) (m : ℕ) (b : Bool) :
    window T 0 (some (q, m, b)) =
      (fun y ↦ positiveEndChart q (y + ((m : ℝ), 0))) '' endWindow T b := by
  simp only [window_some, endOffset_zero, add_zero]

/-- The windows are open, since the positive end charts are open maps. -/
private theorem isOpen_window (T a : ℝ) (i : Option (Puncture × ℕ × Bool)) :
    IsOpen (window T a i) := by
  rcases i with _ | ⟨q, m, b⟩
  · exact isOpen_setOf_forall_fst_positiveEndCoord_lt_and_norm_sub_lt _ _
  · exact ((Homeomorph.addRight (endOffset a q)).isOpenMap.comp ((isOpenMap_positiveEndChart q).comp
      (Homeomorph.addRight ((m : ℝ), (0 : ℝ))).isOpenMap)) _ (isOpen_endWindow T b)

/-- The core window lies in the compact truncation `S_{T + 2 + A}` for every bound `A ≥ |a|`. -/
private theorem window_none_subset {T a A : ℝ} (hT : 0 ≤ T) (hA : |a| ≤ A) :
    window T a none ⊆ equivRealProdCLM.symm ⁻¹' truncation (T + 2 + A) := by
  refine subset_preimage_truncation_of_isOpen (isOpen_window T a none) fun z hz q ↦ ?_
  by_cases hq : q = .inf
  · subst hq
    by_contra h
    -- Off the disc about `0` of radius `2 exp (2π (T + 2 + A))`, the point is too far from `a`.
    have h0 : equivRealProdCLM.symm z ≠ 0 := (mem_thricePuncturedSphereReal_iff.1 hz.1).1
    have hlt := (lt_fst_positiveEndCoord_inf_iff h0).1 (not_le.1 h)
    have hn := norm_sub_norm_le (equivRealProdCLM.symm z) (a : ℂ)
    rw [Complex.norm_real, Real.norm_eq_abs] at hn
    have he1 : 1 ≤ Real.exp (2 * Real.pi * (T + 2)) := Real.one_le_exp (by positivity)
    have he2 := Real.add_one_le_exp (2 * Real.pi * A)
    rw [show 2 * Real.pi * (T + 2 + A) = 2 * Real.pi * (T + 2) + 2 * Real.pi * A by ring,
      Real.exp_add] at hlt
    have hpA : 0 ≤ 2 * Real.pi * A := mul_nonneg (by positivity) ((abs_nonneg a).trans hA)
    have k1 := mul_le_mul_of_nonneg_left he2 (Real.exp_pos (2 * Real.pi * (T + 2))).le
    have k2 : 2 * Real.pi * A ≤ Real.exp (2 * Real.pi * (T + 2)) * (2 * Real.pi * A) :=
      le_mul_of_one_le_left hpA he1
    have k3 : A ≤ 2 * Real.pi * A := by nlinarith [Real.two_le_pi, (abs_nonneg a).trans hA]
    linarith [hz.2.2]
  · exact (hz.2.1 q hq).le.trans (by linarith [abs_nonneg a])

/-- The windows cover `S` when `|a| ≤ T`. -/
private theorem iUnion_window {T a : ℝ} (hT : 0 ≤ T) (ha : |a| ≤ T) :
    ⋃ i, window T a i = thricePuncturedSphereReal := by
  refine subset_antisymm (iUnion_subset fun i ↦ ?_) fun z hz ↦ ?_
  · rcases i with _ | ⟨q, m, b⟩
    · exact fun z hz ↦ hz.1
    · rintro _ ⟨y, hy, rfl⟩
      exact positiveEndChart_add_endOffset_mem hT ha q
        (endWindow_add_mem_Ioi_prod_Ioo le_rfl (Nat.cast_nonneg m) hy).1
  · by_cases hc : (∀ q, q ≠ .inf → (positiveEndCoord q z).1 < T + 2) ∧
        ‖equivRealProdCLM.symm z - a‖ < 2 * Real.exp (2 * Real.pi * (T + 2))
    · exact mem_iUnion.2 ⟨none, hz, hc⟩
    by_cases hin : ∃ q, q ≠ .inf ∧ T + 2 ≤ (positiveEndCoord q z).1
    · -- Far out on an input end.
      obtain ⟨q, hq, hqz⟩ := hin
      obtain ⟨m, b, y, hy, hyz⟩ := exists_mem_image_positiveEndChart_add
        (Puncture.ne_endCenter (mem_thricePuncturedSphereReal_iff.1 hz) q) hqz
      exact mem_iUnion.2 ⟨some (q, m, b), y, hy, by
        simp only at hyz ⊢
        rw [endOffset_of_ne hq, add_zero, hyz]⟩
    · -- Far from `a`, so far out on the output end recentred at `a`.
      simp only [not_exists, not_and, not_le] at hin
      have hfar : 2 * Real.exp (2 * Real.pi * (T + 2)) ≤ ‖equivRealProdCLM.symm z - a‖ :=
        not_lt.1 fun h ↦ hc ⟨fun q hq ↦ hin q hq, h⟩
      set z' : ℝ × ℝ := z - (a, 0)
      have hz' : equivRealProdCLM.symm z' = equivRealProdCLM.symm z - a := by
        simp [z', map_sub, Complex.equivRealProdCLM_symm_apply]
      have h0 : equivRealProdCLM.symm z' ≠ 0 := by
        rw [hz']
        intro h
        rw [h, norm_zero] at hfar
        linarith [Real.exp_pos (2 * Real.pi * (T + 2))]
      have hs : T + 2 ≤ (positiveEndCoord .inf z').1 := le_of_forall_lt fun r hr ↦
        (lt_fst_positiveEndCoord_inf_iff h0).2 (by
          rw [hz']
          exact (mul_lt_mul_of_pos_left (Real.exp_lt_exp.2 (by nlinarith [Real.pi_pos]))
            two_pos).trans_le hfar)
      obtain ⟨m, b, y, hy, hyz⟩ :=
        exists_mem_image_positiveEndChart_add (by rwa [Puncture.endCenter_inf]) hs
      exact mem_iUnion.2 ⟨some (.inf, m, b), y, hy, by
        simp only at hyz ⊢
        rw [endOffset_inf, hyz, sub_add_cancel]⟩

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
      (ω := ω.constSmooth) (K := fun _ ↦ pairOfPantsPerturbation H) (q := q)
      (fun _ w x hw ↦ pairOfPantsPerturbation_eq_smul_endAngularForm hw x) (hH q)
      (fun t ↦ (hHd q t).mdifferentiable) (U := fun _ ↦ thricePuncturedSphereReal)
      (fun _ ↦ isOpen_thricePuncturedSphereReal) hT
      (fun _ _ hζ ↦ positiveEndChart_mem_thricePuncturedSphereReal ((le_max_right _ _).trans_lt hζ))
      (fun k ↦ (hu k).mdifferentiableOn) hΩ hΩT
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
          (window (max T₀ 2) 0 i \ Z) := by
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
  have hcore : window (max T₀ 2) 0 none ⊆ equivRealProdCLM.symm ⁻¹' truncation (max T₀ 2 + 2) := by
    simpa using window_none_subset (T := max T₀ 2) (a := 0) (A := 0) (by positivity) (by simp)
  rcases i with _ | ⟨q, m, b⟩
  · obtain ⟨φ, Z, v, hφ, -, -, hc, -, -, -, hv⟩ := hconvc (u := u ∘ ψ) (a := a ∘ ψ)
      (isOpen_window _ 0 none) hcore (fun k ↦ hu _) (fun k ↦ hfl _)
      (fun k ↦ ha _) (fun k ↦ hA _) (fun k ↦ (huK _).mono_left fun z hz ↦ hz.1)
    exact ⟨φ, hφ, ↑Z, fun z hz ↦
      eventually_ofReal_le_withDensity_of_forall_eventually_le_setIntegral_ball
        (isOpen_window _ 0 none).measurableSet (fun y hy ↦ hy.1)
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
    exact ⟨φ, hφ, _, hc', v', by rwa [window_zero_some]⟩

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
    exists_tendstoLocallyUniformlyOn_subseq_off_finset_iUnion (isOpen_window (max T₀ 2) 0)
      (F := u) (ENNReal.ofReal_pos.2 hδ).ne' ENNReal.ofReal_ne_top
      (fun k ↦ (measure_mono (subset_univ _)).trans (by
        rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]; exact (hE k).2))
      (hwin hu hfl ha hA huK)
  rw [iUnion_window (by positivity) (by rw [abs_zero]; positivity)] at hZ hconv
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

omit [TopologicalSpace M] [CompactSpace M] in
/-- In a family whose output end is recentred at `a(p)`, the perturbations are `H_q(t) dt` beyond
`T₀` in the end chart of every end `q` moved by the offset of `q`. -/
private theorem eq_smul_endAngularForm_of_add_endOffset {Q : Type*} {K : Q → ℂ → M → ℂ →L[ℝ] ℝ}
    {C : Set Q} {a : Q → ℝ} {T₀ : ℝ}
    (hKH : ∀ p ∈ C, ∀ q, q ≠ .inf → ∀ w x, T₀ ≤ q.endSign * (q.endCoord w).re →
      K p w x = H q (q.endCoord w).im x • q.endAngularForm w)
    (hKH' : ∀ p ∈ C, ∀ w x, T₀ ≤ -(Puncture.inf.endCoord w).re →
      K p (w + a p) x = H .inf (Puncture.inf.endCoord w).im x • Puncture.inf.endAngularForm w)
    {p : Q} (hp : p ∈ C) (q : Puncture) (w : ℂ) (x : M)
    (hw : T₀ ≤ q.endSign * (q.endCoord w).re) :
    K p (w + equivRealProdCLM.symm (endOffset (a p) q)) x =
      H q (q.endCoord w).im x • q.endAngularForm w := by
  by_cases hq : q = .inf
  · subst hq
    have hsymm : equivRealProdCLM.symm ((a p, 0) : ℝ × ℝ) = (a p : ℂ) := by
      apply Complex.ext <;> simp
    rw [endOffset_inf, hsymm]
    exact hKH' p hp w x (by simpa using hw)
  · rw [endOffset_of_ne hq, map_zero, add_zero]
    exact hKH p hp q hq w x hw

omit [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I ⊤ M] [CompactSpace M] in
/-- In a family whose output end is recentred at `a(p)`, the structures are `J_q(t)` beyond `T₀`
in the end chart of every end `q` moved by the offset of `q`. -/
private theorem eq_of_endChart_add_endOffset {Q : Type*}
    {J : Q → ℝ × ℝ → (x : M) → AlmostComplexStructure (TangentSpace I x)} {C : Set Q}
    {a : Q → ℝ} {T₀ : ℝ} {Jq : Puncture → ℝ → (x : M) → AlmostComplexStructure (TangentSpace I x)}
    (hJe : ∀ p ∈ C, ∀ q, q ≠ .inf → ∀ s t x, T₀ ≤ s →
      J p (endChart q (q.endSign * s, t)) x = Jq q t x)
    (hJe' : ∀ p ∈ C, ∀ s t x, T₀ ≤ s → J p (endChart .inf (-s, t) + (a p, 0)) x = Jq .inf t x)
    {p : Q} (hp : p ∈ C) (q : Puncture) (s t : ℝ) (x : M) (hs : T₀ ≤ s) :
    J p (endChart q (q.endSign * s, t) + endOffset (a p) q) x = Jq q t x := by
  by_cases hq : q = .inf
  · subst hq
    rw [endOffset_inf, Puncture.endSign_inf, neg_one_mul]
    exact hJe' p hp s t x hs
  · rw [endOffset_of_ne hq, add_zero]
    exact hJe p hp q hq s t x hs

/-- The offsets of an end converge along converging centres. -/
private theorem tendsto_endOffset {c : ℕ → ℝ} {c₀ : ℝ} (hc : Tendsto c atTop (𝓝 c₀))
    (q : Puncture) : Tendsto (fun k ↦ endOffset (c k) q) atTop (𝓝 (endOffset c₀ q)) := by
  by_cases hq : q = .inf
  · subst hq
    simpa only [endOffset_inf] using hc.prodMk_nhds tendsto_const_nhds
  · simpa only [endOffset_of_ne hq] using tendsto_const_nhds

omit [I.Boundaryless] [FiniteDimensional ℝ P] in
/-- **The data of the windows of a family.** Under the hypotheses of the main theorem below, with
`T = max T₀ 2 + A₀` for a bound `A₀` of the centres `|a p|`, `p ∈ C`, of the output end, and a
parameter `p₀ ∈ C`, there is a constant `c > 0` such that on the core truncation `S_{T + 2 + A₀}`
the structures `J_p`, `p ∈ C`, are uniformly tame with respect to `e`, `c ‖d e v‖² ≤ ω(v, J_p v)`,
and such that on each end `q` the structures `J_q` are `C²` in the charts of `M`, tame, and
uniformly tame with the same constant `c`, and the pushforwards of the Hamiltonian vector fields of
the end Hamiltonian `H'_q` are bounded. Beyond `T₀` every `J_p` is `J_q` on the end `q`, read in the
end chart moved by the offset of `q`, so these are properties of `J_{p₀}` on the circles
`φ_q(±T, t)` moved by the offsets of the ends at `p₀`. -/
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
    {a : P → ℝ} {A₀ : ℝ} (hA₀ : ∀ p ∈ C, |a p| ≤ A₀)
    {T₀ : ℝ} {Jq : Puncture → ℝ → (x : M) → AlmostComplexStructure (TangentSpace I x)}
    (hJe : ∀ p ∈ C, ∀ q s t x, T₀ ≤ s →
      J p (endChart q (q.endSign * s, t) + endOffset (a p) q) x = Jq q t x)
    (he : ContMDiff I 𝓘(ℝ, F) 1 e) {p₀ : P} (hp₀ : p₀ ∈ C) :
    ∃ c > 0,
      (∀ p ∈ C, ∀ z ∈ equivRealProdCLM.symm ⁻¹' truncation (max T₀ 2 + A₀ + 2 + A₀), ∀ x v,
        c * ‖mvfderiv I e x v‖ ^ 2 ≤ hω.symplecticFormAt x v (J p z x v)) ∧
      ∀ q, (∀ α, ContDiffOn ℝ 2 (almostComplexInChartAt I α (Jq q))
          (univ ×ˢ (extChartAt I α).target)) ∧
        (∀ t x, (hω.symplecticFormAt x).Tames (Jq q t x)) ∧
        (∀ t x v, c * ‖mvfderiv I e x v‖ ^ 2 ≤ hω.symplecticFormAt x v (Jq q t x v)) ∧
        ∃ L', ∀ t x,
          ‖mvfderiv I e x (ω.hamiltonianVectorField (positiveEndHamiltonian H q t) x)‖ ≤ L' := by
  set T := max T₀ 2 + A₀ with hTdef
  have hA0 : 0 ≤ A₀ := (abs_nonneg _).trans (hA₀ p₀ hp₀)
  -- On the end `q` the structures are those of `J_{p₀}` on the circle `φ_q(±T, t)` of `S`, moved
  -- by the offset of `q` at `p₀`.
  set γ : Puncture → ℝ → ℝ × ℝ := fun q t ↦ endChart q (q.endSign * T, t) + endOffset (a p₀) q
  have hmem (q : Puncture) (t : ℝ) : γ q t ∈ thricePuncturedSphereReal := by
    simp only [γ, endChart_eq_positiveEndChart]
    exact positiveEndChart_add_endOffset_mem hA0 (hA₀ p₀ hp₀) q
      (by rw [hTdef]; linarith [le_max_right T₀ 2])
  have hJq (q : Puncture) : Jq q = fun t ↦ J p₀ (γ q t) :=
    funext fun t ↦ funext fun x ↦
      (hJe p₀ hp₀ q T t x (by rw [hTdef]; linarith [le_max_left T₀ 2])).symm
  have hγ (q : Puncture) : ContDiff ℝ 2 (γ q) :=
    ((contDiff_endChart q 2).comp (contDiff_const.prodMk contDiff_id)).add contDiff_const
  have hJqs (q : Puncture) (α : M) : ContDiffOn ℝ 2 (almostComplexInChartAt I α (Jq q))
      (univ ×ˢ (extChartAt I α).target) := by
    have h := (hJ α).comp (s := univ ×ˢ (extChartAt I α).target)
      (f := fun p : ℝ × E ↦ ((p₀, γ q p.1), p.2))
      ((contDiff_const.prodMk ((hγ q).comp contDiff_fst)).prodMk contDiff_snd).contDiffOn
      fun p hp ↦ ⟨hCW ⟨hp₀, hmem q p.1⟩, hp.2⟩
    rw [hJq]
    exact h.congr fun p _ ↦ almostComplexInChartAt_comp (J := uncurry J)
      (fun t ↦ (p₀, γ q t)) p
  have hJqt (q : Puncture) (t : ℝ) (x : M) : (hω.symplecticFormAt x).Tames (Jq q t x) := by
    rw [hJq]
    exact hJt p₀ hp₀ _ (hmem q t) x
  -- One tameness constant serves the core truncation and the circles `γ q` over `0 ≤ t ≤ 1`.
  set Dt : Set (ℝ × ℝ) := equivRealProdCLM.symm ⁻¹' truncation (T + 2 + A₀) ∪
    ⋃ q, γ q '' Icc 0 1
  have hDtS : Dt ⊆ thricePuncturedSphereReal :=
    union_subset (preimage_truncation_subset_thricePuncturedSphereReal _)
      (iUnion_subset fun q ↦ by rintro _ ⟨t, -, rfl⟩; exact hmem q t)
  obtain ⟨c, hc, hJcD⟩ := hJc Dt ((isCompact_preimage_truncation _).union
    (isCompact_iUnion fun q ↦ isCompact_Icc.image (hγ q).continuous)) hDtS
  have hJqc (q : Puncture) (t : ℝ) (x : M) (v : TangentSpace I x) :
      c * ‖mvfderiv I e x v‖ ^ 2 ≤ hω.symplecticFormAt x v (Jq q t x v) := by
    -- The end chart is `1`-periodic in `t`, so `γ q t` lies on the arc of `γ q` over `[0, 1)`.
    obtain ⟨t', ht', heq⟩ := (periodic_comp_endChart q (· + endOffset (a p₀) q)
      (q.endSign * T)).exists_mem_Ico₀ one_pos t
    -- `heq` reads `(f ∘ endChart q) (±T, t) = (f ∘ endChart q) (±T, t')` for `f = (· + o)`,
    -- which is `γ q t = γ q t'` after unfolding the composition.
    have hγt : γ q t = γ q t' := heq
    have h : c * ‖mvfderiv I e x v‖ ^ 2 ≤ hω.symplecticFormAt x v (J p₀ (γ q t') x v) :=
      hJcD p₀ hp₀ _ (Or.inr (mem_iUnion.2 ⟨q, t', Ico_subset_Icc_self ht', rfl⟩)) x v
    simpa only [hJq, hγt] using h
  exact ⟨c, hc, fun p hp z hz x v ↦ hJcD p hp z (Or.inl hz) x v,
    fun q ↦ ⟨hJqs q, hJqt q, hJqc q, hω.exists_forall_norm_mvfderiv_hamiltonianVectorField_le
      (contMDiff_uncurry_positiveEndHamiltonian (hHs q)) (periodic_positiveEndHamiltonian (hH q))
      he⟩⟩

omit [FiniteDimensional ℝ E] [I.Boundaryless] [CompactSpace M] in
/-- The Floer equation is invariant under translations of the domain: if `u` solves it at `z + o`
for the perturbation `K`, then `w ↦ u (w + o)` solves it at `z` for the translated perturbation. -/
private theorem isComplexLinearMap_perturbedMFDeriv_comp_add {K : ℂ → M → ℂ →L[ℝ] ℝ}
    {u : ℝ × ℝ → M} {o z : ℝ × ℝ} {J : AlmostComplexStructure (TangentSpace I (u (z + o)))}
    (h : IsComplexLinearMap (AlmostComplexStructure.product ℝ) J
      (ω.perturbedMFDeriv (fun z x ↦ K (equivRealProdCLM.symm z) x 1)
        (fun z x ↦ K (equivRealProdCLM.symm z) x Complex.I) u (z + o)).toLinearMap) :
    IsComplexLinearMap (AlmostComplexStructure.product ℝ) J
      (ω.perturbedMFDeriv
        (fun z x ↦ K (equivRealProdCLM.symm z + equivRealProdCLM.symm o) x 1)
        (fun z x ↦ K (equivRealProdCLM.symm z + equivRealProdCLM.symm o) x Complex.I)
        (fun w ↦ u (w + o)) z).toLinearMap := by
  have heq := ω.perturbedMFDeriv_comp_add_right (fun z x ↦ K (equivRealProdCLM.symm z) x 1)
    (fun z x ↦ K (equivRealProdCLM.symm z) x Complex.I) u o z
  simp only [map_add] at heq
  rwa [heq]

omit [FiniteDimensional ℝ E] [I.Boundaryless] [CompactSpace M] in
/-- Translating a map and its perturbation by `o` preserves the energy: the energy of the
translates over `(· + o)⁻¹' S` is the energy over `S`. -/
private theorem lintegral_floerEnergyDensity_comp_add (K : ℂ → M → ℂ →L[ℝ] ℝ) (u : ℝ × ℝ → M)
    (o : ℝ × ℝ) (S : Set (ℝ × ℝ)) :
    ∫⁻ z in (· + o) ⁻¹' S, ENNReal.ofReal (ω.floerEnergyDensity
      (fun z x ↦ K (equivRealProdCLM.symm z + equivRealProdCLM.symm o) x 1)
      (fun z x ↦ K (equivRealProdCLM.symm z + equivRealProdCLM.symm o) x Complex.I)
      (fun w ↦ u (w + o)) z) =
      ∫⁻ z in S, ENNReal.ofReal (ω.floerEnergyDensity (fun z x ↦ K (equivRealProdCLM.symm z) x 1)
        (fun z x ↦ K (equivRealProdCLM.symm z) x Complex.I) u z) := by
  have h := ω.lintegral_floerEnergyDensity_comp_add_right
    (fun z x ↦ K (equivRealProdCLM.symm z) x 1) (fun z x ↦ K (equivRealProdCLM.symm z) x Complex.I)
    u o S
  simp only [map_add] at h
  exact h

omit [FiniteDimensional ℝ E] [I.Boundaryless] [CompactSpace M] in
/-- **Energy concentration under converging translations.** Let `oₙ → o`. If every neighbourhood
of `y` eventually carries energy at least `d` for the energy measures on `(· + oₙ)⁻¹' S` of the
translates `w ↦ uₙ (w + oₙ)`, for the translated perturbations, then every neighbourhood of `y + o`
eventually carries energy at least `d` for the energy measures of the `uₙ` on `S`. -/
private theorem eventually_le_withDensity_of_tendsto_add {K : ℕ → ℂ → M → ℂ →L[ℝ] ℝ}
    {u : ℕ → ℝ × ℝ → M} {o : ℕ → ℝ × ℝ} {o₀ : ℝ × ℝ} (ho : Tendsto o atTop (𝓝 o₀))
    {S : Set (ℝ × ℝ)} {y : ℝ × ℝ} {d : ENNReal}
    (h : ∀ N ∈ 𝓝 y, ∀ᶠ n in atTop, d ≤ (volume.restrict ((· + o n) ⁻¹' S)).withDensity
      (fun z ↦ ENNReal.ofReal (ω.floerEnergyDensity
        (fun z x ↦ K n (equivRealProdCLM.symm z + equivRealProdCLM.symm (o n)) x 1)
        (fun z x ↦ K n (equivRealProdCLM.symm z + equivRealProdCLM.symm (o n)) x Complex.I)
        (fun w ↦ u n (w + o n)) z)) N) :
    ∀ N ∈ 𝓝 (y + o₀), ∀ᶠ n in atTop, d ≤ (volume.restrict S).withDensity
      (fun z ↦ ENNReal.ofReal (ω.floerEnergyDensity
        (fun z x ↦ K n (equivRealProdCLM.symm z) x 1)
        (fun z x ↦ K n (equivRealProdCLM.symm z) x Complex.I) (u n) z)) N := by
  intro N hN
  obtain ⟨ε, hε, hεN⟩ := Metric.mem_nhds_iff.1 hN
  filter_upwards [h _ (ball_mem_nhds y (half_pos hε)),
    ho.eventually (ball_mem_nhds o₀ (half_pos hε))] with n hn hon
  -- The translate of the half disc about `y` lies in the disc about `y + o` inside `N`.
  have hsub : (· + o n) '' ball y (ε / 2) ⊆ N := by
    rintro _ ⟨z, hz, rfl⟩
    refine hεN (mem_ball.2 ?_)
    calc dist (z + o n) (y + o₀) ≤ dist z y + dist (o n) o₀ := dist_add_add_le _ _ _ _
      _ < ε / 2 + ε / 2 := add_lt_add (mem_ball.1 hz) (mem_ball.1 hon)
      _ = ε := add_halves ε
  have hmeas : MeasurableSet ((· + o n) '' ball y (ε / 2)) :=
    (measurableEmbedding_addRight _).measurableSet_image' measurableSet_ball
  refine hn.trans (Eq.trans_le ?_ (measure_mono hsub))
  rw [withDensity_apply _ measurableSet_ball, withDensity_apply _ hmeas,
    Measure.restrict_restrict measurableSet_ball, Measure.restrict_restrict hmeas,
    ← lintegral_floerEnergyDensity_comp_add, preimage_inter,
    preimage_image_eq _ (add_left_injective _)]

omit [FiniteDimensional ℝ E] [I.Boundaryless] [CompactSpace M] in
/-- **Bounds on the energy densities under converging translations.** Let `oₙ → o`. If the
energy densities of the translates `w ↦ uₙ (w + oₙ)`, for the translated perturbations, are
eventually bounded on a neighbourhood of `y`, then the energy densities of the `uₙ` are
eventually bounded on a neighbourhood of `y + o`. -/
private theorem exists_mem_nhds_forall_floerEnergyDensity_le_of_tendsto_add
    {K : ℕ → ℂ → M → ℂ →L[ℝ] ℝ} {u : ℕ → ℝ × ℝ → M} {o : ℕ → ℝ × ℝ} {o₀ : ℝ × ℝ}
    (ho : Tendsto o atTop (𝓝 o₀)) {y : ℝ × ℝ}
    (h : ∃ N ∈ 𝓝 y, ∃ A, ∀ᶠ n in atTop, ∀ x ∈ N, ω.floerEnergyDensity
      (fun z x ↦ K n (equivRealProdCLM.symm z + equivRealProdCLM.symm (o n)) x 1)
      (fun z x ↦ K n (equivRealProdCLM.symm z + equivRealProdCLM.symm (o n)) x Complex.I)
      (fun w ↦ u n (w + o n)) x ≤ A) :
    ∃ N ∈ 𝓝 (y + o₀), ∃ A, ∀ᶠ n in atTop, ∀ x ∈ N, ω.floerEnergyDensity
      (fun z x ↦ K n (equivRealProdCLM.symm z) x 1)
      (fun z x ↦ K n (equivRealProdCLM.symm z) x Complex.I) (u n) x ≤ A := by
  obtain ⟨N, hN, A, hA⟩ := h
  obtain ⟨ε, hε, hεN⟩ := Metric.mem_nhds_iff.1 hN
  refine ⟨ball (y + o₀) (ε / 2), ball_mem_nhds _ (half_pos hε), A, ?_⟩
  filter_upwards [hA, ho.eventually (ball_mem_nhds o₀ (half_pos hε))] with n hn hon x hx
  -- The point `x - oₙ` lies in the disc about `y` inside `N`.
  have hxN : x - o n ∈ N := by
    refine hεN (mem_ball.2 ?_)
    calc dist (x - o n) y = dist (x - o n) (y + o₀ - o₀) := by rw [add_sub_cancel_right]
      _ ≤ dist x (y + o₀) + dist (o n) o₀ := dist_sub_sub_le _ _ _ _
      _ < ε / 2 + ε / 2 := add_lt_add (mem_ball.1 hx) (mem_ball.1 hon)
      _ = ε := add_halves ε
  have heq := ω.floerEnergyDensity_comp_add_right (fun z x ↦ K n (equivRealProdCLM.symm z) x 1)
    (fun z x ↦ K n (equivRealProdCLM.symm z) x Complex.I) (u n) (o n) (x - o n)
  simp only [map_add, sub_add_cancel] at heq
  exact heq ▸ hn _ hxN

omit [FiniteDimensional ℝ E] [I.Boundaryless] [CompactSpace M] [NormedSpace ℝ F] in
/-- **An end window of a family, read on `S`.** Let `oₖ` be offsets, with `o_{φ n} → o`, and let
`Kₖ` be perturbations such that `w ↦ Kₖ(w + oₖ)` is `H_q(t) dt` beyond `T₀` on the end `q`. Let
`g(y) = φ'_q(y + (m, 0))` be the translated positive end chart, `T ≥ T₀` nonnegative, and let the
moved charts `ζ ↦ φ'_q(ζ) + oₖ` map the part `s > T` of the cylinder into `S`. If along `φ` the end
readings `y ↦ uₖ(g(y) + oₖ)`, read through `e`, converge locally uniformly on the end window off a
finite set `Z`, at each point of which the energy `δ` of the end readings concentrates, and their
energy densities are uniformly bounded on every compact subset of the end window off `Z`, then the
solutions read through `e` converge locally uniformly on the window `g(endWindow) + o` of `S` off
`g(Z) + o`, every neighbourhood of a point of `g(Z) + o` eventually carries energy at least `δ`
for the energy measure of `uₖ` on `S`, and the energy densities of the `uₖ` are eventually bounded
near every point of the window off `g(Z) + o`. -/
private theorem concentration_and_tendstoLocallyUniformlyOn_window_some
    {K : ℕ → ℂ → M → ℂ →L[ℝ] ℝ} {T₀ : ℝ} {q : Puncture} {o : ℕ → ℝ × ℝ} {o₀ : ℝ × ℝ}
    {φ : ℕ → ℕ} (ho : Tendsto (fun n ↦ o (φ n)) atTop (𝓝 o₀))
    (hKH : ∀ k w x, T₀ ≤ q.endSign * (q.endCoord w).re →
      K k (w + equivRealProdCLM.symm (o k)) x = H q (q.endCoord w).im x • q.endAngularForm w)
    (hH : Periodic (H q) 1) (hHs : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (H q)))
    {u : ℕ → ℝ × ℝ → M} (hu : ∀ k, ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 (u k) thricePuncturedSphereReal)
    (he : Continuous e) {T : ℝ} (hT₀ : T₀ ≤ T) (hT : 0 ≤ T)
    (hTo : ∀ k (ζ : ℝ × ℝ), T < ζ.1 → positiveEndChart q ζ + o k ∈ thricePuncturedSphereReal)
    (m : ℕ) (b : Bool) {δ : ℝ} {Z : Finset (ℝ × ℝ)} (hZ : ↑Z ⊆ endWindow T b)
    (hconc : ∀ z ∈ Z, ∀ ε > 0, ∀ᶠ n in atTop, δ ≤ ∫ y in ball z ε ∩ endWindow T b,
      ω.floerEnergyDensity (fun _ _ ↦ 0) (fun w ↦ positiveEndHamiltonian H q w.2)
        (fun z ↦ u (φ n) (positiveEndChart q (z + ((m : ℝ), 0)) + o (φ n))) y)
    (hbd : ∀ C, IsCompact C → C ⊆ endWindow T b \ ↑Z → ∃ A, ∀ n, ∀ y ∈ C, ω.floerEnergyDensity
      (fun _ _ ↦ 0) (fun w ↦ positiveEndHamiltonian H q w.2)
      (fun z ↦ u (φ n) (positiveEndChart q (z + ((m : ℝ), 0)) + o (φ n))) y ≤ A)
    {v : ℝ × ℝ → F}
    (hv : TendstoLocallyUniformlyOn
      (fun n z ↦ e (u (φ n) (positiveEndChart q (z + ((m : ℝ), 0)) + o (φ n)))) v atTop
      (endWindow T b \ ↑Z)) :
    (∀ z ∈ (fun y ↦ positiveEndChart q (y + ((m : ℝ), 0)) + o₀) '' ↑Z, ∀ N ∈ 𝓝 z,
      ∀ᶠ n in atTop, ENNReal.ofReal δ ≤ (volume.restrict thricePuncturedSphereReal).withDensity
        (fun y ↦ ENNReal.ofReal (ω.floerEnergyDensity
          (fun z x ↦ K (φ n) (equivRealProdCLM.symm z) x 1)
          (fun z x ↦ K (φ n) (equivRealProdCLM.symm z) x Complex.I) (u (φ n)) y)) N) ∧
      (∀ y ∈ (fun y ↦ positiveEndChart q (y + ((m : ℝ), 0)) + o₀) '' endWindow T b \
          (fun y ↦ positiveEndChart q (y + ((m : ℝ), 0)) + o₀) '' ↑Z,
        ∃ N ∈ 𝓝 y, ∃ A, ∀ᶠ n in atTop, ∀ x ∈ N, ω.floerEnergyDensity
          (fun z x ↦ K (φ n) (equivRealProdCLM.symm z) x 1)
          (fun z x ↦ K (φ n) (equivRealProdCLM.symm z) x Complex.I) (u (φ n)) x ≤ A) ∧
      ∃ v' : ℝ × ℝ → F, TendstoLocallyUniformlyOn (fun n ↦ e ∘ u (φ n)) v' atTop
        ((fun y ↦ positiveEndChart q (y + ((m : ℝ), 0)) + o₀) '' endWindow T b \
          (fun y ↦ positiveEndChart q (y + ((m : ℝ), 0)) + o₀) '' ↑Z) := by
  set g : ℝ × ℝ → ℝ × ℝ := fun y ↦ positiveEndChart q (y + ((m : ℝ), 0))
  -- The translates `ûₖ = uₖ(· + oₖ)` are defined on `Uₖ = S - oₖ`, which contains the end.
  set U : ℕ → Set (ℝ × ℝ) := fun k ↦ (· + o k) ⁻¹' thricePuncturedSphereReal
  have hU (k : ℕ) : IsOpen (U k) :=
    isOpen_thricePuncturedSphereReal.preimage (continuous_id.add continuous_const)
  have hΩT (y : ℝ × ℝ) (hy : y ∈ endWindow T b) :=
    endWindow_add_mem_Ioi_prod_Ioo (max_le le_rfl hT) (Nat.cast_nonneg m) hy
  have hUq (k : ℕ) (ζ : ℝ × ℝ) (hζ : max T 0 < ζ.1) : positiveEndChart q ζ ∈ U k :=
    hTo k ζ ((le_max_left _ _).trans_lt hζ)
  have hû (k : ℕ) : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 (fun w ↦ u k (w + o k)) (U k) :=
    (hu k).comp (contMDiff_id.add contMDiff_const).contMDiffOn fun _ hw ↦ hw
  have hHd (t : ℝ) : MDifferentiable I 𝓘(ℝ) (H q t) :=
    (hHs.comp (contMDiff_const.prodMk contMDiff_id)).mdifferentiable one_ne_zero
  -- The translates converge on `g(endWindow) \ g(Z)`, to a continuous limit.
  obtain ⟨v', hv'⟩ := exists_tendstoLocallyUniformlyOn_image_positiveEndChart_add
    (isOpen_endWindow T b) hΩT hZ (f := fun n ↦ e ∘ fun w ↦ u (φ n) (w + o (φ n))) hv
  have hsub (n : ℕ) : g '' endWindow T b \ g '' ↑Z ⊆ U (φ n) := by
    rintro _ ⟨⟨y, hy, rfl⟩, -⟩
    exact hUq _ _ (hΩT y hy).1
  have hcont := hv'.continuousOn (Eventually.of_forall fun n ↦
    he.comp_continuousOn ((hû (φ n)).continuousOn.mono (hsub n))).frequently
  have hopen : IsOpen (g '' endWindow T b \ g '' ↑Z) :=
    (((isOpenMap_positiveEndChart q).comp (Homeomorph.addRight _).isOpenMap) _
      (isOpen_endWindow T b)).sdiff (Z.finite_toSet.image g).isClosed
  have hset : (· + o₀) '' (g '' endWindow T b \ g '' ↑Z) =
      (fun y ↦ g y + o₀) '' endWindow T b \ (fun y ↦ g y + o₀) '' ↑Z := by
    rw [image_sdiff (add_left_injective o₀), image_image, image_image]
  refine ⟨?_, ?_, fun y ↦ v' (y - o₀), ?_⟩
  · -- The concentration of the translates moves to the solutions along the offsets.
    rintro _ ⟨z, hz, rfl⟩ N hN
    have hc := eventually_ofReal_le_withDensity_image_positiveEndChart_add
      (K := fun k w ↦ K k (w + equivRealProdCLM.symm (o k))) (q := q) hKH hH hHd hU hT₀ hUq
      (fun k ↦ (hû k).mdifferentiableOn one_ne_zero) (isOpen_endWindow T b) hΩT (φ := φ) hconc
    exact eventually_le_withDensity_of_tendsto_add (K := fun n ↦ K (φ n))
      (u := fun n ↦ u (φ n)) (o := fun n ↦ o (φ n)) ho (hc _ ⟨z, hz, rfl⟩) N hN
  · -- So do the bounds on the energy densities of the translates.
    rw [← hset]
    rintro _ ⟨y, hy, rfl⟩
    exact exists_mem_nhds_forall_floerEnergyDensity_le_of_tendsto_add (K := fun n ↦ K (φ n))
      (u := fun n ↦ u (φ n)) (o := fun n ↦ o (φ n)) ho
      (exists_mem_nhds_forall_floerEnergyDensity_le_image_positiveEndChart_add
        (K := fun k w ↦ K k (w + equivRealProdCLM.symm (o k))) (q := q) hKH hH hHd hU hT₀ hUq
        (fun k ↦ (hû k).mdifferentiableOn one_ne_zero) (isOpen_endWindow T b) hΩT (φ := φ) hbd y
        hy)
  · -- The solutions are the translates moved back by the offsets.
    rw [← hset]
    refine (hv'.comp_sub_of_tendsto hopen hcont ho).congr fun n y _ ↦ ?_
    simp only [comp_apply, sub_add_cancel]

/-- **The moved windows of an end, with one threshold.** Let `H_q` be a period-one `C³`
Hamiltonian and `J_q(t, x)` structures on the tangent spaces of `M`, tame, `C²` read in the chart
at every point of `M` and uniformly tame with respect to an injective `C¹` map `e : M → F`, with
the pushforwards through `e` of the Hamiltonian vector fields of `H'_q` bounded. There is a
threshold `δ > 0` with the following property. Let `oₖ → o` be offsets and `Kₖ`, `Jₖ` data such
that beyond `T ≥ 0` on the end `q`, in the end chart moved by `oₖ`, `w ↦ Kₖ(w + oₖ)` is
`H_q(t) dt` and `Jₖ` is `J_q(t)`, and let the moved chart map the part `s > T` of the cylinder into
`S`. Then every sequence of `C³` solutions `uₖ` on `S` of energy at most `E` has, for each
`m ∈ ℕ`, a subsequence converging, read through `e`, locally uniformly on the moved end window
`g(endWindow) + o`, for `g(y) = φ'_q(y + (m, 0))`, off a set at each point of which the energy
measure of every neighbourhood is eventually at least `δ`, and near every other point of the moved
end window the energy densities are eventually bounded. -/
private theorem exists_pos_forall_subseq_window_some (hω : ω.IsNondegenerate) {q : Puncture}
    (hH : Periodic (H q) 1) (hHs : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 3 (uncurry (H q)))
    {Jq : ℝ → (x : M) → AlmostComplexStructure (TangentSpace I x)}
    (hJq : ∀ α, ContDiffOn ℝ 2 (almostComplexInChartAt I α Jq) (univ ×ˢ (extChartAt I α).target))
    (hJt : ∀ t x, (hω.symplecticFormAt x).Tames (Jq t x))
    (he : ContMDiff I 𝓘(ℝ, F) 1 e) (he_inj : Injective e) {c L : ℝ} (hc : 0 < c)
    (hJc : ∀ t x v, c * ‖mvfderiv I e x v‖ ^ 2 ≤ hω.symplecticFormAt x v (Jq t x v))
    (hL : ∀ t x,
      ‖mvfderiv I e x (ω.hamiltonianVectorField (positiveEndHamiltonian H q t) x)‖ ≤ L)
    {T : ℝ} (hT : 0 ≤ T) (b : Bool) :
    ∃ δ > 0, ∀ ⦃K : ℕ → ℂ → M → ℂ →L[ℝ] ℝ⦄
      ⦃J : ℕ → ℝ × ℝ → (x : M) → AlmostComplexStructure (TangentSpace I x)⦄
      ⦃u : ℕ → ℝ × ℝ → M⦄ ⦃E : ℝ⦄ ⦃o : ℕ → ℝ × ℝ⦄ ⦃o₀ : ℝ × ℝ⦄, Tendsto o atTop (𝓝 o₀) →
      (∀ k w x, T ≤ q.endSign * (q.endCoord w).re →
        K k (w + equivRealProdCLM.symm (o k)) x = H q (q.endCoord w).im x • q.endAngularForm w) →
      (∀ k s t x, T ≤ s → J k (endChart q (q.endSign * s, t) + o k) x = Jq t x) →
      (∀ k (ζ : ℝ × ℝ), T < ζ.1 → positiveEndChart q ζ + o k ∈ thricePuncturedSphereReal) →
      (∀ k, ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 3 (u k) thricePuncturedSphereReal) →
      (∀ k, ∀ z ∈ thricePuncturedSphereReal,
        IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J k z (u k z))
          (ω.perturbedMFDeriv (fun z x ↦ K k (equivRealProdCLM.symm z) x 1)
            (fun z x ↦ K k (equivRealProdCLM.symm z) x Complex.I) (u k) z).toLinearMap) →
      0 ≤ E →
      (∀ k, ∫⁻ z in thricePuncturedSphereReal, ENNReal.ofReal (ω.floerEnergyDensity
        (fun z x ↦ K k (equivRealProdCLM.symm z) x 1)
        (fun z x ↦ K k (equivRealProdCLM.symm z) x Complex.I) (u k) z) ≤ ENNReal.ofReal E) →
      ∀ m : ℕ, ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ Z : Set (ℝ × ℝ),
        (∀ z ∈ Z, ∀ N ∈ 𝓝 z, ∀ᶠ n in atTop, ENNReal.ofReal δ ≤
          (volume.restrict thricePuncturedSphereReal).withDensity (fun y ↦ ENNReal.ofReal
            (ω.floerEnergyDensity (fun z x ↦ K (φ n) (equivRealProdCLM.symm z) x 1)
              (fun z x ↦ K (φ n) (equivRealProdCLM.symm z) x Complex.I) (u (φ n)) y)) N) ∧
        (∀ y ∈ (fun y ↦ positiveEndChart q (y + ((m : ℝ), 0)) + o₀) '' endWindow T b \ Z,
          ∃ N ∈ 𝓝 y, ∃ A, ∀ᶠ n in atTop, ∀ x ∈ N, ω.floerEnergyDensity
            (fun z x ↦ K (φ n) (equivRealProdCLM.symm z) x 1)
            (fun z x ↦ K (φ n) (equivRealProdCLM.symm z) x Complex.I) (u (φ n)) x ≤ A) ∧
        ∃ v : ℝ × ℝ → F, TendstoLocallyUniformlyOn (fun n ↦ e ∘ u (φ n)) v atTop
          ((fun y ↦ positiveEndChart q (y + ((m : ℝ), 0)) + o₀) '' endWindow T b \ Z) := by
  obtain ⟨δ, hδ, hconv⟩ :=
    hω.exists_pos_forall_tendstoLocallyUniformlyOn_comp_subseq_off_finset_comp_positiveEndChart
      (T₀ := T) hH hHs hJq hJt (he.mdifferentiable one_ne_zero) he_inj hc hJc hL
      (D := Icc (T + 1) (T + 3) ×ˢ Icc ((bif b then (1 / 2 : ℝ) else 0) - 2 / 5)
        ((bif b then 1 / 2 else 0) + 2 / 5)) (isCompact_Icc.prod isCompact_Icc)
      (t₀ := (bif b then 1 / 2 else 0) - 1 / 2)
      (endWindow_closed_subset_Ioi_prod_Ioo (max_le le_rfl hT) b)
  refine ⟨δ, hδ, fun K J u E o o₀ ho hKH hJe hTo hu hfl hE0 hE m ↦ ?_⟩
  -- Read the end in its end chart moved by the offsets: the translates `uₖ(· + oₖ)` solve the
  -- Floer equation on `S - oₖ`, which contains the end.
  obtain ⟨φ, hφ, Z, hZΩ, -, hconc, hbd, v, -, hv, -⟩ := hconv
    (K := fun k w ↦ K k (w + equivRealProdCLM.symm (o k))) (J := fun k z ↦ J k (z + o k))
    (Ω := endWindow T b) (U := fun k ↦ (· + o k) ⁻¹' thricePuncturedSphereReal)
    (u := fun k z ↦ u k (z + o k)) (R := fun _ ↦ (m : ℝ)) hKH hJe
    (isOpen_endWindow _ b) (endWindow_subset_Icc_prod_Icc _ b) (fun _ ↦ Nat.cast_nonneg m)
    (fun k ↦ isOpen_thricePuncturedSphereReal.preimage (continuous_id.add continuous_const))
    (fun k ζ hζ ↦ hTo k ζ ((le_max_left _ _).trans_lt hζ))
    (fun k ↦ (hu k).comp (contMDiff_id.add contMDiff_const).contMDiffOn fun _ hw ↦ hw)
    (fun k z hz ↦ isComplexLinearMap_perturbedMFDeriv_comp_add (hfl _ _ hz))
    hE0 (fun k ↦ (lintegral_floerEnergyDensity_comp_add _ _ _ _).trans_le (hE _))
  -- Then move the convergence and the concentration back along the offsets.
  have h := concentration_and_tendstoLocallyUniformlyOn_window_some (K := K) (u := u) (o := o)
    (φ := φ) (δ := δ) (ho.comp hφ.tendsto_atTop) hKH hH (hHs.of_le (by norm_num))
    (fun k ↦ (hu k).of_le (by norm_num)) he.continuous le_rfl hT hTo m b hZΩ hconc hbd hv
  exact ⟨φ, hφ, _, h.1, h.2.1, h.2.2⟩

/-- **The windows of a family, with one threshold.** Under the hypotheses of the main theorem
below, for a parameter `p₀ ∈ C` and a bound `A₀` of the centres `|a p|`, `p ∈ C`, of the output
end, there is a threshold `δ > 0` such that on every window for an output end recentred at a limit
`a₀` of the centres `a(pₖ)`, every subsequence of a sequence of solutions for parameters `pₖ ∈ C`,
with energy at most `E` over `S`, has a further subsequence along which the solutions read through
`e` converge off a set at each point of which the energy measure of every neighbourhood is
eventually at least `δ`, and near every other point of the window the energy densities are
eventually bounded. -/
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
    {a : P → ℝ} {A₀ : ℝ} (hA₀ : ∀ p ∈ C, |a p| ≤ A₀)
    {T₀ : ℝ} (hKH : ∀ p ∈ C, ∀ q w x, T₀ ≤ q.endSign * (q.endCoord w).re →
      K p (w + equivRealProdCLM.symm (endOffset (a p) q)) x =
        H q (q.endCoord w).im x • q.endAngularForm w)
    (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 3 (uncurry (H q)))
    {Jq : Puncture → ℝ → (x : M) → AlmostComplexStructure (TangentSpace I x)}
    (hJe : ∀ p ∈ C, ∀ q s t x, T₀ ≤ s →
      J p (endChart q (q.endSign * s, t) + endOffset (a p) q) x = Jq q t x)
    (he : ContMDiff I 𝓘(ℝ, F) 1 e) (he_inj : Injective e) {p₀ : P} (hp₀ : p₀ ∈ C) :
    ∃ δ > 0, ∀ ⦃p : ℕ → P⦄ ⦃u : ℕ → ℝ × ℝ → M⦄ ⦃E a₀ : ℝ⦄, (∀ k, p k ∈ C) →
      Tendsto (fun k ↦ a (p k)) atTop (𝓝 a₀) → |a₀| ≤ A₀ →
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
      (∀ k, ∫ z in window (max T₀ 2 + A₀) a₀ none, ω.floerEnergyDensity
        (fun z x ↦ K (p k) (equivRealProdCLM.symm z) x 1)
        (fun z x ↦ K (p k) (equivRealProdCLM.symm z) x Complex.I) (u k) z ≤ E) →
      ∀ i ⦃ψ : ℕ → ℕ⦄, StrictMono ψ → ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ Z : Set (ℝ × ℝ),
        (∀ z ∈ Z, ∀ N ∈ 𝓝 z, ∀ᶠ n in atTop, ENNReal.ofReal δ ≤
          (volume.restrict thricePuncturedSphereReal).withDensity (fun y ↦ ENNReal.ofReal
            (ω.floerEnergyDensity (fun z x ↦ K (p (ψ (φ n))) (equivRealProdCLM.symm z) x 1)
              (fun z x ↦ K (p (ψ (φ n))) (equivRealProdCLM.symm z) x Complex.I)
              (u (ψ (φ n))) y)) N) ∧
        (∀ y ∈ window (max T₀ 2 + A₀) a₀ i \ Z, ∃ N ∈ 𝓝 y, ∃ A, ∀ᶠ n in atTop, ∀ x ∈ N,
          ω.floerEnergyDensity (fun z x ↦ K (p (ψ (φ n))) (equivRealProdCLM.symm z) x 1)
            (fun z x ↦ K (p (ψ (φ n))) (equivRealProdCLM.symm z) x Complex.I) (u (ψ (φ n))) x ≤
              A) ∧
        ∃ v : ℝ × ℝ → F, TendstoLocallyUniformlyOn (fun n ↦ e ∘ u (ψ (φ n))) v atTop
          (window (max T₀ 2 + A₀) a₀ i \ Z) := by
  set T := max T₀ 2 + A₀ with hTdef
  have hA0 : 0 ≤ A₀ := (abs_nonneg _).trans (hA₀ p₀ hp₀)
  have hTT₀ : T₀ ≤ T := by rw [hTdef]; linarith [le_max_left T₀ 2]
  have hTA : A₀ + 2 ≤ T := by rw [hTdef]; linarith [le_max_right T₀ 2]
  have hDS := preimage_truncation_subset_thricePuncturedSphereReal (T + 2 + A₀)
  obtain ⟨c, hc, hJcc, hq⟩ := exists_pos_family_window_data hω hH
    (fun q ↦ (hHs q).of_le (by norm_num)) hCW hJ hJt hJc hA₀ hJe he hp₀
  obtain ⟨B, hBD⟩ := hB _ (isCompact_preimage_truncation (T + 2 + A₀)) hDS
  -- The thresholds of the two windows of each end, uniform in the translation, and of the core.
  choose δe hδe hconve using fun q b ↦ exists_pos_forall_subseq_window_some hω (hH q) (hHs q)
    (hq q).1 (hq q).2.1 he he_inj hc (hq q).2.2.1 (hq q).2.2.2.choose_spec (T := T)
    (by linarith) b
  obtain ⟨δc, hδc, hconvc⟩ :=
    hω.exists_pos_forall_tendsto_tendstoLocallyUniformlyOn_comp_subseq_off_finset
      (he.mdifferentiable one_ne_zero) he_inj hW hC (isCompact_preimage_truncation (T + 2 + A₀))
      ((prod_mono subset_rfl hDS).trans hCW) hJ hXs hXt (fun p hp z hz x ↦ hJt p hp z (hDS hz) x)
      hc hJcc (fun p hp z hz x ↦ (hBD p hp z hz x).1) fun p hp z hz x ↦ (hBD p hp z hz x).2
  refine ⟨min δc (Finset.univ.inf' ⟨(.zero, false), Finset.mem_univ _⟩
    fun p : Puncture × Bool ↦ δe p.1 p.2), lt_min hδc ((Finset.lt_inf'_iff _).2 fun p _ ↦
      hδe p.1 p.2), fun p u E a₀ hpC ha hA hu hfl hint hE0 hEl hEc i ψ hψ ↦ ?_⟩
  rcases i with _ | ⟨q, m, b⟩
  · have hΩS : window T a₀ none ⊆ thricePuncturedSphereReal := fun y hy ↦ hy.1
    obtain ⟨φ, hφ, -, -, -, Z, -, -, hc, hbd, v, -, hv, -⟩ := hconvc (p := p ∘ ψ) (u := u ∘ ψ)
      (isOpen_window _ _ none) (window_none_subset (by linarith) hA) (fun k ↦ hpC _)
      (fun k ↦ (hu _).mono hΩS) (fun k z hz ↦ hfl _ z (hΩS hz)) (fun k ↦ (hint _).mono_set hΩS)
      fun k ↦ hEc _
    exact ⟨φ, hφ, ↑Z, fun z hz ↦
      eventually_ofReal_le_withDensity_of_forall_eventually_le_setIntegral_ball
        (isOpen_window _ _ none).measurableSet hΩS
        fun ε hε ↦ (hc z hz ε hε).mono fun n hn ↦ (min_le_left _ _).trans hn,
      -- A compact neighbourhood of a point off the bubbling points carries a bound.
      fun y hy ↦ (local_compact_nhds (((isOpen_window _ _ none).sdiff
        Z.finite_toSet.isClosed).mem_nhds hy)).elim fun L ⟨hL, hLΩ, hLc⟩ ↦
          ⟨L, hL, (hbd L hLc hLΩ).imp fun _ hA ↦ .of_forall hA⟩, e ∘ v, hv⟩
  · -- Read the end `q` in its end chart moved by the offsets of `q` at the parameters.
    obtain ⟨φ, hφ, Z, hconc, hbd, v, hv⟩ := hconve q b (K := fun k ↦ K (p (ψ k)))
      (J := fun k ↦ J (p (ψ k))) (u := u ∘ ψ) (tendsto_endOffset (ha.comp hψ.tendsto_atTop) q)
      (fun k w x hw ↦ hKH _ (hpC _) q w x (hTT₀.trans hw))
      (fun k s t x hs ↦ hJe _ (hpC _) q s t x (hTT₀.trans hs))
      (fun k ζ hζ ↦ positiveEndChart_add_endOffset_mem hA0 (hA₀ _ (hpC _)) q (by linarith))
      (fun k ↦ hu _) (fun k ↦ hfl _) hE0 (fun k ↦ hEl _) m
    rw [window_some]
    exact ⟨φ, hφ, Z, fun z hz N hN ↦ (hconc z hz N hN).mono fun n hn ↦
      (ENNReal.ofReal_le_ofReal ((min_le_right _ _).trans (Finset.inf'_le
        (fun p : Puncture × Bool ↦ δe p.1 p.2) (Finset.mem_univ (q, b))))).trans hn, hbd, v, hv⟩

omit [FiniteDimensional ℝ E] [I.Boundaryless] [CompactSpace M] in
/-- The Floer energy densities of solutions for tame structures are nonnegative on `S`, so a bound
`E` on their energies over `S` is nonnegative and bounds their energy measures of `S`. -/
private theorem floerEnergyDensity_nonneg_and_nonneg_and_lintegral_le (hω : ω.IsNondegenerate)
    {K : ℕ → ℂ → M → ℂ →L[ℝ] ℝ}
    {J : ℕ → ℝ × ℝ → (x : M) → AlmostComplexStructure (TangentSpace I x)}
    {u : ℕ → ℝ × ℝ → M} {E : ℝ}
    (hJt : ∀ k, ∀ z ∈ thricePuncturedSphereReal, ∀ x, (hω.symplecticFormAt x).Tames (J k z x))
    (hfl : ∀ k, ∀ z ∈ thricePuncturedSphereReal,
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J k z (u k z))
        (ω.perturbedMFDeriv (fun z x ↦ K k (equivRealProdCLM.symm z) x 1)
          (fun z x ↦ K k (equivRealProdCLM.symm z) x Complex.I) (u k) z).toLinearMap)
    (hint : ∀ k, IntegrableOn (ω.floerEnergyDensity (fun z x ↦ K k (equivRealProdCLM.symm z) x 1)
      (fun z x ↦ K k (equivRealProdCLM.symm z) x Complex.I) (u k)) thricePuncturedSphereReal)
    (hE : ∀ k, ∫ z in thricePuncturedSphereReal, ω.floerEnergyDensity
      (fun z x ↦ K k (equivRealProdCLM.symm z) x 1)
      (fun z x ↦ K k (equivRealProdCLM.symm z) x Complex.I) (u k) z ≤ E) :
    (∀ k, ∀ z ∈ thricePuncturedSphereReal, 0 ≤ ω.floerEnergyDensity
      (fun z x ↦ K k (equivRealProdCLM.symm z) x 1)
      (fun z x ↦ K k (equivRealProdCLM.symm z) x Complex.I) (u k) z) ∧ 0 ≤ E ∧
      ∀ k, ∫⁻ z in thricePuncturedSphereReal, ENNReal.ofReal (ω.floerEnergyDensity
        (fun z x ↦ K k (equivRealProdCLM.symm z) x 1)
        (fun z x ↦ K k (equivRealProdCLM.symm z) x Complex.I) (u k) z) ≤ ENNReal.ofReal E := by
  have hS := isOpen_thricePuncturedSphereReal.measurableSet
  have h0 (k : ℕ) (z : ℝ × ℝ) (hz : z ∈ thricePuncturedSphereReal) :=
    floerEnergyDensity_nonneg hω (hJt k z hz _) (hfl k z hz)
  refine ⟨h0, (setIntegral_nonneg hS (h0 0)).trans (hE 0), fun k ↦ ?_⟩
  rw [← ofReal_integral_eq_lintegral_ofReal (hint k) (ae_restrict_of_forall_mem hS (h0 k))]
  exact ENNReal.ofReal_le_ofReal (hE k)

/-- **Families of Floer pairs of pants in a closed manifold with a recentred output end converge
off finitely many bubbling points on the whole domain.** Let `ω` be a nondegenerate two-form on a
closed manifold `M`, such as a closed symplectic manifold, and let `K_p` and `J_p(z, x)` be
perturbations on `S = ℂ ∖ {0, 1}` and structures on the tangent spaces of `M`, depending on a
parameter `p` in a finite-dimensional real normed space `P`, with `J_p` tamed by `ω` over `S` (read
in real coordinates) for `p` in a compact window `C ⊆ P`. Suppose that, read in the chart at every
point of `M`, the structures and the Hamiltonian vector fields of the two components of `K_p` are
`C²` jointly in `(p, z, y)` on `W × (chart target)` for an open `W ⊇ C × S`, and that they are
cylindrical on the ends with data independent of `p`, the output end being recentred at a point
`a(p)` of the real axis depending continuously on `p ∈ C`: beyond `T₀` on the input end `q`, `K_p`
is `H_q(t) dt` and `J_p` is `J_q(t, x)` in the end coordinates, and beyond `T₀` on the output end,
`w ↦ K_p(w + a(p))` is `H_∞(t) dt` and `J_p` is `J_∞(t, x)` in the end coordinates of the output
end moved by `a(p)`. Here the `H_q` are period-one `C³` Hamiltonians. Let `e : M → F` be an
injective `C¹` map into a normed space, such as the Whitney embedding, and over every compact
`D ⊆ S` let the structures `J_p`, `p ∈ C`, be uniformly tame with respect to `e` and the
pushforwards through `e` of the Hamiltonian vector fields of `K_p` be bounded. There is a threshold
`δ > 0` with the following property. Let `uₖ` be `C³` solutions of `(du - X_{K_{pₖ}})^{0,1} = 0`
on `S` for `J_{pₖ}(z, u)`, with `pₖ ∈ C`, with integrable energy density and Floer energy at most
`E` over `S`. Then there are a subsequence `φ`, a limit `p₀ ∈ C` of the parameters `p_{φ n}`, a
finite set `Z ⊆ S` with `#Z * δ ≤ E` and a map `v : S \ Z → M`, continuous, such that along `φ`
every disc about a point of `Z` eventually carries energy at least `δ`, the energy densities are
eventually bounded near every point of `S \ Z`, and the solutions converge to `v` on `S \ Z`,
locally uniformly after applying `e` and pointwise in `M`. -/
theorem exists_pos_forall_tendsto_tendstoLocallyUniformlyOn_comp_subseq_off_finset_of_recentered
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
    {a : P → ℝ} (ha : ContinuousOn a C)
    {T₀ : ℝ} (hKH : ∀ p ∈ C, ∀ q, q ≠ .inf → ∀ w x, T₀ ≤ q.endSign * (q.endCoord w).re →
      K p w x = H q (q.endCoord w).im x • q.endAngularForm w)
    (hKH' : ∀ p ∈ C, ∀ w x, T₀ ≤ -(Puncture.inf.endCoord w).re →
      K p (w + a p) x = H .inf (Puncture.inf.endCoord w).im x • Puncture.inf.endAngularForm w)
    (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 3 (uncurry (H q)))
    {Jq : Puncture → ℝ → (x : M) → AlmostComplexStructure (TangentSpace I x)}
    (hJe : ∀ p ∈ C, ∀ q, q ≠ .inf → ∀ s t x, T₀ ≤ s →
      J p (endChart q (q.endSign * s, t)) x = Jq q t x)
    (hJe' : ∀ p ∈ C, ∀ s t x, T₀ ≤ s → J p (endChart .inf (-s, t) + (a p, 0)) x = Jq .inf t x)
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
  -- The centres of the output end are bounded on `C`.
  obtain ⟨A₀, hA₀⟩ := hC.exists_bound_of_continuousOn ha
  have hA₀' (p : P) (hp : p ∈ C) : |a p| ≤ A₀ := (Real.norm_eq_abs _).symm.trans_le (hA₀ p hp)
  -- Uniformly in the ends, the data are cylindrical in the end charts moved by the offsets.
  obtain ⟨δ, hδ, hwin⟩ := exists_pos_forall_family_window hω hW hC hCW hJ hXs hXt hJt hJc hB
    hA₀' (fun p hp ↦ eq_smul_endAngularForm_of_add_endOffset hKH hKH' hp) hH hHs
    (fun p hp ↦ eq_of_endChart_add_endOffset hJe hJe' hp) he he_inj hp₁
  refine ⟨δ, hδ, fun p u E hpC hu hfl hint hE ↦ ?_⟩
  have hS := isOpen_thricePuncturedSphereReal.measurableSet
  -- The energy is nonnegative, so it bounds the energy measure of `S` and the energy over parts.
  obtain ⟨h0, hE0, hEl⟩ := floerEnergyDensity_nonneg_and_nonneg_and_lintegral_le hω
    (fun k ↦ hJt _ (hpC k)) hfl hint hE
  -- First make the parameters, and so the centres of the output end, converge.
  obtain ⟨p₀, hp₀, ψ, hψ, hpψ⟩ := hC.tendsto_subseq hpC
  have ha₀ : Tendsto (fun k ↦ a (p (ψ k))) atTop (𝓝 (a p₀)) :=
    (ha p₀ hp₀).tendsto.comp (tendsto_nhdsWithin_iff.2 ⟨hpψ, .of_forall fun k ↦ hpC _⟩)
  -- Assemble the windows by the diagonal argument, for the energy measures of the `uₖ` on `S`.
  obtain ⟨φ, Z, g, hφ, hZ, hcard, hconc, hbd, hconv⟩ :=
    exists_tendstoLocallyUniformlyOn_subseq_off_finset_iUnion_of_le
      (isOpen_window (max T₀ 2 + A₀) (a p₀))
      (F := fun k ↦ e ∘ u (ψ k)) (G := fun k ↦ ω.floerEnergyDensity
        (fun z x ↦ K (p (ψ k)) (equivRealProdCLM.symm z) x 1)
        (fun z x ↦ K (p (ψ k)) (equivRealProdCLM.symm z) x Complex.I) (u (ψ k)))
      (ENNReal.ofReal_pos.2 hδ).ne' ENNReal.ofReal_ne_top
      (fun k ↦ (measure_mono (subset_univ _)).trans (by
        rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
        exact hEl (ψ k)))
      (hwin (p := p ∘ ψ) (u := u ∘ ψ) (fun k ↦ hpC _) ha₀ (hA₀' p₀ hp₀) (fun k ↦ hu _)
        (fun k ↦ hfl _) (fun k ↦ hint _) hE0 (fun k ↦ hEl _) fun k ↦ (setIntegral_mono_set
          (s := window (max T₀ 2 + A₀) (a p₀) none) (hint _)
          (ae_restrict_of_forall_mem hS (h0 _))
          (ae_of_all _ fun _ hy ↦ hy.1)).trans
            (hE _))
  have hA0 : 0 ≤ A₀ := (abs_nonneg _).trans (hA₀' p₀ hp₀)
  rw [iUnion_window (by positivity) (by linarith [hA₀' p₀ hp₀, le_max_right T₀ 2])] at hZ hbd hconv
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
`e` and pointwise in `M`. This is the case of an output end that is not recentred in
`exists_pos_forall_tendsto_tendstoLocallyUniformlyOn_comp_subseq_off_finset_of_recentered`. -/
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
        ∀ z ∈ thricePuncturedSphereReal \ ↑Z, Tendsto (fun n ↦ u (φ n) z) atTop (𝓝 (v z)) :=
  hω.exists_pos_forall_tendsto_tendstoLocallyUniformlyOn_comp_subseq_off_finset_of_recentered hW hC
    hCW hJ hXs hXt hJt hJc hB (a := fun _ ↦ 0) continuousOn_const (fun p hp q _ ↦ hKH p hp q)
    (fun p hp w x hw ↦ by simpa using hKH p hp .inf w x (by simpa using hw)) hH hHs
    (fun p hp q _ ↦ hJe p hp q) (fun p hp s t x hs ↦ by
      rw [Prod.mk_zero_zero, add_zero]; simpa using hJe p hp .inf s t x hs) he he_inj

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
