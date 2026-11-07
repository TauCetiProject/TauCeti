/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.ComparisonFamily
public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.Basic
public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.End.Curvature
import TauCeti.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Geometry.Manifold.Algebra.Monoid
import Mathlib.Geometry.Manifold.Algebra.SMul
import Mathlib.Geometry.Manifold.ContMDiff.Constructions

/-!
# Hamiltonian data on the capped pair of pants

The comparison between the pair-of-pants product and the quantum product attaches a
Piunikhin–Salamon–Schwarz (PSS) plane to each of the three ends of a pair of pants. The result is
a sphere with three poles, which in the coordinate `w` of `ℂ` are `0`, `1` and `∞`, the punctures
of the pair of pants `S = ℂ ∖ {0, 1}`. On the end `q`, in its cylinder coordinates `(s, t)` and
with signed longitudinal coordinate `σ = ±s`, the perturbation datum is the product datum
`β(σ - 1) H_q(t) dt` up to the neck, then, for `L ≥ 0`, `H_q(t) dt` along a neck of length `L`,
and then it is switched off again towards the pole by the datum `β(L + 3 - σ) H_q(t) dt` of a PSS
plane. Here `β` is the smooth transition from `0` on `(-∞, 0]` to `1` on `[1, ∞)`. For `L < 0`
the two transitions overlap and there is no neck.

This file constructs these data, scaled by a factor `a`, as
`TauCeti.Floer.cappedPerturbation a L H`, with the end profile
`TauCeti.Floer.cappedEndProfile L σ = β(σ - 1) β(L + 3 - σ)`, and the one-parameter family

`K_R = cappedPerturbation (ρ R) (L R) H`

(`TauCeti.Floer.cappedComparisonPerturbation`) for the cutoff `ρ = TauCeti.comparisonCutoff`
and the neck length `L = TauCeti.comparisonNeckLength` of `TauCeti.Floer.cutoffNeckFamily`, which
is the single-neck model of the same deformation.

* The datum vanishes outside the compact truncation `S_{L + 3}` of the pair of pants
  (`TauCeti.Floer.cappedPerturbation_eq_zero_of_notMem_truncation`), hence near the three poles
  (`TauCeti.Floer.eventually_cappedPerturbation_eq_zero_of_eq_zero_or_eq_one`,
  `TauCeti.Floer.eventually_cocompact_cappedPerturbation_eq_zero`), so it extends by zero across
  the three poles of the capped sphere.
* It is smooth on `ℂ × M`, jointly with the parameters `a` and `L`
  (`TauCeti.Floer.contMDiff_cappedPerturbation`), and so are its components in the real
  coordinates of `ℂ` (`TauCeti.Floer.contMDiff_cappedPerturbation_apply`,
  `TauCeti.Floer.contDiff_cappedPerturbation_apply`); the family `K_R` is smooth in `R`
  (`TauCeti.Floer.contMDiff_cappedComparisonPerturbation`).
* On the part `±s > 0` of the end `q` it pulls back to `a β(σ - 1) β(L + 3 - σ) H_q(t) dt`
  (`TauCeti.Floer.cappedPerturbation_cylindricalEndLift_of_pos`). For `L ≥ 0` it is
  `a H_q(t) dt` on the neck `2 ≤ σ ≤ L + 2`, and `a` times the pair-of-pants datum
  `TauCeti.Floer.pairOfPantsPerturbation` on the truncation `S_{L + 2}`
  (`TauCeti.Floer.cappedPerturbation_eq_smul_pairOfPantsPerturbation`). Beyond the neck it is the
  datum for `L = 0` translated by `L` along the end
  (`TauCeti.Floer.cappedPerturbation_cylindricalEndLift_add_endSign_mul`), so the PSS plane pieces
  do not depend on the neck length.
* For `R = 0` the datum vanishes, which is the unperturbed problem on the three-pole sphere
  (`TauCeti.Floer.cappedComparisonPerturbation_zero`). It is constant, equal to the datum with
  `a = 1` and `L = 0`, for `2/3 ≤ R ≤ 3/2`
  (`TauCeti.Floer.cappedComparisonPerturbation_of_mem_Icc`), and for `R ≥ 2` it has necks of
  length `R - 1` (`TauCeti.Floer.cappedComparisonPerturbation_of_two_le`).
* For a symplectic vector space target and `|H_q| ≤ B_q`, the integrated curvature of the datum
  along any map is at most `2 |a| (B₀ + B₁ + B_∞)`, independently of `L`
  (`TauCeti.SymplecticForm.lintegral_enorm_hamiltonianCurvature_cappedPerturbation_le`). Along the
  family `K_R`, `R ≥ 0`, it is therefore at most `2 (B₀ + B₁ + B_∞)`
  (`TauCeti.SymplecticForm.lintegral_enorm_hamiltonianCurvature_cappedComparisonPerturbation_le`).
  Each end contributes at most `2 |a| B_q`: the two transition collars each contribute `|a| B_q`,
  and the curvature vanishes along the neck, however long it is.

Almost complex structures, manifold targets for the curvature bound and the moduli spaces of the
comparison are not treated here.

## References

* S. Piunikhin, D. Salamon and M. Schwarz, *Symplectic Floer–Donaldson theory and quantum
  cohomology*, in *Contact and symplectic geometry*, Publ. Newton Inst. 8 (1996), 171–200, on
  the comparison of the pair-of-pants product with the quantum product.
* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, Section 8.1, on the
  curvature of Hamiltonian perturbations and the resulting energy bounds, and Section 12.1, on
  the PSS isomorphism.
-/

public noncomputable section

open Set Real Function Filter MeasureTheory Manifold Topology
open TauCeti.ThricePuncturedSphere TauCeti.ThricePuncturedSphere.Puncture

namespace TauCeti.Floer

/-! ### The profile on an end -/

/-- The profile of the capped perturbation along an end with neck length `L`, as a function of
the signed longitudinal coordinate `σ = ±s`. For `L ≥ 0` it rises from `0` to `1` on `[1, 2]`,
equals `1` on the neck `[2, L + 2]`, and falls back to `0` on `[L + 2, L + 3]`. For `L < 0` the
two transitions overlap, and the profile has no neck. -/
def cappedEndProfile (L σ : ℝ) : ℝ :=
  smoothTransition (σ - 1) * smoothTransition (L + 3 - σ)

theorem cappedEndProfile_def (L σ : ℝ) :
    cappedEndProfile L σ = smoothTransition (σ - 1) * smoothTransition (L + 3 - σ) :=
  (rfl)

variable {L σ : ℝ}

theorem cappedEndProfile_of_le_one (hσ : σ ≤ 1) : cappedEndProfile L σ = 0 := by
  rw [cappedEndProfile_def, smoothTransition.zero_of_nonpos (by linarith), zero_mul]

theorem cappedEndProfile_of_le (hσ : σ ≤ L + 2) :
    cappedEndProfile L σ = smoothTransition (σ - 1) := by
  rw [cappedEndProfile_def, smoothTransition.one_of_one_le (x := L + 3 - σ) (by linarith),
    mul_one]

theorem cappedEndProfile_of_two_le (hσ : 2 ≤ σ) :
    cappedEndProfile L σ = smoothTransition (L + 3 - σ) := by
  rw [cappedEndProfile_def, smoothTransition.one_of_one_le (by linarith), one_mul]

theorem cappedEndProfile_of_ge (hσ : L + 3 ≤ σ) : cappedEndProfile L σ = 0 := by
  rw [cappedEndProfile_def, smoothTransition.zero_of_nonpos (x := L + 3 - σ) (by linarith),
    mul_zero]

/-- The profile is `1` along the neck. -/
theorem cappedEndProfile_of_mem_Icc (hσ : σ ∈ Icc 2 (L + 2)) : cappedEndProfile L σ = 1 := by
  rw [cappedEndProfile_of_two_le hσ.1,
    smoothTransition.one_of_one_le (by linarith [hσ.2])]

/-- The profile vanishes where `|σ| ≥ |L| + 3`. -/
theorem cappedEndProfile_of_le_abs (hσ : |L| + 3 ≤ |σ|) : cappedEndProfile L σ = 0 := by
  rcases le_total 0 σ with h | h
  · rw [abs_of_nonneg h] at hσ
    exact cappedEndProfile_of_ge (by linarith [le_abs_self L])
  · rw [abs_of_nonpos h] at hσ
    exact cappedEndProfile_of_le_one (by linarith [abs_nonneg L])

theorem one_lt_and_lt_of_cappedEndProfile_ne_zero (h : cappedEndProfile L σ ≠ 0) :
    1 < σ ∧ σ < L + 3 :=
  ⟨lt_of_not_ge fun h' ↦ h (cappedEndProfile_of_le_one h'),
    lt_of_not_ge fun h' ↦ h (cappedEndProfile_of_ge h')⟩

/-- Beyond the neck, the profile with neck length `L ≥ 0` is the profile with neck length `0`
translated by `L`. -/
theorem cappedEndProfile_add_eq_cappedEndProfile_zero (hL : 0 ≤ L) (hσ : 2 ≤ σ) :
    cappedEndProfile L (σ + L) = cappedEndProfile 0 σ := by
  rw [cappedEndProfile_of_two_le (by linarith), cappedEndProfile_of_two_le hσ]
  ring_nf

theorem contDiff_cappedEndProfile {n : ℕ∞} : ContDiff ℝ n (uncurry cappedEndProfile) := by
  have h : uncurry cappedEndProfile =
      fun p : ℝ × ℝ ↦ smoothTransition (p.2 - 1) * smoothTransition (p.1 + 3 - p.2) :=
    funext fun p ↦ cappedEndProfile_def p.1 p.2
  rw [h]
  exact (smoothTransition.contDiff.comp (contDiff_snd.sub contDiff_const)).mul
    (smoothTransition.contDiff.comp ((contDiff_fst.add contDiff_const).sub contDiff_snd))

theorem hasDerivAt_cappedEndProfile (L σ : ℝ) :
    HasDerivAt (cappedEndProfile L)
      (deriv smoothTransition (σ - 1) * smoothTransition (L + 3 - σ) -
        smoothTransition (σ - 1) * deriv smoothTransition (L + 3 - σ)) σ := by
  have hd (x : ℝ) : HasDerivAt smoothTransition (deriv smoothTransition x) x :=
    ((smoothTransition.contDiff (n := 1)).differentiable one_ne_zero x).hasDerivAt
  have h₁ := (hd (σ - 1)).comp σ ((hasDerivAt_id' σ).sub_const 1)
  have h₂ := (hd (L + 3 - σ)).comp σ ((hasDerivAt_id' σ).const_sub (L + 3))
  refine (h₁.mul h₂).congr_deriv ?_
  simp only [Function.comp_apply]
  ring

/-- The slope of the profile is bounded by the slopes of its two transitions. -/
theorem abs_deriv_cappedEndProfile_le (L σ : ℝ) :
    |deriv (cappedEndProfile L) σ| ≤
      deriv smoothTransition (σ - 1) + deriv smoothTransition (L + 3 - σ) := by
  have h₁ : 0 ≤ deriv smoothTransition (σ - 1) := smoothTransition.monotone.deriv_nonneg
  have h₂ : 0 ≤ deriv smoothTransition (L + 3 - σ) := smoothTransition.monotone.deriv_nonneg
  rw [(hasDerivAt_cappedEndProfile L σ).deriv]
  refine (abs_sub _ _).trans (add_le_add ?_ ?_)
  · rw [abs_mul, abs_of_nonneg h₁, abs_of_nonneg (smoothTransition.nonneg _)]
    exact mul_le_of_le_one_right h₁ (smoothTransition.le_one _)
  · rw [abs_mul, abs_of_nonneg h₂, abs_of_nonneg (smoothTransition.nonneg _)]
    exact mul_le_of_le_one_left h₂ (smoothTransition.le_one _)

/-! ### The capped perturbation -/

variable {M : Type*}

/-- The Hamiltonian perturbation one-form on the three-pole sphere obtained by capping the three
ends of the pair of pants with PSS planes along necks of length `L ≥ 0`, scaled by `a`. At
`w ∈ ℂ` and `x ∈ M` it is `∑ q, a P_L(±s_q(w)) H_q(t_q(w), x) dt_q`, where `(s_q, t_q)` are the
coordinates of the end `q` and `P_L = TauCeti.Floer.cappedEndProfile L`. The definition makes
sense for every `L`, but for `L < 0` the profile has no neck. -/
def cappedPerturbation (a L : ℝ) (H : Puncture → ℝ → M → ℝ) (w : ℂ) (x : M) : ℂ →L[ℝ] ℝ :=
  ∑ q, (a * cappedEndProfile L (q.endSign * (q.endCoord w).re) * H q (q.endCoord w).im x) •
    q.endAngularForm w

theorem cappedPerturbation_def (a L : ℝ) (H : Puncture → ℝ → M → ℝ) (w : ℂ) (x : M) :
    cappedPerturbation a L H w x =
      ∑ q, (a * cappedEndProfile L (q.endSign * (q.endCoord w).re) * H q (q.endCoord w).im x) •
        q.endAngularForm w :=
  (rfl)

variable {H : Puncture → ℝ → M → ℝ} {a : ℝ}

/-- With the scaling factor `0` the datum vanishes. -/
@[simp]
theorem cappedPerturbation_zero_left (L : ℝ) (H : Puncture → ℝ → M → ℝ) :
    cappedPerturbation 0 L H = 0 := by
  funext w x
  simp [cappedPerturbation_def]

/-- Where the datum is nonzero, some end has signed longitudinal coordinate in `(1, L + 3)`. -/
theorem exists_one_lt_and_lt_of_cappedPerturbation_ne_zero {w : ℂ} {x : M}
    (h : cappedPerturbation a L H w x ≠ 0) :
    ∃ q : Puncture, 1 < q.endSign * (q.endCoord w).re ∧ q.endSign * (q.endCoord w).re < L + 3 := by
  obtain ⟨q, -, hq⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  refine ⟨q, one_lt_and_lt_of_cappedEndProfile_ne_zero fun h' ↦ hq ?_⟩
  simp [h']

/-- **The datum is supported in a truncation.** It vanishes outside the compact truncation
`S_{L + 3}` of the pair of pants, in particular at the punctures `0` and `1`. -/
theorem cappedPerturbation_eq_zero_of_notMem_truncation {w : ℂ} (hw : w ∉ truncation (L + 3))
    (x : M) : cappedPerturbation a L H w x = 0 := by
  by_contra h
  obtain ⟨q, h₁, h₂⟩ := exists_one_lt_and_lt_of_cappedPerturbation_ne_zero h
  obtain ⟨hw₀, hw₁⟩ := q.ne_zero_and_ne_one_of_endSign_mul_re_endCoord_pos (by linarith)
  refine hw (mem_truncation.2 ⟨hw₀, hw₁, fun r ↦ ?_⟩)
  by_cases hr : q = r
  · exact hr ▸ h₂.le
  · linarith [endSign_mul_re_endCoord_nonpos hr (w := w) (by linarith)]

theorem support_cappedPerturbation_subset (x : M) :
    support (fun w ↦ cappedPerturbation a L H w x) ⊆ truncation (L + 3) := fun _ hw ↦
  by_contra fun h ↦ hw (cappedPerturbation_eq_zero_of_notMem_truncation h x)

theorem hasCompactSupport_cappedPerturbation (x : M) :
    HasCompactSupport (fun w ↦ cappedPerturbation a L H w x) :=
  HasCompactSupport.of_support_subset_isCompact (isCompact_truncation _)
    (support_cappedPerturbation_subset x)

/-- Along any map `u` of the plane chart, a component `K(v)` of the capped perturbation has compact
support: it vanishes outside the truncation `S_{L + 3}`. -/
theorem hasCompactSupport_cappedPerturbation_apply (a L : ℝ) (u : ℝ × ℝ → M) (v : ℂ) :
    HasCompactSupport fun z ↦ cappedPerturbation a L H (Complex.equivRealProdCLM.symm z) (u z) v :=
  HasCompactSupport.of_support_subset_isCompact
    (Complex.equivRealProdCLM.symm.toHomeomorph.isCompact_preimage.2 (isCompact_truncation (L + 3)))
    fun z hz ↦ by_contra fun h ↦ hz <| by
      have h' : Complex.equivRealProdCLM.symm z ∉ truncation (L + 3) := h
      dsimp only
      rw [cappedPerturbation_eq_zero_of_notMem_truncation h' (u z)]
      simp

/-- **The datum vanishes near the poles `0` and `1`.** -/
theorem eventually_cappedPerturbation_eq_zero_of_eq_zero_or_eq_one {c : ℂ} (hc : c = 0 ∨ c = 1) :
    ∀ᶠ w in 𝓝 c, ∀ x : M, cappedPerturbation a L H w x = 0 := by
  have hT : c ∉ truncation (L + 3) := by
    intro h
    obtain ⟨h₀, h₁, -⟩ := mem_truncation.1 h
    rcases hc with rfl | rfl
    exacts [h₀ rfl, h₁ rfl]
  filter_upwards [(isCompact_truncation (L + 3)).isClosed.isOpen_compl.mem_nhds hT] with w hw x
  exact cappedPerturbation_eq_zero_of_notMem_truncation hw x

/-- **The datum vanishes near the pole `∞`.** -/
theorem eventually_cocompact_cappedPerturbation_eq_zero :
    ∀ᶠ w in cocompact ℂ, ∀ x : M, cappedPerturbation a L H w x = 0 := by
  filter_upwards [(isCompact_truncation (L + 3)).compl_mem_cocompact] with w hw x
  exact cappedPerturbation_eq_zero_of_notMem_truncation hw x

/-- **The datum on an end.** On the part `±s > 0` of the end `q`, the pullback of the datum along
the end lift `φ` is `a P_L(±s) H_q(t) dt`: it sends a tangent vector `v` of the cylinder to
`Im v · a P_L(±s) H_q(t)`. -/
theorem cappedPerturbation_cylindricalEndLift_of_pos {q : Puncture}
    (hH : Function.Periodic (H q) 1) {z : ℂ} (hz : 0 < q.endSign * z.re) (x : M) (v : ℂ) :
    cappedPerturbation a L H (q.cylindricalEndLift z) x (deriv q.cylindricalEndLift z * v) =
      v.im * (a * cappedEndProfile L (q.endSign * z.re) * H q z.im x) := by
  obtain ⟨k, hk⟩ := q.exists_endCoord_cylindricalEndLift z
  have hre : (q.endCoord (q.cylindricalEndLift z)).re = z.re := by simp [hk]
  rw [cappedPerturbation_def, Finset.sum_eq_single q]
  · have him : (q.endCoord (q.cylindricalEndLift z)).im = z.im + k := by simp [hk]
    have hp : H q (z.im + k) x = H q z.im x := by
      simpa using congrFun (hH.int_mul k z.im) x
    rw [smul_apply, endAngularForm_cylindricalEndLift, hre, him, hp,
      smul_eq_mul, mul_comm]
  · -- The profiles of the other ends vanish, since distinct ends are disjoint.
    intro r _ hr
    have h := endSign_mul_re_endCoord_nonpos (Ne.symm hr) (w := q.cylindricalEndLift z)
      (by rwa [hre])
    simp [cappedEndProfile_of_le_one (h.trans zero_le_one)]
  · simp

/-- **The neck.** On the part `2 ≤ ±s ≤ L + 2` of the end `q`, the pullback of the datum is
`a H_q(t) dt`. -/
theorem cappedPerturbation_cylindricalEndLift_of_mem_Icc {q : Puncture}
    (hH : Function.Periodic (H q) 1) {z : ℂ} (hz : q.endSign * z.re ∈ Icc 2 (L + 2)) (x : M)
    (v : ℂ) :
    cappedPerturbation a L H (q.cylindricalEndLift z) x (deriv q.cylindricalEndLift z * v) =
      v.im * (a * H q z.im x) := by
  rw [cappedPerturbation_cylindricalEndLift_of_pos hH (by linarith [hz.1]),
    cappedEndProfile_of_mem_Icc hz, mul_one]

/-- **The PSS plane pieces do not depend on the neck length.** Beyond the neck of length
`L ≥ 0`, the pullback of the datum along the end `q` is the datum for `L = 0` translated by `L`
along the end. -/
theorem cappedPerturbation_cylindricalEndLift_add_endSign_mul {q : Puncture}
    (hH : Function.Periodic (H q) 1) (hL : 0 ≤ L) {z : ℂ} (hz : 2 ≤ q.endSign * z.re) (x : M)
    (v : ℂ) :
    cappedPerturbation a L H (q.cylindricalEndLift (z + ↑(q.endSign * L)) ) x
        (deriv q.cylindricalEndLift (z + ↑(q.endSign * L)) * v) =
      cappedPerturbation a 0 H (q.cylindricalEndLift z) x (deriv q.cylindricalEndLift z * v) := by
  have hs : q.endSign * q.endSign = 1 := by
    rcases q.endSign_eq_one_or_eq_neg_one with h | h <;> rw [h] <;> norm_num
  have hre : q.endSign * (z + ↑(q.endSign * L)).re = q.endSign * z.re + L := by
    rw [Complex.add_re, Complex.ofReal_re, mul_add, ← mul_assoc, hs, one_mul]
  rw [cappedPerturbation_cylindricalEndLift_of_pos hH (by rw [hre]; linarith),
    cappedPerturbation_cylindricalEndLift_of_pos hH (by linarith), hre,
    cappedEndProfile_add_eq_cappedEndProfile_zero hL hz, Complex.add_im, Complex.ofReal_im,
    add_zero]

/-- **The datum is the pair-of-pants datum up to the necks.** At points where the signed
longitudinal coordinate of every end is at most `L + 2`, such as the points of the truncation
`S_{L + 2}`, the datum is `a` times the pair-of-pants perturbation. -/
theorem cappedPerturbation_eq_smul_pairOfPantsPerturbation {w : ℂ}
    (h : ∀ q : Puncture, q.endSign * (q.endCoord w).re ≤ L + 2) (x : M) :
    cappedPerturbation a L H w x = a • pairOfPantsPerturbation H w x := by
  rw [cappedPerturbation_def, pairOfPantsPerturbation_def, Finset.smul_sum]
  refine Finset.sum_congr rfl fun q _ ↦ ?_
  rw [cappedEndProfile_of_le (h q), smul_smul, mul_assoc]

/-- The datum vanishes at every point where the signed longitudinal coordinate of every end is at
most `1`. -/
theorem cappedPerturbation_eq_zero_of_forall_le {w : ℂ}
    (h : ∀ q : Puncture, q.endSign * (q.endCoord w).re ≤ 1) (x : M) :
    cappedPerturbation a L H w x = 0 := by
  rw [cappedPerturbation_def]
  refine Finset.sum_eq_zero fun q _ ↦ ?_
  rw [cappedEndProfile_of_le_one (h q), mul_zero, zero_mul, zero_smul]

/-! ### Smoothness -/

section Smooth

variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace G]
  {I : ModelWithCorners ℝ E G} [TopologicalSpace M] [ChartedSpace G M]

/-- Near the center of the end `q`, the term of the end `q` in the capped perturbation vanishes,
locally uniformly in the neck length. -/
private theorem eventually_cappedEndProfile_eq_zero (q : Puncture) (L₀ : ℝ) :
    ∀ᶠ p : ℂ × ℝ in 𝓝 (q.endCenter, L₀),
      cappedEndProfile p.2 (q.endSign * (q.endCoord p.1).re) = 0 := by
  have hL : ∀ᶠ p : ℂ × ℝ in 𝓝 (q.endCenter, L₀), |p.2| < |L₀| + 1 :=
    (continuous_abs.comp continuous_snd).continuousAt.eventually
      (gt_mem_nhds (by simp))
  -- Near the center of the end, its longitudinal coordinate is large.
  have hc : ∀ᶠ w in 𝓝 q.endCenter, w = q.endCenter ∨ |L₀| + 4 ≤ (q.endCoord w).re :=
    (eventually_nhdsWithin_iff.1 (q.tendsto_re_endCoord_nhdsNE.eventually_ge_atTop _)).mono
      fun _ hw ↦ or_iff_not_imp_left.2 hw
  filter_upwards [hL, hc.prod_inl_nhds L₀] with p hp hw
  rcases hw with hw | hw
  · rw [hw, re_endCoord_endCenter, mul_zero]
    exact cappedEndProfile_of_le_one zero_le_one
  · refine cappedEndProfile_of_le_abs ?_
    rw [abs_mul, abs_endSign, one_mul]
    linarith [le_abs_self (q.endCoord p.1).re]

/-- **The datum is smooth.** For Hamiltonians of period one which are `C^n` on `ℝ × M`, the datum
`cappedPerturbation a L H w x` is `C^n` jointly in the scaling factor `a`, the neck length `L`, the
point `w ∈ ℂ`, including the poles `0` and `1`, and the target point `x`. -/
theorem contMDiff_cappedPerturbation {n : ℕ∞} (hH : ∀ q, Function.Periodic (H q) 1)
    (hHs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) n (Function.uncurry (H q))) :
    ContMDiff (𝓘(ℝ, ℂ).prod (𝓘(ℝ, ℝ × ℝ).prod I)) 𝓘(ℝ, ℂ →L[ℝ] ℝ) n
      (fun p : ℂ × ((ℝ × ℝ) × M) ↦ cappedPerturbation p.2.1.1 p.2.1.2 H p.1 p.2.2) := by
  rintro ⟨w, ⟨a, L⟩, x⟩
  simp only [cappedPerturbation_def]
  refine contMDiffAt_finsetSum fun q _ ↦ ?_
  -- The parameters `a` and `L` as functions on the total space.
  have hpar : ContMDiffAt (𝓘(ℝ, ℂ).prod (𝓘(ℝ, ℝ × ℝ).prod I)) 𝓘(ℝ, ℝ × ℝ) n
      (fun p : ℂ × ((ℝ × ℝ) × M) ↦ p.2.1) (w, (a, L), x) :=
    contMDiffAt_fst.comp _ contMDiffAt_snd
  by_cases hw : w = q.endCenter
  · -- Near the center of the end, its profile vanishes identically.
    subst hw
    refine contMDiffAt_const (c := (0 : ℂ →L[ℝ] ℝ)).congr_of_eventuallyEq ?_
    have hproj : Tendsto (fun p : ℂ × ((ℝ × ℝ) × M) ↦ (p.1, p.2.1.2))
        (𝓝 (q.endCenter, (a, L), x)) (𝓝 (q.endCenter, L)) :=
      (continuous_fst.prodMk (continuous_snd.comp (continuous_fst.comp continuous_snd))).tendsto
        _
    filter_upwards [hproj.eventually (eventually_cappedEndProfile_eq_zero q L)] with p hp
    simp [hp]
  -- Away from the center, every factor of the term of the end `q` is smooth.
  have hσ : ContMDiffAt (𝓘(ℝ, ℂ).prod (𝓘(ℝ, ℝ × ℝ).prod I)) 𝓘(ℝ, ℝ) n
      (fun p : ℂ × ((ℝ × ℝ) × M) ↦ q.endSign * (q.endCoord p.1).re) (w, (a, L), x) :=
    ContMDiffAt.comp (I' := 𝓘(ℝ, ℂ)) (g := fun w ↦ q.endSign * (q.endCoord w).re) _
      (contDiffAt_const.mul (q.contDiffAt_re_endCoord hw)).contMDiffAt contMDiffAt_fst
  -- The scalar factor `a P_L(σ)`, a smooth function of `σ`, `a` and `L`.
  have hF : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ × ℝ)) 𝓘(ℝ, ℝ) n
      (fun r : ℝ × (ℝ × ℝ) ↦ r.2.1 * cappedEndProfile r.2.2 r.1) := by
    have h : ContMDiff 𝓘(ℝ, ℝ × (ℝ × ℝ)) 𝓘(ℝ, ℝ) n
        (fun r : ℝ × (ℝ × ℝ) ↦ r.2.1 * cappedEndProfile r.2.2 r.1) :=
      ((contDiff_fst.comp contDiff_snd).mul (contDiff_cappedEndProfile.comp
        ((contDiff_snd.comp contDiff_snd).prodMk contDiff_fst))).contMDiff
    rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod] at h
    exact h
  have hP : ContMDiffAt (𝓘(ℝ, ℂ).prod (𝓘(ℝ, ℝ × ℝ).prod I)) 𝓘(ℝ, ℝ) n
      (fun p : ℂ × ((ℝ × ℝ) × M) ↦
        p.2.1.1 * cappedEndProfile p.2.1.2 (q.endSign * (q.endCoord p.1).re)) (w, (a, L), x) :=
    hF.contMDiffAt.comp _ (hσ.prodMk hpar)
  have hHq : ContMDiffAt (𝓘(ℝ, ℂ).prod (𝓘(ℝ, ℝ × ℝ).prod I)) 𝓘(ℝ, ℝ) n
      (fun p : ℂ × ((ℝ × ℝ) × M) ↦ H q (q.endCoord p.1).im p.2.2) (w, (a, L), x) :=
    q.contMDiffAt_comp_im_endCoord (f := fun t (p : (ℝ × ℝ) × M) ↦ H q t p.2)
      (fun t ↦ funext fun p ↦ congrFun (hH q t) p.2)
      ((hHs q).comp (contMDiff_fst.prodMk (contMDiff_snd.comp contMDiff_snd))) hw ((a, L), x)
  have hdt : ContMDiffAt (𝓘(ℝ, ℂ).prod (𝓘(ℝ, ℝ × ℝ).prod I)) 𝓘(ℝ, ℂ →L[ℝ] ℝ) n
      (fun p : ℂ × ((ℝ × ℝ) × M) ↦ q.endAngularForm p.1) (w, (a, L), x) :=
    ContMDiffAt.comp (I' := 𝓘(ℝ, ℂ)) (g := q.endAngularForm) _
      (q.contDiffAt_endAngularForm hw).contMDiffAt contMDiffAt_fst
  exact (hP.smul hHq).smul hdt

/-- A component `K(v)` of the capped perturbation, for a fixed tangent vector `v` of `ℂ`, is `C^n`
jointly in the point of the plane chart `ℝ × ℝ` and the target point. -/
theorem contMDiff_cappedPerturbation_apply {n : ℕ∞} (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) n (uncurry (H q))) (a L : ℝ) (v : ℂ) :
    ContMDiff (𝓘(ℝ, ℝ × ℝ).prod I) 𝓘(ℝ, ℝ) n
      (uncurry fun z x ↦ cappedPerturbation a L H (Complex.equivRealProdCLM.symm z) x v) := by
  have hι : ContMDiff (𝓘(ℝ, ℝ × ℝ).prod I) (𝓘(ℝ, ℂ).prod (𝓘(ℝ, ℝ × ℝ).prod I)) n
      fun p : (ℝ × ℝ) × M ↦ (Complex.equivRealProdCLM.symm p.1, ((a, L), p.2)) :=
    (Complex.equivRealProdCLM.symm.contDiff.contMDiff.comp contMDiff_fst).prodMk
      (contMDiff_const.prodMk contMDiff_snd)
  exact ((contMDiff_cappedPerturbation hH hHs).comp hι).clm_apply contMDiff_const

end Smooth

section SmoothNormed

variable [NormedAddCommGroup M] [NormedSpace ℝ M]

/-- The components of the capped perturbation are `C^n` jointly in the real coordinates of `ℂ`
and the target point, for `C^n` Hamiltonians on a vector space. -/
theorem contDiff_cappedPerturbation_apply {n : ℕ∞} (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContDiff ℝ n (uncurry (H q))) (a L : ℝ) (v : ℂ) :
    ContDiff ℝ n
      (uncurry fun z x ↦ cappedPerturbation a L H (Complex.equivRealProdCLM.symm z) x v) := by
  have hHs' (q : Puncture) : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, M)) 𝓘(ℝ, ℝ) n (uncurry (H q)) := by
    have h := (hHs q).contMDiff
    rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod] at h
    exact h
  rw [← contMDiff_iff_contDiff, modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
  exact contMDiff_cappedPerturbation_apply hH hHs' a L v

end SmoothNormed

/-! ### The comparison family -/

/-- The comparison family of Hamiltonian data on the three-pole sphere: the capped perturbation
`K_R = cappedPerturbation (ρ R) (L R) H` for the cutoff `ρ = TauCeti.comparisonCutoff` and the
neck length `L = TauCeti.comparisonNeckLength`. For `R = 0` it vanishes, it is switched on for
`0 ≤ R ≤ 2/3`, and its necks grow without bound as `R → ∞`. -/
def cappedComparisonPerturbation (H : Puncture → ℝ → M → ℝ) (R : ℝ) : ℂ → M → ℂ →L[ℝ] ℝ :=
  cappedPerturbation (comparisonCutoff R) (comparisonNeckLength R) H

theorem cappedComparisonPerturbation_def (H : Puncture → ℝ → M → ℝ) (R : ℝ) :
    cappedComparisonPerturbation H R =
      cappedPerturbation (comparisonCutoff R) (comparisonNeckLength R) H :=
  (rfl)

/-- The family starts at the zero datum, the unperturbed problem on the three-pole sphere. -/
@[simp]
theorem cappedComparisonPerturbation_zero (H : Puncture → ℝ → M → ℝ) :
    cappedComparisonPerturbation H 0 = 0 := by
  rw [cappedComparisonPerturbation_def, comparisonCutoff_zero, cappedPerturbation_zero_left]

/-- The family is constant on the collar `2/3 ≤ R ≤ 3/2`, where the datum is fully switched on
and has no necks. -/
theorem cappedComparisonPerturbation_of_mem_Icc (H : Puncture → ℝ → M → ℝ) {R : ℝ}
    (hR : R ∈ Icc (2 / 3 : ℝ) (3 / 2)) :
    cappedComparisonPerturbation H R = cappedPerturbation 1 0 H := by
  rw [cappedComparisonPerturbation_def, comparisonCutoff_of_ge hR.1,
    comparisonNeckLength_of_le hR.2]

/-- For `R ≥ 2` the datum is fully switched on and has necks of length `R - 1`. -/
theorem cappedComparisonPerturbation_of_two_le (H : Puncture → ℝ → M → ℝ) {R : ℝ} (hR : 2 ≤ R) :
    cappedComparisonPerturbation H R = cappedPerturbation 1 (R - 1) H := by
  rw [cappedComparisonPerturbation_def, comparisonCutoff_of_ge (by linarith),
    comparisonNeckLength_of_ge hR]

section Smooth

variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace G]
  {I : ModelWithCorners ℝ E G} [TopologicalSpace M] [ChartedSpace G M]

/-- **The comparison family is smooth** jointly in the family parameter `R`, the point `w ∈ ℂ`
and the target point `x`. -/
theorem contMDiff_cappedComparisonPerturbation {n : ℕ∞} (hH : ∀ q, Function.Periodic (H q) 1)
    (hHs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) n (Function.uncurry (H q))) :
    ContMDiff (𝓘(ℝ, ℂ).prod (𝓘(ℝ, ℝ).prod I)) 𝓘(ℝ, ℂ →L[ℝ] ℝ) n
      (fun p : ℂ × (ℝ × M) ↦ cappedComparisonPerturbation H p.2.1 p.1 p.2.2) := by
  have hρL : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ × ℝ) n
      fun R ↦ (comparisonCutoff R, comparisonNeckLength R) :=
    (contDiff_comparisonCutoff.prodMk contDiff_comparisonNeckLength).contMDiff
  exact (contMDiff_cappedPerturbation hH hHs).comp
    (contMDiff_fst.prodMk ((hρL.comp (contMDiff_fst.comp contMDiff_snd)).prodMk
      (contMDiff_snd.comp contMDiff_snd)))

end Smooth

end TauCeti.Floer

/-! ### The integrated curvature -/

namespace TauCeti.SymplecticForm

open Floer

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {H : Puncture → ℝ → V → ℝ}
  {a L : ℝ}

/-- The capped perturbation is `C¹` jointly in the point of `ℂ` and the target point. -/
private theorem contDiff_cappedPerturbation_prod (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContDiff ℝ 1 (uncurry (H q))) (a L : ℝ) :
    ContDiff ℝ 1 (fun p : ℂ × V ↦ cappedPerturbation a L H p.1 p.2) := by
  have hHs' : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, V)) 𝓘(ℝ, ℝ) 1 (uncurry (H q)) := fun q ↦ by
    have h := (hHs q).contMDiff
    rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod] at h
    exact h
  have hι : ContMDiff (𝓘(ℝ, ℂ).prod 𝓘(ℝ, V)) (𝓘(ℝ, ℂ).prod (𝓘(ℝ, ℝ × ℝ).prod 𝓘(ℝ, V))) 1
      fun p : ℂ × V ↦ (p.1, ((a, L), p.2)) :=
    contMDiff_fst.prodMk (contMDiff_const.prodMk contMDiff_snd)
  have h : ContMDiff 𝓘(ℝ, ℂ × V) 𝓘(ℝ, ℂ →L[ℝ] ℝ) 1
      (fun p : ℂ × V ↦ cappedPerturbation a L H p.1 p.2) := by
    rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
    exact (contMDiff_cappedPerturbation (n := 1) hH hHs').comp hι
  exact h.contDiff

/-- The curvature of the datum over the image of the strip of the end `q` is at most `2 |a| B_q`
for a bound `B_q` of the Hamiltonian of that end: each of the two transition collars contributes
at most `|a| B_q`. -/
private theorem setLIntegral_image_endChart_cappedPerturbation_le [FiniteDimensional ℝ V]
    (ω : SymplecticForm V) (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContDiff ℝ 1 (uncurry (H q))) {B : Puncture → ℝ} (hB : ∀ q t x, |H q t x| ≤ B q)
    (u : ℝ × ℝ → V) (q : Puncture) :
    ∫⁻ z in endChart q '' endStrip q, ‖ω.hamiltonianCurvature
        (fun z x ↦ cappedPerturbation a L H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ cappedPerturbation a L H (Complex.equivRealProdCLM.symm z) x Complex.I)
        z (u z)‖ₑ ≤ ENNReal.ofReal (2 * |a|) * ENNReal.ofReal (B q) := by
  have hψ (s : ℝ) : 0 ≤ deriv smoothTransition s := smoothTransition.monotone.deriv_nonneg
  -- The densities of the two transition collars, which bound the profile's derivative along `s`.
  set f₁ : ℝ → ENNReal := fun s ↦ ENNReal.ofReal (deriv smoothTransition (q.endSign * s - 1))
    with hf₁
  set f₂ : ℝ → ENNReal := fun s ↦ ENNReal.ofReal (deriv smoothTransition (L + 3 - q.endSign * s))
    with hf₂
  have hm₁ : Measurable f₁ :=
    (ENNReal.continuous_ofReal.comp
      (((smoothTransition.contDiff (n := 1)).continuous_deriv le_rfl).comp
        (by fun_prop))).measurable
  have hint : ∫⁻ s, ‖deriv (fun σ ↦ a * cappedEndProfile L σ) (q.endSign * s)‖ₑ ≤
      ENNReal.ofReal (2 * |a|) := by
    calc _ ≤ ∫⁻ s, ENNReal.ofReal |a| * (f₁ s + f₂ s) := by
          refine lintegral_mono fun s ↦ ?_
          rw [deriv_const_mul_field', enorm_mul, Real.enorm_eq_ofReal_abs a, hf₁, hf₂,
            ← ENNReal.ofReal_add (hψ _) (hψ _), Real.enorm_eq_ofReal_abs]
          gcongr
          exact abs_deriv_cappedEndProfile_le _ _
      _ = ENNReal.ofReal |a| * 2 := by
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_add_left hm₁, hf₁, hf₂,
            smoothTransition.lintegral_ofReal_deriv_mul_sub _ q.endSign_ne_zero,
            smoothTransition.lintegral_ofReal_deriv_sub_mul _ q.endSign_ne_zero, abs_endSign,
            inv_one, ENNReal.ofReal_one, one_add_one_eq_two]
      _ = _ := by
          rw [← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (abs_nonneg a), mul_comm]
  exact (ω.setLIntegral_image_endChart_enorm_hamiltonianCurvature_le
    (P := fun σ ↦ a * cappedEndProfile L σ)
    (fun _ _ _ ↦ (contDiff_cappedPerturbation_prod hH hHs a L).differentiable one_ne_zero _)
    (fun _ hz x v ↦ cappedPerturbation_cylindricalEndLift_of_pos (hH q) hz x v)
    (fun σ ↦ (hasDerivAt_cappedEndProfile L σ).differentiableAt.const_mul a)
    ((hHs q).differentiable one_ne_zero) (hB q) u).trans (by gcongr)

/-- **The integrated curvature of the capped perturbation.** Let `K` be the capped perturbation
with scaling factor `a` and neck length `L`, built from period-one `C¹` Hamiltonians `H_q` with
`|H_q| ≤ B_q`, and write its components in the global coordinate `z = s + i t` of `ℂ` as
`K_s(z) = K(z)(1)` and `K_t(z) = K(z)(i)`. Then for every map `u` into the target, the integral of
`|R_K(z, u(z))|` over the plane is at most `2 |a| (B₀ + B₁ + B_∞)`, independently of `L`. -/
theorem lintegral_enorm_hamiltonianCurvature_cappedPerturbation_le [FiniteDimensional ℝ V]
    (ω : SymplecticForm V) (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContDiff ℝ 1 (uncurry (H q))) {B : Puncture → ℝ} (hB : ∀ q t x, |H q t x| ≤ B q)
    (a L : ℝ) (u : ℝ × ℝ → V) :
    ∫⁻ z, ‖ω.hamiltonianCurvature
        (fun z x ↦ cappedPerturbation a L H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ cappedPerturbation a L H (Complex.equivRealProdCLM.symm z) x Complex.I)
        z (u z)‖ₑ ≤ ENNReal.ofReal (2 * |a|) * ∑ q, ENNReal.ofReal (B q) := by
  rw [Finset.mul_sum]
  exact (ω.lintegral_enorm_hamiltonianCurvature_le_sum_endStrip
    (fun w hw y ↦ cappedPerturbation_eq_zero_of_forall_le hw y) u).trans
    (Finset.sum_le_sum fun q _ ↦ setLIntegral_image_endChart_cappedPerturbation_le ω hH hHs hB u q)

/-- **The curvature bound is uniform over the comparison family.** For every `R ≥ 0` the
integrated curvature of `K_R` along any map is at most `2 (B₀ + B₁ + B_∞)`. -/
theorem lintegral_enorm_hamiltonianCurvature_cappedComparisonPerturbation_le
    [FiniteDimensional ℝ V] (ω : SymplecticForm V) (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContDiff ℝ 1 (uncurry (H q))) {B : Puncture → ℝ} (hB : ∀ q t x, |H q t x| ≤ B q)
    {R : ℝ} (hR : 0 ≤ R) (u : ℝ × ℝ → V) :
    ∫⁻ z, ‖ω.hamiltonianCurvature
        (fun z x ↦ cappedComparisonPerturbation H R (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ cappedComparisonPerturbation H R (Complex.equivRealProdCLM.symm z) x
          Complex.I) z (u z)‖ₑ ≤ 2 * ∑ q, ENNReal.ofReal (B q) := by
  have hρ := comparisonCutoff_mem_Icc hR
  rw [cappedComparisonPerturbation_def]
  refine (lintegral_enorm_hamiltonianCurvature_cappedPerturbation_le ω hH hHs hB _ _ u).trans
    (mul_le_mul_left ?_ _)
  rw [abs_of_nonneg hρ.1, ← ENNReal.ofReal_ofNat 2]
  exact ENNReal.ofReal_le_ofReal (by linarith [hρ.2])

/-- The integral of the curvature of `K_R`, `R ≥ 0`, along any map and over any set has absolute
value at most `2 (B₀ + B₁ + B_∞)`. This is the curvature term that an energy identity for the
comparison family would need to bound uniformly over the family. -/
theorem abs_setIntegral_hamiltonianCurvature_cappedComparisonPerturbation_le
    [FiniteDimensional ℝ V] (ω : SymplecticForm V) (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContDiff ℝ 1 (uncurry (H q))) {B : Puncture → ℝ} (hB : ∀ q t x, |H q t x| ≤ B q)
    {R : ℝ} (hR : 0 ≤ R) (u : ℝ × ℝ → V) (s : Set (ℝ × ℝ)) :
    |∫ z in s, ω.hamiltonianCurvature
        (fun z x ↦ cappedComparisonPerturbation H R (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ cappedComparisonPerturbation H R (Complex.equivRealProdCLM.symm z) x
          Complex.I) z (u z)| ≤ 2 * ∑ q, B q := by
  have hB₀ (q : Puncture) : 0 ≤ B q := (abs_nonneg _).trans (hB q 0 0)
  rw [← ENNReal.ofReal_le_ofReal_iff
      (mul_nonneg zero_le_two (Finset.sum_nonneg fun q _ ↦ hB₀ q)),
    ← Real.enorm_eq_ofReal_abs, ENNReal.ofReal_mul zero_le_two, ENNReal.ofReal_ofNat,
    ENNReal.ofReal_sum_of_nonneg fun q _ ↦ hB₀ q]
  exact (enorm_integral_le_lintegral_enorm _).trans ((setLIntegral_le_lintegral _ _).trans
    (lintegral_enorm_hamiltonianCurvature_cappedComparisonPerturbation_le ω hH hHs hB hR u))

end TauCeti.SymplecticForm
