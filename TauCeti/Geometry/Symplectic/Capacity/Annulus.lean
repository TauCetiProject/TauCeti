/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Capacity.HoferZehnder
public import TauCeti.Geometry.Symplectic.Hamiltonian.RadialTwist
public import TauCeti.Topology.Circle.Degree
public import TauCeti.Topology.Homotopy.AddCircle
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import TauCeti.Analysis.SpecialFunctions.Complex.Arg

/-!
# The `π₁`-sensitive capacity of a planar annulus is infinite

On the complex line with its standard area form (`TauCeti.stdComplexSymplecticForm`), let `A` be
the annulus `a < ‖w - p‖² < b`, `0 ≤ a`, about a point `p`. Its `π₁`-sensitive Hofer–Zehnder
capacity `c°_HZ(A)`, in which only the fast periodic orbits contractible *in `A`* are excluded
(`TauCeti.SmoothTwoForm.contractibleHZCapacity`), is infinite
(`TauCeti.contractibleHZCapacity_annulus_eq_top`). More generally `c°_HZ(U; W) = ∞` whenever `U`
contains an annulus `a < ‖w - p‖² < b`, `0 < b`, and `W` avoids `p`
(`TauCeti.contractibleHZCapacity_eq_top_of_annulus_subset`).

The admissible Hamiltonians are radial bumps `N φ(‖w - p‖²)` (`TauCeti.radialHamiltonian`), with
`φ` a smooth bump function supported in `(a, b)` and equal to `1` near the middle of the interval.
Every orbit of a radial Hamiltonian turns rigidly around the circle about `p` on which it starts
(`TauCeti.hamiltonianFlow_radialHamiltonian`). So a nonconstant periodic orbit turns a nonzero
number of times around `p`, and its loop is not null-homotopic in any set avoiding `p`
(`TauCeti.eq_of_periodic_of_nullhomotopic_radialHamiltonian`): the loop of directions of the orbit,
seen from `p`, has an explicit angle function, and a null-homotopy away from `p` would give it the
degree of a constant loop (`Circle.degree_eq_of_homotopy_div_norm`). The admissibility condition
is therefore met whatever the height `N` of the bump, and the capacity is the supremum of the
heights `N`.

This is what makes the capacity `c°_HZ(W)` of a set, in which contractibility is tested in the set
itself, fail to be monotone under inclusions: the annulus `A` lies in a disc, whose capacity is
finite by the computation of Hofer and Zehnder (Chapter 3, not formalized here), while
`c°_HZ(A) = ∞`. The capacity of a subset relative to a fixed ambient set, `c°_HZ(U; W)`, is
monotone in `U` (`TauCeti.SmoothTwoForm.contractibleHZCapacity_mono`).

## Main results

* `TauCeti.eq_of_periodic_of_nullhomotopic_radialHamiltonian`: a periodic orbit of a radial
  Hamiltonian whose loop is null-homotopic in a set avoiding the centre is constant.
* `TauCeti.contractibleHZCapacity_eq_top_of_annulus_subset`: `c°_HZ(U; W) = ∞` when `U` contains an
  annulus about `p` and `W` avoids `p`.
* `TauCeti.contractibleHZCapacity_annulus_eq_top`: the `π₁`-sensitive capacity of an annulus is
  infinite.

## References

* H. Hofer, E. Zehnder, *Symplectic Invariants and Hamiltonian Dynamics*, Birkhäuser, 1994,
  Chapter 3 (radial Hamiltonians and the capacity of the ball) and Section 4.1.
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, Definition 6.1 and the remarks after it.
-/

public section

noncomputable section

open Complex Function Set
open scoped unitInterval

namespace TauCeti

/-! ### Periodic orbits of radial Hamiltonians wind around the centre -/

/-- **Nonconstant periodic orbits of a radial Hamiltonian wind around the centre.** Let `γ` be a
`T`-periodic solution, `T > 0`, of Hamilton's equations of the radial Hamiltonian
`-G(‖w - p‖²) / 2` (`TauCeti.radialHamiltonian`) on the complex line, whose vector field is
globally Lipschitz. If the loop `ℝ / Tℤ → W` that `γ` traces is null-homotopic in a set `W` not
containing `p`, then `γ` is constant. -/
theorem eq_of_periodic_of_nullhomotopic_radialHamiltonian {G : ℝ → ℝ} {p : ℂ} {K : NNReal}
    (hX : LipschitzWith K
      (stdComplexSymplecticForm.hamiltonianVectorField (radialHamiltonian G p)))
    {γ : ℝ → ℂ} (hγ : ∀ t, HasDerivAt γ
      (stdComplexSymplecticForm.hamiltonianVectorField (radialHamiltonian G p) (γ t)) t)
    (hG : DifferentiableAt ℝ G (‖γ 0 - p‖ ^ 2)) {T : ℝ} (hT : 0 < T) (hper : Periodic γ T)
    {W : Set ℂ} (hW : p ∉ W)
    (hnull : ∃ f : C(AddCircle T, W), f.Nullhomotopic ∧ ∀ t : ℝ, (f t : ℂ) = γ t) (t : ℝ) :
    γ t = γ 0 := by
  obtain ⟨f, hf, hfγ⟩ := hnull
  set c := deriv G (‖γ 0 - p‖ ^ 2)
  have hrot (s : ℝ) : γ s = p + Complex.exp (Complex.I * ↑(s * c)) * (γ 0 - p) := by
    rw [eq_flowOfLipschitz hX hγ s, ← SymplecticForm.hamiltonianFlow_eq,
      hamiltonianFlow_radialHamiltonian hX hG]
  rcases eq_or_ne c 0 with hc | hc
  · rw [hrot t, hc]
    simp
  -- The loop of `γ` in `W`, and a homotopy in `W` from it to the constant loop.
  have hmem (s : ℝ) : γ s ∈ W := hfγ s ▸ (f s).property
  let δ : ℝ → W := fun s ↦ ⟨γ s, hmem s⟩
  have hδ : Periodic δ T := fun s ↦ Subtype.ext (hper s)
  have hδc : Continuous δ :=
    (continuous_iff_continuousAt.2 fun s ↦ (hγ s).continuousAt).subtype_mk _
  have : Fact (0 < T) := ⟨hT⟩
  obtain ⟨H⟩ := (hδ.exists_nullhomotopic_iff_loop_homotopic_refl hδc 0).1
    ⟨f, hf, fun s ↦ Subtype.ext (hfγ s)⟩
  -- Seen from `p`: the homotopy avoids `0`, and the orbit returns to `γ 0` at time `T`.
  have hne (y : W) : (y : ℂ) - p ≠ 0 := sub_ne_zero.2 fun h ↦ hW (h ▸ y.property)
  have hw : γ 0 - p ≠ 0 := hne (δ 0)
  have hclose : Circle.exp (c * T) = 1 := by
    have h : Complex.exp (Complex.I * ↑(T * c)) * (γ 0 - p) = 1 * (γ 0 - p) := by
      rw [one_mul, eq_sub_iff_add_eq', ← hrot T, ← zero_add T, hper 0]
    refine Circle.ext ?_
    rw [Circle.coe_exp, Circle.coe_one, ← mul_right_cancel₀ hw h]
    congr 1
    push_cast
    ring
  exfalso
  let F : C(I × I, ℂ) := ⟨fun st ↦ (H st : ℂ) - p,
    (continuous_subtypeVal.comp H.continuous).sub continuous_const⟩
  refine hc (mul_eq_zero.1 (Circle.eq_zero_of_homotopy_div_norm_exp (θ₀ := arg (γ 0 - p)) hclose
    F (fun st ↦ hne (H st)) (fun s ↦ ?_) (fun s ↦ ?_) (fun s ↦ ?_)) |>.resolve_right hT.ne')
  · simp only [F, ContinuousMap.coe_mk, H.apply_zero, Path.coe_toContinuousMap,
      Periodic.loop_apply, δ]
    rw [hrot (0 + s * T)]
    simp only [add_sub_cancel_left, norm_mul, norm_exp_I_mul_ofReal, one_mul, mul_div_assoc,
      ← exp_arg_mul_I hw, Circle.coe_exp, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  · simp only [F, ContinuousMap.coe_mk, H.apply_one, Path.coe_toContinuousMap, Path.refl_apply]
    rw [Circle.coe_exp]
    exact exp_arg_mul_I hw
  · simp only [F, ContinuousMap.coe_mk, H.source, H.target]

/-! ### Radial bumps and the capacity of the annulus -/

/-- The point `p + √s` lies at squared distance `s` from `p`. -/
private theorem norm_add_sqrt_sub_sq (p : ℂ) {s : ℝ} (hs : 0 ≤ s) :
    ‖p + (√s : ℂ) - p‖ ^ 2 = s := by
  simp [Real.sq_sqrt hs]

variable {a b c : ℝ} (φ : ContDiffBump c)

/-- The radial bump of height `N`, `w ↦ N φ(‖w - p‖²)`, as a radial Hamiltonian. -/
private theorem radialHamiltonian_bump (p : ℂ) (N : ℝ) :
    radialHamiltonian (fun s ↦ -(2 * N * φ s)) p = fun w ↦ N * φ (‖w - p‖ ^ 2) := by
  funext w
  rw [radialHamiltonian_apply]
  ring

/-- **Radial bumps are admissible.** For a bump function `φ` supported in `(a, b)`, `0 ≤ a`, and
`N ≥ 0`, the radial Hamiltonian `N φ(‖w - p‖²)` is `HZ°`-admissible for the annulus
`a < ‖w - p‖² < b` in every set `W` not containing `p`. -/
private theorem isContractibleHZAdmissible_radialBump (hφ : Metric.closedBall c φ.rOut ⊆ Ioo a b)
    (ha : 0 ≤ a) {N : ℝ} (hN : 0 ≤ N) {p : ℂ} {W : Set ℂ} (hW : p ∉ W) :
    stdComplexSymplecticForm.constSmooth.IsContractibleHZAdmissible W
      ((fun w ↦ ‖w - p‖ ^ 2) ⁻¹' Ioo a b) (radialHamiltonian (fun s ↦ -(2 * N * φ s)) p) := by
  have hEc : Continuous fun w : ℂ ↦ ‖w - p‖ ^ 2 := by fun_prop
  rw [Real.closedBall_eq_Icc] at hφ
  have hlo : a < c - φ.rOut := (hφ ⟨le_rfl, by linarith [φ.rOut_pos]⟩).1
  have hG (n : ℕ∞) : ContDiff ℝ n fun s ↦ -(2 * N * φ s) :=
    (contDiff_const.mul φ.contDiff).neg
  have hφ0 {s : ℝ} (hs : s ∉ Ioo (c - φ.rOut) (c + φ.rOut)) : φ s = 0 := by
    rwa [← notMem_support, φ.support_eq, Real.ball_eq_Ioo]
  have hG0 (s : ℝ) (hs : c + φ.rOut ≤ s) : -(2 * N * φ s) = 0 := by
    rw [hφ0 fun h ↦ by linarith [h.2], mul_zero, neg_zero]
  obtain ⟨K, hX⟩ := exists_lipschitzWith_hamiltonianVectorField_radialHamiltonian (hG 2) hG0 p
  have hK : tsupport (radialHamiltonian (fun s ↦ -(2 * N * φ s)) p) ⊆
      (fun w ↦ ‖w - p‖ ^ 2) ⁻¹' Icc (c - φ.rOut) (c + φ.rOut) := by
    rw [radialHamiltonian_bump]
    exact tsupport_mul_subset_right.trans ((tsupport_comp_subset_preimage φ hEc).trans
      (by rw [φ.tsupport_eq, Real.closedBall_eq_Icc]))
  refine
    { contMDiff := (contDiff_radialHamiltonian (hG ⊤) p).contMDiff
      isCompact_tsupport := (hasCompactSupport_radialHamiltonian hG0 p).isCompact
      tsupport_subset_interior := hK.trans <| by
        rw [(isOpen_Ioo.preimage hEc).interior_eq]
        exact preimage_mono hφ
      tsupport_subset_interior_manifold := by
        rw [ModelWithCorners.interior_eq_univ]
        exact subset_univ _
      nonneg := fun _ ↦ by rw [radialHamiltonian_bump]; exact mul_nonneg hN φ.nonneg
      exists_isOpen_eqOn_zero := ⟨(fun w ↦ ‖w - p‖ ^ 2) ⁻¹' Ioo a (c - φ.rOut),
        isOpen_Ioo.preimage hEc, ⟨p + (√((a + (c - φ.rOut)) / 2) : ℂ), ?_⟩,
        preimage_mono (Ioo_subset_Ioo_right (by linarith [(hφ ⟨by linarith [φ.rOut_pos],
          le_rfl⟩).2, φ.rOut_pos])), fun w hw ↦ ?_⟩
      exists_isOpen_isMaxOn := ⟨(fun w ↦ ‖w - p‖ ^ 2) ⁻¹' Metric.ball c φ.rIn,
        Metric.isOpen_ball.preimage hEc, ⟨p + (√c : ℂ), ?_⟩, fun w hw ↦ isMaxOn_iff.2 ?_⟩
      eq_of_isMIntegralCurve := fun T γ hT _ hγ hper hnull ↦
        eq_of_periodic_of_nullhomotopic_radialHamiltonian hX (fun t ↦ ?_)
          ((hG 1).differentiable one_ne_zero _) hT hper hW hnull }
  · rw [mem_preimage, norm_add_sqrt_sub_sq p (by linarith)]
    constructor <;> linarith
  · simp only [radialHamiltonian_bump, Pi.zero_apply]
    rw [hφ0 fun h ↦ by linarith [h.1, hw.2], mul_zero]
  · rw [mem_preimage, norm_add_sqrt_sub_sq p (by linarith [φ.rOut_pos])]
    exact Metric.mem_ball_self φ.rIn_pos
  · intro v _
    simp only [radialHamiltonian_bump]
    rw [φ.one_of_mem_closedBall (Metric.ball_subset_closedBall hw), mul_one]
    exact mul_le_of_le_one_right hN φ.le_one
  · -- An integral curve of the Hamiltonian vector field solves Hamilton's equations.
    have h := hγ t
    rw [SymplecticForm.hamiltonianVectorField_constSmooth] at h
    exact hasDerivAt_iff_hasFDerivAt.2 (hasMFDerivAt_iff_hasFDerivAt.1 h)

/-- The maximum of the radial bump of height `N ≥ 0` is `N`, when the centre of `φ` is
nonnegative. -/
private theorem iSup_radialHamiltonian_bump (hc : 0 ≤ c) (p : ℂ) {N : ℝ} (hN : 0 ≤ N) :
    ⨆ w, radialHamiltonian (fun s ↦ -(2 * N * φ s)) p w = N := by
  simp only [radialHamiltonian_bump]
  refine ciSup_eq_of_forall_le_of_forall_lt_exists_gt
    (fun _ ↦ mul_le_of_le_one_right hN φ.le_one) fun w hw ↦ ⟨p + (√c : ℂ), ?_⟩
  rw [norm_add_sqrt_sub_sq p hc,
    φ.one_of_mem_closedBall (Metric.mem_closedBall_self φ.rIn_pos.le), mul_one]
  exact hw

/-- **A set containing an annulus has infinite `π₁`-sensitive capacity away from its centre.**
On the complex line with its standard area form, if `U` contains the annulus
`a < ‖w - p‖² < b`, with `0 < b`, and contractibility is tested in a set `W` not containing `p`,
then `c°_HZ(U; W) = ∞`. -/
theorem contractibleHZCapacity_eq_top_of_annulus_subset {p : ℂ} (hab : a < b) (hb : 0 < b)
    {W U : Set ℂ} (hW : p ∉ W) (hU : (fun w ↦ ‖w - p‖ ^ 2) ⁻¹' Ioo a b ⊆ U) :
    stdComplexSymplecticForm.constSmooth.contractibleHZCapacity W U = ⊤ := by
  set a' := max a 0
  have hab' : a' < b := max_lt hab hb
  let φ : ContDiffBump ((a' + b) / 2) :=
    ⟨(b - a') / 8, (b - a') / 4, by linarith, by linarith⟩
  have hφ : Metric.closedBall ((a' + b) / 2) φ.rOut ⊆ Ioo a' b := by
    rw [Real.closedBall_eq_Icc]
    exact Icc_subset_Ioo (by simp only [φ]; linarith) (by simp only [φ]; linarith)
  have hU' : (fun w ↦ ‖w - p‖ ^ 2) ⁻¹' Ioo a' b ⊆ U :=
    (preimage_mono (Ioo_subset_Ioo_left (le_max_left a 0))).trans hU
  refine ENNReal.eq_top_of_forall_nnreal_le fun N ↦ ?_
  have hF := (isContractibleHZAdmissible_radialBump φ hφ (le_max_right a 0) N.coe_nonneg
    hW).mono subset_rfl hU'
  rw [← ENNReal.ofReal_coe_nnreal,
    ← iSup_radialHamiltonian_bump φ (by positivity) p N.coe_nonneg]
  exact hF.ofReal_iSup_le_contractibleHZCapacity

/-- **The `π₁`-sensitive capacity of an annulus is infinite.** On the complex line with its
standard area form, the annulus `A = {a < ‖w - p‖² < b}`, `0 ≤ a < b`, has `c°_HZ(A) = ∞`. -/
theorem contractibleHZCapacity_annulus_eq_top {p : ℂ} (ha : 0 ≤ a) (hab : a < b) :
    stdComplexSymplecticForm.constSmooth.contractibleHZCapacity
      ((fun w ↦ ‖w - p‖ ^ 2) ⁻¹' Ioo a b) ((fun w ↦ ‖w - p‖ ^ 2) ⁻¹' Ioo a b) = ⊤ :=
  contractibleHZCapacity_eq_top_of_annulus_subset hab (ha.trans_lt hab)
    (fun h ↦ by simp only [mem_preimage, sub_self, norm_zero] at h; linarith [h.1]) subset_rfl

end TauCeti
