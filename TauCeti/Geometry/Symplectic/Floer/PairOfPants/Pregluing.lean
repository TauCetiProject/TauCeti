/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.Pregluing
public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.End.Orbit

/-!
# Pre-gluing a Floer cylinder to an end of a pair of pants

A one-parameter family of Floer pairs of pants breaks, at the boundary of its compactification,
into a pair of pants and a Floer cylinder attached at one of its three ends. These breakings
are the terms of the Leibniz rule of the pair-of-pants product. Gluing reverses the breaking:
for every large gluing parameter `R` it produces a pair of pants close to the broken
configuration. Its first step is the *pre-glued map*, an approximate solution of the Floer
equation on the pair of pants `S = ℂ ∖ {0, 1}`, which this file constructs and estimates.

Let `u` be a map on `S` (in the real coordinates `ℝ × ℝ ≃ ℂ`), and fix an end `q` of `S`, read as
a positive end through its positive end chart `φ'_q` (`TauCeti.Floer.positiveEndChart`), with
positive end coordinates `(s, t)` (`TauCeti.Floer.positiveEndCoord`). Suppose that the loops of
`u ∘ φ'_q` converge to a one-periodic orbit `x` as `s → ∞`, and let `v` be a map of the cylinder,
of period one in `t`, whose loops converge to `x` as `s → -∞`. The pre-glued map
(`TauCeti.Floer.pairOfPantsPreglue`) is

`w_R = u + (1 - ρ(s - R)) (x(t) - u) + ρ(R - s) (v(s - 2R, t) - x(t))`,

with the cutoff `ρ = TauCeti.Floer.pregluingCutoff`, equal to `1` on `(-∞, -1]` and `0` on
`[1, ∞)`. It is a map on all of `S`:

* it is `u` where `s ≤ R - 1` (`TauCeti.Floer.pairOfPantsPreglue_of_le`), and near every point
  of `S` where `s < R - 1` (`TauCeti.Floer.pairOfPantsPreglue_eventuallyEq_of_lt`);
* read in the positive end chart, it is the pre-glued map
  `TauCeti.Floer.preglue x (u ∘ φ'_q) v R` of the two cylinders, translated by `R`
  (`TauCeti.Floer.pairOfPantsPreglue_comp_positiveEndChart`), so it is `v(s - 2R, t)` where
  `s ≥ R + 1`, and the end `q` of the pre-glued map is the far end of `v`;
* it is as regular as `u`, `x` and `v` (`TauCeti.Floer.contDiffOn_pairOfPantsPreglue`): the
  angular end coordinate jumps by `1` across a ray, and periodicity of `x` and `v` removes the
  jump.

**The error.** If `u` solves the Floer equation `(du - X_K)^{0,1} = 0` on `S` for a perturbation `K`
equal to `H_q(t) dt` beyond `T₀` on the end `q`, the almost complex structure is `J_q(t)` there, and
`v` is a Floer cylinder for the same data, then the Floer operator of the pre-glued map vanishes
wherever it is `u` or a translate of `v`. Where `s < R - 1` the pre-glued map has the perturbed
derivative of `u` (`TauCeti.SymplecticForm.perturbedFDeriv_pairOfPantsPreglue_of_lt`), so it solves
the Floer equation there. The rest of `S` is the image of the part `s > R - 1` of the positive end
chart, and there the Floer operator is computed in the end coordinates, which are the coordinates of
the cylindrical metric on the end. If `u ∘ φ'_q` and `v` converge to `x` in `C¹` at the exponential
rate `κ`, as finite-energy solutions at a nondegenerate orbit do, the error is `O(e^{-κR})`
uniformly on the part `s ≥ T₀` of the end
(`SymplecticForm.exists_eventually_norm_floerOperator_pairOfPantsPreglue_comp_le`, and
`SymplecticForm.exists_eventually_norm_floerOperator_pairOfPantsPreglue_comp_le_of_floer` with the
Floer equation of `u` on `S` as hypothesis). The estimate is that of
`TauCeti.Geometry.Symplectic.Floer.Pregluing` for broken Floer cylinders; the pair-of-pants
statement places it on the actual domain `S`.

The target is a symplectic vector space. The Sobolev setting, the right inverse of the linearized
operator on `S` and the Newton iteration that corrects `w_R` to a solution are not treated here.

## References

* M. Schwarz, *Cohomology operations from S¹-cobordisms in Floer homology*, PhD thesis,
  ETH Zürich (1995), on gluing Floer cylinders to the ends of a pair of pants.
* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, Chapter 10, on the
  pre-gluing construction and its error estimate.
-/

public section

open Set Function Filter ContinuousLinearMap TauCeti.ThricePuncturedSphere
  TauCeti.ThricePuncturedSphere.Puncture
open scoped Topology

namespace TauCeti

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

namespace Floer

/-- **The pre-glued pair of pants.** The map `u` on the pair of pants, with the cylinder `v`
glued to its end `q` at the orbit `x` with gluing parameter `R`: in the positive end coordinates
`(s, t)` of `q` (`TauCeti.Floer.positiveEndCoord`) it is
`u + (1 - ρ(s - R)) (x(t) - u) + ρ(R - s) (v(s - 2R, t) - x(t))` for the cutoff
`ρ = TauCeti.Floer.pregluingCutoff`. It is `u` where `s ≤ R - 1` and `v(s - 2R, t)` where
`s ≥ R + 1`. -/
noncomputable def pairOfPantsPreglue (q : Puncture) (x : ℝ → V) (u v : ℝ × ℝ → V) (R : ℝ)
    (z : ℝ × ℝ) : V :=
  u z + (1 - pregluingCutoff ((positiveEndCoord q z).1 - R)) • (x (positiveEndCoord q z).2 - u z) +
    pregluingCutoff (R - (positiveEndCoord q z).1) •
      (v (positiveEndCoord q z - (2 * R, 0)) - x (positiveEndCoord q z).2)

variable {q : Puncture} {x : ℝ → V} {u v : ℝ × ℝ → V} {R : ℝ} {z : ℝ × ℝ}

theorem pairOfPantsPreglue_apply (q : Puncture) (x : ℝ → V) (u v : ℝ × ℝ → V) (R : ℝ)
    (z : ℝ × ℝ) :
    pairOfPantsPreglue q x u v R z =
      u z + (1 - pregluingCutoff ((positiveEndCoord q z).1 - R)) •
          (x (positiveEndCoord q z).2 - u z) +
        pregluingCutoff (R - (positiveEndCoord q z).1) •
          (v (positiveEndCoord q z - (2 * R, 0)) - x (positiveEndCoord q z).2) :=
  (rfl)

/-- Where the longitudinal coordinate of the end is at most `R - 1`, the pre-glued map is `u`. -/
theorem pairOfPantsPreglue_of_le (hz : (positiveEndCoord q z).1 ≤ R - 1) :
    pairOfPantsPreglue q x u v R z = u z := by
  rw [pairOfPantsPreglue_apply, pregluingCutoff_of_le_neg_one (by linarith),
    pregluingCutoff_of_one_le (by linarith)]
  simp

/-- Near a point where the longitudinal coordinate of the end is less than `R - 1`, the pre-glued
map is `u`. -/
theorem pairOfPantsPreglue_eventuallyEq_of_lt
    (hz : Complex.equivRealProdCLM.symm z ≠ q.endCenter) (hR : (positiveEndCoord q z).1 < R - 1) :
    pairOfPantsPreglue q x u v R =ᶠ[𝓝 z] u :=
  ((continuousAt_fst_positiveEndCoord q hz).eventually_lt continuousAt_const hR).mono
    fun _ h ↦ pairOfPantsPreglue_of_le h.le

/-- **The pre-glued pair of pants in the end chart.** For an orbit `x` and a cylinder `v` of period
one in `t`, the pre-glued map read in the positive end chart of `q` is the pre-glued map of the
two cylinders `u ∘ φ'_q` and `v`, translated by `R`. -/
theorem pairOfPantsPreglue_comp_positiveEndChart (hx : Periodic x 1)
    (hv : ∀ s, Periodic (fun t ↦ v (s, t)) 1) (ζ : ℝ × ℝ) :
    pairOfPantsPreglue q x u v R (positiveEndChart q ζ) =
      preglue x (u ∘ positiveEndChart q) v R (ζ - (R, 0)) := by
  obtain ⟨k, hk⟩ := exists_positiveEndCoord_positiveEndChart q ζ
  -- The angular coordinate is recovered up to the integer `k`, which `x` and `v` do not see.
  have hxk : x (ζ.2 + k) = x ζ.2 := by simpa using (hx.int_mul k) ζ.2
  have hvk : v (ζ + (0, (k : ℝ)) - (2 * R, 0)) = v (ζ - (2 * R, 0)) := by
    have h := (hv (ζ.1 - 2 * R)).int_mul k ζ.2
    simp only [mul_one] at h
    have e₁ : ζ + (0, (k : ℝ)) - (2 * R, 0) = (ζ.1 - 2 * R, ζ.2 + k) := by ext <;> simp
    have e₂ : ζ - (2 * R, 0) = (ζ.1 - 2 * R, ζ.2) := by ext <;> simp
    rw [e₁, e₂, h]
  have hζ : ζ - (R, 0) - (R, 0) = ζ - (2 * R, 0) := by
    ext <;> simp only [Prod.fst_sub, Prod.snd_sub] <;> ring
  have hp := preglue_sub x (u ∘ positiveEndChart q) v R (ζ - (R, 0))
  rw [sub_eq_iff_eq_add'] at hp
  rw [pairOfPantsPreglue_apply, hk, hp, hvk, sub_add_cancel, hζ]
  simp only [Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, add_zero, sub_zero, hxk,
    comp_apply, neg_sub]
  module

/-- **Regularity of the pre-glued pair of pants.** If `u` is `Cⁿ` on `S`, and the orbit `x` and the
cylinder `v` are `Cⁿ` and of period one in `t`, then the pre-glued map is `Cⁿ` on `S`. -/
theorem contDiffOn_pairOfPantsPreglue {n : ℕ∞} (hx : ContDiff ℝ n x) (hxp : Periodic x 1)
    (hv : ContDiff ℝ n v) (hvp : ∀ s, Periodic (fun t ↦ v (s, t)) 1)
    (hu : ContDiffOn ℝ n u thricePuncturedSphereReal) :
    ContDiffOn ℝ n (pairOfPantsPreglue q x u v R) thricePuncturedSphereReal := by
  intro z hz
  have hc : Complex.equivRealProdCLM.symm z ≠ q.endCenter :=
    ne_endCenter (mem_thricePuncturedSphereReal_iff.1 hz) q
  -- Each coordinate expression is a function on the cylinder of period one in `t`.
  have hper {F : ℝ × ℝ → V} (hF : ContDiff ℝ n F) (hFp : ∀ p, F (p + (0, 1)) = F p) :
      ContDiffAt ℝ n (F ∘ positiveEndCoord q) z :=
    contDiffAt_comp_positiveEndCoord q hF hFp hc
  have hcut {g : ℝ → ℝ} (hg : ContDiff ℝ n g) :
      ContDiffAt ℝ n (fun w ↦ g ((positiveEndCoord q w).1)) z :=
    contDiffAt_comp_positiveEndCoord q (hg.comp contDiff_fst) (fun _ ↦ by simp) hc
  have hxz : ContDiffAt ℝ n (fun w ↦ x (positiveEndCoord q w).2) z :=
    hper (F := fun p ↦ x p.2) (hx.comp contDiff_snd) fun p ↦ by simpa using hxp p.2
  have hvz : ContDiffAt ℝ n (fun w ↦ v (positiveEndCoord q w - (2 * R, 0))) z :=
    hper (F := fun p ↦ v (p - (2 * R, 0))) (hv.comp (contDiff_id.sub contDiff_const))
      fun p ↦ by
        have e₁ : p + (0, 1) - (2 * R, 0) = (p.1 - 2 * R, p.2 + 1) := by ext <;> simp
        have e₂ : p - (2 * R, 0) = (p.1 - 2 * R, p.2) := by ext <;> simp
        rw [e₁, e₂]
        exact hvp (p.1 - 2 * R) p.2
  have huz := (hu z hz).contDiffAt (isOpen_thricePuncturedSphereReal.mem_nhds hz)
  have h₁ := hcut (g := fun s ↦ 1 - pregluingCutoff (s - R))
    (contDiff_const.sub (contDiff_pregluingCutoff.comp (contDiff_id.sub contDiff_const)))
  have h₂ := hcut (g := fun s ↦ pregluingCutoff (R - s))
    (contDiff_pregluingCutoff.comp (contDiff_const.sub contDiff_id))
  exact (huz.add (h₁.smul (hxz.sub huz)) |>.add (h₂.smul (hvz.sub hxz))).contDiffWithinAt

end Floer

namespace SymplecticForm

open Floer

variable [FiniteDimensional ℝ V]

/-- **The pre-glued pair of pants solves the Floer equation off the end.** Where the
longitudinal coordinate of the end `q` is less than `R - 1`, the pre-glued map has the perturbed
derivative of `u`, so it solves the Floer equation for any perturbation and almost complex
structure for which `u` does. -/
theorem perturbedFDeriv_pairOfPantsPreglue_of_lt (ω : SymplecticForm V) (Ks Kt : ℝ × ℝ → V → ℝ)
    (hz : Complex.equivRealProdCLM.symm z ≠ q.endCenter) (hR : (positiveEndCoord q z).1 < R - 1) :
    ω.perturbedFDeriv Ks Kt (pairOfPantsPreglue q x u v R) z = ω.perturbedFDeriv Ks Kt u z := by
  have h := pairOfPantsPreglue_eventuallyEq_of_lt (x := x) (u := u) (v := v) hz hR
  refine ContinuousLinearMap.ext fun w ↦ ?_
  rw [perturbedFDeriv_apply, perturbedFDeriv_apply, h.fderiv_eq, h.eq_of_nhds]

/-- **The Floer operator of the pre-glued pair of pants in the end chart.** For cylindrical data
`J_t`, `H_t dt`, the Floer operator of the pre-glued map read in the positive end chart of `q` is
the Floer operator of the pre-glued map of the two cylinders `u ∘ φ'_q` and `v`, translated by
`R`. -/
theorem floerOperator_pairOfPantsPreglue_comp_positiveEndChart (ω : SymplecticForm V)
    (J : ℝ → V → V →L[ℝ] V) (H : ℝ → V → ℝ) (hx : Periodic x 1)
    (hv : ∀ s, Periodic (fun t ↦ v (s, t)) 1) (ζ : ℝ × ℝ) :
    ω.floerOperator (fun p ↦ J p.2) (fun _ _ ↦ 0) (fun p ↦ H p.2)
        (pairOfPantsPreglue q x u v R ∘ positiveEndChart q) ζ =
      ω.floerOperator (fun p ↦ J p.2) (fun _ _ ↦ 0) (fun p ↦ H p.2)
        (preglue x (u ∘ positiveEndChart q) v R) (ζ - (R, 0)) := by
  have h : pairOfPantsPreglue q x u v R ∘ positiveEndChart q =
      fun ζ ↦ preglue x (u ∘ positiveEndChart q) v R (ζ - (R, 0)) :=
    funext fun ζ ↦ pairOfPantsPreglue_comp_positiveEndChart hx hv ζ
  simp only [floerOperator_def, h, fderiv_comp_sub, Prod.snd_sub, sub_zero]

/-- **The pre-gluing error of a pair of pants is exponentially small.** Let `H_t` be a `C²`
Hamiltonian, `J_t` a continuous family of endomorphisms and `x` a one-periodic orbit of
`X_{H_t}`. Let `u` be a map on `S` whose reading `u ∘ φ'_q` in the positive end chart of `q`
solves the Floer equation `∂_s + J_t (∂_t - X_{H_t}) = 0` where `s ≥ T₀` and converges to `x` in
`C¹` at the exponential rate `κ > 0` as `s → ∞`, and let `v` be a solution of the same equation on
the cylinder, of period one in `t`, converging to `x` in `C¹` at the same rate as `s → -∞`. Then
for every large gluing parameter `R`, the Floer operator of the pre-glued map, read in the
positive end chart, is at most `C' e^{-κR}` on the part `s ≥ T₀` of the end. -/
theorem exists_eventually_norm_floerOperator_pairOfPantsPreglue_comp_le
    (ω : SymplecticForm V)
    {J : ℝ → V → V →L[ℝ] V} {H : ℝ → V → ℝ} {C κ T₀ : ℝ}
    (hH : ContDiff ℝ 2 (uncurry H)) (hJ : Continuous (uncurry J))
    (hx : ∀ t, HasDerivAt x (ω.hamiltonianVectorField (H t) (x t)) t) (hxp : Periodic x 1)
    (hvp : ∀ s, Periodic (fun t ↦ v (s, t)) 1) (hκ : 0 < κ)
    (hud : ∀ᶠ s in atTop, ∀ t ∈ Icc (0 : ℝ) 1, DifferentiableAt ℝ (u ∘ positiveEndChart q) (s, t))
    (hu : ∀ᶠ s in atTop, ∀ t ∈ Icc (0 : ℝ) 1,
      ‖(u ∘ positiveEndChart q) (s, t) - x t‖ ≤ C * Real.exp (-(κ * s)))
    (hdu : ∀ᶠ s in atTop, ∀ t ∈ Icc (0 : ℝ) 1,
      ‖fderiv ℝ (u ∘ positiveEndChart q) (s, t) -
        (snd ℝ ℝ ℝ).smulRight (ω.hamiltonianVectorField (H t) (x t))‖ ≤
          C * Real.exp (-(κ * s)))
    (hvd : ∀ᶠ s in atBot, ∀ t ∈ Icc (0 : ℝ) 1, DifferentiableAt ℝ v (s, t))
    (hv : ∀ᶠ s in atBot, ∀ t ∈ Icc (0 : ℝ) 1, ‖v (s, t) - x t‖ ≤ C * Real.exp (κ * s))
    (hdv : ∀ᶠ s in atBot, ∀ t ∈ Icc (0 : ℝ) 1,
      ‖fderiv ℝ v (s, t) - (snd ℝ ℝ ℝ).smulRight (ω.hamiltonianVectorField (H t) (x t))‖ ≤
        C * Real.exp (κ * s))
    (huF : ∀ ζ : ℝ × ℝ, T₀ ≤ ζ.1 → ζ.2 ∈ Icc (0 : ℝ) 1 →
      ω.floerOperator (fun p ↦ J p.2) (fun _ _ ↦ 0) (fun p ↦ H p.2) (u ∘ positiveEndChart q) ζ =
        0)
    (hvF : ∀ z ∈ univ ×ˢ Icc (0 : ℝ) 1,
      ω.floerOperator (fun p ↦ J p.2) (fun _ _ ↦ 0) (fun p ↦ H p.2) v z = 0) :
    ∃ C', ∀ᶠ R in atTop, ∀ ζ : ℝ × ℝ, T₀ ≤ ζ.1 → ζ.2 ∈ Icc (0 : ℝ) 1 →
      ‖ω.floerOperator (fun p ↦ J p.2) (fun _ _ ↦ 0) (fun p ↦ H p.2)
        (pairOfPantsPreglue q x u v R ∘ positiveEndChart q) ζ‖ ≤ C' * Real.exp (-(κ * R)) := by
  obtain ⟨C', hC'⟩ :=
    ω.exists_eventually_norm_floerOperator_preglue_le hH hJ hx hκ hud hu hdu hvd hv hdv
  refine ⟨C', hC'.mono fun R hR ζ hζ hζt ↦ ?_⟩
  have hpos : 0 ≤ C' * Real.exp (-(κ * R)) :=
    (norm_nonneg _).trans (hR (0, 0) ⟨⟨by norm_num, by norm_num⟩, by norm_num, by norm_num⟩)
  rw [ω.floerOperator_pairOfPantsPreglue_comp_positiveEndChart J H hxp hvp]
  -- Left of the neck the pre-glued map is `u ∘ φ'_q`, right of it a translate of `v`.
  rcases lt_or_ge (ζ - (R, 0)).1 (-1) with h₁ | h₁
  · rw [ω.floerOperator_preglue_of_lt_neg_one J H x _ v R h₁, sub_add_cancel, huF ζ hζ hζt,
      norm_zero]
    exact hpos
  rcases lt_or_ge 1 (ζ - (R, 0)).1 with h₂ | h₂
  · rw [ω.floerOperator_preglue_of_one_lt J H x _ v R h₂,
      hvF _ ⟨mem_univ _, by simpa using hζt⟩, norm_zero]
    exact hpos
  exact hR _ ⟨⟨h₁, h₂⟩, by simpa using hζt⟩

/-- **The pre-gluing error of a Floer pair of pants.** Let `K` be a perturbation equal to
`H_q(t) dt` beyond `T₀ > 0` on each end `q`, for one-periodic `C²` Hamiltonians `H_q`, and let `u`
be differentiable on `S` and solve the Floer equation `(du - X_K)^{0,1} = 0` there for an almost
complex structure `J` which is `J_q(t)` on the part `s ≥ T₀` of the positive end chart of `q`, with
`J_q` continuous. Let `x` be a one-periodic orbit of the end Hamiltonian `H'_q` of the positive end
(`TauCeti.Floer.positiveEndHamiltonian`), and `v` a Floer cylinder for `J_q`, `H'_q`, of period
one in `t`. If `u ∘ φ'_q` converges to `x` in `C¹` at the exponential rate `κ > 0` as `s → ∞`,
and `v` as `s → -∞`, then for every large `R` the Floer operator of the pre-glued map, read in the
positive end chart, is at most `C' e^{-κR}` on the part `s ≥ T₀` of the end. -/
theorem exists_eventually_norm_floerOperator_pairOfPantsPreglue_comp_le_of_floer
    (ω : SymplecticForm V) {K : ℂ → V → ℂ →L[ℝ] ℝ} {H : Puncture → ℝ → V → ℝ}
    {J : ℝ × ℝ → AlmostComplexStructure V} {Jq : ℝ → AlmostComplexStructure V} {C κ T₀ : ℝ}
    (hKH : ∀ q w x, T₀ ≤ q.endSign * (q.endCoord w).re →
      K w x = H q (q.endCoord w).im x • q.endAngularForm w)
    (hH : ∀ q, Periodic (H q) 1) (hHs : ∀ q, ContDiff ℝ 2 (uncurry (H q))) (hT₀ : 0 < T₀)
    (hJq : ∀ ζ : ℝ × ℝ, T₀ ≤ ζ.1 → J (positiveEndChart q ζ) = Jq ζ.2)
    (hJc : Continuous fun t ↦ (Jq t).toLinearMap.toContinuousLinearMap)
    (hu : DifferentiableOn ℝ u thricePuncturedSphereReal)
    (hfloer : ∀ z ∈ thricePuncturedSphereReal,
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
        (ω.perturbedFDeriv (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z : ℝ × ℝ →ₗ[ℝ] V))
    (hx : ∀ t, HasDerivAt x (ω.hamiltonianVectorField (positiveEndHamiltonian H q t) (x t)) t)
    (hxp : Periodic x 1) (hvp : ∀ s, Periodic (fun t ↦ v (s, t)) 1) (hκ : 0 < κ)
    (hu' : ∀ᶠ s in atTop, ∀ t ∈ Icc (0 : ℝ) 1,
      ‖(u ∘ positiveEndChart q) (s, t) - x t‖ ≤ C * Real.exp (-(κ * s)))
    (hdu : ∀ᶠ s in atTop, ∀ t ∈ Icc (0 : ℝ) 1,
      ‖fderiv ℝ (u ∘ positiveEndChart q) (s, t) - (snd ℝ ℝ ℝ).smulRight
        (ω.hamiltonianVectorField (positiveEndHamiltonian H q t) (x t))‖ ≤
          C * Real.exp (-(κ * s)))
    (hvd : ∀ᶠ s in atBot, ∀ t ∈ Icc (0 : ℝ) 1, DifferentiableAt ℝ v (s, t))
    (hv : ∀ᶠ s in atBot, ∀ t ∈ Icc (0 : ℝ) 1, ‖v (s, t) - x t‖ ≤ C * Real.exp (κ * s))
    (hdv : ∀ᶠ s in atBot, ∀ t ∈ Icc (0 : ℝ) 1,
      ‖fderiv ℝ v (s, t) - (snd ℝ ℝ ℝ).smulRight
        (ω.hamiltonianVectorField (positiveEndHamiltonian H q t) (x t))‖ ≤
          C * Real.exp (κ * s))
    (hvF : ∀ z ∈ univ ×ˢ Icc (0 : ℝ) 1,
      ω.floerOperator (fun p _ ↦ (Jq p.2).toLinearMap.toContinuousLinearMap) (fun _ _ ↦ 0)
        (fun p ↦ positiveEndHamiltonian H q p.2) v z = 0) :
    ∃ C', ∀ᶠ R in atTop, ∀ ζ : ℝ × ℝ, T₀ ≤ ζ.1 → ζ.2 ∈ Icc (0 : ℝ) 1 →
      ‖ω.floerOperator (fun p _ ↦ (Jq p.2).toLinearMap.toContinuousLinearMap) (fun _ _ ↦ 0)
        (fun p ↦ positiveEndHamiltonian H q p.2)
        (pairOfPantsPreglue q x u v R ∘ positiveEndChart q) ζ‖ ≤ C' * Real.exp (-(κ * R)) := by
  have hHd : ∀ q t, Differentiable ℝ (H q t) := fun q t ↦
    ((hHs q).differentiable two_ne_zero).comp (differentiable_const t |>.prodMk differentiable_id)
  -- On the part `s > 0` of the positive end chart, `u ∘ φ'_q` is differentiable.
  have hud (ζ : ℝ × ℝ) (hζ : 0 < ζ.1) : DifferentiableAt ℝ (u ∘ positiveEndChart q) ζ := by
    have hS := positiveEndChart_mem_thricePuncturedSphereReal (q := q) hζ
    exact ((hu _ hS).differentiableAt (isOpen_thricePuncturedSphereReal.mem_nhds hS)).comp ζ
      ((contDiff_positiveEndChart q 1).differentiable one_ne_zero ζ)
  refine ω.exists_eventually_norm_floerOperator_pairOfPantsPreglue_comp_le
    (J := fun t _ ↦ (Jq t).toLinearMap.toContinuousLinearMap) (T₀ := T₀)
    (contDiff_uncurry_positiveEndHamiltonian (hHs q)) (hJc.comp continuous_fst) hx hxp hvp hκ
    ((eventually_gt_atTop 0).mono fun s hs t _ ↦ hud (s, t) hs) hu' hdu hvd hv hdv
    (fun ζ hζ _ ↦ ?_) hvF
  -- The Floer equation on `S` reads, in the positive end chart, as the cylinder equation.
  have hζ₀ : 0 < ζ.1 := hT₀.trans_le hζ
  have hS := positiveEndChart_mem_thricePuncturedSphereReal (q := q) hζ₀
  have h := ω.isComplexLinearMap_perturbedFDeriv_comp_positiveEndChart hKH hH hHd hζ
    ((hu _ hS).differentiableAt (isOpen_thricePuncturedSphereReal.mem_nhds hS)) (hfloer _ hS)
  rw [hJq ζ hζ] at h
  exact (ω.floerOperator_eq_zero_iff (fun p _ ↦ Jq p.2) _ _ _ ζ).2 h

end SymplecticForm

end TauCeti
