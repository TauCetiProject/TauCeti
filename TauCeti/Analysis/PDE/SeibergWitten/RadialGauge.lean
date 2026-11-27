/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.DifferentialForm.Poincare
public import TauCeti.Analysis.Normed.Group.LocallyBounded
public import TauCeti.Analysis.PDE.SeibergWitten.CutoffCurrent
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import TauCeti.Analysis.Calculus.DifferentialForm.Regularity
import TauCeti.Analysis.Calculus.Equicontinuity
import TauCeti.Topology.ContinuousMap.Ascoli
import TauCeti.Topology.Algebra.Module.FiniteDimension
import TauCeti.Topology.UniformSpace.LocallyUniformConvergence

/-!
# The radial gauge of an abelian Higgs pair

Let `(a, α)` be an abelian Higgs pair on an open subset `s` of a real normed space `E`: an
imaginary connection form `a = i b` on the trivial Hermitian line, with `b` a real one-form, and a
section `α : E → ℂ`, with covariant derivative `∇_a α = dα + i b α`
(`TauCeti.SeibergWitten.covariantDeriv`). A phase `θ : E → ℝ` acts by the gauge transformation

`(b, α) ↦ (b - dθ, exp (i θ) α)`,

which preserves the curvature `db` and multiplies the covariant derivative by `exp (i θ)`
(`TauCeti.SeibergWitten.covariantDeriv_exp_mul`, in
`TauCeti.Analysis.PDE.SeibergWitten.CutoffCurrent`), so that `|α|` and `|∇_a α|` are gauge
invariant.

When `s` is star-convex with respect to `x₀`, the **radial gauge** centred at `x₀` is given by the
phase

`θ(x) = ∫₀¹ b(x₀ + t (x - x₀))(x - x₀) dt`

(`TauCeti.SeibergWitten.radialPhase`), the Poincaré homotopy `K b` of `b`
(`TauCeti.poincareHomotopy`). By the homotopy formula `d (K b) + K (d b) = b`, the transformed
connection form is the Poincaré homotopy of the curvature,

`b - dθ = K (db)`,  `(K (db))(x) = ∫₀¹ t (db)(x₀ + t (x - x₀))(x - x₀, ·) dt`

(`TauCeti.SeibergWitten.sub_ofSubsingleton_fderiv_radialPhase`). So in the radial gauge the
connection is determined by the curvature alone: its curvature is still `db` when `b` is `C²`
(`StarConvex.extDeriv_poincareHomotopy_extDeriv`), it vanishes on the radial vector `x - x₀`
(`TauCeti.curryLeft_poincareHomotopy_sub_eq_zero`), it is bounded by `|db| |x - x₀| / 2`
(`TauCeti.norm_poincareHomotopy_le`), and a bound on the derivative of the curvature makes it
Lipschitz (`StarConvex.norm_poincareHomotopy_sub_le`).

This is the gauge fixing behind local compactness for abelian gauge fields: bounds on the
curvature and on `α`, `∇_a α` only control the pair up to gauge, and the radial gauge turns them
into bounds on the fields themselves. On a finite-dimensional `E`, a sequence of pairs whose
curvatures and their first derivatives, sections and covariant derivatives are bounded on each
compact subset of `s` has, after the radial gauge transformations, a subsequence converging
locally uniformly on `s`
(`TauCeti.SeibergWitten.exists_strictMono_tendstoLocallyUniformlyOn_radialGauge`).
The limit is only continuous; higher regularity of limits of solutions of the Seiberg–Witten or
vortex equations comes from the equations, not from the gauge.

In Taubes's analysis of Seiberg–Witten solutions at large parameter `r`, the solutions are
rescaled at the length scale `r^(-1/2)`, and his estimates bound the rescaled curvature, `α` and
`∇_a α`. Given also a bound on the derivative of the rescaled curvature, the compactness above
extracts continuous locally uniform limits in the radial gauge. Identifying these limits as
solutions of the equations studied in `TauCeti.Analysis.PDE.SeibergWitten.FlatLimit` requires
further regularity, which comes from the equations.

## Main definitions and results

All in the namespace `TauCeti.SeibergWitten`:

* `radialPhase x₀ b`: the phase of the radial gauge centred at `x₀`, with formula
  `radialPhase_apply` and regularity `contDiffOn_radialPhase`.
* `sub_ofSubsingleton_fderiv_radialPhase`: `b - dθ = K (db)` on `s`.
* `covariantDeriv_poincareHomotopy_exp_mul`: the covariant derivative of the pair in the radial
  gauge is `exp (i θ) ∇_a α`.
* `exists_strictMono_tendstoLocallyUniformlyOn_radialGauge`: local compactness in the radial
  gauge.

## References

* C. H. Taubes, *SW ⇒ Gr: from the Seiberg–Witten equations to pseudo-holomorphic curves*,
  J. Amer. Math. Soc. 9 (1996), 845–918.
* K. K. Uhlenbeck, *Removable singularities in Yang–Mills fields*, Comm. Math. Phys. 83 (1982),
  11–29 (the exponential gauge).
-/

public section

noncomputable section

open AffineMap Complex Filter Metric Set Topology

namespace TauCeti.SeibergWitten

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {x₀ x : E} {s : Set E} {b : E → E [⋀^Fin 1]→L[ℝ] ℝ} {α : E → ℂ}

/-! ### The radial gauge -/

/-- The phase of the **radial gauge** centred at `x₀`: the Poincaré homotopy of the connection form
`b`, `θ(x) = ∫₀¹ b(x₀ + t (x - x₀))(x - x₀) dt` (`radialPhase_apply`). The gauge transformation by
`θ` replaces `b` by the Poincaré homotopy of its curvature
(`sub_ofSubsingleton_fderiv_radialPhase`). -/
def radialPhase (x₀ : E) (b : E → E [⋀^Fin 1]→L[ℝ] ℝ) (x : E) : ℝ :=
  poincareHomotopy x₀ b x ![]

/-- The Poincaré homotopy of a one-form is the zero-form with value the radial phase. -/
theorem poincareHomotopy_eq_constOfIsEmpty_radialPhase (x₀ : E)
    (b : E → E [⋀^Fin 1]→L[ℝ] ℝ) (x : E) :
    poincareHomotopy x₀ b x =
      ContinuousAlternatingMap.constOfIsEmpty ℝ E (Fin 0) (radialPhase x₀ b x) := by
  ext v
  simp [radialPhase, Subsingleton.elim v ![]]

/-- The radial phase vanishes at the centre. -/
@[simp]
theorem radialPhase_self (x₀ : E) (b : E → E [⋀^Fin 1]→L[ℝ] ℝ) : radialPhase x₀ b x₀ = 0 := by
  simp [radialPhase]

/-- The radial phase integrates the connection form along the segment from the centre:
`θ(x) = ∫₀¹ b(x₀ + t (x - x₀))(x - x₀) dt`. -/
theorem radialPhase_apply (x₀ : E) (b : E → E [⋀^Fin 1]→L[ℝ] ℝ) (x : E) :
    radialPhase x₀ b x = ∫ t in (0 : ℝ)..1, b (lineMap x₀ x t) (fun _ ↦ x - x₀) := by
  -- Evaluating a zero-form at the empty tuple is a linear isometric equivalence, which commutes
  -- with integrals without any integrability assumption.
  let L := (ContinuousAlternatingMap.constOfIsEmptyLIE ℝ E ℝ (Fin 0)).symm.toContinuousLinearEquiv
  have hL (f : E [⋀^Fin 0]→L[ℝ] ℝ) : L f = f ![] := by
    rw [← (ContinuousAlternatingMap.constOfIsEmptyLIE ℝ E ℝ (Fin 0)).apply_symm_apply f]
    simp [L]
  rw [radialPhase, poincareHomotopy_apply, ← hL, intervalIntegral.integral_of_le zero_le_one,
    intervalIntegral.integral_of_le zero_le_one, ← L.integral_comp_comm]
  refine MeasureTheory.integral_congr_ae (Eventually.of_forall fun t ↦ ?_)
  simp only [hL, pow_zero, one_smul, ContinuousAlternatingMap.curryLeft_apply_apply]
  congr 1
  ext i
  fin_cases i
  simp

/-- The radial phase of a `C^r` connection form on an open star-convex set is `C^r` there. -/
theorem contDiffOn_radialPhase (hs : StarConvex ℝ x₀ s) (hso : IsOpen s) {r : ℕ∞}
    (hb : ContDiffOn ℝ r b s) : ContDiffOn ℝ r (radialPhase x₀ b) s :=
  (ContinuousAlternatingMap.apply ℝ E ℝ ![]).contDiff.comp_contDiffOn
    (hs.contDiffOn_poincareHomotopy hso hb)

/-- **The radial gauge.** On an open set star-convex with respect to `x₀`, the gauge
transformation of a `C¹` connection form `b` by its radial phase `θ` is the Poincaré homotopy of
the curvature: `b - dθ = K (db)`. -/
theorem sub_ofSubsingleton_fderiv_radialPhase (hs : StarConvex ℝ x₀ s) (hso : IsOpen s)
    (hb : ContDiffOn ℝ 1 b s) (hx : x ∈ s) :
    b x - .ofSubsingleton ℝ E ℝ (0 : Fin 1) (fderiv ℝ (radialPhase x₀ b) x) =
      poincareHomotopy x₀ (extDeriv b) x := by
  have h := hs.extDeriv_poincareHomotopy_add_poincareHomotopy_extDeriv hso hb hx
  rw [funext (poincareHomotopy_eq_constOfIsEmpty_radialPhase x₀ b), extDeriv_constOfIsEmpty] at h
  rw [← h]
  abel

/-- In the radial gauge the covariant derivative of the transformed pair is `exp (i θ) ∇_a α`. -/
theorem covariantDeriv_poincareHomotopy_exp_mul (hs : StarConvex ℝ x₀ s) (hso : IsOpen s)
    (hb : ContDiffOn ℝ 1 b s) (hα : DifferentiableAt ℝ α x) (hx : x ∈ s) :
    covariantDeriv (poincareHomotopy x₀ (extDeriv b))
        (fun y ↦ cexp (radialPhase x₀ b y * I) * α y) x =
      cexp (radialPhase x₀ b x * I) • covariantDeriv b α x :=
  covariantDeriv_exp_mul (((contDiffOn_radialPhase hs hso hb).differentiableOn one_ne_zero x
    hx).differentiableAt (hso.mem_nhds hx)) hα
    (sub_ofSubsingleton_fderiv_radialPhase hs hso hb hx).symm

/-! ### Compactness in the radial gauge -/

/-- **Local compactness in the radial gauge.** Let `s` be an open subset of a finite-dimensional
space, star-convex with respect to `x₀`, and let `(b n, α n)` be abelian Higgs pairs on `s`, with
`C²` connection forms and differentiable sections. Suppose that the curvatures `d (b n)` and their
derivatives, the sections `α n` and their covariant derivatives `∇_(b n) (α n)` are bounded on each
compact subset of `s`, uniformly in `n`. Then, along a subsequence, the radial gauge
transformations `(K (d (b n)), exp (i θₙ) α n)` of the pairs converge locally uniformly on `s`. -/
theorem exists_strictMono_tendstoLocallyUniformlyOn_radialGauge [FiniteDimensional ℝ E]
    (hs : StarConvex ℝ x₀ s) (hso : IsOpen s) {b : ℕ → E → E [⋀^Fin 1]→L[ℝ] ℝ}
    {α : ℕ → E → ℂ} (hb : ∀ n, ContDiffOn ℝ 2 (b n) s) (hα : ∀ n, DifferentiableOn ℝ (α n) s)
    (hF : IsLocallyBoundedOn (fun n ↦ extDeriv (b n)) s)
    (hDF : IsLocallyBoundedOn (fun n ↦ fderiv ℝ (extDeriv (b n))) s)
    (hαb : IsLocallyBoundedOn α s)
    (hDα : IsLocallyBoundedOn (fun n ↦ covariantDeriv (b n) (α n)) s) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∃ (b' : E → E [⋀^Fin 1]→L[ℝ] ℝ) (α' : E → ℂ), ContinuousOn b' s ∧ ContinuousOn α' s ∧
        TendstoLocallyUniformlyOn (fun k ↦ poincareHomotopy x₀ (extDeriv (b (φ k)))) b' atTop s ∧
        TendstoLocallyUniformlyOn (fun k y ↦ cexp (radialPhase x₀ (b (φ k)) y * I) * α (φ k) y)
          α' atTop s := by
  -- The radial gauge transformations of the connections and sections.
  set c : ℕ → E → E [⋀^Fin 1]→L[ℝ] ℝ := fun n ↦ poincareHomotopy x₀ (extDeriv (b n))
  set β : ℕ → E → ℂ := fun n y ↦ cexp (radialPhase x₀ (b n) y * I) * α n y
  have hFc (n : ℕ) : ContDiffOn ℝ 1 (extDeriv (b n)) s :=
    contDiffOn_extDeriv (hb n) hso (by norm_num)
  have hb1 (n : ℕ) : ContDiffOn ℝ 1 (b n) s := (hb n).of_le (by norm_num)
  have hc (n : ℕ) : DifferentiableOn ℝ (c n) s :=
    (hs.contDiffOn_poincareHomotopy hso (hFc n)).differentiableOn one_ne_zero
  have hβ (n : ℕ) : DifferentiableOn ℝ (β n) s := fun y hy ↦
    ((((ofRealCLM.differentiableAt.comp y (((contDiffOn_radialPhase hs hso (hb1 n)).differentiableOn
      one_ne_zero y hy).differentiableAt (hso.mem_nhds hy))).mul_const I).cexp).mul
        ((hα n y hy).differentiableAt (hso.mem_nhds hy))).differentiableWithinAt
  have hcb : IsLocallyBoundedOn c s := hs.isLocallyBoundedOn_poincareHomotopy hF
  have hDc : IsLocallyBoundedOn (fun n ↦ fderiv ℝ (c n)) s :=
    hs.isLocallyBoundedOn_fderiv_poincareHomotopy hso
      (fun n ↦ (hFc n).differentiableOn one_ne_zero) hF hDF
  have hnβ (n : ℕ) (y : E) : ‖β n y‖ = ‖α n y‖ := by simp [β, norm_exp_ofReal_mul_I]
  -- Bounds on the derivatives of the sections in the radial gauge.
  have hDβ (K : Set E) (hK : IsCompact K) (hKs : K ⊆ s) :
      ∃ M, ∀ n, ∀ y ∈ K, ‖fderiv ℝ (β n) y‖ ≤ M := by
    obtain ⟨M, hM⟩ := isLocallyBoundedOn_def.1 hcb K hKs hK
    obtain ⟨A, hA⟩ := isLocallyBoundedOn_def.1 hαb K hKs hK
    obtain ⟨C, hC⟩ := isLocallyBoundedOn_def.1 hDα K hKs hK
    refine ⟨C + M * A, fun n y hy ↦ (norm_fderiv_le_norm_covariantDeriv_add (c n) _ y).trans ?_⟩
    rw [covariantDeriv_poincareHomotopy_exp_mul hs hso (hb1 n)
      ((hα n y (hKs hy)).differentiableAt (hso.mem_nhds (hKs hy))) (hKs hy), norm_smul,
      norm_exp_ofReal_mul_I, one_mul, hnβ]
    exact add_le_add (hC n y hy) (mul_le_mul (hM n y hy) (hA n y hy) (norm_nonneg _)
      ((norm_nonneg _).trans (hM n y hy)))
  -- Arzelà–Ascoli, first for the connections and then for the sections.
  have hcequi : EquicontinuousOn c s := equicontinuousOn_of_forall_isCompact_norm_fderiv_le hso hc
    fun K hK hKs ↦ isLocallyBoundedOn_def.1 hDc K hKs hK
  have hβequi : EquicontinuousOn β s := equicontinuousOn_of_forall_isCompact_norm_fderiv_le hso hβ
    fun K hK hKs ↦ hDβ K hK hKs
  obtain ⟨φ₁, hφ₁, b', hb'⟩ := hcequi.exists_strictMono_tendstoLocallyUniformlyOn hso
    fun y hy ↦ (hcb.exists_forall_norm_le hy).elim fun M hM ↦
      ⟨closedBall 0 M, isCompact_closedBall 0 M, fun n ↦ mem_closedBall_zero_iff.2 (hM n)⟩
  obtain ⟨φ₂, hφ₂, α', hα'⟩ := (hβequi.comp φ₁).exists_strictMono_tendstoLocallyUniformlyOn hso
    fun y hy ↦ (hαb.exists_forall_norm_le hy).elim fun A hA ↦ ⟨closedBall 0 A,
      isCompact_closedBall 0 A, fun n ↦ mem_closedBall_zero_iff.2 ((hnβ _ y).trans_le (hA _))⟩
  -- The limits are continuous, as locally uniform limits of continuous maps.
  exact ⟨φ₁ ∘ φ₂, hφ₁.comp hφ₂, b', α',
    hb'.continuousOn (Eventually.of_forall fun n ↦ hc (φ₁ n) |>.continuousOn).frequently,
    hα'.continuousOn (Eventually.of_forall fun n ↦ hβ (φ₁ (φ₂ n)) |>.continuousOn).frequently,
    hb'.comp_tendsto hφ₂.tendsto_atTop, hα'⟩

end TauCeti.SeibergWitten
