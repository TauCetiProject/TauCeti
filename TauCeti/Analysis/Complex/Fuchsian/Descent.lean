/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Fuchsian.CoarseQuotient

/-!
# Holomorphic descent to the coarse Fuchsian quotient

A function on the coarse quotient of the upper half-plane by a properly discontinuous
projective subgroup is holomorphic if and only if its pullback to the upper half-plane is
holomorphic. This includes elliptic orbits: in the chart at a point with stabilizer order `m`,
the pullback is the composition with `u ↦ u ^ m`, and holomorphy descends through this power map.

The local statement `Subgroup.differentiableOn_comp_stabilizerBallQuotientChart_symm` needs
holomorphy of the pullback only on the chosen stabilizer ball. The global criterion
`Subgroup.mdifferentiable_iff_comp_quotientMk` and the unique descent theorem
`Subgroup.existsUnique_mdifferentiable_quotientMk` apply to functions valued in any complex
Banach space. They use the ordinary orbit quotient, without choosing representatives to
define the descended function.

The elliptic descent argument uses `TauCeti.differentiableOn_descendPow` and follows
Farkas–Kra, *Riemann Surfaces*, Chapter I §§4–5, and Miranda, *Algebraic Curves and
Riemann Surfaces*, Chapter III §§3–4.
-/

public noncomputable section

open Filter Metric MulAction Set TauCeti Topology UpperHalfPlane
open scoped ComplexConjugate Manifold MatrixGroups

namespace Subgroup

variable (Γ : Subgroup PSL(2, ℝ)) {E : Type*}
  [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

section Local

variable {z : ℍ} {ε : ℝ} [Finite (stabilizer Γ z)] (hε : 0 < ε)
  (hopen : IsOpenEmbedding (stabilizerBallQuotientToQuotient Γ z ε))
  {F : orbitRel.Quotient Γ ℍ → E}

/-- In a stabilizer-ball chart, a function on the coarse quotient is holomorphic whenever its
pullback is holomorphic on the ball. This holds also when the stabilizer is nontrivial. -/
theorem differentiableOn_comp_stabilizerBallQuotientChart_symm
    (hF : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ, E) (F ∘ Quotient.mk _) (ball z ε)) :
    DifferentiableOn ℂ (F ∘ (stabilizerBallQuotientChart hε hopen).symm)
      (stabilizerBallQuotientChart hε hopen).target := by
  let e := stabilizerBallQuotientChart hε hopen
  let m := Nat.card (stabilizer Γ z)
  have : NeZero m := ⟨Nat.card_pos.ne'⟩
  let f : ℂ → E := fun w ↦ F (e.symm (w ^ m))
  have hr : 0 < Real.tanh (ε / 2) := by
    rw [← Real.tanh_zero]
    exact Real.tanh_strictMono (by linarith)
  have hf : DifferentiableOn ℂ f (ball 0 (Real.tanh (ε / 2))) := by
    intro w₀ hw₀
    have hw₀' := mem_ball_zero_iff.mp hw₀
    have hball : (discCoordinateHomeomorph z).symm
        (.mk w₀ (hw₀'.trans (Real.tanh_lt_one _))) ∈ ball z ε := by
      rw [mem_ball_iff_norm_discCoordinate_lt]
      simpa using hw₀'
    exact (Γ.differentiableAt_comp_stabilizerBallQuotientChart_symm_pow hε hopen hw₀'
      ((hF _ hball).mdifferentiableAt (isOpen_ball.mem_nhds hball))).differentiableWithinAt
  have hd := differentiableOn_descendPow (m := m) isOpen_ball hf
    (fun w _ ζ ↦ by simp only [f, rootsOfUnity.smul_pow])
  dsimp only [f] at hd
  rw [descendPow_comp_pow (m := m) (fun u ↦ F (e.symm u)), image_pow_ball hr.le] at hd
  simpa only [e, m, Function.comp_def, stabilizerBallQuotientChart_target] using hd

end Local

variable [ProperlyDiscontinuousSMul Γ ℍ]

/-- Holomorphy on the full coarse quotient can be checked after pullback to the upper
half-plane, including at elliptic orbits. -/
@[simp] theorem mdifferentiable_iff_comp_quotientMk {F : orbitRel.Quotient Γ ℍ → E} :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ, E) F ↔
      MDifferentiable 𝓘(ℂ) 𝓘(ℂ, E) (F ∘ Quotient.mk _) := by
  refine ⟨fun hF ↦ hF.comp (mdifferentiable_quotientMk Γ), fun hF q ↦ ?_⟩
  rw [mdifferentiableAt_iff_source_of_mem_source (mem_chart_source ℂ q)]
  simp only [mfld_simps, mdifferentiableWithinAt_univ, mdifferentiableAt_iff_differentiableAt]
  have hd := Γ.differentiableOn_comp_stabilizerBallQuotientChart_symm
    (chartRadius_pos Γ q.out) (isOpenEmbedding_stabilizerBallQuotientToQuotient_chartRadius Γ q.out)
    hF.mdifferentiableOn
  rw [← chartAt_eq] at hd
  exact hd.differentiableAt ((chartAt ℂ q).open_target.mem_nhds
    ((chartAt ℂ q).map_source (mem_chart_source ℂ q)))

/-- Every invariant holomorphic function on the upper half-plane descends uniquely to a
holomorphic function on the coarse quotient, with no freeness assumption. -/
theorem existsUnique_mdifferentiable_quotientMk (f : ℍ → E)
    (hinv : ∀ (g : Γ) (z : ℍ), f (g • z) = f z)
    (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ, E) f) :
    ∃! F : orbitRel.Quotient Γ ℍ → E,
      MDifferentiable 𝓘(ℂ) 𝓘(ℂ, E) F ∧ F ∘ Quotient.mk _ = f := by
  let F : orbitRel.Quotient Γ ℍ → E := Quotient.lift f (by
    intro z w h
    obtain ⟨g, rfl⟩ := mem_orbit_iff.mp (orbitRel_apply.mp h)
    exact hinv g w)
  refine ⟨F, ⟨(Γ.mdifferentiable_iff_comp_quotientMk).mpr hf, rfl⟩, ?_⟩
  intro G hG
  funext q
  induction q using Quotient.inductionOn with
  | h z => exact congrFun hG.2 z

end Subgroup
