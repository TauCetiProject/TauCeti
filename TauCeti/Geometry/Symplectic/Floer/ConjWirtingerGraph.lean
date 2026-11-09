/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Wirtinger.Basic
public import TauCeti.Geometry.Symplectic.Floer.Graph

/-!
# The graph structure of a function `ℂ → ℂ`

For `g : ℂ → ℂ`, the structure

`J_g(z, w)(v, a) = (i v, i a - 2 i \bar∂g(z) conj v)`

on `ℂ × ℂ` (`TauCeti.conjWirtingerGraphStructure`) is Gromov's graph structure
`TauCeti.Floer.graphStructure` for the target structure `i` and the one-form `\bar∂g`, because the
graph `z ↦ (z, g z)` solves the inhomogeneous equation `\bar∂u = \bar∂g`. It squares to `-1`
(`TauCeti.conjWirtingerGraphStructure_apply_apply`), is as regular as `\bar∂g`
(`TauCeti.contDiffOn_conjWirtingerGraphStructure`), and the graph of a real-differentiable `g`
satisfies `dG(i) = J_g dG(1)` (`TauCeti.fderiv_graph_I_eq_conjWirtingerGraphStructure`), so it is
`J_g`-holomorphic in the sense of `TauCeti.IsJHolomorphicAt`
(`TauCeti.isJHolomorphicAt_graph_conjWirtingerGraphAlmostComplex`).

## References

* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, 2nd ed., Section 8.1
  (Gromov's graph construction).
-/

public section

open Complex ComplexConjugate Set

namespace TauCeti

/-- **The graph structure of `g`**: the structure
`J_g(z, w)(v, a) = (i v, i a - 2 i \bar∂g(z) conj v)` on `WithLp 2 (ℂ × ℂ)`, Gromov's graph
structure `TauCeti.Floer.graphStructure` for the target structure `i` and the one-form
`\bar∂g(z) = \bar∂g(z)(1) conj`. The graph of `g` is `J_g`-holomorphic at every point where `g` is
real-differentiable. -/
noncomputable def conjWirtingerGraphStructure (g : ℂ → ℂ) :
    WithLp 2 (ℂ × ℂ) → WithLp 2 (ℂ × ℂ) →L[ℝ] WithLp 2 (ℂ × ℂ) :=
  Floer.graphStructure (fun _ ↦ ContinuousLinearMap.mul ℝ ℂ I)
    (fun p ↦ conjWirtingerDeriv g p.1 1 • (conjCLE : ℂ →L[ℝ] ℂ))

/-- The graph structure of `g` as Gromov's graph structure for the target structure `i` and the
one-form `\bar∂g(z)(1) conj`. -/
theorem conjWirtingerGraphStructure_def (g : ℂ → ℂ) :
    conjWirtingerGraphStructure g =
      Floer.graphStructure (fun _ ↦ ContinuousLinearMap.mul ℝ ℂ I)
        (fun p ↦ conjWirtingerDeriv g p.1 1 • (conjCLE : ℂ →L[ℝ] ℂ)) :=
  (rfl)

/-- The formula `J_g(z, w)(v, a) = (i v, i a - 2 i \bar∂g(z) conj v)`. -/
theorem conjWirtingerGraphStructure_apply (g : ℂ → ℂ) (p ζ : WithLp 2 (ℂ × ℂ)) :
    conjWirtingerGraphStructure g p ζ = WithLp.toLp 2 (I * ζ.fst,
      I * ζ.snd - 2 * I * (conjWirtingerDeriv g p.fst 1 * conj ζ.fst)) := by
  simp [conjWirtingerGraphStructure_def]
  ring

/-- The graph structure squares to `-1`. -/
theorem conjWirtingerGraphStructure_apply_apply (g : ℂ → ℂ) (p ζ : WithLp 2 (ℂ × ℂ)) :
    conjWirtingerGraphStructure g p (conjWirtingerGraphStructure g p ζ) = -ζ := by
  rw [conjWirtingerGraphStructure_def]
  exact Floer.graphStructure_graphStructure (fun v ↦ by simp [← mul_assoc]) ζ

/-- The graph structure is as regular as `\bar∂g`. -/
theorem contDiffOn_conjWirtingerGraphStructure {g : ℂ → ℂ} {n : WithTop ℕ∞} {s : Set ℂ}
    (hg : ContDiffOn ℝ n (fun z ↦ conjWirtingerDeriv g z 1) s) :
    ContDiffOn ℝ n (conjWirtingerGraphStructure g) (WithLp.ofLp ⁻¹' (s ×ˢ univ)) := by
  rw [conjWirtingerGraphStructure_def]
  exact Floer.contDiffOn_graphStructure contDiffOn_const
    ((hg.comp contDiffOn_fst fun _ (hp : _ ∈ s ×ˢ univ) ↦ hp.1).smul contDiffOn_const)

/-- **The graph of `g` solves `dG(i) = J_g dG(1)`.** The graph `G(z) = (z, g z)` of a
real-differentiable `g` solves the inhomogeneous equation `\bar∂g = \bar∂g`, which Gromov's
construction turns into this equation for `J_g`. -/
theorem fderiv_graph_I_eq_conjWirtingerGraphStructure {g : ℂ → ℂ} {z : ℂ}
    (hg : DifferentiableAt ℝ g z) :
    fderiv ℝ (fun w ↦ WithLp.toLp 2 (w, g w)) z I =
      conjWirtingerGraphStructure g (WithLp.toLp 2 (z, g z))
        (fderiv ℝ (fun w ↦ WithLp.toLp 2 (w, g w)) z 1) := by
  rw [conjWirtingerGraphStructure_def]
  refine (Floer.fderiv_toLp_prodMk_I_eq_graphStructure_iff hg).2 ?_
  rw [fderiv_apply_eq_smul_wirtingerDeriv_add_smul_conjWirtingerDeriv (f := g) z I,
    fderiv_apply_eq_smul_wirtingerDeriv_add_smul_conjWirtingerDeriv (f := g) z 1]
  simp only [smul_eq_mul, conj_I, neg_mul, smul_apply, ContinuousLinearEquiv.coe_coe,
    ContinuousAlgEquiv.coeCLE_apply, conjCAE_apply, mul_neg, sub_neg_eq_add, one_mul, map_one,
    wirtingerDeriv_add_conjWirtingerDeriv, mul_one, ContinuousLinearMap.mul_apply']
  rw [← wirtingerDeriv_add_conjWirtingerDeriv g z 1]
  ring

/-- The graph structure of `g` as a point-dependent `TauCeti.AlmostComplexStructure`. -/
noncomputable def conjWirtingerGraphAlmostComplex (g : ℂ → ℂ) (p : WithLp 2 (ℂ × ℂ)) :
    AlmostComplexStructure (WithLp 2 (ℂ × ℂ)) where
  toLinearMap := (conjWirtingerGraphStructure g p).toLinearMap
  square_neg := LinearMap.ext fun ζ ↦ by simp [conjWirtingerGraphStructure_apply_apply]

/-- The almost complex structure acts as the graph structure. -/
@[simp]
theorem conjWirtingerGraphAlmostComplex_apply (g : ℂ → ℂ) (p ζ : WithLp 2 (ℂ × ℂ)) :
    conjWirtingerGraphAlmostComplex g p ζ = conjWirtingerGraphStructure g p ζ :=
  (rfl)

/-- **The graph of `g` is `J_g`-holomorphic** at every point where `g` is real-differentiable, for
the standard structure on the domain `ℂ`. -/
theorem isJHolomorphicAt_graph_conjWirtingerGraphAlmostComplex {g : ℂ → ℂ} {z : ℂ}
    (hg : DifferentiableAt ℝ g z) :
    IsJHolomorphicAt (fun _ ↦ AlmostComplexStructure.ofComplexModule ℂ)
      (conjWirtingerGraphAlmostComplex g) (fun w ↦ WithLp.toLp 2 (w, g w)) z := by
  have hd : DifferentiableAt ℝ (fun w ↦ WithLp.toLp 2 (w, g w)) z :=
    (WithLp.prodContinuousLinearEquiv 2 ℝ ℂ ℂ).symm.differentiableAt.comp z
      (differentiableAt_id.prodMk hg)
  refine isJHolomorphicAt_of_hasFDerivAt hd.hasFDerivAt
    ((isComplexLinearMap_iff_apply _ _ _).2 fun v ↦ ?_)
  have hI := fderiv_graph_I_eq_conjWirtingerGraphStructure hg
  have hv : v = v.re • (1 : ℂ) + v.im • I := by
    apply Complex.ext <;> simp
  have hIv : I • v = v.re • I - v.im • (1 : ℂ) := by
    apply Complex.ext <;> simp
  simp only [ContinuousLinearMap.coe_coe, AlmostComplexStructure.ofComplexModule_apply,
    conjWirtingerGraphAlmostComplex_apply]
  rw [hIv]
  conv_rhs => rw [hv]
  simp only [map_add, map_sub, map_smul, hI, conjWirtingerGraphStructure_apply_apply, smul_neg]
  abel

end TauCeti
