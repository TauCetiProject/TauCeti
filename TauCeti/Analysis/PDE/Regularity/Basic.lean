/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.DirichletProblem
public import TauCeti.Analysis.Sobolev.Wkp.LineDeriv
public import TauCeti.Analysis.PDE.EnergyForm.DifferenceQuotient
import TauCeti.Analysis.Sobolev.DifferenceQuotient
import TauCeti.Analysis.Sobolev.W1p.Density

/-!
# `H²` regularity of whole-space weak solutions

Let `a` be a uniformly elliptic coefficient field on `ℝⁿ`, with lower ellipticity constant `λ`,
which is Lipschitz: `‖a(x) - a(y)‖ ≤ K ‖x - y‖` in the operator norm of the attached bilinear
forms. Let `u ∈ H¹(ℝⁿ)` be a weak solution of the divergence-form equation

`-∂ⱼ(aⁱʲ ∂ᵢu) = f` on `ℝⁿ`, with `f ∈ L²(ℝⁿ)`,

meaning `∫ ⟨a ∇u, ∇v⟩ = ∫ f v` for every `v ∈ H¹(ℝⁿ)`. This file proves that `u` then has
second-order weak derivatives in `L²(ℝⁿ)`, that is `u ∈ H²(ℝⁿ)`, with the estimate

`‖∂_w ∂_y u‖_{L²} ≤ ‖y‖ ‖w‖ (‖f‖_{L²} + K ‖∇u‖_{L²}) / λ`

in every pair of directions. No smoothness of `f` and no regularity of `u` beyond `H¹` is
assumed: one derivative of the coefficients, together with ellipticity, upgrades one weak
derivative of the solution to two. For a constant coefficient matrix `K = 0`, and the estimate
reads `‖∂_w ∂_y u‖_{L²} ≤ ‖y‖ ‖w‖ ‖f‖_{L²} / λ`.

## The difference-quotient method

The proof is the classical difference-quotient argument. For a direction `w` and a step `t`, the
difference quotient `Dᵗ u = t⁻¹ (u(· + t w) - u)` again lies in `H¹(ℝⁿ)`. Substituting
`x ↦ x - t w` moves a translation from one argument of the energy form to the other, at the cost
of translating the coefficient field (`TauCeti.PDE.energyFormH1_translate`). The energy form is
therefore anti-adjoint for the difference quotient up to an error carrying the difference
quotient of `a`, which the Lipschitz bound controls uniformly in `t`:

`|a(Dᵗ u, v) + a(u, D⁻ᵗ v)| ≤ K ‖w‖ ‖∇u‖_{L²} ‖∇v‖_{L²}`

(`TauCeti.PDE.abs_energyFormH1_differenceQuotient_add_le`). For a constant coefficient the error
vanishes and this is the integrated form of the discrete integration-by-parts identity
`∫ (Dᵗ g) h = -∫ g (D⁻ᵗ h)`. Testing the equation against `D⁻ᵗ(Dᵗ u)`, this discrete integration
by parts turns `a(u, D⁻ᵗ(Dᵗ u))` into minus the energy `a(Dᵗ u, Dᵗ u)` of `Dᵗ u`, up to the
Lipschitz error. Using ellipticity on the left and the difference-quotient bound
`‖D⁻ᵗ g‖_{L²} ≤ ‖w‖ ‖∇g‖_{L²}` (with `g = Dᵗ u`) on the right gives

`λ ‖∇Dᵗ u‖²_{L²} ≤ a(Dᵗ u, Dᵗ u) ≤ (‖f‖_{L²} + K ‖∇u‖_{L²}) ‖w‖ ‖∇Dᵗ u‖_{L²}`,

so `‖Dᵗ ∇u‖_{L²} ≤ ‖w‖ (‖f‖_{L²} + K ‖∇u‖_{L²}) / λ` **uniformly in `t`**
(`TauCeti.PDE.UniformlyEllipticOn.norm_gradient_differenceQuotient_le_of_lipschitzWith`). The
difference-quotient criterion
`TauCeti.exists_norm_le_hasWeakLineDerivOn_of_frequently_eLpNorm_inv_mul_sub_le` converts that
uniform bound into a weak derivative of `∇u` in `L²`, and assembling the directions of an
orthonormal basis produces a weak Fréchet derivative of `∇u`, that is, the Hessian.

Working on the whole space is what keeps the argument free of cut-offs: no boundary regularity
is involved, `H¹₀(ℝⁿ) = H¹(ℝⁿ)` (`TauCeti.w1p0Submodule_top_eq_top`), so the solution concept
`TauCeti.PDE.IsWeakSolutionDirichlet` imposes no boundary condition here, and every difference
quotient is a legitimate test function. For a constant principal coefficient and bounded
measurable lower-order coefficients, interior `H²` regularity on a general domain follows by
absorbing the lower-order terms into the forcing and localizing with a cutoff
(`TauCeti.PDE.UniformlyEllipticOn.exists_lowerOrder_eq_restrictL`).

## Main declarations

* `TauCeti.PDE.energyFormH1_translate`: a translation moves from one argument of the energy form
  to the other and onto the coefficient field.
* `TauCeti.PDE.abs_energyFormH1_differenceQuotient_add_le`: discrete integration by parts for a
  Lipschitz coefficient field, up to an error bounded by the Lipschitz constant.
* `TauCeti.PDE.energyFormH1_differenceQuotient_eq_neg`: the exact discrete integration-by-parts
  identity for a constant coefficient matrix.
* `TauCeti.PDE.energyFormH1_differenceQuotient_eq_neg_sub`: the exact identity separating the
  translated energy form from its coefficient commutator.
* `TauCeti.PDE.norm_inv_mul_energyFormH1_comp_add_sub_le`: a uniform bound on that commutator.
* `TauCeti.PDE.UniformlyEllipticOn.norm_gradient_differenceQuotient_le_of_lipschitzWith`: the
  uniform bound on the difference quotients of the gradient of a weak solution.
* `TauCeti.PDE.UniformlyEllipticOn.norm_gradient_differenceQuotient_le_of_abs_energyFormH1_le`:
  the same bound when the forcing is a functional bounded on difference quotients.
* `TauCeti.PDE.UniformlyEllipticOn.exists_norm_le_hasWeakLineDerivOn_gradient_of_lipschitzWith`:
  the second-order weak directional derivatives of a weak solution, with the `H²` estimate.
* `TauCeti.PDE.UniformlyEllipticOn.exists_lowerOrder_eq_of_lipschitzWith`: a weak solution lies
  in `H²(ℝⁿ)`.
* `TauCeti.PDE.UniformlyEllipticOn.norm_gradient_differenceQuotient_le`,
  `TauCeti.PDE.UniformlyEllipticOn.exists_norm_le_hasWeakLineDerivOn_gradient`,
  `TauCeti.PDE.UniformlyEllipticOn.exists_lowerOrder_eq`: the same three statements for a constant
  coefficient matrix, which need only the lower ellipticity bound.

## References

* L. C. Evans, *Partial Differential Equations*, §6.3.1, Theorem 1 (interior `H²` regularity,
  whose proof handles the difference quotient of the coefficients in the same way).
* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Theorem 8.8 and Lemma 7.23.
-/
public section

noncomputable section

open MeasureTheory Set TopologicalSpace
open scoped ENNReal NNReal InnerProductSpace

namespace TauCeti

namespace PDE

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {mu : Measure (EuclideanSpace ℝ ι)}
  [mu.IsAddHaarMeasure] {A : Matrix ι ι ℝ} {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ}
  {lam Lam : ℝ} {K : ℝ≥0}

omit [DecidableEq ι] [mu.IsAddHaarMeasure] in
/-- A bounded coefficient field with continuously varying matrix bilinear forms, translated by
`s`, has an essentially bounded field of drift- and mass-free energy integrands. -/
private theorem memLp_energyIntegrand_comp_add
    (hbdd : Bornology.IsBounded (Set.range fun x => matrixBilinearForm (a x)))
    (ha : Continuous fun x => matrixBilinearForm (a x)) (s : EuclideanSpace ℝ ι) :
    MemLp (fun x => energyIntegrand (a (x + s))
      ((0 : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι) x) ((0 : EuclideanSpace ℝ ι → ℝ) x)) ⊤
      (mu.restrict ((⊤ : Opens (EuclideanSpace ℝ ι)) : Set (EuclideanSpace ℝ ι))) := by
  obtain ⟨C, hC⟩ := hbdd.exists_norm_le
  have hC' : ∀ x, ‖matrixBilinearForm (a x)‖ ≤ C := fun x => hC _ ⟨x, rfl⟩
  exact memLp_energyIntegrand_of_bounds (beta := 0) (gamma := 0)
    ((norm_nonneg (matrixBilinearForm (a 0))).trans (hC' 0))
    (Continuous.aestronglyMeasurable (β := ι → ι → ℝ) <| continuous_of_continuous_matrixBilinearForm
      (ha.comp (continuous_id.add continuous_const)))
    aestronglyMeasurable_const aestronglyMeasurable_const
    (fun x _ eta xi => by
      simpa [Real.norm_eq_abs] using
        (matrixBilinearForm (a (x + s))).le_of_opNorm₂_le_of_le (hC' _) le_rfl le_rfl)
    (fun _ _ => by simp) (fun _ _ => by simp)

omit [DecidableEq ι] in
/-- **Discrete integration by parts for a Lipschitz coefficient field.** Testing the difference
quotient of `u` against `v` is the same, up to sign, as testing `u` against the difference
quotient of `v` with the opposite step, with an error controlled by the Lipschitz constant `K` of
`x ↦ a(x)`:

`|a(Dᵗ u, v) + a(u, D⁻ᵗ v)| ≤ K ‖w‖ ‖∇u‖_{L²} ‖∇v‖_{L²}`.

The error is the energy form of the difference quotient of the coefficient field, which is
bounded by `K ‖w‖` uniformly in the step `t`. For a constant coefficient it vanishes
(`TauCeti.PDE.energyFormH1_differenceQuotient_eq_neg`). The coefficient field only has to be
bounded and Lipschitz, both measured in the operator norm of its matrix bilinear forms. -/
theorem abs_energyFormH1_differenceQuotient_add_le
    (hbdd : Bornology.IsBounded (Set.range fun x => matrixBilinearForm (a x)))
    (hK : LipschitzWith K fun x => matrixBilinearForm (a x)) (w : EuclideanSpace ℝ ι) (t : ℝ)
    (u v : W1p mu ⊤ 2) :
    |energyFormH1 a 0 0 (W1p.differenceQuotient le_rfl w t (Set.mapsTo_univ (· + t • w) _) u) v
        + energyFormH1 a 0 0 u
          (W1p.differenceQuotient le_rfl w (-t) (Set.mapsTo_univ (· + (-t) • w) _) v)|
      ≤ K * ‖w‖ * ‖W1p.gradient u‖ * ‖W1p.gradient v‖ := by
  have hcoeff := memLp_energyIntegrand_comp_add (mu := mu) hbdd hK.continuous 0
  simp only [add_zero] at hcoeff
  have hk : t • w + (-t) • w = 0 := by rw [← add_smul]; simp
  -- What survives is the change of the energy form under translating the coefficient field,
  -- tested against `u` and the translate `τ` of `v`.
  rw [energyFormH1_differenceQuotient_left (b := 0) (c := 0) hcoeff,
    energyFormH1_differenceQuotient_right (b := 0) (c := 0) hcoeff, energyFormH1_translate a hk]
  set τ := W1p.translate (Set.mapsTo_univ (· + (-t) • w) _) v
  rw [show ∀ X Y Z : ℝ, t⁻¹ * (X - Y) + (-t)⁻¹ * (Z - Y) = t⁻¹ * (X - Z) by
    intro X Y Z; rw [inv_neg]; ring]
  -- Translation preserves the `L²` norm of the gradient.
  have hτ : ‖W1p.gradient τ‖ = ‖W1p.gradient v‖ := by
    have : (mu.restrict ((⊤ : Opens (EuclideanSpace ℝ ι)) :
        Set (EuclideanSpace ℝ ι))).IsAddRightInvariant := by
      rw [Opens.coe_top, Measure.restrict_univ]
      infer_instance
    have heq : W1p.gradient τ = (mu.restrict ((⊤ : Opens (EuclideanSpace ℝ ι)) :
        Set (EuclideanSpace ℝ ι))).translateLp 2 ((-t) • w) (W1p.gradient v) :=
      Lp.ext ((W1p.gradient_translate_ae _ v).trans (Measure.coeFn_translateLp _ _).symm)
    rw [heq, LinearIsometryEquiv.norm_map]
  rcases eq_or_ne t 0 with rfl | ht
  · simp only [inv_zero, zero_mul, abs_zero]
    positivity
  rw [abs_mul, abs_inv]
  calc _ ≤ |t|⁻¹ * (K * ‖(-t) • w‖ * ‖W1p.gradient u‖ * ‖W1p.gradient τ‖) := by
        gcongr
        simpa only [Real.norm_eq_abs] using norm_energyFormH1_comp_add_sub_le hcoeff hK _ u τ
    _ = K * ‖w‖ * ‖W1p.gradient u‖ * ‖W1p.gradient v‖ := by
        rw [hτ, norm_smul, norm_neg, Real.norm_eq_abs]
        field_simp

omit [DecidableEq ι] in
/-- **Discrete integration by parts for the constant-coefficient energy form.** Testing the
difference quotient of `u` against `v` is the same, up to sign, as testing `u` against the
difference quotient of `v` with the opposite step:

`a(Dᵗ u, v) = -a(u, D⁻ᵗ v)`.

This is the integrated form of `∫ (Dᵗ g) h = -∫ g (D⁻ᵗ h)`, and it is what lets a
difference-quotient argument move the extra derivative onto the test function. -/
theorem energyFormH1_differenceQuotient_eq_neg (A : Matrix ι ι ℝ) (w : EuclideanSpace ℝ ι)
    (t : ℝ) (u v : W1p mu ⊤ 2) :
    energyFormH1 (fun _ => A) 0 0
        (W1p.differenceQuotient le_rfl w t (Set.mapsTo_univ (· + t • w) _) u) v
      = -energyFormH1 (fun _ => A) 0 0 u
        (W1p.differenceQuotient le_rfl w (-t) (Set.mapsTo_univ (· + (-t) • w) _) v) := by
  have h := energyFormH1_differenceQuotient_eq_neg_sub (mu := mu) (a := fun _ => A)
    (memLp_top_const (energyIntegrand A 0 0)) w t u v
  rwa [sub_self, mul_zero, sub_zero] at h

/-- **The difference-quotient energy estimate for a functional forcing.** Let `a` be uniformly
elliptic on the whole space with lower constant `λ`, and let `x ↦ a(x)` be `K`-Lipschitz in the
operator norm of its bilinear forms. Let `u ∈ H¹(ℝⁿ)` be such that the functional `v ↦ a(u, v)` is
bounded on the difference quotients in the direction `w`:

`|a(u, Dᵗ v)| ≤ M ‖∇v‖_{L²}` for every `v ∈ H¹(ℝⁿ)` and every step `t`.

Then `‖∇Dᵗ u‖_{L²} ≤ (M + K ‖w‖ ‖∇u‖_{L²}) / λ` for every step `t`.

For a weak solution of `-∂ⱼ(aⁱʲ ∂ᵢu) = f` with `f ∈ L²` the hypothesis holds with
`M = ‖w‖ ‖f‖_{L²}`, which is
`TauCeti.PDE.UniformlyEllipticOn.norm_gradient_differenceQuotient_le_of_lipschitzWith`. The
functional form also admits forcing terms in divergence form `-div F`, for which
`a(u, Dᵗ v) = ∫ ⟨F, ∇Dᵗ v⟩` is bounded by moving the difference quotient onto `F`. -/
theorem UniformlyEllipticOn.norm_gradient_differenceQuotient_le_of_abs_energyFormH1_le
    (ha : UniformlyEllipticOn univ a lam Lam)
    (hK : LipschitzWith K fun x => matrixBilinearForm (a x))
    {u : W1p mu ⊤ 2} (w : EuclideanSpace ℝ ι) {M : ℝ} (hM : 0 ≤ M)
    (hu : ∀ (t : ℝ) (v : W1p mu ⊤ 2), |energyFormH1 a 0 0 u
      (W1p.differenceQuotient le_rfl w t (Set.mapsTo_univ (· + t • w) _) v)|
        ≤ M * ‖W1p.gradient v‖)
    (t : ℝ) :
    ‖W1p.gradient (W1p.differenceQuotient le_rfl w t (Set.mapsTo_univ (· + t • w) _) u)‖
      ≤ (M + K * ‖w‖ * ‖W1p.gradient u‖) / lam := by
  have hlam := ha.pos
  have hbdd : Bornology.IsBounded (Set.range fun x => matrixBilinearForm (a x)) :=
    isBounded_iff_forall_norm_le.2 ⟨Lam, by
      rintro _ ⟨x, rfl⟩
      exact ha.opNorm_matrixBilinearForm_le (mem_univ x)⟩
  -- The discrete integration-by-parts estimate, with `Dᵗ u` in the second argument.
  have hDQ := abs_energyFormH1_differenceQuotient_add_le hbdd hK w t u
    (W1p.differenceQuotient le_rfl w t (Set.mapsTo_univ (· + t • w) _) u)
  obtain ⟨g, hg⟩ : ∃ g : W1p mu ⊤ 2,
      g = W1p.differenceQuotient le_rfl w t (Set.mapsTo_univ (· + t • w) _) u := ⟨_, rfl⟩
  rw [← hg] at hDQ ⊢
  -- Ellipticity bounds the Dirichlet energy of the difference quotient from below.
  have hlow : lam * ‖W1p.gradient g‖ ^ 2 ≤ energyFormH1 a 0 0 g g :=
    mul_norm_gradient_sq_le_energyFormH1_self_of_zero_drift (gamma := 0) ha
      (Continuous.aestronglyMeasurable (β := ι → ι → ℝ) <|
        continuous_of_continuous_matrixBilinearForm hK.continuous)
      aestronglyMeasurable_const (fun _ _ => rfl) (fun _ _ => by simp) (fun _ _ => le_rfl) g
  -- The hypothesis, tested against the reverse difference quotient of `Dᵗ u`.
  have hsol := hu (-t) g
  have hkey : lam * ‖W1p.gradient g‖ ^ 2
      ≤ (M + K * ‖w‖ * ‖W1p.gradient u‖) * ‖W1p.gradient g‖ := by
    have h1 := (abs_le.1 hDQ).2
    have h2 := (abs_le.1 hsol).1
    nlinarith
  rcases eq_or_lt_of_le (norm_nonneg (W1p.gradient g)) with hzero | hpos
  · rw [← hzero]
    exact div_nonneg (by positivity) hlam.le
  · rw [le_div_iff₀ hlam]
    nlinarith

/-- **The difference quotients of the gradient of a weak solution are uniformly bounded.** Let
`a` be uniformly elliptic on the whole space with lower constant `λ`, and let `x ↦ a(x)` be
`K`-Lipschitz in the operator norm of its bilinear forms. For a weak solution `u ∈ H¹(ℝⁿ)` of
`-∂ⱼ(aⁱʲ ∂ᵢu) = f`,

`‖∇Dᵗ u‖_{L²} ≤ ‖w‖ (‖f‖_{L²} + K ‖∇u‖_{L²}) / λ`

for every direction `w` and every step `t`, the bound being independent of `t`. Since
`∇Dᵗ u = Dᵗ ∇u`, this is the uniform difference-quotient bound on the gradient that the
difference-quotient criterion turns into a second weak derivative.

On the whole space `H¹₀(ℝⁿ) = H¹(ℝⁿ)`, so the hypothesis imposes no boundary condition; it is
exactly the weak equation tested against every `H¹(ℝⁿ)` function. -/
theorem UniformlyEllipticOn.norm_gradient_differenceQuotient_le_of_lipschitzWith
    (ha : UniformlyEllipticOn Set.univ a lam Lam)
    (hK : LipschitzWith K fun x => matrixBilinearForm (a x))
    {f : Lp ℝ 2 (mu.restrict ((⊤ : Opens (EuclideanSpace ℝ ι)) : Set (EuclideanSpace ℝ ι)))}
    {u : W1p0 mu ⊤ 2} (hu : IsWeakSolutionDirichlet a 0 0 f u)
    (w : EuclideanSpace ℝ ι) (t : ℝ) :
    ‖W1p.gradient (W1p.differenceQuotient le_rfl w t (Set.mapsTo_univ (· + t • w) _)
      (u : W1p mu ⊤ 2))‖ ≤ ‖w‖ * (‖f‖ + K * ‖W1p.gradient (u : W1p mu ⊤ 2)‖) / lam := by
  -- The weak equation and Cauchy--Schwarz bound the forcing on difference quotients.
  have hf : ∀ (s : ℝ) (v : W1p mu ⊤ 2), |energyFormH1 a 0 0 (u : W1p mu ⊤ 2)
      (W1p.differenceQuotient le_rfl w s (Set.mapsTo_univ (· + s • w) _) v)|
        ≤ ‖w‖ * ‖f‖ * ‖W1p.gradient v‖ := fun s v => by
    set v' := W1p.differenceQuotient le_rfl w s (Set.mapsTo_univ (· + s • w) _) v
    have h1 := (isWeakSolutionDirichlet_iff f u).mp hu
      ⟨v', W1p.mem_w1p0Submodule_top (by norm_num) v'⟩
    rw [← dirichletForcing_apply_eq_setIntegral, dirichletForcing_apply] at h1
    rw [h1, mul_comm ‖w‖, mul_assoc]
    exact (abs_real_inner_le_norm f _).trans
      (by gcongr; exact W1p.norm_value_differenceQuotient_le (by norm_num) w s v)
  have h := ha.norm_gradient_differenceQuotient_le_of_abs_energyFormH1_le hK w (by positivity)
    hf t
  rwa [mul_assoc (K : ℝ), mul_left_comm (K : ℝ), ← mul_add] at h

omit [DecidableEq ι] in
/-- **The difference quotients of the gradient of a weak solution are uniformly bounded.** For a
constant, uniformly elliptic `A` and a weak solution `u ∈ H¹(ℝⁿ)` of `-∂ⱼ(Aⁱʲ ∂ᵢu) = f`,

`‖∇Dᵗ u‖_{L²} ≤ ‖w‖ ‖f‖_{L²} / λ`

for every direction `w` and every step `t`. This is the case `K = 0` of
`TauCeti.PDE.UniformlyEllipticOn.norm_gradient_differenceQuotient_le_of_lipschitzWith`. -/
theorem UniformlyEllipticOn.norm_gradient_differenceQuotient_le
    (hlam : 0 < lam)
    (hA : ∀ ξ : EuclideanSpace ℝ ι, lam * ‖ξ‖ ^ 2 ≤ dotProduct ξ (Matrix.mulVec A ξ))
    {f : Lp ℝ 2 (mu.restrict ((⊤ : Opens (EuclideanSpace ℝ ι)) : Set (EuclideanSpace ℝ ι)))}
    {u : W1p0 mu ⊤ 2} (hu : IsWeakSolutionDirichlet (fun _ => A) 0 0 f u)
    (w : EuclideanSpace ℝ ι) (t : ℝ) :
    ‖W1p.gradient (W1p.differenceQuotient le_rfl w t (Set.mapsTo_univ (· + t • w) _)
      (u : W1p mu ⊤ 2))‖ ≤ ‖w‖ * ‖f‖ / lam := by
  classical
  simpa using
    (uniformlyEllipticOn_const univ hlam hA).norm_gradient_differenceQuotient_le_of_lipschitzWith
      (K := 0) (LipschitzWith.const _) hu w t

/-- **The second-order weak directional derivatives of a whole-space weak solution.** Let `a` be
uniformly elliptic on the whole space with lower constant `λ`, and let `x ↦ a(x)` be
`K`-Lipschitz in the operator norm of its bilinear forms. For a weak solution `u ∈ H¹(ℝⁿ)` of
`-∂ⱼ(aⁱʲ ∂ᵢu) = f`, the derivative `∂_y u = ⟪∇u, y⟫` is again weakly differentiable in every
direction `w`, with

`‖∂_w ∂_y u‖_{L²} ≤ ‖y‖ ‖w‖ (‖f‖_{L²} + K ‖∇u‖_{L²}) / λ`.

This is the `H²` estimate in quantitative, direction-by-direction form. -/
theorem UniformlyEllipticOn.exists_norm_le_hasWeakLineDerivOn_gradient_of_lipschitzWith
    (ha : UniformlyEllipticOn Set.univ a lam Lam)
    (hK : LipschitzWith K fun x => matrixBilinearForm (a x))
    {f : Lp ℝ 2 (mu.restrict ((⊤ : Opens (EuclideanSpace ℝ ι)) : Set (EuclideanSpace ℝ ι)))}
    {u : W1p0 mu ⊤ 2} (hu : IsWeakSolutionDirichlet a 0 0 f u)
    (y w : EuclideanSpace ℝ ι) :
    ∃ G : Lp ℝ 2 (mu.restrict ((⊤ : Opens (EuclideanSpace ℝ ι)) : Set (EuclideanSpace ℝ ι))),
      ‖G‖ ≤ ‖y‖ * (‖w‖ * (‖f‖ + K * ‖W1p.gradient (u : W1p mu ⊤ 2)‖) / lam) ∧
        HasWeakLineDerivOn mu ⊤
          (fun x => ⟪W1p.gradient (u : W1p mu ⊤ 2) x, y⟫_ℝ) G w := by
  exact W1p.exists_norm_le_hasWeakLineDerivOn_inner_gradient_of_norm_gradient_le
    (u : W1p mu ⊤ 2) w (ha.norm_gradient_differenceQuotient_le_of_lipschitzWith hK hu w) y

omit [DecidableEq ι] in
/-- **The second-order weak directional derivatives of a whole-space weak solution.** For a
constant, uniformly elliptic `A` and a weak solution `u ∈ H¹(ℝⁿ)` of `-∂ⱼ(Aⁱʲ ∂ᵢu) = f`, the
derivative `∂_y u = ⟪∇u, y⟫` is again weakly differentiable in every direction `w`, with

`‖∂_w ∂_y u‖_{L²} ≤ ‖y‖ ‖w‖ ‖f‖_{L²} / λ`.

Here `λ` is the ellipticity constant and no other feature of `A` enters the bound. This is the
case `K = 0` of
`TauCeti.PDE.UniformlyEllipticOn.exists_norm_le_hasWeakLineDerivOn_gradient_of_lipschitzWith`. -/
theorem UniformlyEllipticOn.exists_norm_le_hasWeakLineDerivOn_gradient
    (hlam : 0 < lam)
    (hA : ∀ ξ : EuclideanSpace ℝ ι, lam * ‖ξ‖ ^ 2 ≤ dotProduct ξ (Matrix.mulVec A ξ))
    {f : Lp ℝ 2 (mu.restrict ((⊤ : Opens (EuclideanSpace ℝ ι)) : Set (EuclideanSpace ℝ ι)))}
    {u : W1p0 mu ⊤ 2} (hu : IsWeakSolutionDirichlet (fun _ => A) 0 0 f u)
    (y w : EuclideanSpace ℝ ι) :
    ∃ G : Lp ℝ 2 (mu.restrict ((⊤ : Opens (EuclideanSpace ℝ ι)) : Set (EuclideanSpace ℝ ι))),
      ‖G‖ ≤ ‖y‖ * (‖w‖ * ‖f‖ / lam) ∧
        HasWeakLineDerivOn mu ⊤
          (fun x => ⟪W1p.gradient (u : W1p mu ⊤ 2) x, y⟫_ℝ) G w := by
  classical
  simpa using (uniformlyEllipticOn_const univ hlam hA)
    |>.exists_norm_le_hasWeakLineDerivOn_gradient_of_lipschitzWith (K := 0) (LipschitzWith.const _)
      hu y w

/-- **A whole-space weak solution with Lipschitz coefficients lies in `H²(ℝⁿ)`.** Let `a` be
uniformly elliptic on the whole space, with `x ↦ a(x)` Lipschitz in the operator norm of its
bilinear forms. A weak solution `u ∈ H¹(ℝⁿ)` of `-∂ⱼ(aⁱʲ ∂ᵢu) = f` with `f ∈ L²(ℝⁿ)` is the
first-order part of an element of `W^{2,2}(ℝⁿ)`: its weak gradient is again weakly
differentiable, with `L²` derivative. The quantitative form of the statement is
`TauCeti.PDE.UniformlyEllipticOn.exists_norm_le_hasWeakLineDerivOn_gradient_of_lipschitzWith`. -/
theorem UniformlyEllipticOn.exists_lowerOrder_eq_of_lipschitzWith
    (ha : UniformlyEllipticOn Set.univ a lam Lam)
    (hK : LipschitzWith K fun x => matrixBilinearForm (a x))
    {f : Lp ℝ 2 (mu.restrict ((⊤ : Opens (EuclideanSpace ℝ ι)) : Set (EuclideanSpace ℝ ι)))}
    {u : W1p0 mu ⊤ 2} (hu : IsWeakSolutionDirichlet a 0 0 f u) :
    ∃ U : Wkp mu ⊤ 2 2, Wkp.lowerOrder 1 U = (u : W1p mu ⊤ 2) :=
  W1p.exists_lowerOrder_eq_of_forall_hasWeakLineDerivOn _ (EuclideanSpace.basisFun ι ℝ)
    fun i j => by
      obtain ⟨G, -, hG⟩ := ha.exists_norm_le_hasWeakLineDerivOn_gradient_of_lipschitzWith hK hu
        (EuclideanSpace.basisFun ι ℝ j) (EuclideanSpace.basisFun ι ℝ i)
      exact ⟨G, hG⟩

omit [DecidableEq ι] in
/-- **A whole-space weak solution lies in `H²(ℝⁿ)`.** For a constant, uniformly elliptic `A`, a
weak solution `u ∈ H¹(ℝⁿ)` of `-∂ⱼ(Aⁱʲ ∂ᵢu) = f` with `f ∈ L²(ℝⁿ)` is the first-order part of an
element of `W^{2,2}(ℝⁿ)`. This is the constant-coefficient case of
`TauCeti.PDE.UniformlyEllipticOn.exists_lowerOrder_eq_of_lipschitzWith`; the quantitative form,
with the ellipticity constant made explicit, is
`TauCeti.PDE.UniformlyEllipticOn.exists_norm_le_hasWeakLineDerivOn_gradient`. -/
theorem UniformlyEllipticOn.exists_lowerOrder_eq
    (hlam : 0 < lam)
    (hA : ∀ ξ : EuclideanSpace ℝ ι, lam * ‖ξ‖ ^ 2 ≤ dotProduct ξ (Matrix.mulVec A ξ))
    {f : Lp ℝ 2 (mu.restrict ((⊤ : Opens (EuclideanSpace ℝ ι)) : Set (EuclideanSpace ℝ ι)))}
    {u : W1p0 mu ⊤ 2} (hu : IsWeakSolutionDirichlet (fun _ => A) 0 0 f u) :
    ∃ U : Wkp mu ⊤ 2 2, Wkp.lowerOrder 1 U = (u : W1p mu ⊤ 2) := by
  classical
  exact (uniformlyEllipticOn_const univ hlam hA).exists_lowerOrder_eq_of_lipschitzWith
    (K := 0) (LipschitzWith.const _) hu

end PDE

end TauCeti
