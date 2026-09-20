/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.DirichletProblem
public import TauCeti.Analysis.Sobolev.Wkp.SecondOrder
public import TauCeti.Analysis.Sobolev.W1p.DifferenceQuotient
import TauCeti.Analysis.Sobolev.DifferenceQuotient
import TauCeti.Analysis.Sobolev.W1p.Density

/-!
# `H²` regularity of whole-space weak solutions

Let `A` be a constant, uniformly elliptic coefficient matrix and let `u ∈ H¹(ℝⁿ)` be a weak
solution of the divergence-form equation

`-∂ⱼ(Aⁱʲ ∂ᵢu) = f` on `ℝⁿ`, with `f ∈ L²(ℝⁿ)`,

meaning `∫ ⟨A ∇u, ∇v⟩ = ∫ f v` for every `v ∈ H¹(ℝⁿ)`. This file proves that `u` then has
second-order weak derivatives in `L²(ℝⁿ)`, that is `u ∈ H²(ℝⁿ)`, with the estimate

`‖∂_w ∂_y u‖_{L²} ≤ ‖y‖ ‖w‖ ‖f‖_{L²} / λ`

in every pair of directions, where `λ` is the ellipticity constant. No smoothness of `f` and no
regularity of `u` beyond `H¹` is assumed: the ellipticity of the operator alone upgrades one
weak derivative to two.

## The difference-quotient method

The proof is the classical difference-quotient argument. For a direction `w` and a step `t`, the
difference quotient `Dᵗ u = t⁻¹ (u(· + t w) - u)` again lies in `H¹(ℝⁿ)`, and because `A` is
constant the energy form is *anti-adjoint* for it,

`a(Dᵗ u, v) = -a(u, D⁻ᵗ v)`

(`TauCeti.PDE.energyFormH1_differenceQuotient_eq_neg`), which is the integrated form of the
discrete integration-by-parts identity `∫ (Dᵗ g) h = -∫ g (D⁻ᵗ h)`. Testing the equation against
`Dᵗ u` itself and using ellipticity on the left and the difference-quotient bound
`‖D⁻ᵗ g‖_{L²} ≤ ‖w‖ ‖∇g‖_{L²}` on the right gives

`λ ‖∇Dᵗ u‖²_{L²} ≤ a(Dᵗ u, Dᵗ u) = -∫ f · D⁻ᵗ(Dᵗ u) ≤ ‖f‖_{L²} ‖w‖ ‖∇Dᵗ u‖_{L²}`,

so `‖Dᵗ ∇u‖_{L²} ≤ ‖w‖ ‖f‖_{L²} / λ` **uniformly in `t`**
(`TauCeti.PDE.UniformlyEllipticOn.norm_gradient_differenceQuotient_le`). The
difference-quotient criterion
`TauCeti.exists_norm_le_hasWeakLineDerivOn_of_frequently_eLpNorm_inv_mul_sub_le` converts that
uniform bound into a weak derivative of `∇u` in `L²`, and assembling the directions of an
orthonormal basis produces a weak Fréchet derivative of `∇u`, that is, the Hessian.

Working on the whole space is what keeps the argument free of cut-offs: no boundary regularity
is involved, `H¹₀(ℝⁿ) = H¹(ℝⁿ)` (`TauCeti.w1p0Submodule_top_eq_top`), so the solution concept
`TauCeti.PDE.IsWeakSolutionDirichlet` imposes no boundary condition here, and every difference
quotient is a legitimate test function. Localising the estimate to a subdomain, and allowing
variable Lipschitz coefficients, are the two steps that separate this from interior `H²`
regularity on a general domain.

## Main declarations

* `TauCeti.PDE.energyFormH1_translate`: a translation moves from one argument of the
  constant-coefficient energy form to the other.
* `TauCeti.PDE.energyFormH1_differenceQuotient_eq_neg`: the discrete integration-by-parts
  identity for the constant-coefficient energy form.
* `TauCeti.PDE.UniformlyEllipticOn.norm_gradient_differenceQuotient_le`: the uniform bound on
  the difference quotients of the gradient of a weak solution.
* `TauCeti.PDE.UniformlyEllipticOn.exists_norm_le_hasWeakLineDerivOn_gradient`: the second-order
  weak directional derivatives of a weak solution, with the `H²` estimate.
* `TauCeti.PDE.UniformlyEllipticOn.exists_lowerOrder_eq`: a weak solution lies in `H²(ℝⁿ)`.

## References

* L. C. Evans, *Partial Differential Equations*, §6.3.1, Theorem 1 (interior `H²` regularity).
* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  §8.3 and Lemma 7.23.
-/

public section

noncomputable section

open MeasureTheory Set TopologicalSpace
open scoped ENNReal InnerProductSpace

namespace TauCeti

namespace PDE

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {mu : Measure (EuclideanSpace ℝ ι)}
  [mu.IsAddHaarMeasure] {A : Matrix ι ι ℝ} {lam Lam : ℝ}

omit [DecidableEq ι] in
/-- With a constant coefficient matrix and no lower-order terms the energy form is the integral
of `⟨A ∇u, ∇v⟩`. -/
private theorem energyFormH1_const_eq_integral (A : Matrix ι ι ℝ) (u v : W1p mu ⊤ 2) :
    energyFormH1 (fun _ => A) 0 0 u v
      = ∫ x in ((⊤ : Opens (EuclideanSpace ℝ ι)) : Set (EuclideanSpace ℝ ι)),
          matrixBilinearForm A (W1p.gradient v x) (W1p.gradient u x) ∂mu := by
  rw [energyFormH1_def]
  simp

omit [DecidableEq ι] in
/-- **Translation moves across the constant-coefficient energy form.** For opposite vectors
`h` and `k`, translating the first argument by `h` is the same as translating the second by
`k`. This is the integrated form of the substitution `x ↦ x - h`, and it is where constancy of
the coefficient matrix is used. -/
theorem energyFormH1_translate (A : Matrix ι ι ℝ) {h k : EuclideanSpace ℝ ι} (hk : h + k = 0)
    (u v : W1p mu ⊤ 2) :
    energyFormH1 (fun _ => A) 0 0 (W1p.translate (Set.mapsTo_univ (· + h) _) u) v
      = energyFormH1 (fun _ => A) 0 0 u (W1p.translate (Set.mapsTo_univ (· + k) _) v) := by
  rw [energyFormH1_const_eq_integral, energyFormH1_const_eq_integral]
  -- Translation invariance of the Haar measure, on an arbitrary integrand.
  have hinv : ∀ F : EuclideanSpace ℝ ι → ℝ,
      ∫ x in ((⊤ : Opens (EuclideanSpace ℝ ι)) : Set (EuclideanSpace ℝ ι)), F (x + h) ∂mu
        = ∫ x in ((⊤ : Opens (EuclideanSpace ℝ ι)) : Set (EuclideanSpace ℝ ι)), F x ∂mu := by
    intro F
    simp only [Opens.coe_top, Measure.restrict_univ]
    exact integral_add_right_eq_self F h
  have hcancel : ∀ x : EuclideanSpace ℝ ι, x + h + k = x := fun x => by
    rw [add_assoc, hk, add_zero]
  calc ∫ x in ((⊤ : Opens (EuclideanSpace ℝ ι)) : Set (EuclideanSpace ℝ ι)),
        matrixBilinearForm A (W1p.gradient v x)
          (W1p.gradient (W1p.translate (Set.mapsTo_univ (· + h) _) u) x) ∂mu
      = ∫ x in ((⊤ : Opens (EuclideanSpace ℝ ι)) : Set (EuclideanSpace ℝ ι)),
          matrixBilinearForm A (W1p.gradient v (x + h + k))
            (W1p.gradient u (x + h)) ∂mu := by
        refine integral_congr_ae ?_
        filter_upwards [W1p.gradient_translate_ae (Set.mapsTo_univ (· + h) _) u] with x hx
        rw [hx, hcancel]
    _ = ∫ x in ((⊤ : Opens (EuclideanSpace ℝ ι)) : Set (EuclideanSpace ℝ ι)),
          matrixBilinearForm A (W1p.gradient v (x + k)) (W1p.gradient u x) ∂mu :=
        hinv fun y => matrixBilinearForm A (W1p.gradient v (y + k)) (W1p.gradient u y)
    _ = ∫ x in ((⊤ : Opens (EuclideanSpace ℝ ι)) : Set (EuclideanSpace ℝ ι)),
          matrixBilinearForm A (W1p.gradient (W1p.translate (Set.mapsTo_univ (· + k) _) v) x)
            (W1p.gradient u x) ∂mu := by
        refine integral_congr_ae ?_
        filter_upwards [W1p.gradient_translate_ae (Set.mapsTo_univ (· + k) _) v] with x hx
        rw [hx]

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
  have hcoeff : MemLp (fun x => energyIntegrand ((fun _ => A) x)
      ((0 : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι) x) ((0 : EuclideanSpace ℝ ι → ℝ) x)) ⊤
      (mu.restrict ((⊤ : Opens (EuclideanSpace ℝ ι)) : Set (EuclideanSpace ℝ ι))) := by
    simpa using memLp_top_const (α := EuclideanSpace ℝ ι)
      (μ := mu.restrict ((⊤ : Opens (EuclideanSpace ℝ ι)) : Set (EuclideanSpace ℝ ι)))
      (energyIntegrand A 0 0)
  -- Both arguments of the energy form are linear, so a difference quotient splits.
  have hsubl : ∀ x y z : W1p mu ⊤ 2, energyFormH1 (fun _ => A) 0 0 (x - y) z
      = energyFormH1 (fun _ => A) 0 0 x z - energyFormH1 (fun _ => A) 0 0 y z := by
    intro x y z
    rw [sub_eq_add_neg, energyFormH1_add_left hcoeff, ← neg_one_smul ℝ y,
      energyFormH1_smul_left]
    ring
  have hsubr : ∀ x y z : W1p mu ⊤ 2, energyFormH1 (fun _ => A) 0 0 x (y - z)
      = energyFormH1 (fun _ => A) 0 0 x y - energyFormH1 (fun _ => A) 0 0 x z := by
    intro x y z
    rw [sub_eq_add_neg, energyFormH1_add_right hcoeff, ← neg_one_smul ℝ z,
      energyFormH1_smul_right]
    ring
  have hleft : ∀ (s : ℝ) (hs : MapsTo (· + s • w)
      ((⊤ : Opens (EuclideanSpace ℝ ι)) : Set (EuclideanSpace ℝ ι))
      ((⊤ : Opens (EuclideanSpace ℝ ι)) : Set (EuclideanSpace ℝ ι))) (x y : W1p mu ⊤ 2),
      energyFormH1 (fun _ => A) 0 0 (W1p.differenceQuotient le_rfl w s hs x) y
        = s⁻¹ * (energyFormH1 (fun _ => A) 0 0 (W1p.translate hs x) y
            - energyFormH1 (fun _ => A) 0 0 x y) := by
    intro s hs x y
    rw [W1p.differenceQuotient_def, energyFormH1_smul_left, hsubl, W1p.restrictL_self]
  have hright : ∀ (s : ℝ) (hs : MapsTo (· + s • w)
      ((⊤ : Opens (EuclideanSpace ℝ ι)) : Set (EuclideanSpace ℝ ι))
      ((⊤ : Opens (EuclideanSpace ℝ ι)) : Set (EuclideanSpace ℝ ι))) (x y : W1p mu ⊤ 2),
      energyFormH1 (fun _ => A) 0 0 x (W1p.differenceQuotient le_rfl w s hs y)
        = s⁻¹ * (energyFormH1 (fun _ => A) 0 0 x (W1p.translate hs y)
            - energyFormH1 (fun _ => A) 0 0 x y) := by
    intro s hs x y
    rw [W1p.differenceQuotient_def, energyFormH1_smul_right, hsubr, W1p.restrictL_self]
  have hk : t • w + (-t) • w = 0 := by rw [← add_smul]; simp
  rw [hleft, hright, energyFormH1_translate A hk, inv_neg]
  ring

/-- **The difference quotients of the gradient of a weak solution are uniformly bounded.** For a
constant, uniformly elliptic `A` and a weak solution `u ∈ H¹(ℝⁿ)` of `-∂ⱼ(Aⁱʲ ∂ᵢu) = f`,

`‖∇Dᵗ u‖_{L²} ≤ ‖w‖ ‖f‖_{L²} / λ`

for every direction `w` and every step `t`, the bound being independent of `t`. Since
`∇Dᵗ u = Dᵗ ∇u`, this is the uniform difference-quotient bound on the gradient that the
difference-quotient criterion turns into a second weak derivative.

On the whole space `H¹₀(ℝⁿ) = H¹(ℝⁿ)`, so the hypothesis imposes no boundary condition; it is
exactly the weak equation tested against every `H¹(ℝⁿ)` function. -/
theorem UniformlyEllipticOn.norm_gradient_differenceQuotient_le
    (hA : UniformlyEllipticOn ((⊤ : Opens (EuclideanSpace ℝ ι)) : Set (EuclideanSpace ℝ ι))
      (fun _ => A) lam Lam)
    {f : Lp ℝ 2 (mu.restrict ((⊤ : Opens (EuclideanSpace ℝ ι)) : Set (EuclideanSpace ℝ ι)))}
    {u : W1p0 mu ⊤ 2} (hu : IsWeakSolutionDirichlet (fun _ => A) 0 0 f u)
    (w : EuclideanSpace ℝ ι) (t : ℝ) :
    ‖W1p.gradient (W1p.differenceQuotient le_rfl w t (Set.mapsTo_univ (· + t • w) _)
      (u : W1p mu ⊤ 2))‖ ≤ ‖w‖ * ‖f‖ / lam := by
  have hlam := hA.pos
  -- The discrete integration-by-parts identity, before naming the difference quotients.
  have hDQ := energyFormH1_differenceQuotient_eq_neg A w t (u : W1p mu ⊤ 2)
    (W1p.differenceQuotient le_rfl w t (Set.mapsTo_univ (· + t • w) _) (u : W1p mu ⊤ 2))
  set g := W1p.differenceQuotient le_rfl w t (Set.mapsTo_univ (· + t • w) _) (u : W1p mu ⊤ 2)
  set v := W1p.differenceQuotient le_rfl w (-t) (Set.mapsTo_univ (· + (-t) • w) _) g
  -- Ellipticity bounds the Dirichlet energy of the difference quotient from below.
  have hlow : lam * ‖W1p.gradient g‖ ^ 2 ≤ energyFormH1 (fun _ => A) 0 0 g g :=
    mul_norm_gradient_sq_le_energyFormH1_self_of_zero_drift (gamma := 0) hA
      aestronglyMeasurable_const aestronglyMeasurable_const (fun _ _ => rfl)
      (fun _ _ => by simp) (fun _ _ => le_rfl) g
  -- The weak equation, tested against the reverse difference quotient of `Dᵗ u`.
  have hv0 : v ∈ w1p0Submodule mu ⊤ 2 := W1p.mem_w1p0Submodule_top (by norm_num) v
  have hsol : energyFormH1 (fun _ => A) 0 0 (u : W1p mu ⊤ 2) v = ⟪f, W1p.value v⟫_ℝ := by
    have h1 := (isWeakSolutionDirichlet_iff f u).mp hu ⟨v, hv0⟩
    rw [← dirichletForcing_apply_eq_setIntegral, dirichletForcing_apply] at h1
    exact h1
  rw [hsol] at hDQ
  -- Cauchy--Schwarz and the difference-quotient bound on the value.
  have hdq : ‖W1p.value v‖ ≤ ‖w‖ * ‖W1p.gradient g‖ :=
    W1p.norm_value_differenceQuotient_le (by norm_num) w (-t) g
  have hkey : lam * ‖W1p.gradient g‖ ^ 2 ≤ ‖f‖ * (‖w‖ * ‖W1p.gradient g‖) := by
    refine hlow.trans (hDQ.le.trans ?_)
    refine ((neg_le_abs _).trans (abs_real_inner_le_norm f _)).trans ?_
    gcongr
  rcases eq_or_lt_of_le (norm_nonneg (W1p.gradient g)) with hzero | hpos
  · rw [← hzero]
    exact div_nonneg (by positivity) hlam.le
  · rw [le_div_iff₀ hlam]
    nlinarith

/-- **The second-order weak directional derivatives of a whole-space weak solution.** For a
constant, uniformly elliptic `A` and a weak solution `u ∈ H¹(ℝⁿ)` of `-∂ⱼ(Aⁱʲ ∂ᵢu) = f`, the
derivative `∂_y u = ⟪∇u, y⟫` is again weakly differentiable in every direction `w`, with

`‖∂_w ∂_y u‖_{L²} ≤ ‖y‖ ‖w‖ ‖f‖_{L²} / λ`.

This is the `H²` estimate in its sharp, direction-by-direction form; `λ` is the ellipticity
constant and no other feature of `A` enters. -/
theorem UniformlyEllipticOn.exists_norm_le_hasWeakLineDerivOn_gradient
    (hA : UniformlyEllipticOn ((⊤ : Opens (EuclideanSpace ℝ ι)) : Set (EuclideanSpace ℝ ι))
      (fun _ => A) lam Lam)
    {f : Lp ℝ 2 (mu.restrict ((⊤ : Opens (EuclideanSpace ℝ ι)) : Set (EuclideanSpace ℝ ι)))}
    {u : W1p0 mu ⊤ 2} (hu : IsWeakSolutionDirichlet (fun _ => A) 0 0 f u)
    (y w : EuclideanSpace ℝ ι) :
    ∃ G : Lp ℝ 2 (mu.restrict ((⊤ : Opens (EuclideanSpace ℝ ι)) : Set (EuclideanSpace ℝ ι))),
      ‖G‖ ≤ ‖y‖ * (‖w‖ * ‖f‖ / lam) ∧
        HasWeakLineDerivOn mu ⊤
          (fun x => ⟪W1p.gradient (u : W1p mu ⊤ 2) x, y⟫_ℝ) G w := by
  have hlam := hA.pos
  have hloc : LocallyIntegrableOn
      (fun x => ⟪W1p.gradient (u : W1p mu ⊤ 2) x, y⟫_ℝ)
      ((⊤ : Opens (EuclideanSpace ℝ ι)) : Set (EuclideanSpace ℝ ι)) mu := by
    simpa using
      ((W1p.hasWeakFDerivOn (u : W1p mu ⊤ 2)).hasWeakLineDerivOn y).locallyIntegrableOn_deriv
  -- The uniform bound on the difference quotients of `∂_y u`, on the whole space.
  have hglobal : ∀ t : ℝ, eLpNorm
      (fun x => t⁻¹ * (⟪W1p.gradient (u : W1p mu ⊤ 2) (x + t • w), y⟫_ℝ
        - ⟪W1p.gradient (u : W1p mu ⊤ 2) x, y⟫_ℝ)) 2
      (mu.restrict ((⊤ : Opens (EuclideanSpace ℝ ι)) : Set (EuclideanSpace ℝ ι)))
      ≤ ENNReal.ofReal (‖y‖ * (‖w‖ * ‖f‖ / lam)) := by
    intro t
    set g := W1p.differenceQuotient le_rfl w t (Set.mapsTo_univ (· + t • w) _) (u : W1p mu ⊤ 2)
    have hae : (fun x => t⁻¹ * (⟪W1p.gradient (u : W1p mu ⊤ 2) (x + t • w), y⟫_ℝ
          - ⟪W1p.gradient (u : W1p mu ⊤ 2) x, y⟫_ℝ))
        =ᵐ[mu.restrict ((⊤ : Opens (EuclideanSpace ℝ ι)) : Set (EuclideanSpace ℝ ι))]
          fun x => ⟪W1p.gradient g x, y⟫_ℝ := by
      filter_upwards [W1p.gradient_differenceQuotient_ae le_rfl w t (Set.mapsTo_univ (· + t • w) _)
        (u : W1p mu ⊤ 2)] with x hx
      rw [hx, inner_smul_left, inner_sub_left]
      simp [mul_sub]
    rw [eLpNorm_congr_ae hae]
    calc eLpNorm (fun x => ⟪W1p.gradient g x, y⟫_ℝ) 2
          (mu.restrict ((⊤ : Opens (EuclideanSpace ℝ ι)) : Set (EuclideanSpace ℝ ι)))
        ≤ eLpNorm (‖y‖ • (W1p.gradient g : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι)) 2
            (mu.restrict ((⊤ : Opens (EuclideanSpace ℝ ι)) : Set (EuclideanSpace ℝ ι))) :=
          eLpNorm_mono_ae (Filter.Eventually.of_forall fun x => by
            rw [Pi.smul_apply, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_norm, mul_comm]
            exact abs_real_inner_le_norm _ y)
      _ = ‖y‖ₑ * eLpNorm (W1p.gradient g : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι) 2
            (mu.restrict ((⊤ : Opens (EuclideanSpace ℝ ι)) : Set (EuclideanSpace ℝ ι))) := by
          rw [eLpNorm_const_smul, enorm_norm]
      _ = ‖y‖ₑ * ENNReal.ofReal ‖W1p.gradient g‖ := by
          rw [Lp.norm_def, ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top _)]
      _ ≤ ‖y‖ₑ * ENNReal.ofReal (‖w‖ * ‖f‖ / lam) := by
          gcongr
          exact hA.norm_gradient_differenceQuotient_le hu w t
      _ = ENNReal.ofReal (‖y‖ * (‖w‖ * ‖f‖ / lam)) := by
          rw [← ofReal_norm, ← ENNReal.ofReal_mul (norm_nonneg y)]
  refine exists_norm_le_hasWeakLineDerivOn_of_frequently_eLpNorm_inv_mul_sub_le hloc w
    (by positivity) fun K hK _ => Filter.Eventually.frequently ?_
  filter_upwards with t
  exact le_trans (eLpNorm_mono_measure _ (Measure.restrict_mono hK le_rfl)) (hglobal t)

/-- **A whole-space weak solution lies in `H²(ℝⁿ)`.** For a constant, uniformly elliptic `A`, a
weak solution `u ∈ H¹(ℝⁿ)` of `-∂ⱼ(Aⁱʲ ∂ᵢu) = f` with `f ∈ L²(ℝⁿ)` is the first-order part of an
element of `W^{2,2}(ℝⁿ)`: its weak gradient is again weakly differentiable, with `L²` derivative.
The quantitative form of the statement, with the ellipticity constant made explicit, is
`TauCeti.PDE.UniformlyEllipticOn.exists_norm_le_hasWeakLineDerivOn_gradient`. -/
theorem UniformlyEllipticOn.exists_lowerOrder_eq
    (hA : UniformlyEllipticOn ((⊤ : Opens (EuclideanSpace ℝ ι)) : Set (EuclideanSpace ℝ ι))
      (fun _ => A) lam Lam)
    {f : Lp ℝ 2 (mu.restrict ((⊤ : Opens (EuclideanSpace ℝ ι)) : Set (EuclideanSpace ℝ ι)))}
    {u : W1p0 mu ⊤ 2} (hu : IsWeakSolutionDirichlet (fun _ => A) 0 0 f u) :
    ∃ U : Wkp mu ⊤ 2 2, Wkp.lowerOrder 1 U = (u : W1p mu ⊤ 2) :=
  Wkp.exists_lowerOrder_eq_of_forall_hasWeakLineDerivOn (EuclideanSpace.basisFun ι ℝ) _
    fun i j => by
      obtain ⟨G, -, hG⟩ := hA.exists_norm_le_hasWeakLineDerivOn_gradient hu
        (EuclideanSpace.basisFun ι ℝ j) (EuclideanSpace.basisFun ι ℝ i)
      exact ⟨G, hG⟩

end PDE

end TauCeti
