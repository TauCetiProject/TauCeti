/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.DirichletProblem
public import TauCeti.Analysis.Sobolev.Wkp.LineDeriv
public import TauCeti.Analysis.PDE.EnergyForm.DifferenceQuotient
public import TauCeti.Analysis.PDE.EnergyForm.Restriction
import TauCeti.Analysis.Sobolev.DifferenceQuotient
import TauCeti.Analysis.Sobolev.W1p.Density

/-!
# `H²` regularity of whole-space weak solutions, and tangential regularity

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

The same argument runs on any open `Ω` that every translation along `w` maps onto itself, such as
a half-space and a direction `w` parallel to its boundary, for a solution `u ∈ H¹₀(Ω)` of the
Dirichlet problem. The difference quotients of `u` along `w` stay in `H¹₀(Ω)`, and translation
preserves the restricted measure on `Ω`, so discrete integration by parts applies directly on
that domain. This bounds `∂_w ∇u` in `L²(Ω)` up to the boundary, the tangential half of
boundary `H²` regularity; the whole-space statements are the case `Ω = ℝⁿ`.

In the whole-space case `Ω = ℝⁿ` the argument needs neither cut-offs nor the extension by zero:
no boundary regularity is involved, `H¹₀(ℝⁿ) = H¹(ℝⁿ)` (`TauCeti.w1p0Submodule_top_eq_top`), so
the solution concept `TauCeti.PDE.IsWeakSolutionDirichlet` imposes no boundary condition there,
and every difference quotient is a legitimate test function. For a constant principal
coefficient and bounded measurable lower-order coefficients, interior `H²` regularity on a general
domain follows by absorbing the lower-order terms into the forcing and localizing with a cutoff
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
* `TauCeti.PDE.UniformlyEllipticOn.norm_gradient_differenceQuotient_le_of_lipschitzOnWith_of_mapsTo`
  and
  `UniformlyEllipticOn.exists_norm_le_hasWeakLineDerivOn_gradient_of_lipschitzOnWith_of_mapsTo`:
  the uniform difference-quotient bound and the second-order weak derivatives along `w`, for the
  Dirichlet problem on a domain mapped onto itself by the translations along `w`.
* `TauCeti.PDE.UniformlyEllipticOn.norm_gradient_differenceQuotient_le_of_lipschitzWith`: the
  uniform bound on the difference quotients of the gradient of a weak solution.
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
  whose proof handles the difference quotient of the coefficients in the same way), and §6.3.2,
  Theorem 4 (boundary `H²` regularity, whose first step is the tangential estimate).
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

omit [DecidableEq ι] in
/-- **Discrete integration by parts for a Lipschitz coefficient field.** Testing the difference
quotient of `u` against `v` is the same, up to sign, as testing `u` against the difference
quotient of `v` with the opposite step, with an error controlled by the Lipschitz constant `K` of
`x ↦ a(x)`:

`|a(Dᵗ u, v) + a(u, D⁻ᵗ v)| ≤ K ‖w‖ ‖∇u‖_{L²} ‖∇v‖_{L²}`.

The error is the energy form of the difference quotient of the coefficient field, which is
bounded by `K ‖w‖` uniformly in the step `t`. For a constant coefficient it vanishes
(`TauCeti.PDE.energyFormH1_differenceQuotient_eq_neg`). The coefficient field needs essentially
bounded energy densities on the invariant domain and
Lipschitz bilinear forms there; its values outside the domain are unrestricted. -/
theorem abs_energyFormH1_differenceQuotient_add_le
    {Omega : Opens (EuclideanSpace ℝ ι)} {w : EuclideanSpace ℝ ι}
    (hw : ∀ t : ℝ, MapsTo (· + t • w) Omega Omega)
    (hcoeff : MemLp (fun x => energyIntegrand (a x) 0 0) ⊤ (mu.restrict Omega))
    (hK : LipschitzOnWith K (fun x => matrixBilinearForm (a x)) Omega) (t : ℝ)
    (u v : W1p mu Omega 2) :
    |energyFormH1 a 0 0 (W1p.differenceQuotient le_rfl w t (hw t) u) v
        + energyFormH1 a 0 0 u
          (W1p.differenceQuotient le_rfl w (-t) (hw (-t)) v)|
      ≤ K * ‖w‖ * ‖W1p.gradient u‖ * ‖W1p.gradient v‖ := by
  have hOmega : ∀ s : ℝ, (Omega : Set (EuclideanSpace ℝ ι)) =
      (· + s • w) ⁻¹' Omega := fun s => Set.ext fun x =>
    ⟨fun hx => hw s hx, fun hx => by
      simpa [neg_smul, add_assoc] using hw (-s) hx⟩
  have hk : t • w + (-t) • w = 0 := by rw [← add_smul]; simp
  -- What survives is the change of the energy form under translating the coefficient field,
  -- tested against `u` and the translate `τ` of `v`.
  rw [energyFormH1_differenceQuotient_left (b := 0) (c := 0) hcoeff,
    energyFormH1_differenceQuotient_right (b := 0) (c := 0) hcoeff,
    energyFormH1_translate a hk (hOmega t) (hh := hw t) (hkOmega := hw (-t))]
  set τ := W1p.translate (hw (-t)) v
  rw [show ∀ X Y Z : ℝ, t⁻¹ * (X - Y) + (-t)⁻¹ * (Z - Y) = t⁻¹ * (X - Z) by
    intro X Y Z; rw [inv_neg]; ring]
  -- Translation preserves the `L²` norm of the gradient.
  have hτ : ‖W1p.gradient τ‖ = ‖W1p.gradient v‖ := by
    have hres : MeasurePreserving (· + (-t) • w)
        (mu.restrict Omega) (mu.restrict Omega) :=
      by simpa only [← hOmega (-t)] using
        (measurePreserving_add_right mu ((-t) • w)).restrict_preimage Omega.isOpen.measurableSet
    have heq : W1p.gradient τ =
        Lp.compMeasurePreserving (· + (-t) • w) hres (W1p.gradient v) :=
      Lp.ext ((W1p.gradient_translate_ae _ v).trans
        (Lp.coeFn_compMeasurePreserving _ _).symm)
    rw [heq, Lp.norm_compMeasurePreserving]
  rcases eq_or_ne t 0 with rfl | ht
  · simp only [inv_zero, zero_mul, abs_zero]
    positivity
  rw [abs_mul, abs_inv]
  calc _ ≤ |t|⁻¹ * (K * ‖(-t) • w‖ * ‖W1p.gradient u‖ * ‖W1p.gradient τ‖) := by
        gcongr
        simpa only [Real.norm_eq_abs] using
          norm_energyFormH1_comp_add_sub_le hcoeff hK _ (hOmega (-t)) u τ
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

/-- **The tangential difference quotients of the gradient of a weak solution are uniformly
bounded.** Let `Ω` be mapped onto itself by every translation along `w`, as a half-space is by
every translation parallel to its boundary. Let `a` be uniformly elliptic on `Ω` with lower
constant `λ`, and let its bilinear forms be `K`-Lipschitz on `Ω` in the operator norm. For a weak
solution `u ∈ H¹₀(Ω)` of `-∂ⱼ(aⁱʲ ∂ᵢu) = f` with `u = 0` on `∂Ω`,

`‖∇Dᵗ u‖_{L²(Ω)} ≤ ‖w‖ (‖f‖_{L²(Ω)} + K ‖∇u‖_{L²(Ω)}) / λ`

for every step `t`, the bound being independent of `t`. No regularity of `∂Ω` is assumed. Only
the values of `a` on `Ω` enter the hypotheses; no conditions are imposed outside the domain. -/
theorem UniformlyEllipticOn.norm_gradient_differenceQuotient_le_of_lipschitzOnWith_of_mapsTo
    {Omega : Opens (EuclideanSpace ℝ ι)} {w : EuclideanSpace ℝ ι}
    (hw : ∀ t : ℝ, MapsTo (· + t • w) Omega Omega)
    (ha : UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam)
    (hK : LipschitzOnWith K (fun x => matrixBilinearForm (a x)) Omega)
    {f : Lp ℝ 2 (mu.restrict Omega)} {u : W1p0 mu Omega 2}
    (hu : IsWeakSolutionDirichlet a 0 0 f u) (t : ℝ) :
    ‖W1p.gradient (W1p.differenceQuotient le_rfl w t (hw t) (u : W1p mu Omega 2))‖ ≤
      ‖w‖ * (‖f‖ + K * ‖W1p.gradient (u : W1p mu Omega 2)‖) / lam := by
  have hlam := ha.pos
  letI : TopologicalSpace.PseudoMetrizableSpace (Matrix ι ι ℝ) :=
    inferInstanceAs (TopologicalSpace.PseudoMetrizableSpace (ι → ι → ℝ))
  have hmeas : AEStronglyMeasurable a (mu.restrict Omega) :=
    (continuousOn_of_continuousOn_matrixBilinearForm hK.continuousOn).aestronglyMeasurable
      Omega.isOpen.measurableSet
  have hcoeff : MemLp (fun x => energyIntegrand (a x) 0 0) ⊤ (mu.restrict Omega) :=
    memLp_energyIntegrand_of_bounds (beta := 0) (gamma := 0) ha.upper_nonneg hmeas
      aestronglyMeasurable_const aestronglyMeasurable_const
      (fun x hx => ha.upper_bound hx) (fun _ _ => by simp) (fun _ _ => by simp)
  have hrev : ∀ s : ℝ, ∀ x, x + s • w ∈ Omega → x ∈ Omega := fun s x hx => by
    simpa [neg_smul, add_assoc] using hw (-s) hx
  -- The difference quotient `g = Dᵗ u` and the test function `v = D⁻ᵗ g`, both in `H¹₀(Ω)`.
  obtain ⟨g, hg0⟩ : ∃ g : W1p0 mu Omega 2,
      (g : W1p mu Omega 2) = W1p.differenceQuotient le_rfl w t (hw t) (u : W1p mu Omega 2) :=
    ⟨⟨_, W1p.differenceQuotient_mem_w1p0Submodule (by norm_num) (hw t) (hrev t) u.2⟩, rfl⟩
  obtain ⟨v, hv0⟩ : ∃ v : W1p0 mu Omega 2,
      (v : W1p mu Omega 2) = W1p.differenceQuotient le_rfl w (-t) (hw (-t)) (g : W1p mu Omega 2) :=
    ⟨⟨_, W1p.differenceQuotient_mem_w1p0Submodule (by norm_num) (hw (-t)) (hrev (-t)) g.2⟩, rfl⟩
  -- Discrete integration by parts is performed on the invariant domain itself.
  have hDQ := abs_energyFormH1_differenceQuotient_add_le hw hcoeff hK t
    (u : W1p mu Omega 2) (g : W1p mu Omega 2)
  rw [← hg0, ← hv0] at hDQ
  -- Ellipticity on `Ω` bounds the Dirichlet energy of the difference quotient from below.
  have hlow : lam * ‖W1p.gradient (g : W1p mu Omega 2)‖ ^ 2 ≤
      energyFormH1 a 0 0 (g : W1p mu Omega 2) (g : W1p mu Omega 2) :=
    mul_norm_gradient_sq_le_energyFormH1_self_of_zero_drift (gamma := 0) ha
      hmeas
      aestronglyMeasurable_const (fun _ _ => rfl) (fun _ _ => by simp) (fun _ _ => le_rfl) _
  -- The weak equation, tested against `v`.
  have hsol : energyFormH1 a 0 0 (u : W1p mu Omega 2) (v : W1p mu Omega 2) =
      ⟪f, W1p.value (v : W1p mu Omega 2)⟫_ℝ := by
    have h1 := (isWeakSolutionDirichlet_iff f u).mp hu v
    rwa [← dirichletForcing_apply_eq_setIntegral, dirichletForcing_apply] at h1
  -- Cauchy--Schwarz and the difference-quotient bound on the value.
  have hdq : ‖W1p.value (v : W1p mu Omega 2)‖ ≤ ‖w‖ * ‖W1p.gradient (g : W1p mu Omega 2)‖ :=
    hv0 ▸ W1p0.norm_value_differenceQuotient_le (by norm_num) (hw (-t)) (hrev (-t)) g
  have hf : |⟪f, W1p.value (v : W1p mu Omega 2)⟫_ℝ| ≤
      ‖f‖ * (‖w‖ * ‖W1p.gradient (g : W1p mu Omega 2)‖) :=
    (abs_real_inner_le_norm f _).trans (by gcongr)
  have hkey : lam * ‖W1p.gradient (g : W1p mu Omega 2)‖ ^ 2 ≤
      ‖w‖ * (‖f‖ + K * ‖W1p.gradient (u : W1p mu Omega 2)‖) *
        ‖W1p.gradient (g : W1p mu Omega 2)‖ := by
    have h1 := (abs_le.1 hDQ).2
    have h2 := (abs_le.1 hf).1
    rw [hsol] at h1
    linarith
  rw [← hg0]
  rcases eq_or_lt_of_le (norm_nonneg (W1p.gradient (g : W1p mu Omega 2))) with hzero | hpos
  · rw [← hzero]
    exact div_nonneg (by positivity) hlam.le
  · rw [le_div_iff₀ hlam]
    exact le_of_mul_le_mul_right (by linarith) hpos

/-- **The difference quotients of the gradient of a weak solution are uniformly bounded.** Let
`a` be uniformly elliptic on the whole space with lower constant `λ`, and let `x ↦ a(x)` be
`K`-Lipschitz in the operator norm of its bilinear forms. For a weak solution `u ∈ H¹(ℝⁿ)` of
`-∂ⱼ(aⁱʲ ∂ᵢu) = f`,

`‖∇Dᵗ u‖_{L²} ≤ ‖w‖ (‖f‖_{L²} + K ‖∇u‖_{L²}) / λ`

for every direction `w` and every step `t`, the bound being independent of `t`. Since
`∇Dᵗ u = Dᵗ ∇u`, this is the uniform difference-quotient bound on the gradient that the
difference-quotient criterion turns into a second weak derivative.

On the whole space `H¹₀(ℝⁿ) = H¹(ℝⁿ)`, so the hypothesis imposes no boundary condition; it is
exactly the weak equation tested against every `H¹(ℝⁿ)` function. This is the case `Ω = ℝⁿ` of
`TauCeti.PDE.UniformlyEllipticOn.norm_gradient_differenceQuotient_le_of_lipschitzOnWith_of_mapsTo`.
-/
theorem UniformlyEllipticOn.norm_gradient_differenceQuotient_le_of_lipschitzWith
    (ha : UniformlyEllipticOn Set.univ a lam Lam)
    (hK : LipschitzWith K fun x => matrixBilinearForm (a x))
    {f : Lp ℝ 2 (mu.restrict ((⊤ : Opens (EuclideanSpace ℝ ι)) : Set (EuclideanSpace ℝ ι)))}
    {u : W1p0 mu ⊤ 2} (hu : IsWeakSolutionDirichlet a 0 0 f u)
    (w : EuclideanSpace ℝ ι) (t : ℝ) :
    ‖W1p.gradient (W1p.differenceQuotient le_rfl w t (Set.mapsTo_univ (· + t • w) _)
      (u : W1p mu ⊤ 2))‖ ≤ ‖w‖ * (‖f‖ + K * ‖W1p.gradient (u : W1p mu ⊤ 2)‖) / lam :=
  ha.norm_gradient_differenceQuotient_le_of_lipschitzOnWith_of_mapsTo
    (fun s => Set.mapsTo_univ (· + s • w) _)
    hK.lipschitzOnWith hu t

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

/-- **The tangential second derivatives of a weak solution.** Let `Ω` be mapped onto itself by
every translation along `w`, as a half-space is by every translation parallel to its boundary.
Let `a` be uniformly elliptic on `Ω` with lower constant `λ`, and let its bilinear forms be
`K`-Lipschitz on `Ω` in the operator norm. For a weak solution `u ∈ H¹₀(Ω)` of
`-∂ⱼ(aⁱʲ ∂ᵢu) = f` with
`u = 0` on `∂Ω`, every first derivative `∂_y u = ⟪∇u, y⟫` has a weak derivative in the direction
`w` in `L²(Ω)`, with

`‖∂_w ∂_y u‖_{L²(Ω)} ≤ ‖y‖ ‖w‖ (‖f‖_{L²(Ω)} + K ‖∇u‖_{L²(Ω)}) / λ`.

The estimate is global on `Ω`, up to the boundary, and no regularity of `∂Ω` is assumed. -/
theorem UniformlyEllipticOn.exists_norm_le_hasWeakLineDerivOn_gradient_of_lipschitzOnWith_of_mapsTo
    {Omega : Opens (EuclideanSpace ℝ ι)} {w : EuclideanSpace ℝ ι}
    (hw : ∀ t : ℝ, MapsTo (· + t • w) Omega Omega)
    (ha : UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam)
    (hK : LipschitzOnWith K (fun x => matrixBilinearForm (a x)) Omega)
    {f : Lp ℝ 2 (mu.restrict Omega)} {u : W1p0 mu Omega 2}
    (hu : IsWeakSolutionDirichlet a 0 0 f u) (y : EuclideanSpace ℝ ι) :
    ∃ G : Lp ℝ 2 (mu.restrict Omega),
      ‖G‖ ≤ ‖y‖ * (‖w‖ * (‖f‖ + K * ‖W1p.gradient (u : W1p mu Omega 2)‖) / lam) ∧
        HasWeakLineDerivOn mu Omega
          (fun x => ⟪W1p.gradient (u : W1p mu Omega 2) x, y⟫_ℝ) G w := by
  have hlam := ha.pos
  have hloc : LocallyIntegrableOn (fun x => ⟪W1p.gradient (u : W1p mu Omega 2) x, y⟫_ℝ)
      (Omega : Set (EuclideanSpace ℝ ι)) mu := by
    simpa using
      ((W1p.hasWeakFDerivOn (u : W1p mu Omega 2)).hasWeakLineDerivOn y).locallyIntegrableOn_deriv
  -- The uniform bound on the difference quotients of `∂_y u`, on all of `Ω`.
  have hglobal : ∀ t : ℝ, eLpNorm
      (fun x => t⁻¹ * (⟪W1p.gradient (u : W1p mu Omega 2) (x + t • w), y⟫_ℝ
        - ⟪W1p.gradient (u : W1p mu Omega 2) x, y⟫_ℝ)) 2 (mu.restrict Omega)
      ≤ ENNReal.ofReal
        (‖y‖ * (‖w‖ * (‖f‖ + K * ‖W1p.gradient (u : W1p mu Omega 2)‖) / lam)) := by
    intro t
    set g := W1p.differenceQuotient le_rfl w t (hw t) (u : W1p mu Omega 2)
    have hae : (fun x => t⁻¹ * (⟪W1p.gradient (u : W1p mu Omega 2) (x + t • w), y⟫_ℝ
          - ⟪W1p.gradient (u : W1p mu Omega 2) x, y⟫_ℝ))
        =ᵐ[mu.restrict Omega] fun x => ⟪W1p.gradient g x, y⟫_ℝ := by
      filter_upwards [W1p.gradient_differenceQuotient_ae le_rfl w t (hw t)
        (u : W1p mu Omega 2)] with x hx
      rw [hx, inner_smul_left, inner_sub_left]
      simp [mul_sub]
    rw [eLpNorm_congr_ae hae]
    calc eLpNorm (fun x => ⟪W1p.gradient g x, y⟫_ℝ) 2 (mu.restrict Omega)
        ≤ eLpNorm (‖y‖ • (W1p.gradient g : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι)) 2
            (mu.restrict Omega) :=
          have hmeas : AEStronglyMeasurable (fun x => ⟪W1p.gradient g x, y⟫_ℝ)
              (mu.restrict Omega) :=
            (Lp.aestronglyMeasurable (W1p.gradient g)).inner_const
          eLpNorm_mono_ae hmeas (Filter.Eventually.of_forall fun x => by
            rw [Pi.smul_apply, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_norm, mul_comm]
            exact abs_real_inner_le_norm _ y)
      _ = ‖y‖ₑ * eLpNorm (W1p.gradient g : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι) 2
            (mu.restrict Omega) := by
          rw [eLpNorm_const_smul, enorm_norm]
      _ = ‖y‖ₑ * ENNReal.ofReal ‖W1p.gradient g‖ := by
          rw [Lp.norm_def, ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top _)]
      _ ≤ ‖y‖ₑ * ENNReal.ofReal
            (‖w‖ * (‖f‖ + K * ‖W1p.gradient (u : W1p mu Omega 2)‖) / lam) := by
          gcongr
          exact ha.norm_gradient_differenceQuotient_le_of_lipschitzOnWith_of_mapsTo hw hK hu t
      _ = ENNReal.ofReal
            (‖y‖ * (‖w‖ * (‖f‖ + K * ‖W1p.gradient (u : W1p mu Omega 2)‖) / lam)) := by
          rw [← ofReal_norm, ← ENNReal.ofReal_mul (norm_nonneg y)]
  refine exists_norm_le_hasWeakLineDerivOn_of_frequently_eLpNorm_inv_mul_sub_le hloc w
    (by positivity) fun S hS _ => Filter.Eventually.frequently ?_
  filter_upwards with t
  exact le_trans (eLpNorm_mono_measure _ (Measure.restrict_mono hS le_rfl)) (hglobal t)

/-- **The second-order weak directional derivatives of a whole-space weak solution.** Let `a` be
uniformly elliptic on the whole space with lower constant `λ`, and let `x ↦ a(x)` be
`K`-Lipschitz in the operator norm of its bilinear forms. For a weak solution `u ∈ H¹(ℝⁿ)` of
`-∂ⱼ(aⁱʲ ∂ᵢu) = f`, the derivative `∂_y u = ⟪∇u, y⟫` is again weakly differentiable in every
direction `w`, with

`‖∂_w ∂_y u‖_{L²} ≤ ‖y‖ ‖w‖ (‖f‖_{L²} + K ‖∇u‖_{L²}) / λ`.

This is the `H²` estimate in quantitative, direction-by-direction form, and the case `Ω = ℝⁿ` of
`UniformlyEllipticOn.exists_norm_le_hasWeakLineDerivOn_gradient_of_lipschitzOnWith_of_mapsTo`.
-/
theorem UniformlyEllipticOn.exists_norm_le_hasWeakLineDerivOn_gradient_of_lipschitzWith
    (ha : UniformlyEllipticOn Set.univ a lam Lam)
    (hK : LipschitzWith K fun x => matrixBilinearForm (a x))
    {f : Lp ℝ 2 (mu.restrict ((⊤ : Opens (EuclideanSpace ℝ ι)) : Set (EuclideanSpace ℝ ι)))}
    {u : W1p0 mu ⊤ 2} (hu : IsWeakSolutionDirichlet a 0 0 f u)
    (y w : EuclideanSpace ℝ ι) :
    ∃ G : Lp ℝ 2 (mu.restrict ((⊤ : Opens (EuclideanSpace ℝ ι)) : Set (EuclideanSpace ℝ ι))),
      ‖G‖ ≤ ‖y‖ * (‖w‖ * (‖f‖ + K * ‖W1p.gradient (u : W1p mu ⊤ 2)‖) / lam) ∧
        HasWeakLineDerivOn mu ⊤
          (fun x => ⟪W1p.gradient (u : W1p mu ⊤ 2) x, y⟫_ℝ) G w :=
  ha.exists_norm_le_hasWeakLineDerivOn_gradient_of_lipschitzOnWith_of_mapsTo
    (fun s => Set.mapsTo_univ (· + s • w) _)
    hK.lipschitzOnWith hu y

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
