/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import TauCeti.Analysis.InnerProductSpace.Variational.Spectrum
public import TauCeti.Analysis.LocallyConvex.WeakSpace
public import TauCeti.Analysis.RCLike.SesquilinearForm
public import TauCeti.Analysis.Variational.DirectMethod
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# Quadratic energies, weak Euler--Lagrange equations, and coercive minimization

Let `V` be a seminormed space over `𝕜` (`ℝ` or `ℂ`, written `[RCLike 𝕜]`), `a : V →L⋆[𝕜] V →L[𝕜] 𝕜`
a bounded sesquilinear form (conjugate-linear in its first slot and `𝕜`-linear in its second), and
`ℓ : StrongDual 𝕜 V` a continuous `𝕜`-linear functional. The associated **quadratic energy** is the
real-valued functional

`quadraticEnergy a ℓ u = RCLike.re (a u u) - 2 * RCLike.re (ℓ u)`.

When `a` is Hermitian (`∀ u v, a u v = star (a v u)`), expanding `quadraticEnergy a ℓ (u + v)`
isolates the linear variation `2 Re(a u v - ℓ v)` from the quadratic remainder `q(v) = Re(a v v)`:

* **Affine shift and restriction.** Translating by a datum `g` shifts the forcing from `ℓ` to
  `ℓ - a g`: `quadraticEnergy a ℓ (g + w) = quadraticEnergy a ℓ g + quadraticEnergy a (ℓ - a g) w`,
  reducing inhomogeneous affine constraints `g +ᵥ W` to homogeneous subspaces `W`.
* **First variation and weak Euler--Lagrange equations.** On a Banach space equipped with its
  compatible real scalar action, `quadraticEnergy a ℓ` is smooth over `ℝ` with derivative
  `v ↦ 2 Re(a u v - ℓ v)`. In any seminormed space over `𝕜`, testing along rays shows that a local
  minimizer `u` on a convex set `C` satisfies the variational inequality
  `Re(ℓ (v - u)) ≤ Re(a u (v - u))` for `v ∈ C`, and a local minimizer on an affine subspace
  `g +ᵥ W` of a `𝕜`-submodule `W` satisfies the full `𝕜`-valued weak equation `a u w = ℓ w` for all
  `w ∈ W`: testing `w` gives the real part, and testing `RCLike.I • w` recovers the imaginary part.
* **Exact energy gap and converse.** At any solution of `a u w = ℓ w`, the linear term cancels and
  `quadraticEnergy a ℓ (u + w) - quadraticEnergy a ℓ u = Re(a w w)`. When `q ≥ 0` on `W`, the weak
  equation on `W` and global minimality on `g +ᵥ W` are therefore equivalent.
* **Coercive forms and direct-method existence.** If `c * ‖w‖² ≤ Re(a w w)` on `W` (`c > 0`), the
  energy gap bounds `c * ‖v - u‖² ≤ E(v) - E(u)`, giving uniqueness of weak solutions and
  minimizers, norm convergence of near-minimizing sequences at rate
  `‖uₙ - u‖² ≤ (E(uₙ) - E(u)) / c`, bounded sublevels on `g +ᵥ W`, `c⁻¹`-Lipschitz dependence of
  weak solutions on `ℓ`, and (by weak lower semicontinuity and the direct method) existence and
  uniqueness of constrained minimizers and weak solutions on reflexive spaces.
* **Identification at `𝕜 = ℝ`.** On a complete real inner-product space, the unique global minimizer
  of `quadraticEnergy B ℓ` for a symmetric coercive bilinear form `B` coincides with
  `IsCoercive.solutionOfFunctional`, `IsCoercive.continuousLinearEquivOfBilin.symm`,
  `IsCoercive.solutionOfInner`, and (for forcing `v ↦ ⟪h, J v⟫_ℝ`) `IsCoercive.formSolutionMap`.

## Main declarations

* `TauCeti.quadraticEnergy`: the energy `u ↦ RCLike.re (a u u) - 2 * RCLike.re (ℓ u)`.
* `TauCeti.quadraticEnergy_add_real_smul_sub_of_eq_star`: exact real-line expansion
  `E(u + t • v) - E(u) = 2 * t * Re(a u v - ℓ v) + t² * Re(a v v)`.
* `TauCeti.hasStrictFDerivAt_quadraticEnergy`: strict real Fréchet derivative of `quadraticEnergy`.
* `TauCeti.apply_eq_of_isLocalMinOn_vadd` and `TauCeti.isMinOn_vadd_quadraticEnergy_iff`: weak
  Euler--Lagrange equation on `g +ᵥ W` and equivalence with minimality when `q ≥ 0` on `W`.
* `TauCeti.norm_sub_sq_le_quadraticEnergy_sub_div` and
  `TauCeti.tendsto_of_tendsto_quadraticEnergy_vadd`: coercivity rate and norm convergence of
  near-minimizers.
* `TauCeti.norm_sub_le_inv_mul_norm_sub_of_forall_apply_eq`: `c⁻¹`-Lipschitz dependence of weak
  solutions on the forcing functional.
* `TauCeti.existsUnique_isMinOn_quadraticEnergy_of_isClosed_convex` and
  `TauCeti.existsUnique_vadd_forall_apply_eq_of_isClosed`: direct-method existence and uniqueness
  of constrained minimizers and weak solutions on reflexive spaces.
* `IsCoercive.isMinOn_quadraticEnergy_iff_eq_solutionOfFunctional` and
  `IsCoercive.isMinOn_quadraticEnergy_toSesqForm_iff_eq_formSolutionMap`: identification with the
  real Lax--Milgram and `formSolutionMap` solutions.

## References

* J. K. Hunter, *Notes on Partial Differential Equations*, Chapter 4: Definition 4.3,
  Proposition 4.5, Corollary 4.6, and Theorem 4.20.
-/

public section

noncomputable section

open Filter Set Bornology NormedSpace
open scoped Topology InnerProductSpace Pointwise

namespace TauCeti

section Basic

variable {𝕜 V : Type*} [RCLike 𝕜] [SeminormedAddCommGroup V] [NormedSpace 𝕜 V]

/-- The real **quadratic energy** `E(u) = Re(a u u) - 2 Re(ℓ u)` attached to a continuous
sesquilinear form `a : V →L⋆[𝕜] V →L[𝕜] 𝕜` and a continuous linear functional
`ℓ : StrongDual 𝕜 V`. -/
def quadraticEnergy (a : V →L⋆[𝕜] V →L[𝕜] 𝕜) (ℓ : StrongDual 𝕜 V) (u : V) : ℝ :=
  RCLike.re (a u u) - 2 * RCLike.re (ℓ u)

/-- Defining formula for `quadraticEnergy`. Kept without `@[simp]` so lemmas stated in terms of
`quadraticEnergy` fire before unfolding. -/
theorem quadraticEnergy_apply (a : V →L⋆[𝕜] V →L[𝕜] 𝕜) (ℓ : StrongDual 𝕜 V) (u : V) :
    quadraticEnergy a ℓ u = RCLike.re (a u u) - 2 * RCLike.re (ℓ u) :=
  (rfl)

/-- Every quadratic energy vanishes at the origin. -/
@[simp]
theorem quadraticEnergy_zero (a : V →L⋆[𝕜] V →L[𝕜] 𝕜) (ℓ : StrongDual 𝕜 V) :
    quadraticEnergy a ℓ 0 = 0 := by
  simp [quadraticEnergy_apply]

/-- With zero forcing, `quadraticEnergy a 0` is the pure quadratic form `u ↦ Re(a u u)`. -/
@[simp]
theorem quadraticEnergy_zero_right (a : V →L⋆[𝕜] V →L[𝕜] 𝕜) (u : V) :
    quadraticEnergy a 0 u = RCLike.re (a u u) := by
  simp [quadraticEnergy_apply]

/-- With zero form, `quadraticEnergy 0 ℓ u` is `-2 * Re(ℓ u)`. -/
@[simp]
theorem quadraticEnergy_zero_left (ℓ : StrongDual 𝕜 V) (u : V) :
    quadraticEnergy 0 ℓ u = -2 * RCLike.re (ℓ u) := by
  simp [quadraticEnergy_apply]

/-- Negating both the forcing and the vector leaves `quadraticEnergy` unchanged. -/
@[simp]
theorem quadraticEnergy_neg_neg (a : V →L⋆[𝕜] V →L[𝕜] 𝕜) (ℓ : StrongDual 𝕜 V) (u : V) :
    quadraticEnergy a (-ℓ) (-u) = quadraticEnergy a ℓ u := by
  simp [quadraticEnergy_apply]

/-- Evaluating `quadraticEnergy a ℓ` at `-u` flips the sign of the forcing. -/
theorem quadraticEnergy_neg (a : V →L⋆[𝕜] V →L[𝕜] 𝕜) (ℓ : StrongDual 𝕜 V) (u : V) :
    quadraticEnergy a ℓ (-u) = quadraticEnergy a (-ℓ) u := by
  simp [quadraticEnergy_apply]

/-- `quadraticEnergy` is additive jointly in the form `a` and the forcing `ℓ`. -/
theorem quadraticEnergy_add_form_functional (a₁ a₂ : V →L⋆[𝕜] V →L[𝕜] 𝕜)
    (ℓ₁ ℓ₂ : StrongDual 𝕜 V) (u : V) :
    quadraticEnergy (a₁ + a₂) (ℓ₁ + ℓ₂) u =
      quadraticEnergy a₁ ℓ₁ u + quadraticEnergy a₂ ℓ₂ u := by
  simp only [quadraticEnergy_apply, add_apply, map_add]
  ring

/-- Pullback of `quadraticEnergy` along a continuous `𝕜`-linear map `L : W →L[𝕜] V`. -/
@[simp]
theorem quadraticEnergy_comp {W : Type*} [SeminormedAddCommGroup W] [NormedSpace 𝕜 W]
    (a : V →L⋆[𝕜] V →L[𝕜] 𝕜) (ℓ : StrongDual 𝕜 V) (L : W →L[𝕜] V) (w : W) :
    quadraticEnergy (a.bilinearComp L L) (ℓ.comp L) w = quadraticEnergy a ℓ (L w) :=
  (rfl)

/-- Over `ℝ`, `quadraticEnergy B ℓ u` is `B u u - 2 * ℓ u`. -/
theorem quadraticEnergy_real_apply {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]
    (B : E →L[ℝ] E →L[ℝ] ℝ) (ℓ : StrongDual ℝ E) (u : E) :
    quadraticEnergy B ℓ u = B u u - 2 * ℓ u := by
  simp [quadraticEnergy_apply]

/-! ### Exact expansion and affine shift identities -/

/-- Increment of `quadraticEnergy a ℓ` from `u` to `u + v` without assuming symmetry of `a`. -/
theorem quadraticEnergy_add_sub (a : V →L⋆[𝕜] V →L[𝕜] 𝕜) (ℓ : StrongDual 𝕜 V) (u v : V) :
    quadraticEnergy a ℓ (u + v) - quadraticEnergy a ℓ u =
      RCLike.re (a u v) + RCLike.re (a v u) - 2 * RCLike.re (ℓ v) + RCLike.re (a v v) := by
  simp only [quadraticEnergy_apply, map_add, add_apply]
  ring

/-- **Exact vector increment** of `quadraticEnergy` for a Hermitian form `a`:
`E(u + v) - E(u) = 2 * Re(a u v - ℓ v) + Re(a v v)`. -/
theorem quadraticEnergy_add_sub_of_eq_star {a : V →L⋆[𝕜] V →L[𝕜] 𝕜}
    (ha : ∀ x y, a x y = star (a y x)) (ℓ : StrongDual 𝕜 V) (u v : V) :
    quadraticEnergy a ℓ (u + v) - quadraticEnergy a ℓ u =
      2 * RCLike.re (a u v - ℓ v) + RCLike.re (a v v) := by
  have hcomm : RCLike.re (a v u) = RCLike.re (a u v) :=
    a.toLinearMap₁₂.re_apply_comm_of_eq_star ha v u
  rw [quadraticEnergy_add_sub, hcomm, map_sub]
  ring

/-- Difference `E(v) - E(u)` between any two vectors for a Hermitian form `a`. -/
theorem quadraticEnergy_sub_quadraticEnergy_of_eq_star {a : V →L⋆[𝕜] V →L[𝕜] 𝕜}
    (ha : ∀ x y, a x y = star (a y x)) (ℓ : StrongDual 𝕜 V) (u v : V) :
    quadraticEnergy a ℓ v - quadraticEnergy a ℓ u =
      2 * RCLike.re (a u (v - u) - ℓ (v - u)) + RCLike.re (a (v - u) (v - u)) := by
  simpa only [add_sub_cancel] using quadraticEnergy_add_sub_of_eq_star ha ℓ u (v - u)

/-- **Affine datum shift** for a Hermitian quadratic energy: translating the argument by `g` shifts
the forcing functional from `ℓ` to `ℓ - a g` up to the additive constant `E(g)`. This reduces
minimization on an inhomogeneous coset `g +ᵥ W` to minimization on the subspace `W`. -/
theorem quadraticEnergy_add_eq_add_sub {a : V →L⋆[𝕜] V →L[𝕜] 𝕜}
    (ha : ∀ x y, a x y = star (a y x)) (ℓ : StrongDual 𝕜 V) (g w : V) :
    quadraticEnergy a ℓ (g + w) =
      quadraticEnergy a ℓ g + quadraticEnergy a (ℓ - a g) w := by
  have h := quadraticEnergy_add_sub_of_eq_star ha ℓ g w
  simp only [quadraticEnergy_apply, sub_apply, map_sub] at h ⊢
  linarith

/-- **Complex/scalar-line expansion** of `quadraticEnergy` for a Hermitian form `a` and `c : 𝕜`:
`E(u + c • v) - E(u) = 2 * Re(c * (a u v - ℓ v)) + ‖c‖² * Re(a v v)`. -/
theorem quadraticEnergy_add_smul_sub_of_eq_star {a : V →L⋆[𝕜] V →L[𝕜] 𝕜}
    (ha : ∀ x y, a x y = star (a y x)) (ℓ : StrongDual 𝕜 V) (u v : V) (c : 𝕜) :
    quadraticEnergy a ℓ (u + c • v) - quadraticEnergy a ℓ u =
      2 * RCLike.re (c * (a u v - ℓ v)) + ‖c‖ ^ 2 * RCLike.re (a v v) := by
  rw [quadraticEnergy_add_sub_of_eq_star ha ℓ u (c • v), map_smul, map_smul, smul_eq_mul,
    smul_eq_mul, ← mul_sub]
  congr 1
  exact a.toLinearMap₁₂.re_apply_smul_self c v

/-- Real-scalar-line expansion via coercion `(t : 𝕜) • v`, requiring no `NormedSpace ℝ V`
instance. -/
theorem quadraticEnergy_add_ofReal_smul_sub_of_eq_star {a : V →L⋆[𝕜] V →L[𝕜] 𝕜}
    (ha : ∀ x y, a x y = star (a y x)) (ℓ : StrongDual 𝕜 V) (u v : V) (t : ℝ) :
    quadraticEnergy a ℓ (u + (t : 𝕜) • v) - quadraticEnergy a ℓ u =
      2 * t * RCLike.re (a u v - ℓ v) + t ^ 2 * RCLike.re (a v v) := by
  rw [quadraticEnergy_add_smul_sub_of_eq_star ha ℓ u v (t : 𝕜), RCLike.re_ofReal_mul,
    RCLike.norm_ofReal, sq_abs]
  ring

section RealScalar

variable [NormedSpace ℝ V] [IsScalarTower ℝ 𝕜 V]

/-- **Real-line expansion** of `quadraticEnergy` for a Hermitian form `a` (Hunter, Proposition 4.5):
`E(u + t • v) - E(u) = 2 * t * Re(a u v - ℓ v) + t² * Re(a v v)`. -/
theorem quadraticEnergy_add_real_smul_sub_of_eq_star {a : V →L⋆[𝕜] V →L[𝕜] 𝕜}
    (ha : ∀ x y, a x y = star (a y x)) (ℓ : StrongDual 𝕜 V) (u v : V) (t : ℝ) :
    quadraticEnergy a ℓ (u + t • v) - quadraticEnergy a ℓ u =
      2 * t * RCLike.re (a u v - ℓ v) + t ^ 2 * RCLike.re (a v v) := by
  rw [← algebraMap_smul 𝕜 t v, RCLike.algebraMap_eq_ofReal]
  exact quadraticEnergy_add_ofReal_smul_sub_of_eq_star ha ℓ u v t

/-- Along a two-point affine combination `t₁ • u + t₂ • v` with `t₁ + t₂ = 1`, the Jensen deficit of
`quadraticEnergy a ℓ` equals `t₁ * t₂ * Re(a (u - v) (u - v))`, independent of the linear forcing
`ℓ`. -/
theorem quadraticEnergy_combo_add_mul_sub {a : V →L⋆[𝕜] V →L[𝕜] 𝕜}
    (ha : ∀ x y, a x y = star (a y x)) (ℓ : StrongDual 𝕜 V) {t₁ t₂ : ℝ} (ht : t₁ + t₂ = 1)
    (u v : V) :
    quadraticEnergy a ℓ (t₁ • u + t₂ • v) +
        t₁ * t₂ * RCLike.re (a (u - v) (u - v)) =
      t₁ * quadraticEnergy a ℓ u + t₂ * quadraticEnergy a ℓ v := by
  have hq := a.toLinearMap₁₂.re_apply_combo_self_add_mul_sub ha ht u v
  have hℓ : RCLike.re (ℓ (t₁ • u + t₂ • v)) =
      t₁ * RCLike.re (ℓ u) + t₂ * RCLike.re (ℓ v) := by
    rw [map_add, ← algebraMap_smul 𝕜 t₁ u, ← algebraMap_smul 𝕜 t₂ v, map_smul, map_smul,
      RCLike.algebraMap_eq_ofReal]
    simp
  -- `hq` is stated on `a.toLinearMap₁₂`; align applications with `a`.
  change RCLike.re (a (t₁ • u + t₂ • v) (t₁ • u + t₂ • v)) +
      t₁ * t₂ * RCLike.re (a (u - v) (u - v)) =
    t₁ * RCLike.re (a u u) + t₂ * RCLike.re (a v v) at hq
  simp only [quadraticEnergy_apply, hℓ]
  linarith

end RealScalar

/-! ### Continuity, convexity, and weak lower semicontinuity -/

/-- `quadraticEnergy a ℓ` is norm-continuous for every continuous sesquilinear form `a` and
continuous linear functional `ℓ`. -/
theorem continuous_quadraticEnergy (a : V →L⋆[𝕜] V →L[𝕜] 𝕜) (ℓ : StrongDual 𝕜 V) :
    Continuous (quadraticEnergy a ℓ) :=
  a.continuous_re_apply_self.sub (continuous_const.mul (RCLike.reCLM.continuous.comp ℓ.continuous))

/-- If `a` is Hermitian and nonnegative on differences of points of a convex set `C`, then
`quadraticEnergy a ℓ` is convex on `C`. -/
theorem convexOn_quadraticEnergy_of_sub_nonneg [NormedSpace ℝ V] [IsScalarTower ℝ 𝕜 V]
    {a : V →L⋆[𝕜] V →L[𝕜] 𝕜} (ha : ∀ x y, a x y = star (a y x)) {C : Set V} (hC : Convex ℝ C)
    (hpos : ∀ u ∈ C, ∀ v ∈ C, 0 ≤ RCLike.re (a (u - v) (u - v))) (ℓ : StrongDual 𝕜 V) :
    ConvexOn ℝ C (quadraticEnergy a ℓ) := by
  refine ⟨hC, fun u hu v hv t₁ t₂ ht₁ ht₂ ht ↦ ?_⟩
  simp only [smul_eq_mul]
  have hdiff : 0 ≤ t₁ * t₂ * RCLike.re (a (u - v) (u - v)) :=
    mul_nonneg (mul_nonneg ht₁ ht₂) (hpos u hu v hv)
  linarith [quadraticEnergy_combo_add_mul_sub ha ℓ ht u v]

/-- If `a` is Hermitian with `∀ u, 0 ≤ Re(a u u)`, then `quadraticEnergy a ℓ` is convex on `V`. -/
theorem convexOn_quadraticEnergy [NormedSpace ℝ V] [IsScalarTower ℝ 𝕜 V]
    {a : V →L⋆[𝕜] V →L[𝕜] 𝕜} (ha : ∀ x y, a x y = star (a y x))
    (hpos : ∀ u, 0 ≤ RCLike.re (a u u)) (ℓ : StrongDual 𝕜 V) :
    ConvexOn ℝ Set.univ (quadraticEnergy a ℓ) :=
  convexOn_quadraticEnergy_of_sub_nonneg ha convex_univ (fun u _ v _ ↦ hpos (u - v)) ℓ

/-- If `a` is Hermitian and nonnegative on differences of points in a norm-closed convex set `C`,
then `quadraticEnergy a ℓ` is lower semicontinuous on `toWeakSpace 𝕜 V '' C` in the `𝕜`-weak
topology; `a` need not be nonnegative outside `C`. -/
theorem lowerSemicontinuousOn_quadraticEnergy_comp_toWeakSpace_symm
    [NormedSpace ℝ V] [IsScalarTower ℝ 𝕜 V]
    {a : V →L⋆[𝕜] V →L[𝕜] 𝕜} (ha : ∀ x y, a x y = star (a y x)) {C : Set V}
    (hC : Convex ℝ C) (hclosed : IsClosed C)
    (hpos : ∀ u ∈ C, ∀ v ∈ C, 0 ≤ RCLike.re (a (u - v) (u - v))) (ℓ : StrongDual 𝕜 V) :
    LowerSemicontinuousOn
      (fun u : WeakSpace 𝕜 V ↦ quadraticEnergy a ℓ ((toWeakSpace 𝕜 V).symm u))
      (toWeakSpace 𝕜 V '' C) := by
  rw [lowerSemicontinuousOn_iff_preimage_Iic]
  intro b
  have hsub_conv : Convex ℝ {x ∈ C | quadraticEnergy a ℓ x ≤ b} :=
    (convexOn_quadraticEnergy_of_sub_nonneg ha hC hpos ℓ).convex_le b
  have hsub_closed : IsClosed {x ∈ C | quadraticEnergy a ℓ x ≤ b} :=
    hclosed.inter ((continuous_quadraticEnergy a ℓ).lowerSemicontinuous.isClosed_preimage b)
  refine ⟨toWeakSpace 𝕜 V '' {x ∈ C | quadraticEnergy a ℓ x ≤ b}, ?_, ?_⟩
  · rw [← hsub_closed.closure_eq, hsub_conv.toWeakSpace_closure 𝕜]
    exact isClosed_closure
  · ext y
    constructor
    · rintro ⟨⟨x, hx, rfl⟩, hle⟩
      exact ⟨⟨x, hx, rfl⟩, ⟨x, ⟨hx, by simpa using hle⟩, rfl⟩⟩
    · rintro ⟨hy, ⟨x, ⟨_, hle⟩, rfl⟩⟩
      exact ⟨hy, by simpa using hle⟩

/-- For a nonnegative continuous Hermitian form `a`, `quadraticEnergy a ℓ` is lower semicontinuous
with respect to the `𝕜`-weak topology `WeakSpace 𝕜 V`. -/
theorem lowerSemicontinuous_quadraticEnergy_comp_toWeakSpace_symm
    {a : V →L⋆[𝕜] V →L[𝕜] 𝕜} (ha : ∀ x y, a x y = star (a y x))
    (hpos : ∀ u, 0 ≤ RCLike.re (a u u)) (ℓ : StrongDual 𝕜 V) :
    LowerSemicontinuous
      (fun u : WeakSpace 𝕜 V ↦ quadraticEnergy a ℓ ((toWeakSpace 𝕜 V).symm u)) := by
  let : NormedSpace ℝ V := NormedSpace.restrictScalars ℝ 𝕜 V
  have : IsScalarTower ℝ 𝕜 V := IsScalarTower.restrictScalars ℝ 𝕜 V
  exact (convexOn_quadraticEnergy ha hpos ℓ).quasiconvexOn.lowerSemicontinuous_comp_toWeakSpace_symm
    (continuous_quadraticEnergy a ℓ).lowerSemicontinuous

end Basic

/-! ### Smoothness and real Fréchet derivatives -/

section Calculus

variable {𝕜 V : Type*} [RCLike 𝕜] [NormedAddCommGroup V] [NormedSpace 𝕜 V]
  [NormedSpace ℝ V] [IsScalarTower ℝ 𝕜 V] {n : WithTop ℕ∞}

/-- `quadraticEnergy a ℓ` is `C^n` over `ℝ` for every `n`. -/
theorem contDiff_quadraticEnergy (a : V →L⋆[𝕜] V →L[𝕜] 𝕜) (ℓ : StrongDual 𝕜 V) :
    ContDiff ℝ n (quadraticEnergy a ℓ) :=
  a.contDiff_re_apply_self.sub
    (contDiff_const.mul (RCLike.reCLM.contDiff.comp (ℓ.restrictScalars ℝ).contDiff))

/-- `quadraticEnergy a ℓ` is Fréchet differentiable over `ℝ`. -/
theorem differentiable_quadraticEnergy (a : V →L⋆[𝕜] V →L[𝕜] 𝕜) (ℓ : StrongDual 𝕜 V) :
    Differentiable ℝ (quadraticEnergy a ℓ) :=
  (contDiff_quadraticEnergy (n := 1) a ℓ).differentiable one_ne_zero

/-- **Strict real Fréchet derivative** of `quadraticEnergy a ℓ` for a Hermitian form `a`: at `u`,
the derivative is the continuous real-linear functional `v ↦ 2 * Re(a u v - ℓ v)`. -/
theorem hasStrictFDerivAt_quadraticEnergy {a : V →L⋆[𝕜] V →L[𝕜] 𝕜}
    (ha : ∀ x y, a x y = star (a y x)) (ℓ : StrongDual 𝕜 V) (u : V) :
    HasStrictFDerivAt (quadraticEnergy a ℓ)
      ((2 : ℝ) • RCLike.reCLM.comp ((a u - ℓ).restrictScalars ℝ)) u := by
  have hq := a.hasStrictFDerivAt_re_apply_self_of_eq_star ha u
  have hℓ : HasStrictFDerivAt (fun w ↦ 2 * RCLike.re (ℓ w))
      ((2 : ℝ) • RCLike.reCLM.comp (ℓ.restrictScalars ℝ)) u :=
    ((2 : ℝ) • RCLike.reCLM.comp (ℓ.restrictScalars ℝ)).hasStrictFDerivAt
  have hderiv : (2 : ℝ) • RCLike.reCLM.comp ((a u).restrictScalars ℝ) -
      (2 : ℝ) • RCLike.reCLM.comp (ℓ.restrictScalars ℝ) =
      (2 : ℝ) • RCLike.reCLM.comp ((a u - ℓ).restrictScalars ℝ) := by
    ext v
    simp only [ContinuousLinearMap.coe_restrictScalars', sub_apply, smul_apply,
      ContinuousLinearMap.comp_apply, RCLike.reCLM_apply, smul_eq_mul, map_sub]
    ring
  exact hderiv ▸ hq.sub hℓ

/-- **Real Fréchet derivative** of `quadraticEnergy a ℓ` for a Hermitian form `a`. -/
theorem hasFDerivAt_quadraticEnergy {a : V →L⋆[𝕜] V →L[𝕜] 𝕜}
    (ha : ∀ x y, a x y = star (a y x)) (ℓ : StrongDual 𝕜 V) (u : V) :
    HasFDerivAt (quadraticEnergy a ℓ)
      ((2 : ℝ) • RCLike.reCLM.comp ((a u - ℓ).restrictScalars ℝ)) u :=
  (hasStrictFDerivAt_quadraticEnergy ha ℓ u).hasFDerivAt

/-- Differential `fderiv ℝ (quadraticEnergy a ℓ) u` for a Hermitian form `a`. -/
theorem fderiv_quadraticEnergy {a : V →L⋆[𝕜] V →L[𝕜] 𝕜}
    (ha : ∀ x y, a x y = star (a y x)) (ℓ : StrongDual 𝕜 V) (u : V) :
    fderiv ℝ (quadraticEnergy a ℓ) u =
      (2 : ℝ) • RCLike.reCLM.comp ((a u - ℓ).restrictScalars ℝ) :=
  (hasFDerivAt_quadraticEnergy ha ℓ u).fderiv

/-- Directional formula for the real Fréchet derivative of `quadraticEnergy a ℓ`:
`fderiv ℝ (quadraticEnergy a ℓ) u v = 2 * Re(a u v - ℓ v)`. -/
theorem fderiv_quadraticEnergy_apply {a : V →L⋆[𝕜] V →L[𝕜] 𝕜}
    (ha : ∀ x y, a x y = star (a y x)) (ℓ : StrongDual 𝕜 V) (u v : V) :
    fderiv ℝ (quadraticEnergy a ℓ) u v = 2 * RCLike.re (a u v - ℓ v) := by
  rw [fderiv_quadraticEnergy ha]
  simp

/-- One-dimensional derivative of `t ↦ quadraticEnergy a ℓ (u + t • v)` at `t : ℝ`. -/
theorem hasDerivAt_quadraticEnergy_add_smul {a : V →L⋆[𝕜] V →L[𝕜] 𝕜}
    (ha : ∀ x y, a x y = star (a y x)) (ℓ : StrongDual 𝕜 V) (u v : V) (t : ℝ) :
    HasDerivAt (fun s : ℝ ↦ quadraticEnergy a ℓ (u + s • v))
      (2 * RCLike.re (a u v - ℓ v) + 2 * t * RCLike.re (a v v)) t := by
  have hpath : HasDerivAt (fun s : ℝ ↦ u + s • v) v t := by
    simpa only [zero_add, one_smul] using
      (hasDerivAt_const t u).fun_add ((hasDerivAt_id' t).smul_const v)
  have hcomp := (hasFDerivAt_quadraticEnergy ha ℓ (u + t • v)).comp_hasDerivAt t hpath
  have hval : ((2 : ℝ) • RCLike.reCLM.comp ((a (u + t • v) - ℓ).restrictScalars ℝ)) v =
      2 * RCLike.re (a u v - ℓ v) + 2 * t * RCLike.re (a v v) := by
    simp only [ContinuousLinearMap.coe_restrictScalars', smul_apply, ContinuousLinearMap.comp_apply,
      sub_apply, RCLike.reCLM_apply, smul_eq_mul, map_add, add_apply, map_sub,
      ← algebraMap_smul 𝕜 t v, a.map_smulₛₗ, RCLike.algebraMap_eq_ofReal, RCLike.conj_ofReal,
      RCLike.re_ofReal_mul]
    ring
  exact hval ▸ hcomp

end Calculus

/-! ### First variation, variational inequality, weak Euler--Lagrange equation, and energy gap -/

section FirstVariation

variable {𝕜 V : Type*} [RCLike 𝕜] [SeminormedAddCommGroup V] [NormedSpace 𝕜 V]

/-- **One-sided ray variation.** If `u` is a local minimizer of `quadraticEnergy a ℓ` on `S` and
`u + (t : 𝕜) • w ∈ S` for all sufficiently small `t > 0`, then `Re(ℓ w) ≤ Re(a u w)`. -/
theorem le_re_apply_of_isLocalMinOn_ray {a : V →L⋆[𝕜] V →L[𝕜] 𝕜}
    (ha : ∀ x y, a x y = star (a y x)) {ℓ : StrongDual 𝕜 V} {S : Set V} {u w : V}
    (hmin : IsLocalMinOn (quadraticEnergy a ℓ) S u)
    (hray : ∀ᶠ t : ℝ in 𝓝[>] 0, u + (t : 𝕜) • w ∈ S) :
    RCLike.re (ℓ w) ≤ RCLike.re (a u w) := by
  have hcont : Continuous (fun t : ℝ ↦ u + (t : 𝕜) • w) :=
    continuous_const.add ((RCLike.continuous_ofReal.comp continuous_id).smul continuous_const)
  have htend : Tendsto (fun t : ℝ ↦ u + (t : 𝕜) • w) (𝓝[>] 0) (𝓝[S] u) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, hray⟩
    simpa only [RCLike.ofReal_zero, zero_smul, add_zero] using
      (hcont.tendsto 0).mono_left nhdsWithin_le_nhds
  have hle : ∀ᶠ t : ℝ in 𝓝[>] 0,
      -(t / 2 * RCLike.re (a w w)) ≤ RCLike.re (a u w - ℓ w) := by
    filter_upwards [htend.eventually hmin, self_mem_nhdsWithin] with t ht htpos
    have hexp := quadraticEnergy_add_ofReal_smul_sub_of_eq_star ha ℓ u w t
    have hmul : 0 ≤ 2 * t * (RCLike.re (a u w - ℓ w) + t / 2 * RCLike.re (a w w)) := by
      linarith [show quadraticEnergy a ℓ u ≤ quadraticEnergy a ℓ (u + (t : 𝕜) • w) from ht]
    have hpos2 : (0 : ℝ) < 2 * t := mul_pos zero_lt_two htpos
    linarith [nonneg_of_mul_nonneg_right hmul hpos2]
  have hlim : Tendsto (fun t : ℝ ↦ -(t / 2 * RCLike.re (a w w))) (𝓝[>] 0) (𝓝 0) := by
    have hc : Continuous (fun t : ℝ ↦ -(t / 2 * RCLike.re (a w w))) := by fun_prop
    simpa using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
  have h0 : 0 ≤ RCLike.re (a u w - ℓ w) := le_of_tendsto hlim hle
  rwa [map_sub, sub_nonneg] at h0

/-- **Variational inequality on a convex constraint** for a local minimizer: if `u ∈ C` is a local
minimizer of `quadraticEnergy a ℓ` on a convex set `C`, then `Re(ℓ (v - u)) ≤ Re(a u (v - u))` for
every `v ∈ C`. -/
theorem le_re_apply_sub_of_isLocalMinOn_convex [NormedSpace ℝ V] [IsScalarTower ℝ 𝕜 V]
    {a : V →L⋆[𝕜] V →L[𝕜] 𝕜} (ha : ∀ x y, a x y = star (a y x)) {ℓ : StrongDual 𝕜 V}
    {C : Set V} (hC : Convex ℝ C) {u : V} (hu : u ∈ C)
    (hmin : IsLocalMinOn (quadraticEnergy a ℓ) C u) {v : V} (hv : v ∈ C) :
    RCLike.re (ℓ (v - u)) ≤ RCLike.re (a u (v - u)) := by
  refine le_re_apply_of_isLocalMinOn_ray ha hmin ?_
  filter_upwards [Ioo_mem_nhdsGT zero_lt_one] with t ht
  rw [← RCLike.algebraMap_eq_ofReal, algebraMap_smul]
  have hcomb : u + t • (v - u) = (1 - t) • u + t • v := by module
  rw [hcomb]
  exact hC hu hv (sub_nonneg.mpr ht.2.le) ht.1.le (sub_add_cancel 1 t)

/-- **Two-sided real-part variation** along a real subspace: at a local minimizer `u` of
`quadraticEnergy a ℓ` on `u +ᵥ W` (`W : Submodule ℝ V`), `Re(a u w) = Re(ℓ w)` for all `w ∈ W`. -/
theorem re_apply_eq_re_of_isLocalMinOn_vadd_real [NormedSpace ℝ V] [IsScalarTower ℝ 𝕜 V]
    {a : V →L⋆[𝕜] V →L[𝕜] 𝕜} (ha : ∀ x y, a x y = star (a y x)) {ℓ : StrongDual 𝕜 V}
    {W : Submodule ℝ V} {u : V} (hmin : IsLocalMinOn (quadraticEnergy a ℓ) (u +ᵥ (W : Set V)) u)
    {w : V} (hw : w ∈ W) :
    RCLike.re (a u w) = RCLike.re (ℓ w) := by
  have hmem (z : V) (hz : z ∈ W) : ∀ᶠ t : ℝ in 𝓝[>] 0, u + (t : 𝕜) • z ∈ u +ᵥ (W : Set V) :=
    Eventually.of_forall fun t ↦ by
      rw [← RCLike.algebraMap_eq_ofReal, algebraMap_smul]
      exact vadd_mem_vadd_set (W.smul_mem t hz)
  have h₁ := le_re_apply_of_isLocalMinOn_ray ha hmin (hmem w hw)
  have h₂ := le_re_apply_of_isLocalMinOn_ray ha hmin (hmem (-w) (W.neg_mem hw))
  simp only [map_neg] at h₂
  linarith

/-- **The `I`-test.** If `a u v` and `ℓ v` have equal real parts both at `v` and at
`RCLike.I • v`, then `a u v = ℓ v`. Over `ℂ`, testing `I • v` supplies the imaginary part; a
single real-part equality does not suffice (`a 1 i = i` has `Re(a 1 i) = 0`). -/
theorem apply_eq_of_re_eq_of_re_I_smul_eq (a : V →L⋆[𝕜] V →L[𝕜] 𝕜) (ℓ : StrongDual 𝕜 V)
    (u v : V) (hre : RCLike.re (a u v) = RCLike.re (ℓ v))
    (him : RCLike.re (a u ((RCLike.I : 𝕜) • v)) = RCLike.re (ℓ ((RCLike.I : 𝕜) • v))) :
    a u v = ℓ v := by
  refine RCLike.ext_of_re_eq_of_re_I_mul_eq hre ?_
  simpa only [map_smul, smul_eq_mul] using him

/-- **Weak Euler--Lagrange equation** at a local minimizer on `u +ᵥ W` for a `𝕜`-submodule `W`:
`a u w = ℓ w` for every `w ∈ W` (Hunter, Definition 4.3 and Proposition 4.5). -/
theorem apply_eq_of_isLocalMinOn_vadd_self {a : V →L⋆[𝕜] V →L[𝕜] 𝕜}
    (ha : ∀ x y, a x y = star (a y x)) {ℓ : StrongDual 𝕜 V} {W : Submodule 𝕜 V} {u : V}
    (hmin : IsLocalMinOn (quadraticEnergy a ℓ) (u +ᵥ (W : Set V)) u) {w : V} (hw : w ∈ W) :
    a u w = ℓ w := by
  have hre_all (z : V) (hz : z ∈ W) : RCLike.re (a u z) = RCLike.re (ℓ z) := by
    have hray (y : V) (hy : y ∈ W) :
        ∀ᶠ t : ℝ in 𝓝[>] 0, u + (t : 𝕜) • y ∈ u +ᵥ (W : Set V) :=
      Eventually.of_forall fun t ↦ vadd_mem_vadd_set (W.smul_mem (t : 𝕜) hy)
    have h₁ := le_re_apply_of_isLocalMinOn_ray ha hmin (hray z hz)
    have h₂ := le_re_apply_of_isLocalMinOn_ray ha hmin (hray (-z) (W.neg_mem hz))
    simp only [map_neg] at h₂
    linarith
  exact apply_eq_of_re_eq_of_re_I_smul_eq a ℓ u w (hre_all w hw)
    (hre_all ((RCLike.I : 𝕜) • w) (W.smul_mem RCLike.I hw))

/-- **Weak Euler--Lagrange equation** on an affine subspace `g +ᵥ W`: if `u ∈ g +ᵥ W` is a local
minimizer of `quadraticEnergy a ℓ` on `g +ᵥ W`, then `a u w = ℓ w` for every `w ∈ W`. -/
theorem apply_eq_of_isLocalMinOn_vadd {a : V →L⋆[𝕜] V →L[𝕜] 𝕜}
    (ha : ∀ x y, a x y = star (a y x)) {ℓ : StrongDual 𝕜 V} {W : Submodule 𝕜 V} {g u : V}
    (hu : u ∈ g +ᵥ (W : Set V))
    (hmin : IsLocalMinOn (quadraticEnergy a ℓ) (g +ᵥ (W : Set V)) u) {w : V} (hw : w ∈ W) :
    a u w = ℓ w := by
  have hset : g +ᵥ (W : Set V) = u +ᵥ (W : Set V) := by
    rw [mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add, neg_add_eq_sub] at hu
    ext x
    simp only [mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add, neg_add_eq_sub, SetLike.mem_coe]
    exact ⟨fun hx ↦ by simpa only [sub_sub_sub_cancel_right] using W.sub_mem hx hu,
      fun hx ↦ by simpa only [sub_add_sub_cancel] using W.add_mem hx hu⟩
  rw [hset] at hmin
  exact apply_eq_of_isLocalMinOn_vadd_self ha hmin hw

/-- Global-minimizer specialization of `apply_eq_of_isLocalMinOn_vadd`. -/
theorem apply_eq_of_isMinOn_vadd {a : V →L⋆[𝕜] V →L[𝕜] 𝕜}
    (ha : ∀ x y, a x y = star (a y x)) {ℓ : StrongDual 𝕜 V} {W : Submodule 𝕜 V} {g u : V}
    (hu : u ∈ g +ᵥ (W : Set V))
    (hmin : IsMinOn (quadraticEnergy a ℓ) (g +ᵥ (W : Set V)) u) {w : V} (hw : w ∈ W) :
    a u w = ℓ w :=
  apply_eq_of_isLocalMinOn_vadd ha hu hmin.isLocalMinOn hw

/-- **Unconstrained weak Euler--Lagrange equation** at a local minimizer: `a u v = ℓ v` for every
`v : V`. -/
theorem apply_eq_of_isLocalMin {a : V →L⋆[𝕜] V →L[𝕜] 𝕜}
    (ha : ∀ x y, a x y = star (a y x)) {ℓ : StrongDual 𝕜 V} {u : V}
    (hmin : IsLocalMin (quadraticEnergy a ℓ) u) (v : V) :
    a u v = ℓ v := by
  have hvadd : u +ᵥ ((⊤ : Submodule 𝕜 V) : Set V) = Set.univ := by
    ext x
    simp
  refine apply_eq_of_isLocalMinOn_vadd_self (W := ⊤) ha ?_ trivial
  rw [hvadd]
  exact hmin.isLocalMinOn Set.univ

/-- Global unconstrained specialization of `apply_eq_of_isLocalMin`. -/
theorem apply_eq_of_isMinOn_univ {a : V →L⋆[𝕜] V →L[𝕜] 𝕜}
    (ha : ∀ x y, a x y = star (a y x)) {ℓ : StrongDual 𝕜 V} {u : V}
    (hmin : IsMinOn (quadraticEnergy a ℓ) Set.univ u) (v : V) :
    a u v = ℓ v :=
  apply_eq_of_isLocalMin ha (isLocalMinOn_univ_iff.mp hmin.isLocalMinOn) v

/-! ### Exact energy gap and equivalence with minimality for nonnegative forms -/

/-- **Exact energy gap** along a test direction `w` satisfying `Re(a u w) = Re(ℓ w)`:
`E(u + w) - E(u) = Re(a w w)` (Hunter, Corollary 4.6). -/
theorem quadraticEnergy_add_sub_eq_re_of_re_eq {a : V →L⋆[𝕜] V →L[𝕜] 𝕜}
    (ha : ∀ x y, a x y = star (a y x)) {ℓ : StrongDual 𝕜 V} {u w : V}
    (h : RCLike.re (a u w) = RCLike.re (ℓ w)) :
    quadraticEnergy a ℓ (u + w) - quadraticEnergy a ℓ u = RCLike.re (a w w) := by
  rw [quadraticEnergy_add_sub_of_eq_star ha ℓ u w, map_sub, h, sub_self, mul_zero, zero_add]

/-- **Exact energy gap** along a test direction `w` solving `a u w = ℓ w`:
`E(u + w) - E(u) = Re(a w w)` (Hunter, Corollary 4.6). -/
theorem quadraticEnergy_add_sub_eq_re_of_apply_eq {a : V →L⋆[𝕜] V →L[𝕜] 𝕜}
    (ha : ∀ x y, a x y = star (a y x)) {ℓ : StrongDual 𝕜 V} {u w : V} (h : a u w = ℓ w) :
    quadraticEnergy a ℓ (u + w) - quadraticEnergy a ℓ u = RCLike.re (a w w) :=
  quadraticEnergy_add_sub_eq_re_of_re_eq ha (congrArg RCLike.re h)

/-- **Exact energy gap** on an affine subspace `g +ᵥ W`: if `u ∈ g +ᵥ W` solves `a u w = ℓ w` for
all `w ∈ W`, then `E(v) - E(u) = Re(a (v - u) (v - u))` for every `v ∈ g +ᵥ W`. -/
theorem quadraticEnergy_sub_eq_re_of_forall_apply_eq {a : V →L⋆[𝕜] V →L[𝕜] 𝕜}
    (ha : ∀ x y, a x y = star (a y x)) {ℓ : StrongDual 𝕜 V} {W : Submodule 𝕜 V} {g u v : V}
    (hu : u ∈ g +ᵥ (W : Set V)) (hv : v ∈ g +ᵥ (W : Set V)) (hsol : ∀ w ∈ W, a u w = ℓ w) :
    quadraticEnergy a ℓ v - quadraticEnergy a ℓ u = RCLike.re (a (v - u) (v - u)) := by
  have hvu : v - u ∈ W := by
    rw [mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add, neg_add_eq_sub] at hu hv
    simpa only [sub_sub_sub_cancel_right] using W.sub_mem hv hu
  simpa only [add_sub_cancel] using quadraticEnergy_add_sub_eq_re_of_apply_eq ha (hsol (v - u) hvu)

/-- At a vector `u` satisfying `a u u = ℓ u` (in particular, a homogeneous weak solution on `W`
with `u ∈ W`), the energy value is `E(u) = -Re(a u u) = -Re(ℓ u)`. -/
theorem quadraticEnergy_eq_neg_re_of_apply_self_eq {a : V →L⋆[𝕜] V →L[𝕜] 𝕜}
    {ℓ : StrongDual 𝕜 V} {u : V} (h : a u u = ℓ u) :
    quadraticEnergy a ℓ u = -RCLike.re (a u u) := by
  rw [quadraticEnergy_apply, ← h]
  ring

/-- **Equivalence of the variational inequality and minimality** on a convex set `C` when `a` is
Hermitian and nonnegative on differences of points in `C`. -/
theorem isMinOn_convex_quadraticEnergy_iff [NormedSpace ℝ V] [IsScalarTower ℝ 𝕜 V]
    {a : V →L⋆[𝕜] V →L[𝕜] 𝕜} (ha : ∀ x y, a x y = star (a y x)) {ℓ : StrongDual 𝕜 V}
    {C : Set V} (hC : Convex ℝ C) (hpos : ∀ x ∈ C, ∀ y ∈ C, 0 ≤ RCLike.re (a (y - x) (y - x)))
    {u : V} (hu : u ∈ C) :
    IsMinOn (quadraticEnergy a ℓ) C u ↔
      ∀ v ∈ C, RCLike.re (ℓ (v - u)) ≤ RCLike.re (a u (v - u)) := by
  refine ⟨fun hmin v hv ↦ le_re_apply_sub_of_isLocalMinOn_convex ha hC hu hmin.isLocalMinOn hv,
    fun hvi ↦ isMinOn_iff.mpr fun v hv ↦ ?_⟩
  have hexp := quadraticEnergy_sub_quadraticEnergy_of_eq_star ha ℓ u v
  rw [map_sub] at hexp
  linarith [hvi v hv, hpos u hu v hv]

/-- **Equivalence of the weak Euler--Lagrange equation and minimality** on an affine subspace
`g +ᵥ W` when `Re(a w w) ≥ 0` for all `w ∈ W` (Hunter, Corollary 4.6). Nonnegativity on `W` is
necessary (`q(u) = -‖u‖²` makes the weak solution `0` a maximizer). -/
theorem isMinOn_vadd_quadraticEnergy_iff {a : V →L⋆[𝕜] V →L[𝕜] 𝕜}
    (ha : ∀ x y, a x y = star (a y x)) {ℓ : StrongDual 𝕜 V} {W : Submodule 𝕜 V}
    (hpos : ∀ w ∈ W, 0 ≤ RCLike.re (a w w)) {g u : V} (hu : u ∈ g +ᵥ (W : Set V)) :
    IsMinOn (quadraticEnergy a ℓ) (g +ᵥ (W : Set V)) u ↔ ∀ w ∈ W, a u w = ℓ w := by
  refine ⟨fun hmin w hw ↦ apply_eq_of_isMinOn_vadd ha hu hmin hw,
    fun hsol ↦ isMinOn_iff.mpr fun v hv ↦ ?_⟩
  have hgap := quadraticEnergy_sub_eq_re_of_forall_apply_eq ha hu hv hsol
  have hvu : v - u ∈ W := by
    rw [mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add, neg_add_eq_sub] at hu hv
    simpa only [sub_sub_sub_cancel_right] using W.sub_mem hv hu
  linarith [hpos (v - u) hvu]

/-- **Unconstrained equivalence** between `IsMinOn (quadraticEnergy a ℓ) Set.univ u` and the weak
equation `∀ v, a u v = ℓ v` for a nonnegative Hermitian form `a`. -/
theorem isMinOn_univ_quadraticEnergy_iff {a : V →L⋆[𝕜] V →L[𝕜] 𝕜}
    (ha : ∀ x y, a x y = star (a y x)) {ℓ : StrongDual 𝕜 V}
    (hpos : ∀ w, 0 ≤ RCLike.re (a w w)) {u : V} :
    IsMinOn (quadraticEnergy a ℓ) Set.univ u ↔ ∀ v, a u v = ℓ v := by
  refine ⟨fun hmin v ↦ apply_eq_of_isMinOn_univ ha hmin v,
    fun hsol ↦ isMinOn_iff.mpr fun v _ ↦ ?_⟩
  have hexp := quadraticEnergy_add_sub_eq_re_of_apply_eq ha (hsol (v - u))
  rw [add_sub_cancel] at hexp
  linarith [hpos (v - u)]

end FirstVariation

/-! ### Coercive forms: quadratic growth, near-minimizer rate, uniqueness, and stability -/

section Coercive

variable {𝕜 V : Type*} [RCLike 𝕜] [SeminormedAddCommGroup V] [NormedSpace 𝕜 V]

/-- **Quantitative quadratic growth** on `g +ᵥ W` around a weak solution `u ∈ g +ᵥ W`: if
`c * ‖w‖² ≤ Re(a w w)` for all `w ∈ W`, then `c * ‖v - u‖² ≤ E(v) - E(u)` for all `v ∈ g +ᵥ W`. -/
theorem mul_norm_sub_sq_le_quadraticEnergy_sub_of_forall_apply_eq {a : V →L⋆[𝕜] V →L[𝕜] 𝕜}
    (ha : ∀ x y, a x y = star (a y x)) {ℓ : StrongDual 𝕜 V} {W : Submodule 𝕜 V} {c : ℝ}
    (hcoer : ∀ w ∈ W, c * ‖w‖ ^ 2 ≤ RCLike.re (a w w)) {g u v : V}
    (hu : u ∈ g +ᵥ (W : Set V)) (hv : v ∈ g +ᵥ (W : Set V)) (hsol : ∀ w ∈ W, a u w = ℓ w) :
    c * ‖v - u‖ ^ 2 ≤ quadraticEnergy a ℓ v - quadraticEnergy a ℓ u := by
  rw [quadraticEnergy_sub_eq_re_of_forall_apply_eq ha hu hv hsol]
  have hvu : v - u ∈ W := by
    rw [mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add, neg_add_eq_sub] at hu hv
    simpa only [sub_sub_sub_cancel_right] using W.sub_mem hv hu
  exact hcoer (v - u) hvu

/-- **Quantitative quadratic growth** along an increment `h ∈ W` at a weak solution `u`:
`c * ‖h‖² ≤ E(u + h) - E(u)`. -/
theorem mul_norm_sq_le_quadraticEnergy_add_sub_of_apply_eq {a : V →L⋆[𝕜] V →L[𝕜] 𝕜}
    (ha : ∀ x y, a x y = star (a y x)) {ℓ : StrongDual 𝕜 V} {c : ℝ} {u h : V}
    (hcoer : c * ‖h‖ ^ 2 ≤ RCLike.re (a h h)) (hsol : a u h = ℓ h) :
    c * ‖h‖ ^ 2 ≤ quadraticEnergy a ℓ (u + h) - quadraticEnergy a ℓ u := by
  rwa [quadraticEnergy_add_sub_eq_re_of_apply_eq ha hsol]

/-- **Quantitative quadratic growth on a convex set** around a local minimizer `u ∈ C`: if
`c * ‖y - x‖² ≤ Re(a (y - x) (y - x))` on `C`, then `c * ‖v - u‖² ≤ E(v) - E(u)` for all
`v ∈ C`. -/
theorem mul_norm_sub_sq_le_quadraticEnergy_sub_of_isLocalMinOn_convex
    [NormedSpace ℝ V] [IsScalarTower ℝ 𝕜 V] {a : V →L⋆[𝕜] V →L[𝕜] 𝕜}
    (ha : ∀ x y, a x y = star (a y x)) {ℓ : StrongDual 𝕜 V} {C : Set V} (hC : Convex ℝ C)
    {c : ℝ} (hcoer : ∀ x ∈ C, ∀ y ∈ C, c * ‖y - x‖ ^ 2 ≤ RCLike.re (a (y - x) (y - x)))
    {u v : V} (hu : u ∈ C) (hv : v ∈ C) (hmin : IsLocalMinOn (quadraticEnergy a ℓ) C u) :
    c * ‖v - u‖ ^ 2 ≤ quadraticEnergy a ℓ v - quadraticEnergy a ℓ u := by
  have hvi := le_re_apply_sub_of_isLocalMinOn_convex ha hC hu hmin hv
  have hexp := quadraticEnergy_sub_quadraticEnergy_of_eq_star ha ℓ u v
  rw [map_sub] at hexp
  linarith [hcoer u hu v hv]

/-- **Near-minimizer distance rate** on `g +ᵥ W`: for `c > 0`, every admissible `v ∈ g +ᵥ W`
satisfies `‖v - u‖² ≤ (E(v) - E(u)) / c` around a minimizer `u ∈ g +ᵥ W`. -/
theorem norm_sub_sq_le_quadraticEnergy_sub_div_of_isMinOn_vadd {a : V →L⋆[𝕜] V →L[𝕜] 𝕜}
    (ha : ∀ x y, a x y = star (a y x)) {ℓ : StrongDual 𝕜 V} {W : Submodule 𝕜 V} {c : ℝ}
    (hc : 0 < c) (hcoer : ∀ w ∈ W, c * ‖w‖ ^ 2 ≤ RCLike.re (a w w)) {g u v : V}
    (hu : u ∈ g +ᵥ (W : Set V)) (hv : v ∈ g +ᵥ (W : Set V))
    (hmin : IsMinOn (quadraticEnergy a ℓ) (g +ᵥ (W : Set V)) u) :
    ‖v - u‖ ^ 2 ≤ (quadraticEnergy a ℓ v - quadraticEnergy a ℓ u) / c := by
  rw [le_div_iff₀ hc, mul_comm]
  exact mul_norm_sub_sq_le_quadraticEnergy_sub_of_forall_apply_eq ha hcoer hu hv
    (fun _ hw ↦ apply_eq_of_isMinOn_vadd ha hu hmin hw)

/-- **Unconstrained near-minimizer distance rate**: for `c > 0` and `∀ w, c * ‖w‖² ≤ Re(a w w)`,
every `v : V` satisfies `‖v - u‖² ≤ (E(v) - E(u)) / c` around a global minimizer `u`. -/
theorem norm_sub_sq_le_quadraticEnergy_sub_div {a : V →L⋆[𝕜] V →L[𝕜] 𝕜}
    (ha : ∀ x y, a x y = star (a y x)) {ℓ : StrongDual 𝕜 V} {c : ℝ} (hc : 0 < c)
    (hcoer : ∀ w, c * ‖w‖ ^ 2 ≤ RCLike.re (a w w)) {u v : V}
    (hmin : IsMinOn (quadraticEnergy a ℓ) Set.univ u) :
    ‖v - u‖ ^ 2 ≤ (quadraticEnergy a ℓ v - quadraticEnergy a ℓ u) / c := by
  rw [le_div_iff₀ hc, mul_comm]
  simpa only [add_sub_cancel] using mul_norm_sq_le_quadraticEnergy_add_sub_of_apply_eq ha
    (hcoer (v - u)) (apply_eq_of_isMinOn_univ ha hmin (v - u))

/-- **Near-minimizer distance rate on a convex set** `C`: for `c > 0`, every `v ∈ C` satisfies
`‖v - u‖² ≤ (E(v) - E(u)) / c` around a local minimizer `u ∈ C`. -/
theorem norm_sub_sq_le_quadraticEnergy_sub_div_of_isLocalMinOn_convex
    [NormedSpace ℝ V] [IsScalarTower ℝ 𝕜 V] {a : V →L⋆[𝕜] V →L[𝕜] 𝕜}
    (ha : ∀ x y, a x y = star (a y x)) {ℓ : StrongDual 𝕜 V} {C : Set V} (hC : Convex ℝ C)
    {c : ℝ} (hc : 0 < c)
    (hcoer : ∀ x ∈ C, ∀ y ∈ C, c * ‖y - x‖ ^ 2 ≤ RCLike.re (a (y - x) (y - x)))
    {u v : V} (hu : u ∈ C) (hv : v ∈ C) (hmin : IsLocalMinOn (quadraticEnergy a ℓ) C u) :
    ‖v - u‖ ^ 2 ≤ (quadraticEnergy a ℓ v - quadraticEnergy a ℓ u) / c := by
  rw [le_div_iff₀ hc, mul_comm]
  exact mul_norm_sub_sq_le_quadraticEnergy_sub_of_isLocalMinOn_convex ha hC hcoer hu hv hmin

/-- **Norm convergence of near-minimizers** from a quantitative quadratic energy bound: if
`‖x i - u‖² ≤ (E(x i) - E(u)) / c` along a filter `l` and `E(x i) → E(u)`, then `x i → u` in
norm. -/
theorem tendsto_of_tendsto_quadraticEnergy_of_sq_le {ι : Type*} {l : Filter ι}
    {a : V →L⋆[𝕜] V →L[𝕜] 𝕜} {ℓ : StrongDual 𝕜 V} {c : ℝ} {u : V} {x : ι → V}
    (hrate : ∀ᶠ i in l, ‖x i - u‖ ^ 2 ≤ (quadraticEnergy a ℓ (x i) - quadraticEnergy a ℓ u) / c)
    (hE : Tendsto (fun i ↦ quadraticEnergy a ℓ (x i)) l (𝓝 (quadraticEnergy a ℓ u))) :
    Tendsto x l (𝓝 u) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hsq : Tendsto (fun i ↦ ‖x i - u‖ ^ 2) l (𝓝 0) := by
    refine squeeze_zero' (Eventually.of_forall fun _ ↦ sq_nonneg _) hrate ?_
    simpa only [sub_self, zero_div] using (hE.sub_const (quadraticEnergy a ℓ u)).div_const c
  simpa only [Real.sqrt_zero] using
    (Real.continuous_sqrt.tendsto 0).comp hsq |>.congr'
      (Eventually.of_forall fun i ↦ Real.sqrt_sq (norm_nonneg (x i - u)))

/-- **Norm convergence of near-minimizers on `g +ᵥ W`**: if `a` is Hermitian and `c`-coercive on
`W` (`c > 0`), `u ∈ g +ᵥ W` minimizes `quadraticEnergy a ℓ` on `g +ᵥ W`, and `x i ∈ g +ᵥ W`
satisfies `E(x i) → E(u)`, then `x i → u` in norm. -/
theorem tendsto_of_tendsto_quadraticEnergy_vadd {ι : Type*} {l : Filter ι}
    {a : V →L⋆[𝕜] V →L[𝕜] 𝕜} (ha : ∀ x y, a x y = star (a y x)) {ℓ : StrongDual 𝕜 V}
    {W : Submodule 𝕜 V} {c : ℝ} (hc : 0 < c)
    (hcoer : ∀ w ∈ W, c * ‖w‖ ^ 2 ≤ RCLike.re (a w w)) {g u : V}
    (hu : u ∈ g +ᵥ (W : Set V)) (hmin : IsMinOn (quadraticEnergy a ℓ) (g +ᵥ (W : Set V)) u)
    {x : ι → V} (hx : ∀ᶠ i in l, x i ∈ g +ᵥ (W : Set V))
    (hE : Tendsto (fun i ↦ quadraticEnergy a ℓ (x i)) l (𝓝 (quadraticEnergy a ℓ u))) :
    Tendsto x l (𝓝 u) :=
  tendsto_of_tendsto_quadraticEnergy_of_sq_le
    (hx.mono fun _ hi ↦ norm_sub_sq_le_quadraticEnergy_sub_div_of_isMinOn_vadd ha hc hcoer hu hi
      hmin) hE

/-- **Norm convergence of near-minimizers on a convex set** `C`: if `a` is Hermitian and
`c`-coercive on differences in `C` (`c > 0`), `u ∈ C` locally minimizes `quadraticEnergy a ℓ` on
`C`, and `x i ∈ C` satisfies `E(x i) → E(u)`, then `x i → u` in norm. -/
theorem tendsto_of_tendsto_quadraticEnergy_convex [NormedSpace ℝ V] [IsScalarTower ℝ 𝕜 V]
    {ι : Type*} {l : Filter ι} {a : V →L⋆[𝕜] V →L[𝕜] 𝕜} (ha : ∀ x y, a x y = star (a y x))
    {ℓ : StrongDual 𝕜 V} {C : Set V} (hC : Convex ℝ C) {c : ℝ} (hc : 0 < c)
    (hcoer : ∀ x ∈ C, ∀ y ∈ C, c * ‖y - x‖ ^ 2 ≤ RCLike.re (a (y - x) (y - x)))
    {u : V} (hu : u ∈ C) (hmin : IsLocalMinOn (quadraticEnergy a ℓ) C u)
    {x : ι → V} (hx : ∀ᶠ i in l, x i ∈ C)
    (hE : Tendsto (fun i ↦ quadraticEnergy a ℓ (x i)) l (𝓝 (quadraticEnergy a ℓ u))) :
    Tendsto x l (𝓝 u) :=
  tendsto_of_tendsto_quadraticEnergy_of_sq_le
    (hx.mono fun _ hi ↦ norm_sub_sq_le_quadraticEnergy_sub_div_of_isLocalMinOn_convex ha hC hc
      hcoer hu hi hmin) hE

/-! ### Bounded sublevels and Lipschitz dependence on the forcing -/

/-- **Bounded sublevels** of a coercive quadratic energy on `S`: if `c * ‖u‖² ≤ Re(a u u)` on `S`
with `c > 0`, then `HasBoundedSublevelsOn (quadraticEnergy a ℓ) S`. No symmetry of `a` is
required. -/
theorem hasBoundedSublevelsOn_quadraticEnergy {a : V →L⋆[𝕜] V →L[𝕜] 𝕜} (ℓ : StrongDual 𝕜 V)
    {S : Set V} {c : ℝ} (hc : 0 < c) (hcoer : ∀ u ∈ S, c * ‖u‖ ^ 2 ≤ RCLike.re (a u u)) :
    HasBoundedSublevelsOn (quadraticEnergy a ℓ) S := by
  rw [hasBoundedSublevelsOn_iff_forall_exists_le_of_le_norm]
  intro b
  refine ⟨max 1 ((2 * ‖ℓ‖ + max b 0) / c), fun u hu hR ↦ ?_⟩
  have h1 : 1 ≤ ‖u‖ := (le_max_left _ _).trans hR
  have h2 : 2 * ‖ℓ‖ + max b 0 ≤ ‖u‖ * c :=
    (div_le_iff₀ hc).mp ((le_max_right _ _).trans hR)
  have hℓ : RCLike.re (ℓ u) ≤ ‖ℓ‖ * ‖u‖ :=
    (le_abs_self _).trans ((RCLike.abs_re_le_norm (ℓ u)).trans (ℓ.le_opNorm u))
  have hb0 : 0 ≤ max b 0 := le_max_right b 0
  have hb1 : b ≤ max b 0 := le_max_left b 0
  have hquad := hcoer u hu
  rw [quadraticEnergy_apply]
  nlinarith

/-- **Bounded sublevels from coercivity on differences.** If `C` is nonempty, `a` is Hermitian,
and `c * ‖y - x‖² ≤ Re(a (y - x) (y - x))` for all `x, y ∈ C` (`c > 0`), then `quadraticEnergy a ℓ`
has bounded sublevels on `C`. -/
theorem hasBoundedSublevelsOn_quadraticEnergy_of_sub_coercive {a : V →L⋆[𝕜] V →L[𝕜] 𝕜}
    (ha : ∀ x y, a x y = star (a y x)) (ℓ : StrongDual 𝕜 V) {C : Set V} (hne : C.Nonempty)
    {c : ℝ} (hc : 0 < c)
    (hcoer : ∀ x ∈ C, ∀ y ∈ C, c * ‖y - x‖ ^ 2 ≤ RCLike.re (a (y - x) (y - x))) :
    HasBoundedSublevelsOn (quadraticEnergy a ℓ) C := by
  rcases hne with ⟨u₀, hu₀⟩
  have hS : HasBoundedSublevelsOn (quadraticEnergy a (ℓ - a u₀)) ((· - u₀) '' C) := by
    refine hasBoundedSublevelsOn_quadraticEnergy (ℓ - a u₀) hc ?_
    rintro _ ⟨u, hu, rfl⟩
    exact hcoer u₀ hu₀ u hu
  rw [hasBoundedSublevelsOn_iff]
  intro b
  have hb := hS.isBounded_sublevel (b - quadraticEnergy a ℓ u₀)
  refine (hb.vadd u₀).subset fun u ⟨hu, hle⟩ ↦ ?_
  rw [mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add, neg_add_eq_sub]
  refine ⟨⟨u, hu, rfl⟩, ?_⟩
  have hshift := quadraticEnergy_add_eq_add_sub ha ℓ u₀ (u - u₀)
  rw [add_sub_cancel] at hshift
  linarith

/-- **Bounded sublevels on an inhomogeneous affine subspace** `g +ᵥ W`: it suffices that `a` be
Hermitian and `c`-coercive (`c > 0`) on the direction submodule `W` alone; `a` may vanish or be
indefinite on the datum `g` (as for shifted elliptic forms with inhomogeneous boundary data). -/
theorem hasBoundedSublevelsOn_quadraticEnergy_vadd {a : V →L⋆[𝕜] V →L[𝕜] 𝕜}
    (ha : ∀ x y, a x y = star (a y x)) (ℓ : StrongDual 𝕜 V) {W : Submodule 𝕜 V} (g : V)
    {c : ℝ} (hc : 0 < c) (hcoer : ∀ w ∈ W, c * ‖w‖ ^ 2 ≤ RCLike.re (a w w)) :
    HasBoundedSublevelsOn (quadraticEnergy a ℓ) (g +ᵥ (W : Set V)) := by
  refine hasBoundedSublevelsOn_quadraticEnergy_of_sub_coercive ha ℓ
    ⟨g + 0, vadd_mem_vadd_set W.zero_mem⟩ hc fun x hx y hy ↦ hcoer (y - x) ?_
  rw [mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add, neg_add_eq_sub] at hx hy
  simpa only [sub_sub_sub_cancel_right] using W.sub_mem hy hx

/-- **`c⁻¹`-Lipschitz dependence of weak solutions on the forcing** relative to a submodule `W`: if
`u₁ - u₂ ∈ W` (for instance `u₁, u₂ ∈ g +ᵥ W`), `a u₁ w = ℓ₁ w` and `a u₂ w = ℓ₂ w` for all
`w ∈ W`, and `c * ‖w‖² ≤ Re(a w w)` on `W` (`c > 0`), then
`‖u₁ - u₂‖ ≤ c⁻¹ * ‖(ℓ₁ - ℓ₂).comp W.subtypeL‖`. No symmetry of `a` is required. -/
theorem norm_sub_le_inv_mul_norm_comp_subtypeL_of_forall_apply_eq {a : V →L⋆[𝕜] V →L[𝕜] 𝕜}
    {ℓ₁ ℓ₂ : StrongDual 𝕜 V} {W : Submodule 𝕜 V} {c : ℝ} (hc : 0 < c)
    (hcoer : ∀ w ∈ W, c * ‖w‖ ^ 2 ≤ RCLike.re (a w w)) {u₁ u₂ : V}
    (hmem : u₁ - u₂ ∈ W) (h₁ : ∀ w ∈ W, a u₁ w = ℓ₁ w) (h₂ : ∀ w ∈ W, a u₂ w = ℓ₂ w) :
    ‖u₁ - u₂‖ ≤ c⁻¹ * ‖(ℓ₁ - ℓ₂).comp W.subtypeL‖ := by
  obtain h0 | hpos := (norm_nonneg (u₁ - u₂)).eq_or_lt
  · rw [← h0]
    positivity
  · have hpair : a (u₁ - u₂) (u₁ - u₂) = ((ℓ₁ - ℓ₂).comp W.subtypeL) ⟨u₁ - u₂, hmem⟩ := by
      rw [a.map_sub, sub_apply, h₁ (u₁ - u₂) hmem, h₂ (u₁ - u₂) hmem]
      rfl
    have hle : c * ‖u₁ - u₂‖ ^ 2 ≤ ‖(ℓ₁ - ℓ₂).comp W.subtypeL‖ * ‖u₁ - u₂‖ := by
      calc c * ‖u₁ - u₂‖ ^ 2 ≤ RCLike.re (a (u₁ - u₂) (u₁ - u₂)) := hcoer (u₁ - u₂) hmem
        _ ≤ ‖a (u₁ - u₂) (u₁ - u₂)‖ :=
            (le_abs_self _).trans (RCLike.abs_re_le_norm _)
        _ = ‖((ℓ₁ - ℓ₂).comp W.subtypeL) ⟨u₁ - u₂, hmem⟩‖ := by rw [hpair]
        _ ≤ ‖(ℓ₁ - ℓ₂).comp W.subtypeL‖ * ‖(⟨u₁ - u₂, hmem⟩ : W)‖ :=
            ((ℓ₁ - ℓ₂).comp W.subtypeL).le_opNorm ⟨u₁ - u₂, hmem⟩
        _ = ‖(ℓ₁ - ℓ₂).comp W.subtypeL‖ * ‖u₁ - u₂‖ := rfl
    have hcancel : c * ‖u₁ - u₂‖ ≤ ‖(ℓ₁ - ℓ₂).comp W.subtypeL‖ := by
      nlinarith
    rwa [← div_eq_inv_mul, le_div_iff₀ hc, mul_comm]

/-- **`c⁻¹`-Lipschitz dependence of weak solutions on the forcing** in the full dual norm:
`‖u₁ - u₂‖ ≤ c⁻¹ * ‖ℓ₁ - ℓ₂‖`. -/
theorem norm_sub_le_inv_mul_norm_sub_of_forall_apply_eq {a : V →L⋆[𝕜] V →L[𝕜] 𝕜}
    {ℓ₁ ℓ₂ : StrongDual 𝕜 V} {W : Submodule 𝕜 V} {c : ℝ} (hc : 0 < c)
    (hcoer : ∀ w ∈ W, c * ‖w‖ ^ 2 ≤ RCLike.re (a w w)) {u₁ u₂ : V}
    (hmem : u₁ - u₂ ∈ W) (h₁ : ∀ w ∈ W, a u₁ w = ℓ₁ w) (h₂ : ∀ w ∈ W, a u₂ w = ℓ₂ w) :
    ‖u₁ - u₂‖ ≤ c⁻¹ * ‖ℓ₁ - ℓ₂‖ := by
  refine (norm_sub_le_inv_mul_norm_comp_subtypeL_of_forall_apply_eq hc hcoer hmem h₁ h₂).trans ?_
  gcongr
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg (ℓ₁ - ℓ₂)) fun w ↦ ?_
  exact (ℓ₁ - ℓ₂).le_opNorm (w : V)

/-- **A priori norm bound** `‖u‖ ≤ c⁻¹ * ‖ℓ‖` for a homogeneous weak solution `u ∈ W` of
`∀ w ∈ W, a u w = ℓ w`. -/
theorem norm_le_inv_mul_norm_of_forall_apply_eq {a : V →L⋆[𝕜] V →L[𝕜] 𝕜}
    {ℓ : StrongDual 𝕜 V} {W : Submodule 𝕜 V} {c : ℝ} (hc : 0 < c)
    (hcoer : ∀ w ∈ W, c * ‖w‖ ^ 2 ≤ RCLike.re (a w w)) {u : V} (hu : u ∈ W)
    (hsol : ∀ w ∈ W, a u w = ℓ w) :
    ‖u‖ ≤ c⁻¹ * ‖ℓ‖ := by
  simpa using norm_sub_le_inv_mul_norm_sub_of_forall_apply_eq (ℓ₁ := ℓ) (ℓ₂ := 0) (u₁ := u)
    (u₂ := 0) hc hcoer (by simpa using hu) hsol (fun _ _ ↦ by simp)

end Coercive

/-! ### Uniqueness and direct-method existence on normed and reflexive spaces -/

section NormedUniquenessAndExistence

variable {𝕜 V : Type*} [RCLike 𝕜] [NormedAddCommGroup V] [NormedSpace 𝕜 V]

/-- **Uniqueness of weak solutions** on an affine subspace `g +ᵥ W` when `a` is `c`-coercive on `W`
(`c > 0`); no symmetry of `a` is required. -/
theorem eq_of_forall_apply_eq_vadd {a : V →L⋆[𝕜] V →L[𝕜] 𝕜} {ℓ : StrongDual 𝕜 V}
    {W : Submodule 𝕜 V} {c : ℝ} (hc : 0 < c)
    (hcoer : ∀ w ∈ W, c * ‖w‖ ^ 2 ≤ RCLike.re (a w w)) {g u₁ u₂ : V}
    (hu₁ : u₁ ∈ g +ᵥ (W : Set V)) (hu₂ : u₂ ∈ g +ᵥ (W : Set V))
    (h₁ : ∀ w ∈ W, a u₁ w = ℓ w) (h₂ : ∀ w ∈ W, a u₂ w = ℓ w) : u₁ = u₂ := by
  have hmem : u₁ - u₂ ∈ W := by
    rw [mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add, neg_add_eq_sub] at hu₁ hu₂
    simpa only [sub_sub_sub_cancel_right] using W.sub_mem hu₁ hu₂
  have hbound := norm_sub_le_inv_mul_norm_sub_of_forall_apply_eq hc hcoer hmem h₁ h₂
  simp only [sub_self, norm_zero, mul_zero] at hbound
  exact sub_eq_zero.mp (norm_le_zero_iff.mp hbound)

/-- **Uniqueness of global weak solutions** when `c * ‖w‖² ≤ Re(a w w)` (`c > 0`). -/
theorem eq_of_forall_apply_eq {a : V →L⋆[𝕜] V →L[𝕜] 𝕜} {ℓ : StrongDual 𝕜 V}
    {c : ℝ} (hc : 0 < c) (hcoer : ∀ w, c * ‖w‖ ^ 2 ≤ RCLike.re (a w w)) {u₁ u₂ : V}
    (h₁ : ∀ v, a u₁ v = ℓ v) (h₂ : ∀ v, a u₂ v = ℓ v) : u₁ = u₂ :=
  eq_of_forall_apply_eq_vadd (W := ⊤) (g := 0) hc (fun w _ ↦ hcoer w)
    (by simp) (by simp) (fun w _ ↦ h₁ w) (fun w _ ↦ h₂ w)

/-- **Uniqueness of local minimizers on a convex set** `C` when `a` is Hermitian and `c`-coercive on
differences in `C` (`c > 0`). -/
theorem eq_of_isLocalMinOn_quadraticEnergy_convex [NormedSpace ℝ V] [IsScalarTower ℝ 𝕜 V]
    {a : V →L⋆[𝕜] V →L[𝕜] 𝕜} (ha : ∀ x y, a x y = star (a y x)) {ℓ : StrongDual 𝕜 V}
    {C : Set V} (hC : Convex ℝ C) {c : ℝ} (hc : 0 < c)
    (hcoer : ∀ x ∈ C, ∀ y ∈ C, c * ‖y - x‖ ^ 2 ≤ RCLike.re (a (y - x) (y - x)))
    {u₁ u₂ : V} (hu₁ : u₁ ∈ C) (hu₂ : u₂ ∈ C)
    (hmin₁ : IsLocalMinOn (quadraticEnergy a ℓ) C u₁)
    (hmin₂ : IsLocalMinOn (quadraticEnergy a ℓ) C u₂) : u₁ = u₂ := by
  have h₁ := mul_norm_sub_sq_le_quadraticEnergy_sub_of_isLocalMinOn_convex ha hC hcoer hu₁ hu₂ hmin₁
  have h₂ := mul_norm_sub_sq_le_quadraticEnergy_sub_of_isLocalMinOn_convex ha hC hcoer hu₂ hu₁ hmin₂
  rw [norm_sub_rev u₂ u₁] at h₁
  have hsq : ‖u₁ - u₂‖ ^ 2 ≤ 0 := by nlinarith
  exact sub_eq_zero.mp (norm_le_zero_iff.mp (sq_eq_zero_iff.mp (le_antisymm hsq (sq_nonneg _))).le)

/-- **Uniqueness of minimizers on an affine subspace** `g +ᵥ W` for a Hermitian form `c`-coercive
on `W` (`c > 0`). -/
theorem eq_of_isMinOn_quadraticEnergy_vadd {a : V →L⋆[𝕜] V →L[𝕜] 𝕜}
    (ha : ∀ x y, a x y = star (a y x)) {ℓ : StrongDual 𝕜 V} {W : Submodule 𝕜 V} {c : ℝ}
    (hc : 0 < c) (hcoer : ∀ w ∈ W, c * ‖w‖ ^ 2 ≤ RCLike.re (a w w)) {g u₁ u₂ : V}
    (hu₁ : u₁ ∈ g +ᵥ (W : Set V)) (hu₂ : u₂ ∈ g +ᵥ (W : Set V))
    (hmin₁ : IsMinOn (quadraticEnergy a ℓ) (g +ᵥ (W : Set V)) u₁)
    (hmin₂ : IsMinOn (quadraticEnergy a ℓ) (g +ᵥ (W : Set V)) u₂) : u₁ = u₂ :=
  eq_of_forall_apply_eq_vadd hc hcoer hu₁ hu₂
    (fun _ hw ↦ apply_eq_of_isMinOn_vadd ha hu₁ hmin₁ hw)
    (fun _ hw ↦ apply_eq_of_isMinOn_vadd ha hu₂ hmin₂ hw)

/-- **Direct-method existence and uniqueness on a closed convex set.** In a reflexive normed space
over `𝕜`, if `a` is Hermitian and `c`-coercive on differences of points in a nonempty closed convex
set `C` (`c > 0`), then `quadraticEnergy a ℓ` attains a unique global minimum on `C`. -/
theorem existsUnique_isMinOn_quadraticEnergy_of_isClosed_convex
    [NormedSpace ℝ V] [IsScalarTower ℝ 𝕜 V]
    (hV : Function.Surjective (inclusionInDoubleDual 𝕜 V))
    {a : V →L⋆[𝕜] V →L[𝕜] 𝕜} (ha : ∀ x y, a x y = star (a y x))
    {C : Set V} (hne : C.Nonempty) (hC : Convex ℝ C) (hclosed : IsClosed C)
    {c : ℝ} (hc : 0 < c)
    (hcoer : ∀ x ∈ C, ∀ y ∈ C, c * ‖y - x‖ ^ 2 ≤ RCLike.re (a (y - x) (y - x)))
    (ℓ : StrongDual 𝕜 V) :
    ∃! u, u ∈ C ∧ IsMinOn (quadraticEnergy a ℓ) C u := by
  have hwclosed : IsClosed (toWeakSpace 𝕜 V '' C) := by
    rw [← hclosed.closure_eq, hC.toWeakSpace_closure 𝕜]
    exact isClosed_closure
  have hpos : ∀ u ∈ C, ∀ v ∈ C, 0 ≤ RCLike.re (a (u - v) (u - v)) := fun u hu v hv ↦
    (mul_nonneg hc.le (sq_nonneg _)).trans (hcoer v hv u hu)
  obtain ⟨u, hu, hmin⟩ := exists_isMinOn_of_weak_closed hV hne hwclosed
    (lowerSemicontinuousOn_quadraticEnergy_comp_toWeakSpace_symm ha hC hclosed hpos ℓ)
    (hasBoundedSublevelsOn_quadraticEnergy_of_sub_coercive ha ℓ hne hc hcoer)
  exact ⟨u, ⟨hu, hmin⟩, fun y ⟨hy, hminy⟩ ↦
    eq_of_isLocalMinOn_quadraticEnergy_convex ha hC hc hcoer hy hu
      hminy.isLocalMinOn hmin.isLocalMinOn⟩

/-- **Direct-method existence and uniqueness of constrained weak solutions** on an affine coset
`g +ᵥ W` of a closed `𝕜`-submodule `W` in a reflexive space over `𝕜`, when `a` is Hermitian and
`c`-coercive on `W` (`c > 0`); `a` need not be nonnegative outside `W`. -/
theorem existsUnique_vadd_forall_apply_eq_of_isClosed
    (hV : Function.Surjective (inclusionInDoubleDual 𝕜 V))
    {a : V →L⋆[𝕜] V →L[𝕜] 𝕜} (ha : ∀ x y, a x y = star (a y x))
    {W : Submodule 𝕜 V} (hW : IsClosed (W : Set V))
    {c : ℝ} (hc : 0 < c) (hcoer : ∀ w ∈ W, c * ‖w‖ ^ 2 ≤ RCLike.re (a w w))
    (g : V) (ℓ : StrongDual 𝕜 V) :
    ∃! u, u ∈ g +ᵥ (W : Set V) ∧ ∀ w ∈ W, a u w = ℓ w := by
  let : NormedSpace ℝ V := NormedSpace.restrictScalars ℝ 𝕜 V
  have : IsScalarTower ℝ 𝕜 V := IsScalarTower.restrictScalars ℝ 𝕜 V
  have hconv : Convex ℝ (g +ᵥ (W : Set V)) :=
    (W.restrictScalars ℝ).convex.vadd g
  have hclosed : IsClosed (g +ᵥ (W : Set V)) := hW.vadd g
  have hwclosed : IsClosed (toWeakSpace 𝕜 V '' (g +ᵥ (W : Set V))) := by
    rw [← hclosed.closure_eq, hconv.toWeakSpace_closure 𝕜]
    exact isClosed_closure
  have hne : (g +ᵥ (W : Set V)).Nonempty := ⟨g + 0, vadd_mem_vadd_set W.zero_mem⟩
  have hpos : ∀ u ∈ g +ᵥ (W : Set V), ∀ v ∈ g +ᵥ (W : Set V),
      0 ≤ RCLike.re (a (u - v) (u - v)) := fun u hu v hv ↦ by
    have huv : u - v ∈ W := by
      rw [mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add, neg_add_eq_sub] at hu hv
      simpa only [sub_sub_sub_cancel_right] using W.sub_mem hu hv
    exact (mul_nonneg hc.le (sq_nonneg _)).trans (hcoer (u - v) huv)
  obtain ⟨u, hu, hmin⟩ := exists_isMinOn_of_weak_closed hV hne hwclosed
    (lowerSemicontinuousOn_quadraticEnergy_comp_toWeakSpace_symm ha hconv hclosed hpos ℓ)
    (hasBoundedSublevelsOn_quadraticEnergy_vadd ha ℓ g hc hcoer)
  refine ⟨u, ⟨hu, fun _ hw ↦ apply_eq_of_isMinOn_vadd ha hu hmin hw⟩, fun y ⟨hy, hsoly⟩ ↦ ?_⟩
  exact eq_of_forall_apply_eq_vadd hc hcoer hy hu hsoly
    (fun _ hw ↦ apply_eq_of_isMinOn_vadd ha hu hmin hw)

end NormedUniquenessAndExistence

end TauCeti

/-! ### Identification at `𝕜 = ℝ` with Mathlib and Tau Ceti Lax--Milgram solutions -/

namespace IsCoercive

variable {V H : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [SeminormedAddCommGroup H] [InnerProductSpace ℝ H]
  {B : V →L[ℝ] V →L[ℝ] ℝ}

/-- For a symmetric coercive bilinear form `B` on a real Hilbert space, the Lax--Milgram functional
solution `hB.solutionOfFunctional ℓ` minimizes `TauCeti.quadraticEnergy B ℓ` over `V`
(Hunter, Theorem 4.20). -/
theorem isMinOn_quadraticEnergy_solutionOfFunctional (hB : IsCoercive B)
    (hsymm : ∀ u v, B u v = B v u) (ℓ : StrongDual ℝ V) :
    IsMinOn (TauCeti.quadraticEnergy B ℓ) Set.univ (hB.solutionOfFunctional ℓ) := by
  have hstar : ∀ u v, B u v = star (B v u) := fun u v ↦ by simpa using hsymm u v
  have hpos : ∀ w, 0 ≤ RCLike.re (B w w) := fun w ↦ by simpa using hB.apply_self_nonneg w
  exact (TauCeti.isMinOn_univ_quadraticEnergy_iff hstar hpos).mpr
    (hB.apply_solutionOfFunctional_eq ℓ)

/-- **Characterization of global minimizers via `IsCoercive.solutionOfFunctional`**: for a symmetric
coercive real bilinear form `B`, `u` minimizes `TauCeti.quadraticEnergy B ℓ` on `Set.univ` if and
only if `u = hB.solutionOfFunctional ℓ`. -/
theorem isMinOn_quadraticEnergy_iff_eq_solutionOfFunctional (hB : IsCoercive B)
    (hsymm : ∀ u v, B u v = B v u) (ℓ : StrongDual ℝ V) {u : V} :
    IsMinOn (TauCeti.quadraticEnergy B ℓ) Set.univ u ↔ u = hB.solutionOfFunctional ℓ := by
  have hstar : ∀ x y, B x y = star (B y x) := fun x y ↦ by simpa using hsymm x y
  have hpos : ∀ w, 0 ≤ RCLike.re (B w w) := fun w ↦ by simpa using hB.apply_self_nonneg w
  rw [TauCeti.isMinOn_univ_quadraticEnergy_iff hstar hpos]
  exact ⟨fun hu ↦ hB.eq_solutionOfFunctional hu,
    fun h ↦ h ▸ hB.apply_solutionOfFunctional_eq ℓ⟩

/-- **Characterization of global minimizers via Mathlib's
`IsCoercive.continuousLinearEquivOfBilin`** and the Fréchet--Riesz equivalence
`InnerProductSpace.toDual ℝ V`. -/
theorem isMinOn_quadraticEnergy_iff_eq_continuousLinearEquivOfBilin_symm (hB : IsCoercive B)
    (hsymm : ∀ u v, B u v = B v u) (ℓ : StrongDual ℝ V) {u : V} :
    IsMinOn (TauCeti.quadraticEnergy B ℓ) Set.univ u ↔
      u = hB.continuousLinearEquivOfBilin.symm ((InnerProductSpace.toDual ℝ V).symm ℓ) := by
  rw [hB.isMinOn_quadraticEnergy_iff_eq_solutionOfFunctional hsymm ℓ,
    solutionOfFunctional_apply, solutionOfInner_def]

/-- **Characterization of global minimizers for represented forcing `⟪F, ·⟫_ℝ`** via
`IsCoercive.solutionOfInner`. -/
theorem isMinOn_quadraticEnergy_toDual_iff_eq_solutionOfInner (hB : IsCoercive B)
    (hsymm : ∀ u v, B u v = B v u) (F : V) {u : V} :
    IsMinOn (TauCeti.quadraticEnergy B (InnerProductSpace.toDual ℝ V F)) Set.univ u ↔
      u = hB.solutionOfInner F := by
  rw [hB.isMinOn_quadraticEnergy_iff_eq_solutionOfFunctional hsymm, solutionOfFunctional_toDual]

/-- For forcing `v ↦ ⟪h, J v⟫_ℝ` (`ContinuousLinearMap.toSesqForm J h`), the solution map
`hB.formSolutionMap J h` minimizes `TauCeti.quadraticEnergy B (ContinuousLinearMap.toSesqForm J h)`
on `Set.univ`. -/
theorem isMinOn_quadraticEnergy_toSesqForm_formSolutionMap (hB : IsCoercive B)
    (hsymm : ∀ u v, B u v = B v u) (J : V →L[ℝ] H) (h : H) :
    IsMinOn (TauCeti.quadraticEnergy B (ContinuousLinearMap.toSesqForm J h)) Set.univ
      (hB.formSolutionMap J h) := by
  rw [formSolutionMap_apply]
  exact hB.isMinOn_quadraticEnergy_solutionOfFunctional hsymm (ContinuousLinearMap.toSesqForm J h)

/-- **Characterization of global minimizers for forcing `v ↦ ⟪h, J v⟫_ℝ`** via
`IsCoercive.formSolutionMap`: `u` minimizes
`TauCeti.quadraticEnergy B (ContinuousLinearMap.toSesqForm J h)` on `Set.univ` if and only if
`u = hB.formSolutionMap J h`. -/
theorem isMinOn_quadraticEnergy_toSesqForm_iff_eq_formSolutionMap (hB : IsCoercive B)
    (hsymm : ∀ u v, B u v = B v u) (J : V →L[ℝ] H) (h : H) {u : V} :
    IsMinOn (TauCeti.quadraticEnergy B (ContinuousLinearMap.toSesqForm J h)) Set.univ u ↔
      u = hB.formSolutionMap J h := by
  rw [hB.isMinOn_quadraticEnergy_iff_eq_solutionOfFunctional hsymm, formSolutionMap_apply]

/-- Minimum value of `TauCeti.quadraticEnergy B ℓ` at the Lax--Milgram solution
`hB.solutionOfFunctional ℓ`. -/
@[simp]
theorem quadraticEnergy_solutionOfFunctional (hB : IsCoercive B) (ℓ : StrongDual ℝ V) :
    TauCeti.quadraticEnergy B ℓ (hB.solutionOfFunctional ℓ) = -ℓ (hB.solutionOfFunctional ℓ) := by
  rw [TauCeti.quadraticEnergy_real_apply, hB.apply_solutionOfFunctional_eq]
  ring

/-- Minimum value of `TauCeti.quadraticEnergy B (ContinuousLinearMap.toSesqForm J h)` at
`hB.formSolutionMap J h`. -/
theorem quadraticEnergy_formSolutionMap (hB : IsCoercive B) (J : V →L[ℝ] H) (h : H) :
    TauCeti.quadraticEnergy B (ContinuousLinearMap.toSesqForm J h) (hB.formSolutionMap J h) =
      -⟪h, J (hB.formSolutionMap J h)⟫_ℝ := by
  rw [formSolutionMap_apply, quadraticEnergy_solutionOfFunctional, ← formSolutionMap_apply]
  rfl

end IsCoercive

end
