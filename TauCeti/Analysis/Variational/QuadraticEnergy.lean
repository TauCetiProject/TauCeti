/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import TauCeti.Analysis.LocallyConvex.WeakSpace
public import TauCeti.Analysis.RCLike.SesquilinearForm
public import TauCeti.Analysis.Variational.DirectMethod
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import TauCeti.Algebra.Group.Subgroup.Pointwise
import TauCeti.Algebra.Group.Subsemigroup.Pointwise
import TauCeti.Topology.MetricSpace.Pseudo.Lemmas

/-!
# Quadratic energies, weak Euler--Lagrange equations, and coercive minimization

Let `V` be a seminormed space over `𝕜` (`ℝ` or `ℂ`, written `[RCLike 𝕜]`), `a : V →L⋆[𝕜] V →L[𝕜] 𝕜`
a bounded sesquilinear form (conjugate-linear in its first slot and `𝕜`-linear in its second), and
`ℓ : StrongDual 𝕜 V` a continuous `𝕜`-linear functional. The associated **quadratic energy** is the
real-valued functional

`quadraticEnergy a ℓ u = RCLike.re (a u u) - 2 * RCLike.re (ℓ u)`.

When `a` is Hermitian (`∀ u v, a u v = star (a v u)`), expanding `quadraticEnergy a ℓ (u + v)`
isolates the linear variation `2 Re(a u v - ℓ v)` from the quadratic remainder `q(v) = Re(a v v)`:

* **Affine shift and restriction.** For a Hermitian form, translating by a datum `g` shifts the
  forcing from `ℓ` to `ℓ - a g`:
  `quadraticEnergy a ℓ (g + w) = quadraticEnergy a ℓ g + quadraticEnergy a (ℓ - a g) w`, reducing
  inhomogeneous affine constraints `g +ᵥ W` to homogeneous subspaces `W`.
* **First variation and weak Euler--Lagrange equations.** On a normed space over `𝕜` equipped with
  its compatible real scalar action, `quadraticEnergy a ℓ` is smooth over `ℝ`, with strict Fréchet
  derivative `v ↦ 2 Re(a u v - ℓ v)` when `a` is Hermitian. In any seminormed space over `𝕜` with
  Hermitian `a`, testing along rays shows that a local minimizer `u` on a convex set `C` satisfies
  the variational inequality `Re(ℓ (v - u)) ≤ Re(a u (v - u))` for `v ∈ C`, and a local minimizer on
  an affine subspace `g +ᵥ W` of a `𝕜`-submodule `W` satisfies the full `𝕜`-valued weak equation
  `a u w = ℓ w` for all `w ∈ W`: testing `w` gives the real part, and testing `RCLike.I • w`
  recovers the imaginary part.
* **Exact energy gap and converse.** For Hermitian `a`, at any solution of `a u w = ℓ w` the linear
  term cancels and `quadraticEnergy a ℓ (u + w) - quadraticEnergy a ℓ u = Re(a w w)`. When `q ≥ 0`
  on `W`, the weak equation on `W` and global minimality on `g +ᵥ W` are therefore equivalent.
* **Coercive forms and direct-method existence.** Even without symmetry of `a`, if
  `c * ‖w‖² ≤ Re(a w w)` (`c > 0`) on differences, local minimality bounds
  `c * ‖v - u‖² ≤ E(v) - E(u)`, giving norm convergence of near-minimizing sequences at rate
  `‖uₙ - u‖² ≤ (E(uₙ) - E(u)) / c` and bounded sublevels on any seminormed space `V`. When `V` is a
  normed space (`[NormedAddCommGroup V]`), this yields uniqueness of local minimizers, and on a
  reflexive normed space weak lower semicontinuity and the direct method yield existence and
  uniqueness of constrained minimizers (and, when `a` is Hermitian, of weak solutions on closed
  affine subspaces `g +ᵥ W` and globally on `V`).

Real Hilbert-space identifications with `IsCoercive.solutionOfFunctional`,
`IsCoercive.solutionOfInner`, and `IsCoercive.formSolutionMap` are proved in
`TauCeti.Analysis.InnerProductSpace.Variational.QuadraticEnergy`.

## Main declarations

* `TauCeti.quadraticEnergy`: the energy `u ↦ RCLike.re (a u u) - 2 * RCLike.re (ℓ u)`.
* `TauCeti.quadraticEnergy_add_real_smul_sub_of_eq_star`: exact real-line expansion
  `E(u + t • v) - E(u) = 2 * t * Re(a u v - ℓ v) + t² * Re(a v v)` for Hermitian `a`.
* `TauCeti.hasStrictFDerivAt_quadraticEnergy`: strict real Fréchet derivative of `quadraticEnergy`.
* `TauCeti.apply_eq_of_isLocalMinOn_quadraticEnergy_vadd` and
  `TauCeti.isMinOn_quadraticEnergy_vadd_iff`: weak Euler--Lagrange equation on `g +ᵥ W` and
  equivalence with minimality when `a` is Hermitian and `q ≥ 0` on `W`.
* `TauCeti.norm_sub_sq_le_quadraticEnergy_sub_div` and
  `TauCeti.tendsto_of_tendsto_quadraticEnergy`: coercivity distance rate and norm convergence of
  near-minimizers.
* `TauCeti.existsUnique_isMinOn_quadraticEnergy_of_isClosed_convex` and
  `ContinuousLinearMap.existsUnique_vadd_forall_apply_eq_of_isClosed_of_coercive`: direct-method
  existence and uniqueness of constrained minimizers and weak solutions on reflexive normed spaces.

## References

* J. K. Hunter, *Notes on Partial Differential Equations*, Chapter 4: Definition 4.3,
  Proposition 4.5, Corollary 4.6, and Theorem 4.20.
-/

public section

noncomputable section

open Filter Set Bornology NormedSpace
open scoped Topology Pointwise

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

/-- Negating both the form `a` and the forcing `ℓ` negates `quadraticEnergy`. -/
@[simp]
theorem quadraticEnergy_neg_form_functional (a : V →L⋆[𝕜] V →L[𝕜] 𝕜) (ℓ : StrongDual 𝕜 V) (u : V) :
    quadraticEnergy (-a) (-ℓ) u = -quadraticEnergy a ℓ u := by
  simp only [quadraticEnergy_apply, neg_apply, map_neg]
  ring

/-- `quadraticEnergy` preserves subtraction jointly in the form `a` and the forcing `ℓ`. -/
theorem quadraticEnergy_sub_form_functional (a₁ a₂ : V →L⋆[𝕜] V →L[𝕜] 𝕜)
    (ℓ₁ ℓ₂ : StrongDual 𝕜 V) (u : V) :
    quadraticEnergy (a₁ - a₂) (ℓ₁ - ℓ₂) u =
      quadraticEnergy a₁ ℓ₁ u - quadraticEnergy a₂ ℓ₂ u := by
  simp only [quadraticEnergy_apply, sub_apply, map_sub]
  ring

/-- Scaling both the form `a` and the forcing `ℓ` by a real scalar `r` scales `quadraticEnergy` by
`r`. -/
@[simp]
theorem quadraticEnergy_smul_form_functional (r : ℝ) (a : V →L⋆[𝕜] V →L[𝕜] 𝕜)
    (ℓ : StrongDual 𝕜 V) (u : V) :
    quadraticEnergy (r • a) (r • ℓ) u = r * quadraticEnergy a ℓ u := by
  simp only [quadraticEnergy_apply, smul_apply, Algebra.smul_def,
    RCLike.algebraMap_eq_ofReal, RCLike.re_ofReal_mul]
  ring

/-- Pullback of `quadraticEnergy` along a continuous `𝕜`-linear map `L : W →L[𝕜] V`. -/
@[simp]
theorem quadraticEnergy_comp {W : Type*} [SeminormedAddCommGroup W] [NormedSpace 𝕜 W]
    (a : V →L⋆[𝕜] V →L[𝕜] 𝕜) (ℓ : StrongDual 𝕜 V) (L : W →L[𝕜] V) (w : W) :
    quadraticEnergy (a.bilinearComp L L) (ℓ.comp L) w = quadraticEnergy a ℓ (L w) := by
  simp [quadraticEnergy_apply]

/-- Over `ℝ`, `quadraticEnergy B ℓ u` is `B u u - 2 * ℓ u`. -/
theorem quadraticEnergy_real_apply {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]
    (B : E →L[ℝ] E →L[ℝ] ℝ) (ℓ : StrongDual ℝ E) (u : E) :
    quadraticEnergy B ℓ u = B u u - 2 * ℓ u := by
  simp [quadraticEnergy_apply]

/-- Viewing `V` over `ℝ`, the real quadratic energy of `a.reBilin` and `Re ∘ ℓ` coincides with
`quadraticEnergy a ℓ`. -/
@[simp]
theorem quadraticEnergy_reBilin [NormedSpace ℝ V] [IsScalarTower ℝ 𝕜 V]
    (a : V →L⋆[𝕜] V →L[𝕜] 𝕜) (ℓ : StrongDual 𝕜 V) (u : V) :
    quadraticEnergy a.reBilin (RCLike.reCLM.comp (ℓ.restrictScalars ℝ)) u =
      quadraticEnergy a ℓ u := by
  rw [quadraticEnergy_real_apply]
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

/-- Real-scalar-line expansion for a Hermitian form `a` via coercion `(t : 𝕜) • v`, requiring no
`Module ℝ V` instance. -/
theorem quadraticEnergy_add_ofReal_smul_sub_of_eq_star {a : V →L⋆[𝕜] V →L[𝕜] 𝕜}
    (ha : ∀ x y, a x y = star (a y x)) (ℓ : StrongDual 𝕜 V) (u v : V) (t : ℝ) :
    quadraticEnergy a ℓ (u + (t : 𝕜) • v) - quadraticEnergy a ℓ u =
      2 * t * RCLike.re (a u v - ℓ v) + t ^ 2 * RCLike.re (a v v) := by
  rw [quadraticEnergy_add_smul_sub_of_eq_star ha ℓ u v (t : 𝕜), RCLike.re_ofReal_mul,
    RCLike.norm_ofReal, sq_abs]
  ring

section RealScalar

variable [Module ℝ V] [IsScalarTower ℝ 𝕜 V]

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
`ℓ` and without assuming symmetry of `a`. -/
theorem quadraticEnergy_combo_add_mul_sub (a : V →L⋆[𝕜] V →L[𝕜] 𝕜) (ℓ : StrongDual 𝕜 V)
    {t₁ t₂ : ℝ} (ht : t₁ + t₂ = 1) (u v : V) :
    quadraticEnergy a ℓ (t₁ • u + t₂ • v) +
        t₁ * t₂ * RCLike.re (a (u - v) (u - v)) =
      t₁ * quadraticEnergy a ℓ u + t₂ * quadraticEnergy a ℓ v := by
  have hq := a.toLinearMap₁₂.re_apply_combo_self_add_mul_sub ht u v
  simp only [ContinuousLinearMap.toLinearMap₁₂_apply_apply_apply] at hq
  have hℓ : RCLike.re (ℓ (t₁ • u + t₂ • v)) =
      t₁ * RCLike.re (ℓ u) + t₂ * RCLike.re (ℓ v) := by
    rw [map_add, ← algebraMap_smul 𝕜 t₁ u, ← algebraMap_smul 𝕜 t₂ v, map_smul, map_smul,
      RCLike.algebraMap_eq_ofReal]
    simp
  simp only [quadraticEnergy_apply, hℓ]
  linarith

/-- One-dimensional derivative of `s ↦ quadraticEnergy a ℓ (u + s • v)` at `t : ℝ` for a Hermitian
form `a`. -/
theorem hasDerivAt_quadraticEnergy_add_smul {a : V →L⋆[𝕜] V →L[𝕜] 𝕜}
    (ha : ∀ x y, a x y = star (a y x)) (ℓ : StrongDual 𝕜 V) (u v : V) (t : ℝ) :
    HasDerivAt (fun s : ℝ ↦ quadraticEnergy a ℓ (u + s • v))
      (2 * RCLike.re (a u v - ℓ v) + 2 * t * RCLike.re (a v v)) t := by
  have hpoly : (fun s : ℝ ↦ quadraticEnergy a ℓ (u + s • v)) =
      fun s : ℝ ↦ quadraticEnergy a ℓ u +
        2 * RCLike.re (a u v - ℓ v) * s + RCLike.re (a v v) * s ^ 2 := by
    ext s
    linarith [quadraticEnergy_add_real_smul_sub_of_eq_star ha ℓ u v s]
  rw [hpoly]
  have hd := ((hasDerivAt_const t (quadraticEnergy a ℓ u)).add
    ((hasDerivAt_id' t).const_mul (2 * RCLike.re (a u v - ℓ v)))).add
    ((hasDerivAt_pow 2 t).const_mul (RCLike.re (a v v)))
  exact (by ring : 0 + 2 * RCLike.re (a u v - ℓ v) * 1 +
    RCLike.re (a v v) * ((2 : ℕ) * t ^ (2 - 1)) =
    2 * RCLike.re (a u v - ℓ v) + 2 * t * RCLike.re (a v v)) ▸ hd

end RealScalar

/-! ### Continuity, convexity, and weak lower semicontinuity -/

/-- `quadraticEnergy a ℓ` is norm-continuous for every continuous sesquilinear form `a` and
continuous linear functional `ℓ`. -/
@[fun_prop]
theorem continuous_quadraticEnergy (a : V →L⋆[𝕜] V →L[𝕜] 𝕜) (ℓ : StrongDual 𝕜 V) :
    Continuous (quadraticEnergy a ℓ) :=
  a.continuous_re_apply_self.sub (continuous_const.mul (RCLike.reCLM.continuous.comp ℓ.continuous))

/-- If `a` is nonnegative on differences of points of a convex set `C`, then `quadraticEnergy a ℓ`
is convex on `C`. No symmetry of `a` is required. -/
theorem convexOn_quadraticEnergy_of_sub_nonneg [Module ℝ V] [IsScalarTower ℝ 𝕜 V]
    {a : V →L⋆[𝕜] V →L[𝕜] 𝕜} {C : Set V} (hC : Convex ℝ C)
    (hpos : ∀ u ∈ C, ∀ v ∈ C, 0 ≤ RCLike.re (a (u - v) (u - v))) (ℓ : StrongDual 𝕜 V) :
    ConvexOn ℝ C (quadraticEnergy a ℓ) := by
  refine ⟨hC, fun u hu v hv t₁ t₂ ht₁ ht₂ ht ↦ ?_⟩
  simp only [smul_eq_mul]
  have hdiff : 0 ≤ t₁ * t₂ * RCLike.re (a (u - v) (u - v)) :=
    mul_nonneg (mul_nonneg ht₁ ht₂) (hpos u hu v hv)
  linarith [quadraticEnergy_combo_add_mul_sub a ℓ ht u v]

/-- If `∀ u, 0 ≤ Re(a u u)`, then `quadraticEnergy a ℓ` is convex on `V`. No symmetry of `a` is
required. -/
theorem convexOn_quadraticEnergy [Module ℝ V] [IsScalarTower ℝ 𝕜 V]
    {a : V →L⋆[𝕜] V →L[𝕜] 𝕜} (hpos : ∀ u, 0 ≤ RCLike.re (a u u)) (ℓ : StrongDual 𝕜 V) :
    ConvexOn ℝ Set.univ (quadraticEnergy a ℓ) :=
  convexOn_quadraticEnergy_of_sub_nonneg convex_univ (fun u _ v _ ↦ hpos (u - v)) ℓ

/-- If `a` is nonnegative on differences of points in a convex set `C`, then `quadraticEnergy a ℓ`
is lower semicontinuous on `toWeakSpace 𝕜 V '' C` in the `𝕜`-weak topology; neither symmetry of `a`,
nonnegativity outside `C`, nor closedness of `C` is required. -/
theorem lowerSemicontinuousOn_quadraticEnergy_comp_toWeakSpace_symm
    [Module ℝ V] [IsScalarTower ℝ 𝕜 V]
    {a : V →L⋆[𝕜] V →L[𝕜] 𝕜} {C : Set V} (hC : Convex ℝ C)
    (hpos : ∀ u ∈ C, ∀ v ∈ C, 0 ≤ RCLike.re (a (u - v) (u - v))) (ℓ : StrongDual 𝕜 V) :
    LowerSemicontinuousOn
      (fun u : WeakSpace 𝕜 V ↦ quadraticEnergy a ℓ ((toWeakSpace 𝕜 V).symm u))
      (toWeakSpace 𝕜 V '' C) := by
  have : LocallyConvexSpace ℝ V := NormedSpace.toLocallyConvexSpace' 𝕜
  exact (convexOn_quadraticEnergy_of_sub_nonneg hC hpos ℓ).quasiconvexOn
    |>.lowerSemicontinuousOn_comp_toWeakSpace_symm
      (continuous_quadraticEnergy a ℓ).continuousOn.lowerSemicontinuousOn

/-- For a continuous sesquilinear form `a` with nonnegative real diagonal, `quadraticEnergy a ℓ` is
lower semicontinuous with respect to the `𝕜`-weak topology `WeakSpace 𝕜 V`. No symmetry of `a` is
required. -/
theorem lowerSemicontinuous_quadraticEnergy_comp_toWeakSpace_symm
    {a : V →L⋆[𝕜] V →L[𝕜] 𝕜} (hpos : ∀ u, 0 ≤ RCLike.re (a u u)) (ℓ : StrongDual 𝕜 V) :
    LowerSemicontinuous
      (fun u : WeakSpace 𝕜 V ↦ quadraticEnergy a ℓ ((toWeakSpace 𝕜 V).symm u)) := by
  let : NormedSpace ℝ V := NormedSpace.restrictScalars ℝ 𝕜 V
  have : IsScalarTower ℝ 𝕜 V := IsScalarTower.restrictScalars ℝ 𝕜 V
  exact (convexOn_quadraticEnergy hpos ℓ).quasiconvexOn.lowerSemicontinuous_comp_toWeakSpace_symm
    (continuous_quadraticEnergy a ℓ).lowerSemicontinuous

end Basic

/-! ### Smoothness and real Fréchet derivatives -/

section Calculus

variable {𝕜 V : Type*} [RCLike 𝕜] [NormedAddCommGroup V] [NormedSpace 𝕜 V]
  [NormedSpace ℝ V] [IsScalarTower ℝ 𝕜 V] {n : WithTop ℕ∞}

/-- `quadraticEnergy a ℓ` is `C^n` over `ℝ` for every `n`. -/
@[fun_prop]
theorem contDiff_quadraticEnergy (a : V →L⋆[𝕜] V →L[𝕜] 𝕜) (ℓ : StrongDual 𝕜 V) :
    ContDiff ℝ n (quadraticEnergy a ℓ) :=
  a.contDiff_re_apply_self.sub
    (contDiff_const.mul (RCLike.reCLM.contDiff.comp (ℓ.restrictScalars ℝ).contDiff))

/-- `quadraticEnergy a ℓ` is Fréchet differentiable over `ℝ`. -/
@[fun_prop]
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
    ((2 : ℝ) • RCLike.reCLM.comp (ℓ.restrictScalars ℝ)).hasStrictFDerivAt.congr_of_eventuallyEq
      (Eventually.of_forall fun _ ↦ by simp)
  have hderiv : (2 : ℝ) • RCLike.reCLM.comp ((a u).restrictScalars ℝ) -
      (2 : ℝ) • RCLike.reCLM.comp (ℓ.restrictScalars ℝ) =
      (2 : ℝ) • RCLike.reCLM.comp ((a u - ℓ).restrictScalars ℝ) := by
    ext v
    simp
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

/-- Directional formula for the real Fréchet derivative of `quadraticEnergy a ℓ` for a Hermitian
form `a`: `fderiv ℝ (quadraticEnergy a ℓ) u v = 2 * Re(a u v - ℓ v)`. -/
theorem fderiv_quadraticEnergy_apply {a : V →L⋆[𝕜] V →L[𝕜] 𝕜}
    (ha : ∀ x y, a x y = star (a y x)) (ℓ : StrongDual 𝕜 V) (u v : V) :
    fderiv ℝ (quadraticEnergy a ℓ) u v = 2 * RCLike.re (a u v - ℓ v) := by
  rw [fderiv_quadraticEnergy ha]
  simp

end Calculus

/-! ### First variation, variational inequality, weak Euler--Lagrange equation, and energy gap -/

section FirstVariation

variable {𝕜 V : Type*} [RCLike 𝕜] [SeminormedAddCommGroup V] [NormedSpace 𝕜 V]

/-- **One-sided ray variation.** For a Hermitian form `a`, if `u` is a local minimizer of
`quadraticEnergy a ℓ` on `S` and `u + (t : 𝕜) • w ∈ S` for all sufficiently small `t > 0`, then
`Re(ℓ w) ≤ Re(a u w)`. -/
theorem le_re_apply_of_isLocalMinOn_quadraticEnergy_ray {a : V →L⋆[𝕜] V →L[𝕜] 𝕜}
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
      linarith
    have hpos2 : (0 : ℝ) < 2 * t := mul_pos zero_lt_two htpos
    linarith [nonneg_of_mul_nonneg_right hmul hpos2]
  have hlim : Tendsto (fun t : ℝ ↦ -(t / 2 * RCLike.re (a w w))) (𝓝[>] 0) (𝓝 0) := by
    have hc : Continuous (fun t : ℝ ↦ -(t / 2 * RCLike.re (a w w))) := by fun_prop
    simpa using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
  have h0 : 0 ≤ RCLike.re (a u w - ℓ w) := le_of_tendsto hlim hle
  rwa [map_sub, sub_nonneg] at h0

/-- **Two-sided line variation.** For a Hermitian form `a`, if `u` is a local minimizer of
`quadraticEnergy a ℓ` on `S` and `u + (t : 𝕜) • w ∈ S` for all `t : ℝ` near `0`, then
`Re(a u w) = Re(ℓ w)`. -/
theorem re_apply_eq_re_of_isLocalMinOn_quadraticEnergy_line {a : V →L⋆[𝕜] V →L[𝕜] 𝕜}
    (ha : ∀ x y, a x y = star (a y x)) {ℓ : StrongDual 𝕜 V} {S : Set V} {u w : V}
    (hmin : IsLocalMinOn (quadraticEnergy a ℓ) S u)
    (hline : ∀ᶠ t : ℝ in 𝓝 0, u + (t : 𝕜) • w ∈ S) :
    RCLike.re (a u w) = RCLike.re (ℓ w) := by
  have h₁ := le_re_apply_of_isLocalMinOn_quadraticEnergy_ray ha hmin
    (nhdsWithin_le_nhds hline)
  have hneg : ∀ᶠ t : ℝ in 𝓝[>] 0, u + (t : 𝕜) • (-w) ∈ S := by
    have hnt : Tendsto (fun t : ℝ ↦ -t) (𝓝[>] 0) (𝓝 0) := by
      simpa only [neg_zero] using (continuous_neg.tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds
    filter_upwards [hnt.eventually hline] with t ht
    have ht' : u + ((-t : ℝ) : 𝕜) • w ∈ S := ht
    simpa only [RCLike.ofReal_neg, neg_smul, smul_neg] using ht'
  have h₂ := le_re_apply_of_isLocalMinOn_quadraticEnergy_ray ha hmin hneg
  simp only [map_neg] at h₂
  linarith

/-- **Variational inequality on a convex constraint** for a Hermitian form `a`: if `u ∈ C` is a
local minimizer of `quadraticEnergy a ℓ` on a convex set `C`, then `Re(ℓ (v - u)) ≤ Re(a u (v - u))`
for every `v ∈ C`. -/
theorem le_re_apply_sub_of_isLocalMinOn_quadraticEnergy_convex [Module ℝ V] [IsScalarTower ℝ 𝕜 V]
    {a : V →L⋆[𝕜] V →L[𝕜] 𝕜} (ha : ∀ x y, a x y = star (a y x)) {ℓ : StrongDual 𝕜 V}
    {C : Set V} (hC : Convex ℝ C) {u : V} (hu : u ∈ C)
    (hmin : IsLocalMinOn (quadraticEnergy a ℓ) C u) {v : V} (hv : v ∈ C) :
    RCLike.re (ℓ (v - u)) ≤ RCLike.re (a u (v - u)) := by
  refine le_re_apply_of_isLocalMinOn_quadraticEnergy_ray ha hmin ?_
  filter_upwards [Ioo_mem_nhdsGT zero_lt_one] with t ht
  rw [← RCLike.algebraMap_eq_ofReal, algebraMap_smul]
  exact hC.add_smul_sub_mem hu hv (Ioo_subset_Icc_self ht)

/-- **Two-sided real-part variation** along a real affine subspace for a Hermitian form `a`: at a
local minimizer `u ∈ g +ᵥ W` of `quadraticEnergy a ℓ` on `g +ᵥ W` (`W : Submodule ℝ V`),
`Re(a u w) = Re(ℓ w)` for all `w ∈ W`. -/
theorem re_apply_eq_re_of_isLocalMinOn_quadraticEnergy_vadd_real
    [Module ℝ V] [IsScalarTower ℝ 𝕜 V] {a : V →L⋆[𝕜] V →L[𝕜] 𝕜}
    (ha : ∀ x y, a x y = star (a y x)) {ℓ : StrongDual 𝕜 V} {W : Submodule ℝ V} {g u : V}
    (hu : u ∈ g +ᵥ (W : Set V))
    (hmin : IsLocalMinOn (quadraticEnergy a ℓ) (g +ᵥ (W : Set V)) u) {w : V} (hw : w ∈ W) :
    RCLike.re (a u w) = RCLike.re (ℓ w) := by
  refine re_apply_eq_re_of_isLocalMinOn_quadraticEnergy_line ha hmin
    (Eventually.of_forall fun t ↦ ?_)
  rw [← RCLike.algebraMap_eq_ofReal, algebraMap_smul]
  exact add_mem_vadd_set hu (W.smul_mem t hw)

/-- **Weak Euler--Lagrange equation** on an affine subspace `g +ᵥ W` for a Hermitian form `a`: if
`u ∈ g +ᵥ W` is a local minimizer of `quadraticEnergy a ℓ` on `g +ᵥ W` (`W : Submodule 𝕜 V`), then
`a u w = ℓ w` for every `w ∈ W` (Hunter, Definition 4.3 and Proposition 4.5). -/
theorem apply_eq_of_isLocalMinOn_quadraticEnergy_vadd {a : V →L⋆[𝕜] V →L[𝕜] 𝕜}
    (ha : ∀ x y, a x y = star (a y x)) {ℓ : StrongDual 𝕜 V} {W : Submodule 𝕜 V} {g u : V}
    (hu : u ∈ g +ᵥ (W : Set V))
    (hmin : IsLocalMinOn (quadraticEnergy a ℓ) (g +ᵥ (W : Set V)) u) {w : V} (hw : w ∈ W) :
    a u w = ℓ w := by
  let : NormedSpace ℝ V := NormedSpace.restrictScalars ℝ 𝕜 V
  have : IsScalarTower ℝ 𝕜 V := IsScalarTower.restrictScalars ℝ 𝕜 V
  exact RCLike.apply_eq_of_re_eq_of_re_I_smul_eq
    (re_apply_eq_re_of_isLocalMinOn_quadraticEnergy_vadd_real (W := W.restrictScalars ℝ) ha hu
      hmin hw)
    (re_apply_eq_re_of_isLocalMinOn_quadraticEnergy_vadd_real (W := W.restrictScalars ℝ) ha hu
      hmin (W.smul_mem RCLike.I hw))

/-- **Weak Euler--Lagrange equation** at a local minimizer on `u +ᵥ W` for a Hermitian form `a` and
a `𝕜`-submodule `W`: `a u w = ℓ w` for every `w ∈ W`. -/
theorem apply_eq_of_isLocalMinOn_quadraticEnergy_vadd_self {a : V →L⋆[𝕜] V →L[𝕜] 𝕜}
    (ha : ∀ x y, a x y = star (a y x)) {ℓ : StrongDual 𝕜 V} {W : Submodule 𝕜 V} {u : V}
    (hmin : IsLocalMinOn (quadraticEnergy a ℓ) (u +ᵥ (W : Set V)) u) {w : V} (hw : w ∈ W) :
    a u w = ℓ w :=
  apply_eq_of_isLocalMinOn_quadraticEnergy_vadd ha ⟨0, W.zero_mem, add_zero u⟩ hmin hw

/-- Global-minimizer specialization of `apply_eq_of_isLocalMinOn_quadraticEnergy_vadd` for a
Hermitian form `a`. -/
theorem apply_eq_of_isMinOn_quadraticEnergy_vadd {a : V →L⋆[𝕜] V →L[𝕜] 𝕜}
    (ha : ∀ x y, a x y = star (a y x)) {ℓ : StrongDual 𝕜 V} {W : Submodule 𝕜 V} {g u : V}
    (hu : u ∈ g +ᵥ (W : Set V))
    (hmin : IsMinOn (quadraticEnergy a ℓ) (g +ᵥ (W : Set V)) u) {w : V} (hw : w ∈ W) :
    a u w = ℓ w :=
  apply_eq_of_isLocalMinOn_quadraticEnergy_vadd ha hu hmin.isLocalMinOn hw

/-- **Unconstrained weak Euler--Lagrange equation** at a local minimizer of `quadraticEnergy a ℓ`
for a Hermitian form `a`: `a u v = ℓ v` for every `v : V`. -/
theorem apply_eq_of_isLocalMin_quadraticEnergy {a : V →L⋆[𝕜] V →L[𝕜] 𝕜}
    (ha : ∀ x y, a x y = star (a y x)) {ℓ : StrongDual 𝕜 V} {u : V}
    (hmin : IsLocalMin (quadraticEnergy a ℓ) u) (v : V) :
    a u v = ℓ v := by
  have hvadd : u +ᵥ ((⊤ : Submodule 𝕜 V) : Set V) = Set.univ := by
    ext x
    simp
  refine apply_eq_of_isLocalMinOn_quadraticEnergy_vadd_self (W := ⊤) ha ?_ trivial
  rw [hvadd]
  exact hmin.isLocalMinOn Set.univ

/-- Global unconstrained specialization of `apply_eq_of_isLocalMin_quadraticEnergy` for a Hermitian
form `a`. -/
theorem apply_eq_of_isMinOn_quadraticEnergy_univ {a : V →L⋆[𝕜] V →L[𝕜] 𝕜}
    (ha : ∀ x y, a x y = star (a y x)) {ℓ : StrongDual 𝕜 V} {u : V}
    (hmin : IsMinOn (quadraticEnergy a ℓ) Set.univ u) (v : V) :
    a u v = ℓ v :=
  apply_eq_of_isLocalMin_quadraticEnergy ha (isLocalMinOn_univ_iff.mp hmin.isLocalMinOn) v

/-! ### Exact energy gap and equivalence with minimality for nonnegative forms -/

/-- **Exact energy gap** for a Hermitian form `a` along a test direction `w` satisfying
`Re(a u w) = Re(ℓ w)`: `E(u + w) - E(u) = Re(a w w)` (Hunter, Corollary 4.6). -/
theorem quadraticEnergy_add_sub_eq_re_of_re_eq {a : V →L⋆[𝕜] V →L[𝕜] 𝕜}
    (ha : ∀ x y, a x y = star (a y x)) {ℓ : StrongDual 𝕜 V} {u w : V}
    (h : RCLike.re (a u w) = RCLike.re (ℓ w)) :
    quadraticEnergy a ℓ (u + w) - quadraticEnergy a ℓ u = RCLike.re (a w w) := by
  rw [quadraticEnergy_add_sub_of_eq_star ha ℓ u w, map_sub, h, sub_self, mul_zero, zero_add]

/-- **Exact energy gap** for a Hermitian form `a` along a test direction `w` solving `a u w = ℓ w`:
`E(u + w) - E(u) = Re(a w w)` (Hunter, Corollary 4.6). -/
theorem quadraticEnergy_add_sub_eq_re_of_apply_eq {a : V →L⋆[𝕜] V →L[𝕜] 𝕜}
    (ha : ∀ x y, a x y = star (a y x)) {ℓ : StrongDual 𝕜 V} {u w : V} (h : a u w = ℓ w) :
    quadraticEnergy a ℓ (u + w) - quadraticEnergy a ℓ u = RCLike.re (a w w) :=
  quadraticEnergy_add_sub_eq_re_of_re_eq ha (congrArg RCLike.re h)

/-- **Exact energy gap** relative to a submodule `W` for a Hermitian form `a`: if `v - u ∈ W` and
`u` solves `a u w = ℓ w` for all `w ∈ W`, then `E(v) - E(u) = Re(a (v - u) (v - u))`. -/
theorem quadraticEnergy_sub_eq_re_of_forall_apply_eq {a : V →L⋆[𝕜] V →L[𝕜] 𝕜}
    (ha : ∀ x y, a x y = star (a y x)) {ℓ : StrongDual 𝕜 V} {W : Submodule 𝕜 V} {u v : V}
    (hmem : v - u ∈ W) (hsol : ∀ w ∈ W, a u w = ℓ w) :
    quadraticEnergy a ℓ v - quadraticEnergy a ℓ u = RCLike.re (a (v - u) (v - u)) := by
  simpa only [add_sub_cancel] using quadraticEnergy_add_sub_eq_re_of_apply_eq ha (hsol (v - u) hmem)

/-- At a vector `u` satisfying `a u u = ℓ u` (in particular, a homogeneous weak solution on `W`
with `u ∈ W`), the energy value is `E(u) = -Re(a u u) = -Re(ℓ u)`. -/
theorem quadraticEnergy_eq_neg_re_of_apply_self_eq {a : V →L⋆[𝕜] V →L[𝕜] 𝕜}
    {ℓ : StrongDual 𝕜 V} {u : V} (h : a u u = ℓ u) :
    quadraticEnergy a ℓ u = -RCLike.re (a u u) := by
  rw [quadraticEnergy_apply, ← h]
  ring

/-- **Equivalence of the variational inequality and minimality** on a convex set `C` when `a` is
Hermitian and nonnegative on differences of points in `C`. -/
theorem isMinOn_quadraticEnergy_iff_of_convex [Module ℝ V] [IsScalarTower ℝ 𝕜 V]
    {a : V →L⋆[𝕜] V →L[𝕜] 𝕜} (ha : ∀ x y, a x y = star (a y x)) {ℓ : StrongDual 𝕜 V}
    {C : Set V} (hC : Convex ℝ C) (hpos : ∀ x ∈ C, ∀ y ∈ C, 0 ≤ RCLike.re (a (y - x) (y - x)))
    {u : V} (hu : u ∈ C) :
    IsMinOn (quadraticEnergy a ℓ) C u ↔
      ∀ v ∈ C, RCLike.re (ℓ (v - u)) ≤ RCLike.re (a u (v - u)) := by
  refine ⟨fun hmin v hv ↦ le_re_apply_sub_of_isLocalMinOn_quadraticEnergy_convex ha hC hu
    hmin.isLocalMinOn hv, fun hvi ↦ isMinOn_iff.mpr fun v hv ↦ ?_⟩
  have hexp := quadraticEnergy_sub_quadraticEnergy_of_eq_star ha ℓ u v
  rw [map_sub] at hexp
  linarith [hvi v hv, hpos u hu v hv]

/-- **Equivalence of the weak Euler--Lagrange equation and minimality** on an affine subspace
`g +ᵥ W` for a Hermitian form `a` when `Re(a w w) ≥ 0` for all `w ∈ W` (Hunter, Corollary 4.6).
Nonnegativity on `W` is necessary (`q(u) = -‖u‖²` makes the weak solution `0` a maximizer). -/
theorem isMinOn_quadraticEnergy_vadd_iff {a : V →L⋆[𝕜] V →L[𝕜] 𝕜}
    (ha : ∀ x y, a x y = star (a y x)) {ℓ : StrongDual 𝕜 V} {W : Submodule 𝕜 V}
    (hpos : ∀ w ∈ W, 0 ≤ RCLike.re (a w w)) {g u : V} (hu : u ∈ g +ᵥ (W : Set V)) :
    IsMinOn (quadraticEnergy a ℓ) (g +ᵥ (W : Set V)) u ↔ ∀ w ∈ W, a u w = ℓ w := by
  refine ⟨fun hmin w hw ↦ apply_eq_of_isMinOn_quadraticEnergy_vadd ha hu hmin hw,
    fun hsol ↦ isMinOn_iff.mpr fun v hv ↦ ?_⟩
  have hvu : v - u ∈ W := sub_mem_of_mem_vadd_set hv hu
  have hgap := quadraticEnergy_sub_eq_re_of_forall_apply_eq ha hvu hsol
  linarith [hpos (v - u) hvu]

/-- **Unconstrained equivalence** between `IsMinOn (quadraticEnergy a ℓ) Set.univ u` and the weak
equation `∀ v, a u v = ℓ v` for a nonnegative Hermitian form `a`. -/
theorem isMinOn_quadraticEnergy_univ_iff {a : V →L⋆[𝕜] V →L[𝕜] 𝕜}
    (ha : ∀ x y, a x y = star (a y x)) {ℓ : StrongDual 𝕜 V}
    (hpos : ∀ w, 0 ≤ RCLike.re (a w w)) {u : V} :
    IsMinOn (quadraticEnergy a ℓ) Set.univ u ↔ ∀ v, a u v = ℓ v := by
  simpa using isMinOn_quadraticEnergy_vadd_iff (W := ⊤) (g := 0) ha (fun w _ ↦ hpos w) (by simp)

end FirstVariation

/-! ### Coercive forms: quadratic growth, near-minimizer rate, and bounded sublevels -/

section Coercive

variable {𝕜 V : Type*} [RCLike 𝕜] [SeminormedAddCommGroup V] [NormedSpace 𝕜 V]

/-- **Quantitative quadratic growth** relative to a submodule `W` for a Hermitian form `a`: if
`v - u ∈ W`, `c * ‖w‖² ≤ Re(a w w)` for all `w ∈ W`, and `u` solves `a u w = ℓ w` on `W`, then
`c * ‖v - u‖² ≤ E(v) - E(u)`. -/
theorem mul_norm_sub_sq_le_quadraticEnergy_sub_of_forall_apply_eq {a : V →L⋆[𝕜] V →L[𝕜] 𝕜}
    (ha : ∀ x y, a x y = star (a y x)) {ℓ : StrongDual 𝕜 V} {W : Submodule 𝕜 V} {c : ℝ}
    (hcoer : ∀ w ∈ W, c * ‖w‖ ^ 2 ≤ RCLike.re (a w w)) {u v : V}
    (hmem : v - u ∈ W) (hsol : ∀ w ∈ W, a u w = ℓ w) :
    c * ‖v - u‖ ^ 2 ≤ quadraticEnergy a ℓ v - quadraticEnergy a ℓ u := by
  rw [quadraticEnergy_sub_eq_re_of_forall_apply_eq ha hmem hsol]
  exact hcoer (v - u) hmem

/-- **Quantitative quadratic growth** along a vector `h` for a Hermitian form `a`: if
`c * ‖h‖² ≤ Re(a h h)` and `a u h = ℓ h`, then `c * ‖h‖² ≤ E(u + h) - E(u)`. -/
theorem mul_norm_sq_le_quadraticEnergy_add_sub_of_apply_eq {a : V →L⋆[𝕜] V →L[𝕜] 𝕜}
    (ha : ∀ x y, a x y = star (a y x)) {ℓ : StrongDual 𝕜 V} {c : ℝ} {u h : V}
    (hcoer : c * ‖h‖ ^ 2 ≤ RCLike.re (a h h)) (hsol : a u h = ℓ h) :
    c * ‖h‖ ^ 2 ≤ quadraticEnergy a ℓ (u + h) - quadraticEnergy a ℓ u := by
  rwa [quadraticEnergy_add_sub_eq_re_of_apply_eq ha hsol]

/-- **Quadratic energy-gap lower bound on a convex set** around a local minimizer `u ∈ C`: for
every `v ∈ C`, `Re(a (v - u) (v - u)) ≤ E(v) - E(u)`. No symmetry of `a` is required. -/
theorem re_apply_sub_self_le_quadraticEnergy_sub_of_isLocalMinOn_convex
    [Module ℝ V] [IsScalarTower ℝ 𝕜 V] {a : V →L⋆[𝕜] V →L[𝕜] 𝕜} {ℓ : StrongDual 𝕜 V}
    {C : Set V} (hC : Convex ℝ C) {u v : V} (hu : u ∈ C) (hv : v ∈ C)
    (hmin : IsLocalMinOn (quadraticEnergy a ℓ) C u) :
    RCLike.re (a (v - u) (v - u)) ≤ quadraticEnergy a ℓ v - quadraticEnergy a ℓ u := by
  have hpath_eq (t : ℝ) : u + (t : 𝕜) • (v - u) = t • v + (1 - t) • u := by
    rw [← RCLike.algebraMap_eq_ofReal, algebraMap_smul]
    module
  have hcont : Continuous (fun t : ℝ ↦ u + (t : 𝕜) • (v - u)) :=
    continuous_const.add ((RCLike.continuous_ofReal.comp continuous_id).smul continuous_const)
  have htend : Tendsto (fun t : ℝ ↦ u + (t : 𝕜) • (v - u)) (𝓝[>] 0) (𝓝[C] u) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · simpa only [RCLike.ofReal_zero, zero_smul, add_zero] using
        (hcont.tendsto 0).mono_left nhdsWithin_le_nhds
    · filter_upwards [Ioo_mem_nhdsGT zero_lt_one] with t ht
      rw [← RCLike.algebraMap_eq_ofReal, algebraMap_smul]
      exact hC.add_smul_sub_mem hu hv (Ioo_subset_Icc_self ht)
  have hle : ∀ᶠ t : ℝ in 𝓝[>] 0,
      (1 - t) * RCLike.re (a (v - u) (v - u)) ≤
        quadraticEnergy a ℓ v - quadraticEnergy a ℓ u := by
    filter_upwards [htend.eventually hmin, self_mem_nhdsWithin] with t ht htpos
    have ht' : quadraticEnergy a ℓ u ≤ quadraticEnergy a ℓ (u + (t : 𝕜) • (v - u)) := ht
    rw [hpath_eq t] at ht'
    have hcombo := quadraticEnergy_combo_add_mul_sub a ℓ (by ring : t + (1 - t) = 1) v u
    have hmul : t * ((1 - t) * RCLike.re (a (v - u) (v - u))) ≤
        t * (quadraticEnergy a ℓ v - quadraticEnergy a ℓ u) := by
      linarith
    exact le_of_mul_le_mul_left hmul htpos
  have hlim : Tendsto (fun t : ℝ ↦ (1 - t) * RCLike.re (a (v - u) (v - u))) (𝓝[>] 0)
      (𝓝 (RCLike.re (a (v - u) (v - u)))) := by
    have hc : Continuous (fun t : ℝ ↦ (1 - t) * RCLike.re (a (v - u) (v - u))) := by fun_prop
    simpa using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
  exact le_of_tendsto hlim hle

/-- **Quantitative quadratic growth on a convex set** around a local minimizer `u ∈ C`: if
`c * ‖y - x‖² ≤ Re(a (y - x) (y - x))` on `C`, then `c * ‖v - u‖² ≤ E(v) - E(u)` for all `v ∈ C`.
No symmetry of `a` is required. -/
theorem mul_norm_sub_sq_le_quadraticEnergy_sub_of_isLocalMinOn_convex
    [Module ℝ V] [IsScalarTower ℝ 𝕜 V] {a : V →L⋆[𝕜] V →L[𝕜] 𝕜}
    {ℓ : StrongDual 𝕜 V} {C : Set V} (hC : Convex ℝ C)
    {c : ℝ} (hcoer : ∀ x ∈ C, ∀ y ∈ C, c * ‖y - x‖ ^ 2 ≤ RCLike.re (a (y - x) (y - x)))
    {u v : V} (hu : u ∈ C) (hv : v ∈ C) (hmin : IsLocalMinOn (quadraticEnergy a ℓ) C u) :
    c * ‖v - u‖ ^ 2 ≤ quadraticEnergy a ℓ v - quadraticEnergy a ℓ u :=
  (hcoer u hu v hv).trans
    (re_apply_sub_self_le_quadraticEnergy_sub_of_isLocalMinOn_convex hC hu hv hmin)

/-- **Near-minimizer distance rate on a convex set** `C`: for `c > 0`, every `v ∈ C` satisfies
`‖v - u‖² ≤ (E(v) - E(u)) / c` around a local minimizer `u ∈ C`. No symmetry of `a` is required. -/
theorem norm_sub_sq_le_quadraticEnergy_sub_div_of_isLocalMinOn_convex
    [Module ℝ V] [IsScalarTower ℝ 𝕜 V] {a : V →L⋆[𝕜] V →L[𝕜] 𝕜}
    {ℓ : StrongDual 𝕜 V} {C : Set V} (hC : Convex ℝ C) {c : ℝ} (hc : 0 < c)
    (hcoer : ∀ x ∈ C, ∀ y ∈ C, c * ‖y - x‖ ^ 2 ≤ RCLike.re (a (y - x) (y - x)))
    {u v : V} (hu : u ∈ C) (hv : v ∈ C) (hmin : IsLocalMinOn (quadraticEnergy a ℓ) C u) :
    ‖v - u‖ ^ 2 ≤ (quadraticEnergy a ℓ v - quadraticEnergy a ℓ u) / c := by
  rw [le_div_iff₀ hc, mul_comm]
  exact mul_norm_sub_sq_le_quadraticEnergy_sub_of_isLocalMinOn_convex hC hcoer hu hv hmin

/-- **Near-minimizer distance rate** on `g +ᵥ W`: for `c > 0`, every admissible `v ∈ g +ᵥ W`
satisfies `‖v - u‖² ≤ (E(v) - E(u)) / c` around a local minimizer `u ∈ g +ᵥ W`. No symmetry of `a`
is required. -/
theorem norm_sub_sq_le_quadraticEnergy_sub_div_of_isLocalMinOn_vadd {a : V →L⋆[𝕜] V →L[𝕜] 𝕜}
    {ℓ : StrongDual 𝕜 V} {W : Submodule 𝕜 V} {c : ℝ}
    (hc : 0 < c) (hcoer : ∀ w ∈ W, c * ‖w‖ ^ 2 ≤ RCLike.re (a w w)) {g u v : V}
    (hu : u ∈ g +ᵥ (W : Set V)) (hv : v ∈ g +ᵥ (W : Set V))
    (hmin : IsLocalMinOn (quadraticEnergy a ℓ) (g +ᵥ (W : Set V)) u) :
    ‖v - u‖ ^ 2 ≤ (quadraticEnergy a ℓ v - quadraticEnergy a ℓ u) / c := by
  let : NormedSpace ℝ V := NormedSpace.restrictScalars ℝ 𝕜 V
  have : IsScalarTower ℝ 𝕜 V := IsScalarTower.restrictScalars ℝ 𝕜 V
  exact norm_sub_sq_le_quadraticEnergy_sub_div_of_isLocalMinOn_convex
    ((W.restrictScalars ℝ).convex.vadd g) hc
    (fun _ hx _ hy ↦ hcoer _ (sub_mem_of_mem_vadd_set hy hx)) hu hv hmin

/-- **Unconstrained near-minimizer distance rate**: for `c > 0` and `∀ w, c * ‖w‖² ≤ Re(a w w)`,
every `v : V` satisfies `‖v - u‖² ≤ (E(v) - E(u)) / c` around a local minimizer `u`. No symmetry of
`a` is required. -/
theorem norm_sub_sq_le_quadraticEnergy_sub_div {a : V →L⋆[𝕜] V →L[𝕜] 𝕜}
    {ℓ : StrongDual 𝕜 V} {c : ℝ} (hc : 0 < c)
    (hcoer : ∀ w, c * ‖w‖ ^ 2 ≤ RCLike.re (a w w)) {u v : V}
    (hmin : IsLocalMin (quadraticEnergy a ℓ) u) :
    ‖v - u‖ ^ 2 ≤ (quadraticEnergy a ℓ v - quadraticEnergy a ℓ u) / c :=
  norm_sub_sq_le_quadraticEnergy_sub_div_of_isLocalMinOn_vadd (W := ⊤) (g := 0) hc
    (fun w _ ↦ hcoer w) (by simp) (by simp)
    (by simpa using hmin.isLocalMinOn Set.univ)

/-- **Norm convergence of near-minimizers on a convex set** `C`: if `a` is `c`-coercive on
differences in `C` (`c > 0`), `u ∈ C` locally minimizes `quadraticEnergy a ℓ` on `C`, and
`x i ∈ C` satisfies `E(x i) → E(u)`, then `x i → u` in norm. No symmetry of `a` is required. -/
theorem tendsto_of_tendsto_quadraticEnergy_convex [Module ℝ V] [IsScalarTower ℝ 𝕜 V]
    {ι : Type*} {l : Filter ι} {a : V →L⋆[𝕜] V →L[𝕜] 𝕜}
    {ℓ : StrongDual 𝕜 V} {C : Set V} (hC : Convex ℝ C) {c : ℝ} (hc : 0 < c)
    (hcoer : ∀ x ∈ C, ∀ y ∈ C, c * ‖y - x‖ ^ 2 ≤ RCLike.re (a (y - x) (y - x)))
    {u : V} (hu : u ∈ C) (hmin : IsLocalMinOn (quadraticEnergy a ℓ) C u)
    {x : ι → V} (hx : ∀ᶠ i in l, x i ∈ C)
    (hE : Tendsto (fun i ↦ quadraticEnergy a ℓ (x i)) l (𝓝 (quadraticEnergy a ℓ u))) :
    Tendsto x l (𝓝 u) :=
  tendsto_of_dist_pow_le_of_tendsto_zero
    (hx.mono fun _ hi ↦ by
      simpa only [← dist_eq_norm] using
        norm_sub_sq_le_quadraticEnergy_sub_div_of_isLocalMinOn_convex hC hc hcoer hu hi hmin)
    (by simpa only [sub_self, zero_div] using (hE.sub_const (quadraticEnergy a ℓ u)).div_const c)

/-- **Norm convergence of near-minimizers on `g +ᵥ W`**: if `a` is `c`-coercive on `W` (`c > 0`),
`u ∈ g +ᵥ W` locally minimizes `quadraticEnergy a ℓ` on `g +ᵥ W`, and `x i ∈ g +ᵥ W` satisfies
`E(x i) → E(u)`, then `x i → u` in norm. No symmetry of `a` is required. -/
theorem tendsto_of_tendsto_quadraticEnergy_vadd {ι : Type*} {l : Filter ι}
    {a : V →L⋆[𝕜] V →L[𝕜] 𝕜} {ℓ : StrongDual 𝕜 V}
    {W : Submodule 𝕜 V} {c : ℝ} (hc : 0 < c)
    (hcoer : ∀ w ∈ W, c * ‖w‖ ^ 2 ≤ RCLike.re (a w w)) {g u : V}
    (hu : u ∈ g +ᵥ (W : Set V)) (hmin : IsLocalMinOn (quadraticEnergy a ℓ) (g +ᵥ (W : Set V)) u)
    {x : ι → V} (hx : ∀ᶠ i in l, x i ∈ g +ᵥ (W : Set V))
    (hE : Tendsto (fun i ↦ quadraticEnergy a ℓ (x i)) l (𝓝 (quadraticEnergy a ℓ u))) :
    Tendsto x l (𝓝 u) :=
  tendsto_of_dist_pow_le_of_tendsto_zero
    (hx.mono fun _ hi ↦ by
      simpa only [← dist_eq_norm] using
        norm_sub_sq_le_quadraticEnergy_sub_div_of_isLocalMinOn_vadd hc hcoer hu hi hmin)
    (by simpa only [sub_self, zero_div] using (hE.sub_const (quadraticEnergy a ℓ u)).div_const c)

/-- **Unconstrained norm convergence of near-minimizers**: if `∀ w, c * ‖w‖² ≤ Re(a w w)` (`c > 0`),
`u` locally minimizes `quadraticEnergy a ℓ`, and `E(x i) → E(u)`, then `x i → u` in norm. No
symmetry of `a` is required. -/
theorem tendsto_of_tendsto_quadraticEnergy {ι : Type*} {l : Filter ι}
    {a : V →L⋆[𝕜] V →L[𝕜] 𝕜} {ℓ : StrongDual 𝕜 V} {c : ℝ} (hc : 0 < c)
    (hcoer : ∀ w, c * ‖w‖ ^ 2 ≤ RCLike.re (a w w)) {u : V}
    (hmin : IsLocalMin (quadraticEnergy a ℓ) u) {x : ι → V}
    (hE : Tendsto (fun i ↦ quadraticEnergy a ℓ (x i)) l (𝓝 (quadraticEnergy a ℓ u))) :
    Tendsto x l (𝓝 u) :=
  tendsto_of_tendsto_quadraticEnergy_vadd (W := ⊤) (g := 0) hc (fun w _ ↦ hcoer w) (by simp)
    (by simpa using hmin.isLocalMinOn Set.univ) (Eventually.of_forall fun _ ↦ by simp) hE

/-! ### Bounded sublevels -/

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

/-- **Bounded sublevels from coercivity on differences.** If `c * ‖y - x‖² ≤ Re(a (y - x) (y - x))`
for all `x, y ∈ C` (`c > 0`), then `quadraticEnergy a ℓ` has bounded sublevels on `C`. Neither
symmetry of `a` nor nonemptiness of `C` is required. -/
theorem hasBoundedSublevelsOn_quadraticEnergy_of_sub_coercive {a : V →L⋆[𝕜] V →L[𝕜] 𝕜}
    (ℓ : StrongDual 𝕜 V) {C : Set V} {c : ℝ} (hc : 0 < c)
    (hcoer : ∀ x ∈ C, ∀ y ∈ C, c * ‖y - x‖ ^ 2 ≤ RCLike.re (a (y - x) (y - x))) :
    HasBoundedSublevelsOn (quadraticEnergy a ℓ) C := by
  rcases C.eq_empty_or_nonempty with rfl | ⟨u₀, hu₀⟩
  · exact hasBoundedSublevelsOn_empty
  · rw [hasBoundedSublevelsOn_iff_forall_exists_le_of_le_norm]
    intro b
    let M : ℝ := 2 * ‖a‖ * ‖u₀‖ + 2 * ‖ℓ‖
    refine ⟨‖u₀‖ + max 1 ((M + max (b - quadraticEnergy a ℓ u₀) 0) / c), fun u hu hR ↦ ?_⟩
    set w : V := u - u₀
    have htri : ‖u‖ ≤ ‖u₀‖ + ‖w‖ := by
      simpa only [w, add_sub_cancel] using norm_add_le u₀ (u - u₀)
    have hw_ge : max 1 ((M + max (b - quadraticEnergy a ℓ u₀) 0) / c) ≤ ‖w‖ := by linarith
    have hw1 : 1 ≤ ‖w‖ := (le_max_left _ _).trans hw_ge
    have hw2 : M + max (b - quadraticEnergy a ℓ u₀) 0 ≤ ‖w‖ * c :=
      (div_le_iff₀ hc).mp ((le_max_right _ _).trans hw_ge)
    dsimp only [M] at hw2
    have ha₁ : -(‖a‖ * ‖u₀‖ * ‖w‖) ≤ RCLike.re (a u₀ w) :=
      neg_le_of_abs_le ((RCLike.abs_re_le_norm _).trans (a.le_opNorm₂ u₀ w))
    have ha₂ : -(‖a‖ * ‖w‖ * ‖u₀‖) ≤ RCLike.re (a w u₀) :=
      neg_le_of_abs_le ((RCLike.abs_re_le_norm _).trans (a.le_opNorm₂ w u₀))
    have hℓw : RCLike.re (ℓ w) ≤ ‖ℓ‖ * ‖w‖ :=
      (le_abs_self _).trans ((RCLike.abs_re_le_norm _).trans (ℓ.le_opNorm w))
    have hquad : c * ‖w‖ ^ 2 ≤ RCLike.re (a w w) := hcoer u₀ hu₀ u hu
    have hinc := quadraticEnergy_add_sub a ℓ u₀ w
    have huw : u₀ + w = u := add_sub_cancel u₀ u
    rw [huw] at hinc
    have hb0 : 0 ≤ max (b - quadraticEnergy a ℓ u₀) 0 := le_max_right _ _
    have hb1 : b - quadraticEnergy a ℓ u₀ ≤ max (b - quadraticEnergy a ℓ u₀) 0 := le_max_left _ _
    nlinarith

/-- **Bounded sublevels on an inhomogeneous affine subspace** `g +ᵥ W`: it suffices that `a` be
`c`-coercive (`c > 0`) on the direction submodule `W` alone; `a` need not be symmetric and may
vanish or be indefinite on the datum `g` (as for shifted elliptic forms with inhomogeneous boundary
data). -/
theorem hasBoundedSublevelsOn_quadraticEnergy_vadd {a : V →L⋆[𝕜] V →L[𝕜] 𝕜}
    (ℓ : StrongDual 𝕜 V) {W : Submodule 𝕜 V} (g : V)
    {c : ℝ} (hc : 0 < c) (hcoer : ∀ w ∈ W, c * ‖w‖ ^ 2 ≤ RCLike.re (a w w)) :
    HasBoundedSublevelsOn (quadraticEnergy a ℓ) (g +ᵥ (W : Set V)) :=
  hasBoundedSublevelsOn_quadraticEnergy_of_sub_coercive ℓ hc fun _ hx _ hy ↦
    hcoer _ (sub_mem_of_mem_vadd_set hy hx)

end Coercive

/-! ### Uniqueness and direct-method existence on normed and reflexive spaces -/

section NormedUniquenessAndExistence

variable {𝕜 V : Type*} [RCLike 𝕜] [NormedAddCommGroup V] [NormedSpace 𝕜 V]

/-- **Uniqueness of local minimizers on a convex set** `C` when `a` is `c`-coercive on differences
in `C` (`c > 0`). No symmetry of `a` is required. -/
theorem eq_of_isLocalMinOn_quadraticEnergy_convex [Module ℝ V] [IsScalarTower ℝ 𝕜 V]
    {a : V →L⋆[𝕜] V →L[𝕜] 𝕜} {ℓ : StrongDual 𝕜 V}
    {C : Set V} (hC : Convex ℝ C) {c : ℝ} (hc : 0 < c)
    (hcoer : ∀ x ∈ C, ∀ y ∈ C, c * ‖y - x‖ ^ 2 ≤ RCLike.re (a (y - x) (y - x)))
    {u₁ u₂ : V} (hu₁ : u₁ ∈ C) (hu₂ : u₂ ∈ C)
    (hmin₁ : IsLocalMinOn (quadraticEnergy a ℓ) C u₁)
    (hmin₂ : IsLocalMinOn (quadraticEnergy a ℓ) C u₂) : u₁ = u₂ := by
  have h₁ := mul_norm_sub_sq_le_quadraticEnergy_sub_of_isLocalMinOn_convex hC hcoer hu₁ hu₂ hmin₁
  have h₂ := mul_norm_sub_sq_le_quadraticEnergy_sub_of_isLocalMinOn_convex hC hcoer hu₂ hu₁ hmin₂
  rw [norm_sub_rev u₂ u₁] at h₁
  have hsq : ‖u₁ - u₂‖ ^ 2 ≤ 0 := by nlinarith
  exact sub_eq_zero.mp (norm_le_zero_iff.mp (sq_eq_zero_iff.mp (le_antisymm hsq (sq_nonneg _))).le)

/-- **Uniqueness of local minimizers on an affine subspace** `g +ᵥ W` when `a` is `c`-coercive on
`W` (`c > 0`). No symmetry of `a` is required. -/
theorem eq_of_isLocalMinOn_quadraticEnergy_vadd {a : V →L⋆[𝕜] V →L[𝕜] 𝕜}
    {ℓ : StrongDual 𝕜 V} {W : Submodule 𝕜 V} {c : ℝ}
    (hc : 0 < c) (hcoer : ∀ w ∈ W, c * ‖w‖ ^ 2 ≤ RCLike.re (a w w)) {g u₁ u₂ : V}
    (hu₁ : u₁ ∈ g +ᵥ (W : Set V)) (hu₂ : u₂ ∈ g +ᵥ (W : Set V))
    (hmin₁ : IsLocalMinOn (quadraticEnergy a ℓ) (g +ᵥ (W : Set V)) u₁)
    (hmin₂ : IsLocalMinOn (quadraticEnergy a ℓ) (g +ᵥ (W : Set V)) u₂) : u₁ = u₂ := by
  let : NormedSpace ℝ V := NormedSpace.restrictScalars ℝ 𝕜 V
  have : IsScalarTower ℝ 𝕜 V := IsScalarTower.restrictScalars ℝ 𝕜 V
  exact eq_of_isLocalMinOn_quadraticEnergy_convex ((W.restrictScalars ℝ).convex.vadd g) hc
    (fun _ hx _ hy ↦ hcoer _ (sub_mem_of_mem_vadd_set hy hx)) hu₁ hu₂ hmin₁ hmin₂

/-- **Uniqueness of unconstrained local minimizers** when `∀ w, c * ‖w‖² ≤ Re(a w w)` (`c > 0`). No
symmetry of `a` is required. -/
theorem eq_of_isLocalMin_quadraticEnergy {a : V →L⋆[𝕜] V →L[𝕜] 𝕜}
    {ℓ : StrongDual 𝕜 V} {c : ℝ} (hc : 0 < c)
    (hcoer : ∀ w, c * ‖w‖ ^ 2 ≤ RCLike.re (a w w)) {u₁ u₂ : V}
    (hmin₁ : IsLocalMin (quadraticEnergy a ℓ) u₁)
    (hmin₂ : IsLocalMin (quadraticEnergy a ℓ) u₂) : u₁ = u₂ :=
  eq_of_isLocalMinOn_quadraticEnergy_vadd (W := ⊤) (g := 0) hc (fun w _ ↦ hcoer w)
    (by simp) (by simp) (by simpa using hmin₁.isLocalMinOn Set.univ)
    (by simpa using hmin₂.isLocalMinOn Set.univ)

/-- **Direct-method existence and uniqueness on a closed convex set.** In a reflexive normed space
over `𝕜`, if `a` is `c`-coercive on differences of points in a nonempty closed convex set `C`
(`c > 0`), then `quadraticEnergy a ℓ` attains a unique global minimum on `C`. No symmetry of `a` is
required. -/
theorem existsUnique_isMinOn_quadraticEnergy_of_isClosed_convex
    [Module ℝ V] [IsScalarTower ℝ 𝕜 V]
    (hV : Function.Surjective (inclusionInDoubleDual 𝕜 V))
    {a : V →L⋆[𝕜] V →L[𝕜] 𝕜}
    {C : Set V} (hne : C.Nonempty) (hC : Convex ℝ C) (hclosed : IsClosed C)
    {c : ℝ} (hc : 0 < c)
    (hcoer : ∀ x ∈ C, ∀ y ∈ C, c * ‖y - x‖ ^ 2 ≤ RCLike.re (a (y - x) (y - x)))
    (ℓ : StrongDual 𝕜 V) :
    ∃! u, u ∈ C ∧ IsMinOn (quadraticEnergy a ℓ) C u := by
  have : LocallyConvexSpace ℝ V := NormedSpace.toLocallyConvexSpace' 𝕜
  have hwclosed : IsClosed (toWeakSpace 𝕜 V '' C) := hC.isClosed_toWeakSpace_image 𝕜 hclosed
  have hpos : ∀ u ∈ C, ∀ v ∈ C, 0 ≤ RCLike.re (a (u - v) (u - v)) := fun u hu v hv ↦
    (mul_nonneg hc.le (sq_nonneg _)).trans (hcoer v hv u hu)
  obtain ⟨u, hu, hmin⟩ := exists_isMinOn_of_weak_closed hV hne hwclosed
    (lowerSemicontinuousOn_quadraticEnergy_comp_toWeakSpace_symm hC hpos ℓ)
    (hasBoundedSublevelsOn_quadraticEnergy_of_sub_coercive ℓ hc hcoer)
  exact ⟨u, ⟨hu, hmin⟩, fun y ⟨hy, hminy⟩ ↦
    eq_of_isLocalMinOn_quadraticEnergy_convex hC hc hcoer hy hu
      hminy.isLocalMinOn hmin.isLocalMinOn⟩

/-- **Unconstrained direct-method existence and uniqueness.** In a reflexive normed space over `𝕜`,
if `∀ w, c * ‖w‖² ≤ Re(a w w)` (`c > 0`), then `quadraticEnergy a ℓ` attains a unique global minimum
on `V`. No symmetry of `a` is required. -/
theorem existsUnique_isMinOn_quadraticEnergy_univ_of_coercive
    (hV : Function.Surjective (inclusionInDoubleDual 𝕜 V))
    {a : V →L⋆[𝕜] V →L[𝕜] 𝕜} {c : ℝ} (hc : 0 < c)
    (hcoer : ∀ w, c * ‖w‖ ^ 2 ≤ RCLike.re (a w w)) (ℓ : StrongDual 𝕜 V) :
    ∃! u, IsMinOn (quadraticEnergy a ℓ) Set.univ u := by
  let : NormedSpace ℝ V := NormedSpace.restrictScalars ℝ 𝕜 V
  have : IsScalarTower ℝ 𝕜 V := IsScalarTower.restrictScalars ℝ 𝕜 V
  simpa only [mem_univ, true_and] using
    existsUnique_isMinOn_quadraticEnergy_of_isClosed_convex hV univ_nonempty convex_univ
      isClosed_univ hc (fun x _ y _ ↦ hcoer (y - x)) ℓ

end NormedUniquenessAndExistence

end TauCeti

namespace ContinuousLinearMap

variable {𝕜 V : Type*} [RCLike 𝕜] [NormedAddCommGroup V] [NormedSpace 𝕜 V]

/-- **Direct-method existence and uniqueness of constrained weak solutions** on an affine coset
`g +ᵥ W` of a closed `𝕜`-submodule `W` in a reflexive normed space over `𝕜`, when `a` is Hermitian
and `c`-coercive on `W` (`c > 0`); `a` need not be nonnegative outside `W`. -/
theorem existsUnique_vadd_forall_apply_eq_of_isClosed_of_coercive
    (hV : Function.Surjective (inclusionInDoubleDual 𝕜 V))
    {a : V →L⋆[𝕜] V →L[𝕜] 𝕜} (ha : ∀ x y, a x y = star (a y x))
    {W : Submodule 𝕜 V} (hW : IsClosed (W : Set V))
    {c : ℝ} (hc : 0 < c) (hcoer : ∀ w ∈ W, c * ‖w‖ ^ 2 ≤ RCLike.re (a w w))
    (g : V) (ℓ : StrongDual 𝕜 V) :
    ∃! u, u ∈ g +ᵥ (W : Set V) ∧ ∀ w ∈ W, a u w = ℓ w := by
  let : NormedSpace ℝ V := NormedSpace.restrictScalars ℝ 𝕜 V
  have : IsScalarTower ℝ 𝕜 V := IsScalarTower.restrictScalars ℝ 𝕜 V
  have hpos : ∀ w ∈ W, 0 ≤ RCLike.re (a w w) := fun w hw ↦
    (mul_nonneg hc.le (sq_nonneg _)).trans (hcoer w hw)
  refine (existsUnique_congr fun u ↦ and_congr_right fun hu ↦
    TauCeti.isMinOn_quadraticEnergy_vadd_iff ha hpos hu).mp ?_
  exact TauCeti.existsUnique_isMinOn_quadraticEnergy_of_isClosed_convex hV
    ⟨g + 0, vadd_mem_vadd_set W.zero_mem⟩ ((W.restrictScalars ℝ).convex.vadd g) (hW.vadd g) hc
    (fun _ hx _ hy ↦ hcoer _ (TauCeti.sub_mem_of_mem_vadd_set hy hx)) ℓ

/-- **Global direct-method existence and uniqueness of weak solutions** in a reflexive normed space
over `𝕜` for a Hermitian form satisfying `∀ w, c * ‖w‖² ≤ Re(a w w)` (`c > 0`). -/
theorem existsUnique_forall_apply_eq_of_coercive
    (hV : Function.Surjective (inclusionInDoubleDual 𝕜 V))
    {a : V →L⋆[𝕜] V →L[𝕜] 𝕜} (ha : ∀ x y, a x y = star (a y x))
    {c : ℝ} (hc : 0 < c) (hcoer : ∀ w, c * ‖w‖ ^ 2 ≤ RCLike.re (a w w))
    (ℓ : StrongDual 𝕜 V) :
    ∃! u, ∀ v, a u v = ℓ v := by
  simpa using a.existsUnique_vadd_forall_apply_eq_of_isClosed_of_coercive (W := ⊤) hV ha
    (by simp) hc (fun w _ ↦ hcoer w) 0 ℓ

end ContinuousLinearMap

end
