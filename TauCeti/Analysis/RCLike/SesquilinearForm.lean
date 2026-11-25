/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.Function
public import Mathlib.Analysis.InnerProductSpace.Defs
public import TauCeti.Analysis.Calculus.Bilinear
public import TauCeti.Analysis.RCLike.Basic
public import TauCeti.LinearAlgebra.SesquilinearForm.Basic
import Mathlib.Analysis.Normed.Module.RCLike.Extend

/-!
# Real quadratic forms, Cauchy--Schwarz, and real-part bilinear maps for sesquilinear forms

Let `a` be a sesquilinear form on a module `V` over `𝕜` (`ℝ` or `ℂ`, written `[RCLike 𝕜]`),
conjugate-linear in its first argument and `𝕜`-linear in its second. When `a` is Hermitian,
`a u v = star (a v u)`, its diagonal values `a u u` are real, so the real quadratic form
`q(u) = RCLike.re (a u u)` determines `a u u` without loss of information, and its off-diagonal
real part `RCLike.re (a u v)` is symmetric in `u` and `v`.

This file develops the algebraic, analytic, and restricted-subspace stability properties of
`q(u) = RCLike.re (a u u)` and of the real-part bilinear pairing `(u, v) ↦ RCLike.re (a u v)`:

* **Polarization and convex-combination identities.** For a Hermitian form, expanding `q(u + c • v)`
  separates the linear variation `2 Re(c * a u v)` from the quadratic remainder `‖c‖² q(v)`. For an
  arbitrary (possibly non-Hermitian) form, the Jensen deficit of `q` along an affine combination
  `t₁ • u + t₂ • v` (`t₁ + t₂ = 1`) is `t₁ t₂ q(u - v)`, so `q` is convex as soon as `q ≥ 0`.
* **Positive-semidefinite forms.** Packaging a Hermitian form with `q ≥ 0` as a
  `PreInnerProductSpace.Core` transfers Mathlib's real-discriminant and complex-phase-test proof of
  Cauchy--Schwarz to `‖a u v‖² ≤ q(u) q(v)`, without assuming definiteness or a norm on `V`. As a
  consequence, the null space `{u | ∀ v, a u v = 0}` coincides with the isotropic cone
  `{u | q(u) = 0}`; indefiniteness breaks this equality (for `diag(1, -1)` at `(1, 1)`).
* **Real-part continuous bilinear form and Fréchet derivative.** On topological modules over `𝕜`
  equipped with compatible real scalar actions, a continuous sesquilinear form `a` induces an
  injectively associated continuous real-bilinear map `a.reBilin : E →L[ℝ] F →L[ℝ] ℝ`, which
  preserves operator norms (`‖a.reBilin‖ = ‖a‖`) on seminormed spaces. On a normed space `V`, `q` is
  `C^n` over `ℝ` for every `n` (via `ContinuousLinearMap.contDiff_apply_self`), with strict Fréchet
  derivative `v ↦ 2 Re(a u v)` when `a` is Hermitian (via
  `ContinuousLinearMap.hasStrictFDerivAt_apply_self`).
* **Subspace-restricted coercive stability.** For an arbitrary (possibly non-Hermitian) continuous
  sesquilinear form satisfying `c * ‖w‖² ≤ q(w)` on a submodule `W`, weak solutions on `W` that
  differ by an element of `W` satisfy `c * ‖u - u'‖ ≤ ‖(ℓ - ℓ').comp W.subtypeL‖` in the restricted
  dual norm on `W`.

## Main declarations

* `LinearMap.convexOn_re_apply_self`: convexity of `u ↦ RCLike.re (a u u)` when `q ≥ 0`, without
  assuming symmetry of `a`.
* `LinearMap.sesqFormCore`: a Hermitian sesquilinear form with `q ≥ 0` as a
  `PreInnerProductSpace.Core 𝕜 V`.
* `LinearMap.norm_apply_sq_le_re_apply_self_mul`: the Cauchy--Schwarz inequality
  `‖a u v‖ ^ 2 ≤ RCLike.re (a u u) * RCLike.re (a v v)`.
* `LinearMap.forall_apply_eq_zero_iff_re_apply_self_eq_zero` and
  `LinearMap.setOf_forall_apply_eq_zero_eq`: the kernel identity
  `{u | ∀ v, a u v = 0} = {u | q(u) = 0}` for nonnegative Hermitian forms.
* `ContinuousLinearMap.reBilin` and `ContinuousLinearMap.norm_reBilin`: the real part
  `(x, y) ↦ RCLike.re (a x y)` of a continuous sesquilinear form as an isometric continuous
  real-bilinear map.
* `ContinuousLinearMap.mul_norm_sub_le_norm_comp_subtypeL_of_coercive`: coercive stability of weak
  solutions on `W` in the restricted dual norm `‖(ℓ - ℓ').comp W.subtypeL‖`.
* `ContinuousLinearMap.hasStrictFDerivAt_re_apply_self_of_eq_star`: the real strict Fréchet
  derivative of `u ↦ RCLike.re (a u u)` for a continuous Hermitian form.
-/

public section

noncomputable section

namespace LinearMap

section Algebraic

variable {𝕜 V : Type*} [RCLike 𝕜] [AddCommGroup V] [Module 𝕜 V]

/-- A Hermitian sesquilinear form takes real values on the diagonal: `im (a u u) = 0`. -/
theorem im_apply_self_of_eq_star {a : V →ₗ⋆[𝕜] V →ₗ[𝕜] 𝕜}
    (ha : ∀ u v, a u v = star (a v u)) (u : V) : RCLike.im (a u u) = 0 :=
  RCLike.conj_eq_iff_im.mp (ha u u).symm

/-- Each diagonal value `a u u` of a Hermitian sesquilinear form equals its real part coerced back
to `𝕜`. -/
theorem ofReal_re_apply_self_of_eq_star {a : V →ₗ⋆[𝕜] V →ₗ[𝕜] 𝕜}
    (ha : ∀ u v, a u v = star (a v u)) (u : V) : (RCLike.re (a u u) : 𝕜) = a u u :=
  RCLike.conj_eq_iff_re.mp (ha u u).symm

/-- The real part of a Hermitian sesquilinear form is symmetric: `re (a u v) = re (a v u)`. -/
theorem re_apply_comm_of_eq_star {a : V →ₗ⋆[𝕜] V →ₗ[𝕜] 𝕜}
    (ha : ∀ u v, a u v = star (a v u)) (u v : V) :
    RCLike.re (a u v) = RCLike.re (a v u) := by
  rw [ha u v, ← RCLike.conj_re, starRingEnd_apply, star_star]

/-- Expansion of `re (a (u + v) (u + v))` for an arbitrary sesquilinear form. -/
theorem re_apply_add_self (a : V →ₗ⋆[𝕜] V →ₗ[𝕜] 𝕜) (u v : V) :
    RCLike.re (a (u + v) (u + v)) =
      RCLike.re (a u u) + RCLike.re (a u v) + RCLike.re (a v u) + RCLike.re (a v v) := by
  simp only [map_add, LinearMap.add_apply]
  ring

/-- Expansion of `re (a (u + v) (u + v))` for a Hermitian sesquilinear form. -/
theorem re_apply_add_self_of_eq_star {a : V →ₗ⋆[𝕜] V →ₗ[𝕜] 𝕜}
    (ha : ∀ u v, a u v = star (a v u)) (u v : V) :
    RCLike.re (a (u + v) (u + v)) =
      RCLike.re (a u u) + 2 * RCLike.re (a u v) + RCLike.re (a v v) := by
  rw [a.re_apply_add_self u v, re_apply_comm_of_eq_star ha v u]
  ring

/-- Expansion of `re (a (u - v) (u - v))` for a Hermitian sesquilinear form. -/
theorem re_apply_sub_self_of_eq_star {a : V →ₗ⋆[𝕜] V →ₗ[𝕜] 𝕜}
    (ha : ∀ u v, a u v = star (a v u)) (u v : V) :
    RCLike.re (a (u - v) (u - v)) =
      RCLike.re (a u u) - 2 * RCLike.re (a u v) + RCLike.re (a v v) := by
  have h := a.re_apply_add_self_of_eq_star ha u (-v)
  simp only [← sub_eq_add_neg, map_neg, LinearMap.neg_apply] at h
  linarith

/-- Quadratic homogeneity of `u ↦ re (a u u)` under `𝕜`-scalar multiplication. No symmetry of `a`
is needed, since `c * star c = ‖c‖²` is already real. -/
theorem re_apply_smul_self (a : V →ₗ⋆[𝕜] V →ₗ[𝕜] 𝕜) (c : 𝕜) (u : V) :
    RCLike.re (a (c • u) (c • u)) = ‖c‖ ^ 2 * RCLike.re (a u u) := by
  simp only [map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, RingHom.id_apply]
  rw [← mul_assoc, RCLike.mul_conj, ← RCLike.ofReal_pow, RCLike.re_ofReal_mul]

/-- Expansion of `re (a (u + c • v) (u + c • v))` along a `𝕜`-line for a Hermitian form. -/
theorem re_apply_add_smul_self_of_eq_star {a : V →ₗ⋆[𝕜] V →ₗ[𝕜] 𝕜}
    (ha : ∀ u v, a u v = star (a v u)) (u v : V) (c : 𝕜) :
    RCLike.re (a (u + c • v) (u + c • v)) =
      RCLike.re (a u u) + 2 * RCLike.re (c * a u v) + ‖c‖ ^ 2 * RCLike.re (a v v) := by
  rw [a.re_apply_add_self_of_eq_star ha u (c • v), map_smul, smul_eq_mul, a.re_apply_smul_self]

section RealScalar

variable [Module ℝ V] [IsScalarTower ℝ 𝕜 V]

/-- Expansion of `re (a (u + t • v) (u + t • v))` along a real line for a Hermitian form. -/
theorem re_apply_add_real_smul_self_of_eq_star {a : V →ₗ⋆[𝕜] V →ₗ[𝕜] 𝕜}
    (ha : ∀ u v, a u v = star (a v u)) (u v : V) (t : ℝ) :
    RCLike.re (a (u + t • v) (u + t • v)) =
      RCLike.re (a u u) + 2 * t * RCLike.re (a u v) + t ^ 2 * RCLike.re (a v v) := by
  rw [← algebraMap_smul 𝕜 t v, RCLike.algebraMap_eq_ofReal,
    a.re_apply_add_smul_self_of_eq_star ha u v (t : 𝕜), RCLike.re_ofReal_mul, RCLike.norm_ofReal,
    sq_abs]
  ring

/-- Along a two-point affine combination `t₁ • u + t₂ • v` with `t₁ + t₂ = 1`, the value of the
quadratic form `q(w) = re (a w w)` of any sesquilinear form satisfies
`q(t₁ • u + t₂ • v) + t₁ * t₂ * q(u - v) = t₁ * q(u) + t₂ * q(v)`. No symmetry of `a` is required,
and the weights `t₁` and `t₂` may be negative. -/
theorem re_apply_combo_self_add_mul_sub (a : V →ₗ⋆[𝕜] V →ₗ[𝕜] 𝕜) {t₁ t₂ : ℝ}
    (ht : t₁ + t₂ = 1) (u v : V) :
    RCLike.re (a (t₁ • u + t₂ • v) (t₁ • u + t₂ • v)) +
        t₁ * t₂ * RCLike.re (a (u - v) (u - v)) =
      t₁ * RCLike.re (a u u) + t₂ * RCLike.re (a v v) := by
  have ht₂ : t₂ = 1 - t₁ := eq_sub_of_add_eq' ht
  subst ht₂
  have hcombo : t₁ • u + (1 - t₁) • v = v + t₁ • (u - v) := by module
  rw [hcombo, ← algebraMap_smul 𝕜 t₁ (u - v), RCLike.algebraMap_eq_ofReal,
    a.re_apply_add_self v ((t₁ : 𝕜) • (u - v))]
  simp only [map_smul, map_smulₛₗ, LinearMap.smul_apply, map_sub, LinearMap.sub_apply,
    smul_eq_mul, RCLike.conj_ofReal, RCLike.re_ofReal_mul]
  ring

/-- If `re (a w w) ≥ 0` for every difference `w = u - v` of points in a convex set `C`, then
`u ↦ re (a u u)` is convex on `C`. No symmetry of `a` is required. -/
theorem convexOn_re_apply_self_of_sub_nonneg {a : V →ₗ⋆[𝕜] V →ₗ[𝕜] 𝕜}
    {C : Set V} (hC : Convex ℝ C)
    (hpos : ∀ u ∈ C, ∀ v ∈ C, 0 ≤ RCLike.re (a (u - v) (u - v))) :
    ConvexOn ℝ C (fun u ↦ RCLike.re (a u u)) := by
  refine ⟨hC, fun u hu v hv t₁ t₂ ht₁ ht₂ ht ↦ ?_⟩
  simp only [smul_eq_mul]
  have hdiff : 0 ≤ t₁ * t₂ * RCLike.re (a (u - v) (u - v)) :=
    mul_nonneg (mul_nonneg ht₁ ht₂) (hpos u hu v hv)
  linarith [a.re_apply_combo_self_add_mul_sub ht u v]

/-- If `a` is nonnegative on the diagonal (`∀ u, 0 ≤ re (a u u)`), then its quadratic form
`u ↦ re (a u u)` is convex on the whole space. No symmetry of `a` is required. -/
theorem convexOn_re_apply_self {a : V →ₗ⋆[𝕜] V →ₗ[𝕜] 𝕜}
    (hpos : ∀ u, 0 ≤ RCLike.re (a u u)) :
    ConvexOn ℝ Set.univ (fun u ↦ RCLike.re (a u u)) :=
  a.convexOn_re_apply_self_of_sub_nonneg convex_univ fun u _ v _ ↦ hpos (u - v)

end RealScalar

/-! ### Positive-semidefinite sesquilinear forms, Cauchy--Schwarz, and the kernel identity -/

/-- A Hermitian sesquilinear form (`a.IsSymm`) with nonnegative real diagonal packaged as a
`PreInnerProductSpace.Core 𝕜 V`. Used internally and by callers needing the pre-inner-product
seminorm without installing a competing `Norm` instance on `V`. -/
@[instance_reducible]
def sesqFormCore (a : V →ₗ⋆[𝕜] V →ₗ[𝕜] 𝕜) (ha : a.IsSymm)
    (hpos : ∀ u, 0 ≤ RCLike.re (a u u)) : PreInnerProductSpace.Core 𝕜 V where
  inner u v := a u v
  conj_inner_symm u v := ha.eq v u
  re_inner_nonneg := hpos
  add_left u v w := by simp only [map_add, LinearMap.add_apply]
  smul_left u v r := by simp only [map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul]

/-- The inner product of `a.sesqFormCore ha hpos` is `a`. -/
@[simp]
theorem sesqFormCore_inner (a : V →ₗ⋆[𝕜] V →ₗ[𝕜] 𝕜) (ha : a.IsSymm)
    (hpos : ∀ u, 0 ≤ RCLike.re (a u u)) (u v : V) :
    (a.sesqFormCore ha hpos).inner u v = a u v :=
  (rfl)

/-- **Cauchy--Schwarz inequality** for a nonnegative Hermitian sesquilinear form:
`‖a u v‖ ^ 2 ≤ re (a u u) * re (a v v)`. -/
theorem norm_apply_sq_le_re_apply_self_mul {a : V →ₗ⋆[𝕜] V →ₗ[𝕜] 𝕜}
    (ha : ∀ u v, a u v = star (a v u)) (hpos : ∀ u, 0 ≤ RCLike.re (a u u)) (u v : V) :
    ‖a u v‖ ^ 2 ≤ RCLike.re (a u u) * RCLike.re (a v v) := by
  have h := @InnerProductSpace.Core.inner_mul_inner_self_le 𝕜 V _ _ _
    (a.sesqFormCore (a.isSymm_iff_eq_star.mpr ha) hpos) u v
  simp only [sesqFormCore_inner] at h
  rwa [ha v u, norm_star, ← sq] at h

/-- Square-root form of the **Cauchy--Schwarz inequality** for a nonnegative Hermitian sesquilinear
form: `‖a u v‖ ≤ √(re (a u u)) * √(re (a v v))`. -/
theorem norm_apply_le_sqrt_re_apply_self_mul {a : V →ₗ⋆[𝕜] V →ₗ[𝕜] 𝕜}
    (ha : ∀ u v, a u v = star (a v u)) (hpos : ∀ u, 0 ≤ RCLike.re (a u u)) (u v : V) :
    ‖a u v‖ ≤ √(RCLike.re (a u u)) * √(RCLike.re (a v v)) := by
  rw [← Real.sqrt_mul (hpos u)]
  exact Real.le_sqrt_of_sq_le (a.norm_apply_sq_le_re_apply_self_mul ha hpos u v)

/-- **Kernel identity** for a nonnegative Hermitian sesquilinear form: `u` pairs to `0` against
every vector `v` if and only if its quadratic value `re (a u u)` vanishes. Nonnegativity is
essential (`diag(1, -1)` at `(1, 1)` fails the reverse implication). -/
theorem forall_apply_eq_zero_iff_re_apply_self_eq_zero {a : V →ₗ⋆[𝕜] V →ₗ[𝕜] 𝕜}
    (ha : ∀ u v, a u v = star (a v u)) (hpos : ∀ u, 0 ≤ RCLike.re (a u u)) {u : V} :
    (∀ v, a u v = 0) ↔ RCLike.re (a u u) = 0 := by
  refine ⟨fun h ↦ by simp [h u], fun hu v ↦ ?_⟩
  have hcs := a.norm_apply_sq_le_re_apply_self_mul ha hpos u v
  rw [hu, zero_mul] at hcs
  exact norm_eq_zero.mp (sq_eq_zero_iff.mp (le_antisymm hcs (sq_nonneg _)))

/-- Set form of the **kernel identity** for a nonnegative Hermitian sesquilinear form:
`{u | ∀ v, a u v = 0} = {u | re (a u u) = 0}`. -/
theorem setOf_forall_apply_eq_zero_eq {a : V →ₗ⋆[𝕜] V →ₗ[𝕜] 𝕜}
    (ha : ∀ u v, a u v = star (a v u)) (hpos : ∀ u, 0 ≤ RCLike.re (a u u)) :
    {u : V | ∀ v, a u v = 0} = {u : V | RCLike.re (a u u) = 0} :=
  Set.ext fun _ ↦ a.forall_apply_eq_zero_iff_re_apply_self_eq_zero ha hpos

/-- For a nonnegative Hermitian sesquilinear form, `a.ker = ⊥` if and only if `re (a u u) = 0`
implies `u = 0`. -/
theorem ker_eq_bot_iff_eq_zero_of_re_apply_self_eq_zero {a : V →ₗ⋆[𝕜] V →ₗ[𝕜] 𝕜}
    (ha : ∀ u v, a u v = star (a v u)) (hpos : ∀ u, 0 ≤ RCLike.re (a u u)) :
    a.ker = ⊥ ↔ ∀ u, RCLike.re (a u u) = 0 → u = 0 := by
  rw [Submodule.eq_bot_iff]
  refine forall_congr' fun u ↦ ?_
  simp only [mem_ker, LinearMap.ext_iff, LinearMap.zero_apply,
    a.forall_apply_eq_zero_iff_re_apply_self_eq_zero ha hpos]

end Algebraic

end LinearMap

namespace ContinuousLinearMap

section TopologicalRealBilin

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [AddCommGroup E] [Module 𝕜 E] [Module ℝ E] [IsScalarTower ℝ 𝕜 E] [TopologicalSpace E]
  [AddCommGroup F] [Module 𝕜 F] [Module ℝ F] [IsScalarTower ℝ 𝕜 F] [TopologicalSpace F]
  [ContinuousSMul 𝕜 F]

/-- The real part `(x, y) ↦ RCLike.re (a x y)` of a continuous `𝕜`-sesquilinear form
`a : E →L⋆[𝕜] F →L[𝕜] 𝕜`, packaged as a continuous real-bilinear map `E →L[ℝ] F →L[ℝ] ℝ`. -/
def reBilin (a : E →L⋆[𝕜] F →L[𝕜] 𝕜) : E →L[ℝ] F →L[ℝ] ℝ where
  toFun x := RCLike.reCLM.comp ((a x).restrictScalars ℝ)
  map_add' x y := by
    ext z
    simp
  map_smul' r x := by
    ext z
    rw [← algebraMap_smul 𝕜 r x, a.map_smulₛₗ]
    simp [RCLike.algebraMap_eq_ofReal]
  cont :=
    ((RCLike.reCLM.postcomp F).continuous.comp (continuous_restrictScalars ℝ)).comp a.continuous

/-- Evaluating `a.reBilin` on `x` gives the real-linear functional `y ↦ RCLike.re (a x y)`. -/
theorem reBilin_apply (a : E →L⋆[𝕜] F →L[𝕜] 𝕜) (x : E) :
    a.reBilin x = RCLike.reCLM.comp ((a x).restrictScalars ℝ) :=
  (rfl)

/-- Evaluating `a.reBilin` on `(x, y)` gives `RCLike.re (a x y)`. -/
@[simp]
theorem reBilin_apply_apply (a : E →L⋆[𝕜] F →L[𝕜] 𝕜) (x : E) (y : F) :
    a.reBilin x y = RCLike.re (a x y) :=
  (rfl)

/-- `reBilin` sends the zero sesquilinear form to `0`. -/
@[simp]
theorem reBilin_zero : (0 : E →L⋆[𝕜] F →L[𝕜] 𝕜).reBilin = 0 := by
  ext x y
  simp

/-- `reBilin` preserves addition of sesquilinear forms. -/
@[simp]
theorem reBilin_add (a b : E →L⋆[𝕜] F →L[𝕜] 𝕜) :
    (a + b).reBilin = a.reBilin + b.reBilin := by
  ext x y
  simp

/-- `reBilin` commutes with negation. -/
@[simp]
theorem reBilin_neg (a : E →L⋆[𝕜] F →L[𝕜] 𝕜) : (-a).reBilin = -a.reBilin := by
  ext x y
  simp

/-- `reBilin` preserves subtraction of sesquilinear forms. -/
@[simp]
theorem reBilin_sub (a b : E →L⋆[𝕜] F →L[𝕜] 𝕜) :
    (a - b).reBilin = a.reBilin - b.reBilin := by
  ext x y
  simp

/-- `reBilin` commutes with real scalar multiplication. -/
@[simp]
theorem reBilin_smul (r : ℝ) (a : E →L⋆[𝕜] F →L[𝕜] 𝕜) :
    (r • a).reBilin = r • a.reBilin := by
  ext x y
  simp [Algebra.smul_def, RCLike.algebraMap_eq_ofReal]

/-- Over `ℝ`, `reBilin` is the identity on continuous real-bilinear forms. -/
@[simp]
theorem reBilin_real {E' F' : Type*}
    [AddCommGroup E'] [Module ℝ E'] [TopologicalSpace E']
    [AddCommGroup F'] [Module ℝ F'] [TopologicalSpace F'] [ContinuousSMul ℝ F']
    (B : E' →L[ℝ] F' →L[ℝ] ℝ) : B.reBilin = B := by
  ext x y
  simp

/-- A continuous `𝕜`-sesquilinear form is uniquely determined by its real-part bilinear form
`a.reBilin`. -/
@[grind inj]
theorem reBilin_injective :
    Function.Injective (reBilin : (E →L⋆[𝕜] F →L[𝕜] 𝕜) → E →L[ℝ] F →L[ℝ] ℝ) := by
  intro a b h
  ext x y
  refine RCLike.apply_eq_of_re_eq_of_re_I_smul_eq ?_ ?_
  · simpa only [reBilin_apply_apply] using DFunLike.congr_fun (DFunLike.congr_fun h x) y
  · simpa only [reBilin_apply_apply] using
      DFunLike.congr_fun (DFunLike.congr_fun h x) ((RCLike.I : 𝕜) • y)

/-- Two continuous sesquilinear forms have equal `reBilin` if and only if they are equal. -/
@[simp]
theorem reBilin_inj {a b : E →L⋆[𝕜] F →L[𝕜] 𝕜} : a.reBilin = b.reBilin ↔ a = b :=
  reBilin_injective.eq_iff

/-- `a.reBilin` vanishes if and only if `a = 0`. -/
@[simp]
theorem reBilin_eq_zero {a : E →L⋆[𝕜] F →L[𝕜] 𝕜} : a.reBilin = 0 ↔ a = 0 := by
  rw [← reBilin_zero (𝕜 := 𝕜) (E := E) (F := F), reBilin_inj]

end TopologicalRealBilin

section TopologicalSelf

variable {𝕜 V : Type*} [RCLike 𝕜] [AddCommGroup V] [Module 𝕜 V] [TopologicalSpace V]

/-- For a continuous Hermitian form `a`, its real-part bilinear form `a.reBilin` is symmetric. -/
theorem reBilin_comm_of_eq_star [Module ℝ V] [IsScalarTower ℝ 𝕜 V] [ContinuousSMul 𝕜 V]
    {a : V →L⋆[𝕜] V →L[𝕜] 𝕜} (ha : ∀ u v, a u v = star (a v u)) (u v : V) :
    a.reBilin u v = a.reBilin v u := by
  simp only [reBilin_apply_apply]
  exact a.toLinearMap₁₂.re_apply_comm_of_eq_star ha u v

end TopologicalSelf

section SeminormedRealBilin

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [SeminormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E]
  [SeminormedAddCommGroup F] [NormedSpace 𝕜 F] [NormedSpace ℝ F] [IsScalarTower ℝ 𝕜 F]

/-- Pulling a sesquilinear form back along continuous `𝕜`-linear maps commutes with `reBilin`. -/
@[simp]
theorem reBilin_bilinearComp {E' F' : Type*}
    [SeminormedAddCommGroup E'] [NormedSpace 𝕜 E'] [NormedSpace ℝ E'] [IsScalarTower ℝ 𝕜 E']
    [SeminormedAddCommGroup F'] [NormedSpace 𝕜 F'] [NormedSpace ℝ F'] [IsScalarTower ℝ 𝕜 F']
    (a : E →L⋆[𝕜] F →L[𝕜] 𝕜) (L₁ : E' →L[𝕜] E) (L₂ : F' →L[𝕜] F) :
    (a.bilinearComp L₁ L₂).reBilin =
      a.reBilin.bilinearComp (L₁.restrictScalars ℝ) (L₂.restrictScalars ℝ) := by
  ext x y
  simp

/-- Taking the real part of the functional `a x` preserves its operator norm. -/
@[simp]
theorem norm_reBilin_apply (a : E →L⋆[𝕜] F →L[𝕜] 𝕜) (x : E) : ‖a.reBilin x‖ = ‖a x‖ := by
  rw [reBilin_apply, ← StrongDual.extendRCLikeₗᵢ_symm_apply (𝕜 := 𝕜) (F := F)]
  exact (StrongDual.extendRCLikeₗᵢ (𝕜 := 𝕜) (F := F)).symm.norm_map (a x)

/-- Taking the real-part bilinear form preserves the operator norm: `‖a.reBilin‖ = ‖a‖`. -/
@[simp]
theorem norm_reBilin (a : E →L⋆[𝕜] F →L[𝕜] 𝕜) : ‖a.reBilin‖ = ‖a‖ := by
  refine le_antisymm ?_ ?_
  · refine opNorm_le_bound _ (norm_nonneg a) fun x ↦ ?_
    rw [norm_reBilin_apply]
    exact a.le_opNorm x
  · refine opNorm_le_bound _ (norm_nonneg a.reBilin) fun x ↦ ?_
    rw [← norm_reBilin_apply]
    exact a.reBilin.le_opNorm x

end SeminormedRealBilin

section SeminormedSelf

variable {𝕜 V : Type*} [RCLike 𝕜] [SeminormedAddCommGroup V] [NormedSpace 𝕜 V]

/-- For a continuous sesquilinear form `a`, the real quadratic map `u ↦ RCLike.re (a u u)` is
continuous. -/
@[fun_prop]
theorem continuous_re_apply_self (a : V →L⋆[𝕜] V →L[𝕜] 𝕜) :
    Continuous (fun u ↦ RCLike.re (a u u)) :=
  RCLike.reCLM.continuous.comp
    (isBoundedBilinearMap_apply.continuous.comp (a.continuous.prodMk continuous_id))

/-- Flipping `a.reBilin` for a Hermitian form `a` returns `a.reBilin`. -/
theorem flip_reBilin_of_eq_star [NormedSpace ℝ V] [IsScalarTower ℝ 𝕜 V]
    {a : V →L⋆[𝕜] V →L[𝕜] 𝕜} (ha : ∀ u v, a u v = star (a v u)) :
    a.reBilin.flip = a.reBilin := by
  ext u v
  exact a.reBilin_comm_of_eq_star ha v u

/-- **Lipschitz dependence of constrained weak solutions on the restricted forcing.** If the real
quadratic part of `a` dominates `c * ‖w‖ ^ 2` on a submodule `W`, then solutions of `a u v = ℓ v`
and `a u' v = ℓ' v` on `W` that differ by an element of `W` satisfy
`c * ‖u - u'‖ ≤ ‖(ℓ - ℓ').comp W.subtypeL‖`. No symmetry of `a` or positivity of `c` is
required. -/
theorem mul_norm_sub_le_norm_comp_subtypeL_of_coercive {a : V →L⋆[𝕜] V →L[𝕜] 𝕜}
    (ℓ : StrongDual 𝕜 V) {W : Submodule 𝕜 V} {c : ℝ}
    (hc : ∀ w ∈ W, c * ‖w‖ ^ 2 ≤ RCLike.re (a w w)) {u u' : V} {ℓ' : StrongDual 𝕜 V}
    (hu : ∀ v ∈ W, a u v = ℓ v) (hu' : ∀ v ∈ W, a u' v = ℓ' v) (h : u - u' ∈ W) :
    c * ‖u - u'‖ ≤ ‖(ℓ - ℓ').comp W.subtypeL‖ := by
  rcases (norm_nonneg (u - u')).eq_or_lt with h0 | hpos
  · rw [← h0, mul_zero]
    exact norm_nonneg _
  · have hpair : a (u - u') (u - u') = ((ℓ - ℓ').comp W.subtypeL) ⟨u - u', h⟩ := by
      rw [a.map_sub, sub_apply, hu (u - u') h, hu' (u - u') h]
      simp
    have hle : c * ‖u - u'‖ ^ 2 ≤ ‖(ℓ - ℓ').comp W.subtypeL‖ * ‖u - u'‖ := by
      calc c * ‖u - u'‖ ^ 2 ≤ RCLike.re (a (u - u') (u - u')) := hc (u - u') h
        _ ≤ ‖a (u - u') (u - u')‖ := RCLike.re_le_norm _
        _ = ‖((ℓ - ℓ').comp W.subtypeL) ⟨u - u', h⟩‖ := by rw [hpair]
        _ ≤ ‖(ℓ - ℓ').comp W.subtypeL‖ * ‖(⟨u - u', h⟩ : W)‖ :=
            le_opNorm ((ℓ - ℓ').comp W.subtypeL) ⟨u - u', h⟩
        _ = ‖(ℓ - ℓ').comp W.subtypeL‖ * ‖u - u'‖ := by simp
    rw [sq, ← mul_assoc] at hle
    exact le_of_mul_le_mul_right hle hpos

end SeminormedSelf

section Calculus

variable {𝕜 V : Type*} [RCLike 𝕜] [NormedAddCommGroup V] [NormedSpace 𝕜 V]
  [NormedSpace ℝ V] [IsScalarTower ℝ 𝕜 V] {n : WithTop ℕ∞}

/-- The real quadratic map `u ↦ RCLike.re (a u u)` of a continuous sesquilinear form is `C^n` over
`ℝ` for every `n`. -/
@[fun_prop]
theorem contDiff_re_apply_self (a : V →L⋆[𝕜] V →L[𝕜] 𝕜) :
    ContDiff ℝ n (fun u ↦ RCLike.re (a u u)) := by
  simpa only [reBilin_apply_apply] using a.reBilin.contDiff_apply_self (n := n)

/-- The real quadratic map `u ↦ RCLike.re (a u u)` of a continuous sesquilinear form is
Fréchet differentiable over `ℝ`. -/
@[fun_prop]
theorem differentiable_re_apply_self (a : V →L⋆[𝕜] V →L[𝕜] 𝕜) :
    Differentiable ℝ (fun u ↦ RCLike.re (a u u)) := by
  simpa only [reBilin_apply_apply] using a.reBilin.differentiable_apply_self

/-- Strict real Fréchet derivative of `u ↦ RCLike.re (a u u)` for an arbitrary continuous
sesquilinear form `a`. -/
theorem hasStrictFDerivAt_re_apply_self (a : V →L⋆[𝕜] V →L[𝕜] 𝕜) (u : V) :
    HasStrictFDerivAt (fun w ↦ RCLike.re (a w w)) (a.reBilin.flip u + a.reBilin u) u := by
  simpa only [reBilin_apply_apply] using a.reBilin.hasStrictFDerivAt_apply_self u

/-- Real Fréchet derivative of `u ↦ RCLike.re (a u u)` for an arbitrary continuous sesquilinear
form `a`. -/
theorem hasFDerivAt_re_apply_self (a : V →L⋆[𝕜] V →L[𝕜] 𝕜) (u : V) :
    HasFDerivAt (fun w ↦ RCLike.re (a w w)) (a.reBilin.flip u + a.reBilin u) u :=
  (a.hasStrictFDerivAt_re_apply_self u).hasFDerivAt

/-- Differential of `u ↦ RCLike.re (a u u)` over `ℝ` for an arbitrary continuous sesquilinear
form `a`. -/
@[simp]
theorem fderiv_re_apply_self (a : V →L⋆[𝕜] V →L[𝕜] 𝕜) (u : V) :
    fderiv ℝ (fun w ↦ RCLike.re (a w w)) u = a.reBilin.flip u + a.reBilin u :=
  (a.hasFDerivAt_re_apply_self u).fderiv

/-- Strict real Fréchet derivative of `u ↦ RCLike.re (a u u)` for a continuous Hermitian
sesquilinear form `a`: at `u`, the derivative is `v ↦ 2 * RCLike.re (a u v)`. -/
theorem hasStrictFDerivAt_re_apply_self_of_eq_star {a : V →L⋆[𝕜] V →L[𝕜] 𝕜}
    (ha : ∀ x y, a x y = star (a y x)) (u : V) :
    HasStrictFDerivAt (fun w ↦ RCLike.re (a w w))
      ((2 : ℝ) • RCLike.reCLM.comp ((a u).restrictScalars ℝ)) u := by
  have h := a.hasStrictFDerivAt_re_apply_self u
  rwa [a.flip_reBilin_of_eq_star ha, ← two_smul ℝ, reBilin_apply] at h

/-- Real Fréchet derivative of `u ↦ RCLike.re (a u u)` for a continuous Hermitian sesquilinear
form `a`. -/
theorem hasFDerivAt_re_apply_self_of_eq_star {a : V →L⋆[𝕜] V →L[𝕜] 𝕜}
    (ha : ∀ x y, a x y = star (a y x)) (u : V) :
    HasFDerivAt (fun w ↦ RCLike.re (a w w))
      ((2 : ℝ) • RCLike.reCLM.comp ((a u).restrictScalars ℝ)) u :=
  (a.hasStrictFDerivAt_re_apply_self_of_eq_star ha u).hasFDerivAt

/-- Differential of `u ↦ RCLike.re (a u u)` over `ℝ` for a continuous Hermitian sesquilinear
form `a`. -/
theorem fderiv_re_apply_self_of_eq_star {a : V →L⋆[𝕜] V →L[𝕜] 𝕜}
    (ha : ∀ x y, a x y = star (a y x)) (u : V) :
    fderiv ℝ (fun w ↦ RCLike.re (a w w)) u =
      (2 : ℝ) • RCLike.reCLM.comp ((a u).restrictScalars ℝ) :=
  (a.hasFDerivAt_re_apply_self_of_eq_star ha u).fderiv

end Calculus

end ContinuousLinearMap

end
