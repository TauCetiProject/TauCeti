/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.YangMills.GaugeIdentities
public import Mathlib.Analysis.Calculus.DifferentialForm.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import TauCeti.Analysis.Calculus.DifferentialForm.Basic
import TauCeti.Analysis.Calculus.DifferentialForm.Regularity
import TauCeti.Analysis.Calculus.FDeriv.Prod
import TauCeti.Analysis.Calculus.SecondDerivative
import TauCeti.Analysis.Normed.Module.Alternating.Curry
import TauCeti.Topology.Algebra.Module.BilinearForm
import TauCeti.Data.Fin.VecNotation

/-!
# The minimal coupling form of a symplectic connection

Let `E` be a normed space carrying a two-form `ω`, let `(V, σ)` be a normed space with a constant
skew-symmetric bilinear form, and let `d + A` be a connection on the trivial bundle `E × V → E`,
given by its connection form `A : E → E →L[ℝ] V →L[ℝ] V`. The connection is **symplectic** at `z`
when `A_z(v)` lies in the Lie algebra of `σ` for every `v`,
`σ(A_z(v) u, u') = -σ(u, A_z(v) u')`. The covariant derivative of the fibre coordinate `w` along a
tangent vector `(v, n)` of the total space is `n + A_z(v) w`, and the **minimal coupling
primitive** is the one-form

`λ_(z, w)(v, n) = σ(w, n + A_z(v) w) / 2`

(`TauCeti.minimalCouplingPrimitive`). The **minimal coupling form** is

`ω_A = π^* ω + dλ`

(`TauCeti.minimalCouplingForm`). This is Sternberg's minimal coupling construction, read in one
trivialization: the closed two-form it produces near the zero section of a symplectic vector
bundle with a symplectic connection, such as the symplectic normal bundle of a symplectic
submanifold, is `ω_A` in each local trivialization. The coupling form `TauCeti.normalCouplingForm`
of a Hermitian connection `d + i a` on a line is the case `V = ℂ`, `σ(n, n') = Im (conj n n')`,
`A = i a`, whose primitive is `Im (conj w (n + i a(v) w)) / 2`
(`TauCeti.normalCouplingForm_eq_minimalCouplingForm`).

This file proves the following.

* **Value.** For any `σ`, `dλ` is computed from the derivative of `A`
  (`TauCeti.extDeriv_minimalCouplingPrimitive_apply_pair`). For skew-symmetric `σ` this gives
  `ω_A((0, n), (0, n')) = σ(n, n')` on the fibres (`TauCeti.minimalCouplingForm_apply_inr_inr`)
  and `ω_A = ω + σ` along the zero section (`TauCeti.minimalCouplingForm_apply_pair_zero`). For
  a connection that is moreover symplectic at `z`,
  `ω_A((v, n), (v', n')) = ω(v, v') + σ(n + A_z(v) w, n' + A_z(v') w) + σ(w, F_z(v, v') w) / 2`,
  where `F = dA + ½[A ∧ A]` is the curvature of `d + A` (`TauCeti.connectionCurvature`)
  (`TauCeti.minimalCouplingForm_apply_pair`,
  `TauCeti.extDeriv_minimalCouplingPrimitive_apply_pair_eq_add_curvature`).
* **Horizontal and vertical.** For a connection symplectic at `z`, the horizontal lift
  `(v, -A_z(v) w)` of `v` is `ω_A`-orthogonal to the fibre
  (`TauCeti.minimalCouplingForm_apply_horizontal_inr`), and on two horizontal lifts `ω_A` is
  `ω + σ(w, F w) / 2` (`TauCeti.minimalCouplingForm_apply_horizontal`). Hence, for nondegenerate
  `σ`, the kernel of `ω_A` at `(z, w)` consists of the horizontal lifts of the kernel of
  `ω + σ(w, F w) / 2` at `z` (`TauCeti.forall_minimalCouplingForm_apply_eq_zero_iff`).
* **Nondegeneracy near the zero section.** For skew-symmetric nondegenerate `σ` and any
  connection, `ω_A` is nondegenerate at `(z, 0)` exactly when `ω` is nondegenerate at `z`
  (`TauCeti.forall_minimalCouplingForm_apply_zero_eq_zero_iff`), and in finite dimensions it is
  then nondegenerate on a neighbourhood of `(z, 0)`
  (`TauCeti.eventually_eq_zero_of_forall_minimalCouplingForm_apply_eq_zero`).
* **Closedness.** `ω_A` is closed where `ω` is (`TauCeti.extDeriv_minimalCouplingForm_eq_zero`),
  being the sum of a pullback of `ω` and an exact form.
* **Gauge transformations.** If `O` is a map to the invertible endomorphisms of `V` preserving
  `σ`, the bundle map `(z, w) ↦ (z, O_z w)` pulls the minimal coupling primitive of the gauge
  transformed connection `O·A = O A O⁻¹ - (dO) O⁻¹` (`TauCeti.gaugeAction`) back to that of `A`
  (`TauCeti.compContinuousLinearMap_minimalCouplingPrimitive_gaugeAction`), and so it pulls the
  minimal coupling form of `O·A` back to that of `A`
  (`TauCeti.compContinuousLinearMap_minimalCouplingForm_gaugeAction`). The local forms of a
  symplectic connection in two symplectic trivializations therefore correspond under the change
  of trivialization.

## References

* S. Sternberg, *Minimal coupling and the symplectic mechanics of a classical particle in the
  presence of a Yang–Mills field*, Proc. Nat. Acad. Sci. U.S.A. 74 (1977), 5253–5254.
* A. Weinstein, *A universal phase space for particles in Yang–Mills fields*, Lett. Math. Phys. 2
  (1978), 417–420.
* V. Guillemin, E. Lerman and S. Sternberg, *Symplectic fibrations and multiplicity diagrams*,
  Cambridge University Press, 1996.
-/

public section

noncomputable section

open ContinuousAlternatingMap
open Filter
open scoped Ring Topology

namespace TauCeti

variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup V]
  [NormedSpace ℝ V] {σ : V →L[ℝ] V →L[ℝ] ℝ} {ω : E → E [⋀^Fin 2]→L[ℝ] ℝ}
  {A : E → E →L[ℝ] V →L[ℝ] V} {z : E} {w : V}

/-! ### The coupling primitive -/

/-- The **minimal coupling primitive** `λ_(z, w)(v, n) = σ(w, n + A_z(v) w) / 2` of the connection
`d + A` on the trivial bundle `E × V`, a one-form on the total space. Here `n + A_z(v) w` is the
covariant derivative of the fibre coordinate `w` along `(v, n)`. -/
def minimalCouplingPrimitive (σ : V →L[ℝ] V →L[ℝ] ℝ) (A : E → E →L[ℝ] V →L[ℝ] V) (p : E × V) :
    (E × V) [⋀^Fin 1]→L[ℝ] ℝ :=
  ofSubsingletonLIE (0 : Fin 1) ((2⁻¹ : ℝ) • (σ p.2).comp (ContinuousLinearMap.snd ℝ E V +
    ((ContinuousLinearMap.apply ℝ V p.2).comp (A p.1)).comp (ContinuousLinearMap.fst ℝ E V)))

/-- The minimal coupling primitive at `p = (z, w)` on a vector `u 0 = (v, n)` is
`σ(w, n + A_z(v) w) / 2`. -/
@[simp]
theorem minimalCouplingPrimitive_apply (σ : V →L[ℝ] V →L[ℝ] ℝ) (A : E → E →L[ℝ] V →L[ℝ] V)
    (p : E × V) (u : Fin 1 → E × V) :
    minimalCouplingPrimitive σ A p u = σ p.2 ((u 0).2 + A p.1 (u 0).1 p.2) / 2 := by
  simp [minimalCouplingPrimitive, ofSubsingletonLIE, div_eq_inv_mul, mul_add]

/-- The minimal coupling primitive on a vector `(v, n)` at `(z, w)` is `σ(w, n + A_z(v) w) / 2`. -/
theorem minimalCouplingPrimitive_apply_const (σ : V →L[ℝ] V →L[ℝ] ℝ)
    (A : E → E →L[ℝ] V →L[ℝ] V) (z : E) (w : V) (v : E) (n : V) :
    minimalCouplingPrimitive σ A (z, w) (fun _ ↦ (v, n)) = σ w (n + A z v w) / 2 :=
  minimalCouplingPrimitive_apply σ A (z, w) _

/-- The minimal coupling primitive of a connection form that is `C^n` at `z` is `C^n` at every
point `(z, w)` of the fibre over `z`. -/
theorem contDiffAt_minimalCouplingPrimitive {n : WithTop ℕ∞} (hA : ContDiffAt ℝ n A z) (w : V) :
    ContDiffAt ℝ n (minimalCouplingPrimitive σ A) (z, w) := by
  have : ContDiffAt ℝ n (fun p : E × V ↦ A p.1) (z, w) := hA.comp (z, w) contDiffAt_fst
  unfold minimalCouplingPrimitive
  fun_prop

/-- The minimal coupling primitive of a `C^n` connection form is `C^n`. -/
theorem contDiff_minimalCouplingPrimitive {n : WithTop ℕ∞} (hA : ContDiff ℝ n A) :
    ContDiff ℝ n (minimalCouplingPrimitive σ A) :=
  contDiff_iff_contDiffAt.2 fun p ↦ contDiffAt_minimalCouplingPrimitive hA.contDiffAt p.2

/-- The minimal coupling primitive of a connection form differentiable at `z` is differentiable at
every point `(z, w)` of the fibre over `z`. -/
theorem differentiableAt_minimalCouplingPrimitive (hA : DifferentiableAt ℝ A z) (w : V) :
    DifferentiableAt ℝ (minimalCouplingPrimitive σ A) (z, w) := by
  have : DifferentiableAt ℝ (fun p : E × V ↦ A p.1) (z, w) := hA.comp (z, w) differentiableAt_fst
  unfold minimalCouplingPrimitive
  fun_prop

/-- **The differential of the minimal coupling primitive**, for an arbitrary bilinear form `σ` and
a connection form differentiable at `z`:

`dλ((v, n), (v', n')) = (σ(n, n' + A_z(v') w) + σ(w, A_z(v') n + (∂_v A)_z(v') w)) / 2`
`  - (σ(n', n + A_z(v) w) + σ(w, A_z(v) n' + (∂_(v') A)_z(v) w)) / 2`.

For skew-symmetric `σ` and a symplectic connection this is
`TauCeti.extDeriv_minimalCouplingPrimitive_apply_pair_eq_add_curvature`. -/
theorem extDeriv_minimalCouplingPrimitive_apply_pair (hA : DifferentiableAt ℝ A z) (v v' : E)
    (n n' : V) :
    extDeriv (minimalCouplingPrimitive σ A) (z, w) ![(v, n), (v', n')] =
      (σ n (n' + A z v' w) + σ w (A z v' n + fderiv ℝ A z v v' w)) / 2 -
        (σ n' (n + A z v w) + σ w (A z v n' + fderiv ℝ A z v' v w)) / 2 := by
  have hA' : HasFDerivAt (fun p : E × V ↦ A p.1)
      ((fderiv ℝ A z).comp (ContinuousLinearMap.fst ℝ E V)) (z, w) :=
    hA.hasFDerivAt.comp (z, w) (hasFDerivAt_fst (p := (z, w)))
  -- The coefficient functions `q ↦ λ_q(v₁, n₁)` and their derivatives at `(z, w)`.
  have hfun (v₁ : E) (n₁ : V) : (fun q ↦ minimalCouplingPrimitive σ A q fun _ ↦ (v₁, n₁)) =
      fun q : E × V ↦ 2⁻¹ * σ q.2 (n₁ + A q.1 v₁ q.2) := by
    funext ⟨a, b⟩
    simp [div_eq_inv_mul]
  have hder (v₁ v₂ : E) (n₁ n₂ : V) :
      fderiv ℝ (fun q : E × V ↦ 2⁻¹ * σ q.2 (n₂ + A q.1 v₂ q.2)) (z, w) (v₁, n₁) =
        (σ n₁ (n₂ + A z v₂ w) + σ w (A z v₂ n₁ + fderiv ℝ A z v₁ v₂ w)) / 2 := by
    have hg := ((hA'.clm_apply (hasFDerivAt_const v₂ (z, w))).clm_apply
      (hasFDerivAt_snd (p := (z, w)))).const_add n₂
    rw [(HasFDerivAt.const_mul (σ.hasFDerivAt_of_bilinear (hasFDerivAt_snd (p := (z, w))) hg)
      2⁻¹).fderiv]
    simp
    ring
  rw [extDeriv_apply_pair_of_differentiableAt (differentiableAt_minimalCouplingPrimitive hA w),
    hfun, hfun, hder, hder]

/-- **The differential of the minimal coupling primitive of a symplectic connection.** Let `σ` be
skew-symmetric and let the connection form take values in the Lie algebra of `σ` at `z`,
`σ(A_z(v) u, u') = -σ(u, A_z(v) u')`. Where `A` is differentiable,

`dλ((v, n), (v', n')) = σ(n + A_z(v) w, n' + A_z(v') w) + σ(w, F_z(v, v') w) / 2`,

where `F = dA + ½[A ∧ A]` is the curvature of `d + A` (`TauCeti.connectionCurvature`). -/
theorem extDeriv_minimalCouplingPrimitive_apply_pair_eq_add_curvature
    (hσ : ∀ u u', σ u u' = -σ u' u) (hAσ : ∀ v u u', σ (A z v u) u' = -σ u (A z v u'))
    (hA : DifferentiableAt ℝ A z) (v v' : E) (n n' : V) :
    extDeriv (minimalCouplingPrimitive σ A) (z, w) ![(v, n), (v', n')] =
      σ (n + A z v w) (n' + A z v' w) + σ w (connectionCurvature ℝ A z v v' w) / 2 := by
  rw [extDeriv_minimalCouplingPrimitive_apply_pair hA]
  simp only [connectionCurvature_apply, Ring.lie_def, map_add, map_sub, _root_.add_apply,
    _root_.sub_apply, mul_apply_eq_comp]
  linear_combination (-1 / 2 : ℝ) * hσ n' n + (1 / 2 : ℝ) * hAσ v' w n -
    (1 / 2 : ℝ) * hσ n (A z v' w) - (1 / 2 : ℝ) * hσ n' (A z v w) - (1 / 2 : ℝ) * hAσ v w n' -
    (1 / 2 : ℝ) * hAσ v w (A z v' w) + (1 / 2 : ℝ) * hAσ v' w (A z v w) -
    (1 / 2 : ℝ) * hσ (A z v w) (A z v' w)

/-! ### The minimal coupling form -/

/-- The **minimal coupling form** `ω_A = π^* ω + dλ` on `E × V` of a two-form `ω` on the base and
the connection `d + A` on the trivial bundle with fibre form `σ`, where `λ` is the minimal coupling
primitive. -/
def minimalCouplingForm (σ : V →L[ℝ] V →L[ℝ] ℝ) (ω : E → E [⋀^Fin 2]→L[ℝ] ℝ)
    (A : E → E →L[ℝ] V →L[ℝ] V) (p : E × V) : (E × V) [⋀^Fin 2]→L[ℝ] ℝ :=
  (ω p.1).compContinuousLinearMap (ContinuousLinearMap.fst ℝ E V) +
    extDeriv (minimalCouplingPrimitive σ A) p

/-- The minimal coupling form is `π^* ω + dλ`, evaluated on vectors. -/
theorem minimalCouplingForm_apply (σ : V →L[ℝ] V →L[ℝ] ℝ) (ω : E → E [⋀^Fin 2]→L[ℝ] ℝ)
    (A : E → E →L[ℝ] V →L[ℝ] V) (p : E × V) (u : Fin 2 → E × V) :
    minimalCouplingForm σ ω A p u =
      ω p.1 (Prod.fst ∘ u) + extDeriv (minimalCouplingPrimitive σ A) p u := (rfl)

/-- The minimal coupling form of a two-form that is `C^n` at `z` and a connection form that is
`C^(n+1)` at `z` is `C^n` at every point `(z, w)` of the fibre over `z`. -/
theorem contDiffAt_minimalCouplingForm {n : WithTop ℕ∞} (hω : ContDiffAt ℝ n ω z)
    (hA : ContDiffAt ℝ (n + 1) A z) (w : V) :
    ContDiffAt ℝ n (minimalCouplingForm σ ω A) (z, w) :=
  (contDiffAt_pullback_continuousLinearMap (ContinuousLinearMap.fst ℝ E V) hω).add
    (contDiffAt_extDeriv (contDiffAt_minimalCouplingPrimitive hA w) le_rfl)

/-- The minimal coupling form of a `C^n` two-form and a `C^(n+1)` connection form is `C^n`. -/
theorem contDiff_minimalCouplingForm {n : WithTop ℕ∞} (hω : ContDiff ℝ n ω)
    (hA : ContDiff ℝ (n + 1) A) : ContDiff ℝ n (minimalCouplingForm σ ω A) :=
  contDiff_iff_contDiffAt.2 fun p ↦
    contDiffAt_minimalCouplingForm hω.contDiffAt hA.contDiffAt p.2

/-- **The minimal coupling form on a fibre** is the fibre form:
`ω_A((0, n), (0, n')) = σ(n, n')`, for skew-symmetric `σ`. -/
theorem minimalCouplingForm_apply_inr_inr (hσ : ∀ u u', σ u u' = -σ u' u)
    (hA : DifferentiableAt ℝ A z) (n n' : V) :
    minimalCouplingForm σ ω A (z, w) ![(0, n), (0, n')] = σ n n' := by
  rw [minimalCouplingForm_apply, Matrix.comp_vec2, extDeriv_minimalCouplingPrimitive_apply_pair hA,
    (ω z).map_coord_zero 0 rfl]
  simp only [_root_.map_zero, _root_.zero_apply, add_zero]
  linear_combination (-1 / 2 : ℝ) * hσ n' n

/-- **The minimal coupling form along the zero section** is the sum of the base and fibre forms:
`ω_A((v, n), (v', n')) = ω(v, v') + σ(n, n')` at `(z, 0)`, for skew-symmetric `σ`. -/
theorem minimalCouplingForm_apply_pair_zero (hσ : ∀ u u', σ u u' = -σ u' u)
    (hA : DifferentiableAt ℝ A z) (v v' : E) (n n' : V) :
    minimalCouplingForm σ ω A (z, 0) ![(v, n), (v', n')] = ω z ![v, v'] + σ n n' := by
  rw [minimalCouplingForm_apply, Matrix.comp_vec2, extDeriv_minimalCouplingPrimitive_apply_pair hA]
  simp only [_root_.map_zero, _root_.zero_apply, add_zero]
  linear_combination (-1 / 2 : ℝ) * hσ n' n

section Symplectic

variable (hσ : ∀ u u', σ u u' = -σ u' u) (hAσ : ∀ v u u', σ (A z v u) u' = -σ u (A z v u'))
  (hA : DifferentiableAt ℝ A z)
include hσ hAσ hA

/-- **The minimal coupling form on a pair of vectors.** For skew-symmetric `σ` and a connection
form with values in the Lie algebra of `σ` at `z`, differentiable at `z`,

`ω_A((v, n), (v', n')) = ω(v, v') + σ(n + A_z(v) w, n' + A_z(v') w) + σ(w, F_z(v, v') w) / 2`,

where `F` is the curvature of `d + A`. -/
theorem minimalCouplingForm_apply_pair (v v' : E) (n n' : V) :
    minimalCouplingForm σ ω A (z, w) ![(v, n), (v', n')] =
      ω z ![v, v'] + σ (n + A z v w) (n' + A z v' w) +
        σ w (connectionCurvature ℝ A z v v' w) / 2 := by
  rw [minimalCouplingForm_apply, Matrix.comp_vec2,
    extDeriv_minimalCouplingPrimitive_apply_pair_eq_add_curvature hσ hAσ hA, add_assoc]

/-- **Horizontal lifts are orthogonal to the fibres.** The horizontal lift `(v, -A_z(v) w)` of `v`
at `(z, w)`, on which the covariant derivative of `w` vanishes, is `ω_A`-orthogonal to every
vertical vector `(0, n)`. -/
theorem minimalCouplingForm_apply_horizontal_inr (v : E) (n : V) :
    minimalCouplingForm σ ω A (z, w) ![(v, -(A z v w)), (0, n)] = 0 := by
  rw [minimalCouplingForm_apply_pair hσ hAσ hA]
  have h₀ : ω z ![v, 0] = 0 := (ω z).map_coord_zero 1 rfl
  simp [h₀, Ring.lie_def]

/-- **The minimal coupling form on horizontal lifts** is `ω + σ(w, F w) / 2`: on the horizontal
lifts `(v, -A_z(v) w)` and `(v', -A_z(v') w)` at `(z, w)` it takes the value
`ω(v, v') + σ(w, F_z(v, v') w) / 2`. For a flat connection this is `ω(v, v')`. -/
theorem minimalCouplingForm_apply_horizontal (v v' : E) :
    minimalCouplingForm σ ω A (z, w) ![(v, -(A z v w)), (v', -(A z v' w))] =
      ω z ![v, v'] + σ w (connectionCurvature ℝ A z v v' w) / 2 := by
  rw [minimalCouplingForm_apply_pair hσ hAσ hA]
  simp

/-- **The kernel of the minimal coupling form.** Let `σ` be nondegenerate. A vector `(v, n)` at
`(z, w)` pairs to zero with every vector under `ω_A` exactly when it is the horizontal lift of `v`,
`n = -A_z(v) w`, and `v` pairs to zero with every vector under `ω + σ(w, F w) / 2`. So `ω_A` is
nondegenerate at `(z, w)` exactly when `v ↦ ω(v, ·) + σ(w, F_z(v, ·) w) / 2` is injective. -/
theorem forall_minimalCouplingForm_apply_eq_zero_iff (hσn : ∀ u, (∀ u', σ u u' = 0) → u = 0)
    (v : E) (n : V) :
    (∀ x : E × V, minimalCouplingForm σ ω A (z, w) ![(v, n), x] = 0) ↔
      n = -(A z v w) ∧
        ∀ v' : E, ω z ![v, v'] + σ w (connectionCurvature ℝ A z v v' w) / 2 = 0 := by
  constructor
  · intro h
    -- Pairing with the vertical vectors shows that the covariant derivative of `w` vanishes.
    have hc : n + A z v w = 0 := hσn _ fun n' ↦ by
      have hvert := h (0, n')
      rw [minimalCouplingForm_apply_pair hσ hAσ hA, (ω z).map_coord_zero 1 rfl] at hvert
      simpa [Ring.lie_def] using hvert
    refine ⟨eq_neg_of_add_eq_zero_left hc, fun v' ↦ ?_⟩
    have hhor := h (v', -(A z v' w))
    rw [minimalCouplingForm_apply_pair hσ hAσ hA, hc] at hhor
    simpa using hhor
  · rintro ⟨hn, hv⟩ ⟨v', n'⟩
    rw [minimalCouplingForm_apply_pair hσ hAσ hA, hn]
    simpa using hv v'

end Symplectic

/-- **Nondegeneracy along the zero section.** For skew-symmetric and nondegenerate `σ`, the
kernel of `ω_A` at `(z, 0)` consists of the vectors `(v, 0)` with `v` in the kernel of `ω` at `z`.
So `ω_A` is nondegenerate along the zero section exactly where `ω` is. -/
theorem forall_minimalCouplingForm_apply_zero_eq_zero_iff (hσ : ∀ u u', σ u u' = -σ u' u)
    (hσn : ∀ u, (∀ u', σ u u' = 0) → u = 0) (hA : DifferentiableAt ℝ A z) (v : E) (n : V) :
    (∀ x : E × V, minimalCouplingForm σ ω A (z, 0) ![(v, n), x] = 0) ↔
      n = 0 ∧ ∀ v' : E, ω z ![v, v'] = 0 := by
  have hω₀ (v' : E) : ω z ![v', 0] = 0 := (ω z).map_coord_zero 1 rfl
  constructor
  · intro h
    have hn : n = 0 := hσn n fun n' ↦ by
      simpa [minimalCouplingForm_apply_pair_zero hσ hA, hω₀] using h (0, n')
    refine ⟨hn, fun v' ↦ ?_⟩
    simpa [minimalCouplingForm_apply_pair_zero hσ hA, hn] using h (v', 0)
  · rintro ⟨rfl, hv⟩ ⟨v', n'⟩
    simp [minimalCouplingForm_apply_pair_zero hσ hA, hv v']

/-- **Nondegeneracy near the zero section.** In finite dimensions, let `σ` be skew-symmetric and
nondegenerate, let the connection form be `C¹` at `z`, and let `ω` be continuous and nondegenerate
at `z`. Then the minimal coupling form is nondegenerate at every point of a neighbourhood of
`(z, 0)`. -/
theorem eventually_eq_zero_of_forall_minimalCouplingForm_apply_eq_zero [FiniteDimensional ℝ E]
    [FiniteDimensional ℝ V] (hσ : ∀ u u', σ u u' = -σ u' u)
    (hσn : ∀ u, (∀ u', σ u u' = 0) → u = 0)
    (hω : ContinuousAt ω z) (hωn : ∀ v, (∀ v', ω z ![v, v'] = 0) → v = 0)
    (hA : ContDiffAt ℝ 1 A z) :
    ∀ᶠ p in 𝓝 (z, (0 : V)), ∀ x : E × V,
      (∀ y : E × V, minimalCouplingForm σ ω A p ![x, y] = 0) → x = 0 := by
  set g : E × V → E × V →L[ℝ] E × V →L[ℝ] ℝ :=
    fun p ↦ flatL ℝ (E × V) ℝ (minimalCouplingForm σ ω A p) with hg
  have hgx (p : E × V) (x : E × V) :
      g p x = 0 ↔ ∀ y : E × V, minimalCouplingForm σ ω A p ![x, y] = 0 := by
    simp [hg, ContinuousLinearMap.ext_iff, flatL_apply_apply]
  have hpull : ContinuousAt (fun p : E × V ↦
      (ω p.1).compContinuousLinearMap (ContinuousLinearMap.fst ℝ E V)) (z, 0) :=
    (compContinuousLinearMapCLM (ContinuousLinearMap.fst ℝ E V)).continuous.continuousAt.comp
      (hω.comp continuousAt_fst)
  have hgc : ContinuousAt g (z, 0) :=
    (flatL ℝ (E × V) ℝ).continuous.continuousAt.comp (hpull.add
      (contDiffAt_extDeriv (contDiffAt_minimalCouplingPrimitive hA 0) (r := 0)
        (by simp)).continuousAt)
  have hnd : (g (z, 0)).toBilinForm.Nondegenerate := by
    rw [ContinuousLinearMap.nondegenerate_toBilinForm_iff_injective,
      injective_iff_map_eq_zero]
    rintro ⟨v, n⟩ h
    obtain ⟨rfl, hv⟩ := (forall_minimalCouplingForm_apply_zero_eq_zero_iff hσ hσn
      (hA.differentiableAt one_ne_zero) v n).1 ((hgx _ _).1 h)
    rw [hωn v hv, Prod.mk_zero_zero]
  filter_upwards [hgc.eventually_toBilinForm_nondegenerate hnd] with p hp x hx
  exact (injective_iff_map_eq_zero _).1
    ((ContinuousLinearMap.nondegenerate_toBilinForm_iff_injective _).1 hp) x ((hgx p x).2 hx)

/-- **The minimal coupling form is closed** where `ω` is: if `ω` is differentiable and closed at
`z` and `A` is `C²` at `z`, then `dω_A = 0` at every point `(z, w)` of the fibre over `z`. -/
theorem extDeriv_minimalCouplingForm_eq_zero (hω : DifferentiableAt ℝ ω z)
    (hdω : extDeriv ω z = 0) (hA : ContDiffAt ℝ 2 A z) :
    extDeriv (minimalCouplingForm σ ω A) (z, w) = 0 := by
  have hlam := contDiffAt_minimalCouplingPrimitive (σ := σ) hA w
  have hpull := differentiableAt_pullback_continuousLinearMap (ContinuousLinearMap.fst ℝ E V)
    (x := (z, w)) hω
  have hdlam : DifferentiableAt ℝ (extDeriv (minimalCouplingPrimitive σ A)) (z, w) :=
    (contDiffAt_extDeriv hlam (r := 1) (by norm_num)).differentiableAt one_ne_zero
  have hsum : minimalCouplingForm σ ω A =
      (fun p : E × V ↦ (ω (ContinuousLinearMap.fst ℝ E V p)).compContinuousLinearMap
        (ContinuousLinearMap.fst ℝ E V)) + extDeriv (minimalCouplingPrimitive σ A) := by
    funext p
    simp [minimalCouplingForm]
  rw [hsum, extDeriv_add hpull hdlam, extDeriv_extDeriv_apply hlam (by simp), add_zero]
  exact (ContinuousLinearMap.fst ℝ E V).extDeriv_pullback_eq_zero hω hdω

/-! ### Gauge transformations -/

section Gauge

variable {O : E → V →L[ℝ] V}

/-- **The gauge transformation of the minimal coupling primitive.** Let `O_z` be invertible and
preserve `σ`, and let `O` be differentiable at `z`. The bundle map `(z, w) ↦ (z, O_z w)` pulls the
minimal coupling primitive of the gauge transformed connection `O·A`
(`TauCeti.gaugeAction`) back to that of `A`, at every point `(z, w)` of the fibre over `z`. -/
theorem compContinuousLinearMap_minimalCouplingPrimitive_gaugeAction
    (hO : DifferentiableAt ℝ O z) (hOz : IsUnit (O z)) (hOσ : ∀ u u', σ (O z u) (O z u') = σ u u')
    (w : V) :
    (minimalCouplingPrimitive σ (gaugeAction ℝ O A) (z, O z w)).compContinuousLinearMap
        (fderiv ℝ (fun p : E × V ↦ (p.1, O p.1 p.2)) (z, w)) =
      minimalCouplingPrimitive σ A (z, w) := by
  have hΦ (x : E × V) : fderiv ℝ (fun p : E × V ↦ (p.1, O p.1 p.2)) (z, w) x =
      (x.1, O z x.2 + fderiv ℝ O z x.1 w) := by
    simp [(((hO.hasFDerivAt.hasFDerivWithinAt (s := Set.univ)).fst_prodMk_clm_apply_snd
      (p := (z, w)) (Set.mapsTo_univ _ _)).hasFDerivAt Filter.univ_mem).fderiv]
  have hcov (v : E) (n : V) :
      O z n + fderiv ℝ O z v w + gaugeAction ℝ O A z v (O z w) = O z (n + A z v w) := by
    have hinv : (O z)⁻¹ʳ (O z w) = w := by
      rw [← mul_apply_eq_comp, Ring.inverse_mul_cancel _ hOz, one_apply_eq_self]
    simp only [gaugeAction_apply, rightMaurerCartan_apply, _root_.sub_apply, mul_apply_eq_comp,
      hinv, map_add]
    abel
  ext u
  simp only [compContinuousLinearMap_apply, minimalCouplingPrimitive_apply, Function.comp_apply, hΦ,
    hcov, hOσ]

/-- **The gauge transformation of the minimal coupling form.** Let `O` be `C²` at `z`, with values
near `z` that are invertible and preserve `σ`, and let `A` be differentiable at `z`. The bundle
map `(z, w) ↦ (z, O_z w)` pulls the minimal coupling form of the gauge transformed connection
`O·A` back to that of `A`, at every point `(z, w)` of the fibre over `z`. So minimal coupling forms
of a symplectic connection read in two symplectic trivializations correspond under the change of
trivialization. -/
theorem compContinuousLinearMap_minimalCouplingForm_gaugeAction [CompleteSpace V]
    (hO : ContDiffAt ℝ 2 O z) (hOu : ∀ᶠ z' in 𝓝 z, IsUnit (O z'))
    (hOσ : ∀ᶠ z' in 𝓝 z, ∀ u u', σ (O z' u) (O z' u') = σ u u') (hA : DifferentiableAt ℝ A z)
    (w : V) :
    (minimalCouplingForm σ ω (gaugeAction ℝ O A) (z, O z w)).compContinuousLinearMap
        (fderiv ℝ (fun p : E × V ↦ (p.1, O p.1 p.2)) (z, w)) =
      minimalCouplingForm σ ω A (z, w) := by
  set Φ : E × V → E × V := fun p ↦ (p.1, O p.1 p.2)
  have hO1 : DifferentiableAt ℝ O z := hO.differentiableAt two_ne_zero
  have hΦc : ContDiffAt ℝ 2 Φ (z, w) :=
    contDiffAt_fst.prodMk ((hO.comp (z, w) contDiffAt_fst).clm_apply contDiffAt_snd)
  -- The pulled back primitive agrees with the primitive of `A` near `(z, w)`.
  have hev : (fun q ↦ (minimalCouplingPrimitive σ (gaugeAction ℝ O A) (Φ q)).compContinuousLinearMap
      (fderiv ℝ Φ q)) =ᶠ[𝓝 (z, w)] minimalCouplingPrimitive σ A := by
    have h := (hO.eventually (by simp)).and (hOu.and hOσ)
    filter_upwards [continuousAt_fst.eventually h] with q hq
    exact compContinuousLinearMap_minimalCouplingPrimitive_gaugeAction
      (hq.1.differentiableAt two_ne_zero) hq.2.1 hq.2.2 q.2
  have hlam : DifferentiableAt ℝ (minimalCouplingPrimitive σ (gaugeAction ℝ O A)) (Φ (z, w)) :=
    differentiableAt_minimalCouplingPrimitive
      (differentiableAt_gaugeAction hO1 (hO.hasFDerivAt_fderiv le_rfl).differentiableAt
        hOu.self_of_nhds hA) _
  have hpull := extDeriv_pullback hlam hΦc (by simp)
  rw [hev.extDeriv_eq] at hpull
  ext u
  rw [compContinuousLinearMap_apply, minimalCouplingForm_apply, minimalCouplingForm_apply,
    hpull, compContinuousLinearMap_apply]
  congr 1
  congr 1
  funext i
  simp [Φ, (((hO1.hasFDerivAt.hasFDerivWithinAt (s := Set.univ)).fst_prodMk_clm_apply_snd
    (p := (z, w)) (Set.mapsTo_univ _ _)).hasFDerivAt Filter.univ_mem).fderiv]

end Gauge

end TauCeti
