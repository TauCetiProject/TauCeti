/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.LeviCivita.Nondegenerate.Basic
import TauCeti.Analysis.Calculus.ContinuousLinearMapInverse
import TauCeti.Analysis.Calculus.FDeriv.ContinuousLinearMap
import TauCeti.Geometry.Manifold.VectorBundle.Bilinear.Family
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.LeviCivita.KoszulVariation
import TauCeti.Geometry.Manifold.VectorBundle.NondegenerateMetric.Musical

/-!
# The first variation of the Levi-Civita connection

Let `g_s` be a one-parameter family of smooth nondegenerate metrics on `M`, of any signature,
jointly `C²` in `(s, x)` as a map into the bundle of bilinear forms on `TM`, and let `∇ˢ` be a
Levi-Civita connection of `g_s` for each `s`. Write `h = ∂ₛ g_s` for the parameter derivative at
`s = t`, a symmetric field of bilinear forms. This file proves that for a vector field `Y` which is
differentiable at `x`, the curve `s ↦ ∇ˢ_v Y` in `T_x M` is differentiable at `t`, and that its
derivative `(∂ₜ∇)_v Y` satisfies the **first variation formula**

`2 g_t((∂ₜ∇)_v Y, w) = (∇ᵗ_v h)(Y, w) + (∇ᵗ_Y h)(v, w) - (∇ᵗ_w h)(v, Y)`,

where `∇ᵗh` is the covariant derivative `CovariantDerivative.derivBilinearTensor` of `h`. In index
notation this is the classical variation `∂ₜΓ^k_ij = ½ g^kl (∇_i h_jl + ∇_j h_il - ∇_l h_ij)` of the
Christoffel symbols. A family of metrics over a parameter manifold is varied along a parameter curve
by applying these results to the restricted family.

The proof differentiates the Koszul formula `2 g_s(∇ˢ_X Y, Z) = K_{g_s}(X, Y, Z)` in `s`. The
parameter derivative of the Koszul expression is the Koszul expression of `h`
(`TauCeti.Manifold.hasDerivAt_koszulBilinear`, in
`TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.LeviCivita.KoszulVariation`).
Differentiability of `s ↦ ∇ˢ_v Y` comes from writing it as `g_s⁻¹` applied to half the Koszul
covector, and the identity
`TauCeti.Manifold.koszulBilinear_sub_two_mul_apply_eq_derivBilinearTensor` turns
`K_h(v, Y, w) - 2 h(∇ᵗ_v Y, w)` into the right-hand side. No positivity is used. Since the
difference `∇ˢ - ∇ᵗ` is tensorial, `s ↦ ∇ˢ_v Y` differs by a constant from the same curve for any
smooth extension of `Y x`, so only differentiability of `Y` at `x` is needed.

## Main results

* `TauCeti.Manifold.differentiableAt_covariantDerivative_apply_of_isLeviCivitaConnection`: a
  family of Levi-Civita connections of a jointly `C²` family of nondegenerate metrics varies
  differentiably.
* `TauCeti.Manifold.two_mul_apply_deriv_eq_derivBilinearTensor_of_isLeviCivitaConnection`: the
  first variation formula for the Levi-Civita connection.

## References

* A. L. Besse, *Einstein Manifolds*, Springer (1987), Section 1.K, Theorem 1.174.
* B. Chow and D. Knopf, *The Ricci Flow: An Introduction*, AMS (2004), Chapter 3, Lemma 3.2.
* B. O'Neill, *Semi-Riemannian Geometry with Applications to Relativity*, Academic Press, 1983,
  Ch. 3, Thm. 11: the Koszul formula for nondegenerate metrics.
-/

public section

noncomputable section

open Bundle FiberBundle Filter VectorField
open scoped ContDiff Manifold Topology

namespace TauCeti.Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {h : (x : M) → TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ} {t : ℝ} {x : M}

variable [IsManifold I ∞ M]

section FiniteDimensional

variable [FiniteDimensional ℝ E]

/-! ### Families of Levi-Civita connections -/

variable {g : ℝ → ContMDiffNondegenerateMetric (I := I) (M := M)}
  {cov : ℝ → CovariantDerivative I E (fun x : M ↦ TangentSpace I x)}
  {Y : Π x : M, TangentSpace I x}

/-- In a family of Levi-Civita connections of a family of nondegenerate metrics, the pairing
`2 g_s(∇ˢ_v Y, w)` is the Koszul expression of `g_s` on extensions of `v` and `w`. -/
private theorem two_mul_apply_eq_koszulBilinear_extend
    (hcov : ∀ s, (g s).IsLeviCivitaConnection (cov s)) (hY : MDiffAt (T% Y) x)
    (s : ℝ) (v w : TangentSpace I x) :
    2 * g s x (cov s Y x v) w = koszulBilinear I (g s) (extend E v) Y (extend E w) x := by
  have h := (hcov s).two_apply_eq_koszul (mdifferentiableAt_extend I E v) hY
    (mdifferentiableAt_extend I E w)
  rw [ContMDiffNondegenerateMetric.koszul_apply, ← koszulBilinear_apply] at h
  simpa using h

/-- The curve `s ↦ ∇ˢ_v Y` differs by a constant from the curve `s ↦ ∇ˢ_v Y₀` for the extension
`Y₀` of `Y x`: the difference `∇ˢ - ∇ᵗ` is tensorial, so `∇ˢ_v Y - ∇ᵗ_v Y` depends on `Y` only
through `Y x`. -/
private theorem apply_eq_apply_extend_add (hY : MDiffAt (T% Y) x) (s : ℝ) (v : TangentSpace I x) :
    cov s Y x v = cov s (extend E (Y x)) x v + (cov t Y x v - cov t (extend E (Y x)) x v) := by
  have hd {Z : Π x : M, TangentSpace I x} (hZ : MDiffAt (T% Z) x) :=
    IsCovariantDerivativeOn.difference_apply (cov s).isCovariantDerivativeOnUniv
      (cov t).isCovariantDerivativeOnUniv (Set.mem_univ x) hZ
  have h := (hd hY).symm.trans (extend_apply_self (F := E) (Y x) ▸ hd
    (mdifferentiableAt_extend I E (Y x)))
  have h' := congr($h v)
  simp only [sub_apply] at h'
  rw [← sub_add_cancel (cov s Y x v) (cov t Y x v), h']
  abel

/-- Levi-Civita connections vary differentiably with the metric, for vector fields `C²` at `x`. -/
private theorem differentiableAt_covariantDerivative_apply_of_contMDiffAt
    (hcov : ∀ s, (g s).IsLeviCivitaConnection (cov s))
    (hg : ContMDiffAt (𝓘(ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) 2
      (fun q : ℝ × M ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun y : M ↦ TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ) q.2 (g q.1 q.2))
      (t, x))
    (hY : CMDiffAt 2 (T% Y) x) (v : TangentSpace I x) :
    DifferentiableAt ℝ (fun s ↦ cov s Y x v) t := by
  -- The metrics at `x`, as a curve of bilinear forms on the model space.
  set G : ℝ → E →L[ℝ] E →L[ℝ] ℝ := fun s ↦ g s x
  have hG : DifferentiableAt ℝ G t := differentiableAt_clm_apply₂.mpr
    (differentiableAt_apply_apply_of_contMDiffAt (b := fun s ↦ g s) (by norm_num) hg)
  -- The covectors `g_s(∇ˢ_v Y, ·)`, which are half the Koszul expressions.
  have hφ : DifferentiableAt ℝ (fun s ↦ G s (cov s Y x v)) t := by
    refine differentiableAt_clm_apply.mpr fun c ↦ ?_
    have hK := (differentiableAt_koszulBilinear (b := fun s ↦ g s) hg (contMDiffAt_extend I E v) hY
      (contMDiffAt_extend I E c)).const_mul (1 / 2 : ℝ)
    refine hK.congr_of_eventuallyEq (Eventually.of_forall fun s ↦ ?_)
    have := two_mul_apply_eq_koszulBilinear_extend hcov (hY.mdifferentiableAt two_ne_zero) s v c
    dsimp only
    rw [← this, one_div, inv_mul_cancel_left₀ two_ne_zero]
    -- `G s` is `g s x` with the tangent space at `x` read as the model space.
    rfl
  have hinv := (DifferentiableAt.clm_inverse_of_completeSpace hG
    ((g t).isInvertible x)).clm_apply hφ
  refine hinv.congr_of_eventuallyEq (Eventually.of_forall fun s ↦ ?_)
  exact (((g s).isInvertible x).inverse_apply_self _).symm

/-- The first variation of the Levi-Civita connection, for vector fields `C²` at `x`. -/
private theorem two_mul_apply_deriv_eq_of_contMDiffAt
    (hcov : ∀ s, (g s).IsLeviCivitaConnection (cov s))
    (hg : ContMDiffAt (𝓘(ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) 2
      (fun q : ℝ × M ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun y : M ↦ TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ) q.2 (g q.1 q.2))
      (t, x))
    (hh : ∀ y v w, HasDerivAt (fun s ↦ g s y v w) (h y v w) t)
    (hY : CMDiffAt 2 (T% Y) x) (v w : TangentSpace I x) :
    2 * g t x (deriv (fun s ↦ cov s Y x v) t) w =
      (cov t).derivBilinearTensor h x (Y x) w v + (cov t).derivBilinearTensor h x v w (Y x) -
        (cov t).derivBilinearTensor h x v (Y x) w := by
  -- The curve `s ↦ ∇ˢ_v Y` and the metrics at `x`, read in the model space.
  set u : ℝ → E := fun s ↦ cov s Y x v
  have hu' : DifferentiableAt ℝ u t :=
    differentiableAt_covariantDerivative_apply_of_contMDiffAt hcov hg hY v
  have hu : HasDerivAt u (deriv u t) t := hu'.hasDerivAt
  set G : ℝ → E →L[ℝ] E →L[ℝ] ℝ := fun s ↦ g s x
  have hG : HasDerivAt G (h x) t := hasDerivAt_clm_apply₂.mpr (hh x)
  -- Differentiate `2 g_s(∇ˢ_v Y, w)` directly ...
  have hleft : HasDerivAt (fun s ↦ 2 * g s x (cov s Y x v) w)
      (2 * (h x (cov t Y x v) w + g t x (deriv u t) w)) t := by
    have := ((hG.clm_apply hu).clm_apply
      (hasDerivAt_const (x := t) (c := tangentSpaceCastModel I x w))).const_mul 2
    simp only [map_zero, add_zero, add_apply] at this
    -- `G s`, `u s` and `tangentSpaceCastModel I x w` are `g s x`, `∇ˢ_v Y` and `w`.
    exact this
  -- ... and as the Koszul expression of `g_s`, whose derivative is that of `h`.
  have hright := hasDerivAt_koszulBilinear (b := fun s ↦ g s) hg (Eventually.of_forall hh)
    (contMDiffAt_extend I E v) hY (contMDiffAt_extend I E w)
  have hK := hleft.unique (hright.congr_of_eventuallyEq (Eventually.of_forall fun s ↦
    two_mul_apply_eq_koszulBilinear_extend hcov (hY.mdifferentiableAt two_ne_zero) s v w))
  -- Rewrite the Koszul expression of the symmetric field `h` along the torsion-free `∇ᵗ`.
  have hsymm (y : M) (a c : TangentSpace I y) : h y a c = h y c a :=
    (hh y a c).unique ((hh y c a).congr_of_eventuallyEq
      (Eventually.of_forall fun s ↦ (g s).apply_comm y a c))
  have hid := koszulBilinear_sub_two_mul_apply_eq_derivBilinearTensor (hcov t).torsion hsymm
    (fun _ _ ↦ mdifferentiableAt_apply_apply_of_hasDerivAt_family (b := fun s ↦ g s) hg
      (Eventually.of_forall hh))
    (mdifferentiableAt_extend I E v) (hY.mdifferentiableAt two_ne_zero)
    (mdifferentiableAt_extend I E w)
  simp only [extend_apply_self] at hid
  have key : 2 * g t x (deriv u t) w =
      (cov t).derivBilinearTensor h x (Y x) w v + (cov t).derivBilinearTensor h x v w (Y x) -
        (cov t).derivBilinearTensor h x v (Y x) w := by
    linarith
  -- The derivative of `u` is that of `s ↦ ∇ˢ_v Y`, with the tangent space read as `E`.
  exact key

/-- For a vector field `Y` differentiable at `x`, the curve `s ↦ ∇ˢ_v Y` has the same derivative at
`t` as the curve `s ↦ ∇ˢ_v Y₀` for the extension `Y₀` of `Y x`. -/
private theorem hasDerivAt_apply_of_extend
    (hcov : ∀ s, (g s).IsLeviCivitaConnection (cov s))
    (hg : ContMDiffAt (𝓘(ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) 2
      (fun q : ℝ × M ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun y : M ↦ TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ) q.2 (g q.1 q.2))
      (t, x))
    (hY : MDiffAt (T% Y) x) (v : TangentSpace I x) :
    HasDerivAt (fun s ↦ cov s Y x v) (deriv (fun s ↦ cov s (extend E (Y x)) x v) t) t := by
  -- `s ↦ ∇ˢ_v Y` and `s ↦ ∇ˢ_v Y₀` for the extension `Y₀` of `Y x` differ by a constant.
  set u : ℝ → E := fun s ↦ cov s (extend E (Y x)) x v
  set c : E := cov t Y x v - cov t (extend E (Y x)) x v
  have hu : DifferentiableAt ℝ u t := differentiableAt_covariantDerivative_apply_of_contMDiffAt
    hcov hg (contMDiffAt_extend I E (Y x)) v
  -- Elaborated without the goal as expected type, so that `u` fixes the codomain as `E`.
  have h := (hu.hasDerivAt.add_const c).congr_of_eventuallyEq
    (Eventually.of_forall fun s ↦ apply_eq_apply_extend_add hY s v)
  exact h

/-- **Levi-Civita connections vary differentiably with the metric.** Let `g_s` be a family of
smooth nondegenerate metrics, jointly `C²` in `(s, y)` at `(t, x)`, and let `∇ˢ` be a Levi-Civita
connection of `g_s` for every `s`. Then for every vector field `Y` which is differentiable at `x`
and every `v ∈ T_x M`, the curve `s ↦ ∇ˢ_v Y` in `T_x M` is differentiable at `t`. -/
theorem differentiableAt_covariantDerivative_apply_of_isLeviCivitaConnection
    (hcov : ∀ s, (g s).IsLeviCivitaConnection (cov s))
    (hg : ContMDiffAt (𝓘(ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) 2
      (fun q : ℝ × M ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun y : M ↦ TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ) q.2 (g q.1 q.2))
      (t, x))
    (hY : MDiffAt (T% Y) x) (v : TangentSpace I x) :
    DifferentiableAt ℝ (fun s ↦ cov s Y x v) t :=
  -- The tangent space at `x` is read as the normed space `E`.
  HasDerivAt.differentiableAt (F := E) (hasDerivAt_apply_of_extend hcov hg hY v)

/-- **The first variation of the Levi-Civita connection.** Let `g_s` be a family of smooth
nondegenerate metrics, jointly `C²` in `(s, y)` at `(t, x)`, with parameter derivative
`h = ∂ₛ g_s` at `s = t`, and let `∇ˢ` be a Levi-Civita connection of `g_s` for every `s`. Then for
every vector field `Y` which is differentiable at `x` and all `v, w ∈ T_x M`,

`2 g_t((∂ₜ∇)_v Y, w) = (∇ᵗ_v h)(Y, w) + (∇ᵗ_Y h)(v, w) - (∇ᵗ_w h)(v, Y)`,

where `(∂ₜ∇)_v Y` is the derivative at `t` of `s ↦ ∇ˢ_v Y` and `∇ᵗh` is the covariant derivative
`CovariantDerivative.derivBilinearTensor` of `h` along `∇ᵗ`. -/
theorem two_mul_apply_deriv_eq_derivBilinearTensor_of_isLeviCivitaConnection
    (hcov : ∀ s, (g s).IsLeviCivitaConnection (cov s))
    (hg : ContMDiffAt (𝓘(ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) 2
      (fun q : ℝ × M ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun y : M ↦ TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ) q.2 (g q.1 q.2))
      (t, x))
    (hh : ∀ y v w, HasDerivAt (fun s ↦ g s y v w) (h y v w) t)
    (hY : MDiffAt (T% Y) x) (v w : TangentSpace I x) :
    2 * g t x (deriv (fun s ↦ cov s Y x v) t) w =
      (cov t).derivBilinearTensor h x (Y x) w v + (cov t).derivBilinearTensor h x v w (Y x) -
        (cov t).derivBilinearTensor h x v (Y x) w := by
  have hderiv : deriv (fun s ↦ cov s Y x v) t = deriv (fun s ↦ cov s (extend E (Y x)) x v) t :=
    HasDerivAt.deriv (F := E) (hasDerivAt_apply_of_extend hcov hg hY v)
  rw [hderiv]
  simpa only [extend_apply_self] using
    two_mul_apply_deriv_eq_of_contMDiffAt hcov hg hh (contMDiffAt_extend I E (Y x)) v w

end FiniteDimensional

end TauCeti.Manifold
