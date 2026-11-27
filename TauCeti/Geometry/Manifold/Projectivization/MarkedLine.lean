/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Projectivization.MFDeriv
public import TauCeti.LinearAlgebra.Projectivization.MarkedLine
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace

/-!
# The evaluation of marked lines is transverse to `H × {p} × {q}`

A line of `ℙⁿ = ℙ 𝕜 (Fin (n + 1) → 𝕜)` with three marked points is given in homogeneous
coordinates by a linear map `A : 𝕜² → 𝕜ⁿ⁺¹`, marked at the images of `0 = [0 : 1]`, `1 = [1 : 1]`
and `∞ = [1 : 0]`. Its evaluation at the marked points is
`A ↦ ([A [0 : 1]], [A [1 : 1]], [A [1 : 0]]) ∈ ℙⁿ × ℙⁿ × ℙⁿ`. By the chain rule for maps given
in homogeneous coordinates (`Projectivization.mfderiv_eq_mfderivMk_comp`), its derivative at `A₀`
sends a variation `A` to the derivatives of the projection `w ↦ [w]` at the three values of `A₀`
along the three values of `A` (`TauCeti.markedPointsMFDeriv`,
`TauCeti.markedPointsMFDeriv_mfderiv`).

Let `H = ℙ(ker φ)` be a hyperplane and `p = [v]`, `q = [w]` two distinct points off `H`. The
marked line `A₀ = TauCeti.markedLine φ v w`, the line through `p` and `q` marked at its point
`h = [u]` on `H`, is the one marked line that the evaluation sends to `H × {p} × {q}`
(`TauCeti.existsUnique_markedLine`). This file proves that the evaluation is transverse to
`H × {p} × {q}` there, at the level of derivatives. Here `T_h H` is taken to be the image of
`ker φ` under the derivative of the projection at `u`, which models the tangent space of `H` at
`h`, `H` being the image of the punctured cone `ker φ ∖ 0`; its identification with the tangent
space of a submanifold structure on `H` is not proved here. The points `p` and `q` contribute the
zero tangent spaces, so `T_h H × 0 × 0` plays the role of the tangent space of `H × {p} × {q}`
at the image point, and:

* **Transversality**: the range of the derivative and `T_h H × 0 × 0` span the tangent space
  `T_h ℙⁿ × T_p ℙⁿ × T_q ℙⁿ` (`TauCeti.range_markedPointsMFDeriv_markedLine_sup_eq_top`);
* **the preimage is a single line**: the variations that the derivative sends into
  `T_h H × 0 × 0` are the multiples of `A₀` (`TauCeti.comap_markedPointsMFDeriv_markedLine`),
  the tangent line of the orbit of `A₀` under rescaling. These rescalings induce the same map of
  projective spaces. The intended consequence is that on the space of marked lines, where `A` is
  taken up to a nonzero scalar, the evaluation meets `H × {p} × {q}` transversally in the single
  point `[A₀]`; that quotient space and the evaluation on it are not formalized here.

Both reduce, through the kernel and the range of the derivative of the projection
(`Projectivization.ker_mfderivMk`, `Projectivization.surjective_mfderivMk`), to the linear
incidence conditions of `TauCeti.markedLineIncidence`. Over `ℂ` these linear statements are
intended to give the transversality of the evaluation map of the three-pointed lines of `ℂℙⁿ` at
the line through two points marked at its point on a hyperplane, behind the three-point count
`⟨x, xⁿ, xⁿ⟩_L = 1` of a hyperplane class and two point classes in the class `L` of a line; that
evaluation map is not formalized here. The orientation sign of this intersection point is not
treated here either.

## References

* W. Fulton and R. Pandharipande, *Notes on stable maps and quantum cohomology*,
  arXiv:alg-geom/9608011, §10, for the count of lines through two points meeting a hyperplane in
  the quantum cohomology of `ℙⁿ`.
-/

public section

namespace TauCeti

open Function Module Projectivization Submodule
open scoped Manifold Topology LinearAlgebra.Projectivization

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {n : ℕ}

/-- **The derivative of the evaluation of lines at their marked points.** At homogeneous
coordinates `A₀ : 𝕜² → 𝕜ⁿ⁺¹` of a marked line, the derivative of the evaluation
`A ↦ ([A [0 : 1]], [A [1 : 1]], [A [1 : 0]])` sends a variation `A` to the triple of tangent
vectors at `[A₀ [0 : 1]]`, `[A₀ [1 : 1]]` and `[A₀ [1 : 0]]` given by the derivative of the
projection `w ↦ [w]` along `A [0 : 1]`, `A [1 : 1]` and `A [1 : 0]`
(`TauCeti.markedPointsMFDeriv_mfderiv`). -/
noncomputable def markedPointsMFDeriv (A₀ : (Fin 2 → 𝕜) →ₗ[𝕜] Fin (n + 1) → 𝕜) :
    ((Fin 2 → 𝕜) →ₗ[𝕜] Fin (n + 1) → 𝕜) →ₗ[𝕜] (Fin n → 𝕜) × (Fin n → 𝕜) × (Fin n → 𝕜) :=
  ((mfderivMk (A₀ (Pi.single 1 1))).toLinearMap ∘ₗ LinearMap.applyₗ (Pi.single 1 1)).prod
    (((mfderivMk (A₀ 1)).toLinearMap ∘ₗ LinearMap.applyₗ 1).prod
      ((mfderivMk (A₀ (Pi.single 0 1))).toLinearMap ∘ₗ LinearMap.applyₗ (Pi.single 0 1)))

@[simp]
theorem markedPointsMFDeriv_apply (A₀ A : (Fin 2 → 𝕜) →ₗ[𝕜] Fin (n + 1) → 𝕜) :
    markedPointsMFDeriv A₀ A =
      (mfderivMk (A₀ (Pi.single 1 1)) (A (Pi.single 1 1)), mfderivMk (A₀ 1) (A 1),
        mfderivMk (A₀ (Pi.single 0 1)) (A (Pi.single 0 1))) :=
  (rfl)

/-- **`markedPointsMFDeriv` is the derivative of the evaluation.** Let `F` be a family of
homogeneous coordinates of marked lines, differentiable at `x`, and let `f₀`, `f₁`, `f₂` be maps
to `ℙⁿ` that near `x` are the evaluations `y ↦ [F y [0 : 1]]`, `[F y [1 : 1]]`, `[F y [1 : 0]]`
at the marked points `0`, `1` and `∞`.
Then their derivatives at `x` along `X` are the components of `markedPointsMFDeriv (F x)` at the
variation `dF X`. -/
theorem markedPointsMFDeriv_mfderiv {E H M : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H} [TopologicalSpace M] [ChartedSpace H M]
    {F : M → (Fin 2 → 𝕜) →L[𝕜] Fin (n + 1) → 𝕜} {f₀ f₁ f₂ : M → ℙ 𝕜 (Fin (n + 1) → 𝕜)} {x : M}
    (hF : MDifferentiableAt I 𝓘(𝕜, (Fin 2 → 𝕜) →L[𝕜] Fin (n + 1) → 𝕜) F x)
    (h₀ : ∀ᶠ y in 𝓝 x, ∃ hy : F y (Pi.single 1 1) ≠ 0, f₀ y = mk 𝕜 _ hy)
    (h₁ : ∀ᶠ y in 𝓝 x, ∃ hy : F y 1 ≠ 0, f₁ y = mk 𝕜 _ hy)
    (h₂ : ∀ᶠ y in 𝓝 x, ∃ hy : F y (Pi.single 0 1) ≠ 0, f₂ y = mk 𝕜 _ hy)
    (X : TangentSpace I x) :
    markedPointsMFDeriv (F x : (Fin 2 → 𝕜) →ₗ[𝕜] Fin (n + 1) → 𝕜)
        (ContinuousLinearMap.toLinearMap
          (mfderiv I 𝓘(𝕜, (Fin 2 → 𝕜) →L[𝕜] Fin (n + 1) → 𝕜) F x X)) =
      (mfderiv I 𝓘(𝕜, Fin n → 𝕜) f₀ x X, mfderiv I 𝓘(𝕜, Fin n → 𝕜) f₁ x X,
        mfderiv I 𝓘(𝕜, Fin n → 𝕜) f₂ x X) := by
  -- Evaluating the family at a point `t` of `𝕜²` is differentiable, with derivative the
  -- evaluation of `dF` at `t`.
  have hev (t : Fin 2 → 𝕜) : HasMFDerivAt I 𝓘(𝕜, Fin (n + 1) → 𝕜) (fun y ↦ F y t) x
      ((ContinuousLinearMap.apply 𝕜 (Fin (n + 1) → 𝕜) t).comp
        (mfderiv I 𝓘(𝕜, (Fin 2 → 𝕜) →L[𝕜] Fin (n + 1) → 𝕜) F x)) :=
    (ContinuousLinearMap.apply 𝕜 (Fin (n + 1) → 𝕜) t).hasMFDerivAt.comp x hF.hasMFDerivAt
  rw [mfderiv_eq_mfderivMk_comp (hev _).mdifferentiableAt h₀,
    mfderiv_eq_mfderivMk_comp (hev _).mdifferentiableAt h₁,
    mfderiv_eq_mfderivMk_comp (hev _).mdifferentiableAt h₂, (hev _).mfderiv, (hev _).mfderiv,
    (hev _).mfderiv]
  -- Both sides now apply the same maps; they differ only in coercing `dF X` to a linear map.
  -- The compositions cross the type synonym `TangentSpace`, which `simp` and `rw` do not unfold,
  -- so the remaining step is definitional.
  rfl

variable {φ : Dual 𝕜 (Fin (n + 1) → 𝕜)} {v w : Fin (n + 1) → 𝕜}

/-- At the marked point `1`, the derivative of the projection vanishes exactly on the line `𝕜 v`:
the marked line sends `1` to a nonzero multiple of `v`. -/
theorem ker_mfderivMk_markedLine_one (hv : φ v ≠ 0) (hw : φ w ≠ 0) :
    (mfderivMk (markedLine φ v w 1)).ker = 𝕜 ∙ v := by
  have hv₀ : v ≠ 0 := fun h ↦ hv (by simp [h])
  rw [ker_mfderivMk (by simpa [markedLine_one] using ⟨hw, hv₀⟩), markedLine_one,
    span_singleton_smul_eq hw.isUnit]

/-- At the marked point `∞`, the derivative of the projection vanishes exactly on the line `𝕜 w`:
the marked line sends `∞` to a nonzero multiple of `w`. -/
theorem ker_mfderivMk_markedLine_single_zero_one (hv : φ v ≠ 0) (hw : φ w ≠ 0) :
    (mfderivMk (markedLine φ v w (Pi.single 0 1))).ker = 𝕜 ∙ w := by
  have hw₀ : w ≠ 0 := fun h ↦ hw (by simp [h])
  rw [ker_mfderivMk (by simpa [markedLine_single_zero_one] using ⟨hv, hw₀⟩),
    markedLine_single_zero_one, span_singleton_smul_eq hv.isUnit]

/-- **The evaluation of marked lines is transverse to `H × {p} × {q}`.** At the line through
`[v]` and `[w]` marked at its point `[u]` on `ker φ`, for `v` and `w` linearly independent and off
`ker φ`, the range of the derivative of the evaluation and the tangent space
`T_[u] ℙ(ker φ) × 0 × 0` of `ℙ(ker φ) × {[v]} × {[w]}` together span the whole tangent space.
Here `T_[u] ℙ(ker φ)` is taken to be the image of `ker φ` under the derivative of the projection
at `u`. -/
theorem range_markedPointsMFDeriv_markedLine_sup_eq_top (hvw : LinearIndependent 𝕜 ![v, w])
    (hv : φ v ≠ 0) (hw : φ w ≠ 0) :
    LinearMap.range (markedPointsMFDeriv (markedLine φ v w)) ⊔
        ((LinearMap.ker φ).map (mfderivMk (markedLine φ v w (Pi.single 1 1))).toLinearMap).prod
          ⊥ = ⊤ := by
  have hne {t : Fin 2 → 𝕜} (ht : t ≠ 0) := markedLine_ne_zero hvw hv hw ht
  refine eq_top_iff'.2 fun ⟨y₀, y₁, y₂⟩ ↦ ?_
  obtain ⟨x₀, rfl⟩ := surjective_mfderivMk (hne (t := Pi.single 1 1) (by simp)) y₀
  obtain ⟨x₁, rfl⟩ := surjective_mfderivMk (hne one_ne_zero) y₁
  obtain ⟨x₂, rfl⟩ := surjective_mfderivMk (hne (t := Pi.single 0 1) (by simp)) y₂
  -- A solution `A` of the linear incidence conditions with the values of `x₀`, `x₁` and `x₂`
  -- has the right derivatives at `1` and `∞`, and at `0` it differs by a vector of `ker φ`.
  obtain ⟨A, hA⟩ := markedLineIncidence_surjective (w := w) hv
    (φ x₀, (𝕜 ∙ v).mkQ x₁, (𝕜 ∙ w).mkQ x₂)
  simp only [markedLineIncidence_apply, mkQ_apply, Prod.mk.injEq, Submodule.Quotient.eq] at hA
  obtain ⟨hA₀, hA₁, hA₂⟩ := hA
  have e₁ : mfderivMk (markedLine φ v w 1) (A 1) = mfderivMk (markedLine φ v w 1) x₁ := by
    rw [← sub_eq_zero, ← map_sub, ← ContinuousLinearMap.coe_coe, ← LinearMap.mem_ker,
      ker_mfderivMk_markedLine_one hv hw]
    exact hA₁
  have e₂ : mfderivMk (markedLine φ v w (Pi.single 0 1)) (A (Pi.single 0 1)) =
      mfderivMk (markedLine φ v w (Pi.single 0 1)) x₂ := by
    rw [← sub_eq_zero, ← map_sub, ← ContinuousLinearMap.coe_coe, ← LinearMap.mem_ker,
      ker_mfderivMk_markedLine_single_zero_one hv hw]
    exact hA₂
  refine mem_sup.2 ⟨markedPointsMFDeriv (markedLine φ v w) A, LinearMap.mem_range_self _ _,
    (mfderivMk (markedLine φ v w (Pi.single 1 1)) (x₀ - A (Pi.single 1 1)), 0, 0),
    mem_prod.2 ⟨mem_map_of_mem (by simp [hA₀]), zero_mem _⟩, ?_⟩
  simp only [markedPointsMFDeriv_apply, Prod.mk_add_mk, add_zero, e₁, e₂, map_sub,
    add_sub_cancel]

/-- **The derivative of the evaluation pulls `T_h H × 0 × 0` back to the line of the marked
line.** At the line through
`[v]` and `[w]` marked at its point `[u]` on `ker φ`, for `v` and `w` linearly independent and off
`ker φ`, the variations that the derivative of the evaluation sends into the tangent space
`T_[u] ℙ(ker φ) × 0 × 0` of `ℙ(ker φ) × {[v]} × {[w]}` are exactly the multiples of the marked
line: the directions of rescaling, which do not move the induced map of projective spaces. Here
`T_[u] ℙ(ker φ)` is taken to be the image of `ker φ` under the derivative of the projection at
`u`. -/
theorem comap_markedPointsMFDeriv_markedLine (hvw : LinearIndependent 𝕜 ![v, w]) (hv : φ v ≠ 0)
    (hw : φ w ≠ 0) :
    (((LinearMap.ker φ).map (mfderivMk (markedLine φ v w (Pi.single 1 1))).toLinearMap).prod
        ⊥).comap (markedPointsMFDeriv (markedLine φ v w)) = 𝕜 ∙ markedLine φ v w := by
  -- The marked point `0` lies on `ker φ`, so the kernel of the derivative of the projection at
  -- it, the line it spans, is contained in `ker φ`.
  have hu : (mfderivMk (markedLine φ v w (Pi.single 1 1))).toLinearMap.ker ≤ LinearMap.ker φ := by
    rw [ker_mfderivMk (markedLine_ne_zero hvw hv hw (t := Pi.single 1 1) (by simp)),
      span_singleton_le_iff_mem, LinearMap.mem_ker]
    exact apply_markedLine_single_one_one_eq_zero
  -- The three conditions of the comap are the three linear incidence conditions.
  have h₀ (z : Fin (n + 1) → 𝕜) : mfderivMk (markedLine φ v w (Pi.single 1 1)) z ∈
      (LinearMap.ker φ).map (mfderivMk (markedLine φ v w (Pi.single 1 1))).toLinearMap ↔
        φ z = 0 := by
    rw [← ContinuousLinearMap.coe_coe, ← mem_comap, comap_map_eq, sup_eq_left.2 hu,
      LinearMap.mem_ker]
  have h₁ (z : Fin (n + 1) → 𝕜) : mfderivMk (markedLine φ v w 1) z = 0 ↔ z ∈ 𝕜 ∙ v := by
    rw [← ContinuousLinearMap.coe_coe, ← LinearMap.mem_ker, ker_mfderivMk_markedLine_one hv hw]
  have h₂ (z : Fin (n + 1) → 𝕜) :
      mfderivMk (markedLine φ v w (Pi.single 0 1)) z = 0 ↔ z ∈ 𝕜 ∙ w := by
    rw [← ContinuousLinearMap.coe_coe, ← LinearMap.mem_ker,
      ker_mfderivMk_markedLine_single_zero_one hv hw]
  ext A
  rw [← ker_markedLineIncidence hv, mem_ker_markedLineIncidence_iff]
  simp only [mem_comap, markedPointsMFDeriv_apply, mem_prod, mem_bot, Prod.mk_eq_zero]
  exact and_congr (h₀ _) (and_congr (h₁ _) (h₂ _))

end TauCeti
