/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.Normed.Module.HahnBanach

/-!
# Lions' representation theorem

Lax–Milgram solves `B u v = ℓ v` when the bilinear form `B` is defined and coercive on a single
Hilbert space. **Lions' representation theorem** is the version in which the solution and the
test vectors live in different spaces: the solution `u` is sought in a Hilbert space `H`, while
the test vectors `φ` range over a vector space `Φ`, which need carry no topology, that is
mapped into `H` by `j`. The form `E φ u` must be continuous in `u` for each fixed `φ`, and
coercive on the diagonal, `c p(φ)² ≤ E φ (j φ)`, for a function `p : Φ → ℝ` dominating
`‖j φ‖` (in applications, a norm on `Φ`). Then every functional `ℓ` on `Φ` bounded by `p` is
represented: there is `u ∈ H` with `E φ u = ℓ φ` for every `φ`.

Unlike Lax–Milgram, the theorem gives no uniqueness, and it needs neither continuity of `E` in
`φ` nor completeness of the test space. This is what makes it applicable to evolution equations.
For `u' + A(t) u = f` with `u(0) = u₀` in a Gelfand triple `V ↪ H ↪ V*`, one takes `L²(0, T; V)`
for the Hilbert space and the `C¹` functions `φ : ℝ → V` with `φ(T) = 0` for the test space,
with `E φ u = ∫ (A(t) u φ - ⟪u, φ'⟫)`: integrating by parts,
`E φ φ = ½ ‖φ(0)‖² + ∫ A(t) φ φ` is coercive for `p φ = (‖φ‖²_{L²(V)} + ‖φ(0)‖²)^{1/2}`, which
also bounds the right-hand side `ℓ φ = ∫ f φ + ⟪u₀, φ(0)⟫`
(`TauCeti.exists_memLp_forall_setIntegral_eq_add_inner`).

## The proof

By the Fréchet–Riesz theorem, `E φ u = ⟪T φ, u⟫` for a linear map `T : Φ → H`. Coercivity and
Cauchy–Schwarz give `c p(φ)² ≤ ⟪T φ, j φ⟫ ≤ ‖T φ‖ p(φ)`, so `c p(φ) ≤ ‖T φ‖`, and therefore
`|ℓ φ| ≤ (M / c) ‖T φ‖`. In particular `ℓ` vanishes on the kernel of `T`, so `T φ ↦ ℓ φ` is a
well-defined functional on the range of `T`, of norm at most `M / c`. Its Hahn–Banach
extension to `H` is represented, again by Fréchet–Riesz, by the vector `u` sought.

## Main declarations

* `LinearMap.exists_forall_apply_eq_and_norm_le_of_coercive`: Lions' representation theorem,
  with the bound `‖u‖ ≤ M / c` on the solution.

## References

* J.-L. Lions, *Équations différentielles opérationnelles et problèmes aux limites*,
  Grundlehren **111**, Springer, 1961.
* R. E. Showalter, *Monotone Operators in Banach Space and Nonlinear Partial Differential
  Equations*, Mathematical Surveys and Monographs **49**, AMS, 1997, Chapter III, Section 2.
-/

public section

open scoped InnerProductSpace

namespace LinearMap

variable {Φ H : Type*} [AddCommGroup Φ] [Module ℝ Φ] [NormedAddCommGroup H]
  [InnerProductSpace ℝ H] [CompleteSpace H]

/-- **Lions' representation theorem.** Let `H` be a real Hilbert space, `Φ` a real vector space
with a map `j : Φ → H` and a function `p : Φ → ℝ` dominating it, `‖j φ‖ ≤ p φ`, and let `E` assign
to each `φ ∈ Φ` a continuous linear functional on `H` that is coercive on the diagonal,
`c p(φ)² ≤ E φ (j φ)` with `c > 0`. Then every linear functional `ℓ` on `Φ` with
`|ℓ φ| ≤ M p(φ)` is represented by some `u ∈ H`, in the sense that `E φ u = ℓ φ` for every
`φ ∈ Φ`, and `u` can be chosen with `‖u‖ ≤ M / c`.

No continuity of `E` in `φ`, completeness of `Φ` or uniqueness of `u` is claimed; the test space
`Φ` carries no topology at all. -/
theorem exists_forall_apply_eq_and_norm_le_of_coercive (E : Φ →ₗ[ℝ] StrongDual ℝ H) (j : Φ → H)
    (p : Φ → ℝ) (ℓ : Φ →ₗ[ℝ] ℝ) {c M : ℝ} (hc : 0 < c) (hM : 0 ≤ M)
    (hE : ∀ φ, c * p φ ^ 2 ≤ E φ (j φ)) (hj : ∀ φ, ‖j φ‖ ≤ p φ)
    (hℓ : ∀ φ, |ℓ φ| ≤ M * p φ) :
    ∃ u : H, (∀ φ, E φ u = ℓ φ) ∧ ‖u‖ ≤ M / c := by
  -- The Fréchet–Riesz representatives of the functionals `E φ`.
  let T : Φ →ₗ[ℝ] H :=
    { toFun := fun φ => (InnerProductSpace.toDual ℝ H).symm (E φ)
      map_add' := fun φ ψ => by simp
      map_smul' := fun r φ => by simp }
  have hT : ∀ φ x, ⟪T φ, x⟫_ℝ = E φ x := fun φ x => InnerProductSpace.toDual_symm_apply
  -- Coercivity and Cauchy–Schwarz bound `ℓ` by the norm of `T`.
  have hbound : ∀ φ, |ℓ φ| ≤ M / c * ‖T φ‖ := by
    intro φ
    refine (hℓ φ).trans ?_
    rcases le_or_gt (p φ) 0 with hp | hp
    · exact (mul_nonpos_of_nonneg_of_nonpos hM hp).trans (by positivity)
    · have hpT : c * p φ ^ 2 ≤ ‖T φ‖ * p φ :=
        calc c * p φ ^ 2 ≤ E φ (j φ) := hE φ
          _ = ⟪T φ, j φ⟫_ℝ := (hT φ (j φ)).symm
          _ ≤ ‖T φ‖ * ‖j φ‖ := real_inner_le_norm _ _
          _ ≤ ‖T φ‖ * p φ := by gcongr; exact hj φ
      have hcp : c * p φ ≤ ‖T φ‖ := by nlinarith
      rw [div_mul_eq_mul_div, le_div_iff₀ hc]
      nlinarith
  -- Hence `T φ ↦ ℓ φ` is a well-defined bounded functional on the range of `T`.
  have hker : ker T ≤ ker ℓ := fun φ hφ => by
    have h := hbound φ
    rw [mem_ker.mp hφ, norm_zero, mul_zero] at h
    exact mem_ker.mpr (abs_nonpos_iff.mp h)
  let g₀ : range T →ₗ[ℝ] ℝ := ((ker T).liftQ ℓ hker).comp T.quotKerEquivRange.symm.toLinearMap
  have hg₀ : ∀ φ, g₀ ⟨T φ, mem_range_self T φ⟩ = ℓ φ := fun φ => by simp [g₀]
  let g : StrongDual ℝ (range T) := g₀.mkContinuous (M / c) fun y => by
    obtain ⟨_, φ, rfl⟩ := y
    rw [hg₀ φ, Real.norm_eq_abs, ← Submodule.norm_coe]
    exact hbound φ
  -- Its Hahn–Banach extension is represented by the solution.
  obtain ⟨G, hG, hGn⟩ := exists_extension_norm_eq (range T) g
  refine ⟨(InnerProductSpace.toDual ℝ H).symm G, fun φ => ?_, ?_⟩
  · rw [← hT, real_inner_comm, InnerProductSpace.toDual_symm_apply]
    simpa [g, hg₀] using hG ⟨T φ, mem_range_self T φ⟩
  · rw [LinearIsometryEquiv.norm_map, hGn]
    exact mkContinuous_norm_le _ (by positivity) _

end LinearMap
