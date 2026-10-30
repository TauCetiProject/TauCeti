/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Wedge.Leibniz

/-!
# Multiplying a differential form by a function

The wedge of the `0`-form of a real function `f` with a real form `φ` of degree `l` is the
pointwise product `f • φ`, once the degree `0 + l` of the wedge is identified with `l`
(`TauCeti.RoughForm.ofFunction_wedge_apply`). The Leibniz rule for the wedge therefore gives the
Leibniz rule for the product of a form by a function:

`d (f • φ) = df ∧ φ + f • dφ`

(`TauCeti.mextDeriv_fun_smul_apply`). The degree `1 + l` of `df ∧ φ` is identified with
`l + 1` by `Fin.cast`.

## References

* John M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Proposition 14.23.
-/

public section

noncomputable section

open Bundle
open scoped Manifold

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] {l : ℕ}

/-- **Leibniz rule for the product of a form by a function**: for a function `f` and a real
form `φ` of degree `l`, both differentiable at `x`, `d (f • φ) = df ∧ φ + f • dφ` at `x`.
The degree `1 + l` of `df ∧ φ` is identified with `l + 1` by `Fin.cast`. -/
theorem mextDeriv_fun_smul_apply [IsManifold I 1 M] {f : M → ℝ} {φ : RoughForm I M ℝ l} {x : M}
    (hf : MDifferentiableAt I 𝓘(ℝ, ℝ) f x)
    (hφ : MDifferentiableAt I (I.prod 𝓘(ℝ, E [⋀^Fin l]→L[ℝ] ℝ))
      (fun y ↦ TotalSpace.mk' (E [⋀^Fin l]→L[ℝ] ℝ) y (φ y)) x)
    (v : Fin (l + 1) → TangentSpace I x) :
    mextDeriv (fun y ↦ f y • φ y) x v =
      (mextDeriv (RoughForm.ofFunction I f)).wedge φ x
          (v ∘ Fin.cast (Nat.add_comm 1 l)) +
        f x • mextDeriv φ x v := by
  -- Express the zero-form section as `f` times the smooth constant unit zero-form.
  let unitForm : SmoothForm I M ℝ 0 :=
    ⟨RoughForm.ofFunction I (fun _ ↦ 1),
      (isSmoothForm_ofFunction_iff.mpr contMDiff_const).mem_smoothForms⟩
  have hf' : MDifferentiableAt I (I.prod 𝓘(ℝ, E [⋀^Fin 0]→L[ℝ] ℝ))
      (fun y ↦ TotalSpace.mk' (E [⋀^Fin 0]→L[ℝ] ℝ) y (RoughForm.ofFunction I f y)) x := by
    convert hf.smul_section (unitForm.mdifferentiableAt x) using 1
    funext y
    congr 1
    ext w
    simp [unitForm]
  -- Identify `f • φ` with the wedge of the `0`-form of `f` with `φ`, across `0 + l = l`.
  have key : ∀ (n : ℕ) (h : 0 + l = n) (ψ : RoughForm I M ℝ n),
      (∀ y w, ψ y w = (RoughForm.ofFunction I f).wedge φ y (w ∘ Fin.cast h)) →
      ∀ w : Fin (n + 1) → TangentSpace I x, mextDeriv ψ x w =
        mextDeriv ((RoughForm.ofFunction I f).wedge φ) x (w ∘ Fin.cast (by omega)) := by
    intro n h ψ hψ w
    subst h
    have : ψ = (RoughForm.ofFunction I f).wedge φ := by
      funext y
      exact ContinuousAlternatingMap.ext fun w ↦ by simpa using hψ y w
    subst this
    simp
  have hsmul : ∀ y (w : Fin l → TangentSpace I y), (fun y ↦ f y • φ y) y w =
      (RoughForm.ofFunction I f).wedge φ y (w ∘ Fin.cast (Nat.zero_add l)) := fun y w ↦ by
    rw [RoughForm.ofFunction_wedge_apply]
    simp [Function.comp_def]
  rw [key l (Nat.zero_add l) _ hsmul v,
    mextDeriv_wedge hf' hφ]
  simp only [pow_zero, RoughForm.ofFunction_wedge_apply, smul_eq_mul]
  simp [Function.comp_def]

end TauCeti
