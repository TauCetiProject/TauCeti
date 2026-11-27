/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.ZLattice.Basic
public import Mathlib.Analysis.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-!
# Unitary characters of a full lattice

Let `L` be a full lattice in a finite-dimensional real normed space `E`. Every unitary character
`ψ : L → S¹` is the restriction of a character of `E` of the form `x ↦ exp (i ℓ(x))`, for a
real-linear form `ℓ` on `E`
(`AddChar.exists_continuousLinearMap_forall_apply_eq_circleExp`): choose a `ℤ`-basis of `L`,
which is also an `ℝ`-basis of `E`, pick an argument of `ψ` on each basis vector, and extend these
arguments linearly.

For a lattice `L` in `ℂ`, the character `ψ` is the holonomy of a flat unitary line over the torus
`ℂ / L`, and `ℓ` is a constant flat connection form `d + i ℓ` on the trivial line with the same
holonomy. So every flat unitary line over a torus is topologically trivial.
-/

public section

open Module

/-- **Unitary characters of a full lattice are exponentials of linear forms.** For a full lattice
`L` in a finite-dimensional real normed space `E`, every unitary character `ψ` of `L` is
`γ ↦ exp (i ℓ(γ))` for some real-linear form `ℓ` on `E`. -/
theorem AddChar.exists_continuousLinearMap_forall_apply_eq_circleExp {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] {L : Submodule ℤ E}
    [DiscreteTopology L] [IsZLattice ℝ L] (ψ : AddChar L Circle) :
    ∃ ℓ : E →L[ℝ] ℝ, ∀ γ : L, ψ γ = Circle.exp (ℓ γ) := by
  have := ZLattice.module_free ℝ L
  let b := Free.chooseBasis ℤ L
  let B := b.ofZLatticeBasis ℝ L
  choose θ hθ using fun i ↦ Circle.exp_surjective (ψ (b i))
  refine ⟨LinearMap.toContinuousLinearMap (B.constr ℝ θ), fun γ ↦ ?_⟩
  -- The two characters, as `ℤ`-linear maps into `Additive Circle`, agree on the basis `b`.
  have key : ψ.toAddMonoidHom.toIntLinearMap =
      (Circle.expHom.comp ((B.constr ℝ θ).toAddMonoidHom.comp
        L.subtype.toAddMonoidHom)).toIntLinearMap :=
    b.ext fun i ↦ by
      have h : B.constr ℝ θ (b i) = θ i := by
        rw [← Basis.ofZLatticeBasis_apply ℝ L b i, Basis.constr_basis]
      simp [h, hθ]
  -- Evaluate both sides at `γ` and unfold the wrappers through their `simp` API.
  simpa only [AddMonoidHom.coe_toIntLinearMap, AddChar.toAddMonoidHom_apply,
    AddMonoidHom.coe_comp, Function.comp_apply, Circle.expHom_apply, LinearMap.toAddMonoidHom_coe,
    Submodule.subtype_apply, toMul_ofMul, LinearMap.coe_toContinuousLinearMap'] using
    congr(Additive.toMul ($key γ))
