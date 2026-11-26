/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.Module.Alternating.HermitianForm
public import TauCeti.Geometry.Manifold.Complex.AlmostComplexStructure
public import TauCeti.Geometry.Symplectic.Manifold.TwoForm

/-!
# The Hermitian form of a real two-form on a complex manifold

Let `X` be a complex manifold modelled on `𝓘(ℂ, E)`, so that every tangent space is `E` and
multiplication by `i` is its almost complex structure `J`. For a real two-form `α` on the
underlying real manifold, `TauCeti.twoFormHermitianForm E α x` is the Hermitian form
`H_α(u, v) = α(u, J v) + i·α(u, v)` of `α` at `x` (`ContinuousAlternatingMap.hermitianForm`).
When `α(x)` has type (1,1) it is a Hermitian sesquilinear form (`TauCeti.twoFormSesqForm`). For a
Hermitian metric `ω`, a smooth two-form compatible with `J`, it is the Hermitian inner product of
`ω`: it is Hermitian since `ω` is invariant under `J`, and positive definite since `ω` tames `J`.

## Main definitions

* `TauCeti.twoFormHermitianForm E α x`: the Hermitian form `H_α` of a real two-form at `x`.
* `TauCeti.twoFormSesqForm`: the same form as a sesquilinear form, when `α` has type (1,1) at `x`.

## Main results

* `TauCeti.twoFormHermitianForm_add` and its companions: `H_α` is real linear in `α`.
* `TauCeti.isSymm_twoFormSesqForm`: `H_α(x)` is Hermitian when `α(x)` has type (1,1).
* `TauCeti.SmoothTwoForm.Invariant.isSymm_twoFormSesqForm` and
  `TauCeti.SmoothTwoForm.Tames.re_twoFormHermitianForm_apply_self_pos`: for a two-form `ω`
  invariant under, respectively taming, multiplication by `i`, `H_ω(x)` is Hermitian,
  respectively positive definite, and
  `TauCeti.SmoothTwoForm.Compatible.re_twoFormSesqForm_apply_self_pos`: for a Hermitian metric the
  sesquilinear form is positive definite.

`TauCeti.SymplecticForm.complexAssociatedForm_eq_hermitianForm`, in
`TauCeti.Geometry.Symplectic.Hermitian`, identifies `H_α` with the complex associated form of a
symplectic form agreeing with `α`, for `J` multiplication by `i`. Continuity of `H_α` for a
continuous `α`, read in a chart, is
`TauCeti.IsSmoothForm.tendsto_twoFormHermitianForm_tangentCoordChange`, in
`TauCeti.Geometry.Manifold.Complex.TwoFormHermitianForm.Continuity`.
-/

public section

open Complex Module
open scoped ContDiff Manifold TauCeti.ComplexManifold

noncomputable section

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {X : Type*} [TopologicalSpace X] [ChartedSpace E X]

section Forms

variable {α : RoughForm 𝓘(ℝ, E) X ℝ 2} {x : X}

variable (E) in
/-- The Hermitian form `H_α(u, v) = α(u, J v) + i·α(u, v)` of a real two-form `α` at `x`, where
`J` is multiplication by `i` on the tangent space `E`. It is complex linear in the second slot; it
is conjugate linear in the first slot, and Hermitian, when `α(x)` has type (1,1); for a Hermitian
metric `ω` it is the Hermitian inner product `h`. -/
def twoFormHermitianForm (α : RoughForm 𝓘(ℝ, E) X ℝ 2) (x : X) (u v : E) : ℂ :=
  ContinuousAlternatingMap.hermitianForm (E := E) (α x) u v

/-- Unfolding lemma for `twoFormHermitianForm`. -/
theorem twoFormHermitianForm_def (u v : E) :
    twoFormHermitianForm E α x u v = ⟨α x ![u, I • v], α x ![u, v]⟩ :=
  ContinuousAlternatingMap.hermitianForm_def (E := E) (α x) u v

/-- `twoFormHermitianForm E α x` is the Hermitian form of the two-form `α x`. -/
theorem twoFormHermitianForm_eq_hermitianForm :
    twoFormHermitianForm E α x = ContinuousAlternatingMap.hermitianForm (E := E) (α x) :=
  (rfl)

/-- The Hermitian form of the zero two-form vanishes. -/
@[simp]
theorem twoFormHermitianForm_zero (u v : E) :
    twoFormHermitianForm E (0 : RoughForm 𝓘(ℝ, E) X ℝ 2) x u v = 0 :=
  ContinuousAlternatingMap.hermitianForm_zero u v

/-- The Hermitian form is additive in the two-form. -/
@[simp]
theorem twoFormHermitianForm_add (β : RoughForm 𝓘(ℝ, E) X ℝ 2) (u v : E) :
    twoFormHermitianForm E (α + β) x u v =
      twoFormHermitianForm E α x u v + twoFormHermitianForm E β x u v :=
  ContinuousAlternatingMap.hermitianForm_add (E := E) (α x) (β x) u v

/-- The Hermitian form of `-α` is `-H_α`. -/
@[simp]
theorem twoFormHermitianForm_neg (u v : E) :
    twoFormHermitianForm E (-α) x u v = -twoFormHermitianForm E α x u v :=
  ContinuousAlternatingMap.hermitianForm_neg (E := E) (α x) u v

/-- The Hermitian form of `α - β` is `H_α - H_β`. -/
@[simp]
theorem twoFormHermitianForm_sub (β : RoughForm 𝓘(ℝ, E) X ℝ 2) (u v : E) :
    twoFormHermitianForm E (α - β) x u v =
      twoFormHermitianForm E α x u v - twoFormHermitianForm E β x u v :=
  ContinuousAlternatingMap.hermitianForm_sub (E := E) (α x) (β x) u v

/-- The Hermitian form of `r • α` is `r·H_α`. -/
@[simp]
theorem twoFormHermitianForm_smul (r : ℝ) (u v : E) :
    twoFormHermitianForm E (r • α) x u v = r * twoFormHermitianForm E α x u v :=
  ContinuousAlternatingMap.hermitianForm_smul (E := E) (α x) r u v

variable (hα : ∀ u v : E, α x ![I • u, I • v] = α x ![u, v])

variable (E α x) in
/-- If `α(x)` has type (1,1), the form `H_α(x)` as a sesquilinear form, conjugate linear in the
first slot. -/
def twoFormSesqForm : E →ₗ⋆[ℂ] E →ₗ[ℂ] ℂ :=
  ContinuousAlternatingMap.hermitianSesqForm (E := E) (α := α x) hα

/-- The sesquilinear form `twoFormSesqForm` evaluates as `H_α`. -/
@[simp]
theorem twoFormSesqForm_apply (u v : E) :
    twoFormSesqForm E α x hα u v = twoFormHermitianForm E α x u v :=
  ContinuousAlternatingMap.hermitianSesqForm_apply (E := E) (α := α x) hα u v

/-- The function underlying `twoFormSesqForm` is `H_α`. -/
theorem coe_twoFormSesqForm :
    (fun u v ↦ twoFormSesqForm E α x hα u v) = twoFormHermitianForm E α x :=
  funext fun u ↦ funext fun v ↦ twoFormSesqForm_apply hα u v

/-- **`H_α(x)` is Hermitian** if `α(x)` has type (1,1). -/
theorem isSymm_twoFormSesqForm : (twoFormSesqForm E α x hα).IsSymm :=
  ContinuousAlternatingMap.isSymm_hermitianSesqForm (E := E) (α := α x) hα

end Forms

namespace SmoothTwoForm

variable [IsManifold 𝓘(ℂ, E) ∞ X] {κ : SmoothTwoForm 𝓘(ℝ, E) X}

/-- A two-form invariant under multiplication by `i` has type (1,1) at every point. -/
theorem Invariant.apply_I_smul_I_smul
    (hκ : κ.Invariant (SmoothAlmostComplexStructure.ofComplexManifold E X)) (x : X) (u v : E) :
    κ.val x ![I • u, I • v] = κ.val x ![u, v] := by
  have h := hκ.apply x u v
  simp only [SmoothAlmostComplexStructure.ofComplexManifold_apply] at h
  exact (SmoothBundleForm.eval₂_apply κ x (I • u) (I • v)).symm.trans
    (h.trans (SmoothBundleForm.eval₂_apply κ x u v))

/-- **The Hermitian form of an invariant two-form is Hermitian.** -/
theorem Invariant.isSymm_twoFormSesqForm
    (hκ : κ.Invariant (SmoothAlmostComplexStructure.ofComplexManifold E X)) (x : X) :
    (twoFormSesqForm E κ.val x (hκ.apply_I_smul_I_smul x)).IsSymm :=
  TauCeti.isSymm_twoFormSesqForm _

/-- **The Hermitian form of a two-form taming multiplication by `i` is positive definite.** -/
theorem Tames.re_twoFormHermitianForm_apply_self_pos
    (hκ : κ.Tames (SmoothAlmostComplexStructure.ofComplexManifold E X)) (x : X) {v : E}
    (hv : v ≠ 0) : 0 < (twoFormHermitianForm E κ.val x v v).re := by
  have h := (SmoothTwoForm.tames_iff.1 hκ) x v hv
  simp only [SmoothAlmostComplexStructure.ofComplexManifold_apply] at h
  rw [twoFormHermitianForm_def]
  exact h.trans_eq (SmoothBundleForm.eval₂_apply κ x v (I • v))

/-- **The Hermitian form of a Hermitian metric is positive definite**, as a sesquilinear form. -/
theorem Compatible.re_twoFormSesqForm_apply_self_pos
    (hκ : κ.Compatible (SmoothAlmostComplexStructure.ofComplexManifold E X)) (x : X) {v : E}
    (hv : v ≠ 0) :
    0 < (twoFormSesqForm E κ.val x (hκ.invariant.apply_I_smul_I_smul x) v v).re := by
  rw [twoFormSesqForm_apply]
  exact hκ.tames.re_twoFormHermitianForm_apply_self_pos x hv

end SmoothTwoForm

end TauCeti
