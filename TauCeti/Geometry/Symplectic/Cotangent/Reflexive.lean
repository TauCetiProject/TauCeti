/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Cotangent.StrongDual
public import TauCeti.Geometry.Symplectic.Hamiltonian.Manifold
public import TauCeti.Topology.ContinuousMap.ZeroAtInfty.Reflexive

/-!
# Weak against strong nondegeneracy on the cotangent model

For a real normed space `V`, the continuous-dual cotangent model `V × V*`, with `V*` the
continuous dual `StrongDual ℝ V`, carries the canonical form

`ω((q, α), (q', β)) = β(q) - α(q')`

(`TauCeti.strongDualCotangentSymplecticForm`). It is always weakly nondegenerate: by Hahn–Banach,
no nonzero vector is `ω`-orthogonal to everything. It is **strongly nondegenerate exactly
when `V` is reflexive**, that is, when the inclusion `V → V**` into the double dual is onto. A
continuous linear form `ℓ` on `V × V*` splits as
`ℓ(q', β) = a(q') + Ψ(β)` with `a ∈ V*` and `Ψ ∈ V**`, while the flat map
`v ↦ ω(v, ·)` (`TauCeti.strongDualCotangentFlat`) sends `(q, α)` to the form
`(q', β) ↦ β(q) - α(q')`, whose `V**`-part is evaluation at `q`. So `ℓ` is hit exactly when `Ψ`
is evaluation at a point of `V` (`TauCeti.surjective_strongDualCotangentFlat_iff`, in
`TauCeti.Geometry.Symplectic.Cotangent.StrongDual`).

Read as a constant two-form on the manifold `V × V*`
(`TauCeti.strongDualCotangentTwoForm`), the same holds pointwise: the flat maps are all onto the
continuous dual exactly when `V` is reflexive
(`TauCeti.surjective_flat_strongDualCotangentTwoForm_iff`, through
`TauCeti.SmoothTwoForm.surjective_flat_const_iff`), while the form is nondegenerate for every `V`
(`TauCeti.isNondegenerate_strongDualCotangentTwoForm`).

The distinction is visible on Hamiltonian vector fields. For every `V`, the position function
`f(q, α) = a(q)` of a covector `a ∈ V*` has the Hamiltonian vector field `(0, -a)`
(`TauCeti.isHamiltonianVectorField_strongDualCotangentTwoForm_comp_fst`), and the momentum
function `g(q, α) = α(b)` of a vector `b ∈ V` has the Hamiltonian vector field `(b, 0)`
(`TauCeti.isHamiltonianVectorField_strongDualCotangentTwoForm_apply_snd`). Their pairing is the
canonical relation `ω((0, -a), (b, 0)) = a(b)` between position and momentum
(`TauCeti.eval₂_strongDualCotangentTwoForm_position_momentum`). If `V` is not reflexive, however,
no flat map is invertible, and the field `TauCeti.SmoothTwoForm.hamiltonianVectorField`, defined
as `(ω♭)⁻¹ df` with the junk value `0` of a non-invertible map, vanishes for every function
(`TauCeti.hamiltonianVectorField_strongDualCotangentTwoForm_eq_zero`). So it is not a Hamiltonian
vector field of the position function of a nonzero `a`
(`TauCeti.not_isHamiltonianVectorField_strongDualCotangentTwoForm_hamiltonianVectorField`), and
the Poisson bracket `TauCeti.SmoothTwoForm.poissonBracket` built from it vanishes identically
(`TauCeti.poissonBracket_strongDualCotangentTwoForm_eq_zero`), although the bracket `ω(X_f, X_g)`
of the genuine Hamiltonian vector fields is `a(b)`. This is why statements about Hamiltonian
vector fields of weakly nondegenerate forms are stated for the predicate
`TauCeti.SmoothTwoForm.IsHamiltonianVectorField`, and statements about `X_f` and `{f, g}` carry
invertibility of the flat maps.

The space `c₀ = C₀(ℕ, ℝ)` of real sequences tending to zero is not reflexive
(`ZeroAtInftyContinuousMap.not_surjective_inclusionInDoubleDual`), so its cotangent model is a
Banach-space example of a weakly but not strongly nondegenerate form
(`TauCeti.not_surjective_flat_strongDualCotangentTwoForm_c0`), with a position function whose
pinned Hamiltonian vector field is not a Hamiltonian vector field
(`TauCeti.not_isHamiltonianVectorField_strongDualCotangentTwoForm_c0`).

## Main definitions

* `TauCeti.strongDualCotangentTwoForm`: the canonical form as a constant smooth two-form on
  `V × V*`, built from its flat map `TauCeti.strongDualCotangentFlat`.

## Main results

* `TauCeti.surjective_flat_strongDualCotangentTwoForm_iff`: the constant two-form is strongly
  nondegenerate exactly when `V` is reflexive.
* `TauCeti.isHamiltonianVectorField_strongDualCotangentTwoForm_comp_fst`,
  `TauCeti.isHamiltonianVectorField_strongDualCotangentTwoForm_apply_snd`: the Hamiltonian vector
  fields of position and momentum functions, for every `V`.
* `TauCeti.hamiltonianVectorField_strongDualCotangentTwoForm_eq_zero`,
  `TauCeti.poissonBracket_strongDualCotangentTwoForm_eq_zero`: on a non-reflexive `V` the pinned
  Hamiltonian vector field and Poisson bracket vanish.
* `TauCeti.not_isHamiltonianVectorField_strongDualCotangentTwoForm_c0`: on `c₀` the pinned field
  of a position function is not a Hamiltonian vector field.

## References

* P. R. Chernoff, J. E. Marsden, *Properties of Infinite Dimensional Hamiltonian Systems*,
  Lecture Notes in Mathematics 425, Springer, 1974, Section 1.2 (weak and strong
  nondegeneracy).
* R. Abraham, J. E. Marsden, *Foundations of Mechanics*, 2nd ed., Addison-Wesley, 1978,
  Section 3.2.
-/

public section

noncomputable section

open NormedSpace
open scoped Manifold ZeroAtInfty

namespace TauCeti

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-! ### The constant two-form -/

variable (V) in
/-- The canonical form `ω((q, α), (q', β)) = β(q) - α(q')` on `V × V*` as a constant smooth
two-form on the manifold `V × V*`. -/
def strongDualCotangentTwoForm :
    SmoothTwoForm 𝓘(ℝ, V × StrongDual ℝ V) (V × StrongDual ℝ V) :=
  SmoothTwoForm.const (strongDualCotangentFlat V)

/-- The constant two-form evaluates two tangent vectors, read in the model space `V × V*`, by the
canonical form. -/
theorem eval₂_strongDualCotangentTwoForm (x : V × StrongDual ℝ V)
    (v w : TangentSpace 𝓘(ℝ, V × StrongDual ℝ V) x) :
    SmoothBundleForm.eval₂ (strongDualCotangentTwoForm V) x v w =
      strongDualCotangentFlat V (fromTangentSpace x v) (fromTangentSpace x w) :=
  SmoothTwoForm.const_apply (strongDualCotangentFlat V) strongDualCotangentFlat_apply_self x v w

/-- **The constant canonical two-form on `V × V*` is strongly nondegenerate exactly when `V` is
reflexive.** -/
theorem surjective_flat_strongDualCotangentTwoForm_iff :
    (∀ x, Function.Surjective ((strongDualCotangentTwoForm V).flat x)) ↔
      Function.Surjective (inclusionInDoubleDual ℝ V) := by
  simp_rw [strongDualCotangentTwoForm, SmoothTwoForm.surjective_flat_const_iff
    (strongDualCotangentFlat V) strongDualCotangentFlat_apply_self,
    surjective_strongDualCotangentFlat_iff]
  exact ⟨fun h ↦ h 0, fun h _ ↦ h⟩

/-- **The constant canonical two-form on `V × V*` is nondegenerate**, for every normed space `V`,
by Hahn–Banach. -/
@[simp]
theorem isNondegenerate_strongDualCotangentTwoForm :
    (strongDualCotangentTwoForm V).IsNondegenerate :=
  (SmoothTwoForm.isNondegenerate_const_iff (strongDualCotangentFlat V)
    strongDualCotangentFlat_apply_self).2
    fun v hv ↦ strongDualCotangentSymplecticForm.nondegenerate.1 v fun w ↦
      (strongDualCotangentFlat_apply_apply_eq_strongDualCotangentSymplecticForm v w).symm.trans
        (hv w)

/-! ### Hamiltonian vector fields of position and momentum functions -/

/-- **The Hamiltonian vector field of a position function.** For a covector `a ∈ V*`, the
function `(q, α) ↦ a(q)` on `V × V*` has the constant Hamiltonian vector field `(0, -a)`, for
every normed space `V`. -/
theorem isHamiltonianVectorField_strongDualCotangentTwoForm_comp_fst (a : StrongDual ℝ V) :
    (strongDualCotangentTwoForm V).IsHamiltonianVectorField (fun z ↦ a z.1)
      (fun x ↦ (fromTangentSpace x).symm ((0 : V), -a)) := by
  refine SmoothTwoForm.isHamiltonianVectorField_iff.2 fun x v ↦ ?_
  have hd : HasFDerivAt (fun z : V × StrongDual ℝ V ↦ a z.1)
      (a.comp (ContinuousLinearMap.fst ℝ V (StrongDual ℝ V))) x :=
    a.hasFDerivAt.comp x hasFDerivAt_fst
  rw [eval₂_strongDualCotangentTwoForm, ContinuousLinearEquiv.apply_symm_apply,
    strongDualCotangentFlat_apply_apply, mvfderiv_eq_fderiv, hd.fderiv]
  simp

/-- **The Hamiltonian vector field of a momentum function.** For a vector `b ∈ V`, the function
`(q, α) ↦ α(b)` on `V × V*` has the constant Hamiltonian vector field `(b, 0)`, for every normed
space `V`. -/
theorem isHamiltonianVectorField_strongDualCotangentTwoForm_apply_snd (b : V) :
    (strongDualCotangentTwoForm V).IsHamiltonianVectorField (fun z ↦ z.2 b)
      (fun x ↦ (fromTangentSpace x).symm (b, (0 : StrongDual ℝ V))) := by
  refine SmoothTwoForm.isHamiltonianVectorField_iff.2 fun x v ↦ ?_
  have hd : HasFDerivAt (fun z : V × StrongDual ℝ V ↦ z.2 b)
      ((ContinuousLinearMap.apply ℝ ℝ b).comp (ContinuousLinearMap.snd ℝ V (StrongDual ℝ V))) x :=
    (ContinuousLinearMap.apply ℝ ℝ b).hasFDerivAt.comp x hasFDerivAt_snd
  rw [eval₂_strongDualCotangentTwoForm, ContinuousLinearEquiv.apply_symm_apply,
    strongDualCotangentFlat_apply_apply, mvfderiv_eq_fderiv, hd.fderiv]
  simp

/-- **Position and momentum are canonically conjugate**: the form pairs the Hamiltonian vector
field `(0, -a)` of `(q, α) ↦ a(q)` with the Hamiltonian vector field `(b, 0)` of
`(q, α) ↦ α(b)` to the constant `a(b)`. -/
theorem eval₂_strongDualCotangentTwoForm_position_momentum (x : V × StrongDual ℝ V)
    (a : StrongDual ℝ V) (b : V) :
    SmoothBundleForm.eval₂ (strongDualCotangentTwoForm V) x
        ((fromTangentSpace x).symm ((0 : V), -a)) ((fromTangentSpace x).symm (b, 0)) =
      a b := by
  rw [eval₂_strongDualCotangentTwoForm]
  simp

/-! ### The pinned Hamiltonian vector field on a non-reflexive space -/

/-- On a non-reflexive `V`, no flat map of the constant canonical two-form is invertible. -/
theorem not_isInvertible_flat_strongDualCotangentTwoForm
    (hV : ¬ Function.Surjective (inclusionInDoubleDual ℝ V)) (x : V × StrongDual ℝ V) :
    ¬ ((strongDualCotangentTwoForm V).flat x).IsInvertible := fun h ↦
  hV <| surjective_strongDualCotangentFlat_iff.1 <|
    (SmoothTwoForm.surjective_flat_const_iff (strongDualCotangentFlat V)
      strongDualCotangentFlat_apply_self x).1 h.surjective

/-- **On a non-reflexive `V` the pinned Hamiltonian vector field vanishes**: the field
`(ω♭)⁻¹ df` of every function on `V × V*` is `0`, since no flat map is invertible. -/
theorem hamiltonianVectorField_strongDualCotangentTwoForm_eq_zero
    (hV : ¬ Function.Surjective (inclusionInDoubleDual ℝ V)) (f : V × StrongDual ℝ V → ℝ) :
    (strongDualCotangentTwoForm V).hamiltonianVectorField f = 0 :=
  funext fun x ↦ SmoothTwoForm.hamiltonianVectorField_eq_zero_of_not_isInvertible_flat
    (not_isInvertible_flat_strongDualCotangentTwoForm hV x) f

/-- **On a non-reflexive `V` the pinned Poisson bracket vanishes**, although the Hamiltonian
vector fields of position and momentum functions pair to `a(b)`
(`TauCeti.eval₂_strongDualCotangentTwoForm_position_momentum`). -/
theorem poissonBracket_strongDualCotangentTwoForm_eq_zero
    (hV : ¬ Function.Surjective (inclusionInDoubleDual ℝ V)) (f g : V × StrongDual ℝ V → ℝ)
    (x : V × StrongDual ℝ V) :
    (strongDualCotangentTwoForm V).poissonBracket f g x = 0 :=
  SmoothTwoForm.poissonBracket_eq_zero_of_not_isInvertible_flat
    (not_isInvertible_flat_strongDualCotangentTwoForm hV x) f g

/-- **On a non-reflexive `V` the pinned Hamiltonian vector field is not a Hamiltonian vector
field**: for a nonzero covector `a`, the pinned field of `(q, α) ↦ a(q)` is `0`, while its
Hamiltonian vector field is `(0, -a)`. -/
theorem not_isHamiltonianVectorField_strongDualCotangentTwoForm_hamiltonianVectorField
    (hV : ¬ Function.Surjective (inclusionInDoubleDual ℝ V)) {a : StrongDual ℝ V} (ha : a ≠ 0) :
    ¬ (strongDualCotangentTwoForm V).IsHamiltonianVectorField (fun z ↦ a z.1)
      ((strongDualCotangentTwoForm V).hamiltonianVectorField fun z ↦ a z.1) := by
  intro h
  have h0 := SmoothTwoForm.IsHamiltonianVectorField.unique
    isNondegenerate_strongDualCotangentTwoForm h
    (isHamiltonianVectorField_strongDualCotangentTwoForm_comp_fst a)
  rw [hamiltonianVectorField_strongDualCotangentTwoForm_eq_zero hV] at h0
  have := congrArg (fun X ↦ fromTangentSpace 0 (X 0)) h0
  simp only [Pi.zero_apply, map_zero, ContinuousLinearEquiv.apply_symm_apply] at this
  exact ha (neg_eq_zero.1 (congrArg Prod.snd this).symm)

/-! ### The example of `c₀` -/

/-- The cotangent model of `c₀ = C₀(ℕ, ℝ)` is not strongly nondegenerate: `c₀` is not reflexive. -/
theorem not_surjective_flat_strongDualCotangentTwoForm_c0 :
    ¬ ∀ x, Function.Surjective ((strongDualCotangentTwoForm C₀(ℕ, ℝ)).flat x) := by
  rw [surjective_flat_strongDualCotangentTwoForm_iff]
  exact ZeroAtInftyContinuousMap.not_surjective_inclusionInDoubleDual

/-- On the cotangent model of `c₀ = C₀(ℕ, ℝ)`, the pinned Hamiltonian vector field of the position
function `(q, α) ↦ q(0)` is not a Hamiltonian vector field. -/
theorem not_isHamiltonianVectorField_strongDualCotangentTwoForm_c0 :
    ¬ (strongDualCotangentTwoForm C₀(ℕ, ℝ)).IsHamiltonianVectorField (fun z ↦ z.1 0)
      ((strongDualCotangentTwoForm C₀(ℕ, ℝ)).hamiltonianVectorField fun z ↦ z.1 0) := by
  have ha : ZeroAtInftyContinuousMap.evalCLM ℝ (0 : ℕ) ≠ (0 : StrongDual ℝ C₀(ℕ, ℝ)) := fun h ↦ by
    simpa [ZeroAtInftyContinuousMap.single_apply] using
      congrArg (fun φ ↦ φ (ZeroAtInftyContinuousMap.single 0 1)) h
  simpa only [ZeroAtInftyContinuousMap.evalCLM_apply] using
    not_isHamiltonianVectorField_strongDualCotangentTwoForm_hamiltonianVectorField
      ZeroAtInftyContinuousMap.not_surjective_inclusionInDoubleDual ha

end TauCeti
