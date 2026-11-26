/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Module.Dual.Reflexive.Basic
public import TauCeti.Geometry.Manifold.TwoForm.Closed
public import TauCeti.Geometry.Symplectic.Cotangent.StrongDual
public import TauCeti.Geometry.Symplectic.Hamiltonian.Manifold
public import TauCeti.Geometry.Symplectic.Manifold.StronglyNondegenerate
public import TauCeti.Topology.ContinuousMap.ZeroAtInfty.Reflexive

import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace

/-!
# Weak and strong nondegeneracy of the canonical form on `V × V*`

For a real normed space `V`, the canonical symplectic form

`ω((q, α), (q', β)) = β(q) - α(q')`

on `V × V*`, with `V* = StrongDual ℝ V` (`TauCeti.strongDualCotangentSymplecticForm`), is a
continuous bilinear form (`TauCeti.strongDualCotangentSymplecticFormL`), hence a constant smooth
two-form on the model manifold `V × V*` (`TauCeti.strongDualCotangentSmoothForm`). It is closed
and, by the Hahn–Banach theorem, weakly nondegenerate in every normed space: the flat map
`ω♭ : (q, α) ↦ ω((q, α), ·)` is injective (`TauCeti.isNondegenerate_strongDualCotangentSmoothForm`,
`TauCeti.SmoothTwoForm.isNondegenerate_iff_injective_flat`).

The flat map is not onto the continuous dual in general. Its image consists of the functionals
`(q', β) ↦ a(q') + β(q)` with `a ∈ V*` and `q ∈ V`, so a functional `φ` of `V × V*` lies in it
exactly when its restriction `β ↦ φ(0, β)` to the second factor, an element of the bidual `V**`,
is evaluation at a point of `V`
(`TauCeti.mem_range_flat_strongDualCotangentSmoothForm_iff`). Hence `ω` is strongly nondegenerate,
and its flat maps are invertible, exactly when `V` is reflexive, that is, when the canonical map
`V → V**` (`NormedSpace.inclusionInDoubleDual`) is onto
(`TauCeti.surjective_flat_strongDualCotangentSmoothForm_iff`,
`TauCeti.isInvertible_flat_strongDualCotangentSmoothForm_iff`). No completeness is assumed: a
reflexive space is complete.

On a non-reflexive space the field `X_f = (ω♭)⁻¹ df` of
`TauCeti.SmoothTwoForm.hamiltonianVectorField` is the junk value `0` for every function `f`, and
the bracket `{f, g} = ω(X_f, X_g)` of
`TauCeti.SmoothTwoForm.poissonBracket` vanishes identically
(`TauCeti.hamiltonianVectorField_strongDualCotangentSmoothForm_eq_zero`,
`TauCeti.poissonBracket_strongDualCotangentSmoothForm_eq_zero`). Yet linear functions do have
Hamiltonian vector fields: the constant field `(b, -a)` satisfies `ι_X ω = df` for
`f(q, α) = a(q) + α(b)` (`TauCeti.isHamiltonianVectorField_strongDualCotangentSmoothForm`), in
every normed space. In particular the position coordinate `f(q, α) = a(q)` has the Hamiltonian
vector field `(0, -a)`, the momentum coordinate `g(q, α) = α(b)` has `(b, 0)`, and these fields
pair to `ω((0, -a), (b, 0)) = a(b)`, the canonical relation between position and momentum. So on a
non-reflexive space, statements about `X_f` that ignore strong nondegeneracy are false, and
statements that hold for weakly nondegenerate forms must be made for the predicate
`TauCeti.SmoothTwoForm.IsHamiltonianVectorField`: `X_f` is not a Hamiltonian vector field of `f`
for `f(q, α) = a(q)` with `a ≠ 0`
(`TauCeti.not_isHamiltonianVectorField_hamiltonianVectorField_strongDualCotangentSmoothForm`).

The space `c₀ = C₀(ι, ℝ)` of families vanishing at infinity, over an infinite discrete index type,
is not reflexive (`ZeroAtInftyContinuousMap.not_surjective_inclusionInDoubleDual`), and gives the
basic example: the canonical form on `c₀ × c₀*` is not strongly nondegenerate
(`TauCeti.not_surjective_flat_strongDualCotangentSmoothForm_zeroAtInfty`), and its fields
`(ω♭)⁻¹ df` all vanish
(`TauCeti.hamiltonianVectorField_strongDualCotangentSmoothForm_zeroAtInfty_eq_zero`).

## Main definitions

* `TauCeti.strongDualCotangentSmoothForm`: the canonical form on `V × V*` as a constant smooth
  two-form.

## Main results

* `TauCeti.isSymplectic_strongDualCotangentSmoothForm`: it is closed and weakly nondegenerate.
* `TauCeti.surjective_flat_strongDualCotangentSmoothForm_iff`: it is strongly nondegenerate
  exactly when `V` is reflexive.
* `TauCeti.hamiltonianVectorField_strongDualCotangentSmoothForm_eq_zero`,
  `TauCeti.poissonBracket_strongDualCotangentSmoothForm_eq_zero`: on a non-reflexive space the
  pinned Hamiltonian vector fields and Poisson brackets vanish.
* `TauCeti.isHamiltonianVectorField_strongDualCotangentSmoothForm`: the Hamiltonian vector field
  `(b, -a)` of the linear function `(q, α) ↦ a(q) + α(b)`.

## References

* P. R. Chernoff, J. E. Marsden, *Properties of Infinite Dimensional Hamiltonian Systems*,
  Lecture Notes in Mathematics 425, Springer, 1974, Section 1.2 (weak and strong nondegeneracy,
  and the canonical form on `V × V*`).
* R. Abraham, J. E. Marsden, *Foundations of Mechanics*, 2nd ed., Addison-Wesley, 1978,
  Section 3.2.
-/

public section

noncomputable section

open Function NormedSpace Set
open scoped Manifold ZeroAtInfty

namespace TauCeti

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-! ### The canonical form as a constant smooth two-form -/

variable (V) in
/-- The canonical symplectic form `((q, α), (q', β)) ↦ β(q) - α(q')` on `V × V*`, as a constant
smooth two-form on the model manifold `V × V*`. In finite dimension it is
`strongDualCotangentSymplecticForm.constSmooth`
(`TauCeti.strongDualCotangentSmoothForm_eq_constSmooth`). -/
def strongDualCotangentSmoothForm :
    SmoothTwoForm 𝓘(ℝ, V × StrongDual ℝ V) (V × StrongDual ℝ V) :=
  SmoothTwoForm.const (strongDualCotangentSymplecticFormL V)

/-- The canonical smooth two-form evaluates as the canonical form on `V × V*`, after the
identification of each tangent space of the model manifold with `V × V*`. -/
theorem eval₂_strongDualCotangentSmoothForm (x : V × StrongDual ℝ V)
    (v w : TangentSpace 𝓘(ℝ, V × StrongDual ℝ V) x) :
    SmoothBundleForm.eval₂ (strongDualCotangentSmoothForm V) x v w =
      strongDualCotangentSymplecticForm (fromTangentSpace x v) (fromTangentSpace x w) :=
  (SmoothTwoForm.const_apply _ (fun _ ↦ by simp) x v w).trans
    (strongDualCotangentSymplecticFormL_apply _ _)

/-- The simp normal form of `TauCeti.eval₂_strongDualCotangentSmoothForm`, with `eval₂`
unfolded. -/
@[simp]
theorem strongDualCotangentSmoothForm_apply (x : V × StrongDual ℝ V)
    (v w : TangentSpace 𝓘(ℝ, V × StrongDual ℝ V) x) :
    (strongDualCotangentSmoothForm V).val x ![v, w] =
      strongDualCotangentSymplecticForm (fromTangentSpace x v) (fromTangentSpace x w) :=
  (SmoothBundleForm.eval₂_apply _ x v w).symm.trans (eval₂_strongDualCotangentSmoothForm x v w)

/-- The flat map of the canonical smooth two-form, after the identification of each tangent space
of the model manifold with `V × V*`. -/
theorem flat_strongDualCotangentSmoothForm_apply (x : V × StrongDual ℝ V)
    (v w : TangentSpace 𝓘(ℝ, V × StrongDual ℝ V) x) :
    (strongDualCotangentSmoothForm V).flat x v w =
      (fromTangentSpace x w).2 (fromTangentSpace x v).1 -
        (fromTangentSpace x v).2 (fromTangentSpace x w).1 := by
  rw [SmoothTwoForm.flat_apply, eval₂_strongDualCotangentSmoothForm,
    strongDualCotangentSymplecticForm_apply]

/-- In finite dimension, the canonical smooth two-form is the constant smooth two-form
`SymplecticForm.constSmooth` of the canonical symplectic form. -/
theorem strongDualCotangentSmoothForm_eq_constSmooth [FiniteDimensional ℝ V] :
    strongDualCotangentSmoothForm V = strongDualCotangentSymplecticForm.constSmooth :=
  SmoothBundleForm.ext_eval₂ fun x v w ↦ by
    rw [eval₂_strongDualCotangentSmoothForm, SymplecticForm.fromTangentSpace_constSmooth_apply]

/-- **The canonical form is weakly nondegenerate** on `V × V*` for every normed space `V`, by the
Hahn–Banach theorem. -/
theorem isNondegenerate_strongDualCotangentSmoothForm :
    (strongDualCotangentSmoothForm V).IsNondegenerate :=
  SmoothTwoForm.isNondegenerate_iff_separatingLeft.2 fun x v hv ↦
    (fromTangentSpace x).injective <| by
      rw [map_zero]
      refine strongDualCotangentSymplecticForm.separatingLeft _ fun w ↦ ?_
      simpa using hv ((fromTangentSpace x).symm w)

/-- **The canonical form on `V × V*` is symplectic**: closed and weakly nondegenerate, for every
normed space `V`. -/
theorem isSymplectic_strongDualCotangentSmoothForm :
    (strongDualCotangentSmoothForm V).IsSymplectic :=
  ⟨SmoothTwoForm.isClosed_const _, isNondegenerate_strongDualCotangentSmoothForm⟩

/-! ### Strong nondegeneracy and reflexivity -/

/-- **The image of the flat map.** A continuous linear functional `φ` on a tangent space of
`V × V*` is `ω((q, α), ·)` for some `(q, α)` exactly when its restriction `β ↦ φ(0, β)` to the
second factor is evaluation at a point `q` of `V`. The image of the flat map thus consists of
the functionals `(q', β) ↦ a(q') + β(q)` with `a ∈ V*` and `q ∈ V`. -/
theorem mem_range_flat_strongDualCotangentSmoothForm_iff {x : V × StrongDual ℝ V}
    {φ : TangentSpace 𝓘(ℝ, V × StrongDual ℝ V) x →L[ℝ] ℝ} :
    φ ∈ range ((strongDualCotangentSmoothForm V).flat x) ↔
      ∃ q : V, ∀ β : StrongDual ℝ V, φ ((fromTangentSpace x).symm (0, β)) = β q := by
  constructor
  · rintro ⟨v, rfl⟩
    refine ⟨(fromTangentSpace x v).1, fun β ↦ ?_⟩
    simp
  · rintro ⟨q, hq⟩
    -- `φ(q', β) = φ(q', 0) + φ(0, β) = a(q') + β(q)`, which is `ω((q, -a), (q', β))`.
    let a : StrongDual ℝ V :=
      φ.comp ((fromTangentSpace x).symm.toContinuousLinearMap.comp
        (ContinuousLinearMap.inl ℝ V (StrongDual ℝ V)))
    refine ⟨(fromTangentSpace x).symm (q, -a), ContinuousLinearMap.ext fun w ↦ ?_⟩
    have hw : w = (fromTangentSpace x).symm ((fromTangentSpace x w).1, 0) +
        (fromTangentSpace x).symm (0, (fromTangentSpace x w).2) := by
      rw [← map_add]
      simp
    rw [flat_strongDualCotangentSmoothForm_apply, ContinuousLinearEquiv.apply_symm_apply]
    conv_rhs => rw [hw, map_add, hq]
    simp [a, sub_eq_add_neg, add_comm]

/-- **The canonical form on `V × V*` is strongly nondegenerate exactly when `V` is reflexive**: its
flat map at any point is onto the continuous dual exactly when the canonical map
`V → V**` is onto. -/
theorem surjective_flat_strongDualCotangentSmoothForm_iff (x : V × StrongDual ℝ V) :
    Surjective ((strongDualCotangentSmoothForm V).flat x) ↔
      Surjective (inclusionInDoubleDual ℝ V) := by
  constructor
  · intro h Ψ
    -- The functional `(q', β) ↦ Ψ(β)` is `ω((q, α), ·)`, and evaluating at `(0, β)` gives
    -- `β(q) = Ψ(β)`.
    obtain ⟨q, hq⟩ := mem_range_flat_strongDualCotangentSmoothForm_iff.1 (h (Ψ.comp
      ((ContinuousLinearMap.snd ℝ V (StrongDual ℝ V)).comp
        (fromTangentSpace x).toContinuousLinearMap)))
    exact ⟨q, ContinuousLinearMap.ext fun β ↦ by simpa using (hq β).symm⟩
  · intro h φ
    obtain ⟨q, hq⟩ := h (φ.comp ((fromTangentSpace x).symm.toContinuousLinearMap.comp
      (ContinuousLinearMap.inr ℝ V (StrongDual ℝ V))))
    exact mem_range_flat_strongDualCotangentSmoothForm_iff.2
      ⟨q, fun β ↦ by simpa using congr($hq β).symm⟩

/-- **The flat maps of the canonical form on `V × V*` are invertible exactly when `V` is
reflexive.** No completeness is assumed: a reflexive space is complete, and then the open mapping
theorem inverts the bijective flat map. -/
theorem isInvertible_flat_strongDualCotangentSmoothForm_iff (x : V × StrongDual ℝ V) :
    ((strongDualCotangentSmoothForm V).flat x).IsInvertible ↔
      Surjective (inclusionInDoubleDual ℝ V) := by
  refine ⟨fun h ↦ (surjective_flat_strongDualCotangentSmoothForm_iff x).1 h.surjective,
    fun h ↦ ?_⟩
  have := completeSpace_of_surjective_inclusionInDoubleDual h
  exact SmoothTwoForm.isInvertible_flat_iff_surjective.2
    ((surjective_flat_strongDualCotangentSmoothForm_iff x).2 h)

/-! ### Hamiltonian vector fields -/

/-- **Hamiltonian vector fields of linear functions.** For every normed space `V`, the constant
vector field `(b, -a)` on `V × V*` is a Hamiltonian vector field of the linear function
`(q, α) ↦ a(q) + α(b)` for the canonical form: `ω((b, -a), (q', β)) = β(b) + a(q')`. -/
theorem isHamiltonianVectorField_strongDualCotangentSmoothForm (a : StrongDual ℝ V) (b : V) :
    (strongDualCotangentSmoothForm V).IsHamiltonianVectorField (fun x ↦ a x.1 + x.2 b)
      fun x ↦ (fromTangentSpace x).symm (b, -a) := by
  -- The function is the continuous linear map `(q, α) ↦ a(q) + α(b)`, its own derivative.
  let L : (V × StrongDual ℝ V) →L[ℝ] ℝ :=
    a.comp (ContinuousLinearMap.fst ℝ V (StrongDual ℝ V)) +
      (ContinuousLinearMap.apply ℝ ℝ b).comp (ContinuousLinearMap.snd ℝ V (StrongDual ℝ V))
  have hLw (w : V × StrongDual ℝ V) : L w = a w.1 + w.2 b := by simp [L]
  have hL : (fun x : V × StrongDual ℝ V ↦ a x.1 + x.2 b) = L := funext fun w ↦ (hLw w).symm
  refine SmoothTwoForm.isHamiltonianVectorField_iff.2 fun x v ↦ ?_
  obtain ⟨w, rfl⟩ := (fromTangentSpace x).symm.surjective v
  rw [hL, mvfderiv_eq_fderiv, L.fderiv]
  simp [hLw, add_comm]

/-- The Hamiltonian vector fields `(0, -a)` of the position coordinate `(q, α) ↦ a(q)` and
`(b, 0)` of the momentum coordinate `(q, α) ↦ α(b)` pair under the canonical form to `a(b)`. -/
theorem eval₂_strongDualCotangentSmoothForm_position_momentum (x : V × StrongDual ℝ V)
    (a : StrongDual ℝ V) (b : V) :
    SmoothBundleForm.eval₂ (strongDualCotangentSmoothForm V) x
      ((fromTangentSpace x).symm (0, -a)) ((fromTangentSpace x).symm (b, 0)) = a b := by
  simp

/-- On a non-reflexive space, **the field `(ω♭)⁻¹ df` is zero for every function `f`**: no flat
map of the canonical form is invertible. -/
theorem hamiltonianVectorField_strongDualCotangentSmoothForm_eq_zero
    (hV : ¬ Surjective (inclusionInDoubleDual ℝ V)) (f : V × StrongDual ℝ V → ℝ) :
    (strongDualCotangentSmoothForm V).hamiltonianVectorField f = 0 :=
  funext fun x ↦ SmoothTwoForm.hamiltonianVectorField_eq_zero_of_not_isInvertible_flat
    (mt (isInvertible_flat_strongDualCotangentSmoothForm_iff x).1 hV) f

/-- On a non-reflexive space, **the Poisson bracket `ω(X_f, X_g)` of the fields `(ω♭)⁻¹ df` and
`(ω♭)⁻¹ dg` vanishes for all functions `f` and `g`**, although the Hamiltonian vector fields of
the position and momentum coordinates pair to their canonical relation
(`TauCeti.eval₂_strongDualCotangentSmoothForm_position_momentum`). -/
theorem poissonBracket_strongDualCotangentSmoothForm_eq_zero
    (hV : ¬ Surjective (inclusionInDoubleDual ℝ V)) (f g : V × StrongDual ℝ V → ℝ) :
    (strongDualCotangentSmoothForm V).poissonBracket f g = 0 :=
  funext fun x ↦ SmoothTwoForm.poissonBracket_eq_zero_of_not_isInvertible_flat
    (mt (isInvertible_flat_strongDualCotangentSmoothForm_iff x).1 hV) f g

/-- **On a non-reflexive space, the field `(ω♭)⁻¹ df` is not a Hamiltonian vector field of `f`.**
For a nonzero functional `a`, the position coordinate `f(q, α) = a(q)` has the Hamiltonian vector
field `(0, -a)` (`TauCeti.isHamiltonianVectorField_strongDualCotangentSmoothForm`), which is
nonzero, while `(ω♭)⁻¹ df` is zero. -/
theorem not_isHamiltonianVectorField_hamiltonianVectorField_strongDualCotangentSmoothForm
    (hV : ¬ Surjective (inclusionInDoubleDual ℝ V)) {a : StrongDual ℝ V} (ha : a ≠ 0) :
    ¬ (strongDualCotangentSmoothForm V).IsHamiltonianVectorField (fun x ↦ a x.1)
      ((strongDualCotangentSmoothForm V).hamiltonianVectorField fun x ↦ a x.1) := fun h ↦ by
  have hX : (strongDualCotangentSmoothForm V).IsHamiltonianVectorField (fun x ↦ a x.1)
      fun x ↦ (fromTangentSpace x).symm (0, -a) := by
    simpa using isHamiltonianVectorField_strongDualCotangentSmoothForm a 0
  -- The two Hamiltonian vector fields agree by weak nondegeneracy, and the second one is zero.
  have hXh := hX.unique isNondegenerate_strongDualCotangentSmoothForm h
  rw [hamiltonianVectorField_strongDualCotangentSmoothForm_eq_zero hV] at hXh
  have h0 := congr(fromTangentSpace 0 ($hXh 0))
  rw [Pi.zero_apply, map_zero, ContinuousLinearEquiv.apply_symm_apply] at h0
  exact ha (neg_eq_zero.1 congr($h0.2))

/-! ### The space `c₀` -/

section ZeroAtInfty

variable {ι : Type*} [TopologicalSpace ι] [DiscreteTopology ι] [Infinite ι]

/-- On `c₀ = C₀(ι, ℝ)`, over an infinite discrete index type, the canonical form is weakly but
not strongly nondegenerate: no flat map is onto the continuous dual. -/
theorem not_surjective_flat_strongDualCotangentSmoothForm_zeroAtInfty
    (x : C₀(ι, ℝ) × StrongDual ℝ C₀(ι, ℝ)) :
    ¬ Surjective ((strongDualCotangentSmoothForm C₀(ι, ℝ)).flat x) :=
  (surjective_flat_strongDualCotangentSmoothForm_iff x).not.2
    (ZeroAtInftyContinuousMap.not_surjective_inclusionInDoubleDual (𝕜 := ℝ) (ι := ι))

/-- On `c₀ = C₀(ι, ℝ)`, over an infinite discrete index type, the field `(ω♭)⁻¹ df` is zero for
every function `f`, although the coordinate `(q, α) ↦ q(i)` has the nonzero Hamiltonian vector
field `(0, -evalᵢ)` (`TauCeti.isHamiltonianVectorField_strongDualCotangentSmoothForm`). -/
theorem hamiltonianVectorField_strongDualCotangentSmoothForm_zeroAtInfty_eq_zero
    (f : C₀(ι, ℝ) × StrongDual ℝ C₀(ι, ℝ) → ℝ) :
    (strongDualCotangentSmoothForm C₀(ι, ℝ)).hamiltonianVectorField f = 0 :=
  hamiltonianVectorField_strongDualCotangentSmoothForm_eq_zero
    (ZeroAtInftyContinuousMap.not_surjective_inclusionInDoubleDual (𝕜 := ℝ) (ι := ι)) f

end ZeroAtInfty

end TauCeti
