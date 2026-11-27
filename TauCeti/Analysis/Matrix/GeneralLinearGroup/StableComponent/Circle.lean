/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Fourier.Winding.Units
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.DeterminantK1
public import TauCeti.Topology.Algebra.Matrix.GeneralLinearGroup.StableComponent
import Mathlib.Topology.Algebra.Group.Matrix
import TauCeti.Topology.Algebra.Group.Connected

/-!
# The winding number on the stable component group of `C(S¹, ℂ)`

Let `A = C(AddCircle T, ℂ)` be the Banach algebra of continuous complex functions on a circle, with
`0 < T`. The winding number of the determinant of an invertible matrix over `A` is unchanged by
stabilization `u ↦ u ⊕ 1`, and it is locally constant on `GLₙ(A)`, because the determinant is
continuous and the winding number is locally constant on the units of `A`
(`ContinuousMap.ker_windingNumberHom`). It therefore descends to a homomorphism
`TauCeti.StableComponentGroup.windingNumber T` from the stable component group
`GL_∞(A) / GL_∞(A)₀` to `ℤ`, written multiplicatively.

Composed with the comparison `K₁(A) → GL_∞(A) / GL_∞(A)₀` of algebraic `K₁` with the stable
component group, it is the winding number of the determinant `K₁(A) → Aˣ`
(`TauCeti.StableComponentGroup.windingNumber_toStableComponentGroup`). It is onto, so the stable
component group of `A` is not trivial, unlike that of `ℂ`
(`TauCeti.StableGeneralLinearGroup.identityComponent_complex`). In particular the class of the
unitary `z = fourier 1`, which winds once around the origin, is nontrivial. On the other hand a unit
`u` of `A` has trivial class exactly when it is an exponential `exp g`, joined to `1` by
`s ↦ exp (s g)` (`TauCeti.AlgebraicK1.toStableComponentGroup_ofUnits_eq_one_iff`). Such a unit
still has the nontrivial class `[u]` in algebraic `K₁(A)` when `u ≠ 1`, since its determinant is
`u`.

## Main definitions

* `TauCeti.StableComponentGroup.windingNumber`: the winding number of the determinant, on the
  stable component group of `C(AddCircle T, ℂ)`.

## Main results

* `TauCeti.StableComponentGroup.windingNumber_mk`: the class of an invertible matrix goes to the
  winding number of its determinant.
* `TauCeti.StableComponentGroup.windingNumber_toStableComponentGroup`: on algebraic `K₁`, it is the
  winding number of the determinant.
* `TauCeti.StableComponentGroup.windingNumber_surjective`: it is onto, and the stable component
  group of `C(AddCircle T, ℂ)` is nontrivial.
* `TauCeti.AlgebraicK1.toStableComponentGroup_ofUnits_eq_one_iff`: a unit has trivial class in the
  stable component group exactly when it is the exponential of a continuous function.
* `TauCeti.AlgebraicK1.toStableComponentGroup_ofUnits_ne_one_of_coe_eq_fourier`: the class of the
  Fourier monomial `fourier k`, `k ≠ 0`, is nontrivial.

## References

* C. A. Weibel, *The K-book: An Introduction to Algebraic K-Theory*, Graduate Studies in
  Mathematics 145 (2013), Chapter III, Corollary 1.5.1 and Example 1.5.2.
-/

public section

noncomputable section

open Matrix

namespace TauCeti

variable (T : ℝ) [Fact (0 < T)]

namespace StableComponentGroup

/-- The **winding number of the determinant** on the stable component group of
`C(AddCircle T, ℂ)`: the class of an invertible matrix `u` goes to the winding number of `det u`,
written multiplicatively. It is well defined because stabilization does not change the
determinant, and because the winding number is constant on the identity component of the units,
into which the continuous determinant maps the identity component of `GLₙ`. -/
def windingNumber : StableComponentGroup C(AddCircle T, ℂ) →* Multiplicative ℤ :=
  lift (fun _ ↦ (ContinuousMap.windingNumberHom T).comp GeneralLinearGroup.det)
    (fun _ _ h u ↦ by simp [det_stabilizeGL]) fun _ ↦ by
      rw [← MonoidHom.comap_ker, ContinuousMap.ker_windingNumberHom,
        ← Subgroup.map_le_iff_le_comap]
      exact Subgroup.map_connectedComponentOfOne_le GeneralLinearGroup.continuous_det

variable {T}

/-- The winding number of the class of an invertible matrix is the winding number of its
determinant. -/
@[simp]
theorem windingNumber_mk (n : ℕ) (u : GL (Fin n) C(AddCircle T, ℂ)) :
    windingNumber T (mk _ n u) = ContinuousMap.windingNumberHom T (GeneralLinearGroup.det u) :=
  lift_mk ..

/-- The winding number of the image of a class of algebraic `K₁(C(AddCircle T, ℂ))` in the stable
component group is the winding number of its determinant. -/
@[simp]
theorem windingNumber_toStableComponentGroup (x : AlgebraicK1 C(AddCircle T, ℂ)) :
    windingNumber T (AlgebraicK1.toStableComponentGroup _ x) =
      ContinuousMap.windingNumberHom T (AlgebraicK1.det _ x) := by
  obtain ⟨n, u, rfl⟩ := AlgebraicK1.exists_mk x
  simp

variable (T) in
/-- The winding number of the determinant is onto `ℤ`: the class of the `1 × 1` matrix `(u)` has
the winding number of `u`. -/
theorem windingNumber_surjective : Function.Surjective (windingNumber T) := fun k ↦ by
  obtain ⟨u, rfl⟩ := ContinuousMap.windingNumberHom_surjective T k
  exact ⟨AlgebraicK1.toStableComponentGroup _ (AlgebraicK1.ofUnits _ u), by simp⟩

/-- The stable component group of `C(AddCircle T, ℂ)` is nontrivial, since it maps onto `ℤ`. -/
instance : Nontrivial (StableComponentGroup C(AddCircle T, ℂ)) :=
  (windingNumber_surjective T).nontrivial

end StableComponentGroup

namespace AlgebraicK1

/-- **Units in the stable component group of `C(AddCircle T, ℂ)`**: a unit has trivial class
exactly when it is the exponential of a continuous function. An exponential `exp g` is joined to
`1` by `s ↦ exp (s g)`, while any other unit has nonzero winding number. -/
theorem toStableComponentGroup_ofUnits_eq_one_iff (u : C(AddCircle T, ℂ)ˣ) :
    toStableComponentGroup _ (ofUnits _ u) = 1 ↔
      ∃ g : C(AddCircle T, ℂ), ∀ x, (u : C(AddCircle T, ℂ)) x = Complex.exp (g x) := by
  rw [← ContinuousMap.windingNumberHom_eq_one_iff_exists_exp]
  refine ⟨fun h ↦ by simpa using congrArg (StableComponentGroup.windingNumber T) h, fun h ↦ ?_⟩
  rw [← MonoidHom.mem_ker, ContinuousMap.ker_windingNumberHom] at h
  exact toStableComponentGroup_ofUnits_eq_one_of_mem_connectedComponentOfOne h

/-- The class in the stable component group of `C(AddCircle T, ℂ)` of the Fourier monomial
`fourier k`, `k ≠ 0`, is nontrivial: its winding number is `k`. For `k = 1` this is the unitary
`z`, which winds once around the origin. -/
theorem toStableComponentGroup_ofUnits_ne_one_of_coe_eq_fourier {u : C(AddCircle T, ℂ)ˣ}
    {k : ℤ} (hu : (u : C(AddCircle T, ℂ)) = fourier k) (hk : k ≠ 0) :
    toStableComponentGroup _ (ofUnits _ u) ≠ 1 := fun h ↦ hk <| by
  simpa [ContinuousMap.windingNumberHom_of_coe_eq_fourier hu] using
    congrArg (StableComponentGroup.windingNumber T) h

end AlgebraicK1

end TauCeti
