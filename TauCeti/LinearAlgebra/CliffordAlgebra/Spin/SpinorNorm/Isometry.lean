/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.SpinorNorm.Basic
import TauCeti.LinearAlgebra.QuadraticForm.CartanDieudonne.Basic

/-!
# Spinor norms under isometries

An isometry of quadratic spaces carries reflections to reflections with the same quadratic
value. Since reflections generate the orthogonal group, it preserves the orthogonal spinor norm
and its restriction to the special orthogonal group. This lets spinor-norm computations be
transported across a change of quadratic coordinates.
-/

public section

namespace CliffordAlgebra

open TauCeti QuadraticMap

universe u v w

variable {K : Type u} [Field K] [Invertible (2 : K)]
  {V : Type v} {W : Type w} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  [AddCommGroup W] [Module K W] [FiniteDimensional K W]
  {Q : QuadraticForm K V} {Q' : QuadraticForm K W}

/-- An isometric equivalence preserves the orthogonal spinor norm. -/
@[simp]
theorem orthogonalSpinorNorm_orthogonalGroupCongr (e : Q.IsometryEquiv Q')
    (hQ : Q.Nondegenerate) (g : QuadraticMap.orthogonalGroup Q) :
    orthogonalSpinorNorm Q' (e.nondegenerate_iff.mp hQ)
      (QuadraticMap.orthogonalGroupCongr e g) = orthogonalSpinorNorm Q hQ g := by
  let H : Subgroup (QuadraticMap.orthogonalGroup Q) :=
    @MonoidHom.eqLocus (QuadraticMap.orthogonalGroup Q) _
      (Multiplicative (SquareClassGroup K)) _
      ((orthogonalSpinorNorm Q' (e.nondegenerate_iff.mp hQ)).comp
        (QuadraticMap.orthogonalGroupCongr e).toMonoidHom)
      (orthogonalSpinorNorm Q hQ)
  have hH : H = ⊤ := QuadraticMap.subgroup_eq_top_of_reflection_mem Q hQ H (by
    intro x _
    have h : Invertible (Q' (e x)) := by rw [e.map_app]; infer_instance
    let _ := h
    -- Membership in the equality locus unfolds to equality of the two homomorphisms.
    change orthogonalSpinorNorm Q' (e.nondegenerate_iff.mp hQ)
        (QuadraticMap.orthogonalGroupCongr e (reflectionOrthogonal Q x)) =
      orthogonalSpinorNorm Q hQ (reflectionOrthogonal Q x)
    rw [QuadraticMap.orthogonalGroupCongr_reflectionOrthogonal,
      orthogonalSpinorNorm_reflectionOrthogonal, orthogonalSpinorNorm_reflectionOrthogonal]
    exact congrArg squareClassHom (by apply Units.ext; simp [e.map_app]))
  have hg : g ∈ H := hH.symm ▸ Subgroup.mem_top g
  exact hg

/-- An isometric equivalence preserves the spinor norm on the special orthogonal group. -/
theorem spinorNorm_specialOrthogonalGroupCongr (e : Q.IsometryEquiv Q')
    (hQ : Q.Nondegenerate) (g : QuadraticMap.specialOrthogonalGroup Q) :
    spinorNorm Q' (e.nondegenerate_iff.mp hQ) (e.specialOrthogonalGroupCongr g) =
      spinorNorm Q hQ g := by
  rw [spinorNorm_apply, spinorNorm_apply]
  have he : QuadraticMap.specialOrthogonalToOrthogonal Q'
        (e.specialOrthogonalGroupCongr g) =
      QuadraticMap.orthogonalGroupCongr e (QuadraticMap.specialOrthogonalToOrthogonal Q g) := by
    apply Subtype.ext
    apply LinearEquiv.ext
    intro x
    simp
  rw [he, orthogonalSpinorNorm_orthogonalGroupCongr]

end CliffordAlgebra
