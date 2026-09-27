/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.SpinorNorm.Basic
public import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.Map
import TauCeti.LinearAlgebra.QuadraticForm.CartanDieudonne.Basic
import TauCeti.Algebra.Group.Subgroup.Ker
import TauCeti.Algebra.Group.Subgroup.Map

/-!
# Spinor norms under isometries

An isometry of quadratic spaces carries reflections to reflections with the same quadratic
value. Since reflections generate the orthogonal group, it preserves the orthogonal spinor norm
and its restriction to the special orthogonal group. This lets spinor-norm computations be
transported across a change of quadratic coordinates. The induced equivalence of spinor-norm
kernels also intertwines the corresponding Spin homomorphisms.

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I §2.
-/

public section

namespace QuadraticMap.IsometryEquiv

open TauCeti QuadraticMap CliffordAlgebra

universe u v w

variable {K : Type u} [Field K] [Invertible (2 : K)]
  {V : Type v} {W : Type w} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  [AddCommGroup W] [Module K W]
  {Q : QuadraticForm K V} {Q' : QuadraticForm K W}

/-- An isometric equivalence preserves the orthogonal spinor norm. -/
@[simp]
theorem orthogonalSpinorNorm_orthogonalGroupCongr (e : Q.IsometryEquiv Q')
    (hQ : Q.Nondegenerate) (g : QuadraticMap.orthogonalGroup Q) :
    @orthogonalSpinorNorm K W _ _ _ e.toLinearEquiv.finiteDimensional _ Q'
      (e.nondegenerate_iff.mp hQ)
      (QuadraticMap.orthogonalGroupCongr e g) = orthogonalSpinorNorm Q hQ g := by
  let _ : FiniteDimensional K W := e.toLinearEquiv.finiteDimensional
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
    rw [MonoidHom.mem_eqLocus, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      QuadraticMap.orthogonalGroupCongr_reflectionOrthogonal,
      orthogonalSpinorNorm_reflectionOrthogonal, orthogonalSpinorNorm_reflectionOrthogonal]
    exact congrArg squareClassHom (by apply Units.ext; simp [e.map_app]))
  have hg : g ∈ H := hH.symm ▸ Subgroup.mem_top g
  exact hg

-- `spinorNorm_apply` is already a simp lemma, so this theorem is not in simp-normal form.
/-- An isometric equivalence preserves the spinor norm on the special orthogonal group. -/
theorem spinorNorm_specialOrthogonalGroupCongr (e : Q.IsometryEquiv Q')
    (hQ : Q.Nondegenerate) (g : QuadraticMap.specialOrthogonalGroup Q) :
    @spinorNorm K W _ _ _ e.toLinearEquiv.finiteDimensional _ Q'
      (e.nondegenerate_iff.mp hQ) (e.specialOrthogonalGroupCongr g) =
      spinorNorm Q hQ g := by
  let _ : FiniteDimensional K W := e.toLinearEquiv.finiteDimensional
  rw [spinorNorm_apply, spinorNorm_apply]
  have he : QuadraticMap.specialOrthogonalToOrthogonal Q'
        (e.specialOrthogonalGroupCongr g) =
      QuadraticMap.orthogonalGroupCongr e (QuadraticMap.specialOrthogonalToOrthogonal Q g) := by
    apply Subtype.ext
    apply LinearEquiv.ext
    intro x
    simp
  rw [he, orthogonalSpinorNorm_orthogonalGroupCongr]

/-- Special-orthogonal transport maps the kernel of the spinor norm onto the kernel for the
isometric quadratic form. -/
theorem map_ker_spinorNorm (e : Q.IsometryEquiv Q') (hQ : Q.Nondegenerate) :
    (MonoidHom.ker (spinorNorm Q hQ)).map
        (e.specialOrthogonalGroupCongr : _ →* _) =
      MonoidHom.ker (@spinorNorm K W _ _ _ e.toLinearEquiv.finiteDimensional _ Q'
        (e.nondegenerate_iff.mp hQ)) := by
  let _ : FiniteDimensional K W := e.toLinearEquiv.finiteDimensional
  apply (Subgroup.map_symm_eq_iff_map_eq
    (MonoidHom.ker (spinorNorm Q hQ))).mp
  rw [← MonoidHom.ker_comp_mulEquiv]
  congr 1
  ext g
  exact e.spinorNorm_specialOrthogonalGroupCongr hQ g

/-- An isometric equivalence restricts to an equivalence of spinor-norm kernels. -/
noncomputable def spinorNormKernelCongr (e : Q.IsometryEquiv Q') (hQ : Q.Nondegenerate) :
    MonoidHom.ker (spinorNorm Q hQ) ≃* MonoidHom.ker
      (@spinorNorm K W _ _ _ e.toLinearEquiv.finiteDimensional _ Q'
        (e.nondegenerate_iff.mp hQ)) :=
  TauCeti.Subgroup.congrOfMapEq e.specialOrthogonalGroupCongr (e.map_ker_spinorNorm hQ)

/-- The underlying special-orthogonal element of `spinorNormKernelCongr` is obtained by
special-orthogonal transport. -/
@[simp]
theorem coe_spinorNormKernelCongr_apply (e : Q.IsometryEquiv Q') (hQ : Q.Nondegenerate)
    (g : MonoidHom.ker (spinorNorm Q hQ)) :
    ((e.spinorNormKernelCongr hQ g : MonoidHom.ker
        (@spinorNorm K W _ _ _ e.toLinearEquiv.finiteDimensional _ Q'
          (e.nondegenerate_iff.mp hQ))) : QuadraticMap.specialOrthogonalGroup Q') =
      e.specialOrthogonalGroupCongr g := by
  rw [spinorNormKernelCongr, TauCeti.Subgroup.coe_congrOfMapEq_apply]

/-- The inverse of `spinorNormKernelCongr` acts through inverse special-orthogonal transport. -/
@[simp]
theorem coe_spinorNormKernelCongr_symm_apply (e : Q.IsometryEquiv Q') (hQ : Q.Nondegenerate)
    (g : MonoidHom.ker
      (@spinorNorm K W _ _ _ e.toLinearEquiv.finiteDimensional _ Q'
        (e.nondegenerate_iff.mp hQ))) :
    (((e.spinorNormKernelCongr hQ).symm g : MonoidHom.ker (spinorNorm Q hQ)) :
        QuadraticMap.specialOrthogonalGroup Q) =
      e.specialOrthogonalGroupCongr.symm g := by
  rw [spinorNormKernelCongr, TauCeti.Subgroup.coe_congrOfMapEq_symm_apply]

/-- Transporting the Spin homomorphism to the spinor-norm kernel agrees with first transporting
the Spin element. -/
@[simp]
theorem spinorNormKernelCongr_spinToSpinorNormKernel (e : Q.IsometryEquiv Q')
    (hQ : Q.Nondegenerate) (x : spinGroup Q) :
    e.spinorNormKernelCongr hQ (spinToSpinorNormKernel Q hQ x) =
      @spinToSpinorNormKernel K W _ _ _ e.toLinearEquiv.finiteDimensional _ Q'
        (e.nondegenerate_iff.mp hQ) (e.spinGroupEquiv x) := by
  let _ : FiniteDimensional K W := e.toLinearEquiv.finiteDimensional
  apply Subtype.ext
  rw [coe_spinorNormKernelCongr_apply, coe_spinToSpinorNormKernel_apply,
    coe_spinToSpinorNormKernel_apply,
    specialOrthogonalGroupCongr_spinToSpecialOrthogonal]

end QuadraticMap.IsometryEquiv
