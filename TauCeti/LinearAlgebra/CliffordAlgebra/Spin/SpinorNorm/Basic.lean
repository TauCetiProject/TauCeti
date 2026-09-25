/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.Pin.Norm
public import TauCeti.LinearAlgebra.CliffordAlgebra.Lipschitz.Kernel
public import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.SpecialOrthogonal
public import TauCeti.LinearAlgebra.QuadraticForm.DetSquareClass
public import TauCeti.LinearAlgebra.QuadraticForm.Radical
import TauCeti.Algebra.Group.Units.Basic
import TauCeti.Algebra.Group.Subgroup.Ker
import TauCeti.LinearAlgebra.CliffordAlgebra.CartanDieudonne
import TauCeti.LinearAlgebra.CliffordAlgebra.Basic

/-!
# The spinor norm

The Clifford norm of a Lipschitz element is a square on the kernel of its orthogonal action.
It therefore descends to the orthogonal group modulo square classes. Restricting this homomorphism
to the special orthogonal group gives the spinor norm, whose kernel is exactly the image of the
Spin group.

## Main results

* `CliffordAlgebra.orthogonalSpinorNorm`: the square-class-valued spinor norm on `O(Q)`.
* `CliffordAlgebra.spinorNorm`: its restriction to `SO(Q)`.
* `CliffordAlgebra.orthogonalSpinorNorm_eq_detSquareClass_of_isSquare_apply`: when every value
  of the form is a square, the orthogonal spinor norm is the determinant square class.
* `CliffordAlgebra.spinToSpecialOrthogonal_surjective_of_isSquare_apply`: the same square-value
  hypothesis makes the Spin action surjective.
* `CliffordAlgebra.range_spinToSpecialOrthogonal_eq_ker_spinorNorm`: the Spin image is
  the kernel of the spinor norm.
* `CliffordAlgebra.spinToSpinorNormKernel`: the Spin action corestricted to that kernel.
* `CliffordAlgebra.spinToSpinorNormKernel_surjective`: the corestricted action is surjective.

## References

See H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I §2.
-/

public section

open QuadraticMap

namespace CliffordAlgebra

open TauCeti

universe u v w

variable {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Invertible (2 : K)]

private theorem lipschitzToOrthogonal_surjective_of_invertible
    (Q : QuadraticForm K V) (hQ : Q.Nondegenerate) :
    Function.Surjective (lipschitzToOrthogonal Q) := by
  have hf : @lipschitzToOrthogonal K V _ _ _ Q (inferInstance : Invertible (2 : K)) =
      @lipschitzToOrthogonal K V _ _ _ Q
        (invertibleOfNonzero (NeZero.ne (2 : K))) := by
    congr 1
    exact Subsingleton.elim _ _
  rw [hf]
  exact lipschitzToOrthogonal_surjective Q hQ

/-- The Clifford norm of an element acting trivially on the quadratic space is a square. -/
theorem isSquare_lipschitzNorm_of_mem_ker (Q : QuadraticForm K V) (hQ : Q.Nondegenerate)
    (x : lipschitzGroup Q) (hx : x ∈ MonoidHom.ker (lipschitzToOrthogonal Q)) :
    IsSquare (lipschitzNorm Q x) := by
  obtain ⟨r, hr⟩ := (mem_ker_lipschitzToOrthogonal_iff hQ).mp hx
  exact ⟨r, lipschitzNorm_eq_of_coe_eq_algebraMap hr⟩

private noncomputable def lipschitzSquareClassHom (Q : QuadraticForm K V) :
    lipschitzGroup Q →* Multiplicative (SquareClassGroup K) :=
  squareClassHom.comp (lipschitzNorm Q)

private theorem ker_lipschitzToOrthogonal_le_ker_lipschitzSquareClassHom
    (Q : QuadraticForm K V) (hQ : Q.Nondegenerate) :
    MonoidHom.ker (lipschitzToOrthogonal Q) ≤ MonoidHom.ker (lipschitzSquareClassHom Q) := by
  intro x hx
  rw [MonoidHom.mem_ker]
  simpa [lipschitzSquareClassHom] using isSquare_lipschitzNorm_of_mem_ker Q hQ x hx

private noncomputable def spinorNormDescentData (Q : QuadraticForm K V) (hQ : Q.Nondegenerate) :
    {g : lipschitzGroup Q →* Multiplicative (SquareClassGroup K) //
      MonoidHom.ker (lipschitzToOrthogonal Q) ≤ MonoidHom.ker g} :=
  ⟨lipschitzSquareClassHom Q,
    ker_lipschitzToOrthogonal_le_ker_lipschitzSquareClassHom Q hQ⟩

/-- The Clifford norm modulo squares, descended through the Lipschitz action to `O(Q)`. -/
noncomputable def orthogonalSpinorNorm (Q : QuadraticForm K V) (hQ : Q.Nondegenerate) :
    QuadraticMap.orthogonalGroup Q →* Multiplicative (SquareClassGroup K) := by
  exact MonoidHom.liftOfSurjective
    (G₃ := Multiplicative (SquareClassGroup K))
    (lipschitzToOrthogonal Q) (lipschitzToOrthogonal_surjective_of_invertible Q hQ)
    (spinorNormDescentData Q hQ)

/-- The descended spinor norm evaluates on a Lipschitz action through its Clifford norm. -/
@[simp]
theorem orthogonalSpinorNorm_lipschitzToOrthogonal (Q : QuadraticForm K V)
    (hQ : Q.Nondegenerate) (x : lipschitzGroup Q) :
    orthogonalSpinorNorm Q hQ (lipschitzToOrthogonal Q x) =
      squareClassHom (lipschitzNorm Q x) := by
  simpa only [orthogonalSpinorNorm, MonoidHom.liftOfSurjective, spinorNormDescentData,
    lipschitzSquareClassHom, MonoidHom.comp_apply] using
    MonoidHom.liftOfRightInverse_comp_apply
      (G₃ := Multiplicative (SquareClassGroup K))
      (lipschitzToOrthogonal Q)
      (Function.surjInv (lipschitzToOrthogonal_surjective_of_invertible Q hQ))
      (Function.rightInverse_surjInv (lipschitzToOrthogonal_surjective_of_invertible Q hQ))
      (spinorNormDescentData Q hQ) x

/-- The spinor norm of an orthogonal reflection is the square class of the negative norm of its
defining vector. -/
@[simp]
theorem orthogonalSpinorNorm_reflectionOrthogonal (Q : QuadraticForm K V)
    (hQ : Q.Nondegenerate)
    (v : V) [Invertible (Q v)] :
    orthogonalSpinorNorm Q hQ (QuadraticMap.reflectionOrthogonal Q v) =
      squareClassHom (-(unitOfInvertible (Q v))) := by
  rw [← lipschitzToOrthogonal_unitι Q v, orthogonalSpinorNorm_lipschitzToOrthogonal,
    lipschitzNorm_unitι]

/-- If every value of a finite-dimensional nondegenerate quadratic form is a square, its
orthogonal spinor norm is the square class of the determinant. This differs from
`spinToSpecialOrthogonal_surjective_of_isSquare`, which assumes that `-⅟(Q v)` is a square. -/
theorem orthogonalSpinorNorm_eq_detSquareClass_of_isSquare_apply
    (Q : QuadraticForm K V) (hQ : Q.Nondegenerate)
    (hsq : ∀ v, IsSquare (Q v)) :
    orthogonalSpinorNorm Q hQ = QuadraticMap.orthogonalDetSquareClass Q := by
  have hH : @MonoidHom.eqLocus (QuadraticMap.orthogonalGroup Q) _
      (Multiplicative (SquareClassGroup K)) _ (orthogonalSpinorNorm Q hQ)
      (QuadraticMap.orthogonalDetSquareClass Q) = ⊤ :=
      QuadraticMap.subgroup_eq_top_of_reflection_mem Q hQ
        (@MonoidHom.eqLocus (QuadraticMap.orthogonalGroup Q) _
          (Multiplicative (SquareClassGroup K)) _ (orthogonalSpinorNorm Q hQ)
          (QuadraticMap.orthogonalDetSquareClass Q)) fun v _ => by
    rw [MonoidHom.mem_eqLocus]
    rw [orthogonalSpinorNorm_reflectionOrthogonal,
      QuadraticMap.orthogonalDetSquareClass_apply]
    rw [QuadraticMap.coe_reflectionOrthogonal, QuadraticMap.det_reflection]
    have hsquareUnit : IsSquare (unitOfInvertible (Q v)) := by
      apply isSquare_units_val_iff.mp
      simpa only [val_unitOfInvertible] using hsq v
    have hsquare : squareClassHom (unitOfInvertible (Q v)) = 1 := by
      simpa using hsquareUnit
    rw [neg_eq_neg_one_mul, map_mul, hsquare]
    exact mul_one (squareClassHom (-1 : Kˣ))
  apply MonoidHom.ext
  intro x
  have hx : x ∈ @MonoidHom.eqLocus (QuadraticMap.orthogonalGroup Q) _
      (Multiplicative (SquareClassGroup K)) _ (orthogonalSpinorNorm Q hQ)
      (QuadraticMap.orthogonalDetSquareClass Q) := by
    rw [hH]
    exact Subgroup.mem_top x
  exact (MonoidHom.mem_eqLocus (G := QuadraticMap.orthogonalGroup Q)
    (M := Multiplicative (SquareClassGroup K)) (f := orthogonalSpinorNorm Q hQ)
    (g := QuadraticMap.orthogonalDetSquareClass Q)).mp hx

/-- The spinor norm on `SO(Q)`, obtained by restricting the orthogonal spinor norm. -/
noncomputable def spinorNorm (Q : QuadraticForm K V) (hQ : Q.Nondegenerate) :
    QuadraticMap.specialOrthogonalGroup Q →* Multiplicative (SquareClassGroup K) :=
  (orthogonalSpinorNorm Q hQ).comp (_root_.QuadraticMap.specialOrthogonalToOrthogonal Q)

/-- The spinor norm is the restriction of the orthogonal spinor norm to `SO(Q)`. -/
@[simp]
theorem spinorNorm_apply (Q : QuadraticForm K V) (hQ : Q.Nondegenerate)
    (g : QuadraticMap.specialOrthogonalGroup Q) :
    spinorNorm Q hQ g =
      orthogonalSpinorNorm Q hQ (_root_.QuadraticMap.specialOrthogonalToOrthogonal Q g) := by
  rw [spinorNorm, MonoidHom.comp_apply]

/-- The Spin action has trivial spinor norm. -/
@[simp high]
theorem spinorNorm_spinToSpecialOrthogonal (Q : QuadraticForm K V) (hQ : Q.Nondegenerate)
    (x : spinGroup Q) : spinorNorm Q hQ (spinToSpecialOrthogonal Q x) = 1 := by
  rw [spinorNorm_apply, specialOrthogonalToOrthogonal_spinToSpecialOrthogonal]
  rw [← pinToOrthogonal_spinToPin]
  rw [pinToOrthogonal_eq_lipschitzToOrthogonal,
    orthogonalSpinorNorm_lipschitzToOrthogonal,
    lipschitzNorm_pinToLipschitz, map_one]

private theorem exists_pinToOrthogonal_eq_of_spinorNorm_eq_one [Nontrivial V]
    (Q : QuadraticForm K V) (hQ : Q.Nondegenerate)
    (g : QuadraticMap.orthogonalGroup Q) (hg : orthogonalSpinorNorm Q hQ g = 1) :
    ∃ p : pinGroup Q, pinToOrthogonal Q p = g := by
  obtain ⟨x, hx⟩ := lipschitzToOrthogonal_surjective_of_invertible Q hQ g
  have hsquare : IsSquare (lipschitzNorm Q x) := by
    have hsquareClass : squareClassHom (lipschitzNorm Q x) = 1 := by
      rw [← orthogonalSpinorNorm_lipschitzToOrthogonal Q hQ, hx, hg]
    simpa using hsquareClass
  obtain ⟨a, ha⟩ := hsquare
  have hv : ∃ v, IsUnit (Q v) := hQ.exists_isUnit
  let y : lipschitzGroup Q := scalarUnits Q hv a⁻¹ * x
  have hynorm : lipschitzNorm Q y = 1 := by
    dsimp only [y]
    rw [map_mul, lipschitzNorm_scalarUnits, ha]
    simp
  have hyact : lipschitzToOrthogonal Q y = g := by
    dsimp only [y]
    rw [map_mul, lipschitzToOrthogonal_scalarUnits, hx, one_mul]
  let p : pinGroup Q :=
    ⟨((y : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q),
      (pinGroup.units_mem_iff).2 ⟨y.2, y.val.isUnit.mem_unitary_of_star_mul_self (by
        rw [star_mul_self_eq_algebraMap_lipschitzNorm Q y, hynorm]
        exact map_one (algebraMap K (CliffordAlgebra Q)))⟩⟩
  refine ⟨p, ?_⟩
  have hpl : pinToLipschitz Q p = y := by
    apply Subtype.ext
    apply Units.ext
    rw [coe_pinToLipschitz_apply]
  rw [pinToOrthogonal_eq_lipschitzToOrthogonal, hpl, hyact]

/-- The image of the Spin action on `SO(Q)` is exactly the kernel of the spinor norm. -/
theorem range_spinToSpecialOrthogonal_eq_ker_spinorNorm
    (Q : QuadraticForm K V) (hQ : Q.Nondegenerate) :
    MonoidHom.range (spinToSpecialOrthogonal Q) = MonoidHom.ker (spinorNorm Q hQ) := by
  rcases subsingleton_or_nontrivial V with hV | hV
  · ext g
    have hg : g = 1 := by
      apply Subtype.ext
      apply LinearEquiv.ext
      intro v
      exact hV.elim _ _
    subst g
    simp
  let _ : Nontrivial V := hV
  apply le_antisymm
  · rintro g ⟨x, rfl⟩
    exact MonoidHom.mem_ker.mpr (spinorNorm_spinToSpecialOrthogonal Q hQ x)
  · intro g hg
    have hg' : orthogonalSpinorNorm Q hQ
        (_root_.QuadraticMap.specialOrthogonalToOrthogonal Q g) = 1 :=
      MonoidHom.mem_ker.mp hg
    obtain ⟨p, hp⟩ := exists_pinToOrthogonal_eq_of_spinorNorm_eq_one Q hQ _ hg'
    have hpEven : (p : CliffordAlgebra Q) ∈ even Q :=
      mem_even_of_det_pinToOrthogonal_eq_one Q p (by
        rw [hp, _root_.QuadraticMap.coe_specialOrthogonalToOrthogonal]
        exact (QuadraticMap.mem_specialOrthogonalGroup_iff.mp g.2).2)
    let x : spinGroup Q := ⟨(p : CliffordAlgebra Q), p.2, hpEven⟩
    refine ⟨x, ?_⟩
    have hxp : spinToPin Q x = p := by
      apply Subtype.ext
      rw [coe_spinToPin_apply]
    have horth : spinToOrthogonal Q x =
        _root_.QuadraticMap.specialOrthogonalToOrthogonal Q g := by
      rw [← pinToOrthogonal_spinToPin, hxp, hp]
    apply _root_.QuadraticMap.specialOrthogonalToOrthogonal_injective
    rw [specialOrthogonalToOrthogonal_spinToSpecialOrthogonal, horth]

/-- The Spin action with codomain restricted to the kernel of the spinor norm. -/
noncomputable def spinToSpinorNormKernel
    (Q : QuadraticForm K V) (hQ : Q.Nondegenerate) :
    spinGroup Q →* MonoidHom.ker (spinorNorm Q hQ) :=
  (spinToSpecialOrthogonal Q).codRestrict _ fun x ↦
    MonoidHom.mem_ker.mpr (spinorNorm_spinToSpecialOrthogonal Q hQ x)

/-- After inclusion into the special orthogonal group, `spinToSpinorNormKernel` is the usual Spin
action. -/
@[simp]
theorem coe_spinToSpinorNormKernel_apply
    (Q : QuadraticForm K V) (hQ : Q.Nondegenerate) (x : spinGroup Q) :
    ((spinToSpinorNormKernel Q hQ x : MonoidHom.ker (spinorNorm Q hQ)) :
      QuadraticMap.specialOrthogonalGroup Q) = spinToSpecialOrthogonal Q x :=
  by rw [spinToSpinorNormKernel, MonoidHom.codRestrict_apply]

/-- Corestricting the Spin action to the spinor-norm kernel does not change its kernel. -/
@[simp]
theorem ker_spinToSpinorNormKernel
    (Q : QuadraticForm K V) (hQ : Q.Nondegenerate) :
    MonoidHom.ker (spinToSpinorNormKernel Q hQ) =
      MonoidHom.ker (spinToSpecialOrthogonal Q) := by
  rw [spinToSpinorNormKernel, MonoidHom.ker_codRestrict]

/-- The Spin action is surjective onto the kernel of the spinor norm. -/
theorem spinToSpinorNormKernel_surjective
    (Q : QuadraticForm K V) (hQ : Q.Nondegenerate) :
    Function.Surjective (spinToSpinorNormKernel Q hQ) := by
  apply (Set.surjective_codRestrict fun x ↦
    MonoidHom.mem_ker.mpr (spinorNorm_spinToSpecialOrthogonal Q hQ x)).2
  rw [← MonoidHom.coe_range, range_spinToSpecialOrthogonal_eq_ker_spinorNorm Q hQ]

/-- If every value of a finite-dimensional nondegenerate quadratic form is a square, the Spin
action on its special orthogonal group is surjective. This differs from
`spinToSpecialOrthogonal_surjective_of_isSquare`, which assumes that `-⅟(Q v)` is a square. -/
theorem spinToSpecialOrthogonal_surjective_of_isSquare_apply
    (Q : QuadraticForm K V) (hQ : Q.Nondegenerate)
    (hsq : ∀ v, IsSquare (Q v)) :
    Function.Surjective (spinToSpecialOrthogonal Q) := by
  rw [← MonoidHom.range_eq_top]
  rw [range_spinToSpecialOrthogonal_eq_ker_spinorNorm Q hQ]
  rw [Subgroup.eq_top_iff']
  intro g
  rw [MonoidHom.mem_ker, spinorNorm_apply,
    orthogonalSpinorNorm_eq_detSquareClass_of_isSquare_apply Q hQ hsq]
  rw [QuadraticMap.orthogonalDetSquareClass_apply]
  have hdet : LinearEquiv.det (g : V ≃ₗ[K] V) = 1 :=
    (QuadraticMap.mem_specialOrthogonalGroup_iff.mp g.2).2
  rw [← _root_.QuadraticMap.orthogonalDet_apply,
    _root_.QuadraticMap.orthogonalDet_apply,
    _root_.QuadraticMap.coe_specialOrthogonalToOrthogonal, hdet, map_one]

end CliffordAlgebra
