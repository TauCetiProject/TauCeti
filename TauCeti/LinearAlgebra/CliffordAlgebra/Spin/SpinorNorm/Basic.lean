/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.Lipschitz.Kernel
public import TauCeti.LinearAlgebra.CliffordAlgebra.Lipschitz.ReverseNorm
public import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.SpecialOrthogonal
public import TauCeti.FieldTheory.SquareClassGroup.Basic
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
* `CliffordAlgebra.orthogonalSpinorNorm_eq_one_of_isSquare_apply`: when every invertible value of
  the form is a square, the orthogonal spinor norm is trivial.
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
theorem isSquare_cliffordNorm_of_mem_ker (Q : QuadraticForm K V) (hQ : Q.Nondegenerate)
    (x : lipschitzGroup Q) (hx : x ∈ MonoidHom.ker (lipschitzToOrthogonal Q)) :
    IsSquare (cliffordNorm Q x) := by
  obtain ⟨r, hr⟩ := (mem_ker_lipschitzToOrthogonal_iff hQ).mp hx
  refine ⟨r, ?_⟩
  have hnorm := cliffordNorm_eq_sq_mul_of_coe_eq_algebraMap_mul
    (x := 1) (y := x) (c := r) (by simpa using hr)
  simpa only [map_one, mul_one, pow_two] using
    hnorm

private noncomputable def cliffordSquareClassHom (Q : QuadraticForm K V) :
    lipschitzGroup Q →* Multiplicative (SquareClassGroup K) :=
  squareClassHom.comp (cliffordNorm Q)

private theorem ker_lipschitzToOrthogonal_le_ker_cliffordSquareClassHom
    (Q : QuadraticForm K V) (hQ : Q.Nondegenerate) :
    MonoidHom.ker (lipschitzToOrthogonal Q) ≤ MonoidHom.ker (cliffordSquareClassHom Q) := by
  intro x hx
  rw [MonoidHom.mem_ker]
  simpa [cliffordSquareClassHom] using isSquare_cliffordNorm_of_mem_ker Q hQ x hx

private noncomputable def spinorNormDescentData (Q : QuadraticForm K V) (hQ : Q.Nondegenerate) :
    {g : lipschitzGroup Q →* Multiplicative (SquareClassGroup K) //
      MonoidHom.ker (lipschitzToOrthogonal Q) ≤ MonoidHom.ker g} :=
  ⟨cliffordSquareClassHom Q,
    ker_lipschitzToOrthogonal_le_ker_cliffordSquareClassHom Q hQ⟩

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
      squareClassHom (cliffordNorm Q x) := by
  simpa only [orthogonalSpinorNorm, MonoidHom.liftOfSurjective, spinorNormDescentData,
    cliffordSquareClassHom, MonoidHom.comp_apply] using
    MonoidHom.liftOfRightInverse_comp_apply
      (G₃ := Multiplicative (SquareClassGroup K))
      (lipschitzToOrthogonal Q)
      (Function.surjInv (lipschitzToOrthogonal_surjective_of_invertible Q hQ))
      (Function.rightInverse_surjInv (lipschitzToOrthogonal_surjective_of_invertible Q hQ))
      (spinorNormDescentData Q hQ) x

/-- The spinor norm of an orthogonal reflection is the square class of the norm of its
defining vector. -/
@[simp]
theorem orthogonalSpinorNorm_reflectionOrthogonal (Q : QuadraticForm K V)
    (hQ : Q.Nondegenerate)
    (v : V) [Invertible (Q v)] :
    orthogonalSpinorNorm Q hQ (QuadraticMap.reflectionOrthogonal Q v) =
      squareClassHom (unitOfInvertible (Q v)) := by
  rw [← lipschitzToOrthogonal_unitι Q v, orthogonalSpinorNorm_lipschitzToOrthogonal,
    cliffordNorm_unitι]

/-- If every invertible value of a finite-dimensional nondegenerate quadratic form is a square,
its orthogonal spinor norm is trivial. -/
theorem orthogonalSpinorNorm_eq_one_of_isSquare_apply
    (Q : QuadraticForm K V) (hQ : Q.Nondegenerate)
    (hsq : ∀ v [Invertible (Q v)], IsSquare (Q v)) :
    orthogonalSpinorNorm Q hQ = 1 := by
  have hker : MonoidHom.ker (orthogonalSpinorNorm Q hQ) = ⊤ :=
    QuadraticMap.subgroup_eq_top_of_reflection_mem Q hQ
      (MonoidHom.ker (orthogonalSpinorNorm Q hQ)) fun v _ => by
        rw [MonoidHom.mem_ker, orthogonalSpinorNorm_reflectionOrthogonal]
        have hsquareUnit : IsSquare (unitOfInvertible (Q v)) := by
          apply isSquare_units_val_iff.mp
          simpa only [val_unitOfInvertible] using hsq v
        simpa using hsquareUnit
  apply MonoidHom.ext
  intro g
  rw [MonoidHom.one_apply]
  apply MonoidHom.mem_ker.mp
  rw [hker]
  exact Subgroup.mem_top g

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
    cliffordNorm_pinToLipschitz_spinToPin, map_one]

private theorem exists_spinToSpecialOrthogonal_eq_of_spinorNorm_eq_one [Nontrivial V]
    (Q : QuadraticForm K V) (hQ : Q.Nondegenerate)
    (g : QuadraticMap.specialOrthogonalGroup Q) (hg : spinorNorm Q hQ g = 1) :
    ∃ s : spinGroup Q, spinToSpecialOrthogonal Q s = g := by
  obtain ⟨x, hx⟩ := lipschitzToOrthogonal_surjective_of_invertible Q hQ
    (_root_.QuadraticMap.specialOrthogonalToOrthogonal Q g)
  have hsquare : IsSquare (cliffordNorm Q x) := by
    have hsquareClass : squareClassHom (cliffordNorm Q x) = 1 := by
      rw [← orthogonalSpinorNorm_lipschitzToOrthogonal Q hQ, hx,
        ← spinorNorm_apply, hg]
    simpa using hsquareClass
  obtain ⟨a, ha⟩ := hsquare
  have hv : ∃ v, IsUnit (Q v) := hQ.exists_isUnit
  let y : lipschitzGroup Q := scalarUnits Q hv a⁻¹ * x
  have hynorm : cliffordNorm Q y = 1 := by
    dsimp only [y]
    rw [map_mul, cliffordNorm_scalarUnits, ha]
    simp
  have hyact : lipschitzToOrthogonal Q y =
      _root_.QuadraticMap.specialOrthogonalToOrthogonal Q g := by
    dsimp only [y]
    rw [map_mul, lipschitzToOrthogonal_scalarUnits, hx, one_mul]
  have hyeven : ((y : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) ∈ even Q :=
    mem_even_of_det_lipschitzToOrthogonal_eq_one Q y (by
      rw [hyact]
      exact _root_.QuadraticMap.orthogonalDet_specialOrthogonalToOrthogonal g)
  have hyspin : ((y : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) ∈ spinGroup Q :=
    (mem_spinGroup_iff_mem_even_and_cliffordNorm_eq_one y).2 ⟨hyeven, hynorm⟩
  let s : spinGroup Q := ⟨((y : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q), hyspin⟩
  refine ⟨s, ?_⟩
  have hsl : pinToLipschitz Q (spinToPin Q s) = y := by
    apply Subtype.ext
    apply Units.ext
    rw [coe_pinToLipschitz_apply, coe_spinToPin_apply]
  apply _root_.QuadraticMap.specialOrthogonalToOrthogonal_injective
  rw [specialOrthogonalToOrthogonal_spinToSpecialOrthogonal,
    ← pinToOrthogonal_spinToPin, pinToOrthogonal_eq_lipschitzToOrthogonal, hsl, hyact]

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
    exact exists_spinToSpecialOrthogonal_eq_of_spinorNorm_eq_one Q hQ g
      (MonoidHom.mem_ker.mp hg)

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

/-- If every invertible value of a finite-dimensional nondegenerate quadratic form is a square,
the Spin action on its special orthogonal group is surjective. This differs from
`spinToSpecialOrthogonal_surjective_of_isSquare`, which assumes that `-⅟(Q v)` is a square. -/
theorem spinToSpecialOrthogonal_surjective_of_isSquare_apply
    (Q : QuadraticForm K V) (hQ : Q.Nondegenerate)
    (hsq : ∀ v [Invertible (Q v)], IsSquare (Q v)) :
    Function.Surjective (spinToSpecialOrthogonal Q) := by
  rw [← MonoidHom.range_eq_top]
  rw [range_spinToSpecialOrthogonal_eq_ker_spinorNorm Q hQ]
  rw [Subgroup.eq_top_iff']
  intro g
  rw [MonoidHom.mem_ker, spinorNorm_apply,
    orthogonalSpinorNorm_eq_one_of_isSquare_apply Q hQ hsq]
  rfl

end CliffordAlgebra
