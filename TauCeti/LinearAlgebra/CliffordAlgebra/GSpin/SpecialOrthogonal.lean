/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.CartanDieudonne
public import TauCeti.LinearAlgebra.CliffordAlgebra.GSpin.Basic
public import TauCeti.LinearAlgebra.CliffordAlgebra.Lipschitz.Kernel
public import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.SpecialOrthogonal

/-!
# The general spin group as a central extension of the special orthogonal group

An element `x` of the general spin group `GSpin(Q)` is even, so its twisted-conjugation action on
the quadratic space is the plain conjugation `v ↦ x v x⁻¹`, and it has determinant one. This gives
the *vector action* `GSpin(Q) →* SO(Q)`, the morphism from `GSpin` to `SO` of the theory of split
classical groups. It restricts to the double cover `Spin(Q) →* SO(Q)` and kills the central
cocharacter `e₀∨`.

For a nondegenerate form on a finite-dimensional space over a field in which `2` is invertible,
the vector action is surjective (Cartan–Dieudonné, together with the fact that a Lipschitz
element acting with determinant one is even), and its kernel is exactly the image of the central
cocharacter, provided some vector is anisotropic. So on rational points there is an exact sequence
`1 → Kˣ → GSpin(Q) → SO(Q) → 1`. In particular the vector action does not determine an element of
`GSpin(Q)`: two elements with the same action differ by a scalar unit, and every scalar unit
occurs (`CliffordAlgebra.gSpinToSpecialOrthogonal_eq_iff`). This is the difference with Spin,
whose elements are determined by their action up to sign.

## Main definitions

* `CliffordAlgebra.gSpinToSpecialOrthogonal Q`: the vector action `GSpin(Q) →* SO(Q)`.

## Main results

* `CliffordAlgebra.ι_gSpinToSpecialOrthogonal_apply`: an element of `GSpin(Q)` acts on vectors by
  conjugation.
* `CliffordAlgebra.gSpinToSpecialOrthogonal_spinToGSpin`: restricted to Spin, the vector action is
  the Spin action.
* `CliffordAlgebra.gSpinToSpecialOrthogonal_gSpinScalarUnits`: the central cocharacter acts
  trivially.
* `CliffordAlgebra.gSpinToSpecialOrthogonal_baseChange`: the vector action is compatible with
  extension of scalars.
* `CliffordAlgebra.ker_gSpinToSpecialOrthogonal`: over a field, the kernel of the vector action is
  the image of the central cocharacter.
* `CliffordAlgebra.gSpinToSpecialOrthogonal_surjective`: over a field, the vector action is onto
  `SO(Q)`.
* `CliffordAlgebra.gSpinToSpecialOrthogonal_eq_iff`: over a field, two elements of `GSpin(Q)` have
  the same action exactly when they differ by a scalar unit.

## References

* M. Asgari, *Local L-functions for split spinor groups*, Canad. J. Math. 54 (2002), §2.
* C. Chevalley, *The Algebraic Theory of Spinors* (1954), Chapter II.
-/

public section

universe u v w

namespace CliffordAlgebra

open TauCeti

section CommRing

variable {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M] [Module R M]
  (Q : QuadraticForm R M) [Invertible (2 : R)]

/-- The **vector action** `GSpin(Q) →* SO(Q)` of the general spin group: the twisted-conjugation
action of the Lipschitz group, which on even elements is plain conjugation and has determinant
one. -/
noncomputable def gSpinToSpecialOrthogonal :
    gSpinGroup Q →* QuadraticMap.specialOrthogonalGroup Q :=
  (((QuadraticMap.orthogonalGroup Q).subtype.comp
      ((lipschitzToOrthogonal Q).comp (gSpinToLipschitz Q))).codRestrict
    (QuadraticMap.specialOrthogonalGroup Q) fun x ↦
      QuadraticMap.mem_specialOrthogonalGroup_iff.2
        ⟨(lipschitzToOrthogonal Q (gSpinToLipschitz Q x)).property, by
          simpa using det_lipschitzToOrthogonal_eq_one_of_mem_even Q (gSpinToLipschitz Q x)
            (by rw [coe_gSpinToLipschitz_apply]; exact gSpinGroup.coe_mem_even x)⟩)

variable {Q}

/-- Followed by the inclusion `SO(Q) →* O(Q)`, the vector action of `GSpin(Q)` is the Lipschitz
action. -/
@[simp]
theorem specialOrthogonalToOrthogonal_gSpinToSpecialOrthogonal (x : gSpinGroup Q) :
    _root_.QuadraticMap.specialOrthogonalToOrthogonal Q (gSpinToSpecialOrthogonal Q x) =
      lipschitzToOrthogonal Q (gSpinToLipschitz Q x) :=
  Subtype.ext <| by
    rw [_root_.QuadraticMap.coe_specialOrthogonalToOrthogonal]
    -- The underlying linear equivalence of a codomain restriction is the unrestricted value.
    rfl

/-- The underlying action of an element of `GSpin(Q)` is its Lipschitz action. -/
@[simp]
theorem coe_gSpinToSpecialOrthogonal_apply (x : gSpinGroup Q) (m : M) :
    ((gSpinToSpecialOrthogonal Q x : QuadraticMap.specialOrthogonalGroup Q) : M ≃ₗ[R] M) m =
      lipschitzVectorAction Q (gSpinToLipschitz Q x) m := by
  rw [← _root_.QuadraticMap.coe_specialOrthogonalToOrthogonal,
    specialOrthogonalToOrthogonal_gSpinToSpecialOrthogonal, coe_lipschitzToOrthogonal_apply]

/-- **An element of `GSpin(Q)` acts on vectors by conjugation**: `ι (x • m) = x * ι m * x⁻¹`.
The grade involution in the twisted conjugation disappears because `x` is even. -/
theorem ι_gSpinToSpecialOrthogonal_apply (x : gSpinGroup Q) (m : M) :
    ι Q (((gSpinToSpecialOrthogonal Q x : QuadraticMap.specialOrthogonalGroup Q) :
        M ≃ₗ[R] M) m) =
      ((x : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) * ι Q m *
        (((x : (CliffordAlgebra Q)ˣ)⁻¹ : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) := by
  have hx := gSpinGroup.coe_mem_even x
  rw [← Subalgebra.mem_toSubmodule, even_toSubmodule] at hx
  rw [coe_gSpinToSpecialOrthogonal_apply, ι_lipschitzVectorAction_apply,
    coe_gSpinToLipschitz_apply, involute_eq_of_mem_even hx]

/-- **Restricted to Spin, the vector action of `GSpin(Q)` is the Spin action.** -/
@[simp]
theorem gSpinToSpecialOrthogonal_spinToGSpin (x : spinGroup Q) :
    gSpinToSpecialOrthogonal Q (spinToGSpin Q x) = spinToSpecialOrthogonal Q x := by
  apply _root_.QuadraticMap.specialOrthogonalToOrthogonal_injective
  rw [specialOrthogonalToOrthogonal_gSpinToSpecialOrthogonal,
    specialOrthogonalToOrthogonal_spinToSpecialOrthogonal, gSpinToLipschitz_spinToGSpin,
    spinToLipschitz_apply, ← pinToOrthogonal_eq_lipschitzToOrthogonal, pinToOrthogonal_spinToPin]

/-- The vector action of `GSpin(Q)`, restricted along the inclusion of Spin, is the Spin
action. -/
theorem gSpinToSpecialOrthogonal_comp_spinToGSpin :
    (gSpinToSpecialOrthogonal Q).comp (spinToGSpin Q) = spinToSpecialOrthogonal Q :=
  MonoidHom.ext gSpinToSpecialOrthogonal_spinToGSpin

/-- **The central cocharacter acts trivially.** -/
@[simp]
theorem gSpinToSpecialOrthogonal_gSpinScalarUnits (hQ : ∃ v, IsUnit (Q v)) (a : Rˣ) :
    gSpinToSpecialOrthogonal Q (gSpinScalarUnits Q hQ a) = 1 := by
  apply _root_.QuadraticMap.specialOrthogonalToOrthogonal_injective
  rw [specialOrthogonalToOrthogonal_gSpinToSpecialOrthogonal, gSpinToLipschitz_gSpinScalarUnits,
    lipschitzToOrthogonal_scalarUnits, map_one]

/-- The image of the central cocharacter lies in the kernel of the vector action. -/
theorem range_gSpinScalarUnits_le_ker_gSpinToSpecialOrthogonal (hQ : ∃ v, IsUnit (Q v)) :
    (gSpinScalarUnits Q hQ).range ≤ (gSpinToSpecialOrthogonal Q).ker := by
  rintro _ ⟨a, rfl⟩
  exact gSpinToSpecialOrthogonal_gSpinScalarUnits hQ a

end CommRing

/-! ### Extension of scalars -/

section BaseChange

open scoped TensorProduct

variable {R : Type u} {A : Type w} {M : Type v} [CommRing R] [CommRing A] [Algebra R A]
  [AddCommGroup M] [Module R M] [Module.Free R M] [Module.Finite R M] [Invertible (2 : R)]
  [Invertible (2 : A)]

/-- **Extension of scalars commutes with the vector action of `GSpin`.** -/
@[simp]
theorem gSpinToSpecialOrthogonal_baseChange (Q : QuadraticForm R M) (x : gSpinGroup Q) :
    TauCeti.QuadraticMap.specialOrthogonalGroupBaseChange (A := A) Q
        (gSpinToSpecialOrthogonal Q x) =
      gSpinToSpecialOrthogonal (Q.baseChange A) (gSpinGroupBaseChange (A := A) Q x) := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro z
  induction z using TensorProduct.inductionOn with
  | tmul a m =>
      rw [TauCeti.QuadraticMap.specialOrthogonalGroupBaseChange_apply_tmul,
        coe_gSpinToSpecialOrthogonal_apply, coe_gSpinToSpecialOrthogonal_apply,
        gSpinToLipschitz_gSpinGroupBaseChange]
      -- The Lipschitz lemma uses its own `Invertible (2 : A)` instance; any two agree.
      convert (lipschitzVectorAction_baseChange_tmul Q (gSpinToLipschitz Q x) a m).symm
      exact Subsingleton.elim _ _
  | add z w hz hw => simp only [map_add, hz, hw]

end BaseChange

/-! ### The exact sequence over a field -/

section Field

variable {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  [Invertible (2 : K)] {Q : QuadraticForm K V}

/-- **The kernel of the vector action of `GSpin(Q)` is the image of the central cocharacter**, for
a nondegenerate form on a finite-dimensional space over a field in which `2` is invertible,
provided some vector is anisotropic (so that the central cocharacter is defined). -/
theorem ker_gSpinToSpecialOrthogonal (hQ : Q.Nondegenerate) (hv : ∃ v, IsUnit (Q v)) :
    (gSpinToSpecialOrthogonal Q).ker = (gSpinScalarUnits Q hv).range := by
  refine le_antisymm (fun x hx ↦ ?_) (range_gSpinScalarUnits_le_ker_gSpinToSpecialOrthogonal hv)
  have hx' : gSpinToLipschitz Q x ∈ (lipschitzToOrthogonal Q).ker := by
    rw [MonoidHom.mem_ker, ← specialOrthogonalToOrthogonal_gSpinToSpecialOrthogonal,
      MonoidHom.mem_ker.1 hx, map_one]
  rw [ker_lipschitzToOrthogonal hQ hv] at hx'
  obtain ⟨a, ha⟩ := hx'
  exact ⟨a, gSpinToLipschitz_injective Q (by rw [gSpinToLipschitz_gSpinScalarUnits, ha])⟩

/-- **The vector action of `GSpin(Q)` is onto `SO(Q)`**, for a nondegenerate form on a
finite-dimensional space over a field in which `2` is invertible: by Cartan–Dieudonné a
determinant-one isometry is the action of a Lipschitz element, and that element is even. -/
theorem gSpinToSpecialOrthogonal_surjective (hQ : Q.Nondegenerate) :
    Function.Surjective (gSpinToSpecialOrthogonal Q) := by
  intro g
  obtain ⟨y, hy⟩ := lipschitzToOrthogonal_surjective Q hQ
    (_root_.QuadraticMap.specialOrthogonalToOrthogonal Q g)
  have heven : ((y : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) ∈ even Q :=
    mem_even_of_det_lipschitzToOrthogonal_eq_one Q y <| by
      rw [hy, _root_.QuadraticMap.orthogonalDet_specialOrthogonalToOrthogonal]
  refine ⟨⟨y, mem_gSpinGroup_iff.2 ⟨y.property, heven⟩⟩,
    _root_.QuadraticMap.specialOrthogonalToOrthogonal_injective ?_⟩
  rw [specialOrthogonalToOrthogonal_gSpinToSpecialOrthogonal, ← hy]
  exact congrArg _ (Subtype.ext (coe_gSpinToLipschitz_apply Q _))

/-- **Two elements of `GSpin(Q)` have the same vector action exactly when they differ by a scalar
unit**, for a nondegenerate form on a finite-dimensional space over a field in which `2` is
invertible and some vector is anisotropic. -/
theorem gSpinToSpecialOrthogonal_eq_iff (hQ : Q.Nondegenerate) (hv : ∃ v, IsUnit (Q v))
    {x y : gSpinGroup Q} :
    gSpinToSpecialOrthogonal Q x = gSpinToSpecialOrthogonal Q y ↔
      ∃ a : Kˣ, x = gSpinScalarUnits Q hv a * y := by
  rw [MonoidHom.eq_iff, ker_gSpinToSpecialOrthogonal hQ hv]
  refine exists_congr fun a ↦ ?_
  rw [eq_inv_mul_iff_mul_eq, Subgroup.mem_center_iff.1 (gSpinScalarUnits_mem_center hv a) y]
  exact eq_comm

end Field

end CliffordAlgebra
