/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.SpinorNorm.Basic
public import TauCeti.LinearAlgebra.QuadraticForm.DetSquareClass
import TauCeti.LinearAlgebra.CliffordAlgebra.CartanDieudonne
import TauCeti.LinearAlgebra.CliffordAlgebra.Pin.Norm

/-!
# The image of the Pin group

Mathlib's Pin group consists of the Lipschitz elements `x` with `star x * x = 1`, where
`star = reverse ∘ involute` is the Clifford conjugation. Its `star` norm `lipschitzNorm` takes the
value `-Q v` on a vector `v`, while the reverse norm `cliffordNorm`, whose square class descends to
the spinor norm `orthogonalSpinorNorm` on `O(Q)`, takes the value `Q v`. The two norms agree on
even elements and differ by a sign on odd ones, and the parity of a Lipschitz element is recorded by
the determinant of its action. So the square class of the `star` norm of a Lipschitz element `x`
acting by `g` is the product of the spinor norm of `g` and the square class of `det g`
(`CliffordAlgebra.squareClassHom_lipschitzNorm`).

A Lipschitz element rescales by a scalar into the Pin group exactly when its `star` norm is a
square, and rescaling does not change its action. Hence, for a finite-dimensional nondegenerate
quadratic space over a field in which `2` is invertible, the image of the Pin group in `O(Q)` is
exactly the kernel of the character `g ↦ θ(g) · [det g]`, where `θ` is the spinor norm. Over `ℝ`
the square classes are the signs, and this is the kernel of the norm-sign character. On a
reflection `τ_v` the character takes the value `[-Q v]`, so `τ_v` lies in the image of the Pin
group exactly when `-Q v` is a square.

## Main results

* `CliffordAlgebra.squareClassHom_lipschitzNorm`: the square class of the `star` norm of a
  Lipschitz element is the spinor norm times the determinant square class of its action.
* `CliffordAlgebra.range_pinToOrthogonal`: the image of the Pin group is the kernel of the
  spinor norm times the determinant square class.
* `CliffordAlgebra.orthogonalSpinorNorm_mul_orthogonalDetSquareClass_reflectionOrthogonal`: the
  character `g ↦ θ(g) · [det g]` takes the value `[-Q v]` on a reflection `τ_v`.
* `CliffordAlgebra.reflectionOrthogonal_mem_range_pinToOrthogonal_iff`: a reflection `τ_v` is
  the action of a Pin element exactly when `-Q v` is a square.

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I §2.
* O. T. O'Meara, *Introduction to Quadratic Forms*, §55.
-/

public section

open QuadraticMap

namespace CliffordAlgebra

open TauCeti

universe u v

variable {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Invertible (2 : K)]

/-- The square class of the `star` norm of a Lipschitz element acting trivially is trivial: the
element is a scalar `r`, whose norm is `r * r`. -/
private theorem ker_lipschitzToOrthogonal_le_ker_squareClassHom_comp_lipschitzNorm
    (Q : QuadraticForm K V) (hQ : Q.Nondegenerate) :
    (lipschitzToOrthogonal Q).ker ≤ (squareClassHom.comp (lipschitzNorm Q)).ker := by
  intro x hx
  obtain ⟨r, hr⟩ := (mem_ker_lipschitzToOrthogonal_iff hQ).mp hx
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply, lipschitzNorm_eq_of_coe_eq_algebraMap hr,
    squareClassHom_eq_one_iff]
  exact ⟨r, rfl⟩

/-- The square class of the `star` norm, descended through the Lipschitz action to `O(Q)`. It is
identified with `orthogonalSpinorNorm Q hQ * orthogonalDetSquareClass Q` below. -/
private noncomputable def orthogonalStarNormClass (Q : QuadraticForm K V)
    (hQ : Q.Nondegenerate) :
    QuadraticMap.orthogonalGroup Q →* (Kˣ ⧸ Subgroup.square Kˣ) :=
  MonoidHom.liftOfSurjective (G₃ := (Kˣ ⧸ Subgroup.square Kˣ))
    (lipschitzToOrthogonal Q) (lipschitzToOrthogonal_surjective Q hQ)
    ⟨squareClassHom.comp (lipschitzNorm Q),
      ker_lipschitzToOrthogonal_le_ker_squareClassHom_comp_lipschitzNorm Q hQ⟩

private theorem orthogonalStarNormClass_lipschitzToOrthogonal (Q : QuadraticForm K V)
    (hQ : Q.Nondegenerate) (x : lipschitzGroup Q) :
    orthogonalStarNormClass Q hQ (lipschitzToOrthogonal Q x) =
      squareClassHom (lipschitzNorm Q x) :=
  MonoidHom.liftOfRightInverse_comp_apply (G₃ := (Kˣ ⧸ Subgroup.square Kˣ))
    (lipschitzToOrthogonal Q)
    (Function.surjInv (lipschitzToOrthogonal_surjective Q hQ))
    (Function.rightInverse_surjInv (lipschitzToOrthogonal_surjective Q hQ)) _ x

/-- **The norm-sign character on a reflection.** The spinor norm times the determinant square
class takes the value `[-Q v]` on the reflection `τ_v` in an anisotropic vector `v`. -/
theorem orthogonalSpinorNorm_mul_orthogonalDetSquareClass_reflectionOrthogonal
    (Q : QuadraticForm K V) (hQ : Q.Nondegenerate) (v : V) [Invertible (Q v)] :
    (orthogonalSpinorNorm Q hQ * orthogonalDetSquareClass Q)
        (QuadraticMap.reflectionOrthogonal Q v) =
      squareClassHom (-unitOfInvertible (Q v)) := by
  rw [MonoidHom.mul_apply, orthogonalSpinorNorm_reflectionOrthogonal,
    orthogonalDetSquareClass_apply, QuadraticMap.coe_reflectionOrthogonal,
    QuadraticMap.det_reflection, ← map_mul, mul_neg_one]

/-- On a reflection `τ_v` both characters take the value `[-Q v]`. -/
private theorem orthogonalStarNormClass_eq (Q : QuadraticForm K V) (hQ : Q.Nondegenerate) :
    orthogonalStarNormClass Q hQ = orthogonalSpinorNorm Q hQ * orthogonalDetSquareClass Q := by
  refine QuadraticMap.orthogonalGroup_hom_ext Q hQ fun v _ ↦ ?_
  rw [orthogonalSpinorNorm_mul_orthogonalDetSquareClass_reflectionOrthogonal,
    ← lipschitzToOrthogonal_unitι, orthogonalStarNormClass_lipschitzToOrthogonal,
    lipschitzNorm_unitι]

/-- **The `star` norm modulo squares.** The square class of the `star` norm `star x * x` of a
Lipschitz element `x` is the spinor norm of its action times the square class of the determinant of
its action. -/
theorem squareClassHom_lipschitzNorm (Q : QuadraticForm K V) (hQ : Q.Nondegenerate)
    (x : lipschitzGroup Q) :
    squareClassHom (lipschitzNorm Q x) =
      orthogonalSpinorNorm Q hQ (lipschitzToOrthogonal Q x) *
        orthogonalDetSquareClass Q (lipschitzToOrthogonal Q x) := by
  rw [← orthogonalStarNormClass_lipschitzToOrthogonal Q hQ, orthogonalStarNormClass_eq,
    MonoidHom.mul_apply]

/-- **The image of the Pin group** of a finite-dimensional nondegenerate quadratic space over a
field in which `2` is invertible is the kernel of the spinor norm times the determinant square
class. Over `ℝ` this is the kernel of the norm-sign character. -/
theorem range_pinToOrthogonal (Q : QuadraticForm K V) (hQ : Q.Nondegenerate) :
    (pinToOrthogonal Q).range = (orthogonalSpinorNorm Q hQ * orthogonalDetSquareClass Q).ker := by
  ext g
  rw [MonoidHom.mem_ker, MonoidHom.mul_apply]
  constructor
  · rintro ⟨p, rfl⟩
    rw [pinToOrthogonal_eq_lipschitzToOrthogonal, ← squareClassHom_lipschitzNorm Q hQ,
      lipschitzNorm_pinToLipschitz, map_one]
  · intro hg
    obtain ⟨x, rfl⟩ := lipschitzToOrthogonal_surjective Q hQ g
    rw [← squareClassHom_lipschitzNorm Q hQ, squareClassHom_eq_one_iff] at hg
    obtain ⟨b, hb⟩ := hg
    rcases subsingleton_or_nontrivial V with hV | hV
    · exact ⟨1, Subtype.ext (LinearEquiv.ext fun v ↦ Subsingleton.elim _ _)⟩
    let y : lipschitzGroup Q := scalarUnits Q hQ.exists_isUnit b⁻¹ * x
    have hy : ((y : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) ∈ pinGroup Q := by
      rw [mem_pinGroup_iff_lipschitzNorm_eq_one, map_mul, lipschitzNorm_scalarUnits, hb]
      group
    refine ⟨⟨_, hy⟩, ?_⟩
    have hyx : pinToLipschitz Q ⟨_, hy⟩ = y :=
      Subtype.ext (Units.ext (coe_pinToLipschitz_apply Q _))
    rw [pinToOrthogonal_eq_lipschitzToOrthogonal, hyx, map_mul, lipschitzToOrthogonal_scalarUnits,
      one_mul]

/-- **Reflections in the image of the Pin group.** The reflection in an anisotropic vector `v` is
the action of an element of the Pin group exactly when `-Q v` is a square. -/
theorem reflectionOrthogonal_mem_range_pinToOrthogonal_iff (Q : QuadraticForm K V)
    (hQ : Q.Nondegenerate) (v : V) [Invertible (Q v)] :
    QuadraticMap.reflectionOrthogonal Q v ∈ (pinToOrthogonal Q).range ↔
      IsSquare (-unitOfInvertible (Q v)) := by
  rw [range_pinToOrthogonal Q hQ, MonoidHom.mem_ker,
    orthogonalSpinorNorm_mul_orthogonalDetSquareClass_reflectionOrthogonal,
    squareClassHom_eq_one_iff]

end CliffordAlgebra
