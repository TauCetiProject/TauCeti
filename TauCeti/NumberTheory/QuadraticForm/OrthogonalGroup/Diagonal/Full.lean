/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.QuadraticForm.OrthogonalGroup.Diagonal.Finite
public import TauCeti.NumberTheory.QuadraticForm.OrthogonalGroup.FullAdelic

/-!
# Rational diagonal points in the full adelic orthogonal groups

The rational diagonal in the full adelic point group retains both the real scalar extension
and the finite adelic diagonal. This file constructs those embeddings for `O`, `SO`, and `Spin`,
with their coordinate formulas, injectivity, and compatibility with `Spin → SO → O`.

The finite projection recovers the existing finite diagonal. In particular, adding the real
place does not change the finite-place integrality conditions. No nondegeneracy or nonzero
rank assumption is needed. These are the embeddings whose images are studied when discussing
discreteness of rational points in the full adeles; no discreteness in the finite adeles is
asserted here.

The construction uses `MonoidHom.prod` and the finite diagonals assembled by
`TauCeti.rationalDiagonal`.

## References

* O. T. O'Meara, *Introduction to Quadratic Forms* (1963), §101.
* A. Weil, *Adeles and Algebraic Groups* (1982), Chapter I.
-/

public section

namespace TauCeti
namespace QuadraticMap
namespace OrthogonalCompactOpens

open _root_.QuadraticMap

noncomputable section

variable {V : Type*} [AddCommGroup V] [Module ℚ V]
  {Q : QuadraticForm ℚ V} (U : OrthogonalCompactOpens Q)

/-- The rational diagonal in full adelic `O`, extending scalars at the real place and at
all finite places. -/
def fullAdelicOrthogonalDiagonal : orthogonalGroup Q →* U.fullAdelicOrthogonal :=
  (orthogonalGroupBaseChange (A := ℝ) Q).prod U.finiteAdelicOrthogonalDiagonal

/-- The real and finite components of the full orthogonal diagonal. -/
@[simp]
theorem fullAdelicOrthogonalDiagonal_apply (g : orthogonalGroup Q) :
    U.fullAdelicOrthogonalDiagonal g =
      (orthogonalGroupBaseChange (A := ℝ) Q g, U.finiteAdelicOrthogonalDiagonal g) :=
  MonoidHom.prod_apply _ _ g

/-- Forgetting the real place recovers the finite orthogonal diagonal. -/
@[simp]
theorem fullAdelicOrthogonalToFinite_comp_fullAdelicOrthogonalDiagonal :
    U.fullAdelicOrthogonalToFinite.comp U.fullAdelicOrthogonalDiagonal =
      U.finiteAdelicOrthogonalDiagonal := by
  ext g : 1
  simp

/-- The full adelic orthogonal diagonal is injective. -/
theorem fullAdelicOrthogonalDiagonal_injective :
    Function.Injective U.fullAdelicOrthogonalDiagonal := by
  intro g h hgh
  apply U.finiteAdelicOrthogonalDiagonal_injective
  exact congrArg Prod.snd hgh

/-- The rational diagonal in full adelic `Spin`, with no integrality condition at the real
place. -/
def fullAdelicSpinDiagonal : spinGroup Q →* U.fullAdelicSpin :=
  (CliffordAlgebra.spinGroupBaseChange (A := ℝ) Q).prod U.finiteAdelicSpinDiagonal

/-- The real and finite components of the full Spin diagonal. -/
@[simp]
theorem fullAdelicSpinDiagonal_apply (x : spinGroup Q) :
    U.fullAdelicSpinDiagonal x =
      (CliffordAlgebra.spinGroupBaseChange (A := ℝ) Q x, U.finiteAdelicSpinDiagonal x) :=
  MonoidHom.prod_apply _ _ x

/-- Forgetting the real place recovers the finite Spin diagonal. -/
@[simp]
theorem fullAdelicSpinToFinite_comp_fullAdelicSpinDiagonal :
    U.fullAdelicSpinToFinite.comp U.fullAdelicSpinDiagonal = U.finiteAdelicSpinDiagonal := by
  ext x : 1
  simp

/-- The full adelic Spin diagonal is injective. -/
theorem fullAdelicSpinDiagonal_injective :
    Function.Injective U.fullAdelicSpinDiagonal := by
  intro x y hxy
  apply U.finiteAdelicSpinDiagonal_injective
  exact congrArg Prod.snd hxy

variable [FiniteDimensional ℚ V]

/-- The rational diagonal in full adelic `SO`. The finite-place integrality condition is
derived from that for `O`. -/
def fullAdelicSpecialOrthogonalDiagonal :
    specialOrthogonalGroup Q →* U.fullAdelicSpecialOrthogonal :=
  (specialOrthogonalGroupBaseChange (A := ℝ) Q).prod U.finiteAdelicSpecialOrthogonalDiagonal

/-- The real and finite components of the full special orthogonal diagonal. -/
@[simp]
theorem fullAdelicSpecialOrthogonalDiagonal_apply (g : specialOrthogonalGroup Q) :
    U.fullAdelicSpecialOrthogonalDiagonal g =
      (specialOrthogonalGroupBaseChange (A := ℝ) Q g,
        U.finiteAdelicSpecialOrthogonalDiagonal g) :=
  MonoidHom.prod_apply _ _ g

/-- Forgetting the real place recovers the finite special orthogonal diagonal. -/
@[simp]
theorem fullAdelicSpecialOrthogonalToFinite_comp_fullAdelicSpecialOrthogonalDiagonal :
    U.fullAdelicSpecialOrthogonalToFinite.comp U.fullAdelicSpecialOrthogonalDiagonal =
      U.finiteAdelicSpecialOrthogonalDiagonal := by
  ext g : 1
  simp

/-- The full adelic special orthogonal diagonal is injective. -/
theorem fullAdelicSpecialOrthogonalDiagonal_injective :
    Function.Injective U.fullAdelicSpecialOrthogonalDiagonal := by
  intro g h hgh
  apply U.finiteAdelicSpecialOrthogonalDiagonal_injective
  exact congrArg Prod.snd hgh

/-- The two routes from rational `Spin` to full adelic `SO`, through the rational projection
or through the full adelic projection, agree. -/
theorem fullAdelicSpinToSpecialOrthogonal_comp_fullAdelicSpinDiagonal :
    U.fullAdelicSpinToSpecialOrthogonal.comp U.fullAdelicSpinDiagonal =
      U.fullAdelicSpecialOrthogonalDiagonal.comp (CliffordAlgebra.spinToSpecialOrthogonal Q) := by
  ext x : 1
  simp only [MonoidHom.comp_apply, fullAdelicSpinToSpecialOrthogonal_apply,
    fullAdelicSpinDiagonal_apply, fullAdelicSpecialOrthogonalDiagonal_apply,
    finiteAdelicSpinToSpecialOrthogonal_finiteAdelicSpinDiagonal]
  apply Prod.ext
  · have h := CliffordAlgebra.spinToSpecialOrthogonal_baseChange (A := ℝ) Q x
    -- The base-change theorem transports the inverse of two; the real carrier uses its
    -- canonical instance. Uniqueness identifies these instances.
    rw [Subsingleton.elim ((Invertible.map (algebraMap ℚ ℝ) 2).copy 2 (map_ofNat _ _).symm)
      (inferInstance : Invertible (2 : ℝ))] at h
    exact h.symm
  · rfl

/-- The full adelic inclusion `SO → O` commutes with the rational diagonals. -/
theorem fullAdelicSpecialOrthogonalToOrthogonal_comp_fullAdelicSpecialOrthogonalDiagonal :
    U.fullAdelicSpecialOrthogonalToOrthogonal.comp U.fullAdelicSpecialOrthogonalDiagonal =
      U.fullAdelicOrthogonalDiagonal.comp (specialOrthogonalToOrthogonal Q) := by
  ext g : 1
  simp only [MonoidHom.comp_apply, fullAdelicSpecialOrthogonalToOrthogonal_apply,
    fullAdelicSpecialOrthogonalDiagonal_apply, fullAdelicOrthogonalDiagonal_apply,
    specialOrthogonalToOrthogonal_specialOrthogonalGroupBaseChange,
    finiteAdelicSpecialOrthogonalToOrthogonal_finiteAdelicSpecialOrthogonalDiagonal]

end

end OrthogonalCompactOpens
end QuadraticMap
end TauCeti
