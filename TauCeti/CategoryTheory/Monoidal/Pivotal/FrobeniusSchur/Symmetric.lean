/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Linear.Basic
public import TauCeti.CategoryTheory.Monoidal.Pivotal.FrobeniusSchur.Basic
public import TauCeti.CategoryTheory.Monoidal.Pivotal.Symmetric

/-!
# Frobenius–Schur rotation in symmetric rigid categories

In a symmetric rigid category `C` equipped with its canonical spherical structure
(`TauCeti.symmetricPivotalCategory`), rotating a morphism `f : 𝟙_ C ⟶ X ⊗ Y` with
`TauCeti.pivotalRotate` simply postcomposes `f` with the braiding `(β_ X Y).hom`
(`TauCeti.pivotalRotate_eq_braiding`): by Frobenius reciprocity every such `f` factors through the
coevaluation `η_ X Xᘁ`, whose rotation is `η_ X Xᘁ ≫ (β_ X Xᘁ).hom`.

Consequently, the Ng–Schauenburg operator `TauCeti.frobeniusSchurRotate V n` on
`𝟙_ C ⟶ tensorPow V (n + 1)` is postcomposition with the cyclic shift
`TauCeti.tensorPowShiftIso V n` (`TauCeti.frobeniusSchurRotate_eq_comp_tensorPowShiftIso_hom`), and
`TauCeti.frobeniusSchurEnd k V n` equals
`CategoryTheory.Linear.rightComp k (𝟙_ C) (tensorPowShiftIso V n).hom`
(`TauCeti.frobeniusSchurEnd_eq_rightComp`).

## Main declarations

* `TauCeti.pivotalRotate_eq_braiding`: in a symmetric rigid category,
  `pivotalRotate f = f ≫ (β_ X Y).hom`;
* `TauCeti.frobeniusSchurRotate_eq_comp_tensorPowShiftIso_hom`,
  `TauCeti.frobeniusSchurEnd_eq_rightComp`, and
  `TauCeti.frobeniusSchurIndicator_eq_trace_rightComp`: `E_V^{(n+1)}` is postcomposition with the
  cyclic shift `tensorPowShiftIso V n`, so `ν_n(V)` is the trace of postcomposition with
  `tensorPowShiftIso V n.natPred`.

## References

* S.-H. Ng, P. Schauenburg, *Higher Frobenius–Schur indicators for pivotal categories*, in
  *Hopf algebras and generalizations*, Contemp. Math. **441** (2007), 63–90, §§4–5
* [P. Etingof, S. Gelaki, D. Nikshych, V. Ostrik, *Tensor categories*][egno15], §8.10
-/

public section

open CategoryTheory MonoidalCategory BraidedCategory ExactPairing

universe w v u

namespace TauCeti

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C] [RigidCategory C]

/-- In a symmetric rigid category with its canonical pivotal structure, rotating `f : 𝟙_ C ⟶ X ⊗ Y`
postcomposes `f` with the braiding `(β_ X Y).hom`. -/
theorem pivotalRotate_eq_braiding {X Y : C} (f : 𝟙_ C ⟶ X ⊗ Y) :
    pivotalRotate f = f ≫ (β_ X Y).hom := by
  let g : Xᘁ ⊗ 𝟙_ C ⟶ Y := (tensorLeftHomEquiv (𝟙_ C) X Xᘁ Y).symm f
  let h : Xᘁ ⟶ Y := (ρ_ Xᘁ).inv ≫ g
  have hf : f = η_ X Xᘁ ≫ X ◁ h :=
    calc f = tensorLeftHomEquiv (𝟙_ C) X Xᘁ Y g := (Equiv.apply_symm_apply _ _).symm
      _ = η_ X Xᘁ ≫ X ◁ h := by simp only [h, tensorLeftHomEquiv, Equiv.coe_fn_mk]; monoidal
  rw [hf, pivotalRotate_comp_whiskerLeft, pivotalRotate_coevaluation,
    pivotalExactPairing_coevaluation_eq_braiding, Category.assoc, ← braiding_naturality_right,
    ← Category.assoc]

/-- In a symmetric rigid category, `frobeniusSchurRotate V n` postcomposes with the cyclic shift
`(tensorPowShiftIso V n).hom`. -/
theorem frobeniusSchurRotate_eq_comp_tensorPowShiftIso_hom (V : C) (n : ℕ)
    (f : 𝟙_ C ⟶ tensorPow V (n + 1)) :
    frobeniusSchurRotate V n f = f ≫ (tensorPowShiftIso V n).hom := by
  rw [frobeniusSchurRotate_def, pivotalRotate_eq_braiding, Category.assoc, ← tensorPowShiftIso_hom]

section Linear

variable (k : Type w) [Preadditive C] [MonoidalPreadditive C]

/-- In a `k`-linear symmetric rigid category, `frobeniusSchurEnd k V n` is postcomposition with
`(tensorPowShiftIso V n).hom`. -/
theorem frobeniusSchurEnd_eq_rightComp [Semiring k] [Linear k C] [MonoidalLinear k C]
    (V : C) (n : ℕ) :
    frobeniusSchurEnd k V n = Linear.rightComp k (𝟙_ C) (tensorPowShiftIso V n).hom := by
  ext f
  rw [congrFun (coe_frobeniusSchurEnd k V n) f, Linear.rightComp_apply,
    frobeniusSchurRotate_eq_comp_tensorPowShiftIso_hom]

/-- In a `k`-linear symmetric rigid category, `ν_{n+1}(V)` is the trace of postcomposition with
`(tensorPowShiftIso V n).hom` on `𝟙_ C ⟶ tensorPow V (n + 1)`. -/
theorem frobeniusSchurIndicator_succPNat_eq_trace_rightComp [CommRing k] [Linear k C]
    [MonoidalLinear k C] (V : C) (n : ℕ) :
    frobeniusSchurIndicator k V n.succPNat =
      LinearMap.trace k (𝟙_ C ⟶ tensorPow V (n + 1))
        (Linear.rightComp k (𝟙_ C) (tensorPowShiftIso V n).hom) := by
  rw [frobeniusSchurIndicator_succPNat, frobeniusSchurEnd_eq_rightComp]

/-- In a `k`-linear symmetric rigid category, `ν_n(V)` is the trace of postcomposition with
`(tensorPowShiftIso V n.natPred).hom` on `𝟙_ C ⟶ tensorPow V (n.natPred + 1)`. -/
theorem frobeniusSchurIndicator_eq_trace_rightComp [CommRing k] [Linear k C]
    [MonoidalLinear k C] (V : C) (n : ℕ+) :
    frobeniusSchurIndicator k V n =
      LinearMap.trace k (𝟙_ C ⟶ tensorPow V (n.natPred + 1))
        (Linear.rightComp k (𝟙_ C) (tensorPowShiftIso V n.natPred).hom) := by
  conv_lhs => rw [← PNat.succPNat_natPred n]
  exact frobeniusSchurIndicator_succPNat_eq_trace_rightComp k V n.natPred

end Linear

end TauCeti
