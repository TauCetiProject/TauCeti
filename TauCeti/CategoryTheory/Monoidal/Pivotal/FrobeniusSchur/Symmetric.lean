/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Linear.Basic
public import TauCeti.CategoryTheory.Monoidal.Braided.TensorPow
public import TauCeti.CategoryTheory.Monoidal.Pivotal.FrobeniusSchur.Basic
public import TauCeti.CategoryTheory.Monoidal.Pivotal.Symmetric

/-!
# Frobenius–Schur rotation and cyclic traces in symmetric rigid categories

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

In the same setting, contracting the cyclic shift `tensorPowShiftIso X n` against the tensor power
`tensorPowMap f (n + 1)` of an endomorphism `f : X ⟶ X` inside the categorical trace yields the
categorical trace of the `(n + 1)`-st iterate `(End.of f ^ (n + 1)).asHom`
(`TauCeti.trace_tensorPowMap_comp_tensorPowShiftIso_hom`). This is the categorical power-trace
identity underlying `ν_n(V) = |G|⁻¹ ∑_{g ∈ G} χ_V(g^n)` in `FDRep k G`.

## Main declarations

* `TauCeti.pivotalRotate_eq_braiding`: in a symmetric rigid category,
  `pivotalRotate f = f ≫ (β_ X Y).hom`;
* `TauCeti.frobeniusSchurRotate_eq_comp_tensorPowShiftIso_hom`,
  `TauCeti.frobeniusSchurEnd_eq_rightComp`, and
  `TauCeti.frobeniusSchurIndicator_eq_trace_rightComp`: `E_V^{(n+1)}` is postcomposition with the
  cyclic shift `tensorPowShiftIso V n`, so `ν_n(V)` is the trace of postcomposition with
  `tensorPowShiftIso V n.natPred`;
* `TauCeti.trace_tensorHom_tensorPowMap_comp_tensorPowShiftIso_hom` and
  `TauCeti.trace_tensorPowMap_comp_tensorPowShiftIso_hom`: the categorical trace of
  `tensorPowMap f (n + 1) ≫ (tensorPowShiftIso X n).hom` is `trace (End.of f ^ (n + 1)).asHom`.

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

section CyclicTrace

omit [RigidCategory C] in
/-- Whiskering on the first of two `X` factors slides across `(α_ X X Z)⁻¹ ≫ β_{X,X} ▷ Z ≫ α`
onto the second `X` factor. -/
private theorem whiskerRight_comp_associator_inv_braiding_associator_hom {X Z : C} (u : X ⟶ X) :
    u ▷ (X ⊗ Z) ≫ (α_ X X Z).inv ≫ (β_ X X).hom ▷ Z ≫ (α_ X X Z).hom =
      (α_ X X Z).inv ≫ (β_ X X).hom ▷ Z ≫ (α_ X X Z).hom ≫ X ◁ (u ▷ Z) := by
  calc _ = (α_ X X Z).inv ≫ ((u ▷ X ≫ (β_ X X).hom) ▷ Z) ≫ (α_ X X Z).hom := by monoidal
    _ = (α_ X X Z).inv ≫ (((β_ X X).hom ≫ X ◁ u) ▷ Z) ≫ (α_ X X Z).hom := by
          rw [braiding_naturality_left]
    _ = _ := by monoidal

omit [RigidCategory C] in
/-- Whiskering on `X ⊗ Z` slides across `(α_ X X Z)⁻¹ ≫ β_{X,X} ▷ Z ≫ α` onto the first `X` and
third `Z` factors. -/
private theorem whiskerLeft_tensorHom_comp_associator_inv_braiding_associator_hom {X Z : C}
    (f : X ⟶ X) (g : Z ⟶ Z) :
    X ◁ (f ⊗ₘ g) ≫ (α_ X X Z).inv ≫ (β_ X X).hom ▷ Z ≫ (α_ X X Z).hom =
      (α_ X X Z).inv ≫ (β_ X X).hom ▷ Z ≫ (α_ X X Z).hom ≫ f ▷ (X ⊗ Z) ≫ X ◁ (X ◁ g) := by
  calc _ = (α_ X X Z).inv ≫ ((X ◁ f) ▷ Z ≫ ((X ⊗ X) ◁ g ≫ (β_ X X).hom ▷ Z)) ≫
        (α_ X X Z).hom := by rw [tensorHom_def]; monoidal
    _ = (α_ X X Z).inv ≫ ((X ◁ f ≫ (β_ X X).hom) ▷ Z) ≫ (X ⊗ X) ◁ g ≫ (α_ X X Z).hom := by
          rw [whisker_exchange]; monoidal
    _ = (α_ X X Z).inv ≫ (((β_ X X).hom ≫ f ▷ X) ▷ Z) ≫ (X ⊗ X) ◁ g ≫ (α_ X X Z).hom := by
          rw [braiding_naturality_right]
    _ = _ := by monoidal

/-- **Cyclic power-trace induction**: in a symmetric rigid category, the categorical trace of
`(a ⊗ₘ tensorPowMap f n) ≫ (tensorPowShiftIso X n).hom` on `tensorPow X (n + 1)` equals the
categorical trace of `(End.of f ^ n).asHom ≫ a` on `X`. -/
theorem trace_tensorHom_tensorPowMap_comp_tensorPowShiftIso_hom {X : C} (a f : X ⟶ X) (n : ℕ) :
    trace ((a ⊗ₘ tensorPowMap f n) ≫ (tensorPowShiftIso X n).hom) =
      trace ((End.of f ^ n).asHom ≫ a) := by
  induction n generalizing a with
  | zero =>
    simpa [tensorPowMap_zero] using trace_conj (ρ_ X).symm a
  | succ n ih =>
    have h1 : (a ⊗ₘ (f ⊗ₘ tensorPowMap f n)) ≫
        (α_ X X (tensorPow X n)).inv ≫ (β_ X X).hom ▷ tensorPow X n ≫
          (α_ X X (tensorPow X n)).hom ≫ X ◁ (tensorPowShiftIso X n).hom =
        ((α_ X X (tensorPow X n)).inv ≫ (β_ X X).hom ▷ tensorPow X n ≫
          (α_ X X (tensorPow X n)).hom ≫
            X ◁ (a ▷ tensorPow X n ≫ X ◁ tensorPowMap f n ≫ (tensorPowShiftIso X n).hom)) ≫
          f ▷ (X ⊗ tensorPow X n) := by
      rw [tensorHom_def a, Category.assoc,
        reassoc_of% (whiskerLeft_tensorHom_comp_associator_inv_braiding_associator_hom f
          (tensorPowMap f n)),
        reassoc_of% (whiskerRight_comp_associator_inv_braiding_associator_hom
          (Z := tensorPow X n) a)]
      simp only [← MonoidalCategory.whiskerLeft_comp, Category.assoc]
      rw [← whisker_exchange, ← MonoidalCategory.whiskerLeft_comp_assoc]
    have h2 : f ▷ (X ⊗ tensorPow X n) ≫
        ((α_ X X (tensorPow X n)).inv ≫ (β_ X X).hom ▷ tensorPow X n ≫
          (α_ X X (tensorPow X n)).hom ≫
            X ◁ (a ▷ tensorPow X n ≫ X ◁ tensorPowMap f n ≫ (tensorPowShiftIso X n).hom)) =
        (α_ X X (tensorPow X n)).inv ≫ (β_ X X).hom ▷ tensorPow X n ≫
          (α_ X X (tensorPow X n)).hom ≫
            X ◁ (((f ≫ a) ⊗ₘ tensorPowMap f n) ≫ (tensorPowShiftIso X n).hom) := by
      rw [reassoc_of% (whiskerRight_comp_associator_inv_braiding_associator_hom
        (Z := tensorPow X n) f)]
      simp only [← MonoidalCategory.whiskerLeft_comp, ← comp_whiskerRight_assoc,
        tensorHom_def, Category.assoc]
    rw [tensorPowMap_succ, tensorPowShiftIso_succ_hom, h1, trace_comm, h2,
      trace_associator_inv_braiding_whiskerRight_associator_hom_comp_whiskerLeft, ih (f ≫ a),
      pow_succ', End.mul_asHom, Category.assoc]

/-- **Categorical trace of a tensor power with cyclic shift**: in a symmetric rigid category, the
categorical trace of `tensorPowMap f (n + 1) ≫ (tensorPowShiftIso X n).hom` is the categorical
trace of the `(n + 1)`-st iterate `(End.of f ^ (n + 1)).asHom`. -/
theorem trace_tensorPowMap_comp_tensorPowShiftIso_hom {X : C} (f : X ⟶ X) (n : ℕ) :
    trace (tensorPowMap f (n + 1) ≫ (tensorPowShiftIso X n).hom) =
      trace (End.of f ^ (n + 1)).asHom := by
  rw [tensorPowMap_succ, trace_tensorHom_tensorPowMap_comp_tensorPowShiftIso_hom, pow_succ',
    End.mul_asHom]

/-- The categorical trace of the cyclic shift `(tensorPowShiftIso X n).hom` on `tensorPow X (n + 1)`
equals the quantum dimension of `X`. -/
@[simp]
theorem trace_tensorPowShiftIso_hom (X : C) (n : ℕ) :
    trace (tensorPowShiftIso X n).hom = quantumDim X := by
  simpa using trace_tensorPowMap_comp_tensorPowShiftIso_hom (𝟙 X) n

end CyclicTrace

end TauCeti
