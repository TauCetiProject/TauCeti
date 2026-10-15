/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Monoidal.Rigid.Closed

/-!
# Dualizable objects in a closed monoidal category

Let `C` be a monoidal category and `Y` a closed object of `C`, so that `Y ⊗ -` has the right
adjoint `(Y ⟶[C] -)`. Write `Yᵛ := (Y ⟶[C] 𝟙_ C)` for the internal hom into the unit. Evaluation
induces the *dual-tensor comparison*

```text
Yᵛ ⊗ Z ⟶ (Y ⟶[C] Z),
```

natural in `Z`: it is the transpose of `Y ⊗ (Yᵛ ⊗ Z) ⟶ (Y ⊗ Yᵛ) ⊗ Z ⟶ 𝟙_ C ⊗ Z ⟶ Z`. For modules
over a commutative ring it is the map `Mᵛ ⊗ N → Hom(M, N)`, `φ ⊗ n ↦ (m ↦ φ m • n)`, formalized as
`dualTensorHom` in `Mathlib.LinearAlgebra.Contraction`. At `Z = 𝟙_ C` it is the right unitor.

The main result is the dual-basis criterion for dualizability. If the identity of `Y`, viewed as
a global element `𝟙_ C ⟶ (Y ⟶[C] Y)`, lifts along the comparison at `Z = Y`, then `Y` has left
dual `Yᵛ`: the lift is the coevaluation and the internal-hom evaluation `Y ⊗ Yᵛ ⟶ 𝟙_ C` is the
evaluation (`TauCeti.exactPairingOfDualTensorIhom`). In particular this applies when the
comparison at `Y` is an isomorphism. Conversely, if `Y` has any left dual then the comparison is
an isomorphism at every `Z`, since it factors through `TauCeti.ihomIsoTensorLeft`. Hence a closed
object is dualizable exactly when the dual-tensor comparison at `Y` itself is invertible
(`TauCeti.nonempty_hasLeftDual_iff_isIso_dualTensorIhom_app`). For a module `M`, this is the
statement that `M` is finite projective exactly when the identity of `M` is a finite sum of
`φᵢ ⊗ mᵢ`, that is, exactly when `M` admits a dual basis.

For sheaves of modules the comparison is `𝓔ᵛ ⊗ 𝓕 ⟶ 𝓗om(𝓔, 𝓕)`. Whether it is an isomorphism can be
checked on an open cover, and once it is known to be invertible this criterion produces the
coevaluation; so it is the route by which finite locally free sheaves are shown to be dualizable,
with dual `𝓗om(𝓔, 𝒪)`.

## Main declarations

* `TauCeti.dualTensorIhom`: the dual-tensor comparison, as a natural transformation
  `tensorLeft (Y ⟶[C] 𝟙_ C) ⟶ ihom Y`, characterized by
  `TauCeti.whiskerLeft_dualTensorIhom_app_comp_ev`;
* `TauCeti.exactPairingOfDualTensorIhom`: `Y` has left dual `(Y ⟶[C] 𝟙_ C)` once the identity of
  `Y` lifts along the comparison, and `TauCeti.exactPairingOfIsIsoDualTensorIhom` when the
  comparison at `Y` is an isomorphism;
* `TauCeti.dualTensorIhom_app_eq_ihomUnitIso_hom_whiskerRight_comp` and
  `TauCeti.isIso_dualTensorIhom`: for an object with a left dual the comparison is an
  isomorphism, so `(Y ⟶[C] Z) ≅ (Y ⟶[C] 𝟙_ C) ⊗ Z`;
* `TauCeti.nonempty_hasLeftDual_iff_isIso_dualTensorIhom_app`: the dualizability criterion.

## References

* [A. Dold and D. Puppe, *Duality, trace, and transfer*][doldpuppe1980], §1
* [L. G. Lewis, J. P. May and M. Steinberger, *Equivariant stable homotopy theory*][lms1986],
  Chapter III, §1
-/

public section

open CategoryTheory MonoidalCategory MonoidalClosed

namespace TauCeti

universe v u

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] (Y : C) [Closed Y]

/-- The dual-tensor comparison `(Y ⟶[C] 𝟙_ C) ⊗ Z ⟶ (Y ⟶[C] Z)` of a closed object `Y`, natural
in `Z`: the transpose of `Y ⊗ ((Y ⟶[C] 𝟙_ C) ⊗ Z) ⟶ (Y ⊗ (Y ⟶[C] 𝟙_ C)) ⊗ Z ⟶ 𝟙_ C ⊗ Z ⟶ Z`,
built from the evaluation of the internal hom into the unit. -/
def dualTensorIhom : tensorLeft (Y ⟶[C] 𝟙_ C) ⟶ ihom Y where
  app Z := curry ((α_ Y (Y ⟶[C] 𝟙_ C) Z).inv ≫ (ihom.ev Y).app (𝟙_ C) ▷ Z ≫ (λ_ Z).hom)
  naturality Z Z' g := by
    apply uncurry_injective
    rw [uncurry_natural_right, uncurry_natural_left, uncurry_curry, uncurry_curry]
    simp only [curriedTensor_obj_map, Functor.id_obj, Category.assoc,
      associator_inv_naturality_right_assoc, whisker_exchange_assoc, leftUnitor_naturality]

/-- The component of the dual-tensor comparison at `Z` is the transpose of
`(Y ⊗ (Y ⟶[C] 𝟙_ C)) ⊗ Z ⟶ 𝟙_ C ⊗ Z ⟶ Z`. -/
theorem dualTensorIhom_app (Z : C) :
    (dualTensorIhom Y).app Z =
      curry ((α_ Y (Y ⟶[C] 𝟙_ C) Z).inv ≫ (ihom.ev Y).app (𝟙_ C) ▷ Z ≫ (λ_ Z).hom) :=
  (rfl)

/-- Evaluation characterizes the dual-tensor comparison: after it, the evaluation of the internal
hom at `Z` is the evaluation into the unit, whiskered by `Z`. -/
@[reassoc (attr := simp)]
theorem whiskerLeft_dualTensorIhom_app_comp_ev (Z : C) :
    Y ◁ (dualTensorIhom Y).app Z ≫ (ihom.ev Y).app Z =
      (α_ Y (Y ⟶[C] 𝟙_ C) Z).inv ≫ (ihom.ev Y).app (𝟙_ C) ▷ Z ≫ (λ_ Z).hom :=
  whiskerLeft_curry_ihom_ev_app _ _ _

/-- At the unit, the dual-tensor comparison is the right unitor. -/
@[simp]
theorem dualTensorIhom_app_unit :
    (dualTensorIhom Y).app (𝟙_ C) = (ρ_ (Y ⟶[C] 𝟙_ C)).hom := by
  apply uncurry_injective
  simp only [uncurry_eq, whiskerLeft_dualTensorIhom_app_comp_ev, Functor.comp_obj,
    curriedTensor_obj_obj, whiskerLeft_rightUnitor, Category.assoc, unitors_equal,
    rightUnitor_naturality]

variable {Y}

section OfLift

variable (η : 𝟙_ C ⟶ (Y ⟶[C] 𝟙_ C) ⊗ Y) (hη : η ≫ (dualTensorIhom Y).app Y = MonoidalClosed.id Y)
include hη

/-- The first zigzag identity for a lift `η` of the identity along the dual-tensor comparison:
it is the transpose of the lifting equation. -/
private theorem whiskerLeft_comp_associator_inv_comp_ev_whiskerRight :
    Y ◁ η ≫ (α_ Y (Y ⟶[C] 𝟙_ C) Y).inv ≫ (ihom.ev Y).app (𝟙_ C) ▷ Y =
      (ρ_ Y).hom ≫ (λ_ Y).inv := by
  have key : (α_ Y (Y ⟶[C] 𝟙_ C) Y).inv ≫ (ihom.ev Y).app (𝟙_ C) ▷ Y =
      Y ◁ (dualTensorIhom Y).app Y ≫ (ihom.ev Y).app Y ≫ (λ_ Y).inv := by
    rw [whiskerLeft_dualTensorIhom_app_comp_ev_assoc, Iso.hom_inv_id, Category.comp_id]
  rw [key, ← MonoidalCategory.whiskerLeft_comp_assoc, hη, MonoidalClosed.id_eq,
    whiskerLeft_curry_ihom_ev_app_assoc]

/-- The dual-basis criterion: if the identity of `Y`, as a global element `𝟙_ C ⟶ (Y ⟶[C] Y)`,
lifts to `η : 𝟙_ C ⟶ (Y ⟶[C] 𝟙_ C) ⊗ Y` along the dual-tensor comparison, then `(Y ⟶[C] 𝟙_ C)`
is a left dual of `Y`, with coevaluation `η` and evaluation the evaluation of the internal hom.

Not an instance: the pairing depends on the chosen lift. -/
@[instance_reducible]
def exactPairingOfDualTensorIhom : ExactPairing (Y ⟶[C] 𝟙_ C) Y where
  coevaluation' := η
  evaluation' := (ihom.ev Y).app (𝟙_ C)
  coevaluation_evaluation' := whiskerLeft_comp_associator_inv_comp_ev_whiskerRight η hη
  evaluation_coevaluation' := by
    -- Both sides are maps into `(Y ⟶[C] 𝟙_ C) ⊗ 𝟙_ C`; after the right unitor, which is the
    -- comparison at the unit, naturality of the comparison in `Z` moves the inner evaluation
    -- past it, and transposing reduces the identity to the first zigzag identity whiskered by
    -- `(Y ⟶[C] 𝟙_ C)`.
    rw [← cancel_mono (ρ_ (Y ⟶[C] 𝟙_ C)).hom]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    have nat := (dualTensorIhom Y).naturality ((ihom.ev Y).app (𝟙_ C))
    simp only [curriedTensor_obj_obj, curriedTensor_obj_map, Functor.id_obj, Functor.comp_obj,
      dualTensorIhom_app_unit] at nat
    rw [nat]
    apply uncurry_injective
    simp only [uncurry_eq, MonoidalCategory.whiskerLeft_comp, Category.assoc, ihom.ev_naturality,
      whiskerLeft_dualTensorIhom_app_comp_ev_assoc]
    calc
      _ = (α_ Y (𝟙_ C) (Y ⟶[C] 𝟙_ C)).inv ≫
            (Y ◁ η ≫ (α_ Y (Y ⟶[C] 𝟙_ C) Y).inv ≫ (ihom.ev Y).app (𝟙_ C) ▷ Y) ▷
              (Y ⟶[C] 𝟙_ C) ≫
            (α_ (𝟙_ C) Y (Y ⟶[C] 𝟙_ C)).hom ≫ (λ_ (Y ⊗ (Y ⟶[C] 𝟙_ C))).hom ≫
            (ihom.ev Y).app (𝟙_ C) := by
        monoidal
      _ = Y ◁ (λ_ (Y ⟶[C] 𝟙_ C)).hom ≫ (ihom.ev Y).app (𝟙_ C) := by
        rw [whiskerLeft_comp_associator_inv_comp_ev_whiskerRight η hη]
        monoidal

/-- The evaluation of the pairing produced by the dual-basis criterion is the evaluation of the
internal hom into the unit. -/
@[simp]
theorem exactPairingOfDualTensorIhom_evaluation :
    @ExactPairing.evaluation C _ _ (Y ⟶[C] 𝟙_ C) Y (exactPairingOfDualTensorIhom η hη) =
      (ihom.ev Y).app (𝟙_ C) :=
  (rfl)

/-- The coevaluation of the pairing produced by the dual-basis criterion is the given lift of the
identity. -/
@[simp]
theorem exactPairingOfDualTensorIhom_coevaluation :
    @ExactPairing.coevaluation C _ _ (Y ⟶[C] 𝟙_ C) Y (exactPairingOfDualTensorIhom η hη) = η :=
  (rfl)

end OfLift

/-- If the dual-tensor comparison of `Y` is an isomorphism at `Y` itself, then `(Y ⟶[C] 𝟙_ C)` is
a left dual of `Y`: the coevaluation is the preimage of the identity of `Y` and the evaluation is
that of the internal hom.

Not an instance: `CategoryTheory.HasLeftDual` may already provide a different left dual. -/
@[instance_reducible]
noncomputable def exactPairingOfIsIsoDualTensorIhom [IsIso ((dualTensorIhom Y).app Y)] :
    ExactPairing (Y ⟶[C] 𝟙_ C) Y :=
  exactPairingOfDualTensorIhom (MonoidalClosed.id Y ≫ inv ((dualTensorIhom Y).app Y)) (by simp)

/-- The evaluation of the pairing of an object with invertible dual-tensor comparison is the
evaluation of the internal hom into the unit. -/
theorem exactPairingOfIsIsoDualTensorIhom_evaluation [IsIso ((dualTensorIhom Y).app Y)] :
    @ExactPairing.evaluation C _ _ (Y ⟶[C] 𝟙_ C) Y exactPairingOfIsIsoDualTensorIhom =
      (ihom.ev Y).app (𝟙_ C) :=
  (rfl)

/-- The coevaluation of the pairing of an object with invertible dual-tensor comparison is the
preimage of the identity of `Y` under the comparison. -/
theorem exactPairingOfIsIsoDualTensorIhom_coevaluation [IsIso ((dualTensorIhom Y).app Y)] :
    @ExactPairing.coevaluation C _ _ (Y ⟶[C] 𝟙_ C) Y exactPairingOfIsIsoDualTensorIhom =
      MonoidalClosed.id Y ≫ inv ((dualTensorIhom Y).app Y) :=
  (rfl)

section HasLeftDual

/-- For a left dual `D` of `Y`, the dual-tensor comparison factors through the identification
`(Y ⟶[C] 𝟙_ C) ≅ D` and the comparison `D ⊗ Z ⟶ (Y ⟶[C] Z)` of the pairing. -/
theorem dualTensorIhom_app_eq_ihomUnitIso_hom_whiskerRight_comp (D : C) [ExactPairing D Y]
    (Z : C) :
    (dualTensorIhom Y).app Z =
      (ihomUnitIso D Y).hom ▷ Z ≫ (ihomIsoTensorLeft D Y).inv.app Z := by
  -- The evaluation into the unit is the pairing's evaluation, read through `ihomUnitIso`.
  have h : (ihom.ev Y).app (𝟙_ C) = Y ◁ (ihomUnitIso D Y).hom ≫ ε_ D Y := by
    rw [← whiskerLeft_ihomUnitIso_inv_comp_ev (D := D) (Y := Y),
      ← MonoidalCategory.whiskerLeft_comp_assoc, Iso.hom_inv_id, MonoidalCategory.whiskerLeft_id,
      Category.id_comp]
  apply uncurry_injective
  simp only [uncurry_eq, whiskerLeft_dualTensorIhom_app_comp_ev, MonoidalCategory.whiskerLeft_comp,
    Category.assoc, whiskerLeft_ihomIsoTensorLeft_inv_app_comp_ev, h]
  monoidal

/-- The dual-tensor comparison of an object with a left dual `D` is an isomorphism, so the
internal hom out of `Y` is tensoring with `(Y ⟶[C] 𝟙_ C)`. -/
theorem isIso_dualTensorIhom_of_exactPairing (D : C) [ExactPairing D Y] :
    IsIso (dualTensorIhom Y) := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro Z
  rw [dualTensorIhom_app_eq_ihomUnitIso_hom_whiskerRight_comp D Z]
  infer_instance

end HasLeftDual

/-- The dual-tensor comparison of an object with a left dual is an isomorphism, so the internal
hom out of `Y` is tensoring with `(Y ⟶[C] 𝟙_ C)`. -/
instance isIso_dualTensorIhom [HasLeftDual Y] : IsIso (dualTensorIhom Y) :=
  isIso_dualTensorIhom_of_exactPairing (ᘁY)

/-- A closed object `Y` has a left dual exactly when its dual-tensor comparison at `Y` itself is
an isomorphism; the left dual is then `(Y ⟶[C] 𝟙_ C)`. -/
theorem nonempty_hasLeftDual_iff_isIso_dualTensorIhom_app :
    Nonempty (HasLeftDual Y) ↔ IsIso ((dualTensorIhom Y).app Y) :=
  ⟨fun ⟨_⟩ ↦ inferInstance,
    fun _ ↦ ⟨{ leftDual := Y ⟶[C] 𝟙_ C, exact := exactPairingOfIsIsoDualTensorIhom }⟩⟩

end TauCeti
