/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Action.Rigid
public import TauCeti.CategoryTheory.Monoidal.Pivotal.FrobeniusSchur.Symmetric

/-!
# Traces of actions in a symmetric rigid category

Let `V` be a symmetric rigid monoidal category and `H` a group. Then `Action V H` is again
symmetric and rigid, so both `V` and `Action V H` carry their canonical spherical structures,
whose pivotal isomorphisms are the Drinfeld isomorphisms. Since the duals, the evaluations, the
coevaluations and the braiding of `Action V H` are those of `V` on underlying objects, so are the
pivotal isomorphisms (`Action.drinfeldIso_hom_hom`), the traces and the dimensions: the
categorical trace of an equivariant endomorphism is the trace of the underlying endomorphism in
`V`.

Furthermore, for any action `X : Action V H`, element `g : H`, and `n : ℕ`, the categorical trace
in `V` of `((tensorPow X (n + 1)).ρ g).asHom` followed by the cyclic shift
`(tensorPowShiftIso X n).hom.hom` equals `trace (X.ρ (g ^ (n + 1))).asHom`
(`Action.trace_ρ_comp_tensorPowShiftIso_hom`). For `V = FGModuleCat k` this computes the higher
Frobenius–Schur indicators of `FDRep k G`.

## Main results

* `Action.rightTrace_hom`, `Action.leftTrace_hom`, `Action.trace_hom`: the traces of an
  endomorphism of an action are those of the underlying endomorphism;
* `Action.quantumDim_hom`: the quantum dimension of an action is that of its underlying object;
* `Action.trace_ρ_comp_tensorPowShiftIso_hom`: the trace of `g` acting on `tensorPow X (n + 1)`
  composed with the cyclic shift equals the trace of `g ^ (n + 1)` acting on `X`.
-/

public section

open CategoryTheory MonoidalCategory BraidedCategory TauCeti

namespace Action

variable {V : Type*} [Category* V] [MonoidalCategory V] [SymmetricCategory V] [RigidCategory V]
  {H : Type*} [Group H]

/-- The right trace of an endomorphism of an action is the right trace of the underlying
endomorphism. -/
@[simp]
theorem rightTrace_hom {X : Action V H} (f : X ⟶ X) : (rightTrace f).hom = rightTrace f.hom := by
  simp [rightTrace_eq_braiding]

/-- The left trace of an endomorphism of an action is the left trace of the underlying
endomorphism. -/
@[simp]
theorem leftTrace_hom {X : Action V H} (f : X ⟶ X) : (leftTrace f).hom = leftTrace f.hom := by
  rw [leftTrace_eq_rightTrace_of_symmetric, leftTrace_eq_rightTrace_of_symmetric, rightTrace_hom]

/-- The trace of an endomorphism of an action is the trace of the underlying endomorphism. -/
@[simp]
theorem trace_hom {X : Action V H} (f : X ⟶ X) : (trace f).hom = trace f.hom := by
  rw [trace_eq_rightTrace, trace_eq_rightTrace, rightTrace_hom]

/-- The quantum dimension of an action is the quantum dimension of its underlying object. -/
@[simp]
theorem quantumDim_hom (X : Action V H) : (quantumDim X).hom = quantumDim X.V := by
  rw [← trace_id, ← trace_id, trace_hom, id_hom]

/-- Structural isomorphism `(tensorPow X n).V ≅ tensorPow X.V n` built recursively by whiskering,
avoiding dependent object casts. -/
private def tensorPowVIso (X : Action V H) : ∀ n : ℕ, (tensorPow X n).V ≅ tensorPow X.V n
  | 0 => Iso.refl (𝟙_ V)
  | n + 1 => whiskerLeftIso X.V (tensorPowVIso X n)

omit [SymmetricCategory V] [RigidCategory V] in
private theorem ρ_comp_tensorPowVIso_hom (X : Action V H) (g : H) (n : ℕ) :
    ((tensorPow X n).ρ g).asHom ≫ (tensorPowVIso X n).hom =
      (tensorPowVIso X n).hom ≫ tensorPowMap (X.ρ g).asHom n := by
  induction n with
  | zero => simp [tensorPowVIso]
  | succ n ih =>
    simp only [tensorPowVIso, whiskerLeftIso_hom]
    rw [tensor_ρ, tensorPowMap_succ, tensorHom_def, Category.assoc,
      ← MonoidalCategory.whiskerLeft_comp, ih, MonoidalCategory.whiskerLeft_comp,
      ← whisker_exchange_assoc, ← tensorHom_def]

omit [SymmetricCategory V] [RigidCategory V] in
private theorem tensorPowSuccIso_hom_comp_tensorPowVIso_hom (X : Action V H) (n : ℕ) :
    (tensorPowSuccIso X n).hom.hom ≫ (tensorPowVIso X (n + 1)).hom =
      (tensorPowVIso X n).hom ▷ X.V ≫ (tensorPowSuccIso X.V n).hom := by
  induction n with
  | zero => simp [tensorPowVIso]
  | succ n ih =>
    have h := congrArg Hom.hom (tensorPowSuccIso_succ_hom X n)
    simp only [comp_hom, associator_hom_hom, whiskerLeft_hom] at h
    have h2 : (tensorPowVIso X (n + 2)).hom = X.V ◁ (tensorPowVIso X (n + 1)).hom := rfl
    rw [h, h2, Category.assoc, ← MonoidalCategory.whiskerLeft_comp, ih,
      tensorPowSuccIso_succ_hom X.V n]
    simp only [tensorPowVIso, whiskerLeftIso_hom]
    monoidal

omit [RigidCategory V] in
private theorem tensorPowShiftIso_hom_comp_tensorPowVIso_hom (X : Action V H) (n : ℕ) :
    (tensorPowShiftIso X n).hom.hom ≫ (tensorPowVIso X (n + 1)).hom =
      (tensorPowVIso X (n + 1)).hom ≫ (tensorPowShiftIso X.V n).hom := by
  rw [tensorPowShiftIso_hom, tensorPowShiftIso_hom, comp_hom, β_hom_hom, Category.assoc,
    tensorPowSuccIso_hom_comp_tensorPowVIso_hom]
  simp only [tensorPowVIso, whiskerLeftIso_hom, ← braiding_naturality_right_assoc]

/-- The categorical trace in `V` of `g` acting on `tensorPow X (n + 1)` followed by the cyclic
shift `(tensorPowShiftIso X n).hom.hom` equals the categorical trace of `g ^ (n + 1)` acting on
`X.V`. -/
theorem trace_ρ_comp_tensorPowShiftIso_hom (X : Action V H) (g : H) (n : ℕ) :
    trace (((tensorPow X (n + 1)).ρ g).asHom ≫ (tensorPowShiftIso X n).hom.hom) =
      trace (X.ρ (g ^ (n + 1))).asHom := by
  have hconj : ((tensorPow X (n + 1)).ρ g).asHom ≫ (tensorPowShiftIso X n).hom.hom =
      (tensorPowVIso X (n + 1)).hom ≫
        (tensorPowMap (X.ρ g).asHom (n + 1) ≫ (tensorPowShiftIso X.V n).hom) ≫
        (tensorPowVIso X (n + 1)).inv := by
    rw [← cancel_mono (tensorPowVIso X (n + 1)).hom]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id,
      tensorPowShiftIso_hom_comp_tensorPowVIso_hom,
      reassoc_of% (ρ_comp_tensorPowVIso_hom X g (n + 1))]
  have hpow : End.of (X.ρ g).asHom ^ (n + 1) = X.ρ (g ^ (n + 1)) :=
    (map_pow X.ρ g (n + 1)).symm
  have htr : trace (((tensorPow X (n + 1)).ρ g).asHom ≫ (tensorPowShiftIso X n).hom.hom) =
      trace (tensorPowMap (X.ρ g).asHom (n + 1) ≫ (tensorPowShiftIso X.V n).hom) := by
    rw [hconj]
    simpa using trace_conj (tensorPowVIso X (n + 1)).symm
      (tensorPowMap (X.ρ g).asHom (n + 1) ≫ (tensorPowShiftIso X.V n).hom)
  rw [htr, trace_tensorPowMap_comp_tensorPowShiftIso_hom, hpow]

end Action
