/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.HermitianBundle.BaseChange
public import TauCeti.NumberTheory.NumberField.HermitianBundle.ExteriorPower.Basic

import TauCeti.LinearAlgebra.ExteriorPower.BaseChange

/-!
# Base change of hermitian exterior powers

The canonical scalar-extension isomorphism for exterior powers is an isometry. At each complex
embedding of the extension field, both forms on a wedge of extended vectors are the same Gram
determinant. In top degree this identifies the determinant metrics used to compute Arakelov
degrees before and after base change.
-/

public noncomputable section

open NumberField NumberField.ComplexEmbedding
open scoped TensorProduct ComplexConjugate

namespace TauCeti.HermitianMetric

variable {K L : Type*} [Field K] [Field L] [Algebra K L]
  {E : Type*} [AddCommGroup E] [Module (𝓞 K) E]
  (h : HermitianMetric K E)

private theorem exteriorPower_baseChange_form_one_tmul (n : ℕ) (τ : L →+* ℂ)
    (x y : ⋀[𝓞 K]^n E) :
    (h.baseChange.exteriorPower n).form τ
        (1 ⊗ₜ (exteriorPower.equivBaseChange (𝓞 L) n).symm (1 ⊗ₜ x))
        (1 ⊗ₜ (exteriorPower.equivBaseChange (𝓞 L) n).symm (1 ⊗ₜ y)) =
      (h.exteriorPower n).form (τ.comp (algebraMap K L)) (1 ⊗ₜ x) (1 ⊗ₜ y) := by
  have tmul_smul (a : 𝓞 K) (z : ⋀[𝓞 K]^n E) :
      (1 : 𝓞 L) ⊗ₜ[𝓞 K] (a • z) = algebraMap (𝓞 K) (𝓞 L) a • ((1 : 𝓞 L) ⊗ₜ[𝓞 K] z) := by
    rw [TensorProduct.tmul_smul, IsScalarTower.algebraMap_smul]
  have embedding_int (a : 𝓞 K) :
      τ (algebraMap (𝓞 K) (𝓞 L) a) = (τ.comp (algebraMap K L)) a := by
    simp only [RingOfIntegers.coe_eq_algebraMap, RingHom.comp_apply,
      ← IsScalarTower.algebraMap_apply (𝓞 K) (𝓞 L) L,
      ← IsScalarTower.algebraMap_apply (𝓞 K) K L]
  let f := (exteriorPower.equivBaseChange (R := 𝓞 K) (M := E) (𝓞 L) n).symm
  let agrees (x y : ⋀[𝓞 K]^n E) :=
    (h.baseChange.exteriorPower n).form τ (1 ⊗ₜ f (1 ⊗ₜ x)) (1 ⊗ₜ f (1 ⊗ₜ y)) =
      (h.exteriorPower n).form (τ.comp (algebraMap K L)) (1 ⊗ₜ x) (1 ⊗ₜ y)
  refine Submodule.span_induction₂ (p := fun x y _ _ ↦ agrees x y)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ (_root_.exteriorPower.mem_span_ιMulti x)
    (_root_.exteriorPower.mem_span_ιMulti y) <;> dsimp only [agrees, f]
  · rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩
    simp only [exteriorPower.equivBaseChange_symm_tmul_ιMulti, one_smul,
      exteriorPower_form_tmul_ιMulti, baseChange_form_tmul_tmul, map_one, one_mul]
  · intros
    simp
  · intros
    simp
  · intro x y z _ _ _ hx hy
    simp only [TensorProduct.tmul_add, map_add, LinearMap.add_apply] at *
    rw [hx, hy]
  · intro x y z _ _ _ hy hz
    simp only [TensorProduct.tmul_add, map_add] at *
    rw [hy, hz]
  · intro a x y _ _ hxy
    simp only [tmul_smul, map_smul, Codomain.tmul_smul, LinearMap.map_smulₛₗ₂,
      embedding_int, hxy]
  · intro a x y _ _ hxy
    simp only [tmul_smul, map_smul, Codomain.tmul_smul, embedding_int, hxy]

/-- The canonical comparison from the base change of the nth exterior power of a hermitian
metric to the nth exterior power of its base change is an isometry. -/
def isometryEquivExteriorPowerBaseChange (n : ℕ) :
    IsometryEquiv ((h.exteriorPower n).baseChange (L := L)) (h.baseChange.exteriorPower n) where
  toLinearEquiv := (exteriorPower.equivBaseChange (𝓞 L) n).symm
  form_tmul τ x y := by
    induction x using TensorProduct.inductionOn generalizing y with
    | add x x' hx hx' =>
      simp only [map_add, TensorProduct.tmul_add, LinearMap.add_apply, hx, hx']
    | tmul a x =>
      induction y using TensorProduct.inductionOn with
      | add y y' hy hy' => simp only [map_add, TensorProduct.tmul_add, hy, hy']
      | tmul b y =>
        have ha : a ⊗ₜ[𝓞 K] x = a • ((1 : 𝓞 L) ⊗ₜ[𝓞 K] x) := by
          rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
        have hb : b ⊗ₜ[𝓞 K] y = b • ((1 : 𝓞 L) ⊗ₜ[𝓞 K] y) := by
          rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
        rw [baseChange_form_tmul_tmul, ha, hb, map_smul, map_smul,
          form_tmul_smul_tmul_smul, exteriorPower_baseChange_form_one_tmul]

/-- The exterior power comparison sends a scalar tensored with a decomposable vector to
that scalar times the wedge of the scalar-extended factors. -/
@[simp]
theorem isometryEquivExteriorPowerBaseChange_tmul_ιMulti {n : ℕ} (a : 𝓞 L) (x : Fin n → E) :
    h.isometryEquivExteriorPowerBaseChange n (a ⊗ₜ exteriorPower.ιMulti (𝓞 K) n x) =
      a • exteriorPower.ιMulti (𝓞 L) n (fun i ↦ 1 ⊗ₜ x i) :=
  exteriorPower.equivBaseChange_symm_tmul_ιMulti (𝓞 L) a x

end TauCeti.HermitianMetric

namespace TauCeti.HermitianBundle

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

/-- The determinant of a base-changed hermitian bundle is isometric to the base change of its
determinant by the canonical top exterior power comparison. -/
def isometryEquivDetBaseChange (E : HermitianBundle K) :
    HermitianMetric.IsometryEquiv (E.det.baseChange (L := L)).metric
      E.baseChange.det.metric := by
  rw [det_def (E.baseChange (L := L)), rank_baseChange]
  exact E.metric.isometryEquivExteriorPowerBaseChange E.rank

end TauCeti.HermitianBundle
