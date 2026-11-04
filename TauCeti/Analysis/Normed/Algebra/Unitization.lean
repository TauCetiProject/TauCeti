/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Algebra.Subalgebra.Adjoin
public import Mathlib.Algebra.Algebra.Subalgebra.Unitization
public import Mathlib.Analysis.Normed.Algebra.UnitizationL1
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Operator.NormedSpace
public import Mathlib.Topology.Algebra.Algebra.Equiv

import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Unitizations of closed nonunital subalgebras

For a closed nonunital subalgebra `B` of a Banach algebra `A` which does not contain `1`,
the map `(r, b) ↦ r • 1 + b` identifies its external ℓ¹ unitization with the closed unital
subalgebra `Algebra.adjoin 𝕜 (B : Set A) = B + 𝕜 1` inside `A`. The identification and its
inverse are bounded; the inherited norm need not equal the ℓ¹ norm.

The ℓ¹ unitization of a commutative normed algebra is moreover a commutative normed ring
(`WithLp.instUnitizationNormedCommRing`).

The canonical inclusion and nonunital coordinate projection of the ℓ¹ unitization are
also bundled as bounded linear maps.

No normalization of the norm of the identity is assumed. The forward map is bounded by
`max ‖(1 : A)‖ 1`, so the results apply to any complete nontrivially normed scalar field.

## References

* Dales, *Banach Algebras and Automatic Continuity*, §§1.3–1.5.
* The algebraic identification is Mathlib's `NonUnitalSubalgebra.unitizationAlgEquiv`;
  the ℓ¹ norm is Mathlib's `WithLp.unitization_norm_def`.
-/

public section

namespace NonUnitalSubalgebra

section NormedField

variable {𝕜 A : Type*} [NormedField 𝕜] [NormedRing A] [NormedAlgebra 𝕜 A]
  (B : NonUnitalSubalgebra 𝕜 A)

/-- The natural unitization map is bounded for the ℓ¹ norm, without normalizing `‖1‖`. -/
theorem norm_unitization_le (x : WithLp 1 (Unitization 𝕜 B)) :
    ‖unitization B (WithLp.ofLp x)‖ ≤ max ‖(1 : A)‖ 1 * ‖x‖ := by
  rw [unitization_apply, Algebra.algebraMap_eq_smul_one, WithLp.unitization_norm_def, mul_add]
  calc
    ‖(WithLp.ofLp x).fst • (1 : A) + (WithLp.ofLp x).snd‖ ≤
        ‖(WithLp.ofLp x).fst‖ * ‖(1 : A)‖ + ‖(WithLp.ofLp x).snd‖ := by
      -- The norm on the subtype `B` is induced from `A`.
      exact (norm_add_le _ _).trans_eq (by rw [norm_smul]; rfl)
    _ ≤ max ‖(1 : A)‖ 1 * ‖(WithLp.ofLp x).fst‖ +
        max ‖(1 : A)‖ 1 * ‖(WithLp.ofLp x).snd‖ := by
      apply add_le_add
      · rw [mul_comm ‖(WithLp.ofLp x).fst‖]
        exact mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)
      · exact le_mul_of_one_le_left (norm_nonneg _) (le_max_right _ _)

/-- Continuity of the natural map from the external ℓ¹ unitization into the ambient algebra. -/
@[continuity]
theorem continuous_unitization :
    Continuous (fun x : WithLp 1 (Unitization 𝕜 B) ↦ unitization B (WithLp.ofLp x)) := by
  exact AddMonoidHomClass.continuous_of_bound
    ((unitization B).comp (WithLp.unitizationAlgEquiv 𝕜).toAlgHom)
    (max ‖(1 : A)‖ 1) B.norm_unitization_le

end NormedField

section TopologicalAlgebra

variable {𝕜 A : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  [Ring A] [TopologicalSpace A] [IsTopologicalAddGroup A] [Algebra 𝕜 A]
  [ContinuousSMul 𝕜 A] (B : NonUnitalSubalgebra 𝕜 A)

/-- Adjoining the identity to a closed nonunital subalgebra gives a closed subalgebra.
Its underlying vector subspace is `B.toSubmodule ⊔ 𝕜 ∙ (1 : A)`. -/
theorem isClosed_adjoin (hB : IsClosed (B : Set A)) :
    IsClosed (Algebra.adjoin 𝕜 (B : Set A) : Set A) := by
  rw [← Subalgebra.coe_toSubmodule, B.adjoin_eq_span_one_sup, sup_comm]
  exact B.toSubmodule.isClosed_sup_finiteDimensional (Submodule.span 𝕜 {1}) hB

end TopologicalAlgebra

section NontriviallyNormedField

variable {𝕜 A : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  [NormedRing A] [NormedAlgebra 𝕜 A] [CompleteSpace A] (B : NonUnitalSubalgebra 𝕜 A)

/-- A closed nonunital subalgebra omitting the ambient identity has its external ℓ¹
unitization boundedly isomorphic to its unital closure with the inherited norm. -/
noncomputable def unitizationContinuousAlgEquiv (hB : IsClosed (B : Set A))
    (h1 : (1 : A) ∉ B) :
    WithLp 1 (Unitization 𝕜 B) ≃A[𝕜] Algebra.adjoin 𝕜 (B : Set A) := by
  letI : CompleteSpace B := hB.completeSpace_coe
  letI : CompleteSpace (Algebra.adjoin 𝕜 (B : Set A)) := (B.isClosed_adjoin hB).completeSpace_coe
  let e := (WithLp.unitizationAlgEquiv 𝕜).trans (unitizationAlgEquiv B h1)
  have he_coe : (fun x ↦ (e x : A)) =
      fun x ↦ unitization B (WithLp.ofLp x) := by
    funext x
    simpa only [e, AlgEquiv.trans_apply, WithLp.unitizationAlgEquiv_apply, unitization_apply]
      using unitizationAlgEquiv_apply_coe B h1 (WithLp.ofLp x)
  have he : Continuous e := continuous_induced_rng.mpr (by
    simp only [Function.comp_def, he_coe]
    exact B.continuous_unitization)
  exact { e with
    continuous_toFun := he
    continuous_invFun := by
      -- Explicit carriers fix the algebra-to-linear coercion for elaboration.
      exact LinearEquiv.continuous_symm (𝕜 := 𝕜) (𝕜' := 𝕜)
        (E := WithLp 1 (Unitization 𝕜 B)) (F := Algebra.adjoin 𝕜 (B : Set A))
        e.toLinearEquiv (by simpa only [AlgEquiv.coe_toLinearEquiv] using he) }

/-- The continuous unitization identification has the standard algebraic identification as its
underlying algebra equivalence, so its inverse is the same algebraic inverse. -/
theorem unitizationContinuousAlgEquiv_toAlgEquiv (hB : IsClosed (B : Set A))
    (h1 : (1 : A) ∉ B) :
    (B.unitizationContinuousAlgEquiv hB h1).toAlgEquiv =
      (WithLp.unitizationAlgEquiv 𝕜).trans (unitizationAlgEquiv B h1) := (rfl)

/-- The bounded identification sends the two unitization coordinates to their sum in `A`. -/
@[simp]
theorem unitizationContinuousAlgEquiv_apply_coe (hB : IsClosed (B : Set A))
    (h1 : (1 : A) ∉ B) (x : WithLp 1 (Unitization 𝕜 B)) :
    (B.unitizationContinuousAlgEquiv hB h1 x : A) =
      algebraMap 𝕜 A (WithLp.ofLp x).fst + (WithLp.ofLp x).snd := by
  rw [← ContinuousAlgEquiv.coe_toAlgEquiv, unitizationContinuousAlgEquiv_toAlgEquiv,
    AlgEquiv.trans_apply,
    unitizationAlgEquiv_apply_coe, WithLp.unitizationAlgEquiv_apply]

/-- The inverse bounded identification recovers the scalar and nonunital coordinates. -/
@[simp↓]
theorem unitizationContinuousAlgEquiv_symm_apply (hB : IsClosed (B : Set A))
    (h1 : (1 : A) ∉ B) (r : 𝕜) (b : B)
    {h : algebraMap 𝕜 A r + b ∈ Algebra.adjoin 𝕜 (B : Set A)} :
    (B.unitizationContinuousAlgEquiv hB h1).symm ⟨algebraMap 𝕜 A r + b, h⟩ =
      WithLp.toLp 1 (Unitization.inl r + (b : Unitization 𝕜 B)) := by
  apply (B.unitizationContinuousAlgEquiv hB h1).symm_apply_eq.mpr
  apply Subtype.ext
  simp

end NontriviallyNormedField

end NonUnitalSubalgebra

namespace WithLp

variable (𝕜 A : Type*) [NormedField 𝕜] [NonUnitalNormedRing A] [NormedSpace 𝕜 A]

/-- The isometric inclusion into the external ℓ¹ unitization as a bounded linear map. -/
noncomputable def unitizationInrL : A →L[𝕜] WithLp 1 (Unitization 𝕜 A) :=
  { (WithLp.linearEquiv 1 𝕜 (Unitization 𝕜 A)).symm.toLinearMap.comp
      (Unitization.inrHom 𝕜 𝕜 A) with
    cont := unitization_isometry_inr.continuous }

/-- The bounded inclusion is the usual inclusion into the ℓ¹ unitization. -/
@[simp]
theorem unitizationInrL_apply (a : A) :
    unitizationInrL 𝕜 A a = toLp 1 (a : Unitization 𝕜 A) := (rfl)

/-- The projection onto the nonunital summand of the external ℓ¹ unitization. -/
noncomputable def unitizationSndL : WithLp 1 (Unitization 𝕜 A) →L[𝕜] A :=
  ((Unitization.sndHom 𝕜 𝕜 A).comp
    (WithLp.linearEquiv 1 𝕜 (Unitization 𝕜 A)).toLinearMap).mkContinuous
    1 fun u ↦ by
      simpa only [LinearMap.comp_apply, Unitization.sndHom_apply, LinearEquiv.coe_coe,
        WithLp.coe_linearEquiv,
        one_mul, unitization_norm_def] using
          (le_add_of_nonneg_left (norm_nonneg (ofLp u).fst) :
            ‖(ofLp u).snd‖ ≤ ‖(ofLp u).fst‖ + ‖(ofLp u).snd‖)

/-- The bounded projection recovers the nonunital coordinate. -/
@[simp]
theorem unitizationSndL_apply (u : WithLp 1 (Unitization 𝕜 A)) :
    unitizationSndL 𝕜 A u = (ofLp u).snd := (rfl)

variable [IsScalarTower 𝕜 A A] [SMulCommClass 𝕜 A A]

/-- The bounded inclusion into the ℓ¹ unitization preserves multiplication. -/
theorem unitizationInrL_mul (a b : A) :
    unitizationInrL 𝕜 A (a * b) = unitizationInrL 𝕜 A a * unitizationInrL 𝕜 A b := by
  apply (unitizationAlgEquiv 𝕜).injective
  simp

variable {𝕜 A}

/-- Every element of the ℓ¹ unitization is the sum of its scalar and nonunital parts. -/
theorem unitization_eq_fst_smul_one_add_inr (u : WithLp 1 (Unitization 𝕜 A)) :
    u = (ofLp u).fst • 1 + toLp 1 ((ofLp u).snd : Unitization 𝕜 A) := by
  apply (unitizationAlgEquiv 𝕜).injective
  simp [← Algebra.algebraMap_eq_smul_one, Unitization.algebraMap_eq_inl,
    Unitization.inl_fst_add_inr_snd_eq]

variable {𝕜 A : Type*} [NormedField 𝕜] [NonUnitalNormedCommRing A] [NormedSpace 𝕜 A]
  [IsScalarTower 𝕜 A A] [SMulCommClass 𝕜 A A]

/-- The ℓ¹ unitization of a commutative normed algebra is a commutative normed ring. -/
noncomputable instance instUnitizationNormedCommRing :
    NormedCommRing (WithLp 1 (Unitization 𝕜 A)) where
  mul_comm x y := (unitizationAlgEquiv 𝕜).injective <| by simp [mul_comm]

end WithLp

namespace ContinuousLinearMap

section Decomposition

variable {𝕜 A E : Type*} [NormedField 𝕜] [NonUnitalNormedRing A]
  [NormedSpace 𝕜 A] [IsScalarTower 𝕜 A A] [SMulCommClass 𝕜 A A]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- A bounded linear map on the ℓ¹ unitization splits into its scalar and nonunital parts. -/
theorem unitization_apply_eq_fst_smul_add (M : WithLp 1 (Unitization 𝕜 A) →L[𝕜] E)
    (u : WithLp 1 (Unitization 𝕜 A)) :
    M u = (WithLp.ofLp u).fst • M 1 +
      M (WithLp.toLp 1 ((WithLp.ofLp u).snd : Unitization 𝕜 A)) := by
  conv_lhs => rw [WithLp.unitization_eq_fst_smul_one_add_inr u]
  simp

end Decomposition

variable {𝕜 A E : Type*} [NontriviallyNormedField 𝕜] [NonUnitalNormedRing A]
  [NormedSpace 𝕜 A] [IsScalarTower 𝕜 A A] [SMulCommClass 𝕜 A A]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- Composing a bounded derivation with the nonunital coordinate projection extends its
Leibniz rule to unital actions of the ℓ¹ unitization. -/
theorem comp_unitizationSndL_mul (D : A →L[𝕜] E)
    (L R : WithLp 1 (Unitization 𝕜 A) →L[𝕜] E →L[𝕜] E)
    (h1L : ∀ x, L 1 x = x) (h1R : ∀ x, R 1 x = x)
    (hD : ∀ a b, D (a * b) =
      L (WithLp.toLp 1 (a : Unitization 𝕜 A)) (D b) +
      R (WithLp.toLp 1 (b : Unitization 𝕜 A)) (D a))
    (u v : WithLp 1 (Unitization 𝕜 A)) :
    (D ∘L WithLp.unitizationSndL 𝕜 A) (u * v) =
      L u ((D ∘L WithLp.unitizationSndL 𝕜 A) v) +
      R v ((D ∘L WithLp.unitizationSndL 𝕜 A) u) := by
  rw [L.unitization_apply_eq_fst_smul_add u, R.unitization_apply_eq_fst_smul_add v]
  simp only [comp_apply, WithLp.unitizationSndL_apply, WithLp.unitization_mul,
    Unitization.snd_mul, map_add, map_smul, hD, add_apply, smul_apply, h1L, h1R]
  abel

/-- Extension through the nonunital coordinate projection does not increase the norm. -/
theorem norm_comp_unitizationSndL_le (D : A →L[𝕜] E) :
    ‖D ∘L WithLp.unitizationSndL 𝕜 A‖ ≤ ‖D‖ := by
  apply opNorm_le_bound _ (norm_nonneg _)
  intro u
  rw [comp_apply, WithLp.unitizationSndL_apply, WithLp.unitization_norm_def]
  exact D.le_opNorm _ |>.trans (by gcongr; exact le_add_of_nonneg_left (norm_nonneg _))

end ContinuousLinearMap
