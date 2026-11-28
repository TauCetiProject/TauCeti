/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.GroupAction.Quotient
public import TauCeti.Geometry.Manifold.Instances.Stiefel.FrameAction.Smooth
public import TauCeti.Geometry.Manifold.Instances.Stiefel.OrientedGrassmannian.Basic
import TauCeti.Data.Nat.Choose.Basic
import TauCeti.Geometry.Lie.Subgroup.Unitary.SpecialOrthogonal
import TauCeti.Geometry.Manifold.IsManifold.Basic

/-!
# The smooth oriented Grassmannian

The rotation action on orthonormal frames is free, smooth and proper. The slice charts
`ProperSMul.orbitRelQuotientChartedSpace` give the quotient a smooth manifold structure of
dimension `r (dim E - r)` and make the frame projection a smooth submersion. The construction
uses the native Lie group structure on `Matrix.specialUnitaryGroup` over the reals.
-/

public section

noncomputable section

open Manifold Matrix Module
open scoped ContDiff Manifold

namespace TauCeti.orientedGrassmannian

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

open scoped Matrix.Norms.L2Operator
attribute [local instance] Matrix.l2OpNormedAlgebraReal
attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField
attribute [local instance] ContMDiffMul.boundarylessManifold

variable (E) (r : ℕ+)

local notation "SO(" r ")" => specialOrthogonalGroup (Fin r) ℝ
local notation "𝓢𝓞(" r ")" => specialUnitaryGroup.model (Fin r) ℝ
local notation "𝓥(" E ", " r ")" => 𝓘(ℝ, stiefel.Model E r)

/-- The Euclidean model of the oriented Grassmannian, obtained by subtracting the dimension of
the rotation group from the dimension of the Stiefel manifold. -/
abbrev Model :=
  let quotientModel {V H : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [TopologicalSpace H]
      (_ : ModelWithCorners ℝ V H) :=
    ProperSMul.QuotientModelSpace V (stiefel.Model E r)
  quotientModel 𝓢𝓞(r)

/-- The quotient model has dimension `r (dim E - r)`. -/
theorem finrank_model : finrank ℝ (Model E r) = (r : ℕ) * (finrank ℝ E - r) := by
  have hSO : finrank ℝ (GroupLieAlgebra 𝓢𝓞(r) (SO(r))) = (Fintype.card (Fin r)).choose 2 :=
    finrank_specialOrthogonalLieAlgebra
  have h (k : ℕ) : (k + 1).choose 2 + k.choose 2 = k * k := by
    simpa [Nat.add_comm 1 k] using Nat.add_choose_two_add_choose_two 1 k
  rw [ProperSMul.finrank_quotientModelSpace,
    ← finrank_tangentSpace (I := 𝓢𝓞(r)) (1 : SO(r))]
  simp only [stiefel.Model, hSO, Fintype.card_fin, Module.finrank_fin_fun,
    Nat.sub_sub, h, Nat.mul_sub_left_distrib]

variable [FiniteDimensional ℝ E]

/-- The oriented Grassmannian has the slice charts for the change-of-basis action. -/
instance instChartedSpace : ChartedSpace (Model E r) (orientedGrassmannian E r) :=
  ProperSMul.orbitRelQuotientChartedSpace 𝓢𝓞(r) (SO(r)) 𝓥(E, (r : ℕ))
    (stiefel E r)

/-- The slice atlas makes the oriented Grassmannian a smooth manifold. -/
instance instIsManifold : IsManifold 𝓘(ℝ, Model E r) ∞ (orientedGrassmannian E r) :=
  ProperSMul.instIsManifoldOrbitRelQuotient
    (I := 𝓢𝓞(r)) (I' := 𝓥(E, (r : ℕ)))

/-- The projection from the Stiefel manifold to the oriented Grassmannian is a smooth submersion. -/
theorem isSubmersion_ofFrame :
    Manifold.IsSubmersion 𝓥(E, (r : ℕ)) 𝓘(ℝ, Model E r) ∞
      (ofFrame : stiefel E r → orientedGrassmannian E r) := by
  rw [ofFrame_eq_quotientMk]
  exact ProperSMul.isSubmersion_quotientMk (I := 𝓢𝓞(r)) (I' := 𝓥(E, (r : ℕ)))

/-- The frame projection is continuously differentiable at every order up to `∞`. -/
theorem contMDiff_ofFrame {n : ℕ∞ω} (hn : n ≤ ∞) :
    ContMDiff 𝓥(E, (r : ℕ)) 𝓘(ℝ, Model E r) n (ofFrame : stiefel E r → orientedGrassmannian E r) :=
  (isSubmersion_ofFrame E r).contMDiff.of_le hn

end TauCeti.orientedGrassmannian
