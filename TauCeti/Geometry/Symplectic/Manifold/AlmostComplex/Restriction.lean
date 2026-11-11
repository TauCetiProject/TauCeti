/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Manifold.AlmostComplex.Family
public import TauCeti.Geometry.Manifold.VectorBundle.Tangent.Restriction

/-!
# Open restrictions of finite-regularity almost complex structures

Both ordinary structures and jointly domain-dependent vertical structures restrict to open
submanifolds through the canonical tangent-space equivalences. The regularity order is unchanged;
zero and infinite regularity are included. No nonempty-domain assumption is used.
-/

public noncomputable section

open Bundle TopologicalSpace
open scoped Manifold ContDiff

namespace TauCeti

variable {E H M EP HP P : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [NormedAddCommGroup EP] [NormedSpace ℝ EP] [TopologicalSpace HP]
  {IP : ModelWithCorners ℝ EP HP} [TopologicalSpace P] [ChartedSpace HP P]
  {n : ℕ∞}

namespace ContMDiffAlmostComplexStructure

/-- Restrict a finite-regularity almost complex structure to an open submanifold. -/
def restrictOpen (J : ContMDiffAlmostComplexStructure I n M) (U : Opens M) :
    ContMDiffAlmostComplexStructure I n U where
  toEndomorphism :=
    ⟨fun x ↦ Manifold.restrictOpenTangentSpaceEnd (fun q : M × M ↦ J.toEndomorphism q.2)
      U ((x : M), x),
      (Manifold.contMDiff_restrictOpenTangentSpaceEnd
        (fun q : M × M ↦ J.toEndomorphism q.2) U
        (J.toEndomorphism.contMDiff.comp (contMDiff_snd (I := I) (J := I)))).comp
          ((contMDiff_subtype_val (I := I) (U := U)).prodMk contMDiff_id)⟩
  square_neg x := by
    ext v
    simp only [ContMDiffSection.coeFn_mk, ContinuousLinearMap.comp_apply, neg_apply,
      ContinuousLinearMap.id_apply]
    -- The section constructor and original/open tangent fibres use inherited instances.
    erw [Manifold.restrictOpenTangentSpaceEnd_apply,
      Manifold.restrictOpenTangentSpaceEnd_apply]
    rw [ContinuousLinearEquiv.apply_symm_apply]
    rw [show J.toEndomorphism x (J.toEndomorphism x _) = -_ from J.apply_apply x _]
    simp only [map_neg, ContinuousLinearEquiv.symm_apply_apply]

/-- Open restriction evaluates the ambient structure through the canonical tangent equivalence. -/
@[simp]
theorem restrictOpen_apply (J : ContMDiffAlmostComplexStructure I n M) (U : Opens M)
    (x : U) (v : TangentSpace I x) :
    J.restrictOpen U x v = (Manifold.tangentSpaceOpenEquiv (I := I) x).symm
      (J (x : M) (Manifold.tangentSpaceOpenEquiv (I := I) x v)) :=
  Manifold.restrictOpenTangentSpaceEnd_apply _ _ _ _

end ContMDiffAlmostComplexStructure

namespace ContMDiffAlmostComplexStructureFamily

/-- Restrict the target variable and target tangent fibres to an open submanifold. -/
def restrictTargetOpen (J : ContMDiffAlmostComplexStructureFamily I M IP P n) (V : Opens M) :
    ContMDiffAlmostComplexStructureFamily I V IP P n :=
  ofContMDiff (Manifold.restrictOpenTangentSpaceEnd J.tangentEndomorphism V)
    (Manifold.contMDiff_restrictOpenTangentSpaceEnd J.tangentEndomorphism V
      J.contMDiff_tangentEndomorphism)
    (fun q v ↦ by
      simp only [Manifold.restrictOpenTangentSpaceEnd_apply,
        ContinuousLinearEquiv.apply_symm_apply]
      rw [tangentEndomorphism_apply_apply]
      simp only [map_neg, ContinuousLinearEquiv.symm_apply_apply])

@[simp]
theorem restrictTargetOpen_toEndomorphism_apply
    (J : ContMDiffAlmostComplexStructureFamily I M IP P n) (V : Opens M) (q : P × V) :
    (J.restrictTargetOpen V).toEndomorphism q =
      Manifold.restrictOpenTangentSpaceEnd J.tangentEndomorphism V q := by
  unfold restrictTargetOpen
  exact ofContMDiff_toEndomorphism_apply _ _ _ q

/-- Restrict a domain-dependent structure to an open product, with its intrinsic target tangent
fibres. Domain composition and target tangent transport preserve the same finite order. -/
def restrictOpen (J : ContMDiffAlmostComplexStructureFamily I M IP P n)
    (U : Opens P) (V : Opens M) : ContMDiffAlmostComplexStructureFamily I V IP U n :=
  (J.restrictTargetOpen V).comp ⟨Subtype.val, contMDiff_subtype_val⟩

@[simp]
theorem restrictOpen_toEndomorphism_apply
    (J : ContMDiffAlmostComplexStructureFamily I M IP P n) (U : Opens P) (V : Opens M)
    (q : U × V) : (J.restrictOpen U V).toEndomorphism q =
      Manifold.restrictOpenTangentSpaceEnd J.tangentEndomorphism V ((q.1 : P), q.2) := by
  unfold restrictOpen
  erw [comp_toEndomorphism_apply, restrictTargetOpen_toEndomorphism_apply]
  rfl

/-- The open-product family acts by canonical conjugation on the target tangent space. -/
theorem restrictOpen_apply (J : ContMDiffAlmostComplexStructureFamily I M IP P n)
    (U : Opens P) (V : Opens M) (q : U × V) (v : TangentSpace I q.2) :
    J.restrictOpen U V q v = (Manifold.tangentSpaceOpenEquiv (I := I) q.2).symm
      (J.tangentEndomorphism ((q.1 : P), (q.2 : M))
        (Manifold.tangentSpaceOpenEquiv (I := I) q.2 v)) := by
  exact (DFunLike.congr_fun (restrictOpen_toEndomorphism_apply J U V q) v).trans
    (Manifold.restrictOpenTangentSpaceEnd_apply J.tangentEndomorphism V
      ((q.1 : P), q.2) v)

/-- Freezing commutes with restriction to an open product. -/
@[simp]
theorem freeze_restrictOpen (J : ContMDiffAlmostComplexStructureFamily I M IP P n)
    (U : Opens P) (V : Opens M) (p : U) :
    (J.restrictOpen U V).freeze p = (J.freeze (p : P)).restrictOpen V := by
  ext x v
  simp only [freeze_toEndomorphism_apply, restrictOpen_toEndomorphism_apply,
    ContMDiffAlmostComplexStructure.restrictOpen_apply]
  erw [Manifold.restrictOpenTangentSpaceEnd_apply]
  rw [tangentEndomorphism_apply]
  rfl

end ContMDiffAlmostComplexStructureFamily

end TauCeti
