/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
module

/-
Staged for Tau Ceti: the polar partial isometry over a general `RCLike` field.
-/

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.Positive
public import Mathlib.Analysis.InnerProductSpace.Projection.Basic
public import Mathlib.Analysis.Normed.Operator.Extend

/-!
# A Gram factorisation produces a contraction

If a bounded operator `T : E →L[𝕜] F` and a **self-adjoint** `A : E →L[𝕜] E`
have the same Gram operator,

```
A ∘L A = T⋆ ∘L T,
```

then there is a contraction `W : E →L[𝕜] F` with

```
W ∘L A = T   and   W⋆ ∘L T = A.
```

`W` is the polar partial isometry: `A` plays the role of `|T|`, and the pair of
identities says exactly that `T` and `A` are two-sided contractive multiples of
one another.

## Why this is stated on the Gram operator rather than on `|T|`

`ForTauCeti/Analysis/InnerProductSpace/Polar/PartialIsometry.lean` specializes this
construction to `A = T.modulus` and packages the result as the canonical polar partial
isometry.  The lower-level Gram formulation remains useful because it needs no functional
calculus at all.  Everything below rests on one consequence of the Gram identity,
`ContinuousLinearMap.norm_apply_eq_of_gram_eq`:

```
‖A x‖ = ‖T x‖.
```

Read left to right it says `A x ↦ T x` is well defined; read as an equation it says that
assignment is isometric.  A caller with the canonical modulus supplies
`A = T.modulus`, `T.modulus_isSelfAdjoint`, and `T.modulus_mul_self`.

## Main definitions and results

* `ContinuousLinearMap.norm_apply_eq_of_gram_eq`: the isometry identity.
* `ContinuousLinearMap.rangeTopologicalClosure`: the initial space, `closure (range A)`.
* `ContinuousLinearMap.gramContraction`: the contraction `W`.
* `ContinuousLinearMap.gramContraction_comp_right`: `W ∘L A = T`.
* `ContinuousLinearMap.adjoint_gramContraction_comp_left`: `W⋆ ∘L T = A`.
* `ContinuousLinearMap.norm_gramContraction_le_one`: `‖W‖ ≤ 1`.
* `ContinuousLinearMap.exists_contraction_of_gram_eq`: the packaged existence
  statement, which is the form consumers want.
* `ContinuousLinearMap.norm_apply_le_of_gram_le`,
  `ContinuousLinearMap.exists_contraction_of_gram_le`: the **one-sided** version,
  where the Gram identity is weakened to the operator inequality
  `T⋆T ≤ A²` and only `W ∘L A = T` survives.

## The one-sided version

Domination `T⋆T ≤ A²` gives `‖T x‖ ≤ ‖A x‖` instead of equality, and that is
already enough for the whole construction: `A x ↦ T x` is still well defined
(if `A x = A y` then `‖T x - T y‖ ≤ ‖A x - A y‖ = 0`) and still bounded by `1`,
so it still extends by continuity.  What is lost is the reverse identity
`W⋆ ∘L T = A`, which genuinely fails under domination alone — take `T = 0` and
`A ≠ 0`.  So `exists_contraction_of_gram_le` is deliberately one-sided.

The construction itself (`rangeTopologicalClosure`, `corestrictRangeClosure`,
`gramContractionOnRangeClosure`, `gramContraction`) mentions no Gram hypothesis at all, so
both versions share it; only the property proofs differ.

## Provenance

* Original repository: Davis--Kahan/DKPS formalization (Kitware, Inc.).
* Original module: authored directly in `ForTauCeti`; it has had no prior home.
* Extraction class: **authored in place** for the Tau Ceti staging layer.
* Original authors / copyright: Jon Crall, Claude Opus 5; Copyright (c) 2026
  Kitware, Inc.; Apache 2.0.
* Spectra influence: **none** — the `ForTauCeti` import firewall admits only
  Mathlib, `TauCeti` and `ForTauCeti`.
-/

public section

namespace ContinuousLinearMap

open scoped InnerProductSpace

universe u v

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type u} {F : Type v}
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

/-! ### The isometry identity -/

/-- **A self-adjoint Gram square root has the same norms as the operator.**

`‖A x‖² = ⟪A x, A x⟫ = ⟪x, A² x⟫ = ⟪x, T⋆T x⟫ = ⟪T x, T x⟫ = ‖T x‖²`.  This is
the only consequence of the Gram identity that the whole construction uses. -/
theorem norm_apply_eq_of_gram_eq {T : E →L[𝕜] F} {A : E →L[𝕜] E}
    (hA : IsSelfAdjoint A) (hgram : A ∘L A = adjoint T ∘L T) (x : E) :
    ‖A x‖ = ‖T x‖ := by
  have hAadj : adjoint A = A := by
    rw [← ContinuousLinearMap.star_eq_adjoint]; exact hA.star_eq
  have hinner : ⟪A x, A x⟫_𝕜 = ⟪T x, T x⟫_𝕜 := by
    calc ⟪A x, A x⟫_𝕜 = ⟪x, adjoint A (A x)⟫_𝕜 := (adjoint_inner_right A x (A x)).symm
      _ = ⟪x, (A ∘L A) x⟫_𝕜 := by rw [hAadj, ContinuousLinearMap.comp_apply]
      _ = ⟪x, (adjoint T ∘L T) x⟫_𝕜 := by rw [hgram]
      _ = ⟪x, adjoint T (T x)⟫_𝕜 := by rw [ContinuousLinearMap.comp_apply]
      _ = ⟪T x, T x⟫_𝕜 := adjoint_inner_right T x (T x)
  have hsq : ‖A x‖ * ‖A x‖ = ‖T x‖ * ‖T x‖ := by
    have h := congrArg RCLike.re hinner
    rwa [inner_self_eq_norm_mul_norm, inner_self_eq_norm_mul_norm] at h
  exact (mul_self_inj (norm_nonneg _) (norm_nonneg _)).mp hsq

/-! ### The initial space -/

/-- The **initial space**: the closure of the range of `A`.  The contraction is
isometric on it and vanishes on its orthogonal complement. -/
noncomputable def rangeTopologicalClosure (A : E →L[𝕜] E) : Submodule 𝕜 E :=
  (LinearMap.range A.toLinearMap).topologicalClosure

omit [CompleteSpace E] in
/-- Every value of `A` lies in the initial space. -/
theorem apply_mem_rangeTopologicalClosure (A : E →L[𝕜] E) (x : E) :
    A x ∈ A.rangeTopologicalClosure :=
  Submodule.le_topologicalClosure _ ⟨x, rfl⟩

/-- The initial space is complete, being a topological closure inside a complete
space.  This is what lets the isometry be extended to it by continuity. -/
instance instCompleteSpaceRangeTopologicalClosure (A : E →L[𝕜] E) :
    CompleteSpace A.rangeTopologicalClosure :=
  Submodule.topologicalClosure.completeSpace _

/-- `A`, corestricted to the initial space, where it has dense range. -/
noncomputable def corestrictRangeClosure (A : E →L[𝕜] E) :
    E →ₗ[𝕜] A.rangeTopologicalClosure :=
  LinearMap.codRestrict A.rangeTopologicalClosure A.toLinearMap
    A.apply_mem_rangeTopologicalClosure

omit [CompleteSpace E] in
/-- The corestriction has the same values as `A`; only its codomain changes. -/
@[simp]
theorem coe_corestrictRangeClosure_apply (A : E →L[𝕜] E) (x : E) :
    (A.corestrictRangeClosure x : E) = A x := (rfl)

omit [CompleteSpace E] in
/-- The corestriction has **dense** range: the initial space is defined as that
closure.  This is the hypothesis `LinearMap.extendOfNorm` needs. -/
theorem denseRange_corestrictRangeClosure (A : E →L[𝕜] E) :
    DenseRange A.corestrictRangeClosure := by
  rw [DenseRange, Subtype.dense_iff]
  have hsub : (LinearMap.range A.toLinearMap : Set E)
      ⊆ (Subtype.val '' Set.range A.corestrictRangeClosure) := by
    rintro _ ⟨x, rfl⟩
    exact ⟨A.corestrictRangeClosure x, ⟨x, rfl⟩, rfl⟩
  calc (A.rangeTopologicalClosure : Set E)
      = closure (LinearMap.range A.toLinearMap : Set E) :=
        Submodule.topologicalClosure_coe _
    _ ⊆ closure (Subtype.val '' Set.range A.corestrictRangeClosure) := closure_mono hsub

/-! ### The contraction -/

/-- The extension of the isometry `A x ↦ T x` from the dense range of `A` to the
whole initial space. -/
noncomputable def gramContractionOnRangeClosure (T : E →L[𝕜] F) (A : E →L[𝕜] E) :
    A.rangeTopologicalClosure →L[𝕜] F :=
  T.toLinearMap.extendOfNorm A.corestrictRangeClosure

/-- **The contraction attached to a Gram factorisation.**

`W = W₀ ∘ P`, where `P` is the orthogonal projection onto the initial space and
`W₀` is the continuous extension of `A x ↦ T x`.  It is a partial isometry:
isometric on the initial space and zero on its orthogonal complement. -/
noncomputable def gramContraction (T : E →L[𝕜] F) (A : E →L[𝕜] E) : E →L[𝕜] F :=
  T.gramContractionOnRangeClosure A ∘L A.rangeTopologicalClosure.orthogonalProjectionOnto

section GramHyp

variable {T : E →L[𝕜] F} {A : E →L[𝕜] E}
  (hA : IsSelfAdjoint A) (hgram : A ∘L A = adjoint T ∘L T)

include hA hgram

/-- The bound that makes the extension possible; it is in fact an equality. -/
theorem norm_apply_le_norm_corestrictRangeClosure (x : E) :
    ‖T.toLinearMap x‖ ≤ 1 * ‖A.corestrictRangeClosure x‖ := by
  rw [one_mul]
  exact le_of_eq (norm_apply_eq_of_gram_eq hA hgram x).symm

/-- The extension undoes `A` on its range: `W₀ (A x) = T x`. -/
theorem gramContractionOnRangeClosure_corestrictRangeClosure (x : E) :
    T.gramContractionOnRangeClosure A (A.corestrictRangeClosure x) = T x :=
  LinearMap.extendOfNorm_eq A.denseRange_corestrictRangeClosure
    ⟨1, norm_apply_le_norm_corestrictRangeClosure hA hgram⟩ x

/-- **The factorisation**: `W A = T`, pointwise. -/
theorem gramContraction_apply_apply (x : E) :
    T.gramContraction A (A x) = T x := by
  have hproj : A.rangeTopologicalClosure.orthogonalProjectionOnto (A x)
      = A.corestrictRangeClosure x := by
    apply Subtype.ext
    simpa using
      Submodule.starProjection_eq_self_iff.mpr (A.apply_mem_rangeTopologicalClosure x)
  rw [gramContraction, ContinuousLinearMap.comp_apply, hproj,
    gramContractionOnRangeClosure_corestrictRangeClosure hA hgram]

/-- **The factorisation**: `W ∘L A = T`. -/
theorem gramContraction_comp_right : T.gramContraction A ∘L A = T := by
  ext x
  exact gramContraction_apply_apply hA hgram x

/-- **The contraction bound**: `‖W‖ ≤ 1`.  Both factors are contractions — the
extension because the map it extends is isometric, the projection because it is
orthogonal. -/
theorem norm_gramContraction_le_one : ‖T.gramContraction A‖ ≤ 1 := by
  have haux : ‖T.gramContractionOnRangeClosure A‖ ≤ 1 :=
    LinearMap.opNorm_extendOfNorm_le A.denseRange_corestrictRangeClosure zero_le_one
      (norm_apply_le_norm_corestrictRangeClosure hA hgram)
  have hproj : ‖A.rangeTopologicalClosure.orthogonalProjectionOnto‖ ≤ 1 :=
    Submodule.orthogonalProjectionOnto_norm_le _
  calc ‖T.gramContraction A‖
      ≤ ‖T.gramContractionOnRangeClosure A‖ *
        ‖A.rangeTopologicalClosure.orthogonalProjectionOnto‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ 1 * 1 := mul_le_mul haux hproj (norm_nonneg _) zero_le_one
    _ = 1 := one_mul 1

/-- The inner-product identity behind `W⋆ T = A`, stated on the initial space so
that it can be proved on the dense range of `A` and transported by continuity. -/
theorem inner_gramContractionOnRangeClosure (x : E) (z : A.rangeTopologicalClosure) :
    ⟪T x, T.gramContractionOnRangeClosure A z⟫_𝕜 = ⟪A x, (z : E)⟫_𝕜 := by
  have hAadj : adjoint A = A := by
    rw [← ContinuousLinearMap.star_eq_adjoint]; exact hA.star_eq
  have heq : Set.EqOn
      (fun w : A.rangeTopologicalClosure => ⟪T x, T.gramContractionOnRangeClosure A w⟫_𝕜)
      (fun w : A.rangeTopologicalClosure => ⟪A x, (w : E)⟫_𝕜)
      (Set.range A.corestrictRangeClosure) := by
    rintro _ ⟨w, rfl⟩
    simp only [gramContractionOnRangeClosure_corestrictRangeClosure hA hgram,
      coe_corestrictRangeClosure_apply]
    calc ⟪T x, T w⟫_𝕜 = ⟪x, adjoint T (T w)⟫_𝕜 := (adjoint_inner_right T x (T w)).symm
      _ = ⟪x, (adjoint T ∘L T) w⟫_𝕜 := by rw [ContinuousLinearMap.comp_apply]
      _ = ⟪x, (A ∘L A) w⟫_𝕜 := by rw [hgram]
      _ = ⟪x, A (A w)⟫_𝕜 := by rw [ContinuousLinearMap.comp_apply]
      _ = ⟪x, adjoint A (A w)⟫_𝕜 := by rw [hAadj]
      _ = ⟪A x, A w⟫_𝕜 := adjoint_inner_right A x (A w)
  exact congrFun (Continuous.ext_on A.denseRange_corestrictRangeClosure
    (by fun_prop) (by fun_prop) heq) z

/-- **The reverse factorisation**: `W⋆ ∘L T = A`.

On the initial space this is the Gram identity read backwards; off it, both
sides vanish, `W` because it is zero there and `A` because its values lie in the
initial space. -/
theorem adjoint_gramContraction_comp_left :
    adjoint (T.gramContraction A) ∘L T = A := by
  ext x
  refine ext_inner_right 𝕜 fun y => ?_
  calc ⟪(adjoint (T.gramContraction A) ∘L T) x, y⟫_𝕜
      = ⟪T x, T.gramContraction A y⟫_𝕜 := by
        rw [ContinuousLinearMap.comp_apply, adjoint_inner_left]
    _ = ⟪T x, T.gramContractionOnRangeClosure A
          (A.rangeTopologicalClosure.orthogonalProjectionOnto y)⟫_𝕜 := by
        rw [gramContraction, ContinuousLinearMap.comp_apply]
    _ = ⟪A x, A.rangeTopologicalClosure.starProjection y⟫_𝕜 :=
        inner_gramContractionOnRangeClosure hA hgram x _
    _ = ⟪A.rangeTopologicalClosure.starProjection (A x), y⟫_𝕜 :=
        (Submodule.inner_starProjection_left_eq_right _ _ _).symm
    _ = ⟪A x, y⟫_𝕜 := by
        rw [Submodule.starProjection_eq_self_iff.mpr
          (A.apply_mem_rangeTopologicalClosure x)]

/-- **A Gram factorisation produces a two-sided contractive equivalence.**

This is the packaged form: `T` and its self-adjoint Gram square root `A` are
contractive multiples of one another.  It is what a symmetric-norm-ideal
argument needs — an ideal gauge bounds `‖W‖ · gauge · ‖V‖`, so two-sided
domination by contractions forces the gauges of `T` and `A` to agree. -/
theorem exists_contraction_of_gram_eq :
    ∃ W : E →L[𝕜] F, ‖W‖ ≤ 1 ∧ ‖adjoint W‖ ≤ 1 ∧ W ∘L A = T ∧ adjoint W ∘L T = A :=
  ⟨T.gramContraction A, norm_gramContraction_le_one hA hgram,
    (LinearIsometryEquiv.norm_map _ _).trans_le (norm_gramContraction_le_one hA hgram),
    gramContraction_comp_right hA hgram, adjoint_gramContraction_comp_left hA hgram⟩

end GramHyp

/-! ### The one-sided version

Only `T⋆T ≤ A²` is assumed.  Every declaration here is the corresponding one
from the section above with the norm *equality* replaced by the norm
*inequality*; the underlying construction is reused verbatim. -/

section GramLeHyp

variable {T : E →L[𝕜] F} {A : E →L[𝕜] E}
  (hA : IsSelfAdjoint A) (hle : adjoint T ∘L T ≤ A ∘L A)

include hA hle

/-- **Gram domination bounds norms pointwise.**

`‖T x‖² = re ⟪T⋆T x, x⟫ ≤ re ⟪A² x, x⟫ = ‖A x‖²`, the middle step being exactly
positivity of `A² - T⋆T` applied at `x`.  This is the only consequence of the
hypothesis that the construction uses, which is why weakening the Gram identity
to an inequality costs nothing but the reverse factorisation. -/
theorem norm_apply_le_of_gram_le (x : E) : ‖T x‖ ≤ ‖A x‖ := by
  have hAadj : adjoint A = A := by
    rw [← ContinuousLinearMap.star_eq_adjoint]; exact hA.star_eq
  have hpos : (A ∘L A - adjoint T ∘L T).IsPositive :=
    ContinuousLinearMap.le_def.mp hle
  have hAA : ⟪x, A (A x)⟫_𝕜 = ⟪A x, A x⟫_𝕜 := by
    have h := adjoint_inner_right A x (A x)
    rwa [hAadj] at h
  have hTT : ⟪x, adjoint T (T x)⟫_𝕜 = ⟪T x, T x⟫_𝕜 := adjoint_inner_right T x (T x)
  have hsplit : ⟪x, (A ∘L A - adjoint T ∘L T) x⟫_𝕜 =
      ⟪A x, A x⟫_𝕜 - ⟪T x, T x⟫_𝕜 := by
    rw [_root_.sub_apply, inner_sub_right,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, hAA, hTT]
  have hnn := hpos.re_inner_nonneg_right x
  rw [hsplit, map_sub, inner_self_eq_norm_mul_norm,
    inner_self_eq_norm_mul_norm] at hnn
  exact nonneg_le_nonneg_of_sq_le_sq (norm_nonneg _) (by linarith)

/-- The bound that makes the extension possible, under domination only. -/
theorem norm_apply_le_norm_corestrictRangeClosure_of_gram_le (x : E) :
    ‖T.toLinearMap x‖ ≤ 1 * ‖A.corestrictRangeClosure x‖ := by
  rw [one_mul]
  exact norm_apply_le_of_gram_le hA hle x

/-- The extension undoes `A` on its range: `W₀ (A x) = T x`. -/
theorem gramContractionOnRangeClosure_corestrictRangeClosure_of_gram_le (x : E) :
    T.gramContractionOnRangeClosure A (A.corestrictRangeClosure x) = T x :=
  LinearMap.extendOfNorm_eq A.denseRange_corestrictRangeClosure
    ⟨1, norm_apply_le_norm_corestrictRangeClosure_of_gram_le hA hle⟩ x

/-- **The factorisation**: `W A = T`, pointwise. -/
theorem gramContraction_apply_apply_of_gram_le (x : E) :
    T.gramContraction A (A x) = T x := by
  have hproj : A.rangeTopologicalClosure.orthogonalProjectionOnto (A x)
      = A.corestrictRangeClosure x := by
    apply Subtype.ext
    simpa using
      Submodule.starProjection_eq_self_iff.mpr (A.apply_mem_rangeTopologicalClosure x)
  rw [gramContraction, ContinuousLinearMap.comp_apply, hproj,
    gramContractionOnRangeClosure_corestrictRangeClosure_of_gram_le hA hle]

/-- **The factorisation**: `W ∘L A = T`. -/
theorem gramContraction_comp_right_of_gram_le : T.gramContraction A ∘L A = T := by
  ext x
  exact gramContraction_apply_apply_of_gram_le hA hle x

/-- **The contraction bound**: `‖W‖ ≤ 1`. -/
theorem norm_gramContraction_le_one_of_gram_le : ‖T.gramContraction A‖ ≤ 1 := by
  have haux : ‖T.gramContractionOnRangeClosure A‖ ≤ 1 :=
    LinearMap.opNorm_extendOfNorm_le A.denseRange_corestrictRangeClosure zero_le_one
      (norm_apply_le_norm_corestrictRangeClosure_of_gram_le hA hle)
  have hproj : ‖A.rangeTopologicalClosure.orthogonalProjectionOnto‖ ≤ 1 :=
    Submodule.orthogonalProjectionOnto_norm_le _
  calc ‖T.gramContraction A‖
      ≤ ‖T.gramContractionOnRangeClosure A‖ *
        ‖A.rangeTopologicalClosure.orthogonalProjectionOnto‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ 1 * 1 := mul_le_mul haux hproj (norm_nonneg _) zero_le_one
    _ = 1 := one_mul 1

/-- **Gram domination produces a contractive factorisation.**

If `T⋆T ≤ A²` with `A` self-adjoint, then `T` factors through `A` by a
contraction.  This is the specialised Douglas factorisation: no functional
calculus, no square roots and no product space, because `A` is supplied as a
hypothesis rather than constructed.

It is deliberately **one-sided**.  The reverse identity `W⋆ ∘L T = A` of
`exists_contraction_of_gram_eq` is false under domination alone — `T = 0` with
`A ≠ 0` satisfies the hypothesis and forces `W⋆ T = 0 ≠ A`. -/
theorem exists_contraction_of_gram_le :
    ∃ W : E →L[𝕜] F, ‖W‖ ≤ 1 ∧ W ∘L A = T :=
  ⟨T.gramContraction A, norm_gramContraction_le_one_of_gram_le hA hle,
    gramContraction_comp_right_of_gram_le hA hle⟩

end GramLeHyp

end ContinuousLinearMap
