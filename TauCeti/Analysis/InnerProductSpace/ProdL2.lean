/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.ProdL2
public import Mathlib.Analysis.Normed.Operator.Compact.Basic
public import TauCeti.Analysis.Normed.Lp.ProdLp

/-!
# Coordinate adjoints, block sums, and `2 × 2` block operators on `WithLp 2 (E × F)`

For complete inner product spaces `E` and `F` over `𝕜` (`[RCLike 𝕜]`), the coordinate inclusions
`WithLp.inlL 2 𝕜 E F` and `WithLp.inrL 2 𝕜 E F` are the Hilbert-space adjoints of the coordinate
projections `WithLp.fstL 2 𝕜 E F` and `WithLp.sndL 2 𝕜 E F` (`WithLp.adjoint_fstL`,
`WithLp.adjoint_sndL`, `WithLp.adjoint_inlL`, `WithLp.adjoint_inrL`).

An operator on `WithLp 2 (E × F)` is a `2 × 2` block matrix of operators between the factors:
`WithLp.blockL2 a b c d` is the operator `(x, y) ↦ (a x + b y, c x + d y)`, every operator is
the block operator of its four blocks (`WithLp.blockL2_eta`), and the blocks of
`WithLp.blockL2 a b c d` are `a`, `b`, `c` and `d` (`WithLp.fstL_comp_blockL2_comp_inlL` and its
three siblings). Block operators multiply as matrices (`WithLp.blockL2_mul_blockL2`), their
adjoint is the conjugate transpose (`WithLp.adjoint_blockL2`), and a block operator with compact
entries is compact (`WithLp.isCompactOperator_blockL2`). The block diagonal operators are the
block sums `ContinuousLinearMap.withLpProdMap` (`WithLp.blockL2_zero_zero`).

In addition, the orthogonal block sum `f.withLpProdMap 2 g` of two rectangular Hilbert-space
operators satisfies `(f ⊕ g)† = f† ⊕ g†` (`ContinuousLinearMap.adjoint_withLpProdMap`), bundles
endomorphism pairs as a star algebra homomorphism (`ContinuousLinearMap.withLpProdMapStarAlgHom`),
and is self-adjoint iff both blocks are (`ContinuousLinearMap.isSelfAdjoint_withLpProdMap_iff`).
Consequently, two nonunital `⋆`-representations `π₁` and `π₂` combine into an orthogonal direct-sum
`⋆`-representation `NonUnitalStarAlgHom.prodStarRep π₁ π₂` on `WithLp 2 (E₁ × E₂)`.
-/

public section

namespace WithLp

section Adjoint

variable (𝕜 E F : Type*) [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

/-- The Hilbert-space adjoint of `WithLp.fstL 2 𝕜 E F` is `WithLp.inlL 2 𝕜 E F`. -/
@[simp]
theorem adjoint_fstL : (WithLp.fstL 2 𝕜 E F).adjoint = inlL 2 𝕜 E F :=
  ((ContinuousLinearMap.eq_adjoint_iff _ _).mpr fun _ _ ↦ by simp).symm

/-- The Hilbert-space adjoint of `WithLp.inlL 2 𝕜 E F` is `WithLp.fstL 2 𝕜 E F`. -/
@[simp]
theorem adjoint_inlL : (inlL 2 𝕜 E F).adjoint = WithLp.fstL 2 𝕜 E F := by
  rw [← adjoint_fstL, ContinuousLinearMap.adjoint_adjoint]

/-- The Hilbert-space adjoint of `WithLp.sndL 2 𝕜 E F` is `WithLp.inrL 2 𝕜 E F`. -/
@[simp]
theorem adjoint_sndL : (WithLp.sndL 2 𝕜 E F).adjoint = inrL 2 𝕜 E F :=
  ((ContinuousLinearMap.eq_adjoint_iff _ _).mpr fun _ _ ↦ by simp).symm

/-- The Hilbert-space adjoint of `WithLp.inrL 2 𝕜 E F` is `WithLp.sndL 2 𝕜 E F`. -/
@[simp]
theorem adjoint_inrL : (inrL 2 𝕜 E F).adjoint = WithLp.sndL 2 𝕜 E F := by
  rw [← adjoint_sndL, ContinuousLinearMap.adjoint_adjoint]

end Adjoint

/-! ### Block operators -/

section Block

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

/-- The operator on `WithLp 2 (E × F)` with the block matrix `[[a, b], [c, d]]`, that is
`(x, y) ↦ (a x + b y, c x + d y)`. -/
def blockL2 (a : E →L[𝕜] E) (b : F →L[𝕜] E) (c : E →L[𝕜] F) (d : F →L[𝕜] F) :
    WithLp 2 (E × F) →L[𝕜] WithLp 2 (E × F) :=
  inlL 2 𝕜 E F ∘L (a ∘L WithLp.fstL 2 𝕜 E F + b ∘L WithLp.sndL 2 𝕜 E F) +
    inrL 2 𝕜 E F ∘L (c ∘L WithLp.fstL 2 𝕜 E F + d ∘L WithLp.sndL 2 𝕜 E F)

@[simp]
theorem blockL2_apply (a : E →L[𝕜] E) (b : F →L[𝕜] E) (c : E →L[𝕜] F) (d : F →L[𝕜] F)
    (z : WithLp 2 (E × F)) :
    blockL2 a b c d z = WithLp.toLp 2 (a z.fst + b z.snd, c z.fst + d z.snd) := by
  simp [blockL2, ← WithLp.toLp_add]

/-- Two block operators agree exactly when their four blocks do. -/
@[simp]
theorem blockL2_inj {a a' : E →L[𝕜] E} {b b' : F →L[𝕜] E} {c c' : E →L[𝕜] F}
    {d d' : F →L[𝕜] F} :
    blockL2 a b c d = blockL2 a' b' c' d' ↔ a = a' ∧ b = b' ∧ c = c' ∧ d = d' := by
  refine ⟨fun h => ⟨?_, ?_, ?_, ?_⟩, by rintro ⟨rfl, rfl, rfl, rfl⟩; rfl⟩ <;> ext x
  · simpa using congr(($h (WithLp.toLp 2 (x, 0))).fst)
  · simpa using congr(($h (WithLp.toLp 2 (0, x))).fst)
  · simpa using congr(($h (WithLp.toLp 2 (x, 0))).snd)
  · simpa using congr(($h (WithLp.toLp 2 (0, x))).snd)

/-- The upper left block of `blockL2 a b c d` is `a`. -/
@[simp]
theorem fstL_comp_blockL2_comp_inlL (a : E →L[𝕜] E) (b : F →L[𝕜] E) (c : E →L[𝕜] F)
    (d : F →L[𝕜] F) : WithLp.fstL 2 𝕜 E F ∘L blockL2 a b c d ∘L inlL 2 𝕜 E F = a :=
  ContinuousLinearMap.ext fun _ => by simp

/-- The upper right block of `blockL2 a b c d` is `b`. -/
@[simp]
theorem fstL_comp_blockL2_comp_inrL (a : E →L[𝕜] E) (b : F →L[𝕜] E) (c : E →L[𝕜] F)
    (d : F →L[𝕜] F) : WithLp.fstL 2 𝕜 E F ∘L blockL2 a b c d ∘L inrL 2 𝕜 E F = b :=
  ContinuousLinearMap.ext fun _ => by simp

/-- The lower left block of `blockL2 a b c d` is `c`. -/
@[simp]
theorem sndL_comp_blockL2_comp_inlL (a : E →L[𝕜] E) (b : F →L[𝕜] E) (c : E →L[𝕜] F)
    (d : F →L[𝕜] F) : WithLp.sndL 2 𝕜 E F ∘L blockL2 a b c d ∘L inlL 2 𝕜 E F = c :=
  ContinuousLinearMap.ext fun _ => by simp

/-- The lower right block of `blockL2 a b c d` is `d`. -/
@[simp]
theorem sndL_comp_blockL2_comp_inrL (a : E →L[𝕜] E) (b : F →L[𝕜] E) (c : E →L[𝕜] F)
    (d : F →L[𝕜] F) : WithLp.sndL 2 𝕜 E F ∘L blockL2 a b c d ∘L inrL 2 𝕜 E F = d :=
  ContinuousLinearMap.ext fun _ => by simp

/-- Every operator on `WithLp 2 (E × F)` is the block operator of its four blocks. -/
theorem blockL2_eta (T : WithLp 2 (E × F) →L[𝕜] WithLp 2 (E × F)) :
    blockL2 (WithLp.fstL 2 𝕜 E F ∘L T ∘L inlL 2 𝕜 E F)
      (WithLp.fstL 2 𝕜 E F ∘L T ∘L inrL 2 𝕜 E F)
      (WithLp.sndL 2 𝕜 E F ∘L T ∘L inlL 2 𝕜 E F)
      (WithLp.sndL 2 𝕜 E F ∘L T ∘L inrL 2 𝕜 E F) = T := by
  refine ContinuousLinearMap.ext fun z => ?_
  have hz : z = inlL 2 𝕜 E F z.fst + inrL 2 𝕜 E F z.snd :=
    WithLp.ofLp_injective 2 (Prod.ext (by simp) (by simp))
  conv_rhs => rw [hz, map_add]
  exact WithLp.ofLp_injective 2 (Prod.ext (by simp) (by simp))

/-- A block operator with zero off-diagonal blocks is the block sum of its diagonal blocks. -/
@[simp]
theorem blockL2_zero_zero (a : E →L[𝕜] E) (d : F →L[𝕜] F) :
    blockL2 a 0 0 d = a.withLpProdMap 2 d :=
  ContinuousLinearMap.ext fun _ => by simp

/-- Block operators multiply as `2 × 2` matrices. -/
theorem blockL2_mul_blockL2 (a a' : E →L[𝕜] E) (b b' : F →L[𝕜] E) (c c' : E →L[𝕜] F)
    (d d' : F →L[𝕜] F) :
    blockL2 a b c d * blockL2 a' b' c' d' =
      blockL2 (a ∘L a' + b ∘L c') (a ∘L b' + b ∘L d') (c ∘L a' + d ∘L c')
        (c ∘L b' + d ∘L d') :=
  ContinuousLinearMap.ext fun _ => by
    simp only [ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_apply, blockL2_apply,
      WithLp.toLp_fst, WithLp.toLp_snd, map_add, add_apply]
    congr 2 <;> abel

theorem blockL2_add_blockL2 (a a' : E →L[𝕜] E) (b b' : F →L[𝕜] E) (c c' : E →L[𝕜] F)
    (d d' : F →L[𝕜] F) :
    blockL2 a b c d + blockL2 a' b' c' d' = blockL2 (a + a') (b + b') (c + c') (d + d') :=
  ContinuousLinearMap.ext fun _ => by
    simp only [add_apply, blockL2_apply, ← WithLp.toLp_add, Prod.mk_add_mk]
    congr 2 <;> abel

theorem blockL2_sub_blockL2 (a a' : E →L[𝕜] E) (b b' : F →L[𝕜] E) (c c' : E →L[𝕜] F)
    (d d' : F →L[𝕜] F) :
    blockL2 a b c d - blockL2 a' b' c' d' = blockL2 (a - a') (b - b') (c - c') (d - d') :=
  ContinuousLinearMap.ext fun _ => by
    simp only [sub_apply, blockL2_apply, ← WithLp.toLp_sub, Prod.mk_sub_mk]
    congr 2 <;> abel

theorem neg_blockL2 (a : E →L[𝕜] E) (b : F →L[𝕜] E) (c : E →L[𝕜] F) (d : F →L[𝕜] F) :
    -blockL2 a b c d = blockL2 (-a) (-b) (-c) (-d) :=
  ContinuousLinearMap.ext fun _ => by
    simp only [neg_apply, blockL2_apply, ← WithLp.toLp_neg, Prod.neg_mk]
    congr 2 <;> abel

/-- A block operator whose four blocks are compact is compact. -/
theorem isCompactOperator_blockL2 {a : E →L[𝕜] E} {b : F →L[𝕜] E} {c : E →L[𝕜] F}
    {d : F →L[𝕜] F} (ha : IsCompactOperator a) (hb : IsCompactOperator b)
    (hc : IsCompactOperator c) (hd : IsCompactOperator d) :
    IsCompactOperator (blockL2 a b c d) := by
  simp only [blockL2, FunLike.coe_add, ContinuousLinearMap.coe_comp]
  exact (((ha.comp_clm _).add (hb.comp_clm _)).clm_comp _).add
    (((hc.comp_clm _).add (hd.comp_clm _)).clm_comp _)

section Adjoint

variable [CompleteSpace E] [CompleteSpace F]

/-- The adjoint of a block operator is its conjugate transpose. -/
@[simp]
theorem adjoint_blockL2 (a : E →L[𝕜] E) (b : F →L[𝕜] E) (c : E →L[𝕜] F) (d : F →L[𝕜] F) :
    (blockL2 a b c d).adjoint = blockL2 a.adjoint c.adjoint b.adjoint d.adjoint := by
  simp only [blockL2, map_add, ContinuousLinearMap.adjoint_comp, adjoint_inlL, adjoint_inrL,
    adjoint_fstL, adjoint_sndL, ContinuousLinearMap.comp_add,
    ContinuousLinearMap.comp_assoc]
  abel

/-- The star of a block operator is its conjugate transpose. -/
@[simp]
theorem star_blockL2 (a : E →L[𝕜] E) (b : F →L[𝕜] E) (c : E →L[𝕜] F) (d : F →L[𝕜] F) :
    star (blockL2 a b c d) = blockL2 (star a) c.adjoint b.adjoint (star d) := by
  simp only [ContinuousLinearMap.star_eq_adjoint, adjoint_blockL2]

end Adjoint

end Block

end WithLp

open scoped ENNReal InnerProduct InnerProductSpace

namespace ContinuousLinearMap

variable {𝕜 E₁ E₂ : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E₁] [InnerProductSpace 𝕜 E₁] [CompleteSpace E₁]
  [NormedAddCommGroup E₂] [InnerProductSpace 𝕜 E₂] [CompleteSpace E₂]

/-- **Adjoint of a Hilbert block sum.** `(f ⊕ g)† = f† ⊕ g†`. -/
@[simp]
theorem adjoint_withLpProdMap {F₁ F₂ : Type*}
    [NormedAddCommGroup F₁] [InnerProductSpace 𝕜 F₁] [CompleteSpace F₁]
    [NormedAddCommGroup F₂] [InnerProductSpace 𝕜 F₂] [CompleteSpace F₂]
    (f : E₁ →L[𝕜] F₁) (g : E₂ →L[𝕜] F₂) :
    (f.withLpProdMap 2 g)† = (f†).withLpProdMap 2 (g†) := by
  refine ((eq_adjoint_iff _ _).mpr fun x y ↦ ?_).symm
  simp [WithLp.prod_inner_apply, adjoint_inner_left]

/-- **Star of a Hilbert block sum.** `star (f ⊕ g) = star f ⊕ star g`. -/
@[simp]
theorem star_withLpProdMap (f : E₁ →L[𝕜] E₁) (g : E₂ →L[𝕜] E₂) :
    star (f.withLpProdMap 2 g) = (star f).withLpProdMap 2 (star g) :=
  adjoint_withLpProdMap f g

/-- The orthogonal block sum `(T₁, T₂) ↦ T₁ ⊕ T₂` as a star algebra homomorphism from pairs of
operators to operators on the Hilbert direct sum. -/
noncomputable def withLpProdMapStarAlgHom :
    (E₁ →L[𝕜] E₁) × (E₂ →L[𝕜] E₂) →⋆ₐ[𝕜] (WithLp 2 (E₁ × E₂) →L[𝕜] WithLp 2 (E₁ × E₂)) where
  toFun T := T.1.withLpProdMap 2 T.2
  map_one' := withLpProdMap_one
  map_mul' T S := withLpProdMap_mul T.1 S.1 T.2 S.2
  map_zero' := withLpProdMap_zero
  map_add' T S := withLpProdMap_add T.1 S.1 T.2 S.2
  commutes' c := by
    simp only [Algebra.algebraMap_eq_smul_one, Prod.smul_fst, Prod.smul_snd, Prod.fst_one,
      Prod.snd_one, withLpProdMap_smul, withLpProdMap_one]
  map_star' T := (star_withLpProdMap T.1 T.2).symm

@[simp]
theorem withLpProdMapStarAlgHom_apply (T : (E₁ →L[𝕜] E₁) × (E₂ →L[𝕜] E₂)) :
    withLpProdMapStarAlgHom T = T.1.withLpProdMap 2 T.2 :=
  (rfl)

/-- A Hilbert block sum is self-adjoint if and only if both blocks are self-adjoint. -/
@[simp]
theorem isSelfAdjoint_withLpProdMap_iff (f : E₁ →L[𝕜] E₁) (g : E₂ →L[𝕜] E₂) :
    IsSelfAdjoint (f.withLpProdMap 2 g) ↔ IsSelfAdjoint f ∧ IsSelfAdjoint g := by
  simp only [IsSelfAdjoint, star_withLpProdMap]
  refine ⟨fun h ↦ ⟨?_, ?_⟩, fun h ↦ by rw [h.1, h.2]⟩
  · ext x
    simpa using congrArg WithLp.fst (DFunLike.congr_fun h (WithLp.toLp 2 (x, 0)))
  · ext y
    simpa using congrArg WithLp.snd (DFunLike.congr_fun h (WithLp.toLp 2 (0, y)))

end ContinuousLinearMap

namespace NonUnitalStarAlgHom

variable {𝕜 A E₁ E₂ : Type*} [RCLike 𝕜]
  [NonUnitalNonAssocSemiring A] [Module 𝕜 A] [Star A]
  [NormedAddCommGroup E₁] [InnerProductSpace 𝕜 E₁] [CompleteSpace E₁]
  [NormedAddCommGroup E₂] [InnerProductSpace 𝕜 E₂] [CompleteSpace E₂]

/-- The orthogonal direct sum of two `⋆`-representations on `WithLp 2 (E₁ × E₂)`. -/
noncomputable def prodStarRep (π₁ : A →⋆ₙₐ[𝕜] E₁ →L[𝕜] E₁) (π₂ : A →⋆ₙₐ[𝕜] E₂ →L[𝕜] E₂) :
    A →⋆ₙₐ[𝕜] WithLp 2 (E₁ × E₂) →L[𝕜] WithLp 2 (E₁ × E₂) :=
  ContinuousLinearMap.withLpProdMapStarAlgHom.toNonUnitalStarAlgHom.comp (π₁.prod π₂)

/-- Evaluation of the orthogonal direct sum `π₁.prodStarRep π₂` at an element `a : A`. -/
@[simp]
theorem prodStarRep_apply (π₁ : A →⋆ₙₐ[𝕜] E₁ →L[𝕜] E₁) (π₂ : A →⋆ₙₐ[𝕜] E₂ →L[𝕜] E₂) (a : A) :
    π₁.prodStarRep π₂ a = (π₁ a).withLpProdMap 2 (π₂ a) :=
  (rfl)

end NonUnitalStarAlgHom
