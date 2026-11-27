/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.ProdL2
public import Mathlib.Analysis.Normed.Operator.Compact.Basic
public import TauCeti.Analysis.Normed.Lp.ProdLp

/-!
# Coordinate embeddings and block operators on the `L²` direct sum `WithLp 2 (E × F)`

For inner product spaces `E` and `F` over `𝕜` (`[RCLike 𝕜]`), `WithLp.inlL2 𝕜 E F` and
`WithLp.inrL2 𝕜 E F` are the coordinate embeddings `x ↦ (x, 0)` and `y ↦ (0, y)` into
`WithLp 2 (E × F)`. These are linear isometries (`WithLp.isometry_inlL2`, `WithLp.isometry_inrL2`)
of operator norm `1` on nontrivial spaces (`WithLp.norm_inlL2`, `WithLp.norm_inrL2`). When `E` and
`F` are complete, they are the Hilbert-space adjoints of the coordinate projections
`WithLp.fstL 2 𝕜 E F` and `WithLp.sndL 2 𝕜 E F` (`WithLp.adjoint_fstL`, `WithLp.adjoint_sndL`,
`WithLp.adjoint_inlL2`, `WithLp.adjoint_inrL2`). The diagonal embedding `WithLp.diagL2 𝕜 E`,
`x ↦ (x, x)`, has adjoint `(x, y) ↦ x + y` (`WithLp.adjoint_diagL2`); being continuous linear,
the map `x ↦ (x, x)` is smooth (`WithLp.contDiff_toLp_diag`).

An operator on `WithLp 2 (E × F)` is a `2 × 2` block matrix of operators between the factors:
`WithLp.blockL2 a b c d` is the operator `(x, y) ↦ (a x + b y, c x + d y)`, and every operator is
the block operator of its four blocks (`WithLp.blockL2_eta`), and the blocks of
`WithLp.blockL2 a b c d` are `a`, `b`, `c` and `d` (`WithLp.fstL_comp_blockL2_comp_inlL2` and its
three siblings). Block operators multiply as matrices (`WithLp.blockL2_mul_blockL2`), their
adjoint is the conjugate transpose (`WithLp.adjoint_blockL2`), and a block operator with compact
entries is compact (`WithLp.isCompactOperator_blockL2`). The block diagonal operators are the
block sums `ContinuousLinearMap.withLpProdMap` (`WithLp.blockL2_zero_zero`).

The orthogonal complement of the diagonal `WithLp.diagonal 2 𝕜 E` of `WithLp 2 (E × E)` consists
of the antidiagonal vectors `(η, -η)` (`WithLp.mem_orthogonal_diagonal_iff`).
-/

public section

namespace WithLp

variable (𝕜 E F : Type*) [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

/-- The isometric embedding `x ↦ (x, 0)` of `E` into the `L²` direct sum `WithLp 2 (E × F)`. -/
def inlL2 : E →L[𝕜] WithLp 2 (E × F) :=
  (WithLp.prodContinuousLinearEquiv 2 𝕜 E F).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.inl 𝕜 E F)

@[simp] theorem inlL2_apply (x : E) : inlL2 𝕜 E F x = WithLp.toLp 2 (x, 0) := by rfl

/-- The isometric embedding `y ↦ (0, y)` of `F` into the `L²` direct sum `WithLp 2 (E × F)`. -/
def inrL2 : F →L[𝕜] WithLp 2 (E × F) :=
  (WithLp.prodContinuousLinearEquiv 2 𝕜 E F).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.inr 𝕜 E F)

@[simp] theorem inrL2_apply (y : F) : inrL2 𝕜 E F y = WithLp.toLp 2 (0, y) := by rfl

@[simp] theorem fstL_comp_inlL2 : (WithLp.fstL 2 𝕜 E F).comp (inlL2 𝕜 E F) = 1 := by ext; simp

@[simp] theorem sndL_comp_inrL2 : (WithLp.sndL 2 𝕜 E F).comp (inrL2 𝕜 E F) = 1 := by ext; simp

@[simp] theorem fstL_comp_inrL2 : (WithLp.fstL 2 𝕜 E F).comp (inrL2 𝕜 E F) = 0 := by ext; simp

@[simp] theorem sndL_comp_inlL2 : (WithLp.sndL 2 𝕜 E F).comp (inlL2 𝕜 E F) = 0 := by ext; simp

/-- `WithLp.inlL2 𝕜 E F` is an isometry. -/
theorem isometry_inlL2 : Isometry (inlL2 𝕜 E F) :=
  AddMonoidHomClass.isometry_of_norm _ fun _ => by simp

/-- `WithLp.inrL2 𝕜 E F` is an isometry. -/
theorem isometry_inrL2 : Isometry (inrL2 𝕜 E F) :=
  AddMonoidHomClass.isometry_of_norm _ fun _ => by simp

/-- On a nontrivial inner product space `E`, `WithLp.inlL2 𝕜 E F` has operator norm `1`. -/
@[simp] theorem norm_inlL2 [Nontrivial E] : ‖inlL2 𝕜 E F‖ = 1 :=
  (inlL2 𝕜 E F).homothety_norm fun _ => by simp

/-- On a nontrivial inner product space `F`, `WithLp.inrL2 𝕜 E F` has operator norm `1`. -/
@[simp] theorem norm_inrL2 [Nontrivial F] : ‖inrL2 𝕜 E F‖ = 1 :=
  (inrL2 𝕜 E F).homothety_norm fun _ => by simp

/-- The diagonal embedding `x ↦ (x, x)` of `E` into the `L²` direct sum `WithLp 2 (E × E)`. -/
def diagL2 : E →L[𝕜] WithLp 2 (E × E) :=
  (WithLp.prodContinuousLinearEquiv 2 𝕜 E E).symm.toContinuousLinearMap.comp
    ((ContinuousLinearMap.id 𝕜 E).prod (ContinuousLinearMap.id 𝕜 E))

@[simp] theorem diagL2_apply (x : E) : diagL2 𝕜 E x = WithLp.toLp 2 (x, x) := by rfl

/-- The diagonal embedding `WithLp.diagL2 𝕜 E`, as a function, is `x ↦ (x, x)`. -/
theorem coe_diagL2 : ⇑(diagL2 𝕜 E) = fun x ↦ WithLp.toLp 2 (x, x) := by rfl

/-- The diagonal map `x ↦ (x, x)` into `WithLp 2 (E × E)` is smooth, being the continuous linear
map `WithLp.diagL2 𝕜 E`. -/
theorem contDiff_toLp_diag {n : WithTop ℕ∞} : ContDiff 𝕜 n fun x : E ↦ WithLp.toLp 2 (x, x) :=
  coe_diagL2 𝕜 E ▸ (diagL2 𝕜 E).contDiff

section Adjoint

variable [CompleteSpace E] [CompleteSpace F]

@[simp] theorem adjoint_fstL : (WithLp.fstL 2 𝕜 E F).adjoint = inlL2 𝕜 E F :=
  ((ContinuousLinearMap.eq_adjoint_iff _ _).mpr fun _ _ => by simp).symm

@[simp] theorem adjoint_inlL2 : (inlL2 𝕜 E F).adjoint = WithLp.fstL 2 𝕜 E F := by
  rw [← adjoint_fstL, ContinuousLinearMap.adjoint_adjoint]

@[simp] theorem adjoint_sndL : (WithLp.sndL 2 𝕜 E F).adjoint = inrL2 𝕜 E F :=
  ((ContinuousLinearMap.eq_adjoint_iff _ _).mpr fun _ _ => by simp).symm

@[simp] theorem adjoint_inrL2 : (inrL2 𝕜 E F).adjoint = WithLp.sndL 2 𝕜 E F := by
  rw [← adjoint_sndL, ContinuousLinearMap.adjoint_adjoint]

/-- The adjoint of the diagonal embedding is the sum of the coordinates, `(x, y) ↦ x + y`. -/
theorem adjoint_diagL2 : (diagL2 𝕜 E).adjoint = WithLp.fstL 2 𝕜 E E + WithLp.sndL 2 𝕜 E E :=
  ((ContinuousLinearMap.eq_adjoint_iff _ _).mpr fun _ _ => by
    simp [WithLp.prod_inner_apply, inner_add_left]).symm

@[simp] theorem adjoint_diagL2_apply (z : WithLp 2 (E × E)) :
    (diagL2 𝕜 E).adjoint z = z.fst + z.snd := by
  simp [adjoint_diagL2]

end Adjoint

/-! ### The diagonal -/

variable {𝕜 E} in
/-- The vectors orthogonal to the diagonal of `WithLp 2 (E × E)` are the `(η, -η)`. -/
@[simp]
theorem mem_orthogonal_diagonal_iff {ζ : WithLp 2 (E × E)} :
    ζ ∈ (diagonal 2 𝕜 E)ᗮ ↔ ζ.snd = -ζ.fst := by
  rw [Submodule.mem_orthogonal]
  refine ⟨fun h ↦ ?_, fun h u hu ↦ ?_⟩
  · have h' := h (toLp 2 (ζ.fst + ζ.snd, ζ.fst + ζ.snd)) (mem_diagonal_iff.2 rfl)
    rw [prod_inner_apply] at h'
    simp only [ofLp_fst, ofLp_snd] at h'
    rw [← inner_add_right, inner_self_eq_zero] at h'
    exact eq_neg_iff_add_eq_zero.2 (by rwa [add_comm])
  · simp [prod_inner_apply, mem_diagonal_iff.1 hu, h]

/-! ### Block operators -/

section Block

variable {𝕜 E F}

/-- The operator on `WithLp 2 (E × F)` with the block matrix `[[a, b], [c, d]]`, that is
`(x, y) ↦ (a x + b y, c x + d y)`. -/
def blockL2 (a : E →L[𝕜] E) (b : F →L[𝕜] E) (c : E →L[𝕜] F) (d : F →L[𝕜] F) :
    WithLp 2 (E × F) →L[𝕜] WithLp 2 (E × F) :=
  inlL2 𝕜 E F ∘L (a ∘L WithLp.fstL 2 𝕜 E F + b ∘L WithLp.sndL 2 𝕜 E F) +
    inrL2 𝕜 E F ∘L (c ∘L WithLp.fstL 2 𝕜 E F + d ∘L WithLp.sndL 2 𝕜 E F)

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
theorem fstL_comp_blockL2_comp_inlL2 (a : E →L[𝕜] E) (b : F →L[𝕜] E) (c : E →L[𝕜] F)
    (d : F →L[𝕜] F) : WithLp.fstL 2 𝕜 E F ∘L blockL2 a b c d ∘L inlL2 𝕜 E F = a :=
  ContinuousLinearMap.ext fun _ => by simp

/-- The upper right block of `blockL2 a b c d` is `b`. -/
@[simp]
theorem fstL_comp_blockL2_comp_inrL2 (a : E →L[𝕜] E) (b : F →L[𝕜] E) (c : E →L[𝕜] F)
    (d : F →L[𝕜] F) : WithLp.fstL 2 𝕜 E F ∘L blockL2 a b c d ∘L inrL2 𝕜 E F = b :=
  ContinuousLinearMap.ext fun _ => by simp

/-- The lower left block of `blockL2 a b c d` is `c`. -/
@[simp]
theorem sndL_comp_blockL2_comp_inlL2 (a : E →L[𝕜] E) (b : F →L[𝕜] E) (c : E →L[𝕜] F)
    (d : F →L[𝕜] F) : WithLp.sndL 2 𝕜 E F ∘L blockL2 a b c d ∘L inlL2 𝕜 E F = c :=
  ContinuousLinearMap.ext fun _ => by simp

/-- The lower right block of `blockL2 a b c d` is `d`. -/
@[simp]
theorem sndL_comp_blockL2_comp_inrL2 (a : E →L[𝕜] E) (b : F →L[𝕜] E) (c : E →L[𝕜] F)
    (d : F →L[𝕜] F) : WithLp.sndL 2 𝕜 E F ∘L blockL2 a b c d ∘L inrL2 𝕜 E F = d :=
  ContinuousLinearMap.ext fun _ => by simp

/-- Every operator on `WithLp 2 (E × F)` is the block operator of its four blocks. -/
theorem blockL2_eta (T : WithLp 2 (E × F) →L[𝕜] WithLp 2 (E × F)) :
    blockL2 (WithLp.fstL 2 𝕜 E F ∘L T ∘L inlL2 𝕜 E F) (WithLp.fstL 2 𝕜 E F ∘L T ∘L inrL2 𝕜 E F)
      (WithLp.sndL 2 𝕜 E F ∘L T ∘L inlL2 𝕜 E F) (WithLp.sndL 2 𝕜 E F ∘L T ∘L inrL2 𝕜 E F) = T := by
  refine ContinuousLinearMap.ext fun z => ?_
  have hz : z = inlL2 𝕜 E F z.fst + inrL2 𝕜 E F z.snd :=
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
  simp only [blockL2, map_add, ContinuousLinearMap.adjoint_comp, adjoint_inlL2, adjoint_inrL2,
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
