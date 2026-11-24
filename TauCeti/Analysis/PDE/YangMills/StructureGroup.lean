/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.BracketNorm
public import TauCeti.Geometry.Lie.Subgroup.Unitary.Matrix
public import Mathlib.LinearAlgebra.QuadraticForm.Prod
public import TauCeti.LinearAlgebra.QuadraticForm.PosDef

/-!
# Compact matrix structure groups

The gauge theory of connections on Euclidean space takes as structure group a compact group `G`
of unitary matrices, with Lie algebra `𝔤 = {X : exp (t X) ∈ G for all real t}` acting on itself
by `Ad(g) X = g X g⁻¹`, together with an inner product `⟨·,·⟩` on `𝔤` that is invariant under
`Ad(G)`. All pointwise norms of connections and curvatures, `|A|² = ∑ⱼ ⟨Aⱼ, Aⱼ⟩`, are formed
with this inner product, and its `Ad`-invariance is what makes them gauge invariant.

This file bundles such a triple as `TauCeti.CompactMatrixStructureGroup n`: a closed subgroup of
`Matrix.unitaryGroup n ℂ` (closed subgroups of `U(n)` are exactly the compact ones), with a
symmetric positive-definite `Ad`-invariant bilinear form on its Lie algebra
`ClosedSubgroup.matrixLieAlgebra`. The group need not be connected, so `Ad`-invariance is part of
the data: it implies that every `ad X` is skew-adjoint, but the converse fails for disconnected
groups.

The structure constant `γ₀ = max {|⁅X, Y⁆| : |X| ≤ 1, |Y| ≤ 1}` of a structure group is the norm
`S.innerForm.toQuadraticMap.lieBracketNorm` of the bracket of `𝔤` for its inner product
(`QuadraticMap.lieBracketNorm`). It does not increase under restriction, and the structure
constant of a block-diagonal product is the larger of those of the factors.

## Main definitions

* `TauCeti.CompactMatrixStructureGroup`: a closed subgroup of `U(n)` with an `Ad`-invariant inner
  product on its Lie algebra.
* `TauCeti.CompactMatrixStructureGroup.ofTraceForm`: every closed subgroup of `U(n)` with the
  trace form `⟨X, Y⟩ = -Re tr (X Y)`.
* `TauCeti.CompactMatrixStructureGroup.restrict`: the restriction to a closed subgroup.
* `TauCeti.CompactMatrixStructureGroup.prod`: the block-diagonal product of two structure groups,
  with the orthogonal sum of the inner products.

## Main results

* `TauCeti.CompactMatrixStructureGroup.innerForm_matrixAdjointRepresentation`: each `Ad(g)` is an
  isometry of the inner product.
* `TauCeti.CompactMatrixStructureGroup.innerForm_lie_left`: each `ad X` is skew-adjoint,
  `⟨[X, Y], Z⟩ = -⟨Y, [X, Z]⟩`.
* `TauCeti.CompactMatrixStructureGroup.lieBracketNorm_restrict_le`: restriction does not increase
  the structure constant.
* `TauCeti.CompactMatrixStructureGroup.lieBracketNorm_prod`: the structure constant of a
  block-diagonal product is the maximum of those of the factors.

## References

* S.-J. Oh and D. Tataru, *The Yang–Mills heat flow and the caloric gauge*, Astérisque 436
  (2022), arXiv:1709.08599, Section 1 (the structure group and its invariant inner product).
* S.-J. Oh and D. Tataru, *The hyperbolic Yang–Mills equation for connections in an arbitrary
  topological class*, Comm. Math. Phys. 365 (2019), arXiv:1709.08604, Section 1.
-/

public section

noncomputable section

attribute [local instance 100] LieRing.ofAssociativeRing

namespace TauCeti

/-- A **compact matrix structure group**: a closed (equivalently, compact) subgroup `group` of the
unitary group `U(n)`, together with an inner product `innerForm` on its Lie algebra
`group.matrixLieAlgebra`, given as a symmetric positive-definite real bilinear form invariant under
the adjoint action `Ad(g) X = g X g⁻¹` of every `g ∈ group`. -/
structure CompactMatrixStructureGroup (n : Type*) [Fintype n] [DecidableEq n] where
  /-- The structure group, a closed subgroup of the unitary group. -/
  group : ClosedSubgroup (Matrix.unitaryGroup n ℂ)
  /-- The inner product on the Lie algebra of the structure group. -/
  innerForm : LinearMap.BilinForm ℝ group.matrixLieAlgebra
  /-- The inner product is symmetric. -/
  isSymm_innerForm : innerForm.IsSymm
  /-- The inner product is positive definite. -/
  posDef_innerForm : innerForm.toQuadraticMap.PosDef
  /-- The inner product is invariant under the adjoint action of the structure group. -/
  isInvariantForm_innerForm :
    Representation.IsInvariantForm group.matrixAdjointRepresentation innerForm

namespace CompactMatrixStructureGroup

variable {n : Type*} [Fintype n] [DecidableEq n] (S : CompactMatrixStructureGroup n)

/-- Each `Ad(g)`, `g ∈ G`, is an isometry of the inner product. -/
@[simp]
theorem innerForm_matrixAdjointRepresentation (g : S.group) (X Y : S.group.matrixLieAlgebra) :
    S.innerForm (S.group.matrixAdjointRepresentation g X)
      (S.group.matrixAdjointRepresentation g Y) = S.innerForm X Y :=
  Representation.isInvariantForm_iff.mp S.isInvariantForm_innerForm g X Y

/-- The inner product is invariant under every `ad X`, in the sense of Mathlib's
`LinearMap.BilinForm.lieInvariant`. -/
theorem lieInvariant_innerForm : S.innerForm.lieInvariant S.group.matrixLieAlgebra :=
  ClosedSubgroup.lieInvariant_of_isInvariantForm S.isInvariantForm_innerForm

/-- Each `ad X` is skew-adjoint for the inner product: `⟨[X, Y], Z⟩ = -⟨Y, [X, Z]⟩`. -/
theorem innerForm_lie_left (X Y Z : S.group.matrixLieAlgebra) :
    S.innerForm ⁅X, Y⁆ Z = -S.innerForm Y ⁅X, Z⁆ :=
  S.lieInvariant_innerForm X Y Z

/-- The inner product is symmetric. -/
theorem innerForm_comm (X Y : S.group.matrixLieAlgebra) : S.innerForm X Y = S.innerForm Y X :=
  S.isSymm_innerForm.eq X Y

/-- The inner product of a nonzero element with itself is positive. -/
theorem innerForm_self_pos {X : S.group.matrixLieAlgebra} (hX : X ≠ 0) :
    0 < S.innerForm X X :=
  S.posDef_innerForm X hX

/-- The inner product of an element with itself is nonnegative. -/
theorem innerForm_self_nonneg (X : S.group.matrixLieAlgebra) : 0 ≤ S.innerForm X X :=
  S.posDef_innerForm.nonneg X

/-- An element is zero exactly when its inner product with itself vanishes. -/
@[simp]
theorem innerForm_self_eq_zero {X : S.group.matrixLieAlgebra} : S.innerForm X X = 0 ↔ X = 0 :=
  S.posDef_innerForm.anisotropic.eq_zero_iff

section OfTraceForm

/-- **Every closed subgroup of `U(n)` is a structure group** for the trace form
`⟨X, Y⟩ = -Re tr (X Y)`. -/
-- The type of `innerForm` depends on `group`, so its value can only be stated once `group` reduces.
@[expose]
def ofTraceForm (G : ClosedSubgroup (Matrix.unitaryGroup n ℂ)) :
    CompactMatrixStructureGroup n where
  group := G
  innerForm := G.matrixTraceForm
  isSymm_innerForm := ClosedSubgroup.isSymm_matrixTraceForm
  posDef_innerForm := ClosedSubgroup.posDef_matrixTraceForm
  isInvariantForm_innerForm := ClosedSubgroup.isInvariantForm_matrixTraceForm

@[simp]
theorem ofTraceForm_group (G : ClosedSubgroup (Matrix.unitaryGroup n ℂ)) :
    (ofTraceForm G).group = G :=
  (rfl)

@[simp]
theorem ofTraceForm_innerForm (G : ClosedSubgroup (Matrix.unitaryGroup n ℂ)) :
    (ofTraceForm G).innerForm = G.matrixTraceForm :=
  (rfl)

end OfTraceForm

section Restrict

variable {H : ClosedSubgroup (Matrix.unitaryGroup n ℂ)}

/-- **Restriction to a closed subgroup** `H ≤ G`: the Lie algebra of `H` is a Lie subalgebra of
that of `G`, and the inner product restricts to it. -/
-- The type of `innerForm` depends on `group`, so its value can only be stated once `group` reduces.
@[expose]
def restrict (S : CompactMatrixStructureGroup n) (hH : H ≤ S.group) :
    CompactMatrixStructureGroup n where
  group := H
  innerForm := S.innerForm.compl₁₂
    (LieSubalgebra.inclusion (ClosedSubgroup.matrixLieAlgebra_mono hH)).toLinearMap
    (LieSubalgebra.inclusion (ClosedSubgroup.matrixLieAlgebra_mono hH)).toLinearMap
  isSymm_innerForm := ⟨fun X Y ↦ S.innerForm_comm _ _⟩
  posDef_innerForm := LinearMap.BilinForm.posDef_toQuadraticMap_compl₁₂ _ S.posDef_innerForm _
    (LieSubalgebra.inclusion_injective (ClosedSubgroup.matrixLieAlgebra_mono hH))
  isInvariantForm_innerForm := Representation.isInvariantForm_iff.mpr fun g X Y ↦ by
    have hAd (Z : H.matrixLieAlgebra) :
        LieSubalgebra.inclusion (ClosedSubgroup.matrixLieAlgebra_mono hH)
            (H.matrixAdjointRepresentation g Z) =
          S.group.matrixAdjointRepresentation ⟨g, hH g.property⟩
            (LieSubalgebra.inclusion (ClosedSubgroup.matrixLieAlgebra_mono hH) Z) :=
      Subtype.ext (by simp)
    simp only [LinearMap.compl₁₂_apply, LieHom.coe_toLinearMap, hAd,
      innerForm_matrixAdjointRepresentation]

@[simp]
theorem restrict_group (hH : H ≤ S.group) : (S.restrict hH).group = H :=
  (rfl)

/-- The inner product of the restriction is the inner product of the ambient Lie algebra. -/
@[simp]
theorem restrict_innerForm_apply (hH : H ≤ S.group) (X Y : H.matrixLieAlgebra) :
    (S.restrict hH).innerForm X Y =
      S.innerForm (LieSubalgebra.inclusion (ClosedSubgroup.matrixLieAlgebra_mono hH) X)
        (LieSubalgebra.inclusion (ClosedSubgroup.matrixLieAlgebra_mono hH) Y) :=
  (rfl)

end Restrict

section Prod

variable {m : Type*} [Fintype m] [DecidableEq m]

/-- **The block-diagonal product of structure groups**: the closed subgroup
`G₁ × G₂ = {diag(g₁, g₂)}` of `U(n ⊕ m)`, whose Lie algebra is `𝔤₁ × 𝔤₂`, with the orthogonal sum
`⟨X, Y⟩ = ⟨X₁, Y₁⟩₁ + ⟨X₂, Y₂⟩₂` of the inner products on the diagonal blocks. -/
-- The type of `innerForm` depends on `group`, so its value can only be stated once `group` reduces.
@[expose]
def prod (S₁ : CompactMatrixStructureGroup n) (S₂ : CompactMatrixStructureGroup m) :
    CompactMatrixStructureGroup (n ⊕ m) where
  group := S₁.group.fromBlocksProd S₂.group
  innerForm :=
    (S₁.innerForm.compl₁₂ (LinearMap.fst ℝ _ _) (LinearMap.fst ℝ _ _) +
        S₂.innerForm.compl₁₂ (LinearMap.snd ℝ _ _) (LinearMap.snd ℝ _ _)).compl₁₂
      (S₁.group.matrixLieAlgebraFromBlocksProdEquiv S₂.group).toLinearEquiv.toLinearMap
      (S₁.group.matrixLieAlgebraFromBlocksProdEquiv S₂.group).toLinearEquiv.toLinearMap
  isSymm_innerForm := ⟨fun X Y ↦ by
    simp only [LinearMap.compl₁₂_apply, LinearMap.add_apply, LinearMap.fst_apply,
      LinearMap.snd_apply, S₁.innerForm_comm, S₂.innerForm_comm]⟩
  posDef_innerForm := by
    refine LinearMap.BilinForm.posDef_toQuadraticMap_compl₁₂ _ ?_ _
      (S₁.group.matrixLieAlgebraFromBlocksProdEquiv S₂.group).toLinearEquiv.injective
    -- The quadratic map of the orthogonal sum of the two forms is, by definition, the product
    -- `QuadraticMap.prod` of their quadratic maps.
    exact S₁.posDef_innerForm.prod S₂.posDef_innerForm
  isInvariantForm_innerForm := Representation.isInvariantForm_iff.mpr fun g X Y ↦ by
    obtain ⟨g₁, h₁, g₂, h₂, hg⟩ := ClosedSubgroup.mem_fromBlocksProd_iff.mp g.property
    have hg' : g = ⟨Matrix.UnitaryGroup.sum (g₁, g₂),
        ClosedSubgroup.sum_mem_fromBlocksProd h₁ h₂⟩ :=
      Subtype.ext (Subtype.ext (by simpa using hg))
    subst hg'
    simp only [LinearMap.compl₁₂_apply, LinearEquiv.coe_coe, LieEquiv.coe_toLinearEquiv]
    rw [ClosedSubgroup.matrixLieAlgebraFromBlocksProdEquiv_matrixAdjointRepresentation h₁ h₂ X,
      ClosedSubgroup.matrixLieAlgebraFromBlocksProdEquiv_matrixAdjointRepresentation h₁ h₂ Y]
    simp only [LinearMap.add_apply, LinearMap.compl₁₂_apply, LinearMap.fst_apply,
      LinearMap.snd_apply, innerForm_matrixAdjointRepresentation]

@[simp]
theorem prod_group (S₁ : CompactMatrixStructureGroup n) (S₂ : CompactMatrixStructureGroup m) :
    (S₁.prod S₂).group = S₁.group.fromBlocksProd S₂.group :=
  (rfl)

/-- The inner product of the product is the sum of the inner products of the diagonal blocks. -/
@[simp]
theorem prod_innerForm_apply (S₁ : CompactMatrixStructureGroup n)
    (S₂ : CompactMatrixStructureGroup m)
    (X Y : (S₁.group.fromBlocksProd S₂.group).matrixLieAlgebra) :
    (S₁.prod S₂).innerForm X Y =
      S₁.innerForm (S₁.group.matrixLieAlgebraFromBlocksProdEquiv S₂.group X).1
          (S₁.group.matrixLieAlgebraFromBlocksProdEquiv S₂.group Y).1 +
        S₂.innerForm (S₁.group.matrixLieAlgebraFromBlocksProdEquiv S₂.group X).2
          (S₁.group.matrixLieAlgebraFromBlocksProdEquiv S₂.group Y).2 :=
  (rfl)

end Prod

section LieBracketNorm

/-! ### The structure constant

The structure constant `γ₀(𝔤, ⟨·,·⟩)` of a structure group is the norm
`S.innerForm.toQuadraticMap.lieBracketNorm` of the Lie bracket of `𝔤` for its inner product. -/

variable {m : Type*} [Fintype m] [DecidableEq m]

/-- The structure constant does not increase under restriction to a closed subgroup. -/
theorem lieBracketNorm_restrict_le {H : ClosedSubgroup (Matrix.unitaryGroup n ℂ)}
    (hH : H ≤ S.group) :
    (S.restrict hH).innerForm.toQuadraticMap.lieBracketNorm ≤
      S.innerForm.toQuadraticMap.lieBracketNorm :=
  QuadraticMap.lieBracketNorm_comp_le S.posDef_innerForm
    (LieSubalgebra.inclusion (ClosedSubgroup.matrixLieAlgebra_mono hH))

/-- **The structure constant of a block-diagonal product** is the larger of the structure
constants of the factors: `γ₀(𝔤₁ ⊕ 𝔤₂) = max (γ₀(𝔤₁)) (γ₀(𝔤₂))`. -/
theorem lieBracketNorm_prod (S₁ : CompactMatrixStructureGroup n)
    (S₂ : CompactMatrixStructureGroup m) :
    (S₁.prod S₂).innerForm.toQuadraticMap.lieBracketNorm =
      max S₁.innerForm.toQuadraticMap.lieBracketNorm
        S₂.innerForm.toQuadraticMap.lieBracketNorm := by
  have h : (S₁.prod S₂).innerForm.toQuadraticMap =
      (S₁.innerForm.toQuadraticMap.prod S₂.innerForm.toQuadraticMap).comp
        (S₁.group.matrixLieAlgebraFromBlocksProdEquiv S₂.group).toLinearEquiv.toLinearMap := by
    ext X
    -- The right side is a quadratic map on the carrier of `S₁.group.fromBlocksProd S₂.group`,
    -- which is that of `(S₁.prod S₂).group` only after unfolding `prod` (`prod_group` is `rfl`),
    -- so `QuadraticMap.comp_apply` and `QuadraticMap.prod_apply` cannot rewrite it. Pointwise,
    -- `toQuadraticMap`, `QuadraticMap.comp` and `QuadraticMap.prod` unfold both sides to the two
    -- sides of `prod_innerForm_apply` at `X X`.
    exact prod_innerForm_apply S₁ S₂ X X
  rw [h]
  exact (QuadraticMap.lieBracketNorm_comp_lieEquiv _).trans
    (QuadraticMap.lieBracketNorm_prod S₁.posDef_innerForm S₂.posDef_innerForm)

end LieBracketNorm

end CompactMatrixStructureGroup

end TauCeti
