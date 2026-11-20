/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.InvariantForm
public import Mathlib.Algebra.Lie.Prod
public import Mathlib.Analysis.Normed.Algebra.MatrixExponential
public import Mathlib.LinearAlgebra.QuadraticForm.Basic
public import Mathlib.Topology.Algebra.Group.ClosedSubgroup
public import TauCeti.RepresentationTheory.InvariantForm
public import TauCeti.Topology.Algebra.UnitaryGroup
import Mathlib.Algebra.Star.UnitaryStarAlgAut
import TauCeti.Analysis.Matrix.Exponential.Block
import TauCeti.Analysis.Matrix.Frobenius
import TauCeti.Analysis.Matrix.Normed
import TauCeti.Analysis.Normed.Algebra.MatrixExponential
import TauCeti.Analysis.SpecialFunctions.Exponential
import TauCeti.Geometry.Lie.Subgroup.Unitary.Basic
import TauCeti.LinearAlgebra.Matrix.Block

/-!
# The matrix Lie algebra of a closed subgroup of the unitary group

For a closed subgroup `G` of the unitary group `U(n) = Matrix.unitaryGroup n 𝕜` (over `ℝ` or `ℂ`),
this file defines its Lie algebra as a real Lie subalgebra of the matrices,
`𝔤 = {X : exp (t • X) ∈ G for all real t}`, with the commutator bracket, and the adjoint action
`Ad(g) X = g X g⁻¹` of `G` on it. This is the concrete form in which compact matrix groups enter
gauge theory: connections and curvatures are `𝔤`-valued matrix functions, and gauge
transformations act on them by `Ad`.

That `𝔤` is closed under addition and the commutator is the closed-subgroup theorem. It is read off
from `TauCeti.Lie.lieSubalgebraOfSubgroup`, the Lie algebra of the closed subgroup of the units
of the matrix algebra that `G` determines, through the identification
`TauCeti.Lie.unitsLieAlgebraLieEquiv_symm_mem_lieSubalgebraOfSubgroup_iff` of its members with the
generators of exponential lines in the subgroup. The same identification shows that `𝔤` consists of
skew-Hermitian matrices. Closedness of the subgroup of units comes from compactness of `G`.

Differentiating the invariance of a bilinear form under `Ad(exp (t • X))` at `t = 0` shows that an
`Ad(G)`-invariant form on `𝔤` is also invariant under `ad X = ⁅X, ·⁆`. The trace form
`⟨X, Y⟩ = -Re tr (X Y)` is an `Ad(G)`-invariant inner product on `𝔤` for every closed `G`.
For closed subgroups `G₁ ≤ U(n)` and `G₂ ≤ U(m)`, the block-diagonal product
`ClosedSubgroup.fromBlocksProd`, the closed subgroup `{diag(g₁, g₂)} ≤ U(n ⊕ m)`, has Lie algebra
the block-diagonal matrices `diag(X₁, X₂)`, `Xᵢ ∈ 𝔤ᵢ`.

## Main definitions

* `ClosedSubgroup.matrixLieAlgebra`: the Lie algebra of a closed subgroup of `U(n)`.
* `ClosedSubgroup.matrixAdjointRepresentation`: its adjoint representation `X ↦ g X g⁻¹`.
* `ClosedSubgroup.matrixTraceForm`: the trace form `⟨X, Y⟩ = -Re tr (X Y)`.
* `ClosedSubgroup.matrixLieAlgebraFromBlocksProdEquiv`: the Lie algebra of the block-diagonal
  product `ClosedSubgroup.fromBlocksProd` is the product of the Lie algebras.

## Main results

* `ClosedSubgroup.conjTranspose_eq_neg_of_mem_matrixLieAlgebra`: the Lie algebra consists of
  skew-Hermitian matrices.
* `ClosedSubgroup.matrixAdjointRepresentation_lie`: each `Ad(g)` preserves the bracket.
* `ClosedSubgroup.lieInvariant_of_isInvariantForm`: an `Ad(G)`-invariant bilinear form is
  `ad`-invariant, `B ⁅X, Y⁆ Z = -B Y ⁅X, Z⁆`.
* `ClosedSubgroup.posDef_matrixTraceForm`, `ClosedSubgroup.isInvariantForm_matrixTraceForm`: the
  trace form is positive definite and `Ad(G)`-invariant.
* `ClosedSubgroup.mem_matrixLieAlgebra_fromBlocksProd_iff`: the Lie algebra of a block-diagonal
  product.

## References

* B. C. Hall, *Lie Groups, Lie Algebras, and Representations*, second edition, Graduate Texts in
  Mathematics 222, Springer (2015), Section 3.3.
-/

public section

open NormedSpace
open scoped Manifold Matrix

noncomputable section

attribute [local instance 100] LieRing.ofAssociativeRing

namespace ClosedSubgroup

variable {n 𝕜 : Type*} [Fintype n] [DecidableEq n] [RCLike 𝕜]

/-- A closed subgroup of `U(n)` is compact. Stated for the entrywise topology, so that it applies
where the topology of the operator norm is selected instead. -/
private theorem isCompact_coe (G : ClosedSubgroup (Matrix.unitaryGroup n 𝕜)) :
    IsCompact (G : Set (Matrix.unitaryGroup n 𝕜)) :=
  G.isClosed'.isCompact

section Transport

open TauCeti TauCeti.Lie

open scoped Matrix.Norms.Operator

attribute [local instance] NormedAddCommGroup.toSeminormedAddCommGroup

attribute [local instance] Matrix.linftyOpTopologicalSpace Matrix.linftyOpContinuousStar

/-- The closed subgroup of the general linear group carried by a closed subgroup of `U(n)`. -/
private def toGL (G : ClosedSubgroup (Matrix.unitaryGroup n 𝕜)) : Subgroup (Matrix n n 𝕜)ˣ :=
  (G : Subgroup (Matrix.unitaryGroup n 𝕜)).map Unitary.toUnits

/-- The subgroup of units determined by `G` is closed, being the compact image of `G`. -/
private theorem isClosed_toGL (G : ClosedSubgroup (Matrix.unitaryGroup n 𝕜)) :
    IsClosed (toGL G : Set (Matrix n n 𝕜)ˣ) :=
  ((isCompact_coe G).image (Unitary.continuous_toUnits (M := Matrix n n 𝕜))).isClosed

/-- Membership of the exponential line in `G` is membership in the Lie algebra of the units. -/
private theorem forall_exp_mem_iff (G : ClosedSubgroup (Matrix.unitaryGroup n 𝕜))
    (X : Matrix n n 𝕜) :
    (∀ t : ℝ, ∃ g ∈ G, (g : Matrix n n 𝕜) = exp (t • X)) ↔
      (unitsLieAlgebraLieEquiv (R := Matrix n n 𝕜)).symm X ∈
        lieSubalgebraOfSubgroup (I := 𝓘(ℝ, Matrix n n 𝕜)) (toGL G) := by
  rw [unitsLieAlgebraLieEquiv_symm_mem_lieSubalgebraOfSubgroup_iff (isClosed_toGL G)]
  refine forall_congr' fun t ↦ ?_
  simp only [toGL, Subgroup.mem_map, Units.ext_iff, Unitary.val_toUnits_apply,
    expUnit_coe]
  -- Membership in `G` and in its underlying subgroup `(G : Subgroup _)` agree by definition.
  exact Iff.rfl

private theorem conjTranspose_eq_neg_of_forall_exp_mem
    (G : ClosedSubgroup (Matrix.unitaryGroup n 𝕜)) {X : Matrix n n 𝕜}
    (hX : ∀ t : ℝ, ∃ g ∈ G, (g : Matrix n n 𝕜) = exp (t • X)) : Xᴴ = -X := by
  rw [← unitsLieAlgebraLieEquiv_symm_mem_lieSubalgebraOfSubgroup_iff_conjTranspose_eq_neg]
  refine lieSubalgebraOfSubgroup_mono ?_ ((forall_exp_mem_iff G X).mp hX)
  rintro _ ⟨g, -, rfl⟩
  exact mem_unitary_units_iff.mpr g.property

private theorem forall_exp_mem_add (G : ClosedSubgroup (Matrix.unitaryGroup n 𝕜))
    {X Y : Matrix n n 𝕜} (hX : ∀ t : ℝ, ∃ g ∈ G, (g : Matrix n n 𝕜) = exp (t • X))
    (hY : ∀ t : ℝ, ∃ g ∈ G, (g : Matrix n n 𝕜) = exp (t • Y)) :
    ∀ t : ℝ, ∃ g ∈ G, (g : Matrix n n 𝕜) = exp (t • (X + Y)) := by
  rw [forall_exp_mem_iff] at hX hY ⊢
  simpa only [map_add] using add_mem hX hY

private theorem forall_exp_mem_lie (G : ClosedSubgroup (Matrix.unitaryGroup n 𝕜))
    {X Y : Matrix n n 𝕜} (hX : ∀ t : ℝ, ∃ g ∈ G, (g : Matrix n n 𝕜) = exp (t • X))
    (hY : ∀ t : ℝ, ∃ g ∈ G, (g : Matrix n n 𝕜) = exp (t • Y)) :
    ∀ t : ℝ, ∃ g ∈ G, (g : Matrix n n 𝕜) = exp (t • ⁅X, Y⁆) := by
  rw [forall_exp_mem_iff] at hX hY ⊢
  simpa only [LieEquiv.map_lie] using LieSubalgebra.lie_mem _ hX hY

/-- A real linear functional on matrices, along conjugation by the exponential line of `X`, has
derivative at `0` its value on the commutator. -/
private theorem hasDerivAt_linearMap_exp_mul_mul_exp_neg (ℓ : Matrix n n 𝕜 →ₗ[ℝ] ℝ)
    (X Y : Matrix n n 𝕜) :
    HasDerivAt (fun t : ℝ ↦ ℓ (exp (t • X) * Y * exp (t • (-X)))) (ℓ (X * Y - Y * X)) 0 :=
  (LinearMap.toContinuousLinearMap ℓ).hasFDerivAt.comp_hasDerivAt 0
    (hasDerivAt_exp_mul_const_mul_exp_neg X Y)

end Transport

/-- The Lie algebra of a closed subgroup `G` of the unitary group `U(n)`, as a real Lie subalgebra
of the `n × n` matrices: the matrices `X` whose exponential line `t ↦ exp (t • X)` stays in `G`.
That it is closed under addition and the commutator is the closed-subgroup theorem. -/
def matrixLieAlgebra (G : ClosedSubgroup (Matrix.unitaryGroup n 𝕜)) :
    LieSubalgebra ℝ (Matrix n n 𝕜) where
  carrier := {X | ∀ t : ℝ, ∃ g ∈ G, (g : Matrix n n 𝕜) = exp (t • X)}
  zero_mem' t := ⟨1, G.one_mem, by simp⟩
  add_mem' := forall_exp_mem_add G
  smul_mem' c X hX t := by simpa only [smul_smul] using hX (t * c)
  lie_mem' := forall_exp_mem_lie G

variable {G H : ClosedSubgroup (Matrix.unitaryGroup n 𝕜)}

/-- A matrix lies in the Lie algebra exactly when its exponential line stays in `G`. -/
theorem mem_matrixLieAlgebra_iff {X : Matrix n n 𝕜} :
    X ∈ G.matrixLieAlgebra ↔ ∀ t : ℝ, ∃ g ∈ G, (g : Matrix n n 𝕜) = exp (t • X) :=
  Iff.rfl

/-- The Lie algebra of a closed subgroup of `U(n)` consists of skew-Hermitian matrices. -/
theorem conjTranspose_eq_neg_of_mem_matrixLieAlgebra {X : Matrix n n 𝕜}
    (hX : X ∈ G.matrixLieAlgebra) : Xᴴ = -X :=
  conjTranspose_eq_neg_of_forall_exp_mem G hX

/-- A larger closed subgroup has a larger Lie algebra. -/
theorem matrixLieAlgebra_mono (h : G ≤ H) : G.matrixLieAlgebra ≤ H.matrixLieAlgebra :=
  fun _ hX t ↦ (hX t).imp fun _ hg ↦ ⟨h hg.1, hg.2⟩

/-- Conjugation by an element of `G` preserves the Lie algebra of `G`. -/
theorem mul_mul_star_mem_matrixLieAlgebra {g : Matrix.unitaryGroup n 𝕜} (hg : g ∈ G)
    {X : Matrix n n 𝕜} (hX : X ∈ G.matrixLieAlgebra) :
    (g : Matrix n n 𝕜) * X * star (g : Matrix n n 𝕜) ∈ G.matrixLieAlgebra := by
  intro t
  obtain ⟨h, hh, hht⟩ := hX t
  refine ⟨g * h * g⁻¹, mul_mem (mul_mem hg hh) (inv_mem hg), ?_⟩
  have hconj := Matrix.exp_units_conj (Unitary.toUnits g) (t • X)
  simp only [Unitary.val_toUnits_apply, Unitary.val_inv_toUnits_apply,
    Matrix.UnitaryGroup.inv_val] at hconj
  rw [← Matrix.smul_mul, ← Matrix.mul_smul, hconj, ← hht]
  simp

variable (G) in
/-- The adjoint representation `Ad(g) X = g X g⁻¹` of a closed subgroup `G` of `U(n)` on its Lie
algebra. For a unitary `g` the inverse `g⁻¹` is the conjugate transpose `star g`. -/
def matrixAdjointRepresentation : Representation ℝ G G.matrixLieAlgebra where
  toFun g :=
    { toFun X := ⟨(g : Matrix n n 𝕜) * X * star (g : Matrix n n 𝕜),
        mul_mul_star_mem_matrixLieAlgebra g.property X.property⟩
      map_add' X Y := by ext1; simp [mul_add, add_mul]
      map_smul' c X := by ext1; simp }
  map_one' := by ext1 X; ext1; simp
  map_mul' g h := by ext1 X; ext1; simp [mul_assoc]

/-- `Ad(g)` acts on matrices by `X ↦ g X g⁻¹`, with `g⁻¹ = star g`. -/
@[simp]
theorem coe_matrixAdjointRepresentation_apply (g : G) (X : G.matrixLieAlgebra) :
    (G.matrixAdjointRepresentation g X : Matrix n n 𝕜) =
      (g : Matrix n n 𝕜) * X * star (g : Matrix n n 𝕜) :=
  (rfl)

/-- Each `Ad(g)` is an automorphism of the Lie algebra: it preserves the commutator. -/
@[simp]
theorem matrixAdjointRepresentation_lie (g : G) (X Y : G.matrixLieAlgebra) :
    G.matrixAdjointRepresentation g ⁅X, Y⁆ =
      ⁅G.matrixAdjointRepresentation g X, G.matrixAdjointRepresentation g Y⁆ := by
  ext1
  simp only [coe_matrixAdjointRepresentation_apply, LieSubalgebra.coe_bracket,
    LieRing.of_associative_ring_bracket]
  -- Conjugation by `g` is the star-algebra automorphism `Unitary.conjStarAlgAut`.
  simp only [← Unitary.conjStarAlgAut_apply (S := ℝ), map_sub, map_mul]

/-- For an `Ad(G)`-invariant form `B`, `B (Ad(exp (t X)) Y) Z = B Y (Ad(exp (-t X)) Z)`, written
in the ambient matrices through a linear retraction `P` of the matrices onto the Lie algebra. -/
private theorem form_exp_mul_mul_exp_neg_eq {B : LinearMap.BilinForm ℝ G.matrixLieAlgebra}
    (hB : TauCeti.Representation.IsInvariantForm G.matrixAdjointRepresentation B)
    {P : Matrix n n 𝕜 →ₗ[ℝ] G.matrixLieAlgebra} (hP : ∀ W : G.matrixLieAlgebra, P W = W)
    (X Y Z : G.matrixLieAlgebra) (t : ℝ) :
    B (P (exp (t • (X : Matrix n n 𝕜)) * Y * exp (t • (-(X : Matrix n n 𝕜))))) Z =
      B Y (P (exp (t • (-(X : Matrix n n 𝕜))) * Z * exp (t • (-(-(X : Matrix n n 𝕜)))))) := by
  obtain ⟨g, hg, hgt⟩ := X.property t
  have hstar : star (g : Matrix n n 𝕜) = exp (t • (-(X : Matrix n n 𝕜))) := by
    rw [hgt, Matrix.star_eq_conjTranspose, ← Matrix.exp_conjTranspose,
      Matrix.conjTranspose_smul, conjTranspose_eq_neg_of_mem_matrixLieAlgebra X.property,
          star_trivial]
  rw [neg_neg, ← hstar, ← hgt]
  have hY : (g : Matrix n n 𝕜) * Y * star (g : Matrix n n 𝕜) =
      (G.matrixAdjointRepresentation ⟨g, hg⟩ Y : Matrix n n 𝕜) := by simp
  have hZ : star (g : Matrix n n 𝕜) * Z * g =
      (G.matrixAdjointRepresentation ⟨g, hg⟩⁻¹ Z : Matrix n n 𝕜) := by simp
  have h := (TauCeti.Representation.isInvariantForm_iff.mp hB) ⟨g, hg⟩⁻¹
    (G.matrixAdjointRepresentation ⟨g, hg⟩ Y) Z
  rw [Representation.inv_self_apply] at h
  rw [hY, hZ, hP, hP, h]

/-- **An `Ad`-invariant form is `ad`-invariant.** If a bilinear form on the Lie algebra of a closed
subgroup `G` of `U(n)` is invariant under every `Ad(g)`, `g ∈ G`, then every `ad(X)` is skew for it:
`B ⁅X, Y⁆ Z = -B Y ⁅X, Z⁆`. -/
theorem lieInvariant_of_isInvariantForm {B : LinearMap.BilinForm ℝ G.matrixLieAlgebra}
    (hB : TauCeti.Representation.IsInvariantForm G.matrixAdjointRepresentation B) :
    B.lieInvariant G.matrixLieAlgebra := by
  intro X Y Z
  -- Extend `B` to the ambient matrices through a linear retraction `P` onto the Lie algebra, and
  -- differentiate `B (Ad(exp (t X)) Y) Z = B Y (Ad(exp (-t X)) Z)` at `t = 0`.
  obtain ⟨P, hP⟩ := LinearMap.exists_leftInverse_of_injective
    (G.matrixLieAlgebra.incl : G.matrixLieAlgebra →ₗ[ℝ] Matrix n n 𝕜)
    (LinearMap.ker_eq_bot.mpr Subtype.val_injective)
  have hPincl (W : G.matrixLieAlgebra) : P W = W := LinearMap.congr_fun hP W
  have hX : HasDerivAt (fun t : ℝ ↦ (B.flip Z ∘ₗ P) (exp (t • (X : Matrix n n 𝕜)) * Y *
        exp (t • (-(X : Matrix n n 𝕜)))))
      ((B.flip Z ∘ₗ P) ((X : Matrix n n 𝕜) * Y - Y * X)) 0 :=
    hasDerivAt_linearMap_exp_mul_mul_exp_neg _ _ _
  have hnegX : HasDerivAt (fun t : ℝ ↦ (B Y ∘ₗ P) (exp (t • (-(X : Matrix n n 𝕜))) * Z *
        exp (t • (-(-(X : Matrix n n 𝕜))))))
      ((B Y ∘ₗ P) (-(X : Matrix n n 𝕜) * Z - Z * -X)) 0 :=
    hasDerivAt_linearMap_exp_mul_mul_exp_neg _ _ _
  simp only [LinearMap.comp_apply, LinearMap.BilinForm.flip_apply,
    form_exp_mul_mul_exp_neg_eq hB hPincl] at hX hnegX
  have h := hX.unique hnegX
  have e₁ : (X : Matrix n n 𝕜) * Y - Y * X = ((⁅X, Y⁆ : G.matrixLieAlgebra) : Matrix n n 𝕜) := by
    rw [LieSubalgebra.coe_bracket, LieRing.of_associative_ring_bracket]
  have e₂ : -(X : Matrix n n 𝕜) * Z - Z * -X = ((-⁅X, Z⁆ : G.matrixLieAlgebra) : Matrix n n 𝕜) := by
    simp only [NegMemClass.coe_neg, LieSubalgebra.coe_bracket, LieRing.of_associative_ring_bracket]
    noncomm_ring
  rw [e₁, e₂, hPincl, hPincl, map_neg] at h
  exact h

variable (G) in
/-- The trace form `⟨X, Y⟩ = -Re tr (X Y)` on the Lie algebra of a closed subgroup of `U(n)`. On
skew-Hermitian matrices it is the real part of the Frobenius inner product `tr (Xᴴ Y)`. -/
def matrixTraceForm : LinearMap.BilinForm ℝ G.matrixLieAlgebra :=
  LinearMap.mk₂ ℝ (fun X Y ↦ -RCLike.re ((X : Matrix n n 𝕜) * Y).trace)
    (fun X X' Y ↦ by simp [add_mul]; ring)
    (fun c X Y ↦ by simp [RCLike.smul_re])
    (fun X Y Y' ↦ by simp [mul_add]; ring)
    (fun c X Y ↦ by simp [RCLike.smul_re])

/-- The trace form is `-Re tr (X Y)`. -/
@[simp]
theorem matrixTraceForm_apply (X Y : G.matrixLieAlgebra) :
    G.matrixTraceForm X Y = -RCLike.re ((X : Matrix n n 𝕜) * Y).trace :=
  (rfl)

/-- The trace form is symmetric. -/
theorem isSymm_matrixTraceForm : G.matrixTraceForm.IsSymm :=
  ⟨fun X Y ↦ by simp only [matrixTraceForm_apply, Matrix.trace_mul_comm (X : Matrix n n 𝕜)]⟩

/-- The trace form of an element with itself is the sum of the squared norms of its entries. -/
theorem matrixTraceForm_self (X : G.matrixLieAlgebra) :
    G.matrixTraceForm X X = ∑ i, ∑ j, ‖(X : Matrix n n 𝕜) i j‖ ^ 2 := by
  rw [matrixTraceForm_apply, ← Matrix.re_trace_mul_conjTranspose_self,
    conjTranspose_eq_neg_of_mem_matrixLieAlgebra X.property, mul_neg, Matrix.trace_neg, map_neg]

/-- The trace form is positive definite. -/
theorem posDef_matrixTraceForm : G.matrixTraceForm.toQuadraticMap.PosDef := by
  intro X hX
  rw [LinearMap.BilinMap.toQuadraticMap_apply, matrixTraceForm_self]
  refine lt_of_le_of_ne (by positivity) fun h ↦ hX (Subtype.ext (Matrix.ext fun i j ↦ ?_))
  have hi := (Finset.sum_eq_zero_iff_of_nonneg fun i _ ↦ by positivity).mp h.symm i
    (Finset.mem_univ i)
  have hij := (Finset.sum_eq_zero_iff_of_nonneg fun j _ ↦ by positivity).mp hi j
    (Finset.mem_univ j)
  simpa using hij

/-- The trace form is invariant under the adjoint action of `G`. -/
theorem isInvariantForm_matrixTraceForm :
    TauCeti.Representation.IsInvariantForm G.matrixAdjointRepresentation G.matrixTraceForm := by
  refine TauCeti.Representation.isInvariantForm_iff.mpr fun g X Y ↦ ?_
  simp only [matrixTraceForm_apply, coe_matrixAdjointRepresentation_apply]
  -- Merge `(g X g⋆) (g Y g⋆)` into `g (X Y) g⋆`: both factors are images of the conjugation
  -- automorphism `Unitary.conjStarAlgAut`, so `map_mul` combines them, and unfolding it again
  -- leaves a single conjugate whose trace is cyclic.
  rw [← Unitary.conjStarAlgAut_apply (S := ℝ), ← Unitary.conjStarAlgAut_apply (S := ℝ), ← map_mul,
    Unitary.conjStarAlgAut_apply]
  rw [Matrix.trace_mul_comm, ← mul_assoc, Matrix.UnitaryGroup.star_mul_self, one_mul]

section FromBlocks

variable {m : Type*} [Fintype m] [DecidableEq m]

/-- The exponential line of a block-diagonal matrix is block diagonal. -/
private theorem exp_smul_fromBlocks_zero (t : ℝ) (A : Matrix n n 𝕜) (D : Matrix m m 𝕜) :
    exp (t • Matrix.fromBlocks A 0 0 D) = Matrix.fromBlocks (exp (t • A)) 0 0 (exp (t • D)) := by
  rw [Matrix.fromBlocks_smul, smul_zero, smul_zero]
  exact Matrix.exp_fromBlocks_diagonal _ _

variable {G₁ : ClosedSubgroup (Matrix.unitaryGroup n 𝕜)}
  {G₂ : ClosedSubgroup (Matrix.unitaryGroup m 𝕜)}

/-- **The Lie algebra of a block-diagonal product** consists of the block-diagonal matrices
`diag(X₁, X₂)` with `X₁` in the Lie algebra of `G₁` and `X₂` in that of `G₂`. -/
theorem mem_matrixLieAlgebra_fromBlocksProd_iff {X : Matrix (n ⊕ m) (n ⊕ m) 𝕜} :
    X ∈ (G₁.fromBlocksProd G₂).matrixLieAlgebra ↔
      X.toBlocks₁₂ = 0 ∧ X.toBlocks₂₁ = 0 ∧ X.toBlocks₁₁ ∈ G₁.matrixLieAlgebra ∧
        X.toBlocks₂₂ ∈ G₂.matrixLieAlgebra := by
  constructor
  · intro hX
    have hexp (t : ℝ) : ∃ g₁ ∈ G₁, ∃ g₂ ∈ G₂,
        exp (t • X) = Matrix.fromBlocks (g₁ : Matrix n n 𝕜) 0 0 (g₂ : Matrix m m 𝕜) := by
      obtain ⟨g, hg, hgt⟩ := hX t
      obtain ⟨g₁, h₁, g₂, h₂, hg'⟩ := mem_fromBlocksProd_iff.mp hg
      exact ⟨g₁, h₁, g₂, h₂, hgt.symm.trans hg'⟩
    -- The off-diagonal entries of `exp (t • X)` vanish for every `t`, hence so do those of `X`.
    have hoff : X.toBlocks₁₂ = 0 ∧ X.toBlocks₂₁ = 0 := by
      refine ⟨?_, ?_⟩ <;>
      · refine Matrix.ext fun i j ↦ Matrix.apply_eq_zero_of_forall_exp_smul_apply_eq_zero fun t ↦ ?_
        obtain ⟨g₁, -, g₂, -, he⟩ := hexp t
        simp [he]
    have hdiag (t : ℝ) : ∃ g₁ ∈ G₁, ∃ g₂ ∈ G₂, (g₁ : Matrix n n 𝕜) = exp (t • X.toBlocks₁₁) ∧
        (g₂ : Matrix m m 𝕜) = exp (t • X.toBlocks₂₂) := by
      obtain ⟨g₁, h₁, g₂, h₂, he⟩ := hexp t
      rw [Matrix.eq_fromBlocks_of_toBlocks₁₂_eq_zero_of_toBlocks₂₁_eq_zero hoff.1 hoff.2,
        exp_smul_fromBlocks_zero, Matrix.fromBlocks_inj] at he
      exact ⟨g₁, h₁, g₂, h₂, he.1.symm, he.2.2.2.symm⟩
    refine ⟨hoff.1, hoff.2, fun t ↦ ?_, fun t ↦ ?_⟩
    · obtain ⟨g₁, h₁, -, -, he, -⟩ := hdiag t
      exact ⟨g₁, h₁, he⟩
    · obtain ⟨-, -, g₂, h₂, -, he⟩ := hdiag t
      exact ⟨g₂, h₂, he⟩
  · rintro ⟨h₁₂, h₂₁, h₁, h₂⟩ t
    obtain ⟨g₁, hg₁, hg₁t⟩ := h₁ t
    obtain ⟨g₂, hg₂, hg₂t⟩ := h₂ t
    refine ⟨_, sum_mem_fromBlocksProd hg₁ hg₂, ?_⟩
    rw [Matrix.UnitaryGroup.coe_sum, ← Matrix.fromBlocks_toBlocks X, h₁₂, h₂₁,
      exp_smul_fromBlocks_zero, hg₁t, hg₂t]

/-- The block-diagonal matrix `diag(X₁, X₂)` lies in the Lie algebra of the product. -/
theorem fromBlocks_mem_matrixLieAlgebra_fromBlocksProd {X₁ X₂}
    (h₁ : X₁ ∈ G₁.matrixLieAlgebra) (h₂ : X₂ ∈ G₂.matrixLieAlgebra) :
    Matrix.fromBlocks X₁ 0 0 X₂ ∈ (G₁.fromBlocksProd G₂).matrixLieAlgebra :=
  mem_matrixLieAlgebra_fromBlocksProd_iff.mpr ⟨rfl, rfl, h₁, h₂⟩

/-- An element of the Lie algebra of the product is the block-diagonal matrix of its diagonal
blocks. -/
theorem eq_fromBlocks_of_mem_matrixLieAlgebra_fromBlocksProd {X : Matrix (n ⊕ m) (n ⊕ m) 𝕜}
    (hX : X ∈ (G₁.fromBlocksProd G₂).matrixLieAlgebra) :
    X = Matrix.fromBlocks X.toBlocks₁₁ 0 0 X.toBlocks₂₂ := by
  obtain ⟨h₁₂, h₂₁, -, -⟩ := mem_matrixLieAlgebra_fromBlocksProd_iff.mp hX
  exact Matrix.eq_fromBlocks_of_toBlocks₁₂_eq_zero_of_toBlocks₂₁_eq_zero h₁₂ h₂₁

variable (G₁ G₂) in
/-- The Lie algebra of the block-diagonal product `G₁ × G₂` is the product of the Lie algebras,
through `diag(X₁, X₂) ↦ (X₁, X₂)`. -/
def matrixLieAlgebraFromBlocksProdEquiv :
    (G₁.fromBlocksProd G₂).matrixLieAlgebra ≃ₗ⁅ℝ⁆ G₁.matrixLieAlgebra × G₂.matrixLieAlgebra where
  toFun X := (⟨(X : Matrix (n ⊕ m) (n ⊕ m) 𝕜).toBlocks₁₁,
      (mem_matrixLieAlgebra_fromBlocksProd_iff.mp X.property).2.2.1⟩,
    ⟨(X : Matrix (n ⊕ m) (n ⊕ m) 𝕜).toBlocks₂₂,
      (mem_matrixLieAlgebra_fromBlocksProd_iff.mp X.property).2.2.2⟩)
  invFun X := ⟨Matrix.fromBlocks X.1 0 0 X.2,
    fromBlocks_mem_matrixLieAlgebra_fromBlocksProd X.1.property X.2.property⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  map_lie' {X Y} := by
    have hX := eq_fromBlocks_of_mem_matrixLieAlgebra_fromBlocksProd X.property
    have hY := eq_fromBlocks_of_mem_matrixLieAlgebra_fromBlocksProd Y.property
    refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_) <;>
    · simp only [LieAlgebra.Prod.bracket_apply, LieSubalgebra.coe_bracket,
        LieRing.of_associative_ring_bracket]
      rw [hX, hY, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
      ext i j
      simp [Matrix.toBlocks₁₁, Matrix.toBlocks₂₂]
  left_inv X := Subtype.ext (eq_fromBlocks_of_mem_matrixLieAlgebra_fromBlocksProd X.property).symm
  right_inv _ := rfl

/-- The first component of the equivalence is the upper-left block. -/
@[simp]
theorem coe_matrixLieAlgebraFromBlocksProdEquiv_fst_apply
    (X : (G₁.fromBlocksProd G₂).matrixLieAlgebra) :
    ((G₁.matrixLieAlgebraFromBlocksProdEquiv G₂ X).1 : Matrix n n 𝕜) =
      (X : Matrix (n ⊕ m) (n ⊕ m) 𝕜).toBlocks₁₁ :=
  (rfl)

/-- The second component of the equivalence is the lower-right block. -/
@[simp]
theorem coe_matrixLieAlgebraFromBlocksProdEquiv_snd_apply
    (X : (G₁.fromBlocksProd G₂).matrixLieAlgebra) :
    ((G₁.matrixLieAlgebraFromBlocksProdEquiv G₂ X).2 : Matrix m m 𝕜) =
      (X : Matrix (n ⊕ m) (n ⊕ m) 𝕜).toBlocks₂₂ :=
  (rfl)

/-- The inverse equivalence is the block-diagonal matrix `diag(X₁, X₂)`. -/
@[simp]
theorem coe_matrixLieAlgebraFromBlocksProdEquiv_symm_apply
    (X : G₁.matrixLieAlgebra × G₂.matrixLieAlgebra) :
    ((G₁.matrixLieAlgebraFromBlocksProdEquiv G₂).symm X : Matrix (n ⊕ m) (n ⊕ m) 𝕜) =
      Matrix.fromBlocks (X.1 : Matrix n n 𝕜) 0 0 (X.2 : Matrix m m 𝕜) :=
  (rfl)

/-- The adjoint action of `diag(g₁, g₂)` acts on the blocks of the Lie algebra of the product by
the adjoint actions of `g₁` and `g₂`. -/
theorem matrixLieAlgebraFromBlocksProdEquiv_matrixAdjointRepresentation {g₁ g₂}
    (h₁ : g₁ ∈ G₁) (h₂ : g₂ ∈ G₂) (X : (G₁.fromBlocksProd G₂).matrixLieAlgebra) :
    G₁.matrixLieAlgebraFromBlocksProdEquiv G₂
        ((G₁.fromBlocksProd G₂).matrixAdjointRepresentation
          ⟨_, sum_mem_fromBlocksProd h₁ h₂⟩ X) =
      (G₁.matrixAdjointRepresentation ⟨g₁, h₁⟩ (G₁.matrixLieAlgebraFromBlocksProdEquiv G₂ X).1,
        G₂.matrixAdjointRepresentation ⟨g₂, h₂⟩
          (G₁.matrixLieAlgebraFromBlocksProdEquiv G₂ X).2) := by
  have hX := eq_fromBlocks_of_mem_matrixLieAlgebra_fromBlocksProd X.property
  ext1 <;> ext1 <;>
  simp only [coe_matrixLieAlgebraFromBlocksProdEquiv_fst_apply,
    coe_matrixLieAlgebraFromBlocksProdEquiv_snd_apply, coe_matrixAdjointRepresentation_apply,
    Matrix.UnitaryGroup.coe_sum] <;>
  rw [hX, Matrix.star_eq_conjTranspose, Matrix.fromBlocks_conjTranspose,
    Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply] <;>
  simp [Matrix.star_eq_conjTranspose]

end FromBlocks

end ClosedSubgroup
