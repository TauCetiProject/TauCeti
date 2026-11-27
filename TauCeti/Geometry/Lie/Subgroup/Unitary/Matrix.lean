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
public import TauCeti.Analysis.Matrix.Frobenius
public import TauCeti.Geometry.Lie.Subgroup.Unitary.Basic
public import TauCeti.RepresentationTheory.InvariantForm
public import TauCeti.Topology.Algebra.UnitaryGroup
import Mathlib.Algebra.Star.UnitaryStarAlgAut
import TauCeti.Analysis.Matrix.Exponential.Block
import TauCeti.Analysis.Matrix.Normed
import TauCeti.Analysis.Normed.Algebra.MatrixExponential
import TauCeti.Analysis.SpecialFunctions.Exponential
import TauCeti.Geometry.Lie.Subgroup.Countable.Basic
import TauCeti.Geometry.Lie.Subgroup.LimitCriterion
import TauCeti.Geometry.Lie.Subgroup.SpecialUnitary
import TauCeti.LinearAlgebra.Matrix.Block
import TauCeti.LinearAlgebra.Matrix.Hermitian.Basic
import TauCeti.LinearAlgebra.Matrix.Trace.Hermitian
import TauCeti.LinearAlgebra.Matrix.Unique

/-!
# The matrix Lie algebra of a closed subgroup of the unitary group

For a closed subgroup `G` of the unitary group `U(n) = Matrix.unitaryGroup n 𝕜` (over `ℝ` or `ℂ`),
this file defines its Lie algebra as a real Lie subalgebra of the matrices,
`𝔤 = {X : exp (t • X) ∈ G for all real t}`, with the commutator bracket, and the adjoint action
`Ad(g) X = g X g⁻¹` of `G` on it. This is the concrete form in which compact matrix groups enter
gauge theory: connections and curvatures are `𝔤`-valued matrix functions, and gauge
transformations act on them by `Ad`.

That `𝔤` is closed under addition and the commutator is the closed-subgroup theorem: `G` embeds
as a closed subgroup `G.toGL` of `(Matrix n n 𝕜)ˣ` (packaged with `ClosedSubgroup.equivToGL` and
`ClosedSubgroup.embeddedLieSubgroupData`), whose Lie algebra in matrix coordinates coincides with
`𝔤` through `TauCeti.Lie.unitsLieAlgebraLieEquiv_symm_mem_lieSubalgebraOfSubgroup_iff`.

We also characterize the Lie algebras of `ClosedSubgroup.unitary` (`Xᴴ = -X`),
`ClosedSubgroup.specialUnitary` (`Xᴴ = -X ∧ X.trace = 0`), countable subgroups (trivial Lie algebra
`⊥`), reindexed subgroups `ClosedSubgroup.reindex` (with isomorphism
`ClosedSubgroup.matrixLieAlgebraReindexEquiv`), and block-diagonal products
`ClosedSubgroup.fromBlocksProd` (with isomorphism
`ClosedSubgroup.matrixLieAlgebraFromBlocksProdEquiv`). Differentiating the invariance of a
bilinear form under `Ad(exp (t • X))` at `t = 0` shows that an `Ad(G)`-invariant form on `𝔤` is
also invariant under `ad X = ⁅X, ·⁆`. The trace form `⟨X, Y⟩ = -Re tr (X Y)` is an
`Ad(G)`-invariant inner product on `𝔤` for every closed `G`.

## Main definitions

* `ClosedSubgroup.toGL`, `ClosedSubgroup.equivToGL`, `ClosedSubgroup.embeddedLieSubgroupData`:
  embedding of `G ≤ U(n)` into `(Matrix n n 𝕜)ˣ` and its embedded Lie subgroup data.
* `ClosedSubgroup.matrixLieAlgebra`: the Lie algebra of a closed subgroup of `U(n)`.
* `ClosedSubgroup.matrixAdjointRepresentation`: its adjoint representation `X ↦ g X g⁻¹`.
* `ClosedSubgroup.matrixTraceForm`: the trace form `⟨X, Y⟩ = -Re tr (X Y)`.
* `ClosedSubgroup.matrixLieAlgebraFromBlocksProdEquiv`: the Lie algebra of the block-diagonal
  product `ClosedSubgroup.fromBlocksProd` is the product of the Lie algebras.
* `ClosedSubgroup.matrixLieAlgebraReindexEquiv`: reindexing induces an isomorphism of Lie algebras.

## Main results

* `ClosedSubgroup.isCompact_image_coe_matrix`: a closed subgroup of `U(n)` is compact as a set of
  matrices.
* `ClosedSubgroup.mem_matrixLieAlgebra_iff`: exponential-line membership criterion.
* `ClosedSubgroup.mem_matrixLieAlgebra_of_tendsto`: the limit criterion, a limit `X` of matrices
  `Xₖ` with `exp (tₖ • Xₖ) ∈ G` for positive scales `tₖ → 0` lies in the Lie algebra.
* `ClosedSubgroup.conjTranspose_eq_neg_of_mem_matrixLieAlgebra`: the Lie algebra consists of
  skew-Hermitian matrices.
* `ClosedSubgroup.mem_matrixLieAlgebra_iff_conjTranspose_eq_neg_of_forall_mem`: the Lie algebra of
  all of `U(n)` is the skew-Hermitian matrices.
* `ClosedSubgroup.eq_zero_of_mem_matrixLieAlgebra_of_countable`: a countable closed subgroup has
  Lie algebra `0`.
* `ClosedSubgroup.matrixAdjointRepresentation_lie`: each `Ad(g)` preserves the bracket.
* `ClosedSubgroup.lieInvariant_of_isInvariantForm`: an `Ad(G)`-invariant bilinear form is
  `ad`-invariant, `B ⁅X, Y⁆ Z = -B Y ⁅X, Z⁆`.
* `ClosedSubgroup.neg_trace_mul_eq_matrixTraceForm`: `-tr (X Y)` is real and equals
  `G.matrixTraceForm X Y`.
* `ClosedSubgroup.matrixTraceForm_eq_frobenius_real_inner`: the trace form is the restriction of
  the real Frobenius inner product.
* `ClosedSubgroup.posDef_matrixTraceForm`, `ClosedSubgroup.isInvariantForm_matrixTraceForm`: the
  trace form is positive definite and `Ad(G)`-invariant.
* `ClosedSubgroup.mem_matrixLieAlgebra_fromBlocksProd_iff`: the Lie algebra of a block-diagonal
  product.
* `ClosedSubgroup.mem_matrixLieAlgebra_unitary_iff`,
  `ClosedSubgroup.mem_matrixLieAlgebra_specialUnitary_iff`: Lie algebras of `U(n)` and `SU(n)`.
* `ClosedSubgroup.mem_matrixLieAlgebra_unitary_fin_one_iff`,
  `ClosedSubgroup.lie_eq_zero_of_unique`,
  `ClosedSubgroup.matrixAdjointRepresentation_eq_id_of_unique`:
  `𝔲(1) = iℝ` is abelian with trivial adjoint representation.
* `ClosedSubgroup.matrixLieAlgebra_eq_bot_of_countable`: every countable subgroup of `U(n)` has
  trivial Lie algebra `⊥`.
* `ClosedSubgroup.mem_matrixLieAlgebra_reindex_iff`: the Lie algebra of a reindexed subgroup.

## References

* B. C. Hall, *Lie Groups, Lie Algebras, and Representations*, second edition, Graduate Texts in
  Mathematics 222, Springer (2015), Section 3.3.
-/

public section

open Filter NormedSpace
open scoped Manifold Matrix Topology

noncomputable section

attribute [local instance 100] LieRing.ofAssociativeRing

namespace ClosedSubgroup

variable {n 𝕜 : Type*} [Fintype n] [DecidableEq n] [RCLike 𝕜]

/-- A closed subgroup of `U(n)` is compact. Stated for the entrywise topology, so that it applies
where the topology of the operator norm is selected instead. -/
private theorem isCompact_coe (G : ClosedSubgroup (Matrix.unitaryGroup n 𝕜)) :
    IsCompact (G : Set (Matrix.unitaryGroup n 𝕜)) :=
  G.isClosed'.isCompact

/-- A closed subgroup of `U(n)` is compact as a set of matrices. -/
theorem isCompact_image_coe_matrix (G : ClosedSubgroup (Matrix.unitaryGroup n 𝕜)) :
    IsCompact (((↑) : Matrix.unitaryGroup n 𝕜 → Matrix n n 𝕜) '' G) :=
  (isCompact_coe G).image continuous_subtypeVal

/-- The subgroup of the general linear group carried by a closed subgroup of `U(n)`, its image
under `Unitary.toUnits`. -/
def toGL (G : ClosedSubgroup (Matrix.unitaryGroup n 𝕜)) : Subgroup (Matrix n n 𝕜)ˣ :=
  (G : Subgroup (Matrix.unitaryGroup n 𝕜)).map Unitary.toUnits

/-- The units of `G.toGL` are the images of the elements of `G`. -/
@[simp]
theorem mem_toGL {G : ClosedSubgroup (Matrix.unitaryGroup n 𝕜)} {u : (Matrix n n 𝕜)ˣ} :
    u ∈ G.toGL ↔ ∃ g ∈ G, Unitary.toUnits g = u :=
  Subgroup.mem_map

/-- The image of an element of `G` lies in `G.toGL`. -/
theorem toUnits_mem_toGL {G : ClosedSubgroup (Matrix.unitaryGroup n 𝕜)}
    {g : Matrix.unitaryGroup n 𝕜} (hg : g ∈ G) : Unitary.toUnits g ∈ G.toGL :=
  mem_toGL.mpr ⟨g, hg, rfl⟩

/-- As a set, `G.toGL` is the image of `G` under `Unitary.toUnits`. -/
theorem coe_toGL (G : ClosedSubgroup (Matrix.unitaryGroup n 𝕜)) :
    (G.toGL : Set (Matrix n n 𝕜)ˣ) = Unitary.toUnits '' (G : Set (Matrix.unitaryGroup n 𝕜)) :=
  Subgroup.coe_map _ _

/-- The image of `ClosedSubgroup.unitary n 𝕜` in `(Matrix n n 𝕜)ˣ` is `unitarySubgroup`. -/
@[simp]
theorem toGL_unitary :
    (unitary n 𝕜).toGL = unitarySubgroup (Matrix n n 𝕜)ˣ := by
  ext g
  simp only [mem_toGL, mem_unitary, true_and, mem_unitarySubgroup_iff,
    TauCeti.mem_unitary_units_iff]
  exact ⟨fun ⟨u, hu⟩ ↦ hu ▸ u.property, fun hg ↦ ⟨⟨g, hg⟩, Units.ext rfl⟩⟩

/-- The image of `ClosedSubgroup.specialUnitary n 𝕜` in `GL n 𝕜` is `TauCeti.GLSpecialUnitary`. -/
@[simp]
theorem toGL_specialUnitary :
    (specialUnitary n 𝕜).toGL = TauCeti.GLSpecialUnitary n 𝕜 := by
  ext g
  simp only [mem_toGL, mem_specialUnitary_iff,
    TauCeti.GLSpecialUnitary.mem_iff_mem_specialUnitaryGroup, Matrix.mem_specialUnitaryGroup_iff]
  exact ⟨fun ⟨u, hu, hgu⟩ ↦ hgu ▸ ⟨u.property, hu⟩,
    fun ⟨hU, hdet⟩ ↦ ⟨⟨(g : Matrix n n 𝕜), hU⟩, hdet, Units.ext rfl⟩⟩

section Transport

open TauCeti TauCeti.Lie

open scoped Matrix.Norms.Operator

attribute [local instance] NormedAddCommGroup.toSeminormedAddCommGroup

attribute [local instance] Matrix.linftyOpTopologicalSpace Matrix.linftyOpContinuousStar

/-- The subgroup of units determined by `G` is closed, being the compact image of `G`. -/
theorem isClosed_toGL (G : ClosedSubgroup (Matrix.unitaryGroup n 𝕜)) :
    IsClosed (toGL G : Set (Matrix n n 𝕜)ˣ) :=
  G.coe_toGL ▸ ((isCompact_coe G).image (Unitary.continuous_toUnits (M := Matrix n n 𝕜))).isClosed

/-- Membership of the exponential line in `G` is membership in the Lie algebra of the units. -/
private theorem forall_exp_mem_iff (G : ClosedSubgroup (Matrix.unitaryGroup n 𝕜))
    (X : Matrix n n 𝕜) :
    (∀ t : ℝ, ∃ g ∈ G, (g : Matrix n n 𝕜) = exp (t • X)) ↔
      (unitsLieAlgebraLieEquiv (R := Matrix n n 𝕜)).symm X ∈
        lieSubalgebraOfSubgroup (I := 𝓘(ℝ, Matrix n n 𝕜)) (toGL G) := by
  rw [unitsLieAlgebraLieEquiv_symm_mem_lieSubalgebraOfSubgroup_iff (isClosed_toGL G)]
  refine forall_congr' fun t ↦ Iff.trans ?_ mem_toGL.symm
  simp only [Units.ext_iff, Unitary.val_toUnits_apply, expUnit_coe]
  -- Membership in `G` is elaborated for the entrywise and for the operator-norm topology on
  -- `U(n)`, which agree by definition.
  exact Iff.rfl

private theorem conjTranspose_eq_neg_of_forall_exp_mem
    (G : ClosedSubgroup (Matrix.unitaryGroup n 𝕜)) {X : Matrix n n 𝕜}
    (hX : ∀ t : ℝ, ∃ g ∈ G, (g : Matrix n n 𝕜) = exp (t • X)) : Xᴴ = -X := by
  rw [← unitsLieAlgebraLieEquiv_symm_mem_lieSubalgebraOfSubgroup_iff_conjTranspose_eq_neg]
  refine lieSubalgebraOfSubgroup_mono ?_ ((forall_exp_mem_iff G X).mp hX)
  intro u hu
  obtain ⟨g, -, rfl⟩ := mem_toGL.mp hu
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

/-- The limit criterion for the Lie algebra of the closed subgroup of units determined by `G`,
read in matrix coordinates. -/
private theorem forall_exp_mem_of_tendsto (G : ClosedSubgroup (Matrix.unitaryGroup n 𝕜))
    {X : Matrix n n 𝕜} {t : ℕ → ℝ} {Xn : ℕ → Matrix n n 𝕜} (ht_pos : ∀ᶠ k in atTop, 0 < t k)
    (ht : Tendsto t atTop (𝓝 0)) (hXn : Tendsto Xn atTop (𝓝 X))
    (hmem : ∀ᶠ k in atTop, ∃ g ∈ G, (g : Matrix n n 𝕜) = exp (t k • Xn k)) :
    ∀ s : ℝ, ∃ g ∈ G, (g : Matrix n n 𝕜) = exp (s • X) := by
  rw [forall_exp_mem_iff]
  refine mem_lieSubalgebraOfSubgroup_of_seq (isClosed_toGL G) ht_pos ht
    (Xn := fun k ↦ (unitsLieAlgebraLieEquiv (R := Matrix n n 𝕜)).symm (Xn k)) ?_ ?_
  · exact ((unitsLieAlgebraLieEquiv (R := Matrix n n 𝕜)).symm.toLinearMap
      |>.continuous_of_finiteDimensional.tendsto X).comp hXn
  · filter_upwards [hmem] with k ⟨g, hg, hgk⟩
    rw [← map_smul, lieExp_eq_expUnit]
    refine ⟨g, hg, Units.ext ?_⟩
    simp [hgk]

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

/-- **The limit criterion for the Lie algebra.** If positive scales `tₖ → 0` and matrices
`Xₖ → X` have `exp (tₖ • Xₖ) ∈ G` for all large `k`, then `X` lies in the Lie algebra of `G`. -/
theorem mem_matrixLieAlgebra_of_tendsto {X : Matrix n n 𝕜} {t : ℕ → ℝ} {Xn : ℕ → Matrix n n 𝕜}
    (ht_pos : ∀ᶠ k in atTop, 0 < t k) (ht : Tendsto t atTop (𝓝 0))
    (hXn : Tendsto Xn atTop (𝓝 X))
    (hmem : ∀ᶠ k in atTop, ∃ g ∈ G, (g : Matrix n n 𝕜) = exp (t k • Xn k)) :
    X ∈ G.matrixLieAlgebra :=
  forall_exp_mem_of_tendsto G ht_pos ht hXn hmem

/-- The Lie algebra of a closed subgroup of `U(n)` consists of skew-Hermitian matrices. -/
theorem conjTranspose_eq_neg_of_mem_matrixLieAlgebra {X : Matrix n n 𝕜}
    (hX : X ∈ G.matrixLieAlgebra) : Xᴴ = -X :=
  conjTranspose_eq_neg_of_forall_exp_mem G hX

section OperatorNorm

open scoped Matrix.Norms.Operator

attribute [local instance] NormedAddCommGroup.toSeminormedAddCommGroup

attribute [local instance] Matrix.linftyOpTopologicalSpace Matrix.linftyOpContinuousStar

/-- **The Lie algebra of `U(n)`.** If `G` is all of `U(n)`, its Lie algebra is the
skew-Hermitian matrices. -/
theorem mem_matrixLieAlgebra_iff_conjTranspose_eq_neg_of_forall_mem (hG : ∀ g, g ∈ G)
    {X : Matrix n n 𝕜} :
    X ∈ G.matrixLieAlgebra ↔ Xᴴ = -X :=
  ⟨conjTranspose_eq_neg_of_mem_matrixLieAlgebra, fun hX t ↦
    ⟨⟨_, exp_mem_unitary_of_mem_skewAdjoint (skewAdjoint.smul_mem t (skewAdjoint.mem_iff.mpr hX))⟩,
      hG _, rfl⟩⟩

/-- **A countable closed subgroup has Lie algebra `0`.** This is the matrix form of
`TauCeti.Lie.lieSubalgebraOfSubgroup_eq_bot_of_countable`. -/
theorem eq_zero_of_mem_matrixLieAlgebra_of_countable
    (hG : (G : Set (Matrix.unitaryGroup n 𝕜)).Countable) {X : Matrix n n 𝕜}
    (hX : X ∈ G.matrixLieAlgebra) : X = 0 := by
  have h := (forall_exp_mem_iff G X).mp hX
  rw [TauCeti.Lie.lieSubalgebraOfSubgroup_eq_bot_of_countable (G.coe_toGL ▸ hG.image _),
    LieSubalgebra.mem_bot] at h
  have h0 := congrArg TauCeti.Lie.unitsLieAlgebraLieEquiv h
  rw [LieEquiv.apply_symm_apply, map_zero] at h0
  -- The two sides carry the zero of the operator-norm and of the entrywise structure on the
  -- matrices, which agree by definition.
  exact h0

end OperatorNorm

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
  obtain ⟨g, hg, hgt⟩ := mem_matrixLieAlgebra_iff.mp X.property t
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

/-- For the trace form, `-tr (X * Y)` is real and coincides with the trace form embedded in `𝕜`. -/
theorem neg_trace_mul_eq_matrixTraceForm (X Y : G.matrixLieAlgebra) :
    -((X : Matrix n n 𝕜) * (Y : Matrix n n 𝕜)).trace = algebraMap ℝ 𝕜 (G.matrixTraceForm X Y) := by
  apply RCLike.ext
  · simp only [map_neg, RCLike.algebraMap_eq_ofReal, RCLike.ofReal_re]
    exact (matrixTraceForm_apply (G := G) X Y).symm
  · have him := Matrix.im_trace_mul_eq_zero_of_conjTranspose_eq_neg
      (conjTranspose_eq_neg_of_mem_matrixLieAlgebra X.property)
      (conjTranspose_eq_neg_of_mem_matrixLieAlgebra Y.property)
    simpa using him

section

open scoped InnerProductSpace Matrix.Norms.Frobenius

/-- The trace form on the Lie algebra is the restriction of the real Frobenius inner product. -/
theorem matrixTraceForm_eq_frobenius_real_inner (X Y : G.matrixLieAlgebra) :
    G.matrixTraceForm X Y = ⟪(X : Matrix n n 𝕜), (Y : Matrix n n 𝕜)⟫_ℝ := by
  rw [matrixTraceForm_apply, Matrix.frobenius_real_inner_eq_neg_re_trace_mul_of_conjTranspose_eq_neg
    (conjTranspose_eq_neg_of_mem_matrixLieAlgebra X.property)]

/-- The trace form is symmetric. -/
theorem isSymm_matrixTraceForm : G.matrixTraceForm.IsSymm :=
  ⟨fun X Y ↦ by simpa only [matrixTraceForm_eq_frobenius_real_inner] using real_inner_comm _ _⟩

/-- The trace form of an element with itself is the sum of the squared norms of its entries. -/
theorem matrixTraceForm_self (X : G.matrixLieAlgebra) :
    G.matrixTraceForm X X = ∑ i, ∑ j, ‖(X : Matrix n n 𝕜) i j‖ ^ 2 := by
  rw [matrixTraceForm_eq_frobenius_real_inner, real_inner_self_eq_norm_sq,
    Matrix.frobenius_norm_sq_eq_sum_norm_sq]

/-- The trace form is positive definite. -/
theorem posDef_matrixTraceForm : G.matrixTraceForm.toQuadraticMap.PosDef := by
  intro X hX
  rw [LinearMap.BilinMap.toQuadraticMap_apply, matrixTraceForm_eq_frobenius_real_inner,
    real_inner_self_eq_norm_sq]
  exact sq_pos_of_pos (norm_pos_iff.mpr (fun h ↦ hX (Subtype.ext h)))

/-- The trace form is invariant under the adjoint action of `G`. -/
theorem isInvariantForm_matrixTraceForm :
    TauCeti.Representation.IsInvariantForm G.matrixAdjointRepresentation G.matrixTraceForm := by
  refine TauCeti.Representation.isInvariantForm_iff.mpr fun g X Y ↦ ?_
  simpa only [matrixTraceForm_eq_frobenius_real_inner, coe_matrixAdjointRepresentation_apply,
    Matrix.star_eq_conjTranspose] using
    Matrix.UnitaryGroup.frobenius_real_inner_conj (g : Matrix.unitaryGroup n 𝕜)
      (X : Matrix n n 𝕜) (Y : Matrix n n 𝕜)

end

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
      obtain ⟨g, hg, hgt⟩ := mem_matrixLieAlgebra_iff.mp hX t
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
    rw [mem_matrixLieAlgebra_iff, mem_matrixLieAlgebra_iff]
    refine ⟨hoff.1, hoff.2, fun t ↦ ?_, fun t ↦ ?_⟩
    · obtain ⟨g₁, h₁, -, -, he, -⟩ := hdiag t
      exact ⟨g₁, h₁, he⟩
    · obtain ⟨-, -, g₂, h₂, -, he⟩ := hdiag t
      exact ⟨g₂, h₂, he⟩
  · rintro ⟨h₁₂, h₂₁, h₁, h₂⟩
    rw [mem_matrixLieAlgebra_iff] at h₁ h₂ ⊢
    intro t
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

section Standard

open TauCeti TauCeti.Lie

open scoped Matrix.Norms.Operator

attribute [local instance] NormedAddCommGroup.toSeminormedAddCommGroup

attribute [local instance] Matrix.linftyOpTopologicalSpace Matrix.linftyOpContinuousStar

/-- The Lie algebra of the full unitary group `ClosedSubgroup.unitary n 𝕜` consists of the
skew-Hermitian matrices `Xᴴ = -X`. -/
@[simp]
theorem mem_matrixLieAlgebra_unitary_iff {X : Matrix n n 𝕜} :
    X ∈ (unitary n 𝕜).matrixLieAlgebra ↔ Xᴴ = -X :=
  mem_matrixLieAlgebra_iff_conjTranspose_eq_neg_of_forall_mem (mem_unitary n 𝕜)

/-- The Lie algebra of the special unitary group `SU(n)` consists of the trace-free skew-Hermitian
matrices `Xᴴ = -X` and `tr X = 0`. -/
@[simp]
theorem mem_matrixLieAlgebra_specialUnitary_iff {X : Matrix n n 𝕜} :
    X ∈ (specialUnitary n 𝕜).matrixLieAlgebra ↔ Xᴴ = -X ∧ X.trace = 0 := by
  have h := forall_exp_mem_iff (specialUnitary n 𝕜) X
  rw [toGL_specialUnitary] at h
  exact h.trans (unitsLieAlgebraLieEquiv_symm_mem_GLSpecialUnitary_lieSubalgebra_iff X)

end Standard

section Unique

/-- A `1 × 1` matrix over `𝕜` lies in the Lie algebra of `U(1)` iff its entry has real part
`0`. -/
theorem mem_matrixLieAlgebra_unitary_fin_one_iff {𝕜 : Type*} [RCLike 𝕜]
    (X : Matrix (Fin 1) (Fin 1) 𝕜) :
    X ∈ (unitary (Fin 1) 𝕜).matrixLieAlgebra ↔ RCLike.re (X 0 0) = 0 := by
  rw [mem_matrixLieAlgebra_unitary_iff]
  constructor
  · intro h
    exact Matrix.re_apply_self_eq_zero_of_conjTranspose_eq_neg h 0
  · intro hre
    ext i j
    fin_cases i
    fin_cases j
    apply RCLike.ext
    · simp [hre]
    · simp

/-- On a singleton index type (in particular `U(1)`), the Lie algebra is abelian: every Lie
bracket vanishes. -/
@[simp]
theorem lie_eq_zero_of_unique [Unique n] (X Y : G.matrixLieAlgebra) :
    ⁅X, Y⁆ = 0 := by
  have hmul : (X : Matrix n n 𝕜) * Y = (Y : Matrix n n 𝕜) * X :=
    Matrix.uniqueStarRingEquiv.injective (by simp [mul_comm])
  exact Subtype.ext (by simp [LieRing.of_associative_ring_bracket, hmul])

/-- On a singleton index type (in particular `U(1)`), the adjoint representation is trivial. -/
@[simp]
theorem matrixAdjointRepresentation_eq_id_of_unique [Unique n] (g : G) :
    G.matrixAdjointRepresentation g = LinearMap.id := by
  ext1 X
  ext1
  rw [coe_matrixAdjointRepresentation_apply]
  have hmul : (g.val : Matrix n n 𝕜) * X.val = (X.val : Matrix n n 𝕜) * g.val :=
    Matrix.uniqueStarRingEquiv.injective (by simp [mul_comm])
  rw [hmul, mul_assoc, Unitary.mul_star_self_of_mem g.val.property, mul_one, LinearMap.id_apply]

end Unique

section Countable

/-- Every countable subgroup of `Matrix.unitaryGroup n 𝕜` has trivial Lie algebra `⊥`. -/
theorem matrixLieAlgebra_eq_bot_of_countable
    (hG : (G : Set (Matrix.unitaryGroup n 𝕜)).Countable) :
    G.matrixLieAlgebra = ⊥ := by
  ext X
  simp only [LieSubalgebra.mem_bot]
  exact ⟨eq_zero_of_mem_matrixLieAlgebra_of_countable hG, fun h ↦ h ▸ zero_mem _⟩

end Countable

section Reindex

variable {m : Type*} [Fintype m] [DecidableEq m]

/-- A matrix lies in the Lie algebra of `G.reindex e` iff its inverse reindexing lies in the
Lie algebra of `G`. -/
theorem mem_matrixLieAlgebra_reindex_iff (e : n ≃ m) {Y : Matrix m m 𝕜} :
    Y ∈ (G.reindex e).matrixLieAlgebra ↔ Matrix.reindex e.symm e.symm Y ∈ G.matrixLieAlgebra := by
  rw [mem_matrixLieAlgebra_iff, mem_matrixLieAlgebra_iff]
  refine forall_congr' fun t ↦ ?_
  have hsmul : Matrix.reindex e.symm e.symm (t • Y) = t • Matrix.reindex e.symm e.symm Y := by
    ext i j; rfl
  constructor
  · rintro ⟨V, hV, hEq⟩
    refine ⟨Matrix.unitaryReindexContinuousMulEquiv 𝕜 e.symm V, (mem_reindex_iff e).mp hV, ?_⟩
    rw [Matrix.coe_unitaryReindexContinuousMulEquiv_apply, hEq, ← Matrix.exp_reindex, hsmul]
  · rintro ⟨U, hU, hEq⟩
    refine ⟨Matrix.unitaryReindexContinuousMulEquiv 𝕜 e U,
      unitaryReindexContinuousMulEquiv_mem_reindex e hU, ?_⟩
    rw [Matrix.coe_unitaryReindexContinuousMulEquiv_apply, hEq, ← Matrix.exp_reindex]
    congr 1
    ext i j
    simp

variable (G) in
/-- Reindexing along a bijection `e : n ≃ m` induces a Lie-algebra isomorphism
`G.matrixLieAlgebra ≃ₗ⁅ℝ⁆ (G.reindex e).matrixLieAlgebra`. -/
def matrixLieAlgebraReindexEquiv (e : n ≃ m) :
    G.matrixLieAlgebra ≃ₗ⁅ℝ⁆ (G.reindex e).matrixLieAlgebra :=
  (Matrix.reindexAlgEquiv ℝ 𝕜 e).toLieEquiv.ofSubalgebras G.matrixLieAlgebra
    (G.reindex e).matrixLieAlgebra (by
      ext Y
      simp only [LieSubalgebra.mem_map, mem_matrixLieAlgebra_reindex_iff]
      constructor
      · rintro ⟨X, hX, rfl⟩
        simpa [Matrix.reindex_apply] using hX
      · intro hY
        exact ⟨Matrix.reindex e.symm e.symm Y, hY, by simp [Matrix.reindex_apply]⟩)

/-- The forward map of `matrixLieAlgebraReindexEquiv` reindexes the underlying matrix by `e`. -/
@[simp]
theorem coe_matrixLieAlgebraReindexEquiv_apply (e : n ≃ m) (X : G.matrixLieAlgebra) :
    ((G.matrixLieAlgebraReindexEquiv e X : (G.reindex e).matrixLieAlgebra) : Matrix m m 𝕜) =
      Matrix.reindex e e (X : Matrix n n 𝕜) := by
  simp [matrixLieAlgebraReindexEquiv]

/-- The inverse map of `matrixLieAlgebraReindexEquiv` reindexes the underlying matrix by
`e.symm`. -/
@[simp]
theorem coe_matrixLieAlgebraReindexEquiv_symm_apply (e : n ≃ m)
    (Y : (G.reindex e).matrixLieAlgebra) :
    (((G.matrixLieAlgebraReindexEquiv e).symm Y : G.matrixLieAlgebra) : Matrix n n 𝕜) =
      Matrix.reindex e.symm e.symm (Y : Matrix m m 𝕜) := by
  simp [matrixLieAlgebraReindexEquiv]

/-- Inverse reindexing intertwines the adjoint action of `G.reindex e` with that of `G`. -/
theorem matrixLieAlgebraReindexEquiv_symm_matrixAdjointRepresentation (e : n ≃ m)
    {g : Matrix.unitaryGroup n 𝕜} (hg : g ∈ G) (Y : (G.reindex e).matrixLieAlgebra) :
    (G.matrixLieAlgebraReindexEquiv e).symm
        ((G.reindex e).matrixAdjointRepresentation
          ⟨Matrix.unitaryReindexContinuousMulEquiv 𝕜 e g,
            unitaryReindexContinuousMulEquiv_mem_reindex e hg⟩ Y) =
      G.matrixAdjointRepresentation ⟨g, hg⟩ ((G.matrixLieAlgebraReindexEquiv e).symm Y) := by
  ext1
  simp only [coe_matrixLieAlgebraReindexEquiv_symm_apply, coe_matrixAdjointRepresentation_apply,
    Matrix.coe_unitaryReindexContinuousMulEquiv_apply, Matrix.star_eq_conjTranspose]
  -- Reindexing by `e.symm` is a ring isomorphism `Matrix.reindexRingEquiv`, so it preserves `*`.
  change Matrix.reindexRingEquiv 𝕜 e.symm
      (Matrix.reindex e e (g : Matrix n n 𝕜) * (Y : Matrix m m 𝕜) *
        (Matrix.reindex e e (g : Matrix n n 𝕜))ᴴ) = _
  rw [map_mul, map_mul]
  simp [Matrix.reindexRingEquiv, Matrix.reindex_apply, Matrix.conjTranspose_submatrix]

end Reindex

section EmbeddedLieSubgroup

open TauCeti TauCeti.Lie

open scoped Matrix.Norms.Operator

attribute [local instance] NormedAddCommGroup.toSeminormedAddCommGroup

attribute [local instance] Matrix.linftyOpTopologicalSpace Matrix.linftyOpContinuousStar

/-- Canonical embedded Lie subgroup data for `G.toGL ≤ (Matrix n n 𝕜)ˣ`. -/
def embeddedLieSubgroupData (G : ClosedSubgroup (Matrix.unitaryGroup n 𝕜)) :
    EmbeddedLieSubgroupData 𝓘(ℝ, Matrix n n 𝕜) (toGL G)
      (lieSubalgebraOfSubgroup (I := 𝓘(ℝ, Matrix n n 𝕜)) (toGL G)).toSubmodule :=
  EmbeddedLieSubgroupData.ofIsClosed (I := 𝓘(ℝ, Matrix n n 𝕜)) (isClosed_toGL G)

/-- The group isomorphism `G ≃* G.toGL` induced by `Unitary.toUnits`. -/
def equivToGL (G : ClosedSubgroup (Matrix.unitaryGroup n 𝕜)) : G ≃* toGL G :=
  Subgroup.equivMapOfInjective (G : Subgroup (Matrix.unitaryGroup n 𝕜)) Unitary.toUnits
    Unitary.toUnits_injective

/-- The underlying matrix of `G.equivToGL g` is that of `g`. -/
@[simp]
theorem coe_equivToGL (G : ClosedSubgroup (Matrix.unitaryGroup n 𝕜)) (g : G) :
    ((G.equivToGL g : (Matrix n n 𝕜)ˣ) : Matrix n n 𝕜) = (g : Matrix n n 𝕜) :=
  congrArg Units.val
    (Subgroup.coe_equivMapOfInjective_apply (G : Subgroup (Matrix.unitaryGroup n 𝕜))
      Unitary.toUnits Unitary.toUnits_injective g)

/-- Under the `L∞` operator norm, `G.matrixLieAlgebra` equals `(toGL G).linearLieSubalgebra`. -/
theorem matrixLieAlgebra_eq_linearLieSubalgebra (G : ClosedSubgroup (Matrix.unitaryGroup n 𝕜)) :
    G.matrixLieAlgebra = (toGL G).linearLieSubalgebra := by
  ext X
  exact (forall_exp_mem_iff G X).trans Subgroup.mem_linearLieSubalgebra.symm

end EmbeddedLieSubgroup

end ClosedSubgroup
