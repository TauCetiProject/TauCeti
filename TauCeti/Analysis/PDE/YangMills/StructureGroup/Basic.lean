/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.InvariantForm
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.Normed.Algebra.MatrixExponential
public import Mathlib.LinearAlgebra.UnitaryGroup
public import TauCeti.Analysis.Matrix.Normed
public import TauCeti.Geometry.Lie.Subgroup.Embedded
public import TauCeti.Geometry.Lie.Subgroup.Units
public import TauCeti.Topology.Algebra.UnitaryGroup
import Mathlib.Analysis.InnerProductSpace.Calculus
import TauCeti.Analysis.SpecialFunctions.Exponential
import TauCeti.Geometry.Lie.Subgroup.Unitary

/-!
# Compact matrix structure groups for Yang–Mills theory

A compact matrix structure group is a closed subgroup `G ≤ Matrix.unitaryGroup n ℂ` (for a finite
index type `n`) equipped with an `Ad(G)`-invariant inner product on its real Lie algebra
`𝔤 = {X ∈ 𝔲(n) : exp (t • X) ∈ G for all t : ℝ}`. The group is not assumed connected, so
`Ad(G)`-invariance is genuinely stronger than infinitesimal `ad(𝔤)`-invariance.

This file defines `TauCeti.YangMills.StructureGroup`, its inner-product Lie algebra `G.LieAlgebra`,
the exponential map `G.exp`, the adjoint isometry `G.Ad`, infinitesimal skew-adjointness of
`ad`, and the tangent space identification `g · 𝔤 = 𝔤 · g` as the range of the differential of the
matrix inclusion `G → Matrix n n ℂ`. Canonical constructions (the trace inner product, `U(n)`,
`SU(n)`, restriction to closed subgroups, and finite subgroups) live in
`TauCeti.Analysis.PDE.YangMills.StructureGroup.Constructions`; reindexing and block-diagonal
products live in `TauCeti.Analysis.PDE.YangMills.StructureGroup.Product`; concrete examples
(`U(1)`, `SU(2)`, `{±1}`, and the disconnected counterexample `T² ⋊ ℤ/2`) live in
`TauCeti.Analysis.PDE.YangMills.StructureGroup.Examples`.

## Main definitions

* `TauCeti.YangMills.toGLSubgroup`: embeds a subgroup of `Matrix.unitaryGroup n ℂ` into `GL n ℂ`.
* `TauCeti.YangMills.unitaryLieSubalgebra`: the real matrix Lie subalgebra of `Matrix n n ℂ`
  associated to a subgroup of `Matrix.unitaryGroup n ℂ`.
* `TauCeti.YangMills.StructureGroup`: a closed subgroup `G ≤ Matrix.unitaryGroup n ℂ` together
  with an `Ad(G)`-invariant symmetric positive-definite bilinear form on its Lie algebra.
* `TauCeti.YangMills.StructureGroup.LieAlgebra`: the Lie algebra `𝔤` of a structure group,
  carrying global `LieRing`, `LieAlgebra ℝ`, `NormedAddCommGroup`, `InnerProductSpace ℝ`,
  `FiniteDimensional ℝ`, and `CompleteSpace` instances.
* `TauCeti.YangMills.StructureGroup.exp`: the matrix exponential map `𝔤 → G`.
* `TauCeti.YangMills.StructureGroup.Ad`: the adjoint action of `G` on `𝔤` as a linear isometry
  equivalence (`G.LieAlgebra ≃ₗᵢ[ℝ] G.LieAlgebra`).
* `TauCeti.YangMills.StructureGroup.tangentSpace`: the tangent space `g · 𝔤` of `G` at `g ∈ G`
  as a real subspace of `Matrix n n ℂ`.

## Main results

* `TauCeti.YangMills.mem_unitaryLieSubalgebra_iff`: for a closed subgroup `H ≤ U(n)`, a matrix `X`
  lies in its Lie algebra iff `exp (t • X) ∈ H` for all `t : ℝ`.
* `TauCeti.YangMills.StructureGroup.inner_lie_left` and
  `TauCeti.YangMills.StructureGroup.adjoint_ad`: `ad(X)` is skew-adjoint with respect to the
  `Ad(G)`-invariant inner product on `𝔤`.
* `TauCeti.YangMills.StructureGroup.tangentSpace_eq_mulRight`,
  `TauCeti.YangMills.StructureGroup.range_mvfderiv_matrixInclusion`, and
  `TauCeti.YangMills.StructureGroup.range_mvfderiv_matrixInclusion_eq_mulRight`: the tangent space
  of `G` at `g` inside `Matrix n n ℂ` is `g · 𝔤 = 𝔤 · g`.

## References

* S.-J. Oh and D. Tataru, *The Yang–Mills heat flow and the caloric gauge*, Astérisque 436 (2022),
  §1.1.
* S.-J. Oh and D. Tataru, *The hyperbolic Yang–Mills equation for connections in an arbitrary
  topological class*, Comm. Math. Phys. 365 (2019), §1.1.
-/

public section

open Manifold NormedSpace Set
open scoped ComplexConjugate ContDiff InnerProductSpace Manifold Matrix

noncomputable section

namespace TauCeti.YangMills

universe u

attribute [local instance 100] LieRing.ofAssociativeRing

/-! ### Private matrix-exponential helpers in the default matrix topology -/

section MatrixExpHelpers

private theorem exp_matrix_add_of_commute {n : Type u} [Fintype n] [DecidableEq n]
    {X Y : Matrix n n ℂ} (h : Commute X Y) :
    NormedSpace.exp (X + Y) = NormedSpace.exp X * NormedSpace.exp Y := by
  let _ : NormedRing (Matrix n n ℂ) := Matrix.linftyOpNormedRing
  let _ : NormedAlgebra ℝ (Matrix n n ℂ) := Matrix.linftyOpNormedAlgebra
  let _ : NormedAlgebra ℚ (Matrix n n ℂ) := TauCeti.normedAlgebraRatOfReal
  let _ : CompleteSpace (Matrix n n ℂ) := Matrix.linftyOpCompleteSpace
  exact NormedSpace.exp_add_of_commute h

private theorem exp_matrix_units_conj {n : Type u} [Fintype n] [DecidableEq n]
    (u : GL n ℂ) (X : Matrix n n ℂ) :
    NormedSpace.exp ((u : Matrix n n ℂ) * X * ((u⁻¹ : GL n ℂ) : Matrix n n ℂ)) =
      (u : Matrix n n ℂ) * NormedSpace.exp X * ((u⁻¹ : GL n ℂ) : Matrix n n ℂ) := by
  let _ : NormedRing (Matrix n n ℂ) := Matrix.linftyOpNormedRing
  let _ : NormedAlgebra ℝ (Matrix n n ℂ) := Matrix.linftyOpNormedAlgebra
  let _ : NormedAlgebra ℚ (Matrix n n ℂ) := TauCeti.normedAlgebraRatOfReal
  let _ : CompleteSpace (Matrix n n ℂ) := Matrix.linftyOpCompleteSpace
  exact NormedSpace.exp_units_conj u X

end MatrixExpHelpers

/-! ### Unitary subgroups and their matrix Lie subalgebras -/

section UnitarySubgroup

variable {n : Type u} [Fintype n] [DecidableEq n]

/-- View a subgroup of `Matrix.unitaryGroup n ℂ` as a subgroup of `GL n ℂ` via
`Unitary.toUnits`. -/
def toGLSubgroup (H : Subgroup (Matrix.unitaryGroup n ℂ)) : Subgroup (GL n ℂ) :=
  H.map Unitary.toUnits

theorem mem_toGLSubgroup_iff {H : Subgroup (Matrix.unitaryGroup n ℂ)} {g : GL n ℂ} :
    g ∈ toGLSubgroup H ↔ ∃ u ∈ H, Unitary.toUnits u = g :=
  Subgroup.mem_map

@[simp]
theorem toUnits_mem_toGLSubgroup_iff {H : Subgroup (Matrix.unitaryGroup n ℂ)}
    {u : Matrix.unitaryGroup n ℂ} :
    Unitary.toUnits u ∈ toGLSubgroup H ↔ u ∈ H := by
  simp only [mem_toGLSubgroup_iff]
  refine ⟨?_, fun hu ↦ ⟨u, hu, rfl⟩⟩
  rintro ⟨v, hv, hvu⟩
  have h : v = u := Unitary.toUnits_injective hvu
  exact h ▸ hv

/-- Every unitary subgroup viewed in `GL n ℂ` is contained in `unitarySubgroup (GL n ℂ)`. -/
theorem toGLSubgroup_le_unitarySubgroup (H : Subgroup (Matrix.unitaryGroup n ℂ)) :
    toGLSubgroup H ≤ unitarySubgroup (GL n ℂ) := by
  rintro g ⟨u, -, rfl⟩
  exact TauCeti.mem_unitary_units_iff.mpr u.2

/-- A larger subgroup of `U(n)` maps to a larger subgroup of `GL n ℂ`. -/
theorem toGLSubgroup_mono {H K : Subgroup (Matrix.unitaryGroup n ℂ)} (h : H ≤ K) :
    toGLSubgroup H ≤ toGLSubgroup K :=
  Subgroup.map_mono h

/-- The image of `⊤ ≤ U(n)` in `GL n ℂ` is `unitarySubgroup (GL n ℂ)`. -/
@[simp]
theorem toGLSubgroup_top :
    toGLSubgroup (⊤ : Subgroup (Matrix.unitaryGroup n ℂ)) = unitarySubgroup (GL n ℂ) := by
  ext g
  simp only [mem_toGLSubgroup_iff, Subgroup.mem_top, true_and, mem_unitarySubgroup_iff,
    TauCeti.mem_unitary_units_iff]
  refine ⟨?_, fun hg ↦ ⟨⟨g, hg⟩, Units.ext rfl⟩⟩
  rintro ⟨u, rfl⟩
  exact u.2

/-- A subgroup `H ≤ U(n)` is closed in `U(n)` iff its image in `GL n ℂ` is closed in `GL n ℂ`. -/
theorem isClosed_toGLSubgroup_iff (H : Subgroup (Matrix.unitaryGroup n ℂ)) :
    IsClosed ((toGLSubgroup H : Subgroup (GL n ℂ)) : Set (GL n ℂ)) ↔
      IsClosed (H : Set (Matrix.unitaryGroup n ℂ)) := by
  let e := TauCeti.unitarySubgroupUnitsHomeomorph (Matrix n n ℂ)
  have hcl : IsClosed ((unitarySubgroup (Matrix n n ℂ)ˣ : Subgroup (Matrix n n ℂ)ˣ) :
      Set (Matrix n n ℂ)ˣ) :=
    TauCeti.isClosed_unitarySubgroup_units (Matrix n n ℂ)
  have himg : ((toGLSubgroup H : Subgroup (GL n ℂ)) : Set (GL n ℂ)) =
      Subtype.val '' (e ⁻¹' (H : Set (Matrix.unitaryGroup n ℂ))) := by
    ext g
    simp only [SetLike.mem_coe, mem_toGLSubgroup_iff, Set.mem_image, Set.mem_preimage]
    constructor
    · rintro ⟨u, hu, rfl⟩
      refine ⟨⟨Unitary.toUnits u, TauCeti.mem_unitary_units_iff.mpr u.2⟩, ?_, rfl⟩
      have he : e ⟨Unitary.toUnits u, TauCeti.mem_unitary_units_iff.mpr u.2⟩ = u := by
        apply Subtype.ext
        rw [TauCeti.unitarySubgroupUnitsHomeomorph_apply,
          unitarySubgroupUnitsEquiv_apply_coe, Unitary.val_toUnits_apply]
      rw [he]
      exact hu
    · rintro ⟨⟨g', hg'⟩, hmem, rfl⟩
      refine ⟨⟨(g' : Matrix n n ℂ), TauCeti.mem_unitary_units_iff.mp hg'⟩, ?_, Units.ext rfl⟩
      have he : e ⟨g', hg'⟩ = ⟨(g' : Matrix n n ℂ), TauCeti.mem_unitary_units_iff.mp hg'⟩ := by
        apply Subtype.ext
        rw [TauCeti.unitarySubgroupUnitsHomeomorph_apply, unitarySubgroupUnitsEquiv_apply_coe]
      rw [← he]
      exact hmem
  rw [himg]
  exact (hcl.isClosedEmbedding_subtypeVal.isClosed_iff_image_isClosed
    (s := e ⁻¹' (H : Set (Matrix.unitaryGroup n ℂ)))).symm.trans e.isClosed_preimage

/-- The real Lie subalgebra of `Matrix n n ℂ` associated to a subgroup `H ≤ U(n)`, defined via
the embedded general linear subgroup `toGLSubgroup H ≤ GL n ℂ`. -/
def unitaryLieSubalgebra (H : Subgroup (Matrix.unitaryGroup n ℂ)) :
    LieSubalgebra ℝ (Matrix n n ℂ) :=
  letI : NormedRing (Matrix n n ℂ) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℝ (Matrix n n ℂ) := Matrix.linftyOpNormedAlgebra
  TauCeti.Lie.unitsLieSubalgebra (toGLSubgroup H)

open scoped Matrix.Norms.Operator in
/-- Under the `L∞` operator norm, `unitaryLieSubalgebra H` agrees with
`TauCeti.Lie.unitsLieSubalgebra (toGLSubgroup H)`. -/
theorem unitaryLieSubalgebra_eq_unitsLieSubalgebra (H : Subgroup (Matrix.unitaryGroup n ℂ)) :
    unitaryLieSubalgebra H = TauCeti.Lie.unitsLieSubalgebra (toGLSubgroup H) :=
  (rfl)

open TauCeti.Lie in
/-- Every element of `unitaryLieSubalgebra H` is skew-Hermitian (`Xᴴ = -X`). -/
theorem conjTranspose_eq_neg_of_mem_unitaryLieSubalgebra
    {H : Subgroup (Matrix.unitaryGroup n ℂ)} {X : Matrix n n ℂ}
    (hX : X ∈ unitaryLieSubalgebra H) : Xᴴ = -X := by
  let _ : NormedRing (Matrix n n ℂ) := Matrix.linftyOpNormedRing
  let _ : NormedAlgebra ℝ (Matrix n n ℂ) := Matrix.linftyOpNormedAlgebra
  have hmem : X ∈ unitsLieSubalgebra (unitarySubgroup (GL n ℂ)) :=
    unitsLieSubalgebra_mono (toGLSubgroup_le_unitarySubgroup H) hX
  rw [mem_unitsLieSubalgebra_iff] at hmem
  exact (unitsLieAlgebraLieEquiv_symm_mem_lieSubalgebraOfSubgroup_iff_conjTranspose_eq_neg
    (n := n) (𝕜 := ℂ) X).1 hmem

/-- **Exponential-line characterization of the Lie algebra of a closed unitary subgroup.**
For a closed subgroup `H ≤ U(n)`, a matrix `X` belongs to `unitaryLieSubalgebra H` iff
`exp (t • X)` lies in `H` for every `t : ℝ`. -/
theorem mem_unitaryLieSubalgebra_iff {H : Subgroup (Matrix.unitaryGroup n ℂ)}
    (hH : IsClosed (H : Set (Matrix.unitaryGroup n ℂ))) (X : Matrix n n ℂ) :
    X ∈ unitaryLieSubalgebra H ↔
      ∀ t : ℝ, NormedSpace.exp (t • X) ∈
        Subtype.val '' (H : Set (Matrix.unitaryGroup n ℂ)) := by
  let _ : NormedRing (Matrix n n ℂ) := Matrix.linftyOpNormedRing
  let _ : NormedAlgebra ℝ (Matrix n n ℂ) := Matrix.linftyOpNormedAlgebra
  let _ : NormedAlgebra ℚ (Matrix n n ℂ) := TauCeti.normedAlgebraRatOfReal
  have hcl : IsClosed ((toGLSubgroup H : Subgroup (GL n ℂ)) : Set (GL n ℂ)) :=
    (isClosed_toGLSubgroup_iff H).2 hH
  change X ∈ TauCeti.Lie.unitsLieSubalgebra (toGLSubgroup H) ↔ _
  rw [TauCeti.Lie.mem_unitsLieSubalgebra_iff_forall_expUnit hcl]
  refine forall_congr' fun t ↦ ?_
  simp only [mem_toGLSubgroup_iff, Set.mem_image, SetLike.mem_coe]
  constructor
  · rintro ⟨u, hu, hEq⟩
    refine ⟨u, hu, ?_⟩
    have hval := congrArg Units.val hEq
    rw [Unitary.val_toUnits_apply, TauCeti.expUnit_coe] at hval
    exact hval
  · rintro ⟨u, hu, hEq⟩
    refine ⟨u, hu, Units.ext ?_⟩
    rw [Unitary.val_toUnits_apply, TauCeti.expUnit_coe]
    exact hEq

/-- Equivalent characterization including skew-Hermitianness explicitly: for a closed subgroup
`H ≤ U(n)`, `X ∈ unitaryLieSubalgebra H` iff `Xᴴ = -X` and `exp (t • X) ∈ H` for all `t : ℝ`. -/
theorem mem_unitaryLieSubalgebra_iff_skewHermitian_and_exp
    {H : Subgroup (Matrix.unitaryGroup n ℂ)}
    (hH : IsClosed (H : Set (Matrix.unitaryGroup n ℂ))) (X : Matrix n n ℂ) :
    X ∈ unitaryLieSubalgebra H ↔
      Xᴴ = -X ∧
        ∀ t : ℝ, NormedSpace.exp (t • X) ∈
          Subtype.val '' (H : Set (Matrix.unitaryGroup n ℂ)) :=
  ⟨fun hX ↦ ⟨conjTranspose_eq_neg_of_mem_unitaryLieSubalgebra hX,
    (mem_unitaryLieSubalgebra_iff hH X).1 hX⟩,
    fun h ↦ (mem_unitaryLieSubalgebra_iff hH X).2 h.2⟩

open TauCeti.Lie in
/-- The Lie subalgebra of the full unitary group `⊤ ≤ U(n)` is the skew-Hermitian matrices. -/
theorem mem_unitaryLieSubalgebra_top_iff (X : Matrix n n ℂ) :
    X ∈ unitaryLieSubalgebra (⊤ : Subgroup (Matrix.unitaryGroup n ℂ)) ↔ Xᴴ = -X := by
  let _ : NormedRing (Matrix n n ℂ) := Matrix.linftyOpNormedRing
  let _ : NormedAlgebra ℝ (Matrix n n ℂ) := Matrix.linftyOpNormedAlgebra
  change X ∈ unitsLieSubalgebra (toGLSubgroup ⊤) ↔ _
  rw [toGLSubgroup_top, mem_unitsLieSubalgebra_iff]
  exact unitsLieAlgebraLieEquiv_symm_mem_lieSubalgebraOfSubgroup_iff_conjTranspose_eq_neg
    (n := n) (𝕜 := ℂ) X

/-- A larger subgroup of `U(n)` has a larger Lie subalgebra. -/
theorem unitaryLieSubalgebra_mono {H K : Subgroup (Matrix.unitaryGroup n ℂ)} (h : H ≤ K) :
    unitaryLieSubalgebra H ≤ unitaryLieSubalgebra K := by
  let _ : NormedRing (Matrix n n ℂ) := Matrix.linftyOpNormedRing
  let _ : NormedAlgebra ℝ (Matrix n n ℂ) := Matrix.linftyOpNormedAlgebra
  exact TauCeti.Lie.unitsLieSubalgebra_mono (toGLSubgroup_mono h)

/-- Conjugation by an element of `H ≤ U(n)` preserves `unitaryLieSubalgebra H`. -/
theorem conj_mem_unitaryLieSubalgebra {H : Subgroup (Matrix.unitaryGroup n ℂ)}
    {g : Matrix.unitaryGroup n ℂ} (hg : g ∈ H) {X : Matrix n n ℂ}
    (hX : X ∈ unitaryLieSubalgebra H) :
    (g : Matrix n n ℂ) * X * (g : Matrix n n ℂ)ᴴ ∈ unitaryLieSubalgebra H := by
  let _ : NormedRing (Matrix n n ℂ) := Matrix.linftyOpNormedRing
  let _ : NormedAlgebra ℝ (Matrix n n ℂ) := Matrix.linftyOpNormedAlgebra
  have hg' : Unitary.toUnits g ∈ toGLSubgroup H := toUnits_mem_toGLSubgroup_iff.2 hg
  have hconj := TauCeti.Lie.conj_mem_unitsLieSubalgebra (Subgroup.le_normalizer hg') hX
  have hinv : (((Unitary.toUnits g)⁻¹ : GL n ℂ) : Matrix n n ℂ) = (g : Matrix n n ℂ)ᴴ := by
    rw [← map_inv, Unitary.val_toUnits_apply, ← Unitary.star_eq_inv, Unitary.coe_star,
      Matrix.star_eq_conjTranspose]
  change (g : Matrix n n ℂ) * X * (g : Matrix n n ℂ)ᴴ ∈
    TauCeti.Lie.unitsLieSubalgebra (toGLSubgroup H)
  simpa only [Unitary.val_toUnits_apply, hinv] using hconj

end UnitarySubgroup

/-! ### Compact matrix structure groups -/

/-- A **compact matrix structure group** on a finite index type `n`: a closed subgroup
`G ≤ Matrix.unitaryGroup n ℂ` together with an `Ad(G)`-invariant symmetric positive-definite real
bilinear form (inner product) on its Lie algebra `unitaryLieSubalgebra G`.

The group is not assumed connected; `Ad(G)`-invariance is imposed for every `g ∈ G`, which implies
infinitesimal `ad(𝔤)`-invariance and is strictly stronger for disconnected groups. -/
structure StructureGroup (n : Type u) [Fintype n] [DecidableEq n] where
  /-- The underlying subgroup of unitary `n × n` complex matrices. -/
  subgroup : Subgroup (Matrix.unitaryGroup n ℂ)
  /-- Closedness of the subgroup inside `Matrix.unitaryGroup n ℂ`. -/
  isClosed : IsClosed (subgroup : Set (Matrix.unitaryGroup n ℂ))
  /-- The `Ad(G)`-invariant inner product on the Lie algebra, given as a real bilinear form. -/
  bilinForm : LinearMap.BilinForm ℝ (unitaryLieSubalgebra subgroup)
  /-- Symmetry of the inner product on the Lie algebra. -/
  bilinForm_symm : bilinForm.IsSymm
  /-- Strict positive definiteness of the inner product on nonzero Lie algebra elements. -/
  bilinForm_pos : ∀ X : unitaryLieSubalgebra subgroup, X ≠ 0 → 0 < bilinForm X X
  /-- `Ad(G)`-invariance of the inner product: `⟨g X gᴴ, g Y gᴴ⟩ = ⟨X, Y⟩` for all `g ∈ G`. -/
  bilinForm_conj : ∀ (g : subgroup) (X Y : unitaryLieSubalgebra subgroup),
    bilinForm
      ⟨(g.1 : Matrix n n ℂ) * X.1 * (g.1 : Matrix n n ℂ)ᴴ,
        conj_mem_unitaryLieSubalgebra g.2 X.2⟩
      ⟨(g.1 : Matrix n n ℂ) * Y.1 * (g.1 : Matrix n n ℂ)ᴴ,
        conj_mem_unitaryLieSubalgebra g.2 Y.2⟩ =
      bilinForm X Y

namespace StructureGroup

section Basic

variable {n : Type u} [Fintype n] [DecidableEq n]

/-- The real Lie subalgebra of `Matrix n n ℂ` associated to a structure group `G`. -/
abbrev lieSubalgebra (G : StructureGroup n) : LieSubalgebra ℝ (Matrix n n ℂ) :=
  unitaryLieSubalgebra G.subgroup

/-- Two structure groups are equal iff they have the same underlying unitary subgroup and their
bilinear forms agree on all pairs of matrices in the Lie algebra. -/
@[ext]
theorem ext {G₁ G₂ : StructureGroup n} (hsub : G₁.subgroup = G₂.subgroup)
    (hform : ∀ (X Y : Matrix n n ℂ) (hX₁ : X ∈ G₁.lieSubalgebra) (hY₁ : Y ∈ G₁.lieSubalgebra)
      (hX₂ : X ∈ G₂.lieSubalgebra) (hY₂ : Y ∈ G₂.lieSubalgebra),
      G₁.bilinForm ⟨X, hX₁⟩ ⟨Y, hY₁⟩ = G₂.bilinForm ⟨X, hX₂⟩ ⟨Y, hY₂⟩) :
    G₁ = G₂ := by
  cases G₁
  cases G₂
  simp only at hsub
  subst hsub
  congr
  ext X Y
  exact hform X.1 Y.1 X.2 Y.2 X.2 Y.2

variable (G : StructureGroup n)

/-- Exponential-line characterization of `G.lieSubalgebra`. -/
theorem mem_lieSubalgebra_iff (X : Matrix n n ℂ) :
    X ∈ G.lieSubalgebra ↔
      ∀ t : ℝ, NormedSpace.exp (t • X) ∈
        Subtype.val '' (G.subgroup : Set (Matrix.unitaryGroup n ℂ)) :=
  mem_unitaryLieSubalgebra_iff G.isClosed X

/-- Every element of `G.lieSubalgebra` is skew-Hermitian. -/
theorem conjTranspose_eq_neg_of_mem_lieSubalgebra {X : Matrix n n ℂ} (hX : X ∈ G.lieSubalgebra) :
    Xᴴ = -X :=
  conjTranspose_eq_neg_of_mem_unitaryLieSubalgebra hX

/-- The subgroup `G.subgroup` is compact as a topological space. -/
instance instCompactSpaceSubgroup : CompactSpace G.subgroup :=
  isCompact_iff_compactSpace.mp G.isClosed.isCompact

/-- The subgroup `G.subgroup` is a compact subset of `Matrix.unitaryGroup n ℂ`. -/
theorem isCompact_subgroup : IsCompact (G.subgroup : Set (Matrix.unitaryGroup n ℂ)) :=
  G.isClosed.isCompact

/-- The matrix carrier of `G` is a compact subset of `Matrix n n ℂ`. -/
theorem isCompact_matrixCarrier :
    IsCompact (Subtype.val '' (G.subgroup : Set (Matrix.unitaryGroup n ℂ))) :=
  G.isCompact_subgroup.image continuous_subtype_val

/-- The matrix carrier of `G` is closed in `Matrix n n ℂ`. -/
theorem isClosed_matrixCarrier :
    IsClosed (Subtype.val '' (G.subgroup : Set (Matrix.unitaryGroup n ℂ))) :=
  G.isCompact_matrixCarrier.isClosed

/-! ### The inner-product Lie algebra `G.LieAlgebra` -/

/-- The Lie algebra `𝔤` of a compact matrix structure group `G`, equipped with its commutator
bracket and `Ad(G)`-invariant real inner product. -/
@[ext]
structure LieAlgebra (G : StructureGroup n) where
  /-- The underlying skew-Hermitian `n × n` complex matrix. -/
  val : Matrix n n ℂ
  /-- Proof that `val` belongs to the Lie subalgebra of `G`. -/
  property : val ∈ G.lieSubalgebra

namespace LieAlgebra

variable {G}

/-- View an element of `G.LieAlgebra` as an element of the subtype `G.lieSubalgebra`. -/
@[expose] def toSubalgebra (X : G.LieAlgebra) : G.lieSubalgebra := ⟨X.val, X.property⟩

/-- Construct an element of `G.LieAlgebra` from an element of the subtype `G.lieSubalgebra`. -/
@[expose] def ofSubalgebra (X : G.lieSubalgebra) : G.LieAlgebra := ⟨X.1, X.2⟩

@[simp] theorem toSubalgebra_ofSubalgebra (X : G.lieSubalgebra) :
    (ofSubalgebra X).toSubalgebra = X := rfl

@[simp] theorem ofSubalgebra_toSubalgebra (X : G.LieAlgebra) :
    ofSubalgebra X.toSubalgebra = X := rfl

@[simp] theorem val_ofSubalgebra (X : G.lieSubalgebra) : (ofSubalgebra X).val = X.1 := rfl

@[simp] theorem toSubalgebra_val (X : G.LieAlgebra) :
    (X.toSubalgebra : Matrix n n ℂ) = X.val := rfl

instance : Zero G.LieAlgebra := ⟨⟨0, G.lieSubalgebra.zero_mem⟩⟩
instance : Add G.LieAlgebra := ⟨fun X Y ↦ ⟨X.val + Y.val, G.lieSubalgebra.add_mem X.2 Y.2⟩⟩
instance : Neg G.LieAlgebra := ⟨fun X ↦ ⟨-X.val, G.lieSubalgebra.neg_mem X.2⟩⟩
instance : Sub G.LieAlgebra := ⟨fun X Y ↦ ⟨X.val - Y.val, G.lieSubalgebra.sub_mem X.2 Y.2⟩⟩
instance : SMul ℝ G.LieAlgebra := ⟨fun r X ↦ ⟨r • X.val, G.lieSubalgebra.smul_mem r X.2⟩⟩
instance : Bracket G.LieAlgebra G.LieAlgebra :=
  ⟨fun X Y ↦ ⟨X.val * Y.val - Y.val * X.val, G.lieSubalgebra.lie_mem X.2 Y.2⟩⟩

@[simp] theorem val_zero : (0 : G.LieAlgebra).val = 0 := rfl
@[simp] theorem val_add (X Y : G.LieAlgebra) : (X + Y).val = X.val + Y.val := rfl
@[simp] theorem val_neg (X : G.LieAlgebra) : (-X).val = -X.val := rfl
@[simp] theorem val_sub (X Y : G.LieAlgebra) : (X - Y).val = X.val - Y.val := rfl
@[simp] theorem val_smul (r : ℝ) (X : G.LieAlgebra) : (r • X).val = r • X.val := rfl
@[simp] theorem val_lie (X Y : G.LieAlgebra) : ⁅X, Y⁆.val = X.val * Y.val - Y.val * X.val := rfl

@[simp]
theorem conjTranspose_val (X : G.LieAlgebra) : X.valᴴ = -X.val :=
  G.conjTranspose_eq_neg_of_mem_lieSubalgebra X.2

instance : AddCommGroup G.LieAlgebra where
  add_assoc X Y Z := LieAlgebra.ext (add_assoc X.val Y.val Z.val)
  zero_add X := LieAlgebra.ext (zero_add X.val)
  add_zero X := LieAlgebra.ext (add_zero X.val)
  nsmul := nsmulRec
  zsmul := zsmulRec
  neg_add_cancel X := LieAlgebra.ext (neg_add_cancel X.val)
  add_comm X Y := LieAlgebra.ext (add_comm X.val Y.val)
  sub_eq_add_neg X Y := LieAlgebra.ext (sub_eq_add_neg X.val Y.val)

instance : Module ℝ G.LieAlgebra where
  one_smul X := LieAlgebra.ext (one_smul ℝ X.val)
  mul_smul a b X := LieAlgebra.ext (mul_smul a b X.val)
  smul_zero a := LieAlgebra.ext (smul_zero a)
  smul_add a X Y := LieAlgebra.ext (smul_add a X.val Y.val)
  add_smul a b X := LieAlgebra.ext (add_smul a b X.val)
  zero_smul X := LieAlgebra.ext (zero_smul ℝ X.val)

instance : LieRing G.LieAlgebra where
  add_lie X Y Z := LieAlgebra.ext (by simp [mul_add, add_mul]; abel)
  lie_add X Y Z := LieAlgebra.ext (by simp [mul_add, add_mul]; abel)
  lie_self X := LieAlgebra.ext (by simp)
  leibniz_lie X Y Z := LieAlgebra.ext (by
    simp only [val_lie, val_add, mul_sub, sub_mul, mul_assoc]
    abel)

instance : _root_.LieAlgebra ℝ G.LieAlgebra where
  lie_smul r X Y :=
    LieAlgebra.ext (by simp [Algebra.mul_smul_comm, Algebra.smul_mul_assoc, smul_sub])

/-- The inclusion `G.LieAlgebra →ₗ[ℝ] Matrix n n ℂ` of the Lie algebra into matrices. -/
def valLinearMap (G : StructureGroup n) : G.LieAlgebra →ₗ[ℝ] Matrix n n ℂ where
  toFun := LieAlgebra.val
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
theorem valLinearMap_apply (X : G.LieAlgebra) : valLinearMap G X = X.val :=
  (rfl)

theorem valLinearMap_injective : Function.Injective (valLinearMap G) :=
  fun _ _ h ↦ LieAlgebra.ext h

instance : FiniteDimensional ℝ G.LieAlgebra :=
  FiniteDimensional.of_injective (valLinearMap G) valLinearMap_injective

@[no_expose]
instance instInnerProductSpaceCore : InnerProductSpace.Core ℝ G.LieAlgebra where
  inner X Y := G.bilinForm X.toSubalgebra Y.toSubalgebra
  conj_inner_symm X Y := by
    simpa only [conj_trivial] using G.bilinForm_symm.eq Y.toSubalgebra X.toSubalgebra
  re_inner_nonneg X := by
    by_cases hX : X.toSubalgebra = 0
    · simp [hX]
    · exact le_of_lt (G.bilinForm_pos X.toSubalgebra hX)
  definite X hX := by
    by_contra hne
    have hne' : X.toSubalgebra ≠ 0 := fun h ↦ hne (LieAlgebra.ext (congrArg Subtype.val h))
    exact (ne_of_gt (G.bilinForm_pos X.toSubalgebra hne')) hX
  add_left X Y Z := by
    change G.bilinForm (X.toSubalgebra + Y.toSubalgebra) Z.toSubalgebra = _
    simp
  smul_left X Y r := by
    change G.bilinForm (r • X.toSubalgebra) Y.toSubalgebra = _
    simp

instance instNormedAddCommGroup : NormedAddCommGroup G.LieAlgebra :=
  InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℝ)

instance instInnerProductSpace : InnerProductSpace ℝ G.LieAlgebra :=
  InnerProductSpace.ofCore _

instance instCompleteSpace : CompleteSpace G.LieAlgebra :=
  FiniteDimensional.completeSpace ℝ G.LieAlgebra

/-- The inner product on `G.LieAlgebra` is given by `G.bilinForm`. -/
theorem inner_eq_bilinForm (X Y : G.LieAlgebra) :
    ⟪X, Y⟫_ℝ = G.bilinForm X.toSubalgebra Y.toSubalgebra :=
  (rfl)

/-- The squared norm on `G.LieAlgebra` is the quadratic form of `G.bilinForm`. -/
theorem norm_sq_eq_bilinForm (X : G.LieAlgebra) :
    ‖X‖ ^ 2 = G.bilinForm X.toSubalgebra X.toSubalgebra := by
  rw [← real_inner_self_eq_norm_sq, inner_eq_bilinForm]

end LieAlgebra

/-- The canonical Lie-algebra isomorphism `G.LieAlgebra ≃ₗ⁅ℝ⁆ G.lieSubalgebra`. -/
def equivLieSubalgebra (G : StructureGroup n) : G.LieAlgebra ≃ₗ⁅ℝ⁆ G.lieSubalgebra where
  toFun := LieAlgebra.toSubalgebra
  invFun := LieAlgebra.ofSubalgebra
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  map_lie' := fun {_ _} ↦ rfl

@[simp]
theorem equivLieSubalgebra_apply (X : G.LieAlgebra) :
    G.equivLieSubalgebra X = X.toSubalgebra :=
  (rfl)

/-! ### Exponential map `G.exp : G.LieAlgebra → G.subgroup` -/

/-- The matrix exponential map `𝔤 → G` of a compact matrix structure group `G`. -/
def exp (X : G.LieAlgebra) : G.subgroup :=
  have hmem : NormedSpace.exp X.val ∈
      Subtype.val '' (G.subgroup : Set (Matrix.unitaryGroup n ℂ)) := by
    simpa only [one_smul] using (G.mem_lieSubalgebra_iff X.val).1 X.property 1
  ⟨hmem.choose, hmem.choose_spec.1⟩

@[simp]
theorem exp_val (X : G.LieAlgebra) :
    ((G.exp X : G.subgroup).1 : Matrix n n ℂ) = NormedSpace.exp X.val := by
  have hmem : NormedSpace.exp X.val ∈
      Subtype.val '' (G.subgroup : Set (Matrix.unitaryGroup n ℂ)) := by
    simpa only [one_smul] using (G.mem_lieSubalgebra_iff X.val).1 X.property 1
  exact hmem.choose_spec.2

@[simp]
theorem exp_zero : G.exp 0 = 1 := by
  apply Subtype.ext
  apply Subtype.ext
  simp [exp_val]

theorem exp_neg (X : G.LieAlgebra) : G.exp (-X) = (G.exp X)⁻¹ := by
  have hmul : (G.exp X) * (G.exp (-X)) = 1 := by
    apply Subtype.ext
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Submonoid.coe_mul, exp_val, LieAlgebra.val_neg,
      OneMemClass.coe_one]
    rw [← exp_matrix_add_of_commute (Commute.neg_right (Commute.refl X.val)), add_neg_cancel,
      NormedSpace.exp_zero]
  exact eq_inv_of_mul_eq_one_right hmul

theorem exp_add_smul (s t : ℝ) (X : G.LieAlgebra) :
    G.exp ((s + t) • X) = G.exp (s • X) * G.exp (t • X) := by
  apply Subtype.ext
  apply Subtype.ext
  simp only [Subgroup.coe_mul, Submonoid.coe_mul, exp_val, LieAlgebra.val_smul, add_smul]
  exact exp_matrix_add_of_commute ((Commute.refl X.val).smul_left s |>.smul_right t)

/-! ### Adjoint action `Ad` and skew-adjointness of `ad` -/

/-- The adjoint action `Ad(g) X = g X gᴴ` of `g ∈ G` on the inner-product Lie algebra
`G.LieAlgebra`, bundled as a linear isometry equivalence. -/
def Ad (g : G.subgroup) : G.LieAlgebra ≃ₗᵢ[ℝ] G.LieAlgebra where
  toFun X := ⟨(g.1 : Matrix n n ℂ) * X.val * (g.1 : Matrix n n ℂ)ᴴ,
    conj_mem_unitaryLieSubalgebra g.2 X.property⟩
  invFun X := ⟨(g.1 : Matrix n n ℂ)ᴴ * X.val * (g.1 : Matrix n n ℂ), by
    have h := conj_mem_unitaryLieSubalgebra (G.subgroup.inv_mem g.2) X.property
    have hinv : ((g.1⁻¹ : Matrix.unitaryGroup n ℂ) : Matrix n n ℂ) = (g.1 : Matrix n n ℂ)ᴴ := by
      rw [← Unitary.star_eq_inv, Unitary.coe_star, Matrix.star_eq_conjTranspose]
    simpa only [hinv, Matrix.conjTranspose_conjTranspose] using h⟩
  map_add' X Y := LieAlgebra.ext (by simp [mul_add, add_mul])
  map_smul' r X := LieAlgebra.ext (by simp [Algebra.mul_smul_comm, Algebra.smul_mul_assoc])
  left_inv X := LieAlgebra.ext (by
    have h1 : (g.1 : Matrix n n ℂ)ᴴ * (g.1 : Matrix n n ℂ) = 1 := by
      simpa only [Matrix.star_eq_conjTranspose] using Matrix.mem_unitaryGroup_iff'.1 g.1.2
    calc (g.1 : Matrix n n ℂ)ᴴ * ((g.1 : Matrix n n ℂ) * X.val * (g.1 : Matrix n n ℂ)ᴴ) *
          (g.1 : Matrix n n ℂ)
        = ((g.1 : Matrix n n ℂ)ᴴ * (g.1 : Matrix n n ℂ)) * X.val *
          ((g.1 : Matrix n n ℂ)ᴴ * (g.1 : Matrix n n ℂ)) := by simp [mul_assoc]
      _ = X.val := by rw [h1, one_mul, mul_one])
  right_inv X := LieAlgebra.ext (by
    have h2 : (g.1 : Matrix n n ℂ) * (g.1 : Matrix n n ℂ)ᴴ = 1 := by
      simpa only [Matrix.star_eq_conjTranspose] using Matrix.mem_unitaryGroup_iff.1 g.1.2
    calc (g.1 : Matrix n n ℂ) * ((g.1 : Matrix n n ℂ)ᴴ * X.val * (g.1 : Matrix n n ℂ)) *
          (g.1 : Matrix n n ℂ)ᴴ
        = ((g.1 : Matrix n n ℂ) * (g.1 : Matrix n n ℂ)ᴴ) * X.val *
          ((g.1 : Matrix n n ℂ) * (g.1 : Matrix n n ℂ)ᴴ) := by simp [mul_assoc]
      _ = X.val := by rw [h2, one_mul, mul_one])
  norm_map' X := by
    let Y : G.LieAlgebra := ⟨(g.1 : Matrix n n ℂ) * X.val * (g.1 : Matrix n n ℂ)ᴴ,
      conj_mem_unitaryLieSubalgebra g.2 X.property⟩
    change ‖Y‖ = ‖X‖
    have hsq : ‖Y‖ ^ 2 = ‖X‖ ^ 2 := by
      rw [LieAlgebra.norm_sq_eq_bilinForm, LieAlgebra.norm_sq_eq_bilinForm]
      exact G.bilinForm_conj g X.toSubalgebra X.toSubalgebra
    nlinarith [norm_nonneg X, norm_nonneg Y]

@[simp]
theorem Ad_val (g : G.subgroup) (X : G.LieAlgebra) :
    (G.Ad g X).val = (g.1 : Matrix n n ℂ) * X.val * (g.1 : Matrix n n ℂ)ᴴ :=
  (rfl)

theorem Ad_val_eq_mul_inv (g : G.subgroup) (X : G.LieAlgebra) :
    (G.Ad g X).val = (g.1 : Matrix n n ℂ) * X.val * ((g⁻¹ : G.subgroup).1 : Matrix n n ℂ) := by
  have hinv : ((g⁻¹ : G.subgroup).1 : Matrix n n ℂ) = (g.1 : Matrix n n ℂ)ᴴ := by
    rw [Subgroup.coe_inv, ← Unitary.star_eq_inv, Unitary.coe_star, Matrix.star_eq_conjTranspose]
  rw [Ad_val, hinv]

@[simp]
theorem Ad_one : G.Ad 1 = LinearIsometryEquiv.refl ℝ G.LieAlgebra := by
  ext X
  simp [Ad_val]

theorem Ad_mul (g h : G.subgroup) (X : G.LieAlgebra) :
    G.Ad (g * h) X = G.Ad g (G.Ad h X) := by
  apply LieAlgebra.ext
  simp [Ad_val, Matrix.conjTranspose_mul, mul_assoc]

@[simp]
theorem Ad_symm (g : G.subgroup) : (G.Ad g).symm = G.Ad g⁻¹ := by
  apply LinearIsometryEquiv.ext
  intro X
  apply LieAlgebra.ext
  have hinv : ((g⁻¹ : G.subgroup).1 : Matrix n n ℂ) = (g.1 : Matrix n n ℂ)ᴴ := by
    rw [Subgroup.coe_inv, ← Unitary.star_eq_inv, Unitary.coe_star, Matrix.star_eq_conjTranspose]
  change (g.1 : Matrix n n ℂ)ᴴ * X.val * (g.1 : Matrix n n ℂ) = _
  rw [Ad_val, hinv, Matrix.conjTranspose_conjTranspose]

/-- `Ad(g)` preserves the Lie bracket on `G.LieAlgebra`. -/
theorem Ad_lie (g : G.subgroup) (X Y : G.LieAlgebra) :
    G.Ad g ⁅X, Y⁆ = ⁅G.Ad g X, G.Ad g Y⁆ := by
  apply LieAlgebra.ext
  have h1 : (g.1 : Matrix n n ℂ)ᴴ * (g.1 : Matrix n n ℂ) = 1 := by
    simpa only [Matrix.star_eq_conjTranspose] using Matrix.mem_unitaryGroup_iff'.1 g.1.2
  simp only [Ad_val, LieAlgebra.val_lie, mul_sub, sub_mul, mul_assoc]
  have hX : (g.1 : Matrix n n ℂ) * (X.val * ((g.1 : Matrix n n ℂ)ᴴ *
      ((g.1 : Matrix n n ℂ) * (Y.val * (g.1 : Matrix n n ℂ)ᴴ)))) =
      (g.1 : Matrix n n ℂ) * (X.val * (Y.val * (g.1 : Matrix n n ℂ)ᴴ)) := by
    rw [← mul_assoc (g.1 : Matrix n n ℂ)ᴴ, h1, one_mul]
  have hY : (g.1 : Matrix n n ℂ) * (Y.val * ((g.1 : Matrix n n ℂ)ᴴ *
      ((g.1 : Matrix n n ℂ) * (X.val * (g.1 : Matrix n n ℂ)ᴴ)))) =
      (g.1 : Matrix n n ℂ) * (Y.val * (X.val * (g.1 : Matrix n n ℂ)ᴴ)) := by
    rw [← mul_assoc (g.1 : Matrix n n ℂ)ᴴ, h1, one_mul]
  rw [hX, hY]

/-- `Ad(g)` as a Lie-algebra automorphism of `G.LieAlgebra`. -/
def adLieEquiv (g : G.subgroup) : G.LieAlgebra ≃ₗ⁅ℝ⁆ G.LieAlgebra where
  __ := (G.Ad g).toLinearEquiv
  map_lie' := fun {X Y} ↦ G.Ad_lie g X Y

@[simp]
theorem adLieEquiv_apply (g : G.subgroup) (X : G.LieAlgebra) :
    G.adLieEquiv g X = G.Ad g X :=
  (rfl)

theorem inner_Ad (g : G.subgroup) (X Y : G.LieAlgebra) :
    ⟪G.Ad g X, G.Ad g Y⟫_ℝ = ⟪X, Y⟫_ℝ :=
  (G.Ad g).inner_map_map X Y

theorem norm_Ad (g : G.subgroup) (X : G.LieAlgebra) :
    ‖G.Ad g X‖ = ‖X‖ :=
  (G.Ad g).norm_map X

/-- Naturality of the exponential map with respect to conjugation:
`g * exp X * g⁻¹ = exp (Ad g X)`. -/
theorem conj_exp (g : G.subgroup) (X : G.LieAlgebra) :
    g * G.exp X * g⁻¹ = G.exp (G.Ad g X) := by
  apply Subtype.ext
  apply Subtype.ext
  have hinv : ((g⁻¹ : G.subgroup).1 : Matrix n n ℂ) = (g.1 : Matrix n n ℂ)ᴴ := by
    rw [Subgroup.coe_inv, ← Unitary.star_eq_inv, Unitary.coe_star, Matrix.star_eq_conjTranspose]
  simp only [Subgroup.coe_mul, Submonoid.coe_mul, exp_val, Ad_val]
  have hu := exp_matrix_units_conj (Unitary.toUnits g.1) X.val
  have hu_inv : (((Unitary.toUnits g.1)⁻¹ : GL n ℂ) : Matrix n n ℂ) = (g.1 : Matrix n n ℂ)ᴴ := by
    rw [← map_inv, Unitary.val_toUnits_apply, ← Unitary.star_eq_inv, Unitary.coe_star,
      Matrix.star_eq_conjTranspose]
  rw [Unitary.val_toUnits_apply, hu_inv] at hu
  rw [hinv]
  exact hu.symm

/-- Differentiating `t ↦ Ad (exp (t • X)) Y` at `t = 0` gives `⁅X, Y⁆`. -/
theorem hasDerivAt_Ad_exp_smul (X Y : G.LieAlgebra) :
    HasDerivAt (fun t : ℝ ↦ G.Ad (G.exp (t • X)) Y) ⁅X, Y⁆ 0 := by
  let _ : NormedRing (Matrix n n ℂ) := Matrix.linftyOpNormedRing
  let _ : NormedAlgebra ℝ (Matrix n n ℂ) := Matrix.linftyOpNormedAlgebra
  let _ : CompleteSpace (Matrix n n ℂ) := Matrix.linftyOpCompleteSpace
  have hker : LinearMap.ker (LieAlgebra.valLinearMap G) = ⊥ :=
    LinearMap.ker_eq_bot.2 LieAlgebra.valLinearMap_injective
  obtain ⟨π, hπ⟩ := (LieAlgebra.valLinearMap G).exists_leftInverse_of_injective hker
  have hπ_apply : ∀ Z : G.LieAlgebra, π Z.val = Z := fun Z ↦ by
    change (π.comp (LieAlgebra.valLinearMap G)) Z = Z
    rw [hπ, LinearMap.id_apply]
  have hderiv : HasDerivAt
      (fun t : ℝ ↦ π (NormedSpace.exp (t • X.val) * Y.val * NormedSpace.exp (t • -X.val)))
      (π ⁅X, Y⁆.val) 0 :=
    (LinearMap.toContinuousLinearMap π).hasFDerivAt.comp_hasDerivAt 0
      (TauCeti.hasDerivAt_exp_mul_const_mul_exp_neg X.val Y.val)
  rw [hπ_apply] at hderiv
  refine hderiv.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t ↦ ?_)
  dsimp only
  rw [← hπ_apply (G.Ad (G.exp (t • X)) Y)]
  congr 1
  rw [G.Ad_val_eq_mul_inv, ← G.exp_neg, ← smul_neg, G.exp_val, G.exp_val,
    LieAlgebra.val_smul, LieAlgebra.val_smul, LieAlgebra.val_neg]

/-- **Infinitesimal skew-adjointness of `ad(X)`.** Differentiating `Ad(G)`-invariance along
`exp (t • X)` at `t = 0` yields `⟪⁅X, Y⁆, Z⟫ = -⟪Y, ⁅X, Z⁆⟫`. -/
theorem inner_lie_left (X Y Z : G.LieAlgebra) :
    ⟪⁅X, Y⁆, Z⟫_ℝ = -⟪Y, ⁅X, Z⁆⟫_ℝ := by
  have hconst : (fun t : ℝ ↦ ⟪G.Ad (G.exp (t • X)) Y, G.Ad (G.exp (t • X)) Z⟫_ℝ) =
      fun _ : ℝ ↦ ⟪Y, Z⟫_ℝ := by
    funext t
    exact G.inner_Ad (G.exp (t • X)) Y Z
  have hzero :
      HasDerivAt (fun t : ℝ ↦ ⟪G.Ad (G.exp (t • X)) Y, G.Ad (G.exp (t • X)) Z⟫_ℝ) 0 0 := by
    rw [hconst]
    exact hasDerivAt_const 0 ⟪Y, Z⟫_ℝ
  have hprod := (G.hasDerivAt_Ad_exp_smul X Y).inner ℝ (G.hasDerivAt_Ad_exp_smul X Z)
  simp only [zero_smul, G.exp_zero, G.Ad_one, LinearIsometryEquiv.coe_refl, id_eq] at hprod
  have heq : ⟪Y, ⁅X, Z⁆⟫_ℝ + ⟪⁅X, Y⁆, Z⟫_ℝ = 0 := hprod.unique hzero
  linarith

/-- Right-hand form of skew-adjointness of `ad`: `⟪X, ⁅Y, Z⁆⟫ = -⟪⁅Y, X⁆, Z⟫`. -/
theorem inner_lie_right (X Y Z : G.LieAlgebra) :
    ⟪X, ⁅Y, Z⁆⟫_ℝ = -⟪⁅Y, X⁆, Z⟫_ℝ := by
  linarith [G.inner_lie_left Y X Z]

/-- The `Ad(G)`-invariant bilinear form on `G.lieSubalgebra` is `ad`-invariant in the sense of
`LinearMap.BilinForm.lieInvariant`. -/
theorem bilinForm_lieInvariant : G.bilinForm.lieInvariant G.lieSubalgebra := by
  intro X Y Z
  have h := G.inner_lie_left (LieAlgebra.ofSubalgebra X) (LieAlgebra.ofSubalgebra Y)
    (LieAlgebra.ofSubalgebra Z)
  simp only [LieAlgebra.inner_eq_bilinForm] at h
  exact h

/-- The operator `ad(X)` on `G.LieAlgebra` is skew-adjoint: `(ad X)† = -ad X`. -/
theorem adjoint_ad (X : G.LieAlgebra) :
    LinearMap.adjoint (_root_.LieAlgebra.ad ℝ G.LieAlgebra X) =
      -(_root_.LieAlgebra.ad ℝ G.LieAlgebra X) := by
  apply LinearMap.ext
  intro Y
  apply ext_inner_right ℝ
  intro Z
  rw [LinearMap.adjoint_inner_left, LinearMap.neg_apply, inner_neg_left,
    _root_.LieAlgebra.ad_apply, _root_.LieAlgebra.ad_apply, G.inner_lie_right]

/-! ### Tangent spaces `g · 𝔤 = 𝔤 · g` -/

/-- The tangent space `g · 𝔤` of `G` at `g ∈ G`, viewed as a real subspace of `Matrix n n ℂ`. -/
def tangentSpace (g : G.subgroup) : Submodule ℝ (Matrix n n ℂ) :=
  G.lieSubalgebra.toSubmodule.map (LinearMap.mulLeft ℝ (g.1 : Matrix n n ℂ))

/-- The left and right translates of the Lie algebra coincide at every `g ∈ G`: `g · 𝔤 = 𝔤 · g`. -/
theorem tangentSpace_eq_mulRight (g : G.subgroup) :
    G.tangentSpace g =
      G.lieSubalgebra.toSubmodule.map (LinearMap.mulRight ℝ (g.1 : Matrix n n ℂ)) := by
  let _ : NormedRing (Matrix n n ℂ) := Matrix.linftyOpNormedRing
  let _ : NormedAlgebra ℝ (Matrix n n ℂ) := Matrix.linftyOpNormedAlgebra
  have hg : Unitary.toUnits g.1 ∈ toGLSubgroup G.subgroup := toUnits_mem_toGLSubgroup_iff.2 g.2
  change (TauCeti.Lie.unitsLieSubalgebra (toGLSubgroup G.subgroup)).toSubmodule.map
      (LinearMap.mulLeft ℝ (g.1 : Matrix n n ℂ)) =
    (TauCeti.Lie.unitsLieSubalgebra (toGLSubgroup G.subgroup)).toSubmodule.map
      (LinearMap.mulRight ℝ (g.1 : Matrix n n ℂ))
  simpa only [Unitary.val_toUnits_apply] using
    TauCeti.Lie.map_mulLeft_unitsLieSubalgebra_eq_map_mulRight (Subgroup.le_normalizer hg)

theorem mem_tangentSpace_iff_mulLeft (g : G.subgroup) (V : Matrix n n ℂ) :
    V ∈ G.tangentSpace g ↔ ∃ X ∈ G.lieSubalgebra, (g.1 : Matrix n n ℂ) * X = V := by
  simp [tangentSpace]

theorem mem_tangentSpace_iff_mulRight (g : G.subgroup) (V : Matrix n n ℂ) :
    V ∈ G.tangentSpace g ↔ ∃ X ∈ G.lieSubalgebra, X * (g.1 : Matrix n n ℂ) = V := by
  rw [G.tangentSpace_eq_mulRight g]
  simp

theorem mem_tangentSpace_iff_conjTranspose_mul (g : G.subgroup) (V : Matrix n n ℂ) :
    V ∈ G.tangentSpace g ↔ (g.1 : Matrix n n ℂ)ᴴ * V ∈ G.lieSubalgebra := by
  rw [mem_tangentSpace_iff_mulLeft]
  have h1 : (g.1 : Matrix n n ℂ)ᴴ * (g.1 : Matrix n n ℂ) = 1 := by
    simpa only [Matrix.star_eq_conjTranspose] using Matrix.mem_unitaryGroup_iff'.1 g.1.2
  have h2 : (g.1 : Matrix n n ℂ) * (g.1 : Matrix n n ℂ)ᴴ = 1 := by
    simpa only [Matrix.star_eq_conjTranspose] using Matrix.mem_unitaryGroup_iff.1 g.1.2
  constructor
  · rintro ⟨X, hX, rfl⟩
    simpa only [← mul_assoc, h1, one_mul] using hX
  · intro hV
    exact ⟨(g.1 : Matrix n n ℂ)ᴴ * V, hV, by rw [← mul_assoc, h2, one_mul]⟩

theorem mem_tangentSpace_iff_mul_conjTranspose (g : G.subgroup) (V : Matrix n n ℂ) :
    V ∈ G.tangentSpace g ↔ V * (g.1 : Matrix n n ℂ)ᴴ ∈ G.lieSubalgebra := by
  rw [mem_tangentSpace_iff_mulRight]
  have h1 : (g.1 : Matrix n n ℂ)ᴴ * (g.1 : Matrix n n ℂ) = 1 := by
    simpa only [Matrix.star_eq_conjTranspose] using Matrix.mem_unitaryGroup_iff'.1 g.1.2
  have h2 : (g.1 : Matrix n n ℂ) * (g.1 : Matrix n n ℂ)ᴴ = 1 := by
    simpa only [Matrix.star_eq_conjTranspose] using Matrix.mem_unitaryGroup_iff.1 g.1.2
  constructor
  · rintro ⟨X, hX, rfl⟩
    simpa only [mul_assoc, h2, mul_one] using hX
  · intro hV
    exact ⟨V * (g.1 : Matrix n n ℂ)ᴴ, hV, by rw [mul_assoc, h1, mul_one]⟩

@[simp]
theorem tangentSpace_one : G.tangentSpace 1 = G.lieSubalgebra.toSubmodule := by
  ext V
  simp [mem_tangentSpace_iff_mulLeft]

end Basic

/-! ### Embedded Lie subgroup structure and differential of the matrix inclusion -/

section EmbeddedLieSubgroup

open scoped Matrix.Norms.Operator

attribute [local instance] Matrix.linftyOpTopologicalSpace

variable {n : Type u} [Fintype n] [DecidableEq n] (G : StructureGroup n)

/-- The image of `G.subgroup` in `GL n ℂ` is closed. -/
theorem isClosed_toGLSubgroup :
    IsClosed ((toGLSubgroup G.subgroup : Subgroup (GL n ℂ)) : Set (GL n ℂ)) :=
  (isClosed_toGLSubgroup_iff G.subgroup).2 G.isClosed

/-- By the closed-subgroup theorem, `toGLSubgroup G.subgroup` is an embedded Lie subgroup of
`GL n ℂ`. -/
theorem isEmbeddedLieSubgroup_toGLSubgroup :
    TauCeti.Lie.IsEmbeddedLieSubgroup (I := 𝓘(ℝ, Matrix n n ℂ)) (toGLSubgroup G.subgroup) :=
  TauCeti.Lie.isEmbeddedLieSubgroup_of_isClosed G.isClosed_toGLSubgroup

/-- Canonical embedded Lie subgroup data for `toGLSubgroup G.subgroup ≤ GL n ℂ`. -/
def embeddedLieSubgroupData :
    TauCeti.Lie.EmbeddedLieSubgroupData 𝓘(ℝ, Matrix n n ℂ) (toGLSubgroup G.subgroup)
      (TauCeti.Lie.lieSubalgebraOfSubgroup (I := 𝓘(ℝ, Matrix n n ℂ))
        (toGLSubgroup G.subgroup)).toSubmodule :=
  TauCeti.Lie.EmbeddedLieSubgroupData.ofIsClosed (I := 𝓘(ℝ, Matrix n n ℂ)) G.isClosed_toGLSubgroup

/-- The group isomorphism `G.subgroup ≃* toGLSubgroup G.subgroup` induced by `Unitary.toUnits`. -/
def subgroupEquivGL (G : StructureGroup n) : G.subgroup ≃* toGLSubgroup G.subgroup where
  toFun g := ⟨Unitary.toUnits g.1, toUnits_mem_toGLSubgroup_iff.2 g.2⟩
  invFun g :=
    let u : Matrix.unitaryGroup n ℂ := ⟨(g.1 : Matrix n n ℂ),
      TauCeti.mem_unitary_units_iff.1 (toGLSubgroup_le_unitarySubgroup G.subgroup g.2)⟩
    ⟨u, toUnits_mem_toGLSubgroup_iff.1 (by
      have h : Unitary.toUnits u = g.1 := Units.ext rfl
      exact h.symm ▸ g.2)⟩
  left_inv g := Subtype.ext (Subtype.ext rfl)
  right_inv g := Subtype.ext (Units.ext rfl)
  map_mul' _ _ := Subtype.ext (map_mul Unitary.toUnits _ _)

@[simp]
theorem subgroupEquivGL_val (g : G.subgroup) :
    ((G.subgroupEquivGL g : GL n ℂ) : Matrix n n ℂ) = (g.1 : Matrix n n ℂ) :=
  (rfl)

/-- At any `g ∈ G`, the range of the differential of the matrix inclusion `G → Matrix n n ℂ`
is the left translate `g · 𝔤 = G.tangentSpace g`. -/
theorem range_mvfderiv_matrixInclusion (g : G.subgroup) :
    let E := (TauCeti.Lie.lieSubalgebraOfSubgroup (I := 𝓘(ℝ, Matrix n n ℂ))
      (toGLSubgroup G.subgroup)).toSubmodule
    let _ : ChartedSpace E (toGLSubgroup G.subgroup) := G.embeddedLieSubgroupData.chartedSpace
    (mvfderiv 𝓘(ℝ, E) (fun k : toGLSubgroup G.subgroup ↦ ((k : GL n ℂ) : Matrix n n ℂ))
      (G.subgroupEquivGL g)).range = G.tangentSpace g := by
  exact G.embeddedLieSubgroupData.range_mvfderiv_unitsVal_subtypeVal (G.subgroupEquivGL g)

/-- At any `g ∈ G`, the range of the differential of the matrix inclusion `G → Matrix n n ℂ`
is also the right translate `𝔤 · g`. -/
theorem range_mvfderiv_matrixInclusion_eq_mulRight (g : G.subgroup) :
    let E := (TauCeti.Lie.lieSubalgebraOfSubgroup (I := 𝓘(ℝ, Matrix n n ℂ))
      (toGLSubgroup G.subgroup)).toSubmodule
    let _ : ChartedSpace E (toGLSubgroup G.subgroup) := G.embeddedLieSubgroupData.chartedSpace
    (mvfderiv 𝓘(ℝ, E) (fun k : toGLSubgroup G.subgroup ↦ ((k : GL n ℂ) : Matrix n n ℂ))
      (G.subgroupEquivGL g)).range =
      G.lieSubalgebra.toSubmodule.map (LinearMap.mulRight ℝ (g.1 : Matrix n n ℂ)) := by
  exact G.embeddedLieSubgroupData.range_mvfderiv_unitsVal_subtypeVal_eq_mulRight
    (G.subgroupEquivGL g)

end EmbeddedLieSubgroup

end StructureGroup

end TauCeti.YangMills
