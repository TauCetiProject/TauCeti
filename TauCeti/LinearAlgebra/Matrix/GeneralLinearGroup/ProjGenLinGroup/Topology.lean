/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
public import Mathlib.Topology.Algebra.Group.Matrix
public import Mathlib.Topology.Algebra.Group.Quotient
public import TauCeti.GroupTheory.Commensurable
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.ProjGenLinGroup.SignDet
public import TauCeti.Topology.Algebra.Group.DiscreteSubgroup
public import TauCeti.Topology.Algebra.Group.Subgroup

/-!
# The quotient topology on the projective general linear group

Mathlib defines `PGL(n, R)` as the quotient of `GL n R` by its centre, as a `def` carrying no
topology. For a topological commutative ring `R` we give it the quotient topology of `GL n R`, the
topology Mathlib puts on the quotient group `GL n R ⧸ Subgroup.center (GL n R)`. It makes
`PGL(n, R)` a topological group and the projection `GL n R → PGL(n, R)` an open quotient map. The
centre of `GL n R` is closed when `R` is Hausdorff, so `PGL(n, R)` is then a regular Hausdorff
space. The map `PSL(n, R) → PGL(n, R)` is continuous, being induced by the inclusion of `SL n R`
in `GL n R`.

Over `ℝ` in even dimension this map is an open embedding: a homeomorphism of `PSL(n, ℝ)` onto the
open subgroup of `PGL(n, ℝ)` of classes of positive determinant, which is the kernel of the sign of
the determinant and has index two (`Matrix.ProjGenLinGroup.ker_signDet`). The inverse is induced by
`g ↦ |det g|^(-1/n) g`, continuous on the matrices of positive determinant. In dimension two this
compares discrete subgroups of the orientation-preserving isometry group `PSL(2, ℝ)` of the
hyperbolic plane with discrete subgroups of the full isometry group `PGL(2, ℝ)`. In particular, for
a subgroup `Γ` of `PSL(n, ℝ)`, if the commensurator of `Γ` in `PSL(n, ℝ)` is discrete, or contains
`Γ` with finite index, then the same holds for the commensurator in `PGL(n, ℝ)` of the image of
`Γ`: the latter meets the image of `PSL(n, ℝ)` in the image of the former
(`Subgroup.Commensurable.map_commensurator`), an open subgroup of index two.

## Main definitions

* `Matrix.ProjGenLinGroup.instTopologicalSpacePGL`: the quotient topology on `PGL(n, R)`.

## Main results

* `Matrix.ProjGenLinGroup.isOpenQuotientMap_mk`: the projection `GL n R → PGL(n, R)` is an open
  quotient map, and `PGL(n, R)` is a topological group, regular Hausdorff when `R` is Hausdorff.
* `Matrix.ProjectiveSpecialLinearGroup.continuous_toPGL`: the map `PSL(n, R) → PGL(n, R)` is
  continuous.
* `Matrix.ProjectiveSpecialLinearGroup.isOpenEmbedding_toPGL`: over `ℝ` in even dimension, the map
  `PSL(n, ℝ) → PGL(n, ℝ)` is an open embedding.
* `Matrix.ProjectiveSpecialLinearGroup.discreteTopology_commensurator_map_toPGL` and
  `Matrix.ProjectiveSpecialLinearGroup.isFiniteRelIndex_commensurator_map_toPGL`: discreteness of
  the commensurator, and finite index in it, pass from a subgroup of `PSL(n, ℝ)` to its image in
  `PGL(n, ℝ)`.

## References

* S. Katok, *Fuchsian Groups*, University of Chicago Press, 1992, Chapter 1.
* J. Voight, *Quaternion Algebras*, Graduate Texts in Mathematics 288, Springer, 2021, §33.
-/

public section

open scoped MatrixGroups
open Topology Subgroup.Commensurable

namespace Matrix.ProjGenLinGroup

variable {n R : Type*} [Fintype n] [DecidableEq n] [CommRing R] [TopologicalSpace R]

/-- The quotient topology of `GL n R` on `PGL(n, R)`, the topology of the quotient group
`GL n R ⧸ Subgroup.center (GL n R)`. -/
instance instTopologicalSpacePGL : TopologicalSpace PGL(n, R) :=
  inferInstanceAs (TopologicalSpace (GL n R ⧸ Subgroup.center (GL n R)))

/-- The projection `GL n R → PGL(n, R)` is a quotient map. -/
theorem isQuotientMap_mk : IsQuotientMap (mk : GL n R → PGL(n, R)) :=
  QuotientGroup.isQuotientMap_mk _

/-- The projection `GL n R → PGL(n, R)` is continuous. -/
@[continuity, fun_prop]
theorem continuous_mk : Continuous (mk : GL n R → PGL(n, R)) :=
  QuotientGroup.continuous_mk

variable [IsTopologicalRing R]

/-- The projection `GL n R → PGL(n, R)` is an open quotient map. -/
theorem isOpenQuotientMap_mk : IsOpenQuotientMap (mk : GL n R → PGL(n, R)) :=
  QuotientGroup.isOpenQuotientMap_mk

/-- `PGL(n, R)` is a topological group, as the quotient of the topological group `GL n R` by a
normal subgroup. -/
instance : IsTopologicalGroup PGL(n, R) :=
  inferInstanceAs (IsTopologicalGroup (GL n R ⧸ Subgroup.center (GL n R)))

/-- The centre of `GL n R` is closed when `R` is Hausdorff, so the quotient is regular
Hausdorff. -/
instance [T2Space R] : T3Space PGL(n, R) :=
  inferInstanceAs (T3Space (GL n R ⧸ Subgroup.center (GL n R)))

end Matrix.ProjGenLinGroup

namespace Matrix.ProjectiveSpecialLinearGroup

open ProjGenLinGroup

section Continuous

variable {n R : Type*} [Fintype n] [DecidableEq n] [CommRing R] [TopologicalSpace R]
  [IsTopologicalRing R]

/-- The map `PSL(n, R) → PGL(n, R)` induced by the inclusion of `SL n R` in `GL n R` is
continuous. -/
@[continuity, fun_prop]
theorem continuous_toPGL : Continuous (toPGL : ProjectiveSpecialLinearGroup n R → PGL(n, R)) :=
  (QuotientGroup.isQuotientMap_mk _).continuous_iff.mpr <|
    ProjGenLinGroup.continuous_mk.comp SpecialLinearGroup.continuous_toGL

end Continuous

section Real

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The positive scalar `|det g|^(-1/n)`, which rescales `g` to a matrix of determinant `±1`. -/
private noncomputable def normScalar (g : GL n ℝ) : ℝ :=
  (|(g.det : ℝ)| ^ ((Fintype.card n : ℝ)⁻¹))⁻¹

private theorem continuous_normScalar : Continuous (normScalar (n := n)) :=
  ((Units.continuous_val.comp GeneralLinearGroup.continuous_det).abs.rpow_const
    fun _ ↦ Or.inr (by positivity)).inv₀
      fun g ↦ (Real.rpow_pos_of_pos (abs_pos.mpr g.det.ne_zero) _).ne'

private theorem normScalar_pos (g : GL n ℝ) : 0 < normScalar g :=
  inv_pos.mpr (Real.rpow_pos_of_pos (abs_pos.mpr g.det.ne_zero) _)

private theorem normScalar_pow (g : GL n ℝ) :
    normScalar g ^ Fintype.card n = |(g.det : ℝ)|⁻¹ := by
  rcases isEmpty_or_nonempty n with hn | hn
  · simp [normScalar]
  rw [normScalar, inv_pow, Real.rpow_inv_natCast_pow (abs_nonneg _) Fintype.card_ne_zero]

variable [Fact (Even (Fintype.card n))]

/-- Rescaling a representative `s a` of `toPGL s`, with `s` of determinant one and `a` a nonzero
real scalar, gives `s` times a central element of `SL(n, ℝ)`. -/
private theorem exists_mem_center_normScalar_smul (s : SpecialLinearGroup n ℝ) (a : ℝˣ) :
    ∃ z ∈ Subgroup.center (SpecialLinearGroup n ℝ),
      normScalar (SpecialLinearGroup.toGL s * GeneralLinearGroup.scalar n a) •
        ((SpecialLinearGroup.toGL s * GeneralLinearGroup.scalar n a : GL n ℝ) : Matrix n n ℝ) =
        ((s * z : SpecialLinearGroup n ℝ) : Matrix n n ℝ) := by
  rcases isEmpty_or_nonempty n with hn | hn
  · exact ⟨1, Subgroup.one_mem _, Subsingleton.elim _ _⟩
  have hpos : 0 < (a : ℝ) ^ Fintype.card n := (Fact.out : Even _).pow_pos a.ne_zero
  have hdet : ((SpecialLinearGroup.toGL s * GeneralLinearGroup.scalar n a).det : ℝ) =
      (a : ℝ) ^ Fintype.card n := by
    simp
  have hc : normScalar (SpecialLinearGroup.toGL s * GeneralLinearGroup.scalar n a) =
      |(a : ℝ)|⁻¹ := by
    rw [normScalar, hdet, abs_pow, Real.pow_rpow_inv_natCast (abs_nonneg _) Fintype.card_ne_zero]
  -- the rescaled matrix is `s` times the scalar `r = a / |a| = ±1`, central in `SL(n, ℝ)`
  have hr : (|(a : ℝ)|⁻¹ * a) ^ Fintype.card n = 1 := by
    rw [mul_pow, inv_pow, ← abs_pow, abs_of_pos hpos, inv_mul_cancel₀ hpos.ne']
  let z : SpecialLinearGroup n ℝ := ⟨Matrix.scalar n (|(a : ℝ)|⁻¹ * a), by simp [hr]⟩
  have hz : (z : Matrix n n ℝ) = Matrix.scalar n (|(a : ℝ)|⁻¹ * a) := rfl
  refine ⟨z, SpecialLinearGroup.mem_center_iff.mpr ⟨_, hr, rfl⟩, ?_⟩
  rw [hc, SpecialLinearGroup.coe_mul, hz, Units.val_mul, GeneralLinearGroup.coe_scalar,
    SpecialLinearGroup.coe_GL_coe_matrix, Matrix.scalar_apply, Matrix.scalar_apply,
    ← Matrix.smul_one_eq_diagonal, ← Matrix.smul_one_eq_diagonal, Matrix.mul_smul,
    Matrix.mul_smul, Matrix.mul_one, smul_smul]

/-- The classes in `PGL(n, ℝ)` of the elements of a subset `U` of `PSL(n, ℝ)`, read in `GL n ℝ`,
are the matrices of positive determinant whose rescaling to determinant one lies over `U`. Here
`W` is a set of matrices cutting out the preimage of `U` in `SL(n, ℝ)`. -/
private theorem preimage_mk_image_toPGL {U : Set (ProjectiveSpecialLinearGroup n ℝ)}
    {W : Set (Matrix n n ℝ)}
    (hWU : Subtype.val ⁻¹' W = (QuotientGroup.mk ⁻¹' U : Set (SpecialLinearGroup n ℝ))) :
    (mk : GL n ℝ → PGL(n, ℝ)) ⁻¹' (toPGL '' U) =
      {g | 0 < (g.det : ℝ)} ∩ (fun g : GL n ℝ ↦ normScalar g • (g : Matrix n n ℝ)) ⁻¹' W := by
  ext g
  simp only [Set.mem_preimage, Set.mem_image, Set.mem_inter_iff, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨u, hu, hug⟩
    obtain ⟨s, rfl⟩ := QuotientGroup.mk_surjective u
    obtain ⟨a, rfl⟩ := mk_eq_mk_iff.mp hug
    obtain ⟨z, hz, heq⟩ := exists_mem_center_normScalar_smul s a
    refine ⟨by simpa using (Fact.out : Even (Fintype.card n)).pow_pos a.ne_zero, ?_⟩
    have hsz : (QuotientGroup.mk (s * z) : ProjectiveSpecialLinearGroup n ℝ) ∈ U := by
      rwa [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff z).mpr hz, mul_one]
    have hsz' : s * z ∈ (Subtype.val ⁻¹' W : Set (SpecialLinearGroup n ℝ)) := hWU ▸ hsz
    rwa [heq]
  · rintro ⟨hg, hgW⟩
    have hdet : (normScalar g • (g : Matrix n n ℝ)).det = 1 := by
      rw [Matrix.det_smul, normScalar_pow, ← GeneralLinearGroup.val_det_apply, abs_of_pos hg,
        inv_mul_cancel₀ hg.ne']
    let s : SpecialLinearGroup n ℝ := ⟨_, hdet⟩
    have hs : s ∈ (QuotientGroup.mk ⁻¹' U : Set (SpecialLinearGroup n ℝ)) := hWU ▸ hgW
    refine ⟨s, hs, (mk_eq_mk_iff.mpr ⟨Units.mk0 _ (normScalar_pos g).ne', ?_⟩).symm⟩
    ext : 1
    rw [Units.val_mul, GeneralLinearGroup.coe_scalar, Units.val_mk0, Matrix.scalar_apply,
      ← Matrix.smul_one_eq_diagonal, Matrix.mul_smul, Matrix.mul_one]
    exact (SpecialLinearGroup.coe_GL_coe_matrix s).symm

/-- Over `ℝ` in even dimension, the map `PSL(n, ℝ) → PGL(n, ℝ)` is open. -/
theorem isOpenMap_toPGL : IsOpenMap (toPGL : ProjectiveSpecialLinearGroup n ℝ → PGL(n, ℝ)) := by
  intro U hU
  obtain ⟨W, hW, hWU⟩ := isOpen_induced_iff.mp (hU.preimage QuotientGroup.continuous_mk)
  rw [← isQuotientMap_mk.isOpen_preimage, preimage_mk_image_toPGL hWU]
  exact (isOpen_lt continuous_const
    (Units.continuous_val.comp GeneralLinearGroup.continuous_det)).inter
      (hW.preimage (continuous_normScalar.smul Units.continuous_val))

/-- Over `ℝ` in even dimension, the map `PSL(n, ℝ) → PGL(n, ℝ)` is an open embedding: a
homeomorphism onto the open subgroup of classes of positive determinant
(`Matrix.ProjGenLinGroup.ker_signDet`). -/
theorem isOpenEmbedding_toPGL :
    IsOpenEmbedding (toPGL : ProjectiveSpecialLinearGroup n ℝ → PGL(n, ℝ)) :=
  .of_continuous_injective_isOpenMap continuous_toPGL toPGL_injective isOpenMap_toPGL

/-- If the commensurator of a subgroup `Γ` of `PSL(n, ℝ)` is discrete, then so is the
commensurator in `PGL(n, ℝ)` of the image of `Γ`. -/
theorem discreteTopology_commensurator_map_toPGL {Γ : Subgroup (ProjectiveSpecialLinearGroup n ℝ)}
    [DiscreteTopology (commensurator Γ)] :
    DiscreteTopology (commensurator (Γ.map toPGL)) := by
  have : DiscreteTopology ((commensurator (Γ.map toPGL)).comap toPGL) := by
    rwa [comap_commensurator_map toPGL_injective]
  exact Subgroup.discreteTopology_of_comap isOpenEmbedding_toPGL

/-- If a subgroup `Γ` of `PSL(n, ℝ)` has finite index in its commensurator, then its image in
`PGL(n, ℝ)` has finite index in its commensurator there. -/
theorem isFiniteRelIndex_commensurator_map_toPGL {Γ : Subgroup (ProjectiveSpecialLinearGroup n ℝ)}
    (hΓ : Γ.IsFiniteRelIndex (commensurator Γ)) :
    (Γ.map toPGL).IsFiniteRelIndex (commensurator (Γ.map toPGL)) :=
  isFiniteRelIndex_commensurator_map toPGL_injective hΓ

end Real

end Matrix.ProjectiveSpecialLinearGroup
