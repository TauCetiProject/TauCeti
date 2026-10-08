/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.ProjectiveGeneralLinear.Conjugation
public import TauCeti.Algebra.AlgebraicGroup.SpecialLinear.Projective

/-!
# Conjugation from the special linear group to the projective general linear group

Construct the coordinate morphism of `SLₙ → PGLₙ` by restricting the general linear
conjugation morphism. In coordinates, it sends the generic matrix of `PGLₙ ⊆ GL_{n²}` to
the conjugation matrix of the generic matrix of `SLₙ` and its inverse. Over every commutative
value algebra it sends a determinant-one matrix to its inner automorphism of the matrix
algebra. Over a field, for positive `n`, its
scheme-theoretic kernel is the represented centre of `SLₙ`, hence `μₙ`. This identifies
the whole kernel scheme, including its infinitesimal structure when the characteristic
divides `n`.

The morphism is surjective on algebraically closed field-valued points. Its finiteness and the
centrality of its kernel are proved in
`TauCeti.Algebra.AlgebraicGroup.SpecialLinear.CentralIsogeny`; faithful flatness is not asserted.

## References

* J. S. Milne, *Algebraic Groups* (2017), Examples 5.49 and 21.4.

The construction reuses `ProjectiveGeneralLinear.conjugationMap`.
-/

public section

open CategoryTheory WithConv

namespace TauCeti.SpecialLinear

universe u w

noncomputable section

variable (n : ℕ)

/-- The coordinate morphism of `SLₙ → PGLₙ`, given by conjugation on the matrix algebra. -/
def conjugationMap (R : Type u) [CommRing R] :
    ProjectiveGeneralLinear.coordinateHopfAlgebra n R ⟶ coordinateHopfAlgebra R n :=
  ProjectiveGeneralLinear.conjugationMap n R ≫ coordinateMap R n

/-- The special-linear conjugation morphism is the restriction of general-linear conjugation. -/
theorem conjugationMap_def (R : Type u) [CommRing R] :
    conjugationMap n R =
      ProjectiveGeneralLinear.conjugationMap n R ≫ coordinateMap R n := (rfl)

/-- **`SLₙ → PGLₙ` in coordinates**: the conjugation homomorphism sends the generic matrix of
`GL_{n²}`, read in `O(PGLₙ)`, to the conjugation matrix of the generic matrix `X` of `SLₙ`, whose
entry at `((p, q), (i, j))` is `Xₚᵢ (X⁻¹)ⱼq`. -/
theorem map_genericMatrix_conjugationMap (R : Type u) [CommRing R] :
    (GeneralLinear.genericMatrix R (n * n)).map
        (CommHopfAlgCat.mkQuotient _ (ProjectiveGeneralLinear.definingHopfIdeal n R) ≫
          conjugationMap n R).hom =
      ProjectiveGeneralLinear.conjugationMatrix
        ((GeneralLinear.genericMatrix R n).map (coordinateMap R n).hom)
        ((GeneralLinear.genericMatrix R n).map (coordinateMap R n).hom)⁻¹ := by
  have h := congrArg (Matrix.map · (coordinateMap R n).hom)
    (ProjectiveGeneralLinear.map_genericMatrix_conjugationMap n R)
  simp only [Matrix.map_map, ProjectiveGeneralLinear.conjugationMatrix_map] at h
  rw [← (coordinateMap R n).hom.coe_toAlgHom, ← GeneralLinear.map_inv_genericMatrix,
    (coordinateMap R n).hom.coe_toAlgHom, ← h, conjugationMap_def, ← Category.assoc,
    CommHopfAlgCat.hom_comp, BialgHom.coe_comp]

/-- On algebra-valued points, the conjugation morphism sends a special-linear matrix to its
inner automorphism of the matrix algebra. -/
@[simp]
theorem pointsMulEquiv_conjugationMap {R : Type u} [CommRing R]
    (A : CommAlgCat.{w} R)
    (g : HopfAlgebra.points (R := R) (H := coordinateHopfAlgebra R n) A) :
    ProjectiveGeneralLinear.pointsMulEquiv n R A
        (toConv (g.ofConv.comp ((conjugationMap n R).hom :
          ProjectiveGeneralLinear.coordinateHopfAlgebra n R →ₐ[R]
            coordinateHopfAlgebra R n))) =
      Matrix.GeneralLinearGroup.innerAut
        (Matrix.SpecialLinearGroup.toGL (pointsMulEquiv (R := R) (A := A) n g)) := by
  have h := ProjectiveGeneralLinear.pointsMulEquiv_conjugationMap n R A
    (CommHopfAlgCat.quotientPointsHom (GeneralLinear.coordinateHopfAlgebra R n)
      (definingHopfIdeal R n) A g)
  rw [pointsMulEquiv_toGL] at h
  have hq : (CommHopfAlgCat.quotientPointsHom (GeneralLinear.coordinateHopfAlgebra R n)
      (definingHopfIdeal R n) A g).ofConv =
      g.ofConv.comp ((coordinateMap R n).hom : GeneralLinear.coordinateHopfAlgebra R n →ₐ[R]
        coordinateHopfAlgebra R n) := by
    ext x
    exact CommHopfAlgCat.quotientPointsHom_apply_apply _ _ A g x
  rw [hq] at h
  simpa only [conjugationMap_def, CommHopfAlgCat.hom_comp, BialgHom.comp_toAlgHom,
    AlgHom.comp_assoc] using h

/-- The scheme-theoretic kernel on any commutative value algebra consists precisely of the
central special-linear matrices. -/
theorem mem_quotientPointsSubgroup_kernelHopfIdeal_conjugationMap_iff
    {R : Type u} [CommRing R] (A : CommAlgCat.{w} R)
    (g : HopfAlgebra.points (R := R) (H := coordinateHopfAlgebra R n) A) :
    g ∈ CommHopfAlgCat.quotientPointsSubgroup _
        (CommHopfAlgCat.kernelHopfIdeal (conjugationMap n R)) A ↔
      pointsMulEquiv (R := R) (A := A) n g ∈
        Subgroup.center (Matrix.SpecialLinearGroup (Fin n) A) := by
  rw [← CommHopfAlgCat.mapPointsFunctor_app_eq_one_iff,
    ← Matrix.SpecialLinearGroup.toGL_mem_center_iff,
    ← Matrix.GeneralLinearGroup.innerAut_eq_one_iff,
    ← pointsMulEquiv_conjugationMap, MulEquiv.map_eq_one_iff]

/-- Over a field, the kernel of `SLₙ → PGLₙ` is the represented centre of `SLₙ`.
The equality is of defining Hopf ideals, so also detects nonreduced central subgroup schemes. -/
theorem kernelHopfIdeal_conjugationMap {k : Type u} [Field k] (hn : 0 < n) :
    CommHopfAlgCat.kernelHopfIdeal (conjugationMap n k) =
      CommHopfAlgCat.centerDefiningIdeal (coordinateHopfAlgebra k n) := by
  -- Follow the universal-point kernel argument for `ProjectiveGeneralLinear.conjugationMap`.
  have hmem : ∀ (A : CommAlgCat.{u} k)
      (g : HopfAlgebra.points (R := k) (H := coordinateHopfAlgebra k n) A),
      g ∈ CommHopfAlgCat.quotientPointsSubgroup _
          (CommHopfAlgCat.kernelHopfIdeal (conjugationMap n k)) A ↔
        g ∈ CommHopfAlgCat.centerPointsSubgroup _ A := by
    intro A g
    rw [mem_quotientPointsSubgroup_kernelHopfIdeal_conjugationMap_iff,
      ← map_centerPointsSubgroup_pointsMulEquiv_eq_center n hn A]
    exact ⟨fun ⟨g', hg', h⟩ => (pointsMulEquiv (R := k) n).injective h ▸ hg',
      fun hg => Subgroup.mem_map_of_mem _ hg⟩
  apply le_antisymm
  · -- Test the kernel ideal on the generic point of the represented centre, rather than
    -- only on field-valued points, which would lose its infinitesimal structure.
    let A : CommAlgCat.{u} k := CommAlgCat.of k (coordinateHopfAlgebra k n ⧸
      (CommHopfAlgCat.centerDefiningIdeal (coordinateHopfAlgebra k n)).toIdeal)
    let q : HopfAlgebra.points (R := k) (H := coordinateHopfAlgebra k n) A :=
      toConv (Ideal.Quotient.mkₐ k _)
    have hq : q ∈ CommHopfAlgCat.centerPointsSubgroup _ A :=
      (CommHopfAlgCat.mem_quotientPointsSubgroup_iff _ _ A q).mpr fun y hy =>
        Ideal.Quotient.eq_zero_iff_mem.mpr (HopfIdeal.mem_toIdeal.mpr hy)
    intro x hx
    have hx0 := (CommHopfAlgCat.mem_quotientPointsSubgroup_iff _ _ A q).mp
      ((hmem A q).mpr hq) x hx
    exact HopfIdeal.mem_toIdeal.mp (Ideal.Quotient.eq_zero_iff_mem.mp hx0)
  · rw [CommHopfAlgCat.centerDefiningIdeal_le_iff,
      CommHopfAlgCat.isCentral_iff_forall_isCentralPoint]
    intro A g hg
    exact (CommHopfAlgCat.mem_centerPointsSubgroup_iff _ A g).mp ((hmem A g).mp hg)

/-- Conjugation from `SLₙ` to `PGLₙ` is surjective on algebraically closed field-valued points,
in every characteristic and also in rank zero. -/
theorem mapPointsFunctor_conjugationMap_app_surjective {R : Type u} [CommRing R]
    (K : Type w) [Field K] [IsAlgClosed K] [Algebra R K] :
    Function.Surjective
      ((CommHopfAlgCat.mapPointsFunctor (conjugationMap n R)).app (CommAlgCat.of R K)) := by
  -- Combine Mathlib's `PSL ≃ PGL` equivalence over algebraically closed fields with the
  -- Skolem–Noether identification `Matrix.ProjGenLinGroup.innerAut_bijective`.
  intro q
  obtain ⟨p, hp⟩ := (Matrix.ProjGenLinGroup.innerAut_bijective (n := Fin n) K).2
    (ProjectiveGeneralLinear.pointsMulEquiv n R _ q)
  obtain ⟨s, hs⟩ := (Matrix.ProjectiveSpecialLinearGroup.isoPSLOfAlgClosed
    (n := Fin n) (F := K)).symm.surjective p
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective s
  refine ⟨(pointsMulEquiv (R := R) (A := K) n).symm g,
    (ProjectiveGeneralLinear.pointsMulEquiv n R _).injective ?_⟩
  rw [CommHopfAlgCat.mapPointsFunctor_app_apply,
    pointsMulEquiv_conjugationMap, MulEquiv.apply_symm_apply]
  rw [← Matrix.ProjGenLinGroup.innerAut_mk]
  have hs' : Matrix.ProjectiveSpecialLinearGroup.toPGL (QuotientGroup.mk g) = p := by
    classical
    -- Mathlib constructs both branches of this equivalence from the same inclusion;
    -- expand its branch selection to recover that inclusion, including in rank zero.
    by_cases h : Nonempty (Fin n)
    · simp only [Matrix.ProjectiveSpecialLinearGroup.isoPSLOfAlgClosed, dite_eq_left h,
        Matrix.ProjectiveSpecialLinearGroup.isoPSLOfAlgClosedOfNonempty,
        MulEquiv.symm_symm] at hs
      exact hs
    · simp only [Matrix.ProjectiveSpecialLinearGroup.isoPSLOfAlgClosed, dite_eq_right h,
        MulEquiv.symm_symm] at hs
      exact hs
  exact (congrArg Matrix.ProjGenLinGroup.innerAut hs').trans hp

end

end TauCeti.SpecialLinear
