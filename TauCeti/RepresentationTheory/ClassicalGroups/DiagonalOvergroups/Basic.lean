/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Group.Matrix
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.ProjGenLinGroup.Center
public import TauCeti.Topology.Algebra.Group.Goursat

/-!
# Diagonal overgroups of the general linear group: algebraic and Goursat structure

Inside the direct product `GL ι R × GL ι R` of two copies of the general linear group sit four
distinguished subgroups containing the diagonal copy `Δ = {(g, g)}`:

1. `TauCeti.DiagonalOvergroups.diagonal`: the diagonal subgroup `Δ = {(g, g)}`;
2. `TauCeti.DiagonalOvergroups.scalarDiagonal`: the scalar-extended diagonal
   `{(scalar ι u * g, g)}`, consisting of pairs `(g, h)` with the same projective class in
   `PGL(ι, R)`, equivalently `g / h ∈ Subgroup.center (GL ι R)`;
3. `TauCeti.DiagonalOvergroups.determinantEqual`: the equal-determinant subgroup
   `{(g, h) | g.det = h.det}`, kernel of `TauCeti.DiagonalOvergroups.determinantRatio`, with
   `g / h ∈ SpecialLinearGroup.toGL.range`;
4. `⊤`: the full product `GL ι R × GL ι R`.

Through `TauCeti/GroupTheory/Goursat.lean`, these four subgroups correspond to the four canonical
normal subgroups `⊥`, `Subgroup.center (GL ι R)`, `SpecialLinearGroup.toGL.range`, and `⊤` of
`GL ι R`. This file develops their membership characterizations, quotient and product
isomorphisms, topological splitting of `scalarDiagonal`, and normalizers:

* `normalizer_diagonal`: `N_{GL × GL}(diagonal ι R) = scalarDiagonal ι R` over any commutative
  ring; for `|ι| ≥ 2` over a nontrivial ring, `diagonal ι R` is not normal;
* `normalizer_scalarDiagonal`: `scalarDiagonal ι R` is self-normalizing over any integral domain
  (via `Matrix.ProjGenLinGroup.center_eq_bot`).

## Main definitions

* `TauCeti.DiagonalOvergroups.diagonalMap`, `TauCeti.DiagonalOvergroups.diagonal`,
  `TauCeti.DiagonalOvergroups.diagonalEquiv`: the diagonal embedding, subgroup, and isomorphism
  `GL ι R ≃* diagonal ι R`.
* `TauCeti.DiagonalOvergroups.determinantRatio`, `TauCeti.DiagonalOvergroups.determinantEqual`:
  the ratio `(g, h) ↦ g.det / h.det` and its kernel.
* `TauCeti.DiagonalOvergroups.scalarDiagonalMap`, `TauCeti.DiagonalOvergroups.scalarDiagonal`,
  `TauCeti.DiagonalOvergroups.sndProj`, `TauCeti.DiagonalOvergroups.scalarProj`:
  the parameterization `(g, u) ↦ (scalar ι u * g, g)`, its image, and its projections.
* `TauCeti.DiagonalOvergroups.scalarDiagonalEquiv`,
  `TauCeti.DiagonalOvergroups.scalarDiagonalContinuousMulEquiv`: the isomorphism
  `GL ι R × Rˣ ≃* scalarDiagonal ι R` (and topological group isomorphism) for nonempty `ι`.
* `TauCeti.DiagonalOvergroups.quotientDeterminantEqualEquiv`,
  `TauCeti.DiagonalOvergroups.quotientDiagonalOfScalarDiagonalEquiv`: quotient isomorphisms onto
  `Rˣ` for nonempty `ι`.

## References

* Jean Dieudonné, *La géométrie des groupes classiques*, 3rd edition, Springer, 1971, Chapter I.
* Serge Lang, *Algebra*, revised third edition, Springer GTM 211, 2002, Chapter I, §9, Exercise 5.
-/

public section

open Matrix
open scoped MatrixGroups

namespace TauCeti.DiagonalOvergroups

section CommRing

variable (ι R : Type*) [Fintype ι] [DecidableEq ι] [CommRing R]

/-- The diagonal embedding `g ↦ (g, g)` of `GL ι R` into `GL ι R × GL ι R`. -/
def diagonalMap : GL ι R →* GL ι R × GL ι R :=
  (MonoidHom.id (GL ι R)).prod (MonoidHom.id (GL ι R))

/-- **The diagonal subgroup** `{(g, g) | g : GL ι R}` inside `GL ι R × GL ι R`. -/
def diagonal : Subgroup (GL ι R × GL ι R) :=
  (diagonalMap ι R).range

/-- **The determinant-ratio homomorphism** `(g, h) ↦ g.det / h.det` from `GL ι R × GL ι R` to
`Rˣ`. -/
def determinantRatio : GL ι R × GL ι R →* Rˣ where
  toFun p := p.1.det / p.2.det
  map_one' := by simp
  map_mul' p q := by simp [div_mul_div_comm]

/-- **The equal-determinant subgroup** `{(g, h) | g.det = h.det}` inside `GL ι R × GL ι R`, defined
as the kernel of `determinantRatio`. -/
def determinantEqual : Subgroup (GL ι R × GL ι R) :=
  (determinantRatio ι R).ker

/-- The parameterization `(g, u) ↦ (scalar ι u * g, g)` of `scalarDiagonal` by `GL ι R × Rˣ`. -/
def scalarDiagonalMap : GL ι R × Rˣ →* GL ι R × GL ι R where
  toFun p := (GeneralLinearGroup.scalar ι p.2 * p.1, p.1)
  map_one' := by simp
  map_mul' p q := Prod.ext (by
    simp only [Prod.fst_mul, Prod.snd_mul, map_mul, mul_assoc]
    rw [← mul_assoc p.1, ← GeneralLinearGroup.scalar_commute q.2 p.1, mul_assoc]) rfl

/-- **The scalar-diagonal subgroup** `{(scalar ι u * g, g) | g : GL ι R, u : Rˣ}` inside
`GL ι R × GL ι R`. -/
def scalarDiagonal : Subgroup (GL ι R × GL ι R) :=
  (scalarDiagonalMap ι R).range

variable {ι R}

@[simp]
theorem diagonalMap_apply (g : GL ι R) : diagonalMap ι R g = (g, g) :=
  (rfl)

theorem diagonal_eq_graph_id : diagonal ι R = (MonoidHom.id (GL ι R)).graph :=
  (MonoidHom.graph_eq_range_prod (MonoidHom.id (GL ι R))).symm

@[simp]
theorem mem_diagonal_iff {p : GL ι R × GL ι R} : p ∈ diagonal ι R ↔ p.1 = p.2 := by
  rw [diagonal_eq_graph_id, MonoidHom.mem_graph, MonoidHom.id_apply]

@[simp]
theorem determinantRatio_apply (p : GL ι R × GL ι R) :
    determinantRatio ι R p = p.1.det / p.2.det :=
  (rfl)

@[simp]
theorem mem_determinantEqual_iff {p : GL ι R × GL ι R} :
    p ∈ determinantEqual ι R ↔ p.1.det = p.2.det := by
  simp [determinantEqual, MonoidHom.mem_ker, div_eq_one]

instance instNormalDeterminantEqual : (determinantEqual ι R).Normal :=
  MonoidHom.normal_ker (determinantRatio ι R)

@[simp]
theorem scalarDiagonalMap_apply (p : GL ι R × Rˣ) :
    scalarDiagonalMap ι R p = (GeneralLinearGroup.scalar ι p.2 * p.1, p.1) :=
  (rfl)

@[simp]
theorem mem_scalarDiagonal_iff {p : GL ι R × GL ι R} :
    p ∈ scalarDiagonal ι R ↔ ∃ u : Rˣ, p.1 = GeneralLinearGroup.scalar ι u * p.2 := by
  constructor
  · rintro ⟨⟨g, u⟩, rfl⟩
    exact ⟨u, rfl⟩
  · rintro ⟨u, hu⟩
    exact ⟨(p.2, u), Prod.ext hu.symm rfl⟩

/-- Two invertible matrices lie in `scalarDiagonal` precisely when they represent the same element
of `PGL(ι, R)`. -/
theorem mem_scalarDiagonal_iff_mk_eq {p : GL ι R × GL ι R} :
    p ∈ scalarDiagonal ι R ↔ ProjGenLinGroup.mk p.1 = ProjGenLinGroup.mk p.2 := by
  rw [mem_scalarDiagonal_iff, ProjGenLinGroup.mk_eq_mk_iff]
  constructor
  · rintro ⟨u, hu⟩
    refine ⟨u⁻¹, ?_⟩
    rw [hu, GeneralLinearGroup.scalar_commute u p.2, mul_assoc, ← map_mul, mul_inv_cancel,
      map_one, mul_one]
  · rintro ⟨u, hu⟩
    refine ⟨u⁻¹, ?_⟩
    rw [← hu, GeneralLinearGroup.scalar_commute u⁻¹ _, mul_assoc, ← map_mul, mul_inv_cancel,
      map_one, mul_one]

/-- `scalarDiagonal` is the Goursat diagonal extension of `Subgroup.center (GL ι R)`. -/
theorem scalarDiagonal_eq_diagonalExt_center :
    scalarDiagonal ι R = Subgroup.diagonalExt (Subgroup.center (GL ι R)) := by
  ext ⟨g, h⟩
  rw [mem_scalarDiagonal_iff, Subgroup.mem_diagonalExt, GeneralLinearGroup.center_eq_range_scalar]
  constructor
  · rintro ⟨u, hu⟩
    refine ⟨u, ?_⟩
    rw [hu, mul_div_cancel_right]
  · rintro ⟨u, hu⟩
    refine ⟨u, ?_⟩
    rw [hu, div_mul_cancel]

/-- `determinantEqual` is the Goursat diagonal extension of `ker det`. -/
theorem determinantEqual_eq_diagonalExt_ker_det :
    determinantEqual ι R = Subgroup.diagonalExt (GeneralLinearGroup.det (n := ι) (R := R)).ker := by
  ext ⟨g, h⟩
  simp [Subgroup.mem_diagonalExt, MonoidHom.mem_ker, div_eq_one]

/-- The diagonal subgroup lies inside `scalarDiagonal`. -/
theorem diagonal_le_scalarDiagonal : diagonal ι R ≤ scalarDiagonal ι R :=
  fun _ hp => mem_scalarDiagonal_iff.mpr ⟨1, by simp [mem_diagonal_iff.mp hp]⟩

/-- The diagonal subgroup lies inside `determinantEqual`. -/
theorem diagonal_le_determinantEqual : diagonal ι R ≤ determinantEqual ι R :=
  fun _ hp =>
    mem_determinantEqual_iff.mpr (congrArg GeneralLinearGroup.det (mem_diagonal_iff.mp hp))

@[simp]
theorem goursatFst_diagonal : (diagonal ι R).goursatFst = ⊥ := by
  rw [diagonal_eq_graph_id, Subgroup.goursatFst_graph_id]

@[simp]
theorem goursatFst_scalarDiagonal :
    (scalarDiagonal ι R).goursatFst = Subgroup.center (GL ι R) := by
  rw [scalarDiagonal_eq_diagonalExt_center, Subgroup.goursatFst_diagonalExt]

@[simp]
theorem goursatFst_determinantEqual :
    (determinantEqual ι R).goursatFst = (SpecialLinearGroup.toGL (n := ι) (R := R)).range := by
  rw [determinantEqual_eq_diagonalExt_ker_det, Subgroup.goursatFst_diagonalExt,
    SpecialLinearGroup.range_toGL_eq_ker_det]

/-! ### Normalizers -/

/-- **The normalizer of the diagonal subgroup in `GL ι R × GL ι R` is `scalarDiagonal ι R`.** -/
@[simp]
theorem normalizer_diagonal :
    Subgroup.normalizer (diagonal ι R : Set (GL ι R × GL ι R)) = scalarDiagonal ι R := by
  rw [diagonal_eq_graph_id, Subgroup.normalizer_graph_id, scalarDiagonal_eq_diagonalExt_center]

/-- The diagonal subgroup is normal inside `scalarDiagonal`. -/
instance instNormalDiagonalSubgroupOfScalarDiagonal :
    ((diagonal ι R).subgroupOf (scalarDiagonal ι R)).Normal := by
  rw [Subgroup.normal_subgroupOf_iff_le_normalizer diagonal_le_scalarDiagonal, normalizer_diagonal]

/-- When `|ι| ≥ 2` over a nontrivial ring, `scalarDiagonal ι R` is a proper subgroup of
`GL ι R × GL ι R`: an elementary transvection in the first factor is not scalar. -/
theorem scalarDiagonal_ne_top [Nontrivial ι] [Nontrivial R] : scalarDiagonal ι R ≠ ⊤ := by
  obtain ⟨i, j, hij⟩ := exists_pair_ne ι
  intro htop
  have hmem : (SpecialLinearGroup.toGL (SpecialLinearGroup.transvection hij (1 : R)), (1 : GL ι R))
      ∈ scalarDiagonal ι R := htop ▸ Subgroup.mem_top _
  obtain ⟨u, hu⟩ := mem_scalarDiagonal_iff.mp hmem
  have hij_eq := congrArg (fun M : Matrix ι ι R => M i j) (congrArg Units.val hu)
  simp [SpecialLinearGroup.coe_GL_coe_matrix, SpecialLinearGroup.transvection_coe,
    GeneralLinearGroup.coe_scalar, hij] at hij_eq

/-- **The diagonal subgroup is not normal in `GL ι R × GL ι R`** when `|ι| ≥ 2` and `R` is
nontrivial. -/
theorem not_normal_diagonal [Nontrivial ι] [Nontrivial R] : ¬ (diagonal ι R).Normal := by
  intro hN
  have htop := @Subgroup.normalizer_eq_top _ _ (diagonal ι R) hN
  rw [normalizer_diagonal] at htop
  exact scalarDiagonal_ne_top htop

/-- **Over an integral domain, `scalarDiagonal ι R` is self-normalizing in `GL ι R × GL ι R`.** -/
@[simp]
theorem normalizer_scalarDiagonal [IsDomain R] :
    Subgroup.normalizer (scalarDiagonal ι R : Set (GL ι R × GL ι R)) = scalarDiagonal ι R := by
  rw [scalarDiagonal_eq_diagonalExt_center]
  refine Subgroup.normalizer_diagonalExt_center_of_center_quotient_eq_bot ?_
  change Subgroup.center PGL(ι, R) = ⊥
  exact ProjGenLinGroup.center_eq_bot

/-! ### Splitting of `scalarDiagonal` and quotient isomorphisms -/

/-- In rank zero, `GL ι R × GL ι R` is trivial, so `scalarDiagonalMap` has full kernel. -/
@[simp]
theorem ker_scalarDiagonalMap_of_isEmpty [IsEmpty ι] :
    (scalarDiagonalMap ι R).ker = ⊤ := by
  ext p
  exact iff_of_true (Subsingleton.elim _ _) trivial

/-- For nonempty `ι`, reading a diagonal entry of a scalar matrix recovers its unit scalar. -/
private def unitOfCenter (i₀ : ι) (z : Subgroup.center (GL ι R)) : Rˣ where
  val := (z.1 : Matrix ι ι R) i₀ i₀
  inv := ((z.1⁻¹ : GL ι R) : Matrix ι ι R) i₀ i₀
  val_inv := by
    obtain ⟨u, hu⟩ := GeneralLinearGroup.center_eq_range_scalar.le z.2
    have hu' : (z.1 : Matrix ι ι R) = Matrix.scalar ι (u : R) := by
      rw [← hu, GeneralLinearGroup.coe_scalar]
    have hinv : ((z.1⁻¹ : GL ι R) : Matrix ι ι R) = Matrix.scalar ι ((u⁻¹ : Rˣ) : R) := by
      rw [← hu, ← map_inv, GeneralLinearGroup.coe_scalar]
    rw [hu', hinv]
    simp
  inv_val := by
    obtain ⟨u, hu⟩ := GeneralLinearGroup.center_eq_range_scalar.le z.2
    have hu' : (z.1 : Matrix ι ι R) = Matrix.scalar ι (u : R) := by
      rw [← hu, GeneralLinearGroup.coe_scalar]
    have hinv : ((z.1⁻¹ : GL ι R) : Matrix ι ι R) = Matrix.scalar ι ((u⁻¹ : Rˣ) : R) := by
      rw [← hu, ← map_inv, GeneralLinearGroup.coe_scalar]
    rw [hu', hinv]
    simp

private theorem unitOfCenter_scalar (i₀ : ι) (u : Rˣ) :
    unitOfCenter i₀ ⟨GeneralLinearGroup.scalar ι u,
      GeneralLinearGroup.center_eq_range_scalar.ge ⟨u, rfl⟩⟩ = u :=
  Units.ext (by simp [unitOfCenter, GeneralLinearGroup.coe_scalar])

private theorem scalar_unitOfCenter (i₀ : ι) (z : Subgroup.center (GL ι R)) :
    GeneralLinearGroup.scalar ι (unitOfCenter i₀ z) = z.1 := by
  obtain ⟨u, hu⟩ := GeneralLinearGroup.center_eq_range_scalar.le z.2
  have hz : z = ⟨GeneralLinearGroup.scalar ι u,
      GeneralLinearGroup.center_eq_range_scalar.ge ⟨u, rfl⟩⟩ := Subtype.ext hu.symm
  rw [hz, unitOfCenter_scalar]

/-- For nonempty `ι`, `scalarDiagonalMap ι R` is injective. -/
theorem scalarDiagonalMap_injective [Nonempty ι] :
    Function.Injective (scalarDiagonalMap ι R) := by
  obtain ⟨i₀⟩ := ‹Nonempty ι›
  intro ⟨g₁, u₁⟩ ⟨g₂, u₂⟩ h
  simp only [scalarDiagonalMap_apply] at h
  obtain ⟨h1, rfl⟩ := Prod.ext_iff.mp h
  have hsc : GeneralLinearGroup.scalar ι u₁ = GeneralLinearGroup.scalar ι u₂ :=
    mul_right_cancel h1
  have hu : u₁ = u₂ := Units.ext <| by
    simpa [GeneralLinearGroup.coe_scalar] using
      congrArg (fun M : Matrix ι ι R => M i₀ i₀) (congrArg Units.val hsc)
  rw [hu]

/-- **Isomorphism `GL ι R ≃* diagonal ι R`** sending `g` to `(g, g)`. -/
def diagonalEquiv : GL ι R ≃* diagonal ι R where
  toFun g := ⟨(g, g), mem_diagonal_iff.mpr rfl⟩
  invFun p := p.1.1
  left_inv _ := rfl
  right_inv p := Subtype.ext (Prod.ext rfl (mem_diagonal_iff.mp p.2))
  map_mul' _ _ := rfl

@[simp]
theorem coe_diagonalEquiv_apply (g : GL ι R) :
    (diagonalEquiv g : GL ι R × GL ι R) = (g, g) :=
  (rfl)

@[simp]
theorem diagonalEquiv_symm_apply (p : diagonal ι R) :
    diagonalEquiv.symm p = p.1.1 :=
  (rfl)

/-- **Isomorphism `GL ι R × Rˣ ≃* scalarDiagonal ι R`** for nonempty `ι`, sending `(g, u)` to
`(scalar ι u * g, g)`. -/
noncomputable def scalarDiagonalEquiv [Nonempty ι] :
    GL ι R × Rˣ ≃* scalarDiagonal ι R where
  toFun p := (scalarDiagonalMap ι R).rangeRestrict p
  invFun q := (q.1.2, unitOfCenter (Classical.arbitrary ι)
    ⟨q.1.1 / q.1.2,
      Subgroup.mem_diagonalExt.mp (scalarDiagonal_eq_diagonalExt_center (ι := ι) (R := R) ▸ q.2)⟩)
  left_inv p := Prod.ext rfl <| by
    simp only [MonoidHom.coe_rangeRestrict, scalarDiagonalMap_apply, mul_div_cancel_right]
    exact unitOfCenter_scalar _ p.2
  right_inv q := Subtype.ext <| Prod.ext
    (by
      rw [MonoidHom.coe_rangeRestrict, scalarDiagonalMap_apply, scalar_unitOfCenter,
        div_mul_cancel])
    rfl
  map_mul' := map_mul _

@[simp]
theorem coe_scalarDiagonalEquiv_apply [Nonempty ι] (p : GL ι R × Rˣ) :
    (scalarDiagonalEquiv p : GL ι R × GL ι R) = (GeneralLinearGroup.scalar ι p.2 * p.1, p.1) :=
  (rfl)

@[simp]
theorem fst_scalarDiagonalEquiv_symm [Nonempty ι] (q : scalarDiagonal ι R) :
    (scalarDiagonalEquiv.symm q).1 = q.1.2 :=
  (rfl)

@[simp]
theorem scalar_snd_scalarDiagonalEquiv_symm [Nonempty ι] (q : scalarDiagonal ι R) :
    GeneralLinearGroup.scalar ι (scalarDiagonalEquiv.symm q).2 = q.1.1 / q.1.2 :=
  scalar_unitOfCenter _ _

/-- For nonempty `ι`, `determinantRatio ι R` is surjective onto `Rˣ`. -/
theorem determinantRatio_surjective [Nonempty ι] :
    Function.Surjective (determinantRatio ι R) := by
  intro u
  obtain ⟨g, hg⟩ := GeneralLinearGroup.det_surjective (n := ι) u
  exact ⟨(g, 1), by simp [hg]⟩

/-- **First-isomorphism identification `(GL ι R × GL ι R) ⧸ determinantEqual ι R ≃* Rˣ`** for
nonempty `ι`. -/
noncomputable def quotientDeterminantEqualEquiv [Nonempty ι] :
    (GL ι R × GL ι R) ⧸ determinantEqual ι R ≃* Rˣ :=
  QuotientGroup.quotientKerEquivOfSurjective (determinantRatio ι R) determinantRatio_surjective

@[simp]
theorem quotientDeterminantEqualEquiv_mk [Nonempty ι] (p : GL ι R × GL ι R) :
    quotientDeterminantEqualEquiv (QuotientGroup.mk p) = p.1.det / p.2.det :=
  (rfl)

/-- The second-coordinate projection `scalarDiagonal ι R →* GL ι R` sending `(scalar ι u * g, g)`
to `g`. -/
def sndProj : scalarDiagonal ι R →* GL ι R :=
  (MonoidHom.snd (GL ι R) (GL ι R)).comp (scalarDiagonal ι R).subtype

@[simp]
theorem sndProj_apply (q : scalarDiagonal ι R) : sndProj q = q.1.2 :=
  (rfl)

theorem sndProj_surjective : Function.Surjective (sndProj (ι := ι) (R := R)) := fun g =>
  ⟨⟨(g, g), diagonal_le_scalarDiagonal (mem_diagonal_iff.mpr rfl)⟩, rfl⟩

/-- The scalar projection `scalarDiagonal ι R →* Rˣ` sending `(scalar ι u * g, g)` to `u`, for
nonempty `ι`. -/
noncomputable def scalarProj [Nonempty ι] : scalarDiagonal ι R →* Rˣ :=
  (MonoidHom.snd (GL ι R) Rˣ).comp scalarDiagonalEquiv.symm.toMonoidHom

@[simp]
theorem scalarProj_apply_scalarDiagonalEquiv [Nonempty ι] (p : GL ι R × Rˣ) :
    scalarProj (scalarDiagonalEquiv p) = p.2 := by
  change (scalarDiagonalEquiv.symm (scalarDiagonalEquiv p)).2 = p.2
  rw [MulEquiv.symm_apply_apply]

theorem ker_scalarProj [Nonempty ι] :
    (scalarProj (ι := ι) (R := R)).ker = (diagonal ι R).subgroupOf (scalarDiagonal ι R) := by
  ext q
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, mem_diagonal_iff]
  constructor
  · intro h1
    have hsc : GeneralLinearGroup.scalar ι (scalarProj q) = 1 := by rw [h1, map_one]
    rw [scalarProj, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MonoidHom.coe_snd,
      scalar_snd_scalarDiagonalEquiv_symm] at hsc
    exact div_eq_one.mp hsc
  · intro hqq
    obtain ⟨⟨g, u⟩, hgu⟩ := scalarDiagonalEquiv.surjective q
    subst hgu
    have hu1 : GeneralLinearGroup.scalar ι u = 1 := by
      simpa [coe_scalarDiagonalEquiv_apply] using hqq
    rw [scalarProj_apply_scalarDiagonalEquiv]
    exact (Prod.ext_iff.mp (scalarDiagonalMap_injective (ι := ι) (R := R)
      (a₁ := (1, u)) (a₂ := (1, 1)) (by simp [hu1]))).2

theorem scalarProj_surjective [Nonempty ι] :
    Function.Surjective (scalarProj (ι := ι) (R := R)) := fun u =>
  ⟨scalarDiagonalEquiv (1, u), by simp⟩

/-- **Quotient identification `scalarDiagonal ι R ⧸ diagonal ι R ≃* Rˣ`** for nonempty `ι`. -/
noncomputable def quotientDiagonalOfScalarDiagonalEquiv [Nonempty ι] :
    scalarDiagonal ι R ⧸ (diagonal ι R).subgroupOf (scalarDiagonal ι R) ≃* Rˣ :=
  (QuotientGroup.quotientMulEquivOfEq ker_scalarProj.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective scalarProj scalarProj_surjective)

@[simp]
theorem quotientDiagonalOfScalarDiagonalEquiv_mk [Nonempty ι] (q : scalarDiagonal ι R) :
    quotientDiagonalOfScalarDiagonalEquiv (QuotientGroup.mk q) = scalarProj q :=
  (rfl)

end CommRing

section TopologicalRing

variable {ι R : Type*} [Fintype ι] [DecidableEq ι] [CommRing R]
  [TopologicalSpace R] [IsTopologicalRing R]

/-- **Topological group isomorphism `GL ι R × Rˣ ≃ₜ* scalarDiagonal ι R`** for nonempty `ι` over a
topological ring `R`: both the forward multiplication `(g, u) ↦ (scalar ι u * g, g)` and the
diagonal-entry extraction of `u` from `p.1 / p.2` are continuous. -/
noncomputable def scalarDiagonalContinuousMulEquiv [Nonempty ι] :
    GL ι R × Rˣ ≃ₜ* scalarDiagonal ι R where
  toMulEquiv := scalarDiagonalEquiv
  continuous_toFun := by
    have hsc : Continuous (GeneralLinearGroup.scalar ι : Rˣ → GL ι R) := by
      rw [Units.continuous_iff]
      refine ⟨?_, ?_⟩
      · simpa only [Function.comp_def, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply] using
          (continuous_pi fun _ => Units.continuous_val).matrix_diagonal
      · simpa only [Function.comp_def, MulOpposite.op_inv, ← map_inv,
          GeneralLinearGroup.coe_scalar, Matrix.scalar_apply] using
          (continuous_pi fun _ => Units.continuous_coe_inv).matrix_diagonal
    exact (((hsc.comp continuous_snd).mul continuous_fst).prodMk continuous_fst).subtype_mk _
  continuous_invFun := by
    refine (continuous_snd.comp continuous_subtype_val).prodMk ?_
    rw [Units.continuous_iff]
    let divMap : scalarDiagonal ι R → GL ι R := fun q => q.1.1 / q.1.2
    have hdiv : Continuous divMap :=
      (continuous_fst.comp continuous_subtype_val).div'
        (continuous_snd.comp continuous_subtype_val)
    refine ⟨?_, ?_⟩
    · exact (Units.continuous_val.comp hdiv).matrix_elem _ _
    · exact (Units.continuous_val.comp hdiv.inv).matrix_elem _ _

end TopologicalRing

end TauCeti.DiagonalOvergroups
