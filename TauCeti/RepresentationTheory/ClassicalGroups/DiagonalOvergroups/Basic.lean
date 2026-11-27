/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Group.Matrix
public import TauCeti.GroupTheory.Goursat
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.ProjGenLinGroup.Center
import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Conjugation
import TauCeti.Topology.Algebra.Matrix.GeneralLinearGroup.Diagonal

/-!
# Diagonal overgroups of the general linear group: algebraic and Goursat structure

Inside `GL ι R × GL ι R` sit four distinguished subgroups containing the diagonal `Δ = {(g, g)}`:
`diagonal`, `scalarDiagonal` (`{(scalar ι u * g, g)}`), `determinantEqual`
(`{(g, h) | g.det = h.det}`), and `⊤`, corresponding via `TauCeti/GroupTheory/Goursat.lean` to the
normal subgroups `⊥`, `Subgroup.center (GL ι R)`, `SpecialLinearGroup.toGL.range`, and `⊤`. This
file develops their Goursat kernels, quotient and product splittings, and normalizers
(`normalizer_diagonal` and `normalizer_scalarDiagonal`).

## References

* Jean Dieudonné, *La géométrie des groupes classiques*, 3rd ed., Springer, 1971, Chapter I.
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
def diagonal : Subgroup (GL ι R × GL ι R) := (diagonalMap ι R).range

/-- **The determinant-ratio homomorphism** `(g, h) ↦ g.det / h.det`. -/
def determinantRatio : GL ι R × GL ι R →* Rˣ where
  toFun p := p.1.det / p.2.det
  map_one' := by simp
  map_mul' _ _ := by simp [div_mul_div_comm]

/-- **The equal-determinant subgroup** `{(g, h) | g.det = h.det}`. -/
def determinantEqual : Subgroup (GL ι R × GL ι R) := (determinantRatio ι R).ker

/-- The parameterization `(g, u) ↦ (scalar ι u * g, g)` of `scalarDiagonal`. -/
def scalarDiagonalMap : GL ι R × Rˣ →* GL ι R × GL ι R where
  toFun p := (GeneralLinearGroup.scalar ι p.2 * p.1, p.1)
  map_one' := by simp
  map_mul' p q := Prod.ext (by
    simp only [Prod.fst_mul, Prod.snd_mul, map_mul, mul_assoc]
    rw [← mul_assoc p.1, ← GeneralLinearGroup.scalar_commute q.2 p.1, mul_assoc]) rfl

/-- **The scalar-diagonal subgroup** `{(scalar ι u * g, g) | g : GL ι R, u : Rˣ}`. -/
def scalarDiagonal : Subgroup (GL ι R × GL ι R) := (scalarDiagonalMap ι R).range

variable {ι R}

@[simp] theorem diagonalMap_apply (g : GL ι R) : diagonalMap ι R g = (g, g) := by rfl

/-- `diagonal ι R` coincides with the graph `(MonoidHom.id (GL ι R)).graph` of the identity. -/
theorem diagonal_eq_graph_id : diagonal ι R = (MonoidHom.id (GL ι R)).graph :=
  (MonoidHom.graph_eq_range_prod (MonoidHom.id (GL ι R))).symm

@[simp] theorem mem_diagonal_iff {p : GL ι R × GL ι R} : p ∈ diagonal ι R ↔ p.1 = p.2 := by
  rw [diagonal_eq_graph_id, MonoidHom.mem_graph, MonoidHom.id_apply]

@[simp] theorem determinantRatio_apply (p : GL ι R × GL ι R) :
    determinantRatio ι R p = p.1.det / p.2.det := by rfl

@[simp] theorem mem_determinantEqual_iff {p : GL ι R × GL ι R} :
    p ∈ determinantEqual ι R ↔ p.1.det = p.2.det := by
  simp [determinantEqual, MonoidHom.mem_ker, div_eq_one]

instance instNormalDeterminantEqual : (determinantEqual ι R).Normal :=
  MonoidHom.normal_ker (determinantRatio ι R)

@[simp] theorem scalarDiagonalMap_apply (p : GL ι R × Rˣ) :
    scalarDiagonalMap ι R p = (GeneralLinearGroup.scalar ι p.2 * p.1, p.1) := by rfl

@[simp] theorem mem_scalarDiagonal_iff {p : GL ι R × GL ι R} :
    p ∈ scalarDiagonal ι R ↔ ∃ u : Rˣ, p.1 = GeneralLinearGroup.scalar ι u * p.2 :=
  ⟨fun ⟨⟨_, u⟩, h⟩ => ⟨u, (congrArg Prod.fst h).symm.trans (by simp [← congrArg Prod.snd h])⟩,
   fun ⟨u, hu⟩ => ⟨(p.2, u), Prod.ext hu.symm rfl⟩⟩

/-- `scalarDiagonal ι R` is the Goursat extension `Subgroup.diagonalExt` of
`Subgroup.center (GL ι R)`. -/
theorem scalarDiagonal_eq_diagonalExt_center :
    scalarDiagonal ι R = Subgroup.diagonalExt (Subgroup.center (GL ι R)) := by
  ext ⟨g, h⟩
  rw [mem_scalarDiagonal_iff, Subgroup.mem_diagonalExt, GeneralLinearGroup.center_eq_range_scalar]
  exact ⟨fun ⟨u, hu⟩ => ⟨u, by rw [hu, mul_div_cancel_right]⟩,
    fun ⟨u, hu⟩ => ⟨u, by rw [hu, div_mul_cancel]⟩⟩

/-- For `p ∈ scalarDiagonal ι R`, the ratio `p.1 / p.2` lies in `Subgroup.center (GL ι R)`. -/
theorem div_mem_center_of_mem_scalarDiagonal {p : GL ι R × GL ι R}
    (hp : p ∈ scalarDiagonal ι R) : p.1 / p.2 ∈ Subgroup.center (GL ι R) :=
  Subgroup.mem_diagonalExt.mp (scalarDiagonal_eq_diagonalExt_center (ι := ι) (R := R) ▸ hp)

/-- Pairs lie in `scalarDiagonal` iff they have the same class in `PGL(ι, R)`. -/
theorem mem_scalarDiagonal_iff_mk_eq {p : GL ι R × GL ι R} :
    p ∈ scalarDiagonal ι R ↔ ProjGenLinGroup.mk p.1 = ProjGenLinGroup.mk p.2 := by
  rw [scalarDiagonal_eq_diagonalExt_center, Subgroup.mem_diagonalExt, ← ProjGenLinGroup.mk_eq_one,
    map_div, div_eq_one]

/-- `determinantEqual ι R` is the Goursat extension `Subgroup.diagonalExt` of
`(GeneralLinearGroup.det).ker`. -/
theorem determinantEqual_eq_diagonalExt_ker_det :
    determinantEqual ι R =
      Subgroup.diagonalExt (GeneralLinearGroup.det (n := ι) (R := R)).ker := by
  ext ⟨g, h⟩; simp [Subgroup.mem_diagonalExt, MonoidHom.mem_ker, div_eq_one]

theorem diagonal_le_scalarDiagonal : diagonal ι R ≤ scalarDiagonal ι R :=
  fun _ hp => mem_scalarDiagonal_iff.mpr ⟨1, by simp [mem_diagonal_iff.mp hp]⟩

theorem graph_id_le_scalarDiagonal : (MonoidHom.id (GL ι R)).graph ≤ scalarDiagonal ι R :=
  diagonal_eq_graph_id (ι := ι) (R := R) ▸ diagonal_le_scalarDiagonal

theorem diagonal_le_determinantEqual : diagonal ι R ≤ determinantEqual ι R :=
  fun _ hp => mem_determinantEqual_iff.mpr (congrArg _ (mem_diagonal_iff.mp hp))

theorem graph_id_le_determinantEqual : (MonoidHom.id (GL ι R)).graph ≤ determinantEqual ι R :=
  diagonal_eq_graph_id (ι := ι) (R := R) ▸ diagonal_le_determinantEqual

/-- The Goursat normal kernel of `diagonal ι R` is `⊥`. -/
@[simp] theorem goursatFst_diagonal : (diagonal ι R).goursatFst = ⊥ := by
  rw [diagonal_eq_graph_id, Subgroup.goursatFst_graph_id]

/-- The Goursat normal kernel of `scalarDiagonal ι R` is `Subgroup.center (GL ι R)`. -/
@[simp] theorem goursatFst_scalarDiagonal :
    (scalarDiagonal ι R).goursatFst = Subgroup.center (GL ι R) := by
  rw [scalarDiagonal_eq_diagonalExt_center, Subgroup.goursatFst_diagonalExt]

/-- The Goursat normal kernel of `determinantEqual ι R` is `SpecialLinearGroup.toGL.range`. -/
@[simp] theorem goursatFst_determinantEqual :
    (determinantEqual ι R).goursatFst = (SpecialLinearGroup.toGL (n := ι) (R := R)).range := by
  rw [determinantEqual_eq_diagonalExt_ker_det, Subgroup.goursatFst_diagonalExt,
    SpecialLinearGroup.range_toGL_eq_ker_det]

/-- **The normalizer of the diagonal subgroup in `GL ι R × GL ι R` is `scalarDiagonal ι R`.** -/
@[simp] theorem normalizer_diagonal :
    Subgroup.normalizer (diagonal ι R : Set (GL ι R × GL ι R)) = scalarDiagonal ι R := by
  rw [diagonal_eq_graph_id, Subgroup.normalizer_graph_id, scalarDiagonal_eq_diagonalExt_center]

instance instNormalDiagonalSubgroupOfScalarDiagonal :
    ((diagonal ι R).subgroupOf (scalarDiagonal ι R)).Normal := by
  rw [Subgroup.normal_subgroupOf_iff_le_normalizer diagonal_le_scalarDiagonal, normalizer_diagonal]

/-- For `|ι| ≥ 2` and nontrivial `R`, `determinantEqual ι R` is not contained in
`scalarDiagonal ι R`. -/
theorem not_determinantEqual_le_scalarDiagonal [Nontrivial ι] [Nontrivial R] :
    ¬ (determinantEqual ι R ≤ scalarDiagonal ι R) := by
  obtain ⟨i, j, hij⟩ := exists_pair_ne ι
  intro hle
  obtain ⟨u, hu⟩ := mem_scalarDiagonal_iff.mp (hle ((mem_determinantEqual_iff
    (p := (SpecialLinearGroup.toGL (SpecialLinearGroup.transvection hij (1 : R)), 1))).mpr
    (by simp)))
  simpa [SpecialLinearGroup.coe_GL_coe_matrix, SpecialLinearGroup.transvection_coe,
    GeneralLinearGroup.coe_scalar, hij] using
    congrArg (fun M : Matrix ι ι R => M i j) (congrArg Units.val hu)

/-- For `|ι| ≥ 2` and nontrivial `R`, `scalarDiagonal ι R` is strictly smaller than `⊤`. -/
theorem scalarDiagonal_ne_top [Nontrivial ι] [Nontrivial R] : scalarDiagonal ι R ≠ ⊤ :=
  fun htop => not_determinantEqual_le_scalarDiagonal (htop ▸ le_top)

/-- **The diagonal subgroup is not normal in `GL ι R × GL ι R`** when `|ι| ≥ 2` and `R` is
nontrivial. -/
theorem not_normal_diagonal [Nontrivial ι] [Nontrivial R] : ¬ (diagonal ι R).Normal :=
  fun hN => scalarDiagonal_ne_top
    (normalizer_diagonal (ι := ι) (R := R) ▸ @Subgroup.normalizer_eq_top _ _ _ hN)

/-- **Over an integral domain, `scalarDiagonal ι R` is self-normalizing in `GL ι R × GL ι R`.** -/
@[simp] theorem normalizer_scalarDiagonal [IsDomain R] :
    Subgroup.normalizer (scalarDiagonal ι R : Set (GL ι R × GL ι R)) = scalarDiagonal ι R := by
  rw [scalarDiagonal_eq_diagonalExt_center]
  exact Subgroup.normalizer_diagonalExt_center_of_center_quotient_eq_bot
    (ProjGenLinGroup.center_eq_bot (n := ι) (R := R))

@[simp] theorem ker_scalarDiagonalMap_of_isEmpty [IsEmpty ι] : (scalarDiagonalMap ι R).ker = ⊤ :=
  eq_top_iff.mpr fun _ _ => Subsingleton.elim _ _

theorem scalarDiagonalMap_injective [Nonempty ι] :
    Function.Injective (scalarDiagonalMap ι R) := by
  rintro ⟨g₁, u₁⟩ ⟨g₂, u₂⟩ h
  obtain ⟨h1, rfl⟩ := Prod.ext_iff.mp h
  exact Prod.ext rfl (GeneralLinearGroup.scalar_injective (mul_right_cancel h1))

/-- **Isomorphism `GL ι R ≃* diagonal ι R`** sending `g` to `(g, g)`. -/
def diagonalEquiv : GL ι R ≃* diagonal ι R where
  toFun g := ⟨(g, g), mem_diagonal_iff.mpr rfl⟩
  invFun p := p.val.1
  left_inv _ := rfl
  right_inv p := Subtype.ext (Prod.ext rfl (mem_diagonal_iff.mp p.property))
  map_mul' _ _ := by rfl

@[simp] theorem coe_diagonalEquiv_apply (g : GL ι R) :
    (diagonalEquiv g : GL ι R × GL ι R) = (g, g) := by rfl

@[simp] theorem diagonalEquiv_symm_apply (p : diagonal ι R) :
    diagonalEquiv.symm p = p.val.1 := by rfl

/-- **Isomorphism `GL ι R × Rˣ ≃* scalarDiagonal ι R`** for nonempty `ι`. -/
noncomputable def scalarDiagonalEquiv [Nonempty ι] :
    GL ι R × Rˣ ≃* scalarDiagonal ι R where
  toFun := (scalarDiagonalMap ι R).rangeRestrict
  invFun q := (q.val.2, (GeneralLinearGroup.unitsMulEquivCenter ι).symm
    ⟨q.val.1 / q.val.2, div_mem_center_of_mem_scalarDiagonal q.property⟩)
  left_inv p := Prod.ext rfl (by simp [mul_div_cancel_right])
  right_inv q := Subtype.ext (Prod.ext (by simp [div_mul_cancel]) rfl)
  map_mul' := map_mul _

@[simp] theorem coe_scalarDiagonalEquiv_apply [Nonempty ι] (p : GL ι R × Rˣ) :
    (scalarDiagonalEquiv p : GL ι R × GL ι R) = (GeneralLinearGroup.scalar ι p.2 * p.1, p.1) := by
  rfl

@[simp] theorem fst_scalarDiagonalEquiv_symm [Nonempty ι] (q : scalarDiagonal ι R) :
    (scalarDiagonalEquiv.symm q).1 = q.val.2 := by rfl

@[simp] theorem scalar_snd_scalarDiagonalEquiv_symm [Nonempty ι] (q : scalarDiagonal ι R) :
    GeneralLinearGroup.scalar ι (scalarDiagonalEquiv.symm q).2 = q.val.1 / q.val.2 :=
  GeneralLinearGroup.scalar_unitsMulEquivCenter_symm _

theorem determinantRatio_surjective [Nonempty ι] :
    Function.Surjective (determinantRatio ι R) := fun u =>
  let ⟨g, hg⟩ := GeneralLinearGroup.det_surjective (n := ι) u
  ⟨(g, 1), by simp [hg]⟩

/-- **First-isomorphism identification `(GL ι R × GL ι R) ⧸ determinantEqual ι R ≃* Rˣ`.** -/
noncomputable def quotientDeterminantEqualEquiv [Nonempty ι] :
    (GL ι R × GL ι R) ⧸ determinantEqual ι R ≃* Rˣ :=
  QuotientGroup.quotientKerEquivOfSurjective (determinantRatio ι R) determinantRatio_surjective

@[simp] theorem quotientDeterminantEqualEquiv_mk [Nonempty ι] (p : GL ι R × GL ι R) :
    quotientDeterminantEqualEquiv (QuotientGroup.mk p) = p.1.det / p.2.det := by rfl

/-- The second-coordinate projection `scalarDiagonal ι R →* GL ι R`. -/
def sndProj : scalarDiagonal ι R →* GL ι R :=
  (MonoidHom.snd (GL ι R) (GL ι R)).comp (scalarDiagonal ι R).subtype

@[simp] theorem sndProj_apply (q : scalarDiagonal ι R) : sndProj q = q.val.2 := by rfl

theorem sndProj_surjective : Function.Surjective (sndProj (ι := ι) (R := R)) := fun g =>
  ⟨⟨(g, g), diagonal_le_scalarDiagonal (mem_diagonal_iff.mpr rfl)⟩, rfl⟩

/-- The scalar projection `scalarDiagonal ι R →* Rˣ` sending `(scalar ι u * g, g)` to `u`. -/
noncomputable def scalarProj [Nonempty ι] : scalarDiagonal ι R →* Rˣ :=
  (MonoidHom.snd (GL ι R) Rˣ).comp scalarDiagonalEquiv.symm.toMonoidHom

@[simp] theorem scalarProj_apply_scalarDiagonalEquiv [Nonempty ι] (p : GL ι R × Rˣ) :
    scalarProj (scalarDiagonalEquiv p) = p.2 :=
  congrArg Prod.snd (MulEquiv.symm_apply_apply scalarDiagonalEquiv p)

/-- Applying `GeneralLinearGroup.scalar ι` to `scalarProj q` recovers the ratio
`q.val.1 / q.val.2`. -/
@[simp] theorem scalar_scalarProj [Nonempty ι] (q : scalarDiagonal ι R) :
    GeneralLinearGroup.scalar ι (scalarProj q) = q.val.1 / q.val.2 :=
  scalar_snd_scalarDiagonalEquiv_symm q

/-- The underlying scalar of `scalarProj q` equals any diagonal entry of `q.val.1 / q.val.2`. -/
theorem val_scalarProj [Nonempty ι] (q : scalarDiagonal ι R) (i : ι) :
    ((scalarProj q : Rˣ) : R) = ((q.val.1 / q.val.2 : GL ι R) : Matrix ι ι R) i i := by
  simpa only [GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.diagonal_apply_eq] using
    congrArg (fun g : GL ι R => (g : Matrix ι ι R) i i) (scalar_scalarProj q)

theorem ker_scalarProj [Nonempty ι] :
    (scalarProj (ι := ι) (R := R)).ker = (diagonal ι R).subgroupOf (scalarDiagonal ι R) := by
  ext q
  obtain ⟨⟨g, u⟩, rfl⟩ := scalarDiagonalEquiv.surjective q
  rw [MonoidHom.mem_ker, scalarProj_apply_scalarDiagonalEquiv, Subgroup.mem_subgroupOf,
    mem_diagonal_iff, coe_scalarDiagonalEquiv_apply, mul_eq_right]
  exact ⟨fun hu => by rw [hu, map_one], fun hu =>
    (Prod.ext_iff.mp (scalarDiagonalMap_injective (ι := ι) (R := R)
      (a₁ := (1, u)) (a₂ := (1, 1)) (by simp [hu]))).2⟩

theorem scalarProj_surjective [Nonempty ι] :
    Function.Surjective (scalarProj (ι := ι) (R := R)) := fun u =>
  ⟨scalarDiagonalEquiv (1, u), by simp⟩

/-- **Quotient identification `scalarDiagonal ι R ⧸ diagonal ι R ≃* Rˣ`** for nonempty `ι`. -/
noncomputable def quotientDiagonalOfScalarDiagonalEquiv [Nonempty ι] :
    scalarDiagonal ι R ⧸ (diagonal ι R).subgroupOf (scalarDiagonal ι R) ≃* Rˣ :=
  (QuotientGroup.quotientMulEquivOfEq ker_scalarProj.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective scalarProj scalarProj_surjective)

@[simp] theorem quotientDiagonalOfScalarDiagonalEquiv_mk [Nonempty ι] (q : scalarDiagonal ι R) :
    quotientDiagonalOfScalarDiagonalEquiv (QuotientGroup.mk q) = scalarProj q := by rfl

end CommRing

section TopologicalRing

variable {ι R : Type*} [Fintype ι] [DecidableEq ι] [CommRing R] [TopologicalSpace R]

/-- **Topological group isomorphism `GL ι R × Rˣ ≃ₜ* scalarDiagonal ι R`** for nonempty `ι`. -/
noncomputable def scalarDiagonalContinuousMulEquiv [IsTopologicalRing R] [Nonempty ι] :
    GL ι R × Rˣ ≃ₜ* scalarDiagonal ι R where
  toMulEquiv := scalarDiagonalEquiv
  continuous_toFun :=
    (((GeneralLinearGroup.continuous_scalar.comp continuous_snd).mul continuous_fst).prodMk
      continuous_fst).subtype_mk _
  continuous_invFun := (continuous_snd.comp continuous_subtypeVal).prodMk <| by
    obtain ⟨i₀⟩ := ‹Nonempty ι›
    have hdiv : Continuous fun q : scalarDiagonal ι R => q.val.1 / q.val.2 :=
      (continuous_fst.comp continuous_subtypeVal).div' (continuous_snd.comp continuous_subtypeVal)
    let divMem (q : scalarDiagonal ι R) : Subgroup.center (GL ι R) :=
      ⟨q.val.1 / q.val.2, div_mem_center_of_mem_scalarDiagonal q.property⟩
    refine Units.continuous_iff.mpr
      ⟨((Units.continuous_val.comp hdiv).matrix_elem i₀ i₀).congr fun q =>
          (GeneralLinearGroup.val_unitsMulEquivCenter_symm_apply (divMem q) i₀).symm,
       ((Units.continuous_val.comp hdiv.inv).matrix_elem i₀ i₀).congr fun q => by
          simpa only [Function.comp_def, Pi.inv_apply, ← map_inv, Subgroup.coe_inv] using
            (GeneralLinearGroup.val_unitsMulEquivCenter_symm_apply (divMem q)⁻¹ i₀).symm⟩

end TopologicalRing

end TauCeti.DiagonalOvergroups
