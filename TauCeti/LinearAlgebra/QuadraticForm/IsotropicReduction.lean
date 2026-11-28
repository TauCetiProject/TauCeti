/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.QuadraticForm.MaxIsotropic
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import TauCeti.LinearAlgebra.QuadraticForm.Basic
import TauCeti.LinearAlgebra.QuadraticForm.Radical

/-!
# Isotropic reduction of quadratic spaces

For a totally isotropic subspace `X`, the quadratic form descends to `Xᗮ / X`, where
orthogonality is taken with respect to its polar form. In finite dimension, a nondegenerate
polar form remains nondegenerate after reduction. The construction retains quadratic
vanishing in characteristic two.

A maximal isotropic subspace `W` reduces to the image of `(W ⊓ Xᗮ) ⊔ X`. This construction
allows intersection counts to be compared in quadratic spaces of successively smaller
dimension.

## References

* B. Poonen and E. Rains, *Random maximal isotropic subspaces and Selmer groups*,
  J. Amer. Math. Soc. 25 (2012), §2.1, Remark 2.4.
-/

public section

open Module LinearMap.BilinForm

namespace QuadraticMap

variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]
  (Q : QuadraticForm R V) (X : Submodule R V)

/-- The orthogonal quotient `Xᗮ / X`, using the preimage of `X` in its polar orthogonal.
The induced quadratic form requires total isotropy of `X`. -/
abbrev OrthogonalQuotient :=
  (orthogonal Q.polarBilin X) ⧸ X.comap (orthogonal Q.polarBilin X).subtype

/-- An isotropic submodule lies in the quadratic radical of the form restricted to its
polar orthogonal. -/
theorem IsTotallyIsotropic.comap_le_radical_restrict_orthogonal
    {Q : QuadraticForm R V} {X : Submodule R V} (hX : Q.IsTotallyIsotropic X) :
    X.comap (orthogonal Q.polarBilin X).subtype ≤
      (Q.restrict (orthogonal Q.polarBilin X)).radical := by
  intro x hx
  refine ⟨hX.apply_eq_zero hx, LinearMap.ext fun y ↦ ?_⟩
  simpa only [polarBilin_restrict, LinearMap.domRestrict₁₂_apply,
    polarBilin_apply_apply, LinearMap.zero_apply] using y.property x hx

/-- The quadratic form on the orthogonal quotient of a totally isotropic submodule. -/
noncomputable def orthogonalQuotientForm (hX : Q.IsTotallyIsotropic X) :
    QuadraticForm R (Q.OrthogonalQuotient X) :=
  (Q.restrict (orthogonal Q.polarBilin X)).lift _
    hX.comap_le_radical_restrict_orthogonal

/-- On representatives, the reduced quadratic form is the original quadratic form. -/
@[simp]
theorem orthogonalQuotientForm_mk (hX : Q.IsTotallyIsotropic X)
    (x : orthogonal Q.polarBilin X) :
    Q.orthogonalQuotientForm X hX (Submodule.Quotient.mk x) = Q x :=
  (rfl)

/-- The polar pairing on representatives of the orthogonal quotient is the original pairing. -/
@[simp]
theorem polar_orthogonalQuotientForm_mk (hX : Q.IsTotallyIsotropic X)
    (x y : orthogonal Q.polarBilin X) :
    polar (Q.orthogonalQuotientForm X hX) (Submodule.Quotient.mk x)
      (Submodule.Quotient.mk y) = polar Q (x : V) (y : V) := by
  rw [orthogonalQuotientForm, polar_lift_mk]
  rfl

/-- The image of `W ∩ Xᗮ` in the orthogonal quotient. For maximal isotropic `W` and
isotropic `X`, this is the isotropic reduction of `W`. -/
def isotropicReductionSubspace (W : Submodule R V) : Submodule R (Q.OrthogonalQuotient X) :=
  (W.comap (orthogonal Q.polarBilin X).subtype).map
    (X.comap (orthogonal Q.polarBilin X).subtype).mkQ

/-- The preimage of a reduced subspace, regarded in the original space, is
`(W ∩ Xᗮ) + X`. -/
theorem map_comap_isotropicReductionSubspace (hX : X ≤ orthogonal Q.polarBilin X)
    (W : Submodule R V) :
    ((Q.isotropicReductionSubspace X W).comap
      (X.comap (orthogonal Q.polarBilin X).subtype).mkQ).map
        (orthogonal Q.polarBilin X).subtype = (W ⊓ orthogonal Q.polarBilin X) ⊔ X := by
  rw [isotropicReductionSubspace, Submodule.comap_map_mkQ, Submodule.map_sup,
    Submodule.map_comap_subtype, Submodule.map_comap_subtype,
    inf_eq_right.mpr hX, sup_comm, inf_comm]

/-- Membership of a quotient representative in a reduced subspace is membership in
`(W ∩ Xᗮ) + X`. -/
@[simp]
theorem mk_mem_isotropicReductionSubspace_iff (hX : X ≤ orthogonal Q.polarBilin X)
    (W : Submodule R V) (v : orthogonal Q.polarBilin X) :
    Submodule.Quotient.mk v ∈ Q.isotropicReductionSubspace X W ↔
      (v : V) ∈ (W ⊓ orthogonal Q.polarBilin X) ⊔ X := by
  rw [← map_comap_isotropicReductionSubspace Q X hX W, Submodule.mem_map]
  simp only [Submodule.mem_comap, Submodule.coe_subtype, Subtype.val_injective.eq_iff,
    exists_eq_right, Submodule.mkQ_apply]

/-- Reduction preserves quadratic isotropy. -/
theorem IsTotallyIsotropic.isotropicReductionSubspace {Q : QuadraticForm R V}
    {W X : Submodule R V} (hW : Q.IsTotallyIsotropic W) (hX : Q.IsTotallyIsotropic X) :
    (Q.orthogonalQuotientForm X hX).IsTotallyIsotropic (Q.isotropicReductionSubspace X W) := by
  apply isTotallyIsotropic_iff.mpr
  rintro _ ⟨v, hv, rfl⟩
  exact (Q.orthogonalQuotientForm_mk X hX v).trans (hW.apply_eq_zero hv)

/-- A maximal isotropic subspace in the orthogonal quotient pulls back to a maximal
isotropic submodule of the original space. This direction needs no nondegeneracy hypothesis. -/
theorem IsMaxIsotropic.map_comap_orthogonalQuotient {Q : QuadraticForm R V}
    {X : Submodule R V} {hX : Q.IsTotallyIsotropic X}
    {U : Submodule R (Q.OrthogonalQuotient X)}
    (hU : (Q.orthogonalQuotientForm X hX).IsMaxIsotropic U) :
    Q.IsMaxIsotropic ((U.comap (X.comap (orthogonal Q.polarBilin X).subtype).mkQ).map
      (orthogonal Q.polarBilin X).subtype) := by
  let S := (U.comap (X.comap (orthogonal Q.polarBilin X).subtype).mkQ).map
    (orthogonal Q.polarBilin X).subtype
  have hXS : X ≤ S := by
    intro x hx
    refine ⟨⟨x, hX.le_orthogonal_polarBilin hx⟩, ?_, rfl⟩
    exact Submodule.le_comap_mkQ _ U hx
  have hS : Q.IsTotallyIsotropic S := by
    apply isTotallyIsotropic_iff.mpr
    rintro _ ⟨v, hv, rfl⟩
    exact (Q.orthogonalQuotientForm_mk X hX v).symm.trans (hU.isTotallyIsotropic.apply_eq_zero hv)
  apply isMaxIsotropic_iff.mpr
  refine ⟨hS, le_antisymm (fun v hv ↦ ?_) hS.le_orthogonal_polarBilin⟩
  have hvX : v ∈ orthogonal Q.polarBilin X := orthogonal_le hXS hv
  refine ⟨⟨v, hvX⟩, hU.mem_iff_forall_polar_eq_zero.mpr ?_, rfl⟩
  intro u hu
  induction u using Submodule.Quotient.induction_on with
  | H u =>
    rw [Submodule.mkQ_apply, polar_orthogonalQuotientForm_mk]
    exact hv u ⟨u, hu, rfl⟩

/-- If the reducing subspace lies in `W`, reduction is the ordinary quotient `W / X`,
characterized by its preimage in the original space. -/
theorem IsMaxIsotropic.map_comap_isotropicReductionSubspace_of_le
    {Q : QuadraticForm R V} {X W : Submodule R V}
    (hW : Q.IsMaxIsotropic W) (hXW : X ≤ W) :
    ((Q.isotropicReductionSubspace X W).comap
      (X.comap (orthogonal Q.polarBilin X).subtype).mkQ).map
        (orthogonal Q.polarBilin X).subtype = W := by
  have hWX : W ≤ orthogonal Q.polarBilin X :=
    hW.orthogonal_polarBilin_eq ▸ orthogonal_le hXW
  rw [map_comap_isotropicReductionSubspace Q X
    (hW.isTotallyIsotropic.mono hXW).le_orthogonal_polarBilin, inf_eq_left.mpr hWX,
    sup_eq_left.mpr hXW]

-- Simplify the outer preimage before comap_bot changes the quotient presentation.
/-- Reduction by zero is the identity, read through the quotient preimage. -/
@[simp↓]
theorem map_comap_isotropicReductionSubspace_bot (W : Submodule R V) :
    ((Q.isotropicReductionSubspace ⊥ W).comap
      ((⊥ : Submodule R V).comap (orthogonal Q.polarBilin ⊥).subtype).mkQ).map
        (orthogonal Q.polarBilin ⊥).subtype = W := by
  rw [map_comap_isotropicReductionSubspace Q ⊥ bot_le]
  simp

/-- Reduction by a maximal isotropic submodule gives the zero module. -/
theorem IsMaxIsotropic.subsingleton_orthogonalQuotient {Q : QuadraticForm R V}
    {X : Submodule R V} (hX : Q.IsMaxIsotropic X) : Subsingleton (Q.OrthogonalQuotient X) := by
  apply Submodule.Quotient.subsingleton_iff.mpr
  exact top_unique fun x _ ↦
    (congrArg (fun S : Submodule R V ↦ (x : V) ∈ S) hX.orthogonal_polarBilin_eq).mp x.property

section Field

variable {K M : Type*} [Field K] [AddCommGroup M] [Module K M]
  [FiniteDimensional K M] {Q : QuadraticForm K M} {X W : Submodule K M}

/-- In a nondegenerate quadratic space, the radical of the polar form restricted to `Xᗮ`
is `X`, viewed inside `Xᗮ`. -/
theorem ker_polarBilin_restrict_orthogonal (hQ : Q.polarBilin.Nondegenerate)
    (X : Submodule K M) :
    (Q.restrict (orthogonal Q.polarBilin X)).polarBilin.ker =
      X.comap (orthogonal Q.polarBilin X).subtype := by
  ext x
  simp only [Submodule.mem_comap, Submodule.coe_subtype]
  rw [← congrArg (fun S : Submodule K M ↦ (x : M) ∈ S)
    (orthogonal_orthogonal hQ Q.isRefl_polarBilin X)]
  simp only [LinearMap.mem_ker, LinearMap.ext_iff, LinearMap.zero_apply,
    polarBilin_restrict, LinearMap.domRestrict₁₂_apply, polarBilin_apply_apply,
    mem_orthogonal_iff]
  constructor
  · intro hx y hy
    rw [polar_comm]
    exact hx ⟨y, hy⟩
  · intro hx y
    rw [polar_comm]
    exact hx y y.property

/-- Isotropic reduction preserves nondegeneracy of the polar form, including in
characteristic two. -/
theorem nondegenerate_polarBilin_orthogonalQuotientForm
    (hQ : Q.polarBilin.Nondegenerate) (hX : Q.IsTotallyIsotropic X) :
    (Q.orthogonalQuotientForm X hX).polarBilin.Nondegenerate := by
  apply LinearMap.IsRefl.nondegenerate_iff_separatingLeft
    (Q.orthogonalQuotientForm X hX).isRefl_polarBilin |>.mpr
  rw [LinearMap.separatingLeft_iff_ker_eq_bot, orthogonalQuotientForm,
    ker_polarBilin_lift, ker_polarBilin_restrict_orthogonal hQ, Submodule.mkQ_map_self]

/-- Isotropic reduction removes twice the dimension of the reducing subspace. -/
theorem finrank_orthogonalQuotient (hQ : Q.polarBilin.Nondegenerate)
    (hX : X ≤ orthogonal Q.polarBilin X) :
    finrank K (Q.OrthogonalQuotient X) = finrank K M - 2 * finrank K X := by
  have hdim := Submodule.finrank_quotient_add_finrank
    (X.comap (orthogonal Q.polarBilin X).subtype)
  have hmap : (X.comap (orthogonal Q.polarBilin X).subtype).map
      (orthogonal Q.polarBilin X).subtype = X := by
    rw [Submodule.map_comap_subtype, inf_eq_right.mpr hX]
  have hsub := Submodule.finrank_map_subtype_eq (orthogonal Q.polarBilin X)
    (X.comap (orthogonal Q.polarBilin X).subtype)
  rw [hmap] at hsub
  rw [finrank_orthogonal hQ] at hdim
  dsimp only [OrthogonalQuotient]
  omega

/-- Reduction of a maximal isotropic subspace is maximal isotropic in the reduced space. -/
theorem IsMaxIsotropic.isotropicReductionSubspace (hW : Q.IsMaxIsotropic W)
    (hX : Q.IsTotallyIsotropic X) :
    (Q.orthogonalQuotientForm X hX).IsMaxIsotropic (Q.isotropicReductionSubspace X W) := by
  apply isMaxIsotropic_iff.mpr
  refine ⟨hW.isTotallyIsotropic.isotropicReductionSubspace hX, ?_⟩
  ext v
  induction v using Submodule.Quotient.induction_on with
  | H v =>
    rw [mk_mem_isotropicReductionSubspace_iff Q X hX.le_orthogonal_polarBilin W]
    have horth : orthogonal Q.polarBilin (W ⊓ orthogonal Q.polarBilin X) = W ⊔ X := by
      have hsup : orthogonal Q.polarBilin (W ⊔ X) =
          orthogonal Q.polarBilin W ⊓ orthogonal Q.polarBilin X :=
        Submodule.orthogonalBilin_sup W X
      rw [hW.orthogonal_polarBilin_eq] at hsup
      rw [← hsup]
      symm
      apply Submodule.eq_of_le_of_finrank_le (le_orthogonal_orthogonal Q.isRefl_polarBilin)
      -- The polar radical lies in both subspaces and contributes equally to their dimensions.
      have hrad : orthogonal Q.polarBilin ⊤ ≤ W :=
        hW.orthogonal_polarBilin_eq ▸ orthogonal_le le_top
      have h₁ := finrank_add_finrank_orthogonal Q.isRefl_polarBilin (W ⊔ X)
      have h₂ := finrank_add_finrank_orthogonal Q.isRefl_polarBilin
        (orthogonal Q.polarBilin (W ⊔ X))
      rw [inf_eq_right.mpr (hrad.trans le_sup_left)] at h₁
      rw [inf_eq_right.mpr (orthogonal_le le_top)] at h₂
      omega
    have hmem : Submodule.Quotient.mk v ∈ orthogonal
        (Q.orthogonalQuotientForm X hX).polarBilin (Q.isotropicReductionSubspace X W) ↔
        (v : M) ∈ orthogonal Q.polarBilin (W ⊓ orthogonal Q.polarBilin X) := by
      simp only [mem_orthogonal_iff, QuadraticMap.isotropicReductionSubspace, Submodule.mem_map,
        forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, Submodule.mem_comap,
        Submodule.coe_subtype, Submodule.mkQ_apply, polarBilin_apply_apply,
        polar_orthogonalQuotientForm_mk]
      constructor
      · intro h w hw
        exact h ⟨w, hw.2⟩ hw.1
      · intro h w hw
        exact h w ⟨hw, w.property⟩
    rw [hmem, horth]
    have hmod : (W ⊓ orthogonal Q.polarBilin X) ⊔ X =
        (W ⊔ X) ⊓ orthogonal Q.polarBilin X := by
      rw [sup_comm W X, sup_inf_assoc_of_le W hX.le_orthogonal_polarBilin, sup_comm]
    rw [hmod, Submodule.mem_inf]
    exact (and_iff_left v.property).symm

/-- The isotropic reduction map on actual maximal isotropic subspaces. -/
def isotropicReduction (hX : Q.IsTotallyIsotropic X)
    (W : Q.maxIsotropicSubspaces) : (Q.orthogonalQuotientForm X hX).maxIsotropicSubspaces :=
  ⟨Q.isotropicReductionSubspace X W, mem_maxIsotropicSubspaces.mpr
    ((mem_maxIsotropicSubspaces.mp W.property).isotropicReductionSubspace hX)⟩

/-- The underlying subspace of isotropic reduction is the quotient image of `W ∩ Xᗮ`. -/
@[simp]
theorem coe_isotropicReduction
    (hX : Q.IsTotallyIsotropic X) (W : Q.maxIsotropicSubspaces) :
    (isotropicReduction hX W : Submodule K (Q.OrthogonalQuotient X)) =
      Q.isotropicReductionSubspace X W :=
  (rfl)

/-- Each quotient maximal isotropic has a unique maximal isotropic lift containing `X`. -/
theorem existsUnique_isotropicReduction_eq
    (hX : Q.IsTotallyIsotropic X) (U : (Q.orthogonalQuotientForm X hX).maxIsotropicSubspaces) :
    ∃! W : Q.maxIsotropicSubspaces, X ≤ (W : Submodule K M) ∧
      isotropicReduction hX W = U := by
  let S := ((U : Submodule K (Q.OrthogonalQuotient X)).comap
    (X.comap (orthogonal Q.polarBilin X).subtype).mkQ).map
      (orthogonal Q.polarBilin X).subtype
  have hS : Q.IsMaxIsotropic S :=
    (mem_maxIsotropicSubspaces.mp U.property).map_comap_orthogonalQuotient
  have hXS : X ≤ S := by
    intro x hx
    exact ⟨⟨x, hX.le_orthogonal_polarBilin hx⟩, Submodule.le_comap_mkQ _ _ hx, rfl⟩
  have hSU : isotropicReduction hX ⟨S, mem_maxIsotropicSubspaces.mpr hS⟩ = U := by
    apply Subtype.ext
    simp only [coe_isotropicReduction, QuadraticMap.isotropicReductionSubspace, S,
      Submodule.comap_map_eq_of_injective (orthogonal Q.polarBilin X).subtype_injective,
      Submodule.map_comap_eq_of_surjective (Submodule.mkQ_surjective _)]
  refine ⟨⟨S, mem_maxIsotropicSubspaces.mpr hS⟩, ⟨hXS, hSU⟩, ?_⟩
  rintro W ⟨hXW, hWU⟩
  apply Subtype.ext
  rw [← (mem_maxIsotropicSubspaces.mp W.property).map_comap_isotropicReductionSubspace_of_le hXW]
  rw [← coe_isotropicReduction hX, hWU]

/-- Isotropic reduction is surjective on maximal isotropic subspaces. -/
theorem isotropicReduction_surjective
    (hX : Q.IsTotallyIsotropic X) : Function.Surjective (isotropicReduction hX) := by
  intro U
  obtain ⟨W, hW, _⟩ := existsUnique_isotropicReduction_eq hX U
  exact ⟨W, hW.2⟩

/-- In ambient dimension `2n`, every reduced maximal isotropic has dimension `n - dim X`. -/
theorem finrank_isotropicReduction (hQ : Q.polarBilin.Nondegenerate)
    (hX : Q.IsTotallyIsotropic X) {n : ℕ} (hM : finrank K M = 2 * n)
    (W : Q.maxIsotropicSubspaces) :
    finrank K (isotropicReduction hX W : Submodule K (Q.OrthogonalQuotient X)) =
      n - finrank K X := by
  have hW := mem_maxIsotropicSubspaces.mp (isotropicReduction hX W).property
  have hdim := hW.two_mul_finrank_eq
    (nondegenerate_of_nondegenerate_polarBilin
      (nondegenerate_polarBilin_orthogonalQuotientForm hQ hX)).radical_eq_bot
  rw [finrank_orthogonalQuotient hQ hX.le_orthogonal_polarBilin, hM] at hdim
  omega

/-- A weakly metabolic space remains weakly metabolic after isotropic reduction. -/
theorem IsWeaklyMetabolic.orthogonalQuotientForm (hQ : Q.IsWeaklyMetabolic)
    (hX : Q.IsTotallyIsotropic X) : (Q.orthogonalQuotientForm X hX).IsWeaklyMetabolic := by
  obtain ⟨W, hW⟩ := hQ.exists_isMaxIsotropic
  apply isWeaklyMetabolic_iff.mpr
  exact ⟨nondegenerate_polarBilin_orthogonalQuotientForm hQ.nondegenerate_polarBilin hX,
    ⟨_, hW.isotropicReductionSubspace hX⟩⟩

end Field

end QuadraticMap
