/-
Copyright (c) 2026 Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex, Claude
-/
module

public import TauCeti.NumberTheory.ClassFieldTheory.Formation.Corestriction
public import TauCeti.NumberTheory.ClassFieldTheory.Formation.GroundNorm
public import TauCeti.NumberTheory.ClassFieldTheory.Formation.Tate.Basic
public import TauCeti.RepresentationTheory.Homological.TateCohomology.NegativeCorestriction
public import TauCeti.RepresentationTheory.Homological.TateCohomology.Restriction.Basic

/-!
# Corestriction of finite-layer Tate cohomology

For a restriction of finite normal layers `K/E` inside `K/F`, this file defines corestriction

`Ĥʳ(Gal(K/E), A^V) ⟶ Ĥʳ(Gal(K/F), A^V)`

in every integer degree. The construction uses the canonical identification of the smaller
Galois group with the image of its inclusion into the larger one. In positive degrees it is the
ordinary cohomological corestriction from
`TauCeti.NumberTheory.ClassFieldTheory.Formation.Corestriction`; in degrees zero and minus one it
is induced by the relative norm and inclusion of norm kernels; and in degrees at most minus two
it is the covariant map on group homology.

The comparison lemmas below identify each branch with the corresponding established map. They
allow consumers to use Tate corestriction without unfolding its integer-degree case split. On
representatives, degree zero is the ground-level norm `N_{U/U'} : A^{U'} → A^U` and degree minus
one is the inclusion of norm kernels; in degrees at most minus two corestriction is the covariant
map on group homology along the inclusion of Galois groups. These descriptions no longer mention
the image subgroup through which the construction passes, and they give functoriality along a
tower `F ⊆ E ⊆ E' ⊆ K` of ground fields in every degree.

## Main definitions

* `TauCeti.ClassFieldTheory.LayerRestriction.tateCor`: corestriction of layer Tate cohomology.
* `TauCeti.ClassFieldTheory.LayerRestriction.trivialTateCor`: corestriction of Tate cohomology
  with trivial integral coefficients.
* `TauCeti.ClassFieldTheory.LayerRestriction.kerNormInclusion`: the inclusion of the norm kernel
  of `K/E` in the norm kernel of `K/F`.

## Main results

* `TauCeti.ClassFieldTheory.LayerRestriction.tateCor_zero_H0π` and
  `TauCeti.ClassFieldTheory.LayerRestriction.tateHZeroEquivNormQuotient_tateCor_H0π`: in degree
  zero, corestriction is the ground-level norm.
* `TauCeti.ClassFieldTheory.LayerRestriction.tateCor_neg_one_HNegOneπ`: in degree minus one,
  corestriction is the inclusion of norm kernels `kerNormInclusion`.
* `TauCeti.ClassFieldTheory.LayerRestriction.tateCor_negSucc_succ_comp_isoGroupHomology_hom`: in
  degrees at most minus two, corestriction is `groupHomology.map` along the inclusion of Galois
  groups.
* `TauCeti.ClassFieldTheory.LayerRestriction.tateCor_trans`: Tate corestriction is functorial
  along a tower of restrictions, in every integer degree.

## References

* E. Artin and J. Tate, *Class Field Theory*, Chapter IV, §6 and Chapter XIV, §4.
* K. S. Brown, *Cohomology of Groups*, Chapter III, §9 and Chapter VI, §5.
-/

public noncomputable section

open CategoryTheory Rep Representation

namespace TauCeti.ClassFieldTheory.LayerRestriction

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [TotallyDisconnectedSpace G] {small big : NormalLayer G}

attribute [local instance] instFintypeRange Subgroup.fintypeQuotientOfFiniteIndex

/-- **Corestriction between the Tate cohomology groups of finite normal layers, in every integer
degree.** Positive degrees use ordinary cohomological corestriction, degrees zero and minus one
use the low-degree norm descriptions, and lower degrees use group-homological corestriction. -/
def tateCor (T : LayerRestriction small big) (F : Formation G) :
    (r : ℤ) → small.TateH F r ⟶ big.TateH F r
  | .ofNat 0 =>
      (T.tateRangeIso F 0).hom ≫
        TauCeti.TateCohomology.H0Cor (big.rep F) T.galHom.range
  | .ofNat (n + 1) =>
      (small.tateHIsoH F (n + 1)).hom ≫ T.cohomologyCor F (n + 1) ≫
        (big.tateHIsoH F (n + 1)).inv
  | .negSucc 0 =>
      (T.tateRangeIso F (-1)).hom ≫
        TauCeti.TateCohomology.HNegOneCor (big.rep F) T.galHom.range
  | .negSucc (n + 1) =>
      (T.tateRangeIso F (Int.negSucc (n + 1))).hom ≫
        TauCeti.TateCohomology.negSuccCor
          (big.rep F) T.galHom.range.subtype (n + 1)

/-- In degree zero, layer Tate corestriction is the range comparison followed by the relative
norm map on degree-zero Tate cohomology. -/
@[simp]
theorem tateCor_zero (T : LayerRestriction small big) (F : Formation G) :
    T.tateCor F 0 = (T.tateRangeIso F 0).hom ≫
      TauCeti.TateCohomology.H0Cor (big.rep F) T.galHom.range :=
  (rfl)

/-- In a positive degree, layer Tate corestriction is ordinary cohomological corestriction read
through the canonical positive-degree comparisons. -/
@[simp]
theorem tateCor_ofNat_succ (T : LayerRestriction small big) (F : Formation G) (n : ℕ) :
    T.tateCor F ((n : ℤ) + 1) =
      (small.tateHIsoH F (n + 1)).hom ≫ T.cohomologyCor F (n + 1) ≫
        (big.tateHIsoH F (n + 1)).inv :=
  (rfl)

/-- Positive-degree Tate corestriction commutes with the canonical comparison to ordinary
cohomology. -/
@[reassoc]
theorem tateCor_comp_tateHIsoH_hom (T : LayerRestriction small big) (F : Formation G)
    (n : ℕ) [NeZero n] :
    T.tateCor F n ≫ (big.tateHIsoH F n).hom =
      (small.tateHIsoH F n).hom ≫ T.cohomologyCor F n := by
  cases n with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ k =>
    simp only [tateCor, Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- In degree minus one, layer Tate corestriction is the range comparison followed by inclusion
of the subgroup norm kernel into the ambient norm kernel. -/
@[simp]
theorem tateCor_neg_one (T : LayerRestriction small big) (F : Formation G) :
    T.tateCor F (-1) = (T.tateRangeIso F (-1)).hom ≫
      TauCeti.TateCohomology.HNegOneCor (big.rep F) T.galHom.range :=
  (rfl)

/-- In degree `-(n+2)`, layer Tate corestriction is the range comparison followed by the
covariant group-homology map in degree `n+1`. -/
@[simp]
theorem tateCor_negSucc_succ (T : LayerRestriction small big) (F : Formation G) (n : ℕ) :
    T.tateCor F (Int.negSucc (n + 1)) =
      (T.tateRangeIso F (Int.negSucc (n + 1))).hom ≫
        TauCeti.TateCohomology.negSuccCor
          (big.rep F) T.galHom.range.subtype (n + 1) :=
  (rfl)

/-- **In degrees at most minus two, layer Tate corestriction is the covariant map on group
homology** along the inclusion of Galois groups, with the canonical identification of coefficients,
read through Mathlib's comparison of Tate cohomology with group homology. -/
@[reassoc]
theorem tateCor_negSucc_succ_comp_isoGroupHomology_hom (T : LayerRestriction small big)
    (F : Formation G) (n : ℕ) :
    T.tateCor F (Int.negSucc (n + 1)) ≫
        (TateCohomology.isoGroupHomology (Int.negSucc (n + 1)) (n + 1)
          (by rw [Int.negSucc_eq])).hom.app (big.rep F) =
      (TateCohomology.isoGroupHomology (Int.negSucc (n + 1)) (n + 1)
          (by rw [Int.negSucc_eq])).hom.app (small.rep F) ≫
        groupHomology.map T.galHom (T.repIso F).hom (n + 1) := by
  rw [tateCor_negSucc_succ, Category.assoc,
    TauCeti.TateCohomology.negSuccCor_comp_isoGroupHomology_hom, tateRangeIso_hom,
    ← Category.assoc, TauCeti.TateCohomology.map_comp_isoGroupHomology_hom]
  -- The comparison with group homology lands in `groupHomology.functor`, whose objects are group
  -- homology only up to unfolding, so the remaining square is composed as a term.
  refine (Category.assoc _ _ _).trans (congrArg (_ ≫ ·) ?_)
  refine (groupHomology.map_comp _ _ _ _ _).symm.trans ?_
  refine groupHomology.map_congr (MonoidHom.ext fun γ ↦ ?_) (LinearMap.ext fun x ↦ ?_) (n + 1)
  · exact MonoidHom.ofInjective_apply T.galHom_injective
  · -- `simp` leaves the two coercions of the coefficient identification to a function, which
    -- agree by definition.
    simp [Representation.equivOfIso]
    rfl

/-- The **inclusion of norm kernels** along a restriction: an element of the top level `A^V` whose
norm for the layer `K/E` vanishes has vanishing norm for the layer `K/F`. It moves no element of
the ambient module (`kerNormInclusion_apply_coe`); on representatives, degree `-1` corestriction is
this inclusion (`tateCor_neg_one_HNegOneπ`). -/
def kerNormInclusion (T : LayerRestriction small big) (F : Formation G) :
    LinearMap.ker (small.rep F).ρ.norm →ₗ[ℤ] LinearMap.ker (big.rep F).ρ.norm :=
  ((T.repIso F).hom.hom.toLinearMap ∘ₗ (LinearMap.ker (small.rep F).ρ.norm).subtype).codRestrict
    (LinearMap.ker (big.rep F).ρ.norm) fun x ↦ by
      have h := (TauCeti.TateCohomology.mapKerNorm (T.isIntertwiningMap_repIso_range F) x).2
      rw [TauCeti.TateCohomology.mapKerNorm_apply_coe] at h
      exact Representation.ker_norm_comp_subtype_le_ker_norm (ρ := (big.rep F).ρ)
        (H := T.galHom.range) h

-- `dsimp% only` on the left-hand side: see the implementation notes of `Formation/Basic.lean`.
/-- The inclusion of norm kernels moves no element of the ambient module. -/
@[simp]
theorem kerNormInclusion_apply_coe (T : LayerRestriction small big) (F : Formation G)
    (x : LinearMap.ker (small.rep F).ρ.norm) :
    (dsimp% only (T.kerNormInclusion F x : F.toRep.V)) = x :=
  T.repIso_hom_apply_coe F x

/-- **In degree minus one, layer Tate corestriction is the inclusion of norm kernels** on
representatives. -/
theorem tateCor_neg_one_HNegOneπ (T : LayerRestriction small big) (F : Formation G)
    (x : LinearMap.ker (small.rep F).ρ.norm) :
    T.tateCor F (-1) (TauCeti.TateCohomology.HNegOneπ (small.rep F) x) =
      TauCeti.TateCohomology.HNegOneπ (big.rep F) (T.kerNormInclusion F x) := by
  rw [tateCor_neg_one, ModuleCat.comp_apply, tateRangeIso_hom,
    TauCeti.TateCohomology.HNegOneπ_comp_map_apply,
    TauCeti.TateCohomology.HNegOneπ_comp_HNegOneCor_apply]
  congr 1
  refine Subtype.ext (Subtype.ext ?_)
  rw [kerNormInclusion_apply_coe, Submodule.coe_inclusion,
    TauCeti.TateCohomology.mapKerNorm_apply_coe (T.isIntertwiningMap_repIso_range F) x]
  exact T.repIso_hom_apply_coe F x

/-- **In degree zero, layer Tate corestriction is the ground-level norm** `N_{U/U'}` on
representatives: the class of an element of the ground level `A^{U'}` of `K/E` goes to the class
of its norm in the ground level `A^U` of `K/F`. -/
theorem tateCor_zero_H0π (T : LayerRestriction small big) (F : Formation G)
    (x : (small.rep F).ρ.invariants) :
    T.tateCor F 0 (TauCeti.TateCohomology.H0π (small.rep F) x) =
      TauCeti.TateCohomology.H0π (big.rep F)
        ((big.groundLevelEquiv F).symm (T.groundNorm F (small.groundLevelEquiv F x))) := by
  rw [tateCor_zero, ModuleCat.comp_apply, tateRangeIso_hom,
    TauCeti.TateCohomology.H0π_comp_map_apply, TauCeti.TateCohomology.H0π_comp_H0Cor_apply]
  congr 1
  refine Subtype.ext (Subtype.ext ?_)
  rw [NormalLayer.groundLevelEquiv_symm_apply_coe, groundNorm_apply_coe,
    Representation.coe_relNormInvariants, Representation.relNorm_apply, Submodule.coe_sum,
    ← finsum_eq_sum_of_fintype]
  -- The cosets of `U'` in `U` are the cosets of the image of `Gal(K/E)` in `Gal(K/F)`.
  have hrel : ∀ a b : big.ground.toSubgroup,
      QuotientGroup.leftRel T.galHom.range (QuotientGroup.mk (s := big.relativeTop) a)
          (QuotientGroup.mk (s := big.relativeTop) b) ↔
        QuotientGroup.leftRel (small.ground.toSubgroup.subgroupOf big.ground.toSubgroup) a b := by
    intro a b
    rw [QuotientGroup.leftRel_apply, QuotientGroup.leftRel_apply, Subgroup.mem_subgroupOf,
      ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul]
    exact T.mk_mem_range_galHom_iff _
  let e : big.ground.toSubgroup ⧸ small.ground.toSubgroup.subgroupOf big.ground.toSubgroup →
      big.Gal ⧸ T.galHom.range :=
    Quotient.map' (QuotientGroup.mk (s := big.relativeTop)) fun a b ↦ (hrel a b).2
  have he : Function.Bijective e := by
    refine ⟨fun p q hpq ↦ ?_, fun p ↦ ?_⟩
    · induction p using Quotient.inductionOn' with | h a => ?_
      induction q using Quotient.inductionOn' with | h b => ?_
      exact Quotient.sound' ((hrel a b).1 (Quotient.exact' hpq))
    · induction p using Quotient.inductionOn' with | h γ => ?_
      induction γ using QuotientGroup.induction_on with | H u => ?_
      exact ⟨Quotient.mk'' u, rfl⟩
  rw [← finsum_comp_equiv (Equiv.ofBijective e he)]
  refine finsum_congr fun q ↦ ?_
  rw [Equiv.ofBijective_apply]
  have hq : e q = QuotientGroup.mk (s := T.galHom.range)
      (QuotientGroup.mk (s := big.relativeTop) q.out) := by
    conv_lhs => rw [← q.out_eq']
    rfl
  rw [Representation.apply_eq_apply_of_quotientGroup_mk_eq
    (TauCeti.TateCohomology.mapInvariants (T.isIntertwiningMap_repIso_range F) x).2
    (a := (e q).out)
    (b := QuotientGroup.mk (s := big.relativeTop) q.out) (by rw [QuotientGroup.out_eq']; exact hq),
    NormalLayer.rep_ρ_mk_apply_coe, TauCeti.TateCohomology.mapInvariants_apply_coe,
    NormalLayer.groundLevelEquiv_apply_coe]
  exact congrArg _ (T.repIso_hom_apply_coe F x)

/-- **In degree zero, corestriction is the ground-level norm on norm quotients.** Read through the
identification of degree-zero Tate cohomology with the norm quotient, corestricting the class of
an element of the ground level `A^{U'}` of `K/E` gives the class of its norm `N_{U/U'}` in the
ground level `A^U` of `K/F`. -/
theorem tateHZeroEquivNormQuotient_tateCor_H0π (T : LayerRestriction small big) (F : Formation G)
    (x : (small.rep F).ρ.invariants) :
    big.tateHZeroEquivNormQuotient F (T.tateCor F 0 (TauCeti.TateCohomology.H0π (small.rep F) x)) =
      big.normQuotientMk F (T.groundNorm F (small.groundLevelEquiv F x)) := by
  rw [tateCor_zero_H0π, NormalLayer.tateHZeroEquivNormQuotient_H0π, LinearEquiv.apply_symm_apply]

/-! ### Towers -/

section Towers

variable {a b c : NormalLayer G}

/-- **Tate corestriction is functorial along a tower of restrictions, in every integer degree.**
Corestricting from `K/E'` to `K/E` and then to `K/F` is corestricting from `K/E'` to `K/F`. -/
theorem tateCor_trans (T : LayerRestriction a b) (T' : LayerRestriction b c) (F : Formation G)
    (r : ℤ) : (T.trans T').tateCor F r = T.tateCor F r ≫ T'.tateCor F r := by
  obtain ⟨n, rfl⟩ | rfl | rfl | ⟨n, rfl⟩ :
      (∃ n : ℕ, r = n + 1) ∨ r = 0 ∨ r = -1 ∨ ∃ n : ℕ, r = Int.negSucc (n + 1) := by
    rcases r with (_ | n) | (_ | n)
    · exact .inr (.inl rfl)
    · exact .inl ⟨n, rfl⟩
    · exact .inr (.inr (.inl rfl))
    · exact .inr (.inr (.inr ⟨n, rfl⟩))
  · rw [tateCor_ofNat_succ, tateCor_ofNat_succ, tateCor_ofNat_succ,
      cohomologyCor_trans T T']
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
  · ext x
    induction x using TauCeti.TateCohomology.H0_induction_on with | h y => ?_
    rw [ModuleCat.comp_apply, tateCor_zero_H0π, tateCor_zero_H0π, tateCor_zero_H0π,
      LinearEquiv.apply_symm_apply, groundNorm_trans T T', AddMonoidHom.comp_apply]
  · ext x
    induction x using TauCeti.TateCohomology.HNegOne_induction_on with | h y => ?_
    rw [ModuleCat.comp_apply, tateCor_neg_one_HNegOneπ, tateCor_neg_one_HNegOneπ,
      tateCor_neg_one_HNegOneπ]
    congr 1
    refine Subtype.ext (Subtype.ext ?_)
    rw [kerNormInclusion_apply_coe, kerNormInclusion_apply_coe, kerNormInclusion_apply_coe]
  · rw [← cancel_mono ((TateCohomology.isoGroupHomology (Int.negSucc (n + 1)) (n + 1)
      (by rw [Int.negSucc_eq])).hom.app (c.rep F)), Category.assoc,
      tateCor_negSucc_succ_comp_isoGroupHomology_hom,
      tateCor_negSucc_succ_comp_isoGroupHomology_hom (T := T')]
    have hmap : groupHomology.map (T.trans T').galHom ((T.trans T').repIso F).hom (n + 1) =
        groupHomology.map T.galHom (T.repIso F).hom (n + 1) ≫
          groupHomology.map T'.galHom (T'.repIso F).hom (n + 1) := by
      rw [← groupHomology.map_comp]
      refine groupHomology.map_congr (galHom_trans T T') (LinearMap.ext fun x ↦ Subtype.ext ?_)
        (n + 1)
      exact ((T.trans T').repIso_hom_apply_coe F x).trans
        ((T'.repIso_hom_apply_coe F _).trans (T.repIso_hom_apply_coe F x)).symm
    -- The comparison with group homology lands in `groupHomology.functor`, whose objects are group
    -- homology only up to unfolding, so the squares are composed as terms.
    refine (congrArg (_ ≫ ·) hmap).trans ((Category.assoc _ _ _).symm.trans ?_)
    exact (congrArg (· ≫ _)
      (T.tateCor_negSucc_succ_comp_isoGroupHomology_hom F n).symm).trans (Category.assoc _ _ _)

end Towers

/-! ### Trivial coefficients -/

/-- **Corestriction on the Tate cohomology of finite normal layers with trivial integral
coefficients, in every integer degree.** It uses cohomological corestriction in positive degrees,
the low-degree norm maps in degrees zero and minus one, and homological corestriction below them. -/
def trivialTateCor (T : LayerRestriction small big) :
    (r : ℤ) → small.TrivialTateH r ⟶ big.TrivialTateH r
  | .ofNat 0 =>
      (T.trivialTateRangeIso 0).hom ≫
        TauCeti.TateCohomology.H0Cor (Rep.trivial ℤ big.Gal ℤ) T.galHom.range
  | .ofNat (n + 1) =>
      (T.trivialTateRangeIso (n + 1)).hom ≫
        (TateCohomology.isoGroupCohomology (n + 1)).hom.app
          (Rep.res T.galHom.range.subtype (Rep.trivial ℤ big.Gal ℤ)) ≫
        TauCeti.groupCohomology.corestriction
          T.galHom.range (Rep.trivial ℤ big.Gal ℤ) (n + 1) ≫
        (TateCohomology.isoGroupCohomology (n + 1)).inv.app
          (Rep.trivial ℤ big.Gal ℤ)
  | .negSucc 0 =>
      (T.trivialTateRangeIso (-1)).hom ≫
        TauCeti.TateCohomology.HNegOneCor (Rep.trivial ℤ big.Gal ℤ) T.galHom.range
  | .negSucc (n + 1) =>
      (T.trivialTateRangeIso (Int.negSucc (n + 1))).hom ≫
        TauCeti.TateCohomology.negSuccCor
          (Rep.trivial ℤ big.Gal ℤ) T.galHom.range.subtype (n + 1)

/-- In degree zero, trivial-coefficient Tate corestriction is the range comparison followed by
the relative norm map. -/
@[simp]
theorem trivialTateCor_zero (T : LayerRestriction small big) :
    T.trivialTateCor 0 = (T.trivialTateRangeIso 0).hom ≫
      TauCeti.TateCohomology.H0Cor (Rep.trivial ℤ big.Gal ℤ) T.galHom.range :=
  (rfl)

/-- In a positive degree, trivial-coefficient Tate corestriction is ordinary cohomological
corestriction after identifying the smaller Galois group with its image. -/
@[simp]
theorem trivialTateCor_ofNat_succ (T : LayerRestriction small big) (n : ℕ) :
    T.trivialTateCor ((n : ℤ) + 1) =
      (T.trivialTateRangeIso (n + 1)).hom ≫
        (TateCohomology.isoGroupCohomology (n + 1)).hom.app
          (Rep.res T.galHom.range.subtype (Rep.trivial ℤ big.Gal ℤ)) ≫
        TauCeti.groupCohomology.corestriction
          T.galHom.range (Rep.trivial ℤ big.Gal ℤ) (n + 1) ≫
        (TateCohomology.isoGroupCohomology (n + 1)).inv.app
          (Rep.trivial ℤ big.Gal ℤ) :=
  (rfl)

/-- Positive-degree trivial-coefficient Tate corestriction commutes with Mathlib's canonical
comparison to ordinary cohomology. -/
@[reassoc]
theorem trivialTateCor_comp_isoGroupCohomology_hom (T : LayerRestriction small big)
    (n : ℕ) [NeZero n] :
    T.trivialTateCor n ≫
        (TateCohomology.isoGroupCohomology n).hom.app (Rep.trivial ℤ big.Gal ℤ) =
      (T.trivialTateRangeIso n).hom ≫
        (TateCohomology.isoGroupCohomology n).hom.app
          (Rep.res T.galHom.range.subtype (Rep.trivial ℤ big.Gal ℤ)) ≫
        TauCeti.groupCohomology.corestriction
          T.galHom.range (Rep.trivial ℤ big.Gal ℤ) n := by
  cases n with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ k =>
    simp only [trivialTateCor]
    -- Peel off the semireducible group-cohomology carrier before cancelling the comparison iso;
    -- `simp`/`rw` cannot match through that carrier, so the cancellation is applied as a term.
    rw [Category.assoc, Category.assoc]
    congr 2
    exact (Category.assoc _ _ _).trans
      ((congrArg _ (Iso.inv_hom_id_app _ _)).trans (Category.comp_id _))

/-- In degree minus one, trivial-coefficient Tate corestriction is the range comparison followed
by inclusion of norm kernels. -/
@[simp]
theorem trivialTateCor_neg_one (T : LayerRestriction small big) :
    T.trivialTateCor (-1) = (T.trivialTateRangeIso (-1)).hom ≫
      TauCeti.TateCohomology.HNegOneCor (Rep.trivial ℤ big.Gal ℤ) T.galHom.range :=
  (rfl)

/-- In degree `-(n+2)`, trivial-coefficient Tate corestriction is the range comparison followed
by the covariant group-homology map in degree `n+1`. -/
@[simp]
theorem trivialTateCor_negSucc_succ (T : LayerRestriction small big) (n : ℕ) :
    T.trivialTateCor (Int.negSucc (n + 1)) =
      (T.trivialTateRangeIso (Int.negSucc (n + 1))).hom ≫
        TauCeti.TateCohomology.negSuccCor
          (Rep.trivial ℤ big.Gal ℤ) T.galHom.range.subtype (n + 1) :=
  (rfl)

end TauCeti.ClassFieldTheory.LayerRestriction
