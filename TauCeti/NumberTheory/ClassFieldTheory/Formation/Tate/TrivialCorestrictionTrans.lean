/-
Copyright (c) 2026 Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.NumberTheory.ClassFieldTheory.Formation.Tate.Corestriction

/-!
# Corestriction of trivial coefficients in a tower

For a tower of finite normal layers, corestriction on integral Tate cohomology composes in every
integer degree. This supplies the trivial-coefficient side of the tower compatibility used by
the Tate isomorphism of a class formation.

In positive degrees these maps agree with ordinary group-cohomology corestriction, and below
degree minus one with group-homology maps. In degree zero the map is the relative norm, while
degree minus one vanishes for integral coefficients.

## References

* E. Artin and J. Tate, *Class Field Theory*, Chapter XIV, §§2–4.
* K. S. Brown, *Cohomology of Groups*, Chapter III, §9.
-/

public noncomputable section

open CategoryTheory

namespace TauCeti.ClassFieldTheory.LayerRestriction

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [TotallyDisconnectedSpace G] {a b c : NormalLayer G}

private def trivialCohomologyCor {small big : NormalLayer G}
    (T : LayerRestriction small big) (n : ℕ) :
    groupCohomology (Rep.trivial ℤ small.Gal ℤ) n ⟶
      groupCohomology (Rep.trivial ℤ big.Gal ℤ) n :=
  (groupCohomology.mapIso
    (B := Rep.trivial ℤ small.Gal ℤ)
    (A := Rep.res T.galHom.range.subtype (Rep.trivial ℤ big.Gal ℤ))
    (MonoidHom.ofInjective T.galHom_injective) (LinearEquiv.refl ℤ ℤ)
    (fun _ ↦ LinearMap.ext fun _ ↦ rfl) n).hom ≫
    TauCeti.groupCohomology.corestriction T.galHom.range (Rep.trivial ℤ big.Gal ℤ) n

private theorem trivialCohomologyCor_trans (T : LayerRestriction a b)
    (T' : LayerRestriction b c) (n : ℕ) :
    trivialCohomologyCor (T.trans T') n =
      trivialCohomologyCor T n ≫ trivialCohomologyCor T' n := by
  have key := (TauCeti.groupCohomology.corestriction_trans T.galHom_injective
      T'.galHom_injective (T.galHom_trans T').symm (Rep.trivial ℤ c.Gal ℤ) n).symm
  -- Restriction of a trivial representation is definitionally trivial, so the general
  -- corestriction law has this type after expanding the local map abbreviation.
  unfold trivialCohomologyCor
  exact key

private theorem homCongr_trivialTateCor {small big : NormalLayer G}
    (T : LayerRestriction small big) (n : ℕ) [NeZero n] :
    ((TateCohomology.isoGroupCohomology n).app (Rep.trivial ℤ small.Gal ℤ)).homCongr
        ((TateCohomology.isoGroupCohomology n).app (Rep.trivial ℤ big.Gal ℤ))
        (T.trivialTateCor n) =
      trivialCohomologyCor T n := by
  let : Fintype T.galHom.range := Fintype.ofFinite _
  rw [Iso.homCongr_apply]
  refine (Iso.inv_comp_eq ((TateCohomology.isoGroupCohomology n).app _)).2 ?_
  have h := T.trivialTateRangeIso_hom_comp_isoGroupCohomology_hom n
  have hcor := congrArg
    (fun f ↦ f ≫ TauCeti.groupCohomology.corestriction T.galHom.range
      (Rep.trivial ℤ big.Gal ℤ) n) h
  exact (T.trivialTateCor_comp_isoGroupCohomology_hom n).trans
    ((Category.assoc _ _ _).symm.trans (hcor.trans (Category.assoc _ _ _)))

private def trivialCoeffHom {small big : NormalLayer G} (T : LayerRestriction small big) :
    Rep.trivial ℤ small.Gal ℤ ⟶ Rep.res T.galHom (Rep.trivial ℤ big.Gal ℤ) :=
  Rep.ofHom ⟨LinearMap.id, fun _ ↦ LinearMap.ext fun _ ↦ rfl⟩

private def trivialHomologyCor {small big : NormalLayer G}
    (T : LayerRestriction small big) (n : ℕ) :
    groupHomology (Rep.trivial ℤ small.Gal ℤ) n ⟶
      groupHomology (Rep.trivial ℤ big.Gal ℤ) n :=
  groupHomology.map T.galHom (trivialCoeffHom T) n

private theorem trivialHomologyCor_trans (T : LayerRestriction a b)
    (T' : LayerRestriction b c) (n : ℕ) :
    trivialHomologyCor (T.trans T') n =
      trivialHomologyCor T n ≫ trivialHomologyCor T' n := by
  rw [trivialHomologyCor, trivialHomologyCor, trivialHomologyCor,
    ← groupHomology.map_comp]
  apply groupHomology.map_congr (galHom_trans T T') _ n
  ext
  rfl

private theorem homCongr_trivialTateCor_negSucc {small big : NormalLayer G}
    (T : LayerRestriction small big) (n : ℕ) :
    ((TateCohomology.isoGroupHomology (Int.negSucc (n + 1)) (n + 1)
          (by rw [Int.negSucc_eq])).app (Rep.trivial ℤ small.Gal ℤ)).homCongr
        ((TateCohomology.isoGroupHomology (Int.negSucc (n + 1)) (n + 1)
          (by rw [Int.negSucc_eq])).app (Rep.trivial ℤ big.Gal ℤ))
        (T.trivialTateCor (Int.negSucc (n + 1))) =
      trivialHomologyCor T (n + 1) := by
  let : Fintype T.galHom.range := Fintype.ofFinite _
  rw [Iso.homCongr_apply]
  refine (Iso.inv_comp_eq ((TateCohomology.isoGroupHomology (Int.negSucc (n + 1)) (n + 1)
    (by rw [Int.negSucc_eq])).app _)).2 ?_
  rw [Iso.app_hom, Iso.app_hom, trivialTateCor_negSucc_succ, Category.assoc,
    TauCeti.TateCohomology.negSuccCor_comp_isoGroupHomology_hom]
  have h := T.trivialTateRangeIso_hom_comp_isoGroupHomology_hom n
  have hcor := congrArg
    (fun f ↦ f ≫ (groupHomology.coresNatTrans ℤ T.galHom.range.subtype (n + 1)).app
      (Rep.trivial ℤ big.Gal ℤ)) h
  have hmap : groupHomology.map (MonoidHom.ofInjective T.galHom_injective)
        T.trivialRangeRepHom (n + 1) ≫
        (groupHomology.coresNatTrans ℤ T.galHom.range.subtype (n + 1)).app
          (Rep.trivial ℤ big.Gal ℤ) = trivialHomologyCor T (n + 1) := by
    rw [groupHomology.coresNatTrans_app]
    refine (groupHomology.map_comp (MonoidHom.ofInjective T.galHom_injective)
      T.galHom.range.subtype T.trivialRangeRepHom
      (𝟙 (Rep.res T.galHom.range.subtype (Rep.trivial ℤ big.Gal ℤ))) (n + 1)).symm.trans ?_
    rw [trivialHomologyCor]
    apply groupHomology.map_congr _ _ (n + 1)
    · ext x
      exact MonoidHom.ofInjective_apply T.galHom_injective
    · ext
      exact T.trivialRangeRepHom_apply 1
  refine (Category.assoc _ _ _).symm.trans (hcor.trans ?_)
  exact (Category.assoc _ _ _).trans (congrArg (_ ≫ ·) hmap)

/-- Trivial-coefficient Tate corestriction is functorial in towers of finite normal layers. -/
theorem trivialTateCor_trans (T : LayerRestriction a b)
    (T' : LayerRestriction b c) (r : ℤ) :
    (T.trans T').trivialTateCor r = T.trivialTateCor r ≫ T'.trivialTateCor r := by
  -- The four cases use ordinary cohomology, the norm quotient, the vanishing of degree minus
  -- one for integral coefficients, and ordinary homology, respectively.
  obtain ⟨n, rfl⟩ | rfl | rfl | ⟨n, rfl⟩ :
      (∃ n : ℕ, r = n + 1) ∨ r = 0 ∨ r = -1 ∨ ∃ n : ℕ, r = Int.negSucc (n + 1) := by
    rcases r with (_ | n) | (_ | n)
    · exact .inr (.inl rfl)
    · exact .inl ⟨n, rfl⟩
    · exact .inr (.inr (.inl rfl))
    · exact .inr (.inr (.inr ⟨n, rfl⟩))
  · have : NeZero (n + 1) := ⟨Nat.succ_ne_zero n⟩
    have hn : (n : ℤ) + 1 = ((n + 1 : ℕ) : ℤ) := by omega
    rw [hn]
    apply ((TateCohomology.isoGroupCohomology (n + 1)).app (Rep.trivial ℤ a.Gal ℤ)).homCongr
      ((TateCohomology.isoGroupCohomology (n + 1)).app (Rep.trivial ℤ c.Gal ℤ)) |>.injective
    rw [Iso.homCongr_comp _
        ((TateCohomology.isoGroupCohomology (n + 1)).app (Rep.trivial ℤ b.Gal ℤ)),
      homCongr_trivialTateCor, homCongr_trivialTateCor, homCongr_trivialTateCor]
    exact trivialCohomologyCor_trans T T' (n + 1)
  · ext x
    induction x using TauCeti.TateCohomology.H0_induction_on with | h y => ?_
    rw [ModuleCat.comp_apply, trivialTateCor_zero_H0π,
      trivialTateCor_zero_H0π, trivialTateCor_zero_H0π]
    congr 1
    apply Subtype.ext
    rw [relativeDegree_trans T T']
    push_cast
    ring
  · have : Subsingleton (c.TrivialTateH (-1)) :=
      TauCeti.TateCohomology.subsingleton_tateCohomology_negOne_trivial_int c.Gal
    ext x
    exact Subsingleton.elim _ _
  · apply ((TateCohomology.isoGroupHomology (Int.negSucc (n + 1)) (n + 1)
        (by rw [Int.negSucc_eq])).app (Rep.trivial ℤ a.Gal ℤ)).homCongr
      ((TateCohomology.isoGroupHomology (Int.negSucc (n + 1)) (n + 1)
        (by rw [Int.negSucc_eq])).app (Rep.trivial ℤ c.Gal ℤ)) |>.injective
    rw [Iso.homCongr_comp _
        ((TateCohomology.isoGroupHomology (Int.negSucc (n + 1)) (n + 1)
          (by rw [Int.negSucc_eq])).app (Rep.trivial ℤ b.Gal ℤ)),
      homCongr_trivialTateCor_negSucc, homCongr_trivialTateCor_negSucc,
      homCongr_trivialTateCor_negSucc]
    exact trivialHomologyCor_trans T T' (n + 1)

end TauCeti.ClassFieldTheory.LayerRestriction
