/-
Copyright (c) 2026 Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import TauCeti.NumberTheory.ClassFieldTheory.Formation.Tate.Restriction
import TauCeti.RepresentationTheory.Homological.TateCohomology.Restriction.Trans

/-!
# Restriction of trivial coefficients in a tower

For a tower of finite normal layers, restriction on integral Tate cohomology composes in every
integer degree. This supplies the trivial-coefficient side of the tower compatibility used by
the Tate isomorphism of a class formation.

In positive degrees these maps agree with ordinary group-cohomology restriction along the
inclusion of Galois groups, and below degree minus one with the transfer in group homology. In
degree zero the map is the identity on integral representatives, while degree minus one vanishes
for integral coefficients.

## Main results

* `TauCeti.ClassFieldTheory.LayerRestriction.trivialTateRes_trans`: trivial-coefficient Tate
  restriction is functorial along a tower of restrictions, in every integer degree.

## Implementation notes

The case split by degree follows the corestriction counterpart
`LayerRestriction.trivialTateCor_trans` in `Formation/Tate/TrivialCorestrictionTrans.lean`. Below
degree minus one the argument follows `tateRes_negSucc_succ_trans` in
`Formation/Tate/Restriction.lean`, the same step with formation coefficients.

## References

* E. Artin and J. Tate, *Class Field Theory*, Chapter XIV, §§2–4.
* K. S. Brown, *Cohomology of Groups*, Chapter III, §9.
-/

public noncomputable section

open CategoryTheory

namespace TauCeti.ClassFieldTheory.LayerRestriction

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [TotallyDisconnectedSpace G] {a b c : NormalLayer G}

attribute [local instance] instFintypeRange

/-! ### Positive degrees -/

private def trivialCohomologyRes {small big : NormalLayer G} (T : LayerRestriction small big)
    (n : ℕ) :
    groupCohomology (Rep.trivial ℤ big.Gal ℤ) n ⟶ groupCohomology (Rep.trivial ℤ small.Gal ℤ) n :=
  -- Restricting the trivial representation gives the trivial one on the nose, so the coefficient
  -- map is `eqToHom rfl`.
  groupCohomology.map T.galHom (eqToHom rfl) n

private theorem trivialCohomologyRes_trans (T : LayerRestriction a b) (T' : LayerRestriction b c)
    (n : ℕ) : trivialCohomologyRes (T.trans T') n =
      trivialCohomologyRes T' n ≫ trivialCohomologyRes T n :=
  (groupCohomology.map_congr (T.galHom_trans T') rfl n).trans (groupCohomology.map_comp ..)

@[reassoc]
private theorem trivialTateRes_comp_isoGroupCohomology_hom_eq_trivialCohomologyRes
    {small big : NormalLayer G} (T : LayerRestriction small big) (n : ℕ) [NeZero n] :
    T.trivialTateRes n ≫
        (TateCohomology.isoGroupCohomology n).hom.app (Rep.trivial ℤ small.Gal ℤ) =
      (TateCohomology.isoGroupCohomology n).hom.app (Rep.trivial ℤ big.Gal ℤ) ≫
        trivialCohomologyRes T n :=
  -- The square for `trivialTateRes` lands in the cohomology of the image subgroup; the range
  -- comparison carries it back to the smaller Galois group, and `map_comp` merges the two maps.
  ((Iso.eq_comp_inv _).2 <| (Category.assoc ..).trans <|
      (congrArg _ (T.trivialTateRangeIso_hom_comp_isoGroupCohomology_hom n).symm).trans
        (T.trivialTateRes_comp_isoGroupCohomology_hom n)).trans <|
    (Category.assoc ..).trans <| congrArg _ (groupCohomology.map_comp ..).symm

/-! ### Degrees below minus one -/

attribute [local instance] Subgroup.fintypeOfFinite in
private theorem trivialTateRes_negSucc_succ_trans (T : LayerRestriction a b)
    (T' : LayerRestriction b c) (n : ℕ) : (T.trans T').trivialTateRes (Int.negSucc (n + 1)) =
      T'.trivialTateRes (Int.negSucc (n + 1)) ≫ T.trivialTateRes (Int.negSucc (n + 1)) := by
  simp only [trivialTateRes_negSucc_succ, Category.assoc]
  -- The transfer is transitive along the image of the tower of Galois groups...
  rw [← TauCeti.TateCohomology.negSuccRes_trans_assoc _ (galHom_range_trans_le T T')]
  refine congrArg (_ ≫ ·) ((Iso.eq_inv_comp _).2 ?_)
  -- ...and compatible with the identification of the middle Galois group with its image.
  simp only [trivialTateRangeIso_hom,
    TauCeti.TateCohomology.map_comp_negSuccRes_assoc _ (MonoidHom.ofInjective T'.galHom_injective) _
      (galHom_range_map_ofInjective T T') (n + 1)]
  refine congrArg (_ ≫ ·) ?_
  -- It remains to compose the identifications of Galois groups and coefficients along the tower.
  -- (`simp only`, not `rw`: rewriting with `trivialTateRangeIso_hom` is far slower here.)
  simp only [TauCeti.TateCohomology.map_comp_assoc, Iso.comp_inv_eq, Iso.eq_inv_comp,
    trivialTateRangeIso_hom, TauCeti.TateCohomology.map_comp]
  -- The coefficient maps are all the identity, so only the Galois groups need comparing.
  refine TauCeti.TateCohomology.map_congr (MulEquiv.ext fun γ ↦ Subtype.ext ?_) rfl _
  simp [MonoidHom.ofInjective_apply, galHom_trans T T']

-- The positive degrees of `trivialTateRes_trans`, where restriction is group-cohomology
-- restriction along the inclusion of Galois groups.
private theorem trivialTateRes_natCast_trans (T : LayerRestriction a b) (T' : LayerRestriction b c)
    (n : ℕ) [NeZero n] :
    (T.trans T').trivialTateRes n = T'.trivialTateRes n ≫ T.trivialTateRes n := by
  rw [← cancel_mono ((TateCohomology.isoGroupCohomology n).hom.app (Rep.trivial ℤ a.Gal ℤ)),
    Category.assoc, trivialTateRes_comp_isoGroupCohomology_hom_eq_trivialCohomologyRes,
    trivialTateRes_comp_isoGroupCohomology_hom_eq_trivialCohomologyRes,
    trivialCohomologyRes_trans T T']
  exact (trivialTateRes_comp_isoGroupCohomology_hom_eq_trivialCohomologyRes_assoc T' n _).symm

/-- **Trivial-coefficient Tate restriction is functorial along a tower of restrictions**, in every
integer degree. For fields `F ⊆ E ⊆ E' ⊆ K`, with `T'` restricting `K/F` to `K/E` and `T`
restricting `K/E` to `K/E'`, restricting Tate cohomology with trivial integral coefficients
directly from `K/F` to `K/E'` agrees with restricting from `K/F` to `K/E` and then to `K/E'`.

This is the trivial-coefficient counterpart of `tateRes_trans_eq_comp`. -/
-- Not `@[simp]`: `LayerRestriction` is a `Prop`, so the left-hand side does not mention `T`, `T'`
-- or the middle layer, and `simp` could never instantiate them.
@[reassoc]
theorem trivialTateRes_trans (T : LayerRestriction a b) (T' : LayerRestriction b c) (r : ℤ) :
    (T.trans T').trivialTateRes r = T'.trivialTateRes r ≫ T.trivialTateRes r := by
  match r with
  | 0 =>
    -- In degree zero, restriction is the identity on integral representatives.
    ext x
    induction x using TauCeti.TateCohomology.H0_induction_on with
    | h y =>
      rw [ModuleCat.comp_apply, trivialTateRes_zero_H0π, trivialTateRes_zero_H0π,
        trivialTateRes_zero_H0π]
  | (n + 1 : ℕ) => exact trivialTateRes_natCast_trans T T' (n + 1)
  | -1 =>
    -- Degree minus one vanishes for integral coefficients.
    ext x
    exact (TauCeti.TateCohomology.subsingleton_tateCohomology_negOne_trivial_int a.Gal).elim _ _
  | .negSucc (n + 1) => exact trivialTateRes_negSucc_succ_trans T T' n

end TauCeti.ClassFieldTheory.LayerRestriction
