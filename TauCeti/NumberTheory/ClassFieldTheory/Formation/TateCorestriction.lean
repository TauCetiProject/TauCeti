/-
Copyright (c) 2026 Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.NumberTheory.ClassFieldTheory.Formation.Corestriction
public import TauCeti.RepresentationTheory.Homological.TateCohomology.Functoriality
public import TauCeti.RepresentationTheory.Homological.TateCohomology.NegativeCorestriction
public import TauCeti.RepresentationTheory.Homological.TateCohomology.Restriction

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
allow consumers to use Tate corestriction without unfolding its integer-degree case split.

## References

* E. Artin and J. Tate, *Class Field Theory*, Chapter IV, §6 and Chapter XIV, §4.
* K. S. Brown, *Cohomology of Groups*, Chapter III, §9 and Chapter VI, §5.
-/

public noncomputable section

open CategoryTheory Rep Representation

namespace TauCeti.ClassFieldTheory.LayerRestriction

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [TotallyDisconnectedSpace G] {small big : NormalLayer G}

noncomputable local instance instFintypeRange (T : LayerRestriction small big) :
    Fintype T.galHom.range :=
  Fintype.ofFinite _

private theorem repIso_isIntertwiningRange (T : LayerRestriction small big) (F : Formation G) :
    (small.rep F).ρ.IsIntertwiningMap
      ((Rep.res T.galHom.range.subtype (big.rep F)).ρ.comp
        (MonoidHom.ofInjective T.galHom_injective : small.Gal ≃* T.galHom.range))
      (Representation.equivOfIso (T.repIso F)).toLinearEquiv := by
  refine ⟨fun g x ↦ ?_⟩
  exact Rep.hom_comm_apply (T.repIso F).hom g x

/-- Tate cohomology of the smaller layer, identified with Tate cohomology of the image of its
Galois group in the larger one. The coefficient identification is `repIso`. -/
def tateRangeIso (T : LayerRestriction small big) (F : Formation G) (r : ℤ) :
    small.TateH F r ≅
      tateCohomology (Rep.res T.galHom.range.subtype (big.rep F)) r :=
  TauCeti.TateCohomology.mapIso
    (M := small.rep F)
    (N := Rep.res T.galHom.range.subtype (big.rep F))
    (e := MonoidHom.ofInjective T.galHom_injective)
    (e' := (Representation.equivOfIso (T.repIso F)).toLinearEquiv)
    (repIso_isIntertwiningRange T F) r

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
theorem tateCor_zero (T : LayerRestriction small big) (F : Formation G) :
    T.tateCor F 0 = (T.tateRangeIso F 0).hom ≫
      TauCeti.TateCohomology.H0Cor (big.rep F) T.galHom.range :=
  (rfl)

/-- In a positive degree, layer Tate corestriction is ordinary cohomological corestriction read
through the canonical positive-degree comparisons. -/
theorem tateCor_ofNat_succ (T : LayerRestriction small big) (F : Formation G) (n : ℕ) :
    T.tateCor F (Int.ofNat (n + 1)) =
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
theorem tateCor_neg_one (T : LayerRestriction small big) (F : Formation G) :
    T.tateCor F (-1) = (T.tateRangeIso F (-1)).hom ≫
      TauCeti.TateCohomology.HNegOneCor (big.rep F) T.galHom.range :=
  (rfl)

/-- In degree `-(n+2)`, layer Tate corestriction is the range comparison followed by the
covariant group-homology map in degree `n+1`. -/
theorem tateCor_negSucc_succ (T : LayerRestriction small big) (F : Formation G) (n : ℕ) :
    T.tateCor F (Int.negSucc (n + 1)) =
      (T.tateRangeIso F (Int.negSucc (n + 1))).hom ≫
        TauCeti.TateCohomology.negSuccCor
          (big.rep F) T.galHom.range.subtype (n + 1) :=
  (rfl)

/-! ### Trivial coefficients -/

private theorem trivial_isIntertwiningRange (T : LayerRestriction small big) :
    Representation.IsIntertwiningMap (Rep.trivial ℤ small.Gal ℤ).ρ
      ((Rep.res T.galHom.range.subtype (Rep.trivial ℤ big.Gal ℤ)).ρ.comp
        (MonoidHom.ofInjective T.galHom_injective : small.Gal ≃* T.galHom.range))
      (LinearEquiv.refl ℤ ℤ) :=
  ⟨fun _ _ ↦ rfl⟩

/-- Tate cohomology with trivial integral coefficients on the smaller Galois group, identified
with the restriction of the trivial representation on the larger Galois group to the image of
the inclusion. -/
def trivialTateRangeIso (T : LayerRestriction small big) (r : ℤ) :
    small.TrivialTateH r ≅
      tateCohomology (Rep.res T.galHom.range.subtype (Rep.trivial ℤ big.Gal ℤ)) r :=
  TauCeti.TateCohomology.mapIso
    (M := Rep.trivial ℤ small.Gal ℤ)
    (N := Rep.res T.galHom.range.subtype (Rep.trivial ℤ big.Gal ℤ))
    (e := MonoidHom.ofInjective T.galHom_injective)
    (e' := LinearEquiv.refl ℤ ℤ)
    (trivial_isIntertwiningRange T) r

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
theorem trivialTateCor_zero (T : LayerRestriction small big) :
    T.trivialTateCor 0 = (T.trivialTateRangeIso 0).hom ≫
      TauCeti.TateCohomology.H0Cor (Rep.trivial ℤ big.Gal ℤ) T.galHom.range :=
  (rfl)

/-- In a positive degree, trivial-coefficient Tate corestriction is ordinary cohomological
corestriction after identifying the smaller Galois group with its image. -/
theorem trivialTateCor_ofNat_succ (T : LayerRestriction small big) (n : ℕ) :
    T.trivialTateCor (Int.ofNat (n + 1)) =
      (T.trivialTateRangeIso (n + 1)).hom ≫
        (TateCohomology.isoGroupCohomology (n + 1)).hom.app
          (Rep.res T.galHom.range.subtype (Rep.trivial ℤ big.Gal ℤ)) ≫
        TauCeti.groupCohomology.corestriction
          T.galHom.range (Rep.trivial ℤ big.Gal ℤ) (n + 1) ≫
        (TateCohomology.isoGroupCohomology (n + 1)).inv.app
          (Rep.trivial ℤ big.Gal ℤ) :=
  (rfl)

/-- In degree minus one, trivial-coefficient Tate corestriction is the range comparison followed
by inclusion of norm kernels. -/
theorem trivialTateCor_neg_one (T : LayerRestriction small big) :
    T.trivialTateCor (-1) = (T.trivialTateRangeIso (-1)).hom ≫
      TauCeti.TateCohomology.HNegOneCor (Rep.trivial ℤ big.Gal ℤ) T.galHom.range :=
  (rfl)

/-- In degree `-(n+2)`, trivial-coefficient Tate corestriction is the range comparison followed
by the covariant group-homology map in degree `n+1`. -/
theorem trivialTateCor_negSucc_succ (T : LayerRestriction small big) (n : ℕ) :
    T.trivialTateCor (Int.negSucc (n + 1)) =
      (T.trivialTateRangeIso (Int.negSucc (n + 1))).hom ≫
        TauCeti.TateCohomology.negSuccCor
          (Rep.trivial ℤ big.Gal ℤ) T.galHom.range.subtype (n + 1) :=
  (rfl)

end TauCeti.ClassFieldTheory.LayerRestriction
