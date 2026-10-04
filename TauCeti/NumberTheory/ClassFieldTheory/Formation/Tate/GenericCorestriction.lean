/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.NumberTheory.ClassFieldTheory.Formation.Tate.Corestriction
public import TauCeti.RepresentationTheory.Homological.TateCohomology.Restriction.AllDegrees

/-!
# Finite-layer corestriction and generic Tate corestriction

The corestriction maps of finite normal layers agree, in every integer degree, with generic
subgroup corestriction after the range comparison identifying the smaller Galois group with
its image in the larger one. This holds both for formation coefficients and for trivial
integral coefficients.

These comparisons let the generic Tate cup-product projection formula apply to the existing
finite-layer maps, for use in establishing compatibility of finite-layer Tate isomorphisms
with corestriction and norm compatibility of Artin maps.

## References

* E. Artin and J. Tate, *Class Field Theory*, Chapter XIV, §4.
* K. S. Brown, *Cohomology of Groups*, Chapter III, §9 and Chapter VI, §5.
-/

public noncomputable section

open CategoryTheory Rep

namespace TauCeti.ClassFieldTheory.LayerRestriction

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [TotallyDisconnectedSpace G] {small big : NormalLayer G}

attribute [local instance] Subgroup.fintypeOfFinite Subgroup.fintypeQuotientOfFiniteIndex

-- The proofs follow the corresponding restriction comparisons in
-- TauCeti.NumberTheory.ClassFieldTheory.Formation.Tate.Restriction.

/-- Layer Tate corestriction is the range comparison followed by generic subgroup corestriction,
in every integer degree. The subgroup carrier uses `Subgroup.fintypeOfFinite`, as fixed by the
generic map `TauCeti.TateCohomology.cor`. -/
@[reassoc]
theorem tateCor_eq_cor (T : LayerRestriction small big) (F : Formation G) (r : ℤ) :
    T.tateCor F r = (T.tateRangeIso F r).hom ≫
      TauCeti.TateCohomology.cor (big.rep F) T.galHom.range r := by
  cases r with
  | ofNat n =>
    cases n with
    | zero => simp
    | succ n =>
      simp only [Int.ofNat_eq_natCast]
      let A := big.rep F
      let B := small.rep F
      let C := Rep.res T.galHom.range.subtype A
      let j : tateCohomology B ((n + 1 : ℕ) : ℤ) ≅ groupCohomology B (n + 1) :=
        (TateCohomology.isoGroupCohomology (n + 1)).app B
      let k : tateCohomology C ((n + 1 : ℕ) : ℤ) ≅ groupCohomology C (n + 1) :=
        (TateCohomology.isoGroupCohomology (n + 1)).app C
      have hf : groupCohomology.map
          ((MonoidHom.ofInjective T.galHom_injective).symm : T.galHom.range →* small.Gal)
          (Representation.IsIntertwiningMap.ofRes (T.isIntertwiningMap_repIso_range F))
          (n + 1) = (T.cohomologyRangeIso F (n + 1)).hom := by
        rw [cohomologyRangeIso_def, groupCohomology.mapIso_hom]
        apply groupCohomology.map_congr rfl
        ext x
        simp only [Representation.IsIntertwiningMap.ofRes_hom_toLinearMap]
        rfl
      have hm : (T.tateRangeIso F ((n + 1 : ℕ) : ℤ)).hom ≫ k.hom =
          j.hom ≫ (T.cohomologyRangeIso F (n + 1)).hom := by
        rw [tateRangeIso_hom, ← hf]
        exact TauCeti.TateCohomology.map_comp_isoGroupCohomology_hom
          (T.isIntertwiningMap_repIso_range F) (n + 1)
      have hc := TauCeti.TateCohomology.cor_pos_comp_isoGroupCohomology_hom A T.galHom.range n
      have ht := T.tateCor_comp_tateHIsoH_hom F (n + 1)
      rw [cohomologyCor_def, NormalLayer.tateHIsoH_def, NormalLayer.tateHIsoH_def] at ht
      ext x
      apply (big.tateHIsoH F (n + 1)).toLinearEquiv.injective
      simp only [ModuleCat.comp_apply, NormalLayer.tateHIsoH_def]
      -- Evaluate the comparison squares across the ordinary-cohomology functor carriers.
      exact (ConcreteCategory.congr_hom ht x).trans
        ((congrArg (TauCeti.groupCohomology.corestriction T.galHom.range A (n + 1))
          (ConcreteCategory.congr_hom hm x).symm).trans
            (ConcreteCategory.congr_hom hc _).symm)
  | negSucc n => cases n <;> simp

/-- With trivial integral coefficients, layer Tate corestriction is the range comparison
followed by generic subgroup corestriction, in every integer degree. The subgroup carrier uses
the `Subgroup.fintypeOfFinite` instance fixed by the generic corestriction map. -/
@[reassoc]
theorem trivialTateCor_eq_cor (T : LayerRestriction small big) (r : ℤ) :
    T.trivialTateCor r = (T.trivialTateRangeIso r).hom ≫
      TauCeti.TateCohomology.cor (Rep.trivial ℤ big.Gal ℤ) T.galHom.range r := by
  cases r with
  | ofNat n =>
    cases n with
    | zero => simp
    | succ n =>
      simp only [Int.ofNat_eq_natCast]
      let A := Rep.trivial ℤ big.Gal ℤ
      let j : tateCohomology A ((n + 1 : ℕ) : ℤ) ≅ groupCohomology A (n + 1) :=
        (TateCohomology.isoGroupCohomology (n + 1)).app A
      have hc := TauCeti.TateCohomology.cor_pos_comp_isoGroupCohomology_hom A
        T.galHom.range n
      ext x
      apply j.toLinearEquiv.injective
      simp only [ModuleCat.comp_apply]
      exact (ConcreteCategory.congr_hom
        (T.trivialTateCor_comp_isoGroupCohomology_hom (n + 1)) x).trans
          (ConcreteCategory.congr_hom hc _).symm
  | negSucc n => cases n <;> simp

end TauCeti.ClassFieldTheory.LayerRestriction
