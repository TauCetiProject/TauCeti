/-
Copyright (c) 2026 Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import TauCeti.NumberTheory.ClassFieldTheory.Formation.Tate.Basic
public import TauCeti.NumberTheory.ClassFieldTheory.Formation.Tate.Corestriction

/-!
# Restriction of finite-layer Tate cohomology

For a restriction of finite normal layers `K/E` inside `K/F`, this file defines restriction

`Hhatʳ(Gal(K/F), A^V) ⟶ Hhatʳ(Gal(K/E), A^V)`

in every integer degree, with formation coefficients and with trivial integral coefficients. In
positive degrees it is the ordinary cohomological restriction `LayerRestriction.cohomologyRes`;
in degree zero it is induced by the inclusion of invariants, which on ground levels is the
inclusion `A^U ⊆ A^{U'}`; in degree minus one it is induced by the relative transfer; and in
degrees at most minus two it is the transfer on group homology. In degrees at most zero the smaller
Galois group is identified with the image of its inclusion into the larger one, exactly as for
`LayerRestriction.tateCor`.

The comparison lemmas below identify each branch with the corresponding established map, and the
degree-zero lemma reads restriction on norm quotients as the ground-level inclusion. Corestriction
after restriction is multiplication by the relative degree `[E : F]` in every degree.

## Main definitions

* `TauCeti.ClassFieldTheory.LayerRestriction.tateRes`: restriction of layer Tate cohomology.
* `TauCeti.ClassFieldTheory.LayerRestriction.trivialTateRes`: restriction of Tate cohomology with
  trivial integral coefficients.

## Main results

* `TauCeti.ClassFieldTheory.LayerRestriction.tateRes_comp_tateHIsoH_hom` and
  `TauCeti.ClassFieldTheory.LayerRestriction.trivialTateRes_comp_isoGroupCohomology_hom`: in
  positive degrees, Tate restriction is ordinary cohomological restriction.
* `TauCeti.ClassFieldTheory.LayerRestriction.tateHZeroEquivNormQuotient_tateRes_H0π`: in degree
  zero, restriction is the ground-level inclusion read on norm quotients.
* `TauCeti.ClassFieldTheory.LayerRestriction.tateCor_tateRes`: `cor ∘ res = [E : F]` in every
  degree.

## References

* E. Artin and J. Tate, *Class Field Theory*, Chapter IV, §6 and Chapter XIV, §4.
* K. S. Brown, *Cohomology of Groups*, Chapter III, §9 and Chapter VI, §5.
-/

public noncomputable section

open CategoryTheory Rep Representation

namespace TauCeti.ClassFieldTheory.LayerRestriction

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [TotallyDisconnectedSpace G] {small big : NormalLayer G}

attribute [local instance] instFintypeRange

/-- **Restriction between the Tate cohomology groups of finite normal layers, in every integer
degree.** Positive degrees use ordinary cohomological restriction, degrees zero and minus one use
the low-degree descriptions by invariants and norm kernels, and lower degrees use the transfer on
group homology. -/
def tateRes (T : LayerRestriction small big) (F : Formation G) :
    (r : ℤ) → big.TateH F r ⟶ small.TateH F r
  | .ofNat 0 =>
      TauCeti.TateCohomology.H0Res (big.rep F) T.galHom.range ≫ (T.tateRangeIso F 0).inv
  | .ofNat (n + 1) =>
      (big.tateHIsoH F (n + 1)).hom ≫ T.cohomologyRes F (n + 1) ≫
        (small.tateHIsoH F (n + 1)).inv
  | .negSucc 0 =>
      TauCeti.TateCohomology.HNegOneRes (big.rep F) T.galHom.range ≫
        (T.tateRangeIso F (-1)).inv
  | .negSucc (n + 1) =>
      TauCeti.TateCohomology.negSuccRes (big.rep F) T.galHom.range (n + 1) ≫
        (T.tateRangeIso F (Int.negSucc (n + 1))).inv

/-- In degree zero, layer Tate restriction is restriction of invariants to the image subgroup,
followed by the range comparison. -/
@[simp]
theorem tateRes_zero (T : LayerRestriction small big) (F : Formation G) :
    T.tateRes F 0 =
      TauCeti.TateCohomology.H0Res (big.rep F) T.galHom.range ≫ (T.tateRangeIso F 0).inv :=
  (rfl)

/-- In a positive degree, layer Tate restriction is ordinary cohomological restriction read
through the canonical positive-degree comparisons. -/
@[simp]
theorem tateRes_ofNat_succ (T : LayerRestriction small big) (F : Formation G) (n : ℕ) :
    T.tateRes F ((n : ℤ) + 1) =
      (big.tateHIsoH F (n + 1)).hom ≫ T.cohomologyRes F (n + 1) ≫
        (small.tateHIsoH F (n + 1)).inv :=
  (rfl)

/-- Positive-degree Tate restriction commutes with the canonical comparison to ordinary
cohomology. -/
@[reassoc]
theorem tateRes_comp_tateHIsoH_hom (T : LayerRestriction small big) (F : Formation G)
    (n : ℕ) [NeZero n] :
    T.tateRes F n ≫ (small.tateHIsoH F n).hom =
      (big.tateHIsoH F n).hom ≫ T.cohomologyRes F n := by
  cases n with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ k =>
    simp only [tateRes, Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- In degree minus one, layer Tate restriction is the relative transfer on norm kernels,
followed by the range comparison. -/
@[simp]
theorem tateRes_neg_one (T : LayerRestriction small big) (F : Formation G) :
    T.tateRes F (-1) =
      TauCeti.TateCohomology.HNegOneRes (big.rep F) T.galHom.range ≫
        (T.tateRangeIso F (-1)).inv :=
  (rfl)

/-- In degree `-(n+2)`, layer Tate restriction is the transfer in group homology of degree `n+1`,
followed by the range comparison. -/
@[simp]
theorem tateRes_negSucc_succ (T : LayerRestriction small big) (F : Formation G) (n : ℕ) :
    T.tateRes F (Int.negSucc (n + 1)) =
      TauCeti.TateCohomology.negSuccRes (big.rep F) T.galHom.range (n + 1) ≫
        (T.tateRangeIso F (Int.negSucc (n + 1))).inv :=
  (rfl)

/-- **In degree zero, restriction is the ground-level inclusion.** Read through the identification
of `Hhat⁰` with the norm quotient `A^U / N(A^V)`, restricting the class of an element of the ground
level `A^U` of `K/F` gives the class of the same element in the ground level `A^{U'}` of `K/E`. -/
theorem tateHZeroEquivNormQuotient_tateRes_H0π (T : LayerRestriction small big) (F : Formation G)
    (x : (big.rep F).ρ.invariants) :
    small.tateHZeroEquivNormQuotient F (T.tateRes F 0 (TateCohomology.H0π (big.rep F) x)) =
      small.normQuotientMk F (T.groundInclusion F (big.groundLevelEquiv F x)) := by
  rw [tateRes_zero, ModuleCat.comp_apply, TauCeti.TateCohomology.H0π_comp_H0Res_apply,
    tateRangeIso_inv_H0π, NormalLayer.tateHZeroEquivNormQuotient_H0π]
  congr 1
  ext
  rw [NormalLayer.groundLevelEquiv_apply_coe, groundInclusion_apply_coe,
    NormalLayer.groundLevelEquiv_apply_coe]
  exact T.repIso_inv_apply_coe F _

/-- **Corestriction after restriction is multiplication by the relative degree** `[E : F]`, in
every Tate degree. -/
@[reassoc, elementwise]
theorem tateCor_tateRes (T : LayerRestriction small big) (F : Formation G) (r : ℤ) :
    T.tateRes F r ≫ T.tateCor F r = T.relativeDegree • 𝟙 (big.TateH F r) := by
  obtain ⟨n, rfl⟩ | rfl | rfl | ⟨n, rfl⟩ :
      (∃ n : ℕ, r = n + 1) ∨ r = 0 ∨ r = -1 ∨ ∃ n : ℕ, r = Int.negSucc (n + 1) := by
    rcases lt_trichotomy r 0 with h | rfl | h
    · rcases eq_or_lt_of_le (show r ≤ -1 by omega) with rfl | h'
      · exact .inr (.inr (.inl rfl))
      · exact .inr (.inr (.inr ⟨(-r - 2).toNat, by omega⟩))
    · exact .inr (.inl rfl)
    · exact .inl ⟨(r - 1).toNat, by omega⟩
  · simp only [tateRes_ofNat_succ, tateCor_ofNat_succ, Category.assoc, Iso.inv_hom_id_assoc,
      cohomologyCor_cohomologyRes_assoc, Linear.smul_comp, Category.id_comp, Linear.comp_smul,
      Iso.hom_inv_id]
  · rw [← T.index_range_galHom]
    simpa using TauCeti.TateCohomology.H0Res_comp_H0Cor (big.rep F) T.galHom.range
  · rw [← T.index_range_galHom]
    simpa using
      TauCeti.TateCohomology.HNegOneRes_comp_HNegOneCor (big.rep F) T.galHom.range
  · rw [← T.index_range_galHom]
    simpa using
      TauCeti.TateCohomology.negSuccRes_comp_negSuccCor (big.rep F) T.galHom.range (n + 1)

/-! ### Trivial coefficients -/

/-- **Restriction on the Tate cohomology of finite normal layers with trivial integral
coefficients, in every integer degree.** It uses cohomological restriction in positive degrees,
the low-degree maps in degrees zero and minus one, and the homological transfer below them. -/
def trivialTateRes (T : LayerRestriction small big) :
    (r : ℤ) → big.TrivialTateH r ⟶ small.TrivialTateH r
  | .ofNat 0 =>
      TauCeti.TateCohomology.H0Res (Rep.trivial ℤ big.Gal ℤ) T.galHom.range ≫
        (T.trivialTateRangeIso 0).inv
  | .ofNat (n + 1) =>
      (TateCohomology.isoGroupCohomology (n + 1)).hom.app (Rep.trivial ℤ big.Gal ℤ) ≫
        groupCohomology.map T.galHom.range.subtype
          (𝟙 (Rep.res T.galHom.range.subtype (Rep.trivial ℤ big.Gal ℤ))) (n + 1) ≫
        (T.trivialTateRangeIso ((n + 1 : ℕ) : ℤ) ≪≫
          (TateCohomology.isoGroupCohomology (n + 1)).app
          (Rep.res T.galHom.range.subtype (Rep.trivial ℤ big.Gal ℤ))).inv
  | .negSucc 0 =>
      TauCeti.TateCohomology.HNegOneRes (Rep.trivial ℤ big.Gal ℤ) T.galHom.range ≫
        (T.trivialTateRangeIso (-1)).inv
  | .negSucc (n + 1) =>
      TauCeti.TateCohomology.negSuccRes (Rep.trivial ℤ big.Gal ℤ) T.galHom.range (n + 1) ≫
        (T.trivialTateRangeIso (Int.negSucc (n + 1))).inv

/-- In degree zero, trivial-coefficient Tate restriction is restriction of invariants to the image
subgroup, followed by the range comparison. -/
@[simp]
theorem trivialTateRes_zero (T : LayerRestriction small big) :
    T.trivialTateRes 0 =
      TauCeti.TateCohomology.H0Res (Rep.trivial ℤ big.Gal ℤ) T.galHom.range ≫
        (T.trivialTateRangeIso 0).inv :=
  (rfl)

/-- In a positive degree, trivial-coefficient Tate restriction is ordinary cohomological
restriction to the image subgroup, followed by the range comparison. -/
@[simp]
theorem trivialTateRes_ofNat_succ (T : LayerRestriction small big) (n : ℕ) :
    T.trivialTateRes ((n : ℤ) + 1) =
      (TateCohomology.isoGroupCohomology (n + 1)).hom.app (Rep.trivial ℤ big.Gal ℤ) ≫
        groupCohomology.map T.galHom.range.subtype
          (𝟙 (Rep.res T.galHom.range.subtype (Rep.trivial ℤ big.Gal ℤ))) (n + 1) ≫
        (T.trivialTateRangeIso ((n + 1 : ℕ) : ℤ) ≪≫
          (TateCohomology.isoGroupCohomology (n + 1)).app
          (Rep.res T.galHom.range.subtype (Rep.trivial ℤ big.Gal ℤ))).inv :=
  (rfl)

/-- Positive-degree trivial-coefficient Tate restriction is ordinary cohomological restriction to
the image subgroup, read through the canonical comparisons with ordinary cohomology. -/
@[reassoc]
theorem trivialTateRes_comp_isoGroupCohomology_hom (T : LayerRestriction small big) (n : ℕ)
    [NeZero n] :
    T.trivialTateRes n ≫ (T.trivialTateRangeIso n ≪≫ (TateCohomology.isoGroupCohomology n).app
        (Rep.res T.galHom.range.subtype (Rep.trivial ℤ big.Gal ℤ))).hom =
      (TateCohomology.isoGroupCohomology n).hom.app (Rep.trivial ℤ big.Gal ℤ) ≫
        groupCohomology.map T.galHom.range.subtype
          (𝟙 (Rep.res T.galHom.range.subtype (Rep.trivial ℤ big.Gal ℤ))) n := by
  cases n with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ k =>
    simp only [trivialTateRes]
    -- The comparison maps are composed across the semireducible group-cohomology carrier, where
    -- `simp`/`rw` cannot reassociate; the cancellation is applied as a term.
    exact (Category.assoc _ _ _).trans (congrArg _ ((Category.assoc _ _ _).trans
      ((congrArg _ (Iso.inv_hom_id _)).trans (Category.comp_id _))))

/-- In degree minus one, trivial-coefficient Tate restriction is the relative transfer on norm
kernels, followed by the range comparison. -/
@[simp]
theorem trivialTateRes_neg_one (T : LayerRestriction small big) :
    T.trivialTateRes (-1) =
      TauCeti.TateCohomology.HNegOneRes (Rep.trivial ℤ big.Gal ℤ) T.galHom.range ≫
        (T.trivialTateRangeIso (-1)).inv :=
  (rfl)

/-- In degree `-(n+2)`, trivial-coefficient Tate restriction is the transfer in group homology of
degree `n+1`, followed by the range comparison. -/
@[simp]
theorem trivialTateRes_negSucc_succ (T : LayerRestriction small big) (n : ℕ) :
    T.trivialTateRes (Int.negSucc (n + 1)) =
      TauCeti.TateCohomology.negSuccRes (Rep.trivial ℤ big.Gal ℤ) T.galHom.range (n + 1) ≫
        (T.trivialTateRangeIso (Int.negSucc (n + 1))).inv :=
  (rfl)

end TauCeti.ClassFieldTheory.LayerRestriction
