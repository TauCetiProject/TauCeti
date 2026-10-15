/-
Copyright (c) 2026 Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: √2, Codex
-/
module

public import TauCeti.RepresentationTheory.Homological.TateCohomology.Restriction.AllDegrees
public import TauCeti.RepresentationTheory.Homological.TateCohomology.Connecting.LowDegree
public import TauCeti.RepresentationTheory.Homological.TateCohomology.Connecting.GroupHomology
public import TauCeti.RepresentationTheory.Homological.GroupHomology.LongExactSequence

public import TauCeti.RepresentationTheory.Homological.TateCohomology.Connecting.GroupCohomology

/-!
# Corestriction and connecting maps in every Tate degree

For a subgroup `H` of a finite group `G`, Tate corestriction commutes with the connecting map
of every short exact sequence of representations, from degree `r` to degree `r + 1` for
every integer `r`. This includes the norm boundary from degree minus one to degree zero. When both
degrees are at most `-2`, the compatibility holds along any homomorphism of finite groups.

In negative degrees, the canonical comparison with group homology intertwines corestriction
with the map induced by subgroup inclusion. At the norm boundary, the compatibility relates
the norm-kernel inclusion in degree minus one to the relative norm on invariants in degree zero.

In nonnegative degrees, the canonical map from ordinary cohomology to Tate cohomology
intertwines corestriction: in degree zero this is the relative norm on invariants, and in
positive degrees it is ordinary cohomological corestriction. Since this comparison is
surjective, the compatibility with ordinary connecting maps determines the Tate square.

These squares allow dimension shifting across the entire Tate complex and its norm boundary,
in particular when proving the projection formula for cup products.

## Main results

* `TauCeti.TateCohomology.cor_comp_toGroupHomology`: negative corestriction is the covariant
  map on group homology through the canonical comparison.
* `TauCeti.TateCohomology.δ_comp_negSuccCor`: corestriction along any homomorphism of finite
  groups commutes with connecting maps whose source and target degrees are at most `-2`.
* `TauCeti.TateCohomology.δ_comp_cor_neg_one`: corestriction commutes with the norm-boundary
  connecting map.
* `Rep.fromGroupCohomology_comp_cor`: the comparison from ordinary
  cohomology intertwines corestriction in every nonnegative degree.
* `TauCeti.TateCohomology.δ_comp_cor`: corestriction commutes with connecting maps in every
  integer degree.

## References

* K. S. Brown, *Cohomology of Groups*, Chapter III, §9 and Chapter VI, §5.
* E. Artin and J. Tate, *Class Field Theory*, Chapter IV, §6 and Chapter XIV, §4.
-/

public noncomputable section

universe u

open CategoryTheory Rep

namespace TauCeti.TateCohomology

variable {R G : Type u} [CommRing R] [Group G] [Fintype G]

attribute [local instance] Subgroup.fintypeOfFinite Subgroup.fintypeQuotientOfFiniteIndex

/-- Through the canonical comparison with group homology, negative Tate corestriction is
induced by the inclusion of the subgroup. This also holds in degree minus one, where the
comparison is an injection rather than an isomorphism. -/
@[reassoc]
theorem cor_comp_toGroupHomology (M : Rep R G) (H : Subgroup G) (n : ℕ) :
    cor M H (Int.negSucc n) ≫ toGroupHomology M n =
      toGroupHomology (Rep.res H.subtype M) n ≫
        groupHomology.map H.subtype (𝟙 (Rep.res H.subtype M)) n := by
  cases n with
  | zero =>
    -- `Int.negSucc 0` is the degree `-1` used by the norm-kernel API. Rewriting the degree
    -- alone would break the dependent composition with `toGroupHomology`.
    change cor M H (-1) ≫ _ = _
    rw [cor_neg_one, ← cancel_epi (HNegOneπ (Rep.res H.subtype M)),
      HNegOneπ_comp_HNegOneCor_assoc, HNegOneπ_comp_toGroupHomology,
      HNegOneπ_comp_toGroupHomology_assoc, groupHomology.H0π_comp_map]
    -- The norm-kernel inclusion and the identity coefficient map leave the same element
    -- unchanged. Only their subtype proofs and categorical wrappers differ.
    ext z
    rfl
  | succ n =>
    rw [cor_negSucc_succ, toGroupHomology_eq_negSuccIso_hom,
      toGroupHomology_eq_negSuccIso_hom, negSuccCor_comp_negSuccIso_hom]

/-- Corestriction commutes with the connecting map from degree minus one to degree zero.
On representatives this is the relative-norm identity `N_{G/H} N_H = N_G`. -/
@[reassoc (attr := simp)]
theorem δ_comp_cor_neg_one {S : ShortComplex (Rep R G)} (hS : S.ShortExact)
    (H : Subgroup G) :
    _root_.TateCohomology.δ ((shortExact_res H.subtype).2 hS) (-1) ≫ H0Cor S.X₁ H =
      HNegOneCor S.X₃ H ≫ _root_.TateCohomology.δ hS (-1) := by
  -- Use `δ_neg_one_HNegOneπ`, the specialization of Mathlib's concrete connecting-map
  -- formula, and the relative-norm identity `N_{G/H} N_H = N_G` on representatives.
  ext z
  induction z using HNegOne_induction_on with
  | h z =>
    obtain ⟨y, x, hy, hx, hδ⟩ :=
      exists_δ_neg_one_eq_H0π ((shortExact_res H.subtype).2 hS) z
    simp only [ConcreteCategory.comp_apply, hδ]
    refine (ConcreteCategory.congr_hom (H0π_comp_H0Cor S.X₁ H) x).trans ?_
    refine Eq.trans ?_ (congrArg (_root_.TateCohomology.δ hS (-1))
      (ConcreteCategory.congr_hom (HNegOneπ_comp_HNegOneCor S.X₃ H) z).symm)
    apply (δ_neg_one_HNegOneπ hS
      (Submodule.inclusion
        (Representation.ker_norm_comp_subtype_le_ker_norm (ρ := S.X₃.ρ) (H := H)) z)
      y hy (Representation.relNormInvariants S.X₁.ρ H x) ?_).symm
    rw [Representation.coe_relNormInvariants, Representation.relNorm_apply, map_sum]
    calc
      _ = ∑ q : G ⧸ H, S.X₂.ρ q.out (S.f.hom x.1) :=
        Finset.sum_congr rfl fun q _ ↦ Rep.hom_comm_apply S.f q.out x.1
      _ = S.X₂.ρ.norm y := by
        -- Restriction keeps the coefficient map and replaces the action by `ρ.comp H.subtype`.
        -- The norm of the restricted middle representation in `hx` is therefore `N_H`.
        have hx' : S.f.hom x.1 = Representation.norm (S.X₂.ρ.comp H.subtype) y := hx
        rw [hx', ← Representation.relNorm_apply, Representation.relNorm_norm_apply]

/-- Corestriction along a homomorphism of finite groups commutes with the connecting map
from degree `-(n+2)` to degree `-(n+1)` when `n > 0`, so both degrees are at most `-2`. -/
@[reassoc (attr := simp)]
theorem δ_comp_negSuccCor {H : Type u} [Group H] [Fintype H]
    {S : ShortComplex (Rep R G)} (hS : S.ShortExact) (f : H →* G) (n : ℕ) [NeZero n] :
    _root_.TateCohomology.δ ((shortExact_res f).2 hS) (Int.negSucc (n + 1)) ≫
        negSuccCor S.X₁ f n =
      negSuccCor S.X₃ f (n + 1) ≫
        _root_.TateCohomology.δ hS (Int.negSucc (n + 1)) := by
  -- Follow the restriction argument in
  -- `TauCeti.RepresentationTheory.Homological.TateCohomology.Restriction.Delta`, replacing
  -- homological transfer by the covariant group map and its naturality theorem.
  -- Both degrees have an isomorphism with group homology, so cancel the target comparison.
  refine (cancel_mono ((negSuccIso S.X₁ n).hom)).1 ?_
  calc
    _ = (negSuccIso (Rep.res f S.X₃) (n + 1)).hom ≫
        groupHomology.δ ((shortExact_res f).2 hS) (n + 1) n rfl ≫
          groupHomology.map f (𝟙 (Rep.res f S.X₁)) n := by
      rw [Category.assoc, negSuccCor_comp_negSuccIso_hom]
      have hδ := δ_comp_negSuccIso_hom ((shortExact_res f).2 hS) n
      dsimp only [ShortComplex.map_X₁, ShortComplex.map_X₃] at hδ
      exact (Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) hδ)
    _ = (negSuccIso (Rep.res f S.X₃) (n + 1)).hom ≫
        groupHomology.map f (𝟙 (Rep.res f S.X₃)) (n + 1) ≫
          groupHomology.δ hS (n + 1) n rfl := by
      have hδ := TauCeti.groupHomology.δ_naturality f
        ((shortExact_res f).2 hS) hS (𝟙 (S.map (resFunctor f)))
        (n + 1) n rfl
      simp only [ShortComplex.id_τ₁, ShortComplex.id_τ₃,
        ShortComplex.map_X₁, ShortComplex.map_X₃] at hδ
      exact congrArg (_ ≫ ·) hδ
    _ = _ := by
      rw [← negSuccCor_comp_negSuccIso_hom_assoc, Category.assoc]
      exact congrArg (_ ≫ ·) (δ_comp_negSuccIso_hom hS n).symm

/-- Corestriction commutes with the connecting map below the norm boundary. -/
private theorem δ_comp_cor_negSucc {S : ShortComplex (Rep R G)} (hS : S.ShortExact)
    (H : Subgroup G) (n : ℕ) :
    _root_.TateCohomology.δ ((shortExact_res H.subtype).2 hS) (Int.negSucc (n + 1)) ≫
        cor S.X₁ H (Int.negSucc n) =
      cor S.X₃ H (Int.negSucc (n + 1)) ≫
        _root_.TateCohomology.δ hS (Int.negSucc (n + 1)) := by
  cases n with
  | succ n =>
    simpa only [cor_negSucc_succ] using δ_comp_negSuccCor hS H.subtype (n + 1)
  | zero =>
    -- The comparison is injective even in degree minus one, so cancel it to prove the Tate square.
    refine (cancel_mono (toGroupHomology S.X₁ 0)).1 ?_
    calc
      _ = toGroupHomology (Rep.res H.subtype S.X₃) (0 + 1) ≫
          groupHomology.δ ((shortExact_res H.subtype).2 hS) (0 + 1) 0 rfl ≫
            groupHomology.map H.subtype (𝟙 (Rep.res H.subtype S.X₁)) 0 := by
        rw [Category.assoc, cor_comp_toGroupHomology]
        have hδ := δ_comp_toGroupHomology ((shortExact_res H.subtype).2 hS) 0
        dsimp only [ShortComplex.map_X₁, ShortComplex.map_X₃] at hδ
        exact (Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) hδ)
      _ = toGroupHomology (Rep.res H.subtype S.X₃) (0 + 1) ≫
          groupHomology.map H.subtype (𝟙 (Rep.res H.subtype S.X₃)) (0 + 1) ≫
            groupHomology.δ hS (0 + 1) 0 rfl := by
        have hδ := TauCeti.groupHomology.δ_naturality H.subtype
          ((shortExact_res H.subtype).2 hS) hS (𝟙 (S.map (resFunctor H.subtype)))
          (0 + 1) 0 rfl
        simp only [ShortComplex.id_τ₁, ShortComplex.id_τ₃,
          ShortComplex.map_X₁, ShortComplex.map_X₃] at hδ
        exact congrArg (_ ≫ ·) hδ
      _ = _ := by
        rw [← cor_comp_toGroupHomology_assoc, Category.assoc]
        exact congrArg (_ ≫ ·) (δ_comp_toGroupHomology hS 0).symm

/-- Tate corestriction commutes with the connecting map from degree `r` to `r + 1` for
every negative degree `r`, including the boundary from minus one to zero. -/
private theorem δ_comp_cor_of_neg {S : ShortComplex (Rep R G)} (hS : S.ShortExact)
    (H : Subgroup G) {r : ℤ} (hr : r < 0) :
    _root_.TateCohomology.δ ((shortExact_res H.subtype).2 hS) r ≫ cor S.X₁ H (r + 1) =
      cor S.X₃ H r ≫ _root_.TateCohomology.δ hS r := by
  obtain ⟨_ | n, rfl⟩ := Int.eq_negSucc_of_lt_zero hr
  · -- Retype both sides together at the norm boundary; rewriting a degree in isolation
    -- would break the dependent types of the composite morphisms.
    change _root_.TateCohomology.δ ((shortExact_res H.subtype).2 hS) (-1) ≫
      cor S.X₁ H 0 = cor S.X₃ H (-1) ≫ _root_.TateCohomology.δ hS (-1)
    rw [cor_zero, cor_neg_one]
    exact δ_comp_cor_neg_one hS H
  · exact δ_comp_cor_negSucc hS H n

/-- The canonical comparison from ordinary cohomology to Tate cohomology intertwines
corestriction in every nonnegative degree, including the relative norm in degree zero.

As in `cor`, the subgroup Tate carrier uses `Subgroup.fintypeOfFinite H`; callers with
another `Fintype H` should select this instance when forming the square. The generic
`Rep.fromGroupCohomology` comparison itself preserves the ambient group instance. -/
@[reassoc]
theorem _root_.Rep.fromGroupCohomology_comp_cor (M : Rep R G) (H : Subgroup G) (n : ℕ) :
    fromGroupCohomology (Rep.res H.subtype M) n ≫ cor M H n =
      groupCohomology.corestriction H M n ≫ fromGroupCohomology M n := by
  cases n with
  | zero =>
    -- Degree zero is the same index written through the natural-number inclusion.
    erw [fromGroupCohomology_zero, fromGroupCohomology_zero, cor_zero,
      Category.assoc, H0π_comp_H0Cor]
    have hNorm := Rep.H0Iso_inv_comp_corestriction_comp_H0Iso_hom M H
    rw [Iso.inv_comp_eq] at hNorm
    exact (Category.assoc _ _ _).symm.trans (congrArg (· ≫ H0π M) hNorm.symm)
  | succ n =>
    rw [← cancel_mono ((_root_.TateCohomology.isoGroupCohomology (n + 1)).app M).hom]
    have hCor := cor_pos_comp_isoGroupCohomology_hom M H n
    simp only [Int.natCast_add, Int.cast_ofNat_Int, Iso.app_hom] at hCor ⊢
    rw [Category.assoc, hCor, fromGroupCohomology_succ,
      Category.assoc, fromGroupCohomology_succ]
    have hH := Iso.inv_hom_id
      ((_root_.TateCohomology.isoGroupCohomology (G := H) (n + 1)).app
        (Rep.res H.subtype M))
    have hG := Iso.inv_hom_id
      ((_root_.TateCohomology.isoGroupCohomology (n + 1)).app M)
    simp only [Iso.app_inv, Iso.app_hom] at hH hG ⊢
    exact ((Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ groupCohomology.corestriction H M (n + 1)) hH).trans
        (Category.id_comp _))).trans
      ((congrArg (groupCohomology.corestriction H M (n + 1) ≫ ·) hG).trans
        (Category.comp_id _)).symm

private theorem δ_comp_cor_of_nonneg {S : ShortComplex (Rep R G)} (hS : S.ShortExact)
    (H : Subgroup G) (n : ℕ) :
    _root_.TateCohomology.δ ((shortExact_res H.subtype).2 hS) n ≫
        cor S.X₁ H (n + 1) =
      cor S.X₃ H n ≫ _root_.TateCohomology.δ hS n := by
  let hRes := (shortExact_res H.subtype).2 hS
  have hδ := δ_comp_fromGroupCohomology hRes n
  dsimp only [ShortComplex.map_X₁, ShortComplex.map_X₃] at hδ
  have hC₁ := fromGroupCohomology_comp_cor S.X₁ H (n + 1)
  have hC₃ := fromGroupCohomology_comp_cor S.X₃ H n
  simp only [Int.natCast_add, Int.cast_ofNat_Int] at hC₁
  rw [← cancel_epi (fromGroupCohomology (Rep.res H.subtype S.X₃) n),
    ← reassoc_of% hδ]
  calc
    _ = groupCohomology.δ hRes n (n + 1) rfl ≫
        groupCohomology.corestriction H S.X₁ (n + 1) ≫
          fromGroupCohomology S.X₁ (n + 1) := congrArg (_ ≫ ·) hC₁
    _ = groupCohomology.corestriction H S.X₃ n ≫
        fromGroupCohomology S.X₃ n ≫ _root_.TateCohomology.δ hS n := by
      rw [← Category.assoc, groupCohomology.δ_comp_corestriction H hS n (n + 1) rfl,
        Category.assoc, δ_comp_fromGroupCohomology]
    _ = _ := ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) hC₃.symm)).trans
      (Category.assoc _ _ _)

/-- Tate corestriction commutes with the connecting map from degree `r` to degree `r + 1`
for every integer degree, including both sides of the norm boundary.

The subgroup Tate carrier uses the `Subgroup.fintypeOfFinite H` instance fixed by `cor`. -/
@[reassoc (attr := simp)]
theorem δ_comp_cor {S : ShortComplex (Rep R G)} (hS : S.ShortExact)
    (H : Subgroup G) (r : ℤ) :
    _root_.TateCohomology.δ ((shortExact_res H.subtype).2 hS) r ≫ cor S.X₁ H (r + 1) =
      cor S.X₃ H r ≫ _root_.TateCohomology.δ hS r := by
  by_cases hr : r < 0
  · exact δ_comp_cor_of_neg hS H hr
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le (by omega : 0 ≤ r)
    exact δ_comp_cor_of_nonneg hS H n

end TauCeti.TateCohomology
