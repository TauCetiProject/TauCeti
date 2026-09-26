/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
public import TauCeti.Algebra.Group.NormalizerQuotient.Conjugation
import TauCeti.Algebra.Group.Conj
import Mathlib.Tactic.Group

/-!
# Basepoint change for fundamental groups

The pointed classification of connected covers records a subgroup of the fundamental group at
a chosen basepoint. Changing the basepoint along a path transports that subgroup by the
standard path-conjugation isomorphism of fundamental groups. This file packages that transport
and the induced transport of the normalizer quotient `N(H) / H` used for deck groups of covers
attached to subgroups.

It also records the element-level behaviour of the transport: path-quotient formulas, its
compatibility with concatenation of paths, and the fact that two paths with the same endpoints
give conjugate transports. In a path-connected space the latter yields a path-independent
conjugacy class at every basepoint.

Mathlib already supplies the fundamental-group isomorphism
`FundamentalGroup.fundamentalGroupMulEquivOfPath`; the declarations here are the computation
rules, conjugacy-class, subgroup, and normalizer-quotient bookkeeping built on it.

## Main declarations

* `TauCeti.FundamentalGroup.basepointChangeSubgroup`: transport a subgroup of `π₁(X, x₀)`
  along a path `γ : Path x₀ x₁`.
* Domain-specific membership, inclusion, monotonicity, and normality lemmas for
  `basepointChangeSubgroup`.
* `TauCeti.FundamentalGroup.basepointChangeNormalizerQuotientEquiv`: the corresponding
  isomorphism `N(H) / H ≃* N(γ₊H) / γ₊H`.
* `FundamentalGroup.fundamentalGroupMulEquivOfPath_apply` and
  `FundamentalGroup.fundamentalGroupMulEquivOfPath_symm_apply`: basepoint change as conjugation
  by the path in the path quotient.
* `FundamentalGroup.fundamentalGroupMulEquivOfPath_trans`: basepoint change along a concatenated
  path is the composite of the basepoint changes.
* `FundamentalGroup.fundamentalGroupMulEquivOfPath_eq_conj`: basepoint change along a loop is
  conjugation by its class.
* `FundamentalGroup.isConj_fundamentalGroupMulEquivOfPath_apply_of_paths`: transports along two
  paths with the same endpoints are conjugate.
* `FundamentalGroup.conjClassAt`: the path-independent conjugacy class of `g ∈ π₁(X, x₀)` at
  `x₁`, with `FundamentalGroup.mk_fundamentalGroupMulEquivOfPath_eq_conjClassAt`,
  `FundamentalGroup.conjClassAt_self`, and `FundamentalGroup.map_conjClassAt`.
* `TauCeti.FundamentalGroup.mem_basepointChangeSubgroup` and the representative `[simp]`
  lemmas for membership and quotient calculations under these domain-specific names.

## References

This supplies a small prerequisite for `TauCetiRoadmap/UniversalCovers/README.md`, Stage 2,
items 7 and 8: the pointed cover attached to `H ≤ π₁(X, x₀)`, conjugacy under basepoint
change, and the normalizer quotient `N(H) / H` appearing as the deck group of that cover. The
path-independent conjugacy classes supply `TauCetiRoadmap/BelyiMaps/README.md`, Layer 5, §5.7.
-/

public section

namespace TauCeti

namespace FundamentalGroup

open CategoryTheory in
/-- The inverse basepoint-change equivalence is represented by conjugation with the reverse path.
This path-quotient formula is the interface for computations with the equivalence. -/
lemma _root_.FundamentalGroup.fundamentalGroupMulEquivOfPath_symm_apply
    {X : Type*} [TopologicalSpace X] {x₀ x₁ : X}
    (γ : Path x₀ x₁) (g : _root_.FundamentalGroup X x₁) :
    (_root_.FundamentalGroup.fundamentalGroupMulEquivOfPath γ).symm g =
      Path.Homotopic.Quotient.trans (Path.Homotopic.Quotient.mk γ)
        (Path.Homotopic.Quotient.trans g (Path.Homotopic.Quotient.mk γ).symm) := by
  let γq : Path.Homotopic.Quotient x₀ x₁ := Path.Homotopic.Quotient.mk γ
  let α : FundamentalGroupoid.mk x₀ ≅ FundamentalGroupoid.mk x₁ :=
    (Groupoid.isoEquivHom _ _).symm γq
  have hα_hom : α.hom = γq := by
    exact (Groupoid.isoEquivHom (FundamentalGroupoid.mk x₀)
      (FundamentalGroupoid.mk x₁)).apply_symm_apply γq
  have hα_inv : α.inv = γq.symm := by
    apply (cancel_mono γq).1
    calc
      α.inv ≫ γq = α.inv ≫ α.hom := by rw [hα_hom]
      _ = 𝟙 (FundamentalGroupoid.mk x₁) := α.inv_hom_id
      _ = γq.symm ≫ γq := by
        rw [FundamentalGroupoid.id_eq_path_refl]
        exact (Path.Homotopic.Quotient.symm_trans γq).symm
  rw [MulEquiv.symm_apply_eq]
  have hconj : Path.Homotopic.Quotient.trans γq
      (Path.Homotopic.Quotient.trans g γq.symm) = α.symm.conj g := by
    rw [CategoryTheory.Iso.conj_apply, CategoryTheory.Iso.symm_inv,
      CategoryTheory.Iso.symm_hom, hα_hom, hα_inv]
    simp only [FundamentalGroupoid.comp_eq]
  rw [hconj]
  exact (α.self_symm_conj g).symm

/-- **Basepoint change along a loop is an inner automorphism.** For a loop `γ` at `x`, changing
basepoint along `γ` is conjugation by the class of `γ` in `π₁(X, x)`. In particular it is invisible
to any homomorphism from `π₁(X, x)` to a commutative group. -/
lemma _root_.FundamentalGroup.fundamentalGroupMulEquivOfPath_eq_conj {X : Type*}
    [TopologicalSpace X] {x : X} (γ : Path x x) :
    _root_.FundamentalGroup.fundamentalGroupMulEquivOfPath γ =
      MulAut.conj (_root_.FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk γ)) := by
  ext g
  rw [MulAut.conj_apply, ← MulEquiv.eq_symm_apply,
    _root_.FundamentalGroup.fundamentalGroupMulEquivOfPath_symm_apply]
  -- In `π₁(X, x)` concatenation is multiplication in the reverse order and reversal is inversion
  -- (`FundamentalGroup.mul_def`, `FundamentalGroup.inv_def`); restate the path formula as a word.
  have htrans (a b : _root_.FundamentalGroup X x) : a.trans b = b * a :=
    (_root_.FundamentalGroup.mul_def).symm
  have hsymm (a : _root_.FundamentalGroup X x) : Path.Homotopic.Quotient.symm a = a⁻¹ :=
    (_root_.FundamentalGroup.inv_def).symm
  rw [hsymm, htrans, htrans]
  group

/-- Basepoint change along `γ` is represented by conjugation with `γ` in the path quotient: a loop
`g` at `x₀` goes to the class of `γ⁻¹ ⬝ g ⬝ γ`. This is the forward counterpart of
`FundamentalGroup.fundamentalGroupMulEquivOfPath_symm_apply`. -/
lemma _root_.FundamentalGroup.fundamentalGroupMulEquivOfPath_apply
    {X : Type*} [TopologicalSpace X] {x₀ x₁ : X}
    (γ : Path x₀ x₁) (g : _root_.FundamentalGroup X x₀) :
    _root_.FundamentalGroup.fundamentalGroupMulEquivOfPath γ g =
      Path.Homotopic.Quotient.trans (Path.Homotopic.Quotient.mk γ).symm
        (Path.Homotopic.Quotient.trans g (Path.Homotopic.Quotient.mk γ)) := by
  rw [← MulEquiv.eq_symm_apply, _root_.FundamentalGroup.fundamentalGroupMulEquivOfPath_symm_apply]
  -- Cancel `γ⁻¹ ⬝ γ` on the right, then `γ ⬝ γ⁻¹` on the left.
  rw [Path.Homotopic.Quotient.trans_assoc, Path.Homotopic.Quotient.trans_assoc,
    Path.Homotopic.Quotient.trans_symm, Path.Homotopic.Quotient.trans_refl,
    ← Path.Homotopic.Quotient.trans_assoc, Path.Homotopic.Quotient.trans_symm,
    Path.Homotopic.Quotient.refl_trans]

/-- Basepoint change along a concatenated path is basepoint change along each piece in turn. -/
lemma _root_.FundamentalGroup.fundamentalGroupMulEquivOfPath_trans
    {X : Type*} [TopologicalSpace X] {x₀ x₁ x₂ : X} (γ : Path x₀ x₁) (δ : Path x₁ x₂) :
    _root_.FundamentalGroup.fundamentalGroupMulEquivOfPath (γ.trans δ) =
      (_root_.FundamentalGroup.fundamentalGroupMulEquivOfPath γ).trans
        (_root_.FundamentalGroup.fundamentalGroupMulEquivOfPath δ) := by
  ext g
  rw [MulEquiv.trans_apply, _root_.FundamentalGroup.fundamentalGroupMulEquivOfPath_apply,
    _root_.FundamentalGroup.fundamentalGroupMulEquivOfPath_apply,
    _root_.FundamentalGroup.fundamentalGroupMulEquivOfPath_apply,
    ← Path.Homotopic.Quotient.mk_symm, Path.trans_symm]
  -- Both sides are the word `δ⁻¹ ⬝ γ⁻¹ ⬝ g ⬝ γ ⬝ δ`, up to reassociation.
  simp only [Path.Homotopic.Quotient.mk_trans, Path.Homotopic.Quotient.mk_symm,
    Path.Homotopic.Quotient.trans_assoc]

/-- Transporting an element of a fundamental group along two paths with the same endpoints gives
conjugate elements. Thus basepoint transport determines a conjugacy class independently of the
chosen path. -/
lemma _root_.FundamentalGroup.isConj_fundamentalGroupMulEquivOfPath_apply_of_paths
    {X : Type*} [TopologicalSpace X] {x₀ x₁ : X} (γ δ : Path x₀ x₁)
    (g : _root_.FundamentalGroup X x₀) :
    IsConj (_root_.FundamentalGroup.fundamentalGroupMulEquivOfPath γ g)
      (_root_.FundamentalGroup.fundamentalGroupMulEquivOfPath δ g) := by
  -- The loop `γ⁻¹ ⬝ δ` at `x₁` conjugates `γ⁻¹ ⬝ g ⬝ γ` to `δ⁻¹ ⬝ g ⬝ δ`. In `π₁(X, x₁)`,
  -- multiplication is concatenation in the reverse order (`FundamentalGroup.mul_def`).
  refine ⟨toUnits (Path.Homotopic.Quotient.mk (γ.symm.trans δ)), ?_⟩
  rw [SemiconjBy, val_toUnits_apply, _root_.FundamentalGroup.mul_def,
    _root_.FundamentalGroup.mul_def, _root_.FundamentalGroup.fundamentalGroupMulEquivOfPath_apply,
    _root_.FundamentalGroup.fundamentalGroupMulEquivOfPath_apply,
    Path.Homotopic.Quotient.mk_trans, Path.Homotopic.Quotient.mk_symm]
  -- Both sides reduce to `γ⁻¹ ⬝ g ⬝ δ` after cancelling `γ ⬝ γ⁻¹` and `δ ⬝ δ⁻¹` respectively.
  simp only [Path.Homotopic.Quotient.trans_assoc]
  rw [← Path.Homotopic.Quotient.trans_assoc (Path.Homotopic.Quotient.mk γ),
    Path.Homotopic.Quotient.trans_symm, Path.Homotopic.Quotient.refl_trans,
    ← Path.Homotopic.Quotient.trans_assoc (Path.Homotopic.Quotient.mk δ),
    Path.Homotopic.Quotient.trans_symm, Path.Homotopic.Quotient.refl_trans]

/-- The conjugacy class of `g` transported from `x₀` to `x₁`, independent of the chosen path. -/
noncomputable def _root_.FundamentalGroup.conjClassAt
    {X : Type*} [TopologicalSpace X] [PathConnectedSpace X]
    (x₀ x₁ : X) (g : _root_.FundamentalGroup X x₀) :
    ConjClasses (_root_.FundamentalGroup X x₁) :=
  ConjClasses.mk (_root_.FundamentalGroup.fundamentalGroupMulEquivOfPathConnected x₀ x₁ g)

/-- Any path from `x₀` to `x₁` realizes the path-independent conjugacy class of `g`. -/
@[simp]
theorem _root_.FundamentalGroup.mk_fundamentalGroupMulEquivOfPath_eq_conjClassAt
    {X : Type*} [TopologicalSpace X] [PathConnectedSpace X]
    {x₀ x₁ : X} (γ : Path x₀ x₁) (g : _root_.FundamentalGroup X x₀) :
    ConjClasses.mk (_root_.FundamentalGroup.fundamentalGroupMulEquivOfPath γ g) =
      _root_.FundamentalGroup.conjClassAt x₀ x₁ g := by
  rw [_root_.FundamentalGroup.conjClassAt, ConjClasses.mk_eq_mk_iff_isConj]
  exact _root_.FundamentalGroup.isConj_fundamentalGroupMulEquivOfPath_apply_of_paths
    γ (PathConnectedSpace.somePath x₀ x₁) g

/-- At the original basepoint, the path-independent class of `g` is the class of `g` itself. -/
@[simp]
theorem _root_.FundamentalGroup.conjClassAt_self
    {X : Type*} [TopologicalSpace X] [PathConnectedSpace X]
    (x : X) (g : _root_.FundamentalGroup X x) :
    _root_.FundamentalGroup.conjClassAt x x g = ConjClasses.mk g := by
  rw [← _root_.FundamentalGroup.mk_fundamentalGroupMulEquivOfPath_eq_conjClassAt (Path.refl x) g,
    _root_.FundamentalGroup.fundamentalGroupMulEquivOfPath_eq_conj]
  have hrefl : _root_.FundamentalGroup.fromPath
      (Path.Homotopic.Quotient.mk (Path.refl x)) = 1 := by
    simp only [Path.Homotopic.Quotient.mk_refl, _root_.FundamentalGroup.one_def]
  rw [MulAut.conj_apply, hrefl]
  simp only [one_mul, inv_one, mul_one]

/-- Transporting a path-independent class along another path gives the class at its endpoint. -/
@[simp]
theorem _root_.FundamentalGroup.map_conjClassAt
    {X : Type*} [TopologicalSpace X] [PathConnectedSpace X]
    {x₀ x₁ x₂ : X} (δ : Path x₁ x₂) (g : _root_.FundamentalGroup X x₀) :
    ConjClasses.map (_root_.FundamentalGroup.fundamentalGroupMulEquivOfPath δ :
        _root_.FundamentalGroup X x₁ →* _root_.FundamentalGroup X x₂)
      (_root_.FundamentalGroup.conjClassAt x₀ x₁ g) =
        _root_.FundamentalGroup.conjClassAt x₀ x₂ g := by
  let γ : Path x₀ x₁ := PathConnectedSpace.somePath x₀ x₁
  rw [← _root_.FundamentalGroup.mk_fundamentalGroupMulEquivOfPath_eq_conjClassAt γ g,
    ConjClasses.map_mk,
    ← _root_.FundamentalGroup.mk_fundamentalGroupMulEquivOfPath_eq_conjClassAt (γ.trans δ) g,
    _root_.FundamentalGroup.fundamentalGroupMulEquivOfPath_trans, MulEquiv.trans_apply,
    MonoidHom.coe_coe]

variable {X : Type*} [TopologicalSpace X] {x₀ x₁ : X}

/-- The subgroup of `π₁(X, x₁)` obtained from `H ≤ π₁(X, x₀)` by changing basepoint along a
path `γ : Path x₀ x₁`. This is the subgroup-level form of conjugating loops by `γ`. -/
noncomputable def basepointChangeSubgroup (γ : Path x₀ x₁)
    (H : Subgroup (_root_.FundamentalGroup X x₀)) :
    Subgroup (_root_.FundamentalGroup X x₁) :=
  H.map (((_root_.FundamentalGroup.fundamentalGroupMulEquivOfPath γ) :
    _root_.FundamentalGroup X x₀ →* _root_.FundamentalGroup X x₁))

/-- Membership in the subgroup transported along a basepoint-change path. -/
lemma mem_basepointChangeSubgroup (γ : Path x₀ x₁) (H : Subgroup (_root_.FundamentalGroup X x₀))
    (g : _root_.FundamentalGroup X x₁) :
    g ∈ basepointChangeSubgroup γ H ↔
      ∃ h ∈ H, _root_.FundamentalGroup.fundamentalGroupMulEquivOfPath γ h = g :=
  Iff.rfl

/-- Membership in a transported subgroup, expressed by applying the inverse basepoint-change
isomorphism. -/
@[simp]
lemma mem_basepointChangeSubgroup_iff (γ : Path x₀ x₁) (H : Subgroup (_root_.FundamentalGroup X x₀))
    (g : _root_.FundamentalGroup X x₁) :
    g ∈ basepointChangeSubgroup γ H ↔
      (_root_.FundamentalGroup.fundamentalGroupMulEquivOfPath γ).symm g ∈ H := by
  simpa [basepointChangeSubgroup] using
    (Subgroup.mem_map_equiv
      (f := _root_.FundamentalGroup.fundamentalGroupMulEquivOfPath γ) (K := H) (x := g))

/-- A subgroup of the target fundamental group is contained in the transported subgroup iff
its inverse basepoint-change image is contained in the original subgroup. -/
lemma le_basepointChangeSubgroup_iff (γ : Path x₀ x₁) (K : Subgroup (_root_.FundamentalGroup X x₁))
    (H : Subgroup (_root_.FundamentalGroup X x₀)) :
    K ≤ basepointChangeSubgroup γ H ↔
      K.map (((_root_.FundamentalGroup.fundamentalGroupMulEquivOfPath γ).symm) :
        _root_.FundamentalGroup X x₁ →* _root_.FundamentalGroup X x₀) ≤ H := by
  rw [basepointChangeSubgroup]
  constructor
  · intro h x hx
    rcases Subgroup.mem_map.mp hx with ⟨y, hyK, rfl⟩
    exact (Subgroup.mem_map_equiv
      (f := _root_.FundamentalGroup.fundamentalGroupMulEquivOfPath γ) (K := H)
        (x := y)).mp (h hyK)
  · intro h y hy
    exact (Subgroup.mem_map_equiv
      (f := _root_.FundamentalGroup.fundamentalGroupMulEquivOfPath γ) (K := H)
        (x := y)).mpr (h (Subgroup.mem_map_of_mem _ hy))

/-- The transported subgroup is contained in a target subgroup iff the original subgroup is
contained in the target subgroup's inverse image under basepoint change. -/
lemma basepointChangeSubgroup_le_iff (γ : Path x₀ x₁) (H : Subgroup (_root_.FundamentalGroup X x₀))
    (K : Subgroup (_root_.FundamentalGroup X x₁)) :
    basepointChangeSubgroup γ H ≤ K ↔
      H ≤ K.comap (((_root_.FundamentalGroup.fundamentalGroupMulEquivOfPath γ) :
        _root_.FundamentalGroup X x₀ →* _root_.FundamentalGroup X x₁)) := by
  rw [basepointChangeSubgroup, Subgroup.map_le_iff_le_comap]

/-- Basepoint-change transport is monotone on subgroups. -/
lemma basepointChangeSubgroup_mono (γ : Path x₀ x₁)
    {H K : Subgroup (_root_.FundamentalGroup X x₀)} (h : H ≤ K) :
    basepointChangeSubgroup γ H ≤ basepointChangeSubgroup γ K := by
  rw [basepointChangeSubgroup, basepointChangeSubgroup]
  exact Subgroup.map_mono h

/-- Normality is invariant under basepoint-change transport. -/
lemma basepointChangeSubgroup_normal_iff (γ : Path x₀ x₁)
    (H : Subgroup (_root_.FundamentalGroup X x₀)) :
    (basepointChangeSubgroup γ H).Normal ↔ H.Normal := by
  rw [basepointChangeSubgroup]
  exact MulEquiv.normal_map_iff

/-- A normal subgroup remains normal after basepoint-change transport. -/
lemma basepointChangeSubgroup.normal (γ : Path x₀ x₁)
    {H : Subgroup (_root_.FundamentalGroup X x₀)} (hH : H.Normal) :
    (basepointChangeSubgroup γ H).Normal :=
  (basepointChangeSubgroup_normal_iff γ H).2 hH

/-- The normalizer quotient `N(H) / H` transported along a basepoint-change path. -/
noncomputable def basepointChangeNormalizerQuotientEquiv (γ : Path x₀ x₁)
    (H : Subgroup (_root_.FundamentalGroup X x₀)) :
    Subgroup.normalizerQuotient H ≃*
      Subgroup.normalizerQuotient (basepointChangeSubgroup γ H) :=
  (Subgroup.normalizerQuotientEquivMap H
    (_root_.FundamentalGroup.fundamentalGroupMulEquivOfPath γ)).trans
    (Subgroup.normalizerQuotientCongr (by rw [basepointChangeSubgroup]))

/-- On normalizer representatives, basepoint-change transport is induced by the
path-conjugation isomorphism of fundamental groups. -/
@[simp]
lemma basepointChangeNormalizerQuotientEquiv_mk (γ : Path x₀ x₁)
    (H : Subgroup (_root_.FundamentalGroup X x₀))
    (g : _root_.Subgroup.normalizer (H : Set (_root_.FundamentalGroup X x₀))) :
    basepointChangeNormalizerQuotientEquiv γ H (g : Subgroup.normalizerQuotient H) =
      ((MulEquiv.subgroupCongr (by rw [basepointChangeSubgroup])
          (Subgroup.normalizerEquivMap H
            (_root_.FundamentalGroup.fundamentalGroupMulEquivOfPath γ) g) :
          _root_.Subgroup.normalizer
            ((basepointChangeSubgroup γ H) : Set (_root_.FundamentalGroup X x₁))) :
        Subgroup.normalizerQuotient (basepointChangeSubgroup γ H)) := by
  rw [← Subgroup.normalizerQuotientMk_apply, ← Subgroup.normalizerQuotientMk_apply,
    basepointChangeNormalizerQuotientEquiv, MulEquiv.trans_apply,
    Subgroup.normalizerQuotientEquivMap_mk,
    Subgroup.normalizerQuotientCongr_mk]

/-- The inverse basepoint-change transport sends a target representative to the inverse
path-conjugation representative. -/
@[simp]
lemma basepointChangeNormalizerQuotientEquiv_symm_mk (γ : Path x₀ x₁)
    (H : Subgroup (_root_.FundamentalGroup X x₀)) (g : _root_.Subgroup.normalizer
      ((basepointChangeSubgroup γ H) : Set (_root_.FundamentalGroup X x₁))) :
    (basepointChangeNormalizerQuotientEquiv γ H).symm
        (g : Subgroup.normalizerQuotient (basepointChangeSubgroup γ H)) =
      (((Subgroup.normalizerEquivMap H
          (_root_.FundamentalGroup.fundamentalGroupMulEquivOfPath γ)).symm
          ((MulEquiv.subgroupCongr (by rw [basepointChangeSubgroup])).symm g)) :
        Subgroup.normalizerQuotient H) := by
  rw [← Subgroup.normalizerQuotientMk_apply, ← Subgroup.normalizerQuotientMk_apply,
    basepointChangeNormalizerQuotientEquiv, MulEquiv.symm_trans_apply,
    Subgroup.normalizerQuotientCongr_symm_mk, Subgroup.normalizerQuotientEquivMap_symm_mk]
  -- The forward and inverse `subgroupCongr` agree on representatives (both are the identity on
  -- underlying elements), so the two transported representatives coincide.
  rfl

/-- On representatives, basepoint-change transport applies the path-conjugation isomorphism
of fundamental groups. -/
lemma basepointChangeNormalizerQuotientEquiv_mk_coe (γ : Path x₀ x₁)
    (H : Subgroup (_root_.FundamentalGroup X x₀))
    (g : _root_.Subgroup.normalizer (H : Set (_root_.FundamentalGroup X x₀))) :
    basepointChangeNormalizerQuotientEquiv γ H (Subgroup.normalizerQuotientMk H g) =
      Subgroup.normalizerQuotientMk (basepointChangeSubgroup γ H)
        (MulEquiv.subgroupCongr (by rw [basepointChangeSubgroup])
          (⟨_root_.FundamentalGroup.fundamentalGroupMulEquivOfPath γ
              (g : _root_.FundamentalGroup X x₀),
            by
              rw [← Subgroup.normalizerEquivMap_apply_coe H
                (_root_.FundamentalGroup.fundamentalGroupMulEquivOfPath γ) g]
              exact (Subgroup.normalizerEquivMap H
                (_root_.FundamentalGroup.fundamentalGroupMulEquivOfPath γ) g).2⟩ :
            _root_.Subgroup.normalizer
              ((H.map ((_root_.FundamentalGroup.fundamentalGroupMulEquivOfPath γ) :
                _root_.FundamentalGroup X x₀ →* _root_.FundamentalGroup X x₁)) :
                  Set (_root_.FundamentalGroup X x₁)))) := by
  rw [basepointChangeNormalizerQuotientEquiv, MulEquiv.trans_apply,
    Subgroup.normalizerQuotientEquivMap_mk_coe,
    Subgroup.normalizerQuotientCongr_mk]

end FundamentalGroup

end TauCeti
