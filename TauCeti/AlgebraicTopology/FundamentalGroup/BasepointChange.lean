/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
public import TauCeti.Algebra.Group.Conj
public import TauCeti.Algebra.Group.NormalizerQuotient.Conjugation
import Mathlib.Tactic.Group

/-!
# Basepoint change for fundamental groups

The pointed classification of connected covers records a subgroup of the fundamental group at
a chosen basepoint. Changing the basepoint along a path transports that subgroup by the
standard path-conjugation isomorphism of fundamental groups. This file packages that transport
and the induced transport of the normalizer quotient `N(H) / H` used for deck groups of covers
attached to subgroups. It also descends basepoint change to conjugacy classes, where the result is
independent of the chosen path.

It also records the element-level behaviour of the transport: path-quotient formulas and its
compatibility with concatenation of paths.

Mathlib already supplies the fundamental-group isomorphism
`FundamentalGroup.fundamentalGroupMulEquivOfPath`; the declarations here are the computation
rules, subgroup, and normalizer-quotient bookkeeping built on it.

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
* `FundamentalGroup.conjClassesEquivOfPath`: the induced equivalence of conjugacy classes.
* `FundamentalGroup.conjClassesEquivOfPath_eq`: this equivalence is independent of the path.
* `FundamentalGroup.conjClassesEquivOfPathConnected_trans`: canonical conjugacy-class transport
  in a path-connected space is natural under further path transport.
* `TauCeti.FundamentalGroup.mem_basepointChangeSubgroup` and the representative `[simp]`
  lemmas for membership and quotient calculations under these domain-specific names.

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

open CategoryTheory in
/-- Basepoint change along `γ` is represented by conjugation with `γ` in the path quotient: a loop
`g` at `x₀` goes to the class of `γ⁻¹ ⬝ g ⬝ γ`. This is the forward counterpart of
`FundamentalGroup.fundamentalGroupMulEquivOfPath_symm_apply`. -/
@[simp]
lemma _root_.FundamentalGroup.fundamentalGroupMulEquivOfPath_apply
    {X : Type*} [TopologicalSpace X] {x₀ x₁ : X}
    (γ : Path x₀ x₁) (g : _root_.FundamentalGroup X x₀) :
    _root_.FundamentalGroup.fundamentalGroupMulEquivOfPath γ g =
      Path.Homotopic.Quotient.trans (Path.Homotopic.Quotient.mk γ).symm
        (Path.Homotopic.Quotient.trans g (Path.Homotopic.Quotient.mk γ)) := by
  let γq : Path.Homotopic.Quotient x₀ x₁ := Path.Homotopic.Quotient.mk γ
  let α : FundamentalGroupoid.mk x₀ ≅ FundamentalGroupoid.mk x₁ :=
    (Groupoid.isoEquivHom _ _).symm γq
  -- Mathlib defines the transport as `α.conj`; the groupoid arrow and path quotient are
  -- definitionally the same type (`FundamentalGroupoid.Hom` is a path quotient).
  change α.conj g = γq.symm.trans (g.trans γq)
  rw [CategoryTheory.Iso.conj_apply]
  rfl

open CategoryTheory in
/-- Basepoint change along a concatenated path is basepoint change along each piece in turn. -/
@[simp]
lemma _root_.FundamentalGroup.fundamentalGroupMulEquivOfPath_trans
    {X : Type*} [TopologicalSpace X] {x₀ x₁ x₂ : X} (γ : Path x₀ x₁) (δ : Path x₁ x₂) :
    _root_.FundamentalGroup.fundamentalGroupMulEquivOfPath (γ.trans δ) =
      (_root_.FundamentalGroup.fundamentalGroupMulEquivOfPath γ).trans
        (_root_.FundamentalGroup.fundamentalGroupMulEquivOfPath δ) := by
  let α : FundamentalGroupoid.mk x₀ ≅ FundamentalGroupoid.mk x₁ :=
    (Groupoid.isoEquivHom _ _).symm (Path.Homotopic.Quotient.mk γ)
  let β : FundamentalGroupoid.mk x₁ ≅ FundamentalGroupoid.mk x₂ :=
    (Groupoid.isoEquivHom _ _).symm (Path.Homotopic.Quotient.mk δ)
  have h : (Groupoid.isoEquivHom (FundamentalGroupoid.mk x₀)
      (FundamentalGroupoid.mk x₂)).symm (Path.Homotopic.Quotient.mk (γ.trans δ)) =
        α ≪≫ β := by
    apply CategoryTheory.Iso.ext
    -- `Iso.ext` exposes groupoid arrows; composition there is path-quotient concatenation.
    change Path.Homotopic.Quotient.mk (γ.trans δ) =
      Path.Homotopic.Quotient.trans (Path.Homotopic.Quotient.mk γ)
        (Path.Homotopic.Quotient.mk δ)
    exact Path.Homotopic.Quotient.mk_trans γ δ
  ext g
  -- Unfold Mathlib's path transport to `Iso.conj` on the associated groupoid arrows.
  change ((Groupoid.isoEquivHom _ _).symm
      (Path.Homotopic.Quotient.mk (γ.trans δ))).conj g = β.conj (α.conj g)
  rw [h]
  exact CategoryTheory.Iso.trans_conj α β g

/-- Reversing a basepoint-change path gives the inverse equivalence of fundamental groups. -/
@[simp]
lemma _root_.FundamentalGroup.fundamentalGroupMulEquivOfPath_symm
    {X : Type*} [TopologicalSpace X] {x₀ x₁ : X} (γ : Path x₀ x₁) :
    _root_.FundamentalGroup.fundamentalGroupMulEquivOfPath γ.symm =
      (_root_.FundamentalGroup.fundamentalGroupMulEquivOfPath γ).symm := by
  ext g
  rw [_root_.FundamentalGroup.fundamentalGroupMulEquivOfPath_apply,
    _root_.FundamentalGroup.fundamentalGroupMulEquivOfPath_symm_apply]
  have hsymm : (Path.Homotopic.Quotient.mk γ).symm.symm =
      Path.Homotopic.Quotient.mk γ := by
    rw [← Path.Homotopic.Quotient.mk_symm, ← Path.Homotopic.Quotient.mk_symm,
      Path.symm_symm]
  rw [Path.Homotopic.Quotient.mk_symm, hsymm]

/-- Basepoint change along the constant path is the identity equivalence. -/
@[simp]
lemma _root_.FundamentalGroup.fundamentalGroupMulEquivOfPath_refl
    {X : Type*} [TopologicalSpace X] (x : X) :
    _root_.FundamentalGroup.fundamentalGroupMulEquivOfPath (Path.refl x) =
      MulEquiv.refl (_root_.FundamentalGroup X x) := by
  ext g
  rw [_root_.FundamentalGroup.fundamentalGroupMulEquivOfPath_apply]
  have hrefl : (Path.Homotopic.Quotient.refl x).symm =
      Path.Homotopic.Quotient.refl x := by
    rw [← Path.Homotopic.Quotient.mk_refl, ← Path.Homotopic.Quotient.mk_symm,
      Path.refl_symm, Path.Homotopic.Quotient.mk_refl]
  rw [Path.Homotopic.Quotient.mk_refl, hrefl,
    Path.Homotopic.Quotient.trans_refl, Path.Homotopic.Quotient.refl_trans,
    MulEquiv.refl_apply]

/-- Changing basepoint along a path induces an equivalence between conjugacy classes in the two
fundamental groups. -/
noncomputable def _root_.FundamentalGroup.conjClassesEquivOfPath
    {X : Type*} [TopologicalSpace X] {x₀ x₁ : X} (γ : Path x₀ x₁) :
    ConjClasses (_root_.FundamentalGroup X x₀) ≃
      ConjClasses (_root_.FundamentalGroup X x₁) :=
  (_root_.FundamentalGroup.fundamentalGroupMulEquivOfPath γ).conjClassesEquiv

/-- On a representative, transport of conjugacy classes is induced by the usual basepoint-change
equivalence of fundamental groups. -/
@[simp]
lemma _root_.FundamentalGroup.conjClassesEquivOfPath_mk
    {X : Type*} [TopologicalSpace X] {x₀ x₁ : X} (γ : Path x₀ x₁)
    (g : _root_.FundamentalGroup X x₀) :
    _root_.FundamentalGroup.conjClassesEquivOfPath γ (ConjClasses.mk g) =
      ConjClasses.mk (_root_.FundamentalGroup.fundamentalGroupMulEquivOfPath γ g) := by
  exact MulEquiv.conjClassesEquiv_mk
    (_root_.FundamentalGroup.fundamentalGroupMulEquivOfPath γ) g

/-- Transport of conjugacy classes along a concatenated path is transport along each piece in
turn. -/
@[simp]
lemma _root_.FundamentalGroup.conjClassesEquivOfPath_trans
    {X : Type*} [TopologicalSpace X] {x₀ x₁ x₂ : X} (γ : Path x₀ x₁) (δ : Path x₁ x₂) :
    _root_.FundamentalGroup.conjClassesEquivOfPath (γ.trans δ) =
      (_root_.FundamentalGroup.conjClassesEquivOfPath γ).trans
        (_root_.FundamentalGroup.conjClassesEquivOfPath δ) := by
  simp only [_root_.FundamentalGroup.conjClassesEquivOfPath,
    _root_.FundamentalGroup.fundamentalGroupMulEquivOfPath_trans,
    MulEquiv.conjClassesEquiv_trans]

/-- Transport along a concatenated path acts by the two transports in succession. -/
lemma _root_.FundamentalGroup.conjClassesEquivOfPath_trans_apply
    {X : Type*} [TopologicalSpace X] {x₀ x₁ x₂ : X} (γ : Path x₀ x₁) (δ : Path x₁ x₂)
    (C : ConjClasses (_root_.FundamentalGroup X x₀)) :
    _root_.FundamentalGroup.conjClassesEquivOfPath (γ.trans δ) C =
      _root_.FundamentalGroup.conjClassesEquivOfPath δ
        (_root_.FundamentalGroup.conjClassesEquivOfPath γ C) := by
  rw [_root_.FundamentalGroup.conjClassesEquivOfPath_trans]
  rfl

/-- Reversing a path gives the inverse equivalence on conjugacy classes. -/
@[simp]
lemma _root_.FundamentalGroup.conjClassesEquivOfPath_symm
    {X : Type*} [TopologicalSpace X] {x₀ x₁ : X} (γ : Path x₀ x₁) :
    _root_.FundamentalGroup.conjClassesEquivOfPath γ.symm =
      (_root_.FundamentalGroup.conjClassesEquivOfPath γ).symm := by
  simp only [_root_.FundamentalGroup.conjClassesEquivOfPath,
    _root_.FundamentalGroup.fundamentalGroupMulEquivOfPath_symm,
    MulEquiv.conjClassesEquiv_symm]

/-- Transport along the constant path is the identity on conjugacy classes. -/
@[simp]
lemma _root_.FundamentalGroup.conjClassesEquivOfPath_refl
    {X : Type*} [TopologicalSpace X] (x : X) :
    _root_.FundamentalGroup.conjClassesEquivOfPath (Path.refl x) =
      Equiv.refl (ConjClasses (_root_.FundamentalGroup X x)) := by
  simp only [_root_.FundamentalGroup.conjClassesEquivOfPath,
    _root_.FundamentalGroup.fundamentalGroupMulEquivOfPath_refl,
    MulEquiv.conjClassesEquiv_refl]

/-- **Conjugacy-class basepoint change is independent of the path.** Two paths with the same
endpoints can change individual fundamental-group elements by an inner automorphism, but induce
the same equivalence on conjugacy classes. -/
lemma _root_.FundamentalGroup.conjClassesEquivOfPath_eq
    {X : Type*} [TopologicalSpace X] {x₀ x₁ : X} (γ δ : Path x₀ x₁) :
    _root_.FundamentalGroup.conjClassesEquivOfPath γ =
      _root_.FundamentalGroup.conjClassesEquivOfPath δ := by
  ext C
  obtain ⟨g, rfl⟩ := ConjClasses.exists_rep C
  rw [_root_.FundamentalGroup.conjClassesEquivOfPath_mk,
    _root_.FundamentalGroup.conjClassesEquivOfPath_mk,
    ConjClasses.mk_eq_mk_iff_isConj, isConj_iff]
  let q := _root_.FundamentalGroup.fromPath
    (Path.Homotopic.Quotient.mk (γ.symm.trans δ))
  have htransport :
      (_root_.FundamentalGroup.fundamentalGroupMulEquivOfPath γ).symm.trans
          (_root_.FundamentalGroup.fundamentalGroupMulEquivOfPath δ) =
        MulAut.conj q := by
    rw [← _root_.FundamentalGroup.fundamentalGroupMulEquivOfPath_symm,
      ← _root_.FundamentalGroup.fundamentalGroupMulEquivOfPath_trans]
    exact _root_.FundamentalGroup.fundamentalGroupMulEquivOfPath_eq_conj (γ.symm.trans δ)
  refine ⟨q, ?_⟩
  calc
    q * _root_.FundamentalGroup.fundamentalGroupMulEquivOfPath γ g * q⁻¹ =
        MulAut.conj q (_root_.FundamentalGroup.fundamentalGroupMulEquivOfPath γ g) :=
          (MulAut.conj_apply q _).symm
    _ = ((_root_.FundamentalGroup.fundamentalGroupMulEquivOfPath γ).symm.trans
          (_root_.FundamentalGroup.fundamentalGroupMulEquivOfPath δ))
          (_root_.FundamentalGroup.fundamentalGroupMulEquivOfPath γ g) := by rw [htransport]
    _ = _root_.FundamentalGroup.fundamentalGroupMulEquivOfPath δ g := by
      rw [MulEquiv.trans_apply, MulEquiv.symm_apply_apply]

/-- In a path-connected space, conjugacy classes of fundamental groups at two points are
canonically equivalent: the result does not depend on the path chosen by the instance. -/
noncomputable def _root_.FundamentalGroup.conjClassesEquivOfPathConnected
    {X : Type*} [TopologicalSpace X] [PathConnectedSpace X] (x₀ x₁ : X) :
    ConjClasses (_root_.FundamentalGroup X x₀) ≃
      ConjClasses (_root_.FundamentalGroup X x₁) :=
  _root_.FundamentalGroup.conjClassesEquivOfPath (PathConnectedSpace.somePath x₀ x₁)

/-- The canonical equivalence of conjugacy classes in a path-connected space agrees with
transport along any specified path. -/
lemma _root_.FundamentalGroup.conjClassesEquivOfPathConnected_eq
    {X : Type*} [TopologicalSpace X] [PathConnectedSpace X] {x₀ x₁ : X}
    (γ : Path x₀ x₁) :
    _root_.FundamentalGroup.conjClassesEquivOfPathConnected x₀ x₁ =
      _root_.FundamentalGroup.conjClassesEquivOfPath γ :=
  _root_.FundamentalGroup.conjClassesEquivOfPath_eq _ _

/-- Canonical conjugacy-class transport from a point to itself is the identity. -/
@[simp]
lemma _root_.FundamentalGroup.conjClassesEquivOfPathConnected_self
    {X : Type*} [TopologicalSpace X] [PathConnectedSpace X] (x : X) :
    _root_.FundamentalGroup.conjClassesEquivOfPathConnected x x =
      Equiv.refl (ConjClasses (_root_.FundamentalGroup X x)) := by
  rw [_root_.FundamentalGroup.conjClassesEquivOfPathConnected_eq (Path.refl x),
    _root_.FundamentalGroup.conjClassesEquivOfPath_refl]

/-- Reversing the endpoints of canonical conjugacy-class transport gives its inverse. -/
@[simp]
lemma _root_.FundamentalGroup.conjClassesEquivOfPathConnected_symm
    {X : Type*} [TopologicalSpace X] [PathConnectedSpace X] (x₀ x₁ : X) :
    (_root_.FundamentalGroup.conjClassesEquivOfPathConnected x₀ x₁).symm =
      _root_.FundamentalGroup.conjClassesEquivOfPathConnected x₁ x₀ := by
  let γ := PathConnectedSpace.somePath x₀ x₁
  rw [_root_.FundamentalGroup.conjClassesEquivOfPathConnected_eq γ,
    _root_.FundamentalGroup.conjClassesEquivOfPathConnected_eq γ.symm,
    _root_.FundamentalGroup.conjClassesEquivOfPath_symm]

/-- Canonical conjugacy-class transport in a path-connected space is compatible with subsequent
transport along a specified path. -/
@[simp]
lemma _root_.FundamentalGroup.conjClassesEquivOfPathConnected_trans
    {X : Type*} [TopologicalSpace X] [PathConnectedSpace X] (b : X) {x₀ x₁ : X}
    (γ : Path x₀ x₁) :
    (_root_.FundamentalGroup.conjClassesEquivOfPathConnected b x₀).trans
        (_root_.FundamentalGroup.conjClassesEquivOfPath γ) =
      _root_.FundamentalGroup.conjClassesEquivOfPathConnected b x₁ := by
  rw [_root_.FundamentalGroup.conjClassesEquivOfPathConnected,
    ← _root_.FundamentalGroup.conjClassesEquivOfPath_trans]
  exact _root_.FundamentalGroup.conjClassesEquivOfPath_eq _ _

/-- Applying path transport after canonical transport is canonical transport to the new
basepoint. -/
@[simp]
lemma _root_.FundamentalGroup.conjClassesEquivOfPath_conjClassesEquivOfPathConnected
    {X : Type*} [TopologicalSpace X] [PathConnectedSpace X] (b : X) {x₀ x₁ : X}
    (γ : Path x₀ x₁) (C : ConjClasses (_root_.FundamentalGroup X b)) :
    _root_.FundamentalGroup.conjClassesEquivOfPath γ
        (_root_.FundamentalGroup.conjClassesEquivOfPathConnected b x₀ C) =
      _root_.FundamentalGroup.conjClassesEquivOfPathConnected b x₁ C := by
  rw [← Equiv.trans_apply,
    _root_.FundamentalGroup.conjClassesEquivOfPathConnected_trans]

/-- Applying canonical transport twice is canonical transport directly to the final basepoint. -/
@[simp]
lemma _root_.FundamentalGroup.conjClassesEquivOfPathConnected_trans_conjClassesEquivOfPathConnected
    {X : Type*} [TopologicalSpace X] [PathConnectedSpace X] (b x₀ x₁ : X)
    (C : ConjClasses (_root_.FundamentalGroup X b)) :
    _root_.FundamentalGroup.conjClassesEquivOfPathConnected x₀ x₁
        (_root_.FundamentalGroup.conjClassesEquivOfPathConnected b x₀ C) =
      _root_.FundamentalGroup.conjClassesEquivOfPathConnected b x₁ C := by
  rw [_root_.FundamentalGroup.conjClassesEquivOfPathConnected_eq
      (PathConnectedSpace.somePath x₀ x₁),
    _root_.FundamentalGroup.conjClassesEquivOfPath_conjClassesEquivOfPathConnected]

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
