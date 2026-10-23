/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.InducedMaps
public import TauCeti.Algebra.Group.Conj
public import TauCeti.Algebra.Group.NormalizerQuotient.Conjugation
import Mathlib.Tactic.Group
import TauCeti.AlgebraicTopology.FundamentalGroup.Basic
import TauCeti.AlgebraicTopology.FundamentalGroup.Homeomorph
import TauCeti.Topology.Homotopy.Path

/-!
# Basepoint change for fundamental groups

The pointed classification of connected covers records a subgroup of the fundamental group at
a chosen basepoint. Changing the basepoint along a path transports that subgroup by the
standard path-conjugation isomorphism of fundamental groups. This file packages that transport
and the induced transport of the normalizer quotient `N(H) / H` used for deck groups of covers
attached to subgroups. It also descends basepoint change to conjugacy classes, where the result is
independent of the chosen path.

It also records the element-level behaviour of the transport: path-quotient formulas, its
compatibility with concatenation of paths and with induced maps, and the comparison of the maps
induced by freely homotopic maps, which differ by basepoint change along the trace of the homotopy.

Mathlib already supplies the fundamental-group isomorphism
`FundamentalGroup.fundamentalGroupMulEquivOfPath`; the declarations here are the computation
rules, subgroup, and normalizer-quotient bookkeeping built on it.

## Main declarations

* `FundamentalGroup.basepointChangeSubgroup`: transport a subgroup of `π₁(X, x₀)`
  along a path `γ : Path x₀ x₁`.
* Domain-specific membership, inclusion, monotonicity, and normality lemmas for
  `basepointChangeSubgroup`.
* `FundamentalGroup.basepointChangeNormalizerQuotientEquiv`: the corresponding
  isomorphism `N(H) / H ≃* N(γ₊H) / γ₊H`.
* `FundamentalGroup.fundamentalGroupMulEquivOfPath_apply` and
  `FundamentalGroup.fundamentalGroupMulEquivOfPath_symm_apply`: basepoint change as conjugation
  by the path in the path quotient.
* `FundamentalGroup.fundamentalGroupMulEquivOfPath_trans`: basepoint change along a concatenated
  path is the composite of the basepoint changes.
* `FundamentalGroup.fundamentalGroupMulEquivOfPath_eq_conj`: basepoint change along a loop is
  conjugation by its class.
* `FundamentalGroup.map_fundamentalGroupMulEquivOfPath`: induced maps commute with basepoint
  change.
* `ContinuousMap.Homotopy.fundamentalGroupMulEquivOfPath_evalAt_map`: **freely homotopic maps
  induce the same map on fundamental groups, up to basepoint change along the trace of the
  homotopy.**
* `ContinuousMap.Homotopy.exists_path_fundamentalGroupMulEquivOfPath_map_comp`: composing with a
  homotopy right inverse `s` of `f` realizes, up to basepoint change, any homomorphism through
  which `g_*` factors via `f_*`.
* `FundamentalGroup.conjClassesEquivOfPath`: the induced equivalence of conjugacy classes.
* `FundamentalGroup.conjClassesEquivOfPath_eq`: this equivalence is independent of the path.
* `FundamentalGroup.conjClassesEquivOfPathConnected_trans`: canonical conjugacy-class transport
  in a path-connected space is natural under further path transport.
* `FundamentalGroup.mem_basepointChangeSubgroup` and the representative `[simp]`
  lemmas for membership and quotient calculations under these domain-specific names.

-/

public section

open TauCeti

namespace FundamentalGroup

open CategoryTheory in
/-- The inverse basepoint-change equivalence is represented by conjugation with the reverse path.
This path-quotient formula is the interface for computations with the equivalence. -/
@[simp]
lemma fundamentalGroupMulEquivOfPath_symm_apply
    {X : Type*} [TopologicalSpace X] {x₀ x₁ : X}
    (γ : Path x₀ x₁) (g : FundamentalGroup X x₁) :
    (fundamentalGroupMulEquivOfPath γ).symm g =
      .of (Path.Homotopic.Quotient.trans (Path.Homotopic.Quotient.mk γ)
        (Path.Homotopic.Quotient.trans g.asHom (Path.Homotopic.Quotient.mk γ).symm)) := by
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
  have hconj : (End.of (Path.Homotopic.Quotient.trans γq
      (Path.Homotopic.Quotient.trans g.asHom γq.symm)) : FundamentalGroup X x₀) =
        α.symm.conj g := by
    ext
    rw [CategoryTheory.Iso.conj_apply_asHom, CategoryTheory.Iso.symm_inv,
      CategoryTheory.Iso.symm_hom, hα_hom, hα_inv]
    simp only [FundamentalGroupoid.comp_eq]
  rw [hconj]
  exact (α.self_symm_conj g).symm

/-- **Basepoint change along a loop is an inner automorphism.** For a loop `γ` at `x`, changing
basepoint along `γ` is conjugation by the class of `γ` in `π₁(X, x)`. In particular it is invisible
to any homomorphism from `π₁(X, x)` to a commutative group. -/
lemma fundamentalGroupMulEquivOfPath_eq_conj {X : Type*}
    [TopologicalSpace X] {x : X} (γ : Path x x) :
    fundamentalGroupMulEquivOfPath γ =
      MulAut.conj (fromPath (Path.Homotopic.Quotient.mk γ)) := by
  ext g : 1
  rw [MulAut.conj_apply, ← MulEquiv.eq_symm_apply,
    fundamentalGroupMulEquivOfPath_symm_apply]
  -- In `π₁(X, x)` concatenation is multiplication in the reverse order and reversal is inversion
  -- (`FundamentalGroup.mul_def`, `FundamentalGroup.inv_def`); restate the path formula as a word.
  let c : FundamentalGroup X x := fromPath (Path.Homotopic.Quotient.mk γ)
  change g = c⁻¹ * (c * g * c⁻¹) * c
  group

open CategoryTheory in
/-- Basepoint change along `γ` is represented by conjugation with `γ` in the path quotient: a loop
`g` at `x₀` goes to the class of `γ⁻¹ ⬝ g ⬝ γ`. This is the forward counterpart of
`FundamentalGroup.fundamentalGroupMulEquivOfPath_symm_apply`. -/
@[simp]
lemma fundamentalGroupMulEquivOfPath_apply
    {X : Type*} [TopologicalSpace X] {x₀ x₁ : X}
    (γ : Path x₀ x₁) (g : FundamentalGroup X x₀) :
    fundamentalGroupMulEquivOfPath γ g =
      .of (Path.Homotopic.Quotient.trans (Path.Homotopic.Quotient.mk γ).symm
        (Path.Homotopic.Quotient.trans g.asHom (Path.Homotopic.Quotient.mk γ))) := by
  let γq : Path.Homotopic.Quotient x₀ x₁ := Path.Homotopic.Quotient.mk γ
  let α : FundamentalGroupoid.mk x₀ ≅ FundamentalGroupoid.mk x₁ :=
    (Groupoid.isoEquivHom _ _).symm γq
  -- Mathlib defines the transport as `α.conj`; the groupoid arrow and path quotient are
  -- definitionally the same type (`FundamentalGroupoid.Hom` is a path quotient).
  change α.conj g = .of (γq.symm.trans (g.asHom.trans γq))
  ext
  rw [CategoryTheory.Iso.conj_apply_asHom]
  rfl

open CategoryTheory in
/-- Basepoint change along a concatenated path is basepoint change along each piece in turn. -/
@[simp]
lemma fundamentalGroupMulEquivOfPath_trans
    {X : Type*} [TopologicalSpace X] {x₀ x₁ x₂ : X} (γ : Path x₀ x₁) (δ : Path x₁ x₂) :
    fundamentalGroupMulEquivOfPath (γ.trans δ) =
      (fundamentalGroupMulEquivOfPath γ).trans
        (fundamentalGroupMulEquivOfPath δ) := by
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
  ext g : 1
  -- Unfold Mathlib's path transport to `Iso.conj` on the associated groupoid arrows.
  change ((Groupoid.isoEquivHom _ _).symm
      (Path.Homotopic.Quotient.mk (γ.trans δ))).conj g = β.conj (α.conj g)
  rw [h]
  exact CategoryTheory.Iso.trans_conj α β g

/-- Reversing a basepoint-change path gives the inverse equivalence of fundamental groups. -/
@[simp]
lemma fundamentalGroupMulEquivOfPath_symm
    {X : Type*} [TopologicalSpace X] {x₀ x₁ : X} (γ : Path x₀ x₁) :
    fundamentalGroupMulEquivOfPath γ.symm =
      (fundamentalGroupMulEquivOfPath γ).symm := by
  ext g
  simp

/-- Basepoint change along the constant path is the identity equivalence. -/
@[simp]
lemma fundamentalGroupMulEquivOfPath_refl
    {X : Type*} [TopologicalSpace X] (x : X) :
    fundamentalGroupMulEquivOfPath (Path.refl x) =
      MulEquiv.refl (FundamentalGroup X x) := by
  ext g
  simp

open CategoryTheory in
/-- **Induced maps commute with basepoint change.** Changing basepoint along `γ` and then applying
`f` is applying `f` and then changing basepoint along the image path `γ.map f.continuous`. -/
lemma map_fundamentalGroupMulEquivOfPath {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {x₀ x₁ : X} (f : C(X, Y)) (γ : Path x₀ x₁) (g : FundamentalGroup X x₀) :
    map f x₁ (fundamentalGroupMulEquivOfPath γ g) =
      fundamentalGroupMulEquivOfPath (γ.map f.continuous) (map f x₀ g) := by
  -- `FundamentalGroupoid.map f` sends the class of `γ` to the class of `γ.map f.continuous` by
  -- definition, so the image of the basepoint-change isomorphism is the one along the image path.
  have hα : (FundamentalGroupoid.map f).mapIso ((Groupoid.isoEquivHom _ _).symm ⟦γ⟧) =
      (Groupoid.isoEquivHom _ _).symm ⟦γ.map f.continuous⟧ := Iso.ext rfl
  ext
  refine (Functor.map_conj (FundamentalGroupoid.map f) _ g).trans ?_
  rw [hα]
  -- Mathlib defines basepoint change as `Iso.conj` and `FundamentalGroup.map` as
  -- `Functor.mapEnd`, so the two sides now agree by unfolding these definitions.
  rfl

open CategoryTheory in
/-- **Freely homotopic maps induce the same map on fundamental groups, up to basepoint change.**
A homotopy `H` from `f₀` to `f₁` moves the image of the basepoint `x` along its trace
`H.evalAt x`, and changing basepoint along this trace carries the map induced by `f₀` to the map
induced by `f₁`. This is the naturality of Mathlib's
`FundamentalGroupoidFunctor.homotopicMapsNatIso`, read on endomorphisms of `x`. -/
lemma _root_.ContinuousMap.Homotopy.fundamentalGroupMulEquivOfPath_evalAt_map {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] {f₀ f₁ : C(X, Y)} (H : f₀.Homotopy f₁) (x : X)
    (g : FundamentalGroup X x) :
    fundamentalGroupMulEquivOfPath (H.evalAt x) (map f₀ x g) = map f₁ x g := by
  let α : FundamentalGroupoid.mk (f₀ x) ≅ FundamentalGroupoid.mk (f₁ x) :=
    (Groupoid.isoEquivHom _ _).symm ⟦H.evalAt x⟧
  -- The component of `homotopicMapsNatIso H` at `x` is `α.hom`, by `homotopicMapsNatIso_app`.
  have h : (FundamentalGroupoid.map f₀).map g.asHom ≫ α.hom =
      α.hom ≫ (FundamentalGroupoid.map f₁).map g.asHom := by
    have h := (FundamentalGroupoidFunctor.homotopicMapsNatIso H).naturality g.asHom
    rwa [FundamentalGroupoidFunctor.homotopicMapsNatIso_app] at h
  ext
  exact (Iso.conj_apply_asHom α _).trans
    ((congrArg (α.inv ≫ ·) h).trans (Iso.inv_hom_id_assoc α _))

/-- **Basepoint change through a homotopy right inverse.** If `s` is a right inverse of `f` up to
the homotopy `H`, then `g ∘ s` induces on fundamental groups any homomorphism `φ` with
`φ ∘ f_* = g_*`, up to a change of base point in the target. The path changing the base point
combines the image under `g` of a path from `w` to `s x` with a loop at `y` correcting by an inner
automorphism. -/
lemma _root_.ContinuousMap.Homotopy.exists_path_fundamentalGroupMulEquivOfPath_map_comp
    {W X Y : Type*} [TopologicalSpace W] [TopologicalSpace X] [TopologicalSpace Y]
    [PathConnectedSpace W] {f : C(W, X)} {g : C(W, Y)} {s : C(X, W)}
    (H : (f.comp s).Homotopy (ContinuousMap.id X)) {w : W} {x : X} {y : Y} (hf : f w = x)
    (hg : g w = y) (φ : FundamentalGroup X x →* FundamentalGroup Y y)
    (hφ : φ.comp (mapOfEq f hf) = mapOfEq g hg) :
    ∃ γ : Path (g (s x)) y,
      ∀ a, fundamentalGroupMulEquivOfPath γ (map (g.comp s) x a) = φ a := by
  subst hf hg
  rw [FundamentalGroup.mapOfEq_rfl, FundamentalGroup.mapOfEq_rfl] at hφ
  let α : Path w (s (f w)) := PathConnectedSpace.somePath _ _
  -- The trace of `H` at `f w`, read as a path ending at `f w` rather than at `id (f w)`.
  let δ : Path (f (s (f w))) (f w) := H.evalAt (f w)
  let c : FundamentalGroup X (f w) :=
    fromPath (Path.Homotopic.Quotient.mk ((α.map f.continuous).trans δ))
  let ℓ : Path (g w) (g w) := Quotient.out (toPath (φ c))
  refine ⟨(α.map g.continuous).symm.trans ℓ, fun a ↦ ?_⟩
  obtain ⟨b, hb⟩ := (fundamentalGroupMulEquivOfPath α).surjective (map s (f w) a)
  -- Both `(f ∘ s)_* a` and `(g ∘ s)_* a` are computed through `b`, by naturality of basepoint
  -- change.
  have hfs : map (f.comp s) (f w) a =
      fundamentalGroupMulEquivOfPath (α.map f.continuous) (map f w b) := by
    rw [map_comp, MonoidHom.comp_apply, ← hb, map_fundamentalGroupMulEquivOfPath]
  have hgs : map (g.comp s) (f w) a =
      fundamentalGroupMulEquivOfPath (α.map g.continuous) (map g w b) := by
    rw [map_comp, MonoidHom.comp_apply, ← hb, map_fundamentalGroupMulEquivOfPath]
  -- The trace formula for `H` gives `f_* b = c⁻¹ a c`.
  have h₁ : c * map f w b * c⁻¹ = a := calc
    _ = fundamentalGroupMulEquivOfPath ((α.map f.continuous).trans δ) (map f w b) := by
      rw [fundamentalGroupMulEquivOfPath_eq_conj, MulAut.conj_apply]
    _ = a := by
      rw [fundamentalGroupMulEquivOfPath_trans, MulEquiv.trans_apply, ← hfs]
      exact (H.fundamentalGroupMulEquivOfPath_evalAt_map (f w) a).trans
        (DFunLike.congr_fun (map_id (f w)) a)
  -- Hence `(g ∘ s)_* a`, moved back to `y` along `g ∘ α`, is `g_* b = φ (c⁻¹ a c)`.
  calc
    _ = fundamentalGroupMulEquivOfPath ℓ (map g w b) := by
      rw [hgs, fundamentalGroupMulEquivOfPath_trans, MulEquiv.trans_apply,
        fundamentalGroupMulEquivOfPath_symm, MulEquiv.symm_apply_apply]
    _ = φ (c * map f w b * c⁻¹) := by
      rw [fundamentalGroupMulEquivOfPath_eq_conj, fromPath_mk_out, ← hφ]
      simp
    _ = φ a := by rw [h₁]

/-- Changing basepoint along a path induces an equivalence between conjugacy classes in the two
fundamental groups. -/
noncomputable def conjClassesEquivOfPath
    {X : Type*} [TopologicalSpace X] {x₀ x₁ : X} (γ : Path x₀ x₁) :
    ConjClasses (FundamentalGroup X x₀) ≃
      ConjClasses (FundamentalGroup X x₁) :=
  (fundamentalGroupMulEquivOfPath γ).conjClassesEquiv

/-- On a representative, transport of conjugacy classes is induced by the usual basepoint-change
equivalence of fundamental groups. -/
@[simp]
lemma conjClassesEquivOfPath_mk
    {X : Type*} [TopologicalSpace X] {x₀ x₁ : X} (γ : Path x₀ x₁)
    (g : FundamentalGroup X x₀) :
    conjClassesEquivOfPath γ (ConjClasses.mk g) =
      ConjClasses.mk (fundamentalGroupMulEquivOfPath γ g) := by
  exact MulEquiv.conjClassesEquiv_mk
    (fundamentalGroupMulEquivOfPath γ) g

/-- Transport of conjugacy classes along a concatenated path is transport along each piece in
turn. -/
@[simp]
lemma conjClassesEquivOfPath_trans
    {X : Type*} [TopologicalSpace X] {x₀ x₁ x₂ : X} (γ : Path x₀ x₁) (δ : Path x₁ x₂) :
    conjClassesEquivOfPath (γ.trans δ) =
      (conjClassesEquivOfPath γ).trans
        (conjClassesEquivOfPath δ) := by
  simp only [conjClassesEquivOfPath,
    fundamentalGroupMulEquivOfPath_trans,
    MulEquiv.conjClassesEquiv_trans]

/-- Reversing a path gives the inverse equivalence on conjugacy classes. -/
@[simp]
lemma conjClassesEquivOfPath_symm
    {X : Type*} [TopologicalSpace X] {x₀ x₁ : X} (γ : Path x₀ x₁) :
    conjClassesEquivOfPath γ.symm =
      (conjClassesEquivOfPath γ).symm := by
  simp only [conjClassesEquivOfPath,
    fundamentalGroupMulEquivOfPath_symm,
    MulEquiv.conjClassesEquiv_symm]

/-- Inverse transport of a conjugacy-class representative is induced by inverse basepoint
change on the representative. -/
@[simp]
lemma conjClassesEquivOfPath_symm_mk
    {X : Type*} [TopologicalSpace X] {x₀ x₁ : X} (γ : Path x₀ x₁)
    (g : FundamentalGroup X x₁) :
    (conjClassesEquivOfPath γ).symm (ConjClasses.mk g) =
      ConjClasses.mk
        ((fundamentalGroupMulEquivOfPath γ).symm g) := by
  exact MulEquiv.conjClassesEquiv_symm_mk
    (fundamentalGroupMulEquivOfPath γ) g

/-- Transport along the constant path is the identity on conjugacy classes. -/
@[simp]
lemma conjClassesEquivOfPath_refl
    {X : Type*} [TopologicalSpace X] (x : X) :
    conjClassesEquivOfPath (Path.refl x) =
      Equiv.refl (ConjClasses (FundamentalGroup X x)) := by
  simp only [conjClassesEquivOfPath,
    fundamentalGroupMulEquivOfPath_refl,
    MulEquiv.conjClassesEquiv_refl]

/-- **Conjugacy-class basepoint change is independent of the path.** Two paths with the same
endpoints can change individual fundamental-group elements by an inner automorphism, but induce
the same equivalence on conjugacy classes. -/
lemma conjClassesEquivOfPath_eq
    {X : Type*} [TopologicalSpace X] {x₀ x₁ : X} (γ δ : Path x₀ x₁) :
    conjClassesEquivOfPath γ =
      conjClassesEquivOfPath δ := by
  let q := fromPath
    (Path.Homotopic.Quotient.mk (γ.symm.trans δ))
  have htransport :
      (fundamentalGroupMulEquivOfPath γ).symm.trans
          (fundamentalGroupMulEquivOfPath δ) =
        MulAut.conj q := by
    rw [← fundamentalGroupMulEquivOfPath_symm,
      ← fundamentalGroupMulEquivOfPath_trans]
    exact fundamentalGroupMulEquivOfPath_eq_conj (γ.symm.trans δ)
  have h : fundamentalGroupMulEquivOfPath δ =
      (fundamentalGroupMulEquivOfPath γ).trans (MulAut.conj q) := by
    ext g
    rw [MulEquiv.trans_apply, ← htransport, MulEquiv.trans_apply,
      MulEquiv.symm_apply_apply]
  ext C
  simp only [conjClassesEquivOfPath]
  rw [h, MulEquiv.conjClassesEquiv_trans, Equiv.trans_apply,
    MulAut.conjClassesEquiv_apply, TauCeti.mulAut_conj_smul_conjClasses]

/-- In a path-connected space, conjugacy classes of fundamental groups at two points are
canonically equivalent: the result does not depend on the path chosen by the instance. -/
noncomputable def conjClassesEquivOfPathConnected
    {X : Type*} [TopologicalSpace X] [PathConnectedSpace X] (x₀ x₁ : X) :
    ConjClasses (FundamentalGroup X x₀) ≃
      ConjClasses (FundamentalGroup X x₁) :=
  (fundamentalGroupMulEquivOfPathConnected x₀ x₁).conjClassesEquiv

/-- Canonical transport sends the conjugacy class of a representative to the class of its
image under Mathlib's canonical basepoint-change equivalence. -/
@[simp]
lemma conjClassesEquivOfPathConnected_mk
    {X : Type*} [TopologicalSpace X] [PathConnectedSpace X] (x₀ x₁ : X)
    (g : FundamentalGroup X x₀) :
    conjClassesEquivOfPathConnected x₀ x₁ (ConjClasses.mk g) =
      ConjClasses.mk
        (fundamentalGroupMulEquivOfPathConnected x₀ x₁ g) := by
  exact MulEquiv.conjClassesEquiv_mk
    (fundamentalGroupMulEquivOfPathConnected x₀ x₁) g

/-- The canonical equivalence of conjugacy classes in a path-connected space agrees with
transport along any specified path. -/
lemma conjClassesEquivOfPathConnected_eq
    {X : Type*} [TopologicalSpace X] [PathConnectedSpace X] {x₀ x₁ : X}
    (γ : Path x₀ x₁) :
    conjClassesEquivOfPathConnected x₀ x₁ =
      conjClassesEquivOfPath γ :=
  conjClassesEquivOfPath_eq _ _

/-- Canonical conjugacy-class transport from a point to itself is the identity. -/
@[simp]
lemma conjClassesEquivOfPathConnected_self
    {X : Type*} [TopologicalSpace X] [PathConnectedSpace X] (x : X) :
    conjClassesEquivOfPathConnected x x =
      Equiv.refl (ConjClasses (FundamentalGroup X x)) := by
  rw [conjClassesEquivOfPathConnected_eq (Path.refl x),
    conjClassesEquivOfPath_refl]

/-- Reversing the endpoints of canonical conjugacy-class transport gives its inverse. -/
@[simp]
lemma conjClassesEquivOfPathConnected_symm
    {X : Type*} [TopologicalSpace X] [PathConnectedSpace X] (x₀ x₁ : X) :
    (conjClassesEquivOfPathConnected x₀ x₁).symm =
      conjClassesEquivOfPathConnected x₁ x₀ := by
  let γ := PathConnectedSpace.somePath x₀ x₁
  rw [conjClassesEquivOfPathConnected_eq γ,
    conjClassesEquivOfPathConnected_eq γ.symm,
    conjClassesEquivOfPath_symm]

/-- Canonical conjugacy-class transport in a path-connected space is compatible with subsequent
transport along a specified path. -/
@[simp]
lemma conjClassesEquivOfPathConnected_trans
    {X : Type*} [TopologicalSpace X] [PathConnectedSpace X] (b : X) {x₀ x₁ : X}
    (γ : Path x₀ x₁) :
    (conjClassesEquivOfPathConnected b x₀).trans
        (conjClassesEquivOfPath γ) =
      conjClassesEquivOfPathConnected b x₁ := by
  rw [conjClassesEquivOfPathConnected_eq
      (PathConnectedSpace.somePath b x₀),
    ← conjClassesEquivOfPath_trans]
  exact conjClassesEquivOfPath_eq _ _

/-- Applying path transport after canonical transport is canonical transport to the new
basepoint. -/
@[simp]
lemma conjClassesEquivOfPath_conjClassesEquivOfPathConnected
    {X : Type*} [TopologicalSpace X] [PathConnectedSpace X] (b : X) {x₀ x₁ : X}
    (γ : Path x₀ x₁) (C : ConjClasses (FundamentalGroup X b)) :
    conjClassesEquivOfPath γ
        (conjClassesEquivOfPathConnected b x₀ C) =
      conjClassesEquivOfPathConnected b x₁ C := by
  rw [← Equiv.trans_apply,
    conjClassesEquivOfPathConnected_trans]

/-- Applying canonical transport twice is canonical transport directly to the final basepoint. -/
@[simp]
lemma conjClassesEquivOfPathConnected_trans_conjClassesEquivOfPathConnected
    {X : Type*} [TopologicalSpace X] [PathConnectedSpace X] (b x₀ x₁ : X)
    (C : ConjClasses (FundamentalGroup X b)) :
    conjClassesEquivOfPathConnected x₀ x₁
        (conjClassesEquivOfPathConnected b x₀ C) =
      conjClassesEquivOfPathConnected b x₁ C := by
  rw [conjClassesEquivOfPathConnected_eq
      (PathConnectedSpace.somePath x₀ x₁),
    conjClassesEquivOfPath_conjClassesEquivOfPathConnected]

variable {X : Type*} [TopologicalSpace X] {x₀ x₁ : X}

/-- The subgroup of `π₁(X, x₁)` obtained from `H ≤ π₁(X, x₀)` by changing basepoint along a
path `γ : Path x₀ x₁`. This is the subgroup-level form of conjugating loops by `γ`. -/
noncomputable def basepointChangeSubgroup (γ : Path x₀ x₁)
    (H : Subgroup (FundamentalGroup X x₀)) :
    Subgroup (FundamentalGroup X x₁) :=
  H.map (((fundamentalGroupMulEquivOfPath γ) :
    FundamentalGroup X x₀ →* FundamentalGroup X x₁))

/-- Membership in the subgroup transported along a basepoint-change path. -/
lemma mem_basepointChangeSubgroup (γ : Path x₀ x₁) (H : Subgroup (FundamentalGroup X x₀))
    (g : FundamentalGroup X x₁) :
    g ∈ basepointChangeSubgroup γ H ↔
      ∃ h ∈ H, fundamentalGroupMulEquivOfPath γ h = g :=
  Iff.rfl

/-- Membership in a transported subgroup, expressed by applying the inverse basepoint-change
isomorphism. -/
@[simp]
lemma mem_basepointChangeSubgroup_iff (γ : Path x₀ x₁) (H : Subgroup (FundamentalGroup X x₀))
    (g : FundamentalGroup X x₁) :
    g ∈ basepointChangeSubgroup γ H ↔
      (fundamentalGroupMulEquivOfPath γ).symm g ∈ H := by
  simpa [basepointChangeSubgroup] using
    (Subgroup.mem_map_equiv
      (f := fundamentalGroupMulEquivOfPath γ) (K := H) (x := g))

/-- A subgroup of the target fundamental group is contained in the transported subgroup iff
its inverse basepoint-change image is contained in the original subgroup. -/
lemma le_basepointChangeSubgroup_iff (γ : Path x₀ x₁) (K : Subgroup (FundamentalGroup X x₁))
    (H : Subgroup (FundamentalGroup X x₀)) :
    K ≤ basepointChangeSubgroup γ H ↔
      K.map (((fundamentalGroupMulEquivOfPath γ).symm) :
        FundamentalGroup X x₁ →* FundamentalGroup X x₀) ≤ H := by
  rw [basepointChangeSubgroup]
  constructor
  · intro h x hx
    rcases Subgroup.mem_map.mp hx with ⟨y, hyK, rfl⟩
    exact (Subgroup.mem_map_equiv
      (f := fundamentalGroupMulEquivOfPath γ) (K := H)
        (x := y)).mp (h hyK)
  · intro h y hy
    exact (Subgroup.mem_map_equiv
      (f := fundamentalGroupMulEquivOfPath γ) (K := H)
        (x := y)).mpr (h (Subgroup.mem_map_of_mem _ hy))

/-- The transported subgroup is contained in a target subgroup iff the original subgroup is
contained in the target subgroup's inverse image under basepoint change. -/
lemma basepointChangeSubgroup_le_iff (γ : Path x₀ x₁) (H : Subgroup (FundamentalGroup X x₀))
    (K : Subgroup (FundamentalGroup X x₁)) :
    basepointChangeSubgroup γ H ≤ K ↔
      H ≤ K.comap (((fundamentalGroupMulEquivOfPath γ) :
        FundamentalGroup X x₀ →* FundamentalGroup X x₁)) := by
  rw [basepointChangeSubgroup, Subgroup.map_le_iff_le_comap]

/-- Basepoint-change transport is monotone on subgroups. -/
lemma basepointChangeSubgroup_mono (γ : Path x₀ x₁)
    {H K : Subgroup (FundamentalGroup X x₀)} (h : H ≤ K) :
    basepointChangeSubgroup γ H ≤ basepointChangeSubgroup γ K := by
  rw [basepointChangeSubgroup, basepointChangeSubgroup]
  exact Subgroup.map_mono h

/-- Normality is invariant under basepoint-change transport. -/
lemma basepointChangeSubgroup_normal_iff (γ : Path x₀ x₁)
    (H : Subgroup (FundamentalGroup X x₀)) :
    (basepointChangeSubgroup γ H).Normal ↔ H.Normal := by
  rw [basepointChangeSubgroup]
  exact MulEquiv.normal_map_iff

/-- A normal subgroup remains normal after basepoint-change transport. -/
lemma basepointChangeSubgroup.normal (γ : Path x₀ x₁)
    {H : Subgroup (FundamentalGroup X x₀)} (hH : H.Normal) :
    (basepointChangeSubgroup γ H).Normal :=
  (basepointChangeSubgroup_normal_iff γ H).2 hH

/-- The normalizer quotient `N(H) / H` transported along a basepoint-change path. -/
noncomputable def basepointChangeNormalizerQuotientEquiv (γ : Path x₀ x₁)
    (H : Subgroup (FundamentalGroup X x₀)) :
    Subgroup.normalizerQuotient H ≃*
      Subgroup.normalizerQuotient (basepointChangeSubgroup γ H) :=
  (Subgroup.normalizerQuotientEquivMap H
    (fundamentalGroupMulEquivOfPath γ)).trans
    (Subgroup.normalizerQuotientCongr (by rw [basepointChangeSubgroup]))

/-- On normalizer representatives, basepoint-change transport is induced by the
path-conjugation isomorphism of fundamental groups. -/
@[simp]
lemma basepointChangeNormalizerQuotientEquiv_mk (γ : Path x₀ x₁)
    (H : Subgroup (FundamentalGroup X x₀))
    (g : Subgroup.normalizer (H : Set (FundamentalGroup X x₀))) :
    basepointChangeNormalizerQuotientEquiv γ H (g : Subgroup.normalizerQuotient H) =
      ((MulEquiv.subgroupCongr (by rw [basepointChangeSubgroup])
          (Subgroup.normalizerEquivMap H
            (fundamentalGroupMulEquivOfPath γ) g) :
          Subgroup.normalizer
            ((basepointChangeSubgroup γ H) : Set (FundamentalGroup X x₁))) :
        Subgroup.normalizerQuotient (basepointChangeSubgroup γ H)) := by
  rw [← Subgroup.normalizerQuotientMk_apply, ← Subgroup.normalizerQuotientMk_apply,
    basepointChangeNormalizerQuotientEquiv, MulEquiv.trans_apply,
    Subgroup.normalizerQuotientEquivMap_mk,
    Subgroup.normalizerQuotientCongr_mk]

/-- The inverse basepoint-change transport sends a target representative to the inverse
path-conjugation representative. -/
@[simp]
lemma basepointChangeNormalizerQuotientEquiv_symm_mk (γ : Path x₀ x₁)
    (H : Subgroup (FundamentalGroup X x₀)) (g : Subgroup.normalizer
      ((basepointChangeSubgroup γ H) : Set (FundamentalGroup X x₁))) :
    (basepointChangeNormalizerQuotientEquiv γ H).symm
        (g : Subgroup.normalizerQuotient (basepointChangeSubgroup γ H)) =
      (((Subgroup.normalizerEquivMap H
          (fundamentalGroupMulEquivOfPath γ)).symm
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
    (H : Subgroup (FundamentalGroup X x₀))
    (g : Subgroup.normalizer (H : Set (FundamentalGroup X x₀))) :
    basepointChangeNormalizerQuotientEquiv γ H (Subgroup.normalizerQuotientMk H g) =
      Subgroup.normalizerQuotientMk (basepointChangeSubgroup γ H)
        (MulEquiv.subgroupCongr (by rw [basepointChangeSubgroup])
          (⟨fundamentalGroupMulEquivOfPath γ
              (g : FundamentalGroup X x₀),
            by
              rw [← Subgroup.normalizerEquivMap_apply_coe H
                (fundamentalGroupMulEquivOfPath γ) g]
              exact (Subgroup.normalizerEquivMap H
                (fundamentalGroupMulEquivOfPath γ) g).2⟩ :
            Subgroup.normalizer
              ((H.map ((fundamentalGroupMulEquivOfPath γ) :
                FundamentalGroup X x₀ →* FundamentalGroup X x₁)) :
                  Set (FundamentalGroup X x₁)))) := by
  rw [basepointChangeNormalizerQuotientEquiv, MulEquiv.trans_apply,
    Subgroup.normalizerQuotientEquivMap_mk_coe,
    Subgroup.normalizerQuotientCongr_mk]

end FundamentalGroup
