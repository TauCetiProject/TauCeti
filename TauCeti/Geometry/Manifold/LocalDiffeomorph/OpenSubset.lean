/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.LocalDiffeomorph
import TauCeti.Geometry.Manifold.ContMDiff.Subtype

/-!
# Partial diffeomorphisms and open subsets

Mathlib's `OpenPartialHomeomorph.restrOpen` shrinks the source of an open partial homeomorphism
to its intersection with an open set. This file provides the same operation for Mathlib's
`PartialDiffeomorph`: the restriction is still `C^n` in both directions, because both of its
domains are subsets of the original ones. It is used to make charts small, for example to make
finitely many charts centred at distinct points pairwise disjoint.

A partial diffeomorphism is also a diffeomorphism between its source and its target, each an open
subset carrying the charts Mathlib restricts to it. This is the analogue for partial
diffeomorphisms of Mathlib's `OpenPartialHomeomorph.toHomeomorphSourceTarget`, and lets results
about diffeomorphisms be applied to a partial diffeomorphism on its domain.

The file also records that the inclusion of an open subset, with the charts Mathlib restricts to
it, is a local diffeomorphism. Structures defined through charts, such as orientations, can then
be compared on an open subset and on the ambient manifold. An open subset equal to the whole
manifold is diffeomorphic to it through its inclusion.

## Main declarations

* `PartialDiffeomorph.restrOpen`: the restriction of a partial diffeomorphism to an open set.
* `PartialDiffeomorph.contMDiffOn_toOpenPartialHomeomorph_restrOpen` and its `symm` version: the
  restrictions of the underlying open partial homeomorphism to an open set are smooth.
* `PartialDiffeomorph.toDiffeomorphSourceTarget`: a partial diffeomorphism as a diffeomorphism
  between its open source and its open target.
* `Diffeomorph.ofTop`: an open subset equal to `⊤` is diffeomorphic to the ambient manifold.
* `TauCeti.isLocalDiffeomorph_subtype_val`: the inclusion of an open subset is a `C^n` local
  diffeomorphism.
-/

public section

open Set
open scoped Manifold

namespace PartialDiffeomorph

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {H : Type*} [TopologicalSpace H] {G : Type*} [TopologicalSpace G]
  {I : ModelWithCorners 𝕜 E H} {J : ModelWithCorners 𝕜 F G} {n : WithTop ℕ∞}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N]
  (Φ : PartialDiffeomorph I J M N n) {s : Set M}

/-- The restriction of a partial diffeomorphism to an open set `s`: its source is
`Φ.source ∩ s`, and its target is the image of that set. -/
def restrOpen (s : Set M) (hs : IsOpen s) : PartialDiffeomorph I J M N n where
  toPartialEquiv := (Φ.toOpenPartialHomeomorph.restrOpen s hs).toPartialEquiv
  open_source := (Φ.toOpenPartialHomeomorph.restrOpen s hs).open_source
  open_target := (Φ.toOpenPartialHomeomorph.restrOpen s hs).open_target
  contMDiffOn_toFun := Φ.contMDiffOn_toFun.mono inter_subset_left
  contMDiffOn_invFun := Φ.contMDiffOn_invFun.mono inter_subset_left

/-- The underlying partial equivalence of the restriction is the restriction of the underlying
partial equivalence. -/
theorem restrOpen_toPartialEquiv (hs : IsOpen s) :
    (Φ.restrOpen s hs).toPartialEquiv = Φ.toPartialEquiv.restr s :=
  (rfl)

/-- The source of the restriction to `s` is `Φ.source ∩ s`. -/
@[simp]
theorem restrOpen_source (hs : IsOpen s) : (Φ.restrOpen s hs).source = Φ.source ∩ s :=
  (rfl)

/-- The target of the restriction to `s` consists of the points of `Φ.target` whose preimage
lies in `s`. -/
@[simp]
theorem restrOpen_target (hs : IsOpen s) :
    (Φ.restrOpen s hs).target = Φ.target ∩ Φ.toPartialEquiv.symm ⁻¹' s :=
  (rfl)

/-- The restriction has the same forward map. -/
@[simp]
theorem coe_restrOpen (hs : IsOpen s) : ⇑(Φ.restrOpen s hs) = Φ :=
  (rfl)

/-- The restriction has the same inverse map. -/
@[simp]
theorem coe_restrOpen_symm (hs : IsOpen s) :
    ⇑(Φ.restrOpen s hs).toPartialEquiv.symm = Φ.toPartialEquiv.symm :=
  (rfl)

/-- The open partial homeomorphism of a partial diffeomorphism has its source. -/
theorem toOpenPartialHomeomorph_source :
    Φ.toOpenPartialHomeomorph.source = Φ.source :=
  congrArg PartialEquiv.source (Φ.toOpenPartialHomeomorph_toPartialHomeomorph_toPartialEquiv)

/-- The open partial homeomorphism of a partial diffeomorphism has its target. -/
theorem toOpenPartialHomeomorph_target :
    Φ.toOpenPartialHomeomorph.target = Φ.target :=
  congrArg PartialEquiv.target (Φ.toOpenPartialHomeomorph_toPartialHomeomorph_toPartialEquiv)

/-- The inverse of the open partial homeomorphism of a partial diffeomorphism is the inverse
function of the partial diffeomorphism. -/
@[simp]
theorem coe_toOpenPartialHomeomorph_symm :
    ⇑Φ.toOpenPartialHomeomorph.symm = Φ.symm :=
  rfl

/-- Restricting the open partial homeomorphism of a partial diffeomorphism to an open set keeps it
smooth on its source. -/
theorem contMDiffOn_toOpenPartialHomeomorph_restrOpen {V : Set M} (hV : IsOpen V) :
    ContMDiffOn I J n (Φ.toOpenPartialHomeomorph.restrOpen V hV)
      (Φ.toOpenPartialHomeomorph.restrOpen V hV).source := by
  rw [OpenPartialHomeomorph.coe_restrOpen, OpenPartialHomeomorph.restrOpen_source,
    Φ.toFun'_toOpenPartialHomeomorph, Φ.toOpenPartialHomeomorph_source]
  exact Φ.contMDiffOn.mono inter_subset_left

/-- The inverse of the restriction of the open partial homeomorphism of a partial diffeomorphism to
an open set is smooth on the target of the restriction. -/
theorem contMDiffOn_toOpenPartialHomeomorph_restrOpen_symm {V : Set M} (hV : IsOpen V) :
    ContMDiffOn J I n (Φ.toOpenPartialHomeomorph.restrOpen V hV).symm
      (Φ.toOpenPartialHomeomorph.restrOpen V hV).target := by
  have htarget : (Φ.toOpenPartialHomeomorph.restrOpen V hV).target ⊆ Φ.target := by
    rw [OpenPartialHomeomorph.restrOpen_toPartialEquiv, PartialEquiv.restr_target,
      ← Φ.toOpenPartialHomeomorph_target]
    exact inter_subset_left
  rw [OpenPartialHomeomorph.coe_restrOpen_symm, Φ.coe_toOpenPartialHomeomorph_symm]
  exact Φ.symm.contMDiffOn.mono htarget

/-- A partial diffeomorphism is a diffeomorphism between its source and its target, as open
subsets of `M` and `N`. -/
def toDiffeomorphSourceTarget :
    (⟨Φ.source, Φ.open_source⟩ : TopologicalSpace.Opens M) ≃ₘ^n⟮I, J⟯
      (⟨Φ.target, Φ.open_target⟩ : TopologicalSpace.Opens N) where
  toEquiv := Φ.toOpenPartialHomeomorph.toHomeomorphSourceTarget.toEquiv
  contMDiff_toFun := (TauCeti.ContMDiff.subtypeVal_comp_iff _ _).1 fun x ↦
    ((Φ.contMDiffOn x x.2).contMDiffAt (Φ.open_source.mem_nhds x.2)).comp x
      contMDiff_subtype_val.contMDiffAt
  contMDiff_invFun := (TauCeti.ContMDiff.subtypeVal_comp_iff _ _).1 fun x ↦
    ((Φ.symm.contMDiffOn x x.2).contMDiffAt (Φ.open_target.mem_nhds x.2)).comp x
      contMDiff_subtype_val.contMDiffAt

/-- The diffeomorphism `PartialDiffeomorph.toDiffeomorphSourceTarget` evaluates as the partial
diffeomorphism. -/
@[simp]
theorem toDiffeomorphSourceTarget_apply_coe
    (x : (⟨Φ.source, Φ.open_source⟩ : TopologicalSpace.Opens M)) :
    (Φ.toDiffeomorphSourceTarget x : N) = Φ x :=
  (rfl)

/-- The inverse of `PartialDiffeomorph.toDiffeomorphSourceTarget` evaluates as the inverse of the
partial diffeomorphism. -/
@[simp]
theorem toDiffeomorphSourceTarget_symm_apply_coe
    (x : (⟨Φ.target, Φ.open_target⟩ : TopologicalSpace.Opens N)) :
    (Φ.toDiffeomorphSourceTarget.symm x : M) = Φ.symm x :=
  (rfl)

end PartialDiffeomorph

namespace Diffeomorph

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners 𝕜 E H} {n : WithTop ℕ∞}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

/-- An open subset `U` of `M` equal to `⊤` is `C^n` diffeomorphic to `M` through its inclusion. -/
def ofTop (U : TopologicalSpace.Opens M) (hU : U = ⊤) : U ≃ₘ^n⟮I, I⟯ M where
  toFun := Subtype.val
  invFun x := ⟨x, hU.symm ▸ trivial⟩
  left_inv _ := rfl
  right_inv _ := rfl
  contMDiff_toFun := contMDiff_subtype_val
  contMDiff_invFun := (TauCeti.ContMDiff.subtypeVal_comp_iff U _).mp contMDiff_id

/-- The diffeomorphism `Diffeomorph.ofTop` is the inclusion. -/
@[simp]
theorem ofTop_apply {U : TopologicalSpace.Opens M} {hU : U = ⊤} (x : U) :
    ofTop (I := I) (n := n) U hU x = x :=
  (rfl)

/-- The diffeomorphism `Diffeomorph.ofTop` is the inclusion, as a function. -/
theorem coe_ofTop {U : TopologicalSpace.Opens M} {hU : U = ⊤} :
    ⇑(ofTop (I := I) (n := n) U hU) = Subtype.val :=
  (rfl)

/-- The inverse of `Diffeomorph.ofTop` sends a point to itself, viewed in `U`. -/
@[simp]
theorem coe_ofTop_symm_apply {U : TopologicalSpace.Opens M} {hU : U = ⊤} (x : M) :
    ((ofTop (I := I) (n := n) U hU).symm x : M) = x :=
  (rfl)

end Diffeomorph

namespace TauCeti

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners 𝕜 E H} {n : WithTop ℕ∞}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

/-- The inclusion of an open subset `U` of `M`, charted by the restrictions of the charts of `M`,
is a `C^n` local diffeomorphism. -/
theorem isLocalDiffeomorph_subtype_val {U : TopologicalSpace.Opens M} :
    IsLocalDiffeomorph I I n (Subtype.val : U → M) := fun x ↦ by
  let e := U.openPartialHomeomorphSubtypeCoe ⟨x⟩
  let Φ : PartialDiffeomorph I I U M n :=
    { e.toPartialEquiv with
      open_source := e.open_source
      open_target := e.open_target
      contMDiffOn_toFun := contMDiff_subtype_val.contMDiffOn
      contMDiffOn_invFun := fun y hy ↦ by
        refine (ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff _ _ _).1 ?_
        exact contMDiffWithinAt_id.congr (fun z hz ↦ e.right_inv hz) (e.right_inv hy) }
  exact Φ.isLocalDiffeomorphAt I I n (mem_univ x)

end TauCeti
