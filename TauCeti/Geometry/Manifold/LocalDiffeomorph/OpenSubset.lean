/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.LocalDiffeomorph

/-!
# Partial diffeomorphisms and open subsets

Mathlib's `OpenPartialHomeomorph.restrOpen` shrinks the source of an open partial homeomorphism
to its intersection with an open set. This file provides the same operation for Mathlib's
`PartialDiffeomorph`: the restriction is still `C^n` in both directions, because both of its
domains are subsets of the original ones. It is used to make charts small, for example to make
finitely many charts centred at distinct points pairwise disjoint.

The file also records that the inclusion of an open subset, with the charts Mathlib restricts to
it, is a local diffeomorphism. Structures defined through charts, such as orientations, can then
be compared on an open subset and on the ambient manifold.

## Main declarations

* `PartialDiffeomorph.restrOpen`: the restriction of a partial diffeomorphism to an open set.
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

end PartialDiffeomorph

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
