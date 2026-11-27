/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.LocalDiffeomorph
import all Mathlib.Geometry.Manifold.LocalDiffeomorph
import TauCeti.Geometry.Manifold.ContMDiff.Subtype
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Constructions
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Injective
import TauCeti.Geometry.Manifold.VectorBundle.Tangent.Basic

/-!
# Partial diffeomorphisms and open subsets

Mathlib's `OpenPartialHomeomorph.restrOpen` shrinks the source of an open partial homeomorphism
to its intersection with an open set. This file provides the same operation for Mathlib's
`PartialDiffeomorph`: the restriction is still `C^n` in both directions, because both of its
domains are subsets of the original ones. It is used to make charts small, for example to make
finitely many charts centred at distinct points pairwise disjoint. A partial diffeomorphism of `M`
also restricts to a partial diffeomorphism of any nonempty open subset of `M`, the analogue of
Mathlib's `OpenPartialHomeomorph.subtypeRestr`.

A partial diffeomorphism is also a diffeomorphism between its source and its target, each an open
subset carrying the charts Mathlib restricts to it. This is the analogue for partial
diffeomorphisms of Mathlib's `OpenPartialHomeomorph.toHomeomorphSourceTarget`, and lets results
about diffeomorphisms be applied to a partial diffeomorphism on its domain.

The file also records that the inclusion of an open subset, with the charts Mathlib restricts to
it, is a local diffeomorphism. Structures defined through charts, such as orientations, can then
be compared on an open subset and on the ambient manifold. An open subset equal to the whole
manifold is diffeomorphic to it through its inclusion, and a diffeomorphism mapping an open subset
onto another restricts to a diffeomorphism between them. A partial diffeomorphism out of an open
subset can be carried, near any point of its source, to the ambient manifold. A partial
diffeomorphism between nonempty open subsets is itself a partial diffeomorphism between the ambient
manifolds, with the same source and target read in them. Correcting a partial diffeomorphism by a
diffeomorphism of its source gives, on any open subset of the source, a diffeomorphism onto an open
subset of the target manifold.

## Main declarations

* `PartialDiffeomorph.restrOpen`: the restriction of a partial diffeomorphism to an open set.
* `OpenPartialHomeomorph.contMDiffOn_subtypeRestr`,
  `OpenPartialHomeomorph.contMDiffOn_subtypeRestr_symm`: restricting a partial homeomorphism that is
  `C^n` on its source, or whose inverse is `C^n` on its target, to an open subset keeps that
  property; `OpenPartialHomeomorph.mfderiv_subtypeRestr_symm_apply`: the inverse of the restriction
  has the differential of the original inverse.
* `PartialDiffeomorph.subtypeRestr`: the restriction of a partial diffeomorphism to a nonempty open
  subset, as a partial diffeomorphism of that subset.
* `PartialDiffeomorph.contMDiffOn_toOpenPartialHomeomorph_restrOpen` and its `symm` version: the
  restrictions of the underlying open partial homeomorphism to an open set are smooth.
* `PartialDiffeomorph.toDiffeomorphSourceTarget`: a partial diffeomorphism as a diffeomorphism
  between its open source and its open target.
* `Diffeomorph.ofTop`: an open subset equal to `⊤` is diffeomorphic to the ambient manifold.
* `Diffeomorph.nestedOpen`: for nested open subsets `U ≤ D`, the preimage of `U` in `D` is
  diffeomorphic to `U`. It compares structures on a restriction to `D` followed by a restriction
  to `U` with the direct restriction to `U`.
* `Diffeomorph.subtype`: a diffeomorphism restricts to a diffeomorphism between open subsets that
  it maps onto each other.
* `TauCeti.isLocalDiffeomorph_subtype_val`: the inclusion of an open subset is a `C^n` local
  diffeomorphism.
* `TauCeti.bijective_mfderiv_subtype_val`, `TauCeti.bijective_mfderiv_inclusion`: the inclusions
  of an open subset in `M` and in a larger open subset have bijective differentials.
* `PartialDiffeomorph.exists_ambient_of_opens`: a partial diffeomorphism out of an open subset
  agrees near a point of its source with a partial diffeomorphism out of the ambient manifold.
* `PartialDiffeomorph.subtypeVal`: the inclusion of a nonempty open subset as a partial
  diffeomorphism.
* `PartialDiffeomorph.liftOpens`: a partial diffeomorphism between nonempty open subsets, as a
  partial diffeomorphism between the ambient manifolds. On the open subset it has the values
  (`PartialDiffeomorph.liftOpens_comp_subtypeVal`) and the differentials
  (`PartialDiffeomorph.mfderiv_liftOpens_apply_coe`) of the original one.
* `IsLocalDiffeomorphAt.exists_partialDiffeomorph_eqOn`: a local diffeomorphism at `x` agrees with
  a partial diffeomorphism whose source contains `x` and lies in a prescribed open set.
* `PartialDiffeomorph.exists_diffeomorph_opens_comp_eq`: a partial diffeomorphism corrected by a
  diffeomorphism of its source is, on an open subset of the source, a diffeomorphism onto an open
  subset.
-/

public section

open Set
open scoped Manifold

namespace OpenPartialHomeomorph

variable {𝕜 E H M E' H' N : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  [TopologicalSpace M] [ChartedSpace H M]
  [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] [TopologicalSpace H'] {J : ModelWithCorners 𝕜 E' H'}
  [TopologicalSpace N] [ChartedSpace H' N] {n : WithTop ℕ∞} {e : OpenPartialHomeomorph M N}
  {U : TopologicalSpace.Opens M}

/-- The restriction `e|_U` of a partial homeomorphism that is `C^n` on its source to an open
subset `U` is `C^n` on its source. -/
theorem contMDiffOn_subtypeRestr (hU : Nonempty U) (he : ContMDiffOn I J n e e.source) :
    ContMDiffOn I J n (e.subtypeRestr hU) (e.subtypeRestr hU).source := by
  rw [subtypeRestr_coe, subtypeRestr_source]
  exact he.comp contMDiff_subtypeVal.contMDiffOn fun _ hx ↦ hx

/-- If the inverse of a partial homeomorphism `e` is `C^n` on its target, so is the inverse of its
restriction `e|_U` to an open subset `U`. -/
theorem contMDiffOn_subtypeRestr_symm (hU : Nonempty U)
    (he : ContMDiffOn J I n e.symm e.target) :
    ContMDiffOn J I n (e.subtypeRestr hU).symm (e.subtypeRestr hU).target := by
  rw [← TauCeti.ContMDiffOn.subtypeVal_comp_iff]
  exact (he.mono (e.subtypeRestr_target_subset hU)).congr (e.subtypeRestr_symm_eqOn hU).symm

/-- On the target of the restriction `e|_U` of a partial homeomorphism to an open subset `U`, the
inverse of `e|_U` has the same differential as the inverse of `e`, the tangent spaces of `U` being
those of `M`. -/
theorem mfderiv_subtypeRestr_symm_apply (hU : Nonempty U) {y : N}
    (hy : y ∈ (e.subtypeRestr hU).target) (v : TangentSpace J y) :
    mfderiv J I (e.subtypeRestr hU).symm y v = mfderiv J I e.symm y v := by
  have hev : (Subtype.val ∘ (e.subtypeRestr hU).symm) =ᶠ[nhds y] e.symm :=
    Filter.eventuallyEq_of_mem ((e.subtypeRestr hU).open_target.mem_nhds hy)
      fun z hz ↦ e.subtypeRestr_symm_apply hU hz
  rw [← TauCeti.Manifold.mfderiv_subtype_val_comp_apply, hev.mfderiv_eq]
  -- The base points `(Subtype.val ∘ (e|_U)⁻¹) y` and `e⁻¹ y` differ syntactically, so
  -- `mfderiv_eq` inserts a cast between their tangent spaces, which is the identity of `E`.
  rfl

end OpenPartialHomeomorph

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

/-- The restriction of a partial diffeomorphism of `M` to a nonempty open subset `U` of `M`, as a
partial diffeomorphism of `U` carrying the charts that Mathlib restricts to it. This is the
counterpart for partial diffeomorphisms of Mathlib's `OpenPartialHomeomorph.subtypeRestr`; its
source is the preimage of `Φ.source` in `U`. -/
noncomputable def subtypeRestr (U : TopologicalSpace.Opens M) (hU : Nonempty U) :
    PartialDiffeomorph I J U N n where
  toPartialEquiv := (Φ.toOpenPartialHomeomorph.subtypeRestr hU).toPartialEquiv
  open_source := (Φ.toOpenPartialHomeomorph.subtypeRestr hU).open_source
  open_target := (Φ.toOpenPartialHomeomorph.subtypeRestr hU).open_target
  contMDiffOn_toFun := Φ.toOpenPartialHomeomorph.contMDiffOn_subtypeRestr hU Φ.contMDiffOn
  contMDiffOn_invFun :=
    Φ.toOpenPartialHomeomorph.contMDiffOn_subtypeRestr_symm hU Φ.symm.contMDiffOn

/-- The underlying open partial homeomorphism of the restriction to `U` is Mathlib's
restriction to that open subset. -/
@[simp]
theorem subtypeRestr_toOpenPartialHomeomorph (U : TopologicalSpace.Opens M) (hU : Nonempty U) :
    (Φ.subtypeRestr U hU).toOpenPartialHomeomorph = Φ.toOpenPartialHomeomorph.subtypeRestr hU :=
  (rfl)

/-- The source of the restriction to `U` is the preimage of `Φ.source` in `U`. -/
@[simp]
theorem subtypeRestr_source (U : TopologicalSpace.Opens M) (hU : Nonempty U) :
    (Φ.subtypeRestr U hU).source = Subtype.val ⁻¹' Φ.source :=
  Φ.toOpenPartialHomeomorph.subtypeRestr_source hU

/-- The target of the restriction to `U` consists of the points of `Φ.target` whose preimage
lies in `U`. -/
@[simp]
theorem subtypeRestr_target (U : TopologicalSpace.Opens M) (hU : Nonempty U) :
    (Φ.subtypeRestr U hU).target = Φ.target ∩ Φ.symm ⁻¹' U := by
  rw [← toOpenPartialHomeomorph_target, subtypeRestr_toOpenPartialHomeomorph]
  simp [OpenPartialHomeomorph.subtypeRestr_def, mfld_simps]

/-- The restriction to `U` evaluates as `Φ`. -/
@[simp]
theorem subtypeRestr_apply (U : TopologicalSpace.Opens M) (hU : Nonempty U) (x : U) :
    Φ.subtypeRestr U hU x = Φ x :=
  congrFun (Φ.toOpenPartialHomeomorph.subtypeRestr_coe hU) x

/-- On its target, the inverse of the restriction to `U` is the inverse of `Φ`, read in `U`. -/
theorem coe_subtypeRestr_symm_apply (U : TopologicalSpace.Opens M) (hU : Nonempty U) {y : N}
    (hy : y ∈ (Φ.subtypeRestr U hU).target) :
    ((Φ.subtypeRestr U hU).symm y : M) = Φ.symm y :=
  (Φ.toOpenPartialHomeomorph.subtypeRestr_symm_eqOn hU hy).symm

/-- A partial diffeomorphism is a diffeomorphism between its source and its target, as open
subsets of `M` and `N`. -/
def toDiffeomorphSourceTarget :
    (⟨Φ.source, Φ.open_source⟩ : TopologicalSpace.Opens M) ≃ₘ^n⟮I, J⟯
      (⟨Φ.target, Φ.open_target⟩ : TopologicalSpace.Opens N) where
  toEquiv := Φ.toOpenPartialHomeomorph.toHomeomorphSourceTarget.toEquiv
  contMDiff_toFun := (TauCeti.ContMDiff.subtypeVal_comp_iff _ _).1 fun x ↦
    ((Φ.contMDiffOn x x.property).contMDiffAt (Φ.open_source.mem_nhds x.property)).comp x
      contMDiff_subtypeVal.contMDiffAt
  contMDiff_invFun := (TauCeti.ContMDiff.subtypeVal_comp_iff _ _).1 fun x ↦
    ((Φ.symm.contMDiffOn x x.property).contMDiffAt (Φ.open_target.mem_nhds x.property)).comp x
      contMDiff_subtypeVal.contMDiffAt

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
  contMDiff_toFun := contMDiff_subtypeVal
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

/-- For nested open subsets `U ≤ D`, the preimage of `U` in `D` is diffeomorphic to `U`. -/
def nestedOpen {U D : TopologicalSpace.Opens M} (h : U ≤ D) :
    (TopologicalSpace.Opens.comap (⟨Subtype.val, continuous_subtypeVal⟩ : C(D, M)) U)
      ≃ₘ^n⟮I, I⟯ U where
  toFun x := ⟨x.val.val, x.property⟩
  invFun u := ⟨⟨u.val, h u.property⟩, u.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  contMDiff_toFun := (TauCeti.ContMDiff.subtypeVal_comp_iff U _).mp
    ((contMDiff_subtypeVal (I := I) (U := D)).comp contMDiff_subtypeVal)
  contMDiff_invFun := (TauCeti.ContMDiff.subtypeVal_comp_iff _ _).mp
    ((TauCeti.ContMDiff.subtypeVal_comp_iff D _).mp contMDiff_subtypeVal)

/-- The diffeomorphism `Diffeomorph.nestedOpen` keeps the underlying point. -/
@[simp]
theorem nestedOpen_apply {U D : TopologicalSpace.Opens M} (h : U ≤ D)
    (x : TopologicalSpace.Opens.comap (⟨Subtype.val, continuous_subtypeVal⟩ : C(D, M)) U) :
    nestedOpen (I := I) (n := n) h x = ⟨x.val.val, x.property⟩ :=
  (rfl)

/-- The inverse of `Diffeomorph.nestedOpen` views a point of `U` in `D`. -/
@[simp]
theorem nestedOpen_symm_apply {U D : TopologicalSpace.Opens M} (h : U ≤ D) (x : U) :
    (nestedOpen (I := I) (n := n) h).symm x = ⟨⟨x.val, h x.property⟩, x.property⟩ :=
  (rfl)

section Subtype

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] {G : Type*} [TopologicalSpace G]
  {J : ModelWithCorners 𝕜 F G} {N : Type*} [TopologicalSpace N] [ChartedSpace G N]
  {U : TopologicalSpace.Opens M} {V : TopologicalSpace.Opens N}

/-- A diffeomorphism `g : M ≃ₘ N` restricts to a diffeomorphism between open subsets `U` and `V`
that it maps onto each other, each carrying the charts Mathlib restricts to it. This is the smooth
form of Mathlib's `Homeomorph.subtype`. -/
def subtype (g : M ≃ₘ^n⟮I, J⟯ N) (h_iff : ∀ x, x ∈ U ↔ g x ∈ V) : U ≃ₘ^n⟮I, J⟯ V where
  toEquiv := g.toEquiv.subtypeEquiv h_iff
  contMDiff_toFun := (TauCeti.ContMDiff.subtypeVal_comp_iff _ _).1
    (g.contMDiff.comp contMDiff_subtypeVal)
  contMDiff_invFun := (TauCeti.ContMDiff.subtypeVal_comp_iff _ _).1
    (g.symm.contMDiff.comp contMDiff_subtypeVal)

/-- The restriction `Diffeomorph.subtype` evaluates as the diffeomorphism. -/
@[simp]
theorem subtype_apply_coe (g : M ≃ₘ^n⟮I, J⟯ N) (h_iff : ∀ x, x ∈ U ↔ g x ∈ V) (x : U) :
    (g.subtype h_iff x : N) = g x :=
  (rfl)

/-- The inverse of the restriction `Diffeomorph.subtype` evaluates as the inverse
diffeomorphism. -/
@[simp]
theorem subtype_symm_apply_coe (g : M ≃ₘ^n⟮I, J⟯ N) (h_iff : ∀ x, x ∈ U ↔ g x ∈ V) (y : V) :
    ((g.subtype h_iff).symm y : M) = g.symm y :=
  (rfl)

end Subtype

end Diffeomorph

namespace PartialDiffeomorph

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H]
  (I : ModelWithCorners 𝕜 E H) (n : WithTop ℕ∞)
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

/-- The inclusion of a nonempty open subset `U` of `M`, charted by the restrictions of the charts
of `M`, as a `C^n` partial diffeomorphism from `U` to `M`. Its source is all of `U` and its target
is `U`. The nonemptiness hypothesis provides the junk values of the inverse off `U`. -/
noncomputable def subtypeVal (U : TopologicalSpace.Opens M) (hU : Nonempty U) :
    PartialDiffeomorph I I U M n where
  toPartialEquiv := (U.openPartialHomeomorphSubtypeCoe hU).toPartialEquiv
  open_source := (U.openPartialHomeomorphSubtypeCoe hU).open_source
  open_target := (U.openPartialHomeomorphSubtypeCoe hU).open_target
  contMDiffOn_toFun := contMDiff_subtypeVal.contMDiffOn
  contMDiffOn_invFun := fun y hy ↦ by
    refine (ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff _ _ _).1 ?_
    exact contMDiffWithinAt_id.congr
      (fun z hz ↦ (U.openPartialHomeomorphSubtypeCoe hU).right_inv hz)
      ((U.openPartialHomeomorphSubtypeCoe hU).right_inv hy)

variable {I n}

@[simp]
theorem coe_subtypeVal (U : TopologicalSpace.Opens M) (hU : Nonempty U) :
    ⇑(subtypeVal I n U hU) = Subtype.val :=
  (rfl)

@[simp]
theorem subtypeVal_source (U : TopologicalSpace.Opens M) (hU : Nonempty U) :
    (subtypeVal I n U hU).source = univ :=
  U.openPartialHomeomorphSubtypeCoe_source hU

@[simp]
theorem subtypeVal_target (U : TopologicalSpace.Opens M) (hU : Nonempty U) :
    (subtypeVal I n U hU).target = U :=
  U.openPartialHomeomorphSubtypeCoe_target hU

/-- The inverse of the inclusion of `U` sends each point of `U` to itself. -/
theorem subtypeVal_symm_apply (U : TopologicalSpace.Opens M) (hU : Nonempty U) {x : M}
    (hx : x ∈ U) : (subtypeVal I n U hU).toPartialEquiv.symm x = ⟨x, hx⟩ :=
  (U.openPartialHomeomorphSubtypeCoe hU).left_inv (x := ⟨x, hx⟩) (mem_univ _)

@[simp]
theorem subtypeVal_symm_apply_coe (U : TopologicalSpace.Opens M) (hU : Nonempty U) (x : U) :
    (subtypeVal I n U hU).toPartialEquiv.symm x = x :=
  subtypeVal_symm_apply U hU x.property

end PartialDiffeomorph

namespace TauCeti

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners 𝕜 E H} {n : WithTop ℕ∞}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

/-- The inclusion of an open subset `U` of `M`, charted by the restrictions of the charts of `M`,
is a `C^n` local diffeomorphism. -/
theorem isLocalDiffeomorph_subtype_val {U : TopologicalSpace.Opens M} :
    IsLocalDiffeomorph I I n (Subtype.val : U → M) := fun x ↦
  (PartialDiffeomorph.subtypeVal I n U ⟨x⟩).isLocalDiffeomorphAt I I n (mem_univ x)

/-- The inclusion of an open subset has bijective differentials. -/
theorem bijective_mfderiv_subtype_val {U : TopologicalSpace.Opens M} (x : U) :
    Function.Bijective (mfderiv I I (Subtype.val : U → M) x) :=
  ((isLocalDiffeomorph_subtype_val (n := 1) x).isInvertible_mfderiv one_ne_zero).bijective

/-- The differential of the inclusion of `V` in `M` factors through the inclusion of `V` in a
larger open set `U`. -/
theorem mfderiv_subtype_val_inclusion_apply {U V : TopologicalSpace.Opens M} (h : V ≤ U) (y : V)
    (v : TangentSpace I y) :
    mfderiv I I (Subtype.val : U → M) (TopologicalSpace.Opens.inclusion h y)
        (mfderiv I I (TopologicalSpace.Opens.inclusion h) y v) =
      mfderiv I I (Subtype.val : V → M) y v := by
  rw [← mfderiv_comp_apply y ((contMDiff_subtypeVal (n := 1)).mdifferentiableAt one_ne_zero)
    ((contMDiff_inclusion (n := 1) h).mdifferentiableAt one_ne_zero)]
  -- `Subtype.val ∘ Opens.inclusion h` is `Subtype.val`, pointwise by definition.
  rfl

/-- The inclusion of nested open sets has bijective differentials. -/
theorem bijective_mfderiv_inclusion {U V : TopologicalSpace.Opens M} (h : V ≤ U) (y : V) :
    Function.Bijective (mfderiv I I (TopologicalSpace.Opens.inclusion h) y) := by
  have hcomp : ⇑(mfderiv I I (Subtype.val : U → M) (TopologicalSpace.Opens.inclusion h y)) ∘
      ⇑(mfderiv I I (TopologicalSpace.Opens.inclusion h) y) =
      ⇑(mfderiv I I (Subtype.val : V → M) y) :=
    funext (mfderiv_subtype_val_inclusion_apply h y)
  exact (Function.Bijective.of_comp_iff' (bijective_mfderiv_subtype_val _) _).1
    (hcomp ▸ bijective_mfderiv_subtype_val y)

end TauCeti

namespace PartialDiffeomorph

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {H : Type*} [TopologicalSpace H] {G : Type*} [TopologicalSpace G]
  {I : ModelWithCorners 𝕜 E H} {J : ModelWithCorners 𝕜 F G} {n : WithTop ℕ∞}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N]

/-- **Carrying a partial diffeomorphism out of an open subset to the ambient manifold.** If `Φ` is
a `C^n` partial diffeomorphism out of an open subset `U` of `M` and `x ∈ Φ.source`, then there is a
`C^n` partial diffeomorphism `e` out of `M` whose source contains `x` and lies in `U`, which agrees
with `Φ` at `x`, whose target lies in that of `Φ`, and whose inverse is the inverse of `Φ` followed
by the inclusion of `U`. -/
theorem exists_ambient_of_opens {U : TopologicalSpace.Opens M}
    (Φ : PartialDiffeomorph I J U N n) {x : U} (hx : x ∈ Φ.source) :
    ∃ e : PartialDiffeomorph I J M N n, (x : M) ∈ e.source ∧ e.source ⊆ U ∧ e x = Φ x ∧
      e.target ⊆ Φ.target ∧ ∀ z ∈ e.target, e.symm z = Φ.symm z := by
  -- Precompose `Φ` with a local inverse `Ψ` of the inclusion at `x`.
  have hi := TauCeti.isLocalDiffeomorph_subtype_val (I := I) (n := n) (U := U) x
  let Ψ := hi.localInverse
  have hΨx : Ψ x = x := hi.localInverse_left_inv hi.localInverse_mem_target
  refine ⟨Ψ.trans Φ, ?_, fun y hy ↦ ?_, ?_, fun z hz ↦ ?_, fun z hz ↦ ?_⟩
  · rw [trans_source, mem_inter_iff, mem_preimage, hΨx]
    exact ⟨hi.localInverse_mem_source, hx⟩
  · rw [← hi.localInverse_right_inv ((Ψ.trans_source Φ).subset hy).1]
    exact (Ψ y).property
  · rw [coe_trans, Function.comp_apply, hΨx]
  · exact ((Ψ.trans_target Φ).subset hz).1
  · -- On the target of `Ψ`, the inverse of `Ψ` is the inclusion.
    have hz' := ((Ψ.trans_target Φ).subset hz).2
    have h := hi.localInverse_right_inv (Ψ.map_target hz')
    rw [Ψ.right_inv hz'] at h
    rw [coe_trans_symm, Function.comp_apply]
    exact h.symm

/-- **A partial diffeomorphism between open subsets, read in the ambient manifolds.** A
partial diffeomorphism `Φ` from an open subset `U` of `M` to an open subset `V` of `N` is a partial
diffeomorphism from `M` to `N`, with source and target the images of those of `Φ` in `M` and `N`,
and which agrees with `Φ` on `U`. The nonemptiness hypotheses provide the junk values off `U` and
`V`. -/
noncomputable def liftOpens {U : TopologicalSpace.Opens M} {V : TopologicalSpace.Opens N}
    (Φ : PartialDiffeomorph I J U V n) (hU : Nonempty U) (hV : Nonempty V) :
    PartialDiffeomorph I J M N n :=
  (subtypeVal I n U hU).symm.trans (Φ.trans (subtypeVal J n V hV))

variable {U : TopologicalSpace.Opens M} {V : TopologicalSpace.Opens N}
  (Ψ : PartialDiffeomorph I J U V n) (hU : Nonempty U) (hV : Nonempty V)

/-- On `U`, the lift of `Ψ` is `Ψ`. -/
@[simp]
theorem liftOpens_apply_coe (x : U) : ⇑(Ψ.liftOpens hU hV) x = Ψ x := by
  simp only [liftOpens, coe_trans, Function.comp_apply, PartialDiffeomorph.symm_toPartialEquiv,
    subtypeVal_symm_apply_coe, coe_subtypeVal]

/-- The lift of `Ψ` restricts to `Ψ` on `U`. -/
theorem liftOpens_comp_subtypeVal :
    ⇑(Ψ.liftOpens hU hV) ∘ Subtype.val = Subtype.val ∘ Ψ :=
  funext (Ψ.liftOpens_apply_coe hU hV)

/-- On `U`, the lift of `Ψ` has the differential of `Ψ`, the tangent spaces of `U` and `V` being
those of `M` and `N`. -/
theorem mfderiv_liftOpens_apply_coe (x : U) (v : TangentSpace I (x : M)) :
    mfderiv I J (Ψ.liftOpens hU hV) x v = mfderiv I J Ψ x v :=
  (TauCeti.Manifold.mfderiv_apply_of_subtype_val_comp_eq
    (Ψ.liftOpens_comp_subtypeVal hU hV).symm v).symm

/-- On `V`, the inverse of the lift of `Ψ` is the inverse of `Ψ`. -/
@[simp]
theorem liftOpens_symm_apply_coe (y : V) :
    (Ψ.liftOpens hU hV).toPartialEquiv.symm y = Ψ.toPartialEquiv.symm y :=
  -- By definition, the inverse of the lift is the inverse of the inclusion of `V`, followed by
  -- the inverse of `Ψ` and the inclusion of `U`.
  congrArg Subtype.val
    (congrArg Ψ.toPartialEquiv.symm (subtypeVal_symm_apply_coe (I := J) (n := n) V hV y))

@[simp]
theorem liftOpens_source : (Ψ.liftOpens hU hV).source = Subtype.val '' Ψ.source := by
  ext x
  simp only [liftOpens, trans_source, PartialDiffeomorph.symm_toPartialEquiv,
    PartialEquiv.symm_source, subtypeVal_target, subtypeVal_source, preimage_univ, inter_univ,
    mem_inter_iff, mem_preimage, mem_image, SetLike.mem_coe]
  refine ⟨fun ⟨hx, hΨ⟩ ↦ ⟨⟨x, hx⟩, ?_, rfl⟩, ?_⟩
  · rwa [subtypeVal_symm_apply U hU hx] at hΨ
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.property, by rwa [subtypeVal_symm_apply_coe]⟩

@[simp]
theorem liftOpens_target : (Ψ.liftOpens hU hV).target = Subtype.val '' Ψ.target := by
  ext y
  simp only [liftOpens, trans_target, PartialDiffeomorph.symm_toPartialEquiv,
    PartialEquiv.symm_target, subtypeVal_source, subtypeVal_target, preimage_univ, inter_univ,
    mem_inter_iff, mem_preimage, mem_image, SetLike.mem_coe]
  refine ⟨fun ⟨hy, hΨ⟩ ↦ ⟨⟨y, hy⟩, ?_, rfl⟩, ?_⟩
  · rwa [subtypeVal_symm_apply V hV hy] at hΨ
  · rintro ⟨z, hz, rfl⟩
    exact ⟨z.property, by rwa [subtypeVal_symm_apply_coe]⟩

end PartialDiffeomorph

namespace IsLocalDiffeomorphAt

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {H : Type*} [TopologicalSpace H] {G : Type*} [TopologicalSpace G]
  {I : ModelWithCorners 𝕜 E H} {J : ModelWithCorners 𝕜 F G} {n : WithTop ℕ∞}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N] {f : M → N} {x : M}

/-- A `C^n` local diffeomorphism at `x` agrees with a partial diffeomorphism on its source, which
contains `x` and lies inside any prescribed open set containing `x`. -/
theorem exists_partialDiffeomorph_eqOn (hf : IsLocalDiffeomorphAt I J n f x) {s : Set M}
    (hs : IsOpen s) (hxs : x ∈ s) :
    ∃ Φ : PartialDiffeomorph I J M N n, x ∈ Φ.source ∧ Φ.source ⊆ s ∧ EqOn f Φ Φ.source := by
  obtain ⟨Φ, hxΦ, hfΦ⟩ := hf
  refine ⟨Φ.restrOpen s hs, ?_, ?_, fun y hy ↦ ?_⟩
  · rw [PartialDiffeomorph.restrOpen_source]
    exact ⟨hxΦ, hxs⟩
  · rw [PartialDiffeomorph.restrOpen_source]
    exact inter_subset_right
  · rw [PartialDiffeomorph.restrOpen_source] at hy
    rw [PartialDiffeomorph.coe_restrOpen]
    exact hfΦ hy.1

/-- Being a local diffeomorphism at a point depends only on the germ of the map there. -/
theorem congr_of_eventuallyEq {g : M → N} (hf : IsLocalDiffeomorphAt I J n f x)
    (h : g =ᶠ[nhds x] f) : IsLocalDiffeomorphAt I J n g x := by
  obtain ⟨s, hfg, hs, hxs⟩ := eventually_nhds_iff.mp h
  obtain ⟨Φ, hxΦ, hΦs, hfΦ⟩ := hf.exists_partialDiffeomorph_eqOn hs hxs
  exact ⟨Φ, hxΦ, fun y hy ↦ (hfg y (hΦs hy)).trans (hfΦ hy)⟩

end IsLocalDiffeomorphAt

namespace PartialDiffeomorph

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {H : Type*} [TopologicalSpace H] {G : Type*} [TopologicalSpace G]
  {I : ModelWithCorners 𝕜 E H} {J : ModelWithCorners 𝕜 F G} {n : WithTop ℕ∞}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N]

open TopologicalSpace in
/-- **Correcting a partial diffeomorphism by a diffeomorphism of its source.** Let `Ψ` be a `C^n`
partial diffeomorphism from `M` to `N` and `Θ` a `C^n` diffeomorphism of the source of `Ψ`. On any
open subset `U₀` of the source, `Ψ ∘ Θ` is a `C^n` diffeomorphism onto an open subset of `N`. -/
theorem exists_diffeomorph_opens_comp_eq (Ψ : PartialDiffeomorph I J M N n)
    (Θ : (⟨Ψ.source, Ψ.open_source⟩ : Opens M) ≃ₘ^n⟮I, I⟯ (⟨Ψ.source, Ψ.open_source⟩ : Opens M))
    {U₀ : Opens M} (hU₀ : U₀ ≤ (⟨Ψ.source, Ψ.open_source⟩ : Opens M)) :
    ∃ (U₁ : Opens N) (φ : U₀ ≃ₘ^n⟮I, J⟯ U₁),
      Subtype.val ∘ ⇑φ = (Ψ ∘ Subtype.val) ∘ Θ ∘ Opens.inclusion hU₀ := by
  let ι := Opens.inclusion hU₀
  let Φ : U₀ → N := (Ψ ∘ Subtype.val) ∘ Θ ∘ ι
  have hinj : Function.Injective Φ := fun z z' h ↦ by
    have h' := Ψ.toPartialEquiv.injOn (Θ (ι z)).property (Θ (ι z')).property h
    have hv := congrArg Subtype.val (Θ.injective (Subtype.ext h') : ι z = ι z')
    exact Subtype.ext hv
  -- Near each point, `ι` is the inclusion of `U₀` followed by the inverse of that of the source.
  have hι : IsLocalDiffeomorph I I n ι := fun z ↦ by
    let e := (subtypeVal I n U₀ ⟨z⟩).trans (subtypeVal I n _ ⟨ι z⟩).symm
    have he : ⇑e = ι := funext fun y ↦ subtypeVal_symm_apply (I := I) (n := n) _ _ (hU₀ y.property)
    have hz : z ∈ e.source := by
      simp only [e, trans_source, symm_toPartialEquiv, PartialEquiv.symm_source,
        subtypeVal_source, subtypeVal_target, coe_subtypeVal, mem_inter_iff, mem_univ,
        mem_preimage, SetLike.mem_coe, true_and]
      exact hU₀ z.property
    exact he ▸ e.isLocalDiffeomorphAt I I n hz
  -- `Φ` is a composite of local diffeomorphisms.
  have hloc : IsLocalDiffeomorph I J n Φ := fun z ↦
    (hι z).comp (hg := (Θ.isLocalDiffeomorph _).comp
      (hg := (TauCeti.isLocalDiffeomorph_subtype_val _).comp
        (hg := Ψ.isLocalDiffeomorphAt I J n (Θ (ι z)).property)))
  exact ⟨hloc.image, hloc.diffeomorphOfInjective hinj,
    funext (IsLocalDiffeomorph.coe_diffeomorphOfInjective_apply hloc hinj)⟩

end PartialDiffeomorph
