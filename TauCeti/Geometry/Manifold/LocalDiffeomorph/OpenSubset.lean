/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.LocalDiffeomorph
import TauCeti.Geometry.Manifold.ContMDiff.Subtype
import TauCeti.Geometry.Manifold.Diffeomorph.Basic
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Constructions

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
manifold is diffeomorphic to it through its inclusion, and a diffeomorphism mapping an open subset
onto another restricts to a diffeomorphism between them. A partial diffeomorphism out of an open
subset can be carried, near any point of its source, to the ambient manifold.

## Main declarations

* `PartialDiffeomorph.restrOpen`: the restriction of a partial diffeomorphism to an open set.
* `PartialDiffeomorph.contMDiffOn_toOpenPartialHomeomorph_restrOpen` and its `symm` version: the
  restrictions of the underlying open partial homeomorphism to an open set are smooth.
* `PartialDiffeomorph.toDiffeomorphSourceTarget`: a partial diffeomorphism as a diffeomorphism
  between its open source and its open target.
* `Diffeomorph.ofTop`: an open subset equal to `⊤` is diffeomorphic to the ambient manifold.
* `Diffeomorph.subtype`: a diffeomorphism restricts to a diffeomorphism between open subsets that
  it maps onto each other.
* `TopologicalSpace.Opens.partialDiffeomorphSubtypeCoe`: the inclusion of a nonempty open subset as
  a `C^n` partial diffeomorphism.
* `Diffeomorph.toPartialDiffeomorphOpens`: a `C^n` diffeomorphism between nonempty open subsets as
  a `C^n` partial diffeomorphism between the ambient manifolds.
* `TauCeti.isLocalDiffeomorph_subtype_val`: the inclusion of an open subset is a `C^n` local
  diffeomorphism.
* `PartialDiffeomorph.exists_ambient_of_opens`: a partial diffeomorphism out of an open subset
  agrees near a point of its source with a partial diffeomorphism out of the ambient manifold.
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
    (g.contMDiff.comp contMDiff_subtype_val)
  contMDiff_invFun := (TauCeti.ContMDiff.subtypeVal_comp_iff _ _).1
    (g.symm.contMDiff.comp contMDiff_subtype_val)

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

namespace TopologicalSpace.Opens

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners 𝕜 E H} {n : WithTop ℕ∞}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

/-- The inclusion of a nonempty open subset `U` of `M`, charted by the restrictions of the charts
of `M`, as a `C^n` partial diffeomorphism from `U` to `M`. -/
noncomputable def partialDiffeomorphSubtypeCoe (U : TopologicalSpace.Opens M) (hU : Nonempty U) :
    PartialDiffeomorph I I U M n :=
  let e := U.openPartialHomeomorphSubtypeCoe hU
  { e.toPartialEquiv with
    open_source := e.open_source
    open_target := e.open_target
    contMDiffOn_toFun := contMDiff_subtype_val.contMDiffOn
    contMDiffOn_invFun := fun _ hy ↦
      (ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff _ _ _).1 <|
        contMDiffWithinAt_id.congr (fun _ hz ↦ e.right_inv hz) (e.right_inv hy) }

/-- As a function, `Opens.partialDiffeomorphSubtypeCoe` is `Subtype.val`. -/
@[simp]
theorem coe_partialDiffeomorphSubtypeCoe (U : TopologicalSpace.Opens M) (hU : Nonempty U) :
    (U.partialDiffeomorphSubtypeCoe (I := I) (n := n) hU : U → M) = Subtype.val :=
  (rfl)

/-- The source of `Opens.partialDiffeomorphSubtypeCoe` is `Set.univ`. -/
@[simp]
theorem partialDiffeomorphSubtypeCoe_source (U : TopologicalSpace.Opens M) (hU : Nonempty U) :
    (U.partialDiffeomorphSubtypeCoe (I := I) (n := n) hU).source = univ :=
  (rfl)

/-- The target of `Opens.partialDiffeomorphSubtypeCoe` is `U`. -/
@[simp]
theorem partialDiffeomorphSubtypeCoe_target (U : TopologicalSpace.Opens M) (hU : Nonempty U) :
    (U.partialDiffeomorphSubtypeCoe (I := I) (n := n) hU).target = U :=
  U.openPartialHomeomorphSubtypeCoe_target hU

/-- The underlying partial equivalence of `Opens.partialDiffeomorphSubtypeCoe`. -/
theorem partialDiffeomorphSubtypeCoe_toPartialEquiv (U : TopologicalSpace.Opens M)
    (hU : Nonempty U) :
    (U.partialDiffeomorphSubtypeCoe (I := I) (n := n) hU).toPartialEquiv =
      (U.openPartialHomeomorphSubtypeCoe hU).toPartialEquiv :=
  (rfl)

/-- On `U`, the inverse partial equivalence of `Opens.partialDiffeomorphSubtypeCoe` sends `x : U`
to `x`. -/
@[simp]
theorem partialDiffeomorphSubtypeCoe_toPartialEquiv_symm_apply_coe
    (U : TopologicalSpace.Opens M) (hU : Nonempty U) (x : U) :
    (U.partialDiffeomorphSubtypeCoe (I := I) (n := n) hU).toPartialEquiv.symm x = x :=
  (U.partialDiffeomorphSubtypeCoe (I := I) (n := n) hU).left_inv (mem_univ x)

/-- On `U`, the inverse of `Opens.partialDiffeomorphSubtypeCoe` sends `x : U` to `x`. -/
theorem partialDiffeomorphSubtypeCoe_symm_apply_coe (U : TopologicalSpace.Opens M) (hU : Nonempty U)
    (x : U) : (U.partialDiffeomorphSubtypeCoe (I := I) (n := n) hU).symm x = x :=
  U.partialDiffeomorphSubtypeCoe_toPartialEquiv_symm_apply_coe hU x

/-- At a point `x ∈ U`, the inverse of `Opens.partialDiffeomorphSubtypeCoe` evaluates to
`⟨x, hx⟩`. -/
theorem partialDiffeomorphSubtypeCoe_symm_apply (U : TopologicalSpace.Opens M) (hU : Nonempty U)
    {x : M} (hx : x ∈ U) :
    (U.partialDiffeomorphSubtypeCoe (I := I) (n := n) hU).symm x = ⟨x, hx⟩ :=
  U.partialDiffeomorphSubtypeCoe_symm_apply_coe hU ⟨x, hx⟩

end TopologicalSpace.Opens

namespace Diffeomorph

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {H : Type*} [TopologicalSpace H] {G : Type*} [TopologicalSpace G]
  {I : ModelWithCorners 𝕜 E H} {J : ModelWithCorners 𝕜 F G} {n : WithTop ℕ∞}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N]
  {U : TopologicalSpace.Opens M} {V : TopologicalSpace.Opens N}

/-- A `C^n` diffeomorphism between nonempty open subsets `U ⊆ M` and `V ⊆ N` as a `C^n` partial
diffeomorphism between `M` and `N` with source `U` and target `V`. This is inverse to
`PartialDiffeomorph.toDiffeomorphSourceTarget`. -/
noncomputable def toPartialDiffeomorphOpens (d : U ≃ₘ^n⟮I, J⟯ V) (hU : Nonempty U) :
    PartialDiffeomorph I J M N n :=
  ((U.partialDiffeomorphSubtypeCoe hU).symm.trans d.toPartialDiffeomorph).trans
    (V.partialDiffeomorphSubtypeCoe (hU.map d))

/-- The underlying partial equivalence of `Diffeomorph.toPartialDiffeomorphOpens`. -/
theorem toPartialDiffeomorphOpens_toPartialEquiv (d : U ≃ₘ^n⟮I, J⟯ V) (hU : Nonempty U) :
    (d.toPartialDiffeomorphOpens hU).toPartialEquiv =
      ((U.openPartialHomeomorphSubtypeCoe hU).toPartialEquiv.symm.trans
        d.toEquiv.toPartialEquiv).trans
        (V.openPartialHomeomorphSubtypeCoe (hU.map d)).toPartialEquiv := by
  simp [toPartialDiffeomorphOpens, PartialDiffeomorph.trans_toPartialEquiv,
    PartialDiffeomorph.symm_toPartialEquiv,
    TopologicalSpace.Opens.partialDiffeomorphSubtypeCoe_toPartialEquiv]

/-- The source of `Diffeomorph.toPartialDiffeomorphOpens` is `U`. -/
@[simp]
theorem toPartialDiffeomorphOpens_source (d : U ≃ₘ^n⟮I, J⟯ V) (hU : Nonempty U) :
    (d.toPartialDiffeomorphOpens hU).source = U := by
  simp [toPartialDiffeomorphOpens_toPartialEquiv]

/-- The target of `Diffeomorph.toPartialDiffeomorphOpens` is `V`. -/
@[simp]
theorem toPartialDiffeomorphOpens_target (d : U ≃ₘ^n⟮I, J⟯ V) (hU : Nonempty U) :
    (d.toPartialDiffeomorphOpens hU).target = V := by
  simp [toPartialDiffeomorphOpens_toPartialEquiv]

/-- On `U`, `Diffeomorph.toPartialDiffeomorphOpens` evaluates as `d`. -/
@[simp]
theorem toPartialDiffeomorphOpens_apply_coe (d : U ≃ₘ^n⟮I, J⟯ V) (hU : Nonempty U) (x : U) :
    d.toPartialDiffeomorphOpens hU x = d x := by
  simp only [toPartialDiffeomorphOpens_toPartialEquiv, PartialEquiv.trans_apply,
    Equiv.toPartialEquiv_apply]
  have hx : (U.openPartialHomeomorphSubtypeCoe hU).symm x = x :=
    (U.openPartialHomeomorphSubtypeCoe hU).left_inv (mem_univ x)
  exact congrArg (Subtype.val ∘ d) hx

/-- At a point `x ∈ U`, `Diffeomorph.toPartialDiffeomorphOpens` evaluates as `d ⟨x, hx⟩`. -/
theorem toPartialDiffeomorphOpens_apply (d : U ≃ₘ^n⟮I, J⟯ V) (hU : Nonempty U)
    {x : M} (hx : x ∈ U) : d.toPartialDiffeomorphOpens hU x = d ⟨x, hx⟩ :=
  d.toPartialDiffeomorphOpens_apply_coe hU ⟨x, hx⟩

/-- On `V`, the inverse partial equivalence of `Diffeomorph.toPartialDiffeomorphOpens` evaluates as
`d.symm`. -/
@[simp]
theorem toPartialDiffeomorphOpens_toPartialEquiv_symm_apply_coe
    (d : U ≃ₘ^n⟮I, J⟯ V) (hU : Nonempty U) (y : V) :
    (d.toPartialDiffeomorphOpens hU).toPartialEquiv.symm y = d.symm y := by
  simp only [toPartialDiffeomorphOpens_toPartialEquiv, PartialEquiv.trans_symm_eq_symm_trans_symm,
    PartialEquiv.symm_symm, PartialEquiv.trans_apply, Equiv.toPartialEquiv_symm_apply]
  have hy : (V.openPartialHomeomorphSubtypeCoe (hU.map d)).symm y = y :=
    (V.openPartialHomeomorphSubtypeCoe (hU.map d)).left_inv (mem_univ y)
  exact congrArg (Subtype.val ∘ d.symm) hy

/-- On `V`, the inverse of `Diffeomorph.toPartialDiffeomorphOpens` evaluates as `d.symm`. -/
theorem toPartialDiffeomorphOpens_symm_apply_coe (d : U ≃ₘ^n⟮I, J⟯ V) (hU : Nonempty U) (y : V) :
    (d.toPartialDiffeomorphOpens hU).symm y = d.symm y :=
  d.toPartialDiffeomorphOpens_toPartialEquiv_symm_apply_coe hU y

/-- At a point `y ∈ V`, the inverse of `Diffeomorph.toPartialDiffeomorphOpens` evaluates as
`d.symm ⟨y, hy⟩`. -/
theorem toPartialDiffeomorphOpens_symm_apply (d : U ≃ₘ^n⟮I, J⟯ V) (hU : Nonempty U)
    {y : N} (hy : y ∈ V) : (d.toPartialDiffeomorphOpens hU).symm y = d.symm ⟨y, hy⟩ :=
  d.toPartialDiffeomorphOpens_symm_apply_coe hU ⟨y, hy⟩

/-- The inverse of `Diffeomorph.toPartialDiffeomorphOpens` is `toPartialDiffeomorphOpens` of the
inverse diffeomorphism. -/
@[simp]
theorem toPartialDiffeomorphOpens_symm (d : U ≃ₘ^n⟮I, J⟯ V) (hU : Nonempty U) :
    (d.toPartialDiffeomorphOpens hU).symm = d.symm.toPartialDiffeomorphOpens (hU.map d) := by
  suffices (d.toPartialDiffeomorphOpens hU).symm.toPartialEquiv =
      (d.symm.toPartialDiffeomorphOpens (hU.map d)).toPartialEquiv by
    revert this
    cases (d.toPartialDiffeomorphOpens hU).symm
    cases d.symm.toPartialDiffeomorphOpens (hU.map d)
    rintro rfl
    rfl
  exact PartialEquiv.ext
    (fun y ↦ by simp [PartialDiffeomorph.symm_toPartialEquiv,
      toPartialDiffeomorphOpens_toPartialEquiv])
    (fun x ↦ by simp [PartialDiffeomorph.symm_toPartialEquiv,
      toPartialDiffeomorphOpens_toPartialEquiv])
    (by simp)

end Diffeomorph

namespace TauCeti

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners 𝕜 E H} {n : WithTop ℕ∞}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

/-- The inclusion of an open subset `U` of `M`, charted by the restrictions of the charts of `M`,
is a `C^n` local diffeomorphism. -/
theorem isLocalDiffeomorph_subtype_val {U : TopologicalSpace.Opens M} :
    IsLocalDiffeomorph I I n (Subtype.val : U → M) := fun x ↦
  (U.partialDiffeomorphSubtypeCoe (I := I) (n := n) ⟨x⟩).isLocalDiffeomorphAt I I n (mem_univ x)

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
    exact (Ψ y).2
  · rw [coe_trans, Function.comp_apply, hΨx]
  · exact ((Ψ.trans_target Φ).subset hz).1
  · -- On the target of `Ψ`, the inverse of `Ψ` is the inclusion.
    have hz' := ((Ψ.trans_target Φ).subset hz).2
    have h := hi.localInverse_right_inv (Ψ.map_target hz')
    rw [Ψ.right_inv hz'] at h
    rw [coe_trans_symm, Function.comp_apply]
    exact h.symm

end PartialDiffeomorph
