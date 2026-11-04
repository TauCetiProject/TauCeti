/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.LocalDiffeomorph
public import Mathlib.Geometry.Manifold.VectorBundle.Basic
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Basic

/-!
# The fibre coordinate and partial diffeomorphism of a bundle trivialization

Near a point `v₀` of the total space of a fibre bundle, every point can be read in the preferred
trivialization at the base point `v₀.proj`. For a `C^n` model of the total space, the fibre
coordinate of such a point in that trivialization is `C^n` at `v₀`. That points near `v₀` lie over
the base set of the trivialization is the topological fact
`Bundle.TotalSpace.eventually_proj_mem_baseSet_trivializationAt`.

For a vector bundle, the same reading applies to a `C^n` map from a normed space into the total
space: its fibre part, read through the linear map of the trivialization at the image of the base
point, is a `C^n` map between normed spaces there. Moreover, every atlas trivialization of a `C^n`
vector bundle is a `C^n` partial diffeomorphism between its source in `TotalSpace F E` and its
target `e.baseSet ×ˢ univ` in `B × F`, and hence a `C^n` local diffeomorphism in both directions.

## Main results

* `Bundle.TotalSpace.contMDiffAt_trivializationAt_snd`: the fibre coordinate in the
  trivialization at `v₀.proj` is `C^n` at `v₀`.
* `ContMDiffAt.contDiffAt_continuousLinearMapAt_trivializationAt`: a `C^n` map from a normed space
  into the total space of a vector bundle has `C^n` fibre coordinates in the trivialization at the
  base point of its value.
* `Bundle.Trivialization.toPartialDiffeomorph`, `Bundle.Trivialization.isLocalDiffeomorphAt`,
  `Bundle.Trivialization.isLocalDiffeomorphAt_symm`: an atlas trivialization of a `C^n` vector
  bundle as a `C^n` partial diffeomorphism and local diffeomorphism.
-/

public noncomputable section

open Bundle
open scoped Manifold

namespace Bundle.TotalSpace

variable {n : WithTop ℕ∞} {𝕜 B F : Type*} {E : B → Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [TopologicalSpace (TotalSpace F E)]
  [∀ x, TopologicalSpace (E x)] {EB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB]
  {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners 𝕜 EB HB} [TopologicalSpace B]
  [ChartedSpace HB B] [FiberBundle F E]

/-- The fibre coordinate in the trivialization at `v₀.proj` is `C^n` at `v₀`. -/
theorem contMDiffAt_trivializationAt_snd (v₀ : TotalSpace F E) :
    ContMDiffAt (IB.prod 𝓘(𝕜, F)) 𝓘(𝕜, F) n
      (fun v ↦ (trivializationAt F E v₀.proj v).2) v₀ :=
  (contMDiffAt_totalSpace.1 contMDiffAt_id).2

end Bundle.TotalSpace

namespace ContMDiffAt

variable {n : WithTop ℕ∞} {𝕜 B F : Type*} {E : B → Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [TopologicalSpace (TotalSpace F E)]
  [∀ x, TopologicalSpace (E x)] [∀ x, AddCommMonoid (E x)] [∀ x, Module 𝕜 (E x)]
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB]
  {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners 𝕜 EB HB} [TopologicalSpace B]
  [ChartedSpace HB B] [FiberBundle F E] [VectorBundle 𝕜 F E]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G] {b : G → B} {s : ∀ z, E (b z)} {z₀ : G}

/-- A `C^n` map `z ↦ (b z, s z)` from a normed space into the total space of a vector bundle has
`C^n` fibre coordinates in the trivialization at `b z₀`, read through its linear map. -/
theorem contDiffAt_continuousLinearMapAt_trivializationAt
    (h : ContMDiffAt 𝓘(𝕜, G) (IB.prod 𝓘(𝕜, F)) n (fun z ↦ TotalSpace.mk' F (b z) (s z)) z₀) :
    ContDiffAt 𝕜 n (fun z ↦ (trivializationAt F E (b z₀)).continuousLinearMapAt 𝕜 (b z) (s z))
      z₀ := by
  refine (contMDiffAt_iff_contDiffAt.mp (contMDiffAt_totalSpace.mp h).2).congr_of_eventuallyEq ?_
  filter_upwards [(contMDiffAt_totalSpace.mp h).1.continuousAt.preimage_mem_nhds
    ((trivializationAt F E (b z₀)).open_baseSet.mem_nhds
      (FiberBundle.mem_baseSet_trivializationAt F E _))] with z hz
  exact (trivializationAt F E (b z₀)).continuousLinearMapAt_apply_of_mem (R := 𝕜) hz _

end ContMDiffAt

namespace Bundle.Trivialization

variable {𝕜 B F : Type*} {E : B → Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [TopologicalSpace (TotalSpace F E)]
  [∀ x, TopologicalSpace (E x)] [∀ x, AddCommMonoid (E x)] [∀ x, Module 𝕜 (E x)]
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB]
  {HB : Type*} [TopologicalSpace HB] (IB : ModelWithCorners 𝕜 EB HB) [TopologicalSpace B]
  [ChartedSpace HB B] (n : WithTop ℕ∞) [FiberBundle F E] [VectorBundle 𝕜 F E]
  [ContMDiffVectorBundle n F E IB]
  (e : Trivialization F (π F E)) [MemTrivializationAtlas e]

/-- An atlas trivialization of a `C^n` vector bundle as a `C^n` partial diffeomorphism between
its open source in `TotalSpace F E` and its open target `e.baseSet ×ˢ univ` in `B × F`. -/
def toPartialDiffeomorph :
    PartialDiffeomorph (IB.prod 𝓘(𝕜, F)) (IB.prod 𝓘(𝕜, F)) (TotalSpace F E) (B × F) n where
  toPartialEquiv := e.toPartialEquiv
  open_source := e.open_source
  open_target := e.open_target
  contMDiffOn_toFun := e.contMDiffOn
  contMDiffOn_invFun := e.contMDiffOn_symm

/-- The underlying `PartialEquiv` of `e.toPartialDiffeomorph` is `e.toPartialEquiv`. -/
@[simp]
theorem toPartialDiffeomorph_toPartialEquiv :
    (e.toPartialDiffeomorph IB n).toPartialEquiv = e.toPartialEquiv := (rfl)

/-- The source of `e.toPartialDiffeomorph` is `e.source`. -/
theorem toPartialDiffeomorph_source : (e.toPartialDiffeomorph IB n).source = e.source := (rfl)

/-- The target of `e.toPartialDiffeomorph` is `e.target`. -/
theorem toPartialDiffeomorph_target : (e.toPartialDiffeomorph IB n).target = e.target := (rfl)

/-- Coercing `e.toPartialDiffeomorph` to a function recovers `e`. -/
theorem coe_toPartialDiffeomorph : ⇑(e.toPartialDiffeomorph IB n) = e := e.coe_coe.symm

/-- Applying the partial inverse of `e.toPartialDiffeomorph` agrees with
`e.toOpenPartialHomeomorph.symm`. -/
theorem toPartialDiffeomorph_symm_apply (q : B × F) :
    (e.toPartialDiffeomorph IB n).toPartialEquiv.symm q = e.toOpenPartialHomeomorph.symm q := (rfl)

variable {IB n e}

/-- An atlas trivialization of a `C^n` vector bundle is a `C^n` local diffeomorphism at every
point of its source. -/
theorem isLocalDiffeomorphAt {p : TotalSpace F E} (hp : p ∈ e.source) :
    IsLocalDiffeomorphAt (IB.prod 𝓘(𝕜, F)) (IB.prod 𝓘(𝕜, F)) n e p :=
  TauCeti.isLocalDiffeomorphAt_of_eqOn (Φ := e.toPartialDiffeomorph IB n) hp
    fun _ _ ↦ (congrFun e.coe_coe _).symm

/-- The partial inverse of an atlas trivialization of a `C^n` vector bundle is a `C^n` local
diffeomorphism at every point of its target. -/
theorem isLocalDiffeomorphAt_symm {q : B × F} (hq : q ∈ e.target) :
    IsLocalDiffeomorphAt (IB.prod 𝓘(𝕜, F)) (IB.prod 𝓘(𝕜, F)) n e.toOpenPartialHomeomorph.symm q :=
  TauCeti.isLocalDiffeomorphAt_of_eqOn (Φ := (e.toPartialDiffeomorph IB n).symm) hq
    fun _ _ ↦ rfl

end Bundle.Trivialization
