/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.LocalDiffeomorph

/-!
# Injective local diffeomorphisms on open sets

A local diffeomorphism that is injective on an open set identifies that set smoothly with
its image. The inverse is smooth because it agrees near each image point with a local
smooth inverse.

Main results:
* `IsLocalDiffeomorphOn.isOpen_image`: the image of an open set is open.
* `IsLocalDiffeomorphOn.contMDiffOn_invFunOn`: the inverse on an injective open set is smooth.
* `IsLocalDiffeomorphOn.partialDiffeomorphOfInjOn`: the partial diffeomorphism onto the image,
  with simp lemmas for its source, target, forward function and inverse.

The construction extends Mathlib's `IsLocalDiffeomorph.diffeomorphOfBijective`, using
`Set.InjOn.toPartialEquiv` for the inverse and its inverse laws. Nonemptiness of the domain
is required to define the inverse function outside the image, even when the open set is empty.

Reference: J. M. Lee, *Introduction to Smooth Manifolds*, second edition, Proposition 4.6.
-/

public section

noncomputable section

open Set Function Filter Topology
open scoped Manifold

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E F : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {H G : Type*} [TopologicalSpace H] [TopologicalSpace G]
  {I : ModelWithCorners 𝕜 E H} {J : ModelWithCorners 𝕜 F G}
  {M N : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [TopologicalSpace N] [ChartedSpace G N]
  {n : WithTop ℕ∞} {f : M → N} {s : Set M}

namespace IsLocalDiffeomorphOn

/-- The image of an open set under a local diffeomorphism on that set is open. -/
theorem isOpen_image (hf : IsLocalDiffeomorphOn I J n f s) (hs : IsOpen s) :
    IsOpen (f '' s) := by
  apply isOpen_iff_mem_nhds.mpr
  rintro _ ⟨x, hx, rfl⟩
  rw [← hf.isLocalHomeomorphOn.map_nhds_eq hx]
  exact Filter.image_mem_map (hs.mem_nhds hx)

variable [Nonempty M]

-- The inverse proof adapts `TauCeti.Manifold.IsNormalDomain.contMDiffOn_riemannianLog`.
/-- The inverse of a local diffeomorphism injective on an open set is `C^n` on its image.
The values chosen outside the image impose no regularity requirement. -/
theorem contMDiffOn_invFunOn (hf : IsLocalDiffeomorphOn I J n f s)
    (hs : IsOpen s) (hinj : InjOn f s) :
    ContMDiffOn J I n (invFunOn f s) (f '' s) := by
  rintro _ ⟨x, hx, rfl⟩
  let h := hf ⟨x, hx⟩
  have hmem : ∀ᶠ y in 𝓝 (f x), h.localInverse y ∈ s := by
    have heq := h.localInverse_left_inv h.localInverse_mem_target
    exact h.contMDiffAt_localInverse.continuousAt.eventually
      (heq.symm ▸ hs.mem_nhds hx)
  apply (h.contMDiffAt_localInverse.congr_of_eventuallyEq ?_).contMDiffWithinAt
  filter_upwards [hmem, h.localInverse.open_source.mem_nhds h.localInverse_mem_source]
    with y hys hy
  have hfy := h.localInverse_right_inv hy
  have hyimage : ∃ z ∈ s, f z = y := ⟨h.localInverse y, hys, hfy⟩
  exact hinj (invFunOn_mem hyimage) hys ((invFunOn_eq hyimage).trans hfy.symm)

/-- A local diffeomorphism injective on an open set, packaged as a partial diffeomorphism
with that source and its actual image as target. No global injectivity is needed. -/
def partialDiffeomorphOfInjOn (hf : IsLocalDiffeomorphOn I J n f s)
    (hs : IsOpen s) (hinj : InjOn f s) : PartialDiffeomorph I J M N n where
  toPartialEquiv := hinj.toPartialEquiv f s
  open_source := hs
  open_target := hf.isOpen_image hs
  contMDiffOn_toFun := hf.contMDiffOn
  contMDiffOn_invFun := hf.contMDiffOn_invFunOn hs hinj

/-- The assembled partial diffeomorphism has exactly the prescribed open source. -/
@[simp] theorem partialDiffeomorphOfInjOn_source (hf : IsLocalDiffeomorphOn I J n f s)
    (hs : IsOpen s) (hinj : InjOn f s) :
    (hf.partialDiffeomorphOfInjOn hs hinj).source = s := (rfl)

/-- The target of the assembled partial diffeomorphism is the image of its source. -/
@[simp] theorem partialDiffeomorphOfInjOn_target (hf : IsLocalDiffeomorphOn I J n f s)
    (hs : IsOpen s) (hinj : InjOn f s) :
    (hf.partialDiffeomorphOfInjOn hs hinj).target = f '' s := (rfl)

/-- The assembled partial diffeomorphism retains the original forward function everywhere. -/
@[simp] theorem coe_partialDiffeomorphOfInjOn (hf : IsLocalDiffeomorphOn I J n f s)
    (hs : IsOpen s) (hinj : InjOn f s) :
    ⇑(hf.partialDiffeomorphOfInjOn hs hinj) = f := (rfl)

/-- The inverse function of the assembled partial diffeomorphism is the inverse on its source. -/
@[simp] theorem partialDiffeomorphOfInjOn_symm_apply (hf : IsLocalDiffeomorphOn I J n f s)
    (hs : IsOpen s) (hinj : InjOn f s) (y : N) :
    (hf.partialDiffeomorphOfInjOn hs hinj).toPartialEquiv.symm y = invFunOn f s y := (rfl)

end IsLocalDiffeomorphOn
