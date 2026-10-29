/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.LocalDiffeomorph

-- The local-diffeomorphism witnesses are needed to construct their product.
import all Mathlib.Geometry.Manifold.LocalDiffeomorph

/-!
# Products of local diffeomorphisms

The product of two partial diffeomorphisms has product source and target. Applying this to local
representatives shows that the product of two local diffeomorphisms is a local diffeomorphism.
-/

public noncomputable section

open Set
open scoped Manifold ContDiff

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E E' F F' : Type*}
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [NormedAddCommGroup F'] [NormedSpace 𝕜 F']
  {H H' G G' : Type*}
  [TopologicalSpace H] [TopologicalSpace H'] [TopologicalSpace G] [TopologicalSpace G']
  {I : ModelWithCorners 𝕜 E H} {I' : ModelWithCorners 𝕜 E' H'}
  {J : ModelWithCorners 𝕜 F G} {J' : ModelWithCorners 𝕜 F' G'}
  {M M' N N' : Type*}
  [TopologicalSpace M] [ChartedSpace H M] [TopologicalSpace M'] [ChartedSpace H' M']
  [TopologicalSpace N] [ChartedSpace G N] [TopologicalSpace N'] [ChartedSpace G' N']
  {n : ℕ∞ω}

/-- The product of partial diffeomorphisms, on the product of their sources. -/
def PartialDiffeomorph.prod (e : PartialDiffeomorph I I' M M' n)
    (f : PartialDiffeomorph J J' N N' n) :
    PartialDiffeomorph (I.prod J) (I'.prod J') (M × N) (M' × N') n where
  toPartialEquiv := e.toPartialEquiv.prod f.toPartialEquiv
  open_source := e.open_source.prod f.open_source
  open_target := e.open_target.prod f.open_target
  contMDiffOn_toFun := e.contMDiffOn.prodMap f.contMDiffOn
  contMDiffOn_invFun := e.symm.contMDiffOn.prodMap f.symm.contMDiffOn

/-- The source of a product partial diffeomorphism is the product of its sources. -/
@[simp]
theorem PartialDiffeomorph.prod_source (e : PartialDiffeomorph I I' M M' n)
    (f : PartialDiffeomorph J J' N N' n) : (e.prod f).source = e.source ×ˢ f.source := (rfl)

/-- The target of a product partial diffeomorphism is the product of its targets. -/
@[simp]
theorem PartialDiffeomorph.prod_target (e : PartialDiffeomorph I I' M M' n)
    (f : PartialDiffeomorph J J' N N' n) : (e.prod f).target = e.target ×ˢ f.target := (rfl)

/-- A product partial diffeomorphism acts componentwise. -/
@[simp]
theorem PartialDiffeomorph.prod_apply (e : PartialDiffeomorph I I' M M' n)
    (f : PartialDiffeomorph J J' N N' n) (z : M × N) : (e.prod f) z = (e z.1, f z.2) := (rfl)

/-- The inverse of a product is the product of the inverses. -/
@[simp]
theorem PartialDiffeomorph.prod_symm (e : PartialDiffeomorph I I' M M' n)
    (f : PartialDiffeomorph J J' N N' n) : (e.prod f).symm = e.symm.prod f.symm := (rfl)

/-- The product map is a local diffeomorphism at a pair of points where its factors are. -/
theorem IsLocalDiffeomorphAt.prodMap {f : M → M'} {g : N → N'} {x : M} {y : N}
    (hf : IsLocalDiffeomorphAt I I' n f x) (hg : IsLocalDiffeomorphAt J J' n g y) :
    IsLocalDiffeomorphAt (I.prod J) (I'.prod J') n (Prod.map f g) (x, y) := by
  obtain ⟨e, hx, he⟩ := hf
  obtain ⟨e', hy, he'⟩ := hg
  exact ⟨e.prod e', ⟨hx, hy⟩, fun z hz ↦ Prod.ext (he hz.1) (he' hz.2)⟩

/-- Products of local diffeomorphisms are local diffeomorphisms. -/
theorem IsLocalDiffeomorph.prodMap {f : M → M'} {g : N → N'}
    (hf : IsLocalDiffeomorph I I' n f) (hg : IsLocalDiffeomorph J J' n g) :
    IsLocalDiffeomorph (I.prod J) (I'.prod J') n (Prod.map f g) :=
  fun z ↦ (hf z.1).prodMap (hg z.2)
