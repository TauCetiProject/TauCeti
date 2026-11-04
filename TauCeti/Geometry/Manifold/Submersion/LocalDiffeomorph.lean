/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.LocalDiffeomorph
public import Mathlib.Geometry.Manifold.Submersion
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Basic
import TauCeti.Geometry.Manifold.Submersion.Basic

/-!
# Composing submersions with local diffeomorphisms

Mathlib defines `Manifold.IsSubmersion` by a normal form in charts and lists the composition of
submersions as a `TODO` in `Mathlib/Geometry/Manifold/Submersion.lean`. This file treats the
local diffeomorphism case: composing with a `C^n` **local diffeomorphism**, on either side,
preserves the submersion normal form at a point, with the same complement.

Nothing has to be recombined. A partial diffeomorphism `Φ` of the source carries a chart `ψ` of
the maximal atlas to the chart `Φ ≫ ψ`, and `f ∘ Φ` read in it is `f` read in `ψ`. On the target,
a partial diffeomorphism `Θ` near `f x` pulls a chart `χ` back to `Θ⁻¹ ≫ χ`, and `Θ ∘ f` read in
it is `f` read in `χ`, once the source chart is shrunk so that `f` maps it into the source of `Θ`.

Precomposition can also be undone: if `q` is a local diffeomorphism at `x` and `f ∘ q` is a
submersion at `x`, then `f` is a submersion at `q x`, since near `q x` the map `f` is `f ∘ q`
composed with a local inverse of `q`. This is how submersions descend along quotient maps which
are local diffeomorphisms, such as orbit projections of free properly discontinuous actions.

## Main results

* `TauCeti.isSubmersionAtOfComplement_comp_isLocalDiffeomorphAt`,
  `TauCeti.isSubmersionAtOfComplement_isLocalDiffeomorphAt_comp`: the pointwise normal form with
  a fixed complement survives composing with a local diffeomorphism on the source or on the
  target; `TauCeti.isSubmersionAt_comp_isLocalDiffeomorphAt` and
  `TauCeti.isSubmersionAt_isLocalDiffeomorphAt_comp` are the versions without a fixed complement.
* `TauCeti.isSubmersionOfComplement_comp_isLocalDiffeomorph`,
  `TauCeti.isSubmersionOfComplement_isLocalDiffeomorphAt_comp`,
  `TauCeti.isSubmersion_comp_isLocalDiffeomorph`, `TauCeti.isSubmersion_isLocalDiffeomorphAt_comp`:
  the corresponding statements for submersions.
* `TauCeti.isSubmersionAtOfComplement_of_comp_isLocalDiffeomorphAt`,
  `TauCeti.isSubmersionAt_of_comp_isLocalDiffeomorphAt`: if `f ∘ q` is a submersion at `x` and `q`
  is a local diffeomorphism at `x`, then `f` is a submersion at `q x`.
* `TauCeti.isSubmersionAtOfComplement_comp_isLocalDiffeomorphAt_iff`,
  `TauCeti.isSubmersionAt_comp_isLocalDiffeomorphAt_iff`: hence precomposing with a local
  diffeomorphism neither creates nor destroys submersions at a point.

The two composition proofs share their chart constructions with those for immersions in
`TauCeti.Geometry.Manifold.Immersion.LocalDiffeomorph`: both use
`IsLocalDiffeomorphAt.exists_mem_maximalAtlas_eqOn_extend_symm` and
`IsLocalDiffeomorphAt.exists_mem_maximalAtlas_comp_eqOn`, with the submersion normal form in place
of the immersion normal form.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer GTM 218 (2013), Chapter 4
  (submersions and local diffeomorphisms).
-/

public section

noncomputable section

namespace TauCeti

open Manifold Set Topology
open scoped Manifold ContDiff

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {H : Type*} [TopologicalSpace H] {G : Type*} [TopologicalSpace G]
  {I : ModelWithCorners 𝕜 E H} {J : ModelWithCorners 𝕜 E' G}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {M' : Type*} [TopologicalSpace M'] [ChartedSpace H M']
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N]
  {P : Type*} [TopologicalSpace P] [ChartedSpace G P]
  {n : ℕ∞ω} {f : M → N}

/-! ### Precomposing with a local diffeomorphism -/

/-- Precomposing with a local diffeomorphism of the source preserves the submersion normal form at
a point, with the same complement: the domain chart is pulled back along a partial diffeomorphism
representing the local diffeomorphism. -/
theorem isSubmersionAtOfComplement_comp_isLocalDiffeomorphAt [IsManifold I n M']
    {g : M' → M} {x : M'} (hg : IsLocalDiffeomorphAt I I n g x)
    (h : IsSubmersionAtOfComplement F I J n f (g x)) :
    IsSubmersionAtOfComplement F I J n (f ∘ g) x := by
  obtain ⟨φ, hφ, hxφ, hφt, hgφ⟩ :=
    hg.exists_mem_maximalAtlas_eqOn_extend_symm h.domChart_mem_maximalAtlas h.mem_domChart_source
  exact .mk_of_continuousAt (h.contMDiffAt.continuousAt.comp hg.contMDiffAt.continuousAt) h.equiv
    φ h.codChart hxφ h.mem_codChart_source hφ h.codChart_mem_maximalAtlas fun u hu =>
      (congrArg (h.codChart.extend J ∘ f) (hgφ hu)).trans (h.writtenInCharts (hφt hu))

/-- Precomposing with a local diffeomorphism of the source preserves being a submersion at a
point. -/
theorem isSubmersionAt_comp_isLocalDiffeomorphAt [IsManifold I n M']
    {g : M' → M} {x : M'} (hg : IsLocalDiffeomorphAt I I n g x)
    (h : IsSubmersionAt I J n f (g x)) : IsSubmersionAt I J n (f ∘ g) x :=
  (isSubmersionAtOfComplement_comp_isLocalDiffeomorphAt hg
    h.isSubmersionAtOfComplement_complement).isSubmersionAt

/-- Precomposing a submersion with a fixed complement by a local diffeomorphism gives a submersion
with the same complement. -/
theorem isSubmersionOfComplement_comp_isLocalDiffeomorph [IsManifold I n M']
    {g : M' → M} (hg : IsLocalDiffeomorph I I n g) (h : IsSubmersionOfComplement F I J n f) :
    IsSubmersionOfComplement F I J n (f ∘ g) :=
  isSubmersionOfComplement_iff.2 fun x =>
    isSubmersionAtOfComplement_comp_isLocalDiffeomorphAt (hg x) (h.isSubmersionAt (g x))

/-- Precomposing a submersion with a local diffeomorphism gives a submersion. -/
theorem isSubmersion_comp_isLocalDiffeomorph [IsManifold I n M']
    {g : M' → M} (hg : IsLocalDiffeomorph I I n g) (h : IsSubmersion I J n f) :
    IsSubmersion I J n (f ∘ g) :=
  (isSubmersionOfComplement_comp_isLocalDiffeomorph hg
    h.isSubmersionOfComplement_complement).isSubmersion

/-- **Undoing a precomposition.** If `q` is a local diffeomorphism at `x` and `f ∘ q` is a
submersion at `x`, then `f` is a submersion at `q x`, with the same complement: near `q x`, the map
`f` is `f ∘ q` composed with a local inverse of `q`. -/
theorem isSubmersionAtOfComplement_of_comp_isLocalDiffeomorphAt [IsManifold I n M]
    {q : M' → M} {x : M'} (hq : IsLocalDiffeomorphAt I I n q x)
    (h : IsSubmersionAtOfComplement F I J n (f ∘ q) x) :
    IsSubmersionAtOfComplement F I J n f (q x) := by
  have h' : IsSubmersionAtOfComplement F I J n (f ∘ q) (hq.localInverse (q x)) := by
    rwa [hq.localInverse_left_inv hq.localInverse_mem_target]
  exact (isSubmersionAtOfComplement_comp_isLocalDiffeomorphAt
    hq.localInverse_isLocalDiffeomorphAt h').congr_of_eventuallyEq
    (hq.localInverse_eventuallyEq_right.fun_comp f)

/-- **Undoing a precomposition.** If `q` is a local diffeomorphism at `x` and `f ∘ q` is a
submersion at `x`, then `f` is a submersion at `q x`. -/
theorem isSubmersionAt_of_comp_isLocalDiffeomorphAt [IsManifold I n M]
    {q : M' → M} {x : M'} (hq : IsLocalDiffeomorphAt I I n q x)
    (h : IsSubmersionAt I J n (f ∘ q) x) : IsSubmersionAt I J n f (q x) :=
  (isSubmersionAtOfComplement_of_comp_isLocalDiffeomorphAt hq
    h.isSubmersionAtOfComplement_complement).isSubmersionAt

/-- Precomposing with a local diffeomorphism of the source neither creates nor destroys the
submersion normal form at a point: `f ∘ g` is a submersion at `x`, with complement `F`, exactly
when `f` is one at `g x`. -/
theorem isSubmersionAtOfComplement_comp_isLocalDiffeomorphAt_iff [IsManifold I n M]
    [IsManifold I n M'] {g : M' → M} {x : M'} (hg : IsLocalDiffeomorphAt I I n g x) :
    IsSubmersionAtOfComplement F I J n (f ∘ g) x ↔
      IsSubmersionAtOfComplement F I J n f (g x) :=
  ⟨isSubmersionAtOfComplement_of_comp_isLocalDiffeomorphAt hg,
    isSubmersionAtOfComplement_comp_isLocalDiffeomorphAt hg⟩

/-- Precomposing with a local diffeomorphism of the source neither creates nor destroys
submersions at a point: `f ∘ g` is a submersion at `x` exactly when `f` is one at `g x`. -/
theorem isSubmersionAt_comp_isLocalDiffeomorphAt_iff [IsManifold I n M] [IsManifold I n M']
    {g : M' → M} {x : M'} (hg : IsLocalDiffeomorphAt I I n g x) :
    IsSubmersionAt I J n (f ∘ g) x ↔ IsSubmersionAt I J n f (g x) :=
  ⟨isSubmersionAt_of_comp_isLocalDiffeomorphAt hg, isSubmersionAt_comp_isLocalDiffeomorphAt hg⟩

/-! ### Postcomposing with a local diffeomorphism -/

/-- Postcomposing with a local diffeomorphism of the target preserves the submersion normal form at
a point, with the same complement: the codomain chart is pulled back along a partial
diffeomorphism representing the local diffeomorphism, after shrinking the domain chart so that the
submersion maps it into the source of that partial diffeomorphism. -/
theorem isSubmersionAtOfComplement_isLocalDiffeomorphAt_comp [IsManifold J n P]
    {k : N → P} {x : M} (hk : IsLocalDiffeomorphAt J J n k (f x))
    (h : IsSubmersionAtOfComplement F I J n f x) :
    IsSubmersionAtOfComplement F I J n (k ∘ f) x := by
  have hf : ContinuousAt f x := h.contMDiffAt.continuousAt
  obtain ⟨φ, hφ, ψ, hψ, hxφ, hψx, hφt, hfφ⟩ := hk.exists_mem_maximalAtlas_comp_eqOn hf
    h.domChart_mem_maximalAtlas h.mem_domChart_source h.codChart_mem_maximalAtlas
    h.mem_codChart_source
  exact .mk_of_continuousAt (hk.contMDiffAt.continuousAt.comp hf) h.equiv φ ψ hxφ hψx hφ hψ
    fun u hu => (hfφ hu).trans (h.writtenInCharts (hφt hu))

/-- Postcomposing with a local diffeomorphism of the target preserves being a submersion at a
point. -/
theorem isSubmersionAt_isLocalDiffeomorphAt_comp [IsManifold J n P] {k : N → P} {x : M}
    (hk : IsLocalDiffeomorphAt J J n k (f x))
    (h : IsSubmersionAt I J n f x) : IsSubmersionAt I J n (k ∘ f) x :=
  (isSubmersionAtOfComplement_isLocalDiffeomorphAt_comp hk
    h.isSubmersionAtOfComplement_complement).isSubmersionAt

/-- Postcomposing a submersion with a fixed complement by a map which is a local diffeomorphism at
every point of its image gives a submersion with the same complement. -/
theorem isSubmersionOfComplement_isLocalDiffeomorphAt_comp [IsManifold J n P] {k : N → P}
    (hk : ∀ x, IsLocalDiffeomorphAt J J n k (f x)) (h : IsSubmersionOfComplement F I J n f) :
    IsSubmersionOfComplement F I J n (k ∘ f) :=
  isSubmersionOfComplement_iff.2 fun x =>
    isSubmersionAtOfComplement_isLocalDiffeomorphAt_comp (hk x) (h.isSubmersionAt x)

/-- Postcomposing a submersion with a map which is a local diffeomorphism at every point of its
image gives a submersion. -/
theorem isSubmersion_isLocalDiffeomorphAt_comp [IsManifold J n P] {k : N → P}
    (hk : ∀ x, IsLocalDiffeomorphAt J J n k (f x))
    (h : IsSubmersion I J n f) : IsSubmersion I J n (k ∘ f) :=
  (isSubmersionOfComplement_isLocalDiffeomorphAt_comp hk
    h.isSubmersionOfComplement_complement).isSubmersion

end TauCeti
