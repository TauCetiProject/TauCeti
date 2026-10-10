/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
module

/-
Staged for Tau Ceti, roadmap topic `PolarDecomposition`.  Mathlib is
not the destination (`ForTauCeti/README.md`); on the closed Mathlib track this
would have gone to `Mathlib/Analysis/InnerProductSpace/`, beside the polar
decomposition.

Formalized by Claude Opus 5 (claude-opus-5[1m]).
-/

public import TauCeti.Analysis.InnerProductSpace.PartialIsometry

/-!
# Partial isometries between different spaces

`ForTauCeti.Analysis.InnerProductSpace.PartialIsometry` defines a partial isometry
algebraically, as `u * star u * u = u` in a `Monoid` with `StarMul`.  That is the right
definition when it applies, and it makes `IsPartialIsometry.star_star` and the
initial-projection identity fall out of star-monoid algebra.

**It does not apply to a map between different spaces.**  `u : E →ₗ[𝕜] F` has no `star`
and lives in no monoid: `star u` would be an `F →ₗ[𝕜] E`, and there is no
multiplication carrying both.  The rectangular case has to be written with `adjoint`
and `∘ₗ` directly, which is what this file does:

* `LinearMap.IsPartialIsometry` — `u ∘ₗ u.adjoint ∘ₗ u = u`, for `u : E →ₗ[𝕜] F`;
* `LinearMap.isPartialIsometry_iff_starMul` — on endomorphisms the two agree, so
  nothing is forked and every star-monoid lemma remains available;
* `LinearMap.IsPartialIsometry.adjoint` — the class is closed under adjoint, the
  rectangular counterpart of `IsPartialIsometry.star_star`.

**Why the agreement theorem matters more than it looks.**  Two predicates of the same
name, one general and one carrier-specific, is exactly the shape that produces a
library where half the lemmas apply to a given operator and nobody can tell which
half.  `isPartialIsometry_iff_starMul` is what keeps that from happening: on `E →ₗ[𝕜] E`
the two are interchangeable, so the rectangular definition is a *generalization* rather
than a competitor.  The proof is the associativity difference and nothing else --
`u * star u * u` brackets to the left and `u ∘ₗ u.adjoint ∘ₗ u` to the right.

The polar decomposition is the consumer: `M = W |M|` with `W` a partial isometry needs
exactly this predicate when `M` is rectangular, since `W` maps `E` to `F`.

## Provenance

* Original repository: none — written directly in `ForTauCeti` on 2026-08-02.
* Extraction class: **new**.  This is not a move or a generalization of existing
  material.  `ForTauCeti.Analysis.InnerProductSpace.PartialIsometry` carries the
  square theory and stays unchanged; the rectangular predicate is the roadmap's
  `PolarDecomposition` target `isPartialIsometry_iff_starMul`, which
  presupposes a `LinearMap.IsPartialIsometry` that did not exist.
* Original authors / copyright: Jon Crall, Claude Opus 5; Copyright (c) 2026
  Kitware, Inc.; Apache 2.0.
* Spectra influence: **none** — this module imports only a sibling `ForTauCeti`
  staging module.
-/

public section

open scoped InnerProductSpace

namespace LinearMap

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 F]

/-- **Partial isometry between possibly different spaces**: `u ∘ₗ u.adjoint ∘ₗ u = u`.

This is the Moore--Penrose-style identity that the algebraic `u * star u * u = u`
becomes when source and target differ and no single carrier holds both `u` and its
adjoint. -/
@[expose]
def IsPartialIsometry (u : E →ₗ[𝕜] F) : Prop :=
  u ∘ₗ u.adjoint ∘ₗ u = u

/-- On endomorphisms the carrier-specific and star-monoid predicates agree.

The only content is bracketing: `_root_.IsPartialIsometry` reads `u * star u * u = u`,
which is `(u * star u) * u = u`, while `LinearMap.IsPartialIsometry` reads
`u ∘ₗ (u.adjoint ∘ₗ u) = u`.  `star_eq_adjoint` identifies the involutions and
`Module.End.mul_eq_comp` the products. -/
theorem isPartialIsometry_iff_starMul {u : E →ₗ[𝕜] E} :
    u.IsPartialIsometry ↔ _root_.IsPartialIsometry u := by
  simp only [LinearMap.IsPartialIsometry, _root_.IsPartialIsometry, star_eq_adjoint,
    Module.End.mul_eq_comp, LinearMap.comp_assoc]

/-- **Operator characterization, rectangular**: `u` is a partial isometry exactly when it
preserves norms on the orthogonal complement of its kernel (Conway VI.3.2).

The square version in `ForTauCeti.Analysis.InnerProductSpace.PartialIsometry` proves this
through star-monoid algebra, via `star_mul_self_eq_starProjection`.  That route is closed
here -- `star u` would be an `F →ₗ[𝕜] E` and there is no carrier holding both -- so the
argument is written directly: `u⋆ u` is the orthogonal projection onto `(ker u)ᗮ`, which is
what both directions turn on. -/
theorem isPartialIsometry_iff_norm_map {u : E →ₗ[𝕜] F} :
    u.IsPartialIsometry ↔ ∀ x ∈ (LinearMap.ker u)ᗮ, ‖u x‖ = ‖x‖ := by
  constructor
  · intro hu x hx
    have hux : u (u.adjoint (u x)) = u x := by
      have := LinearMap.congr_fun hu x
      simpa only [LinearMap.comp_apply] using this
    -- `u⋆ u x` and `x` agree, because their difference lies in `ker u` and in `(ker u)ᗮ`
    have hmemO : u.adjoint (u x) ∈ (LinearMap.ker u)ᗮ := by
      rw [LinearMap.orthogonal_ker]; exact LinearMap.mem_range_self _ _
    have hdiffO : x - u.adjoint (u x) ∈ (LinearMap.ker u)ᗮ := Submodule.sub_mem _ hx hmemO
    have hdiffK : x - u.adjoint (u x) ∈ LinearMap.ker u := by
      rw [LinearMap.mem_ker, map_sub, hux, sub_self]
    have hadj : u.adjoint (u x) = x := by
      have hz : ⟪x - u.adjoint (u x), x - u.adjoint (u x)⟫_𝕜 = 0 :=
        Submodule.inner_right_of_mem_orthogonal hdiffK hdiffO
      have := inner_self_eq_zero.mp hz
      rw [sub_eq_zero] at this
      exact this.symm
    have hsq : ‖u x‖ ^ 2 = ‖x‖ ^ 2 := by
      rw [InnerProductSpace.norm_sq_eq_re_inner (𝕜 := 𝕜) (u x),
        InnerProductSpace.norm_sq_eq_re_inner (𝕜 := 𝕜) x,
        ← LinearMap.adjoint_inner_left, hadj]
    rw [← Real.sqrt_sq (norm_nonneg (u x)), ← Real.sqrt_sq (norm_nonneg x), hsq]
  · intro h
    have hinner : ∀ a ∈ (LinearMap.ker u)ᗮ, ∀ b ∈ (LinearMap.ker u)ᗮ,
        ⟪u a, u b⟫_𝕜 = ⟪a, b⟫_𝕜 := by
      have hg : ∀ w : ((LinearMap.ker u)ᗮ), ‖(u ∘ₗ ((LinearMap.ker u)ᗮ).subtype) w‖ = ‖w‖ := by
        intro w; simpa using h w.1 w.2
      intro a ha b hb
      have hmap := (LinearMap.norm_map_iff_inner_map_map
        (u ∘ₗ ((LinearMap.ker u)ᗮ).subtype)).mp hg ⟨a, ha⟩ ⟨b, hb⟩
      simpa using hmap
    ext x
    have hq : u.adjoint (u x) ∈ (LinearMap.ker u)ᗮ := by
      rw [LinearMap.orthogonal_ker]; exact LinearMap.mem_range_self _ _
    set P := ((LinearMap.ker u)ᗮ).starProjection with hP
    have hPx : P x ∈ (LinearMap.ker u)ᗮ := Submodule.starProjection_apply_mem _ _
    have hux : u x = u (P x) := by
      have hmem0 : x - P x ∈ LinearMap.ker u := by
        have h1 : x - P x ∈ ((LinearMap.ker u)ᗮ)ᗮ := by
          rw [hP]; exact Submodule.sub_starProjection_mem_orthogonal x
        rwa [Submodule.orthogonal_orthogonal] at h1
      rw [LinearMap.mem_ker, map_sub, sub_eq_zero] at hmem0
      exact hmem0
    have hqP : u.adjoint (u x) = P x := by
      have hmem : u.adjoint (u x) - P x ∈ (LinearMap.ker u)ᗮ := Submodule.sub_mem _ hq hPx
      set w := u.adjoint (u x) - P x with hw
      have hzero : ⟪w, w⟫_𝕜 = 0 := by
        have e1 : ⟪u.adjoint (u x), w⟫_𝕜 = ⟪P x, w⟫_𝕜 := by
          rw [LinearMap.adjoint_inner_left, hux, hinner (P x) hPx w hmem]
        calc ⟪w, w⟫_𝕜 = ⟪u.adjoint (u x), w⟫_𝕜 - ⟪P x, w⟫_𝕜 := by rw [hw, inner_sub_left]
          _ = 0 := by rw [e1, sub_self]
      have hw0 := inner_self_eq_zero.mp hzero
      rw [hw, sub_eq_zero] at hw0
      exact hw0
    simp only [LinearMap.comp_apply, hqP]
    exact hux.symm

/-- Partial isometries are closed under adjoint, in the rectangular setting.

The rectangular counterpart of `IsPartialIsometry.star_star`, and it cannot be obtained
from that lemma: `u.adjoint` lives in `F →ₗ[𝕜] E`, a different space from `u`.  Taking
adjoints through `u ∘ₗ u.adjoint ∘ₗ u = u` reverses the composition and
`LinearMap.adjoint_adjoint` collapses the double adjoint, which lands exactly on the
statement. -/
theorem IsPartialIsometry.adjoint {u : E →ₗ[𝕜] F} (hu : u.IsPartialIsometry) :
    u.adjoint.IsPartialIsometry := by
  have h := congrArg LinearMap.adjoint hu
  unfold LinearMap.IsPartialIsometry
  simpa only [LinearMap.adjoint_comp, LinearMap.adjoint_adjoint, LinearMap.comp_assoc] using h

end LinearMap

namespace ContinuousLinearMap

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

/-- **Partial isometry between possibly different spaces**, bounded form:
`u ∘L u.adjoint ∘L u = u`.

The same typed equation as `LinearMap.IsPartialIsometry`, stated on the bounded carrier so
that consumers on complete spaces -- the rectangular polar decomposition in particular --
never leave `→L`.  A rectangular map is not an element of one monoid, so the star-monoid
predicate `u * star u * u = u` is unavailable here. -/
@[expose]
def IsPartialIsometry (u : E →L[𝕜] F) : Prop :=
  u ∘L u.adjoint ∘L u = u

/-- The adjoint of a partial isometry is a partial isometry. -/
theorem IsPartialIsometry.adjoint {u : E →L[𝕜] F} (hu : u.IsPartialIsometry) :
    u.adjoint.IsPartialIsometry := by
  have h := congrArg ContinuousLinearMap.adjoint hu
  unfold ContinuousLinearMap.IsPartialIsometry
  simpa only [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_adjoint,
    ← ContinuousLinearMap.comp_assoc] using h

end ContinuousLinearMap
