/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Restrict
public import Mathlib.Topology.ContinuousMap.Algebra

/-!
# Continuous maps from a compact space into a localized module

Let `R` be a commutative ring, `S ⊆ R` a submonoid and `V` a topological `R`-module on which
each scalar acts continuously. Let `T` be an open submodule of `V` absorbing `V` along `S`: every
`v` has some `s ∈ S` with `s • v ∈ T`. The sets `{v | s • v ∈ T}` for `s ∈ S` form an open cover
of `V`, directed because `T` is a submodule, so a compact subset of `V` lies in one of them. Hence
every continuous map `f : X → V` from a compact space satisfies `s • f x ∈ T` for one `s ∈ S` and
all `x`.

When `V` is moreover a module over a localization `K` of `R` at `S`, compatibly with `R`, this
says that `C(X, V)` is the localization of `C(X, T)` at `S`, so `C(X, V) = K ⊗[R] C(X, T)`.
For `T` a finite free `ℤ_p`-module and `V = T ⊗ ℚ_p` this is the statement
`C(X, V) = C(X, T) ⊗ ℚ_p` of continuous cochains (Rubin, *Euler Systems*, Appendix B, §2,
Proposition 2.4); the `p`-adic case is in `TauCeti.NumberTheory.Padics.ContinuousMapLattice`.

## Main results

* `TauCeti.exists_smul_mem_of_isCompact`: a compact subset of `V` lies in `s⁻¹ T` for one
  `s ∈ S`.
* `TauCeti.exists_smul_apply_mem_of_compactSpace`: so does the range of a continuous map from a
  compact space.
* `TauCeti.isLocalizedModule_compLeftContinuous_subtypeL`: `C(X, T) → C(X, V)` is
  a localization at `S`.
* `TauCeti.isBaseChange_compLeftContinuous_subtypeL`: `C(X, T) → C(X, V)` is the
  base change to `K`.
-/

public section

namespace TauCeti

section Compact

variable {R V : Type*} [CommSemiring R] [AddCommMonoid V] [Module R V] [TopologicalSpace V]
  [ContinuousConstSMul R V] (S : Submonoid R) (T : Submodule R V)

/-- If an open submodule `T` absorbs `V` along a submonoid `S`, a compact subset of `V` lies in
`s⁻¹ T` for a single `s ∈ S`. -/
theorem exists_smul_mem_of_isCompact (hT : IsOpen (T : Set V)) (habs : ∀ v, ∃ s ∈ S, s • v ∈ T)
    {C : Set V} (hC : IsCompact C) : ∃ s ∈ S, ∀ v ∈ C, s • v ∈ T := by
  obtain ⟨s, hs⟩ := hC.elim_directed_cover (ι := S) (fun s ↦ (fun v ↦ (s : R) • v) ⁻¹' T)
    (fun s ↦ hT.preimage (continuous_const_smul _))
    (fun v _ ↦ by obtain ⟨s, hs, hv⟩ := habs v; exact Set.mem_iUnion.2 ⟨⟨s, hs⟩, hv⟩)
    (fun s t ↦ ⟨t * s, fun v hv ↦ by simpa [mul_smul] using T.smul_mem (t : R) hv,
      fun v hv ↦ by simpa [mul_comm (t : R), mul_smul] using T.smul_mem (s : R) hv⟩)
  exact ⟨s, s.property, fun v hv ↦ hs hv⟩

variable {X : Type*} [TopologicalSpace X] [CompactSpace X]

/-- If an open submodule `T` absorbs `V` along `S`, every continuous map from a compact space
into `V` lands in `s⁻¹ T` for a single `s ∈ S`. -/
theorem exists_smul_apply_mem_of_compactSpace (hT : IsOpen (T : Set V))
    (habs : ∀ v, ∃ s ∈ S, s • v ∈ T) (f : C(X, V)) : ∃ s ∈ S, ∀ x, s • f x ∈ T := by
  obtain ⟨s, hs, h⟩ := exists_smul_mem_of_isCompact S T hT habs (isCompact_range f.continuous)
  exact ⟨s, hs, fun x ↦ h _ ⟨x, rfl⟩⟩

end Compact

section Localization

variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V] [TopologicalSpace V]
  [IsTopologicalAddGroup V] [ContinuousConstSMul R V] (S : Submonoid R) (T : Submodule R V)
  {X : Type*} [TopologicalSpace X] [CompactSpace X]
  (K : Type*) [CommRing K] [Algebra R K] [IsLocalization S K]
  [Module K V] [IsScalarTower R K V] [ContinuousConstSMul K V]

include K in
/-- If an open submodule `T` absorbs `V` along `S` and `V` is a module over the localization `K`
of `R` at `S`, then for compact `X` the inclusion `C(X, T) → C(X, V)` is a localization at
`S`. -/
theorem isLocalizedModule_compLeftContinuous_subtypeL (hT : IsOpen (T : Set V))
    (habs : ∀ v, ∃ s ∈ S, s • v ∈ T) :
    IsLocalizedModule S (T.subtypeL.compLeftContinuous R X : C(X, T) →ₗ[R] C(X, V)) where
  map_units s := by
    rw [← (Algebra.lsmul R (A := K) R C(X, V)).commutes]
    exact (IsLocalization.map_units K s).map _
  surj g := by
    obtain ⟨s, hs, h⟩ := exists_smul_apply_mem_of_compactSpace S T hT habs g
    exact ⟨(⟨fun x ↦ ⟨s • g x, h x⟩, (g.continuous.const_smul s).subtype_mk _⟩, ⟨s, hs⟩),
      by ext x; simp⟩
  exists_of_eq {f₁ f₂} h := ⟨1, by
    ext x
    simpa using congr($h x)⟩

/-- If an open submodule `T` absorbs `V` along `S` and `V` is a module over the localization `K`
of `R` at `S`, then for compact `X` the inclusion `C(X, T) → C(X, V)` identifies `C(X, V)` with
`K ⊗[R] C(X, T)`. -/
theorem isBaseChange_compLeftContinuous_subtypeL (hT : IsOpen (T : Set V))
    (habs : ∀ v, ∃ s ∈ S, s • v ∈ T) :
    IsBaseChange K (T.subtypeL.compLeftContinuous R X : C(X, T) →ₗ[R] C(X, V)) :=
  haveI := isLocalizedModule_compLeftContinuous_subtypeL (X := X) S T K hT habs
  IsLocalizedModule.isBaseChange S K _

end Localization

end TauCeti
