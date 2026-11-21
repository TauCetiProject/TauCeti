/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.Flat.Basic
public import TauCeti.Topology.Algebra.Module.Compact.Adic
import Mathlib.RingTheory.Flat.TorsionFree
import TauCeti.RingTheory.Flat.Pi

/-!
# Profinite flat modules

A topological module `M` over a commutative topological ring `R` is *profinite flat*
(`TauCeti.IsProfiniteFlat`) if it is a compact module (`TauCeti.IsCompactModule R M`) and
algebraically flat over `R` (`Module.Flat R M`). Over a Dedekind domain, profinite flatness is
equivalent to `IsCompactModule` plus torsion-freeness
(`TauCeti.isProfiniteFlat_iff_isCompactModule_and_isTorsionFree`) and passes to closed submodules
and arbitrary products (`TauCeti.IsProfiniteFlat.submodule`, `TauCeti.IsProfiniteFlat.pi`).

## References

* [P. Chojecki, D. Hansen, C. Johansson, *Overconvergent modular forms and perfectoid Shimura
  curves*], Doc. Math. 22 (2017), 191–262 (`arXiv:1507.04875v2`, §6.1, Definition 6.1).
-/

public section

namespace TauCeti

/-- A topological `R`-module `M` over a commutative ring `R` is *profinite flat* if it is a compact
module (`IsCompactModule R M`) and flat over `R` (`Module.Flat R M`). -/
structure IsProfiniteFlat (R M : Type*) [CommRing R] [TopologicalSpace R]
    [AddCommGroup M] [Module R M] [TopologicalSpace M] : Prop extends IsCompactModule R M where
  /-- The underlying `R`-module is flat. -/
  flat : Module.Flat R M

@[grind =]
theorem isProfiniteFlat_iff {R M : Type*} [CommRing R] [TopologicalSpace R]
    [AddCommGroup M] [Module R M] [TopologicalSpace M] :
    IsProfiniteFlat R M ↔ IsCompactModule R M ∧ Module.Flat R M :=
  ⟨fun h ↦ ⟨h.toIsCompactModule, h.flat⟩, fun ⟨h₁, h₂⟩ ↦ ⟨h₁, h₂⟩⟩

end TauCeti

namespace ContinuousLinearEquiv

variable {R M N : Type*} [CommRing R] [TopologicalSpace R]
  [AddCommGroup M] [Module R M] [TopologicalSpace M]
  [AddCommGroup N] [Module R N] [TopologicalSpace N]

/-- A continuous linear equivalence preserves `TauCeti.IsProfiniteFlat`. -/
theorem isProfiniteFlat_iff (e : M ≃L[R] N) :
    TauCeti.IsProfiniteFlat R M ↔ TauCeti.IsProfiniteFlat R N := by
  simp only [TauCeti.isProfiniteFlat_iff]
  exact and_congr e.isCompactModule_iff (Module.Flat.equiv_iff e.toLinearEquiv)

end ContinuousLinearEquiv

namespace TauCeti.IsProfiniteFlat

section CommRing

variable {R M : Type*} [CommRing R] [TopologicalSpace R]
  [AddCommGroup M] [Module R M] [TopologicalSpace M]

/-- Every profinite flat module is torsion-free over `R`. -/
theorem isTorsionFree (hM : IsProfiniteFlat R M) : Module.IsTorsionFree R M :=
  have := hM.flat; inferInstance

/-- A compact, totally disconnected commutative topological ring is profinite flat over itself. -/
theorem self [IsTopologicalRing R] [CompactSpace R] [TotallyDisconnectedSpace R] :
    IsProfiniteFlat R R :=
  ⟨.self, inferInstance⟩

/-- A compact Hausdorff commutative ring whose topology is `I`-adic is profinite flat over
itself. -/
theorem self_of_isAdic [CompactSpace R] [T2Space R] {I : Ideal R} (hI : IsAdic I) :
    IsProfiniteFlat R R :=
  ⟨.self_of_isAdic hI, inferInstance⟩

/-- Any subsingleton topological `R`-module is profinite flat. -/
theorem of_subsingleton [Subsingleton M] : IsProfiniteFlat R M :=
  ⟨.of_subsingleton, inferInstance⟩

/-- Binary products of profinite flat modules are profinite flat. -/
theorem prod {N : Type*} [AddCommGroup N] [Module R N] [TopologicalSpace N]
    (hM : IsProfiniteFlat R M) (hN : IsProfiniteFlat R N) :
    IsProfiniteFlat R (M × N) :=
  have := hM.flat; have := hN.flat
  ⟨hM.toIsCompactModule.prod hN.toIsCompactModule, inferInstance⟩

/-- Finite products of profinite flat modules over any commutative ring are profinite flat. -/
theorem pi_of_finite {ι : Type*} [Finite ι] {P : ι → Type*} [∀ i, AddCommGroup (P i)]
    [∀ i, Module R (P i)] [∀ i, TopologicalSpace (P i)] (hP : ∀ i, IsProfiniteFlat R (P i)) :
    IsProfiniteFlat R (∀ i, P i) :=
  have := fun i ↦ (hP i).flat
  ⟨IsCompactModule.pi fun i ↦ (hP i).toIsCompactModule, inferInstance⟩

/-- Transport `IsProfiniteFlat` along a continuous linear equivalence. -/
theorem of_continuousLinearEquiv {N : Type*} [AddCommGroup N] [Module R N] [TopologicalSpace N]
    (hM : IsProfiniteFlat R M) (e : M ≃L[R] N) : IsProfiniteFlat R N :=
  e.isProfiniteFlat_iff.mp hM

end CommRing

section DedekindDomain

variable {R M : Type*} [CommRing R] [IsDedekindDomain R] [TopologicalSpace R]
  [AddCommGroup M] [Module R M] [TopologicalSpace M]

/-- Over a Dedekind domain, a topological module is profinite flat if and only if it is a compact
module and torsion-free. -/
theorem _root_.TauCeti.isProfiniteFlat_iff_isCompactModule_and_isTorsionFree :
    IsProfiniteFlat R M ↔ IsCompactModule R M ∧ Module.IsTorsionFree R M :=
  ⟨fun h ↦ ⟨h.toIsCompactModule, h.isTorsionFree⟩,
    fun ⟨hc, _⟩ ↦ ⟨hc, inferInstance⟩⟩

/-- Over a Dedekind domain, a closed submodule of a profinite flat module is profinite flat. -/
theorem submodule (hM : IsProfiniteFlat R M) (N : Submodule R M) (hN : IsClosed (N : Set M)) :
    IsProfiniteFlat R N :=
  have := hM.isTorsionFree; ⟨hM.toIsCompactModule.submodule N hN, inferInstance⟩

/-- Over a Dedekind domain, an arbitrary product of profinite flat modules is profinite flat. -/
theorem pi {ι : Type*} {P : ι → Type*} [∀ i, AddCommGroup (P i)] [∀ i, Module R (P i)]
    [∀ i, TopologicalSpace (P i)] (hP : ∀ i, IsProfiniteFlat R (P i)) :
    IsProfiniteFlat R (∀ i, P i) :=
  have := fun i ↦ (hP i).isTorsionFree
  ⟨IsCompactModule.pi fun i ↦ (hP i).toIsCompactModule, inferInstance⟩

/-- Over a compact totally disconnected Dedekind domain, every product `I → R` is profinite flat. -/
theorem pi_self [IsTopologicalRing R] [CompactSpace R] [TotallyDisconnectedSpace R] (I : Type*) :
    IsProfiniteFlat R (I → R) :=
  pi fun _ : I ↦ self

end DedekindDomain

end TauCeti.IsProfiniteFlat
