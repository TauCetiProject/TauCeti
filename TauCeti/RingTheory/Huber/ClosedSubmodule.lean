/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.DenseSubmodule
public import TauCeti.Topology.Algebra.Module.Noetherian
public import TauCeti.Topology.Algebra.IsUniformGroup.Submodule
public import Mathlib.Algebra.Exact.Basic
import Mathlib.Algebra.Module.FinitePresentation
import TauCeti.Topology.Algebra.Nonarchimedean.Pi

/-!
# Closed submodules and noetherianity over Tate rings

A submodule of a complete, metrisable module over a complete Tate ring whose topological closure
is module-finite is itself closed. This is Bosch–Güntzer–Remmert §3.7.2/1 in its closure form. It
gives the *only if* direction of Wedhorn's Proposition 6.17, that every submodule of a noetherian
module is closed; with the converse `TauCeti.isNoetherian_of_forall_isClosed`
this file proves Proposition 6.17 in both directions. Its consequence for a
noetherian ring — every submodule of a finitely generated module is closed — is what makes a finite
presentation of a finite module *strict*, which is the form in which Wedhorn's Remark 8.29 consumes
Proposition 6.18(2).

The proof is one application of `TauCeti.Huber.eq_top_of_dense_of_module_finite`, made inside the
closure `N.topologicalClosure` rather than inside the ambient module. That closure is closed in a
complete space, so it is complete — the one instance that has to be supplied by hand; it is a
uniform additive group with a countably generated uniformity by `Submodule.isUniformAddGroup` and
`Submodule.isCountablyGenerated_uniformity`; and it is module-finite by hypothesis. Inside that
closure the submodule `N` is dense, by the very definition of the closure. So `N` is everything in
the closure, that is `N.topologicalClosure = N`, and `N` is closed because its closure is.

## Main results

* `TauCeti.Huber.isClosed_of_module_finite_topologicalClosure`: a submodule whose topological
  closure is module-finite is closed.
* `TauCeti.Huber.isClosed_of_isNoetherian`: in a noetherian module, *every* submodule is closed.
* `TauCeti.Huber.isNoetherian_iff_forall_isClosed` and
  `TauCeti.Huber.isNoetherianRing_iff_forall_isClosed`: Wedhorn's Proposition 6.17, that a complete
  Hausdorff first-countable module over a complete Hausdorff Tate ring, and in particular the ring
  itself, is noetherian exactly when all of its submodules are closed. The converse direction is
  `TauCeti.isNoetherian_of_forall_isClosed`.
* `TauCeti.Huber.IsTateRing.exists_presentation_isStrictMap_isOpenMap`: over a complete
  noetherian Tate ring, a finite module with its module topology has a presentation
  `Aⁿ →[u] Aᵐ →[p] M → 0` with `u` strict and `p` open — Wedhorn's Remark 8.29's use of
  Proposition 6.18(2).

## References

* [Bosch, Güntzer, Remmert, *Non-Archimedean Analysis*][bosch-guntzer-remmert], §3.7.2/1.
* [Wedhorn, *Adic Spaces*][wedhorn_adic], Propositions 6.17–6.18 and Remark 8.29.

## Provenance

Adapted from the AINTLIB development (`github.com/CBirkbeck/AINTLIB`, Apache-2.0), branch
`dev/adic-spaces` at commit `37bbdaeb9ad9`, file
`projects/AdicSpaces/Adic spaces/WedhornBanachTheorem.lean`, where the same statement is
`fg_topologicalClosure_isClosed`. The argument is AINTLIB's, and the density step follows its
proof closely. Three things differ. AINTLIB establishes the uniform-group, countable-generation,
separation and `ContinuousSMul` instances on the closure by hand; here all four are found by
instance search — the first two from `Submodule.isUniformAddGroup` and
`Submodule.isCountablyGenerated_uniformity`, the last from this repository's `ContinuousSMul`
instance on a submodule — so only completeness is supplied. The engine is this repository's
`TauCeti.Huber.eq_top_of_dense_of_module_finite`, stated with `T0Space`, rather than AINTLIB's
`T2Space`-based `eq_top_of_dense_of_finite`. And the passage from `N' = ⊤` back to
`N.topologicalClosure ≤ N` is `Submodule.comap_subtype_eq_top` rather than AINTLIB's element-level
unfolding.

`TauCeti.Huber.isClosed_of_isNoetherian` follows the same development's
`_sub_lemma_L3_1b_fg_submodule_closed` (same file, line 778 at the commit above), which is where
the plan of discharging closedness from noetherianity is taken from. Only the plan is shared: that
proof concludes closedness from *completeness* of the finitely generated submodule, via its
`_sub_lemma_L3_1a_completion_fg_complete` and `completeSpace_coe_iff_isComplete`, whereas the proof
here routes through this file's own `isClosed_of_module_finite_topologicalClosure` and so never
mentions completeness of `N`. The hypotheses differ too: that statement asks for `[IsNoetherianRing
A]` together with an explicit `(hN_fg : N.FG)`, while `[IsNoetherian A V]` here covers every
submodule at once and needs no finite-generation argument at the call site. Sharing only the plan
is not a stylistic choice: that proof reaches completeness through
`_sub_lemma_L3_1a_completion_fg_complete`, whose body in that development is `sorry` (same file,
line 611), so its route is not available to import even in principle.
-/

open Filter Topology
open scoped Uniformity

public section

namespace TauCeti.Huber

variable {A : Type*} [CommRing A] [UniformSpace A] [IsUniformAddGroup A] [CompleteSpace A]
  [T2Space A] [IsTopologicalRing A] [IsTateRing A]
  {V : Type*} [AddCommGroup V] [UniformSpace V] [IsUniformAddGroup V] [CompleteSpace V]
  [(𝓤 V).IsCountablyGenerated] [T0Space V] [Module A V] [ContinuousSMul A V]

/-- **A submodule whose topological closure is module-finite is closed**
(Bosch–Güntzer–Remmert §3.7.2/1).

Working inside `N.topologicalClosure`, which is complete because it is closed in a complete space,
the submodule `N` is dense and that closure is module-finite, so
`eq_top_of_dense_of_module_finite` gives `N = N.topologicalClosure`. -/
theorem isClosed_of_module_finite_topologicalClosure (N : Submodule A V)
    (hfin : Module.Finite A N.topologicalClosure) : IsClosed (N : Set V) := by
  have hclosed : IsClosed (N.topologicalClosure : Set V) := N.isClosed_topologicalClosure
  have : CompleteSpace N.topologicalClosure := hclosed.completeSpace_coe
  -- `N` seen inside its own closure, where it is dense.
  set N' : Submodule A N.topologicalClosure := N.comap N.topologicalClosure.subtype
  have himg : Subtype.val '' (N' : Set N.topologicalClosure) = (N : Set V) := by
    ext z
    exact ⟨fun ⟨⟨_, _⟩, hw, hwz⟩ ↦ hwz ▸ hw, fun hz ↦ ⟨⟨z, N.le_topologicalClosure hz⟩, hz, rfl⟩⟩
  have hdense : Dense (N' : Set N.topologicalClosure) := fun x ↦ by
    rw [closure_subtype, himg, ← N.topologicalClosure_coe]
    exact x.2
  -- `N' = ⊤` inside the closure says exactly that the closure is contained in `N`.
  have hle : N.topologicalClosure ≤ N :=
    Submodule.comap_subtype_eq_top.mp (eq_top_of_dense_of_module_finite N' hdense)
  exact le_antisymm hle N.le_topologicalClosure ▸ hclosed

/-- **In a noetherian module, every submodule is closed.**

Every submodule of a noetherian module is finitely generated — the topological closure of `N`
included. That closure is therefore module-finite, which is exactly what
`TauCeti.Huber.isClosed_of_module_finite_topologicalClosure` asks of it.

The hypothesis is on the module and not on the ring, because that is all the argument uses: the
noetherian-base, module-finite case is recovered from Mathlib's instance
`isNoetherian_of_isNoetherianRing_of_finite`, so no separate statement of it is needed.

This is the *only if* direction of [Wedhorn, *Adic Spaces*][wedhorn_adic], Proposition 6.17; the
equivalence is `TauCeti.Huber.isNoetherian_iff_forall_isClosed`. -/
theorem isClosed_of_isNoetherian [IsNoetherian A V] (N : Submodule A V) :
    IsClosed (N : Set V) :=
  isClosed_of_module_finite_topologicalClosure N <|
    Module.Finite.iff_fg.mpr (IsNoetherian.noetherian _)

/-- **A complete Hausdorff first-countable module over a complete Hausdorff Tate ring is noetherian
if and only if all of its submodules are closed** ([Wedhorn, *Adic Spaces*][wedhorn_adic],
Proposition 6.17). The forward direction is `TauCeti.Huber.isClosed_of_isNoetherian`; the converse,
a Baire category argument, is `TauCeti.isNoetherian_of_forall_isClosed`. -/
theorem isNoetherian_iff_forall_isClosed :
    IsNoetherian A V ↔ ∀ N : Submodule A V, IsClosed (N : Set V) :=
  ⟨fun _ ↦ isClosed_of_isNoetherian, TauCeti.isNoetherian_of_forall_isClosed⟩

/-- **A complete Hausdorff Tate ring is noetherian if and only if all of its ideals are closed**
([Wedhorn, *Adic Spaces*][wedhorn_adic], Proposition 6.17, the case of the ring itself). -/
theorem isNoetherianRing_iff_forall_isClosed :
    IsNoetherianRing A ↔ ∀ I : Ideal A, IsClosed (I : Set A) :=
  have : (𝓤 A).IsCountablyGenerated := IsUniformAddGroup.uniformity_countably_generated
  isNoetherian_iff_forall_isClosed

section ModuleFinite

variable {A : Type*} [CommRing A] [UniformSpace A] [IsUniformAddGroup A] [CompleteSpace A]
  [(𝓤 A).IsCountablyGenerated] [T0Space A] [NonarchimedeanRing A] [IsTateRing A]
  [IsNoetherianRing A]
  {M : Type*} [AddCommGroup M] [Module A M] [Module.Finite A M] [TopologicalSpace M]
  [IsModuleTopology A M]

/-- **A finite module over a complete noetherian Tate ring has a strict finite presentation.**
This is the sentence Wedhorn's Remark 8.29 opens with: "we find a presentation
`Aⁿ →[u] Aᵐ →[p] M → 0` (because `A` is noetherian). Proposition 6.18(2) shows that `u` and `p`
are continuous and open onto its image."

`M` carries its canonical topology, which is Mathlib's module topology: every complete
first-countable module topology on a finite module is the module topology
(`TauCeti.Huber.IsTateRing.isModuleTopology`), so `IsModuleTopology A M` is the topology
Proposition 6.18(1) speaks of, and nothing else is asked of `M`. The presentation is Mathlib's
`Module.FinitePresentation.exists_fin'`, available because a finite module over a noetherian ring
is finitely presented. Both maps are continuous by `IsModuleTopology.continuous_of_linearMap`,
`p` is open by `IsModuleTopology.isOpenMap_of_surjective` — the module topology on `M` is the
quotient topology along any linear surjection from `Aᵐ` — and `u` is strict by
`TauCeti.Huber.IsTateRing.isStrictMap_of_isClosed_range`, its range being closed in `Aᵐ` by
`TauCeti.Huber.isClosed_of_isNoetherian`. That closedness is the one place, beyond the existence
of the presentation, where `A` being noetherian enters, and the open mapping theorem is spent on
the free module `Aᵐ`, not on `M`. -/
theorem IsTateRing.exists_presentation_isStrictMap_isOpenMap :
    ∃ (n m : ℕ) (u : (Fin n → A) →ₗ[A] (Fin m → A)) (p : (Fin m → A) →ₗ[A] M),
      Continuous u ∧ Continuous p ∧ Function.Surjective p ∧ Function.Exact u p ∧
        Topology.IsStrictMap u ∧ IsOpenMap p := by
  have := Module.finitePresentation_of_finite A M
  have := IsModuleTopology.toContinuousAdd A M
  obtain ⟨m, n, p, u, hsurj, hexact⟩ := Module.FinitePresentation.exists_fin' A M
  have hu : Continuous u := IsModuleTopology.continuous_of_linearMap u
  exact ⟨n, m, u, p, hu, IsModuleTopology.continuous_of_linearMap p, hsurj, hexact,
    IsTateRing.isStrictMap_of_isClosed_range u hu.continuousAt (isClosed_of_isNoetherian _),
    IsModuleTopology.isOpenMap_of_surjective hsurj⟩

end ModuleFinite

end TauCeti.Huber
