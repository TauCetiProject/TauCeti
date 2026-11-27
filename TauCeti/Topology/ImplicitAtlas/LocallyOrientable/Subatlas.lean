/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.ImplicitAtlas.LocallyOrientable.Basic
public import TauCeti.Topology.ImplicitAtlas.Subatlas

/-!
# Local orientability of relabelled atlases and subatlases

Local orientability of an implicit atlas (`TauCeti.ImplicitAtlas.IsLocallyOrientable`) is a
condition at the regular zeros of each thickening `X_I` separately: every element of `Γ_I` fixing
such a point `x` acts on the local orientation line `o_x` by the sign of its determinant on the
obstruction space `E_I`. The relabelling `𝒜.relabel f h` of an atlas along an embedding
`f : A' ↪ A` of index sets has, at a finite `I ⊆ A'`, the thickening `X_(f I)`, the regular locus
`X_(f I)^reg`, the same zero set, and the group `∏_(α ∈ I) Γ_(f α)` acting through the relabelling
isomorphism onto `Γ_(f I)`; its obstruction space `∏_(α ∈ I) E_(f α)` is `E_(f I)` relabelled,
on which an element acts with the same determinant. So the condition for the relabelled atlas at
`I` is the condition for `𝒜` at `f I`, and local orientability passes to relabellings
(`TauCeti.ImplicitAtlas.IsLocallyOrientable.relabel`) and in particular to subatlases
(`TauCeti.ImplicitAtlas.IsLocallyOrientable.restrict`), such as the finite subatlases of an atlas
on a compact space (`TauCeti.ImplicitAtlas.exists_finset_iUnion_footprint_eq_univ`). The virtual
cochain complex and the virtual fundamental class of a compact locally orientable atlas are built
from a finite subatlas (Pardon, Definition 5.1.1), and comparing two finite subatlases compares
two locally orientable atlases; both uses need the subatlases to be locally orientable.

A subatlas only constrains the thickenings `X_I` with `I` inside its index set, so its local
orientability says nothing about the regular zeros of the other thickenings.

## Main results

* `TauCeti.ImplicitAtlas.IsLocallyOrientable.relabel`: the relabelling of a locally orientable
  atlas along an embedding of index sets is locally orientable.
* `TauCeti.ImplicitAtlas.IsLocallyOrientable.restrict`: a subatlas of a locally orientable atlas is
  locally orientable.

## References

* J. Pardon, *An algebraic approach to virtual fundamental cycles on moduli spaces of
  pseudo-holomorphic curves*, Geom. Topol. 20 (2016), 779–1034, Definition 4.1.2 (locally
  orientable implicit atlases), Definition 5.1.1 (the virtual fundamental class) and Lemma 5.2.3
  (local orientability of subatlases).
-/

public section

open Set
open Finset hiding range

universe w

namespace TauCeti.ImplicitAtlas

variable {A A' : Type*} [DecidableEq A] [DecidableEq A'] {Γ : A → Type*} [∀ α, Group (Γ α)]
  [∀ α, Finite (Γ α)] {E : A → Type*} [∀ α, NormedAddCommGroup (E α)] [∀ α, NormedSpace ℝ (E α)]
  [∀ α, FiniteDimensional ℝ (E α)] {ρ : ∀ α, Representation ℝ (Γ α) (E α)}
  {T : Finset A → Type w} [∀ I, TopologicalSpace (T I)] [∀ I, T2Space (T I)]
  {act : ∀ I : Finset A, ((α : I) → Γ α) →* (T I ≃ₜ T I)}
  {X : Type*} [TopologicalSpace X] {d : ℤ} {𝒜 : ImplicitAtlas Γ E ρ T act X d}

/-- **Local orientability of relabelled atlases.** The relabelling of a locally orientable implicit
atlas along an embedding `f : A' ↪ A` of index sets is locally orientable: its condition at a
finite `I ⊆ A'` is the condition for `𝒜` at `f I`. -/
theorem IsLocallyOrientable.relabel (h : 𝒜.IsLocallyOrientable) (f : A' ↪ A)
    (hf : ⋃ I : Finset A', 𝒜.footprint (I.map f) = univ) :
    (𝒜.relabel f hf).IsLocallyOrientable := by
  refine isLocallyOrientable_iff.2 fun I x hx hx₀ g hg n hn ↦ ?_
  -- The element `g` acts on `X_(f I)` as its relabelling in `Γ_(f I)`, with the same
  -- determinant on the relabelled obstruction space.
  have hdet : LinearMap.det (Representation.externalPi (fun α : I ↦ ρ (f α)) g) =
      LinearMap.det (Representation.externalPi (fun α : I.map f ↦ ρ α)
        (MulEquiv.piFinsetMap Γ f I g)) := by
    rw [Representation.det_externalPi, Representation.det_externalPi]
    refine Fintype.prod_equiv (I.equivMap f) _ _ fun α ↦ ?_
    have hα : I.equivMap f α = ⟨f α, mem_map_of_mem f α.property⟩ := Subtype.ext (by simp)
    rw [hα, MulEquiv.piFinsetMap_apply_mk]
  rw [regLocus_relabel] at hx
  have hg' : act (I.map f) (MulEquiv.piFinsetMap Γ f I g) x = x := by
    rwa [relabelAct_apply] at hg
  -- The map of local homology only depends on the homeomorphism, here given by two expressions.
  rw [localHomologyMap_congr _ (congrArg (fun φ : T (I.map f) ≃ₜ T (I.map f) ↦
    (φ : C(T (I.map f), T (I.map f)))) (relabelAct_apply f act I g)) _ n, hdet]
  exact h.localHomologyMap_eq (I := I.map f) hx
    ((𝒜.kuranishiZeroSet_relabel f hf ∅ I) ▸ hx₀) hg' (by rw [hn, sum_map])

/-- **Local orientability of subatlases.** A subatlas of a locally orientable implicit atlas, on a
set `S` of indices whose footprints cover, is locally orientable (Pardon, Lemma 5.2.3). -/
theorem IsLocallyOrientable.restrict (h : 𝒜.IsLocallyOrientable) (S : Set A)
    (hS : ⋃ (I : Finset A) (_ : (I : Set A) ⊆ S), 𝒜.footprint I = univ) :
    (𝒜.restrict S hS).IsLocallyOrientable := by
  have hS' : ⋃ I : Finset S, 𝒜.footprint (I.map (.subtype (· ∈ S))) = univ := by
    simpa only [footprint_restrict] using (𝒜.restrict S hS).iUnion_footprint
  rw [restrict_eq_relabel 𝒜 S hS hS']
  exact h.relabel _ hS'

end TauCeti.ImplicitAtlas
