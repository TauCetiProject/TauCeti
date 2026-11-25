/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RepresentationTheory.Basic
public import TauCeti.RepresentationTheory.Irreducible

/-!
# Multiplicities and admissible representations

For a representation `ρ` of a monoid `G` on a vector space `V` over a field `k`, the multiplicity
of a representation `σ` in `ρ` is the dimension of `Hom_G(σ, ρ)`, and `ρ` has finite
multiplicities when `Hom_G(σ, ρ)` is finite-dimensional for every irreducible `σ`. These are the
notions used for the `K`-action of a `(𝔤, K)`-module
(`TauCeti/RepresentationTheory/GKModule/Basic.lean`), where `K` is a maximal compact subgroup of a
real reductive group: such a module is *admissible* when its `K`-action has finite multiplicities.
This is not the admissibility of smooth representations of topological groups,
`Representation.IsAdmissible` (`TauCeti/RepresentationTheory/Smooth/Admissible.lean`), which asks
for finitely generated invariants under compact open subgroups.

## Main definitions

* `Representation.multiplicity ρ σ`: the dimension of `Hom_G(σ, ρ)` in `ℕ∞`, equal to `⊤` when it
  is infinite.
* `Representation.HasFiniteMultiplicities ρ`: `Hom_G(σ, ρ)` is finite-dimensional for every
  irreducible `σ`.

## Main statements

* `Representation.HasFiniteMultiplicities.finiteDimensional`: in a representation with finite
  multiplicities, `Hom_G(σ, ρ)` is finite-dimensional for every irreducible `σ`, in any universe.
* `Representation.HasFiniteMultiplicities.subrepresentation`,
  `Representation.HasFiniteMultiplicities.directSum`: finite multiplicities pass to
  subrepresentations and to finite direct sums.
* `Representation.hasFiniteMultiplicities_of_finiteDimensional`: a finite-dimensional
  representation has finite multiplicities.

## Implementation notes

For irreducible `σ` with `Hom_G(σ, ρ)` finite-dimensional, when `k` is not algebraically closed
the multiplicity is the number of copies of `σ` in the `σ`-isotypic component multiplied by the
dimension of the division algebra `End_G(σ)`. The predicate is quantified over the irreducible
subrepresentations of `V`, which avoids fixing a universe for `σ`: an irreducible representation
with a nonzero map to `V` is isomorphic to its image.

## References

* J. Bernstein and B. Krötz, *Smooth Fréchet globalizations of Harish-Chandra modules*, Israel J.
  Math. 199 (2014), 45–111, §4.1.
-/

public section

namespace Representation

universe v w

variable {k G V W : Type*} [Field k] [Monoid G] [AddCommGroup V] [Module k V] [AddCommGroup W]
  [Module k W] (ρ : Representation k G V) (σ : Representation k G W)

/-- The **multiplicity** of `σ` in `ρ`: the dimension of `Hom_G(σ, ρ)`, as an element of `ℕ∞`,
which is `⊤` when `Hom_G(σ, ρ)` is infinite-dimensional. -/
noncomputable def multiplicity : ℕ∞ :=
  (Module.rank k (IntertwiningMap σ ρ)).toENat

theorem multiplicity_def : ρ.multiplicity σ = (Module.rank k (IntertwiningMap σ ρ)).toENat :=
  (rfl)

/-- When `Hom_G(σ, ρ)` is finite-dimensional, the multiplicity is its `finrank`. -/
theorem multiplicity_eq_finrank [FiniteDimensional k (IntertwiningMap σ ρ)] :
    ρ.multiplicity σ = Module.finrank k (IntertwiningMap σ ρ) := by
  rw [multiplicity_def, ← Module.finrank_eq_rank, Cardinal.toENat_nat]

/-- The multiplicity is finite exactly when `Hom_G(σ, ρ)` is finite-dimensional. -/
theorem multiplicity_lt_top_iff :
    ρ.multiplicity σ < ⊤ ↔ FiniteDimensional k (IntertwiningMap σ ρ) := by
  rw [multiplicity_def, Cardinal.toENat_lt_top, Module.rank_lt_aleph0_iff]

/-- A representation **has finite multiplicities** when `Hom_G(σ, ρ)` is finite-dimensional for
every irreducible representation `σ` of `G`; for the `K`-action of a `(𝔤, K)`-module this is
admissibility. Only an irreducible `σ` with a nonzero map to `V` can violate this, and such a `σ`
is isomorphic to its image, so the definition quantifies over the irreducible subrepresentations
of `ρ`; `Representation.HasFiniteMultiplicities.finiteDimensional` gives the statement for every
irreducible `σ`, in any universe. -/
def HasFiniteMultiplicities : Prop :=
  ∀ U : Subrepresentation ρ, U.toRepresentation.IsIrreducible →
    FiniteDimensional k (IntertwiningMap U.toRepresentation ρ)

theorem hasFiniteMultiplicities_iff :
    ρ.HasFiniteMultiplicities ↔ ∀ U : Subrepresentation ρ, U.toRepresentation.IsIrreducible →
      FiniteDimensional k (IntertwiningMap U.toRepresentation ρ) :=
  Iff.rfl

namespace HasFiniteMultiplicities

variable {ρ}

/-- In a representation `ρ` with finite multiplicities, `Hom_G(σ, ρ)` is finite-dimensional for
every irreducible `σ`. -/
theorem finiteDimensional (hρ : ρ.HasFiniteMultiplicities) {W : Type w} [AddCommGroup W]
    [Module k W] (σ : Representation k G W) [hσ : σ.IsIrreducible] :
    FiniteDimensional k (IntertwiningMap σ ρ) := by
  by_cases h : ∃ f : IntertwiningMap σ ρ, f ≠ 0
  swap
  · push Not at h
    have : Subsingleton (IntertwiningMap σ ρ) := ⟨fun f f' ↦ (h f).trans (h f').symm⟩
    infer_instance
  obtain ⟨f, hf⟩ := h
  have hinj : Function.Injective f := (IsIrreducible.injective_or_eq_zero f).resolve_right hf
  let e := f.equivOfRange hinj (P := f.range) rfl
  have := hρ f.range (e.isIrreducible hσ)
  exact (e.intertwiningMapCongr (Representation.Equiv.refl ρ)).symm.finiteDimensional

/-- A representation on `V` in which `Hom_G(σ, ρ)` is finite-dimensional for every irreducible
`σ` on a carrier in the universe of `V` has finite multiplicities. -/
theorem of_forall {V : Type v} [AddCommGroup V] [Module k V] {ρ : Representation k G V}
    (h : ∀ (W : Type v) [AddCommGroup W] [Module k W] (σ : Representation k G W),
      σ.IsIrreducible → FiniteDimensional k (IntertwiningMap σ ρ)) :
    ρ.HasFiniteMultiplicities := fun U hU ↦ h U.toSubmodule U.toRepresentation hU

/-- A subrepresentation of a representation with finite multiplicities has finite
multiplicities. -/
theorem subrepresentation (hρ : ρ.HasFiniteMultiplicities) (N : Subrepresentation ρ) :
    N.toRepresentation.HasFiniteMultiplicities := by
  intro U hU
  have := hρ.finiteDimensional U.toRepresentation
  refine Module.Finite.of_injective
    (IntertwiningMap.llcomp U.toRepresentation _ _ N.subtype) fun f f' h ↦ ?_
  ext w
  have h' : N.subtype (f w) = N.subtype (f' w) := congr($h w)
  simpa using h'

/-- A finite direct sum of representations with finite multiplicities has finite
multiplicities. -/
theorem directSum {ι : Type*} [Finite ι] {V : ι → Type*} [∀ i, AddCommGroup (V i)]
    [∀ i, Module k (V i)] {ρ : ∀ i, Representation k G (V i)}
    (hρ : ∀ i, (ρ i).HasFiniteMultiplicities) :
    (Representation.directSum ρ).HasFiniteMultiplicities := by
  intro U hU
  have := fun i ↦ (hρ i).finiteDimensional U.toRepresentation
  let c : IntertwiningMap U.toRepresentation (Representation.directSum ρ) →ₗ[k]
      ∀ i, IntertwiningMap U.toRepresentation (ρ i) :=
    { toFun f i :=
        ⟨(DirectSum.component k ι V i).comp f.toLinearMap, fun g ↦ by
          ext w
          simp only [LinearMap.comp_apply, IntertwiningMap.toLinearMap_apply,
            IntertwiningMap.isIntertwining, ← DirectSum.apply_eq_component,
            Representation.directSum_apply, DirectSum.lmap_apply]⟩
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }
  refine Module.Finite.of_injective c fun f f' h ↦ ?_
  ext w i
  exact congr($h i w)

end HasFiniteMultiplicities

/-- A finite-dimensional representation has finite multiplicities. -/
theorem hasFiniteMultiplicities_of_finiteDimensional [FiniteDimensional k V] :
    ρ.HasFiniteMultiplicities :=
  fun _ _ ↦ inferInstance

end Representation
