/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RepresentationTheory.Intertwining
public import TauCeti.LinearAlgebra.Span.FiniteRange
public import TauCeti.RepresentationTheory.Subrepresentation

/-!
# `G`-finite vectors of a representation

A vector `v` of a representation `ρ` of a monoid `G` on a vector space `V` is **`G`-finite** when
its orbit `{ρ g v | g ∈ G}` spans a finite-dimensional subspace, equivalently when `v` lies in a
finite-dimensional subrepresentation. The `G`-finite vectors form a submodule
`Representation.gFiniteSubmodule ρ`, which is invariant under `ρ` and is carried into the
`G`-finite vectors of the target by every intertwining map.

The notion is purely algebraic: no topology on `G` or `V` enters. For a strongly continuous Banach
representation of a compact group, this is the space of `K`-finite vectors of harmonic analysis
(for `G = K` a maximal compact subgroup), and the theorem that it is dense is
`ContRepresentation.dense_gFiniteSubmodule` in
`TauCeti/RepresentationTheory/Compact/GFiniteDensity.lean`.

## Main definitions

* `Representation.IsGFinite ρ v`: the orbit of `v` spans a finite-dimensional subspace.
* `Representation.gFiniteSubmodule ρ`: the submodule of `G`-finite vectors, the case of the family
  `ρ` of `TauCeti.finiteSpanRangeSubmodule` from `TauCeti/LinearAlgebra/Span/FiniteRange.lean`.

## Main statements

* `Representation.IsGFinite.of_apply_eq`: a vector whose orbit is the image under a linear map of a
  family spanning a finite-dimensional subspace is `G`-finite.
* `Representation.IsGFinite.of_forall_apply_mem`: a vector whose orbit lies in a
  finite-dimensional submodule is `G`-finite.
* `Representation.isGFinite_iff_exists_subrepresentation`: a vector is `G`-finite exactly when it
  lies in a finite-dimensional subrepresentation.
* `Representation.IsGFinite.add`, `Representation.IsGFinite.smul`, `Representation.IsGFinite.zero`:
  the `G`-finite vectors are closed under the linear operations.
* `Representation.IsGFinite.apply` and `Representation.apply_mem_gFiniteSubmodule`: the `G`-finite
  vectors are invariant under the representation.
* `Representation.IsGFinite.map` and `Representation.map_gFiniteSubmodule_le`: intertwining maps
  preserve `G`-finiteness.
* `Representation.IsGFinite.of_injective`: injective intertwining maps reflect `G`-finiteness.
* `Representation.gFiniteSubmodule_eq_top`: every vector of a finite-dimensional representation is
  `G`-finite.

## References

* N. R. Wallach, *Real Reductive Groups I*, Academic Press (1988), §1.4 (`K`-finite vectors).
-/

public section

namespace Representation

open TauCeti

variable {k G V W : Type*} [Field k] [Monoid G] [AddCommGroup V] [Module k V] [AddCommGroup W]
  [Module k W] (ρ : Representation k G V) (σ : Representation k G W)

/-- A vector `v` is **`G`-finite** for the representation `ρ` when its orbit `{ρ g v | g ∈ G}`
spans a finite-dimensional subspace of `V`. -/
def IsGFinite (v : V) : Prop :=
  FiniteDimensional k (Submodule.span k (Set.range fun g : G => ρ g v))

/-- Unfolding `G`-finiteness: the orbit spans a finite-dimensional subspace. -/
theorem isGFinite_iff (v : V) :
    ρ.IsGFinite v ↔ FiniteDimensional k (Submodule.span k (Set.range fun g : G => ρ g v)) :=
  (Iff.rfl)

/-- The **`G`-finite vectors** of a representation, as a submodule: the vectors whose images under
the family of maps `ρ g` span a finite-dimensional subspace. -/
def gFiniteSubmodule : Submodule k V :=
  finiteSpanRangeSubmodule fun g : G => ρ g

/-- Membership in the `G`-finite submodule is `G`-finiteness. -/
@[simp]
theorem mem_gFiniteSubmodule {v : V} : v ∈ ρ.gFiniteSubmodule ↔ ρ.IsGFinite v :=
  mem_finiteSpanRangeSubmodule.trans (ρ.isGFinite_iff v).symm

variable {ρ} in
/-- A vector whose whole orbit lies in a finite-dimensional submodule is `G`-finite. -/
theorem IsGFinite.of_forall_apply_mem {W : Submodule k V} [FiniteDimensional k W] {v : V}
    (h : ∀ g, ρ g v ∈ W) : ρ.IsGFinite v :=
  Submodule.finiteDimensional_of_le (S₂ := W) (Submodule.span_le.2 (Set.range_subset_iff.2 h))

/-- A vector is `G`-finite exactly when it lies in a finite-dimensional subrepresentation: the
span of its orbit is one. -/
theorem isGFinite_iff_exists_subrepresentation (v : V) :
    ρ.IsGFinite v ↔ ∃ W : Subrepresentation ρ, FiniteDimensional k W.toSubmodule ∧ v ∈ W := by
  refine ⟨fun hv => ⟨cyclicSubrepresentation ρ v, by rwa [toSubmodule_cyclicSubrepresentation],
    mem_cyclicSubrepresentation_self v⟩,
    fun ⟨W, _, hvW⟩ => IsGFinite.of_forall_apply_mem fun g => W.apply_mem_toSubmodule g hvW⟩

variable {ρ σ}

/-- A vector in a finite-dimensional invariant submodule is `G`-finite. -/
theorem IsGFinite.of_mem {W : Submodule k V} [FiniteDimensional k W]
    (hW : ∀ g, ∀ w ∈ W, ρ g w ∈ W) {v : V} (hv : v ∈ W) : ρ.IsGFinite v :=
  IsGFinite.of_forall_apply_mem fun g => hW g v hv

/-- Every vector of a finite-dimensional representation is `G`-finite. -/
theorem IsGFinite.of_finiteDimensional [FiniteDimensional k V] (v : V) : ρ.IsGFinite v :=
  Submodule.finiteDimensional_of_le le_top

/-- The zero vector is `G`-finite. -/
@[simp]
theorem IsGFinite.zero : ρ.IsGFinite 0 :=
  ρ.mem_gFiniteSubmodule.1 ρ.gFiniteSubmodule.zero_mem

/-- A sum of `G`-finite vectors is `G`-finite. -/
theorem IsGFinite.add {v w : V} (hv : ρ.IsGFinite v) (hw : ρ.IsGFinite w) :
    ρ.IsGFinite (v + w) :=
  ρ.mem_gFiniteSubmodule.1 <|
    ρ.gFiniteSubmodule.add_mem (ρ.mem_gFiniteSubmodule.2 hv) (ρ.mem_gFiniteSubmodule.2 hw)

/-- A scalar multiple of a `G`-finite vector is `G`-finite. -/
theorem IsGFinite.smul {v : V} (hv : ρ.IsGFinite v) (c : k) : ρ.IsGFinite (c • v) :=
  ρ.mem_gFiniteSubmodule.1 <| ρ.gFiniteSubmodule.smul_mem c (ρ.mem_gFiniteSubmodule.2 hv)

/-- The image of a `G`-finite vector under the representation is `G`-finite. -/
theorem IsGFinite.apply {v : V} (hv : ρ.IsGFinite v) (g : G) : ρ.IsGFinite (ρ g v) := by
  rw [isGFinite_iff] at hv
  exact IsGFinite.of_forall_apply_mem (W := Submodule.span k (Set.range fun g : G => ρ g v))
    fun h => Submodule.subset_span ⟨h * g, by simp⟩

/-- A vector whose orbit is the image under a linear map `f` of a family `u` spanning a
finite-dimensional subspace is `G`-finite. -/
theorem IsGFinite.of_apply_eq {M : Type*} [AddCommGroup M] [Module k M] (f : M →ₗ[k] V)
    {u : G → M} [FiniteDimensional k (Submodule.span k (Set.range u))] {v : V}
    (h : ∀ g, ρ g v = f (u g)) : ρ.IsGFinite v := by
  rw [isGFinite_iff, show Set.range (fun g : G => ρ g v) = f '' Set.range u by
    rw [← Set.range_comp]
    exact congrArg Set.range (funext h), Submodule.span_image]
  infer_instance

/-- An intertwining map carries `G`-finite vectors to `G`-finite vectors. -/
theorem IsGFinite.map (f : IntertwiningMap ρ σ) {v : V} (hv : ρ.IsGFinite v) :
    σ.IsGFinite (f v) := by
  rw [isGFinite_iff] at hv
  exact IsGFinite.of_apply_eq f.toLinearMap fun g =>
    (IntertwiningMap.isIntertwining _ _ f g v).symm

/-- An injective intertwining map reflects `G`-finiteness: a vector whose image is `G`-finite is
`G`-finite. -/
theorem IsGFinite.of_injective (f : IntertwiningMap ρ σ) (hf : Function.Injective f) {v : V}
    (hv : σ.IsGFinite (f v)) : ρ.IsGFinite v := by
  rw [isGFinite_iff] at hv ⊢
  have : FiniteDimensional k
      ((Submodule.span k (Set.range fun g : G => ρ g v)).map f.toLinearMap) := by
    rwa [Submodule.map_span, ← Set.range_comp,
      show ⇑f.toLinearMap ∘ (fun g : G => ρ g v) = fun g => σ g (f v) from
        funext fun g => IntertwiningMap.isIntertwining _ _ f g v]
  exact LinearEquiv.finiteDimensional (Submodule.equivMapOfInjective _ hf _).symm

variable (ρ)

/-- The `G`-finite vectors are invariant under the representation. -/
theorem apply_mem_gFiniteSubmodule {v : V} (hv : v ∈ ρ.gFiniteSubmodule) (g : G) :
    ρ g v ∈ ρ.gFiniteSubmodule :=
  ρ.mem_gFiniteSubmodule.2 ((ρ.mem_gFiniteSubmodule.1 hv).apply g)

variable {ρ} in
/-- An intertwining map carries the `G`-finite vectors into the `G`-finite vectors. -/
theorem map_gFiniteSubmodule_le (f : IntertwiningMap ρ σ) :
    ρ.gFiniteSubmodule.map f.toLinearMap ≤ σ.gFiniteSubmodule := by
  rintro _ ⟨v, hv, rfl⟩
  exact σ.mem_gFiniteSubmodule.2 ((ρ.mem_gFiniteSubmodule.1 hv).map f)

/-- In a finite-dimensional representation every vector is `G`-finite. -/
@[simp]
theorem gFiniteSubmodule_eq_top [FiniteDimensional k V] : ρ.gFiniteSubmodule = ⊤ :=
  eq_top_iff.2 fun v _ => ρ.mem_gFiniteSubmodule.2 (IsGFinite.of_finiteDimensional v)

end Representation
