/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.RepresentationTheory.Intertwining

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
* `Representation.gFiniteSubmodule ρ`: the submodule of `G`-finite vectors.

## Main statements

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
* `Representation.gFiniteSubmodule_eq_top`: every vector of a finite-dimensional representation is
  `G`-finite.

## References

* N. R. Wallach, *Real Reductive Groups I*, Academic Press (1988), §1.4 (`K`-finite vectors).
-/

public section

namespace Representation

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

/-- The span of the orbit of a vector is invariant under the representation. -/
theorem apply_mem_span_range_apply (v : V) (g : G) {w : V}
    (hw : w ∈ Submodule.span k (Set.range fun h : G => ρ h v)) :
    ρ g w ∈ Submodule.span k (Set.range fun h : G => ρ h v) := by
  refine (Submodule.map_span_le (ρ g) _ _).2 ?_ (Submodule.mem_map_of_mem hw)
  rintro _ ⟨h, rfl⟩
  exact Submodule.subset_span ⟨g * h, by simp⟩

variable {ρ} in
/-- A vector whose whole orbit lies in a finite-dimensional submodule is `G`-finite. -/
theorem IsGFinite.of_forall_apply_mem {W : Submodule k V} [FiniteDimensional k W] {v : V}
    (h : ∀ g, ρ g v ∈ W) : ρ.IsGFinite v :=
  Submodule.finiteDimensional_of_le (S₂ := W) (Submodule.span_le.2 (Set.range_subset_iff.2 h))

/-- A vector is `G`-finite exactly when it lies in a finite-dimensional subrepresentation: the
span of its orbit is one. -/
theorem isGFinite_iff_exists_subrepresentation (v : V) :
    ρ.IsGFinite v ↔ ∃ W : Subrepresentation ρ, FiniteDimensional k W.toSubmodule ∧ v ∈ W := by
  refine ⟨fun hv => ⟨⟨Submodule.span k (Set.range fun g : G => ρ g v),
    fun g _ hw => ρ.apply_mem_span_range_apply v g hw⟩, hv, Submodule.subset_span ⟨1, by simp⟩⟩,
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
  IsGFinite.of_forall_apply_mem (W := ⊥) fun g => by simp

/-- A sum of `G`-finite vectors is `G`-finite. -/
theorem IsGFinite.add {v w : V} (hv : ρ.IsGFinite v) (hw : ρ.IsGFinite w) :
    ρ.IsGFinite (v + w) := by
  rw [isGFinite_iff] at hv hw
  refine IsGFinite.of_forall_apply_mem (W := Submodule.span k (Set.range fun g : G => ρ g v) ⊔
    Submodule.span k (Set.range fun g : G => ρ g w)) fun g => ?_
  rw [map_add]
  exact Submodule.add_mem_sup (Submodule.subset_span ⟨g, rfl⟩) (Submodule.subset_span ⟨g, rfl⟩)

/-- A scalar multiple of a `G`-finite vector is `G`-finite. -/
theorem IsGFinite.smul {v : V} (hv : ρ.IsGFinite v) (c : k) : ρ.IsGFinite (c • v) := by
  rw [isGFinite_iff] at hv
  refine IsGFinite.of_forall_apply_mem
    (W := Submodule.span k (Set.range fun g : G => ρ g v)) fun g => ?_
  rw [map_smul]
  exact Submodule.smul_mem _ c (Submodule.subset_span ⟨g, rfl⟩)

/-- The image of a `G`-finite vector under the representation is `G`-finite. -/
theorem IsGFinite.apply {v : V} (hv : ρ.IsGFinite v) (g : G) : ρ.IsGFinite (ρ g v) := by
  rw [isGFinite_iff] at hv
  exact IsGFinite.of_forall_apply_mem (W := Submodule.span k (Set.range fun g : G => ρ g v))
    fun h => Submodule.subset_span ⟨h * g, by simp⟩

/-- An intertwining map carries `G`-finite vectors to `G`-finite vectors. -/
theorem IsGFinite.map (f : IntertwiningMap ρ σ) {v : V} (hv : ρ.IsGFinite v) :
    σ.IsGFinite (f v) := by
  rw [isGFinite_iff] at hv ⊢
  have : Set.range (fun g : G => σ g (f v)) = f.toLinearMap '' Set.range fun g : G => ρ g v := by
    rw [← Set.range_comp]
    exact congrArg Set.range (funext fun g => (IntertwiningMap.isIntertwining _ _ f g v).symm)
  rw [this, Submodule.span_image]
  infer_instance

variable (ρ)

/-- The **`G`-finite vectors** of a representation, as a submodule. -/
def gFiniteSubmodule : Submodule k V where
  carrier := {v | ρ.IsGFinite v}
  add_mem' := IsGFinite.add
  zero_mem' := IsGFinite.zero
  smul_mem' c _ hv := hv.smul c

/-- Membership in the `G`-finite submodule is `G`-finiteness. -/
@[simp]
theorem mem_gFiniteSubmodule {v : V} : v ∈ ρ.gFiniteSubmodule ↔ ρ.IsGFinite v :=
  (Iff.rfl)

/-- The `G`-finite vectors are invariant under the representation. -/
theorem apply_mem_gFiniteSubmodule {v : V} (hv : v ∈ ρ.gFiniteSubmodule) (g : G) :
    ρ g v ∈ ρ.gFiniteSubmodule :=
  IsGFinite.apply hv g

variable {ρ} in
/-- An intertwining map carries the `G`-finite vectors into the `G`-finite vectors. -/
theorem map_gFiniteSubmodule_le (f : IntertwiningMap ρ σ) :
    ρ.gFiniteSubmodule.map f.toLinearMap ≤ σ.gFiniteSubmodule := by
  rintro _ ⟨v, hv, rfl⟩
  exact hv.map f

/-- In a finite-dimensional representation every vector is `G`-finite. -/
@[simp]
theorem gFiniteSubmodule_eq_top [FiniteDimensional k V] : ρ.gFiniteSubmodule = ⊤ :=
  eq_top_iff.2 fun v _ => IsGFinite.of_finiteDimensional v

end Representation
