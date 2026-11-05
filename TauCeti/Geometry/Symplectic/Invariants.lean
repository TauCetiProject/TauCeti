/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RepresentationTheory.Invariants
public import Mathlib.RepresentationTheory.Subrepresentation
public import TauCeti.Geometry.Symplectic.Lagrangian.Basic
public import TauCeti.Geometry.Symplectic.PolarCompatible

/-!
# Fixed vectors of symplectic representations of compact groups

Let a compact group `G` act continuously and linearly on a finite-dimensional real vector space
`E`, preserving a symplectic form `ω`. The subspace `E^G` of vectors fixed by every element of `G`
is then a **symplectic subspace**: `ω` restricts to it nondegenerately
(`TauCeti.SymplecticForm.isSymplectic_invariants`). The same holds for the vectors fixed by any
subgroup of `G` (`TauCeti.SymplecticForm.isSymplectic_invariants_comp_subtype`). Hence
`E = E^G ⊕ (E^G)^ω`, and the symplectic complement `(E^G)^ω` carries the **normal representation**
(`TauCeti.SymplecticForm.normalSubrepresentation`): a symplectic representation of `G` without
nonzero fixed vectors (`TauCeti.SymplecticForm.IsSymplectic.invariants_normalSubrepresentation`).

This is the linear model of the fixed locus of a compact group of symplectomorphisms: applied to the
isotropy representation on a tangent space, it shows that the invariant tangent vectors at a fixed
point form a symplectic subspace, with the normal representation acting on its symplectic
complement.

Compactness cannot be dropped: the shear `(q, p) ↦ (q + p, p)` of `ℝ²` is symplectic, and the line
`p = 0` of its fixed vectors is isotropic. Compactness enters only through an invariant compatible
complex structure `J` (`TauCeti.SymplecticForm.exists_compatible_forall_isComplexLinearMap`). The
underlying statement holds for any representation by maps commuting with an almost complex
structure `J` tamed by `ω`: its invariants are `J`-stable, and a `J`-stable subspace `L` is
symplectic, because a vector `v ∈ L ∩ L^ω` has `ω (v, J v) = 0`
(`TauCeti.SymplecticForm.Tames.isSymplectic`,
`TauCeti.SymplecticForm.Tames.isSymplectic_invariants`).

## Main definitions

* `TauCeti.SymplecticForm.normalSubrepresentation ω hρ`: the symplectic complement of the
  invariants of a representation `ρ` preserving `ω`, as a subrepresentation of `ρ`.

## Main results

* `TauCeti.SymplecticForm.Tames.isSymplectic_invariants`: the invariants of a representation by
  maps commuting with such a structure form a symplectic subspace.
* `TauCeti.SymplecticForm.apply_mem_orthogonal`: the symplectic complement of a subspace stable
  under a group preserving `ω` is stable too.
* `TauCeti.SymplecticForm.IsSymplectic.invariants_normalSubrepresentation`: when the invariants
  are symplectic, the normal representation has no nonzero fixed vector.
* `TauCeti.SymplecticForm.isSymplectic_invariants`: the fixed vectors of a continuous symplectic
  representation of a compact group form a symplectic subspace.
* `TauCeti.SymplecticForm.isSymplectic_invariants_comp_subtype`: so do the fixed vectors of each of
  its subgroups.

## References

* M. F. Atiyah, *Convexity and commuting Hamiltonians*, Bull. London Math. Soc. 14 (1982), 1–15.
* V. Guillemin and S. Sternberg, *Convexity properties of the moment mapping*, Invent. Math. 67
  (1982), 491–513.
-/

public section

namespace TauCeti.SymplecticForm

variable {V : Type*} [AddCommGroup V] [Module ℝ V] {ω : SymplecticForm V}

/-! ### Subspaces stable under a tame almost complex structure -/

section Tames

variable {J : AlmostComplexStructure V}

/-- The vectors fixed by a representation of a group by maps complex linear for an almost complex
structure tamed by `ω` form a symplectic subspace. -/
theorem Tames.isSymplectic_invariants {G : Type*} [Group G] (hJ : ω.Tames J)
    {ρ : Representation ℝ G V} (hρ : ∀ g, IsComplexLinearMap J J (ρ g)) :
    ω.IsSymplectic ρ.invariants :=
  hJ.isSymplectic fun v hv ↦ (Representation.mem_invariants ρ _).2 fun g ↦ by
    rw [(isComplexLinearMap_iff_apply J J (ρ g)).1 (hρ g) v,
      (Representation.mem_invariants ρ v).1 hv g]

end Tames

/-! ### The normal representation -/

section Normal

variable {G : Type*} [Group G] {ρ : Representation ℝ G V}

/-- The symplectic complement of a subspace stable under a representation preserving `ω` is
stable under it as well. -/
theorem apply_mem_orthogonal (hρ : ∀ g u v, ω (ρ g u) (ρ g v) = ω u v) {L : Submodule ℝ V}
    (hL : ∀ g, ∀ v ∈ L, ρ g v ∈ L) (g : G) {v : V} (hv : v ∈ ω.orthogonal L) :
    ρ g v ∈ ω.orthogonal L := by
  rw [mem_orthogonal_iff] at hv ⊢
  intro y hy
  rw [← ρ.self_inv_apply g y, hρ]
  exact hv _ (hL g⁻¹ y hy)

variable (ω) in
/-- The **normal representation** of a representation `ρ` preserving `ω`: the restriction of `ρ`
to the symplectic complement `(V^G)^ω` of its invariants. When `V` is finite-dimensional and the
invariants form a symplectic subspace, as they do for a continuous representation of a compact
group on a finite-dimensional space (`TauCeti.SymplecticForm.isSymplectic_invariants`),
`V = V^G ⊕ (V^G)^ω` and this is the symplectic representation of `G` on the normal space to its
fixed vectors. -/
noncomputable def normalSubrepresentation (hρ : ∀ g u v, ω (ρ g u) (ρ g v) = ω u v) :
    Subrepresentation ρ where
  toSubmodule := ω.orthogonal ρ.invariants
  apply_mem_toSubmodule :=
    apply_mem_orthogonal hρ fun g v hv ↦ by rwa [(Representation.mem_invariants ρ v).1 hv g]

@[simp]
theorem toSubmodule_normalSubrepresentation (hρ : ∀ g u v, ω (ρ g u) (ρ g v) = ω u v) :
    (ω.normalSubrepresentation hρ).toSubmodule = ω.orthogonal ρ.invariants :=
  (rfl)

@[simp]
theorem mem_normalSubrepresentation_iff (hρ : ∀ g u v, ω (ρ g u) (ρ g v) = ω u v) {v : V} :
    v ∈ ω.normalSubrepresentation hρ ↔ ∀ w ∈ ρ.invariants, ω w v = 0 :=
  mem_orthogonal_iff

/-- When the invariants of `ρ` form a symplectic subspace, the normal representation has no
nonzero fixed vector. -/
theorem IsSymplectic.invariants_normalSubrepresentation
    (hρ : ∀ g u v, ω (ρ g u) (ρ g v) = ω u v) (h : ω.IsSymplectic ρ.invariants) :
    (ω.normalSubrepresentation hρ).toRepresentation.invariants = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro v hv
  refine Subtype.ext ((Submodule.disjoint_def.1 (isSymplectic_iff_disjoint.1 h)) v ?_ v.2)
  intro g
  simpa [Subrepresentation.toRepresentation_apply_coe] using
    congrArg Subtype.val ((Representation.mem_invariants _ v).1 hv g)

end Normal

/-! ### Compact groups -/

section Compact

variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  {ω : SymplecticForm E} {π : ContRepresentation ℝ G E}

/-- The vectors fixed by each subgroup of a compact group acting continuously by linear
symplectic maps form a symplectic subspace. A single compatible complex structure commutes with
the whole group, so the subgroup need not be closed. -/
theorem isSymplectic_invariants_comp_subtype (hπ : Continuous π)
    (hω : ∀ g u v, ω (π g u) (π g v) = ω u v) (H : Subgroup G) :
    ω.IsSymplectic (Representation.invariants (π.toRepresentation.comp H.subtype)) := by
  obtain ⟨J, hJ, hπJ⟩ := ω.exists_compatible_forall_isComplexLinearMap π hπ hω
  exact Tames.isSymplectic_invariants hJ.tames fun g ↦ hπJ g

/-- **The fixed vectors of a compact group of symplectic maps form a symplectic subspace.** For a
continuous linear action of a compact group `G` on a finite-dimensional real vector space `E`
preserving a symplectic form `ω`, the subspace `E^G` of fixed vectors is symplectic. -/
theorem isSymplectic_invariants (hπ : Continuous π) (hω : ∀ g u v, ω (π g u) (π g v) = ω u v) :
    ω.IsSymplectic π.toRepresentation.invariants := by
  obtain ⟨J, hJ, hπJ⟩ := ω.exists_compatible_forall_isComplexLinearMap π hπ hω
  exact Tames.isSymplectic_invariants hJ.tames hπJ

end Compact

end TauCeti.SymplecticForm
