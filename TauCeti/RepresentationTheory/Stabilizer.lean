/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Span.Defs
public import Mathlib.RepresentationTheory.Stabilizer
public import TauCeti.RepresentationTheory.Quotient
import Mathlib.Algebra.Module.Submodule.Union
import Mathlib.LinearAlgebra.FixedSubmodule

/-!
# Pointwise stabilizers of subsets and subspaces in representations

Let a group `G` act linearly on an `R`-module `M` through a representation `ρ`. Every element fixing
a set `s` of vectors pointwise fixes its `R`-linear span (`Representation.biInf_stabilizer_span`).

When `G` is finite and acts on a vector space `V` over an infinite field `K`, the pointwise
stabilizer `⨅ w ∈ U, ρ.stabilizer w` of any subspace `U` (and hence of any subset `s`, inside
`Submodule.span K s`) is realized as the stabilizer `ρ.stabilizer v` of a single general-position
vector `v ∈ U`: for each `g` not fixing `U` pointwise, `U ∩ ker (ρ g - 1)` is a proper subspace of
`U`, and `U` is not covered by finitely many proper subspaces
(`Submodule.exists_forall_notMem_of_forall_ne_top`). Neither finite-dimensionality of `V` nor any
characteristic assumption beyond `Infinite K` is needed.

Finally, quotienting `G` by a normal subgroup acting trivially pulls back point stabilizers without
change.

## Main results

* `Representation.biInf_stabilizer_span`: the pointwise stabilizer of `Submodule.span R s` equals
  the pointwise stabilizer of `s`.
* `Representation.exists_mem_stabilizer_eq_biInf`: over an infinite field, every subspace `U` of a
  representation of a finite group contains a vector whose stabilizer is the pointwise stabilizer
  of `U`.
* `Representation.exists_mem_span_stabilizer_eq_biInf`: the analogous general-position witness in
  `Submodule.span K s` for an arbitrary subset `s`.
* `Representation.comap_mk'_stabilizer_ofQuotient` and `Representation.map_mk'_stabilizer`: point
  stabilizers commute with passing to a quotient by a trivially acting normal subgroup.

## References

* R. Kane, *Reflection Groups and Invariant Theory*, CMS Books in Mathematics, Springer (2001),
  § 22.1.
-/

public section

namespace Representation

section Semiring

variable {R G M : Type*} [Semiring R] [Group G] [AddCommMonoid M] [Module R M]
variable (ρ : Representation R G M)

/-- The pointwise stabilizer of the `R`-linear span of `s` equals the pointwise stabilizer of
`s`. -/
@[simp]
theorem biInf_stabilizer_span (s : Set M) :
    (⨅ v ∈ Submodule.span R s, ρ.stabilizer v) = ⨅ v ∈ s, ρ.stabilizer v := by
  refine le_antisymm (le_iInf₂ fun v hv ↦ iInf₂_le v (Submodule.subset_span hv)) ?_
  refine le_iInf₂ fun v hv ↦ ?_
  induction hv using Submodule.span_induction with
  | mem x hx => exact iInf₂_le x hx
  | zero => simp [stabilizer_zero]
  | add x y _ _ ihx ihy => exact (le_inf ihx ihy).trans (ρ.le_stabilizer_add x y)
  | smul r x _ ihx => exact ihx.trans (ρ.le_stabilizer_smul r x)

/-- Pulling back the stabilizer of `v` in a quotient by a trivially acting normal subgroup recovers
`ρ.stabilizer v`. -/
@[simp]
theorem comap_mk'_stabilizer_ofQuotient (S : Subgroup G) [S.Normal]
    [IsTrivial (ρ.comp S.subtype)] (v : M) :
    ((ρ.ofQuotient S).stabilizer v).comap (QuotientGroup.mk' S) = ρ.stabilizer v := by
  ext g
  simp [Subgroup.mem_comap, QuotientGroup.mk'_apply, ρ.ofQuotient_coe_apply S g v]

/-- Pushing `ρ.stabilizer v` forward along the quotient by a trivially acting normal subgroup gives
the stabilizer of `v` in the quotient representation. -/
@[simp]
theorem map_mk'_stabilizer (S : Subgroup G) [S.Normal]
    [IsTrivial (ρ.comp S.subtype)] (v : M) :
    (ρ.stabilizer v).map (QuotientGroup.mk' S) = (ρ.ofQuotient S).stabilizer v := by
  rw [← ρ.comap_mk'_stabilizer_ofQuotient S v,
    Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective S)]

end Semiring

section InfiniteField

variable {K G V : Type*} [Field K] [Infinite K] [Group G] [Finite G]
  [AddCommGroup V] [Module K V] (ρ : Representation K G V)

/-- **General-position witness for a subspace stabilizer.** When a finite group `G` acts linearly on
a vector space `V` over an infinite field `K`, every subspace `U` contains a vector `v ∈ U` whose
stabilizer equals the pointwise stabilizer `⨅ w ∈ U, ρ.stabilizer w` of `U`. -/
theorem exists_mem_stabilizer_eq_biInf (U : Submodule K V) :
    ∃ v ∈ U, ρ.stabilizer v = ⨅ w ∈ U, ρ.stabilizer w := by
  classical
  set H : Subgroup G := ⨅ w ∈ U, ρ.stabilizer w
  -- Each `g ∉ H` fixes only a proper subspace of `U`.
  let p : {g : G // g ∉ H} → Submodule K U :=
    fun g ↦ (ρ g.1).fixedSubmodule.comap U.subtype
  have hp (g : {g : G // g ∉ H}) : p g ≠ ⊤ := by
    intro htop
    apply g.2
    rw [Subgroup.mem_iInf]
    intro w
    rw [Subgroup.mem_iInf]
    intro hw
    have hmem : (⟨w, hw⟩ : U) ∈ p g := htop ▸ Submodule.mem_top
    simpa [p] using hmem
  obtain ⟨u, hu⟩ := Submodule.exists_forall_notMem_of_forall_ne_top p hp
  refine ⟨u.1, u.2, le_antisymm ?_ (iInf₂_le u.1 u.2)⟩
  intro g hg
  by_contra hgH
  exact hu ⟨g, hgH⟩ (by simpa [p] using hg)

/-- **General-position witness for a set stabilizer.** Over an infinite field, the pointwise
stabilizer of any subset `s` of a representation of a finite group equals the stabilizer of a
single vector in `Submodule.span K s`. -/
theorem exists_mem_span_stabilizer_eq_biInf (s : Set V) :
    ∃ v ∈ Submodule.span K s, ρ.stabilizer v = ⨅ w ∈ s, ρ.stabilizer w := by
  obtain ⟨v, hv, hstab⟩ := ρ.exists_mem_stabilizer_eq_biInf (Submodule.span K s)
  exact ⟨v, hv, hstab.trans (ρ.biInf_stabilizer_span s)⟩

end InfiniteField

end Representation
