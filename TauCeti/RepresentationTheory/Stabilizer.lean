/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Span.Defs
public import Mathlib.RepresentationTheory.Stabilizer
import Mathlib.Algebra.Module.Submodule.Union
import Mathlib.LinearAlgebra.FixedSubmodule
import TauCeti.RepresentationTheory.Quotient

/-!
# Pointwise stabilizers of subsets and subspaces in representations

Let a group `G` act linearly on an `R`-module `M` through `ρ`. Every element fixing a set `s`
pointwise fixes `Submodule.span R s` (`Representation.biInf_stabilizer_span`), and pulling `ρ` back
along a group homomorphism pulls back point stabilizers (`Representation.stabilizer_comp`) and
pushes them forward when surjective (`Representation.map_stabilizer_comp_of_surjective`).

When `G` is finite and acts on a vector space `V` over an infinite field `K` (without dimension or
characteristic restrictions), the pointwise stabilizer `⨅ w ∈ U, ρ.stabilizer w` of any subspace `U`
equals `ρ.stabilizer v` for a single general-position vector `v ∈ U`, via subspace avoidance
(`Submodule.exists_forall_notMem_of_forall_ne_top`).

## Main results

* `Representation.biInf_stabilizer_span`: pointwise stabilizer of `Submodule.span R s`.
* `Representation.stabilizer_comp`, `Representation.map_stabilizer_comp_of_surjective`,
  `Representation.comap_mk'_stabilizer_ofQuotient`, and `Representation.map_mk'_stabilizer`:
  pullback and pushforward of point stabilizers under group homomorphisms and quotients.
* `Representation.exists_mem_stabilizer_eq_biInf` and
  `Representation.exists_mem_span_stabilizer_eq_biInf`: general-position stabilizer witnesses in `U`
  and `Submodule.span K s` over an infinite field.

## References

* R. Kane, *Reflection Groups and Invariant Theory*, CMS Books in Mathematics, Springer (2001),
  § 22.1.
-/

public section

namespace Representation

section Semiring

variable {R G M : Type*} [Semiring R] [Group G] [AddCommMonoid M] [Module R M]
  (ρ : Representation R G M)

/-- The pointwise stabilizer of the `R`-linear span of `s` equals the pointwise stabilizer of
`s`. -/
@[simp] theorem biInf_stabilizer_span (s : Set M) :
    (⨅ v ∈ Submodule.span R s, ρ.stabilizer v) = ⨅ v ∈ s, ρ.stabilizer v := by
  refine le_antisymm (le_iInf₂ fun v hv ↦ iInf₂_le v (Submodule.subset_span hv)) (le_iInf₂ ?_)
  intro v hv
  induction hv using Submodule.span_induction with
  | mem x hx => exact iInf₂_le x hx
  | zero => simp [stabilizer_zero]
  | add x y _ _ ihx ihy => exact (le_inf ihx ihy).trans (ρ.le_stabilizer_add x y)
  | smul r x _ ihx => exact ihx.trans (ρ.le_stabilizer_smul r x)

/-- Pulling a representation back along a group homomorphism `f` pulls back point stabilizers by
`Subgroup.comap f`. -/
@[simp] theorem stabilizer_comp {H : Type*} [Group H] (f : H →* G) (v : M) :
    stabilizer (ρ.comp f) v = (ρ.stabilizer v).comap f := rfl

/-- Pushing forward the stabilizer of `v` in `ρ.comp f` along a surjective group homomorphism `f`
recovers `ρ.stabilizer v`. -/
theorem map_stabilizer_comp_of_surjective {H : Type*} [Group H] {f : H →* G}
    (hf : Function.Surjective f) (v : M) :
    (stabilizer (ρ.comp f) v).map f = ρ.stabilizer v := by
  rw [ρ.stabilizer_comp f v, Subgroup.map_comap_eq_self_of_surjective hf]

/-- Pulling back the stabilizer of `v` in a quotient by a trivially acting normal subgroup recovers
`ρ.stabilizer v`. -/
@[simp] theorem comap_mk'_stabilizer_ofQuotient (S : Subgroup G) [S.Normal]
    [IsTrivial (ρ.comp S.subtype)] (v : M) :
    ((ρ.ofQuotient S).stabilizer v).comap (QuotientGroup.mk' S) = ρ.stabilizer v := by
  rw [← (ρ.ofQuotient S).stabilizer_comp (QuotientGroup.mk' S) v, ρ.ofQuotient_comp_mk' S]

/-- Pushing `ρ.stabilizer v` forward along the quotient by a trivially acting normal subgroup gives
the stabilizer of `v` in the quotient representation. -/
@[simp] theorem map_mk'_stabilizer (S : Subgroup G) [S.Normal]
    [IsTrivial (ρ.comp S.subtype)] (v : M) :
    (ρ.stabilizer v).map (QuotientGroup.mk' S) = (ρ.ofQuotient S).stabilizer v := by
  simpa only [ρ.ofQuotient_comp_mk' S] using
    (ρ.ofQuotient S).map_stabilizer_comp_of_surjective (QuotientGroup.mk'_surjective S) v

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
  let p : {g : G // g ∉ H} → Submodule K U := fun g ↦ (ρ g.1).fixedSubmodule.comap U.subtype
  have hp (g : {g : G // g ∉ H}) : p g ≠ ⊤ := fun htop ↦ g.2 <|
    Subgroup.mem_iInf.mpr fun w ↦ Subgroup.mem_iInf.mpr fun hw ↦ by
      simpa [p] using (htop ▸ Submodule.mem_top : (⟨w, hw⟩ : U) ∈ p g)
  obtain ⟨u, hu⟩ := Submodule.exists_forall_notMem_of_forall_ne_top p hp
  refine ⟨u.1, u.2, le_antisymm (fun g hg ↦ ?_) (iInf₂_le u.1 u.2)⟩
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
