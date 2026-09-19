/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.Group.Profinite.ProP.Burnside
public import Mathlib.LinearAlgebra.Basis.Basic
import TauCeti.Algebra.Module.ZMod.Span
import TauCeti.Topology.Algebra.Group.Subgroup

/-!
# Bases of the Frattini quotient and topological generation

Burnside's topological generation criterion says that a set generates a profinite pro-`p`
group topologically exactly when its image spans a dense subspace of the Frattini quotient
over `𝔽_p`. When the quotient is finite, this is equivalent to algebraic spanning. Any basis
of the Frattini quotient lifts to topological generators, even when the quotient is infinite.

## References

* L. Ribes and P. Zalesskii, *Profinite Groups*, Section 2.8 (Burnside's basis theorem).
-/

public section

namespace TauCeti

variable {p : ℕ} [Fact p.Prime]
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [TotallyDisconnectedSpace G]

/-- **Burnside's basis theorem, dense spanning form.** A set topologically generates a
profinite pro-`p` group exactly when the span of its image in the Frattini quotient is dense. -/
theorem topologicallyGenerates_iff_frattiniQuotient_span_topologicalClosure_eq_top
    (hG : IsProP p G) (s : Set G) :
    (Subgroup.closure s).topologicalClosure = ⊤ ↔
      (Submodule.span (ZMod p)
        ((fun g ↦ Additive.ofMul
          (QuotientGroup.mk' (proPFrattini p G) g)) '' s)).toAddSubgroup.topologicalClosure =
        ⊤ := by
  rw [topologicallyGenerates_iff_frattiniQuotient hG s]
  let t := (QuotientGroup.mk' (proPFrattini p G)) '' s
  have himage : (fun g ↦ Additive.ofMul ((QuotientGroup.mk' (proPFrattini p G)) g)) '' s =
      Additive.toMul ⁻¹' t := by
    simpa only [t, Set.image_image, Function.comp_def, Additive.ofMul_symm_eq] using
      (Additive.ofMul.image_eq_preimage_symm t)
  rw [himage, span_zmod_eq_addSubgroupClosure, ← Subgroup.toAddSubgroup_closure]
  rw [← toAddSubgroup_topologicalClosure, ← Subgroup.toAddSubgroup.map_top,
    Subgroup.toAddSubgroup.injective.eq_iff]

/-- **Burnside's basis theorem, spanning form.** If the Frattini quotient is finite, a set
topologically generates a profinite pro-`p` group exactly when its images span that quotient
over `𝔽_p`. -/
theorem topologicallyGenerates_iff_frattiniQuotient_span_eq_top
    [Finite (G ⧸ proPFrattini p G)] (hG : IsProP p G) (s : Set G) :
    (Subgroup.closure s).topologicalClosure = ⊤ ↔
      Submodule.span (ZMod p)
        ((fun g ↦ Additive.ofMul ((QuotientGroup.mk' (proPFrattini p G)) g)) '' s) = ⊤ := by
  rw [topologicallyGenerates_iff_frattiniQuotient_span_topologicalClosure_eq_top hG s]
  have hclosed (S : AddSubgroup (Additive (G ⧸ proPFrattini p G))) :
      S.topologicalClosure = S :=
    le_antisymm (S.topologicalClosure_minimal le_rfl (Set.toFinite _).isClosed)
      S.le_topologicalClosure
  rw [hclosed, Submodule.toAddSubgroup_eq_top]

/-- Any chosen lifts of a basis of the Frattini quotient topologically generate the
profinite pro-`p` group. -/
theorem topologicallyGenerates_of_basis_frattiniQuotient (hG : IsProP p G) {ι : Type*}
    (b : Module.Basis ι (ZMod p) (Additive (G ⧸ proPFrattini p G)))
    (g : ι → G)
    (hg : ∀ i, Additive.ofMul ((QuotientGroup.mk' (proPFrattini p G)) (g i)) = b i) :
    (Subgroup.closure (Set.range g)).topologicalClosure = ⊤ := by
  rw [topologicallyGenerates_iff_frattiniQuotient_span_topologicalClosure_eq_top hG]
  have himage :
      (fun x ↦ Additive.ofMul ((QuotientGroup.mk' (proPFrattini p G)) x)) '' Set.range g =
        Set.range b := by
    rw [← Set.range_comp]
    simp only [Function.comp_def, hg]
  rw [himage, b.span_eq, Submodule.top_toAddSubgroup]
  exact top_unique (AddSubgroup.le_topologicalClosure _)

/-- Every basis of the Frattini quotient has a lift to a topological generating family. -/
theorem exists_lift_basis_frattiniQuotient_topologicallyGenerates (hG : IsProP p G) {ι : Type*}
    (b : Module.Basis ι (ZMod p) (Additive (G ⧸ proPFrattini p G))) :
    ∃ g : ι → G,
      (∀ i, Additive.ofMul ((QuotientGroup.mk' (proPFrattini p G)) (g i)) = b i) ∧
      (Subgroup.closure (Set.range g)).topologicalClosure = ⊤ := by
  choose g hg using fun i ↦ QuotientGroup.mk'_surjective (proPFrattini p G) (b i).toMul
  have hg' i : Additive.ofMul ((QuotientGroup.mk' (proPFrattini p G)) (g i)) = b i :=
    congrArg Additive.ofMul (hg i)
  exact ⟨g, hg', topologicallyGenerates_of_basis_frattiniQuotient hG b g hg'⟩

end TauCeti
