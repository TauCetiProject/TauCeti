/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.Group.Profinite.ProP.FiniteGeneration
public import Mathlib.LinearAlgebra.Basis.Basic
import TauCeti.LinearAlgebra.Span.ZMod

/-!
# Bases of the Frattini quotient and topological generation

When the Frattini quotient is finite, Burnside's topological generation criterion becomes
a linear spanning criterion over `𝔽_p`. Any basis of the Frattini quotient lifts to
topological generators, even when the quotient is infinite.

The finiteness assumption in the spanning equivalence is on the quotient itself.
For a profinite pro-`p` group it is equivalent to topological finite generation, by
`IsProP.isTopologicallyFinitelyGenerated_iff_finite_quotient_proPFrattini`.
Without that assumption, the equivalence requires the topological closure of the algebraic
span. Algebraic spanning still suffices for topological generation.

## References

* L. Ribes and P. Zalesskii, *Profinite Groups*, Section 2.8 (Burnside's basis theorem).
-/

public section

namespace TauCeti

variable {p : ℕ} [Fact p.Prime]
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [TotallyDisconnectedSpace G]

/-- **Burnside's basis theorem, spanning form.** If the Frattini quotient is finite, a set
topologically generates a profinite pro-`p` group exactly when its images span that quotient
over `𝔽_p`. -/
theorem topologicallyGenerates_iff_span_frattiniQuotient [Finite (G ⧸ proPFrattini p G)]
    (hG : IsProP p G) (s : Set G) :
    (Subgroup.closure s).topologicalClosure = ⊤ ↔
      Submodule.span (ZMod p)
        ((fun g ↦ Additive.ofMul ((QuotientGroup.mk' (proPFrattini p G)) g)) '' s) = ⊤ := by
  rw [topologicallyGenerates_iff_frattiniQuotient hG s]
  let t := (QuotientGroup.mk' (proPFrattini p G)) '' s
  have hclosed : (Subgroup.closure t).topologicalClosure = Subgroup.closure t :=
    le_antisymm ((Subgroup.closure t).topologicalClosure_minimal le_rfl
      (Set.toFinite _).isClosed) (Subgroup.le_topologicalClosure _)
  rw [hclosed]
  have himage : (fun g ↦ Additive.ofMul ((QuotientGroup.mk' (proPFrattini p G)) g)) '' s =
      Additive.toMul ⁻¹' t := by
    simpa only [t, Set.image_image, Function.comp_def, Additive.ofMul_symm_eq] using
      (Additive.ofMul.image_eq_preimage_symm t)
  rw [himage, ← Submodule.toAddSubgroup_inj, span_zmod_eq_addSubgroupClosure,
    ← Subgroup.toAddSubgroup_closure]
  exact Subgroup.toAddSubgroup.injective.eq_iff.symm

/-- Any chosen lifts of a basis of the Frattini quotient topologically generate the
profinite pro-`p` group. -/
theorem topologicallyGenerates_of_basis_frattiniQuotient (hG : IsProP p G) {ι : Type*}
    (b : Module.Basis ι (ZMod p) (Additive (G ⧸ proPFrattini p G)))
    (g : ι → G)
    (hg : ∀ i, Additive.ofMul ((QuotientGroup.mk' (proPFrattini p G)) (g i)) = b i) :
    (Subgroup.closure (Set.range g)).topologicalClosure = ⊤ := by
  rw [topologicallyGenerates_iff_frattiniQuotient hG]
  have himage : Additive.toMul ⁻¹'
      ((QuotientGroup.mk' (proPFrattini p G)) '' Set.range g) = Set.range b := by
    rw [← Additive.ofMul_symm_eq, ← Additive.ofMul.image_eq_preimage_symm,
      Set.image_image, ← Set.range_comp]
    simp only [Function.comp_def, hg]
  have hclosure : Subgroup.closure
      ((QuotientGroup.mk' (proPFrattini p G)) '' Set.range g) = ⊤ := by
    apply Subgroup.toAddSubgroup.injective
    rw [Subgroup.toAddSubgroup_closure, himage,
      ← span_zmod_eq_addSubgroupClosure (n := p), b.span_eq]
    rfl
  exact top_unique (hclosure ▸ Subgroup.le_topologicalClosure _)

/-- Every basis of the Frattini quotient has a lift to a topological generating family. -/
theorem exists_lift_basis_frattiniQuotient (hG : IsProP p G) {ι : Type*}
    (b : Module.Basis ι (ZMod p) (Additive (G ⧸ proPFrattini p G))) :
    ∃ g : ι → G,
      (∀ i, Additive.ofMul ((QuotientGroup.mk' (proPFrattini p G)) (g i)) = b i) ∧
      (Subgroup.closure (Set.range g)).topologicalClosure = ⊤ := by
  choose g hg using fun i ↦ QuotientGroup.mk'_surjective (proPFrattini p G) (b i).toMul
  have hg' i : Additive.ofMul ((QuotientGroup.mk' (proPFrattini p G)) (g i)) = b i :=
    congrArg Additive.ofMul (hg i)
  exact ⟨g, hg', topologicallyGenerates_of_basis_frattiniQuotient hG b g hg'⟩

end TauCeti
