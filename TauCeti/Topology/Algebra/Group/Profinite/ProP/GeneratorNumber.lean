/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.Group.Profinite.ProP.FiniteGeneration
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.Dimension.Constructions
import TauCeti.LinearAlgebra.Span.ZMod

/-!
# The number of generators of a finitely generated pro-`p` group

When the Frattini quotient is finite, Burnside's topological generation criterion becomes
a linear spanning criterion over `𝔽_p`. Consequently a basis lifts to topological generators,
and the least length of a generating tuple is the dimension of the Frattini quotient.

The finiteness assumption is on the quotient itself. For a profinite pro-`p` group it is
equivalent to topological finite generation, by
`IsProP.isTopologicallyFinitelyGenerated_iff_finite_quotient_proPFrattini`.
Without that assumption, algebraic span must be replaced by its topological closure.

## References

* L. Ribes and P. Zalesskii, *Profinite Groups*, Section 2.8 (Burnside's basis theorem).
-/

public section

namespace TauCeti

variable {p : ℕ} [Fact p.Prime]
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [TotallyDisconnectedSpace G]
  [Finite (G ⧸ proPFrattini p G)]

/-- **Burnside's basis theorem, spanning form.** If the Frattini quotient is finite, a set
topologically generates a profinite pro-`p` group exactly when its images span that quotient
over `𝔽_p`. -/
theorem topologicallyGenerates_iff_span_frattiniQuotient (hG : IsProP p G) (s : Set G) :
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

/-- Any chosen lifts of a basis of the finite Frattini quotient topologically generate the
profinite pro-`p` group. -/
theorem topologicallyGenerates_of_basis_frattiniQuotient (hG : IsProP p G) {ι : Type*}
    (b : Module.Basis ι (ZMod p) (Additive (G ⧸ proPFrattini p G)))
    (g : ι → G)
    (hg : ∀ i, Additive.ofMul ((QuotientGroup.mk' (proPFrattini p G)) (g i)) = b i) :
    (Subgroup.closure (Set.range g)).topologicalClosure = ⊤ := by
  rw [topologicallyGenerates_iff_span_frattiniQuotient hG, ← Set.range_comp]
  simpa only [Function.comp_def, hg] using b.span_eq

/-- Every basis of the finite Frattini quotient has a lift to a topological generating family. -/
theorem exists_lift_basis_frattiniQuotient (hG : IsProP p G) {ι : Type*}
    (b : Module.Basis ι (ZMod p) (Additive (G ⧸ proPFrattini p G))) :
    ∃ g : ι → G,
      (∀ i, Additive.ofMul ((QuotientGroup.mk' (proPFrattini p G)) (g i)) = b i) ∧
      (Subgroup.closure (Set.range g)).topologicalClosure = ⊤ := by
  choose g hg using fun i ↦ QuotientGroup.mk'_surjective (proPFrattini p G) (b i).toMul
  have hg' i : Additive.ofMul ((QuotientGroup.mk' (proPFrattini p G)) (g i)) = b i :=
    congrArg Additive.ofMul (hg i)
  exact ⟨g, hg', topologicallyGenerates_of_basis_frattiniQuotient hG b g hg'⟩

/-- **The generator number from the Frattini quotient.** A profinite pro-`p` group with
finite Frattini quotient admits a topological generating `n`-tuple exactly when the quotient
has dimension at most `n`. In particular, its dimension is the minimum possible tuple length,
including length zero for the trivial group. -/
theorem exists_topologicalClosure_closure_range_eq_top_iff_finrank_le (hG : IsProP p G)
    {n : ℕ} :
    (∃ g : Fin n → G, (Subgroup.closure (Set.range g)).topologicalClosure = ⊤) ↔
      Module.finrank (ZMod p) (Additive (G ⧸ proPFrattini p G)) ≤ n := by
  constructor
  · rintro ⟨g, hg⟩
    have hspan := (topologicallyGenerates_iff_span_frattiniQuotient hG _).mp hg
    rw [← Set.range_comp] at hspan
    simpa using finrank_le_of_span_eq_top hspan
  · intro hn
    classical
    obtain ⟨g, -, hg⟩ := exists_lift_basis_frattiniQuotient hG
      (Module.finBasis (ZMod p) (Additive (G ⧸ proPFrattini p G)))
    let e := Fin.castLEEmb hn
    let f := Function.extend e g (fun _ ↦ (1 : G))
    refine ⟨f, top_unique ?_⟩
    rw [← hg]
    apply Subgroup.topologicalClosure_mono
    apply Subgroup.closure_mono
    rintro _ ⟨i, rfl⟩
    exact ⟨e i, e.injective.extend_apply _ _ _⟩

end TauCeti
