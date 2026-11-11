/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Representation.ExteriorStabilizer.Character
public import TauCeti.Algebra.AlgebraicGroup.Representation.Faithful.Product
public import TauCeti.Algebra.AlgebraicGroup.Representation.Stabilizer.Product
import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Points.Order

/-!
# Faithful Chevalley line representations

For every closed subgroup of a finite-type affine group over a field, a faithful
finite-dimensional comodule contains a unimodular vector whose line stabilizer is that subgroup.
Take the Chevalley line in an exterior-power representation, add a faithful comodule, and embed
its generator as `(m, 0)`. This preserves the line stabilizer and makes the representation faithful.

Equality of Hopf ideals is recovered from points over all commutative value algebras, retaining
the subgroup's infinitesimal structure. Neither algebraic closedness nor reducedness is needed.

This proves the faithful-line prerequisite of TauCetiRoadmap/FlagVarieties/README.md,
Layer 4.0(c), step 1.

## References

* J. S. Milne, *Algebraic Groups* (2017), Theorems 4.9 and 4.27.
* J. E. Humphreys, *Linear Algebraic Groups*, §11.5 and §21.3.
-/

public section

open scoped TensorProduct

universe u

namespace TauCeti.HopfIdeal

attribute [local instance] Comodule.exteriorPower Comodule.Prod

/-- **Chevalley's theorem in a faithful representation.** Every closed subgroup of a finite-type
affine group over a field is the scheme-theoretic stabilizer of a line in a faithful
finite-dimensional comodule. No algebraic closedness or reducedness is required. -/
theorem exists_isFaithful_line_stabilizer {k H : Type u} [Field k]
    [CommRing H] [HopfAlgebra k H] [Algebra.FiniteType k H] (I : HopfIdeal k H) :
    ∃ (M : FGComoduleCat.{u, u, u} k H) (m : M) (_hm : Module.IsUnimodular k m),
      Comodule.IsFaithful (k := k) (H := H) (V := M) ∧
        (Submodule.span k {m}).stabilizerHopfIdeal H = I := by
  let K := _root_.CommHopfAlgCat.of k H
  have := Algebra.FiniteType.isNoetherianRing k H
  obtain ⟨U, n, hU, L, hL, _, hstab⟩ :=
    I.exists_finite_subcomodule_exteriorPower_line_stabilizer (H := K)
      (IsNoetherian.noetherian I.toIdeal)
  let : Module.Finite k U := hU
  let : AddCommGroup U := Module.addCommMonoidToAddCommGroup k
  let : AddCommGroup (⋀[k]^n U) := Module.addCommMonoidToAddCommGroup k
  let : AddCommGroup L := Module.addCommMonoidToAddCommGroup k
  obtain ⟨m, hm, hgen⟩ := (finrank_eq_one_iff' (K := k) (V := L)).mp hL
  have hspan : L = k ∙ (m : ⋀[k]^n U) := by
    apply le_antisymm
    · intro z hz
      obtain ⟨c, hc⟩ := hgen ⟨z, hz⟩
      exact Submodule.mem_span_singleton.mpr ⟨c, congrArg Subtype.val hc⟩
    · exact Submodule.span_le.mpr (Set.singleton_subset_iff.mpr m.property)
  have hLI : L.stabilizerHopfIdeal H = I := by
    apply HopfIdeal.eq_of_forall_quotientPointsSubgroup_eq (H := K)
    intro A
    ext g
    rw [CommHopfAlgCat.mem_quotientPointsSubgroup_iff]
    change ((L.stabilizerHopfIdeal H).toIdeal ≤ RingHom.ker g.ofConv) ↔ _
    exact (L.stabilizerHopfIdeal_le_ker_iff g).trans (hstab A g).symm
  obtain ⟨V, hV⟩ := Comodule.exists_isFaithful (k := k) (H := H)
  let M := FGComoduleCat.of (R := k) (C := H) ((⋀[k]^n U) × V)
  have hne : ((m : ⋀[k]^n U), (0 : V)) ≠ 0 := by
    intro h
    exact hm (Subtype.ext (congrArg Prod.fst h))
  refine ⟨M, ((m : ⋀[k]^n U), 0),
    Module.isUnimodular_iff.mpr (Module.Projective.exists_dual_eq_one k hne),
    hV.prod_right, ?_⟩
  exact (Submodule.stabilizerHopfIdeal_span_singleton_prod_zero (H := H)
    (V := V) (m : ⋀[k]^n U)).trans (hspan ▸ hLI)

end TauCeti.HopfIdeal
