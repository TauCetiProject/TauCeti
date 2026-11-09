/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Orthogonal.TypeB.SpinCarrier.Generated.Positive.StandardComodule
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.B.Positive

/-!
# The weight order on invariant type-B spin subspaces

An invariant subspace for the positive spin subgroup contains every weight line above any of
its weight lines in the integral positive-root order. Equivalently, a coordinate span is
invariant precisely when its indices are upward closed for that order. This is the coordinate
flag constraint used to control negative-root directions in solvable overgroups of the positive
subgroup, extending the one-step raising criterion to arbitrary positive-cone differences.

The statements concern the universal coaction, over every nontrivial commutative coefficient
ring for the equivalence, not just the action of field-valued points. They combine the existing
spin raising-operator calculation with
`TauCeti.DynkinType.typeBSpin_raisingPath_iff_mem_posRootCone`.

## References

* J. C. Jantzen, *Representations of Algebraic Groups*, I.2 and II.2.
* J. E. Humphreys, *Linear Algebraic Groups*, §21.
-/

public section

namespace TauCeti.TypeBSpinCarrier.Generated.Positive

open DynkinType

noncomputable section

variable {n : ℕ} {R : Type*} [CommRing R]

attribute [local instance] standardComodule

/-- A subcomodule containing a spin weight line contains every higher line in the integral
positive-root order. This also holds over coefficient rings with torsion. -/
theorem single_mem_of_sub_mem_posRootCone
    (N : Subcomodule R (coordinateHopfAlgebra n R) (Fin (dimension n) → R))
    {a b : Fin (dimension n)}
    (hab : basisWeight n b - basisWeight n a ∈
      posRootCone (typeBSimplyConnectedRootDatum (n + 1)) (typeBSimplyConnectedBase (n + 1)))
    (ha : Pi.single a (1 : R) ∈ N) : Pi.single b (1 : R) ∈ N := by
  let e := Fintype.equivFin (Finset (Fin (n + 1)))
  have hpath := (typeBSpin_raisingPath_iff_mem_posRootCone (signSet n a) (signSet n b)).mpr hab
  have hmem : ∀ t, Relation.ReflTransGen TypeBSpinRaisingStep (signSet n a) t →
      Pi.single (e t) (1 : R) ∈ N := by
    intro t h
    induction h with
    | refl => simpa only [e, signSet, Equiv.apply_symm_apply] using ha
    | @tail t u h htu ih =>
      obtain ⟨i, hi, rfl⟩ := (typeBSpinRaisingStep_iff _ _).mp htu
      have hweight : basisWeight n (e t) i = -1 := by
        simpa only [basisWeight, signSet, e, Equiv.symm_apply_apply] using hi
      have hindex : basisReflection n i (e t) = e (typeBSpinReflection i t) := by
        simpa only [List.foldl_cons, List.foldl_nil] using foldl_basisReflection n [i] t
      simpa only [hindex] using single_basisReflection_mem n R N i (e t) hweight ih
  simpa only [e, signSet, Equiv.apply_symm_apply] using hmem _ hpath

/-- A coordinate span is invariant precisely when its indices are upward closed for the
integral positive-root order on spin weights. -/
theorem coordinateSpanIsStable_iff_posRootCone [Nontrivial R] (s : Set (Fin (dimension n))) :
    (Pi.basisFun R (Fin (dimension n))).coordinateSpanIsStable
        (C := coordinateHopfAlgebra n R) s ↔
      ∀ a ∈ s, ∀ b, basisWeight n b - basisWeight n a ∈
        posRootCone (typeBSimplyConnectedRootDatum (n + 1)) (typeBSimplyConnectedBase (n + 1)) →
          b ∈ s := by
  classical
  constructor
  · intro hs a ha b hab
    let N := (Pi.basisFun R (Fin (dimension n))).coordinateSpanSubcomodule s hs
    have hsingle : Pi.single a (1 : R) ∈ N := by
      rw [Module.Basis.mem_coordinateSpanSubcomodule]
      exact Submodule.subset_span ⟨a, ha, Pi.basisFun_apply R (Fin (dimension n)) a⟩
    have hb := single_mem_of_sub_mem_posRootCone N hab hsingle
    rw [Module.Basis.mem_coordinateSpanSubcomodule] at hb
    exact (Pi.basisFun R (Fin (dimension n))).mem_span_image.mp hb (by simp)
  · intro hs
    apply (coordinateSpanIsStable_iff s).mpr
    intro i a ha hia
    apply hs a ha (basisReflection n i a)
    apply (typeBSpin_raisingPath_iff_mem_posRootCone _ _).mp
    exact Relation.ReflTransGen.single
      ((typeBSpinRaisingStep_iff _ _).mpr ⟨i, hia, (signSet_basisReflection n i a).symm⟩)

end

end TauCeti.TypeBSpinCarrier.Generated.Positive
