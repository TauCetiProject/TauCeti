/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Orthogonal.TypeD.SpinCarrier.Generated.Positive.StandardComodule
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.D.Positive

/-!
# Positive-root order and invariant spin coordinate spans

An invariant submodule for the generated positive type-D spin subgroup contains every weight
line above any line it contains in the integral positive-root order. Conversely a coordinate
span is invariant exactly when its index set is upward closed for that order. The propagation
works over every commutative ring; the converse characterization requires only nontriviality.

The weight differences and the cone use the simply connected character lattice, not toral
Lie eigenvalues in the coefficient ring. Thus the statements include characteristic two
and nonreduced coefficient rings, without identifying the two half-spin parities.

## References

* J. C. Jantzen, *Representations of Algebraic Groups*, I.2.
* J. E. Humphreys, *Linear Algebraic Groups*, §§21 and 27.

This combines the existing raising-step subcomodule criterion with the full-spin
positive-root path criterion in `TauCeti.DynkinType.typeDSpin_raisingPath_iff_mem_posRootCone`.
-/

public section

namespace TauCeti.TypeDSpinCarrier.Generated.Positive

open DynkinType

universe u

noncomputable section

variable (n : ℕ) (hn : 4 ≤ n) (R : Type u) [CommRing R]

attribute [local instance] standardComodule

local notation "C₊" => posRootCone (typeDSimplyConnectedRootDatum n hn)
  (typeDSimplyConnectedBase n hn)

/-- An invariant submodule containing a spin weight line contains every weight line above it
in the integral positive-root order. -/
theorem single_mem_of_mem_posRootCone
    (N : Subcomodule R (coordinateHopfAlgebra n hn R) (Fin (dimension n) → R))
    {a b : Fin (dimension n)} (hab : basisWeight n b - basisWeight n a ∈ C₊)
    (ha : Pi.single a (1 : R) ∈ N) : Pi.single b (1 : R) ∈ N := by
  let e := Fintype.equivFin (Finset (Fin n))
  have hprop (s t : Finset (Fin n)) (h : Relation.ReflTransGen TypeDSpinRaisingStep s t) :
      Pi.single (e s) (1 : R) ∈ N → Pi.single (e t) (1 : R) ∈ N := by
    induction h with
    | refl => exact id
    | @tail t v h htv ih =>
      obtain ⟨i, hi, rfl⟩ := (typeDSpinRaisingStep_iff _ _).mp htv
      intro hs
      have hweight : basisWeight n (e t) i = -1 := by
        simpa only [basisWeight, signSet, e, Equiv.symm_apply_apply] using hi
      have hreflect : basisReflection n i (e t) = e (typeDSpinReflection i t) := by
        apply e.symm.injective
        simpa only [signSet, e, Equiv.symm_apply_apply] using
          signSet_basisReflection n i (e t)
      rw [← hreflect]
      exact single_basisReflection_mem n hn R N i (e t) hweight (ih hs)
  have hpath := (typeDSpin_raisingPath_iff_mem_posRootCone hn (signSet n a) (signSet n b)).mpr hab
  have ha' : Pi.single (e (signSet n a)) (1 : R) ∈ N := by
    simpa only [e, signSet, Equiv.apply_symm_apply] using ha
  simpa only [e, signSet, Equiv.apply_symm_apply] using hprop _ _ hpath ha'

/-- A coordinate span is invariant precisely when its index set is upward closed for the
integral positive-root order. This is a universal-coaction criterion over any nontrivial ring. -/
theorem coordinateSpanIsStable_iff_mem_posRootCone [Nontrivial R]
    (s : Set (Fin (dimension n))) :
    (Pi.basisFun R (Fin (dimension n))).coordinateSpanIsStable
        (C := coordinateHopfAlgebra n hn R) s ↔
      ∀ a ∈ s, ∀ b, basisWeight n b - basisWeight n a ∈ C₊ → b ∈ s := by
  classical
  constructor
  · intro h a ha b hab
    let N := (Pi.basisFun R (Fin (dimension n))).coordinateSpanSubcomodule s h
    have hv : Pi.single a (1 : R) ∈ N := by
      rw [Module.Basis.mem_coordinateSpanSubcomodule]
      exact Submodule.subset_span ⟨a, ha, Pi.basisFun_apply R (Fin (dimension n)) a⟩
    have hb := single_mem_of_mem_posRootCone n hn R N hab hv
    rw [Module.Basis.mem_coordinateSpanSubcomodule] at hb
    exact (Pi.basisFun R (Fin (dimension n))).mem_span_image.mp hb (by simp)
  · intro hs
    apply (coordinateSpanIsStable_iff s).mpr
    intro i a ha hia
    apply hs a ha
    exact (typeDSpin_raisingPath_iff_mem_posRootCone hn _ _).mp
      (.single ((typeDSpinRaisingStep_iff _ _).mpr
        ⟨i, hia, (signSet_basisReflection n i a).symm⟩))

end

end TauCeti.TypeDSpinCarrier.Generated.Positive
