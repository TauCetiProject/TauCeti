/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Chevalley.Root.Subgroup
import TauCeti.LinearAlgebra.RootSystem.Weyl.Orbit.Basic

/-!
# Extending pinned comparison equations to every root

A homomorphism between the point groups of two Chevalley data of the same type that matches
both signs of the numbered simple root subgroups matches every root subgroup. The value rings
may differ: parameters are transported by a specified ring homomorphism. In particular, checking
a comparison on the pinning suffices for its all-root equations and its Weyl-element equations.

The proof uses simple-reflection induction and the signed conjugation formula
`ChevalleyDatum.weylElement_conj_rootSubgroupPoints`. The sign depends only on the pinned Lie
algebra, not on the representation or admissible lattice, and ring homomorphisms preserve it.
No generation assertion about the entire point group is needed or asserted.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, Chapter 3, Lemma 19 and Corollary 5 to Theorem 4′.
* R. W. Carter, *Simple Groups of Lie Type*, §§6.4 and 7.2.
-/

public section

namespace TauCeti.DynkinType.ChevalleyDatum

variable {t : DynkinType} {ht : t.Valid} (D E : ChevalleyDatum t ht)
  {A B : Type*} [CommRing A] [CommRing B] (φ : A →+* B) (f : D.points A →* E.points B)
  (hpos : ∀ i u, f (D.rootSubgroupPoints (t.simpleIndex ht i) A (Multiplicative.ofAdd u)) =
    E.rootSubgroupPoints (t.simpleIndex ht i) B (Multiplicative.ofAdd (φ u)))
  (hneg : ∀ i u, f (D.rootSubgroupPoints ((t.simplyConnectedRootDatum ht).reflectionPerm
      (t.simpleIndex ht i) (t.simpleIndex ht i)) A (Multiplicative.ofAdd u)) =
    E.rootSubgroupPoints ((t.simplyConnectedRootDatum ht).reflectionPerm
      (t.simpleIndex ht i) (t.simpleIndex ht i)) B (Multiplicative.ofAdd (φ u)))

include hpos hneg

private theorem map_weylElement_simpleIndex (i : Fin t.rank) (s : Aˣ) :
    f (D.weylElement (t.simpleIndex ht i) A s) =
      E.weylElement (t.simpleIndex ht i) B (Units.map (φ : A →* B) s) := by
  simp only [weylElement_def, map_mul, hpos, hneg, Units.coe_map,
    MonoidHom.coe_ofClass, map_neg, ← map_inv]

/-- A homomorphism matching the positive and negative simple root parametrizations matches
all root parametrizations, with parameters transported along the same ring homomorphism.
This holds for arbitrary character lattices and commutative value rings. -/
theorem map_rootSubgroupPoints_of_simple (γ : Fin t.numRoots) (u : A) :
    f (D.rootSubgroupPoints γ A (Multiplicative.ofAdd u)) =
      E.rootSubgroupPoints γ B (Multiplicative.ofAdd (φ u)) := by
  have step (i : Fin t.rank) (k : Fin t.numRoots)
      (hk : ∀ u, f (D.rootSubgroupPoints k A (Multiplicative.ofAdd u)) =
        E.rootSubgroupPoints k B (Multiplicative.ofAdd (φ u))) (u : A) :
      f (D.rootSubgroupPoints
          ((t.simplyConnectedRootDatum ht).reflectionPerm (t.simpleIndex ht i) k) A
          (Multiplicative.ofAdd u)) =
        E.rootSubgroupPoints
          ((t.simplyConnectedRootDatum ht).reflectionPerm (t.simpleIndex ht i) k) B
          (Multiplicative.ofAdd (φ u)) := by
    set ε : ℤˣ := t.chevalleyWeylSign ht (t.simpleIndex ht i) k with hsign
    have hε : (ε : A) * (ε : A) = 1 := by
      simp [← Int.cast_mul, ← Units.val_mul]
    -- Apply conjugation at εu so that its signed target parameter is u in both value rings.
    have hconj := congrArg f (D.weylElement_conj_rootSubgroupPoints i k A ((ε : A) * u))
    rw [map_mul, map_mul, map_inv,
      D.map_weylElement_simpleIndex E φ f hpos hneg, hk] at hconj
    have hεB : (ε : B) * (ε : B) = 1 := by
      simp [← Int.cast_mul, ← Units.val_mul]
    simpa only [map_one, E.weylElement_conj_rootSubgroupPoints, map_mul, map_intCast,
      ← mul_assoc, ← hsign, hε, hεB, one_mul] using hconj.symm
  refine (t.rationalBase ht).induction_simple_reflect γ
    (p := fun k => ∀ u, f (D.rootSubgroupPoints k A (Multiplicative.ofAdd u)) =
      E.rootSubgroupPoints k B (Multiplicative.ofAdd (φ u)))
    (fun k hk => ?_) (fun k j hk hj => ?_) u
  · obtain ⟨i, rfl⟩ := exists_simpleIndex_eq_of_mem_support hk
    exact hpos i
  · obtain ⟨i, rfl⟩ := exists_simpleIndex_eq_of_mem_support hj
    simpa only [reflectionPerm_rationalRootSystem] using step i k hk

/-- A pinned comparison sends every Steinberg Weyl element to the corresponding Weyl element,
including its unit parameter. No restriction on the weight lattices is required. -/
theorem map_weylElement_of_simple (γ : Fin t.numRoots) (s : Aˣ) :
    f (D.weylElement γ A s) =
      E.weylElement γ B (Units.map (φ : A →* B) s) := by
  simp only [weylElement_def, map_mul, D.map_rootSubgroupPoints_of_simple E φ f hpos hneg,
    Units.coe_map, MonoidHom.coe_ofClass, map_neg, ← map_inv]

end TauCeti.DynkinType.ChevalleyDatum
