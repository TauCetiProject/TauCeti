/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.Gram
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.Reduced

/-!
# Roots and coroots of the pinned datum of a simply-laced type

The pinned simply connected root datum `t.simplyConnectedRootDatum ht` writes roots in the
fundamental-weight basis and coroots in the simple-coroot basis.  In a simply-laced type every root
`α` has the same length as the simple roots, so `α` and its coroot `α^∨` have the same coordinates
in the simple-root and simple-coroot bases respectively.  On the pinned datum this says that the
root with index `k` is the image of the coroot with index `k` under the Cartan matrix, since the
simple roots are the rows of the Cartan matrix.

Consequently the pairing of the datum is the symmetric bilinear form of the Cartan matrix on
coroot coordinates, and the reflection in a simple root acts on coroot coordinates by
`c ↦ c - (c, αᵢ) eᵢ`.  These are the coordinate facts through which the root lattice
`TauCeti.DynkinType.rootLattice`, whose Gram matrix is the Cartan matrix, sees the roots.

The proof is uniform in the type: the identity holds at the simple roots by the pinning, and is
preserved by simple reflections because the Cartan matrix is symmetric, so Mathlib's
`RootPairing.Base.induction_reflect` propagates it to every root.

## Main results

* `TauCeti.DynkinType.root_eq_coroot_vecMul_cartanMatrix`: the root with index `k` is
  `coroot k ᵥ* t.cartanMatrix`.
* `TauCeti.DynkinType.root_eq_sum_coroot_smul_root_simpleIndex`: the root with index `k` is the
  combination of the simple roots with coefficients the coordinates of `coroot k`.
* `TauCeti.DynkinType.pairing_eq_coroot_vecMul_dotProduct`: the pairing is the Cartan form of the
  coroot coordinates.
* `TauCeti.DynkinType.coroot_reflectionPerm_simpleIndex`: simple reflections in coroot
  coordinates.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Ch. VI, §1.1 and Plates I--VII.
* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, §§9.1, 10.3.
-/

public section

namespace TauCeti.DynkinType

open _root_.Matrix

variable (t : DynkinType) (ht : t.Valid) (hs : t.IsSimplyLaced)

include hs in
/-- **In a simply-laced type, a root is the Cartan image of its coroot**: the root of the pinned
datum with index `k`, in fundamental-weight coordinates, is `coroot k ᵥ* t.cartanMatrix`, where
`coroot k` is written in simple-coroot coordinates. -/
theorem root_eq_coroot_vecMul_cartanMatrix (k : Fin t.numRoots) :
    (t.simplyConnectedRootDatum ht).root k =
      (t.simplyConnectedRootDatum ht).coroot k ᵥ* t.cartanMatrix := by
  have := t.isReduced_simplyConnectedRootDatum ht
  set P := t.simplyConnectedRootDatum ht
  have hpairing (i j : Fin t.numRoots) : P.pairing i j = P.root i ⬝ᵥ P.coroot j := by
    rw [← RootPairing.root_coroot_eq_pairing, toLinearMap_simplyConnectedRootDatum]
  have hsimple (s : Fin t.rank) :
      P.root (t.simpleIndex ht s) = P.coroot (t.simpleIndex ht s) ᵥ* t.cartanMatrix := by
    rw [root_simpleIndex, coroot_simpleIndex, single_one_vecMul]
    ext
    simp
  refine (t.simplyConnectedBase ht).induction_reflect (p := fun k ↦
      P.root k = P.coroot k ᵥ* t.cartanMatrix) k (fun i hi ↦ ?_) (fun i hi ↦ ?_)
    fun i j hi hj ↦ ?_
  · rw [RootPairing.root_reflectionPerm, RootPairing.reflection_apply_self,
      RootPairing.coroot_reflectionPerm, RootPairing.coreflection_apply_self, hi, neg_vecMul]
  · obtain ⟨s, rfl⟩ : ∃ s, t.simpleIndex ht s = i :=
      ⟨⟨i, (mem_support_simplyConnectedBase t ht).mp hi⟩, Fin.ext (simpleIndex_val t ht _)⟩
    exact hsimple s
  · obtain ⟨s, rfl⟩ : ∃ s, t.simpleIndex ht s = j :=
      ⟨⟨j, (mem_support_simplyConnectedBase t ht).mp hj⟩, Fin.ext (simpleIndex_val t ht _)⟩
    rw [RootPairing.root_reflectionPerm, RootPairing.reflection_apply_root,
      RootPairing.coroot_reflectionPerm, RootPairing.coreflection_apply_coroot, sub_vecMul,
      smul_vecMul, hpairing, hpairing, hi, hsimple, vecMul_dotProduct_comm hs.isSymm_cartanMatrix]

include hs in
/-- **In a simply-laced type, the coroot coordinates of a root are its simple-root coordinates.**
The root of the pinned datum with index `k` is the integral combination of the simple roots whose
coefficients are the coordinates of the coroot with index `k` in the simple-coroot basis. -/
theorem root_eq_sum_coroot_smul_root_simpleIndex (k : Fin t.numRoots) :
    (t.simplyConnectedRootDatum ht).root k =
      ∑ i, (t.simplyConnectedRootDatum ht).coroot k i •
        (t.simplyConnectedRootDatum ht).root (t.simpleIndex ht i) := by
  rw [t.root_eq_coroot_vecMul_cartanMatrix ht hs k]
  ext j
  simp [vecMul, dotProduct, Finset.sum_apply]

include hs in
/-- **In a simply-laced type, the pairing is the Cartan form of the coroot coordinates**:
`⟨α_k, α_l^∨⟩ = (c_k ᵥ* t.cartanMatrix) ⬝ᵥ c_l`, where `c_k` and `c_l` are the coroots with indices
`k` and `l` in simple-coroot coordinates. -/
theorem pairing_eq_coroot_vecMul_dotProduct (k l : Fin t.numRoots) :
    (t.simplyConnectedRootDatum ht).pairing k l =
      ((t.simplyConnectedRootDatum ht).coroot k ᵥ* t.cartanMatrix) ⬝ᵥ
        (t.simplyConnectedRootDatum ht).coroot l := by
  rw [← RootPairing.root_coroot_eq_pairing, toLinearMap_simplyConnectedRootDatum,
    t.root_eq_coroot_vecMul_cartanMatrix ht hs]

include hs in
/-- **Simple reflections in coroot coordinates**: in a simply-laced type, reflecting in the `i`-th
simple root acts on simple-coroot coordinates by `c ↦ c - (c ᵥ* t.cartanMatrix) i • eᵢ`. -/
theorem coroot_reflectionPerm_simpleIndex (i : Fin t.rank) (k : Fin t.numRoots) :
    (t.simplyConnectedRootDatum ht).coroot
        ((t.simplyConnectedRootDatum ht).reflectionPerm (t.simpleIndex ht i) k) =
      (t.simplyConnectedRootDatum ht).coroot k -
        ((t.simplyConnectedRootDatum ht).coroot k ᵥ* t.cartanMatrix) i • Pi.single i 1 := by
  rw [RootPairing.coroot_reflectionPerm, RootPairing.coreflection_apply_coroot,
    t.pairing_eq_coroot_vecMul_dotProduct ht hs, coroot_simpleIndex,
    vecMul_dotProduct_comm hs.isSymm_cartanMatrix, dotProduct_single, mul_one]

end TauCeti.DynkinType
