/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.AInfinity.Algebra.Transfer.Basic
public import TauCeti.Algebra.Homology.AInfinity.Algebra.Transfer.Naturality
public import TauCeti.Algebra.Module.GradedModule.Multilinear.Composition
public import TauCeti.Combinatorics.Tree.ReducedPlanar
public import TauCeti.LinearAlgebra.TensorCoalgebra.BlockWord

/-!
# Planar-tree formulas for homological transfer of A-infinity algebras

Let `𝒜` be an `A∞` algebra on `A`, and let `c` be a special contraction of `(A, m₁)` onto a
graded module `(H, d_H)` with homotopy `h` of degree `-1` and inclusion `i` and projection `p` of
degree zero. Homological perturbation of the bar construction (`TauCeti.AInfinityAlgebra.transfer`
and `TauCeti.AInfinityAlgebra.transferInclusion`) produces a transferred `A∞` algebra on `H` and an
extending `A∞` quasi-isomorphism `H ⟶ A`. This file expresses all higher operations of the
transferred structure and all arity components of the extending morphism as explicit sums over
reduced planar rooted trees (`TauCeti.ReducedPlanarTree`).

On the suspended bar coalgebra, the tree evaluations carry no Koszul signs: each input leaf of a
reduced planar tree `t` applies `i`, each internal vertex of arity `k + 2` applies the suspended
operation `b_{k + 2}` (`TauCeti.AInfinityAlgebra.suspendedM`), each non-root internal vertex (and
the root of a branch tree) applies `-h`, and the root of an operation tree applies `p`. Precomposing
with the Koszul twists `t.numLeaves - 1 - l` unsuspends these multilinear maps to `H`, producing
the branch map `TauCeti.AInfinityAlgebra.treeBranch` (of cohomological degree `1 - t.numLeaves`) and
the operation map `TauCeti.AInfinityAlgebra.treeOperation` (of cohomological degree
`2 - t.numLeaves`). At an internal vertex `node k children`, the unsuspended evaluation decomposes
through `TauCeti.InternalGrading.signedCompMultilinearMap` up to the explicit vertex sign
`(-1) ^ ∑ i, (k + 1 - i) * (1 - (children i).numLeaves)`.

To identify these tree sums with the perturbation-series transfer, we first derive the operator
fixed-point equations `f.taylor = i ∘ letter - h ∘ higherTaylor ∘ f.barMap` and
`transfer.taylor = d_H ∘ letter + p ∘ higherTaylor ∘ f.barMap`, expand `higherTaylor ∘ f.barMap`
on a pure tensor word as a sum over compositions into at least two blocks, and match that arity
recursion with the root-composition bijection `TauCeti.ReducedPlanarTree.arityCompositionEquiv`.
When all operations of `𝒜` in arity at least three vanish (the differential graded algebra case),
every non-binary tree evaluates to zero and the sums restrict to planar binary trees.

## Main definitions

* `TauCeti.AInfinityAlgebra.suspendedM`: the suspended `n`-ary operation `bₙ` of an `A∞` algebra.
* `TauCeti.AInfinityAlgebra.suspendedTreeBranch` and
  `TauCeti.AInfinityAlgebra.suspendedTreeOperation`: the sign-free suspended multilinear maps
  attached to a reduced planar tree.
* `TauCeti.AInfinityAlgebra.treeBranch` and `TauCeti.AInfinityAlgebra.treeOperation`: the
  unsuspended multilinear branch and operation maps attached to a reduced planar tree.

## Main results

* `TauCeti.AInfinityAlgebra.isHomogeneous_treeBranch` and
  `TauCeti.AInfinityAlgebra.isHomogeneous_treeOperation`: cohomological degrees `1 - t.numLeaves`
  and `2 - t.numLeaves` of the unsuspended tree maps.
* `TauCeti.AInfinityAlgebra.treeBranch_node` and `TauCeti.AInfinityAlgebra.treeOperation_node`:
  unsuspended recursion at an internal vertex via `InternalGrading.signedCompMultilinearMap`.
* `TauCeti.AInfinityAlgebra.treeBranch_binary` and `TauCeti.AInfinityAlgebra.treeOperation_binary`:
  explicit Koszul-signed recursion on a binary vertex `binary l r`.
* `TauCeti.AInfinityAlgebra.taylor_transferInclusion_eq_sub` and
  `TauCeti.AInfinityAlgebra.taylor_transfer_eq_add`: Merkulov's recursive fixed-point equations for
  the Taylor maps of the extending morphism and the transferred `A∞` structure.
* `TauCeti.AInfinityAlgebra.component_transferInclusion` and
  `TauCeti.AInfinityAlgebra.m_transfer_eq_sum_arity`: for every `n`, the arity-`n` component of
  `transferInclusion` is the sum of `treeBranch` over `ReducedPlanarTree.Arity n`, and for every
  `n ≥ 2`, the transferred operation `mₙ` is the sum of `treeOperation` over
  `ReducedPlanarTree.Arity n`.
* `TauCeti.AInfinityAlgebra.component_three_transferInclusion`: explicit cubic component of the
  extending `A∞` quasi-isomorphism as a three-tree sum.
* `TauCeti.AInfinityAlgebra.component_transferInclusion_eq_sum_isBinary` and
  `TauCeti.AInfinityAlgebra.m_transfer_eq_sum_isBinary`: Kontsevich--Soibelman binary-tree
  specialization when `𝒜.m k = 0` for all `k ≥ 3`.
* `TauCeti.AInfinityAlgebra.map_treeBranch` and `TauCeti.AInfinityAlgebra.map_treeOperation`:
  tree-by-tree naturality under strict `A∞` morphisms compatible with the contractions.

## References

* V. K. A. M. Gugenheim, L. A. Lambe, and J. D. Stasheff, *Perturbation theory in differential
  homological algebra II*, Illinois Journal of Mathematics 35 (1991), 357--373.
* J. Huebschmann and T. Kadeishvili, *Small models for chain algebras*, Mathematische Zeitschrift
  207 (1991), 245--280.
* B. Keller, *Introduction to A-infinity algebras and modules*, Section 3.3.
* M. Kontsevich and Y. Soibelman, *Homological mirror symmetry and torus fibrations*, Section 6.4.
* J.-L. Loday and B. Vallette, *Algebraic Operads*, Chapter 10, Section 10.3.
* S. A. Merkulov, *Strongly homotopy algebras of a Kähler manifold*.
-/

public section

open scoped BigOperators

universe uR uA uH uB uK

namespace TauCeti.AInfinityAlgebra

open ReducedTensorWords

section General

variable {R : Type uR} {A : Type uA} {H : Type uH}
  [CommRing R] [AddCommGroup A] [Module R A] [AddCommGroup H] [Module R H]

/-! ### Suspended operations and higher bar evaluation on morphisms -/

/-- The suspended arity-`n` operation `bₙ : (sA)⊗ⁿ ⟶ sA` of an `A∞` algebra, obtained by
precomposing `𝒜.m n` with the Koszul twists `n - 1 - i` that relate unsuspended operations to the
Taylor map of the bar differential (`taylor_of_tprod`). -/
noncomputable def suspendedM (𝒜 : AInfinityAlgebra R A) (n : ℕ) :
    MultilinearMap (RingHom.id R) (fun _ : Fin n ↦ A) A :=
  (𝒜.m n).compLinearMap fun i ↦ 𝒜.grading.koszulTwist ((n : ℤ) - 1 - i)

/-- The suspended operation in arity zero vanishes. -/
@[simp]
theorem suspendedM_zero (𝒜 : AInfinityAlgebra R A) : 𝒜.suspendedM 0 = 0 := by
  rw [suspendedM, 𝒜.m_zero, MultilinearMap.zero_compLinearMap]

/-- Evaluate the suspended arity-`n` operation through the Koszul-twisted unsuspended operation. -/
theorem suspendedM_apply (𝒜 : AInfinityAlgebra R A) (n : ℕ) (x : Fin n → A) :
    𝒜.suspendedM n x =
      𝒜.m n fun i ↦ 𝒜.grading.koszulTwist ((n : ℤ) - 1 - i) (x i) :=
  MultilinearMap.compLinearMap_apply ..

/-- Reindexing a suspended operation along an equality of arities evaluates on `Fin.cast`. -/
private theorem suspendedM_congr (𝒜 : AInfinityAlgebra R A) {m n : ℕ} (h : m = n)
    (x : Fin n → A) :
    𝒜.suspendedM m (fun i ↦ x (i.cast h)) = 𝒜.suspendedM n x := by
  subst h
  rfl

/-- On a pure tensor word of positive length, the Taylor map evaluates `suspendedM`. -/
theorem taylor_of_tprod_eq_suspendedM (𝒜 : AInfinityAlgebra R A) (n : {n : ℕ // 0 < n})
    (x : Fin n.1 → A) :
    𝒜.taylor (of R A n (PiTensorProduct.tprod R x)) = 𝒜.suspendedM n.1 x :=
  (𝒜.taylor_of_tprod n x).trans (𝒜.suspendedM_apply n.1 x).symm

/-- On a pure tensor word of length at least two, the higher Taylor map evaluates `suspendedM`. -/
theorem higherTaylor_of_tprod_eq_suspendedM (𝒜 : AInfinityAlgebra R A) {n : ℕ} (hn : 2 ≤ n)
    (x : Fin n → A) :
    𝒜.higherTaylor (of R A ⟨n, by omega⟩ (PiTensorProduct.tprod R x)) = 𝒜.suspendedM n x := by
  rw [𝒜.higherTaylor_of ⟨n, by omega⟩ (by dsimp; omega), 𝒜.taylor_of_tprod_eq_suspendedM]

/-- Precomposing `suspendedM n` with the Koszul twists `n - 1 - i` recovers `𝒜.m n`. -/
theorem m_eq_compLinearMap_suspendedM (𝒜 : AInfinityAlgebra R A) (n : ℕ) :
    𝒜.m n = (𝒜.suspendedM n).compLinearMap fun i ↦ 𝒜.grading.koszulTwist ((n : ℤ) - 1 - i) := by
  ext x
  simp only [suspendedM, MultilinearMap.compLinearMap_apply]
  congr 1
  funext i
  rw [← LinearMap.comp_apply (𝒜.grading.koszulTwist _), InternalGrading.koszulTwist_comp_self,
    LinearMap.id_apply]

/-- In positive arity, `suspendedM n` has degree one for the suspended grading
`𝒜.grading.shift 1`. -/
theorem isHomogeneous_suspendedM (𝒜 : AInfinityAlgebra R A) {n : ℕ} (hn : 0 < n) :
    MultilinearMap.IsHomogeneous (𝒜.suspendedM n)
      (fun _ ↦ (𝒜.grading.shift 1).piece) (𝒜.grading.shift 1).piece 1 := by
  rw [MultilinearMap.isHomogeneous_def]
  intro d x hx
  rw [← 𝒜.taylor_of_tprod_eq_suspendedM ⟨n, hn⟩ x]
  exact (𝒜.taylor_isSuspension.isHomogeneous 𝒜.m_degree).map_mem
    (mem_gradedPiece_of_tprod (𝒜.grading.shift 1) hn x d hx)

/-- Evaluating `𝒜.higherTaylor` after the bar map of any `A∞` morphism `f : ℬ ⟶ 𝒜` on a pure
tensor word of positive length expands over all compositions of `n` into at least two blocks,
applying `f.suspendedComponent` on each block and `𝒜.suspendedM` at the root. -/
theorem higherTaylor_barMap_of_tprod (𝒜 : AInfinityAlgebra R A)
    {B : Type uB} [AddCommGroup B] [Module R B] {ℬ : AInfinityAlgebra R B} (f : AInfinityHom ℬ 𝒜)
    {n : ℕ} (hn : 0 < n) (x : Fin n → B) :
    𝒜.higherTaylor (f.barMap (of R B ⟨n, hn⟩ (PiTensorProduct.tprod R x))) =
      ∑ d : {d : Composition n // 2 ≤ d.length},
        𝒜.suspendedM d.1.length
          (fun i ↦ f.suspendedComponent (d.1.blocksFun i) (x ∘ d.1.embedding i)) := by
  rw [f.barMap_eq_coalgHom, coalgHom_of_tprod_eq_sum_composition f.taylor hn x, map_sum]
  have hone (m : ℕ) (hm : 0 < m) (hm1 : m = 1) (z : Fin m → A) :
      of R A ⟨m, hm⟩ (PiTensorProduct.tprod R z) = ofLetter R A (z ⟨0, hm⟩) := by
    subst hm1
    rw [of_tprod_eq_subword R hm z, subword_one R A z hm]
  have hterm (d : Composition n) :
      𝒜.higherTaylor (of R A ⟨d.length, d.length_pos_of_pos hn⟩
          (PiTensorProduct.tprod R fun i ↦
            f.taylor (of R B ⟨d.blocksFun i, d.one_le_blocksFun i⟩
              (PiTensorProduct.tprod R (x ∘ d.embedding i))))) =
        if 2 ≤ d.length then
          𝒜.suspendedM d.length
            (fun i ↦ f.suspendedComponent (d.blocksFun i) (x ∘ d.embedding i))
        else 0 := by
    have harg : (fun i : Fin d.length ↦
        f.taylor (of R B ⟨d.blocksFun i, d.one_le_blocksFun i⟩
          (PiTensorProduct.tprod R (x ∘ d.embedding i)))) =
        fun i ↦ f.suspendedComponent (d.blocksFun i) (x ∘ d.embedding i) :=
      funext fun i ↦ (f.suspendedComponent_apply (d.blocksFun i) (d.one_le_blocksFun i) _).symm
    rw [harg]
    split_ifs with hd
    · exact 𝒜.higherTaylor_of_tprod_eq_suspendedM hd _
    · have hd1 : d.length = 1 := by
        have hpos := d.length_pos_of_pos hn
        omega
      rw [hone d.length (d.length_pos_of_pos hn) hd1 _, ← LinearMap.comp_apply,
        𝒜.higherTaylor_comp_ofLetter, LinearMap.zero_apply]
  simp_rw [hterm, ← Finset.sum_filter]
  exact Finset.sum_subtype (Finset.univ.filter fun d : Composition n ↦ 2 ≤ d.length)
    (fun _ ↦ Finset.mem_filter.trans (and_iff_right (Finset.mem_univ _)))
    (fun d ↦ 𝒜.suspendedM d.length
      (fun i ↦ f.suspendedComponent (d.blocksFun i) (x ∘ d.embedding i)))

/-! ### Suspended and unsuspended planar-tree maps -/

section TreeDefs

variable (𝒜 : AInfinityAlgebra R A) {dA : Module.End R A} {dH : Module.End R H}
  (c : LinearSpecialContraction dA dH)

/-- The **suspended branch map** of a reduced planar tree `t`: a sign-free multilinear map
`H^{t.numLeaves} ⟶ A` applying `c.incl` at a single leaf and `-c.homotopy ∘ 𝒜.suspendedM (k + 2)`
to the child branch maps at an internal node `node k children`. -/
noncomputable def suspendedTreeBranch :
    (t : ReducedPlanarTree) → MultilinearMap (RingHom.id R) (fun _ : Fin t.numLeaves ↦ H) A
  | .leaf => (MultilinearMap.ofSubsingleton (RingHom.id R) H A (0 : Fin 1)) c.incl
  | .node k children =>
      ((-c.homotopy).compMultilinearMap
        ((𝒜.suspendedM (k + 2)).compMultilinearMap fun i ↦
          suspendedTreeBranch (children i))).domDomCongr
        (ReducedPlanarTree.nodeLeavesEquiv k children)

/-- The **suspended operation map** of a reduced planar tree `t`: zero on the single leaf, and
`c.proj ∘ 𝒜.suspendedM (k + 2)` applied to the child branch maps at an internal node
`node k children`. -/
noncomputable def suspendedTreeOperation :
    (t : ReducedPlanarTree) → MultilinearMap (RingHom.id R) (fun _ : Fin t.numLeaves ↦ H) H
  | .leaf => 0
  | .node k children =>
      (c.proj.compMultilinearMap
        ((𝒜.suspendedM (k + 2)).compMultilinearMap fun i ↦
          𝒜.suspendedTreeBranch c (children i))).domDomCongr
        (ReducedPlanarTree.nodeLeavesEquiv k children)

/-- On the single leaf, `suspendedTreeBranch` applies `c.incl` to its sole input. -/
theorem suspendedTreeBranch_leaf :
    𝒜.suspendedTreeBranch c .leaf =
      (MultilinearMap.ofSubsingleton (RingHom.id R) H A (0 : Fin 1)) c.incl := (rfl)

@[simp]
theorem suspendedTreeBranch_leaf_apply (x : Fin ReducedPlanarTree.leaf.numLeaves → H) :
    𝒜.suspendedTreeBranch c .leaf x = c.incl (x ⟨0, by decide⟩) :=
  MultilinearMap.ofSubsingleton_apply_apply ..

/-- Unfold `suspendedTreeBranch` at an internal `(k + 2)`-ary vertex. -/
theorem suspendedTreeBranch_node (k : ℕ) (children : Fin (k + 2) → ReducedPlanarTree) :
    𝒜.suspendedTreeBranch c (.node k children) =
      ((-c.homotopy).compMultilinearMap
        ((𝒜.suspendedM (k + 2)).compMultilinearMap fun i ↦
          𝒜.suspendedTreeBranch c (children i))).domDomCongr
        (ReducedPlanarTree.nodeLeavesEquiv k children) := (rfl)

/-- Evaluate `suspendedTreeBranch` at an internal `(k + 2)`-ary vertex on an input tuple `x`. -/
theorem suspendedTreeBranch_node_apply (k : ℕ) (children : Fin (k + 2) → ReducedPlanarTree)
    (x : Fin (ReducedPlanarTree.node k children).numLeaves → H) :
    𝒜.suspendedTreeBranch c (.node k children) x =
      -c.homotopy (𝒜.suspendedM (k + 2) fun i ↦
        𝒜.suspendedTreeBranch c (children i) fun j ↦
          x (ReducedPlanarTree.nodeLeavesEquiv k children ⟨i, j⟩)) := (rfl)

@[simp]
theorem suspendedTreeOperation_leaf : 𝒜.suspendedTreeOperation c .leaf = 0 := (rfl)

/-- Unfold `suspendedTreeOperation` at an internal `(k + 2)`-ary vertex. -/
theorem suspendedTreeOperation_node (k : ℕ) (children : Fin (k + 2) → ReducedPlanarTree) :
    𝒜.suspendedTreeOperation c (.node k children) =
      (c.proj.compMultilinearMap
        ((𝒜.suspendedM (k + 2)).compMultilinearMap fun i ↦
          𝒜.suspendedTreeBranch c (children i))).domDomCongr
        (ReducedPlanarTree.nodeLeavesEquiv k children) := (rfl)

/-- Evaluate `suspendedTreeOperation` at an internal `(k + 2)`-ary vertex on an input tuple `x`. -/
theorem suspendedTreeOperation_node_apply (k : ℕ) (children : Fin (k + 2) → ReducedPlanarTree)
    (x : Fin (ReducedPlanarTree.node k children).numLeaves → H) :
    𝒜.suspendedTreeOperation c (.node k children) x =
      c.proj (𝒜.suspendedM (k + 2) fun i ↦
        𝒜.suspendedTreeBranch c (children i) fun j ↦
          x (ReducedPlanarTree.nodeLeavesEquiv k children ⟨i, j⟩)) := (rfl)

/-- The **unsuspended branch map** `H^{t.numLeaves} ⟶ A` of a reduced planar tree `t`, obtained
from `suspendedTreeBranch` by precomposing input `l` with the Koszul twist `t.numLeaves - 1 - l`. -/
noncomputable def treeBranch (GH : InternalGrading R H ℤ) (t : ReducedPlanarTree) :
    MultilinearMap (RingHom.id R) (fun _ : Fin t.numLeaves ↦ H) A :=
  (𝒜.suspendedTreeBranch c t).compLinearMap fun l ↦
    GH.koszulTwist ((t.numLeaves : ℤ) - 1 - l)

/-- The **unsuspended operation map** `H^{t.numLeaves} ⟶ H` of a reduced planar tree `t`, obtained
from `suspendedTreeOperation` by precomposing input `l` with the Koszul twist
`t.numLeaves - 1 - l`. -/
noncomputable def treeOperation (GH : InternalGrading R H ℤ) (t : ReducedPlanarTree) :
    MultilinearMap (RingHom.id R) (fun _ : Fin t.numLeaves ↦ H) H :=
  (𝒜.suspendedTreeOperation c t).compLinearMap fun l ↦
    GH.koszulTwist ((t.numLeaves : ℤ) - 1 - l)

@[simp]
theorem treeBranch_leaf_apply (GH : InternalGrading R H ℤ)
    (x : Fin ReducedPlanarTree.leaf.numLeaves → H) :
    𝒜.treeBranch c GH .leaf x = c.incl (x ⟨0, by decide⟩) := by
  change c.incl (GH.koszulTwist ((1 : ℤ) - 1 - (0 : ℕ)) (x ⟨0, by decide⟩)) = _
  simp

/-- On the single leaf, `treeBranch` applies `c.incl` to its sole input. -/
theorem treeBranch_leaf (GH : InternalGrading R H ℤ) :
    𝒜.treeBranch c GH .leaf =
      (MultilinearMap.ofSubsingleton (RingHom.id R) H A (0 : Fin 1)) c.incl := by
  ext x
  exact 𝒜.treeBranch_leaf_apply c GH x

/-- On the single leaf, `treeOperation` vanishes. -/
@[simp]
theorem treeOperation_leaf (GH : InternalGrading R H ℤ) :
    𝒜.treeOperation c GH .leaf = 0 := by
  rw [treeOperation, suspendedTreeOperation_leaf, MultilinearMap.zero_compLinearMap]

private theorem treeBranch_binary_children (GH : InternalGrading R H ℤ)
    (l r : ReducedPlanarTree) (x : Fin (l.numLeaves + r.numLeaves) → H)
    (hbin : (ReducedPlanarTree.node 0 ![l, r]).numLeaves = l.numLeaves + r.numLeaves) :
    (fun i : Fin 2 ↦
      𝒜.treeBranch c GH (![l, r] i)
        (Sigma.curry (γ := fun _ _ ↦ H)
          (fun ij : Σ a : Fin 2, Fin (![l, r] a).numLeaves ↦
            GH.koszulTwist
              (∑ b : Fin 2, if ij.1 < b then (1 - ((![l, r] b).numLeaves : ℤ)) else 0)
              (x (finCongr hbin (ReducedPlanarTree.nodeLeavesEquiv 0 ![l, r] ij)))) i)) =
    ![𝒜.treeBranch c GH l (fun j ↦
        GH.koszulTwist (1 - r.numLeaves) (x (Fin.castAdd r.numLeaves j))),
      𝒜.treeBranch c GH r (fun j ↦ x (Fin.natAdd l.numLeaves j))] := by
  funext i
  fin_cases i
  · change 𝒜.treeBranch c GH l
        (fun j : Fin l.numLeaves ↦
          GH.koszulTwist
            (∑ b : Fin 2, if (0 : Fin 2) < b then (1 - ((![l, r] b).numLeaves : ℤ)) else 0)
            (x (finCongr hbin (ReducedPlanarTree.nodeLeavesEquiv 0 ![l, r] ⟨0, j⟩)))) =
      𝒜.treeBranch c GH l (fun j ↦
        GH.koszulTwist (1 - r.numLeaves) (x (Fin.castAdd r.numLeaves j)))
    congr 1
    funext j
    have hsum0 :
        (∑ b : Fin 2, if (0 : Fin 2) < b then (1 - ((![l, r] b).numLeaves : ℤ)) else 0) =
          1 - r.numLeaves := by
      rw [Fin.sum_univ_two]
      simp
    rw [hsum0]
    congr 2
    apply Fin.ext
    simp
  · change 𝒜.treeBranch c GH r
        (fun j : Fin r.numLeaves ↦
          GH.koszulTwist
            (∑ b : Fin 2, if (1 : Fin 2) < b then (1 - ((![l, r] b).numLeaves : ℤ)) else 0)
            (x (finCongr hbin (ReducedPlanarTree.nodeLeavesEquiv 0 ![l, r] ⟨1, j⟩)))) =
      𝒜.treeBranch c GH r (fun j ↦ x (Fin.natAdd l.numLeaves j))
    congr 1
    funext j
    have hsum1 :
        (∑ b : Fin 2, if (1 : Fin 2) < b then (1 - ((![l, r] b).numLeaves : ℤ)) else 0) = 0 := by
      rw [Fin.sum_univ_two]
      simp
    rw [hsum1, GH.koszulTwist_zero, LinearMap.id_apply]
    congr 1

private theorem suspendedM_ofComposition_apply {n : ℕ} (d : Composition n) (hd : 2 ≤ d.length)
    (children : ∀ i : Fin d.length, ReducedPlanarTree.Arity (d.blocksFun i)) (x : Fin n → H)
    (hnode :
      (ReducedPlanarTree.node (d.length - 2)
        fun i ↦ (children (i.cast (Nat.sub_add_cancel hd))).val).numLeaves = n) :
    𝒜.suspendedM (d.length - 2 + 2)
      (fun i ↦ (𝒜.suspendedTreeBranch c (children (i.cast (Nat.sub_add_cancel hd))).val)
        fun j ↦ x (finCongr hnode
          (ReducedPlanarTree.nodeLeavesEquiv (d.length - 2)
            (fun i ↦ (children (i.cast (Nat.sub_add_cancel hd))).val) ⟨i, j⟩))) =
    𝒜.suspendedM d.length fun i ↦
      ((𝒜.suspendedTreeBranch c (children i).val).domDomCongr
        (finCongr (children i).property)) (x ∘ d.embedding i) := by
  have hlen : d.length - 2 + 2 = d.length := Nat.sub_add_cancel hd
  rw [← 𝒜.suspendedM_congr hlen]
  refine congrArg (𝒜.suspendedM (d.length - 2 + 2)) ?_
  funext i
  rw [MultilinearMap.domDomCongr_apply]
  refine congrArg (𝒜.suspendedTreeBranch c (children (i.cast hlen)).val) ?_
  funext j
  simp only [finCongr_apply, Function.comp_apply]
  congr 1
  apply Fin.ext
  rw [Fin.val_cast, ReducedPlanarTree.coe_nodeLeavesEquiv_apply, d.coe_embedding, Fin.val_cast]
  have hsum :
      (∑ a : Fin i.1, (children ((Fin.castLE i.2.le a).cast hlen)).val.numLeaves) =
        d.sizeUpTo i.1 := by
    rw [d.sizeUpTo_eq_sum_blocksFun (by omega : i.1 ≤ d.length)]
    exact Finset.sum_congr rfl fun a _ ↦ (children _).property
  exact congrArg (· + j.1) hsum

/-- Evaluating `suspendedTreeBranch` on `ReducedPlanarTree.ofComposition` applies
`-c.homotopy ∘ 𝒜.suspendedM d.length` to the child branch evaluations on `x ∘ d.embedding i`. -/
theorem suspendedTreeBranch_ofComposition {n : ℕ} (d : Composition n) (hd : 2 ≤ d.length)
    (children : ∀ i : Fin d.length, ReducedPlanarTree.Arity (d.blocksFun i)) (x : Fin n → H) :
    ((𝒜.suspendedTreeBranch c (ReducedPlanarTree.ofComposition d hd children).val).domDomCongr
        (finCongr (ReducedPlanarTree.ofComposition d hd children).property)) x =
      -c.homotopy (𝒜.suspendedM d.length fun i ↦
        ((𝒜.suspendedTreeBranch c (children i).val).domDomCongr
          (finCongr (children i).property)) (x ∘ d.embedding i)) := by
  have hnode :
      (ReducedPlanarTree.node (d.length - 2)
        fun i ↦ (children (i.cast (Nat.sub_add_cancel hd))).val).numLeaves = n :=
    (ReducedPlanarTree.ofComposition d hd children).property
  refine (𝒜.suspendedTreeBranch_node_apply c (d.length - 2)
    (fun i ↦ (children (i.cast (Nat.sub_add_cancel hd))).val)
    (fun i ↦ x (finCongr hnode i))).trans ?_
  exact congrArg (fun z ↦ -c.homotopy z) (suspendedM_ofComposition_apply 𝒜 c d hd children x hnode)

/-- Evaluating `suspendedTreeOperation` on `ReducedPlanarTree.ofComposition` applies
`c.proj ∘ 𝒜.suspendedM d.length` to the child branch evaluations on `x ∘ d.embedding i`. -/
theorem suspendedTreeOperation_ofComposition {n : ℕ} (d : Composition n) (hd : 2 ≤ d.length)
    (children : ∀ i : Fin d.length, ReducedPlanarTree.Arity (d.blocksFun i)) (x : Fin n → H) :
    ((𝒜.suspendedTreeOperation c (ReducedPlanarTree.ofComposition d hd children).val).domDomCongr
        (finCongr (ReducedPlanarTree.ofComposition d hd children).property)) x =
      c.proj (𝒜.suspendedM d.length fun i ↦
        ((𝒜.suspendedTreeBranch c (children i).val).domDomCongr
          (finCongr (children i).property)) (x ∘ d.embedding i)) := by
  have hnode :
      (ReducedPlanarTree.node (d.length - 2)
        fun i ↦ (children (i.cast (Nat.sub_add_cancel hd))).val).numLeaves = n :=
    (ReducedPlanarTree.ofComposition d hd children).property
  refine (𝒜.suspendedTreeOperation_node_apply c (d.length - 2)
    (fun i ↦ (children (i.cast (Nat.sub_add_cancel hd))).val)
    (fun i ↦ x (finCongr hnode i))).trans ?_
  exact congrArg c.proj (suspendedM_ofComposition_apply 𝒜 c d hd children x hnode)

end TreeDefs

/-! ### Homogeneity and Koszul-signed unsuspended node formulas -/

/-- Split a `Fin m`-indexed integer sum at `i : Fin m` into the prefix before `i`, the `i`-th term,
and the suffix strictly after `i`. -/
private theorem sum_fin_split {m : ℕ} (f : Fin m → ℤ) (i : Fin m) :
    (∑ a : Fin m, f a) =
      (∑ a : Fin i.1, f (Fin.castLE i.2.le a)) + f i +
        ∑ b : Fin m, if i < b then f b else 0 := by
  have hpre :
      (∑ a : Fin i.1, f (Fin.castLE i.2.le a)) =
        ∑ a : Fin m, if a < i then f a else 0 := by
    rw [← Finset.sum_filter]
    refine Finset.sum_bij (fun (a : Fin i.1) _ ↦ Fin.castLE i.2.le a) ?_ ?_ ?_ ?_
    · intro a _
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, a.2⟩
    · intro a₁ _ a₂ _ h
      exact Fin.ext (by simpa using congrArg Fin.val h)
    · intro b hb
      exact ⟨⟨b.1, (Finset.mem_filter.mp hb).2⟩, Finset.mem_univ _, rfl⟩
    · intro _ _
      rfl
  rw [hpre]
  have hpoint (a : Fin m) :
      f a = (if a < i then f a else 0) + (if a = i then f a else 0) +
        (if i < a then f a else 0) := by
    rcases lt_trichotomy a i with hlt | rfl | hgt
    · simp [hlt, lt_asymm hlt, ne_of_lt hlt]
    · simp
    · simp [hgt, lt_asymm hgt, ne_of_gt hgt]
  conv_lhs => rw [show (∑ a : Fin m, f a) = ∑ a : Fin m,
    ((if a < i then f a else 0) + (if a = i then f a else 0) + (if i < a then f a else 0)) from
    Finset.sum_congr rfl fun a _ ↦ hpoint a]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  simp

/-- Rearrange the slotwise Koszul twist exponents at an internal `(k + 2)`-ary tree vertex into the
intrinsic vertex sign `∑ i, (k + 1 - i) * (1 - nᵢ)`, the prefix degree sign of
`signedCompMultilinearMap`, and an even correction `2 * ∑_{b > i} n_b * d_{i,j}`. -/
private theorem unsuspend_node_sign_eq (k : ℕ) (children : Fin (k + 2) → ReducedPlanarTree)
    (d : (Σ i : Fin (k + 2), Fin (children i).numLeaves) → ℤ) :
    (∑ i : Fin (k + 2),
      (((k + 2 : ℤ) - 1 - i) * (1 - (children i).numLeaves) +
        ∑ j : Fin (children i).numLeaves,
          (((k + 2 : ℤ) - 1 - i) +
            ∑ b : Fin (k + 2), if i < b then ((children b).numLeaves : ℤ) else 0) * d ⟨i, j⟩)) =
    ((∑ i : Fin (k + 2), ((k + 2 : ℤ) - 1 - i) * (1 - (children i).numLeaves)) +
      ∑ ij : Σ i : Fin (k + 2), Fin (children i).numLeaves,
        (∑ b : Fin (k + 2), if ij.1 < b then (1 - ((children b).numLeaves : ℤ)) else 0) *
          d ij) +
      2 * ∑ ij : Σ i : Fin (k + 2), Fin (children i).numLeaves,
        (∑ b : Fin (k + 2), if ij.1 < b then ((children b).numLeaves : ℤ) else 0) * d ij := by
  rw [Finset.sum_add_distrib, Fintype.sum_sigma, Fintype.sum_sigma, add_assoc]
  congr 1
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  have hcard : ((k + 2 : ℤ) - 1 - i) = ∑ b : Fin (k + 2), if i < b then (1 : ℤ) else 0 := by
    have h1 := sum_fin_split (fun _ : Fin (k + 2) ↦ (1 : ℤ)) i
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one,
      Nat.cast_add, Nat.cast_ofNat] at h1
    linarith
  have hsum1 :
      (∑ b : Fin (k + 2), if i < b then (1 - ((children b).numLeaves : ℤ)) else 0) +
        2 * (∑ b : Fin (k + 2), if i < b then ((children b).numLeaves : ℤ) else 0) =
      ((k + 2 : ℤ) - 1 - i) +
        ∑ b : Fin (k + 2), if i < b then ((children b).numLeaves : ℤ) else 0 := by
    rw [hcard, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun b _ ↦ ?_
    split_ifs <;> ring
  calc (((k + 2 : ℤ) - 1 - i) +
          ∑ b : Fin (k + 2), if i < b then ((children b).numLeaves : ℤ) else 0) * d ⟨i, j⟩
      = ((∑ b : Fin (k + 2), if i < b then (1 - ((children b).numLeaves : ℤ)) else 0) +
          2 * (∑ b : Fin (k + 2), if i < b then ((children b).numLeaves : ℤ) else 0)) *
            d ⟨i, j⟩ := by rw [hsum1]
    _ = (∑ b : Fin (k + 2), if i < b then (1 - ((children b).numLeaves : ℤ)) else 0) * d ⟨i, j⟩ +
          2 * ((∑ b : Fin (k + 2), if i < b then ((children b).numLeaves : ℤ) else 0) *
            d ⟨i, j⟩) := by ring

section HomogeneousTree

variable (𝒜 : AInfinityAlgebra R A) {GH : InternalGrading R H ℤ}
  {dA : Module.End R A} {dH : Module.End R H} (c : LinearSpecialContraction dA dH)
  (hh : LinearMap.IsHomogeneous c.homotopy 𝒜.grading.piece 𝒜.grading.piece (-1))
  (hincl : LinearMap.IsHomogeneous c.incl GH.piece 𝒜.grading.piece 0)
  (hproj : LinearMap.IsHomogeneous c.proj 𝒜.grading.piece GH.piece 0)

section BranchHomogeneous

include hh hincl

/-- The suspended branch map of every reduced planar tree has degree zero between the suspended
gradings `(GH.shift 1).piece` and `(𝒜.grading.shift 1).piece`. -/
theorem isHomogeneous_suspendedTreeBranch (t : ReducedPlanarTree) :
    MultilinearMap.IsHomogeneous (𝒜.suspendedTreeBranch c t)
      (fun _ ↦ (GH.shift 1).piece) (𝒜.grading.shift 1).piece 0 := by
  induction t with
  | leaf =>
    rw [MultilinearMap.isHomogeneous_def]
    intro d x hx
    have hd : (∑ i, d i) = d ⟨0, by decide⟩ := Fin.sum_univ_one d
    rw [suspendedTreeBranch_leaf_apply, hd]
    simpa only [add_zero] using
      (LinearMap.isHomogeneous_shift_piece_iff.2 hincl).map_mem (hx ⟨0, by decide⟩)
  | node k children ih =>
    rw [suspendedTreeBranch_node]
    have hinner := (𝒜.isHomogeneous_suspendedM (Nat.succ_pos (k + 1))).compMultilinearMap ih
    simp only [Finset.sum_const_zero, zero_add] at hinner
    have hnh : LinearMap.IsHomogeneous (-c.homotopy)
        (𝒜.grading.shift 1).piece (𝒜.grading.shift 1).piece (-1) :=
      (LinearMap.isHomogeneous_shift_piece_iff.2 hh).neg
    have hcomp : MultilinearMap.IsHomogeneous
        ((-c.homotopy).compMultilinearMap
          ((𝒜.suspendedM (k + 2)).compMultilinearMap fun i ↦
            𝒜.suspendedTreeBranch c (children i)))
        (fun _ ↦ (GH.shift 1).piece) (𝒜.grading.shift 1).piece 0 := by
      simpa only [add_neg_cancel] using hnh.compMultilinearMap hinner
    convert hcomp.domDomCongrLinearEquiv' (ReducedPlanarTree.nodeLeavesEquiv k children) using 1
    ext x
    simp only [MultilinearMap.domDomCongr_apply,
      _root_.MultilinearMap.domDomCongrLinearEquiv'_apply, _root_.MultilinearMap.coe_mk,
      Function.comp_apply]
    congr 1; funext ij; simp

/-- The unsuspended branch map of a reduced planar tree `t` is homogeneous of cohomological degree
`1 - t.numLeaves`. -/
theorem isHomogeneous_treeBranch (t : ReducedPlanarTree) :
    MultilinearMap.IsHomogeneous (𝒜.treeBranch c GH t)
      (fun _ ↦ GH.piece) 𝒜.grading.piece (1 - t.numLeaves) := by
  have hH : (GH.shift 1).piece = Graded.shift GH.piece (1 : ℤ) := by
    funext p
    rw [InternalGrading.shift_piece, Graded.shift_apply]
  have hA : (𝒜.grading.shift 1).piece = Graded.shift 𝒜.grading.piece (1 : ℤ) := by
    funext p
    rw [InternalGrading.shift_piece, Graded.shift_apply]
  have hs : MultilinearMap.IsHomogeneous (𝒜.suspendedTreeBranch c t)
      (fun _ ↦ GH.piece) 𝒜.grading.piece (1 - t.numLeaves) := by
    have h := MultilinearMap.isHomogeneous_shift_const_iff.1
      (hH ▸ hA ▸ 𝒜.isHomogeneous_suspendedTreeBranch c hh hincl t)
    simpa [show (0 : ℤ) + 1 - t.numLeaves = 1 - t.numLeaves by ring] using h
  have htwist : ∀ l : Fin t.numLeaves, LinearMap.IsHomogeneous
      (GH.koszulTwist ((t.numLeaves : ℤ) - 1 - l)) GH.piece GH.piece 0 := by
    intro l
    rw [LinearMap.isHomogeneous_def]
    intro p x hx
    simpa only [add_zero] using GH.koszulTwist_mem_piece hx _
  simpa [treeBranch] using hs.compLinearMap htwist

/-- Evaluate the `i`-th Koszul-twisted child branch on homogeneous inputs of the whole node in
terms of the unsuspended child branch `treeBranch`. -/
private theorem koszulTwist_suspendedTreeBranch_apply (k : ℕ)
    (children : Fin (k + 2) → ReducedPlanarTree)
    (d : (Σ a : Fin (k + 2), Fin (children a).numLeaves) → ℤ)
    (x : (Σ a : Fin (k + 2), Fin (children a).numLeaves) → H)
    (hx : ∀ ij, x ij ∈ GH.piece (d ij)) (i : Fin (k + 2)) :
    𝒜.grading.koszulTwist (((k + 2 : ℕ) : ℤ) - 1 - i)
      (𝒜.suspendedTreeBranch c (children i)
        (Sigma.curry (γ := fun _ _ ↦ H)
          (fun ij ↦ GH.koszulTwist (((ReducedPlanarTree.node k children).numLeaves : ℤ) - 1 -
            (ReducedPlanarTree.nodeLeavesEquiv k children ij : ℕ)) (x ij)) i)) =
      negOnePowCast R
        (((k + 2 : ℤ) - 1 - i) * (1 - (children i).numLeaves) +
          ∑ j : Fin (children i).numLeaves,
            (((k + 2 : ℤ) - 1 - i) +
              ∑ b : Fin (k + 2), if i < b then ((children b).numLeaves : ℤ) else 0) *
              d ⟨i, j⟩) •
        𝒜.treeBranch c GH (children i) (fun j ↦ x ⟨i, j⟩) := by
  rw [Nat.cast_add, Nat.cast_ofNat,
    show Sigma.curry (γ := fun _ _ ↦ H)
        (fun ij ↦ GH.koszulTwist (((ReducedPlanarTree.node k children).numLeaves : ℤ) - 1 -
          (ReducedPlanarTree.nodeLeavesEquiv k children ij : ℕ)) (x ij)) i =
      fun j ↦ GH.koszulTwist (((ReducedPlanarTree.node k children).numLeaves : ℤ) - 1 -
        (ReducedPlanarTree.nodeLeavesEquiv k children ⟨i, j⟩ : ℕ)) (x ⟨i, j⟩) from rfl]
  let R_i : ℤ := ∑ b : Fin (k + 2), if i < b then ((children b).numLeaves : ℤ) else 0
  have hparam (j : Fin (children i).numLeaves) :
      (((ReducedPlanarTree.node k children).numLeaves : ℤ) - 1 -
        (ReducedPlanarTree.nodeLeavesEquiv k children ⟨i, j⟩ : ℕ)) =
        (((children i).numLeaves : ℤ) - 1 - j) + R_i := by
    have hsplit := sum_fin_split (fun a : Fin (k + 2) ↦ ((children a).numLeaves : ℤ)) i
    rw [ReducedPlanarTree.coe_nodeLeavesEquiv_apply, ReducedPlanarTree.numLeaves_node,
      Nat.cast_sum, hsplit, Nat.cast_add, Nat.cast_sum]
    dsimp only [R_i]
    ring
  have htw (j : Fin (children i).numLeaves) :
      GH.koszulTwist (((ReducedPlanarTree.node k children).numLeaves : ℤ) - 1 -
        (ReducedPlanarTree.nodeLeavesEquiv k children ⟨i, j⟩ : ℕ)) (x ⟨i, j⟩) =
        negOnePowCast R (R_i * d ⟨i, j⟩) •
          GH.koszulTwist (((children i).numLeaves : ℤ) - 1 - j) (x ⟨i, j⟩) := by
    rw [hparam j, ← GH.koszulTwist_comp, LinearMap.comp_apply,
      GH.koszulTwist_apply_of_mem (hx ⟨i, j⟩), map_smul, negOnePowCast_eq_intCast]
  simp_rw [htw]
  rw [MultilinearMap.map_smul_univ]
  simp only [RingHom.id_apply]
  rw [← negOnePowCast_sum, show 𝒜.suspendedTreeBranch c (children i)
      (fun j ↦ GH.koszulTwist (((children i).numLeaves : ℤ) - 1 - j) (x ⟨i, j⟩)) =
      𝒜.treeBranch c GH (children i) (fun j ↦ x ⟨i, j⟩) from rfl, map_smul,
    𝒜.grading.koszulTwist_apply_of_mem
      ((𝒜.isHomogeneous_treeBranch c hh hincl (children i)).map_mem
        (fun j ↦ d ⟨i, j⟩) (fun j ↦ x ⟨i, j⟩) fun j ↦ hx ⟨i, j⟩),
    ← negOnePowCast_eq_intCast, smul_smul, ← negOnePowCast_add]
  congr 2
  rw [mul_add, ← add_assoc, Finset.mul_sum, ← Finset.sum_add_distrib]
  have hsub (j : Fin (children i).numLeaves) :
      R_i * d ⟨i, j⟩ + ((k + 2 : ℤ) - 1 - i) * d ⟨i, j⟩ =
        (((k + 2 : ℤ) - 1 - i) + R_i) * d ⟨i, j⟩ := by ring
  simp_rw [hsub]
  ring

/-- Core Koszul-sign identity relating the unsuspended evaluation of `𝒜.suspendedM (k + 2)` on
`suspendedTreeBranch` children to `InternalGrading.signedCompMultilinearMap` on `𝒜.m (k + 2)` and
`treeBranch` children. -/
private theorem unsuspend_suspendedM_comp_suspendedTreeBranch (k : ℕ)
    (children : Fin (k + 2) → ReducedPlanarTree) :
    (((𝒜.suspendedM (k + 2)).compMultilinearMap fun i ↦
        𝒜.suspendedTreeBranch c (children i)).domDomCongr
        (ReducedPlanarTree.nodeLeavesEquiv k children)).compLinearMap
        (fun l ↦ GH.koszulTwist (((ReducedPlanarTree.node k children).numLeaves : ℤ) - 1 - l)) =
      negOnePowCast R
        (∑ i : Fin (k + 2), ((k + 2 : ℤ) - 1 - i) * (1 - (children i).numLeaves)) •
      (InternalGrading.signedCompMultilinearMap
        (fun (_ : Fin (k + 2)) _ ↦ GH)
        (fun _ ↦ 𝒜.grading.piece)
        𝒜.grading.piece
        ⟨𝒜.m (k + 2), MultilinearMap.mem_homogeneousSubmodule.mpr (𝒜.m_degree (k + 2) (by omega))⟩
        (fun i ↦ ⟨𝒜.treeBranch c GH (children i),
          MultilinearMap.mem_homogeneousSubmodule.mpr
            (𝒜.isHomogeneous_treeBranch c hh hincl (children i))⟩)).val.domDomCongr
        (ReducedPlanarTree.nodeLeavesEquiv k children) := by
  suffices hsigma :
      (((𝒜.suspendedM (k + 2)).compMultilinearMap fun i ↦
          𝒜.suspendedTreeBranch c (children i)).compLinearMap
        fun ij ↦ GH.koszulTwist
          (((ReducedPlanarTree.node k children).numLeaves : ℤ) - 1 -
            (ReducedPlanarTree.nodeLeavesEquiv k children ij : ℕ))) =
      negOnePowCast R
        (∑ i : Fin (k + 2), ((k + 2 : ℤ) - 1 - i) * (1 - (children i).numLeaves)) •
      (InternalGrading.signedCompMultilinearMap
        (fun (_ : Fin (k + 2)) _ ↦ GH) (fun _ ↦ 𝒜.grading.piece) 𝒜.grading.piece
        ⟨𝒜.m (k + 2), MultilinearMap.mem_homogeneousSubmodule.mpr (𝒜.m_degree (k + 2) (by omega))⟩
        (fun i ↦ ⟨𝒜.treeBranch c GH (children i),
          MultilinearMap.mem_homogeneousSubmodule.mpr
            (𝒜.isHomogeneous_treeBranch c hh hincl (children i))⟩)).val by
    ext x
    exact congrArg (· fun ij ↦ x (ReducedPlanarTree.nodeLeavesEquiv k children ij)) hsigma
  apply InternalGrading.multilinearMap_ext (fun _ ↦ GH)
  intro d x hx
  rw [smul_apply,
    InternalGrading.signedCompMultilinearMap_apply
      (fun (_ : Fin (k + 2)) _ ↦ GH) (fun _ ↦ 𝒜.grading.piece) 𝒜.grading.piece _ _ d x hx,
    smul_smul, ← negOnePowCast_add, MultilinearMap.compLinearMap_apply,
    MultilinearMap.compMultilinearMap_apply, suspendedM_apply,
    funext (koszulTwist_suspendedTreeBranch_apply 𝒜 c hh hincl k children d x hx),
    MultilinearMap.map_smul_univ]
  simp only [RingHom.id_apply]
  rw [← negOnePowCast_sum, unsuspend_node_sign_eq k children d, negOnePowCast_add,
    negOnePowCast_two_mul, mul_one]

/-- **Unsuspended recursion for `treeBranch` at an internal vertex**: it applies `-c.homotopy` to
the Koszul-signed substitution (`InternalGrading.signedCompMultilinearMap`) of the child branch
maps into `𝒜.m (k + 2)`, multiplied by `(-1) ^ ∑ i, (k + 1 - i) * (1 - (children i).numLeaves)`. -/
theorem treeBranch_node (k : ℕ) (children : Fin (k + 2) → ReducedPlanarTree) :
    𝒜.treeBranch c GH (.node k children) =
      negOnePowCast R
        (∑ i : Fin (k + 2), ((k + 2 : ℤ) - 1 - i) * (1 - (children i).numLeaves)) •
      ((-c.homotopy).compMultilinearMap
        (InternalGrading.signedCompMultilinearMap
          (fun (_ : Fin (k + 2)) _ ↦ GH)
          (fun _ ↦ 𝒜.grading.piece)
          𝒜.grading.piece
          ⟨𝒜.m (k + 2), MultilinearMap.mem_homogeneousSubmodule.mpr
            (𝒜.m_degree (k + 2) (by omega))⟩
          (fun i ↦ ⟨𝒜.treeBranch c GH (children i),
            MultilinearMap.mem_homogeneousSubmodule.mpr
              (𝒜.isHomogeneous_treeBranch c hh hincl (children i))⟩)).val).domDomCongr
        (ReducedPlanarTree.nodeLeavesEquiv k children) := by
  have hcore := unsuspend_suspendedM_comp_suspendedTreeBranch 𝒜 c hh hincl k children
  ext x
  have hx := congrArg (fun M ↦ -c.homotopy (M x)) hcore
  refine hx.trans ?_
  rw [smul_apply, smul_apply, map_smul, ← smul_neg]
  rfl

/-- **Unsuspended recursion for `treeOperation` at an internal vertex**: it applies `c.proj` to the
Koszul-signed substitution (`InternalGrading.signedCompMultilinearMap`) of the child branch maps
into `𝒜.m (k + 2)`, multiplied by `(-1) ^ ∑ i, (k + 1 - i) * (1 - (children i).numLeaves)`. -/
theorem treeOperation_node (k : ℕ) (children : Fin (k + 2) → ReducedPlanarTree) :
    𝒜.treeOperation c GH (.node k children) =
      negOnePowCast R
        (∑ i : Fin (k + 2), ((k + 2 : ℤ) - 1 - i) * (1 - (children i).numLeaves)) •
      (c.proj.compMultilinearMap
        (InternalGrading.signedCompMultilinearMap
          (fun (_ : Fin (k + 2)) _ ↦ GH)
          (fun _ ↦ 𝒜.grading.piece)
          𝒜.grading.piece
          ⟨𝒜.m (k + 2), MultilinearMap.mem_homogeneousSubmodule.mpr
            (𝒜.m_degree (k + 2) (by omega))⟩
          (fun i ↦ ⟨𝒜.treeBranch c GH (children i),
            MultilinearMap.mem_homogeneousSubmodule.mpr
              (𝒜.isHomogeneous_treeBranch c hh hincl (children i))⟩)).val).domDomCongr
        (ReducedPlanarTree.nodeLeavesEquiv k children) := by
  have hcore := unsuspend_suspendedM_comp_suspendedTreeBranch 𝒜 c hh hincl k children
  ext x
  have hx := congrArg (fun M ↦ c.proj (M x)) hcore
  refine hx.trans ?_
  rw [smul_apply, smul_apply, map_smul]
  rfl

/-- **Unsuspended recursion for `treeBranch` on a binary vertex `binary l r`**: the left inputs are
twisted by `1 - r.numLeaves` from moving the right branch past them, and the overall sign is
`(-1) ^ (1 - l.numLeaves)`. -/
theorem treeBranch_binary (l r : ReducedPlanarTree)
    (x : Fin (l.numLeaves + r.numLeaves) → H) :
    ((𝒜.treeBranch c GH (.binary l r)).domDomCongr
        (finCongr (ReducedPlanarTree.numLeaves_binary l r))) x =
      negOnePowCast R (1 - l.numLeaves) •
        (-c.homotopy (𝒜.m 2
          ![𝒜.treeBranch c GH l (fun j ↦
              GH.koszulTwist (1 - r.numLeaves) (x (Fin.castAdd r.numLeaves j))),
            𝒜.treeBranch c GH r (fun j ↦ x (Fin.natAdd l.numLeaves j))])) := by
  have hbin : (ReducedPlanarTree.node 0 ![l, r]).numLeaves = l.numLeaves + r.numLeaves :=
    ReducedPlanarTree.numLeaves_binary l r
  have hnode := congrArg (· fun i ↦ x (finCongr hbin i))
    (𝒜.treeBranch_node c hh hincl 0 ![l, r])
  refine hnode.trans ?_
  rw [smul_apply, MultilinearMap.domDomCongr_apply, LinearMap.compMultilinearMap_apply,
    LinearMap.neg_apply, InternalGrading.signedCompMultilinearMap_val,
    MultilinearMap.compLinearMap_apply, MultilinearMap.compMultilinearMap_apply]
  have hexp :
      (∑ i : Fin 2, (((0 : ℕ) : ℤ) + 2 - 1 - i) * (1 - (![l, r] i).numLeaves)) =
        1 - l.numLeaves := by
    rw [Fin.sum_univ_two]
    simp
  rw [hexp]
  exact congrArg (fun v ↦ negOnePowCast R (1 - l.numLeaves) • (-c.homotopy (𝒜.m 2 v)))
    (treeBranch_binary_children 𝒜 c GH l r x hbin)

/-- **Unsuspended recursion for `treeOperation` on a binary vertex `binary l r`**: the left inputs
are twisted by `1 - r.numLeaves` from moving the right branch past them, and the overall sign is
`(-1) ^ (1 - l.numLeaves)`. -/
theorem treeOperation_binary (l r : ReducedPlanarTree)
    (x : Fin (l.numLeaves + r.numLeaves) → H) :
    ((𝒜.treeOperation c GH (.binary l r)).domDomCongr
        (finCongr (ReducedPlanarTree.numLeaves_binary l r))) x =
      negOnePowCast R (1 - l.numLeaves) •
        c.proj (𝒜.m 2
          ![𝒜.treeBranch c GH l (fun j ↦
              GH.koszulTwist (1 - r.numLeaves) (x (Fin.castAdd r.numLeaves j))),
            𝒜.treeBranch c GH r (fun j ↦ x (Fin.natAdd l.numLeaves j))]) := by
  have hbin : (ReducedPlanarTree.node 0 ![l, r]).numLeaves = l.numLeaves + r.numLeaves :=
    ReducedPlanarTree.numLeaves_binary l r
  have hnode := congrArg (· fun i ↦ x (finCongr hbin i))
    (𝒜.treeOperation_node c hh hincl 0 ![l, r])
  refine hnode.trans ?_
  rw [smul_apply, MultilinearMap.domDomCongr_apply, LinearMap.compMultilinearMap_apply,
    InternalGrading.signedCompMultilinearMap_val, MultilinearMap.compLinearMap_apply,
    MultilinearMap.compMultilinearMap_apply]
  have hexp :
      (∑ i : Fin 2, (((0 : ℕ) : ℤ) + 2 - 1 - i) * (1 - (![l, r] i).numLeaves)) =
        1 - l.numLeaves := by
    rw [Fin.sum_univ_two]
    simp
  rw [hexp]
  exact congrArg (fun v ↦ negOnePowCast R (1 - l.numLeaves) • c.proj (𝒜.m 2 v))
    (treeBranch_binary_children 𝒜 c GH l r x hbin)

end BranchHomogeneous

section Corolla

include hincl

private theorem corolla_suspendedM_apply (k : ℕ) (x : Fin (k + 2) → H)
    (hcor : (ReducedPlanarTree.node k fun _ ↦ .leaf).numLeaves = k + 2) :
    𝒜.suspendedM (k + 2)
      (fun i ↦ (𝒜.suspendedTreeBranch c .leaf) fun j ↦
        GH.koszulTwist
          (((ReducedPlanarTree.node k fun _ ↦ .leaf).numLeaves : ℤ) - 1 -
            (ReducedPlanarTree.nodeLeavesEquiv k (fun _ ↦ .leaf) ⟨i, j⟩ : ℕ))
          (x (finCongr hcor
            (ReducedPlanarTree.nodeLeavesEquiv k (fun _ ↦ .leaf) ⟨i, j⟩)))) =
      𝒜.m (k + 2) fun i ↦ c.incl (x i) := by
  rw [suspendedM_apply]
  congr 1
  funext i
  rw [suspendedTreeBranch_leaf_apply, finCongr_apply]
  have hidx :
      Fin.cast hcor
        (ReducedPlanarTree.nodeLeavesEquiv k (fun _ ↦ .leaf) ⟨i, ⟨0, by decide⟩⟩) = i := by
    apply Fin.ext
    simp
  have hparam :
      (((ReducedPlanarTree.node k fun _ ↦ .leaf).numLeaves : ℤ) - 1 -
        (ReducedPlanarTree.nodeLeavesEquiv k (fun _ ↦ .leaf) ⟨i, ⟨0, by decide⟩⟩ : ℕ)) =
        (k + 2 : ℤ) - 1 - i := by
    simp
  rw [hidx, hparam]
  simpa [mul_zero] using hincl.koszulTwist_apply ((k + 2 : ℤ) - 1 - i)
    (GH.koszulTwist ((k + 2 : ℤ) - 1 - i) (x i))

/-- On the `(k + 2)`-input corolla, `treeBranch` applies `-c.homotopy ∘ 𝒜.m (k + 2)` to the
included inputs with no extra Koszul signs. -/
theorem treeBranch_corolla (k : ℕ) (x : Fin (k + 2) → H) :
    ((𝒜.treeBranch c GH (.corolla k)).domDomCongr
        (finCongr (ReducedPlanarTree.numLeaves_corolla k))) x =
      -c.homotopy (𝒜.m (k + 2) fun i ↦ c.incl (x i)) := by
  have hcor : (ReducedPlanarTree.node k fun _ ↦ .leaf).numLeaves = k + 2 :=
    ReducedPlanarTree.numLeaves_corolla k
  change (𝒜.suspendedTreeBranch c (.node k fun _ ↦ .leaf))
      (fun i ↦ GH.koszulTwist (((ReducedPlanarTree.node k fun _ ↦ .leaf).numLeaves : ℤ) - 1 - i)
        (x (finCongr hcor i))) = _
  rw [suspendedTreeBranch_node_apply, corolla_suspendedM_apply 𝒜 c hincl k x hcor]

/-- Evaluate `treeBranch` on the binary corolla `corolla 0` directly without an external
`domDomCongr`. -/
private theorem treeBranch_corolla_zero_apply
    (f : Fin (ReducedPlanarTree.corolla 0).numLeaves → H) :
    𝒜.treeBranch c GH (.corolla 0) f =
      -c.homotopy (𝒜.m 2 ![c.incl (f ⟨0, by decide⟩), c.incl (f ⟨1, by decide⟩)]) := by
  let x : Fin 2 → H := ![f ⟨0, by decide⟩, f ⟨1, by decide⟩]
  have hf : f = fun j ↦ x (finCongr (ReducedPlanarTree.numLeaves_corolla 0) j) := by
    funext ⟨i, hi⟩
    rcases i with _ | _ | i
    · rfl
    · rfl
    · exfalso; rw [ReducedPlanarTree.numLeaves_corolla] at hi; omega
  rw [hf, ← MultilinearMap.domDomCongr_apply, 𝒜.treeBranch_corolla c hincl 0 x]
  refine congrArg (fun v ↦ -c.homotopy (𝒜.m 2 v)) ?_
  funext i
  fin_cases i <;> rfl

/-- On the `(k + 2)`-input corolla, `treeOperation` applies `c.proj ∘ 𝒜.m (k + 2)` to the included
inputs with no extra Koszul signs. -/
theorem treeOperation_corolla (k : ℕ) (x : Fin (k + 2) → H) :
    ((𝒜.treeOperation c GH (.corolla k)).domDomCongr
        (finCongr (ReducedPlanarTree.numLeaves_corolla k))) x =
      c.proj (𝒜.m (k + 2) fun i ↦ c.incl (x i)) := by
  have hcor : (ReducedPlanarTree.node k fun _ ↦ .leaf).numLeaves = k + 2 :=
    ReducedPlanarTree.numLeaves_corolla k
  change (𝒜.suspendedTreeOperation c (.node k fun _ ↦ .leaf))
      (fun i ↦ GH.koszulTwist (((ReducedPlanarTree.node k fun _ ↦ .leaf).numLeaves : ℤ) - 1 - i)
        (x (finCongr hcor i))) = _
  rw [suspendedTreeOperation_node_apply, corolla_suspendedM_apply 𝒜 c hincl k x hcor]

end Corolla

section OperationHomogeneous

include hh hincl hproj

/-- The suspended operation map of every reduced planar tree has degree one between the suspended
gradings `(GH.shift 1).piece` and `(GH.shift 1).piece`. -/
theorem isHomogeneous_suspendedTreeOperation (t : ReducedPlanarTree) :
    MultilinearMap.IsHomogeneous (𝒜.suspendedTreeOperation c t)
      (fun _ ↦ (GH.shift 1).piece) (GH.shift 1).piece 1 := by
  cases t with
  | leaf =>
    rw [suspendedTreeOperation_leaf]
    exact MultilinearMap.isHomogeneous_zero _ _ _
  | node k children =>
    rw [suspendedTreeOperation_node]
    have hinner := (𝒜.isHomogeneous_suspendedM (Nat.succ_pos (k + 1))).compMultilinearMap
      fun i ↦ 𝒜.isHomogeneous_suspendedTreeBranch c hh hincl (children i)
    simp only [Finset.sum_const_zero, zero_add] at hinner
    have hcomp : MultilinearMap.IsHomogeneous
        (c.proj.compMultilinearMap
          ((𝒜.suspendedM (k + 2)).compMultilinearMap fun i ↦
            𝒜.suspendedTreeBranch c (children i)))
        (fun _ ↦ (GH.shift 1).piece) (GH.shift 1).piece 1 := by
      simpa only [add_zero] using
        (LinearMap.isHomogeneous_shift_piece_iff.2 hproj).compMultilinearMap hinner
    convert hcomp.domDomCongrLinearEquiv' (ReducedPlanarTree.nodeLeavesEquiv k children) using 1
    ext x
    simp only [MultilinearMap.domDomCongr_apply,
      _root_.MultilinearMap.domDomCongrLinearEquiv'_apply, _root_.MultilinearMap.coe_mk,
      Function.comp_apply]
    congr 1; funext ij; simp

/-- The unsuspended operation map of a reduced planar tree `t` is homogeneous of cohomological
degree `2 - t.numLeaves`. -/
theorem isHomogeneous_treeOperation (t : ReducedPlanarTree) :
    MultilinearMap.IsHomogeneous (𝒜.treeOperation c GH t)
      (fun _ ↦ GH.piece) GH.piece (2 - t.numLeaves) := by
  have hH : (GH.shift 1).piece = Graded.shift GH.piece 1 := by
    funext p
    rw [InternalGrading.shift_piece, Graded.shift_apply]
  have hs : MultilinearMap.IsHomogeneous (𝒜.suspendedTreeOperation c t)
      (fun _ ↦ GH.piece) GH.piece (2 - t.numLeaves) := by
    have h := MultilinearMap.isHomogeneous_shift_const_iff.1
      (hH ▸ 𝒜.isHomogeneous_suspendedTreeOperation c hh hincl hproj t)
    simpa [show (1 : ℤ) + 1 - t.numLeaves = 2 - t.numLeaves by ring] using h
  have htwist : ∀ l : Fin t.numLeaves, LinearMap.IsHomogeneous
      (GH.koszulTwist ((t.numLeaves : ℤ) - 1 - l)) GH.piece GH.piece 0 := by
    intro l
    rw [LinearMap.isHomogeneous_def]
    intro p x hx
    simpa only [add_zero] using GH.koszulTwist_mem_piece hx _
  simpa [treeOperation] using hs.compLinearMap htwist

end OperationHomogeneous

end HomogeneousTree

end General

/-! ### Merkulov operator recursions and main planar-tree transfer theorems -/

section TransferFormulas

variable {R : Type uR} {A : Type uA} {H : Type uH}
  [CommRing R] [AddCommGroup A] [Module R A] [AddCommGroup H] [Module R H]
  (𝒜 : AInfinityAlgebra R A) {GH : InternalGrading R H ℤ} {dH : Module.End R H}
  (c : LinearSpecialContraction 𝒜.differential dH)
  (hh : LinearMap.IsHomogeneous c.homotopy 𝒜.grading.piece 𝒜.grading.piece (-1))
  (hincl : LinearMap.IsHomogeneous c.incl GH.piece 𝒜.grading.piece 0)
  (hproj : LinearMap.IsHomogeneous c.proj 𝒜.grading.piece GH.piece 0)

/-- **Merkulov's fixed-point equation for `transferInclusion`**: its suspended Taylor map equals
`c.incl` on single letters minus `c.homotopy ∘ 𝒜.higherTaylor` applied to its own bar map. -/
theorem taylor_transferInclusion_eq_sub :
    (𝒜.transferInclusion c hh hincl hproj).taylor =
      c.incl ∘ₗ letter R H -
        c.homotopy ∘ₗ 𝒜.higherTaylor ∘ₗ (𝒜.transferInclusion c hh hincl hproj).barMap := by
  have hbar : (𝒜.transferInclusion c hh hincl hproj).barMap =
      ((𝒜.barTensorTrick c hh hincl hproj).perturb 𝒜.higherBarDifferential
        𝒜.gradedCoderiv_differential_add_higherBarDifferential_comp_self
        (𝒜.isUnit_one_add_higherBarDifferential_mul_barTensorTrick_homotopy
          c hh hincl hproj)).incl := by
    rw [barMap_transferInclusion, LinearSpecialContraction.perturb_incl, barTensorTrick_incl,
      barTensorTrick_homotopy]
  calc (𝒜.transferInclusion c hh hincl hproj).taylor
      = letter R A ∘ₗ ((𝒜.barTensorTrick c hh hincl hproj).perturb 𝒜.higherBarDifferential
          𝒜.gradedCoderiv_differential_add_higherBarDifferential_comp_self
          (𝒜.isUnit_one_add_higherBarDifferential_mul_barTensorTrick_homotopy
            c hh hincl hproj)).incl := by
        rw [AInfinityHom.taylor_def, hbar]
    _ = letter R A ∘ₗ (ReducedTensorWords.map (R := R) c.incl -
          c.reducedTensorWordsHomotopy (𝒜.grading.shift 1) ∘ₗ
            𝒜.higherBarDifferential ∘ₗ (𝒜.transferInclusion c hh hincl hproj).barMap) := by
        rw [LinearSpecialContraction.perturb_incl_eq_sub, barTensorTrick_incl,
          barTensorTrick_homotopy, ← hbar]
    _ = c.incl ∘ₗ letter R H -
          c.homotopy ∘ₗ 𝒜.higherTaylor ∘ₗ (𝒜.transferInclusion c hh hincl hproj).barMap := by
        rw [LinearMap.comp_sub, letter_comp_map, ← LinearMap.comp_assoc,
          c.letter_comp_reducedTensorWordsHomotopy, LinearMap.comp_assoc,
          ← LinearMap.comp_assoc _ 𝒜.higherBarDifferential (letter R A),
          𝒜.letter_comp_higherBarDifferential]

/-- **Merkulov's equation for the transferred Taylor map**: it equals `dH` on single letters plus
`c.proj ∘ 𝒜.higherTaylor` applied to the bar map of `transferInclusion`. -/
theorem taylor_transfer_eq_add :
    (𝒜.transfer c hh hincl hproj).taylor =
      dH ∘ₗ letter R H +
        c.proj ∘ₗ 𝒜.higherTaylor ∘ₗ (𝒜.transferInclusion c hh hincl hproj).barMap := by
  have hbar : (𝒜.transferInclusion c hh hincl hproj).barMap =
      ((𝒜.barTensorTrick c hh hincl hproj).perturb 𝒜.higherBarDifferential
        𝒜.gradedCoderiv_differential_add_higherBarDifferential_comp_self
        (𝒜.isUnit_one_add_higherBarDifferential_mul_barTensorTrick_homotopy
          c hh hincl hproj)).incl := by
    rw [barMap_transferInclusion, LinearSpecialContraction.perturb_incl, barTensorTrick_incl,
      barTensorTrick_homotopy]
  calc (𝒜.transfer c hh hincl hproj).taylor
      = letter R H ∘ₗ (gradedCoderiv (GH.shift 1) (dH ∘ₗ letter R H) 1 +
          ReducedTensorWords.map (R := R) c.proj ∘ₗ 𝒜.higherBarDifferential ∘ₗ
            (𝒜.transferInclusion c hh hincl hproj).barMap) := by
        rw [transfer_taylor, transferBarDifferential_def,
          (𝒜.barTensorTrick c hh hincl hproj).perturbedDifferential_eq_add_proj_comp_perturb_incl
            𝒜.higherBarDifferential
            𝒜.gradedCoderiv_differential_add_higherBarDifferential_comp_self
            (𝒜.isUnit_one_add_higherBarDifferential_mul_barTensorTrick_homotopy c hh hincl hproj),
          barTensorTrick_proj, ← hbar]
    _ = dH ∘ₗ letter R H +
          c.proj ∘ₗ 𝒜.higherTaylor ∘ₗ (𝒜.transferInclusion c hh hincl hproj).barMap := by
        rw [LinearMap.comp_add, letter_comp_gradedCoderiv, ← LinearMap.comp_assoc,
          letter_comp_map, LinearMap.comp_assoc,
          ← LinearMap.comp_assoc _ 𝒜.higherBarDifferential (letter R A),
          𝒜.letter_comp_higherBarDifferential]

/-- The higher Taylor map of the transferred `A∞` structure is `c.proj ∘ 𝒜.higherTaylor` composed
with the bar map of `transferInclusion`. -/
theorem higherTaylor_transfer :
    (𝒜.transfer c hh hincl hproj).higherTaylor =
      c.proj ∘ₗ 𝒜.higherTaylor ∘ₗ (𝒜.transferInclusion c hh hincl hproj).barMap := by
  apply linearMap_ext
  rintro ⟨n, hn⟩ x
  rcases eq_or_ne n 1 with rfl | hn1
  · have hword : of R H ⟨1, hn⟩ (PiTensorProduct.tprod R x) = ofLetter R H (x 0) := by
      rw [of_tprod_eq_subword R hn x, subword_one R H x hn]
      rfl
    rw [hword, ← LinearMap.comp_apply (𝒜.transfer c hh hincl hproj).higherTaylor,
      higherTaylor_comp_ofLetter, LinearMap.zero_apply, LinearMap.comp_apply, LinearMap.comp_apply,
      AInfinityHom.barMap_ofLetter, linearPart_transferInclusion,
      ← LinearMap.comp_apply 𝒜.higherTaylor, 𝒜.higherTaylor_comp_ofLetter, LinearMap.zero_apply,
      map_zero]
  · have hne1 : (⟨n, hn⟩ : {m : ℕ // 0 < m}) ≠ 1 := by
      intro h
      have h1 : n = 1 := by simpa using congrArg Subtype.val h
      exact hn1 h1
    rw [(𝒜.transfer c hh hincl hproj).higherTaylor_of ⟨n, hn⟩ (by dsimp; omega),
      taylor_transfer_eq_add, LinearMap.add_apply, LinearMap.comp_apply,
      letter_of_of_ne_one R H hne1, map_zero, zero_add]

/-- **Planar-tree formula for the suspended components of `transferInclusion`**: in every positive
arity `n`, `suspendedComponent n` is the sum of `suspendedTreeBranch` over all reduced planar trees
with `n` leaves. -/
theorem suspendedComponent_transferInclusion {n : ℕ} (hn : 0 < n) :
    (𝒜.transferInclusion c hh hincl hproj).suspendedComponent n =
      ∑ t : ReducedPlanarTree.Arity n,
        (𝒜.suspendedTreeBranch c t.val).domDomCongr (finCongr t.property) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases eq_or_ne n 1 with rfl | hn1
    · ext x
      rw [Fintype.sum_unique, ReducedPlanarTree.default_arity_one,
        AInfinityHom.suspendedComponent_apply _ 1 (by omega)]
      have hword : of R H ⟨1, Nat.one_pos⟩ (PiTensorProduct.tprod R x) = ofLetter R H (x 0) := by
        rw [of_tprod_eq_subword R Nat.one_pos x, subword_one R H x Nat.one_pos]
        rfl
      rw [hword, ← AInfinityHom.linearPart_apply, linearPart_transferInclusion,
        MultilinearMap.domDomCongr_apply, suspendedTreeBranch_leaf_apply]
      rfl
    · have hn2 : 2 ≤ n := by omega
      ext x
      have hne1 : (⟨n, hn⟩ : {m : ℕ // 0 < m}) ≠ 1 := by
        intro h
        have h1 : n = 1 := by simpa using congrArg Subtype.val h
        exact hn1 h1
      rw [AInfinityHom.suspendedComponent_apply _ n hn, taylor_transferInclusion_eq_sub,
        LinearMap.sub_apply, LinearMap.comp_apply, letter_of_of_ne_one R H hne1, map_zero, zero_sub,
        LinearMap.comp_apply, LinearMap.comp_apply,
        𝒜.higherTaylor_barMap_of_tprod (𝒜.transferInclusion c hh hincl hproj) hn x, map_sum,
        ← Finset.sum_neg_distrib, sum_apply,
        ← (ReducedPlanarTree.arityCompositionEquiv hn2).sum_comp, Fintype.sum_sigma]
      refine Finset.sum_congr rfl fun d _ ↦ ?_
      have hlt (i : Fin d.1.length) : d.1.blocksFun i < n :=
        (Composition.ne_single_iff hn).mp
          ((Composition.two_le_length_iff_ne_single hn d.1).mp d.2) i
      have harg :
          (fun i : Fin d.1.length ↦
            (𝒜.transferInclusion c hh hincl hproj).suspendedComponent (d.1.blocksFun i)
              (x ∘ d.1.embedding i)) =
          fun i ↦ ∑ t : ReducedPlanarTree.Arity (d.1.blocksFun i),
            ((𝒜.suspendedTreeBranch c t.val).domDomCongr (finCongr t.property))
              (x ∘ d.1.embedding i) := by
        funext i
        rw [ih (d.1.blocksFun i) (hlt i) (d.1.one_le_blocksFun i), sum_apply]
      rw [harg, MultilinearMap.map_sum, map_sum, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun children _ ↦ ?_
      rw [ReducedPlanarTree.arityCompositionEquiv_apply]
      exact (𝒜.suspendedTreeBranch_ofComposition c d.1 d.2 children x).symm

/-- **Planar-tree formula for the extending `A∞` quasi-isomorphism**: in every arity `n`, the
unsuspended component `(𝒜.transferInclusion c hh hincl hproj).component n` is the sum of
`𝒜.treeBranch c GH t` over all reduced planar trees `t` with `n` leaves. -/
theorem component_transferInclusion (n : ℕ) :
    (𝒜.transferInclusion c hh hincl hproj).component n =
      ∑ t : ReducedPlanarTree.Arity n,
        (𝒜.treeBranch c GH t.val).domDomCongr (finCongr t.property) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · ext x
    rw [AInfinityHom.component_apply _ n hn, ← AInfinityHom.suspendedComponent_apply _ n hn,
      transfer_grading, 𝒜.suspendedComponent_transferInclusion c hh hincl hproj hn, sum_apply,
      sum_apply]
    refine Finset.sum_congr rfl fun t _ ↦ ?_
    simp only [MultilinearMap.domDomCongr_apply, treeBranch, MultilinearMap.compLinearMap_apply,
      finCongr_apply]
    congr 1
    funext l
    congr 2
    rw [Fin.val_cast]
    exact congrArg (fun k : ℕ ↦ (k : ℤ) - 1 - (l : ℕ)) t.property.symm

/-- **Planar-tree formula for the suspended higher operations of `transfer`**: in every arity
`n ≥ 2`, `(𝒜.transfer c hh hincl hproj).suspendedM n` is the sum of `suspendedTreeOperation` over
all reduced planar trees with `n` leaves. -/
theorem suspendedM_transfer_eq_sum_arity {n : ℕ} (hn : 2 ≤ n) :
    (𝒜.transfer c hh hincl hproj).suspendedM n =
      ∑ t : ReducedPlanarTree.Arity n,
        (𝒜.suspendedTreeOperation c t.val).domDomCongr (finCongr t.property) := by
  have hpos : 0 < n := by omega
  have hne1 : (⟨n, hpos⟩ : {m : ℕ // 0 < m}) ≠ 1 := by
    intro h
    have h1 : n = 1 := by simpa using congrArg Subtype.val h
    omega
  ext x
  rw [← (𝒜.transfer c hh hincl hproj).taylor_of_tprod_eq_suspendedM ⟨n, hpos⟩ x,
    taylor_transfer_eq_add, LinearMap.add_apply, LinearMap.comp_apply,
    letter_of_of_ne_one R H hne1, map_zero, zero_add, LinearMap.comp_apply, LinearMap.comp_apply,
    𝒜.higherTaylor_barMap_of_tprod (𝒜.transferInclusion c hh hincl hproj) hpos x, map_sum,
    sum_apply, ← (ReducedPlanarTree.arityCompositionEquiv hn).sum_comp, Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun d _ ↦ ?_
  have harg :
      (fun i : Fin d.1.length ↦
        (𝒜.transferInclusion c hh hincl hproj).suspendedComponent (d.1.blocksFun i)
          (x ∘ d.1.embedding i)) =
      fun i ↦ ∑ t : ReducedPlanarTree.Arity (d.1.blocksFun i),
        ((𝒜.suspendedTreeBranch c t.val).domDomCongr (finCongr t.property))
          (x ∘ d.1.embedding i) := by
    funext i
    rw [𝒜.suspendedComponent_transferInclusion c hh hincl hproj (d.1.one_le_blocksFun i),
      sum_apply]
  rw [harg, MultilinearMap.map_sum, map_sum]
  refine Finset.sum_congr rfl fun children _ ↦ ?_
  rw [ReducedPlanarTree.arityCompositionEquiv_apply]
  exact (𝒜.suspendedTreeOperation_ofComposition c d.1 d.2 children x).symm

/-- **Planar-tree formula for the transferred `A∞` operations** (Merkulov; Kontsevich--Soibelman):
for every `n ≥ 2`, `(𝒜.transfer c hh hincl hproj).m n` is the sum of `𝒜.treeOperation c GH t` over
all reduced planar trees `t` with `n` leaves. -/
theorem m_transfer_eq_sum_arity {n : ℕ} (hn : 2 ≤ n) :
    (𝒜.transfer c hh hincl hproj).m n =
      ∑ t : ReducedPlanarTree.Arity n,
        (𝒜.treeOperation c GH t.val).domDomCongr (finCongr t.property) := by
  ext x
  rw [(𝒜.transfer c hh hincl hproj).m_eq_compLinearMap_suspendedM n,
    MultilinearMap.compLinearMap_apply, transfer_grading,
    𝒜.suspendedM_transfer_eq_sum_arity c hh hincl hproj hn, sum_apply, sum_apply]
  refine Finset.sum_congr rfl fun t _ ↦ ?_
  simp only [MultilinearMap.domDomCongr_apply, treeOperation, MultilinearMap.compLinearMap_apply,
    finCongr_apply]
  congr 1
  funext l
  congr 2
  rw [Fin.val_cast]
  exact congrArg (fun k : ℕ ↦ (k : ℤ) - 1 - (l : ℕ)) t.property.symm

/-- For every arity `n ≠ 1` (including `n = 0`, where both sides vanish), the transferred operation
`m n` equals the sum of `treeOperation` over `ReducedPlanarTree.Arity n`. -/
theorem m_transfer_of_ne_one {n : ℕ} (hn : n ≠ 1) :
    (𝒜.transfer c hh hincl hproj).m n =
      ∑ t : ReducedPlanarTree.Arity n,
        (𝒜.treeOperation c GH t.val).domDomCongr (finCongr t.property) := by
  rcases Nat.eq_zero_or_pos n with rfl | hpos
  · simp
  · exact 𝒜.m_transfer_eq_sum_arity c hh hincl hproj (by omega)

section ThreeLeaf

include hh hincl

/-- Evaluate `treeBranch` on the left-comb binary 3-leaf tree `binary (corolla 0) leaf`. -/
theorem treeBranch_binary_corolla_zero_leaf (x y z : H) :
    ((𝒜.treeBranch c GH (.binary (.corolla 0) .leaf)).domDomCongr
      (finCongr (by simp))) ![x, y, z] =
      -c.homotopy (𝒜.m 2 ![c.homotopy (𝒜.m 2 ![c.incl x, c.incl y]), c.incl z]) := by
  have hneg_l (u v : A) : 𝒜.m 2 ![-u, v] = -𝒜.m 2 ![u, v] := by
    simpa only [mul_apply, LinearMap.neg_apply] using LinearMap.congr_fun (𝒜.mul.map_neg u) v
  have h3 : (ReducedPlanarTree.corolla 0).numLeaves + ReducedPlanarTree.leaf.numLeaves = 3 := by
    simp
  have hlhs :
      ((𝒜.treeBranch c GH (.binary (.corolla 0) .leaf)).domDomCongr
        (finCongr (by simp))) ![x, y, z] =
      ((𝒜.treeBranch c GH (.binary (.corolla 0) .leaf)).domDomCongr
        (finCongr (ReducedPlanarTree.numLeaves_binary (.corolla 0) .leaf)))
        (![x, y, z] ∘ finCongr h3) := rfl
  rw [hlhs, 𝒜.treeBranch_binary c hh hincl (.corolla 0) .leaf,
    𝒜.treeBranch_corolla_zero_apply c hincl, treeBranch_leaf_apply]
  have hs1 : (1 : ℤ) - (ReducedPlanarTree.corolla 0).numLeaves = -1 := by simp
  have hv0 : (![x, y, z] : Fin 3 → H)
      (finCongr h3 (Fin.castAdd ReducedPlanarTree.leaf.numLeaves ⟨0, by decide⟩)) = x := rfl
  have hv1 : (![x, y, z] : Fin 3 → H)
      (finCongr h3 (Fin.castAdd ReducedPlanarTree.leaf.numLeaves ⟨1, by decide⟩)) = y := rfl
  have hv2 : (![x, y, z] : Fin 3 → H)
      (finCongr h3 (Fin.natAdd (ReducedPlanarTree.corolla 0).numLeaves ⟨0, by decide⟩)) = z := rfl
  simp only [hs1, negOnePowCast_neg, negOnePowCast_one, ReducedPlanarTree.numLeaves_leaf,
    Nat.cast_one, sub_self, GH.koszulTwist_zero, LinearMap.id_apply, Function.comp_apply,
    hv0, hv1, hv2, hneg_l, map_neg, neg_neg, neg_one_smul]

/-- Evaluate `treeBranch` on the right-comb binary 3-leaf tree `binary leaf (corolla 0)`. -/
theorem treeBranch_binary_leaf_corolla_zero (x y z : H) :
    ((𝒜.treeBranch c GH (.binary .leaf (.corolla 0))).domDomCongr
      (finCongr (by simp))) ![x, y, z] =
      c.homotopy (𝒜.m 2 ![c.incl (GH.koszulTwist 1 x),
        c.homotopy (𝒜.m 2 ![c.incl y, c.incl z])]) := by
  have hneg_r (u v : A) : 𝒜.m 2 ![u, -v] = -𝒜.m 2 ![u, v] := by
    simpa only [mul_apply] using map_neg (𝒜.mul u) v
  have h3 : ReducedPlanarTree.leaf.numLeaves + (ReducedPlanarTree.corolla 0).numLeaves = 3 := by
    simp
  have hlhs :
      ((𝒜.treeBranch c GH (.binary .leaf (.corolla 0))).domDomCongr
        (finCongr (by simp))) ![x, y, z] =
      ((𝒜.treeBranch c GH (.binary .leaf (.corolla 0))).domDomCongr
        (finCongr (ReducedPlanarTree.numLeaves_binary .leaf (.corolla 0))))
        (![x, y, z] ∘ finCongr h3) := rfl
  rw [hlhs, 𝒜.treeBranch_binary c hh hincl .leaf (.corolla 0),
    treeBranch_leaf_apply, 𝒜.treeBranch_corolla_zero_apply c hincl]
  have hs2 : (1 : ℤ) - (ReducedPlanarTree.corolla 0).numLeaves = -1 := by simp
  have hv0 : (![x, y, z] : Fin 3 → H)
      (finCongr h3 (Fin.castAdd (ReducedPlanarTree.corolla 0).numLeaves ⟨0, by decide⟩)) = x := rfl
  have hv1 : (![x, y, z] : Fin 3 → H)
      (finCongr h3 (Fin.natAdd ReducedPlanarTree.leaf.numLeaves ⟨0, by decide⟩)) = y := rfl
  have hv2 : (![x, y, z] : Fin 3 → H)
      (finCongr h3 (Fin.natAdd ReducedPlanarTree.leaf.numLeaves ⟨1, by decide⟩)) = z := rfl
  simp only [ReducedPlanarTree.numLeaves_leaf, Nat.cast_one, sub_self, negOnePowCast_zero,
    one_smul, hs2, GH.koszulTwist_neg, Function.comp_apply, hv0, hv1, hv2, hneg_r, map_neg,
    neg_neg]

end ThreeLeaf

/-- **Cubic component of the extending `A∞` quasi-isomorphism**: the three-leaf tree sum evaluates
to `-h m₃ (i ⊗ i ⊗ i) - h m₂ (h m₂ (i ⊗ i) ⊗ i) + h m₂ (i τ ⊗ h m₂ (i ⊗ i))`. -/
theorem component_three_transferInclusion (x y z : H) :
    (𝒜.transferInclusion c hh hincl hproj).component 3 ![x, y, z] =
      -c.homotopy (𝒜.m 3 ![c.incl x, c.incl y, c.incl z]) -
        c.homotopy (𝒜.m 2 ![c.homotopy (𝒜.m 2 ![c.incl x, c.incl y]), c.incl z]) +
        c.homotopy (𝒜.m 2 ![c.incl (GH.koszulTwist 1 x),
          c.homotopy (𝒜.m 2 ![c.incl y, c.incl z])]) := by
  rw [𝒜.component_transferInclusion c hh hincl hproj 3, sum_apply,
    ReducedPlanarTree.sum_arity_three]
  have ht0 :
      ((𝒜.treeBranch c GH (.corolla 1)).domDomCongr
        (finCongr (ReducedPlanarTree.numLeaves_corolla 1))) ![x, y, z] =
      -c.homotopy (𝒜.m 3 ![c.incl x, c.incl y, c.incl z]) := by
    rw [𝒜.treeBranch_corolla c hincl 1 ![x, y, z]]
    refine congrArg (fun v ↦ -c.homotopy (𝒜.m 3 v)) ?_
    funext i
    fin_cases i <;> rfl
  rw [ht0, 𝒜.treeBranch_binary_corolla_zero_leaf c hh hincl x y z,
    𝒜.treeBranch_binary_leaf_corolla_zero c hh hincl x y z]
  abel

/-! ### Binary-tree specialization when higher operations vanish -/

section BinarySpecialization

/-- When `𝒜.m k = 0` for all `k ≥ 3`, every non-binary tree has zero suspended branch map. -/
theorem suspendedTreeBranch_eq_zero_of_not_isBinary
    {dA : Module.End R A} (c' : LinearSpecialContraction dA dH)
    (h₃ : ∀ k, 3 ≤ k → 𝒜.m k = 0) {t : ReducedPlanarTree} (ht : ¬ t.IsBinary) :
    𝒜.suspendedTreeBranch c' t = 0 := by
  induction t with
  | leaf => exact absurd ReducedPlanarTree.isBinary_leaf ht
  | node k children ih =>
    rw [ReducedPlanarTree.isBinary_node, not_and_or, not_forall] at ht
    ext x
    rw [suspendedTreeBranch_node_apply, zero_apply]
    rcases ht with hk | ⟨i, hi⟩
    · rw [suspendedM_apply, h₃ (k + 2) (by omega), zero_apply, map_zero, neg_zero]
    · have hzero : 𝒜.suspendedTreeBranch c' (children i)
          (fun j ↦ x (finSigmaFinEquiv ⟨i, j⟩)) = 0 := by
        rw [ih i hi, zero_apply]
      rw [(𝒜.suspendedM (k + 2)).map_coord_zero i hzero, map_zero, neg_zero]

/-- When `𝒜.m k = 0` for all `k ≥ 3`, every non-binary tree has zero suspended operation map. -/
theorem suspendedTreeOperation_eq_zero_of_not_isBinary
    {dA : Module.End R A} (c' : LinearSpecialContraction dA dH)
    (h₃ : ∀ k, 3 ≤ k → 𝒜.m k = 0) {t : ReducedPlanarTree} (ht : ¬ t.IsBinary) :
    𝒜.suspendedTreeOperation c' t = 0 := by
  cases t with
  | leaf => exact suspendedTreeOperation_leaf 𝒜 c'
  | node k children =>
    rw [ReducedPlanarTree.isBinary_node, not_and_or, not_forall] at ht
    ext x
    rw [suspendedTreeOperation_node_apply, zero_apply]
    rcases ht with hk | ⟨i, hi⟩
    · rw [suspendedM_apply, h₃ (k + 2) (by omega), zero_apply, map_zero]
    · have hzero : 𝒜.suspendedTreeBranch c' (children i)
          (fun j ↦ x (finSigmaFinEquiv ⟨i, j⟩)) = 0 := by
        rw [𝒜.suspendedTreeBranch_eq_zero_of_not_isBinary c' h₃ hi, zero_apply]
      rw [(𝒜.suspendedM (k + 2)).map_coord_zero i hzero, map_zero]

/-- When `𝒜.m k = 0` for all `k ≥ 3`, every non-binary tree has zero unsuspended branch map. -/
theorem treeBranch_eq_zero_of_not_isBinary
    {dA : Module.End R A} (c' : LinearSpecialContraction dA dH)
    (h₃ : ∀ k, 3 ≤ k → 𝒜.m k = 0) {t : ReducedPlanarTree} (ht : ¬ t.IsBinary) :
    𝒜.treeBranch c' GH t = 0 := by
  rw [treeBranch, 𝒜.suspendedTreeBranch_eq_zero_of_not_isBinary c' h₃ ht,
    MultilinearMap.zero_compLinearMap]

/-- When `𝒜.m k = 0` for all `k ≥ 3`, every non-binary tree has zero unsuspended operation map. -/
theorem treeOperation_eq_zero_of_not_isBinary
    {dA : Module.End R A} (c' : LinearSpecialContraction dA dH)
    (h₃ : ∀ k, 3 ≤ k → 𝒜.m k = 0) {t : ReducedPlanarTree} (ht : ¬ t.IsBinary) :
    𝒜.treeOperation c' GH t = 0 := by
  rw [treeOperation, 𝒜.suspendedTreeOperation_eq_zero_of_not_isBinary c' h₃ ht,
    MultilinearMap.zero_compLinearMap]

/-- **Kontsevich--Soibelman binary-tree formula for `transferInclusion`**: when all operations of
`𝒜` in arity at least three vanish, `(𝒜.transferInclusion c hh hincl hproj).component n` sums only
over binary planar trees with `n` leaves. -/
theorem component_transferInclusion_eq_sum_isBinary (h₃ : ∀ k, 3 ≤ k → 𝒜.m k = 0) (n : ℕ) :
    (𝒜.transferInclusion c hh hincl hproj).component n =
      ∑ t : {t : ReducedPlanarTree.Arity n // t.val.IsBinary},
        (𝒜.treeBranch c GH t.1.val).domDomCongr (finCongr t.1.property) := by
  rw [𝒜.component_transferInclusion c hh hincl hproj n,
    ← Finset.sum_subtype (Finset.univ.filter fun t : ReducedPlanarTree.Arity n ↦ t.val.IsBinary)
      (fun _ ↦ Finset.mem_filter.trans (and_iff_right (Finset.mem_univ _)))
      (fun t ↦ (𝒜.treeBranch c GH t.val).domDomCongr (finCongr t.property)),
    Finset.sum_filter]
  refine Finset.sum_congr rfl fun t _ ↦ ?_
  split_ifs with ht
  · rfl
  · rw [𝒜.treeBranch_eq_zero_of_not_isBinary c h₃ ht]
    rfl

/-- **Kontsevich--Soibelman binary-tree formula for `transfer`**: when all operations of `𝒜` in
arity at least three vanish, `(𝒜.transfer c hh hincl hproj).m n` (`n ≥ 2`) sums only over binary
planar trees with `n` leaves. -/
theorem m_transfer_eq_sum_isBinary (h₃ : ∀ k, 3 ≤ k → 𝒜.m k = 0) {n : ℕ} (hn : 2 ≤ n) :
    (𝒜.transfer c hh hincl hproj).m n =
      ∑ t : {t : ReducedPlanarTree.Arity n // t.val.IsBinary},
        (𝒜.treeOperation c GH t.1.val).domDomCongr (finCongr t.1.property) := by
  rw [𝒜.m_transfer_eq_sum_arity c hh hincl hproj hn,
    ← Finset.sum_subtype (Finset.univ.filter fun t : ReducedPlanarTree.Arity n ↦ t.val.IsBinary)
      (fun _ ↦ Finset.mem_filter.trans (and_iff_right (Finset.mem_univ _)))
      (fun t ↦ (𝒜.treeOperation c GH t.val).domDomCongr (finCongr t.property)),
    Finset.sum_filter]
  refine Finset.sum_congr rfl fun t _ ↦ ?_
  split_ifs with ht
  · rfl
  · rw [𝒜.treeOperation_eq_zero_of_not_isBinary c h₃ ht]
    rfl

end BinarySpecialization

end TransferFormulas

/-! ### Tree-by-tree naturality under strict morphisms -/

section Naturality

variable {R : Type uR} [CommRing R]
  {A : Type uA} {H : Type uH} {B : Type uB} {K : Type uK}
  [AddCommGroup A] [Module R A] [AddCommGroup H] [Module R H]
  [AddCommGroup B] [Module R B] [AddCommGroup K] [Module R K]
  {𝒜 : AInfinityAlgebra R A} {ℬ : AInfinityAlgebra R B}
  {GH : InternalGrading R H ℤ} {GK : InternalGrading R K ℤ}
  {dA : Module.End R A} {dH : Module.End R H}
  {dB : Module.End R B} {dK : Module.End R K}
  (c : LinearSpecialContraction dA dH)
  (c' : LinearSpecialContraction dB dK)
  (f : AInfinityStrictHom 𝒜 ℬ) (g : H →ₗ[R] K)

/-- A strict morphism of `A∞` algebras commutes with `suspendedM`. -/
theorem map_suspendedM (n : ℕ) (x : Fin n → A) :
    f (𝒜.suspendedM n x) = ℬ.suspendedM n (fun i ↦ f (x i)) := by
  rw [suspendedM_apply, f.map_m, suspendedM_apply]
  congr 1
  funext i
  simpa [mul_zero] using (f.isHomogeneous.koszulTwist_apply ((n : ℤ) - 1 - i) (x i)).symm

section BranchNaturality

variable (hι : f.toLinearMap ∘ₗ c.incl = c'.incl ∘ₗ g)
  (hη : f.toLinearMap ∘ₗ c.homotopy = c'.homotopy ∘ₗ f.toLinearMap)
include hι hη

/-- Compatible strict morphisms intertwine `suspendedTreeBranch` on every reduced planar tree. -/
theorem map_suspendedTreeBranch (t : ReducedPlanarTree) :
    f.toLinearMap.compMultilinearMap (𝒜.suspendedTreeBranch c t) =
      (ℬ.suspendedTreeBranch c' t).compLinearMap fun _ ↦ g := by
  induction t with
  | leaf =>
    ext x
    simpa only [LinearMap.compMultilinearMap_apply, MultilinearMap.compLinearMap_apply,
      suspendedTreeBranch_leaf_apply, AInfinityStrictHom.coe_toLinearMap,
      LinearMap.comp_apply] using LinearMap.congr_fun hι (x ⟨0, by decide⟩)
  | node k children ih =>
    ext x
    simp only [LinearMap.compMultilinearMap_apply, AInfinityStrictHom.coe_toLinearMap,
      MultilinearMap.compLinearMap_apply, suspendedTreeBranch_node_apply, map_neg]
    have hηx := LinearMap.congr_fun hη
    simp only [LinearMap.comp_apply, AInfinityStrictHom.coe_toLinearMap] at hηx
    rw [hηx, map_suspendedM]
    refine congrArg (fun v ↦ -c'.homotopy (ℬ.suspendedM (k + 2) v)) (funext fun i ↦ ?_)
    simpa [LinearMap.compMultilinearMap_apply, MultilinearMap.compLinearMap_apply] using
      congrArg (· fun j ↦ x (ReducedPlanarTree.nodeLeavesEquiv k children ⟨i, j⟩)) (ih i)

/-- Compatible strict morphisms and a degree-zero retract map intertwine `treeBranch` on every
reduced planar tree. -/
theorem map_treeBranch (hg : LinearMap.IsHomogeneous g GH.piece GK.piece 0)
    (t : ReducedPlanarTree) :
    f.toLinearMap.compMultilinearMap (𝒜.treeBranch c GH t) =
      (ℬ.treeBranch c' GK t).compLinearMap fun _ ↦ g := by
  ext x
  have hs := congrArg (· fun l ↦ GH.koszulTwist ((t.numLeaves : ℤ) - 1 - l) (x l))
    (map_suspendedTreeBranch c c' f g hι hη t)
  simp only [LinearMap.compMultilinearMap_apply, MultilinearMap.compLinearMap_apply] at hs
  rw [LinearMap.compMultilinearMap_apply, treeBranch, MultilinearMap.compLinearMap_apply, hs,
    MultilinearMap.compLinearMap_apply, treeBranch, MultilinearMap.compLinearMap_apply]
  congr 1
  funext l
  simpa [mul_zero] using (hg.koszulTwist_apply ((t.numLeaves : ℤ) - 1 - l) (x l)).symm

end BranchNaturality

section OperationNaturality

variable (hι : f.toLinearMap ∘ₗ c.incl = c'.incl ∘ₗ g)
  (hπ : g ∘ₗ c.proj = c'.proj ∘ₗ f.toLinearMap)
  (hη : f.toLinearMap ∘ₗ c.homotopy = c'.homotopy ∘ₗ f.toLinearMap)
include hι hπ hη

/-- Compatible strict morphisms intertwine `suspendedTreeOperation` on every reduced planar tree. -/
theorem map_suspendedTreeOperation (t : ReducedPlanarTree) :
    g.compMultilinearMap (𝒜.suspendedTreeOperation c t) =
      (ℬ.suspendedTreeOperation c' t).compLinearMap fun _ ↦ g := by
  cases t with
  | leaf =>
    ext x
    simp
  | node k children =>
    ext x
    simp only [LinearMap.compMultilinearMap_apply, MultilinearMap.compLinearMap_apply,
      suspendedTreeOperation_node_apply]
    have hπx := LinearMap.congr_fun hπ
    simp only [LinearMap.comp_apply, AInfinityStrictHom.coe_toLinearMap] at hπx
    rw [hπx, map_suspendedM]
    refine congrArg (fun v ↦ c'.proj (ℬ.suspendedM (k + 2) v)) (funext fun i ↦ ?_)
    simpa [LinearMap.compMultilinearMap_apply, MultilinearMap.compLinearMap_apply] using
      congrArg (· fun j ↦ x (ReducedPlanarTree.nodeLeavesEquiv k children ⟨i, j⟩))
        (map_suspendedTreeBranch c c' f g hι hη (children i))

/-- Compatible strict morphisms and a degree-zero retract map intertwine `treeOperation` on every
reduced planar tree. -/
theorem map_treeOperation (hg : LinearMap.IsHomogeneous g GH.piece GK.piece 0)
    (t : ReducedPlanarTree) :
    g.compMultilinearMap (𝒜.treeOperation c GH t) =
      (ℬ.treeOperation c' GK t).compLinearMap fun _ ↦ g := by
  ext x
  have hs := congrArg (· fun l ↦ GH.koszulTwist ((t.numLeaves : ℤ) - 1 - l) (x l))
    (map_suspendedTreeOperation c c' f g hι hπ hη t)
  simp only [LinearMap.compMultilinearMap_apply, MultilinearMap.compLinearMap_apply] at hs
  rw [LinearMap.compMultilinearMap_apply, treeOperation, MultilinearMap.compLinearMap_apply, hs,
    MultilinearMap.compLinearMap_apply, treeOperation, MultilinearMap.compLinearMap_apply]
  congr 1
  funext l
  simpa [mul_zero] using (hg.koszulTwist_apply ((t.numLeaves : ℤ) - 1 - l) (x l)).symm

end OperationNaturality

end Naturality

end TauCeti.AInfinityAlgebra
