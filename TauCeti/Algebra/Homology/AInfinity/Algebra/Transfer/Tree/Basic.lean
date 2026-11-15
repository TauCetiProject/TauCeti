/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.AInfinity.Algebra.BarDifferential
public import TauCeti.Algebra.Homology.Contraction.Linear.Basic
public import TauCeti.Algebra.Module.GradedModule.Multilinear.Composition
public import TauCeti.Combinatorics.Tree.ReducedPlanar

/-!
# Planar-tree evaluation maps for A-infinity algebras

Given an `A∞` algebra `𝒜` on `A` and a linear special contraction `c` between `(A, d_A)` and
`(H, d_H)`, each reduced planar rooted tree `t : ReducedPlanarTree` defines sign-free suspended
multilinear maps `suspendedTreeBranch` (`H^{t.numLeaves} ⟶ A`) and `suspendedTreeOperation`
(`H^{t.numLeaves} ⟶ H`), applying `c.incl` at leaves, `𝒜.suspendedM (k + 2)` at `(k + 2)`-ary
internal vertices, `-c.homotopy` along internal edges (and at a branch root), and `c.proj` at an
operation root. Precomposing input `l` with the Koszul twist `t.numLeaves - 1 - l` produces the
unsuspended maps `treeBranch` (of degree `1 - t.numLeaves`) and `treeOperation` (of degree
`2 - t.numLeaves`), whose recursion at an internal vertex decomposes through
`TauCeti.InternalGrading.signedCompMultilinearMap`.

## Main definitions

* `TauCeti.AInfinityAlgebra.suspendedM`: the suspended `n`-ary operation `bₙ` of `𝒜`.
* `TauCeti.AInfinityAlgebra.suspendedTreeBranch` and
  `TauCeti.AInfinityAlgebra.suspendedTreeOperation`: sign-free suspended tree maps.
* `TauCeti.AInfinityAlgebra.treeBranch` and `TauCeti.AInfinityAlgebra.treeOperation`: Koszul-twisted
  unsuspended branch and operation maps attached to a reduced planar tree.

## Main results

* `TauCeti.AInfinityAlgebra.isHomogeneous_treeBranch` and
  `TauCeti.AInfinityAlgebra.isHomogeneous_treeOperation`: cohomological degrees `1 - t.numLeaves`
  and `2 - t.numLeaves`.
* `TauCeti.AInfinityAlgebra.treeBranch_node`, `TauCeti.AInfinityAlgebra.treeOperation_node`,
  `TauCeti.AInfinityAlgebra.treeBranch_binary`, `TauCeti.AInfinityAlgebra.treeOperation_binary`,
  `TauCeti.AInfinityAlgebra.treeBranch_corolla`, and
  `TauCeti.AInfinityAlgebra.treeOperation_corolla`: unsuspended recursions at general internal
  vertices, binary vertices, and corollas.
-/

public section

open scoped BigOperators

universe uR uA uH

namespace TauCeti.AInfinityAlgebra

open ReducedTensorWords

variable {R : Type uR} {A : Type uA} {H : Type uH}
  [CommRing R] [AddCommGroup A] [Module R A] [AddCommGroup H] [Module R H]

/-! ### Suspended operations -/

/-- The suspended arity-`n` operation `bₙ : (sA)⊗ⁿ ⟶ sA` of an `A∞` algebra, obtained by
precomposing `𝒜.m n` with the Koszul twists `n - 1 - i` (`taylor_of_tprod`). -/
noncomputable def suspendedM (𝒜 : AInfinityAlgebra R A) (n : ℕ) :
    MultilinearMap (RingHom.id R) (fun _ : Fin n ↦ A) A :=
  (𝒜.m n).compLinearMap fun i ↦ 𝒜.grading.koszulTwist ((n : ℤ) - 1 - i)

@[simp]
theorem suspendedM_zero (𝒜 : AInfinityAlgebra R A) : 𝒜.suspendedM 0 = 0 := by
  rw [suspendedM, 𝒜.m_zero, MultilinearMap.zero_compLinearMap]

/-- Evaluate the suspended arity-`n` operation through the Koszul-twisted unsuspended operation. -/
theorem suspendedM_apply (𝒜 : AInfinityAlgebra R A) (n : ℕ) (x : Fin n → A) :
    𝒜.suspendedM n x = 𝒜.m n fun i ↦ 𝒜.grading.koszulTwist ((n : ℤ) - 1 - i) (x i) :=
  MultilinearMap.compLinearMap_apply ..

private theorem suspendedM_congr (𝒜 : AInfinityAlgebra R A) {m n : ℕ} (h : m = n)
    (x : Fin n → A) : 𝒜.suspendedM m (fun i ↦ x (i.cast h)) = 𝒜.suspendedM n x := by
  subst h; rfl

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
  refine congrArg (𝒜.m n) (funext fun i ↦ ?_)
  rw [← LinearMap.comp_apply (𝒜.grading.koszulTwist _), InternalGrading.koszulTwist_comp_self,
    LinearMap.id_apply]

/-- In positive arity, `suspendedM n` has degree one for `𝒜.grading.shift 1`. -/
theorem isHomogeneous_suspendedM (𝒜 : AInfinityAlgebra R A) {n : ℕ} (hn : 0 < n) :
    MultilinearMap.IsHomogeneous (𝒜.suspendedM n)
      (fun _ ↦ (𝒜.grading.shift 1).piece) (𝒜.grading.shift 1).piece 1 := by
  rw [MultilinearMap.isHomogeneous_def]
  intro d x hx
  rw [← 𝒜.taylor_of_tprod_eq_suspendedM ⟨n, hn⟩ x]
  exact (𝒜.taylor_isSuspension.isHomogeneous 𝒜.m_degree).map_mem
    (mem_gradedPiece_of_tprod (𝒜.grading.shift 1) hn x d hx)

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
`c.proj ∘ 𝒜.suspendedM (k + 2)` applied to the child branch maps at `node k children`. -/
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

/-- Unfold `treeBranch` as `suspendedTreeBranch` precomposed with input Koszul twists. -/
theorem treeBranch_def (GH : InternalGrading R H ℤ) (t : ReducedPlanarTree) :
    𝒜.treeBranch c GH t = (𝒜.suspendedTreeBranch c t).compLinearMap fun l ↦
      GH.koszulTwist ((t.numLeaves : ℤ) - 1 - l) := (rfl)

/-- The **unsuspended operation map** `H^{t.numLeaves} ⟶ H` of a reduced planar tree `t`, obtained
from `suspendedTreeOperation` by precomposing input `l` with the Koszul twist
`t.numLeaves - 1 - l`. -/
noncomputable def treeOperation (GH : InternalGrading R H ℤ) (t : ReducedPlanarTree) :
    MultilinearMap (RingHom.id R) (fun _ : Fin t.numLeaves ↦ H) H :=
  (𝒜.suspendedTreeOperation c t).compLinearMap fun l ↦
    GH.koszulTwist ((t.numLeaves : ℤ) - 1 - l)

/-- Unfold `treeOperation` as `suspendedTreeOperation` precomposed with input Koszul twists. -/
theorem treeOperation_def (GH : InternalGrading R H ℤ) (t : ReducedPlanarTree) :
    𝒜.treeOperation c GH t = (𝒜.suspendedTreeOperation c t).compLinearMap fun l ↦
      GH.koszulTwist ((t.numLeaves : ℤ) - 1 - l) := (rfl)

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
  ext x; exact 𝒜.treeBranch_leaf_apply c GH x

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
  · change 𝒜.treeBranch c GH l (fun j : Fin l.numLeaves ↦
          GH.koszulTwist
            (∑ b : Fin 2, if (0 : Fin 2) < b then (1 - ((![l, r] b).numLeaves : ℤ)) else 0)
            (x (finCongr hbin (ReducedPlanarTree.nodeLeavesEquiv 0 ![l, r] ⟨0, j⟩)))) =
      𝒜.treeBranch c GH l (fun j ↦
        GH.koszulTwist (1 - r.numLeaves) (x (Fin.castAdd r.numLeaves j)))
    refine congrArg (𝒜.treeBranch c GH l) (funext fun j ↦ ?_)
    have h0 : (∑ b : Fin 2, if (0 : Fin 2) < b then (1 - ((![l, r] b).numLeaves : ℤ)) else 0) =
        1 - r.numLeaves := by simp [Fin.sum_univ_two]
    rw [h0]
    exact congrArg _ (congrArg x (Fin.ext (by simp)))
  · change 𝒜.treeBranch c GH r (fun j : Fin r.numLeaves ↦
          GH.koszulTwist
            (∑ b : Fin 2, if (1 : Fin 2) < b then (1 - ((![l, r] b).numLeaves : ℤ)) else 0)
            (x (finCongr hbin (ReducedPlanarTree.nodeLeavesEquiv 0 ![l, r] ⟨1, j⟩)))) =
      𝒜.treeBranch c GH r (fun j ↦ x (Fin.natAdd l.numLeaves j))
    refine congrArg (𝒜.treeBranch c GH r) (funext fun j ↦ ?_)
    have h1 : (∑ b : Fin 2, if (1 : Fin 2) < b then (1 - ((![l, r] b).numLeaves : ℤ)) else 0) =
        0 := by simp [Fin.sum_univ_two]
    rw [h1, GH.koszulTwist_zero, LinearMap.id_apply]
    exact congrArg x (Fin.ext (by simp))

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
  refine congrArg (𝒜.suspendedM (d.length - 2 + 2)) (funext fun i ↦ ?_)
  rw [MultilinearMap.domDomCongr_apply]
  refine congrArg (𝒜.suspendedTreeBranch c (children (i.cast hlen)).val) (funext fun j ↦ ?_)
  refine congrArg x (Fin.ext ?_)
  simp only [finCongr_apply, Fin.val_cast, ReducedPlanarTree.coe_nodeLeavesEquiv_apply,
    d.coe_embedding]
  rw [d.sizeUpTo_eq_sum_blocksFun (by omega : i.1 ≤ d.length)]
  exact congrArg (· + j.1) (Finset.sum_congr rfl fun a _ ↦ (children _).property)

/-- Evaluating `suspendedTreeBranch` on `ReducedPlanarTree.ofComposition` applies
`-c.homotopy ∘ 𝒜.suspendedM d.length` to the child branch evaluations on `x ∘ d.embedding i`. -/
theorem suspendedTreeBranch_ofComposition {n : ℕ} (d : Composition n) (hd : 2 ≤ d.length)
    (children : ∀ i : Fin d.length, ReducedPlanarTree.Arity (d.blocksFun i)) (x : Fin n → H) :
    ((𝒜.suspendedTreeBranch c (ReducedPlanarTree.ofComposition d hd children).val).domDomCongr
        (finCongr (ReducedPlanarTree.ofComposition d hd children).property)) x =
      -c.homotopy (𝒜.suspendedM d.length fun i ↦
        ((𝒜.suspendedTreeBranch c (children i).val).domDomCongr
          (finCongr (children i).property)) (x ∘ d.embedding i)) := by
  have hnode := (ReducedPlanarTree.ofComposition d hd children).property
  exact (𝒜.suspendedTreeBranch_node_apply c (d.length - 2)
    (fun i ↦ (children (i.cast (Nat.sub_add_cancel hd))).val)
    (fun i ↦ x (finCongr hnode i))).trans
    (congrArg (fun z ↦ -c.homotopy z) (suspendedM_ofComposition_apply 𝒜 c d hd children x hnode))

/-- Evaluating `suspendedTreeOperation` on `ReducedPlanarTree.ofComposition` applies
`c.proj ∘ 𝒜.suspendedM d.length` to the child branch evaluations on `x ∘ d.embedding i`. -/
theorem suspendedTreeOperation_ofComposition {n : ℕ} (d : Composition n) (hd : 2 ≤ d.length)
    (children : ∀ i : Fin d.length, ReducedPlanarTree.Arity (d.blocksFun i)) (x : Fin n → H) :
    ((𝒜.suspendedTreeOperation c (ReducedPlanarTree.ofComposition d hd children).val).domDomCongr
        (finCongr (ReducedPlanarTree.ofComposition d hd children).property)) x =
      c.proj (𝒜.suspendedM d.length fun i ↦
        ((𝒜.suspendedTreeBranch c (children i).val).domDomCongr
          (finCongr (children i).property)) (x ∘ d.embedding i)) := by
  have hnode := (ReducedPlanarTree.ofComposition d hd children).property
  exact (𝒜.suspendedTreeOperation_node_apply c (d.length - 2)
    (fun i ↦ (children (i.cast (Nat.sub_add_cancel hd))).val)
    (fun i ↦ x (finCongr hnode i))).trans
    (congrArg c.proj (suspendedM_ofComposition_apply 𝒜 c d hd children x hnode))

end TreeDefs

/-! ### Homogeneity and Koszul-signed unsuspended node formulas -/

private theorem sum_fin_split {m : ℕ} (f : Fin m → ℤ) (i : Fin m) :
    (∑ a : Fin m, f a) =
      (∑ a : Fin i.1, f (Fin.castLE i.2.le a)) + f i +
        ∑ b : Fin m, if i < b then f b else 0 := by
  have hpre : (∑ a : Fin i.1, f (Fin.castLE i.2.le a)) = ∑ a : Fin m, if a < i then f a else 0 := by
    rw [← Finset.sum_filter]
    exact Finset.sum_bij (fun (a : Fin i.1) _ ↦ Fin.castLE i.2.le a)
      (fun a _ ↦ Finset.mem_filter.mpr ⟨Finset.mem_univ _, a.2⟩)
      (fun _ _ _ _ h ↦ Fin.ext (by simpa using congrArg Fin.val h))
      (fun b hb ↦ ⟨⟨b.1, (Finset.mem_filter.mp hb).2⟩, Finset.mem_univ _, rfl⟩)
      (fun _ _ ↦ rfl)
  rw [hpre]
  have hpoint (a : Fin m) : f a = (if a < i then f a else 0) + (if a = i then f a else 0) +
      (if i < a then f a else 0) := by
    rcases lt_trichotomy a i with hlt | rfl | hgt
    · simp [hlt, lt_asymm hlt, ne_of_lt hlt]
    · simp
    · simp [hgt, lt_asymm hgt, ne_of_gt hgt]
  conv_lhs => rw [Finset.sum_congr rfl fun a _ ↦ hpoint a]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  simp

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
  rw [← hsum1]
  ring

private theorem shift_one_piece_eq {M : Type*} [AddCommGroup M] [Module R M]
    (G : InternalGrading R M ℤ) : (G.shift 1).piece = Graded.shift G.piece (1 : ℤ) :=
  funext fun p ↦ (G.shift_piece 1 p).trans (Graded.shift_apply G.piece 1 p).symm

private theorem isHomogeneous_koszulTwist_zero (GH : InternalGrading R H ℤ) (s : ℤ) :
    LinearMap.IsHomogeneous (GH.koszulTwist s) GH.piece GH.piece 0 := by
  rw [LinearMap.isHomogeneous_def]
  intro p x hx
  simpa only [add_zero] using GH.koszulTwist_mem_piece hx s

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
    exact congrArg _ (funext fun _ ↦ by simp)

/-- The unsuspended branch map of a reduced planar tree `t` is homogeneous of cohomological degree
`1 - t.numLeaves`. -/
theorem isHomogeneous_treeBranch (t : ReducedPlanarTree) :
    MultilinearMap.IsHomogeneous (𝒜.treeBranch c GH t)
      (fun _ ↦ GH.piece) 𝒜.grading.piece (1 - t.numLeaves) := by
  have hs : MultilinearMap.IsHomogeneous (𝒜.suspendedTreeBranch c t)
      (fun _ ↦ GH.piece) 𝒜.grading.piece (1 - t.numLeaves) := by
    have h := MultilinearMap.isHomogeneous_shift_const_iff.1
      (shift_one_piece_eq GH ▸ shift_one_piece_eq 𝒜.grading ▸
        𝒜.isHomogeneous_suspendedTreeBranch c hh hincl t)
    simpa [show (0 : ℤ) + 1 - t.numLeaves = 1 - t.numLeaves by ring] using h
  simpa [treeBranch] using hs.compLinearMap fun _ ↦ isHomogeneous_koszulTwist_zero GH _

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
    rw [ReducedPlanarTree.coe_nodeLeavesEquiv_apply, ReducedPlanarTree.numLeaves_node,
      Nat.cast_sum, sum_fin_split (fun a : Fin (k + 2) ↦ ((children a).numLeaves : ℤ)) i,
      Nat.cast_add, Nat.cast_sum]
    dsimp only [R_i]; ring
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
  simp_rw [hsub]; ring

private theorem unsuspend_suspendedM_comp_suspendedTreeBranch (k : ℕ)
    (children : Fin (k + 2) → ReducedPlanarTree) :
    (((𝒜.suspendedM (k + 2)).compMultilinearMap fun i ↦
        𝒜.suspendedTreeBranch c (children i)).domDomCongr
        (ReducedPlanarTree.nodeLeavesEquiv k children)).compLinearMap
        (fun l ↦ GH.koszulTwist (((ReducedPlanarTree.node k children).numLeaves : ℤ) - 1 - l)) =
      negOnePowCast R
        (∑ i : Fin (k + 2), ((k + 2 : ℤ) - 1 - i) * (1 - (children i).numLeaves)) •
      (InternalGrading.signedCompMultilinearMap (fun (_ : Fin (k + 2)) _ ↦ GH)
        (fun _ ↦ 𝒜.grading.piece) 𝒜.grading.piece
        ⟨𝒜.m (k + 2), MultilinearMap.mem_homogeneousSubmodule.mpr (𝒜.m_degree (k + 2) (by omega))⟩
        (fun i ↦ ⟨𝒜.treeBranch c GH (children i), MultilinearMap.mem_homogeneousSubmodule.mpr
          (𝒜.isHomogeneous_treeBranch c hh hincl (children i))⟩)).val.domDomCongr
        (ReducedPlanarTree.nodeLeavesEquiv k children) := by
  suffices hsigma :
      (((𝒜.suspendedM (k + 2)).compMultilinearMap fun i ↦
          𝒜.suspendedTreeBranch c (children i)).compLinearMap
        fun ij ↦ GH.koszulTwist (((ReducedPlanarTree.node k children).numLeaves : ℤ) - 1 -
          (ReducedPlanarTree.nodeLeavesEquiv k children ij : ℕ))) =
      negOnePowCast R (∑ i : Fin (k + 2), ((k + 2 : ℤ) - 1 - i) * (1 - (children i).numLeaves)) •
      (InternalGrading.signedCompMultilinearMap (fun (_ : Fin (k + 2)) _ ↦ GH)
        (fun _ ↦ 𝒜.grading.piece) 𝒜.grading.piece
        ⟨𝒜.m (k + 2), MultilinearMap.mem_homogeneousSubmodule.mpr (𝒜.m_degree (k + 2) (by omega))⟩
        (fun i ↦ ⟨𝒜.treeBranch c GH (children i), MultilinearMap.mem_homogeneousSubmodule.mpr
          (𝒜.isHomogeneous_treeBranch c hh hincl (children i))⟩)).val by
    ext x; exact congrArg (· fun ij ↦ x (ReducedPlanarTree.nodeLeavesEquiv k children ij)) hsigma
  apply InternalGrading.multilinearMap_ext (fun _ ↦ GH)
  intro d x hx
  rw [smul_apply, InternalGrading.signedCompMultilinearMap_apply
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
        (InternalGrading.signedCompMultilinearMap (fun (_ : Fin (k + 2)) _ ↦ GH)
          (fun _ ↦ 𝒜.grading.piece) 𝒜.grading.piece
          ⟨𝒜.m (k + 2), MultilinearMap.mem_homogeneousSubmodule.mpr (𝒜.m_degree (k + 2) (by omega))⟩
          (fun i ↦ ⟨𝒜.treeBranch c GH (children i), MultilinearMap.mem_homogeneousSubmodule.mpr
            (𝒜.isHomogeneous_treeBranch c hh hincl (children i))⟩)).val).domDomCongr
        (ReducedPlanarTree.nodeLeavesEquiv k children) := by
  ext x
  refine (congrArg (fun M ↦ -c.homotopy (M x))
    (unsuspend_suspendedM_comp_suspendedTreeBranch 𝒜 c hh hincl k children)).trans ?_
  rw [smul_apply, smul_apply, map_smul, ← smul_neg]; rfl

/-- **Unsuspended recursion for `treeOperation` at an internal vertex**: it applies `c.proj` to the
Koszul-signed substitution (`InternalGrading.signedCompMultilinearMap`) of the child branch maps
into `𝒜.m (k + 2)`, multiplied by `(-1) ^ ∑ i, (k + 1 - i) * (1 - (children i).numLeaves)`. -/
theorem treeOperation_node (k : ℕ) (children : Fin (k + 2) → ReducedPlanarTree) :
    𝒜.treeOperation c GH (.node k children) =
      negOnePowCast R
        (∑ i : Fin (k + 2), ((k + 2 : ℤ) - 1 - i) * (1 - (children i).numLeaves)) •
      (c.proj.compMultilinearMap
        (InternalGrading.signedCompMultilinearMap (fun (_ : Fin (k + 2)) _ ↦ GH)
          (fun _ ↦ 𝒜.grading.piece) 𝒜.grading.piece
          ⟨𝒜.m (k + 2), MultilinearMap.mem_homogeneousSubmodule.mpr (𝒜.m_degree (k + 2) (by omega))⟩
          (fun i ↦ ⟨𝒜.treeBranch c GH (children i), MultilinearMap.mem_homogeneousSubmodule.mpr
            (𝒜.isHomogeneous_treeBranch c hh hincl (children i))⟩)).val).domDomCongr
        (ReducedPlanarTree.nodeLeavesEquiv k children) := by
  ext x
  refine (congrArg (fun M ↦ c.proj (M x))
    (unsuspend_suspendedM_comp_suspendedTreeBranch 𝒜 c hh hincl k children)).trans ?_
  rw [smul_apply, smul_apply, map_smul]; rfl

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
  refine (congrArg (· fun i ↦ x (finCongr hbin i))
    (𝒜.treeBranch_node c hh hincl 0 ![l, r])).trans ?_
  rw [smul_apply, MultilinearMap.domDomCongr_apply, LinearMap.compMultilinearMap_apply,
    LinearMap.neg_apply, InternalGrading.signedCompMultilinearMap_val,
    MultilinearMap.compLinearMap_apply, MultilinearMap.compMultilinearMap_apply,
    show (∑ i : Fin 2, (((0 : ℕ) : ℤ) + 2 - 1 - i) * (1 - (![l, r] i).numLeaves)) =
      1 - l.numLeaves by simp [Fin.sum_univ_two]]
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
  refine (congrArg (· fun i ↦ x (finCongr hbin i))
    (𝒜.treeOperation_node c hh hincl 0 ![l, r])).trans ?_
  rw [smul_apply, MultilinearMap.domDomCongr_apply, LinearMap.compMultilinearMap_apply,
    InternalGrading.signedCompMultilinearMap_val, MultilinearMap.compLinearMap_apply,
    MultilinearMap.compMultilinearMap_apply,
    show (∑ i : Fin 2, (((0 : ℕ) : ℤ) + 2 - 1 - i) * (1 - (![l, r] i).numLeaves)) =
      1 - l.numLeaves by simp [Fin.sum_univ_two]]
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
  refine congrArg (𝒜.m (k + 2)) (funext fun i ↦ ?_)
  rw [suspendedTreeBranch_leaf_apply, finCongr_apply,
    show Fin.cast hcor (ReducedPlanarTree.nodeLeavesEquiv k (fun _ ↦ .leaf) ⟨i, ⟨0, by decide⟩⟩) =
      i from Fin.ext (by simp),
    show (((ReducedPlanarTree.node k fun _ ↦ .leaf).numLeaves : ℤ) - 1 -
      (ReducedPlanarTree.nodeLeavesEquiv k (fun _ ↦ .leaf) ⟨i, ⟨0, by decide⟩⟩ : ℕ)) =
      (k + 2 : ℤ) - 1 - i by simp]
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
    exact congrArg _ (funext fun _ ↦ by simp)

/-- The unsuspended operation map of a reduced planar tree `t` is homogeneous of cohomological
degree `2 - t.numLeaves`. -/
theorem isHomogeneous_treeOperation (t : ReducedPlanarTree) :
    MultilinearMap.IsHomogeneous (𝒜.treeOperation c GH t)
      (fun _ ↦ GH.piece) GH.piece (2 - t.numLeaves) := by
  have hs : MultilinearMap.IsHomogeneous (𝒜.suspendedTreeOperation c t)
      (fun _ ↦ GH.piece) GH.piece (2 - t.numLeaves) := by
    have h := MultilinearMap.isHomogeneous_shift_const_iff.1
      (shift_one_piece_eq GH ▸ 𝒜.isHomogeneous_suspendedTreeOperation c hh hincl hproj t)
    simpa [show (1 : ℤ) + 1 - t.numLeaves = 2 - t.numLeaves by ring] using h
  simpa [treeOperation] using hs.compLinearMap fun _ ↦ isHomogeneous_koszulTwist_zero GH _

end OperationHomogeneous

end HomogeneousTree

end TauCeti.AInfinityAlgebra
