/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.AInfinity.Algebra
public import TauCeti.Algebra.Module.GradedModule.Multilinear.Composition
public import TauCeti.Algebra.Module.GradedModule.Multilinear.Suspension
public import TauCeti.Combinatorics.Tree.ReducedPlanar
import Mathlib.Order.Interval.Finset.Fin
import TauCeti.Algebra.BigOperators.Fin

/-!
# Planar-tree evaluation maps for A-infinity algebras

Given an `A∞` algebra `𝒜` on `A` together with linear maps `incl : H →ₗ[R] A`, `proj : A →ₗ[R] H`,
and `h : Module.End R A`, each reduced planar rooted tree `t : ReducedPlanarTree` defines the tree
summands used in `TauCeti.Algebra.Homology.AInfinity.Algebra.Transfer.Tree.Formula` to express the
homological-perturbation transfer `𝒜.transfer` and extending morphism `𝒜.transferInclusion`:
* Sign-free suspended maps `suspendedTreeBranch` (`H^{t.numLeaves} ⟶ A`, depending on `incl`, `h`)
  and `suspendedTreeOperation` (`H^{t.numLeaves} ⟶ H`, also using `proj`), applying `incl` at
  leaves, `𝒜.suspendedM (k + 2)` at `(k + 2)`-ary vertices, `-h` on internal edges (and at a branch
  root), and `proj` at an operation root.
* Given an internal grading `GH : InternalGrading R H ℤ` on `H`, precomposing input `l` with the
  Koszul twist `t.numLeaves - 1 - l` yields the unsuspended maps `treeBranch` and `treeOperation`.

When `h` has degree `-1` for `𝒜.grading.piece` and `incl`, `proj` have degree `0` between
`GH.piece` and `𝒜.grading.piece`, `treeBranch` and `treeOperation` have degrees `1 - t.numLeaves`
and `2 - t.numLeaves`, and vertex recursions factor via `InternalGrading.signedCompMultilinearMap`.

## Main definitions and results

* `TauCeti.AInfinityAlgebra.suspendedTreeBranch`, `TauCeti.AInfinityAlgebra.suspendedTreeOperation`,
  `TauCeti.AInfinityAlgebra.treeBranch`, `TauCeti.AInfinityAlgebra.treeOperation`.
* `TauCeti.AInfinityAlgebra.isHomogeneous_treeBranch` and
  `TauCeti.AInfinityAlgebra.isHomogeneous_treeOperation`: degrees `1 - t.numLeaves` and
  `2 - t.numLeaves` when `h` has degree `-1` and `incl`, `proj` have degree `0`.
* `TauCeti.AInfinityAlgebra.treeBranch_node`, `TauCeti.AInfinityAlgebra.treeOperation_node`,
  `TauCeti.AInfinityAlgebra.domDomCongr_treeBranch_binary_apply`,
  `TauCeti.AInfinityAlgebra.domDomCongr_treeOperation_binary_apply`,
  `TauCeti.AInfinityAlgebra.domDomCongr_treeBranch_corolla_apply`, and
  `TauCeti.AInfinityAlgebra.domDomCongr_treeOperation_corolla_apply`.
* `TauCeti.AInfinityAlgebra.suspendedTreeBranch_eq_zero_of_not_isBinary`,
  `TauCeti.AInfinityAlgebra.suspendedTreeOperation_eq_zero_of_not_isBinary`,
  `TauCeti.AInfinityAlgebra.treeBranch_eq_zero_of_not_isBinary`, and
  `TauCeti.AInfinityAlgebra.treeOperation_eq_zero_of_not_isBinary`: vanishing on non-binary trees
  when `𝒜.m k = 0` for `k ≥ 3`.

## References

* M. Kontsevich and Y. Soibelman, *Homological mirror symmetry and torus fibrations*, Section 6.4.
* J.-L. Loday and B. Vallette, *Algebraic Operads*, Chapter 10, Section 10.3.
* S. A. Merkulov, *Strongly homotopy algebras of a Kähler manifold*, IMRN 1999, no. 3, 153--164.
* E. Getzler and J. D. S. Jones, *A-infinity algebras and the cyclic bar complex*, Sections 1--2,
  and B. Keller, *Introduction to A-infinity algebras and modules*, Sections 3.1, 3.3, and 3.6.
-/

public section

open scoped BigOperators

universe uR uA uH

namespace TauCeti.AInfinityAlgebra

variable {R : Type uR} {A : Type uA} {H : Type uH}
  [CommRing R] [AddCommGroup A] [Module R A] [AddCommGroup H] [Module R H]

/-! ### Suspended and unsuspended planar-tree maps -/

private theorem domDomCongr_finCongr_apply_of_eq {N : Type*} [AddCommMonoid N] [Module R N]
    (F : (t : ReducedPlanarTree) → MultilinearMap (RingHom.id R) (fun _ : Fin t.numLeaves ↦ H) N)
    {t t' : ReducedPlanarTree} (h : t = t') {n : ℕ} (ht : t.numLeaves = n) (x : Fin n → H) :
    ((F t).domDomCongr (finCongr ht)) x = F t' (fun i ↦ x (finCongr (h ▸ ht) i)) := by
  subst h; exact MultilinearMap.domDomCongr_apply ..

section TreeDefs

variable (𝒜 : AInfinityAlgebra R A)

section BranchDefs

variable (incl : H →ₗ[R] A) (h : Module.End R A)

/-- The **suspended branch map** of a reduced planar tree `t`: a sign-free multilinear map
`H^{t.numLeaves} ⟶ A` applying `incl` at a single leaf and `-h ∘ 𝒜.suspendedM (k + 2)` to the child
branch maps at an internal node `node k children`. -/
noncomputable def suspendedTreeBranch :
    (t : ReducedPlanarTree) → MultilinearMap (RingHom.id R) (fun _ : Fin t.numLeaves ↦ H) A
  | .leaf => (MultilinearMap.ofSubsingleton (RingHom.id R) H A (0 : Fin 1)) incl
  | .node k children =>
      ((-h).compMultilinearMap ((𝒜.suspendedM (k + 2)).compMultilinearMap fun i ↦
        suspendedTreeBranch (children i))).domDomCongr finSigmaFinEquiv

/-- On the single leaf, `suspendedTreeBranch` applies `incl` to its sole input. -/
theorem suspendedTreeBranch_leaf : 𝒜.suspendedTreeBranch incl h .leaf =
    (MultilinearMap.ofSubsingleton (RingHom.id R) H A (0 : Fin 1)) incl := (rfl)

@[simp]
theorem suspendedTreeBranch_leaf_apply (x : Fin ReducedPlanarTree.leaf.numLeaves → H) :
    𝒜.suspendedTreeBranch incl h .leaf x = incl (x ⟨0, ReducedPlanarTree.leaf.numLeaves_pos⟩) :=
  MultilinearMap.ofSubsingleton_apply_apply ..

/-- Unfold `suspendedTreeBranch` at an internal `(k + 2)`-ary vertex. -/
theorem suspendedTreeBranch_node (k : ℕ) (children : Fin (k + 2) → ReducedPlanarTree) :
    𝒜.suspendedTreeBranch incl h (.node k children) =
      ((-h).compMultilinearMap ((𝒜.suspendedM (k + 2)).compMultilinearMap fun i ↦
        𝒜.suspendedTreeBranch incl h (children i))).domDomCongr finSigmaFinEquiv := (rfl)

/-- Evaluate `suspendedTreeBranch` at an internal `(k + 2)`-ary vertex on an input tuple `x`. -/
theorem suspendedTreeBranch_node_apply (k : ℕ) (children : Fin (k + 2) → ReducedPlanarTree)
    (x : Fin (ReducedPlanarTree.node k children).numLeaves → H) :
    𝒜.suspendedTreeBranch incl h (.node k children) x = -h (𝒜.suspendedM (k + 2) fun i ↦
      𝒜.suspendedTreeBranch incl h (children i) fun j ↦ x (finSigmaFinEquiv ⟨i, j⟩)) := (rfl)

/-- The **unsuspended branch map** `H^{t.numLeaves} ⟶ A` of a reduced planar tree `t`, obtained
from `suspendedTreeBranch` by precomposing input `l` with the Koszul twist `t.numLeaves - 1 - l`. -/
noncomputable def treeBranch (GH : InternalGrading R H ℤ) (t : ReducedPlanarTree) :
    MultilinearMap (RingHom.id R) (fun _ : Fin t.numLeaves ↦ H) A :=
  (𝒜.suspendedTreeBranch incl h t).compLinearMap fun l ↦ GH.koszulTwist ((t.numLeaves : ℤ) - 1 - l)

/-- Unfold `treeBranch` as `suspendedTreeBranch` precomposed with input Koszul twists. -/
theorem treeBranch_def (GH : InternalGrading R H ℤ) (t : ReducedPlanarTree) :
    𝒜.treeBranch incl h GH t = (𝒜.suspendedTreeBranch incl h t).compLinearMap fun l ↦
      GH.koszulTwist ((t.numLeaves : ℤ) - 1 - l) := (rfl)

/-- Evaluate `treeBranch` through `suspendedTreeBranch` precomposed with input Koszul twists. -/
theorem treeBranch_apply (GH : InternalGrading R H ℤ) (t : ReducedPlanarTree)
    (x : Fin t.numLeaves → H) : 𝒜.treeBranch incl h GH t x =
      𝒜.suspendedTreeBranch incl h t fun l ↦ GH.koszulTwist ((t.numLeaves : ℤ) - 1 - l) (x l) :=
  MultilinearMap.compLinearMap_apply ..

@[simp]
theorem treeBranch_leaf_apply (GH : InternalGrading R H ℤ)
    (x : Fin ReducedPlanarTree.leaf.numLeaves → H) :
    𝒜.treeBranch incl h GH .leaf x = incl (x ⟨0, ReducedPlanarTree.leaf.numLeaves_pos⟩) := by
  rw [treeBranch_apply, suspendedTreeBranch_leaf_apply]; simp [InternalGrading.koszulTwist_zero]

/-- On the single leaf, `treeBranch` applies `incl` to its sole input. -/
theorem treeBranch_leaf (GH : InternalGrading R H ℤ) : 𝒜.treeBranch incl h GH .leaf =
    (MultilinearMap.ofSubsingleton (RingHom.id R) H A (0 : Fin 1)) incl := by
  ext x; exact 𝒜.treeBranch_leaf_apply incl h GH x

private theorem treeBranch_binary_children (GH : InternalGrading R H ℤ)
    (l r : ReducedPlanarTree) (x : Fin (l.numLeaves + r.numLeaves) → H)
    (hbin : (∑ a : Fin 2, (![l, r] a).numLeaves) = l.numLeaves + r.numLeaves) :
    (fun i : Fin 2 ↦ 𝒜.treeBranch incl h GH (![l, r] i)
      (Sigma.curry (γ := fun _ _ ↦ H) (fun ij : Σ a : Fin 2, Fin (![l, r] a).numLeaves ↦
        GH.koszulTwist (∑ b : Fin 2, if ij.1 < b then (1 - ((![l, r] b).numLeaves : ℤ)) else 0)
          (x (finCongr hbin (finSigmaFinEquiv ij)))) i)) =
    ![𝒜.treeBranch incl h GH l (fun j ↦
        GH.koszulTwist (1 - r.numLeaves) (x (Fin.castAdd r.numLeaves j))),
      𝒜.treeBranch incl h GH r (fun j ↦ x (Fin.natAdd l.numLeaves j))] := by
  funext i; fin_cases i
  · have h0 : (∑ b : Fin 2, if (0 : Fin 2) < b then (1 - ((![l, r] b).numLeaves : ℤ)) else 0) =
        1 - r.numLeaves := by simp [Fin.sum_univ_two]
    dsimp only [Fin.zero_eta, Matrix.cons_val_zero]
    refine congrArg (𝒜.treeBranch incl h GH l) (funext fun j ↦ ?_)
    simp only [Sigma.curry, h0]
    exact congrArg _ (congrArg x (Fin.ext (by simpa using (Fin.val_castAdd r.numLeaves j).symm)))
  · have h1 : (∑ b : Fin 2, if (1 : Fin 2) < b then (1 - ((![l, r] b).numLeaves : ℤ)) else 0) =
        0 := by simp [Fin.sum_univ_two]
    dsimp only [Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    refine congrArg (𝒜.treeBranch incl h GH r) (funext fun j ↦ ?_)
    simp only [Sigma.curry, h1, GH.koszulTwist_zero, LinearMap.id_apply]
    exact congrArg x (Fin.ext (by simpa using (Fin.val_natAdd l.numLeaves j).symm))

private theorem suspendedM_ofComposition_apply {n : ℕ} (d : Composition n) (hd : 2 ≤ d.length)
    (children : ∀ i : Fin d.length, ReducedPlanarTree.Arity (d.blocksFun i)) (x : Fin n → H)
    (hnode : (∑ i : Fin (d.length - 2 + 2),
      (children (i.cast (Nat.sub_add_cancel hd))).val.numLeaves) = n) :
    𝒜.suspendedM (d.length - 2 + 2) (fun i ↦
      (𝒜.suspendedTreeBranch incl h (children (i.cast (Nat.sub_add_cancel hd))).val) fun j ↦
        x (finCongr hnode (finSigmaFinEquiv
          (n := fun i ↦ (children (i.cast (Nat.sub_add_cancel hd))).val.numLeaves) ⟨i, j⟩))) =
    𝒜.suspendedM d.length fun i ↦ ((𝒜.suspendedTreeBranch incl h (children i).val).domDomCongr
      (finCongr (children i).property)) (x ∘ d.embedding i) := by
  have hlen : d.length - 2 + 2 = d.length := Nat.sub_add_cancel hd
  rw [← 𝒜.suspendedM_congr hlen]
  refine congrArg (𝒜.suspendedM (d.length - 2 + 2)) (funext fun i ↦ ?_)
  rw [MultilinearMap.domDomCongr_apply]
  refine congrArg (𝒜.suspendedTreeBranch incl h (children (i.cast hlen)).val) (funext fun j ↦ ?_)
  refine congrArg x (Fin.ext ?_)
  simp only [finCongr_apply, Fin.val_cast, finSigmaFinEquiv_apply, d.coe_embedding]
  rw [d.sizeUpTo_eq_sum_blocksFun (by omega : i.val ≤ d.length)]
  exact congrArg (· + j.val) (Finset.sum_congr rfl fun a _ ↦ (children _).property)

/-- Evaluating `suspendedTreeBranch` on `ReducedPlanarTree.ofComposition` applies
`-h ∘ 𝒜.suspendedM d.length` to the child branch evaluations on `x ∘ d.embedding i`. -/
theorem domDomCongr_suspendedTreeBranch_ofComposition_apply {n : ℕ} (d : Composition n)
    (hd : 2 ≤ d.length) (children : ∀ i : Fin d.length, ReducedPlanarTree.Arity (d.blocksFun i))
    (x : Fin n → H) :
    ((𝒜.suspendedTreeBranch incl h (ReducedPlanarTree.ofComposition d hd children).val).domDomCongr
        (finCongr (ReducedPlanarTree.ofComposition d hd children).property)) x =
      -h (𝒜.suspendedM d.length fun i ↦
        ((𝒜.suspendedTreeBranch incl h (children i).val).domDomCongr
          (finCongr (children i).property)) (x ∘ d.embedding i)) := by
  rw [domDomCongr_finCongr_apply_of_eq (𝒜.suspendedTreeBranch incl h)
      (ReducedPlanarTree.val_ofComposition d hd children), suspendedTreeBranch_node_apply]
  exact congrArg (-h ·) (𝒜.suspendedM_ofComposition_apply incl h d hd children x _)

end BranchDefs

section OperationDefs

variable (incl : H →ₗ[R] A) (proj : A →ₗ[R] H) (h : Module.End R A)

/-- The **suspended operation map** of a reduced planar tree `t`: zero on the single leaf, and
`proj ∘ 𝒜.suspendedM (k + 2)` applied to the child branch maps at `node k children`. -/
noncomputable def suspendedTreeOperation :
    (t : ReducedPlanarTree) → MultilinearMap (RingHom.id R) (fun _ : Fin t.numLeaves ↦ H) H
  | .leaf => 0
  | .node k children =>
      (proj.compMultilinearMap ((𝒜.suspendedM (k + 2)).compMultilinearMap fun i ↦
        𝒜.suspendedTreeBranch incl h (children i))).domDomCongr finSigmaFinEquiv

@[simp]
theorem suspendedTreeOperation_leaf : 𝒜.suspendedTreeOperation incl proj h .leaf = 0 := (rfl)

/-- Unfold `suspendedTreeOperation` at an internal `(k + 2)`-ary vertex. -/
theorem suspendedTreeOperation_node (k : ℕ) (children : Fin (k + 2) → ReducedPlanarTree) :
    𝒜.suspendedTreeOperation incl proj h (.node k children) =
      (proj.compMultilinearMap ((𝒜.suspendedM (k + 2)).compMultilinearMap fun i ↦
        𝒜.suspendedTreeBranch incl h (children i))).domDomCongr finSigmaFinEquiv := (rfl)

/-- Evaluate `suspendedTreeOperation` at an internal `(k + 2)`-ary vertex on an input tuple `x`. -/
theorem suspendedTreeOperation_node_apply (k : ℕ) (children : Fin (k + 2) → ReducedPlanarTree)
    (x : Fin (ReducedPlanarTree.node k children).numLeaves → H) :
    𝒜.suspendedTreeOperation incl proj h (.node k children) x = proj (𝒜.suspendedM (k + 2) fun i ↦
      𝒜.suspendedTreeBranch incl h (children i) fun j ↦ x (finSigmaFinEquiv ⟨i, j⟩)) := (rfl)

/-- The **unsuspended operation map** `H^{t.numLeaves} ⟶ H` of a reduced planar tree `t`, obtained
from `suspendedTreeOperation` by precomposing input `l` with Koszul twist `t.numLeaves - 1 - l`. -/
noncomputable def treeOperation (GH : InternalGrading R H ℤ) (t : ReducedPlanarTree) :
    MultilinearMap (RingHom.id R) (fun _ : Fin t.numLeaves ↦ H) H :=
  (𝒜.suspendedTreeOperation incl proj h t).compLinearMap fun l ↦
    GH.koszulTwist ((t.numLeaves : ℤ) - 1 - l)

/-- Unfold `treeOperation` as `suspendedTreeOperation` precomposed with input Koszul twists. -/
theorem treeOperation_def (GH : InternalGrading R H ℤ) (t : ReducedPlanarTree) :
    𝒜.treeOperation incl proj h GH t = (𝒜.suspendedTreeOperation incl proj h t).compLinearMap
      fun l ↦ GH.koszulTwist ((t.numLeaves : ℤ) - 1 - l) := (rfl)

/-- Evaluate `treeOperation` through `suspendedTreeOperation` precomposed with Koszul twists. -/
theorem treeOperation_apply (GH : InternalGrading R H ℤ) (t : ReducedPlanarTree)
    (x : Fin t.numLeaves → H) : 𝒜.treeOperation incl proj h GH t x =
      𝒜.suspendedTreeOperation incl proj h t fun l ↦
        GH.koszulTwist ((t.numLeaves : ℤ) - 1 - l) (x l) :=
  MultilinearMap.compLinearMap_apply ..

@[simp]
theorem treeOperation_leaf (GH : InternalGrading R H ℤ) :
    𝒜.treeOperation incl proj h GH .leaf = 0 := by
  rw [treeOperation, suspendedTreeOperation_leaf, MultilinearMap.zero_compLinearMap]

/-- Evaluating `suspendedTreeOperation` on `ReducedPlanarTree.ofComposition` applies
`proj ∘ 𝒜.suspendedM d.length` to the child branch evaluations on `x ∘ d.embedding i`. -/
theorem domDomCongr_suspendedTreeOperation_ofComposition_apply {n : ℕ} (d : Composition n)
    (hd : 2 ≤ d.length) (children : ∀ i : Fin d.length, ReducedPlanarTree.Arity (d.blocksFun i))
    (x : Fin n → H) :
    ((𝒜.suspendedTreeOperation incl proj h
          (ReducedPlanarTree.ofComposition d hd children).val).domDomCongr
        (finCongr (ReducedPlanarTree.ofComposition d hd children).property)) x =
      proj (𝒜.suspendedM d.length fun i ↦
        ((𝒜.suspendedTreeBranch incl h (children i).val).domDomCongr
          (finCongr (children i).property)) (x ∘ d.embedding i)) := by
  rw [domDomCongr_finCongr_apply_of_eq (𝒜.suspendedTreeOperation incl proj h)
      (ReducedPlanarTree.val_ofComposition d hd children), suspendedTreeOperation_node_apply]
  exact congrArg (proj ·) (𝒜.suspendedM_ofComposition_apply incl h d hd children x _)

end OperationDefs
end TreeDefs

/-! ### Homogeneity and Koszul-signed unsuspended node formulas -/

private theorem unsuspend_node_sign_eq (k : ℕ) (children : Fin (k + 2) → ReducedPlanarTree)
    (d : (Σ i : Fin (k + 2), Fin (children i).numLeaves) → ℤ) :
    (∑ i : Fin (k + 2), (((k + 2 : ℤ) - 1 - i) * (1 - (children i).numLeaves) +
      ∑ j : Fin (children i).numLeaves, (((k + 2 : ℤ) - 1 - i) +
        ∑ b : Fin (k + 2), if i < b then ((children b).numLeaves : ℤ) else 0) * d ⟨i, j⟩)) =
    ((∑ i : Fin (k + 2), ((k + 2 : ℤ) - 1 - i) * (1 - (children i).numLeaves)) +
      ∑ ij : Σ i : Fin (k + 2), Fin (children i).numLeaves,
        (∑ b : Fin (k + 2), if ij.1 < b then (1 - ((children b).numLeaves : ℤ)) else 0) * d ij) +
      2 * ∑ ij : Σ i : Fin (k + 2), Fin (children i).numLeaves,
        (∑ b : Fin (k + 2), if ij.1 < b then ((children b).numLeaves : ℤ) else 0) * d ij := by
  rw [Finset.sum_add_distrib, Fintype.sum_sigma, Fintype.sum_sigma, add_assoc]
  congr 1
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  have hcard : ((k + 2 : ℤ) - 1 - i) = ∑ b : Fin (k + 2), if i < b then (1 : ℤ) else 0 := by
    rw [← Finset.sum_filter, Finset.filter_lt_eq_Ioi, Finset.sum_const, Fin.card_Ioi,
      nsmul_eq_mul, mul_one]
    have hi := i.isLt; omega
  have hsum1 : (∑ b : Fin (k + 2), if i < b then (1 - ((children b).numLeaves : ℤ)) else 0) +
      2 * (∑ b : Fin (k + 2), if i < b then ((children b).numLeaves : ℤ) else 0) =
      ((k + 2 : ℤ) - 1 - i) +
        ∑ b : Fin (k + 2), if i < b then ((children b).numLeaves : ℤ) else 0 := by
    rw [hcard, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun b _ ↦ by split_ifs <;> ring
  rw [← hsum1]; ring

section HomogeneousTree

variable (𝒜 : AInfinityAlgebra R A) {GH : InternalGrading R H ℤ}

section BranchHomogeneous

variable (incl : H →ₗ[R] A) (h : Module.End R A)
  (hh : LinearMap.IsHomogeneous h 𝒜.grading.piece 𝒜.grading.piece (-1))
  (hincl : LinearMap.IsHomogeneous incl GH.piece 𝒜.grading.piece 0)

include hh hincl

/-- The suspended branch map of every reduced planar tree has degree zero between the suspended
gradings `(GH.shift 1).piece` and `(𝒜.grading.shift 1).piece`. -/
theorem isHomogeneous_suspendedTreeBranch (t : ReducedPlanarTree) :
    MultilinearMap.IsHomogeneous (𝒜.suspendedTreeBranch incl h t)
      (fun _ ↦ (GH.shift 1).piece) (𝒜.grading.shift 1).piece 0 := by
  induction t with
  | leaf =>
    rw [MultilinearMap.isHomogeneous_def]; intro d x hx
    have hd : (∑ i, d i) = d ⟨0, by decide⟩ := Fin.sum_univ_one d
    rw [suspendedTreeBranch_leaf_apply, hd]
    simpa only [add_zero] using
      (LinearMap.isHomogeneous_shift_piece_iff.2 hincl).map_mem (hx ⟨0, by decide⟩)
  | node k children ih =>
    rw [suspendedTreeBranch_node]
    have hinner := (𝒜.isHomogeneous_suspendedM (k + 2)).compMultilinearMap ih
    simp only [Finset.sum_const_zero, zero_add] at hinner
    have hcomp : MultilinearMap.IsHomogeneous
        ((-h).compMultilinearMap ((𝒜.suspendedM (k + 2)).compMultilinearMap fun i ↦
          𝒜.suspendedTreeBranch incl h (children i)))
        (fun _ ↦ (GH.shift 1).piece) (𝒜.grading.shift 1).piece 0 := by
      simpa only [add_neg_cancel] using
        (LinearMap.isHomogeneous_shift_piece_iff.2 hh).neg.compMultilinearMap hinner
    exact hcomp.domDomCongr finSigmaFinEquiv

/-- The unsuspended branch map of a reduced planar tree `t` is homogeneous of cohomological degree
`1 - t.numLeaves`. -/
theorem isHomogeneous_treeBranch (t : ReducedPlanarTree) :
    MultilinearMap.IsHomogeneous (𝒜.treeBranch incl h GH t)
      (fun _ ↦ GH.piece) 𝒜.grading.piece (1 - t.numLeaves) := by
  have hs : MultilinearMap.IsHomogeneous (𝒜.suspendedTreeBranch incl h t)
      (fun _ ↦ (GH.shift 1).piece) (Graded.shift 𝒜.grading.piece 1) 0 := by
    simpa only [MultilinearMap.isHomogeneous_def, InternalGrading.shift_piece, Graded.shift_apply]
      using 𝒜.isHomogeneous_suspendedTreeBranch incl h hh hincl t
  have hm := ((InternalGrading.suspensionEquiv (fun _ : Fin t.numLeaves ↦ GH) 𝒜.grading.piece
    0).symm ⟨_, MultilinearMap.mem_homogeneousSubmodule.mpr hs⟩).property
  rwa [MultilinearMap.mem_homogeneousSubmodule, InternalGrading.suspensionEquiv_symm_val,
    zero_add] at hm

private theorem koszulTwist_suspendedTreeBranch_apply (k : ℕ)
    (children : Fin (k + 2) → ReducedPlanarTree)
    (d : (Σ a : Fin (k + 2), Fin (children a).numLeaves) → ℤ)
    (x : (Σ a : Fin (k + 2), Fin (children a).numLeaves) → H)
    (hx : ∀ ij, x ij ∈ GH.piece (d ij)) (i : Fin (k + 2)) :
    𝒜.grading.koszulTwist (((k + 2 : ℕ) : ℤ) - 1 - i) (𝒜.suspendedTreeBranch incl h (children i)
      (Sigma.curry (γ := fun _ _ ↦ H) (fun ij ↦ GH.koszulTwist
        (((ReducedPlanarTree.node k children).numLeaves : ℤ) - 1 -
          (finSigmaFinEquiv (n := fun a ↦ (children a).numLeaves) ij : ℕ)) (x ij)) i)) =
      negOnePowCast R (((k + 2 : ℤ) - 1 - i) * (1 - (children i).numLeaves) +
        ∑ j : Fin (children i).numLeaves, (((k + 2 : ℤ) - 1 - i) +
          ∑ b : Fin (k + 2), if i < b then ((children b).numLeaves : ℤ) else 0) * d ⟨i, j⟩) •
        𝒜.treeBranch incl h GH (children i) (fun j ↦ x ⟨i, j⟩) := by
  rw [Nat.cast_add, Nat.cast_ofNat]
  let R_i : ℤ := ∑ b : Fin (k + 2), if i < b then ((children b).numLeaves : ℤ) else 0
  have hparam (j : Fin (children i).numLeaves) :
      (((ReducedPlanarTree.node k children).numLeaves : ℤ) - 1 -
        (finSigmaFinEquiv (n := fun a ↦ (children a).numLeaves) ⟨i, j⟩ : ℕ)) =
        (((children i).numLeaves : ℤ) - 1 - j) + R_i := by
    have hflt : Finset.univ.filter (· < i) = Finset.Iio i := by ext; simp
    have htot : (∑ a : Fin (k + 2), ((children a).numLeaves : ℤ)) =
        (∑ a ∈ Finset.Iio i, ((children a).numLeaves : ℤ)) + (children i).numLeaves + R_i := by
      rw [← Finset.sum_compl_add_sum {i}, ← Finset.Ioi_disjUnion_Iio i, Finset.sum_disjUnion,
        Finset.sum_singleton]
      dsimp only [R_i]; rw [← Finset.sum_filter, Finset.filter_lt_eq_Ioi]; ring
    rw [val_finSigmaFinEquiv_eq_sum_filter, hflt, ReducedPlanarTree.numLeaves_node, Nat.cast_sum,
      htot, Nat.cast_add, Nat.cast_sum]; ring
  have htw : Sigma.curry (γ := fun _ _ ↦ H) (fun ij ↦ GH.koszulTwist
      (((ReducedPlanarTree.node k children).numLeaves : ℤ) - 1 -
        (finSigmaFinEquiv (n := fun a ↦ (children a).numLeaves) ij : ℕ)) (x ij)) i =
      fun j ↦ negOnePowCast R (R_i * d ⟨i, j⟩) •
        GH.koszulTwist (((children i).numLeaves : ℤ) - 1 - j) (x ⟨i, j⟩) := by
    funext j; simp only [Sigma.curry]
    rw [hparam j, ← GH.koszulTwist_comp, LinearMap.comp_apply,
      GH.koszulTwist_apply_of_mem (hx ⟨i, j⟩), map_smul, negOnePowCast_eq_intCast]
  rw [htw, MultilinearMap.map_smul_univ]; simp only [RingHom.id_apply]
  rw [← negOnePowCast_sum, ← treeBranch_apply, map_smul, 𝒜.grading.koszulTwist_apply_of_mem
      ((𝒜.isHomogeneous_treeBranch incl h hh hincl (children i)).map_mem (fun j ↦ d ⟨i, j⟩)
        (fun j ↦ x ⟨i, j⟩) fun j ↦ hx ⟨i, j⟩),
    ← negOnePowCast_eq_intCast, smul_smul, ← negOnePowCast_add]
  congr 2; rw [mul_add, ← add_assoc, Finset.mul_sum, ← Finset.sum_add_distrib]
  have hsub (j : Fin (children i).numLeaves) : R_i * d ⟨i, j⟩ + ((k + 2 : ℤ) - 1 - i) * d ⟨i, j⟩ =
      (((k + 2 : ℤ) - 1 - i) + R_i) * d ⟨i, j⟩ := by ring
  simp_rw [hsub]; ring

private theorem unsuspend_suspendedM_comp_suspendedTreeBranch (k : ℕ)
    (children : Fin (k + 2) → ReducedPlanarTree) :
    (((𝒜.suspendedM (k + 2)).compMultilinearMap fun i ↦
        𝒜.suspendedTreeBranch incl h (children i)).compLinearMap
      fun ij ↦ GH.koszulTwist (((ReducedPlanarTree.node k children).numLeaves : ℤ) - 1 -
        (finSigmaFinEquiv (n := fun a ↦ (children a).numLeaves) ij : ℕ))) =
    negOnePowCast R (∑ i : Fin (k + 2), ((k + 2 : ℤ) - 1 - i) * (1 - (children i).numLeaves)) •
    (InternalGrading.signedCompMultilinearMap (fun (_ : Fin (k + 2)) _ ↦ GH)
      (fun _ ↦ 𝒜.grading.piece) 𝒜.grading.piece
      ⟨𝒜.m (k + 2), MultilinearMap.mem_homogeneousSubmodule.mpr (𝒜.m_degree (k + 2) (by omega))⟩
      (fun i ↦ ⟨𝒜.treeBranch incl h GH (children i), MultilinearMap.mem_homogeneousSubmodule.mpr
        (𝒜.isHomogeneous_treeBranch incl h hh hincl (children i))⟩)).val := by
  apply InternalGrading.multilinearMap_ext (fun _ ↦ GH); intro d x hx
  rw [smul_apply, InternalGrading.signedCompMultilinearMap_apply
      (fun (_ : Fin (k + 2)) _ ↦ GH) (fun _ ↦ 𝒜.grading.piece) 𝒜.grading.piece _ _ d x hx,
    smul_smul, ← negOnePowCast_add, MultilinearMap.compLinearMap_apply,
    MultilinearMap.compMultilinearMap_apply, suspendedM_apply,
    funext (koszulTwist_suspendedTreeBranch_apply 𝒜 incl h hh hincl k children d x hx),
    MultilinearMap.map_smul_univ]; simp only [RingHom.id_apply]
  rw [← negOnePowCast_sum, unsuspend_node_sign_eq k children d, negOnePowCast_add,
    negOnePowCast_two_mul, mul_one]

omit 𝒜 incl h hh hincl in
private theorem compLinearMap_domDomCongr_compMultilinearMap {N : Type*} [AddCommMonoid N]
    [Module R N] (L : A →ₗ[R] N) {k : ℕ} (children : Fin (k + 2) → ReducedPlanarTree)
    (M S : MultilinearMap (RingHom.id R) (fun _ : Σ i, Fin (children i).numLeaves ↦ H) A) (c : R)
    (hMS : M.compLinearMap (fun ij ↦ GH.koszulTwist
        (((ReducedPlanarTree.node k children).numLeaves : ℤ) - 1 -
          (finSigmaFinEquiv (n := fun a ↦ (children a).numLeaves) ij : ℕ))) = c • S) :
    ((L.compMultilinearMap M).domDomCongr finSigmaFinEquiv).compLinearMap
        (fun l ↦ GH.koszulTwist (((ReducedPlanarTree.node k children).numLeaves : ℤ) - 1 - l)) =
      c • (L.compMultilinearMap S).domDomCongr finSigmaFinEquiv := by
  ext x; simp only [MultilinearMap.compLinearMap_apply, MultilinearMap.domDomCongr_apply,
    LinearMap.compMultilinearMap_apply, smul_apply]
  simpa only [MultilinearMap.compLinearMap_apply, smul_apply, map_smul] using
    congrArg L (MultilinearMap.congr_fun hMS (fun ij ↦ x (finSigmaFinEquiv ij)))

/-- **Unsuspended recursion for `treeBranch` at an internal vertex**: it applies `-h` to the
Koszul-signed substitution (`InternalGrading.signedCompMultilinearMap`) of the child branch maps
into `𝒜.m (k + 2)`, multiplied by `(-1) ^ ∑ i, (k + 1 - i) * (1 - (children i).numLeaves)`. -/
theorem treeBranch_node (k : ℕ) (children : Fin (k + 2) → ReducedPlanarTree) :
    𝒜.treeBranch incl h GH (.node k children) =
      negOnePowCast R (∑ i : Fin (k + 2), ((k + 2 : ℤ) - 1 - i) * (1 - (children i).numLeaves)) •
      ((-h).compMultilinearMap
        (InternalGrading.signedCompMultilinearMap (fun (_ : Fin (k + 2)) _ ↦ GH)
          (fun _ ↦ 𝒜.grading.piece) 𝒜.grading.piece
          ⟨𝒜.m (k + 2), MultilinearMap.mem_homogeneousSubmodule.mpr (𝒜.m_degree (k + 2) (by omega))⟩
          (fun i ↦ ⟨𝒜.treeBranch incl h GH (children i), MultilinearMap.mem_homogeneousSubmodule.mpr
            (𝒜.isHomogeneous_treeBranch incl h hh hincl (children i))⟩)).val).domDomCongr
        finSigmaFinEquiv := by
  rw [treeBranch_def, suspendedTreeBranch_node]
  exact compLinearMap_domDomCongr_compMultilinearMap (-h) children _ _ _
    (unsuspend_suspendedM_comp_suspendedTreeBranch 𝒜 incl h hh hincl k children)

private theorem unsuspend_binary_apply (l r : ReducedPlanarTree)
    (x : Fin (l.numLeaves + r.numLeaves) → H)
    (hbin : (∑ a : Fin 2, (![l, r] a).numLeaves) = l.numLeaves + r.numLeaves) :
    𝒜.suspendedM (0 + 2) (fun i ↦ 𝒜.suspendedTreeBranch incl h (![l, r] i) fun j ↦
      GH.koszulTwist (((ReducedPlanarTree.node 0 ![l, r]).numLeaves : ℤ) - 1 -
        (finSigmaFinEquiv (n := fun a ↦ (![l, r] a).numLeaves) ⟨i, j⟩ : ℕ))
        (x (finCongr hbin (finSigmaFinEquiv ⟨i, j⟩)))) =
    negOnePowCast R (1 - l.numLeaves) • 𝒜.m 2
      ![𝒜.treeBranch incl h GH l (fun j ↦
          GH.koszulTwist (1 - r.numLeaves) (x (Fin.castAdd r.numLeaves j))),
        𝒜.treeBranch incl h GH r (fun j ↦ x (Fin.natAdd l.numLeaves j))] := by
  have hsum : (∑ i : Fin 2, (((0 : ℕ) : ℤ) + 2 - 1 - i) * (1 - (![l, r] i).numLeaves)) =
      1 - l.numLeaves := by simp [Fin.sum_univ_two]
  have hu := MultilinearMap.congr_fun
    (unsuspend_suspendedM_comp_suspendedTreeBranch 𝒜 incl h hh hincl 0 ![l, r])
    (fun ij ↦ x (finCongr hbin (finSigmaFinEquiv ij)))
  simp only [MultilinearMap.compLinearMap_apply, MultilinearMap.compMultilinearMap_apply,
    smul_apply, InternalGrading.signedCompMultilinearMap_val, hsum] at hu
  exact hu.trans (congrArg (fun v ↦ negOnePowCast R (1 - l.numLeaves) • 𝒜.m 2 v)
    (treeBranch_binary_children 𝒜 incl h GH l r x hbin))

/-- **Unsuspended recursion for `treeBranch` on a binary vertex `binary l r`**: the left inputs are
twisted by `1 - r.numLeaves` from moving the right branch past them, and the overall sign is
`(-1) ^ (1 - l.numLeaves)`. -/
theorem domDomCongr_treeBranch_binary_apply (l r : ReducedPlanarTree)
    (x : Fin (l.numLeaves + r.numLeaves) → H) :
    ((𝒜.treeBranch incl h GH (.binary l r)).domDomCongr
        (finCongr (ReducedPlanarTree.numLeaves_binary l r))) x =
      negOnePowCast R (1 - l.numLeaves) • (-h (𝒜.m 2
        ![𝒜.treeBranch incl h GH l (fun j ↦
            GH.koszulTwist (1 - r.numLeaves) (x (Fin.castAdd r.numLeaves j))),
          𝒜.treeBranch incl h GH r (fun j ↦ x (Fin.natAdd l.numLeaves j))])) := by
  rw [domDomCongr_finCongr_apply_of_eq (𝒜.treeBranch incl h GH) (ReducedPlanarTree.binary_def l r),
    treeBranch_apply, suspendedTreeBranch_node_apply]
  exact (congrArg ((-h : Module.End R A) ·)
    (unsuspend_binary_apply 𝒜 incl h hh hincl l r x _)).trans (map_smul (-h) _ _)

/-- **Unsuspended recursion for `treeOperation` at an internal vertex**: it applies `proj` to the
Koszul-signed substitution (`InternalGrading.signedCompMultilinearMap`) of the child branch maps
into `𝒜.m (k + 2)`, multiplied by `(-1) ^ ∑ i, (k + 1 - i) * (1 - (children i).numLeaves)`. -/
theorem treeOperation_node (proj : A →ₗ[R] H) (k : ℕ) (children : Fin (k + 2) → ReducedPlanarTree) :
    𝒜.treeOperation incl proj h GH (.node k children) =
      negOnePowCast R (∑ i : Fin (k + 2), ((k + 2 : ℤ) - 1 - i) * (1 - (children i).numLeaves)) •
      (proj.compMultilinearMap
        (InternalGrading.signedCompMultilinearMap (fun (_ : Fin (k + 2)) _ ↦ GH)
          (fun _ ↦ 𝒜.grading.piece) 𝒜.grading.piece
          ⟨𝒜.m (k + 2), MultilinearMap.mem_homogeneousSubmodule.mpr (𝒜.m_degree (k + 2) (by omega))⟩
          (fun i ↦ ⟨𝒜.treeBranch incl h GH (children i), MultilinearMap.mem_homogeneousSubmodule.mpr
            (𝒜.isHomogeneous_treeBranch incl h hh hincl (children i))⟩)).val).domDomCongr
        finSigmaFinEquiv := by
  rw [treeOperation_def, suspendedTreeOperation_node]
  exact compLinearMap_domDomCongr_compMultilinearMap proj children _ _ _
    (unsuspend_suspendedM_comp_suspendedTreeBranch 𝒜 incl h hh hincl k children)

/-- **Unsuspended recursion for `treeOperation` on a binary vertex `binary l r`**: the left inputs
are twisted by `1 - r.numLeaves` from moving the right branch past them, and the overall sign is
`(-1) ^ (1 - l.numLeaves)`. -/
theorem domDomCongr_treeOperation_binary_apply (proj : A →ₗ[R] H) (l r : ReducedPlanarTree)
    (x : Fin (l.numLeaves + r.numLeaves) → H) :
    ((𝒜.treeOperation incl proj h GH (.binary l r)).domDomCongr
        (finCongr (ReducedPlanarTree.numLeaves_binary l r))) x =
      negOnePowCast R (1 - l.numLeaves) • proj (𝒜.m 2
        ![𝒜.treeBranch incl h GH l (fun j ↦
            GH.koszulTwist (1 - r.numLeaves) (x (Fin.castAdd r.numLeaves j))),
          𝒜.treeBranch incl h GH r (fun j ↦ x (Fin.natAdd l.numLeaves j))]) := by
  rw [domDomCongr_finCongr_apply_of_eq (𝒜.treeOperation incl proj h GH)
      (ReducedPlanarTree.binary_def l r), treeOperation_apply, suspendedTreeOperation_node_apply]
  exact (congrArg (proj ·) (unsuspend_binary_apply 𝒜 incl h hh hincl l r x _)).trans
    (map_smul proj _ _)

end BranchHomogeneous

section Corolla

variable (incl : H →ₗ[R] A) (h : Module.End R A)
  (hincl : LinearMap.IsHomogeneous incl GH.piece 𝒜.grading.piece 0)
include hincl

private theorem corolla_suspendedM_apply (k : ℕ) (x : Fin (k + 2) → H)
    (hcor : (∑ _ : Fin (k + 2), ReducedPlanarTree.leaf.numLeaves) = k + 2) :
    𝒜.suspendedM (k + 2) (fun i ↦ (𝒜.suspendedTreeBranch incl h .leaf) fun j ↦
      GH.koszulTwist (((ReducedPlanarTree.node k fun _ ↦ .leaf).numLeaves : ℤ) - 1 -
          (finSigmaFinEquiv (n := fun _ : Fin (k + 2) ↦ ReducedPlanarTree.leaf.numLeaves)
            ⟨i, j⟩ : ℕ))
        (x (finCongr hcor (finSigmaFinEquiv
          (n := fun _ : Fin (k + 2) ↦ ReducedPlanarTree.leaf.numLeaves) ⟨i, j⟩)))) =
      𝒜.m (k + 2) fun i ↦ incl (x i) := by
  rw [suspendedM_apply]; refine congrArg (𝒜.m (k + 2)) (funext fun i ↦ ?_)
  have hidx : Fin.cast hcor
      (finSigmaFinEquiv (n := fun _ : Fin (k + 2) ↦ ReducedPlanarTree.leaf.numLeaves)
        ⟨i, ⟨0, ReducedPlanarTree.leaf.numLeaves_pos⟩⟩) = i := Fin.ext (by simp)
  have hexp : (((ReducedPlanarTree.node k fun _ ↦ .leaf).numLeaves : ℤ) - 1 -
      (finSigmaFinEquiv (n := fun _ : Fin (k + 2) ↦ ReducedPlanarTree.leaf.numLeaves)
        ⟨i, ⟨0, ReducedPlanarTree.leaf.numLeaves_pos⟩⟩ : ℕ)) = (k + 2 : ℤ) - 1 - i := by simp
  rw [suspendedTreeBranch_leaf_apply, finCongr_apply, hidx, hexp]
  simpa [mul_zero] using hincl.koszulTwist_apply ((k + 2 : ℤ) - 1 - i)
    (GH.koszulTwist ((k + 2 : ℤ) - 1 - i) (x i))

/-- On the `(k + 2)`-input corolla, `treeBranch` applies `-h ∘ 𝒜.m (k + 2)` to the included inputs
with no extra Koszul signs. -/
theorem domDomCongr_treeBranch_corolla_apply (k : ℕ) (x : Fin (k + 2) → H) :
    ((𝒜.treeBranch incl h GH (.corolla k)).domDomCongr
        (finCongr (ReducedPlanarTree.numLeaves_corolla k))) x =
      -h (𝒜.m (k + 2) fun i ↦ incl (x i)) := by
  rw [domDomCongr_finCongr_apply_of_eq (𝒜.treeBranch incl h GH) (ReducedPlanarTree.corolla_def k),
    treeBranch_apply, suspendedTreeBranch_node_apply]
  exact congrArg (-h ·) (corolla_suspendedM_apply 𝒜 incl h hincl k x _)

/-- On the `(k + 2)`-input corolla, `treeOperation` applies `proj ∘ 𝒜.m (k + 2)` to the included
inputs with no extra Koszul signs. -/
theorem domDomCongr_treeOperation_corolla_apply (proj : A →ₗ[R] H) (k : ℕ) (x : Fin (k + 2) → H) :
    ((𝒜.treeOperation incl proj h GH (.corolla k)).domDomCongr
        (finCongr (ReducedPlanarTree.numLeaves_corolla k))) x =
      proj (𝒜.m (k + 2) fun i ↦ incl (x i)) := by
  rw [domDomCongr_finCongr_apply_of_eq (𝒜.treeOperation incl proj h GH)
      (ReducedPlanarTree.corolla_def k), treeOperation_apply, suspendedTreeOperation_node_apply]
  exact congrArg (proj ·) (corolla_suspendedM_apply 𝒜 incl h hincl k x _)

end Corolla

section OperationHomogeneous

variable (incl : H →ₗ[R] A) (proj : A →ₗ[R] H) (h : Module.End R A)
  (hh : LinearMap.IsHomogeneous h 𝒜.grading.piece 𝒜.grading.piece (-1))
  (hincl : LinearMap.IsHomogeneous incl GH.piece 𝒜.grading.piece 0)
  (hproj : LinearMap.IsHomogeneous proj 𝒜.grading.piece GH.piece 0)
include hh hincl hproj

/-- The suspended operation map of every reduced planar tree has degree one between the suspended
gradings `(GH.shift 1).piece` and `(GH.shift 1).piece`. -/
theorem isHomogeneous_suspendedTreeOperation (t : ReducedPlanarTree) :
    MultilinearMap.IsHomogeneous (𝒜.suspendedTreeOperation incl proj h t)
      (fun _ ↦ (GH.shift 1).piece) (GH.shift 1).piece 1 := by
  cases t with
  | leaf => rw [suspendedTreeOperation_leaf]; exact MultilinearMap.isHomogeneous_zero _ _ _
  | node k children =>
    rw [suspendedTreeOperation_node]
    have hinner := (𝒜.isHomogeneous_suspendedM (k + 2)).compMultilinearMap
      fun i ↦ 𝒜.isHomogeneous_suspendedTreeBranch incl h hh hincl (children i)
    simp only [Finset.sum_const_zero, zero_add] at hinner
    have hcomp : MultilinearMap.IsHomogeneous
        (proj.compMultilinearMap ((𝒜.suspendedM (k + 2)).compMultilinearMap fun i ↦
          𝒜.suspendedTreeBranch incl h (children i)))
        (fun _ ↦ (GH.shift 1).piece) (GH.shift 1).piece 1 := by
      simpa only [add_zero] using
        (LinearMap.isHomogeneous_shift_piece_iff.2 hproj).compMultilinearMap hinner
    exact hcomp.domDomCongr finSigmaFinEquiv

/-- The unsuspended operation map of a reduced planar tree `t` is homogeneous of cohomological
degree `2 - t.numLeaves`. -/
theorem isHomogeneous_treeOperation (t : ReducedPlanarTree) :
    MultilinearMap.IsHomogeneous (𝒜.treeOperation incl proj h GH t)
      (fun _ ↦ GH.piece) GH.piece (2 - t.numLeaves) := by
  have hs : MultilinearMap.IsHomogeneous (𝒜.suspendedTreeOperation incl proj h t)
      (fun _ ↦ (GH.shift 1).piece) (Graded.shift GH.piece 1) 1 := by
    simpa only [MultilinearMap.isHomogeneous_def, InternalGrading.shift_piece, Graded.shift_apply]
      using 𝒜.isHomogeneous_suspendedTreeOperation incl proj h hh hincl hproj t
  have hm := ((InternalGrading.suspensionEquiv (fun _ : Fin t.numLeaves ↦ GH) GH.piece 1).symm
    ⟨_, MultilinearMap.mem_homogeneousSubmodule.mpr hs⟩).property
  rwa [MultilinearMap.mem_homogeneousSubmodule, InternalGrading.suspensionEquiv_symm_val,
    one_add_one_eq_two] at hm

end OperationHomogeneous
end HomogeneousTree

/-! ### Binary-tree vanishing -/

section PureBinaryVanishing

variable (𝒜 : AInfinityAlgebra R A)

/-- When `𝒜.m k = 0` for all `k ≥ 3`, every non-binary tree has zero suspended branch map. -/
theorem suspendedTreeBranch_eq_zero_of_not_isBinary (incl : H →ₗ[R] A) (h : Module.End R A)
    (h₃ : ∀ k, 3 ≤ k → 𝒜.m k = 0) {t : ReducedPlanarTree} (ht : ¬ t.IsBinary) :
    𝒜.suspendedTreeBranch incl h t = 0 := by
  induction t with
  | leaf => exact absurd ReducedPlanarTree.isBinary_leaf ht
  | node k children ih =>
    rw [ReducedPlanarTree.isBinary_node, not_and_or, not_forall] at ht
    ext x; rw [suspendedTreeBranch_node_apply, zero_apply]
    rcases ht with hk | ⟨i, hi⟩
    · rw [suspendedM_apply, h₃ (k + 2) (by omega), zero_apply, map_zero, neg_zero]
    · rw [(𝒜.suspendedM (k + 2)).map_coord_zero i (by rw [ih i hi, zero_apply]), map_zero, neg_zero]

/-- When `𝒜.m k = 0` for all `k ≥ 3`, every non-binary tree has zero suspended operation map. -/
theorem suspendedTreeOperation_eq_zero_of_not_isBinary (incl : H →ₗ[R] A) (proj : A →ₗ[R] H)
    (h : Module.End R A) (h₃ : ∀ k, 3 ≤ k → 𝒜.m k = 0) {t : ReducedPlanarTree} (ht : ¬ t.IsBinary) :
    𝒜.suspendedTreeOperation incl proj h t = 0 := by
  cases t with
  | leaf => exact suspendedTreeOperation_leaf 𝒜 incl proj h
  | node k children =>
    rw [ReducedPlanarTree.isBinary_node, not_and_or, not_forall] at ht
    ext x; rw [suspendedTreeOperation_node_apply, zero_apply]
    rcases ht with hk | ⟨i, hi⟩
    · rw [suspendedM_apply, h₃ (k + 2) (by omega), zero_apply, map_zero]
    · rw [(𝒜.suspendedM (k + 2)).map_coord_zero i
        (by rw [𝒜.suspendedTreeBranch_eq_zero_of_not_isBinary incl h h₃ hi, zero_apply]), map_zero]

/-- When `𝒜.m k = 0` for all `k ≥ 3`, every non-binary tree has zero unsuspended branch map. -/
theorem treeBranch_eq_zero_of_not_isBinary (incl : H →ₗ[R] A) (h : Module.End R A)
    (GH : InternalGrading R H ℤ) (h₃ : ∀ k, 3 ≤ k → 𝒜.m k = 0) {t : ReducedPlanarTree}
    (ht : ¬ t.IsBinary) : 𝒜.treeBranch incl h GH t = 0 := by
  rw [treeBranch_def, 𝒜.suspendedTreeBranch_eq_zero_of_not_isBinary incl h h₃ ht,
    MultilinearMap.zero_compLinearMap]

/-- When `𝒜.m k = 0` for all `k ≥ 3`, every non-binary tree has zero unsuspended operation map. -/
theorem treeOperation_eq_zero_of_not_isBinary (incl : H →ₗ[R] A) (proj : A →ₗ[R] H)
    (h : Module.End R A) (GH : InternalGrading R H ℤ) (h₃ : ∀ k, 3 ≤ k → 𝒜.m k = 0)
    {t : ReducedPlanarTree} (ht : ¬ t.IsBinary) : 𝒜.treeOperation incl proj h GH t = 0 := by
  rw [treeOperation_def, 𝒜.suspendedTreeOperation_eq_zero_of_not_isBinary incl proj h h₃ ht,
    MultilinearMap.zero_compLinearMap]

end PureBinaryVanishing
end TauCeti.AInfinityAlgebra
