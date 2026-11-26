/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.AInfinity.Algebra.Transfer.Basic
public import TauCeti.Algebra.Homology.AInfinity.Algebra.Transfer.Tree.Basic
import TauCeti.Algebra.Homology.AInfinity.Algebra.Hom.BarDifferential
import TauCeti.LinearAlgebra.Multilinear.Basic

/-!
# Planar-tree formulas for homological transfer of A-infinity algebras

Let `𝒜` be an `A∞` algebra on `A` and `c` a special contraction of `(A, m₁)` onto `(H, d_H)` with
homotopy `h` of degree `-1` and inclusion `i` and projection `p` of degree `0` for an internal
grading `GH` on `H`. Homological perturbation of the bar construction
(`TauCeti.AInfinityAlgebra.transfer` and `TauCeti.AInfinityAlgebra.transferInclusion`) builds a
transferred `A∞` algebra on `H` and an extending `A∞` quasi-isomorphism `H ⟶ A`. This file
expresses all non-unary operations of `transfer` (`n ≠ 1`) and all components of `transferInclusion`
as finite sums over `TauCeti.ReducedPlanarTree.Arity n` of the planar-tree evaluation maps from
`TauCeti.Algebra.Homology.AInfinity.Algebra.Transfer.Tree.Basic`, via Merkulov's Taylor fixed-point
equations (`TauCeti.AInfinityAlgebra.taylor_transferInclusion_eq_sub`,
`TauCeti.AInfinityAlgebra.higherTaylor_transfer`),
`TauCeti.AInfinityAlgebra.higherTaylor_barMap_of_tprod`, and
`TauCeti.ReducedPlanarTree.arityCompositionEquiv`. When `𝒜.m k = 0` for `k ≥ 3`, the sums restrict
to planar binary trees, and in arity `3` the branch sum yields the explicit cubic formula for `f₃`.

## Main results

* `TauCeti.AInfinityAlgebra.suspendedComponent_transferInclusion_eq_sum_arity` and
  `TauCeti.AInfinityAlgebra.component_transferInclusion_eq_sum_arity`: all-arity planar-tree sum
  formulas for the extending `A∞` quasi-isomorphism.
* `TauCeti.AInfinityAlgebra.suspendedM_transfer_eq_sum_arity` and
  `TauCeti.AInfinityAlgebra.m_transfer_eq_sum_arity`: planar-tree sum formulas for the transferred
  `A∞` operations in every arity `n ≠ 1`.
* `TauCeti.AInfinityAlgebra.domDomCongr_treeBranch_binary_corolla_zero_leaf_apply`,
  `TauCeti.AInfinityAlgebra.domDomCongr_treeBranch_binary_leaf_corolla_zero_apply`, and
  `TauCeti.AInfinityAlgebra.component_three_transferInclusion`: three-leaf branch evaluations and
  `f₃`.
* `TauCeti.AInfinityAlgebra.component_transferInclusion_eq_sum_isBinary` and
  `TauCeti.AInfinityAlgebra.m_transfer_eq_sum_isBinary`: Kontsevich--Soibelman binary-tree formulas.

## References

* M. Kontsevich and Y. Soibelman, *Homological mirror symmetry and torus fibrations*, Section 6.4.
* J.-L. Loday and B. Vallette, *Algebraic Operads*, Chapter 10, Section 10.3.
* S. A. Merkulov, *Strongly homotopy algebras of a Kähler manifold*, IMRN 1999, no. 3, 153--164.
-/

public section

open scoped BigOperators

universe uR uA uH

namespace TauCeti

namespace AInfinityAlgebra

open ReducedTensorWords

/-! ### Three-leaf branch evaluations -/

variable {R : Type uR} {A : Type uA} {H : Type uH}
  [CommRing R] [AddCommGroup A] [Module R A] [AddCommGroup H] [Module R H]

section ThreeLeaf

open ReducedPlanarTree

variable (𝒜 : AInfinityAlgebra R A) (incl : H →ₗ[R] A) (h : Module.End R A)
  {GH : InternalGrading R H ℤ}

private theorem treeBranch_corolla_zero_apply
    (hincl : LinearMap.IsHomogeneous incl GH.piece 𝒜.grading.piece 0)
    (f : Fin (corolla 0).numLeaves → H) :
    𝒜.treeBranch incl h GH (.corolla 0) f =
      -h (𝒜.m 2 ![incl (f ⟨0, by simp⟩), incl (f ⟨1, by simp⟩)]) := by
  let x : Fin 2 → H := ![f ⟨0, by simp⟩, f ⟨1, by simp⟩]
  have hf : f = fun j ↦ x (finCongr (numLeaves_corolla 0) j) := by
    funext ⟨i, hi⟩; rw [numLeaves_corolla] at hi
    rcases i with _ | _ | i <;> first | (simp [x]; done) | omega
  rw [hf, ← MultilinearMap.domDomCongr_apply,
    𝒜.domDomCongr_treeBranch_corolla_apply incl h hincl 0 x]
  exact congrArg (fun v ↦ -h (𝒜.m 2 v)) (funext fun i ↦ by fin_cases i <;> simp [x])

/-- Evaluate `treeBranch` on the left-comb binary 3-leaf tree `binary (corolla 0) leaf`. -/
theorem domDomCongr_treeBranch_binary_corolla_zero_leaf_apply
    (hh : LinearMap.IsHomogeneous h 𝒜.grading.piece 𝒜.grading.piece (-1))
    (hincl : LinearMap.IsHomogeneous incl GH.piece 𝒜.grading.piece 0) (x y z : H) :
    ((𝒜.treeBranch incl h GH (.binary (.corolla 0) .leaf)).domDomCongr
      (finCongr (by simp))) ![x, y, z] = -h (𝒜.m 2 ![h (𝒜.m 2 ![incl x, incl y]), incl z]) := by
  have hneg_l (u v : A) : 𝒜.m 2 ![-u, v] = -𝒜.m 2 ![u, v] := by
    simpa only [mul_apply, LinearMap.neg_apply] using LinearMap.congr_fun (𝒜.mul.map_neg u) v
  have h3 : (corolla 0).numLeaves + leaf.numLeaves = 3 := by simp
  rw [← MultilinearMap.domDomCongr_finCongr_domDomCongr_finCongr _
      (numLeaves_binary (.corolla 0) .leaf) h3, MultilinearMap.domDomCongr_apply,
    𝒜.domDomCongr_treeBranch_binary_apply incl h hh hincl (.corolla 0) .leaf,
    𝒜.treeBranch_corolla_zero_apply incl h hincl, treeBranch_leaf_apply]
  simp [hneg_l]

/-- Evaluate `treeBranch` on the right-comb binary 3-leaf tree `binary leaf (corolla 0)`. -/
theorem domDomCongr_treeBranch_binary_leaf_corolla_zero_apply
    (hincl : LinearMap.IsHomogeneous incl GH.piece 𝒜.grading.piece 0) (x y z : H) :
    ((𝒜.treeBranch incl h GH (.binary .leaf (.corolla 0))).domDomCongr
      (finCongr (by simp))) ![x, y, z] =
      h (𝒜.m 2 ![incl (GH.koszulTwist 1 x), h (𝒜.m 2 ![incl y, incl z])]) := by
  -- Unlike the left comb, `h` acts only at the root and on the right child `corolla 0`, where
  -- `suspendedM 2` applies `koszulTwist 0 = id`; unfolding at the root avoids `hh`.
  have hsum : (∑ a : Fin 2, (![leaf, corolla 0] a).numLeaves) = 3 := by simp [Fin.sum_univ_two]
  have hbin {t : ReducedPlanarTree} (e : t = node 0 ![leaf, corolla 0]) (ht : t.numLeaves = 3) :
      ((𝒜.treeBranch incl h GH t).domDomCongr (finCongr ht)) ![x, y, z] =
        𝒜.treeBranch incl h GH (node 0 ![leaf, corolla 0])
          (fun i ↦ ![x, y, z] (finCongr hsum i)) := by
    subst e; exact MultilinearMap.domDomCongr_apply ..
  have hneg_r (u v : A) : -h (𝒜.m 2 ![u, -v]) = h (𝒜.m 2 ![u, v]) := by
    rw [← mul_apply, map_neg, map_neg, neg_neg, mul_apply]
  have h3 : ((node 0 ![leaf, corolla 0]).numLeaves : ℤ) = 3 := by
    rw [numLeaves_node, hsum, Nat.cast_ofNat]
  rw [hbin (binary_def .leaf (.corolla 0)), ← hneg_r, treeBranch_apply,
    suspendedTreeBranch_node_apply, suspendedM_apply, h3]
  refine congrArg (fun v ↦ -h (𝒜.m 2 v))
    (funext fun i ↦ Fin.cases ?_ (fun i ↦ Fin.cases ?_ (fun j ↦ j.elim0) i) i)
  · have hexp0 : (((0 + 2 : ℕ) : ℤ) - 1 - ((0 : Fin 2) : ℕ)) = 1 := by simp
    have h0 : finCongr hsum (finSigmaFinEquiv
        (n := fun a : Fin (0 + 2) ↦ (![leaf, corolla 0] a).numLeaves)
        ⟨0, ⟨0, (![leaf, corolla 0] (0 : Fin (0 + 2))).numLeaves_pos⟩⟩) = (0 : Fin 3) :=
      Fin.ext (by simp)
    rw [hexp0]
    exact (congrArg (𝒜.grading.koszulTwist 1) (𝒜.suspendedTreeBranch_leaf_apply incl h _)).trans
      (by simp [finCongr_apply] at h0; simp [h0, hincl.koszulTwist_apply 1 x])
  · have hexp1 : (((0 + 2 : ℕ) : ℤ) - 1 - (((0 : Fin 1).succ : Fin 2) : ℕ)) = 0 := by simp
    have hrhs : 𝒜.treeBranch incl h GH (.corolla 0)
        (fun j ↦ ![y, z] (finCongr (numLeaves_corolla 0) j)) = -h (𝒜.m 2 ![incl y, incl z]) := by
      simpa using 𝒜.treeBranch_corolla_zero_apply incl h hincl
        (fun j ↦ ![y, z] (finCongr (numLeaves_corolla 0) j))
    rw [hexp1, 𝒜.grading.koszulTwist_zero, LinearMap.id_apply, ← hrhs, treeBranch_apply]
    refine congrArg (𝒜.suspendedTreeBranch incl h (.corolla 0)) (funext fun j ↦ ?_)
    have hj : (finSigmaFinEquiv (n := fun a ↦ (![leaf, corolla 0] a).numLeaves)
        ⟨(0 : Fin 1).succ, j⟩ : ℕ) = j.val + 1 := by simp [add_comm]
    have htw : (3 : ℤ) - 1 - (j.val + 1 : ℕ) = ((corolla 0).numLeaves : ℤ) - 1 - j.val := by
      rw [numLeaves_corolla]; omega
    have hidx : finCongr hsum (finSigmaFinEquiv (n := fun a ↦ (![leaf, corolla 0] a).numLeaves)
        ⟨(0 : Fin 1).succ, j⟩) = (finCongr (numLeaves_corolla 0) j).succ :=
      Fin.ext <| by
        rw [finCongr_apply_coe, hj, Fin.val_succ, finCongr_apply_coe (numLeaves_corolla 0) j]
    rw [hj, htw]
    exact congrArg _ ((congrArg ![x, y, z] hidx).trans (Matrix.cons_val_succ _ _ _))

end ThreeLeaf

/-! ### Main planar-tree transfer theorems -/

section TransferFormulas

variable (𝒜 : AInfinityAlgebra R A) {GH : InternalGrading R H ℤ} {dH : Module.End R H}
  (c : LinearSpecialContraction 𝒜.differential dH)
  (hh : LinearMap.IsHomogeneous c.homotopy 𝒜.grading.piece 𝒜.grading.piece (-1))
  (hincl : LinearMap.IsHomogeneous c.incl GH.piece 𝒜.grading.piece 0)
  (hproj : LinearMap.IsHomogeneous c.proj 𝒜.grading.piece GH.piece 0)

/-- **Planar-tree formula for the suspended components of `transferInclusion`**: in every arity `n`,
`suspendedComponent n` is the sum of `suspendedTreeBranch` over all reduced planar trees with `n`
leaves. -/
theorem suspendedComponent_transferInclusion_eq_sum_arity (n : ℕ) :
    (𝒜.transferInclusion c hh hincl hproj).suspendedComponent n = ∑ t : ReducedPlanarTree.Arity n,
      (𝒜.suspendedTreeBranch c.incl c.homotopy t.val).domDomCongr (finCongr t.property) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · rcases eq_or_ne n 1 with rfl | hn1
      · ext x
        rw [Fintype.sum_unique, ReducedPlanarTree.default_arity_one,
          AInfinityHom.suspendedComponent_apply _ 1 Nat.one_pos, of_one_tprod R H x,
          ← AInfinityHom.linearPart_apply, linearPart_transferInclusion,
          MultilinearMap.domDomCongr_apply, suspendedTreeBranch_leaf_apply]
        exact congrArg c.incl (congrArg x (Subsingleton.elim _ _))
      · ext x
        have hne1 : (⟨n, hn⟩ : {m : ℕ // 0 < m}) ≠ 1 := fun h ↦ hn1 (congrArg Subtype.val h)
        rw [AInfinityHom.suspendedComponent_apply _ n hn, taylor_transferInclusion_eq_sub,
          LinearMap.sub_apply, LinearMap.comp_apply, letter_of_of_ne_one R H hne1, map_zero,
          zero_sub, LinearMap.comp_apply, LinearMap.comp_apply,
          𝒜.higherTaylor_barMap_of_tprod (𝒜.transferInclusion c hh hincl hproj) hn x, map_sum,
          ← Finset.sum_neg_distrib, sum_apply,
          ← (ReducedPlanarTree.arityCompositionEquiv hn1).sum_comp, Fintype.sum_sigma]
        refine Finset.sum_congr rfl fun d _ ↦ ?_
        have hih (i : Fin d.val.length) := ih (d.val.blocksFun i)
          ((Composition.ne_single_iff hn).mp
            ((Composition.two_le_length_iff_ne_single hn d.val).mp d.property) i)
        simp_rw [hih, sum_apply]
        rw [MultilinearMap.map_sum, map_sum, ← Finset.sum_neg_distrib]
        refine Finset.sum_congr rfl fun children _ ↦ ?_
        rw [ReducedPlanarTree.arityCompositionEquiv_apply]
        exact (𝒜.domDomCongr_suspendedTreeBranch_ofComposition_apply c.incl c.homotopy
          d.val d.property children x).symm

/-- **Planar-tree formula for the extending `A∞` quasi-isomorphism**: in every arity `n`, the
unsuspended component `(𝒜.transferInclusion c hh hincl hproj).component n` is the sum of
`𝒜.treeBranch c.incl c.homotopy GH t` over all reduced planar trees `t` with `n` leaves. -/
theorem component_transferInclusion_eq_sum_arity (n : ℕ) :
    (𝒜.transferInclusion c hh hincl hproj).component n = ∑ t : ReducedPlanarTree.Arity n,
      (𝒜.treeBranch c.incl c.homotopy GH t.val).domDomCongr (finCongr t.property) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · ext x
    rw [AInfinityHom.component_apply _ n hn, ← AInfinityHom.suspendedComponent_apply _ n hn,
      transfer_grading, 𝒜.suspendedComponent_transferInclusion_eq_sum_arity c hh hincl hproj n,
      sum_apply, sum_apply]
    exact Finset.sum_congr rfl fun t _ ↦ by
      rw [treeBranch_def, MultilinearMap.domDomCongr_compLinearMap,
        MultilinearMap.compLinearMap_apply]
      exact congrArg _ (funext fun l ↦ by rw [finCongr_symm_apply_coe, t.property])

/-- **Planar-tree formula for the suspended non-unary operations of `transfer`**: in every arity
`n ≠ 1`, `(𝒜.transfer c hh hincl hproj).suspendedM n` is the sum of `suspendedTreeOperation` over
all reduced planar trees with `n` leaves. -/
theorem suspendedM_transfer_eq_sum_arity {n : ℕ} (hn : n ≠ 1) :
    (𝒜.transfer c hh hincl hproj).suspendedM n = ∑ t : ReducedPlanarTree.Arity n,
      (𝒜.suspendedTreeOperation c.incl c.proj c.homotopy t.val).domDomCongr
        (finCongr t.property) := by
  rcases Nat.eq_zero_or_pos n with rfl | hpos
  · simp
  · have hn2 : 2 ≤ n := by omega
    ext x
    rw [← (𝒜.transfer c hh hincl hproj).higherTaylor_of_tprod_eq_suspendedM hn2 x,
      higherTaylor_transfer, LinearMap.comp_apply, LinearMap.comp_apply,
      𝒜.higherTaylor_barMap_of_tprod (𝒜.transferInclusion c hh hincl hproj) hpos x, map_sum,
      sum_apply, ← (ReducedPlanarTree.arityCompositionEquiv hn).sum_comp, Fintype.sum_sigma]
    refine Finset.sum_congr rfl fun d _ ↦ ?_
    simp_rw [𝒜.suspendedComponent_transferInclusion_eq_sum_arity c hh hincl hproj, sum_apply]
    rw [MultilinearMap.map_sum, map_sum]
    refine Finset.sum_congr rfl fun children _ ↦ ?_
    rw [ReducedPlanarTree.arityCompositionEquiv_apply]
    exact (𝒜.domDomCongr_suspendedTreeOperation_ofComposition_apply c.incl c.proj c.homotopy
      d.val d.property children x).symm

/-- **Planar-tree formula for the transferred `A∞` operations** (Merkulov; Kontsevich--Soibelman):
for every arity `n ≠ 1`, `(𝒜.transfer c hh hincl hproj).m n` is the sum of
`𝒜.treeOperation c.incl c.proj c.homotopy GH t` over all reduced planar trees `t` with `n`
leaves. -/
theorem m_transfer_eq_sum_arity {n : ℕ} (hn : n ≠ 1) :
    (𝒜.transfer c hh hincl hproj).m n = ∑ t : ReducedPlanarTree.Arity n,
      (𝒜.treeOperation c.incl c.proj c.homotopy GH t.val).domDomCongr (finCongr t.property) := by
  ext x
  rw [(𝒜.transfer c hh hincl hproj).m_eq_compLinearMap_suspendedM n,
    MultilinearMap.compLinearMap_apply, transfer_grading,
    𝒜.suspendedM_transfer_eq_sum_arity c hh hincl hproj hn, sum_apply, sum_apply]
  exact Finset.sum_congr rfl fun t _ ↦ by
    rw [treeOperation_def, MultilinearMap.domDomCongr_compLinearMap,
      MultilinearMap.compLinearMap_apply]
    exact congrArg _ (funext fun l ↦ by rw [finCongr_symm_apply_coe, t.property])

/-- **Cubic component of the extending `A∞` quasi-isomorphism**: the three-leaf tree sum evaluates
to `-h m₃ (i ⊗ i ⊗ i) - h m₂ (h m₂ (i ⊗ i) ⊗ i) + h m₂ (i ⊗ h m₂ (i ⊗ i))`, where moving
degree-`-1` `h` past the first input introduces the Koszul twist `GH.koszulTwist 1`. -/
@[simp]
theorem component_three_transferInclusion (x y z : H) :
    (𝒜.transferInclusion c hh hincl hproj).component 3 ![x, y, z] =
      -c.homotopy (𝒜.m 3 ![c.incl x, c.incl y, c.incl z]) -
        c.homotopy (𝒜.m 2 ![c.homotopy (𝒜.m 2 ![c.incl x, c.incl y]), c.incl z]) +
        c.homotopy (𝒜.m 2 ![c.incl (GH.koszulTwist 1 x),
          c.homotopy (𝒜.m 2 ![c.incl y, c.incl z])]) := by
  rw [𝒜.component_transferInclusion_eq_sum_arity c hh hincl hproj 3, sum_apply,
    ReducedPlanarTree.sum_arity_three]
  have ht0 : ((𝒜.treeBranch c.incl c.homotopy GH (.corolla 1)).domDomCongr
      (finCongr (ReducedPlanarTree.numLeaves_corolla 1))) ![x, y, z] =
      -c.homotopy (𝒜.m 3 ![c.incl x, c.incl y, c.incl z]) := by
    rw [𝒜.domDomCongr_treeBranch_corolla_apply c.incl c.homotopy hincl 1 ![x, y, z]]
    exact congrArg (fun v ↦ -c.homotopy (𝒜.m 3 v)) (funext fun i ↦ by fin_cases i <;> simp)
  rw [ht0, 𝒜.domDomCongr_treeBranch_binary_corolla_zero_leaf_apply c.incl c.homotopy hh hincl x y z,
    𝒜.domDomCongr_treeBranch_binary_leaf_corolla_zero_apply c.incl c.homotopy hincl x y z]; abel

/-- **Kontsevich--Soibelman binary-tree formula for `transferInclusion`**: when all operations of
`𝒜` in arity at least three vanish, `(𝒜.transferInclusion c hh hincl hproj).component n` sums only
over binary planar trees with `n` leaves. -/
theorem component_transferInclusion_eq_sum_isBinary (h₃ : ∀ k, 3 ≤ k → 𝒜.m k = 0) (n : ℕ) :
    (𝒜.transferInclusion c hh hincl hproj).component n =
      ∑ t : {t : ReducedPlanarTree.Arity n // t.val.IsBinary},
        (𝒜.treeBranch c.incl c.homotopy GH t.val.val).domDomCongr (finCongr t.val.property) := by
  rw [𝒜.component_transferInclusion_eq_sum_arity c hh hincl hproj n]
  exact Finset.sum_congr_set {t : ReducedPlanarTree.Arity n | t.val.IsBinary} _ _ (fun _ _ ↦ rfl)
    fun t ht ↦ by
      rw [𝒜.treeBranch_eq_zero_of_not_isBinary c.incl c.homotopy GH h₃ ht]; ext; simp

/-- **Kontsevich--Soibelman binary-tree formula for `transfer`**: when all operations of `𝒜` in
arity at least three vanish, `(𝒜.transfer c hh hincl hproj).m n` (`n ≠ 1`) sums only over binary
planar trees with `n` leaves. -/
theorem m_transfer_eq_sum_isBinary (h₃ : ∀ k, 3 ≤ k → 𝒜.m k = 0) {n : ℕ} (hn : n ≠ 1) :
    (𝒜.transfer c hh hincl hproj).m n =
      ∑ t : {t : ReducedPlanarTree.Arity n // t.val.IsBinary},
        (𝒜.treeOperation c.incl c.proj c.homotopy GH t.val.val).domDomCongr
          (finCongr t.val.property) := by
  rw [𝒜.m_transfer_eq_sum_arity c hh hincl hproj hn]
  exact Finset.sum_congr_set {t : ReducedPlanarTree.Arity n | t.val.IsBinary} _ _ (fun _ _ ↦ rfl)
    fun t ht ↦ by
      rw [𝒜.treeOperation_eq_zero_of_not_isBinary c.incl c.proj c.homotopy GH h₃ ht]; ext; simp

end TransferFormulas

end AInfinityAlgebra

end TauCeti
