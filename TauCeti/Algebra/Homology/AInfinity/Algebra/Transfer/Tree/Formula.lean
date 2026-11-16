/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.AInfinity.Algebra.Transfer.Basic
public import TauCeti.Algebra.Homology.AInfinity.Algebra.Transfer.Tree.Basic
import TauCeti.Algebra.Homology.AInfinity.Algebra.Hom.BarDifferential

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
to planar binary trees; we also evaluate the cubic component `f₃` and establish naturality.

## Main results

* `TauCeti.AInfinityAlgebra.suspendedComponent_transferInclusion` and
  `TauCeti.AInfinityAlgebra.component_transferInclusion`: all-arity planar-tree sum formulas for the
  extending `A∞` quasi-isomorphism.
* `TauCeti.AInfinityAlgebra.suspendedM_transfer_eq_sum_arity` and
  `TauCeti.AInfinityAlgebra.m_transfer_eq_sum_arity`: planar-tree sum formulas for the transferred
  `A∞` operations in every arity `n ≠ 1`.
* `TauCeti.AInfinityAlgebra.domDomCongr_treeBranch_binary_corolla_zero_leaf_apply`,
  `TauCeti.AInfinityAlgebra.domDomCongr_treeBranch_binary_leaf_corolla_zero_apply`, and
  `TauCeti.AInfinityAlgebra.component_three_transferInclusion`: three-leaf branch evaluations and
  `f₃`.
* `TauCeti.AInfinityAlgebra.component_transferInclusion_eq_sum_isBinary` and
  `TauCeti.AInfinityAlgebra.m_transfer_eq_sum_isBinary`: Kontsevich--Soibelman binary-tree formulas.
* `TauCeti.AInfinityStrictHom.compMultilinearMap_suspendedTreeBranch`,
  `TauCeti.AInfinityStrictHom.compMultilinearMap_treeBranch`,
  `TauCeti.AInfinityStrictHom.compMultilinearMap_suspendedTreeOperation`, and
  `TauCeti.AInfinityStrictHom.compMultilinearMap_treeOperation`: naturality under strict morphisms.

## References

* M. Kontsevich and Y. Soibelman, *Homological mirror symmetry and torus fibrations*, Section 6.4.
* J.-L. Loday and B. Vallette, *Algebraic Operads*, Chapter 10, Section 10.3.
* S. A. Merkulov, *Strongly homotopy algebras of a Kähler manifold*, IMRN 1999, no. 3, 153--164.
-/

public section

open scoped BigOperators

universe uR uA uH uB uK

namespace TauCeti

namespace AInfinityAlgebra

open ReducedTensorWords

/-! ### Three-leaf branch evaluations and binary-tree vanishing -/

private theorem finCongr_trans {a b c : ℕ} (h₁ : a = b) (h₂ : b = c) :
    (finCongr h₁).trans (finCongr h₂) = finCongr (h₁.trans h₂) := by ext; simp

private theorem domDomCongr_finCongr_reassoc {R : Type uR} {H : Type uH} {N : Type*}
    [CommSemiring R] [AddCommMonoid H] [Module R H] [AddCommMonoid N] [Module R N]
    {a b c : ℕ} (h₁ : a = b) (h₂ : b = c) (h : a = c)
    (F : MultilinearMap (RingHom.id R) (fun _ : Fin a ↦ H) N) (v : Fin c → H) :
    (F.domDomCongr (finCongr h)) v = (F.domDomCongr (finCongr h₁)) (v ∘ finCongr h₂) := by
  rw [Subsingleton.elim h (h₁.trans h₂), ← finCongr_trans h₁ h₂, MultilinearMap.domDomCongr_trans,
    MultilinearMap.domDomCongr_apply, ← Function.comp_def]

private theorem domDomCongr_compLinearMap_koszulTwist {R : Type uR} {H : Type uH} {N : Type*}
    [CommRing R] [AddCommMonoid H] [Module R H] [AddCommMonoid N] [Module R N]
    (GH : InternalGrading R H ℤ) {m n : ℕ} (hmn : m = n)
    (M : MultilinearMap (RingHom.id R) (fun _ : Fin m ↦ H) N) :
    (M.compLinearMap fun l ↦ GH.koszulTwist ((m : ℤ) - 1 - l)).domDomCongr (finCongr hmn) =
      (M.domDomCongr (finCongr hmn)).compLinearMap fun l ↦ GH.koszulTwist ((n : ℤ) - 1 - l) := by
  subst hmn; rfl

variable {R : Type uR} {A : Type uA} {H : Type uH}
  [CommRing R] [AddCommGroup A] [Module R A] [AddCommGroup H] [Module R H]

section ThreeLeaf

variable (𝒜 : AInfinityAlgebra R A) (incl : H →ₗ[R] A) (h : Module.End R A)
  {GH : InternalGrading R H ℤ}

private theorem treeBranch_corolla_zero_apply
    (hincl : LinearMap.IsHomogeneous incl GH.piece 𝒜.grading.piece 0)
    (f : Fin (ReducedPlanarTree.corolla 0).numLeaves → H) :
    𝒜.treeBranch incl h GH (.corolla 0) f =
      -h (𝒜.m 2 ![incl (f ⟨0, by rw [ReducedPlanarTree.numLeaves_corolla]; omega⟩),
        incl (f ⟨1, by rw [ReducedPlanarTree.numLeaves_corolla]; omega⟩)]) := by
  let x : Fin 2 → H := ![f ⟨0, by rw [ReducedPlanarTree.numLeaves_corolla]; omega⟩,
    f ⟨1, by rw [ReducedPlanarTree.numLeaves_corolla]; omega⟩]
  have hf : f = fun j ↦ x (finCongr (ReducedPlanarTree.numLeaves_corolla 0) j) := by
    funext ⟨i, hi⟩; rw [ReducedPlanarTree.numLeaves_corolla] at hi
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
  have h3 : (ReducedPlanarTree.corolla 0).numLeaves + ReducedPlanarTree.leaf.numLeaves = 3 := by
    simp
  rw [domDomCongr_finCongr_reassoc (ReducedPlanarTree.numLeaves_binary (.corolla 0) .leaf) h3,
    𝒜.domDomCongr_treeBranch_binary_apply incl h hh hincl (.corolla 0) .leaf,
    𝒜.treeBranch_corolla_zero_apply incl h hincl, treeBranch_leaf_apply]
  have hs1 : (1 : ℤ) - (ReducedPlanarTree.corolla 0).numLeaves = -1 := by simp
  have hv0 : finCongr h3 (Fin.castAdd ReducedPlanarTree.leaf.numLeaves
      ⟨0, by rw [ReducedPlanarTree.numLeaves_corolla]; omega⟩) = 0 := Fin.ext (by simp)
  have hv1 : finCongr h3 (Fin.castAdd ReducedPlanarTree.leaf.numLeaves
      ⟨1, by rw [ReducedPlanarTree.numLeaves_corolla]; omega⟩) = 1 := Fin.ext (by simp)
  have hv2 : finCongr h3 (Fin.natAdd (ReducedPlanarTree.corolla 0).numLeaves
      ⟨0, ReducedPlanarTree.leaf.numLeaves_pos⟩) = 2 := Fin.ext (by simp)
  simp only [hs1, negOnePowCast_neg, negOnePowCast_one, ReducedPlanarTree.numLeaves_leaf,
    Nat.cast_one, sub_self, GH.koszulTwist_zero, LinearMap.id_apply, Function.comp_apply,
    hv0, hv1, hv2, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.tail_cons, Matrix.head_cons, hneg_l, map_neg, neg_neg, neg_one_smul]

private theorem binary_leaf_corolla_zero_suspendedM
    (hincl : LinearMap.IsHomogeneous incl GH.piece 𝒜.grading.piece 0) (x y z : H)
    (hbin : (∑ a : Fin 2, (![ReducedPlanarTree.leaf, .corolla 0] a).numLeaves) = 3) :
    𝒜.suspendedM 2 (fun i : Fin 2 ↦
      𝒜.suspendedTreeBranch incl h (![ReducedPlanarTree.leaf, .corolla 0] i) fun j ↦
        GH.koszulTwist (((∑ a : Fin 2, (![ReducedPlanarTree.leaf, .corolla 0] a).numLeaves) : ℤ) -
          1 - (finSigmaFinEquiv
            (n := fun a : Fin 2 ↦ (![ReducedPlanarTree.leaf, .corolla 0] a).numLeaves) ⟨i, j⟩ : ℕ))
          ((![x, y, z] : Fin 3 → H) (finCongr hbin (finSigmaFinEquiv ⟨i, j⟩)))) =
      𝒜.m 2 ![incl (GH.koszulTwist 1 x), -h (𝒜.m 2 ![incl y, incl z])] := by
  rw [suspendedM_apply]
  refine congrArg (𝒜.m 2)
    (funext fun i ↦ Fin.cases ?_ (fun i ↦ Fin.cases ?_ (fun j ↦ Fin.elim0 j) i) i)
  · have ht0 : (((2 : ℕ) : ℤ) - 1 - ((0 : Fin 2) : ℕ)) = 1 := by simp
    have hk : (finCongr hbin (finSigmaFinEquiv
        (n := fun a : Fin 2 ↦ (![ReducedPlanarTree.leaf, .corolla 0] a).numLeaves)
        ⟨0, ⟨0, ReducedPlanarTree.leaf.numLeaves_pos⟩⟩) : Fin 3) = 0 := Fin.ext (by simp)
    rw [ht0]
    refine (congrArg (𝒜.grading.koszulTwist 1) (𝒜.suspendedTreeBranch_leaf_apply incl h _)).trans ?_
    simpa [Fin.sum_univ_two, GH.koszulTwist_two_mul 1, mul_zero] using
      (congrArg (fun k ↦ 𝒜.grading.koszulTwist 1 (incl (![x, y, z] k))) hk).trans
        (hincl.koszulTwist_apply 1 x)
  · have ht1 : (((2 : ℕ) : ℤ) - 1 - (((0 : Fin 1).succ : Fin 2) : ℕ)) = 0 := by simp
    rw [ht1, 𝒜.grading.koszulTwist_zero, LinearMap.id_apply]
    have hsub : (fun j : Fin (ReducedPlanarTree.corolla 0).numLeaves ↦ GH.koszulTwist
        (((∑ a : Fin 2, (![ReducedPlanarTree.leaf, .corolla 0] a).numLeaves) : ℤ) - 1 -
          (finSigmaFinEquiv
            (n := fun a : Fin 2 ↦ (![ReducedPlanarTree.leaf, .corolla 0] a).numLeaves)
            ⟨(0 : Fin 1).succ, j⟩ : ℕ))
        ((![x, y, z] : Fin 3 → H) (finCongr hbin (finSigmaFinEquiv ⟨(0 : Fin 1).succ, j⟩)))) =
        fun j : Fin (ReducedPlanarTree.corolla 0).numLeaves ↦
          GH.koszulTwist (((ReducedPlanarTree.corolla 0).numLeaves : ℤ) - 1 - (j : ℕ))
            ((![y, z] : Fin 2 → H) (finCongr (ReducedPlanarTree.numLeaves_corolla 0) j)) := by
      funext j
      have hexp : (((∑ a : Fin 2, (![ReducedPlanarTree.leaf, .corolla 0] a).numLeaves) : ℤ) - 1 -
          (finSigmaFinEquiv
            (n := fun a : Fin 2 ↦ (![ReducedPlanarTree.leaf, .corolla 0] a).numLeaves)
            ⟨(0 : Fin 1).succ, j⟩ : ℕ)) =
          ((ReducedPlanarTree.corolla 0).numLeaves : ℤ) - 1 - (j : ℕ) := by
        simp [Fin.sum_univ_two]; ring
      have hfin : (finCongr hbin (finSigmaFinEquiv
          (n := fun a : Fin 2 ↦ (![ReducedPlanarTree.leaf, .corolla 0] a).numLeaves)
          ⟨(0 : Fin 1).succ, j⟩) : Fin 3) =
          (finCongr (ReducedPlanarTree.numLeaves_corolla 0) j).succ :=
        Fin.ext (by simp [Fin.val_succ, add_comm])
      rw [hexp, hfin, Matrix.cons_val_succ]
    refine (congrArg (𝒜.suspendedTreeBranch incl h (.corolla 0)) hsub).trans ?_
    rw [← treeBranch_apply, ← MultilinearMap.domDomCongr_apply,
      𝒜.domDomCongr_treeBranch_corolla_apply incl h hincl 0 ![y, z]]
    exact congrArg (fun v ↦ -h (𝒜.m 2 v)) (funext fun a ↦ by fin_cases a <;> simp)

/-- Evaluate `treeBranch` on the right-comb binary 3-leaf tree `binary leaf (corolla 0)`. -/
theorem domDomCongr_treeBranch_binary_leaf_corolla_zero_apply
    (hincl : LinearMap.IsHomogeneous incl GH.piece 𝒜.grading.piece 0) (x y z : H) :
    ((𝒜.treeBranch incl h GH (.binary .leaf (.corolla 0))).domDomCongr
      (finCongr (by simp))) ![x, y, z] =
      h (𝒜.m 2 ![incl (GH.koszulTwist 1 x), h (𝒜.m 2 ![incl y, incl z])]) := by
  have hneg_r (u v : A) : 𝒜.m 2 ![u, -v] = -𝒜.m 2 ![u, v] := by
    simpa only [mul_apply] using map_neg (𝒜.mul u) v
  suffices ∀ hn : (ReducedPlanarTree.binary .leaf (.corolla 0)).numLeaves = 3,
      ((𝒜.treeBranch incl h GH (.binary .leaf (.corolla 0))).domDomCongr (finCongr hn)) ![x, y, z] =
        h (𝒜.m 2 ![incl (GH.koszulTwist 1 x), h (𝒜.m 2 ![incl y, incl z])]) from this _
  rw [ReducedPlanarTree.binary_def]; intro hn
  rw [MultilinearMap.domDomCongr_apply, treeBranch_apply, suspendedTreeBranch_node_apply]
  exact (congrArg (-h ·) (𝒜.binary_leaf_corolla_zero_suspendedM incl h hincl x y z _)).trans
    (by rw [hneg_r, map_neg, neg_neg])

end ThreeLeaf

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
    · have hzero : 𝒜.suspendedTreeBranch incl h (children i)
          (fun j ↦ x (finSigmaFinEquiv ⟨i, j⟩)) = 0 := by rw [ih i hi, zero_apply]
      rw [(𝒜.suspendedM (k + 2)).map_coord_zero i hzero, map_zero, neg_zero]

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
    · have hzero : 𝒜.suspendedTreeBranch incl h (children i)
          (fun j ↦ x (finSigmaFinEquiv ⟨i, j⟩)) = 0 := by
        rw [𝒜.suspendedTreeBranch_eq_zero_of_not_isBinary incl h h₃ hi, zero_apply]
      rw [(𝒜.suspendedM (k + 2)).map_coord_zero i hzero, map_zero]

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
theorem suspendedComponent_transferInclusion (n : ℕ) :
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
        have hlt (i : Fin d.1.length) : d.1.blocksFun i < n :=
          (Composition.ne_single_iff hn).mp
            ((Composition.two_le_length_iff_ne_single hn d.1).mp d.2) i
        have harg : (fun i : Fin d.1.length ↦
            (𝒜.transferInclusion c hh hincl hproj).suspendedComponent (d.1.blocksFun i)
              (x ∘ d.1.embedding i)) =
            fun i ↦ ∑ t : ReducedPlanarTree.Arity (d.1.blocksFun i),
              ((𝒜.suspendedTreeBranch c.incl c.homotopy t.val).domDomCongr (finCongr t.property))
                (x ∘ d.1.embedding i) := by
          funext i; rw [ih (d.1.blocksFun i) (hlt i), sum_apply]
        rw [harg, MultilinearMap.map_sum, map_sum, ← Finset.sum_neg_distrib]
        refine Finset.sum_congr rfl fun children _ ↦ ?_
        rw [ReducedPlanarTree.arityCompositionEquiv_apply]
        exact (𝒜.domDomCongr_suspendedTreeBranch_ofComposition_apply c.incl c.homotopy
          d.1 d.2 children x).symm

/-- **Planar-tree formula for the extending `A∞` quasi-isomorphism**: in every arity `n`, the
unsuspended component `(𝒜.transferInclusion c hh hincl hproj).component n` is the sum of
`𝒜.treeBranch c.incl c.homotopy GH t` over all reduced planar trees `t` with `n` leaves. -/
theorem component_transferInclusion (n : ℕ) :
    (𝒜.transferInclusion c hh hincl hproj).component n = ∑ t : ReducedPlanarTree.Arity n,
      (𝒜.treeBranch c.incl c.homotopy GH t.val).domDomCongr (finCongr t.property) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · ext x
    rw [AInfinityHom.component_apply _ n hn, ← AInfinityHom.suspendedComponent_apply _ n hn,
      transfer_grading, 𝒜.suspendedComponent_transferInclusion c hh hincl hproj n, sum_apply,
      sum_apply]
    exact Finset.sum_congr rfl fun t _ ↦ by
      rw [treeBranch_def, domDomCongr_compLinearMap_koszulTwist, MultilinearMap.compLinearMap_apply]

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
    have harg : (fun i : Fin d.1.length ↦
        (𝒜.transferInclusion c hh hincl hproj).suspendedComponent (d.1.blocksFun i)
          (x ∘ d.1.embedding i)) =
        fun i ↦ ∑ t : ReducedPlanarTree.Arity (d.1.blocksFun i),
          ((𝒜.suspendedTreeBranch c.incl c.homotopy t.val).domDomCongr (finCongr t.property))
            (x ∘ d.1.embedding i) := by
      funext i
      rw [𝒜.suspendedComponent_transferInclusion c hh hincl hproj (d.1.blocksFun i), sum_apply]
    rw [harg, MultilinearMap.map_sum, map_sum]
    refine Finset.sum_congr rfl fun children _ ↦ ?_
    rw [ReducedPlanarTree.arityCompositionEquiv_apply]
    exact (𝒜.domDomCongr_suspendedTreeOperation_ofComposition_apply c.incl c.proj c.homotopy
      d.1 d.2 children x).symm

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
    rw [treeOperation_def, domDomCongr_compLinearMap_koszulTwist,
      MultilinearMap.compLinearMap_apply]

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
  rw [𝒜.component_transferInclusion c hh hincl hproj 3, sum_apply,
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
        (𝒜.treeBranch c.incl c.homotopy GH t.1.val).domDomCongr (finCongr t.1.property) := by
  rw [𝒜.component_transferInclusion c hh hincl hproj n]
  exact Finset.sum_congr_set {t : ReducedPlanarTree.Arity n | t.val.IsBinary}
    (fun t ↦ (𝒜.treeBranch c.incl c.homotopy GH t.val).domDomCongr (finCongr t.property))
    (fun t ↦ (𝒜.treeBranch c.incl c.homotopy GH t.1.val).domDomCongr (finCongr t.1.property))
    (fun _ _ ↦ rfl) fun t ht ↦ by
      rw [Set.mem_ofPred_eq] at ht
      rw [𝒜.treeBranch_eq_zero_of_not_isBinary c.incl c.homotopy GH h₃ ht]; ext; simp

/-- **Kontsevich--Soibelman binary-tree formula for `transfer`**: when all operations of `𝒜` in
arity at least three vanish, `(𝒜.transfer c hh hincl hproj).m n` (`n ≠ 1`) sums only over binary
planar trees with `n` leaves. -/
theorem m_transfer_eq_sum_isBinary (h₃ : ∀ k, 3 ≤ k → 𝒜.m k = 0) {n : ℕ} (hn : n ≠ 1) :
    (𝒜.transfer c hh hincl hproj).m n =
      ∑ t : {t : ReducedPlanarTree.Arity n // t.val.IsBinary},
        (𝒜.treeOperation c.incl c.proj c.homotopy GH t.1.val).domDomCongr
          (finCongr t.1.property) := by
  rw [𝒜.m_transfer_eq_sum_arity c hh hincl hproj hn]
  exact Finset.sum_congr_set {t : ReducedPlanarTree.Arity n | t.val.IsBinary}
    (fun t ↦ (𝒜.treeOperation c.incl c.proj c.homotopy GH t.val).domDomCongr (finCongr t.property))
    (fun t ↦
      (𝒜.treeOperation c.incl c.proj c.homotopy GH t.1.val).domDomCongr (finCongr t.1.property))
    (fun _ _ ↦ rfl) fun t ht ↦ by
      rw [Set.mem_ofPred_eq] at ht
      rw [𝒜.treeOperation_eq_zero_of_not_isBinary c.incl c.proj c.homotopy GH h₃ ht]; ext; simp

end TransferFormulas

end AInfinityAlgebra

/-! ### Tree-by-tree naturality under strict morphisms -/

namespace AInfinityStrictHom

section Naturality

variable {R : Type uR} [CommRing R] {A : Type uA} {H : Type uH} {B : Type uB} {K : Type uK}
  [AddCommGroup A] [Module R A] [AddCommGroup H] [Module R H]
  [AddCommGroup B] [Module R B] [AddCommGroup K] [Module R K]
  {𝒜 : AInfinityAlgebra R A} {ℬ : AInfinityAlgebra R B}
  {GH : InternalGrading R H ℤ} {GK : InternalGrading R K ℤ}
  {incl : H →ₗ[R] A} {h : Module.End R A} {incl' : K →ₗ[R] B} {h' : Module.End R B}
  (f : AInfinityStrictHom 𝒜 ℬ) (g : H →ₗ[R] K)

private theorem compMultilinearMap_compLinearMap_koszulTwist {M N : Type*}
    [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]
    (L : M →ₗ[R] N) (hg : LinearMap.IsHomogeneous g GH.piece GK.piece 0) {n : ℕ}
    (F : MultilinearMap (RingHom.id R) (fun _ : Fin n ↦ H) M)
    (F' : MultilinearMap (RingHom.id R) (fun _ : Fin n ↦ K) N)
    (hF : L.compMultilinearMap F = F'.compLinearMap fun _ ↦ g) :
    L.compMultilinearMap (F.compLinearMap fun l ↦ GH.koszulTwist ((n : ℤ) - 1 - l)) =
      (F'.compLinearMap fun l ↦ GK.koszulTwist ((n : ℤ) - 1 - l)).compLinearMap fun _ ↦ g := by
  ext x
  have hs := MultilinearMap.congr_fun hF fun l ↦ GH.koszulTwist ((n : ℤ) - 1 - l) (x l)
  simp only [LinearMap.compMultilinearMap_apply, MultilinearMap.compLinearMap_apply] at hs ⊢
  rw [hs]
  exact congrArg F' (funext fun l ↦
    by simpa [mul_zero] using (hg.koszulTwist_apply ((n : ℤ) - 1 - l) (x l)).symm)

section BranchNaturality

variable (hι : f.toLinearMap ∘ₗ incl = incl' ∘ₗ g) (hη : f.toLinearMap ∘ₗ h = h' ∘ₗ f.toLinearMap)
include hι hη

/-- A strict `A∞` morphism `f` and a retract linear map `g` intertwining `(incl, h)` with
`(incl', h')` intertwine `suspendedTreeBranch` on every reduced planar tree. -/
theorem compMultilinearMap_suspendedTreeBranch (t : ReducedPlanarTree) :
    f.toLinearMap.compMultilinearMap (𝒜.suspendedTreeBranch incl h t) =
      (ℬ.suspendedTreeBranch incl' h' t).compLinearMap fun _ ↦ g := by
  induction t with
  | leaf =>
    ext x
    simpa only [LinearMap.compMultilinearMap_apply, MultilinearMap.compLinearMap_apply,
      AInfinityAlgebra.suspendedTreeBranch_leaf_apply, coe_toLinearMap, LinearMap.comp_apply] using
      LinearMap.congr_fun hι (x ⟨0, ReducedPlanarTree.leaf.numLeaves_pos⟩)
  | node k children ih =>
    ext x
    simp only [LinearMap.compMultilinearMap_apply, coe_toLinearMap,
      MultilinearMap.compLinearMap_apply, AInfinityAlgebra.suspendedTreeBranch_node_apply, map_neg]
    have hηx := LinearMap.congr_fun hη
    simp only [LinearMap.comp_apply, coe_toLinearMap] at hηx
    rw [hηx, f.map_suspendedM]
    refine congrArg (fun v ↦ -h' (ℬ.suspendedM (k + 2) v)) (funext fun i ↦ ?_)
    simpa [LinearMap.compMultilinearMap_apply, MultilinearMap.compLinearMap_apply] using
      MultilinearMap.congr_fun (ih i) fun j ↦ x (finSigmaFinEquiv ⟨i, j⟩)

/-- A strict `A∞` morphism `f` and a degree-zero retract linear map `g` intertwining `(incl, h)`
with `(incl', h')` intertwine `treeBranch` on every reduced planar tree. -/
theorem compMultilinearMap_treeBranch (hg : LinearMap.IsHomogeneous g GH.piece GK.piece 0)
    (t : ReducedPlanarTree) :
    f.toLinearMap.compMultilinearMap (𝒜.treeBranch incl h GH t) =
      (ℬ.treeBranch incl' h' GK t).compLinearMap fun _ ↦ g := by
  rw [AInfinityAlgebra.treeBranch_def, AInfinityAlgebra.treeBranch_def]
  exact compMultilinearMap_compLinearMap_koszulTwist g f.toLinearMap hg _ _
    (f.compMultilinearMap_suspendedTreeBranch g hι hη t)

end BranchNaturality

section OperationNaturality

variable {proj : A →ₗ[R] H} {proj' : B →ₗ[R] K} (hι : f.toLinearMap ∘ₗ incl = incl' ∘ₗ g)
  (hπ : g ∘ₗ proj = proj' ∘ₗ f.toLinearMap) (hη : f.toLinearMap ∘ₗ h = h' ∘ₗ f.toLinearMap)
include hι hπ hη

/-- A strict `A∞` morphism `f` and a retract linear map `g` intertwining `(incl, proj, h)` with
`(incl', proj', h')` intertwine `suspendedTreeOperation` on every reduced planar tree. -/
theorem compMultilinearMap_suspendedTreeOperation (t : ReducedPlanarTree) :
    g.compMultilinearMap (𝒜.suspendedTreeOperation incl proj h t) =
      (ℬ.suspendedTreeOperation incl' proj' h' t).compLinearMap fun _ ↦ g := by
  cases t with
  | leaf => ext x; simp
  | node k children =>
    ext x
    simp only [LinearMap.compMultilinearMap_apply, MultilinearMap.compLinearMap_apply,
      AInfinityAlgebra.suspendedTreeOperation_node_apply]
    have hπx := LinearMap.congr_fun hπ
    simp only [LinearMap.comp_apply, coe_toLinearMap] at hπx
    rw [hπx, f.map_suspendedM]
    refine congrArg (fun v ↦ proj' (ℬ.suspendedM (k + 2) v)) (funext fun i ↦ ?_)
    simpa [LinearMap.compMultilinearMap_apply, MultilinearMap.compLinearMap_apply] using
      MultilinearMap.congr_fun (f.compMultilinearMap_suspendedTreeBranch g hι hη (children i))
        fun j ↦ x (finSigmaFinEquiv ⟨i, j⟩)

/-- A strict `A∞` morphism `f` and a degree-zero retract linear map `g` intertwining
`(incl, proj, h)` with `(incl', proj', h')` intertwine `treeOperation` on every reduced planar
tree. -/
theorem compMultilinearMap_treeOperation (hg : LinearMap.IsHomogeneous g GH.piece GK.piece 0)
    (t : ReducedPlanarTree) :
    g.compMultilinearMap (𝒜.treeOperation incl proj h GH t) =
      (ℬ.treeOperation incl' proj' h' GK t).compLinearMap fun _ ↦ g := by
  rw [AInfinityAlgebra.treeOperation_def, AInfinityAlgebra.treeOperation_def]
  exact compMultilinearMap_compLinearMap_koszulTwist g g hg _ _
    (f.compMultilinearMap_suspendedTreeOperation g hι hπ hη t)

end OperationNaturality
end Naturality
end AInfinityStrictHom
end TauCeti
