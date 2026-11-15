/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.AInfinity.Algebra.Hom.Strict
public import TauCeti.Algebra.Homology.AInfinity.Algebra.Transfer.Basic
public import TauCeti.Algebra.Homology.AInfinity.Algebra.Transfer.Tree.Basic
public import TauCeti.LinearAlgebra.TensorCoalgebra.BlockWord

/-!
# Planar-tree formulas for homological transfer of A-infinity algebras

Let `𝒜` be an `A∞` algebra on `A`, and let `c` be a special contraction of `(A, m₁)` onto `(H, d_H)`
with homotopy `h` of degree `-1` and inclusion `i` and projection `p` of degree zero. Homological
perturbation of the bar construction (`TauCeti.AInfinityAlgebra.transfer` and
`TauCeti.AInfinityAlgebra.transferInclusion`) produces a transferred `A∞` algebra on `H` and an
extending `A∞` quasi-isomorphism `H ⟶ A`. This file expresses all higher operations of `transfer`
and all arity components of `transferInclusion` as explicit finite sums over
`TauCeti.ReducedPlanarTree.Arity n` of the tree maps from
`TauCeti.Algebra.Homology.AInfinity.Algebra.Transfer.Tree.Basic`.

We establish Merkulov's operator fixed-point equations for the Taylor maps, expand
`𝒜.higherTaylor ∘ f.barMap` on pure tensor words over integer compositions into at least two blocks,
and match that recursion with `TauCeti.ReducedPlanarTree.arityCompositionEquiv`. When `𝒜.m k = 0`
for all `k ≥ 3`, non-binary trees evaluate to zero and the sums restrict to planar binary trees.

## Main results

* `TauCeti.AInfinityAlgebra.taylor_transferInclusion_eq_sub` and
  `TauCeti.AInfinityAlgebra.taylor_transfer_eq_add`: Merkulov's Taylor fixed-point equations.
* `TauCeti.AInfinityAlgebra.component_transferInclusion` and
  `TauCeti.AInfinityAlgebra.m_transfer_eq_sum_arity`: all-arity planar-tree sum formulas for the
  extending `A∞` quasi-isomorphism and transferred operations `mₙ` (`n ≥ 2`).
* `TauCeti.AInfinityAlgebra.component_three_transferInclusion`: cubic component `f₃` as a three-tree
  sum.
* `TauCeti.AInfinityAlgebra.component_transferInclusion_eq_sum_isBinary` and
  `TauCeti.AInfinityAlgebra.m_transfer_eq_sum_isBinary`: Kontsevich--Soibelman binary-tree
  specialization when `𝒜.m k = 0` for `k ≥ 3`.
* `TauCeti.AInfinityAlgebra.map_treeBranch` and `TauCeti.AInfinityAlgebra.map_treeOperation`:
  tree-by-tree naturality under compatible strict `A∞` morphisms.

## References

* M. Kontsevich and Y. Soibelman, *Homological mirror symmetry and torus fibrations*, Section 6.4.
* J.-L. Loday and B. Vallette, *Algebraic Operads*, Chapter 10, Section 10.3.
* S. A. Merkulov, *Strongly homotopy algebras of a Kähler manifold*.
-/

public section

open scoped BigOperators

universe uR uA uH uB uK

namespace TauCeti.AInfinityAlgebra

open ReducedTensorWords

/-! ### Higher bar evaluation on morphisms -/

/-- Evaluating `𝒜.higherTaylor` after the bar map of any `A∞` morphism `f : ℬ ⟶ 𝒜` on a pure
tensor word of positive length expands over all compositions of `n` into at least two blocks,
applying `f.suspendedComponent` on each block and `𝒜.suspendedM` at the root. -/
theorem higherTaylor_barMap_of_tprod {R : Type uR} {A : Type uA} {B : Type uB}
    [CommRing R] [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
    (𝒜 : AInfinityAlgebra R A) {ℬ : AInfinityAlgebra R B} (f : AInfinityHom ℬ 𝒜)
    {n : ℕ} (hn : 0 < n) (x : Fin n → B) :
    𝒜.higherTaylor (f.barMap (of R B ⟨n, hn⟩ (PiTensorProduct.tprod R x))) =
      ∑ d : {d : Composition n // 2 ≤ d.length},
        𝒜.suspendedM d.1.length
          (fun i ↦ f.suspendedComponent (d.1.blocksFun i) (x ∘ d.1.embedding i)) := by
  rw [f.barMap_eq_coalgHom, coalgHom_of_tprod_eq_sum_composition f.taylor hn x, map_sum]
  have hone (m : ℕ) (hm : 0 < m) (hm1 : m = 1) (z : Fin m → A) :
      of R A ⟨m, hm⟩ (PiTensorProduct.tprod R z) = ofLetter R A (z ⟨0, hm⟩) := by
    subst hm1; rw [of_tprod_eq_subword R hm z, subword_one R A z hm]
  have hterm (d : Composition n) :
      𝒜.higherTaylor (of R A ⟨d.length, d.length_pos_of_pos hn⟩
          (PiTensorProduct.tprod R fun i ↦
            f.taylor (of R B ⟨d.blocksFun i, d.one_le_blocksFun i⟩
              (PiTensorProduct.tprod R (x ∘ d.embedding i))))) =
        if 2 ≤ d.length then
          𝒜.suspendedM d.length
            (fun i ↦ f.suspendedComponent (d.blocksFun i) (x ∘ d.embedding i))
        else 0 := by
    rw [show (fun i : Fin d.length ↦ f.taylor (of R B ⟨d.blocksFun i, d.one_le_blocksFun i⟩
        (PiTensorProduct.tprod R (x ∘ d.embedding i)))) =
      fun i ↦ f.suspendedComponent (d.blocksFun i) (x ∘ d.embedding i) from
      funext fun i ↦ (f.suspendedComponent_apply (d.blocksFun i) (d.one_le_blocksFun i) _).symm]
    split_ifs with hd
    · exact 𝒜.higherTaylor_of_tprod_eq_suspendedM hd _
    · have hpos := d.length_pos_of_pos hn
      rw [hone d.length hpos (by omega) _, ← LinearMap.comp_apply,
        𝒜.higherTaylor_comp_ofLetter, LinearMap.zero_apply]
  simp_rw [hterm, ← Finset.sum_filter]
  exact Finset.sum_subtype (Finset.univ.filter fun d : Composition n ↦ 2 ≤ d.length)
    (fun _ ↦ Finset.mem_filter.trans (and_iff_right (Finset.mem_univ _)))
    (fun d ↦ 𝒜.suspendedM d.length
      (fun i ↦ f.suspendedComponent (d.blocksFun i) (x ∘ d.embedding i)))

/-! ### Merkulov operator recursions and main planar-tree transfer theorems -/

section TransferFormulas

variable {R : Type uR} {A : Type uA} {H : Type uH}
  [CommRing R] [AddCommGroup A] [Module R A] [AddCommGroup H] [Module R H]
  (𝒜 : AInfinityAlgebra R A) {GH : InternalGrading R H ℤ} {dH : Module.End R H}
  (c : LinearSpecialContraction 𝒜.differential dH)
  (hh : LinearMap.IsHomogeneous c.homotopy 𝒜.grading.piece 𝒜.grading.piece (-1))
  (hincl : LinearMap.IsHomogeneous c.incl GH.piece 𝒜.grading.piece 0)
  (hproj : LinearMap.IsHomogeneous c.proj 𝒜.grading.piece GH.piece 0)

private theorem barMap_transferInclusion_eq_perturb_incl :
    (𝒜.transferInclusion c hh hincl hproj).barMap =
      ((𝒜.barTensorTrick c hh hincl hproj).perturb 𝒜.higherBarDifferential
        𝒜.gradedCoderiv_differential_add_higherBarDifferential_comp_self
        (𝒜.isUnit_one_add_higherBarDifferential_mul_barTensorTrick_homotopy
          c hh hincl hproj)).incl := by
  rw [barMap_transferInclusion, LinearSpecialContraction.perturb_incl, barTensorTrick_incl,
    barTensorTrick_homotopy]

/-- **Merkulov's fixed-point equation for `transferInclusion`**: its suspended Taylor map equals
`c.incl` on single letters minus `c.homotopy ∘ 𝒜.higherTaylor` applied to its own bar map. -/
theorem taylor_transferInclusion_eq_sub :
    (𝒜.transferInclusion c hh hincl hproj).taylor =
      c.incl ∘ₗ letter R H -
        c.homotopy ∘ₗ 𝒜.higherTaylor ∘ₗ (𝒜.transferInclusion c hh hincl hproj).barMap := by
  have hbar := 𝒜.barMap_transferInclusion_eq_perturb_incl c hh hincl hproj
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
  have hbar := 𝒜.barMap_transferInclusion_eq_perturb_incl c hh hincl hproj
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
      rw [of_tprod_eq_subword R hn x, subword_one R H x hn]; rfl
    rw [hword, ← LinearMap.comp_apply (𝒜.transfer c hh hincl hproj).higherTaylor,
      higherTaylor_comp_ofLetter, LinearMap.zero_apply, LinearMap.comp_apply, LinearMap.comp_apply,
      AInfinityHom.barMap_ofLetter, linearPart_transferInclusion,
      ← LinearMap.comp_apply 𝒜.higherTaylor, 𝒜.higherTaylor_comp_ofLetter, LinearMap.zero_apply,
      map_zero]
  · have hne1 : (⟨n, hn⟩ : {m : ℕ // 0 < m}) ≠ 1 := fun h ↦ hn1 (congrArg Subtype.val h)
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
        AInfinityHom.suspendedComponent_apply _ 1 (by omega),
        of_tprod_eq_subword R Nat.one_pos x, subword_one R H x Nat.one_pos,
        ← AInfinityHom.linearPart_apply, linearPart_transferInclusion,
        MultilinearMap.domDomCongr_apply, suspendedTreeBranch_leaf_apply]
      rfl
    · have hn2 : 2 ≤ n := by omega
      ext x
      have hne1 : (⟨n, hn⟩ : {m : ℕ // 0 < m}) ≠ 1 := fun h ↦ hn1 (congrArg Subtype.val h)
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
      have harg : (fun i : Fin d.1.length ↦
          (𝒜.transferInclusion c hh hincl hproj).suspendedComponent (d.1.blocksFun i)
            (x ∘ d.1.embedding i)) =
          fun i ↦ ∑ t : ReducedPlanarTree.Arity (d.1.blocksFun i),
            ((𝒜.suspendedTreeBranch c t.val).domDomCongr (finCongr t.property))
              (x ∘ d.1.embedding i) := by
        funext i; rw [ih (d.1.blocksFun i) (hlt i) (d.1.one_le_blocksFun i), sum_apply]
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
    simp only [MultilinearMap.domDomCongr_apply, treeBranch_def, MultilinearMap.compLinearMap_apply,
      finCongr_apply]
    congr 1; funext l; congr 2; rw [Fin.val_cast]
    exact congrArg (fun k : ℕ ↦ (k : ℤ) - 1 - (l : ℕ)) t.property.symm

/-- **Planar-tree formula for the suspended higher operations of `transfer`**: in every arity
`n ≥ 2`, `(𝒜.transfer c hh hincl hproj).suspendedM n` is the sum of `suspendedTreeOperation` over
all reduced planar trees with `n` leaves. -/
theorem suspendedM_transfer_eq_sum_arity {n : ℕ} (hn : 2 ≤ n) :
    (𝒜.transfer c hh hincl hproj).suspendedM n =
      ∑ t : ReducedPlanarTree.Arity n,
        (𝒜.suspendedTreeOperation c t.val).domDomCongr (finCongr t.property) := by
  have hpos : 0 < n := by omega
  have hne1 : (⟨n, hpos⟩ : {m : ℕ // 0 < m}) ≠ 1 :=
    fun h ↦ by have : n = 1 := congrArg Subtype.val h; omega
  ext x
  rw [← (𝒜.transfer c hh hincl hproj).taylor_of_tprod_eq_suspendedM ⟨n, hpos⟩ x,
    taylor_transfer_eq_add, LinearMap.add_apply, LinearMap.comp_apply,
    letter_of_of_ne_one R H hne1, map_zero, zero_add, LinearMap.comp_apply, LinearMap.comp_apply,
    𝒜.higherTaylor_barMap_of_tprod (𝒜.transferInclusion c hh hincl hproj) hpos x, map_sum,
    sum_apply, ← (ReducedPlanarTree.arityCompositionEquiv hn).sum_comp, Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun d _ ↦ ?_
  have harg : (fun i : Fin d.1.length ↦
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
  simp only [MultilinearMap.domDomCongr_apply, treeOperation_def,
    MultilinearMap.compLinearMap_apply, finCongr_apply]
  congr 1; funext l; congr 2; rw [Fin.val_cast]
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

omit hh in
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
  exact congrArg (fun v ↦ -c.homotopy (𝒜.m 2 v)) (funext fun i ↦ by fin_cases i <;> rfl)

/-- Evaluate `treeBranch` on the left-comb binary 3-leaf tree `binary (corolla 0) leaf`. -/
theorem treeBranch_binary_corolla_zero_leaf (x y z : H) :
    ((𝒜.treeBranch c GH (.binary (.corolla 0) .leaf)).domDomCongr
      (finCongr (by simp))) ![x, y, z] =
      -c.homotopy (𝒜.m 2 ![c.homotopy (𝒜.m 2 ![c.incl x, c.incl y]), c.incl z]) := by
  have hneg_l (u v : A) : 𝒜.m 2 ![-u, v] = -𝒜.m 2 ![u, v] := by
    simpa only [mul_apply, LinearMap.neg_apply] using LinearMap.congr_fun (𝒜.mul.map_neg u) v
  have h3 : (ReducedPlanarTree.corolla 0).numLeaves + ReducedPlanarTree.leaf.numLeaves = 3 := by
    simp
  change ((𝒜.treeBranch c GH (.binary (.corolla 0) .leaf)).domDomCongr
      (finCongr (ReducedPlanarTree.numLeaves_binary (.corolla 0) .leaf)))
      (![x, y, z] ∘ finCongr h3) = _
  rw [𝒜.treeBranch_binary c hh hincl (.corolla 0) .leaf,
    𝒜.treeBranch_corolla_zero_apply c hincl, treeBranch_leaf_apply]
  have hs1 : (1 : ℤ) - (ReducedPlanarTree.corolla 0).numLeaves = -1 := by simp
  have hv0 : (![x, y, z] : Fin 3 → H) (finCongr h3 (Fin.castAdd _ ⟨0, by decide⟩)) = x := rfl
  have hv1 : (![x, y, z] : Fin 3 → H) (finCongr h3 (Fin.castAdd _ ⟨1, by decide⟩)) = y := rfl
  have hv2 : (![x, y, z] : Fin 3 → H) (finCongr h3 (Fin.natAdd _ ⟨0, by decide⟩)) = z := rfl
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
  change ((𝒜.treeBranch c GH (.binary .leaf (.corolla 0))).domDomCongr
      (finCongr (ReducedPlanarTree.numLeaves_binary .leaf (.corolla 0))))
      (![x, y, z] ∘ finCongr h3) = _
  rw [𝒜.treeBranch_binary c hh hincl .leaf (.corolla 0),
    treeBranch_leaf_apply, 𝒜.treeBranch_corolla_zero_apply c hincl]
  have hs2 : (1 : ℤ) - (ReducedPlanarTree.corolla 0).numLeaves = -1 := by simp
  have hv0 : (![x, y, z] : Fin 3 → H) (finCongr h3 (Fin.castAdd _ ⟨0, by decide⟩)) = x := rfl
  have hv1 : (![x, y, z] : Fin 3 → H) (finCongr h3 (Fin.natAdd _ ⟨0, by decide⟩)) = y := rfl
  have hv2 : (![x, y, z] : Fin 3 → H) (finCongr h3 (Fin.natAdd _ ⟨1, by decide⟩)) = z := rfl
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
  have ht0 : ((𝒜.treeBranch c GH (.corolla 1)).domDomCongr
      (finCongr (ReducedPlanarTree.numLeaves_corolla 1))) ![x, y, z] =
      -c.homotopy (𝒜.m 3 ![c.incl x, c.incl y, c.incl z]) := by
    rw [𝒜.treeBranch_corolla c hincl 1 ![x, y, z]]
    exact congrArg (fun v ↦ -c.homotopy (𝒜.m 3 v)) (funext fun i ↦ by fin_cases i <;> rfl)
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
          (fun j ↦ x (finSigmaFinEquiv ⟨i, j⟩)) = 0 := by rw [ih i hi, zero_apply]
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
  rw [treeBranch_def, 𝒜.suspendedTreeBranch_eq_zero_of_not_isBinary c' h₃ ht,
    MultilinearMap.zero_compLinearMap]

/-- When `𝒜.m k = 0` for all `k ≥ 3`, every non-binary tree has zero unsuspended operation map. -/
theorem treeOperation_eq_zero_of_not_isBinary
    {dA : Module.End R A} (c' : LinearSpecialContraction dA dH)
    (h₃ : ∀ k, 3 ≤ k → 𝒜.m k = 0) {t : ReducedPlanarTree} (ht : ¬ t.IsBinary) :
    𝒜.treeOperation c' GH t = 0 := by
  rw [treeOperation_def, 𝒜.suspendedTreeOperation_eq_zero_of_not_isBinary c' h₃ ht,
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
      (fun t ↦ (𝒜.treeBranch c GH t.val).domDomCongr (finCongr t.property)), Finset.sum_filter]
  refine Finset.sum_congr rfl fun t _ ↦ ?_
  split_ifs with ht
  · rfl
  · rw [𝒜.treeBranch_eq_zero_of_not_isBinary c h₃ ht]; rfl

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
      (fun t ↦ (𝒜.treeOperation c GH t.val).domDomCongr (finCongr t.property)), Finset.sum_filter]
  refine Finset.sum_congr rfl fun t _ ↦ ?_
  split_ifs with ht
  · rfl
  · rw [𝒜.treeOperation_eq_zero_of_not_isBinary c h₃ ht]; rfl

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
  exact congrArg (ℬ.m n) (funext fun i ↦
    (by simpa [mul_zero] using (f.isHomogeneous.koszulTwist_apply ((n : ℤ) - 1 - i) (x i)).symm))

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
  rw [LinearMap.compMultilinearMap_apply, treeBranch_def, MultilinearMap.compLinearMap_apply, hs,
    MultilinearMap.compLinearMap_apply, treeBranch_def, MultilinearMap.compLinearMap_apply]
  exact congrArg _ (funext fun l ↦
    by simpa [mul_zero] using (hg.koszulTwist_apply ((t.numLeaves : ℤ) - 1 - l) (x l)).symm)

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
  | leaf => ext x; simp
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
  rw [LinearMap.compMultilinearMap_apply, treeOperation_def, MultilinearMap.compLinearMap_apply, hs,
    MultilinearMap.compLinearMap_apply, treeOperation_def, MultilinearMap.compLinearMap_apply]
  exact congrArg _ (funext fun l ↦
    by simpa [mul_zero] using (hg.koszulTwist_apply ((t.numLeaves : ℤ) - 1 - l) (x l)).symm)

end OperationNaturality

end Naturality

end TauCeti.AInfinityAlgebra
