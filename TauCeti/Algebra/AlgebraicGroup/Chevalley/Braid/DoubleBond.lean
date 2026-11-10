/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Chevalley.Orthogonal
public import TauCeti.Algebra.AlgebraicGroup.Chevalley.RankOne

/-!
# The double-bond braid relation in Chevalley data

Pinned simple Weyl representatives at a double bond satisfy the length-four braid relation
in the actual group of points over every commutative ring. This includes bad characteristic
and nonreduced rings, and imposes no condition on the datum's weight lattice.

The two long roots obtained by reflecting one another across the short simple root are
strongly orthogonal. Their rank-one subgroups therefore commute. The square of the short
Weyl representative also commutes with the long rank-one subgroup: it is the coroot at
minus one, and the relevant Cartan integer is even. Together these two commutations give
the braid relation without computing the signs of the reflected root vectors.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, Chapter 3, Lemmas 15 and 19, and Chapter 6.
* R. W. Carter, *Simple Groups of Lie Type*, §§6.4 and 7.2.
-/

public section

namespace TauCeti.DynkinType.ChevalleyDatum

universe v

variable {t : DynkinType} {ht : t.Valid} (D : ChevalleyDatum t ht)

private theorem doubleBond_stronglyOrthogonal (i j : Fin t.rank)
    (hij : t.cartanMatrix i j = -1) (hji : t.cartanMatrix j i = -2) :
    let P := t.simplyConnectedRootDatum ht
    let α := t.simpleIndex ht i
    let β := t.simpleIndex ht j
    let γ := P.reflectionPerm α β
    (P.root γ + P.root β ∉ Set.range P.root) ∧
      (P.root γ + P.root β ≠ 0) ∧
      (P.root γ - P.root β ∉ Set.range P.root) ∧
      (P.root γ - P.root β ≠ 0) := by
  dsimp only
  let P := t.simplyConnectedRootDatum ht
  let α := t.simpleIndex ht i
  let β := t.simpleIndex ht j
  have := t.isReduced_simplyConnectedRootDatum ht
  have hγ : P.root (P.reflectionPerm α β) = P.root β + 2 • P.root α := by
    rw [RootPairing.root_reflectionPerm, RootPairing.reflection_apply_root]
    simp only [P, α, β, t.pairing_simpleIndex, hji, neg_smul, sub_neg_eq_add]
    rfl
  have hsum : P.root (P.reflectionPerm α β) + P.root β =
      2 • P.root (P.reflectionPerm β α) := by
    rw [hγ, RootPairing.root_reflectionPerm, RootPairing.reflection_apply_root]
    simp only [P, α, β, t.pairing_simpleIndex, hij, neg_one_smul, sub_neg_eq_add]
    module
  have hsub : P.root (P.reflectionPerm α β) - P.root β = 2 • P.root α := by
    rw [hγ]
    module
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hsum]
    exact P.nsmul_notMem_range_root (n := 2)
  · rw [hsum]
    exact fun h => P.ne_zero _ ((nsmul_right_injective (by decide))
      (h.trans (smul_zero _).symm))
  · rw [hsub]
    exact P.nsmul_notMem_range_root (n := 2)
  · rw [hsub]
    exact fun h => P.ne_zero _ ((nsmul_right_injective (by decide))
      (h.trans (smul_zero _).symm))

private theorem doubleBond_commute_conjugate (i j : Fin t.rank)
    (hij : t.cartanMatrix i j = -1) (hji : t.cartanMatrix j i = -2)
    (A : Type v) [CommRing A] :
    let a := D.weylElement (t.simpleIndex ht i) A 1
    let b := D.weylElement (t.simpleIndex ht j) A 1
    Commute (a * b * a⁻¹) b := by
  let P := t.simplyConnectedRootDatum ht
  let α := t.simpleIndex ht i
  let β := t.simpleIndex ht j
  let γ := P.reflectionPerm α β
  let a := D.weylElement α A 1
  let b := D.weylElement β A 1
  let R := Subgroup.closure (Set.range (D.rootSubgroupPoints γ A) ∪
    Set.range (D.rootSubgroupPoints (P.reflectionPerm γ γ) A))
  have hneg : P.reflectionPerm α (P.reflectionPerm β β) = P.reflectionPerm γ γ := by
    apply P.root.injective
    rw [RootPairing.root_reflectionPerm, RootPairing.root_reflectionPerm,
      RootPairing.reflection_apply_self, map_neg, ← RootPairing.root_reflectionPerm,
      RootPairing.root_reflectionPerm P γ γ, RootPairing.reflection_apply_self]
  have hc (δ : Fin t.numRoots) (u : A) :
      a * D.rootSubgroupPoints δ A (Multiplicative.ofAdd u) * a⁻¹ =
        D.rootSubgroupPoints (P.reflectionPerm α δ) A
          (Multiplicative.ofAdd (((t.chevalleyWeylSign ht α δ : ℤ) : A) * u)) :=
    D.weylElement_conj_rootSubgroupPoints i δ A u
  have hab : a * b * a⁻¹ ∈ R := by
    have hp (u : A) : a * D.rootSubgroupPoints β A (Multiplicative.ofAdd u) * a⁻¹ ∈ R := by
      rw [hc]
      exact Subgroup.subset_closure (Or.inl ⟨_, rfl⟩)
    have hn (u : A) : a * D.rootSubgroupPoints (P.reflectionPerm β β) A
        (Multiplicative.ofAdd u) * a⁻¹ ∈ R := by
      rw [hc, hneg]
      exact Subgroup.subset_closure (Or.inr ⟨_, rfl⟩)
    have hb : a * b * a⁻¹ =
        (a * D.rootSubgroupPoints β A (Multiplicative.ofAdd 1) * a⁻¹) *
        (a * D.rootSubgroupPoints (P.reflectionPerm β β) A
          (Multiplicative.ofAdd (-1)) * a⁻¹) *
        (a * D.rootSubgroupPoints β A (Multiplicative.ofAdd 1) * a⁻¹) := by
      simp only [b, D.weylElement_def, Units.val_one, inv_one]
      dsimp only [P]
      group
    rw [hb]
    exact R.mul_mem (R.mul_mem (hp 1) (hn (-1))) (hp 1)
  have horth := doubleBond_stronglyOrthogonal (ht := ht) i j hij hji
  exact (Subgroup.mem_centralizer_iff.mp
      (D.closure_rootPair_le_centralizer A γ β horth.1 horth.2.1 horth.2.2.1
        horth.2.2.2 hab) b (D.weylElement_mem_closure_rootPair β A 1)).symm

private theorem doubleBond_commute_square (i j : Fin t.rank)
    (hji : t.cartanMatrix j i = -2) (A : Type v) [CommRing A] :
    Commute (D.weylElement (t.simpleIndex ht i) A 1 *
      D.weylElement (t.simpleIndex ht i) A 1) (D.weylElement (t.simpleIndex ht j) A 1) := by
  let P := t.simplyConnectedRootDatum ht
  let β := t.simpleIndex ht j
  have hx (δ : Fin t.numRoots) (hδ : P.root δ i = -2 ∨ P.root δ i = 2) (u : A) :
      Commute (D.simpleCorootPoints i A (-1))
        (D.rootSubgroupPoints δ A (Multiplicative.ofAdd u)) := by
    apply mul_inv_eq_iff_eq_mul.mp
    rw [D.simpleCorootPoints_eq_torusPoints, D.torusPoints_conj_rootSubgroupPoints]
    simp only [coordinateRoot_def, D.torusCharacter_simpleCorootParameter]
    dsimp only [P] at hδ
    rcases hδ with hδ | hδ <;> simp [hδ]
  have hp : P.root β i = -2 := by simp [P, β, t.root_simpleIndex, hji]
  have hn : P.root (P.reflectionPerm β β) i = 2 := by
    simp only [RootPairing.root_reflectionPerm, RootPairing.reflection_apply_self, Pi.neg_apply,
      hp, neg_neg]
  have h := ((hx β (Or.inl hp) 1).mul_right
    (hx (P.reflectionPerm β β) (Or.inr hn) (-1))).mul_right (hx β (Or.inl hp) 1)
  rw [D.weylElement_mul_self]
  simpa only [D.weylElement_def, Units.val_one, inv_one] using h

/-- Pinned simple Weyl representatives at a double bond satisfy the length-four braid
relation over every commutative value ring. The Cartan matrix is indexed by root, then coroot,
so `j` is the long node and `i` the short node. -/
theorem weylElement_braid_of_cartanMatrix_eq_neg_two (i j : Fin t.rank)
    (hij : t.cartanMatrix i j = -1) (hji : t.cartanMatrix j i = -2)
    (A : Type v) [CommRing A] :
    D.weylElement (t.simpleIndex ht i) A 1 * D.weylElement (t.simpleIndex ht j) A 1 *
        D.weylElement (t.simpleIndex ht i) A 1 * D.weylElement (t.simpleIndex ht j) A 1 =
      D.weylElement (t.simpleIndex ht j) A 1 * D.weylElement (t.simpleIndex ht i) A 1 *
        D.weylElement (t.simpleIndex ht j) A 1 * D.weylElement (t.simpleIndex ht i) A 1 := by
  let a := D.weylElement (t.simpleIndex ht i) A 1
  let b := D.weylElement (t.simpleIndex ht j) A 1
  have hcomm : Commute (a * b * a⁻¹) b := D.doubleBond_commute_conjugate i j hij hji A
  have hsq : Commute (a * a) b := D.doubleBond_commute_square i j hji A
  -- Replace the inverse in the orthogonal-pair commutation using the commuting square.
  have h := congrArg (fun g => g * a * a) hcomm.eq
  calc
    a * b * a * b = (a * b * a⁻¹ * b) * a * a := by
      calc
        _ = (a * b * a⁻¹) * ((a * a) * b) := by group
        _ = (a * b * a⁻¹) * (b * (a * a)) := by rw [hsq.eq]
        _ = _ := by group
    _ = (b * (a * b * a⁻¹)) * a * a := h
    _ = b * a * b * a := by group

end TauCeti.DynkinType.ChevalleyDatum
