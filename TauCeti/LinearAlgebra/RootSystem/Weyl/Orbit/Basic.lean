/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.RootSystem.CartanMatrix
public import TauCeti.LinearAlgebra.RootSystem.Weyl.Group

/-!
# The Weyl orbit of the simple roots

A base of a root pairing carries only finitely much data — the Cartan matrix of its simple roots —
yet it controls every root, because the Weyl-group orbits of the simple roots cover all roots. This
file proves that covering statement, at the level of root indices, and draws the consequence that
concerns lengths: a root-positive form takes on the roots exactly the values it takes on the simple
roots.

The proof is the lowering argument, packaged by Mathlib as
`RootPairing.Base.induction_reflect`: reflecting a positive root in a suitable simple root
decreases its height, and reflection in a root sends that root to its negative, so induction on
height reaches a simple root from anywhere.

## Main results

* `TauCeti.exists_mem_support_weylGroupToPerm_eq`: **every root index is the image of a simple root
  index under the Weyl group.**
* `RootPairing.Base.induction_simple_reflect`: a property of root indices holding at the simple
  roots and preserved by the simple reflections holds at every root.
* `RootPairing.Base.exists_weylGroupToPerm_eq_of_isSimplyLaced`: **in a simply laced irreducible
  root system the Weyl group is transitive on the roots.**
* `RootPairing.Base.orbit_root_eq_range_of_isSimplyLaced` and
  `RootPairing.Base.card_weylGroup_eq_card_mul_card_stabilizer_of_isSimplyLaced`: the Weyl orbit of
  any root is the set of all roots, so the Weyl group has order the number of roots times the order
  of the stabilizer of a root.
* `RootPairing.RootPositiveForm.rootLength_weylGroupToPerm`: root length is a Weyl-group
  invariant, with `RootPairing.RootPositiveForm.rootLength_reflectionPerm` the special case
  of a single reflection.
* `RootPairing.RootPositiveForm.exists_mem_support_rootLength_eq`: **every root has the
  length of some simple root.** This is what turns a statement about the two entries of a rank-two
  Cartan matrix into a statement about all the roots.

## References

See Bourbaki, *Lie Groups and Lie Algebras, Chapters 4-6*, Ch. VI §1.5, and Humphreys,
*Introduction to Lie Algebras and Representation Theory*, §10.3, where the same statement is proved
by the same induction.
-/

public section

namespace TauCeti

variable {ι R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N]
  [Module R N] {P : RootPairing ι R M N}

/-- **Every root is Weyl-conjugate to a simple root.** Stated on root indices: for a base `b`, each
index `j` satisfies `P.weylGroupToPerm w i = j` for some `i` in the support of `b` and some
Weyl-group element `w`.

The Weyl-group element is far from unique — the stabilizer of a simple root index is generally
nontrivial — so this is an existence statement and not a parametrization of the roots by
`b.support × P.weylGroup`. -/
theorem exists_mem_support_weylGroupToPerm_eq [CharZero R] [Finite ι] [IsDomain R]
    [P.IsCrystallographic] [P.IsReduced] (b : P.Base) (j : ι) :
    ∃ i ∈ b.support, ∃ w : P.weylGroup, P.weylGroupToPerm w i = j := by
  -- One reflection more: prefix the Weyl-group element by the reflection in `k`, which lies in the
  -- Weyl group whether or not `k` is simple.
  have step : ∀ k x : ι, (∃ i ∈ b.support, ∃ w : P.weylGroup, P.weylGroupToPerm w i = x) →
      ∃ i ∈ b.support, ∃ w : P.weylGroup, P.weylGroupToPerm w i = P.reflectionPerm k x := by
    rintro k x ⟨i, hi, w, rfl⟩
    exact ⟨i, hi, _root_.RootPairing.weylGroup.ofIdx P k * w,
      RootPairing.weylGroupToPerm_ofIdx_mul_apply P w k i⟩
  exact b.induction_reflect j (fun k hk ↦ step k k hk) (fun i hi ↦ ⟨i, hi, 1, by simp⟩)
    fun x k hx _ ↦ step k x hx

/-- **Simple reflections carry the simple roots onto every root.** A property of root indices
that holds at the simple roots of a base and is preserved by the reflection in each simple root
holds at every root index.

Unlike `RootPairing.Base.induction_reflect`, closure under negation is not asked for: the negative
of a simple root `αᵢ` is its reflection `sᵢ αᵢ`, so the simple reflections already reach the
negative roots. -/
theorem _root_.RootPairing.Base.induction_simple_reflect [CharZero R] [Finite ι] [IsDomain R]
    [P.IsCrystallographic] [P.IsReduced] (b : P.Base) (i : ι) {p : ι → Prop}
    (h₁ : ∀ i ∈ b.support, p i)
    (h₂ : ∀ i j, p i → j ∈ b.support → p (P.reflectionPerm j i)) :
    p i := by
  -- induct on a root and its negative together, since `induction_reflect` needs negation
  refine (b.induction_reflect i (p := fun k ↦ p k ∧ p (P.reflectionPerm k k))
    (fun k hk ↦ ?_) (fun k hk ↦ ⟨h₁ k hk, h₂ k k (h₁ k hk) hk⟩)
    (fun k j hk hj ↦ ⟨h₂ k j hk.1 hj, ?_⟩)).1
  · have hkk : P.reflectionPerm (P.reflectionPerm k k) (P.reflectionPerm k k) = k :=
      ((P.root_eq_neg_iff).mp (by simp [P.root_reflectionPerm])).symm
    rw [hkk]
    exact hk.symm
  · have hneg : P.reflectionPerm (P.reflectionPerm j k) (P.reflectionPerm j k) =
        P.reflectionPerm j (P.reflectionPerm k k) :=
      ((P.root_eq_neg_iff).mp (by simp [P.root_reflectionPerm])).symm
    rw [hneg]
    exact h₂ _ j hk.2 hj

/-- Two roots whose Cartan integers against each other are both `-1` are exchanged by a product of
two reflections: `sᵢ (sⱼ αᵢ) = sᵢ (αᵢ + αⱼ) = -αᵢ + (αⱼ + αᵢ) = αⱼ`. -/
theorem _root_.RootPairing.reflectionPerm_reflectionPerm_of_pairing_eq_neg_one {i j : ι}
    (hij : P.pairing i j = -1) (hji : P.pairing j i = -1) :
    P.reflectionPerm i (P.reflectionPerm j i) = j := by
  refine P.root.injective ?_
  simp only [RootPairing.root_reflectionPerm, RootPairing.reflection_apply_root, hij, map_sub,
    map_smul, RootPairing.pairing_same, hji]
  module

/-- **In a simply laced irreducible root system the Weyl group is transitive on the roots.** Stated
on root indices: any root index `i` is carried to any other `j` by some Weyl-group element.

The simple roots are Weyl-conjugate to one another, because adjacent simple roots `αᵢ`, `αⱼ` of a
simply laced base satisfy `sᵢ sⱼ αᵢ = αⱼ` and the Dynkin diagram of an irreducible system is
connected; every root is Weyl-conjugate to a simple root by
`TauCeti.exists_mem_support_weylGroupToPerm_eq`.

Both hypotheses are needed. In `A₁ × A₁` the two simple roots lie in different orbits, and in
`B₂` the long and the short roots do. -/
theorem _root_.RootPairing.Base.exists_weylGroupToPerm_eq_of_isSimplyLaced [CharZero R] [Finite ι]
    [IsDomain R] [P.IsCrystallographic] [P.IsReduced] [P.IsIrreducible] (b : P.Base)
    (hsl : b.cartanMatrix.IsSimplyLaced) (i j : ι) :
    ∃ w : P.weylGroup, P.weylGroupToPerm w i = j := by
  -- the simple roots are Weyl-conjugate, by induction along the connected Dynkin diagram
  have hsimple (k l : b.support) : ∃ w : P.weylGroup, P.weylGroupToPerm w k = l := by
    refine b.induction_on_cartanMatrix (i := k) (j := l) (fun l : b.support ↦ ∃ w : P.weylGroup,
      P.weylGroupToPerm w k = l) ⟨1, by simp⟩ fun u v ⟨w, hw⟩ hvu ↦ ?_
    rcases eq_or_ne u v with rfl | hne
    · exact ⟨w, hw⟩
    have hpairing (x y : b.support) (hxy : x ≠ y) (h : b.cartanMatrix x y ≠ 0) :
        P.pairing x y = -1 := by
      have : P.pairingIn ℤ x y = -1 := by
        simpa [RootPairing.Base.cartanMatrix, RootPairing.Base.cartanMatrixIn_def] using
          (hsl hxy).resolve_left h
      rw [← P.algebraMap_pairingIn ℤ, this]
      simp
    refine ⟨RootPairing.weylGroup.ofIdx P u * (RootPairing.weylGroup.ofIdx P v * w), ?_⟩
    rw [RootPairing.weylGroupToPerm_ofIdx_mul_apply, RootPairing.weylGroupToPerm_ofIdx_mul_apply,
      hw, RootPairing.reflectionPerm_reflectionPerm_of_pairing_eq_neg_one
        (hpairing u v hne (b.cartanMatrix_apply_eq_zero_iff_symm.not.mp hvu))
        (hpairing v u hne.symm hvu)]
  obtain ⟨k, hk, u, rfl⟩ := exists_mem_support_weylGroupToPerm_eq b i
  obtain ⟨l, hl, v, rfl⟩ := exists_mem_support_weylGroupToPerm_eq b j
  obtain ⟨w, hw⟩ := hsimple ⟨k, hk⟩ ⟨l, hl⟩
  refine ⟨v * w * u⁻¹, ?_⟩
  rw [map_mul, map_mul, map_inv, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply,
    Equiv.Perm.inv_def, Equiv.symm_apply_apply]
  exact congrArg (P.weylGroupToPerm v) hw

/-- **In a simply laced irreducible root system the Weyl orbit of any root is the set of all
roots.** This is `RootPairing.Base.exists_weylGroupToPerm_eq_of_isSimplyLaced`, stated on the
roots themselves. -/
theorem _root_.RootPairing.Base.orbit_root_eq_range_of_isSimplyLaced [CharZero R] [Finite ι]
    [IsDomain R] [P.IsCrystallographic] [P.IsReduced] [P.IsIrreducible] (b : P.Base)
    (hsl : b.cartanMatrix.IsSimplyLaced) (i : ι) :
    MulAction.orbit P.weylGroup (P.root i) = Set.range P.root := by
  ext x
  refine ⟨?_, ?_⟩
  · rintro ⟨w, rfl⟩
    exact ⟨_, (P.weylGroup_apply_root w i).symm⟩
  · rintro ⟨j, rfl⟩
    obtain ⟨w, hw⟩ := b.exists_weylGroupToPerm_eq_of_isSimplyLaced hsl i j
    exact ⟨w, (P.weylGroup_apply_root w i).trans (congrArg P.root hw)⟩

/-- **The order of the Weyl group of a simply laced irreducible root system** is the number of
roots times the order of the stabilizer of any one of them, by the orbit-stabilizer theorem and
`RootPairing.Base.orbit_root_eq_range_of_isSimplyLaced`. -/
theorem _root_.RootPairing.Base.card_weylGroup_eq_card_mul_card_stabilizer_of_isSimplyLaced
    [CharZero R] [Finite ι] [IsDomain R] [P.IsCrystallographic] [P.IsReduced] [P.IsIrreducible]
    (b : P.Base) (hsl : b.cartanMatrix.IsSimplyLaced) (i : ι) :
    Nat.card P.weylGroup =
      Nat.card ι * Nat.card (MulAction.stabilizer P.weylGroup (P.root i)) := by
  rw [← Subgroup.card_mul_index (MulAction.stabilizer P.weylGroup (P.root i)),
    MulAction.index_stabilizer, ← Nat.card_coe_set_eq, b.orbit_root_eq_range_of_isSimplyLaced hsl,
    Nat.card_range_of_injective P.root.injective, mul_comm]

section

variable {S : Type*} [CommRing S] [LinearOrder S] [Algebra S R]
  [FaithfulSMul S R] [Module S M] [IsScalarTower S R M] [P.IsValuedIn S]

/-- **Root length is a Weyl-group invariant.** A root-positive form is invariant under the Weyl
group by construction, and the Weyl group carries the root indexed by `i` to the root indexed by
`P.weylGroupToPerm w i`. -/
-- Not a `simp` lemma: `simp` unfolds `P.weylGroupToPerm w i` to `(↑↑w).indexEquiv i` through
-- `MonoidHom.domRestrict_apply` and `RootPairing.Equiv.indexHom_apply`, so this left-hand side is
-- never in normal form. The `reflectionPerm` form below is the usable `simp` lemma.
theorem _root_.RootPairing.RootPositiveForm.rootLength_weylGroupToPerm
    (B : P.RootPositiveForm S) (w : P.weylGroup) (i : ι) :
    B.rootLength (P.weylGroupToPerm w i) = B.rootLength i := by
  apply FaithfulSMul.algebraMap_injective S R
  rw [B.algebraMap_rootLength, B.algebraMap_rootLength, ← P.weylGroup_apply_root w i]
  exact _root_.RootPairing.InvariantForm.apply_weylGroup_smul P (B := B.toInvariantForm) w _ _

/-- Reflection in any root preserves root lengths. Mathlib's
`RootPairing.RootPositiveForm.rootLength_reflectionPerm_self` is the case `i = j`. -/
@[simp]
theorem _root_.RootPairing.RootPositiveForm.rootLength_reflectionPerm
    (B : P.RootPositiveForm S) (i j : ι) :
    B.rootLength (P.reflectionPerm i j) = B.rootLength j := by
  rw [← RootPairing.weylGroupToPerm_ofIdx_apply P i j]
  exact RootPairing.RootPositiveForm.rootLength_weylGroupToPerm B _ j

/-- **Every root has the length of one of the simple roots.** Consequently the set of root lengths
of a root pairing is read off its base, which is what lets a rank-two Cartan matrix control the
lengths of all the roots and not only of the two simple ones. -/
theorem _root_.RootPairing.RootPositiveForm.exists_mem_support_rootLength_eq
    [CharZero R] [Finite ι] [IsDomain R]
    [P.IsCrystallographic] [P.IsReduced] (B : P.RootPositiveForm S) (b : P.Base) (j : ι) :
    ∃ i ∈ b.support, B.rootLength j = B.rootLength i := by
  obtain ⟨i, hi, w, rfl⟩ := exists_mem_support_weylGroupToPerm_eq b j
  exact ⟨i, hi, RootPairing.RootPositiveForm.rootLength_weylGroupToPerm B w i⟩

end

end TauCeti
