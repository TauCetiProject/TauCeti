/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.HighestRoot.Basic
public import TauCeti.LinearAlgebra.RootSystem.InvariantForm.SimplyLaced
public import TauCeti.LinearAlgebra.RootSystem.Raising

/-!
# Raising a root to the highest root

Let `b` be a base of a finite, reduced, irreducible, crystallographic root system. The raising step
`RootPairing.Base.exists_root_eq_add_root_and_sub_mem_posRootCone` characterizes the highest root
`θ` by a root-string test: a positive root to which no simple root can be added is `θ`. So `θ` is
greatest and not merely maximal, which also reads as a statement about coefficients in the simple
roots: those of `θ` dominate those of every root, and `θ` is the unique maximum of every strictly
positive weighting of the coefficients.

When the Cartan matrix is simply laced the test can be run by reflections alone: all roots have the
same length, so `α + αₖ` is the reflection of `α` in `αₖ`, and every maximal sequence of simple
reflections raising the height by one ends at `θ`. Without the hypothesis, in `B₂` the positive root
`e₁` lies below the root `e₁ + e₂` but its simple reflections do not raise its height by one.

## Main results

* `RootPairing.Base.eq_highestRoot_of_forall_root_add_notMem`: a positive root to which no simple
  root can be added is the highest root.
* `RootPairing.Base.toWeightBasisInt_repr_le_highestRoot` and
  `RootPairing.Base.sum_mul_toWeightBasisInt_repr_lt_highestRoot`: the highest root in the integral
  coordinates given by the simple roots.
* `RootPairing.Base.exists_isSimpleRaise`: in a simply laced system every positive root other than
  `θ` admits a simple reflection raising its height by one.
* `RootPairing.Base.getLast_eq_highestRoot_of_isChain`: every maximal sequence of such steps ends
  at `θ`.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4–6*, Ch. VI, §1, nos. 3 and 8.
* J. S. Milne, *Algebraic Groups*, Cambridge University Press, 2017, Appendix C, C.24.
-/

public section

open Set

namespace RootPairing.Base

variable {ι R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N]
  [Module R N] {P : RootPairing ι R M N} [CharZero R] (b : P.Base)

/-- The highest root admits no simple raising step. -/
@[simp]
theorem not_isSimpleRaise_highestRoot [Finite ι] [Nonempty ι] (j : ι) :
    ¬ b.IsSimpleRaise b.highestRoot j := fun h ↦ by
  have := b.height_le_height_highestRoot j
  rw [h.height_eq] at this
  omega

section HighestRoot

variable [Finite ι] [Nonempty ι] [IsDomain R] [P.IsCrystallographic] [P.IsReduced]
  [P.IsIrreducible]

/-- **A positive root to which no simple root can be added is the highest root**: the highest root
is greatest among the roots, and not merely maximal. -/
theorem eq_highestRoot_of_forall_root_add_notMem {i : ι} (hi : b.IsPos i)
    (h : ∀ k ∈ b.support, P.root i + P.root k ∉ range P.root) : i = b.highestRoot := by
  by_contra hne
  obtain ⟨k, hk, m, hm, -⟩ := b.exists_root_eq_add_root_and_sub_mem_posRootCone hi hne
    (b.root_highestRoot_sub_mem_posRootCone i)
  exact h k hk ⟨m, hm⟩

/-- A positive root is the highest root exactly when no simple root can be added to it. -/
theorem eq_highestRoot_iff_forall_root_add_notMem {i : ι} (hi : b.IsPos i) :
    i = b.highestRoot ↔ ∀ k ∈ b.support, P.root i + P.root k ∉ range P.root :=
  ⟨fun h _ hk ↦ h ▸ b.root_highestRoot_add_root_notMem hk,
    b.eq_highestRoot_of_forall_root_add_notMem hi⟩

/-- **The coefficients of the highest root dominate those of every root**, in the integral basis of
the root lattice given by the simple roots. -/
theorem toWeightBasisInt_repr_le_highestRoot (j : ι) (k : b.support) :
    b.toWeightBasisInt.repr (P.rootSpanMem ℤ j) k ≤
      b.toWeightBasisInt.repr (P.rootSpanMem ℤ b.highestRoot) k := by
  classical
  obtain ⟨c, hc⟩ := (TauCeti.mem_posRootCone P b).mp (b.root_highestRoot_sub_mem_posRootCone j)
  have hx : P.rootSpanMem ℤ b.highestRoot - P.rootSpanMem ℤ j =
      ∑ l : b.support, c l • b.toWeightBasisInt l := Subtype.ext <| by
    simpa [← Finset.sum_coe_sort b.support] using hc
  have := congrArg (fun x ↦ b.toWeightBasisInt.repr x k) hx
  simp only [map_sub, Finsupp.sub_apply, map_sum, map_nsmul, Module.Basis.repr_self,
    Finsupp.finsetSum_apply, Finsupp.smul_apply] at this
  rw [← sub_nonneg, this]
  refine Finset.sum_nonneg fun _ _ ↦ nsmul_nonneg ?_ _
  rw [Finsupp.single_apply]
  split_ifs <;> simp

/-- **The highest root is the unique maximum of every strictly positive weighting** of the integral
coefficients in the simple roots. -/
theorem sum_mul_toWeightBasisInt_repr_lt_highestRoot {w : b.support → ℤ} (hw : ∀ k, 0 < w k) {j : ι}
    (hj : j ≠ b.highestRoot) :
    ∑ k, w k * b.toWeightBasisInt.repr (P.rootSpanMem ℤ j) k <
      ∑ k, w k * b.toWeightBasisInt.repr (P.rootSpanMem ℤ b.highestRoot) k := by
  have hle := b.toWeightBasisInt_repr_le_highestRoot j
  obtain ⟨k, hk⟩ : ∃ k, b.toWeightBasisInt.repr (P.rootSpanMem ℤ j) k ≠
      b.toWeightBasisInt.repr (P.rootSpanMem ℤ b.highestRoot) k := by
    by_contra! hall
    exact hj (P.root.injective (congrArg Subtype.val (b.toWeightBasisInt.ext_elem hall)))
  exact Finset.sum_lt_sum (fun l _ ↦ mul_le_mul_of_nonneg_left (hle l) (hw l).le)
    ⟨k, Finset.mem_univ k, mul_lt_mul_of_pos_left (lt_of_le_of_ne (hle k) hk) (hw k)⟩

end HighestRoot

section SimplyLaced

variable [Finite ι] [Nonempty ι] [IsDomain R] [P.IsCrystallographic] [P.IsReduced]
  [P.IsIrreducible]

/-- **In a simply laced irreducible root system, every positive root other than the highest root
admits a simple reflection raising its height by exactly one.** -/
theorem exists_isSimpleRaise (hsl : b.cartanMatrix.IsSimplyLaced) {i : ι} (hi : b.IsPos i)
    (hne : i ≠ b.highestRoot) : ∃ j, b.IsSimpleRaise i j := by
  by_contra! h
  refine hne (b.eq_highestRoot_of_forall_root_add_notMem hi fun k hk ⟨m, hm⟩ ↦ ?_)
  exact h _ (b.isSimpleRaise_iff.mpr
    ⟨k, hk, rfl, b.pairingIn_eq_neg_one_of_isSimplyLaced hsl hm⟩)

/-- **In a simply laced irreducible root system, the highest root is the only positive root without
a simple raising step.** -/
theorem eq_highestRoot_iff_forall_not_isSimpleRaise (hsl : b.cartanMatrix.IsSimplyLaced) {i : ι}
    (hi : b.IsPos i) : i = b.highestRoot ↔ ∀ j, ¬ b.IsSimpleRaise i j :=
  ⟨fun h ↦ h ▸ b.not_isSimpleRaise_highestRoot, fun h ↦ by
    by_contra hne
    obtain ⟨j, hj⟩ := b.exists_isSimpleRaise hsl hi hne
    exact h j hj⟩

/-- **In a simply laced irreducible root system, simple raising steps lead every positive root to
the highest root.** -/
theorem reflTransGen_isSimpleRaise_highestRoot (hsl : b.cartanMatrix.IsSimplyLaced) {i : ι}
    (hi : b.IsPos i) : Relation.ReflTransGen b.IsSimpleRaise i b.highestRoot := by
  induction hn : (b.height b.highestRoot - b.height i).toNat using Nat.strong_induction_on
    generalizing i with
  | _ n ih =>
  rcases eq_or_ne i b.highestRoot with rfl | hne
  · exact .refl
  obtain ⟨j, hj⟩ := b.exists_isSimpleRaise hsl hi hne
  have hle := b.height_le_height_highestRoot j
  have hlt : (b.height b.highestRoot - b.height j).toNat < n := by
    rw [hj.height_eq] at hle ⊢
    omega
  exact .head hj (ih _ hlt (hj.isPos hi) rfl)

/-- **In a simply laced irreducible root system, every maximal sequence of simple raising steps
ends at the highest root.** Such a sequence starts at a positive root and has no further step from
its last root. -/
theorem getLast_eq_highestRoot_of_isChain (hsl : b.cartanMatrix.IsSimplyLaced) {l : List ι}
    (hl : l ≠ []) (hchain : l.IsChain b.IsSimpleRaise) (hhead : b.IsPos (l.head hl))
    (hmax : ∀ j, ¬ b.IsSimpleRaise (l.getLast hl) j) : l.getLast hl = b.highestRoot := by
  refine (b.eq_highestRoot_iff_forall_not_isSimpleRaise hsl ?_).mpr hmax
  exact hchain.induction b.IsPos _ (fun _ _ h ↦ h.isPos) (fun _ ↦ hhead) _ (l.getLast_mem hl)

end SimplyLaced

end RootPairing.Base
