/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RepresentationTheory.FinGroupCharZero
public import TauCeti.GroupTheory.DoubleCoset.Identity
public import TauCeti.RepresentationTheory.Induction.Mackey.Intertwining
import TauCeti.CategoryTheory.Simple.Endomorphism
import TauCeti.CategoryTheory.Preadditive.Indecomposable

/-!
# Mackey disjointness and the necessary condition for irreducibility

Let `H` be a subgroup of a finite group `G` and let `A` be a finite-dimensional representation of
`H` over a field. The intertwining-number formula `TauCeti.finrank_hom_indFDRep_mackey_erase` reads

`dim End_G(Ind_H^G A) = dim End_H A + ∑_{HsH ≠ H} dim Hom_{H ⊓ sHs⁻¹}(Res A, {}^s A)`,

a sum of natural numbers. If the left-hand side is `1`, the first summand is `1` and every other
summand is `0`. Thus `A` is simple and the restrictions `Res_{H ⊓ sHs⁻¹} A` and
`Res_{H ⊓ sHs⁻¹} ({}^s A)` are **disjoint**, that is, have no nonzero intertwiner, for every
nonidentity double coset. Disjointness is named here as `TauCeti.MackeyDisjoint`.

This necessary condition holds over any field in which `|H|` is invertible, without algebraic
closure or invertibility of `|G|`. `FDRep.forall_mackeyDisjoint_out_iff` converts between the
double-coset and elementwise forms over any field. `Mackey.Split` builds on these lemmas for the
splitting-field criterion and its algebraically closed corollaries.

## Main definitions

* `TauCeti.MackeyDisjoint`: the restrictions of `A` and of `{}^s A` to the Mackey subgroup
  `H ⊓ sHs⁻¹` admit no nonzero intertwiner.

## Main statements

* `TauCeti.mackeyDisjoint_iff_subsingleton`, `TauCeti.MackeyDisjoint.eq_zero` and
  `TauCeti.mackeyDisjoint_of_forall_eq_zero`: the predicate read back as the vanishing of every
  intertwiner.
* `FDRep.simple_and_mackeyDisjoint_of_finrank_end_indFDRep_eq_one`: the necessary condition
  from a one-dimensional induced endomorphism space, assuming only invertibility of `|H|`.
* `FDRep.forall_mackeyDisjoint_out_iff`: equivalence of double-coset and elementwise disjointness.
* `TauCeti.mackeyDisjoint_mul_left_mul_right_iff`: Mackey disjointness depends only on the double
  coset.

## Implementation notes

`TauCeti.MackeyDisjoint` is stated as `Subsingleton` of the intertwining space; the
intertwining-number formula produces the dimension of that space instead, and
`TauCeti.mackeyDisjoint_iff_finrank_eq_zero` is the bridge between the two readings, along which
the double-coset criterion is proved.  That bridge is deliberately not a `simp` lemma: the named
predicate is the form the criteria are stated in and the form its own API
(`TauCeti.mackeyDisjoint_mul_left_mul_right_iff`) applies to, so unfolding it to a dimension on
sight would be the wrong normal form.

The step in those proofs that the arithmetic does not hand over for free is that `dim End_H A`
cannot be `0`: a representation with no nonzero endomorphism is a zero object, whose induction
is also zero, contradicting `dim End_G(Ind A) = 1`. The resulting necessary condition
`FDRep.simple_and_mackeyDisjoint_of_finrank_end_indFDRep_eq_one` needs no algebraic closure.

Passing between the two forms of the criterion needs the Mackey term to be constant on a double
coset, which is `TauCeti.finrank_hom_res_mackeyToH_mul_left_mul_right`, proved with the formula it
belongs to; `TauCeti.mackeyDisjoint_mul_left_mul_right_iff` is its reading through the predicate.

The dimension formula follows from `FDRep.indHomMackeyLinearEquiv` and holds over every
field. `TauCeti.MackeyDisjoint` and its API hold over any field.

For a normal subgroup the Mackey subgroup is all of `H`. Restricting along
`TauCeti.mackeySubgroupNormalEquiv` shows that the corresponding Mackey term and
`Hom_H(A, {}^s A)` have equal dimensions. For simple `A`,
`TauCeti.mackeyDisjoint_iff_isEmpty_iso_of_normal` identifies disjointness with the absence of
an isomorphism from the conjugate to `A`.

## References

* J.-P. Serre, *Linear Representations of Finite Groups*, Chapter 7.4, Proposition 23.
* I. M. Isaacs, *Character Theory of Finite Groups*, Chapter 5, Theorem 5.6 and Corollary 5.7.
-/

public section

open scoped Pointwise

open CategoryTheory Limits

namespace TauCeti

universe u

section Disjoint

variable {k G : Type u} [Field k] [Group G] {H : Subgroup G}

/-- **Mackey disjointness at `s`**: the restrictions of `A` and of its conjugate `{}^s A` to the
Mackey subgroup `H ⊓ sHs⁻¹` admit no nonzero intertwiner.  The conjugation and the restriction of
`{}^s A` are packaged into the single homomorphism `TauCeti.mackeyToH`.

This is the condition the Mackey irreducibility criterion imposes on every double coset other than
`H` itself. -/
def MackeyDisjoint (A : FDRep k H) (s : G) : Prop :=
  Subsingleton (Subgroup.resFDRep ((mackeySubgroup s H H).subgroupOf H) A ⟶
    (Action.res (FGModuleCat k) (mackeyToH s H H)).obj A)

/-- **Mackey disjointness unfolded.**  The body of `TauCeti.MackeyDisjoint` is not exposed, so
this is how a consumer reads the definition. -/
theorem mackeyDisjoint_iff_subsingleton (A : FDRep k H) (s : G) :
    MackeyDisjoint A s ↔
      Subsingleton (Subgroup.resFDRep ((mackeySubgroup s H H).subgroupOf H) A ⟶
        (Action.res (FGModuleCat k) (mackeyToH s H H)).obj A) :=
  Iff.rfl

/-- An intertwiner between the two restrictions of a Mackey disjoint pair is zero. -/
theorem MackeyDisjoint.eq_zero {A : FDRep k H} {s : G} (h : MackeyDisjoint A s)
    (φ : Subgroup.resFDRep ((mackeySubgroup s H H).subgroupOf H) A ⟶
      (Action.res (FGModuleCat k) (mackeyToH s H H)).obj A) : φ = 0 :=
  @Subsingleton.elim _ h φ 0

/-- Mackey disjointness holds as soon as every intertwiner between the two restrictions is zero. -/
theorem mackeyDisjoint_of_forall_eq_zero {A : FDRep k H} {s : G}
    (h : ∀ φ : Subgroup.resFDRep ((mackeySubgroup s H H).subgroupOf H) A ⟶
      (Action.res (FGModuleCat k) (mackeyToH s H H)).obj A, φ = 0) : MackeyDisjoint A s :=
  ⟨fun φ ψ => (h φ).trans (h ψ).symm⟩

/-- Mackey disjointness read as the vanishing of a dimension, which is the shape in which the
intertwining-number formula produces it. -/
theorem mackeyDisjoint_iff_finrank_eq_zero (A : FDRep k H) (s : G) :
    MackeyDisjoint A s ↔
      Module.finrank k (Subgroup.resFDRep ((mackeySubgroup s H H).subgroupOf H) A ⟶
        (Action.res (FGModuleCat k) (mackeyToH s H H)).obj A) = 0 :=
  Module.finrank_zero_iff.symm

/-- **Mackey disjointness depends only on the double coset**: it holds at `h₁ s h₂` with
`h₁, h₂ ∈ H` exactly when it holds at `s`.  This is the predicate form of
`TauCeti.finrank_hom_res_mackeyToH_mul_left_mul_right`, and is what moves the criterion between
its double-coset and its elementwise reading. -/
theorem mackeyDisjoint_mul_left_mul_right_iff (A : FDRep k H) {h₁ h₂ : G} (hh₁ : h₁ ∈ H)
    (hh₂ : h₂ ∈ H) (s : G) : MackeyDisjoint A (h₁ * s * h₂) ↔ MackeyDisjoint A s := by
  rw [mackeyDisjoint_iff_finrank_eq_zero, mackeyDisjoint_iff_finrank_eq_zero,
    finrank_hom_res_mackeyToH_mul_left_mul_right A A hh₁ hh₂ s]

end Disjoint

section NormalDisjoint

variable {k G : Type u} [Field k] [Group G] {H : Subgroup G} [H.Normal]

/-- For a normal subgroup and an irreducible `A`, Mackey disjointness at `s` says exactly that
the conjugate `{}^s A` is not isomorphic to `A`. -/
theorem mackeyDisjoint_iff_isEmpty_iso_of_normal (A : FDRep k H) [Simple A] (s : G) :
    MackeyDisjoint A s ↔ IsEmpty (conjNormalFDRep s A ≅ A) := by
  have hsimple : Simple (conjNormalFDRep s A) := by
    rw [conjNormalFDRep, ← conjNormalFDRepEquiv_functor]
    exact CategoryTheory.simple_obj _ A
  let _ := hsimple
  rw [mackeyDisjoint_iff_finrank_eq_zero, finrank_hom_res_mackeyToH_of_normal]
  constructor
  · intro h
    have hsubsingleton : Subsingleton (A ⟶ conjNormalFDRep s A) :=
      Module.finrank_zero_iff.mp h
    exact ⟨fun e ↦ (CategoryTheory.isIso_iff_nonzero e.symm.hom).mp inferInstance
      (hsubsingleton.elim e.symm.hom 0)⟩
  · intro h
    exact CategoryTheory.finrank_hom_simple_simple_eq_zero_of_not_iso k
      fun e ↦ h.false e.symm

end NormalDisjoint

end TauCeti

namespace FDRep

open TauCeti

variable {k G : Type u} [Field k] [Group G] {H : Subgroup G}

/-- Mackey disjointness outside the subgroup is equivalent to disjointness at the
chosen representatives of all nonidentity double cosets. -/
theorem forall_mackeyDisjoint_out_iff (A : FDRep k H) :
    (∀ D : DoubleCoset.Quotient (H : Set G) (H : Set G),
      D ≠ DoubleCoset.mk H H 1 → MackeyDisjoint A D.out) ↔
      ∀ s ∉ H, MackeyDisjoint A s := by
  constructor
  · intro h s hs
    obtain ⟨a, ha, b, hb, hab⟩ :=
      DoubleCoset.eq.mp (DoubleCoset.out_eq' (DoubleCoset.mk H H s))
    exact hab ▸ (mackeyDisjoint_mul_left_mul_right_iff A ha hb _).mpr
      (h _ fun hc => hs ((doubleCosetMk_eq_mk_one_iff_mem H s).mp hc))
  · intro h D hD
    exact h D.out fun hmem => hD ((DoubleCoset.out_eq' D).symm.trans
      ((doubleCosetMk_eq_mk_one_iff_mem H D.out).mpr hmem))

/-- If the induced endomorphism space is a line, the original representation is simple
and every nonidentity Mackey intertwining space vanishes. Only invertibility of the
subgroup order, not of the ambient group order or a splitting hypothesis, is needed. -/
theorem simple_and_mackeyDisjoint_of_finrank_end_indFDRep_eq_one [Finite G] (A : FDRep k H)
    (hH : IsUnit (Nat.card H : k))
    (hEnd : Module.finrank k (indFDRep A ⟶ indFDRep A) = 1) :
    Simple A ∧ ∀ D : DoubleCoset.Quotient (H : Set G) (H : Set G),
      D ≠ DoubleCoset.mk H H 1 → MackeyDisjoint A D.out := by
  classical
  let := Fintype.ofFinite (DoubleCoset.Quotient (H : Set G) (H : Set G))
  have : NeZero (Nat.card H : k) := ⟨hH.ne_zero⟩
  have hA : Module.finrank k (A ⟶ A) ≠ 0 := by
    intro hzero
    have : Subsingleton (A ⟶ A) := Module.finrank_zero_iff.mp hzero
    have hz : IsZero A := (IsZero.iff_id_eq_zero A).mpr (Subsingleton.elim _ _)
    apply not_isZero_of_finrank_end_eq_one hEnd
    simpa only [indFDRepFunctor_obj] using
      (indFDRepFunctor (k := k) (S := H)).map_isZero hz
  rw [finrank_hom_indFDRep_mackey_erase] at hEnd
  have hsplit := (Nat.add_eq_one_iff.mp hEnd).resolve_left fun h => hA h.1
  refine ⟨CategoryTheory.simple_of_finrank_end_eq_one k A hsplit.1, fun D hD => ?_⟩
  apply (mackeyDisjoint_iff_finrank_eq_zero A D.out).mpr
  exact Finset.sum_eq_zero_iff.mp hsplit.2 D (Finset.mem_erase.mpr ⟨hD, by simp⟩)

end FDRep
