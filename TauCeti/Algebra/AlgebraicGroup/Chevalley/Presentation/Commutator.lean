/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Chevalley.Presentation.Basic
public import Mathlib.LinearAlgebra.RootSystem.Finite.G2
import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.NotG2

/-!
# Commutators of root generators in Steinberg's presented group

For a valid Dynkin type `t` and a commutative ring `A`, let `St` be the group presented by
Steinberg's relations, `TauCeti.DynkinType.steinbergRelators`. If the roots `α` and `β` sum to a
root, the commutator relations write the commutator of the generators `X_α(u)` and `X_β(v)` as a
product of generators at roots `jα + kβ` with `j, k > 0`. This file records that shape: the
commutator lies in every subgroup of `St` containing the generators at all such roots. The roots
`α` and `β` may have any signs.

Outside `G₂` the relevant relators are the one- and two-factor ones, along the root strings
`β, α + β, 2α + β` and `α, α + β, α + 2β`. In type `G₂` the lengths of `α`, `β` and `α + β` sort
the pair into the one-, three- and four-factor relators, using the root-string facts of
`TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.G2.RootString`.

## Main results

* `TauCeti.DynkinType.commutatorElement_mem_of_root_eq_add`: the commutator of the generators
  at roots `α`, `β` with `α + β` a root lies in every subgroup containing the generators at the
  roots `jα + kβ` with `j, k > 0`. Its two cases are
  `TauCeti.DynkinType.commutatorElement_mem_of_isNotG2_of_root_eq_add` outside `G₂` and
  `TauCeti.DynkinType.commutatorElement_mem_of_g2_of_root_eq_add` in type `G₂`.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, Chapter 3, Lemma 15, and Chapter 6, proof of
  Theorem 8.
* R. W. Carter, *Simple Groups of Lie Type*, Theorem 5.2.2 and Chapter 12.
-/

public section

open scoped commutatorElement
open Multiplicative

namespace TauCeti.DynkinType

universe u

variable {t : DynkinType} {ht : t.Valid} {A : Type u} [CommRing A]

/-- **Commutators of root generators outside `G₂`.** If the roots `α` and `β` sum to a root `γ`,
the commutator of the generators at `α` and `β` lies in every subgroup that contains the generators
at all roots `jα + kβ` with `j, k > 0`: by the root-string relators it is a product of generators
at `α + β` and possibly `2α + β` or `α + 2β`. -/
theorem commutatorElement_mem_of_isNotG2_of_root_eq_add [(t.rationalRootSystem ht).IsNotG2]
    {α β γ : Fin t.numRoots} {H : Subgroup (PresentedGroup (t.steinbergRelators ht A))}
    (hγ : (t.simplyConnectedRootDatum ht).root γ =
      (t.simplyConnectedRootDatum ht).root α + (t.simplyConnectedRootDatum ht).root β)
    (hH : ∀ (δ : Fin t.numRoots) (j k : ℕ), 0 < j → 0 < k →
      (t.rationalRootSystem ht).root δ =
        j • (t.rationalRootSystem ht).root α + k • (t.rationalRootSystem ht).root β →
      ∀ w : A, PresentedGroup.mk (t.steinbergRelators ht A) (steinbergRoot δ w) ∈ H)
    (u v : A) :
    ⁅t.steinbergRootSubgroup ht A α (ofAdd u), t.steinbergRootSubgroup ht A β (ofAdd v)⁆ ∈ H := by
  let P := t.rationalRootSystem ht
  let R := t.simplyConnectedRootDatum ht
  have hγQ : P.root γ = P.root α + P.root β := by
    simpa only [one_nsmul] using
      (t.root_rationalRootSystem_eq_nsmul_add_iff ht α β γ 1).mpr (by rwa [one_nsmul])
  have hlin := P.linearIndependent_of_add_mem_range_root' ⟨γ, hγQ⟩
  have hγH := hH γ 1 1 one_pos one_pos (by rwa [one_nsmul, one_nsmul])
  by_cases hdouble : 2 • R.root α + R.root β ∈ Set.range R.root
  · -- The root string `β, α + β, 2α + β`.
    obtain ⟨δ, hδ⟩ := hdouble
    rw [commutatorElement_eq_of_isSteinbergRelator (IsSteinbergRelator.commutator_two_nsmul_add
      hγ hδ (three_nsmul_add_notMem_range_root α β)
      (add_two_nsmul_notMem_range_root hlin ⟨δ, hδ⟩) u v), map_mul]
    exact H.mul_mem (hγH _) (hH δ 2 1 two_pos one_pos (by
      rw [(t.root_rationalRootSystem_eq_nsmul_add_iff ht α β δ 2).mpr hδ, one_nsmul]) _)
  · by_cases hdouble' : R.root α + 2 • R.root β ∈ Set.range R.root
    · -- The root string `α, α + β, α + 2β`.
      obtain ⟨δ, hδ⟩ := hdouble'
      have hthree : R.root α + 3 • R.root β ∉ Set.range R.root := by
        rw [add_comm]
        exact three_nsmul_add_notMem_range_root β α
      rw [commutatorElement_eq_of_isSteinbergRelator
        (IsSteinbergRelator.commutator_add_two_nsmul hγ hδ hdouble hthree u v), map_mul]
      exact H.mul_mem (hγH _) (hH δ 1 2 one_pos two_pos (by
        rw [(t.root_rationalRootSystem_eq_nsmul_add_iff ht β α δ 2).mpr (by rw [hδ, add_comm]),
          one_nsmul, add_comm]) _)
    · -- Neither double string: the one-factor relation.
      rw [commutatorElement_eq_of_isSteinbergRelator
        (IsSteinbergRelator.commutator_add hγ hdouble hdouble' u v)]
      exact hγH _

/-- In type `G₂`, if the roots `α` and `β` sum to a short root `γ`, the commutator of their
generators is a product of generators at `γ` and at two or three further roots `jα + kβ` with
`j, k > 0`, by the three- or four-factor relation. The hypothesis `hmem` is stated for the
integral roots, in which the relators are written. -/
private theorem g2_commutatorElement_mem_of_short_sum {ht : G2.Valid} {α β γ : Fin G2.numRoots}
    {H : Subgroup (PresentedGroup (G2.steinbergRelators ht A))} (hγs : g2Length γ = 1)
    (hγ : (G2.simplyConnectedRootDatum ht).root γ =
      (G2.simplyConnectedRootDatum ht).root α + (G2.simplyConnectedRootDatum ht).root β)
    (hmem : ∀ (δ : Fin G2.numRoots) (j k : ℕ), 0 < j → 0 < k →
      (G2.simplyConnectedRootDatum ht).root δ =
        j • (G2.simplyConnectedRootDatum ht).root α + k • (G2.simplyConnectedRootDatum ht).root β →
      ∀ w : A, PresentedGroup.mk (G2.steinbergRelators ht A) (steinbergRoot δ w) ∈ H)
    (u v : A) :
    ⁅G2.steinbergRootSubgroup ht A α (ofAdd u), G2.steinbergRootSubgroup ht A β (ofAdd v)⁆ ∈
      H := by
  -- The `G₂` root-string facts are stated for the native datum, which is the assembled one.
  have hγn : g2SimplyConnectedRootDatum.root γ =
      g2SimplyConnectedRootDatum.root α + g2SimplyConnectedRootDatum.root β := by
    rwa [← simplyConnectedRootDatum_G2 ht]
  set R := G2.simplyConnectedRootDatum ht
  have hγH := hmem γ 1 1 one_pos one_pos (by rw [hγ, one_nsmul, one_nsmul])
  rcases g2Length_eq_one_or_eq_three α with hαs | hαl <;>
    rcases g2Length_eq_one_or_eq_three β with hβs | hβl
  · -- Two short roots: the three-factor relation, with factors at `2α + β` and `α + 2β`.
    obtain ⟨l, m, hl, hm⟩ : ∃ l m : Fin G2.numRoots,
        R.root l = R.root α + R.root γ ∧ R.root m = R.root γ + R.root β := by
      have h := g2_exists_root_eq_add_of_short_add_short_eq_short α β γ hαs hβs hγs hγn
      rwa [← simplyConnectedRootDatum_G2 ht] at h
    rw [commutatorElement_eq_of_isSteinbergRelator
      (IsSteinbergRelator.g2_short_pair hαs hβs hγs hγ hl hm u v), map_mul, map_mul]
    exact H.mul_mem (H.mul_mem (hγH _) (hmem l 2 1 two_pos one_pos (by
      rw [hl, hγ]; module) _)) (hmem m 1 2 one_pos two_pos (by rw [hm, hγ]; module) _)
  · -- Short root first: factors at `2α + β`, `3α + β` and `3α + 2β`.
    obtain ⟨δ, ε, ζ, hδ, hε, hζ⟩ : ∃ δ ε ζ : Fin G2.numRoots, R.root δ = R.root α + R.root γ ∧
        R.root ε = R.root α + R.root δ ∧ R.root ζ = R.root δ + R.root γ := by
      have h := g2_exists_root_eq_add_of_short_add_long_eq_root α β γ hαs hβl hγn
      rwa [← simplyConnectedRootDatum_G2 ht] at h
    rw [commutatorElement_eq_of_isSteinbergRelator
      (IsSteinbergRelator.g2_short_long hγ hδ hε hζ u v), map_mul, map_mul, map_mul]
    exact H.mul_mem (H.mul_mem (H.mul_mem (hγH _)
      (hmem δ 2 1 two_pos one_pos (by rw [hδ, hγ]; module) _))
      (hmem ε 3 1 three_pos one_pos (by rw [hε, hδ, hγ]; module) _))
      (hmem ζ 3 2 three_pos two_pos (by rw [hζ, hδ, hγ]; module) _)
  · -- Long root first: factors at `α + 2β`, `α + 3β` and `2α + 3β`.
    have hγ' : R.root γ = R.root β + R.root α := hγ.trans (add_comm _ _)
    obtain ⟨δ, ε, ζ, hδ, hε, hζ⟩ : ∃ δ ε ζ : Fin G2.numRoots, R.root δ = R.root β + R.root γ ∧
        R.root ε = R.root β + R.root δ ∧ R.root ζ = R.root δ + R.root γ := by
      have h := g2_exists_root_eq_add_of_short_add_long_eq_root β α γ hβs hαl
        (hγn.trans (add_comm _ _))
      rwa [← simplyConnectedRootDatum_G2 ht] at h
    rw [commutatorElement_eq_of_isSteinbergRelator
      (IsSteinbergRelator.g2_long_short hγ' hδ hε hζ v u), map_mul, map_mul, map_mul]
    exact H.mul_mem (H.mul_mem (H.mul_mem (hγH _)
      (hmem δ 1 2 one_pos two_pos (by rw [hδ, hγ]; module) _))
      (hmem ε 1 3 one_pos three_pos (by rw [hε, hδ, hγ]; module) _))
      (hmem ζ 2 3 two_pos three_pos (by rw [hζ, hδ, hγ]; module) _)
  · -- Two long roots have a long sum.
    have := g2Length_eq_three_of_long_add_long_eq_root α β γ hαl hβl hγn
    omega

/-- **Commutators of root generators in type `G₂`.** If the roots `α` and `β` of `G₂` sum to a
root `γ`, the commutator of the generators at `α` and `β` lies in every subgroup containing the
generators at all roots `jα + kβ` with `j, k > 0`: by the relators it is a product of generators
at `α + β` and, depending on the lengths of `α`, `β` and `γ`, at none, two or three further such
roots. -/
theorem commutatorElement_mem_of_g2_of_root_eq_add {ht : G2.Valid} {α β γ : Fin G2.numRoots}
    {H : Subgroup (PresentedGroup (G2.steinbergRelators ht A))}
    (hγ : (G2.simplyConnectedRootDatum ht).root γ =
      (G2.simplyConnectedRootDatum ht).root α + (G2.simplyConnectedRootDatum ht).root β)
    (hH : ∀ (δ : Fin G2.numRoots) (j k : ℕ), 0 < j → 0 < k →
      (G2.rationalRootSystem ht).root δ =
        j • (G2.rationalRootSystem ht).root α + k • (G2.rationalRootSystem ht).root β →
      ∀ w : A, PresentedGroup.mk (G2.steinbergRelators ht A) (steinbergRoot δ w) ∈ H)
    (u v : A) :
    ⁅G2.steinbergRootSubgroup ht A α (ofAdd u), G2.steinbergRootSubgroup ht A β (ofAdd v)⁆ ∈
      H := by
  -- The relators are stated for the integral roots; `hH` asks for the rational ones.
  have hmem (δ : Fin G2.numRoots) (j k : ℕ) (hj : 0 < j) (hk : 0 < k)
      (hδ : (G2.simplyConnectedRootDatum ht).root δ =
        j • (G2.simplyConnectedRootDatum ht).root α + k • (G2.simplyConnectedRootDatum ht).root β)
      (w : A) : PresentedGroup.mk (G2.steinbergRelators ht A) (steinbergRoot δ w) ∈ H := by
    refine hH δ j k hj hk (funext fun l => ?_) w
    simp only [Pi.add_apply, Pi.smul_apply, root_rationalRootSystem, hδ]
    simp only [nsmul_eq_mul]
    push_cast
    ring
  rcases g2Length_eq_one_or_eq_three γ with hγs | hγl
  · exact g2_commutatorElement_mem_of_short_sum hγs hγ hmem u v
  · -- A long sum: neither `2α + β = α + γ` nor `α + 2β = β + γ` is a root, so the one-factor
    -- relation applies.
    have hγn : g2SimplyConnectedRootDatum.root γ =
        g2SimplyConnectedRootDatum.root α + g2SimplyConnectedRootDatum.root β := by
      rwa [← simplyConnectedRootDatum_G2 ht]
    have hα := g2_root_add_notMem_range_of_add_eq_long α β γ hγl hγn
    have hβ := g2_root_add_notMem_range_of_add_eq_long β α γ hγl (hγn.trans (add_comm _ _))
    rw [← simplyConnectedRootDatum_G2 ht] at hα hβ
    set R := G2.simplyConnectedRootDatum ht
    have h2α : 2 • R.root α + R.root β = R.root α + R.root γ := by rw [hγ]; module
    have h2β : R.root α + 2 • R.root β = R.root β + R.root γ := by rw [hγ]; module
    rw [commutatorElement_eq_of_isSteinbergRelator (IsSteinbergRelator.commutator_add hγ
      (by rwa [h2α]) (by rwa [h2β]) u v)]
    exact hmem γ 1 1 one_pos one_pos (by rw [hγ, one_nsmul, one_nsmul]) _

/-- **Commutators of root generators.** If the roots `α` and `β` sum to a root `γ`, the
commutator of the generators at `α` and `β` lies in every subgroup containing the generators at
all roots `jα + kβ` with `j, k > 0`. -/
theorem commutatorElement_mem_of_root_eq_add {α β γ : Fin t.numRoots}
    {H : Subgroup (PresentedGroup (t.steinbergRelators ht A))}
    (hγ : (t.simplyConnectedRootDatum ht).root γ =
      (t.simplyConnectedRootDatum ht).root α + (t.simplyConnectedRootDatum ht).root β)
    (hH : ∀ (δ : Fin t.numRoots) (j k : ℕ), 0 < j → 0 < k →
      (t.rationalRootSystem ht).root δ =
        j • (t.rationalRootSystem ht).root α + k • (t.rationalRootSystem ht).root β →
      ∀ w : A, PresentedGroup.mk (t.steinbergRelators ht A) (steinbergRoot δ w) ∈ H)
    (u v : A) :
    ⁅t.steinbergRootSubgroup ht A α (ofAdd u), t.steinbergRootSubgroup ht A β (ofAdd v)⁆ ∈ H := by
  by_cases htG2 : t = G2
  · subst htG2
    exact commutatorElement_mem_of_g2_of_root_eq_add hγ hH u v
  · have := isNotG2_rationalRootSystem_of_ne_G2 (ht := ht) htG2
    exact commutatorElement_mem_of_isNotG2_of_root_eq_add hγ hH u v

end TauCeti.DynkinType
