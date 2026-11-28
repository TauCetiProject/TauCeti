/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.DoubleCoset
public import Mathlib.GroupTheory.Index
public import Mathlib.RepresentationTheory.Basic
import Mathlib.Tactic.Group
import TauCeti.Algebra.Module.NatInt
import TauCeti.GroupTheory.GroupAction.ConjAct
import TauCeti.RepresentationTheory.RelativeNorm

/-!
# Spherical group-algebra lifts of translates

A translate by `g` need not preserve the vectors fixed by a subgroup `K`. If the index of
`K ∩ gKg⁻¹` in `K` is invertible, averaging the translate over this quotient gives an element of
the group algebra supported on `KgK`. The same element works for every representation: it sends
`K`-fixed vectors into `K`-fixed vectors and agrees with the original translate when tested by a
`K`-invariant linear map. In particular, in a unitary representation it gives the matrix
coefficients of the translate between `K`-fixed vectors, by testing against the inner product with
a fixed vector. Over `ℂ`, the index is invertible when `K` is compact open in a topological group.

The averaging argument follows `New.Data.exists_heckeAlgebra_inner_eq_inner_translate` in
`grh/src/New/Spanning/Multiplicities/EqualMultiplicities.lean` of lsernau/grh-lean (`72fead1`).
-/

public section

open scoped Pointwise
open Representation

universe u v

namespace Subgroup

/-- A single group-algebra element supported on `K g K` realizes the compression of translation
by `g` in every representation: it preserves `K`-fixed vectors and has the same evaluations as `g`
on them against every `K`-invariant linear map. The coefficient ring need only invert the relative
index of `K ∩ gKg⁻¹` in `K`. -/
theorem exists_spherical_lift_of_translate {R G : Type*} [CommSemiring R] [Group G]
    (K : Subgroup G) (g : G) (hindex : IsUnit ((ConjAct.toConjAct g • K).relIndex K : R)) :
    ∃ a : MonoidAlgebra R G, (↑a.coeff.support : Set G) ⊆ DoubleCoset.doubleCoset g K K ∧
      ∀ {V : Type u} [AddCommMonoid V] [Module R V] (ρ : Representation R G V)
        {x : V}, (∀ k : K, ρ k x = x) →
          (∀ k : K, ρ k (ρ.asAlgebraHom a x) = ρ.asAlgebraHom a x) ∧
          ∀ {W : Type v} [AddCommMonoid W] [Module R W] (f : V →ₗ[R] W),
            (∀ k : K, ∀ y : V, f (ρ k y) = f y) →
            f (ρ.asAlgebraHom a x) = f (ρ g x) := by
  classical
  rcases subsingleton_or_nontrivial R with hR | hR
  · refine ⟨0, by simp, ?_⟩
    intro V _ _ ρ x _
    have : Subsingleton V := Module.subsingleton R V
    refine ⟨by simp, ?_⟩
    intro W _ _ f _
    exact congrArg f (Subsingleton.elim _ _)
  let H : Subgroup K := (ConjAct.toConjAct g • K).subgroupOf K
  have hunit : IsUnit (H.index : R) := hindex
  have : H.FiniteIndex := ⟨fun h ↦ hunit.ne_zero (by simp [h])⟩
  let _ : Fintype (K ⧸ H) := H.fintypeQuotientOfFiniteIndex
  let c : R := Ring.inverse (H.index : R)
  let a : MonoidAlgebra R G := ∑ q : K ⧸ H, MonoidAlgebra.single ((q.out : G) * g) c
  refine ⟨a, ?_, ?_⟩
  · intro z hz
    by_contra hnot
    apply Finsupp.mem_support_iff.mp (Finset.mem_coe.mp hz)
    simp only [a, MonoidAlgebra.coeff_sum, MonoidAlgebra.coeff_single, Finsupp.finsetSum_apply]
    refine Finset.sum_eq_zero fun q _ ↦ Finsupp.single_eq_of_ne fun he ↦ hnot ?_
    subst z
    exact DoubleCoset.mem_doubleCoset.mpr ⟨q.out, q.out.property, 1, K.one_mem, by simp⟩
  intro V _ _ ρ x hx
  have hsum : ρ.asAlgebraHom a x = c • relNorm (ρ.comp K.subtype) H (ρ g x) := by
    simp only [a, map_sum, LinearMap.sum_apply, asAlgebraHom_single, LinearMap.smul_apply,
      relNorm_apply, Finset.smul_sum, map_mul, mul_apply_eq_comp, MonoidHom.comp_apply,
      coe_subtype]
  constructor
  · have hfix (k : H) : (ρ.comp K.subtype) (k : K) (ρ g x) = ρ g x := by
      have hk : g⁻¹ * (k : K) * g ∈ K := Subgroup.mem_conjAct_smul_iff.mp k.property
      have he : (k : G) * g = g * (g⁻¹ * (k : K) * g) := by group
      simp only [MonoidHom.comp_apply, coe_subtype]
      rw [← mul_apply_eq_comp, ← map_mul, he, map_mul, mul_apply_eq_comp, hx ⟨_, hk⟩]
    intro k
    rw [hsum, map_smul]
    exact congrArg (c • ·) (relNorm_apply_eq_self (ρ.comp K.subtype) (H := H) hfix k)
  · intro W _ _ f hf
    rw [hsum, map_smul, relNorm_apply, map_sum]
    simp only [MonoidHom.comp_apply, coe_subtype, hf, Finset.sum_const, Finset.card_univ,
      ← Nat.card_eq_fintype_card, ← Subgroup.index_eq_card]
    exact Ring.inverse_natCast_smul_nsmul hunit _

end Subgroup
