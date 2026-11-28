/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Module.Defs
public import TauCeti.GroupTheory.DoubleCoset.ClassSum
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Module.Field
import TauCeti.GroupTheory.DoubleCoset.Finite
import TauCeti.Topology.Algebra.Group.OpenSubgroup.FiniteIndex

/-!
# Positivity of class sums and class integrals

A nonnegative function has a strictly positive class integral if it is positive somewhere,
provided the classes and stabilisers are finite at the level where the function is evaluated.
This is the positivity argument for integrating the diagonal of a pairing of algebraic modular
forms; see B. Gross, *Algebraic modular forms*, Israel J. Math. 113 (1999), §4, and
`New.Space.exists_isUnitary_formTranslation` in
`grh/src/Lib/Adelic/AutomorphicForms/HeckeEigenforms.lean` of [grh-lean](https://github.com/lsernau/grh-lean/tree/72fead1).
-/

public section

namespace TauCeti

variable {G V W : Type*} [Group G] [AddCommGroup W] [Module ℚ W]
  [PartialOrder W] [IsOrderedAddMonoid W] {Γ K : Subgroup G} {f : G → W}

/-- A class sum of a nonnegative function is nonnegative, including when a stabiliser
is infinite or the sum has infinite support. -/
theorem doubleCosetClassSum_nonneg [PosSMulMono ℚ W] (hf : ∀ g, 0 ≤ f g) :
    0 ≤ doubleCosetClassSum Γ K f := by
  rw [doubleCosetClassSum_def]
  exact finsum_nonneg fun q ↦ smul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _)) (hf q.out)

/-- A nonnegative function whose positive locus is constant on double cosets has positive class
sum exactly when it is positive somewhere, if the classes and stabilisers are finite. -/
theorem doubleCosetClassSum_pos_iff [PosSMulMono ℚ W]
    [Finite (DoubleCoset.Quotient (Γ : Set G) K)]
    (hfin : ∀ g, Finite (mackeySubgroup g K Γ))
    (hl : ∀ γ ∈ Γ, ∀ g, 0 < f (γ * g) ↔ 0 < f g)
    (hr : ∀ k ∈ K, ∀ g, 0 < f (g * k) ↔ 0 < f g)
    (hf : ∀ g, 0 ≤ f g) : 0 < doubleCosetClassSum Γ K f ↔ ∃ g, 0 < f g := by
  classical
  let : PosSMulStrictMono ℚ W := PosSMulMono.toPosSMulStrictMono
  have := Fintype.ofFinite (DoubleCoset.Quotient (Γ : Set G) K)
  constructor
  · contrapose!
    intro h
    have hz : ∀ g, f g = 0 := fun g ↦ (eq_of_le_of_not_lt (hf g) (h g)).symm
    simp [doubleCosetClassSum_def, hz]
  · rintro ⟨g, hg⟩
    let q := DoubleCoset.mk Γ K g
    obtain ⟨γ, hγ, k, hk, hout⟩ := DoubleCoset.mk_out_eq_mul Γ K g
    have hq : 0 < f q.out := by
      simpa only [q, hout, hr k hk, hl γ hγ] using hg
    rw [doubleCosetClassSum_def, finsum_eq_sum_of_fintype]
    refine Finset.sum_pos' (fun p _ ↦ smul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
      (hf p.out)) ⟨q, Finset.mem_univ _, ?_⟩
    have := hfin q.out
    exact smul_pos (inv_pos.mpr (Nat.cast_pos.mpr Nat.card_pos)) hq

/-- A class integral of a nonnegative function is nonnegative, regardless of the index
of its right-translation stabiliser. -/
theorem classIntegral_nonneg [PosSMulMono ℚ W] (hf : ∀ g, 0 ≤ f g) : 0 ≤ classIntegral Γ K f := by
  rw [classIntegral_def]
  exact smul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _)) (doubleCosetClassSum_nonneg hf)

/-- For a pair of finite type, an additive probe of a class integral is positive exactly when
it is positive on some value of the integrand. The probe must be nonnegative on all values,
and its positive locus must be left-invariant; the integrand need only have open stabiliser
on the right. -/
theorem map_classIntegral_pos_iff [PosSMulMono ℚ W] [TopologicalSpace G]
    [SeparatelyContinuousMul G] [AddCommGroup V] [Module ℚ V]
    (hK : HasFiniteType Γ K) (p : V →+ W) {f : G → V}
    (hl : ∀ γ ∈ Γ, ∀ g, 0 < p (f (γ * g)) ↔ 0 < p (f g))
    (ho : IsOpen (rightTranslationStabilizer f : Set G)) (hf : ∀ g, 0 ≤ p (f g)) :
    0 < p (classIntegral Γ K f) ↔ ∃ g, 0 < p (f g) := by
  let J := rightTranslationStabilizer f ⊓ K
  have hJK : J ≤ K := inf_le_right
  have : J.IsFiniteRelIndex K :=
    Subgroup.isFiniteRelIndex_of_isOpen_of_isCompact (ho.inter hK.isOpen) hK.isCompact
  have := hK.finite_doubleCoset
  have := finite_doubleCoset_of_le (Γ := Γ) hJK
  have hfin (g : G) : Finite (mackeySubgroup g J Γ) := by
    have := hK.finite_mackeySubgroup g
    have hle : mackeySubgroup g J Γ ≤ mackeySubgroup g K Γ := by
      intro x hx
      rw [mem_mackeySubgroup_iff] at hx ⊢
      exact ⟨hx.1, hJK hx.2⟩
    exact Finite.of_injective (Subgroup.inclusion hle) (Subgroup.inclusion_injective hle)
  let : PosSMulStrictMono ℚ W := PosSMulMono.toPosSMulStrictMono
  have hstep : 0 < p (classIntegral Γ K f) ↔ 0 < doubleCosetClassSum Γ J (p ∘ f) := by
    rw [classIntegral_def, map_rat_smul, map_doubleCosetClassSum]
    exact smul_pos_iff_of_pos_left (inv_pos.mpr (Nat.cast_pos.mpr
      (Nat.pos_of_ne_zero (Subgroup.relIndex_ne_zero (H := J) (K := K)))))
  refine hstep.trans (doubleCosetClassSum_pos_iff hfin hl (fun k hk g ↦ ?_) hf)
  simp only [Function.comp_apply, mem_rightTranslationStabilizer.mp (Subgroup.mem_inf.mp hk).1 g]

end TauCeti
