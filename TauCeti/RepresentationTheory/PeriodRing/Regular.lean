/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Torsion.Free
public import Mathlib.LinearAlgebra.LinearIndependent.Defs
public import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.Tactic.LinearCombination
import TauCeti.Algebra.Group.Action.MulDistribMulAction
import TauCeti.RingTheory.Localization.Action

/-!
# Regular period rings

Fontaine's formalism of period rings starts from a field `F`, a group `G` and a domain `B` on
which `G` acts by `F`-algebra automorphisms, with field of invariants `E = B^G`. The ring `B` is
**regular** when

* the invariants of the fraction field are no larger: `Frac(B)^G = E`, and
* every nonzero `b ∈ B` spanning a `G`-stable `F`-line `F b` is a unit of `B`.

Fields are regular (`IsRegularPeriodRing.of_field`); the motivating examples are Fontaine's
period rings `B_dR`, `B_HT`, `B_cris` and `B_st` over a `p`-adic field. Regularity is what makes
the functor `V ↦ (B ⊗[F] V)^G` well behaved on finite-dimensional representations: see
`TauCeti.RepresentationTheory.PeriodRing.Admissible`.

We state the first condition without the fraction field: whenever `c ≠ 0` and the fraction
`b / c` is `G`-invariant, that is `(g • b) * c = b * (g • c)` for all `g`, then `b = e c` for
some `e ∈ E`. `IsRegularPeriodRing.fixedPoints_fractionRing_eq_range_algebraMap` and
`IsRegularPeriodRing.of_fixedPoints_subset_range` show that this is the condition
`Frac(B)^G = E` for any fraction field of `B` with the induced action. The invariants of `B` are
then exactly `E`, `IsRegularPeriodRing.fixedPoints_eq_range_algebraMap`.

The basic consequence of the first condition is `LinearIndependent.of_invariant`: in a
torsion-free `B`-module with a `B`-semilinear action of `G`, invariant vectors that are linearly
independent over `E` remain linearly independent over `B`. The proof is the classical argument
with a relation of minimal length, whose coefficients are forced to be invariant fractions.

## Main definitions

* `TauCeti.IsRegularPeriodRing F E G B`: Fontaine's regularity of `B` for the action of `G`,
  with field of invariants `E` and lines over `F`.

## Main results

* `LinearIndependent.of_invariant`: invariant vectors independent over `E` are independent
  over `B`.
* `TauCeti.IsRegularPeriodRing.of_field`: a field is a regular period ring.
* `TauCeti.IsRegularPeriodRing.fixedPoints_eq_range_algebraMap`: `B^G = E`.
* `TauCeti.IsRegularPeriodRing.fixedPoints_fractionRing_eq_range_algebraMap`,
  `TauCeti.IsRegularPeriodRing.of_fixedPoints_subset_range`: the first condition of regularity
  says exactly that `Frac(B)^G = E`.

## References

* O. Brinon and B. Conrad, *CMI Summer School notes on p-adic Hodge theory* (2009),
  Definition 5.1.1 and Theorem 5.2.1.
* J.-M. Fontaine and Y. Ouyang, *Theory of p-adic Galois representations*,
  Definition 2.8 and Theorem 2.13.
-/

public section

open Module

section LinearIndependent

variable {E G B W ι : Type*} [CommRing E] [Monoid G] [CommRing B] [IsDomain B] [Algebra E B]
  [MulSemiringAction G B] [AddCommGroup W] [Module B W] [Module E W] [IsScalarTower E B W]
  [IsTorsionFree B W]

/-- Let `G` act on a domain `B` by ring endomorphisms, and suppose every `G`-invariant fraction
`b / c` of `B` is the image of a scalar `e ∈ E`. If `G` acts `B`-semilinearly on a torsion-free
`B`-module `W`, then `G`-invariant vectors of `W` that are linearly independent over `E` are
linearly independent over `B`. -/
theorem LinearIndependent.of_invariant {x : ι → W} (hx : LinearIndependent E x)
    (σ : (g : G) → W →ₛₗ[MulSemiringAction.toRingHom G B g] W) (hσ : ∀ g i, σ g (x i) = x i)
    (hfrac : ∀ ⦃b c : B⦄, c ≠ 0 → (∀ g : G, (g • b) * c = b * (g • c)) →
      ∃ e : E, algebraMap E B e * c = b) :
    LinearIndependent B x := by
  classical
  rw [linearIndependent_iff']
  intro s
  induction s using Finset.strongInduction with
  | H s ih =>
  intro a ha i₀ hi₀
  by_contra hne
  -- Every coefficient is an invariant multiple of `a i₀`: otherwise twisting the relation by
  -- some `g` and subtracting would give a shorter nontrivial relation.
  have hcross (g : G) (i : ι) (hi : i ∈ s) : (g • a i) * a i₀ = a i * (g • a i₀) := by
    have hga : ∑ i ∈ s, (g • a i) • x i = 0 := by
      simpa [map_sum, hσ] using congrArg (σ g) ha
    have hshort : ∑ i ∈ s.erase i₀, ((g • a i₀) * a i - a i₀ * (g • a i)) • x i = 0 := by
      rw [Finset.sum_erase _ (by simp [mul_comm])]
      simp only [sub_smul, Finset.sum_sub_distrib, mul_smul, ← Finset.smul_sum, ha, hga,
        smul_zero, sub_self]
    by_cases hii : i = i₀
    · subst hii
      ring
    · have := ih (s.erase i₀) (Finset.erase_ssubset hi₀) _ hshort i (Finset.mem_erase.2 ⟨hii, hi⟩)
      linear_combination -this
  have hexists (i : ι) (hi : i ∈ s) : ∃ e : E, algebraMap E B e * a i₀ = a i :=
    hfrac hne fun g ↦ hcross g i hi
  choose! e he using hexists
  have hsmul : a i₀ • ∑ i ∈ s, e i • x i = 0 := by
    rw [Finset.smul_sum, ← ha]
    refine Finset.sum_congr rfl fun i hi ↦ ?_
    rw [← he i hi, ← algebraMap_smul B (e i) (x i), smul_smul, mul_comm]
  have hzero := linearIndependent_iff'.1 hx s e ((smul_eq_zero.1 hsmul).resolve_left hne) i₀ hi₀
  exact hne (by rw [← he i₀ hi₀, hzero, map_zero, zero_mul])

end LinearIndependent

namespace TauCeti

variable (F E G B : Type*) [Field F] [Field E] [CommRing B] [Algebra F B] [Algebra E B]

/-- **Fontaine's regular period rings.** A domain `B` with an action of `G` by ring
automorphisms is regular, with field of invariants `E` and lines over `F`, when

* every `G`-invariant fraction of `B` comes from `E`: if `c ≠ 0` and
  `(g • b) * c = b * (g • c)` for all `g`, then `b = e c` for some `e ∈ E`; and
* every nonzero `b ∈ B` spanning a `G`-stable `F`-line is a unit.

When `G` fixes `E` the first condition says that `E` is the field of invariants of the fraction
field of `B` (`IsRegularPeriodRing.fixedPoints_fractionRing_eq_range_algebraMap`), and in
particular `B^G = E`. -/
structure IsRegularPeriodRing [Monoid G] [MulSemiringAction G B] : Prop where
  isDomain : IsDomain B
  exists_algebraMap_mul_eq ⦃b c : B⦄ :
    c ≠ 0 → (∀ g : G, (g • b) * c = b * (g • c)) → ∃ e : E, algebraMap E B e * c = b
  isUnit ⦃b : B⦄ : b ≠ 0 → (∀ g : G, g • b ∈ Submodule.span F {b}) → IsUnit b

namespace IsRegularPeriodRing

variable {F E G B}

section Monoid

variable [Monoid G] [MulSemiringAction G B]

/-- The invariants of a regular period ring are its field of invariant scalars: `B^G = E`. -/
theorem fixedPoints_eq_range_algebraMap [SMulCommClass G E B]
    (h : IsRegularPeriodRing F E G B) :
    MulAction.fixedPoints G B = Set.range (algebraMap E B) := by
  ext b
  refine ⟨fun hb ↦ ?_, ?_⟩
  · have := h.isDomain
    obtain ⟨e, he⟩ := h.exists_algebraMap_mul_eq (b := b) one_ne_zero fun g ↦ by
      rw [smul_one, hb g]
    exact ⟨e, by rwa [mul_one] at he⟩
  · rintro ⟨e, rfl⟩ g
    exact smul_algebraMap g e

variable (L : Type*) [Field L] [Algebra B L] [IsFractionRing B L] [MulSemiringAction G L]
  [SMulDistribClass G B L] [Algebra E L] [IsScalarTower E B L]

/-- For a regular period ring `B`, the invariants of a fraction field `L` of `B`, with the
induced action, are the field of invariant scalars: `Frac(B)^G = E`. -/
theorem fixedPoints_fractionRing_eq_range_algebraMap [SMulCommClass G E B]
    (h : IsRegularPeriodRing F E G B) :
    MulAction.fixedPoints G L = Set.range (algebraMap E L) := by
  have := h.isDomain
  ext x
  refine ⟨fun hx ↦ ?_, ?_⟩
  · obtain ⟨b, c, hc, rfl⟩ := IsFractionRing.div_surjective (A := B) x
    have hc' : c ≠ 0 := nonZeroDivisors.ne_zero hc
    obtain ⟨e, he⟩ :=
      h.exists_algebraMap_mul_eq hc' ((IsFractionRing.div_mem_fixedPoints_iff L b hc').1 hx)
    refine ⟨e, ?_⟩
    rw [eq_div_iff ((map_ne_zero_iff _ (IsFractionRing.injective B L)).2 hc'), ← he, map_mul,
      IsScalarTower.algebraMap_apply E B L]
  · rintro ⟨e, rfl⟩ g
    rw [IsScalarTower.algebraMap_apply E B L, ← algebraMap.smul', smul_algebraMap]

/-- Conversely, a domain `B` such that `Frac(B)^G = E`, for a fraction field `L` of `B` with the
induced action, and whose nonzero elements spanning `G`-stable `F`-lines are units, is a regular
period ring. -/
theorem of_fixedPoints_subset_range [IsDomain B]
    (hL : MulAction.fixedPoints G L ⊆ Set.range (algebraMap E L))
    (hunit : ∀ ⦃b : B⦄, b ≠ 0 → (∀ g : G, g • b ∈ Submodule.span F {b}) → IsUnit b) :
    IsRegularPeriodRing F E G B where
  isDomain := inferInstance
  exists_algebraMap_mul_eq b c hc hbc := by
    obtain ⟨e, he⟩ := hL ((IsFractionRing.div_mem_fixedPoints_iff L b hc).2 hbc)
    have hc' : algebraMap B L c ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective B L)).2 hc
    refine ⟨e, IsFractionRing.injective B L ?_⟩
    rw [map_mul, ← IsScalarTower.algebraMap_apply, he, div_mul_cancel₀ _ hc']
  isUnit := hunit

/-- A field on which `G` acts with field of invariants `E` is a regular period ring. -/
theorem of_field {K : Type*} [Field K] [Algebra F K] [Algebra E K] [MulSemiringAction G K]
    (h : ∀ x : K, (∀ g : G, g • x = x) → ∃ e : E, algebraMap E K e = x) :
    IsRegularPeriodRing F E G K :=
  have := IsFractionRing.idem K
  of_fixedPoints_subset_range K (fun x hx ↦ h x hx) fun _ hb _ ↦ hb.isUnit

end Monoid

end IsRegularPeriodRing

end TauCeti
