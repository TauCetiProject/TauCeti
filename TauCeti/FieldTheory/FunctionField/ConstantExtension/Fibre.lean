/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.ConstantExtension.Algebraic
public import TauCeti.FieldTheory.FunctionField.ConstantExtension.Degree
public import TauCeti.FieldTheory.FunctionField.ConstantExtension.ResidueField
public import TauCeti.FieldTheory.FunctionField.ConstantExtension.Unramified
public import TauCeti.FieldTheory.FunctionField.Divisor.ProductFormula
public import TauCeti.FieldTheory.FunctionField.Place.Extension.Basic
public import TauCeti.FieldTheory.FunctionField.RiemannRoch.Genus

import TauCeti.FieldTheory.FunctionField.ConstantExtension.Basis
import TauCeti.FieldTheory.FunctionField.ConstantExtension.FiniteDescent
import TauCeti.FieldTheory.FunctionField.Place.Approximation
import TauCeti.FieldTheory.FunctionField.Place.Degree
import TauCeti.FieldTheory.FunctionField.Place.Extension.Existence
import TauCeti.FieldTheory.FunctionField.Place.Extension.Fibre
import TauCeti.FieldTheory.FunctionField.Place.Extension.Tower

/-!
# The places over a place in an algebraic constant field extension

Let `F / k` be an algebraic function field, let `k' / k` be an algebraic extension, finite or not,
and let `F' = F · k'` be the compositum. This file proves that a place `P` of `F / k` has at most
`deg P` places of `F' / k'` above it. In particular the fibre over `P` is finite even when
`F' / F` is an infinite extension, and a rational place has exactly one place above it. Neither
separability of `k' / k` nor exactness of `k` in `F` is assumed for these bounds.

For a finite extension `k' / k` this is a count in the fundamental inequality. A place `P'` over
`P` has residue field containing both `F_P` and `k'`, so the tower identity
`[k' : k] · deg P' = f(P' ∣ P) · deg P` gives `[k' : k] ≤ f(P' ∣ P) · deg P`. Summing over the
fibre and using `∑ e(P' ∣ P) f(P' ∣ P) ≤ [F' : F] ≤ [k' : k]` bounds the number of places by
`deg P`.

For an arbitrary algebraic `k' / k`, finitely many distinct places of `F'` are told apart by
finitely many functions, one in the valuation ring of each place and outside that of another.
These functions already lie in `F · L` for a finite subextension `L / k`
(`TauCeti.exists_finiteDimensional_constantSubfield_of_finset_subset_constantCompositum`), so
the places stay distinct after restriction to `F · L`, where the finite bound applies.

When `k' / k` is separable and `k` is the exact constant field of `F`, the degrees of the places
over `P` add up to the degree of `P`:

`∑_{P' ∣ P} deg P' = deg P`.

This is Stichtenoth's Theorem 3.6.3(c), `deg (Con A) = deg A`, for the divisor `A = P`, and it
holds for infinite `k' / k` as well. The place `P` is the only pole of some function `z ∈ F`.
Every place over `P` has ramification index one, so the pole divisor of `z` in `F'` is `m` times
the sum of the places over `P`, where `m = -ord_P z`, while in `F` it is `m P`. The degree of a
pole divisor is the degree `[F : k(z)]`, which does not change when the constants are extended.
Equality `#{P' ∣ P} = deg P` holds when every place over `P` is rational. This is the case when
`k' / k` is normal and the residue field of `P` embeds into `k'`, for example when `k'` is a
separable closure of `k` and the residue field of `P` is separable over `k`: then `P` splits into
exactly `deg P` rational places.

The finiteness of the fibre is what the conorm of a divisor needs, so these statements are the
first step in comparing the divisor theories of `F / k` and `F · k' / k'` for an infinite
algebraic extension of constants, such as an algebraic closure of `k`.

## Main results

* `TauCeti.Place.card_le_degree_of_constantCompositum_eq_top`: finitely many distinct places of
  `F · k'` over `P` number at most `deg P`.
* `TauCeti.Place.finite_setOf_restrict_eq_of_constantCompositum_eq_top`: the fibre over `P` is
  finite.
* `TauCeti.Place.ncard_setOf_restrict_eq_le_degree_of_constantCompositum_eq_top`: the fibre over
  `P` has at most `deg P` elements.
* `TauCeti.Place.existsUnique_restrict_eq_of_degree_eq_one_of_constantCompositum_eq_top`:
  exactly one place lies over a rational place.
* `TauCeti.Place.finsum_degree_restrict_eq_degree_of_constantCompositum_eq_top`: **the degrees of
  the places over `P` add up to `deg P`** in a separable algebraic constant field extension.
* `TauCeti.Place.ncard_setOf_restrict_eq_eq_degree_of_constantCompositum_eq_top`: there are exactly
  `deg P` places over `P` when `k' / k` is normal and the residue field of `P` embeds into `k'`.

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Theorem 3.1.11, Section III.6 and Theorem 3.6.3(c), (g).
-/

public section

namespace TauCeti

namespace Place

universe u u' v v'

variable {k : Type u} {k' : Type u'} {F : Type v} {F' : Type v'}
variable [Field k] [Field k'] [Field F] [Field F']
variable [Algebra k k'] [Algebra k F] [Algebra k F'] [Algebra k' F'] [Algebra F F']
variable [IsScalarTower k k' F'] [IsScalarTower k F F']

section Integral

variable [Algebra.IsIntegral F F']

/-- The bound for a finite extension of constants: each place over `P` contributes at least
`[k' : k]` to `deg P · ∑ e(P' ∣ P) f(P' ∣ P) ≤ deg P · [k' : k]`. -/
private theorem card_le_degree_of_finiteDimensional [FiniteDimensional k k']
    (hF : IsFunctionField k F) (h : constantCompositum F k' F' = ⊤) (P : Place k F)
    (t : Finset (Place k' F')) (ht : ∀ P' ∈ t, P'.restrict k F = P) :
    t.card ≤ P.degree := by
  let := finiteDimensional_of_constantCompositum_eq_top (k := k) (k' := k') h
  have hF' := hF.of_constantCompositum_eq_top h
  have hpos : 0 < Module.finrank k k' := Module.finrank_pos
  -- a place over `P` has residue field containing `k'`, so `[k' : k] ≤ f(P' ∣ P) · deg P`
  have hle (P' : Place k' F') (hP' : P' ∈ t) :
      Module.finrank k k' ≤ ramificationIdx F P' * relativeDegree k F P' * P.degree := by
    have hdeg := finrank_mul_degree_eq_relativeDegree_mul_degree_restrict k F P'
    rw [ht P' hP'] at hdeg
    have h₁ := P'.one_le_degree_of_isFunctionField hF'
    have h₂ := ramificationIdx_pos F P'
    calc Module.finrank k k' ≤ Module.finrank k k' * P'.degree := Nat.le_mul_of_pos_right _ h₁
      _ = relativeDegree k F P' * P.degree := hdeg
      _ ≤ ramificationIdx F P' * (relativeDegree k F P' * P.degree) :=
        Nat.le_mul_of_pos_left _ h₂
      _ = _ := (mul_assoc _ _ _).symm
  have hsum := sum_ramificationIdx_mul_relativeDegree_le_finrank k F P t ht
  have hcomp := finrank_le_finrank_of_constantCompositum_eq_top (k := k) h
  refine Nat.le_of_mul_le_mul_right ?_ hpos
  calc t.card * Module.finrank k k' = ∑ _P' ∈ t, Module.finrank k k' := by
        rw [Finset.sum_const, smul_eq_mul]
    _ ≤ ∑ P' ∈ t, ramificationIdx F P' * relativeDegree k F P' * P.degree :=
        Finset.sum_le_sum hle
    _ = (∑ P' ∈ t, ramificationIdx F P' * relativeDegree k F P') * P.degree :=
        (Finset.sum_mul _ _ _).symm
    _ ≤ Module.finrank k k' * P.degree := Nat.mul_le_mul_right _ (hsum.trans hcomp)
    _ = P.degree * Module.finrank k k' := mul_comm _ _

/-- The bound once finitely many places over `P` are told apart by functions of `F · L` for a
finite subextension `L / k`: restriction to `F · L` is then injective on them, and the finite
bound applies there. -/
private theorem card_le_degree_of_separated (hF : IsFunctionField k F) (L : IntermediateField k k')
    [FiniteDimensional k L] (P : Place k F) (t : Finset (Place k' F'))
    (ht : ∀ P' ∈ t, P'.restrict k F = P)
    (hsep : ∀ P₁ ∈ t, ∀ P₂ ∈ t, P₁ ≠ P₂ →
      ∃ z ∈ constantCompositum F L F', z ∈ P₁.integers ∧ z ∉ P₂.integers) :
    t.card ≤ P.degree := by
  classical
  let E := constantCompositum F L F'
  let : Algebra L E := ((algebraMap L F').codRestrict E
    (algebraMap_mem_constantCompositum F L F')).toAlgebra
  have : IsScalarTower L E F' := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have : IsScalarTower k L E := IsScalarTower.of_algebraMap_eq fun c ↦
    Subtype.ext (IsScalarTower.algebraMap_apply k L F' c)
  have hE : constantCompositum F L E = ⊤ := (constantCompositum_eq_top_iff F L F' E).mpr rfl
  let : FiniteDimensional F E := finiteDimensional_of_constantCompositum_eq_top (k := k) hE
  let : Algebra.IsAlgebraic E F' := Algebra.IsAlgebraic.tower_top (K := F) (L := E)
  have hinj : Set.InjOn (fun P' : Place k' F' ↦ P'.restrict L E) t := by
    intro P₁ h₁ P₂ h₂ heq
    beta_reduce at heq
    by_contra hne
    obtain ⟨z, hzE, hz₁, hz₂⟩ := hsep P₁ h₁ P₂ h₂ hne
    have hmem : (⟨z, hzE⟩ : E) ∈ (P₁.restrict L E).integers :=
      (mem_integers_restrict_iff L E P₁ _).mpr hz₁
    rw [heq, mem_integers_restrict_iff] at hmem
    exact hz₂ hmem
  rw [← Finset.card_image_of_injOn hinj]
  exact card_le_degree_of_finiteDimensional hF hE P _ fun Q hQ ↦ by
    obtain ⟨P', hP', rfl⟩ := Finset.mem_image.mp hQ
    rw [restrict_restrict]
    exact ht P' hP'

variable [Algebra.IsAlgebraic k k']

/-- **A place has at most `deg P` places above it in a constant field extension**: if
`F' = F · k'` for an algebraic extension `k' / k`, finite or not, then finitely many distinct places
of `F' / k'` lying over a place `P` of `F / k` number at most `deg P`. Neither separability of
`k' / k` nor exactness of the constants is needed. -/
theorem card_le_degree_of_constantCompositum_eq_top (hF : IsFunctionField k F)
    (h : constantCompositum F k' F' = ⊤) (P : Place k F) (t : Finset (Place k' F'))
    (ht : ∀ P' ∈ t, P'.restrict k F = P) :
    t.card ≤ P.degree := by
  classical
  -- distinct places are told apart by a function regular at the first and not at the second
  have hsep (P₁ P₂ : Place k' F') :
      ∃ z : F', P₁ ≠ P₂ → z ∈ P₁.integers ∧ z ∉ P₂.integers := by
    by_cases hne : P₁ = P₂
    · exact ⟨0, fun h ↦ (h hne).elim⟩
    · obtain ⟨z, hz₁, hz₂⟩ := exists_mem_integers_notMem_integers hne
      exact ⟨z, fun _ ↦ ⟨hz₁, hz₂⟩⟩
  choose z hz using hsep
  -- the finitely many separating functions are defined over a finite extension `L / k`
  obtain ⟨L, hL, hzL⟩ :=
    exists_finiteDimensional_constantSubfield_of_finset_subset_constantCompositum
      (k := k) (F := F) ((t ×ˢ t).image fun p ↦ z p.1 p.2) fun x _ ↦ h ▸ IntermediateField.mem_top
  let : FiniteDimensional k L := hL
  exact card_le_degree_of_separated hF L P t ht fun P₁ h₁ P₂ h₂ hne ↦
    ⟨z P₁ P₂, hzL _ (Finset.mem_image.mpr ⟨(P₁, P₂), Finset.mem_product.mpr ⟨h₁, h₂⟩, rfl⟩),
      hz P₁ P₂ hne⟩

/-- **A place has only finitely many places above it in a constant field extension**: if
`F' = F · k'` for an algebraic extension `k' / k`, finite or not, the places of `F' / k'` lying
over a place of `F / k` form a finite set. -/
theorem finite_setOf_restrict_eq_of_constantCompositum_eq_top (hF : IsFunctionField k F)
    (h : constantCompositum F k' F' = ⊤) (P : Place k F) :
    {P' : Place k' F' | P'.restrict k F = P}.Finite := by
  rw [← Set.not_infinite]
  intro hinf
  obtain ⟨t, hts, hcard⟩ := hinf.exists_subset_card_eq (P.degree + 1)
  have := card_le_degree_of_constantCompositum_eq_top hF h P t fun P' hP' ↦ hts hP'
  omega

/-- **A place has at most `deg P` places above it in a constant field extension**: if
`F' = F · k'` for an algebraic extension `k' / k`, finite or not, the set of places of `F' / k'`
lying over a place `P` of `F / k` has at most `deg P` elements. -/
theorem ncard_setOf_restrict_eq_le_degree_of_constantCompositum_eq_top
    (hF : IsFunctionField k F) (h : constantCompositum F k' F' = ⊤) (P : Place k F) :
    {P' : Place k' F' | P'.restrict k F = P}.ncard ≤ P.degree := by
  have hfin := finite_setOf_restrict_eq_of_constantCompositum_eq_top hF h P
  rw [Set.ncard_eq_toFinset_card _ hfin]
  exact card_le_degree_of_constantCompositum_eq_top hF h P _ fun P' hP' ↦
    hfin.mem_toFinset.mp hP'

/-- **A rational place has exactly one place above it in a constant field extension**: if
`F' = F · k'` for an algebraic extension `k' / k`, finite or not, and `P` is a place of `F / k`
of degree one, then exactly one place of `F' / k'` lies over `P`. -/
theorem existsUnique_restrict_eq_of_degree_eq_one_of_constantCompositum_eq_top
    (hF : IsFunctionField k F) (h : constantCompositum F k' F' = ⊤) {P : Place k F}
    (hP : P.degree = 1) :
    ∃! P' : Place k' F', P'.restrict k F = P := by
  classical
  obtain ⟨P', hP'⟩ := restrict_surjective (k := k) (F := F) (hF.of_constantCompositum_eq_top h) P
  refine ⟨P', hP', fun Q hQ ↦ ?_⟩
  by_contra hne
  have := card_le_degree_of_constantCompositum_eq_top hF h P {Q, P'} (by simp [hQ, hP'])
  rw [Finset.card_pair hne, hP] at this
  omega

end Integral

variable [Algebra.IsSeparable k k']

/-- **The degrees of the places over a place add up to its degree** (Stichtenoth,
Theorem 3.6.3(c), for a single place): if `k` is the exact constant field of `F` and
`F' = F · k'` for a separable algebraic extension `k' / k`, finite or not, then for every place
`P` of `F / k`,

`∑_{P' ∣ P} deg P' = deg P`,

where `deg P'` is the degree of `P'` over `k'`. -/
theorem finsum_degree_restrict_eq_degree_of_constantCompositum_eq_top
    (hF : IsFunctionField k F) (hex : IsIntegrallyClosedIn k F)
    (h : constantCompositum F k' F' = ⊤) (P : Place k F) :
    letI := isAlgebraic_of_constantCompositum_eq_top (k := k) (k' := k') h
    ∑ᶠ P' ∈ {P' : Place k' F' | P'.restrict k F = P}, P'.degree = P.degree := by
  classical
  let := isAlgebraic_of_constantCompositum_eq_top (k := k) (k' := k') h
  have hF' : IsFunctionField k' F' := hF.of_constantCompositum_eq_top h
  have hfin := finite_setOf_restrict_eq_of_constantCompositum_eq_top hF h P
  obtain ⟨z, hP, hQ⟩ := exists_ord_neg_and_forall_ne_ord_nonneg hF P
  obtain ⟨n, hn⟩ : ∃ n : ℕ, P.ord z = -(n : ℤ) := ⟨(-P.ord z).toNat, by omega⟩
  have hn0 : n ≠ 0 := by omega
  have hz0 : z ≠ 0 := by
    rintro rfl
    simp at hP
  have hz : algebraMap F F' z ≠ 0 := (map_ne_zero _).2 hz0
  have hzk : ¬IsAlgebraic k z := P.transcendental_of_ord_ne_zero hP.ne
  have hzk' : ¬IsAlgebraic k' (algebraMap F F' z) :=
    (Algebra.IsAlgebraic.transcendental_iff k k').1
      ((transcendental_algebraMap_iff (algebraMap F F').injective).2 hzk)
  -- In `F'`, every place over `P` is unramified, so the pole divisor of `z` is `m` times the sum
  -- of the places over `P`.
  have hpoles' : Divisor.poles hF' (Units.mk0 _ hz) =
      (n : ℤ) • AlgebraicGeometry.WeilDivisor.ofFinset hfin.toFinset := by
    ext P'
    rw [Divisor.coeff_poles, Units.val_mk0, AlgebraicGeometry.WeilDivisor.coeff_zsmul,
      AlgebraicGeometry.WeilDivisor.coeff_ofFinset, ord_algebraMap_restrict k F P' z,
      ramificationIdx_eq_one_of_constantCompositum_eq_top (k := k) h P', Nat.cast_one, one_mul]
    by_cases hP' : P'.restrict k F = P
    · simp only [hP', Set.Finite.mem_toFinset, Set.mem_ofPred_eq, ite_true, mul_one]
      omega
    · have := hQ _ hP'
      simp only [hP', Set.Finite.mem_toFinset, Set.mem_ofPred_eq, ite_false, mul_zero]
      omega
  -- The degree of the pole divisor of `z` is `[F' : k'(z)] = [F : k(z)] = n deg P`.
  have hdeg := Divisor.degree_poles hF' (Units.mk0 _ hz) (by simpa using hzk')
  rw [hpoles', Divisor.degree_zsmul, AlgebraicGeometry.WeilDivisor.ofFinset_eq_sum, map_sum,
    Units.val_mk0, finrank_over_adjoin_simple_eq_of_constantCompositum_eq_top hex h z,
    finrank_adjoin_eq_mul_degree_of_ord_eq_neg hF hn0 hn hQ] at hdeg
  simp only [Divisor.degree_ofPoint] at hdeg
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin]
  push_cast at hdeg
  exact_mod_cast mul_left_cancel₀ (by exact_mod_cast hn0 : (n : ℤ) ≠ 0) hdeg

/-- **A place splits into `deg P` rational places once its residue field embeds into the
constants**: if `k` is the exact constant field of `F`, `F' = F · k'` for a separable normal
algebraic extension `k' / k`, finite or not, and the residue field of a place `P` of `F / k`
admits a `k`-embedding into `k'`, then exactly `deg P` places of `F' / k'` lie over `P`. This
applies to every place with residue field separable over `k` when `k'` is a separable closure of
`k`. -/
theorem ncard_setOf_restrict_eq_eq_degree_of_constantCompositum_eq_top [Normal k k']
    (hF : IsFunctionField k F) (hex : IsIntegrallyClosedIn k F)
    (h : constantCompositum F k' F' = ⊤) (P : Place k F) (φ : P.ResidueField →ₐ[k] k') :
    letI := isAlgebraic_of_constantCompositum_eq_top (k := k) (k' := k') h
    {P' : Place k' F' | P'.restrict k F = P}.ncard = P.degree := by
  let := isAlgebraic_of_constantCompositum_eq_top (k := k) (k' := k') h
  have hfin := finite_setOf_restrict_eq_of_constantCompositum_eq_top hF h P
  rw [← finsum_degree_restrict_eq_degree_of_constantCompositum_eq_top hF hex h P,
    finsum_mem_eq_finite_toFinset_sum _ hfin, Set.ncard_eq_toFinset_card _ hfin,
    Finset.card_eq_sum_ones]
  refine Finset.sum_congr rfl fun P' hP' ↦ ?_
  rw [Set.Finite.mem_toFinset, Set.mem_ofPred_eq] at hP'
  subst hP'
  exact (degree_eq_one_of_constantCompositum_eq_top hF hex h P' φ).symm

end Place

end TauCeti
