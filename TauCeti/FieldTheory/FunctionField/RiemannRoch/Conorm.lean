/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.Divisor.Conorm
public import TauCeti.FieldTheory.FunctionField.RiemannRoch.Basic
import TauCeti.FieldTheory.IntermediateField.Adjoin.Basic
import TauCeti.FieldTheory.RatFunc.Transcendental
import TauCeti.RingTheory.Algebraic.LinearIndependent

/-!
# Riemann–Roch spaces under extension of function fields

For an algebraic extension of function fields with finite restriction fibres, the functions in
`L(D)` are exactly those functions from the smaller field whose images belong to `L(Con D)`.
This gives the
intersection of `L(Con D)` with the smaller field as a submodule equality.

More generally, along any integral extension, finite or not, `f` lies in `L(D)` exactly when its
image lies in `L(D')` for any divisor `D'` of `F'` with the coefficients `e(P' ∣ P) · D(P)` of a
conorm (`TauCeti.mem_riemannRochSpace_algebraMap_iff_of_coeff_eq`). Multiples of a pole divisor
are an example: a function `f` of `F` lies in `L(n (z)_∞)` exactly when its image lies in
`L(n (z)_∞)` computed in `F'` (`TauCeti.mem_riemannRochSpace_nsmul_poles_map_iff`), with no
conorm needed, because both pole divisors are read off from the orders of `z`. For `F' = F`
this says that `L(n (z)_∞)` does not change when the constants `k` are enlarged to an algebraic
extension inside `F` (`TauCeti.restrictScalars_riemannRochSpace_nsmul_poles`). For a
transcendental `x`, descending to the rational subfield `k(x)` shows that a function of `k(x)`
lying in `L((x)_∞)` is a polynomial of degree at most one in `x`
(`TauCeti.mem_span_pair_of_mem_adjoin`).

Multiplying a basis of `L(A)` by an `F`-linearly independent family of `r` functions in `L(C)`
gives `r ℓ(A) ≤ [k' : k] ℓ(Con A + C)`
(`TauCeti.Divisor.card_mul_dim_le_finrank_mul_dim_conorm_add`).

## Reference

H. Stichtenoth, *Algebraic Function Fields and Codes*, second edition, Section III.6,
Theorem 3.6.3(d).
-/

public section

open scoped IntermediateField

namespace TauCeti

open AlgebraicGeometry

universe u u' v v'

variable {k : Type u} {k' : Type u'} {F : Type v} {F' : Type v'}
variable [Field k] [Field k'] [Field F] [Field F']
variable [Algebra k k'] [Algebra k F] [Algebra k' F'] [Algebra F F'] [Algebra k F']
variable [IsScalarTower k k' F'] [IsScalarTower k F F']
variable [Algebra.IsIntegral k k']

/-- **Riemann–Roch membership descends along integral extensions**: let `D'` be a divisor of
`F'` whose coefficient at each place `P'` is `e(P' ∣ P) · D(P)` for a divisor `D` of `F`, where
`P` is the place below `P'`. Then a function `f` of `F` lies in `L(D)` precisely when its image in
`F'` lies in `L(D')`. The extensions `F' / F` and `k' / k` need only be integral, not finite. -/
theorem mem_riemannRochSpace_algebraMap_iff_of_coeff_eq [Algebra.IsIntegral F F']
    (hF' : IsFunctionField k' F') {D : Divisor k F} {D' : Divisor k' F'}
    (hD : ∀ P' : Place k' F',
      D'.coeff P' = Place.ramificationIdx F P' * D.coeff (P'.restrict k F)) (f : F) :
    algebraMap F F' f ∈ riemannRochSpace D' ↔ f ∈ riemannRochSpace D := by
  rcases eq_or_ne f 0 with rfl | hf
  · simp
  have hf' : algebraMap F F' f ≠ 0 := by
    simpa using (algebraMap F F').injective.ne hf
  rw [mem_riemannRochSpace_iff_neg_le_ord hf',
    mem_riemannRochSpace_iff_neg_le_ord hf]
  constructor
  · intro h P
    obtain ⟨P', hP'⟩ := Place.restrict_surjective (k := k) (F := F) hF' P
    dsimp only at hP'
    have hbound := h P'
    rw [hD, Place.ord_algebraMap_restrict k F P'] at hbound
    rw [hP'] at hbound
    have he : (0 : ℤ) < Place.ramificationIdx F P' := by
      exact_mod_cast Place.ramificationIdx_pos F P'
    nlinarith
  · intro h P'
    rw [hD, Place.ord_algebraMap_restrict k F P']
    have he : (0 : ℤ) < Place.ramificationIdx F P' := by
      exact_mod_cast Place.ramificationIdx_pos F P'
    nlinarith [h (P'.restrict k F)]

/-- **Pole bounds descend along integral extensions**: a function `f` of `F` lies in
`L(n (z)_∞)` precisely when its image in `F'` lies in the Riemann–Roch space of `n` times the pole
divisor of the image of `z`. The extensions `F' / F` and `k' / k` need only be integral, not
finite. -/
theorem mem_riemannRochSpace_nsmul_poles_map_iff [Algebra.IsIntegral F F']
    (hF : IsFunctionField k F) (hF' : IsFunctionField k' F') (n : ℕ) (z : Fˣ) (f : F) :
    algebraMap F F' f ∈
        riemannRochSpace (n • Divisor.poles hF' (Units.map (algebraMap F F' : F →* F') z)) ↔
      f ∈ riemannRochSpace (n • Divisor.poles hF z) := by
  -- at a place `P'` over `P` the pole order of `z` scales by `e(P' ∣ P) ≥ 0`
  refine mem_riemannRochSpace_algebraMap_iff_of_coeff_eq hF' (fun P' ↦ ?_) f
  simp only [WeilDivisor.coeff_nsmul, Divisor.coeff_poles, Units.coe_map,
    MonoidHom.coe_ofClass, Place.ord_algebraMap_restrict k F]
  have hmax := mul_max_of_nonneg (-(P'.restrict k F).ord (z : F)) 0
    (Nat.cast_nonneg (α := ℤ) (Place.ramificationIdx F P'))
  rw [mul_zero, mul_neg] at hmax
  rw [← hmax]
  ring

/-- **Enlarging the constants does not change `L(n (z)_∞)`**: for an algebraic extension `k'` of
`k` inside `F`, for instance the full constant field `algebraicClosure k F`, the Riemann–Roch space
of `n` times the pole divisor of `z`, computed over `k'`, is the one computed over `k`. -/
theorem restrictScalars_riemannRochSpace_nsmul_poles [Algebra k' F] [IsScalarTower k k' F]
    (hF : IsFunctionField k F) (hF' : IsFunctionField k' F) (n : ℕ) (z : Fˣ) :
    (riemannRochSpace (n • Divisor.poles hF' z)).restrictScalars k =
      riemannRochSpace (n • Divisor.poles hF z) := by
  ext f
  simpa using mem_riemannRochSpace_nsmul_poles_map_iff (F' := F) hF hF' n z f

/-- **A function of `k(x)` whose poles are bounded by those of `x` lies in `k + k x`**: inside the
rational function field `k(x)`, the Riemann–Roch space of `(x)_∞` contains `1` and `x` and has
dimension at most `deg (x)_∞ + 1 = 2`, and membership descends from `F` to `k(x)`. -/
theorem mem_span_pair_of_mem_adjoin (hF : IsFunctionField k F) {x : F}
    (hx : Transcendental k x) {z : F} (hzx : z ∈ k⟮x⟯)
    (hz : z ∈ riemannRochSpace (Divisor.poles hF (Units.mk0 x fun h ↦ hx (h ▸ isAlgebraic_zero)))) :
    z ∈ Submodule.span k {1, x} := by
  set x₀ := IntermediateField.AdjoinSimple.gen k x
  have hK₀ : IsFunctionField k k⟮x⟯ := hx.isFunctionField_adjoin
  have hex₀ : IsIntegrallyClosedIn k k⟮x⟯ := hx.isIntegrallyClosedIn_adjoin
  have : FiniteDimensional k⟮x⟯ F := hF.finiteDimensional_adjoin hx
  have hx₀ : Transcendental k (x₀ : k⟮x⟯) :=
    (transcendental_algebraMap_iff (algebraMap k⟮x⟯ F).injective).mp hx
  set u : k⟮x⟯ˣ := Units.mk0 x₀ fun h ↦ hx₀ (h ▸ isAlgebraic_zero)
  -- In `k(x)`, the pole divisor of `x` has degree `[k(x) : k(x)] = 1`, so `ℓ((x)_∞) ≤ 2`.
  have hdeg : Divisor.degree (Divisor.poles hK₀ u) = 1 := by
    rw [Divisor.degree_poles hK₀ u hx₀, Units.val_mk0,
      IntermediateField.adjoin_adjoinSimple_gen_eq_top, IntermediateField.finrank_top,
      Nat.cast_one]
  have hdim : Divisor.dim (Divisor.poles hK₀ u) ≤ 2 := by
    have := Divisor.dim_le_degree_posPart_add_one hK₀ hex₀ (Divisor.poles hK₀ u)
    rw [posPart_eq_self.mpr (Divisor.isEffective_poles hK₀ u).zero_le, hdeg] at this
    omega
  -- So `L((x)_∞) = k + k x` inside `k(x)`.
  have hspan : Submodule.span k {(1 : k⟮x⟯), x₀} = riemannRochSpace (Divisor.poles hK₀ u) := by
    -- `1, x₀` are the first two powers of the transcendental `x₀`.
    have hcard := hx₀.finrank_span_range_pow 2
    rw [show (Set.range fun i : Fin 2 ↦ x₀ ^ (i : ℕ)) = {1, x₀} by
      ext; simp [Fin.exists_fin_two, eq_comm]] at hcard
    have := finiteDimensional_riemannRochSpace hK₀ (Divisor.poles hK₀ u)
    refine Submodule.eq_of_le_of_finrank_le ?_ (by rw [hcard, ← Divisor.dim_def]; exact hdim)
    rw [Submodule.span_le, Set.insert_subset_iff, Set.singleton_subset_iff]
    exact ⟨one_mem_riemannRochSpace_iff.mpr (Divisor.isEffective_poles hK₀ u).zero_le,
      mem_riemannRochSpace_poles hK₀ u⟩
  -- The function `z` descends to `L((x)_∞)` computed in `k(x)`.
  have hw : (⟨z, hzx⟩ : k⟮x⟯) ∈ riemannRochSpace (Divisor.poles hK₀ u) := by
    have hu : Units.map (algebraMap k⟮x⟯ F : k⟮x⟯ →* F) u =
        Units.mk0 x fun h ↦ hx (h ▸ isAlgebraic_zero) :=
      Units.ext (IntermediateField.AdjoinSimple.algebraMap_gen k x)
    have h := mem_riemannRochSpace_nsmul_poles_map_iff (k' := k) hK₀ hF 1 u ⟨z, hzx⟩
    rw [one_nsmul, one_nsmul, hu] at h
    -- `algebraMap k⟮x⟯ F ⟨z, hzx⟩` is `z` by definition.
    exact h.mp hz
  rw [← hspan, Submodule.mem_span_pair] at hw
  obtain ⟨a, b, hab⟩ := hw
  rw [Submodule.mem_span_pair]
  exact ⟨a, b, by simpa [x₀] using congrArg (algebraMap k⟮x⟯ F) hab⟩

section FiniteFibres

variable [Algebra.IsIntegral F F']
variable [∀ P : Place k F, Finite {P' : Place k' F' // P'.restrict k F = P}]

/-- A function from `F` belongs to `L(D)` precisely when its image in `F'` belongs to the
Riemann–Roch space of the conorm of `D`. -/
-- This equivalence is for targeted rewriting: `simpNF` rejects it as a simp lemma because
-- simplification unfolds Riemann–Roch membership on the left-hand side.
theorem mem_riemannRochSpace_conorm_iff (hF' : IsFunctionField k' F')
    (D : Divisor k F) (f : F) :
    algebraMap F F' f ∈ riemannRochSpace (Divisor.conorm k' F' D) ↔
      f ∈ riemannRochSpace D :=
  mem_riemannRochSpace_algebraMap_iff_of_coeff_eq hF' (Divisor.coeff_conorm k' F' D) f

/-- The intersection of `L(Con D)` with the image of `F` is `L(D)`, expressed as a
`k`-submodule equality. This form can be used without unfolding either Riemann–Roch space. -/
@[simp]
theorem riemannRochSpace_conorm_comap (hF' : IsFunctionField k' F')
    (D : Divisor k F) :
    Submodule.comap (IsScalarTower.toAlgHom k F F').toLinearMap
      ((riemannRochSpace (Divisor.conorm k' F' D) : Submodule k' F').restrictScalars k) =
        riemannRochSpace D := by
  ext f
  exact mem_riemannRochSpace_conorm_iff hF' D f

end FiniteFibres

variable [FiniteDimensional F F']

/-- An `F`-linearly independent family of `r` functions in `L(C)` multiplies the dimension of
the Riemann–Roch space of any divisor `A` of `F`: `r ℓ(A) ≤ [k' : k] ℓ(Con A + C)`, where `ℓ(A)`
is a dimension over `k` and `ℓ(Con A + C)` one over `k'`.  The products of a `k`-basis of `L(A)`
with the family are `k`-linearly independent and lie in `L(Con A + C)`, whose dimension over `k`
is `[k' : k] ℓ(Con A + C)`.  When the constants do not grow, `k' = k`, this reads
`r ℓ(A) ≤ ℓ(Con A + C)`. -/
theorem Divisor.card_mul_dim_le_finrank_mul_dim_conorm_add [FiniteDimensional k k']
    (hF' : IsFunctionField k' F') {ι : Type*} [Fintype ι] {z : ι → F'}
    (hz : LinearIndependent F z) {C : Divisor k' F'} (hzC : ∀ i, z i ∈ riemannRochSpace C)
    (A : Divisor k F) :
    Fintype.card ι * Divisor.dim A ≤
      Module.finrank k k' * Divisor.dim (Divisor.conorm k' F' A + C) := by
  have : Algebra.IsAlgebraic F F' := Algebra.IsAlgebraic.of_finite F F'
  have hF : IsFunctionField k F := (hF'.of_finiteDimensional (k := k)).of_isAlgebraic_top
  set V := riemannRochSpace (Divisor.conorm k' F' A + C)
  have := finiteDimensional_riemannRochSpace hF A
  have := finiteDimensional_riemannRochSpace hF' (Divisor.conorm k' F' A + C)
  have : FiniteDimensional k V := Module.Finite.trans k' V
  let u := Module.finBasis k (riemannRochSpace A)
  have hu : LinearIndependent k fun j ↦ (u j : F) :=
    u.linearIndependent.map' _ (Submodule.ker_subtype _)
  have hmem (p : Fin (Module.finrank k (riemannRochSpace A)) × ι) : (u p.1 : F) • z p.2 ∈ V := by
    rw [Algebra.smul_def]
    exact mul_mem_riemannRochSpace_add
      ((mem_riemannRochSpace_conorm_iff hF' A _).mpr (u p.1).2) (hzC p.2)
  have hv : LinearIndependent k fun p ↦ (⟨_, hmem p⟩ : V) := by
    refine LinearIndependent.of_comp (V.subtype.restrictScalars k) ?_
    simpa [Function.comp_def] using linearIndependent_smul hu hz
  have hcard := hv.fintype_card_le_finrank
  rw [Fintype.card_prod, Fintype.card_fin, ← Module.finrank_mul_finrank k k' V] at hcard
  rw [Divisor.dim_def, Divisor.dim_def, mul_comm]
  exact hcard

end TauCeti
