/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.Place.Extension.Fundamental
import TauCeti.RingTheory.DedekindDomain.IntegralClosure
import TauCeti.RingTheory.Ideal.GoingUp
import TauCeti.RingTheory.Length.Norm.Basic

/-!
# The order of a norm at a place

Let `F' / k'` be a finite extension of the field extension `F / k`, with `k'` integral over `k`,
and let `P` be a place of `F / k` whose local model `𝒪'_P`, the integral closure of `𝒪_P` in
`F'`, is a finite `𝒪_P`-module. This holds when `F' / F` is separable
(`TauCeti.Place.moduleFinite_integralClosure`) and when `F / k` is an algebraic function field
(`TauCeti.Place.moduleFinite_integralClosure_of_isFunctionField`). For `x ∈ F'` this file then
proves the **order-of-a-norm formula**

`ord_P (N_{F'/F} x) = ∑_{P' ∣ P} f(P' ∣ P) · ord_{P'} x`,

the sum running over the finitely many places `P'` of `F' / k'` above `P`, weighted by their
relative degrees. It is the coefficient identity behind the norm of divisors,
`N(div x) = div (N_{F'/F} x)` (`TauCeti.Divisor.norm_principal`).

The proof reads Fulton's order-of-a-norm formula `TauCeti.ordFrac_norm_eq_finprod` on the local
model `𝒪_P ⊆ 𝒪'_P`, which needs `𝒪'_P` to be a finite `𝒪_P`-module. The maximal ideals of the
Dedekind domain `𝒪'_P` are the centres of the places above `P`, their local rings are the
valuation rings of those places, and the `𝒪_P`-length of each residue ring is the relative degree,
so Fulton's formula is the displayed one.

## Main results

* `TauCeti.Place.ord_norm_of_moduleFinite`: the order-of-a-norm formula whenever `𝒪'_P` is a finite
  `𝒪_P`-module, in particular for a separable extension.
* `TauCeti.Place.ord_norm_of_isFunctionField`: the order-of-a-norm formula for any finite extension
  of an algebraic function field, with no separability hypothesis.

## References

* W. Fulton, *Intersection Theory*, 2nd ed., Springer, 1998, Appendix A.3 and Proposition 1.4.
* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Section III.1 (places of an extension, ramification index and relative degree).
-/

public section

open IsDedekindDomain

namespace TauCeti

namespace Place

universe u u' v v'

variable {k : Type u} {k' : Type u'} {F : Type v} {F' : Type v'}
variable [Field k] [Field k'] [Field F] [Field F']
variable [Algebra k k'] [Algebra k F] [Algebra k' F'] [Algebra F F'] [Algebra k F']
variable [IsScalarTower k k' F'] [IsScalarTower k F F']

attribute [local instance 10] algebraIntegersExtension isScalarTowerIntegersExtension

variable [FiniteDimensional F F']

section LocalModel

/-! ### The order of a norm on the local model

Throughout, `𝒪'_P` is the integral closure of `𝒪_P` in `F'`, assumed to be a finite `𝒪_P`-module,
and given its `k'`-algebra structure. It is then a semilocal Dedekind domain whose maximal ideals
are the centres of the places above `P`, so Fulton's order-of-a-norm formula
`TauCeti.ordFrac_norm_eq_finprod` for `𝒪_P ⊆ 𝒪'_P` is the formula for `ord_P` of a norm. -/

variable (P : Place k F) [Module.Finite P.integers (integralClosure P.integers F')]
  [IsDedekindDomain (integralClosure P.integers F')] [Algebra k' (integralClosure P.integers F')]
  [IsScalarTower k' (integralClosure P.integers F') F']

/-- The `𝒪_P`-length of the residue ring of a height one prime `𝔓` of the local model is the
relative degree of the place of `𝔓`. -/
private theorem length_quotient_toNat (𝔓 : HeightOneSpectrum (integralClosure P.integers F')) :
    (Module.length P.integers (integralClosure P.integers F' ⧸ 𝔓.asIdeal)).toNat =
      relativeDegree k F (ofPrime k' F' 𝔓) := by
  have := Ideal.liesOver_maximalIdeal_of_isIntegral (R := P.integers) 𝔓.asIdeal
  let _ : Field (P.integers ⧸ IsLocalRing.maximalIdeal P.integers) := Ideal.Quotient.field _
  have : Module.Finite (P.integers ⧸ IsLocalRing.maximalIdeal P.integers)
      (integralClosure P.integers F' ⧸ 𝔓.asIdeal) :=
    Module.Finite.of_restrictScalars_finite P.integers _ _
  rw [relativeDegree_ofPrime (k := k) (F := F) (R := P.integers),
    Ideal.inertiaDeg_eq_of_isMaximal (IsLocalRing.maximalIdeal P.integers) 𝔓.asIdeal,
    Module.length_eq_of_surjective (R := P.integers ⧸ IsLocalRing.maximalIdeal P.integers)
      Ideal.Quotient.mk_surjective, Module.length_eq_finrank, ENat.toNat_natCast]

/-- **The order of a norm on the local model**, in multiplicative form. -/
private theorem valuation_norm_inv {s : Finset (Place k' F')}
    (hs : ∀ P' : Place k' F', P' ∈ s ↔ P'.restrict k F = P) {x : F'} (hx : x ≠ 0) :
    (P.valuation (Algebra.norm F x))⁻¹ =
      ∏ P' ∈ s, ((P'.valuation x)⁻¹) ^ relativeDegree k F P' := by
  have hR : ∀ r : P.integers, algebraMap P.integers F r ∈ P.integers := fun r ↦ r.property
  have hne (m : MaximalSpectrum (integralClosure P.integers F')) : m.asIdeal ≠ ⊥ :=
    have := Ideal.liesOver_maximalIdeal_of_isIntegral (R := P.integers) m.asIdeal
    Ideal.ne_bot_of_liesOver_of_ne_bot (IsDiscreteValuationRing.not_a_field P.integers) m.asIdeal
  -- An opaque name for the height one prime of a maximal ideal, so that the instances on its
  -- place are found syntactically.
  obtain ⟨toH, htoH⟩ : ∃ toH : MaximalSpectrum (integralClosure P.integers F') →
      HeightOneSpectrum (integralClosure P.integers F'), ∀ m, (toH m).asIdeal = m.asIdeal :=
    ⟨fun m ↦ ⟨m.asIdeal, m.isMaximal.isPrime, hne m⟩, fun _ ↦ rfl⟩
  have : ∀ m, IsLocalization.AtPrime (ofPrime k' F' (toH m)).integers m.asIdeal := fun m ↦ by
    have h : IsLocalization.AtPrime (ofPrime k' F' (toH m)).integers (toH m).asIdeal :=
      inferInstance
    convert h using 2
    exact (htoH m).symm
  -- The family instances of `ordFrac_norm_eq_finprod` are not found under the binder `∀ m`, so
  -- they are stated here.
  let _ : ∀ m, Algebra (integralClosure P.integers F') (ofPrime k' F' (toH m)).integers :=
    fun _ ↦ inferInstance
  have : ∀ m, IsScalarTower (integralClosure P.integers F') (ofPrime k' F' (toH m)).integers F' :=
    fun _ ↦ inferInstance
  have key := ordFrac_norm_eq_finprod (A := P.integers) (K := F)
    (B := integralClosure P.integers F') (L := F') (fun m ↦ (ofPrime k' F' (toH m)).integers) hx
  -- Reindex the maximal ideals of the local model by the places above `P`: these are the primes
  -- of the local model over the centre of `P`, the maximal ideal of `𝒪_P`.
  have hs' (P' : Place k' F') : P' ∈ s ↔ P'.restrict k F = ofPrime k F (P.center hR) := by
    rw [hs, ofPrime_center]
  let e : {P' // P' ∈ s} ≃ MaximalSpectrum (integralClosure P.integers F') :=
    ((Equiv.subtypeEquivRight hs').trans (restrictOfPrimeEquivPrimesOver k F (P.center hR))).trans
      { toFun 𝔓 := ⟨𝔓.val, 𝔓.property.1.isMaximal (Ideal.ne_bot_of_mem_primesOver
          (P.center hR).ne_bot 𝔓.property)⟩
        invFun m := ⟨m.asIdeal, m.isMaximal.isPrime, P.center_integers_asIdeal hR ▸
          Ideal.liesOver_maximalIdeal_of_isIntegral m.asIdeal⟩
        left_inv _ := rfl
        right_inv _ := rfl }
  have he (P' : {P' // P' ∈ s}) : ofPrime k' F' (toH (e P')) = P' :=
    (congrArg _ (HeightOneSpectrum.ext ((htoH _).trans
      (restrictOfPrimeEquivPrimesOver_apply_coe k F (P.center hR) _)))).trans
      (ofPrime_center k' F' P'.val _)
  rw [← ordFrac_integers, key, ← finprod_comp_equiv e,
    finprod_eq_prod_of_fintype, ← Finset.prod_coe_sort s]
  refine Finset.prod_congr rfl fun P' _ ↦ ?_
  rw [ordFrac_integers, ← he P', ← length_quotient_toNat P (toH (e P')), htoH]

end LocalModel

variable [Algebra.IsIntegral k k']

/-- **The order of a norm** at a place `P` of `F / k` whose local model `𝒪'_P` is a finite
`𝒪_P`-module: for `x ∈ F'`, `ord_P (N_{F'/F} x) = ∑_{P' ∣ P} f(P' ∣ P) · ord_{P'} x`.

The finite set `s` is the fibre of `TauCeti.Place.restrict` over `P`. The finiteness hypothesis
holds for a separable `F' / F` (`TauCeti.Place.moduleFinite_integralClosure`) and for any finite
extension of an algebraic function field; that case is
`TauCeti.Place.ord_norm_of_isFunctionField`. -/
theorem ord_norm_of_moduleFinite (P : Place k F)
    [Module.Finite P.integers (integralClosure P.integers F')]
    {s : Finset (Place k' F')} (hs : ∀ P' : Place k' F', P' ∈ s ↔ P'.restrict k F = P)
    (x : F') : P.ord (Algebra.norm F x) = ∑ P' ∈ s, (relativeDegree k F P' : ℤ) * P'.ord x := by
  obtain rfl | hx := eq_or_ne x 0
  · simp
  have : IsDedekindDomain (integralClosure P.integers F') :=
    TauCeti.integralClosure.isDedekindDomain P.integers F F'
  let _ := algebraConstantsIntegralClosure (k' := k') (F' := F') P
  have := isScalarTower_constants_integralClosure (k' := k') (F' := F') P
  have hkey := valuation_norm_inv P hs hx
  simp only [valuation_eq_exp_neg_ord _ (Algebra.norm_ne_zero_iff.mpr hx),
    valuation_eq_exp_neg_ord _ hx, ← WithZero.exp_neg, neg_neg, ← WithZero.exp_nsmul] at hkey
  -- `WithZero.exp` turns sums into products: it is `ofAdd` followed by the coercion.
  have hexp : ∏ P' ∈ s, WithZero.exp (relativeDegree k F P' • P'.ord x) =
      WithZero.exp (∑ P' ∈ s, relativeDegree k F P' • P'.ord x) := by
    simp only [WithZero.exp_eq_coe_ofAdd, ofAdd_sum]
    exact (map_prod (WithZero.coeMonoidHom (α := Multiplicative ℤ)) _ s).symm
  rw [← WithZero.exp_inj, hkey, hexp]
  simp

/-- **The order of a norm** at a place of an algebraic function field: if `F / k` is an algebraic
function field, `F' / F` is finite, `P` is a place of `F / k` and `x ∈ F'`, then
`ord_P (N_{F'/F} x) = ∑_{P' ∣ P} f(P' ∣ P) · ord_{P'} x`, with no separability hypothesis.

The finite set `s` is the fibre of `TauCeti.Place.restrict` over `P`. -/
theorem ord_norm_of_isFunctionField (hF : IsFunctionField k F) (P : Place k F)
    {s : Finset (Place k' F')} (hs : ∀ P' : Place k' F', P' ∈ s ↔ P'.restrict k F = P) (x : F') :
    P.ord (Algebra.norm F x) = ∑ P' ∈ s, (relativeDegree k F P' : ℤ) * P'.ord x := by
  have := moduleFinite_integralClosure_of_isFunctionField F' P hF
  exact ord_norm_of_moduleFinite P hs x

end Place

end TauCeti
