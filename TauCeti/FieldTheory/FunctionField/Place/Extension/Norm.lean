/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.AffineModel.Extension
public import TauCeti.FieldTheory.FunctionField.Place.Extension.Fundamental
public import Mathlib.RingTheory.OrderOfVanishing.Noetherian
import TauCeti.FieldTheory.FunctionField.AffineModel.IntegralClosure
import TauCeti.RingTheory.DedekindDomain.IntegralClosure
import TauCeti.RingTheory.IntegralClosure.MvPolynomial
import TauCeti.RingTheory.IntegralClosure.Transfer
import TauCeti.RingTheory.Length.Norm

/-!
# The order of a norm at a place

Let `F' / k'` be a finite extension of the field extension `F / k`, with `k'` integral over `k`,
and let `P` be a place of `F / k`. For `x ∈ F'` this file proves the **order-of-a-norm formula**

`ord_P (N_{F'/F} x) = ∑_{P' ∣ P} f(P' ∣ P) · ord_{P'} x`,

the sum running over the finitely many places `P'` of `F' / k'` above `P`, weighted by their
relative degrees. It is the coefficient identity behind the norm of divisors,
`N(div x) = div (N_{F'/F} x)` (`TauCeti.Divisor.norm_principal`).

The proof reads Fulton's order-of-a-norm formula `TauCeti.ordFrac_norm_eq_finprod` on the local
model `𝒪_P ⊆ 𝒪'_P`, where `𝒪'_P` is the integral closure of `𝒪_P` in `F'`. That formula needs
`𝒪'_P` to be a finite `𝒪_P`-module. For a separable extension this is Mathlib's
`IsIntegralClosure.finite`. For an algebraic function field `F / k` it holds for every finite
extension (`TauCeti.Place.moduleFinite_integralClosure_of_isFunctionField`): the integral closure
`S` of the affine model `R = R_t` of a uniformizer `t` at `P` is a finite `R`-module without
separability, `𝒪_P` is the localization of `R` at the centre of `P`, and clearing denominators
places `𝒪'_P` inside the `𝒪_P`-span of finitely many generators of `S`. The maximal ideals of the
Dedekind domain `𝒪'_P` are the centres of the places above `P`, their local rings are the
valuation rings of those places, and the `𝒪_P`-length of each residue ring is the relative degree,
so Fulton's formula is the displayed one.

## Main results

* `TauCeti.Place.ordFrac_integers`: Mathlib's order of vanishing `Ring.ordFrac` along the valuation
  ring of a place is the inverse of the valuation of the place.
* `TauCeti.Place.moduleFinite_integralClosure_of_isFunctionField`: for an algebraic function field
  the local model `𝒪'_P` is a finite `𝒪_P`-module, with no separability hypothesis.
* `TauCeti.Place.ord_norm_of_isSeparable` and `TauCeti.Place.ord_norm_of_isFunctionField`: the
  order-of-a-norm formula, for a separable extension and for any finite extension of an algebraic
  function field.

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

omit [Field k'] [Field F'] [Algebra k k'] [Algebra k' F'] [Algebra F F'] [Algebra k F']
  [IsScalarTower k k' F'] [IsScalarTower k F F'] in
/-- The centre of a place on its own valuation ring is the maximal ideal. -/
private theorem center_integers (P : Place k F)
    (hR : ∀ r : P.integers, algebraMap P.integers F r ∈ P.integers) :
    P.center hR = IsDiscreteValuationRing.maximalIdeal P.integers := by
  ext r
  rw [mem_center_asIdeal]
  exact P.mem_maximalIdeal_iff_valuation_lt_one.symm

omit [Field k'] [Field F'] [Algebra k k'] [Algebra k' F'] [Algebra F F'] [Algebra k F']
  [IsScalarTower k k' F'] [IsScalarTower k F F'] in
/-- The order of vanishing along the valuation ring of a place, Mathlib's `Ring.ordFrac`, is the
inverse of the valuation of the place. -/
theorem ordFrac_integers (P : Place k F) (x : F) :
    Ring.ordFrac P.integers x = (P.valuation x)⁻¹ := by
  have hR : ∀ r : P.integers, algebraMap P.integers F r ∈ P.integers := fun r ↦ r.2
  rw [Ring.ordFrac_eq_valuation_inv, ← center_integers P hR, valuation_center]

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

omit [Algebra k F'] [IsScalarTower k F F'] [FiniteDimensional F F']
  [Module.Finite P.integers (integralClosure P.integers F')]
  [IsDedekindDomain (integralClosure P.integers F')] [Algebra k' (integralClosure P.integers F')]
  [IsScalarTower k' (integralClosure P.integers F') F'] in
/-- Every maximal ideal of the local model lies over the maximal ideal of `𝒪_P`. -/
private theorem liesOver_maximalIdeal (m : Ideal (integralClosure P.integers F')) [m.IsMaximal] :
    m.LiesOver (IsLocalRing.maximalIdeal P.integers) :=
  ⟨(IsLocalRing.eq_maximalIdeal
    (Ideal.isMaximal_under_of_isIntegral_of_isMaximal (R := P.integers) m)).symm⟩

/-- The `𝒪_P`-length of the residue ring of a height one prime `𝔓` of the local model is the
relative degree of the place of `𝔓`. -/
private theorem length_quotient_toNat (𝔓 : HeightOneSpectrum (integralClosure P.integers F')) :
    (Module.length P.integers (integralClosure P.integers F' ⧸ 𝔓.asIdeal)).toNat =
      relativeDegree k F (ofPrime k' F' 𝔓) := by
  have := liesOver_maximalIdeal P 𝔓.asIdeal
  let _ : Field (P.integers ⧸ IsLocalRing.maximalIdeal P.integers) := Ideal.Quotient.field _
  have : Module.Finite (P.integers ⧸ IsLocalRing.maximalIdeal P.integers)
      (integralClosure P.integers F' ⧸ 𝔓.asIdeal) :=
    Module.Finite.of_restrictScalars_finite P.integers _ _
  rw [relativeDegree_ofPrime (k := k) (F := F) (R := P.integers),
    Ideal.inertiaDeg_eq_of_isMaximal (IsLocalRing.maximalIdeal P.integers) 𝔓.asIdeal,
    Module.length_eq_of_surjective (R := P.integers ⧸ IsLocalRing.maximalIdeal P.integers)
      Ideal.Quotient.mk_surjective, Module.length_eq_finrank, ENat.toNat_natCast]

/-- The places of the height one primes of the local model are exactly the places above `P`. -/
private theorem exists_ofPrime_eq_iff (P' : Place k' F') :
    (∃ 𝔓 : HeightOneSpectrum (integralClosure P.integers F'), ofPrime k' F' 𝔓 = P') ↔
      P'.restrict k F = P := by
  have hR : ∀ r : P.integers, algebraMap P.integers F r ∈ P.integers := fun r ↦ r.2
  have hmax : (P.center hR).asIdeal = IsLocalRing.maximalIdeal P.integers := by
    rw [center_integers P hR]
    rfl
  constructor
  · rintro ⟨𝔓, rfl⟩
    have : 𝔓.asIdeal.LiesOver (P.center hR).asIdeal := hmax ▸ liesOver_maximalIdeal P 𝔓.asIdeal
    rw [restrict_ofPrime k F (P.center hR) 𝔓, ofPrime_center]
  · intro h
    have hS := algebraMap_mem_integers_of_restrict_eq_ofPrime (S := integralClosure P.integers F')
      k F (P.center hR) (h.trans (ofPrime_center k F P hR).symm)
    exact ⟨P'.center hS, ofPrime_center k' F' P' hS⟩

/-- **The order of a norm on the local model**, in multiplicative form. -/
private theorem valuation_norm_inv {s : Finset (Place k' F')}
    (hs : ∀ P' : Place k' F', P' ∈ s ↔ P'.restrict k F = P) {x : F'} (hx : x ≠ 0) :
    (P.valuation (Algebra.norm F x))⁻¹ =
      ∏ P' ∈ s, ((P'.valuation x)⁻¹) ^ relativeDegree k F P' := by
  have hne (m : MaximalSpectrum (integralClosure P.integers F')) : m.asIdeal ≠ ⊥ :=
    have := liesOver_maximalIdeal P m.asIdeal
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
  -- Reindex the maximal ideals of the local model by their places, the places above `P`.
  have hinj : Function.Injective fun m ↦ ofPrime k' F' (toH m) := fun m m' h ↦
    MaximalSpectrum.ext (by rw [← htoH m, ← htoH m', ofPrime_injective k' F' h])
  have hrange : Set.range (fun m ↦ ofPrime k' F' (toH m)) = (s : Set (Place k' F')) := by
    ext P'
    rw [Finset.mem_coe, hs, ← exists_ofPrime_eq_iff P]
    refine ⟨fun ⟨m, hm⟩ ↦ ⟨toH m, hm⟩, fun ⟨𝔓, h𝔓⟩ ↦ ⟨⟨𝔓.asIdeal, 𝔓.isMaximal⟩, ?_⟩⟩
    simpa only [show toH ⟨𝔓.asIdeal, 𝔓.isMaximal⟩ = 𝔓 from HeightOneSpectrum.ext (htoH _)]
  rw [← ordFrac_integers, key, ← finprod_mem_coe_finset, ← hrange, finprod_mem_range hinj]
  refine finprod_congr fun m ↦ ?_
  rw [ordFrac_integers, ← length_quotient_toNat P (toH m), htoH]

end LocalModel

variable [Algebra.IsIntegral k k']

omit [FiniteDimensional F F'] in
/-- The local model `𝒪'_P` is a `k'`-algebra: the constants `k'` are integral over `k ⊆ 𝒪_P`. -/
private theorem algebraMap_mem_integralClosure (P : Place k F) (c : k') :
    algebraMap k' F' c ∈ integralClosure P.integers F' :=
  have : IsScalarTower k P.integers F' := .of_algebraMap_eq fun c ↦ by
    rw [IsScalarTower.algebraMap_apply P.integers F F',
      ← IsScalarTower.algebraMap_apply k P.integers F, ← IsScalarTower.algebraMap_apply k F F']
  (IsIntegral.algebraMap (Algebra.IsIntegral.isIntegral (R := k) c)).tower_top

/-- The additive form of `valuation_norm_inv`, for a finite local model. -/
private theorem ord_norm_eq_sum_of_moduleFinite (P : Place k F)
    [Module.Finite P.integers (integralClosure P.integers F')]
    {s : Finset (Place k' F')} (hs : ∀ P' : Place k' F', P' ∈ s ↔ P'.restrict k F = P)
    (x : F') : P.ord (Algebra.norm F x) = ∑ P' ∈ s, (relativeDegree k F P' : ℤ) * P'.ord x := by
  obtain rfl | hx := eq_or_ne x 0
  · simp
  have : IsDedekindDomain (integralClosure P.integers F') :=
    TauCeti.integralClosure.isDedekindDomain P.integers F F'
  let _ : Algebra k' (integralClosure P.integers F') :=
    ((algebraMap k' F').codRestrict _ (algebraMap_mem_integralClosure P)).toAlgebra
  have : IsScalarTower k' (integralClosure P.integers F') F' := .of_algebraMap_eq fun _ ↦ rfl
  have hkey := valuation_norm_inv P hs hx
  simp only [valuation_eq_exp_neg_ord _ (Algebra.norm_ne_zero_iff.mpr hx),
    valuation_eq_exp_neg_ord _ hx, ← WithZero.exp_neg, neg_neg, ← WithZero.exp_nsmul] at hkey
  have hexp (t : Finset (Place k' F')) (g : Place k' F' → ℤ) :
      ∏ P' ∈ t, WithZero.exp (g P') = WithZero.exp (∑ P' ∈ t, g P') := by
    induction t using Finset.cons_induction with
    | empty => simp
    | cons a t ha ih => rw [Finset.prod_cons, Finset.sum_cons, ih, WithZero.exp_add]
  rw [← WithZero.exp_inj, hkey, hexp]
  simp

section AffineModel

/-! ### Finiteness of the local model

If `P` is finite on an affine model `R` of `F / k` whose integral closure `S` in `F'` is a finite
`R`-module, then `𝒪_P` is the localization of `R` at the centre of `P`, and clearing denominators
places `𝒪'_P` inside the `𝒪_P`-span of finitely many generators of `S`. -/

variable (P : Place k F) {R : Type*} [CommRing R] [IsDedekindDomain R] [Algebra R F]
  [IsFractionRing R F] [Algebra R F'] [IsScalarTower R F F']
  (hR : ∀ r : R, algebraMap R F r ∈ P.integers)

include hR

omit [Algebra k F'] [IsScalarTower k F F'] [FiniteDimensional F F'] [Algebra.IsIntegral k k'] in
/-- A function integral over `𝒪_P` becomes integral over `R` after multiplication by an element of
`R` outside the centre of `P`. -/
private theorem exists_mul_isIntegral {y : F'} (hy : IsIntegral P.integers y) :
    ∃ c : R, c ∉ (P.center hR).asIdeal ∧ IsIntegral R (algebraMap R F' c * y) := by
  -- `𝒪_P` is Mathlib's localization of `R` at the centre of `P`.
  let V := HeightOneSpectrum.valuationSubringAtPrime F (P.center hR)
  have hV : V = P.integers := valuationSubringAtPrime_eq_integers P hR
  let _ : Algebra V F' := ((algebraMap F F').comp (algebraMap V F)).toAlgebra
  have : IsScalarTower R V F' := .of_algebraMap_eq fun r ↦ by
    rw [IsScalarTower.algebraMap_apply R F F', IsScalarTower.algebraMap_apply R V F]
    rfl
  have hyV : IsIntegral V y :=
    IsIntegral.map_of_comp_eq (ValuationSubring.inclusion _ _ hV.ge) (RingHom.id F')
      (RingHom.ext fun _ ↦ rfl) hy
  obtain ⟨⟨c, hc⟩, hcy⟩ := hyV.exists_multiple_integral_of_isLocalization
    (P.center hR).asIdeal.primeCompl y
  exact ⟨c, hc, by simpa [Submonoid.smul_def, Algebra.smul_def] using hcy⟩

omit [Algebra k F'] [IsScalarTower k F F'] [FiniteDimensional F F'] [Algebra.IsIntegral k k'] in
/-- `𝒪'_P` lies in the `𝒪_P`-span of any set spanning `S` over `R`. -/
private theorem toSubmodule_integralClosure_le_span {T : Set (integralClosure R F')}
    (hT : Submodule.span R T = ⊤) :
    Subalgebra.toSubmodule ((integralClosure P.integers F').restrictScalars P.integers) ≤
      Submodule.span P.integers ((↑) '' T) := by
  -- The `R`-span of `T` in `F'` lies in its `𝒪_P`-span, since `R` maps into `𝒪_P`.
  have hRN : ∀ w ∈ Submodule.span R ((↑) '' T : Set F'), w ∈ Submodule.span P.integers
      ((↑) '' T) := by
    intro w hw
    induction hw using Submodule.span_induction with
    | mem w hw => exact Submodule.subset_span hw
    | zero => exact zero_mem _
    | add _ _ _ _ h₁ h₂ => exact add_mem h₁ h₂
    | smul r w _ h =>
      have : r • w = (⟨algebraMap R F r, hR r⟩ : P.integers) • w := by
        rw [Algebra.smul_def, Algebra.smul_def, IsScalarTower.algebraMap_apply R F F',
          IsScalarTower.algebraMap_apply P.integers F F']
        rfl
      rw [this]
      exact Submodule.smul_mem _ _ h
  intro y hy
  obtain ⟨c, hc, hcy⟩ := exists_mul_isIntegral P hR hy
  -- `c` is a unit at `P`, so `y = c⁻¹ · (c y)` with `c y` in the `R`-span of `T`.
  have hc0 : c ≠ 0 := fun h ↦ hc (h ▸ zero_mem _)
  have hcF : algebraMap R F c ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective R F)).mpr hc0
  have hord : P.ord (algebraMap R F c) = 0 := by
    have := (P.mem_integers_iff_ord_nonneg).mp (hR c)
    have := (P.mem_center_asIdeal_iff_ord_pos hR hc0).not.mp hc
    omega
  have hinv : (algebraMap R F c)⁻¹ ∈ P.integers := by
    rw [P.mem_integers_iff_ord_nonneg, ord_inv, hord, neg_zero]
  have hz : algebraMap R F' c * y ∈ Submodule.span R ((↑) '' T : Set F') := by
    have h₁ : (⟨_, hcy⟩ : integralClosure R F') ∈ Submodule.span R T := hT ▸ Submodule.mem_top
    have h₂ := Submodule.mem_map_of_mem (f := (integralClosure R F').val.toLinearMap) h₁
    rw [← Submodule.span_image] at h₂
    exact h₂
  have hy' : y = (⟨(algebraMap R F c)⁻¹, hinv⟩ : P.integers) • (algebraMap R F' c * y) := by
    rw [Algebra.smul_def, IsScalarTower.algebraMap_apply P.integers F F',
      IsScalarTower.algebraMap_apply R F F', ← mul_assoc, ← map_mul,
      ValuationSubring.algebraMap_apply, inv_mul_cancel₀ hcF, map_one, one_mul]
  rw [hy']
  exact Submodule.smul_mem _ _ (hRN _ hz)

omit [Algebra k F'] [IsScalarTower k F F'] [FiniteDimensional F F'] [Algebra.IsIntegral k k'] in
/-- If the integral closure of an affine model `R` on which `P` is finite is a finite
`R`-module, then the local model `𝒪'_P` is a finite `𝒪_P`-module. -/
private theorem moduleFinite_integralClosure_of_affineModel
    [Module.Finite R (integralClosure R F')] :
    Module.Finite P.integers (integralClosure P.integers F') := by
  obtain ⟨T, hT⟩ := Module.Finite.fg_top (R := R) (M := integralClosure R F')
  have : IsNoetherian P.integers (Submodule.span P.integers
      (Subtype.val '' (T : Set (integralClosure R F')))) :=
    isNoetherian_span_of_finite _ (T.finite_toSet.image _)
  have := isNoetherian_of_le (toSubmodule_integralClosure_le_span P hR hT)
  exact Module.IsNoetherian.finite P.integers
    (Subalgebra.toSubmodule ((integralClosure P.integers F').restrictScalars P.integers))

end AffineModel

omit [Algebra k F'] [IsScalarTower k F F'] in
open _root_.IntermediateField _root_.IntermediateField.algebraAdjoinAdjoin in
/-- **The local model of a finite extension of an algebraic function field is finite**: for a
place `P` of `F / k` and a finite extension `F' / F`, the integral closure `𝒪'_P` of `𝒪_P` in `F'`
is a finite `𝒪_P`-module, with no separability hypothesis. -/
theorem moduleFinite_integralClosure_of_isFunctionField (hF : IsFunctionField k F)
    (P : Place k F) : Module.Finite P.integers (integralClosure P.integers F') := by
  -- A uniformizer `t` at `P` is transcendental over `k` and has no pole at `P`.
  obtain ⟨t, ht⟩ := P.exists_isUniformizer
  have htP : P.ord t = 1 := P.isUniformizer_iff_ord_eq_one.mp ht
  have htr : Transcendental k t := P.transcendental_of_ord_ne_zero (by omega)
  have hti : t ∈ P.integers := P.mem_integers_iff_ord_nonneg.mpr (by omega)
  have : FiniteDimensional k⟮t⟯ F := hF.finiteDimensional_adjoin htr
  have : FiniteDimensional k⟮t⟯ F' := Module.Finite.trans F F'
  -- The integral closure `R` of `k[t]` in `F` is an affine model on which `P` is finite, and its
  -- integral closure in `F'` is a finite `R`-module without separability.
  let R := integralClosure (Algebra.adjoin k {t}) F
  have : IsDedekindDomain R := isDedekindDomain_integralClosure_adjoin hF t
  have : IsFractionRing R F := isFractionRing_integralClosure_adjoin hF htr
  have : Module.Finite R (integralClosure R F') :=
    IsIntegralClosure.finite_integralClosure_integralClosure_adjoin k t F'
  exact moduleFinite_integralClosure_of_affineModel P (R := R) fun r ↦ P.mem_integers_iff.mpr
    (P.forall_algebraMap_mem_integers_integralClosure_adjoin_iff.mpr hti r r.2)

/-- **The order of a norm**, for a separable extension: if `F' / F` is finite and separable, `P` is
a place of `F / k` and `x ∈ F'`, then `ord_P (N_{F'/F} x) = ∑_{P' ∣ P} f(P' ∣ P) · ord_{P'} x`.

The finite set `s` is the fibre of `TauCeti.Place.restrict` over `P`. When `F / k` is an algebraic
function field no separability is needed; that is `TauCeti.Place.ord_norm_of_isFunctionField`. -/
theorem ord_norm_of_isSeparable [Algebra.IsSeparable F F'] (P : Place k F)
    {s : Finset (Place k' F')} (hs : ∀ P' : Place k' F', P' ∈ s ↔ P'.restrict k F = P) (x : F') :
    P.ord (Algebra.norm F x) = ∑ P' ∈ s, (relativeDegree k F P' : ℤ) * P'.ord x := by
  exact ord_norm_eq_sum_of_moduleFinite P hs x

/-- **The order of a norm** at a place of an algebraic function field: if `F / k` is an algebraic
function field, `F' / F` is finite, `P` is a place of `F / k` and `x ∈ F'`, then
`ord_P (N_{F'/F} x) = ∑_{P' ∣ P} f(P' ∣ P) · ord_{P'} x`, with no separability hypothesis.

The finite set `s` is the fibre of `TauCeti.Place.restrict` over `P`. -/
theorem ord_norm_of_isFunctionField (hF : IsFunctionField k F) (P : Place k F)
    {s : Finset (Place k' F')} (hs : ∀ P' : Place k' F', P' ∈ s ↔ P'.restrict k F = P) (x : F') :
    P.ord (Algebra.norm F x) = ∑ P' ∈ s, (relativeDegree k F P' : ℤ) * P'.ord x := by
  have := moduleFinite_integralClosure_of_isFunctionField (F' := F') hF P
  exact ord_norm_eq_sum_of_moduleFinite P hs x

end Place

end TauCeti
