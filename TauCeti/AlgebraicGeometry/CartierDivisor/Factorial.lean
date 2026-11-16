/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.CartierDivisor.ClassGroup
public import TauCeti.AlgebraicGeometry.CartierDivisor.IdealSheaf
public import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.Factorial
public import TauCeti.AlgebraicGeometry.Scheme.Normal
public import TauCeti.AlgebraicGeometry.Scheme.Regular
public import TauCeti.AlgebraicGeometry.WeilDivisor.Scheme.Cartier.Inverse
import TauCeti.AlgebraicGeometry.IdealSheaf.Affine
import TauCeti.AlgebraicGeometry.Scheme.StalkSpecializes
import TauCeti.RingTheory.Ideal.Quotient.Colon
import TauCeti.RingTheory.SerreCondition.Normal

/-!
# Algebraic Hartogs' principle and the Weil–Cartier equivalence on locally factorial schemes

Let `X` be a locally Noetherian normal integral scheme. Each local ring `𝒪_{X,x}` is a Noetherian
integrally closed domain, hence satisfies Serre's condition `(S_2)`
(`TauCeti.satisfiesSerreS_two_of_forall_isIntegrallyClosed`): for any nonzerodivisor `b ∈ 𝒪_{X,x}`,
every associated prime of `𝒪_{X,x} ⧸ (b)` has height one
(`Module.SatisfiesSerreS.height_eq_one_of_isAssociatedPrime_quotient_span_singleton`), so it comes
from a codimension-one generization `η` of `x` whose local ring `𝒪_{X,η}` is a discrete valuation
ring (`IsNormalScheme.isDiscreteValuationRing_stalk`). Consequently, a rational function on `X`
whose order of vanishing is nonnegative at every codimension-one point of a nonempty open `U` is
regular on `U` (*algebraic Hartogs' principle*,
`Scheme.exists_germToFunctionField_eq_of_ord_nonneg_of_isNormalScheme`), and a rational unit with
zero order at every codimension-one point of `U` is a regular unit on `U`
(`Scheme.exists_unit_germToFunctionField_eq_of_ord_eq_zero_of_isNormalScheme`). On a Noetherian
normal integral scheme, the Cartier-to-Weil homomorphism `D ↦ D.toWeilDivisor` is therefore
injective (`Scheme.CartierDivisor.toWeilDivisor_injective`).

Conversely, on any integral scheme `X`, an effective Cartier ideal sheaf `I`
(`I.IsEffectiveCartier`) determines an effective Cartier divisor `hI.toCartierDivisor` by gluing
its local nonzerodivisor generators in the Cartier-divisor sheaf `𝒦_X^× / 𝒪_X^×`. Its
closed-subscheme ideal sheaf is `I` itself (`hI.idealSheaf_toCartierDivisor`), and its line-bundle
class `[𝒪_X(D)]` is the inverse of the class `[I]` of the invertible ideal sheaf
(`hI.toLineBundleClass_toCartierDivisor`).

When `X` is a Noetherian integral scheme whose local rings are unique factorization domains (for
instance a regular scheme of dimension at most two, such as a regular model of a curve over a
discrete valuation ring), the closure `closure {η}` of each codimension-one point `η` is an
effective Cartier divisor
(`Scheme.IdealSheafData.isEffectiveCartier_vanishingIdeal_closure_singleton`) whose Cartier divisor
has Weil divisor `WeilDivisor.ofPoint η`. Extending `ℤ`-linearly gives an inverse to
`toWeilDivisorHom`, identifying Weil divisors with Cartier divisors
(`SchemeWeilDivisor.equivCartierDivisorOfUniqueFactorizationMonoid`) and the Weil divisor class
group `Cl(X)` with the Picard group `Additive (LineBundleClass X)`
(`SchemeWeilDivisor.classGroupAddEquivLineBundleClassOfUniqueFactorizationMonoid`).

## Main declarations

* `TauCeti.AlgebraicGeometry.Scheme.exists_comap_stalkSpecializes_maximalIdeal_eq`: every prime of
  `𝒪_{X,y}` on a locally Noetherian scheme comes from a generization `x ⤳ y` of the same height;
* `TauCeti.AlgebraicGeometry.Scheme.exists_algebraMap_stalk_eq_of_forall_specializes_ord_nonneg` and
`TauCeti.AlgebraicGeometry.Scheme.exists_germToFunctionField_eq_of_ord_nonneg_of_isNormalScheme`:
  algebraic Hartogs' principle on locally Noetherian normal integral schemes;
* `TauCeti.AlgebraicGeometry.Scheme.CartierDivisor.toWeilDivisor_injective`: injectivity of
  `CartierDivisor X →+ SchemeWeilDivisor X` on Noetherian normal integral schemes;
* `AlgebraicGeometry.Scheme.IdealSheafData.IsEffectiveCartier.toCartierDivisor`: the Cartier
  divisor of an effective Cartier ideal sheaf on an integral scheme, with line-bundle class `[I]⁻¹`;
* `TauCeti.AlgebraicGeometry.SchemeWeilDivisor.equivCartierDivisorOfUniqueFactorizationMonoid`:
  the Weil–Cartier additive equivalence on Noetherian locally factorial integral schemes, together
  with the induced `Cl(X) ≃+ Pic(X)` equivalence.

## References

* [Stacks Project, Tag 031T](https://stacks.math.columbia.edu/tag/031T) (algebraic Hartogs'
  principle on normal Noetherian domains),
  [Tag 01WQ](https://stacks.math.columbia.edu/tag/01WQ) (effective Cartier divisors and invertible
  ideal sheaves), and [Tag 0BE9](https://stacks.math.columbia.edu/tag/0BE9) (Weil and Cartier
  divisors on locally factorial schemes).
* R. Hartshorne, *Algebraic Geometry*, Chapter II, Proposition 6.3A, Proposition 6.11, and
  Corollary 6.16.
-/

public section

open AlgebraicGeometry CategoryTheory Opposite Order TopologicalSpace
open scoped nonZeroDivisors

namespace TauCeti

namespace AlgebraicGeometry

universe u

noncomputable section

namespace Scheme

variable {X : Scheme.{u}}

/-- **Primes of a local ring and generizations.** On a locally Noetherian scheme, every prime ideal
`P` of the local ring `𝒪_{X,y}` is the preimage under `stalkSpecializes` of the maximal ideal of
`𝒪_{X,x}` for some generization `x ⤳ y` with `coheight x = P.height`. -/
theorem exists_comap_stalkSpecializes_maximalIdeal_eq [IsLocallyNoetherian X] {y : X}
    (P : Ideal (X.presheaf.stalk y)) [hP : P.IsPrime] :
    ∃ x : X, Order.coheight x = P.height ∧ ∃ h : x ⤳ y,
      (IsLocalRing.maximalIdeal (X.presheaf.stalk x)).comap
        (X.presheaf.stalkSpecializes h).hom = P := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hyU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ y) isOpen_univ
  have : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  replace hU : IsAffineOpen U := hU
  let := X.presheaf.algebra_section_stalk ⟨y, hyU⟩
  have := hU.isLocalization_stalk ⟨y, hyU⟩
  set Q := hU.primeIdealOf ⟨y, hyU⟩
  let q : Spec Γ(X, U) := ⟨P.comap (algebraMap Γ(X, U) (X.presheaf.stalk y)), inferInstance⟩
  have hqQ : q.asIdeal ≤ Q.asIdeal := by
    rw [← IsLocalization.AtPrime.under_maximalIdeal (X.presheaf.stalk y) Q.asIdeal]
    exact Ideal.comap_mono (IsLocalRing.le_maximalIdeal hP.ne_top)
  have hxy : hU.fromSpec q ⤳ y :=
    (((PrimeSpectrum.le_iff_specializes q Q).mp hqQ).map hU.fromSpec.continuous).trans
      (specializes_of_eq (hU.fromSpec_primeIdealOf ⟨y, hyU⟩))
  have hprime : hU.primeIdealOf ⟨_, hxy.mem_open U.isOpen hyU⟩ = q :=
    hU.fromSpec.isOpenEmbedding.injective (hU.fromSpec_primeIdealOf _)
  have hdisj : Disjoint (Q.asIdeal.primeCompl : Set Γ(X, U)) q.asIdeal :=
    Set.disjoint_left.mpr fun a ha haq ↦ ha (hqQ haq)
  have hmap : q.asIdeal.map (algebraMap Γ(X, U) (X.presheaf.stalk y)) = P :=
    IsLocalization.map_under Q.asIdeal.primeCompl _ P
  have hcoh : Order.coheight (hU.fromSpec q) = P.height := by
    rw [coheight_eq_of_isOpenImmersion hU.fromSpec, ← idealHeight_eq_coheight,
      ← IsLocalization.height_map_of_disjoint (S := X.presheaf.stalk y) Q.asIdeal.primeCompl
        q.asIdeal hdisj, hmap]
  refine ⟨_, hcoh, hxy, ?_⟩
  rw [← IsLocalization.map_under Q.asIdeal.primeCompl (X.presheaf.stalk y)
      ((IsLocalRing.maximalIdeal _).comap (X.presheaf.stalkSpecializes hxy).hom), ← hmap]
  congr 1
  exact (comap_germ_comap_stalkSpecializes_maximalIdeal hU hyU hxy).trans (congrArg _ hprime)

section Hartogs

variable [IsIntegral X] [IsLocallyNoetherian X] [IsNormalScheme X]

/-- **Local algebraic Hartogs' principle.** On a locally Noetherian normal integral scheme, a
rational function whose order is nonnegative at every codimension-one generization of `x` belongs
to the local ring `𝒪_{X,x}`. Stacks, Lemma 10.157.6 (031T); Hartshorne, Proposition II.6.3A. -/
@[stacks 031T]
theorem exists_algebraMap_stalk_eq_of_forall_specializes_ord_nonneg {x : X} {f : X.functionField}
    (hf : ∀ η : CodimensionOnePoint X, (η : X) ⤳ x → 0 ≤ X.ord f η) :
    ∃ g : X.presheaf.stalk x, algebraMap (X.presheaf.stalk x) X.functionField g = f := by
  set R := X.presheaf.stalk x
  have hS : Module.SatisfiesSerreS 2 R R :=
    TauCeti.satisfiesSerreS_two_of_forall_isIntegrallyClosed fun p _ ↦
      ⟨IsLocalization.isDomain_localization p.primeCompl_le_nonZeroDivisors,
        isIntegrallyClosed_of_isLocalization _ p.primeCompl p.primeCompl_le_nonZeroDivisors⟩
  obtain ⟨⟨a, ⟨b, hb⟩⟩, hf'⟩ := IsLocalization.mk'_surjective R⁰ f
  dsimp only at hf'
  subst hf'
  by_cases hab : a ∈ Ideal.span {b}
  · obtain ⟨g, rfl⟩ := Ideal.mem_span_singleton'.mp hab
    exact ⟨g, IsLocalization.eq_mk'_iff_mul_eq.mpr (by rw [← map_mul, mul_comm])⟩
  exfalso
  -- An associated prime `P` of `R ⧸ (b)` containing `((b) : a)` has height one by `(S_2)`.
  obtain ⟨P, hPass, hle⟩ := exists_le_isAssociatedPrime_of_isNoetherianRing R
    (Ideal.Quotient.mk (Ideal.span {b}) a) (by rwa [Ne, Ideal.Quotient.eq_zero_iff_mem])
  have := hPass.isPrime
  have hP1 := hS.height_eq_one_of_isAssociatedPrime_quotient_span_singleton hb hPass
  obtain ⟨η, hη, hηx, hcomap⟩ := exists_comap_stalkSpecializes_maximalIdeal_eq P
  rw [hP1] at hη
  have : IsDiscreteValuationRing (X.presheaf.stalk η) :=
    IsNormalScheme.isDiscreteValuationRing_stalk η hη
  obtain ⟨y, hy⟩ := exists_algebraMap_stalk_eq_of_ord_nonneg (hf ⟨η, hη⟩ hηx)
  -- Then `a ∈ (b) 𝒪_{X,η}` inside the localization `𝒪_{X,η} = R_P`, contradicting `s ∉ P`.
  let := (X.presheaf.stalkSpecializes hηx).hom.toAlgebra
  have : IsLocalization.AtPrime (X.presheaf.stalk η) P :=
    hcomap ▸ isLocalization_stalkSpecializes hηx
  have hmul : y * (X.presheaf.stalkSpecializes hηx).hom b =
      (X.presheaf.stalkSpecializes hηx).hom a :=
    IsFractionRing.injective (X.presheaf.stalk η) X.functionField <| by
      rw [map_mul, hy, algebraMap_stalkSpecializes hηx, algebraMap_stalkSpecializes hηx,
        IsLocalization.mk'_spec]
  have hmem : algebraMap R (X.presheaf.stalk η) a ∈
      (Ideal.span {b}).map (algebraMap R (X.presheaf.stalk η)) := by
    rw [Ideal.map_span, Set.image_singleton]
    exact Ideal.mem_span_singleton'.mpr ⟨y, hmul⟩
  obtain ⟨s, hs, hsa⟩ :=
    (IsLocalization.algebraMap_mem_map_algebraMap_iff P.primeCompl (X.presheaf.stalk η) _ _).mp hmem
  exact hs (hle (TauCeti.Ideal.Quotient.mem_colon_singleton_mk.mpr hsa))

/-- **Algebraic Hartogs' principle.** On a locally Noetherian normal integral scheme, a rational
function whose order of vanishing is nonnegative at every codimension-one point of a nonempty open
subset `U` is regular on `U`. -/
theorem exists_germToFunctionField_eq_of_ord_nonneg_of_isNormalScheme {U : X.Opens} [Nonempty U]
    {f : X.functionField} (hf : ∀ y : CodimensionOnePoint X, (y : X) ∈ U → 0 ≤ X.ord f y) :
    ∃ a : Γ(X, U), X.germToFunctionField U a = f :=
  exists_germToFunctionField_eq_of_forall_mem_range fun _ hx ↦
    exists_algebraMap_stalk_eq_of_forall_specializes_ord_nonneg fun η hηx ↦
      hf η (hηx.mem_open U.isOpen hx)

/-- On a locally Noetherian normal integral scheme, a nonzero rational function whose order of
vanishing is zero at every codimension-one point of a nonempty open subset `U` is a regular unit
on `U`. -/
theorem exists_unit_germToFunctionField_eq_of_ord_eq_zero_of_isNormalScheme {U : X.Opens}
    [Nonempty U] {f : X.functionFieldˣ}
    (hf : ∀ y : CodimensionOnePoint X, (y : X) ∈ U → X.ord (f : X.functionField) y = 0) :
    ∃ a : Γ(X, U)ˣ, X.germToFunctionField U (a : Γ(X, U)) = (f : X.functionField) := by
  obtain ⟨a, ha⟩ := exists_germToFunctionField_eq_of_ord_nonneg_of_isNormalScheme
    (f := (f : X.functionField)) fun y hy ↦ (hf y hy).ge
  obtain ⟨b, hb⟩ := exists_germToFunctionField_eq_of_ord_nonneg_of_isNormalScheme
    (f := ((f⁻¹ : X.functionFieldˣ) : X.functionField)) fun y hy ↦ by
      rw [Units.val_inv_eq_inv_val, _root_.AlgebraicGeometry.Scheme.ord_inv, hf y hy, neg_zero]
  have hab : a * b = 1 := X.germToFunctionField_injective U <| by
    rw [map_mul, ha, hb, map_one, Units.mul_inv]
  exact ⟨⟨a, b, hab, (mul_comm b a).trans hab⟩, ha⟩

end Hartogs

namespace CartierDivisor

/-- **Cartier divisors embed into Weil divisors on a normal Noetherian scheme.** If two Cartier
divisors on a Noetherian normal integral scheme have the same orders at all codimension-one points,
their local equations differ by rational functions without zeros or poles, which are regular units
by algebraic Hartogs' principle. Hartshorne, Proposition II.6.11. -/
theorem toWeilDivisor_injective [IsIntegral X] [IsNoetherian X] [IsNormalScheme X] :
    Function.Injective (toWeilDivisor (X := X)) := by
  have hinj : Function.Injective (toWeilDivisorHom (X := X)) := by
    refine (injective_iff_map_eq_zero toWeilDivisorHom).mpr fun D hD ↦ ?_
    choose U _ hxU g hg using fun x : X ↦ D.exists_localEquation_le ⊤ (Opens.mem_top x)
    have hcover : (⊤ : X.Opens) ≤ ⨆ x, U x := fun x _ ↦ Opens.mem_iSup.mpr ⟨x, hxU x⟩
    refine TopCat.Sheaf.eq_of_locally_eq' (cartierDivisorSheaf X) U ⊤ (fun _ ↦ homOfLE le_top)
      hcover D 0 fun x ↦ ?_
    have : Nonempty (U x) := ⟨⟨x, hxU x⟩⟩
    obtain ⟨u, hu⟩ := exists_unit_germToFunctionField_eq_of_ord_eq_zero_of_isNormalScheme
      (U := U x) (f := g x) fun y hy ↦ by
        rw [← D.coeff_toWeilDivisor_eq_ord y hy (g x) (hg x), ← toWeilDivisorHom_apply, hD,
          WeilDivisor.coeff_zero]
    have hunit : Units.map (X.germToFunctionField (U x)).hom u = g x := Units.ext hu
    -- Unfold the presheaf map on `cartierDivisorSheaf` to the `|_` notation used by `hg` and `h0`.
    change D |_ U x = (0 : CartierDivisor X) |_ U x
    have h0 : (0 : CartierDivisor X) |_ U x = 0 := map_zero _
    rw [h0, ← hg x, ← hunit, rationalUnitClass_germToFunctionField_eq_zero]
  intro D E h
  exact hinj (by simpa only [toWeilDivisorHom_apply] using h)

end CartierDivisor

end Scheme

end

end AlgebraicGeometry

end TauCeti

namespace AlgebraicGeometry.Scheme.IdealSheafData

open TauCeti.AlgebraicGeometry

variable {X : Scheme.{u}} [IsIntegral X]

noncomputable section

/-- If two sections generate the same ideal sheaf on affine opens `U` and `V`, then over any
nonempty open `W` contained in `U ⊓ V`, the ratio of their rational functions is regular. -/
private lemma exists_germToFunctionField_mul_eq_of_ideal_eq_span {I : X.IdealSheafData}
    {U V : X.affineOpens} [Nonempty U.1] [Nonempty V.1]
    {a : Γ(X, U)} (hIa : I.ideal U = Ideal.span {a})
    {b : Γ(X, V)} (hb : b ≠ 0) (hIb : I.ideal V = Ideal.span {b})
    {W : X.Opens} [Nonempty W] (hWU : W ≤ U.1) (hWV : W ≤ V.1) :
    ∃ c : Γ(X, W), X.germToFunctionField W c * X.germToFunctionField V.1 b =
      X.germToFunctionField U.1 a := by
  have hbK : X.germToFunctionField V.1 b ≠ 0 :=
    (map_ne_zero_iff _ (X.germToFunctionField_injective V.1)).mpr hb
  obtain ⟨c, hc⟩ := Scheme.exists_germToFunctionField_eq_of_forall_mem_range (U := W)
    (f := X.germToFunctionField U.1 a * (X.germToFunctionField V.1 b)⁻¹) fun x hxW ↦ by
      obtain ⟨_, ⟨Z, hZ, rfl⟩, hxZ, hZW⟩ :=
        X.isBasis_affineOpens.exists_subset_of_mem_open hxW W.isOpen
      replace hZW : Z ≤ W := hZW
      have hZa : X.presheaf.map (homOfLE (hZW.trans hWU)).op a ∈
          Ideal.span {X.presheaf.map (homOfLE (hZW.trans hWV)).op b} := by
        have h1 : I.ideal ⟨Z, hZ⟩ =
            Ideal.span {X.presheaf.map (homOfLE (hZW.trans hWU)).op a} := by
          rw [← I.map_ideal (U := ⟨Z, hZ⟩) (V := U) (hZW.trans hWU), hIa, Ideal.map_span,
            Set.image_singleton]
          rfl
        have h2 : I.ideal ⟨Z, hZ⟩ =
            Ideal.span {X.presheaf.map (homOfLE (hZW.trans hWV)).op b} := by
          rw [← I.map_ideal (U := ⟨Z, hZ⟩) (V := V) (hZW.trans hWV), hIb, Ideal.map_span,
            Set.image_singleton]
          rfl
        exact h2 ▸ h1 ▸ Ideal.mem_span_singleton_self _
      obtain ⟨d, hd⟩ := Ideal.mem_span_singleton'.mp hZa
      refine ⟨X.presheaf.germ Z x hxZ d, ?_⟩
      rw [eq_mul_inv_iff_mul_eq₀ hbK,
        ← X.algebraMap_germ_eq_germToFunctionField ((hZW.trans hWU) hxZ),
        ← X.algebraMap_germ_eq_germToFunctionField ((hZW.trans hWV) hxZ), ← map_mul]
      refine congrArg (algebraMap (X.presheaf.stalk x) X.functionField) ?_
      rw [← X.presheaf.germ_res_apply (homOfLE (hZW.trans hWV)) x hxZ b,
        ← X.presheaf.germ_res_apply (homOfLE (hZW.trans hWU)) x hxZ a, ← map_mul, hd]
  exact ⟨c, by rw [hc, inv_mul_cancel_right₀ hbK]⟩

/-- Two nonzero sections generating the same ideal sheaf on affine opens have the same Cartier
class on any nonempty open contained in their intersection. -/
private lemma rationalUnitClass_eq_of_ideal_eq_span {I : X.IdealSheafData}
    {U V : X.affineOpens} [Nonempty U.1] [Nonempty V.1]
    {a : Γ(X, U)} (ha : a ≠ 0) (hIa : I.ideal U = Ideal.span {a})
    {b : Γ(X, V)} (hb : b ≠ 0) (hIb : I.ideal V = Ideal.span {b})
    {W : X.Opens} [Nonempty W] (hWU : W ≤ U.1) (hWV : W ≤ V.1) :
    Scheme.rationalUnitClass X W
        (Additive.ofMul (Units.mk0 (X.germToFunctionField U.1 a)
          ((map_ne_zero_iff _ (X.germToFunctionField_injective U.1)).mpr ha))) =
      Scheme.rationalUnitClass X W
        (Additive.ofMul (Units.mk0 (X.germToFunctionField V.1 b)
          ((map_ne_zero_iff _ (X.germToFunctionField_injective V.1)).mpr hb))) := by
  set fa := Units.mk0 (X.germToFunctionField U.1 a)
    ((map_ne_zero_iff _ (X.germToFunctionField_injective U.1)).mpr ha)
  set fb := Units.mk0 (X.germToFunctionField V.1 b)
    ((map_ne_zero_iff _ (X.germToFunctionField_injective V.1)).mpr hb)
  obtain ⟨c, hc⟩ := exists_germToFunctionField_mul_eq_of_ideal_eq_span hIa hb hIb hWU hWV
  obtain ⟨d, hd⟩ := exists_germToFunctionField_mul_eq_of_ideal_eq_span hIb ha hIa hWV hWU
  have hcd : c * d = 1 := X.germToFunctionField_injective W <| by
    refine mul_right_cancel₀ ((map_ne_zero_iff _ (X.germToFunctionField_injective U.1)).mpr ha) ?_
    rw [map_mul, mul_assoc, hd, hc, map_one, one_mul]
  let u : Γ(X, W)ˣ := ⟨c, d, hcd, (mul_comm d c).trans hcd⟩
  exact (Scheme.rationalUnitClass_eq_rationalUnitClass_iff X W fa fb).mpr
    ⟨u, Units.ext (by simpa [Scheme.regularUnitToFunctionField_apply, fa, fb] using hc)⟩

/-- **Unique Cartier divisor of an effective Cartier ideal sheaf.** On an integral scheme, an
effective Cartier ideal sheaf `I` has a unique global Cartier divisor restricting on every nonempty
affine open where `I = (b)` to the Cartier class of `b`. -/
theorem IsEffectiveCartier.existsUnique_cartierDivisor {I : X.IdealSheafData}
    (hI : I.IsEffectiveCartier) :
    ∃! D : Scheme.CartierDivisor X,
      ∀ (V : X.affineOpens) [Nonempty V.1] {b : Γ(X, V)} (hb : b ≠ 0),
        I.ideal V = Ideal.span {b} →
        D |_ V.1 = Scheme.rationalUnitClass X V.1
          (Additive.ofMul (Units.mk0 (X.germToFunctionField V.1 b)
            ((map_ne_zero_iff _ (X.germToFunctionField_injective V.1)).mpr hb))) := by
  choose U hxU a ha hUa using (isEffectiveCartier_iff I).mp hI
  have hne : ∀ x, Nonempty (U x).1 := fun x ↦ ⟨⟨x, hxU x⟩⟩
  have ha0 : ∀ x, a x ≠ 0 := fun x h0 ↦
    one_ne_zero (α := Γ(X, U x)) (ha x (by simp [h0] : a x * 1 = a x * 0))
  let sf : ∀ x, ((Scheme.cartierDivisorSheaf X).obj.obj (op (U x).1) : Type u) :=
    fun x ↦ Scheme.rationalUnitClass X (U x).1 (Additive.ofMul
      (Units.mk0 (X.germToFunctionField (U x).1 (a x))
        ((map_ne_zero_iff _ (X.germToFunctionField_injective (U x).1)).mpr (ha0 x))))
  have hcompat : TopCat.Presheaf.IsCompatible (Scheme.cartierDivisorSheaf X).obj
      (fun x ↦ (U x).1) sf := by
    intro x y
    have : Nonempty ((U x).1 ⊓ (U y).1 : X.Opens) :=
      ⟨⟨genericPoint X, Scheme.genericPoint_mem (U x).1, Scheme.genericPoint_mem (U y).1⟩⟩
    change sf x |_ ((U x).1 ⊓ (U y).1) = sf y |_ ((U x).1 ⊓ (U y).1)
    rw [Scheme.rationalUnitClass_restrict X inf_le_left,
      Scheme.rationalUnitClass_restrict X inf_le_right]
    exact rationalUnitClass_eq_of_ideal_eq_span (ha0 x) (hUa x) (ha0 y) (hUa y)
      inf_le_left inf_le_right
  have htop : (⊤ : X.Opens) ≤ ⨆ x, (U x).1 := fun x _ ↦ Opens.mem_iSup.mpr ⟨x, hxU x⟩
  obtain ⟨D, hD, huniq⟩ := (Scheme.cartierDivisorSheaf X).existsUnique_gluing'
    (fun x ↦ (U x).1) ⊤ (fun _ ↦ homOfLE le_top) htop sf hcompat
  have hD' : ∀ x, D |_ (U x).1 = sf x := hD
  refine ⟨D, fun V _ b hb hVb ↦ ?_, fun E hE ↦ huniq E fun x ↦ hE (U x) (ha0 x) (hUa x)⟩
  let W : V.1 → X.Opens := fun y ↦ V.1 ⊓ (U y.1).1
  have hcover : V.1 ≤ ⨆ y : V.1, W y := fun x hx ↦ Opens.mem_iSup.mpr ⟨⟨x, hx⟩, hx, hxU x⟩
  refine TopCat.Sheaf.eq_of_locally_eq' (Scheme.cartierDivisorSheaf X) W V.1
    (fun _ ↦ homOfLE inf_le_left) hcover _ _ fun y ↦ ?_
  have : Nonempty (W y) := ⟨⟨y.1, y.2, hxU y.1⟩⟩
  change (D |_ V.1) |_ W y = (Scheme.rationalUnitClass X V.1 _) |_ W y
  rw [TopCat.Presheaf.restrict_restrict, ← TopCat.Presheaf.restrict_restrict inf_le_right le_top,
    hD' y.1, Scheme.rationalUnitClass_restrict X inf_le_right,
    Scheme.rationalUnitClass_restrict X inf_le_left]
  exact rationalUnitClass_eq_of_ideal_eq_span (ha0 y.1) (hUa y.1) hb hVb inf_le_right inf_le_left

/-- **The Cartier divisor of an effective Cartier ideal sheaf.** On an integral scheme, an effective
Cartier ideal sheaf `I` determines a global Cartier divisor by gluing the classes of its local
nonzerodivisor equations in `𝒦_X^× / 𝒪_X^×`. -/
def IsEffectiveCartier.toCartierDivisor {I : X.IdealSheafData} (hI : I.IsEffectiveCartier) :
    Scheme.CartierDivisor X :=
  hI.existsUnique_cartierDivisor.choose

/-- On any nonempty affine open where `I` is generated by a nonzero section `b`, the Cartier divisor
`hI.toCartierDivisor` restricts to the Cartier class of `b`. -/
theorem IsEffectiveCartier.toCartierDivisor_restrict {I : X.IdealSheafData}
    (hI : I.IsEffectiveCartier) (V : X.affineOpens) [Nonempty V.1]
    {b : Γ(X, V)} (hb : b ≠ 0) (hVb : I.ideal V = Ideal.span {b}) :
    hI.toCartierDivisor |_ V.1 = Scheme.rationalUnitClass X V.1
      (Additive.ofMul (Units.mk0 (X.germToFunctionField V.1 b)
        ((map_ne_zero_iff _ (X.germToFunctionField_injective V.1)).mpr hb))) :=
  hI.existsUnique_cartierDivisor.choose_spec.1 V hb hVb

/-- The Cartier divisor attached to an effective Cartier ideal sheaf is effective. -/
theorem IsEffectiveCartier.isEffective_toCartierDivisor {I : X.IdealSheafData}
    (hI : I.IsEffectiveCartier) : hI.toCartierDivisor.IsEffective := by
  refine Scheme.CartierDivisor.isEffective_iff_exists.mpr fun x ↦ ?_
  obtain ⟨U, hxU, a, ha, hUa⟩ := (isEffectiveCartier_iff I).mp hI x
  have : Nonempty U.1 := ⟨⟨x, hxU⟩⟩
  have ha0 : a ≠ 0 := fun h0 ↦ one_ne_zero (α := Γ(X, U)) (ha (by simp [h0] : a * 1 = a * 0))
  refine ⟨Units.mk0 (X.germToFunctionField U.1 a)
      ((map_ne_zero_iff _ (X.germToFunctionField_injective U.1)).mpr ha0),
    Scheme.CartierDivisor.isLocalEquationAt_iff.mpr
      ⟨U.1, hxU, (hI.toCartierDivisor_restrict U ha0 hUa).symm⟩,
    X.presheaf.germ U.1 x hxU a, ?_⟩
  exact X.algebraMap_germ_eq_germToFunctionField hxU a

/-- Taking the closed-subscheme ideal sheaf of `hI.toCartierDivisor` recovers `I`. -/
@[simp]
theorem IsEffectiveCartier.idealSheaf_toCartierDivisor {I : X.IdealSheafData}
    (hI : I.IsEffectiveCartier) :
    hI.isEffective_toCartierDivisor.idealSheaf = I := by
  choose U hxU a ha hUa using (isEffectiveCartier_iff I).mp hI
  refine ext_of_iSup_eq_top U (eq_top_iff.mpr fun x _ ↦ Opens.mem_iSup.mpr ⟨x, hxU x⟩) fun x ↦ ?_
  have : Nonempty (U x).1 := ⟨⟨x, hxU x⟩⟩
  have ha0 : a x ≠ 0 := fun h0 ↦
    one_ne_zero (α := Γ(X, U x)) (ha x (by simp [h0] : a x * 1 = a x * 0))
  rw [hUa x]
  exact hI.isEffective_toCartierDivisor.idealSheaf_ideal_eq_span (U x)
    (hI.toCartierDivisor_restrict (U x) ha0 (hUa x)).symm rfl

omit [IsIntegral X] in
private lemma mk_toInvertibleSheaf_congr {I J : X.IdealSheafData} (h : I = J)
    (hI : I.IsEffectiveCartier) (hJ : J.IsEffectiveCartier) :
    LineBundleClass.mk hI.toInvertibleSheaf = LineBundleClass.mk hJ.toInvertibleSheaf := by
  subst h
  rfl

/-- The line-bundle class of `hI.toCartierDivisor` is the inverse of the class of the invertible
ideal sheaf `I`. -/
@[simp]
theorem IsEffectiveCartier.toLineBundleClass_toCartierDivisor {I : X.IdealSheafData}
    (hI : I.IsEffectiveCartier) :
    hI.toCartierDivisor.toLineBundleClass = (LineBundleClass.mk hI.toInvertibleSheaf)⁻¹ := by
  rw [← mk_toInvertibleSheaf_congr hI.idealSheaf_toCartierDivisor
    hI.isEffective_toCartierDivisor.isEffectiveCartier_idealSheaf hI,
    hI.isEffective_toCartierDivisor.mk_idealSheaf_eq_inv, inv_inv]

end

end AlgebraicGeometry.Scheme.IdealSheafData

namespace TauCeti.AlgebraicGeometry

open _root_.AlgebraicGeometry

noncomputable section

section LocallyFactorial

variable {X : Scheme.{u}} [IsIntegral X] [IsNoetherian X]
  [∀ x : X, UniqueFactorizationMonoid (X.presheaf.stalk x)]

/-- A scheme whose local rings are integral unique factorization domains is normal. -/
instance IsNormalScheme.of_uniqueFactorizationMonoid_stalk : IsNormalScheme X :=
  isNormalScheme_iff_forall_stalk.mpr fun _ ↦ ⟨inferInstance, inferInstance⟩

/-- **The Weil divisor of a prime effective Cartier divisor.** On a Noetherian integral scheme with
factorial local rings, the Cartier divisor of the prime closed subscheme `closure {η}` has Weil
divisor `ofPoint η`. -/
@[simp]
theorem toWeilDivisor_toCartierDivisor_vanishingIdeal_closure_singleton
    (η : CodimensionOnePoint X) :
    (Scheme.IdealSheafData.isEffectiveCartier_vanishingIdeal_closure_singleton
      η.2).toCartierDivisor.toWeilDivisor = WeilDivisor.ofPoint η := by
  apply WeilDivisor.ext
  intro ξ
  set hη := Scheme.IdealSheafData.isEffectiveCartier_vanishingIdeal_closure_singleton η.2
  obtain ⟨U, hξU, a, ha, hUa⟩ := (Scheme.IdealSheafData.isEffectiveCartier_iff _).mp hη (ξ : X)
  have : Nonempty U.1 := ⟨⟨ξ, hξU⟩⟩
  have ha0 : a ≠ 0 := fun h0 ↦ one_ne_zero (α := Γ(X, U)) (ha (by simp [h0] : a * 1 = a * 0))
  rw [hη.toCartierDivisor.coeff_toWeilDivisor_eq_ord ξ hξU _
      (hη.toCartierDivisor_restrict U ha0 hUa).symm]
  change X.ord (X.germToFunctionField U.1 a) ξ = _
  rw [← X.algebraMap_germ_eq_germToFunctionField hξU a]
  set b := X.presheaf.germ U.1 ξ hξU a
  have hspan : ((Scheme.IdealSheafData.vanishingIdeal
      ⟨closure {(η : X)}, isClosed_closure⟩).ideal U).map (X.presheaf.germ U.1 ξ hξU).hom =
      Ideal.span {b} := by
    rw [hUa, Ideal.map_span, Set.image_singleton]
  rcases eq_or_ne ξ η with rfl | hne
  · rw [WeilDivisor.coeff_ofPoint_self]
    rw [Scheme.IdealSheafData.map_ideal_vanishingIdeal_closure_singleton_of_specializes hξU
      specializes_rfl] at hspan
    exact Scheme.ord_algebraMap_stalk_eq_one ξ.2 specializes_rfl hspan
  · rw [WeilDivisor.coeff_ofPoint_of_ne hne]
    have hnot : ¬ (η : X) ⤳ (ξ : X) := fun hsp ↦
      hne (CodimensionOnePoint.eq_of_specializes hsp).symm
    rw [Scheme.IdealSheafData.map_ideal_vanishingIdeal_closure_singleton_of_not_specializes hξU
      hnot] at hspan
    have hu : IsUnit b := Ideal.span_singleton_eq_top.mp hspan.symm
    exact (Scheme.ord_algebraMap_stalk_eq_zero_iff ξ.2 specializes_rfl hu.ne_zero).mpr fun hm ↦
      (IsLocalRing.mem_maximalIdeal _).mp (by simpa using hm) hu

namespace SchemeWeilDivisor

/-- The homomorphism sending a Weil divisor on a Noetherian locally factorial integral scheme to its
Cartier divisor, defined on prime divisors `ofPoint η` by the effective Cartier ideal sheaf of
`closure {η}`. -/
def toCartierDivisorOfUniqueFactorizationMonoid : SchemeWeilDivisor X →+ Scheme.CartierDivisor X :=
  (Finsupp.linearCombination ℤ fun η : CodimensionOnePoint X ↦
    (Scheme.IdealSheafData.isEffectiveCartier_vanishingIdeal_closure_singleton
      η.2).toCartierDivisor).toAddMonoidHom

/-- A prime Weil divisor `ofPoint η` maps to the Cartier divisor of `closure {η}`. -/
@[simp]
theorem toCartierDivisorOfUniqueFactorizationMonoid_ofPoint (η : CodimensionOnePoint X) :
    toCartierDivisorOfUniqueFactorizationMonoid (WeilDivisor.ofPoint η) =
      (Scheme.IdealSheafData.isEffectiveCartier_vanishingIdeal_closure_singleton
        η.2).toCartierDivisor := by
  rw [← one_zsmul (WeilDivisor.ofPoint η), ← WeilDivisor.single_eq_zsmul_ofPoint,
    toCartierDivisorOfUniqueFactorizationMonoid]
  simp

/-- Taking the Weil divisor of `toCartierDivisorOfUniqueFactorizationMonoid D` recovers `D`. -/
@[simp]
theorem toWeilDivisor_toCartierDivisorOfUniqueFactorizationMonoid (D : SchemeWeilDivisor X) :
    (toCartierDivisorOfUniqueFactorizationMonoid D).toWeilDivisor = D := by
  have hcomp : Scheme.CartierDivisor.toWeilDivisorHom.comp
      (toCartierDivisorOfUniqueFactorizationMonoid (X := X)) = AddMonoidHom.id _ := by
    refine Finsupp.addHom_ext' fun η ↦ AddMonoidHom.ext_int ?_
    simp only [AddMonoidHom.comp_apply, Finsupp.singleAddHom_apply,
      WeilDivisor.single_eq_zsmul_ofPoint, one_zsmul,
      Scheme.CartierDivisor.toWeilDivisorHom_apply,
      toCartierDivisorOfUniqueFactorizationMonoid_ofPoint,
      toWeilDivisor_toCartierDivisor_vanishingIdeal_closure_singleton, AddMonoidHom.id_apply]
  simpa only [AddMonoidHom.comp_apply, Scheme.CartierDivisor.toWeilDivisorHom_apply,
    AddMonoidHom.id_apply] using DFunLike.congr_fun hcomp D

/-- **The Weil–Cartier equivalence on locally factorial schemes.** On a Noetherian integral scheme
whose local rings are unique factorization domains, Weil divisors and Cartier divisors are
additively equivalent. Stacks, Lemma 31.15.7 (0BE9); Hartshorne, Proposition II.6.11. -/
@[stacks 0BE9]
def equivCartierDivisorOfUniqueFactorizationMonoid :
    SchemeWeilDivisor X ≃+ Scheme.CartierDivisor X where
  toFun := toCartierDivisorOfUniqueFactorizationMonoid
  invFun := Scheme.CartierDivisor.toWeilDivisor
  left_inv := toWeilDivisor_toCartierDivisorOfUniqueFactorizationMonoid
  right_inv D := Scheme.CartierDivisor.toWeilDivisor_injective
    (toWeilDivisor_toCartierDivisorOfUniqueFactorizationMonoid D.toWeilDivisor)
  map_add' := map_add toCartierDivisorOfUniqueFactorizationMonoid

/-- Evaluating the Weil–Cartier equivalence on `ofPoint η` gives the Cartier divisor of
`closure {η}`. -/
@[simp]
theorem equivCartierDivisorOfUniqueFactorizationMonoid_ofPoint (η : CodimensionOnePoint X) :
    equivCartierDivisorOfUniqueFactorizationMonoid (WeilDivisor.ofPoint η) =
      (Scheme.IdealSheafData.isEffectiveCartier_vanishingIdeal_closure_singleton
        η.2).toCartierDivisor :=
  toCartierDivisorOfUniqueFactorizationMonoid_ofPoint η

/-- The inverse of the Weil–Cartier equivalence sends a Cartier divisor to its Weil divisor. -/
@[simp]
theorem equivCartierDivisorOfUniqueFactorizationMonoid_symm_apply (D : Scheme.CartierDivisor X) :
    equivCartierDivisorOfUniqueFactorizationMonoid.symm D = D.toWeilDivisor :=
  (rfl)

/-- The Weil–Cartier equivalence sends principal Weil divisors to principal Cartier divisors. -/
@[simp]
theorem equivCartierDivisorOfUniqueFactorizationMonoid_principalDivisor
    (g : Additive X.functionFieldˣ) :
    equivCartierDivisorOfUniqueFactorizationMonoid
        ((WeilDivisor.OrderSystem.ofScheme X).principalDivisor g) =
      Scheme.principalCartierDivisor X g.toMul := by
  apply Scheme.CartierDivisor.toWeilDivisor_injective
  rw [← equivCartierDivisorOfUniqueFactorizationMonoid_symm_apply, AddEquiv.symm_apply_apply,
    Scheme.CartierDivisor.toWeilDivisor_principalCartierDivisor]

variable (X) in
/-- **`Cl(X) ≃+ Pic(X)` on locally factorial schemes.** On a Noetherian integral scheme whose local
rings are unique factorization domains, the Weil divisor class group is additively equivalent to
the Picard group of line-bundle classes. Hartshorne, Corollary II.6.16. -/
def classGroupAddEquivLineBundleClassOfUniqueFactorizationMonoid :
    (WeilDivisor.OrderSystem.ofScheme X).ClassGroup ≃+ Additive (LineBundleClass X) :=
  QuotientAddGroup.liftEquiv (WeilDivisor.OrderSystem.ofScheme X).principalSubgroup
    (φ := Scheme.CartierDivisor.toLineBundleClassHom.comp
      equivCartierDivisorOfUniqueFactorizationMonoid.toAddMonoidHom)
    (fun a ↦ by
      obtain ⟨E, hE⟩ := Scheme.CartierDivisor.toLineBundleClass_surjective a.toMul
      refine ⟨equivCartierDivisorOfUniqueFactorizationMonoid.symm E, ?_⟩
      rw [AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom, AddEquiv.apply_symm_apply,
        Scheme.CartierDivisor.toLineBundleClassHom_apply, hE, ofMul_toMul])
    (by
      ext D
      rw [WeilDivisor.OrderSystem.mem_principalSubgroup, AddMonoidHom.mem_ker,
        AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom,
        ← AddMonoidHom.mem_ker, ← Scheme.CartierDivisor.principalSubgroup_eq_ker,
        Scheme.CartierDivisor.mem_principalSubgroup]
      constructor
      · rintro ⟨g, rfl⟩
        exact ⟨g.toMul, (equivCartierDivisorOfUniqueFactorizationMonoid_principalDivisor g).symm⟩
      · rintro ⟨f, hf⟩
        exact ⟨Additive.ofMul f, equivCartierDivisorOfUniqueFactorizationMonoid.injective <|
          (equivCartierDivisorOfUniqueFactorizationMonoid_principalDivisor _).trans hf⟩)

/-- On the class of a Weil divisor `D`, the `Cl(X) ≃+ Pic(X)` equivalence sends `[D]` to the
line-bundle class of the corresponding Cartier divisor. -/
@[simp]
theorem classGroupAddEquivLineBundleClassOfUniqueFactorizationMonoid_divisorClass
    (D : SchemeWeilDivisor X) :
    classGroupAddEquivLineBundleClassOfUniqueFactorizationMonoid X
        ((WeilDivisor.OrderSystem.ofScheme X).divisorClass D) =
      Additive.ofMul (equivCartierDivisorOfUniqueFactorizationMonoid D).toLineBundleClass := by
  rw [WeilDivisor.OrderSystem.divisorClass_eq_mk', QuotientAddGroup.mk'_apply,
    classGroupAddEquivLineBundleClassOfUniqueFactorizationMonoid]
  exact (QuotientAddGroup.liftEquiv_mk _ _ _ D).trans
    (Scheme.CartierDivisor.toLineBundleClassHom_apply _)

/-- The `Cl(X) ≃+ Pic(X)` equivalence sends the class of a prime divisor `ofPoint η` to the
inverse of the line-bundle class of the ideal sheaf of `closure {η}`, namely
`[𝒪_X(closure {η})]`. -/
theorem classGroupAddEquivLineBundleClassOfUniqueFactorizationMonoid_ofPoint
    (η : CodimensionOnePoint X) :
    classGroupAddEquivLineBundleClassOfUniqueFactorizationMonoid X
        ((WeilDivisor.OrderSystem.ofScheme X).divisorClass (WeilDivisor.ofPoint η)) =
      Additive.ofMul (LineBundleClass.mk
        (Scheme.IdealSheafData.isEffectiveCartier_vanishingIdeal_closure_singleton
          η.2).toInvertibleSheaf)⁻¹ := by
  rw [classGroupAddEquivLineBundleClassOfUniqueFactorizationMonoid_divisorClass,
    equivCartierDivisorOfUniqueFactorizationMonoid_ofPoint,
    Scheme.IdealSheafData.IsEffectiveCartier.toLineBundleClass_toCartierDivisor]

end SchemeWeilDivisor

end LocallyFactorial

end

end TauCeti.AlgebraicGeometry
