/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Kaehler.Basic
public import Mathlib.RingTheory.Kaehler.JacobiZariski
public import Mathlib.RingTheory.Kaehler.TensorProduct
public import Mathlib.RingTheory.Kaehler.Polynomial
public import Mathlib.RingTheory.Unramified.Basic

/-!
# Base-change maps for Kähler differentials

This file identifies the base-change map `B ⊗[A] Ω[A⁄R] → Ω[B⁄R]` with the `liftBaseChange`
of `KaehlerDifferential.map R R A B`, gives an extensionality criterion for `B`-linear maps out of
`B ⊗[A] Ω[A⁄R]`, and records reusable consequences of the Jacobi–Zariski sequence:

* the base-change map onto `Ω[B⁄R]` is surjective exactly when `Ω[B⁄A]` vanishes, and if `Ω[A⁄R]`
  is spanned by a set `s` then its range is spanned by the image of `s`;
* when `H¹(L_{B/A}) = 0` (for example, when `B` is formally smooth over `A`), the base-change map
  `B ⊗[A] Ω[A⁄R] → Ω[B⁄R]` is injective, and if in addition `B` is faithfully flat over `A` then
  `KaehlerDifferential.map R R A B : Ω[A⁄R] → Ω[B⁄R]` is injective.

For a base change `B = S ⊗[R] A`, Mathlib's isomorphism `B ⊗[A] Ω[A⁄R] ≃ Ω[B⁄S]`
(`KaehlerDifferential.tensorKaehlerEquiv`) is the base-change map into `Ω[B⁄R]` followed by the
map `Ω[B⁄R] → Ω[B⁄S]` sending `d_R b` to `d_S b`.

## Main results

* `TauCeti.mapBaseChange_eq_liftBaseChange`
* `TauCeti.kaehlerBaseChange_linearMap_ext`
* `TauCeti.subsingleton_kaehlerDifferential_iff_range_mapBaseChange_eq_top`
* `TauCeti.range_mapBaseChange_eq_span_image`
* `TauCeti.injective_mapBaseChange_of_subsingleton_h1Cotangent`
* `TauCeti.injective_kaehlerDifferential_map_of_subsingleton_h1Cotangent`
* `TauCeti.map_comp_mapBaseChange_eq_tensorKaehlerEquiv`
* `KaehlerDifferential.mapBaseChange_surjective_of_formallyUnramified`: if `B` is formally
  unramified over `A`, then `B ⊗[A] Ω[A⁄R] → Ω[B⁄R]` is surjective.
* `KaehlerDifferential.isBaseChange_map`: for `B = S ⊗[R] A`, the map `Ω[A⁄R] → Ω[B⁄S]` is a base
  change along `A → B`.
* `TauCeti.finrank_kaehlerDifferential_le_of_formallyUnramified_mvPolynomial`: a field formally
  unramified over a polynomial ring `K[X_i]` has Kähler differentials over `K` of dimension at most
  the number of variables.
-/

public section

noncomputable section

namespace TauCeti

open KaehlerDifferential TensorProduct

variable (R A B : Type*) [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
  [Algebra A B] [IsScalarTower R A B]

/-- The base-change map `B ⊗[A] Ω[A⁄R] → Ω[B⁄R]` is the `B`-linear extension of the
`A`-linear map `KaehlerDifferential.map R R A B : Ω[A⁄R] → Ω[B⁄R]`. -/
theorem mapBaseChange_eq_liftBaseChange :
    mapBaseChange R A B = (map R R A B).liftBaseChange B := by
  ext; simp

/-- Two `B`-linear maps out of `B ⊗[A] Ω[A⁄R]` agree as soon as they agree on `1 ⊗ₜ D R A a` for
all `a : A`. -/
theorem kaehlerBaseChange_linearMap_ext
    {R A B M : Type*} [CommRing R] [CommRing A] [CommRing B] [AddCommGroup M]
    [Algebra R A] [Algebra A B] [Module B M]
    {L₁ L₂ : B ⊗[A] Ω[A⁄R] →ₗ[B] M}
    (h : ∀ a : A, L₁ (1 ⊗ₜ[A] D R A a) = L₂ (1 ⊗ₜ[A] D R A a)) :
    L₁ = L₂ := by
  let : Module A M := Module.compHom M (algebraMap A B)
  have : IsScalarTower A B M := .of_algebraMap_smul fun _ _ ↦ rfl
  exact AlgebraTensorModule.curry_injective <| LinearMap.ext_ring <|
    LinearMap.ext_on_range (span_range_derivation R A) fun a ↦ by
      simpa using h a

/-- In a tower `R → A → B`, the first map in the Jacobi–Zariski sequence is surjective
exactly when the relative differential module `Ω[B⁄A]` vanishes. -/
theorem subsingleton_kaehlerDifferential_iff_range_mapBaseChange_eq_top :
    Subsingleton Ω[B⁄A] ↔ (mapBaseChange R A B).range = ⊤ := by
  -- The range of `mapBaseChange` is the kernel of `map R A B B : Ω[B⁄R] → Ω[B⁄A]`. That map
  -- is surjective, so it vanishes exactly when its range `⊤` is `⊥`, i.e. when `Ω[B⁄A]` is
  -- trivial.
  rw [range_mapBaseChange, LinearMap.ker_eq_top, ← LinearMap.range_eq_bot,
    LinearMap.range_eq_top.mpr (map_surjective R A B)]
  grind [subsingleton_iff_bot_eq_top, Submodule.subsingleton_iff]

/-- If `Ω[A⁄R]` is spanned by `s`, then the range of the base-change map to `Ω[B⁄R]` is
spanned by the image of `s`. -/
theorem range_mapBaseChange_eq_span_image {s : Set Ω[A⁄R]} (hs : Submodule.span A s = ⊤) :
    (mapBaseChange R A B).range = Submodule.span B (map R R A B '' s) := by
  rw [mapBaseChange_eq_liftBaseChange, LinearMap.range_liftBaseChange, LinearMap.range_eq_map,
    ← hs, ← Submodule.span_image, Submodule.span_span_of_tower]

/-- In a tower `R → A → B` with `H¹(L_{B/A}) = 0` (in particular when `B` is formally smooth over
`A`), the base-change map `B ⊗[A] Ω[A⁄R] → Ω[B⁄R]` is injective. -/
theorem injective_mapBaseChange_of_subsingleton_h1Cotangent
    [Subsingleton (Algebra.H1Cotangent A B)] :
    Function.Injective (mapBaseChange R A B) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨y, rfl⟩ := (Algebra.H1Cotangent.exact_δ_mapBaseChange R A B x).mp hx
  rw [Subsingleton.elim y 0, map_zero]

/-- In a tower `R → A → B` where `H¹(L_{B/A}) = 0` and `B` is faithfully flat over `A` (for
instance, a formally smooth extension of fields), `KaehlerDifferential.map R R A B : Ω[A⁄R] →
Ω[B⁄R]` is injective. -/
theorem injective_kaehlerDifferential_map_of_subsingleton_h1Cotangent
    [Subsingleton (Algebra.H1Cotangent A B)] [Module.FaithfullyFlat A B] :
    Function.Injective (map R R A B) := by
  rw [injective_iff_map_eq_zero]
  intro ω hω
  have h0 : mapBaseChange R A B (1 ⊗ₜ[A] ω) = 0 := by
    simpa [mapBaseChange_tmul] using hω
  simpa using
    (map_eq_zero_iff _ (injective_mapBaseChange_of_subsingleton_h1Cotangent R A B)).mp h0

/-- For a base change `B = S ⊗[R] A`, Mathlib's isomorphism
`KaehlerDifferential.tensorKaehlerEquiv : B ⊗[A] Ω[A⁄R] ≃ Ω[B⁄S]` is the base-change map
`B ⊗[A] Ω[A⁄R] → Ω[B⁄R]` followed by `KaehlerDifferential.map R S B B : Ω[B⁄R] → Ω[B⁄S]`, which
sends `d_R b` to `d_S b`. Neither factor need be an isomorphism. -/
theorem map_comp_mapBaseChange_eq_tensorKaehlerEquiv (S : Type*) [CommRing S] [Algebra R S]
    [Algebra S B] [IsScalarTower R S B] [Algebra.IsPushout R S A B] :
    (map R S B B).comp (mapBaseChange R A B) = (tensorKaehlerEquiv R S A B).toLinearMap :=
  kaehlerBaseChange_linearMap_ext fun a ↦ by simp

end TauCeti

namespace KaehlerDifferential

/-- If `A` is formally unramified over `S`, then `A ⊗[S] Ω[S⁄R] → Ω[A⁄R]` is surjective. This
generalizes `KaehlerDifferential.mapBaseChange_surjective`, for `S → A` surjective. -/
theorem mapBaseChange_surjective_of_formallyUnramified (R S A : Type*) [CommRing R] [CommRing S]
    [CommRing A] [Algebra R S] [Algebra R A] [Algebra S A] [IsScalarTower R S A]
    [Algebra.FormallyUnramified S A] :
    Function.Surjective (mapBaseChange R S A) :=
  LinearMap.range_eq_top.mp <|
    (TauCeti.subsingleton_kaehlerDifferential_iff_range_mapBaseChange_eq_top R S A).mp
      inferInstance

/-- For a base change `B = S ⊗[R] A`, the map `KaehlerDifferential.map R S A B : Ω[A⁄R] → Ω[B⁄S]`
exhibits `Ω[B⁄S]` as the base change of `Ω[A⁄R]` along `A → B`. Compare
`KaehlerDifferential.isBaseChange`, the base change along `R → S`. -/
theorem isBaseChange_map (R S A B : Type*) [CommRing R] [CommRing S] [CommRing A] [CommRing B]
    [Algebra R S] [Algebra R A] [Algebra R B] [Algebra A B] [Algebra S B] [IsScalarTower R A B]
    [IsScalarTower R S B] [Algebra.IsPushout R S A B] :
    IsBaseChange B (map R S A B) :=
  .of_equiv (tensorKaehlerEquiv R S A B) fun ω => by
    suffices h : (tensorKaehlerEquiv R S A B).toLinearMap.restrictScalars A ∘ₗ
        TensorProduct.mk A B Ω[A⁄R] 1 = map R S A B from LinearMap.congr_fun h ω
    ext a
    simp

end KaehlerDifferential

namespace TauCeti

open KaehlerDifferential TensorProduct

/-- **Differentials of a field unramified over a polynomial ring.** If a field `L` over a ring `K`
is a formally unramified algebra over the polynomial ring `K[X_i]`, then `Ω[L⁄K]` is spanned by the
images of the `d X_i`, so its dimension is at most the number of variables. -/
theorem finrank_kaehlerDifferential_le_of_formallyUnramified_mvPolynomial {σ K L : Type*}
    [Finite σ] [CommRing K] [Field L] [Algebra K L] [Algebra (MvPolynomial σ K) L]
    [IsScalarTower K (MvPolynomial σ K) L] [Algebra.FormallyUnramified (MvPolynomial σ K) L] :
    Module.finrank L Ω[L⁄K] ≤ Nat.card σ := by
  have hsurj := mapBaseChange_surjective_of_formallyUnramified K (MvPolynomial σ K) L
  have b := (mvPolynomialBasis K σ).baseChange L
  have : Module.Finite L (L ⊗[MvPolynomial σ K] Ω[MvPolynomial σ K⁄K]) := .of_basis b
  calc Module.finrank L Ω[L⁄K]
      ≤ Module.finrank L (L ⊗[MvPolynomial σ K] Ω[MvPolynomial σ K⁄K]) :=
        LinearMap.finrank_le_finrank_of_surjective hsurj
    _ = Nat.card σ := by rw [Module.finrank_eq_nat_card_basis b]

end TauCeti
