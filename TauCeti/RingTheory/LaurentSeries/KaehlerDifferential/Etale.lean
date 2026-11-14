/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Derivation.FormallyEtale
public import TauCeti.RingTheory.Kaehler.MapSemilinear
public import TauCeti.RingTheory.LaurentSeries.KaehlerDifferential.Basic
public import TauCeti.Topology.Algebra.Module.ModuleTopology

/-!
# Continuous one-forms of étale extensions of Laurent series

Let `K` be a field, `F = K⸨t⸩` and `L` a formally étale `F`-algebra, for instance a finite
separable field extension of `F` (`Algebra.FormallyEtale.of_isSeparable`). The formal derivative
`D = d/dt` of `F` extends uniquely to a `K`-derivation `D_L` of `L`
(`TauCeti.LaurentSeries.Extension.derivation`), by the extension of derivations along formally
étale maps (`Derivation.extendOfFormallyEtale`).

The continuous one-forms `Ω¹_cont(L/K)` are built from `D_L` exactly as `Ω¹_cont(F/K)` is built
from `D` (`TauCeti.ContinuousKaehlerDifferential`): they are the quotient of the algebraic Kähler
differentials `Ω[L⁄K]` by the kernel of the `L`-linear map `λ_L : Ω[L⁄K] → L`, `x dy ↦ x * D_L y`,
induced by `D_L`. This file shows:

* `λ_L` induces an `L`-linear equivalence `Ω¹_cont(L/K) ≃ L` sending `dt` to `1`, so every
  continuous one-form on `L` is uniquely `x dt`, and `dy = D_L y dt`.
* The pullback `Ω¹_cont(F/K) → Ω¹_cont(L/K)`, `f dg ↦ f dg`, is induced by the map
  `Ω[F⁄K] → Ω[L⁄K]` of Kähler differentials, and it extends to an `L`-linear equivalence
  `L ⊗_F Ω¹_cont(F/K) ≃ Ω¹_cont(L/K)`, `x ⊗ ω ↦ x ω`.
* `D_L` and `Ω¹_cont(L/K)` are functorial in `F`-algebra homomorphisms `φ : M →ₐ[F] L` between
  formally étale `F`-algebras: `φ` commutes with `d/dt`, induces a `φ`-semilinear pullback on
  continuous one-forms compatible with `KaehlerDifferential.mapSemilinear`, and in a tower
  `F → M → L` induces the relative scalar-extension equivalence
  `L ⊗_M Ω¹_cont(M/K) ≃ Ω¹_cont(L/K)`.
* `d : L → Ω¹_cont(L/K)` is the universal derivation among `K`-derivations of `L` whose restriction
  to `F` is continuous for the valuation topology: for an `L`-module `M` with a Hausdorff topology
  for which scalar multiplication by `F` is continuous, a `K`-derivation `δ : L → M` factors as
  `ℓ ∘ d` with `ℓ` an `L`-linear map exactly when `δ` is continuous on `F`, and then `ℓ` is unique.
  This characterization does not use a topology on `L`.
* When `L` carries a topology, `Ω¹_cont(L/K)` carries the `L`-module topology; when `L` is a
  topological semiring, `Ω¹_cont(L/K) ≃ L` is a continuous `L`-linear equivalence, and when `L` is
  a finite `F`-algebra carrying the `F`-module topology, `Ω¹_cont(L/K)` also carries the
  `F`-module topology.

## Main definitions

* `TauCeti.LaurentSeries.Extension.derivation K L`: the derivation `D_L = d/dt` of `L`.
* `TauCeti.LaurentSeries.Extension.ContinuousKaehlerDifferential K L`: the continuous one-forms
  `Ω¹_cont(L/K)`.
* `Extension.ContinuousKaehlerDifferential.D K L`: the universal derivation `d`.
* `Extension.ContinuousKaehlerDifferential.equivSelf K L`: the `L`-linear equivalence
  `Ω¹_cont(L/K) ≃ L` sending `d t` to `1` (upgraded to `continuousEquivSelf` when `L` is a
  topological semiring).
* `Extension.ContinuousKaehlerDifferential.map K L`: the pullback `Ω¹_cont(F/K) → Ω¹_cont(L/K)`.
* `Extension.ContinuousKaehlerDifferential.tensorEquiv K L`: the `L`-linear equivalence
  `L ⊗_F Ω¹_cont(F/K) ≃ Ω¹_cont(L/K)`.
* `Extension.ContinuousKaehlerDifferential.mapAlgHom` and `mapAlgEquiv`: semilinear functoriality
  along `F`-algebra homomorphisms and isomorphisms, and `relativeTensorEquiv` in towers.
* `Extension.ContinuousKaehlerDifferential.lift`: the factorization of a derivation that is
  continuous on `F` through `d`.

## Main results

* `TauCeti.LaurentSeries.Extension.derivation_algebraMap` and `derivation_algHom`: `D_L` extends
  `D` and commutes with `F`-algebra homomorphisms.
* `TauCeti.LaurentSeries.Extension.eq_derivation`: `D_L` is the only derivation of `L` extending
  `D`.
* `Extension.ContinuousKaehlerDifferential.map_mk` and `mapAlgHom_mk`: pullbacks are induced by
  maps of algebraic Kähler differentials.
* `Extension.ContinuousKaehlerDifferential.tensorEquiv_tmul` and `relativeTensorEquiv_tmul`: the
  base-change equivalences send `x ⊗ ω` to `x` times the pullback of `ω`.
* `Extension.ContinuousKaehlerDifferential.existsUnique_compDer_eq`: a derivation continuous on
  `F` factors uniquely through `d`.
* `Extension.ContinuousKaehlerDifferential.exists_compDer_eq_iff`: a derivation factors through `d`
  if and only if it is continuous on `F`.

## References

* J. Tate, *Residues of differentials on curves*, Ann. Sci. ÉNS 1 (1968), for the continuous
  differentials of a finite separable extension of a complete discretely valued field.
-/

public section

open HahnSeries TensorProduct
open scoped LaurentSeries

namespace TauCeti.LaurentSeries.Extension

variable (K : Type*) [Field K] (L : Type*) [CommRing L] [Algebra K⸨X⸩ L] [Algebra K L]
  [IsScalarTower K K⸨X⸩ L] [Algebra.FormallyEtale K⸨X⸩ L]

/-! ### The derivation `d/dt` of an étale extension -/

/-- The derivation `D_L = d/dt` of a formally étale `K⸨X⸩`-algebra `L`: the unique extension of the
formal derivative of `K⸨X⸩` (`TauCeti.LaurentSeries.Extension.eq_derivation`). -/
noncomputable def derivation : Derivation K L L :=
  ((Algebra.linearMap K⸨X⸩ L).compDer (laurentSeriesDerivation K)).extendOfFormallyEtale L

variable {K L}

/-- The derivation `D_L` extends the formal derivative of `K⸨X⸩`. -/
@[simp]
theorem derivation_algebraMap (f : K⸨X⸩) :
    derivation K L (algebraMap K⸨X⸩ L f) =
      algebraMap K⸨X⸩ L (laurentSeriesDerivation K f) := by
  simp [derivation]

/-- `D_L t = 1`. -/
theorem derivation_algebraMap_single_one :
    derivation K L (algebraMap K⸨X⸩ L (single 1 1)) = 1 := by
  simp

/-- **Uniqueness of `d/dt`.** The derivation `D_L` is the only `K`-derivation of `L` extending the
formal derivative of `K⸨X⸩`. -/
theorem eq_derivation {δ : Derivation K L L}
    (h : ∀ f : K⸨X⸩, δ (algebraMap K⸨X⸩ L f) = algebraMap K⸨X⸩ L (laurentSeriesDerivation K f)) :
    δ = derivation K L :=
  Derivation.eq_extendOfFormallyEtale _ h

/-- Any `K⸨X⸩`-algebra homomorphism between formally étale `K⸨X⸩`-algebras commutes with `d/dt`. -/
@[simp]
theorem derivation_algHom {M : Type*} [CommRing M] [Algebra K⸨X⸩ M] [Algebra K M]
    [IsScalarTower K K⸨X⸩ M] [Algebra.FormallyEtale K⸨X⸩ M] (φ : M →ₐ[K⸨X⸩] L) (x : M) :
    derivation K L (φ x) = φ (derivation K M x) :=
  ((derivation K M).algHom_apply_of_formallyUnramified φ (fun f ↦ by simp) x).symm

/-- Any `K⸨X⸩`-algebra isomorphism between formally étale `K⸨X⸩`-algebras commutes with `d/dt`. -/
@[simp]
theorem derivation_algEquiv {M : Type*} [CommRing M] [Algebra K⸨X⸩ M] [Algebra K M]
    [IsScalarTower K K⸨X⸩ M] [Algebra.FormallyEtale K⸨X⸩ M] (e : M ≃ₐ[K⸨X⸩] L) (x : M) :
    derivation K L (e x) = e (derivation K M x) :=
  derivation_algHom e.toAlgHom x

/-- In a tower `K⸨X⸩ → M → L` of formally étale `K⸨X⸩`-algebras, `D_L` extends `D_M`. -/
theorem derivation_algebraMap_of_tower (M : Type*) [CommRing M] [Algebra K⸨X⸩ M] [Algebra K M]
    [IsScalarTower K K⸨X⸩ M] [Algebra.FormallyEtale K⸨X⸩ M] [Algebra M L]
    [IsScalarTower K⸨X⸩ M L] (x : M) :
    derivation K L (algebraMap M L x) = algebraMap M L (derivation K M x) :=
  derivation_algHom (IsScalarTower.toAlgHom K⸨X⸩ M L) x

variable (K L) in
/-- The map `x dy ↦ x * D_L y` from the Kähler differentials is surjective: `x dt ↦ x`. -/
theorem derivation_liftKaehlerDifferential_surjective :
    Function.Surjective (derivation K L).liftKaehlerDifferential :=
  fun x ↦ ⟨x • KaehlerDifferential.D K L (algebraMap K⸨X⸩ L (single 1 1)), by
    rw [map_smul, Derivation.liftKaehlerDifferential_comp_D, derivation_algebraMap_single_one,
      smul_eq_mul, mul_one]⟩

/-! ### Continuous one-forms -/

variable (K L) in
/-- The **continuous one-forms** `Ω¹_cont(L/K)` of a formally étale `K⸨X⸩`-algebra `L`: the
quotient of the Kähler differentials `Ω[L⁄K]` by the kernel of the `L`-linear map
`x dy ↦ x * D_L y` induced by the derivation `D_L = d/dt` of `L`. -/
def ContinuousKaehlerDifferential : Type _ :=
  Ω[L⁄K] ⧸ LinearMap.ker (derivation K L).liftKaehlerDifferential

namespace ContinuousKaehlerDifferential

noncomputable instance : AddCommGroup (ContinuousKaehlerDifferential K L) :=
  inferInstanceAs <| AddCommGroup <|
    Ω[L⁄K] ⧸ LinearMap.ker (derivation K L).liftKaehlerDifferential

noncomputable instance : Module L (ContinuousKaehlerDifferential K L) :=
  inferInstanceAs <| Module L <|
    Ω[L⁄K] ⧸ LinearMap.ker (derivation K L).liftKaehlerDifferential

noncomputable instance : Module K⸨X⸩ (ContinuousKaehlerDifferential K L) :=
  inferInstanceAs <| Module K⸨X⸩ <|
    Ω[L⁄K] ⧸ LinearMap.ker (derivation K L).liftKaehlerDifferential

noncomputable instance : Module K (ContinuousKaehlerDifferential K L) :=
  inferInstanceAs <| Module K <|
    Ω[L⁄K] ⧸ LinearMap.ker (derivation K L).liftKaehlerDifferential

instance : IsScalarTower K⸨X⸩ L (ContinuousKaehlerDifferential K L) :=
  inferInstanceAs <| IsScalarTower K⸨X⸩ L <|
    Ω[L⁄K] ⧸ LinearMap.ker (derivation K L).liftKaehlerDifferential

instance : IsScalarTower K L (ContinuousKaehlerDifferential K L) :=
  inferInstanceAs <| IsScalarTower K L <|
    Ω[L⁄K] ⧸ LinearMap.ker (derivation K L).liftKaehlerDifferential

instance : IsScalarTower K K⸨X⸩ (ContinuousKaehlerDifferential K L) :=
  inferInstanceAs <| IsScalarTower K K⸨X⸩ <|
    Ω[L⁄K] ⧸ LinearMap.ker (derivation K L).liftKaehlerDifferential

variable (K L)

/-- The quotient map from the Kähler differentials to the continuous one-forms. -/
noncomputable def mk : Ω[L⁄K] →ₗ[L] ContinuousKaehlerDifferential K L :=
  Submodule.mkQ _

theorem mk_surjective : Function.Surjective (mk K L) :=
  Submodule.mkQ_surjective _

variable {K L} in
/-- A Kähler differential vanishes in `Ω¹_cont(L/K)` exactly when its image `Σ xᵢ * D_L yᵢ` under
the map induced by `D_L` vanishes. -/
theorem mk_eq_zero_iff {ω : Ω[L⁄K]} :
    mk K L ω = 0 ↔ (derivation K L).liftKaehlerDifferential ω = 0 :=
  Submodule.Quotient.mk_eq_zero _

/-- The universal derivation `d : L → Ω¹_cont(L/K)`. -/
noncomputable def D : Derivation K L (ContinuousKaehlerDifferential K L) :=
  (mk K L).compDer (KaehlerDifferential.D K L)

theorem D_apply (x : L) : D K L x = mk K L (KaehlerDifferential.D K L x) :=
  (rfl)

/-- **Continuous one-forms are multiples of `dt`.** The `L`-linear equivalence
`Ω¹_cont(L/K) ≃ L` induced by `D_L`, sending `x dy` to `x * D_L y` and `d t` to `1`. -/
noncomputable def equivSelf : ContinuousKaehlerDifferential K L ≃ₗ[L] L :=
  (derivation K L).liftKaehlerDifferential.quotKerEquivOfSurjective
    (derivation_liftKaehlerDifferential_surjective K L)

variable {K L}

@[simp]
theorem equivSelf_mk (ω : Ω[L⁄K]) :
    equivSelf K L (mk K L ω) = (derivation K L).liftKaehlerDifferential ω :=
  (rfl)

/-- The equivalence sends `d y` to `D_L y`. -/
@[simp]
theorem equivSelf_D (x : L) : equivSelf K L (D K L x) = derivation K L x := by
  simp [D_apply]

/-- The continuous one-form corresponding to `x` is `x dt`. -/
@[simp]
theorem equivSelf_symm_apply (x : L) :
    (equivSelf K L).symm x = x • D K L (algebraMap K⸨X⸩ L (single 1 1)) := by
  rw [LinearEquiv.symm_apply_eq, map_smul, equivSelf_D, derivation_algebraMap_single_one,
    smul_eq_mul, mul_one]

/-- Every continuous one-form is `x dt` for the unique `x = equivSelf K L ω`. -/
theorem equivSelf_smul_D_algebraMap_single_one (ω : ContinuousKaehlerDifferential K L) :
    equivSelf K L ω • D K L (algebraMap K⸨X⸩ L (single 1 1)) = ω := by
  rw [← equivSelf_symm_apply, LinearEquiv.symm_apply_apply]

/-- **`dy = D_L y dt`.** -/
theorem derivation_smul_D_algebraMap_single_one (x : L) :
    derivation K L x • D K L (algebraMap K⸨X⸩ L (single 1 1)) = D K L x := by
  rw [← equivSelf_D, equivSelf_smul_D_algebraMap_single_one]

variable (K L) in
/-- `Ω¹_cont(L/K)` is free of rank one over `L`. -/
theorem finrank_eq_one [Nontrivial L] : Module.finrank L (ContinuousKaehlerDifferential K L) = 1 :=
  (equivSelf K L).finrank_eq.trans (Module.finrank_self L)

/-- Semilinear maps out of `Ω¹_cont(L/K)` agree as soon as they agree on `d t`. -/
@[ext]
theorem hom_ext {S N : Type*} [Semiring S] [AddCommMonoid N] [Module S N] {σ : L →+* S}
    {ℓ ℓ' : ContinuousKaehlerDifferential K L →ₛₗ[σ] N}
    (h : ℓ (D K L (algebraMap K⸨X⸩ L (single 1 1))) = ℓ' (D K L (algebraMap K⸨X⸩ L (single 1 1)))) :
    ℓ = ℓ' := by
  ext ω
  rw [← equivSelf_smul_D_algebraMap_single_one ω, map_smulₛₗ, map_smulₛₗ, h]

/-! ### Comparison with the one-forms of `K⸨X⸩` -/

variable (K L) in
/-- The **pullback of one-forms** `Ω¹_cont(K⸨X⸩/K) → Ω¹_cont(L/K)`, `f dg ↦ f dg`, read through
the rank-one normal forms: it sends `f dt` to `f dt`. It is induced by the map of Kähler
differentials (`TauCeti.LaurentSeries.Extension.ContinuousKaehlerDifferential.map_mk`). -/
noncomputable def map :
    TauCeti.ContinuousKaehlerDifferential K →ₗ[K⸨X⸩] ContinuousKaehlerDifferential K L :=
  (equivSelf K L).symm.toLinearMap.restrictScalars K⸨X⸩ ∘ₗ Algebra.linearMap K⸨X⸩ L ∘ₗ
    (TauCeti.ContinuousKaehlerDifferential.equivLaurentSeries K).toLinearMap

/-- The pullback sends `f dt` to `f dt`. -/
@[simp]
theorem equivSelf_map (ω : TauCeti.ContinuousKaehlerDifferential K) :
    equivSelf K L (map K L ω) =
      algebraMap K⸨X⸩ L (TauCeti.ContinuousKaehlerDifferential.equivLaurentSeries K ω) := by
  simp [map, -equivSelf_symm_apply]

/-- The pullback sends `d g` to `d g`. -/
@[simp]
theorem map_D (g : K⸨X⸩) :
    map K L (TauCeti.ContinuousKaehlerDifferential.D K g) = D K L (algebraMap K⸨X⸩ L g) :=
  (equivSelf K L).injective <| by
    rw [equivSelf_map, equivSelf_D, derivation_algebraMap,
      TauCeti.ContinuousKaehlerDifferential.equivLaurentSeries_D, laurentSeriesDerivation_apply]

/-- The pullback of one-forms is induced by the map `Ω[K⸨X⸩⁄K] → Ω[L⁄K]` of Kähler
differentials. -/
theorem map_mk (ω : Ω[K⸨X⸩⁄K]) :
    map K L (TauCeti.ContinuousKaehlerDifferential.mk K ω) =
      mk K L (KaehlerDifferential.map K K K⸨X⸩ L ω) := by
  have h : map K L ∘ₗ TauCeti.ContinuousKaehlerDifferential.mk K =
      (mk K L).restrictScalars K⸨X⸩ ∘ₗ KaehlerDifferential.map K K K⸨X⸩ L :=
    Derivation.liftKaehlerDifferential_unique _ _ <| Derivation.ext fun g ↦ by
      simpa [← TauCeti.ContinuousKaehlerDifferential.D_apply] using D_apply K L _
  exact congr($h ω)

/-- The pullback of one-forms is injective. -/
theorem map_injective [FaithfulSMul K⸨X⸩ L] : Function.Injective (map K L) := by
  intro ω η h
  apply (TauCeti.ContinuousKaehlerDifferential.equivLaurentSeries K).injective
  simpa using congr(equivSelf K L $h)

variable (K L) in
/-- **`Ω¹_cont(L/K) = L ⊗_F Ω¹_cont(F/K)`.** For a formally étale `F`-algebra `L`, `F = K⸨X⸩`, the
pullback of one-forms extends to an `L`-linear equivalence
`L ⊗_F Ω¹_cont(F/K) ≃ Ω¹_cont(L/K)`, `x ⊗ ω ↦ x ω`
(`TauCeti.LaurentSeries.Extension.ContinuousKaehlerDifferential.tensorEquiv_tmul`). -/
noncomputable def tensorEquiv :
    L ⊗[K⸨X⸩] TauCeti.ContinuousKaehlerDifferential K ≃ₗ[L] ContinuousKaehlerDifferential K L :=
  LinearEquiv.baseChange K⸨X⸩ L _ _
      (TauCeti.ContinuousKaehlerDifferential.equivLaurentSeries K).toLinearEquiv ≪≫ₗ
    AlgebraTensorModule.rid K⸨X⸩ L L ≪≫ₗ (equivSelf K L).symm

/-- The equivalence `L ⊗_F Ω¹_cont(F/K) ≃ Ω¹_cont(L/K)` sends `x ⊗ ω` to `x` times the pullback
of `ω`. -/
@[simp]
theorem tensorEquiv_tmul (x : L) (ω : TauCeti.ContinuousKaehlerDifferential K) :
    tensorEquiv K L (x ⊗ₜ ω) = x • map K L ω := by
  apply (equivSelf K L).injective
  simp [tensorEquiv, LinearEquiv.baseChange, Algebra.smul_def, mul_comm]

/-- The inverse of `tensorEquiv` sends `x` times a pulled-back one-form `ω` to `x ⊗ ω`. -/
theorem tensorEquiv_symm_smul_map (x : L) (ω : TauCeti.ContinuousKaehlerDifferential K) :
    (tensorEquiv K L).symm (x • map K L ω) = x ⊗ₜ ω :=
  (tensorEquiv K L).symm_apply_eq.mpr (tensorEquiv_tmul x ω).symm

/-- The inverse of `tensorEquiv` sends a pulled-back one-form `ω` to `1 ⊗ ω`. -/
@[simp]
theorem tensorEquiv_symm_map (ω : TauCeti.ContinuousKaehlerDifferential K) :
    (tensorEquiv K L).symm (map K L ω) = 1 ⊗ₜ ω := by
  simpa using tensorEquiv_symm_smul_map (1 : L) ω

/-- The equivalence `L ⊗_F Ω¹_cont(F/K) ≃ Ω¹_cont(L/K)` is the `L`-linear lift of `map K L`. -/
theorem toLinearMap_tensorEquiv :
    (tensorEquiv K L).toLinearMap = (map K L).liftBaseChange L :=
  TensorProduct.AlgebraTensorModule.curry_injective <| LinearMap.ext₂ fun x ω ↦ by simp

/-! ### Functoriality and extension towers -/

section Functoriality

variable {M E : Type*} [CommRing M] [Algebra K⸨X⸩ M] [Algebra K M] [IsScalarTower K K⸨X⸩ M]
  [Algebra.FormallyEtale K⸨X⸩ M] [CommRing E] [Algebra K⸨X⸩ E] [Algebra K E]
  [IsScalarTower K K⸨X⸩ E] [Algebra.FormallyEtale K⸨X⸩ E]

/-- **Functoriality of continuous one-forms.** A `K⸨X⸩`-algebra homomorphism `φ : M →ₐ[K⸨X⸩] L`
between formally étale `K⸨X⸩`-algebras induces a `φ`-semilinear pullback
`Ω¹_cont(M/K) → Ω¹_cont(L/K)`, sending `x dt` to `φ x dt` and `d x` to `d (φ x)`. -/
noncomputable def mapAlgHom (φ : M →ₐ[K⸨X⸩] L) :
    ContinuousKaehlerDifferential K M →ₛₗ[φ.toRingHom] ContinuousKaehlerDifferential K L :=
  (equivSelf K L).symm.toLinearMap.comp
    (φ.toRingHom.toSemilinearMap.comp (equivSelf K M).toLinearMap)

/-- In the coordinate `dt`, pullback along `φ` applies `φ` to the coefficient. -/
@[simp]
theorem equivSelf_mapAlgHom (φ : M →ₐ[K⸨X⸩] L) (ω : ContinuousKaehlerDifferential K M) :
    equivSelf K L (mapAlgHom φ ω) = φ (equivSelf K M ω) :=
  (equivSelf K L).apply_symm_apply _

/-- The `φ`-semilinearity law of `mapAlgHom`, stated with `φ` rather than `φ.toRingHom`. -/
@[simp]
theorem mapAlgHom_smul (φ : M →ₐ[K⸨X⸩] L) (x : M) (ω : ContinuousKaehlerDifferential K M) :
    mapAlgHom φ (x • ω) = φ x • mapAlgHom φ ω :=
  (mapAlgHom φ).map_smulₛₗ x ω

/-- Pullback along `φ` commutes with the universal derivations `d`. -/
@[simp]
theorem mapAlgHom_D (φ : M →ₐ[K⸨X⸩] L) (x : M) :
    mapAlgHom φ (D K M x) = D K L (φ x) := by
  apply (equivSelf K L).injective
  rw [equivSelf_mapAlgHom, equivSelf_D, equivSelf_D, derivation_algHom]

/-- Pullback on the continuous quotient is induced by `KaehlerDifferential.mapSemilinear`. -/
@[simp]
theorem mapAlgHom_mk (φ : M →ₐ[K⸨X⸩] L) (ω : Ω[M⁄K]) :
    mapAlgHom φ (mk K M ω) =
      mk K L (KaehlerDifferential.mapSemilinear (φ.restrictScalars K) ω) := by
  -- The two compositions are semilinear over `φ.toRingHom` and `(φ.restrictScalars K).toRingHom`,
  -- so we induct on generators of `Ω[M⁄K]` rather than applying `LinearMap.ext_on`.
  induction (KaehlerDifferential.span_range_derivation K M ▸ Submodule.mem_top :
      ω ∈ Submodule.span M (Set.range (KaehlerDifferential.D K M))) using
      Submodule.span_induction with
  | mem _ hω =>
    obtain ⟨x, rfl⟩ := hω
    rw [← D_apply, mapAlgHom_D, KaehlerDifferential.mapSemilinear_D, D_apply,
      AlgHom.restrictScalars_apply]
  | zero => rw [map_zero, LinearMap.map_zero, LinearMap.map_zero, map_zero]
  | add _ _ _ _ ih₁ ih₂ => rw [map_add, LinearMap.map_add, LinearMap.map_add, map_add, ih₁, ih₂]
  | smul a _ _ ih =>
    rw [map_smul, mapAlgHom_smul, KaehlerDifferential.mapSemilinear_smul, map_smul, ih,
      AlgHom.restrictScalars_apply]

/-- Pullback from `Ω¹_cont(K⸨X⸩/K)` commutes with `mapAlgHom`. -/
@[simp]
theorem mapAlgHom_map (φ : M →ₐ[K⸨X⸩] L) (ω : TauCeti.ContinuousKaehlerDifferential K) :
    mapAlgHom φ (map K M ω) = map K L ω := by
  apply (equivSelf K L).injective
  rw [equivSelf_mapAlgHom, equivSelf_map, equivSelf_map, φ.commutes]

/-- `mapAlgHom φ` is the unique `φ`-semilinear map sending `dt` to `dt`. -/
theorem eq_mapAlgHom_of_apply_D_algebraMap_single_one (φ : M →ₐ[K⸨X⸩] L)
    (ℓ : ContinuousKaehlerDifferential K M →ₛₗ[φ.toRingHom] ContinuousKaehlerDifferential K L)
    (h : ℓ (D K M (algebraMap K⸨X⸩ M (single 1 1))) = D K L (algebraMap K⸨X⸩ L (single 1 1))) :
    ℓ = mapAlgHom φ :=
  hom_ext <| by rw [h, mapAlgHom_D, φ.commutes]

/-- Pullback along an injective `K⸨X⸩`-algebra homomorphism is injective. -/
theorem mapAlgHom_injective (φ : M →ₐ[K⸨X⸩] L) (hφ : Function.Injective φ) :
    Function.Injective (mapAlgHom (K := K) φ) := by
  intro ω η h
  apply (equivSelf K M).injective
  apply hφ
  simpa only [equivSelf_mapAlgHom] using congrArg (equivSelf K L) h

/-- Pullback along the identity `K⸨X⸩`-algebra homomorphism fixes every continuous one-form. -/
@[simp]
theorem mapAlgHom_id (ω : ContinuousKaehlerDifferential K L) :
    mapAlgHom (AlgHom.id K⸨X⸩ L) ω = ω := by
  apply (equivSelf K L).injective
  rw [equivSelf_mapAlgHom, AlgHom.id_apply]

/-- Pullback of continuous one-forms is functorial in `K⸨X⸩`-algebra homomorphisms. -/
theorem mapAlgHom_comp (ψ : L →ₐ[K⸨X⸩] E) (φ : M →ₐ[K⸨X⸩] L)
    (ω : ContinuousKaehlerDifferential K M) :
    mapAlgHom (ψ.comp φ) ω = mapAlgHom ψ (mapAlgHom φ ω) := by
  apply (equivSelf K E).injective
  rw [equivSelf_mapAlgHom, equivSelf_mapAlgHom, equivSelf_mapAlgHom, AlgHom.comp_apply]

attribute [local instance] RingHomInvPair.of_ringEquiv RingHomInvPair.of_ringEquiv_symm

/-- A `K⸨X⸩`-algebra isomorphism `e : M ≃ₐ[K⸨X⸩] L` between formally étale `K⸨X⸩`-algebras induces a
semilinear equivalence of continuous one-forms. -/
noncomputable def mapAlgEquiv (e : M ≃ₐ[K⸨X⸩] L) :
    ContinuousKaehlerDifferential K M
      ≃ₛₗ[(e.toRingEquiv : M →+* L)] ContinuousKaehlerDifferential K L where
  toFun := mapAlgHom e.toAlgHom
  invFun := mapAlgHom e.symm.toAlgHom
  map_add' := map_add _
  map_smul' := (mapAlgHom e.toAlgHom).map_smul'
  left_inv ω := by rw [← mapAlgHom_comp, AlgEquiv.symm_comp, mapAlgHom_id]
  right_inv ω := by rw [← mapAlgHom_comp, AlgEquiv.comp_symm, mapAlgHom_id]

@[simp]
theorem mapAlgEquiv_apply (e : M ≃ₐ[K⸨X⸩] L) (ω : ContinuousKaehlerDifferential K M) :
    mapAlgEquiv e ω = mapAlgHom e.toAlgHom ω :=
  (rfl)

@[simp]
theorem mapAlgEquiv_symm_apply (e : M ≃ₐ[K⸨X⸩] L) (ω : ContinuousKaehlerDifferential K L) :
    (mapAlgEquiv e).symm ω = mapAlgHom e.symm.toAlgHom ω :=
  (rfl)

end Functoriality

/-! ### The universal property -/

section UniversalProperty

variable {M : Type*} [AddCommGroup M] [Module L M] [Module K M] [IsScalarTower K L M]
  [Module K⸨X⸩ M] [IsScalarTower K⸨X⸩ L M] [IsScalarTower K K⸨X⸩ M] [TopologicalSpace M]
  [ContinuousSMul K⸨X⸩ M]

/-- Every derivation factoring through `d` is continuous on `K⸨X⸩` when scalar multiplication by
`K⸨X⸩` on its target is continuous. -/
theorem continuous_compAlgebraMap_compDer (ℓ : ContinuousKaehlerDifferential K L →ₗ[L] M) :
    Continuous ((ℓ.compDer (D K L)).compAlgebraMap K⸨X⸩) := by
  have h : (ℓ.compDer (D K L)).compAlgebraMap K⸨X⸩ =
      (ℓ.restrictScalars K⸨X⸩ ∘ₗ map K L).compDer (TauCeti.ContinuousKaehlerDifferential.D K) :=
    Derivation.ext fun g ↦ by simp
  rw [h]
  exact TauCeti.ContinuousKaehlerDifferential.continuous_compDer _

section Hausdorff

variable [T2Space M]

/-- A `K`-derivation `δ : L → M` into a Hausdorff module that is continuous on `K⸨X⸩` satisfies
`δ y = D_L y • δ t`. -/
theorem apply_eq_derivation_smul (δ : Derivation K L M) (hδ : Continuous (δ.compAlgebraMap K⸨X⸩))
    (x : L) : δ x = derivation K L x • δ (algebraMap K⸨X⸩ L (single 1 1)) := by
  have h : δ = (LinearMap.toSpanSingleton L M (δ (algebraMap K⸨X⸩ L (single 1 1)))).compDer
      (derivation K L) := Derivation.eq_of_formallyUnramified (S := K⸨X⸩) fun f ↦ by
    rw [Derivation.coe_comp, LinearMap.comp_apply, Derivation.coeFn_coe, derivation_algebraMap,
      LinearMap.coe_restrictScalars, LinearMap.toSpanSingleton_apply, algebraMap_smul]
    exact (δ.compAlgebraMap K⸨X⸩).apply_eq_laurentSeriesDerivation_smul hδ f
  exact congr($h x)

/-- For a derivation `δ` continuous on `K⸨X⸩`, the map `Ω[L⁄K] → M` it induces is `λ_L` followed
by `x ↦ x • δ t`, where `λ_L` is the map induced by `D_L`. -/
theorem liftKaehlerDifferential_eq_toSpanSingleton_comp (δ : Derivation K L M)
    (hδ : Continuous (δ.compAlgebraMap K⸨X⸩)) :
    δ.liftKaehlerDifferential = LinearMap.toSpanSingleton L M
      (δ (algebraMap K⸨X⸩ L (single 1 1))) ∘ₗ (derivation K L).liftKaehlerDifferential := by
  ext x
  simp [apply_eq_derivation_smul δ hδ x]

/-- **The factorization of a derivation through `d`.** A `K`-derivation `δ : L → M` that is
continuous on `K⸨X⸩` factors through `Ω¹_cont(L/K)`, by the `L`-linear map induced by its Kähler
lift. -/
noncomputable def lift (δ : Derivation K L M) (hδ : Continuous (δ.compAlgebraMap K⸨X⸩)) :
    ContinuousKaehlerDifferential K L →ₗ[L] M :=
  Submodule.liftQ _ δ.liftKaehlerDifferential fun ω hω ↦ by
    rw [LinearMap.mem_ker, liftKaehlerDifferential_eq_toSpanSingleton_comp δ hδ,
      LinearMap.comp_apply, LinearMap.mem_ker.mp hω, map_zero]

@[simp]
theorem lift_mk (δ : Derivation K L M) (hδ : Continuous (δ.compAlgebraMap K⸨X⸩)) (ω : Ω[L⁄K]) :
    lift δ hδ (mk K L ω) = δ.liftKaehlerDifferential ω :=
  (rfl)

@[simp]
theorem lift_D (δ : Derivation K L M) (hδ : Continuous (δ.compAlgebraMap K⸨X⸩)) (x : L) :
    lift δ hδ (D K L x) = δ x := by
  simp [D_apply]

/-- The factorization of `δ` through `d` recovers `δ`. -/
theorem compDer_lift (δ : Derivation K L M) (hδ : Continuous (δ.compAlgebraMap K⸨X⸩)) :
    (lift δ hδ).compDer (D K L) = δ :=
  Derivation.ext (lift_D δ hδ)

/-- The factorization of `δ` through `d` is unique. -/
theorem lift_unique (δ : Derivation K L M) (hδ : Continuous (δ.compAlgebraMap K⸨X⸩))
    (ℓ : ContinuousKaehlerDifferential K L →ₗ[L] M) (h : ℓ.compDer (D K L) = δ) :
    ℓ = lift δ hδ :=
  hom_ext <| by rw [lift_D, ← h]; simp

/-- **Universal property of the continuous one-forms.** Every `K`-derivation of `L` into a
Hausdorff module that is continuous on `K⸨X⸩` factors uniquely through `d` by an `L`-linear
map. -/
theorem existsUnique_compDer_eq (δ : Derivation K L M) (hδ : Continuous (δ.compAlgebraMap K⸨X⸩)) :
    ∃! ℓ : ContinuousKaehlerDifferential K L →ₗ[L] M, ℓ.compDer (D K L) = δ :=
  ⟨lift δ hδ, compDer_lift δ hδ, fun ℓ h ↦ lift_unique δ hδ ℓ h⟩

/-- A `K`-derivation of `L` into a Hausdorff module factors through `d` if and only if it is
continuous on `K⸨X⸩`. -/
theorem exists_compDer_eq_iff (δ : Derivation K L M) :
    (∃ ℓ : ContinuousKaehlerDifferential K L →ₗ[L] M, ℓ.compDer (D K L) = δ) ↔
      Continuous (δ.compAlgebraMap K⸨X⸩) :=
  ⟨fun ⟨ℓ, h⟩ ↦ h ▸ continuous_compAlgebraMap_compDer ℓ, fun hδ ↦ ⟨lift δ hδ, compDer_lift δ hδ⟩⟩

end Hausdorff

end UniversalProperty

/-! ### Module topology -/

section Topology

variable [TopologicalSpace L]

/-- When `L` carries a topology, `Ω¹_cont(L/K)` carries the `L`-module topology. -/
noncomputable instance : TopologicalSpace (ContinuousKaehlerDifferential K L) :=
  moduleTopology L _

instance : IsModuleTopology L (ContinuousKaehlerDifferential K L) := ⟨rfl⟩

instance : IsTopologicalAddGroup (ContinuousKaehlerDifferential K L) :=
  IsModuleTopology.isTopologicalAddGroup L _

/-- Pullback along a continuous `K⸨X⸩`-algebra homomorphism is continuous for the module topologies
on continuous one-forms. -/
@[fun_prop]
theorem continuous_mapAlgHom {M : Type*} [CommRing M] [Algebra K⸨X⸩ M] [Algebra K M]
    [IsScalarTower K K⸨X⸩ M] [Algebra.FormallyEtale K⸨X⸩ M] [TopologicalSpace M]
    (φ : M →ₐ[K⸨X⸩] L) (hφ : Continuous φ) :
    Continuous (mapAlgHom (K := K) φ) :=
  IsModuleTopology.continuous_of_linearMapₛₗ hφ (mapAlgHom φ)

section TopologicalSemiring

variable [IsTopologicalSemiring L]

variable (K L) in
/-- When `L` is a topological semiring, `Ω¹_cont(L/K) ≃ L` is a continuous `L`-linear equivalence
for the module topology on `Ω¹_cont(L/K)`. -/
noncomputable def continuousEquivSelf : ContinuousKaehlerDifferential K L ≃L[L] L :=
  (equivSelf K L).toContinuousLinearEquivOfIsModuleTopology

@[simp]
theorem continuousEquivSelf_apply (ω : ContinuousKaehlerDifferential K L) :
    continuousEquivSelf K L ω = equivSelf K L ω := by
  simp [continuousEquivSelf]

@[simp]
theorem continuousEquivSelf_symm_apply (x : L) :
    (continuousEquivSelf K L).symm x = (equivSelf K L).symm x := by
  simp [continuousEquivSelf]

@[simp]
theorem toLinearEquiv_continuousEquivSelf :
    (continuousEquivSelf K L).toLinearEquiv = equivSelf K L := by
  simp [continuousEquivSelf]

instance [T2Space L] : T2Space (ContinuousKaehlerDifferential K L) :=
  (continuousEquivSelf K L).toHomeomorph.isEmbedding.t2Space

/-- The universal derivation `d : L → Ω¹_cont(L/K)` is continuous if and only if `D_L : L → L` is
continuous. -/
theorem continuous_D_iff : Continuous (D K L) ↔ Continuous (derivation K L) := by
  constructor
  · intro h
    simpa only [Function.comp_def, continuousEquivSelf_apply, equivSelf_D] using
      (continuousEquivSelf K L).continuous.comp h
  · intro h
    exact (continuousEquivSelf K L).toHomeomorph.comp_continuous_iff.mp <| by
      simpa only [ContinuousLinearEquiv.coe_toHomeomorph, Function.comp_def,
        continuousEquivSelf_apply, equivSelf_D] using h

/-- Every `L`-linear map out of `Ω¹_cont(L/K)` into a module with continuous `L`-scalar
multiplication is continuous, without assuming continuity of addition on the target. -/
@[fun_prop]
theorem continuous_of_linearMap {N : Type*} [AddCommMonoid N] [Module L N]
    [TopologicalSpace N] [ContinuousSMul L N]
    (ℓ : ContinuousKaehlerDifferential K L →ₗ[L] N) : Continuous ℓ :=
  ((continuousEquivSelf K L).continuous.fun_smul continuous_const).congr fun ω ↦ by
    simpa only [map_smul, continuousEquivSelf_apply] using
      congrArg ℓ (equivSelf_smul_D_algebraMap_single_one ω)

/-- When `L`-scalar multiplication on `N` is continuous, the factorization `lift δ hδ` of a
derivation `δ : L → N` through `d` is continuous. -/
theorem continuous_lift {N : Type*} [AddCommGroup N] [Module L N] [Module K N]
    [IsScalarTower K L N] [Module K⸨X⸩ N] [IsScalarTower K⸨X⸩ L N] [IsScalarTower K K⸨X⸩ N]
    [TopologicalSpace N] [ContinuousSMul K⸨X⸩ N] [ContinuousSMul L N] [T2Space N]
    (δ : Derivation K L N) (hδ : Continuous (δ.compAlgebraMap K⸨X⸩)) :
    Continuous (lift δ hδ) :=
  continuous_of_linearMap _

/-- When `K⸨X⸩` acts continuously on `L`, the pullback `Ω¹_cont(K⸨X⸩/K) → Ω¹_cont(L/K)` is
continuous. -/
theorem continuous_map [ContinuousSMul K⸨X⸩ L] : Continuous (map K L) := by
  have halg : Continuous (algebraMap K⸨X⸩ L) :=
    (continuous_id.smul (continuous_const (y := (1 : L)))).congr fun f ↦
      (Algebra.algebraMap_eq_smul_one f).symm
  exact ((continuousEquivSelf K L).symm.continuous.comp
    (halg.comp (TauCeti.ContinuousKaehlerDifferential.equivLaurentSeries K).continuous)).congr
      fun ω ↦ by simp [map, -equivSelf_symm_apply]

end TopologicalSemiring

/-- When `L` is a finite `K⸨X⸩`-algebra carrying the `K⸨X⸩`-module topology, `Ω¹_cont(L/K)` also
carries the `K⸨X⸩`-module topology. -/
instance [Module.Finite K⸨X⸩ L] [IsModuleTopology K⸨X⸩ L] :
    IsModuleTopology K⸨X⸩ (ContinuousKaehlerDifferential K L) :=
  IsModuleTopology.restrictScalars K⸨X⸩ L _

end Topology

end ContinuousKaehlerDifferential

end TauCeti.LaurentSeries.Extension

namespace TauCeti.LaurentSeries.Extension.ContinuousKaehlerDifferential

section Tower

variable (K M L : Type*) [Field K] [CommRing M] [CommRing L]
  [Algebra K⸨X⸩ M] [Algebra K M] [IsScalarTower K K⸨X⸩ M] [Algebra.FormallyEtale K⸨X⸩ M]
  [Algebra K⸨X⸩ L] [Algebra K L] [IsScalarTower K K⸨X⸩ L] [Algebra.FormallyEtale K⸨X⸩ L]
  [Algebra M L] [IsScalarTower K⸨X⸩ M L]

/-- **Relative base change of continuous one-forms in a tower.** For a tower `K⸨X⸩ → M → L` of
formally étale `K⸨X⸩`-algebras, `L ⊗_M Ω¹_cont(M/K) ≃ Ω¹_cont(L/K)` as `L`-modules, sending
`x ⊗ ω` to `x` times the pullback of `ω` along `M → L`. -/
noncomputable def relativeTensorEquiv :
    L ⊗[M] ContinuousKaehlerDifferential K M ≃ₗ[L] ContinuousKaehlerDifferential K L :=
  LinearEquiv.baseChange M L _ _ (equivSelf K M) ≪≫ₗ
    AlgebraTensorModule.rid M L L ≪≫ₗ (equivSelf K L).symm

variable {K M L}

/-- `relativeTensorEquiv` sends `x ⊗ ω` to `x` times the pullback of `ω` along `M → L`. -/
@[simp]
theorem relativeTensorEquiv_tmul (x : L) (ω : ContinuousKaehlerDifferential K M) :
    relativeTensorEquiv K M L (x ⊗ₜ ω) = x • mapAlgHom (IsScalarTower.toAlgHom K⸨X⸩ M L) ω := by
  apply (equivSelf K L).injective
  rw [map_smul, equivSelf_mapAlgHom, IsScalarTower.coe_toAlgHom', smul_eq_mul]
  simp [relativeTensorEquiv, LinearEquiv.baseChange, Algebra.smul_def, mul_comm]

/-- The inverse of `relativeTensorEquiv` sends `x` times the pullback of `ω` to `x ⊗ ω`. -/
theorem relativeTensorEquiv_symm_smul_mapAlgHom (x : L) (ω : ContinuousKaehlerDifferential K M) :
    (relativeTensorEquiv K M L).symm (x • mapAlgHom (IsScalarTower.toAlgHom K⸨X⸩ M L) ω) =
      x ⊗ₜ ω :=
  (relativeTensorEquiv K M L).symm_apply_eq.mpr (relativeTensorEquiv_tmul x ω).symm

/-- The inverse of `relativeTensorEquiv` sends the pullback of `ω` along `M → L` to `1 ⊗ ω`. -/
@[simp]
theorem relativeTensorEquiv_symm_mapAlgHom (ω : ContinuousKaehlerDifferential K M) :
    (relativeTensorEquiv K M L).symm (mapAlgHom (IsScalarTower.toAlgHom K⸨X⸩ M L) ω) =
      1 ⊗ₜ ω := by
  simpa using relativeTensorEquiv_symm_smul_mapAlgHom (1 : L) ω

end Tower

end TauCeti.LaurentSeries.Extension.ContinuousKaehlerDifferential
