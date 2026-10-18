/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Kaehler.Basic
public import Mathlib.Topology.Algebra.Module.ModuleTopology
public import TauCeti.RingTheory.LaurentSeries.ContinuousDerivation

/-!
# Continuous Kähler differentials of formal Laurent series

Let `K` be a field and `F = K⸨X⸩`, with the valuation topology, and let `D` be the formal
derivative `TauCeti.laurentSeriesDerivation K`. The algebraic Kähler differentials `Ω[F⁄K]` do
not see the topology of `F`; in characteristic zero they are much larger than `F`, since `F` has
infinite transcendence degree over `K(X)`. The module of continuous differentials `Ω¹_cont(F/K)`
is the quotient of `Ω[F⁄K]` by the kernel of the map `λ : Ω[F⁄K] → F`, `f dg ↦ f * D g`,
induced by `D` through the universal property of Kähler differentials.

This file constructs `Ω¹_cont(F/K)` as `TauCeti.ContinuousKaehlerDifferential K`, together with
its universal derivation `d = TauCeti.ContinuousKaehlerDifferential.D K`, and shows:

* `λ` induces an `F`-linear equivalence `Ω¹_cont(F/K) ≃ F` sending `dX` to `1`, so every
  continuous one-form is uniquely `f dX`.
* `Ω¹_cont(F/K)` carries the module topology over `F`, for which this equivalence is a
  homeomorphism; thus it is the valuation topology of `F` transported along it, and `d` is
  continuous.
* For every `F`-module `M` with its module topology, a `K`-derivation `δ : F → M` is continuous
  if and only if `δ f = D f • δ X` for all `f`, and then it factors uniquely as `ℓ ∘ d` with
  `ℓ : Ω¹_cont(F/K) → M` an `F`-linear map, which is automatically continuous. Conversely every
  `ℓ ∘ d` is continuous. So `d` is the universal continuous derivation.

The classification of such derivations is
`Derivation.continuous_iff_exists_apply_eq_laurentSeriesDerivation_smul`, from
`LaurentSeries.ContinuousDerivation`.

## Main definitions

* `TauCeti.ContinuousKaehlerDifferential K`: the continuous Kähler differentials `Ω¹_cont(F/K)`.
* `TauCeti.ContinuousKaehlerDifferential.D K`: the universal continuous derivation `d`.
* `TauCeti.ContinuousKaehlerDifferential.equivLaurentSeries K`: the continuous `F`-linear
  equivalence `Ω¹_cont(F/K) ≃ F` sending `d X` to `1`.
* `TauCeti.ContinuousKaehlerDifferential.lift`: the factorization of a continuous derivation
  through `d`.

## Main results

* `TauCeti.ContinuousKaehlerDifferential.continuous_D`: the universal derivation is continuous.
* `TauCeti.ContinuousKaehlerDifferential.existsUnique_compDer_eq`: every continuous derivation
  factors uniquely through `d`.
-/

public section

open HahnSeries
open scoped LaurentSeries

namespace TauCeti

variable (K : Type*) [Field K]

/-- The map `f dg ↦ f * D g` from the Kähler differentials is surjective: `f dX ↦ f`. -/
theorem laurentSeriesDerivation_liftKaehlerDifferential_surjective :
    Function.Surjective (laurentSeriesDerivation K).liftKaehlerDifferential :=
  fun f ↦ ⟨f • KaehlerDifferential.D K K⸨X⸩ (single 1 1), by simp⟩

/-- The **continuous Kähler differentials** `Ω¹_cont(K⸨X⸩/K)`: the quotient of the Kähler
differentials `Ω[K⸨X⸩⁄K]` by the kernel of the `K⸨X⸩`-linear map `f dg ↦ f * D g` induced by the
formal derivative `D`. -/
def ContinuousKaehlerDifferential : Type _ :=
  Ω[K⸨X⸩⁄K] ⧸ LinearMap.ker (laurentSeriesDerivation K).liftKaehlerDifferential

namespace ContinuousKaehlerDifferential

noncomputable instance : AddCommGroup (ContinuousKaehlerDifferential K) :=
  inferInstanceAs <| AddCommGroup <|
    Ω[K⸨X⸩⁄K] ⧸ LinearMap.ker (laurentSeriesDerivation K).liftKaehlerDifferential

noncomputable instance : Module K⸨X⸩ (ContinuousKaehlerDifferential K) :=
  inferInstanceAs <| Module K⸨X⸩ <|
    Ω[K⸨X⸩⁄K] ⧸ LinearMap.ker (laurentSeriesDerivation K).liftKaehlerDifferential

/-- The `K`-module structure on `Ω¹_cont(K⸨X⸩/K)` restricted from its `K⸨X⸩`-module structure. -/
noncomputable instance : Module K (ContinuousKaehlerDifferential K) :=
  Module.compHom _ (algebraMap K K⸨X⸩)

instance : IsScalarTower K K⸨X⸩ (ContinuousKaehlerDifferential K) :=
  -- `c • ω` is `algebraMap K K⸨X⸩ c • ω` by definition of the restricted action.
  ⟨fun c f ω ↦ by rw [← laurentSeries_algebraMap_mul_eq_smul, mul_smul]; rfl⟩

/-- `Ω¹_cont(K⸨X⸩/K)` carries the module topology over `K⸨X⸩`. By
`TauCeti.ContinuousKaehlerDifferential.equivLaurentSeries` this is the valuation topology of
`K⸨X⸩` transported to the differentials. -/
noncomputable instance : TopologicalSpace (ContinuousKaehlerDifferential K) :=
  moduleTopology K⸨X⸩ _

instance : IsModuleTopology K⸨X⸩ (ContinuousKaehlerDifferential K) := ⟨rfl⟩

instance : IsTopologicalAddGroup (ContinuousKaehlerDifferential K) :=
  IsModuleTopology.isTopologicalAddGroup K⸨X⸩ _

/-- The quotient map from the Kähler differentials to the continuous differentials. -/
noncomputable def mk : Ω[K⸨X⸩⁄K] →ₗ[K⸨X⸩] ContinuousKaehlerDifferential K :=
  Submodule.mkQ _

theorem mk_surjective : Function.Surjective (mk K) :=
  Submodule.mkQ_surjective _

/-- A Kähler differential vanishes in `Ω¹_cont(K⸨X⸩/K)` exactly when its image `Σ fᵢ * D gᵢ`
under the map induced by the formal derivative vanishes. -/
theorem mk_eq_zero_iff {ω : Ω[K⸨X⸩⁄K]} :
    mk K ω = 0 ↔ (laurentSeriesDerivation K).liftKaehlerDifferential ω = 0 :=
  Submodule.Quotient.mk_eq_zero _

/-- The universal continuous derivation `d : K⸨X⸩ → Ω¹_cont(K⸨X⸩/K)`. -/
noncomputable def D : Derivation K K⸨X⸩ (ContinuousKaehlerDifferential K) :=
  (mk K).compDer (KaehlerDifferential.D K K⸨X⸩)

theorem D_apply (f : K⸨X⸩) : D K f = mk K (KaehlerDifferential.D K K⸨X⸩ f) :=
  (rfl)

/-- **Continuous one-forms are multiples of `dX`.** The equivalence `Ω¹_cont(K⸨X⸩/K) ≃ K⸨X⸩`
induced by the formal derivative, sending `f dg` to `f * D g` and `d X` to `1`. It is a
homeomorphism for the module topology on the differentials and the valuation topology on
`K⸨X⸩`. -/
noncomputable def equivLaurentSeries :
    ContinuousKaehlerDifferential K ≃L[K⸨X⸩] K⸨X⸩ :=
  let e : ContinuousKaehlerDifferential K ≃ₗ[K⸨X⸩] K⸨X⸩ :=
    (laurentSeriesDerivation K).liftKaehlerDifferential.quotKerEquivOfSurjective
      (laurentSeriesDerivation_liftKaehlerDifferential_surjective K)
  { e with
    continuous_toFun := IsModuleTopology.continuous_of_linearMap e.toLinearMap
    continuous_invFun := IsModuleTopology.continuous_of_linearMap e.symm.toLinearMap }

@[simp]
theorem equivLaurentSeries_mk (ω : Ω[K⸨X⸩⁄K]) :
    equivLaurentSeries K (mk K ω) = (laurentSeriesDerivation K).liftKaehlerDifferential ω :=
  (rfl)

/-- The equivalence sends `d f` to the formal derivative of `f`. -/
@[simp]
theorem equivLaurentSeries_D (f : K⸨X⸩) :
    equivLaurentSeries K (D K f) = LaurentSeries.derivative K f := by
  simp [D_apply]

/-- The equivalence sends the differential `d X` of the parameter to `1`. -/
theorem equivLaurentSeries_D_single_one : equivLaurentSeries K (D K (single 1 1)) = 1 := by
  simp

/-- The continuous one-form corresponding to `f` is `f d X`. -/
@[simp]
theorem equivLaurentSeries_symm_apply (f : K⸨X⸩) :
    (equivLaurentSeries K).symm f = f • D K (single 1 1) := by
  rw [ContinuousLinearEquiv.symm_apply_eq, map_smul, equivLaurentSeries_D_single_one, smul_eq_mul,
    mul_one]

/-- Every continuous one-form is `f d X` for the unique `f = equivLaurentSeries K ω`. -/
theorem equivLaurentSeries_smul_D_single_one (ω : ContinuousKaehlerDifferential K) :
    equivLaurentSeries K ω • D K (single 1 1) = ω := by
  rw [← equivLaurentSeries_symm_apply, ContinuousLinearEquiv.symm_apply_apply]

/-- `Ω¹_cont(K⸨X⸩/K)` has rank one over `K⸨X⸩`. -/
theorem finrank_eq_one : Module.finrank K⸨X⸩ (ContinuousKaehlerDifferential K) = 1 :=
  (equivLaurentSeries K).toLinearEquiv.finrank_eq.trans (Module.finrank_self _)

/-- The universal derivation `d` is continuous. -/
theorem continuous_D : Continuous (D K) :=
  (Derivation.continuous_iff_exists_apply_eq_laurentSeriesDerivation_smul.mpr
    ⟨D K (single 1 1), fun f ↦ by
      rw [laurentSeriesDerivation_apply, ← equivLaurentSeries_D,
        equivLaurentSeries_smul_D_single_one]⟩)

variable {K}

/-- Linear maps out of `Ω¹_cont(K⸨X⸩/K)` agree as soon as they agree on `d X`. -/
@[ext]
theorem hom_ext {N : Type*} [AddCommGroup N] [Module K⸨X⸩ N]
    {ℓ ℓ' : ContinuousKaehlerDifferential K →ₗ[K⸨X⸩] N}
    (h : ℓ (D K (single 1 1)) = ℓ' (D K (single 1 1))) : ℓ = ℓ' := by
  ext ω
  rw [← equivLaurentSeries_smul_D_single_one K ω, map_smul, map_smul, h]

variable {M : Type*} [AddCommGroup M] [Module K⸨X⸩ M] [Module K M]
  [IsScalarTower K K⸨X⸩ M] [TopologicalSpace M] [IsModuleTopology K⸨X⸩ M]

/-- For a continuous derivation `δ`, the map `Ω[K⸨X⸩⁄K] → M` it induces is `λ` followed by
`f ↦ f • δ X`, where `λ` is the map induced by the formal derivative. -/
theorem _root_.Derivation.liftKaehlerDifferential_eq_toSpanSingleton_comp
    (δ : Derivation K K⸨X⸩ M) (hδ : Continuous δ) :
    δ.liftKaehlerDifferential = LinearMap.toSpanSingleton K⸨X⸩ M (δ (single 1 1)) ∘ₗ
      (laurentSeriesDerivation K).liftKaehlerDifferential := by
  ext f
  simp [δ.apply_eq_laurentSeriesDerivation_smul hδ f]

/-- **The factorization of a continuous derivation through `d`.** A continuous `K`-derivation
`δ : K⸨X⸩ → M` factors through `Ω¹_cont(K⸨X⸩/K)`, by the `K⸨X⸩`-linear map induced by its
Kähler lift. -/
noncomputable def lift (δ : Derivation K K⸨X⸩ M) (hδ : Continuous δ) :
    ContinuousKaehlerDifferential K →ₗ[K⸨X⸩] M :=
  Submodule.liftQ _ δ.liftKaehlerDifferential fun ω hω ↦ by
    rw [LinearMap.mem_ker, δ.liftKaehlerDifferential_eq_toSpanSingleton_comp hδ,
      LinearMap.comp_apply, LinearMap.mem_ker.mp hω, map_zero]

@[simp]
theorem lift_mk (δ : Derivation K K⸨X⸩ M) (hδ : Continuous δ) (ω : Ω[K⸨X⸩⁄K]) :
    lift δ hδ (mk K ω) = δ.liftKaehlerDifferential ω :=
  (rfl)

@[simp]
theorem lift_D (δ : Derivation K K⸨X⸩ M) (hδ : Continuous δ) (f : K⸨X⸩) :
    lift δ hδ (D K f) = δ f := by
  simp [D_apply]

theorem compDer_lift (δ : Derivation K K⸨X⸩ M) (hδ : Continuous δ) :
    (lift δ hδ).compDer (D K) = δ :=
  Derivation.ext (lift_D δ hδ)

/-- The factorization of a continuous derivation is continuous. -/
theorem continuous_lift (δ : Derivation K K⸨X⸩ M) (hδ : Continuous δ) :
    Continuous (lift δ hδ) :=
  have := IsModuleTopology.toContinuousAdd K⸨X⸩ M
  IsModuleTopology.continuous_of_linearMap _

/-- The factorization of `δ` through `d` is unique. -/
theorem lift_unique (δ : Derivation K K⸨X⸩ M) (hδ : Continuous δ)
    (ℓ : ContinuousKaehlerDifferential K →ₗ[K⸨X⸩] M) (h : ℓ.compDer (D K) = δ) :
    ℓ = lift δ hδ :=
  hom_ext <| by rw [lift_D, ← h]; simp

/-- **Universal property of continuous differentials.** Every continuous `K`-derivation of
`K⸨X⸩` into a module with its module topology factors uniquely through `d` by a
`K⸨X⸩`-linear map. -/
theorem existsUnique_compDer_eq (δ : Derivation K K⸨X⸩ M) (hδ : Continuous δ) :
    ∃! ℓ : ContinuousKaehlerDifferential K →ₗ[K⸨X⸩] M, ℓ.compDer (D K) = δ :=
  ⟨lift δ hδ, compDer_lift δ hδ, fun ℓ h ↦ lift_unique δ hδ ℓ h⟩

/-- Conversely, every derivation factoring through `d` is continuous. -/
theorem continuous_compDer (ℓ : ContinuousKaehlerDifferential K →ₗ[K⸨X⸩] M) :
    Continuous (ℓ.compDer (D K)) :=
  have := IsModuleTopology.toContinuousAdd K⸨X⸩ M
  (IsModuleTopology.continuous_of_linearMap ℓ).comp (continuous_D K)

end ContinuousKaehlerDifferential

end TauCeti
