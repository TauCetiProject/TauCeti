/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.LaurentSeries.KaehlerDifferential.Basic
public import TauCeti.RingTheory.LaurentSeries.Puiseux.ContinuousDerivation

/-!
# Continuous Kähler differentials of Puiseux series

Let `K` be a field of characteristic zero and `P = puiseuxField K`, with its valuation topology
and the derivative `D = d/dt` of `TauCeti.puiseuxField.derivation K`. As for `K⸨X⸩` in
`TauCeti.ContinuousKaehlerDifferential`, the module of continuous one-forms `Ω¹_cont(P/K)` is
the quotient of the Kähler differentials `Ω[P⁄K]` by the kernel of the map `f dg ↦ f * D g`
induced by `D`. This file constructs it as `TauCeti.puiseuxField.ContinuousKaehlerDifferential K`
and shows, using the classification `Derivation.apply_eq_puiseuxFieldDerivation_smul` of continuous
derivations of `P`:

* `Ω¹_cont(P/K)` is free of rank one on `dt`, through a homeomorphic `P`-linear equivalence with
  `P` sending `dt` to `1`, and its universal derivation `d` is the universal continuous
  derivation of `P`.
* Each level `K⸨u⸩` has its own continuous one-forms `Ω¹_cont(K⸨u⸩/K)`, the module
  `TauCeti.ContinuousKaehlerDifferential K` in the variable `u`. They map to `Ω¹_cont(P/K)` by
  `f du ↦ f (t ^ (1 / n)) d(t ^ (1 / n))`, semilinearly over the level embedding, compatibly with
  `d`. For `n ∣ m` the transition map from level `n` to level `m` is the substitution
  `u_n ↦ u_m ^ (m / n)` into one-forms, and the level maps are compatible with it. Every
  continuous one-form on `P` comes from some level.

## Main definitions

* `TauCeti.puiseuxField.ContinuousKaehlerDifferential K`: the continuous Kähler differentials
  `Ω¹_cont(P/K)`.
* `TauCeti.puiseuxField.ContinuousKaehlerDifferential.D K`: the universal continuous derivation.
* `TauCeti.puiseuxField.ContinuousKaehlerDifferential.equivPuiseuxField K`: the continuous
  `P`-linear equivalence `Ω¹_cont(P/K) ≃ P` sending `dt` to `1`.
* `TauCeti.puiseuxField.ContinuousKaehlerDifferential.lift`: the factorization of a continuous
  derivation through `d`.
* `TauCeti.puiseuxField.ContinuousKaehlerDifferential.levelMap K n`: the map from the continuous
  one-forms of level `n` to those of `P`.

## Main results

* `TauCeti.puiseuxField.ContinuousKaehlerDifferential.existsUnique_compDer_eq`: every continuous
  derivation factors uniquely through `d`.
* `TauCeti.puiseuxField.ContinuousKaehlerDifferential.levelMap_D`: the level maps commute with
  `d`.
* `TauCeti.puiseuxField.ContinuousKaehlerDifferential.levelMap_subst_X_pow`: the level maps are
  compatible with the transition maps.
* `TauCeti.puiseuxField.ContinuousKaehlerDifferential.exists_levelMap_eq`: every continuous
  one-form on `P` comes from some level.
-/

public section

open HahnSeries
open scoped LaurentSeries

namespace TauCeti

namespace puiseuxField

variable {K : Type*} [Field K] [CharZero K]

/-! ### Continuous one-forms -/

/-- The map `f dg ↦ f * dg/dt` from the Kähler differentials is surjective: `f dt ↦ f`. -/
theorem derivation_liftKaehlerDifferential_surjective :
    Function.Surjective (derivation K).liftKaehlerDifferential :=
  fun x ↦ ⟨x • KaehlerDifferential.D K (puiseuxField K) (single K 1 1), by
    rw [map_smul, Derivation.liftKaehlerDifferential_comp_D, derivation_single_one, smul_eq_mul,
      mul_one]⟩

variable (K) in
/-- The **continuous Kähler differentials** `Ω¹_cont(P/K)` of the Puiseux field `P`: the quotient
of the Kähler differentials `Ω[P⁄K]` by the kernel of the `P`-linear map `f dg ↦ f * dg/dt`
induced by the derivative `d/dt`. -/
def ContinuousKaehlerDifferential : Type _ :=
  Ω[puiseuxField K⁄K] ⧸ LinearMap.ker (derivation K).liftKaehlerDifferential

namespace ContinuousKaehlerDifferential

noncomputable instance : AddCommGroup (ContinuousKaehlerDifferential K) :=
  inferInstanceAs <| AddCommGroup <|
    Ω[puiseuxField K⁄K] ⧸ LinearMap.ker (derivation K).liftKaehlerDifferential

noncomputable instance : Module (puiseuxField K) (ContinuousKaehlerDifferential K) :=
  inferInstanceAs <| Module (puiseuxField K) <|
    Ω[puiseuxField K⁄K] ⧸ LinearMap.ker (derivation K).liftKaehlerDifferential

/-- The `K`-module structure on `Ω¹_cont(P/K)` restricted from its `P`-module structure. -/
noncomputable instance : Module K (ContinuousKaehlerDifferential K) :=
  Module.compHom _ (algebraMap K (puiseuxField K))

instance : IsScalarTower K (puiseuxField K) (ContinuousKaehlerDifferential K) :=
  -- `c • ω` is `algebraMap K P c • ω` by definition of the restricted action.
  ⟨fun c x ω ↦ by rw [Algebra.smul_def, mul_smul]; rfl⟩

/-- `Ω¹_cont(P/K)` carries the module topology over the Puiseux field `P`. By
`TauCeti.puiseuxField.ContinuousKaehlerDifferential.equivPuiseuxField` this is the valuation
topology of `P` transported to the differentials. -/
noncomputable instance : TopologicalSpace (ContinuousKaehlerDifferential K) :=
  moduleTopology (puiseuxField K) _

instance : IsModuleTopology (puiseuxField K) (ContinuousKaehlerDifferential K) := ⟨rfl⟩

instance : IsTopologicalAddGroup (ContinuousKaehlerDifferential K) :=
  IsModuleTopology.isTopologicalAddGroup (puiseuxField K) _

variable (K) in
/-- The quotient map from the Kähler differentials to the continuous differentials. -/
noncomputable def mk : Ω[puiseuxField K⁄K] →ₗ[puiseuxField K] ContinuousKaehlerDifferential K :=
  Submodule.mkQ _

variable (K) in
theorem mk_surjective : Function.Surjective (mk K) :=
  Submodule.mkQ_surjective _

/-- A Kähler differential vanishes in `Ω¹_cont(P/K)` exactly when its image `Σ fᵢ * dgᵢ/dt`
under the map induced by the derivative vanishes. -/
theorem mk_eq_zero_iff {ω : Ω[puiseuxField K⁄K]} :
    mk K ω = 0 ↔ (derivation K).liftKaehlerDifferential ω = 0 :=
  Submodule.Quotient.mk_eq_zero _

variable (K) in
/-- The universal continuous derivation `d : P → Ω¹_cont(P/K)`. -/
noncomputable def D : Derivation K (puiseuxField K) (ContinuousKaehlerDifferential K) :=
  (mk K).compDer (KaehlerDifferential.D K (puiseuxField K))

theorem D_apply (x : puiseuxField K) : D K x = mk K (KaehlerDifferential.D K _ x) :=
  (rfl)

variable (K) in
/-- **Continuous one-forms are multiples of `dt`.** The equivalence `Ω¹_cont(P/K) ≃ P` induced
by the derivative, sending `f dg` to `f * dg/dt` and `dt` to `1`. It is a homeomorphism for the
module topology on the differentials and the valuation topology on `P`. -/
noncomputable def equivPuiseuxField :
    ContinuousKaehlerDifferential K ≃L[puiseuxField K] puiseuxField K :=
  let e : ContinuousKaehlerDifferential K ≃ₗ[puiseuxField K] puiseuxField K :=
    (derivation K).liftKaehlerDifferential.quotKerEquivOfSurjective
      derivation_liftKaehlerDifferential_surjective
  { e with
    continuous_toFun := IsModuleTopology.continuous_of_linearMap e.toLinearMap
    continuous_invFun := IsModuleTopology.continuous_of_linearMap e.symm.toLinearMap }

@[simp]
theorem equivPuiseuxField_mk (ω : Ω[puiseuxField K⁄K]) :
    equivPuiseuxField K (mk K ω) = (derivation K).liftKaehlerDifferential ω :=
  (rfl)

/-- The equivalence sends `dx` to the derivative `dx/dt`. -/
@[simp]
theorem equivPuiseuxField_D (x : puiseuxField K) :
    equivPuiseuxField K (D K x) = derivation K x := by
  simp [D_apply]

/-- The continuous one-form corresponding to `x` is `x dt`. -/
@[simp]
theorem equivPuiseuxField_symm_apply (x : puiseuxField K) :
    (equivPuiseuxField K).symm x = x • D K (single K 1 1) := by
  rw [ContinuousLinearEquiv.symm_apply_eq, map_smul, equivPuiseuxField_D, derivation_single_one,
    smul_eq_mul, mul_one]

/-- Every continuous one-form is `x dt` for the unique `x = equivPuiseuxField K ω`. -/
theorem equivPuiseuxField_smul_D_single_one (ω : ContinuousKaehlerDifferential K) :
    equivPuiseuxField K ω • D K (single K 1 1) = ω := by
  rw [← equivPuiseuxField_symm_apply, ContinuousLinearEquiv.symm_apply_apply]

/-- **`dx = (dx/dt) dt`.** -/
theorem derivation_smul_D_single_one (x : puiseuxField K) :
    derivation K x • D K (single K 1 1) = D K x := by
  rw [← equivPuiseuxField_D, equivPuiseuxField_smul_D_single_one]

variable (K) in
/-- `Ω¹_cont(P/K)` has rank one over `P`. -/
theorem finrank_eq_one :
    Module.finrank (puiseuxField K) (ContinuousKaehlerDifferential K) = 1 :=
  (equivPuiseuxField K).toLinearEquiv.finrank_eq.trans (Module.finrank_self _)

variable (K) in
/-- The universal derivation `d` is continuous. -/
theorem continuous_D : Continuous (D K) :=
  (equivPuiseuxField K).toHomeomorph.comp_continuous_iff.mp <| by
    simpa only [ContinuousLinearEquiv.coe_toHomeomorph, Function.comp_def,
      equivPuiseuxField_D] using continuous_derivation (K := K)

/-- Semilinear maps out of `Ω¹_cont(P/K)` agree as soon as they agree on `dt`. -/
@[ext]
theorem hom_ext {S N : Type*} [Semiring S] [AddCommMonoid N] [Module S N]
    {σ : puiseuxField K →+* S} {ℓ ℓ' : ContinuousKaehlerDifferential K →ₛₗ[σ] N}
    (h : ℓ (D K (single K 1 1)) = ℓ' (D K (single K 1 1))) : ℓ = ℓ' := by
  ext ω
  rw [← equivPuiseuxField_smul_D_single_one ω, map_smulₛₗ, map_smulₛₗ, h]

/-- Every linear map from the continuous differentials to a module with continuous scalar
multiplication is continuous. -/
@[fun_prop]
theorem continuous_of_linearMap {M : Type*} [AddCommMonoid M] [Module (puiseuxField K) M]
    [TopologicalSpace M] [ContinuousSMul (puiseuxField K) M]
    (ℓ : ContinuousKaehlerDifferential K →ₗ[puiseuxField K] M) : Continuous ℓ :=
  ((equivPuiseuxField K).continuous.fun_smul continuous_const).congr fun ω ↦ by
    simpa only [map_smul] using congrArg ℓ (equivPuiseuxField_smul_D_single_one ω)

variable {M : Type*} [AddCommGroup M] [Module (puiseuxField K) M] [Module K M]
  [IsScalarTower K (puiseuxField K) M] [TopologicalSpace M] [ContinuousSMul (puiseuxField K) M]

section Hausdorff

variable [T2Space M]

/-- **The factorization of a continuous derivation through `d`.** A continuous `K`-derivation
`δ : P → M` factors through `Ω¹_cont(P/K)`, by the `P`-linear map induced by its Kähler lift. -/
noncomputable def lift (δ : Derivation K (puiseuxField K) M) (hδ : Continuous δ) :
    ContinuousKaehlerDifferential K →ₗ[puiseuxField K] M :=
  Submodule.liftQ _ δ.liftKaehlerDifferential fun ω hω ↦ by
    have h : δ.liftKaehlerDifferential =
        LinearMap.toSpanSingleton (puiseuxField K) M (δ (single K 1 1)) ∘ₗ
          (derivation K).liftKaehlerDifferential := by
      ext x
      simp [δ.apply_eq_puiseuxFieldDerivation_smul hδ x]
    rw [LinearMap.mem_ker, h, LinearMap.comp_apply, LinearMap.mem_ker.mp hω, map_zero]

@[simp]
theorem lift_mk (δ : Derivation K (puiseuxField K) M) (hδ : Continuous δ)
    (ω : Ω[puiseuxField K⁄K]) : lift δ hδ (mk K ω) = δ.liftKaehlerDifferential ω :=
  (rfl)

@[simp]
theorem lift_D (δ : Derivation K (puiseuxField K) M) (hδ : Continuous δ) (x : puiseuxField K) :
    lift δ hδ (D K x) = δ x := by
  simp [D_apply]

theorem compDer_lift (δ : Derivation K (puiseuxField K) M) (hδ : Continuous δ) :
    (lift δ hδ).compDer (D K) = δ :=
  Derivation.ext (lift_D δ hδ)

/-- The factorization of a continuous derivation is continuous. -/
theorem continuous_lift (δ : Derivation K (puiseuxField K) M) (hδ : Continuous δ) :
    Continuous (lift δ hδ) :=
  continuous_of_linearMap _

/-- The factorization of `δ` through `d` is unique. -/
theorem lift_unique (δ : Derivation K (puiseuxField K) M) (hδ : Continuous δ)
    (ℓ : ContinuousKaehlerDifferential K →ₗ[puiseuxField K] M) (h : ℓ.compDer (D K) = δ) :
    ℓ = lift δ hδ :=
  hom_ext <| by rw [lift_D, ← h]; simp

/-- **Universal property of continuous differentials.** Every continuous `K`-derivation of the
Puiseux field into a Hausdorff module with continuous scalar multiplication factors uniquely
through `d` by a `P`-linear map. -/
theorem existsUnique_compDer_eq (δ : Derivation K (puiseuxField K) M) (hδ : Continuous δ) :
    ∃! ℓ : ContinuousKaehlerDifferential K →ₗ[puiseuxField K] M, ℓ.compDer (D K) = δ :=
  ⟨lift δ hδ, compDer_lift δ hδ, fun ℓ h ↦ lift_unique δ hδ ℓ h⟩

end Hausdorff

/-- Every derivation factoring through `d` is continuous when scalar multiplication on its
target is continuous. -/
theorem continuous_compDer (ℓ : ContinuousKaehlerDifferential K →ₗ[puiseuxField K] M) :
    Continuous (ℓ.compDer (D K)) :=
  (continuous_of_linearMap ℓ).comp (continuous_D K)

/-! ### One-forms of the ramified levels -/

variable (K) in
/-- The map from the continuous one-forms of level `n` to those of the Puiseux field,
`f du ↦ f (t ^ (1 / n)) d(t ^ (1 / n))`. Here `TauCeti.ContinuousKaehlerDifferential K` is read in
the variable `u` of level `n`, and the map is semilinear over the level embedding
`u ↦ t ^ (1 / n)`. -/
noncomputable def levelMap (n : ℕ+) :
    TauCeti.ContinuousKaehlerDifferential K
      →ₛₗ[(levelEmbedding K n : K⸨X⸩ →+* puiseuxField K)] ContinuousKaehlerDifferential K where
  toFun ω := (equivPuiseuxField K).symm
    (levelEmbedding K n (TauCeti.ContinuousKaehlerDifferential.equivLaurentSeries K ω) *
      derivation K (levelEmbedding K n (HahnSeries.single 1 1)))
  map_add' ω η := by simp only [map_add, add_mul]
  map_smul' f ω := by
    rw [map_smul, smul_eq_mul, map_mul (levelEmbedding K n), mul_assoc, ← smul_eq_mul,
      (equivPuiseuxField K).symm.map_smul, RingHom.coe_coe]

/-- The level map sends `f du` to `f (t ^ (1 / n)) • d(t ^ (1 / n))`. -/
@[simp]
theorem equivPuiseuxField_levelMap (n : ℕ+) (ω : TauCeti.ContinuousKaehlerDifferential K) :
    equivPuiseuxField K (levelMap K n ω) =
      levelEmbedding K n (TauCeti.ContinuousKaehlerDifferential.equivLaurentSeries K ω) *
        derivation K (levelEmbedding K n (HahnSeries.single 1 1)) :=
  (equivPuiseuxField K).apply_symm_apply _

/-- **The level maps commute with `d`**: `levelMap K n (dg) = d (g (t ^ (1 / n)))`. -/
@[simp]
theorem levelMap_D (n : ℕ+) (g : K⸨X⸩) :
    levelMap K n (TauCeti.ContinuousKaehlerDifferential.D K g) = D K (levelEmbedding K n g) :=
  (equivPuiseuxField K).injective <| by
    have hX : LaurentSeries.derivative K (HahnSeries.single 1 1 : K⸨X⸩) = 1 := by simp
    rw [equivPuiseuxField_levelMap, TauCeti.ContinuousKaehlerDifferential.equivLaurentSeries_D,
      equivPuiseuxField_D, derivation_levelEmbedding, derivation_levelEmbedding, hX, mul_one,
      ← map_mul, mul_comm]

/-- The level maps are continuous. -/
theorem continuous_levelMap (n : ℕ+) : Continuous (levelMap K n) :=
  IsModuleTopology.continuous_of_linearMapₛₗ (continuous_levelEmbedding n) (levelMap K n)

/-- The level maps are injective. -/
theorem levelMap_injective (n : ℕ+) : Function.Injective (levelMap K n) := by
  intro ω η h
  have hu : derivation K (levelEmbedding K n (HahnSeries.single 1 1)) ≠ 0 := by
    rw [derivation_levelEmbedding]
    simp
  have h' := congrArg (equivPuiseuxField K) h
  rw [equivPuiseuxField_levelMap, equivPuiseuxField_levelMap, mul_left_inj' hu] at h'
  exact (TauCeti.ContinuousKaehlerDifferential.equivLaurentSeries K).injective
    ((levelEmbedding K n).injective h')

/-- **Compatibility with the transition maps.** The transition map from level `n` to level
`n * d` substitutes `u ^ d` for `u` in one-forms; following it by the level map of level `n * d`
gives the level map of level `n`. -/
theorem levelMap_subst_X_pow (n d : ℕ+) (ω : TauCeti.ContinuousKaehlerDifferential K) :
    levelMap K (n * d) (TauCeti.ContinuousKaehlerDifferential.subst (K := K)
      (φ := PowerSeries.X ^ (d : ℕ)) (by simp) (pow_ne_zero _ PowerSeries.X_ne_zero) ω) =
      levelMap K n ω := by
  have h (g : K⸨X⸩) : levelEmbedding K (n * d) (LaurentSeries.substAlgHom
      (φ := PowerSeries.X ^ (d : ℕ)) (by simp) (pow_ne_zero _ PowerSeries.X_ne_zero) g) =
      levelEmbedding K n g := by
    rw [LaurentSeries.substAlgHom_X_pow_eq_expand, levelEmbedding_expand]
  rw [← TauCeti.ContinuousKaehlerDifferential.equivLaurentSeries_smul_D_single_one K ω]
  simp only [map_smulₛₗ, TauCeti.ContinuousKaehlerDifferential.subst_D, levelMap_D,
    RingHom.coe_coe, h]

/-- **Every continuous one-form on the Puiseux field comes from a level.** -/
theorem exists_levelMap_eq (ω : ContinuousKaehlerDifferential K) :
    ∃ n : ℕ+, ∃ η : TauCeti.ContinuousKaehlerDifferential K, levelMap K n η = ω := by
  obtain ⟨n, hn⟩ := exists_mem_range_levelEmbedding (equivPuiseuxField K ω)
  obtain ⟨f, hf⟩ := (AlgHom.mem_range _).mp hn
  refine ⟨n, f • TauCeti.ContinuousKaehlerDifferential.D K (HahnSeries.single (n : ℤ) 1), ?_⟩
  rw [map_smulₛₗ, levelMap_D, levelEmbedding_single_self, RingHom.coe_coe, hf,
    equivPuiseuxField_smul_D_single_one]

end ContinuousKaehlerDifferential

end puiseuxField

end TauCeti
