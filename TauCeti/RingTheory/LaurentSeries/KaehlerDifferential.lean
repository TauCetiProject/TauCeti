/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Kaehler.Basic
public import Mathlib.Topology.Algebra.Module.ModuleTopology
public import TauCeti.RingTheory.LaurentSeries.ContinuousDerivation
public import TauCeti.RingTheory.LaurentSeries.Substitution

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

Continuous one-forms are covariant under changes of parameter. For a nonzero power series `φ` with
zero constant coefficient, substitution `f dX ↦ f (φ) dφ` is a continuous map of `Ω¹_cont(F/K)`,
semilinear over the substitution `f ↦ f (φ)` of `F`. Since `dφ = Dφ dX`, it sends `f dX` to
`f (φ) Dφ dX`, and by the chain rule it sends `d g` to `d (g (φ))`. Substitutions compose as power
series do, and the residue of `ω (φ)` is `ord φ` times the residue of `ω`. A formal coordinate
`φ = u X + ⋯`, `u ≠ 0`, therefore acts by a semilinear automorphism of `Ω¹_cont(F/K)`, inverse to
that of `φ⁻¹`, which preserves residues.

## Main definitions

* `TauCeti.ContinuousKaehlerDifferential K`: the continuous Kähler differentials `Ω¹_cont(F/K)`.
* `TauCeti.ContinuousKaehlerDifferential.D K`: the universal continuous derivation `d`.
* `TauCeti.ContinuousKaehlerDifferential.equivLaurentSeries K`: the continuous `F`-linear
  equivalence `Ω¹_cont(F/K) ≃ F` sending `d X` to `1`.
* `TauCeti.ContinuousKaehlerDifferential.lift`: the factorization of a continuous derivation
  through `d`.
* `TauCeti.ContinuousKaehlerDifferential.subst`: substitution `f dX ↦ f (φ) dφ` into one-forms.
* `TauCeti.ContinuousKaehlerDifferential.substEquiv`: for a formal coordinate `φ`, substitution
  into one-forms as a semilinear equivalence.

## Main results

* `TauCeti.ContinuousKaehlerDifferential.continuous_D`: the universal derivation is continuous.
* `TauCeti.ContinuousKaehlerDifferential.existsUnique_compDer_eq`: every continuous derivation
  factors uniquely through `d`.
* `TauCeti.ContinuousKaehlerDifferential.derivative_smul_D_single_one`: `d f = Df dX`.
* `TauCeti.ContinuousKaehlerDifferential.subst_D`: coordinate covariance, `(d g) (φ) = d (g (φ))`.
* `TauCeti.ContinuousKaehlerDifferential.subst_subst`: substituting `φ` and then `ψ` is
  substituting `φ (ψ)`.
* `TauCeti.ContinuousKaehlerDifferential.coeff_neg_one_equivLaurentSeries_subst`: the residue of
  `ω (φ)` is `ord φ` times that of `ω`.
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

/-- **`d f = Df dX`.** The differential of a Laurent series is its formal derivative times `d X`;
in particular `d φ = Dφ dX` for a change of parameter `φ`. -/
theorem derivative_smul_D_single_one (f : K⸨X⸩) :
    LaurentSeries.derivative K f • D K (single 1 1) = D K f := by
  rw [← equivLaurentSeries_D, equivLaurentSeries_smul_D_single_one]

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

/-- Semilinear maps out of `Ω¹_cont(K⸨X⸩/K)` agree as soon as they agree on `d X`. -/
@[ext]
theorem hom_ext {S N : Type*} [Semiring S] [AddCommGroup N] [Module S N] {σ : K⸨X⸩ →+* S}
    {ℓ ℓ' : ContinuousKaehlerDifferential K →ₛₗ[σ] N}
    (h : ℓ (D K (single 1 1)) = ℓ' (D K (single 1 1))) : ℓ = ℓ' := by
  ext ω
  rw [← equivLaurentSeries_smul_D_single_one K ω, map_smulₛₗ, map_smulₛₗ, h]

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

/-! ### Substitution into one-forms -/

section Subst

open TauCeti.LaurentSeries PowerSeries

variable {φ : K⟦X⟧} (hφ : constantCoeff φ = 0) (hφ₀ : φ ≠ 0)

/-- **Substitution into continuous one-forms.** For a nonzero power series `φ` with zero constant
coefficient, the map `f dX ↦ f (φ) dφ = f (φ) Dφ dX` on `Ω¹_cont(K⸨X⸩/K)`. It is semilinear
over the substitution `f ↦ f (φ)` of `TauCeti.LaurentSeries.substAlgHom`, and it sends `d g` to
`d (g (φ))` (`TauCeti.ContinuousKaehlerDifferential.subst_D`). -/
noncomputable def subst :
    ContinuousKaehlerDifferential K →ₛₗ[(substAlgHom hφ hφ₀ : K⸨X⸩ →+* K⸨X⸩)]
      ContinuousKaehlerDifferential K where
  toFun ω := (equivLaurentSeries K).symm
    (substAlgHom hφ hφ₀ (equivLaurentSeries K ω) * LaurentSeries.derivative K (φ : K⸨X⸩))
  map_add' ω η := by simp only [map_add, add_mul]
  map_smul' f ω := by
    simp only [map_smul, smul_eq_mul, map_mul, mul_assoc]
    rw [← smul_eq_mul, map_smul, RingHom.coe_coe]

/-- Substitution sends `f dX` to `f (φ) Dφ dX`. -/
@[simp]
theorem equivLaurentSeries_subst (ω : ContinuousKaehlerDifferential K) :
    equivLaurentSeries K (subst hφ hφ₀ ω) =
      substAlgHom hφ hφ₀ (equivLaurentSeries K ω) * LaurentSeries.derivative K (φ : K⸨X⸩) :=
  (equivLaurentSeries K).apply_symm_apply _

/-- **Coordinate covariance of the differential.** Substitution into one-forms sends `d g` to
`d (g (φ))`; this is the chain rule `D (g (φ)) = (Dg) (φ) Dφ`. -/
@[simp]
theorem subst_D (g : K⸨X⸩) : subst hφ hφ₀ (D K g) = D K (substAlgHom hφ hφ₀ g) :=
  (equivLaurentSeries K).injective <| by
    rw [equivLaurentSeries_subst, equivLaurentSeries_D, equivLaurentSeries_D,
      derivative_substAlgHom]

/-- Substitution into one-forms sends `d X` to `d φ`. -/
theorem subst_D_single_one : subst hφ hφ₀ (D K (single 1 1)) = D K (φ : K⸨X⸩) := by
  rw [subst_D, substAlgHom_single_one]

/-- Substitution into one-forms is the unique `f ↦ f (φ)`-semilinear map sending `d X` to `d φ`. -/
theorem eq_subst_of_apply_D_single_one
    (ℓ : ContinuousKaehlerDifferential K →ₛₗ[(substAlgHom hφ hφ₀ : K⸨X⸩ →+* K⸨X⸩)]
      ContinuousKaehlerDifferential K)
    (h : ℓ (D K (single 1 1)) = D K (φ : K⸨X⸩)) : ℓ = subst hφ hφ₀ :=
  hom_ext <| by rw [h, subst_D_single_one]

/-- Substitution into one-forms is continuous. -/
theorem continuous_subst : Continuous (subst hφ hφ₀) :=
  (equivLaurentSeries K).symm.continuous.comp
    (((continuous_substAlgHom hφ hφ₀).comp (equivLaurentSeries K).continuous).mul
      continuous_const)

/-- **Residues of substituted one-forms.** Substituting `φ` multiplies the residue of a one-form
by the order of `φ`: `Res (ω (φ)) = ord φ • Res ω`, where the residue of `f dX` is the coefficient
of `X⁻¹` in `f`. -/
theorem coeff_neg_one_equivLaurentSeries_subst (ω : ContinuousKaehlerDifferential K) :
    (equivLaurentSeries K (subst hφ hφ₀ ω)).coeff (-1) =
      φ.order.toNat • (equivLaurentSeries K ω).coeff (-1) := by
  rw [equivLaurentSeries_subst, coeff_neg_one_substAlgHom_mul_derivative_eq_nsmul]

/-- Substituting `φ` into one-forms and then `ψ` is substituting `φ (ψ)`. -/
theorem subst_subst {ψ : K⟦X⟧} (hψ : constantCoeff ψ = 0) (hψ₀ : ψ ≠ 0)
    (ω : ContinuousKaehlerDifferential K) :
    subst hψ hψ₀ (subst hφ hφ₀ ω) =
      subst (constantCoeff_subst_eq_zero hψ φ hφ) ((subst_eq_zero_iff hψ hψ₀).not.mpr hφ₀) ω := by
  refine (equivLaurentSeries K).injective ?_
  have hD : LaurentSeries.derivative K ((φ.subst ψ : K⟦X⟧) : K⸨X⸩) =
      substAlgHom hψ hψ₀ (LaurentSeries.derivative K (φ : K⸨X⸩)) *
        LaurentSeries.derivative K (ψ : K⸨X⸩) := by
    rw [← substAlgHom_coe hψ hψ₀, derivative_substAlgHom]
  rw [equivLaurentSeries_subst, equivLaurentSeries_subst,
    equivLaurentSeries_subst (constantCoeff_subst_eq_zero hψ φ hφ)
      ((subst_eq_zero_iff hψ hψ₀).not.mpr hφ₀) ω, hD, map_mul,
    TauCeti.LaurentSeries.substAlgHom_comp_substAlgHom_apply, mul_assoc]

/-- Substituting `X` into one-forms is the identity. -/
@[simp]
theorem subst_X (ω : ContinuousKaehlerDifferential K) :
    subst (K := K) (φ := X) constantCoeff_X X_ne_zero ω = ω :=
  (equivLaurentSeries K).injective <| by
    rw [equivLaurentSeries_subst, TauCeti.LaurentSeries.substAlgHom_X, AlgHom.id_apply,
      PowerSeries.coe_X, ← equivLaurentSeries_D, equivLaurentSeries_D_single_one, mul_one]

/-- `subst_X`, for a series `φ` known to equal `X` and carrying its own hypotheses. -/
private theorem subst_eq_self_of_eq_X (h : φ = X) (ω : ContinuousKaehlerDifferential K) :
    subst hφ hφ₀ ω = ω := by
  subst h
  exact subst_X ω

end Subst

/-- **Formal coordinate changes act invertibly on one-forms.** For a formal coordinate `φ`,
substitution `f dX ↦ f (φ) dφ` into continuous one-forms, as an equivalence that is semilinear
over the substitution automorphism `TauCeti.LaurentSeries.substAlgEquiv φ` of `K⸨X⸩`. Its inverse
is substitution of the compositional inverse `φ⁻¹`. -/
noncomputable def substEquiv (φ : FormalCoordinate K) :
    ContinuousKaehlerDifferential K
      ≃ₛₗ[((LaurentSeries.substAlgEquiv φ).toRingEquiv : K⸨X⸩ →+* K⸨X⸩)]
      ContinuousKaehlerDifferential K where
  toFun := subst φ.constantCoeff_toPowerSeries φ.toPowerSeries_ne_zero
  invFun := subst φ⁻¹.constantCoeff_toPowerSeries φ⁻¹.toPowerSeries_ne_zero
  map_add' := map_add _
  map_smul' f ω := by simp
  left_inv ω := by
    rw [subst_subst]
    exact subst_eq_self_of_eq_X _ _ (FormalCoordinate.toPowerSeries_mul_inv φ) ω
  right_inv ω := by
    rw [subst_subst]
    exact subst_eq_self_of_eq_X _ _ (FormalCoordinate.toPowerSeries_inv_mul φ) ω

@[simp]
theorem substEquiv_apply (φ : FormalCoordinate K) (ω : ContinuousKaehlerDifferential K) :
    substEquiv φ ω = subst φ.constantCoeff_toPowerSeries φ.toPowerSeries_ne_zero ω :=
  (rfl)

@[simp]
theorem substEquiv_symm_apply (φ : FormalCoordinate K) (ω : ContinuousKaehlerDifferential K) :
    (substEquiv φ).symm ω = substEquiv φ⁻¹ ω :=
  (rfl)

/-- Substituting the composite coordinate `φ ∘ ψ` into one-forms is substituting `φ` and then
`ψ`. -/
theorem substEquiv_mul_apply (φ ψ : FormalCoordinate K) (ω : ContinuousKaehlerDifferential K) :
    substEquiv (φ * ψ) ω = substEquiv ψ (substEquiv φ ω) := by
  rw [substEquiv_apply, substEquiv_apply, substEquiv_apply, subst_subst]

/-- Substituting the identity coordinate `X` into one-forms is the identity. -/
theorem substEquiv_one_apply (ω : ContinuousKaehlerDifferential K) :
    substEquiv (1 : FormalCoordinate K) ω = ω :=
  subst_eq_self_of_eq_X _ _ FormalCoordinate.toPowerSeries_one ω

/-- **Formal coordinate changes preserve residues of one-forms.** -/
theorem coeff_neg_one_equivLaurentSeries_substEquiv (φ : FormalCoordinate K)
    (ω : ContinuousKaehlerDifferential K) :
    (equivLaurentSeries K (substEquiv φ ω)).coeff (-1) = (equivLaurentSeries K ω).coeff (-1) := by
  rw [substEquiv_apply, coeff_neg_one_equivLaurentSeries_subst,
    FormalCoordinate.order_toPowerSeries, ENat.toNat_one, one_smul]

end ContinuousKaehlerDifferential

end TauCeti
