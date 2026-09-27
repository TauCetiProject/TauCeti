/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.Galois.Restriction
public import TauCeti.NumberTheory.LocalField.GaloisAction
public import TauCeti.NumberTheory.LocalField.RamificationIndex
public import TauCeti.RingTheory.DiscreteValuationRing.Monogenic
public import TauCeti.RingTheory.Invariant.Basic
public import TauCeti.RingTheory.LocalRing.RamificationGroup
public import TauCeti.RingTheory.Valuation.AddValuation

/-!
# The lower index of a quotient of a Galois group

Let `M/K` be a finite Galois extension of nonarchimedean local fields with group `G`, and let
`L` be an intermediate field, normal over `K`, so that restriction `G → Gal(L/K)` identifies
`Gal(L/K)` with the quotient `G / H` by `H = Gal(M/L)`. Serre's lower index
`i_G(σ) = min_{x ∈ 𝒪[M]} v_M(σ x - x)` (`TauCeti.IsLocalRing.lowerIndex`) encodes the lower
ramification filtration, since `σ ∈ G_i ↔ i + 1 ≤ i_G(σ)`. This file proves how it behaves
under passage to the quotient:

`e(M/L) · i_{G/H}(σ') = ∑_{σ ↦ σ'} i_G(σ)`,

where `e(M/L)` is the ramification index of `M/L`. The identity is stated in `ℕ∞`, where it
holds for every `σ'`: at `σ' = 1` both sides are `⊤`. It is the input from which Herbrand's
theorem, the compatibility of the upper numbering with quotients, is derived.

## Main results

* `TauCeti.LocalFieldsRamification.ramificationIndex_mul_lowerIndex_restrictNormal_eq_sum`: for
  `σ : Gal(M/K)`, `e(M/L) · i(σ|_L) = ∑_{τ ∈ Gal(M/L)} i(σ τ)`, the sum over the coset `σ H`.
* `TauCeti.LocalFieldsRamification.ramificationIndex_mul_lowerIndex_eq_sum`: for
  `σ' : Gal(L/K)`, `e(M/L) · i(σ') = ∑_{σ|_L = σ'} i(σ)`, the sum over the fibre of restriction.

## References

* [J.-P. Serre, *Corps Locaux*][serre1968], Chapter IV, §1, Proposition 3.
-/

public section
noncomputable section

open ValuativeRel Polynomial
open TauCeti.IsLocalRing (lowerIndex lowerIndex_eq_addVal_of_adjoin_singleton_eq_top)

namespace TauCeti.LocalFieldsRamification

variable {K L M : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L] [Field M] [ValuativeRel M] [TopologicalSpace M]
  [IsNonarchimedeanLocalField M]
  [Algebra K L] [ValuativeExtension K L] [Module.Finite K L] [Normal K L]
  [Algebra L M] [ValuativeExtension L M] [Module.Finite L M]
  [Algebra K M] [ValuativeExtension K M] [Module.Finite K M] [IsGalois K M]
  [IsScalarTower K L M]

omit [TopologicalSpace M] [IsNonarchimedeanLocalField M] [ValuativeExtension K L]
  [Module.Finite K L] [Normal K L] [IsGalois K M] in
/-- The characteristic polynomial of `x` under `Gal(M/L)`, transformed by `σ` and evaluated at
`x`, is the product `∏_τ (x - σ τ x)`. -/
private theorem eval_smul_charpoly (σ : M ≃ₐ[K] M) (x : 𝒪[M]) :
    (σ • MulSemiringAction.charpoly (M ≃ₐ[L] M) x).eval x =
      ∏ τ : M ≃ₐ[L] M, (x - (σ * τ.restrictScalars K) • x) := by
  simpa only [AlgEquiv.restrictScalarsHom_apply] using
    (MulSemiringAction.eval_smul_charpoly (AlgEquiv.restrictScalarsHom (S := L) K)
      (fun τ b ↦ AlgEquiv.restrictScalars_smul_integerRing (K := K) τ b) σ x)

omit [IsGalois K M] in
/-- The displacement `σ y - y` of a generator `y` of `𝒪[L]` divides `(σ f)(x)`, where `f` is
the characteristic polynomial of `x` under `Gal(M/L)`: the coefficients of `f` lie in `𝒪[L]`,
and `f(x) = 0`. -/
private theorem smul_sub_dvd_eval_smul_charpoly [IsGalois L M] {y : 𝒪[L]}
    (hy : Algebra.adjoin 𝒪[K] {y} = ⊤) (σ : M ≃ₐ[K] M) (x : 𝒪[M]) :
    σ • algebraMap 𝒪[L] 𝒪[M] y - algebraMap 𝒪[L] 𝒪[M] y ∣
      (σ • MulSemiringAction.charpoly (M ≃ₐ[L] M) x).eval x := by
  set P := MulSemiringAction.charpoly (M ≃ₐ[L] M) x
  rw [← sub_zero ((σ • P).eval x), ← MulSemiringAction.eval_charpoly (M ≃ₐ[L] M) x, ← eval_sub,
    eval_eq_sum_range]
  refine Finset.dvd_sum fun n _ ↦ Dvd.dvd.mul_right ?_ _
  obtain ⟨w, hw⟩ := Algebra.IsInvariant.isInvariant (A := 𝒪[L]) (G := M ≃ₐ[L] M) (P.coeff n)
    (MulSemiringAction.smul_coeff_charpoly x n)
  rw [coeff_sub, coeff_smul, ← hw, AlgEquiv.smul_algebraMap_integerRing,
    AlgEquiv.smul_algebraMap_integerRing, ← map_sub, ← map_sub]
  exact map_dvd _ (smul_sub_dvd_smul_sub_of_adjoin_singleton_eq_top hy _ w)

omit [ValuativeExtension K L] [Module.Finite K L] [Normal K L] [IsGalois K M] in
/-- Conversely `(σ f)(x)` divides `y - σ y`: writing `y = g(x)` with `g` over `𝒪[K]`, the
characteristic polynomial `f` divides `g - y`, which vanishes on the orbit of `x`. -/
private theorem eval_smul_charpoly_dvd_sub_smul {x : 𝒪[M]} (hx : Algebra.adjoin 𝒪[K] {x} = ⊤)
    (y : 𝒪[L]) (σ : M ≃ₐ[K] M) :
    (σ • MulSemiringAction.charpoly (M ≃ₐ[L] M) x).eval x ∣
      algebraMap 𝒪[L] 𝒪[M] y - σ • algebraMap 𝒪[L] 𝒪[M] y := by
  obtain ⟨q, hq⟩ : ∃ q : 𝒪[K][X], aeval x q = algebraMap 𝒪[L] 𝒪[M] y := by
    rw [← AlgHom.mem_range, ← Algebra.adjoin_singleton_eq_range_aeval, hx]
    exact Algebra.mem_top
  set g := q.map (algebraMap 𝒪[K] 𝒪[M]) - C (algebraMap 𝒪[L] 𝒪[M] y)
  -- `g` vanishes on the orbit of `x`, since `Gal(M/L)` fixes both `𝒪[K]` and `y`.
  have hg : ∀ τ : M ≃ₐ[L] M, g.eval (τ • x) = 0 := fun τ ↦ by
    rw [eval_sub, eval_C, eval_map_algebraMap,
      ← AlgEquiv.restrictScalars_smul_integerRing (K := K) τ x,
      Polynomial.aeval_smul, hq, AlgEquiv.restrictScalars_smul_integerRing,
      smul_algebraMap, sub_self]
  -- The translates of `x` under `Gal(M/L)` are pairwise distinct, as `x` generates `𝒪[M]`.
  have hinj : Function.Injective fun τ : M ≃ₐ[L] M ↦ τ • x := by
    simpa [Function.comp_def] using
      (smul_left_injective_of_adjoin_singleton_eq_top (G := M ≃ₐ[K] M) hx).comp
        (AlgEquiv.restrictScalars_injective (R := K) (S := L) (A := M))
  obtain ⟨h, hh⟩ := MulSemiringAction.charpoly_dvd hinj hg
  have hσg : σ • g = q.map (algebraMap 𝒪[K] 𝒪[M]) - C (σ • algebraMap 𝒪[L] 𝒪[M] y) := by
    have hmap : (MulSemiringAction.toRingHom (M ≃ₐ[K] M) 𝒪[M] σ).comp
        (algebraMap 𝒪[K] 𝒪[M]) = algebraMap 𝒪[K] 𝒪[M] :=
      RingHom.ext fun r ↦ smul_algebraMap σ r
    rw [smul_sub, smul_C, smul_eq_map, Polynomial.map_map]
    rw [hmap]
  refine ⟨(σ • h).eval x, ?_⟩
  rw [← eval_mul, ← smul_mul', ← hh, hσg, eval_sub, eval_C, eval_map_algebraMap, hq]

omit [IsGalois K M] in
/-- **Serre's quotient formula for the lower index**, over a coset. For an intermediate field
`L` of `M/K` normal over `K` and `σ : Gal(M/K)`,
`e(M/L) · i_{L/K}(σ|_L) = ∑_{τ ∈ Gal(M/L)} i_{M/K}(σ τ)`. -/
theorem ramificationIndex_mul_lowerIndex_restrictNormal_eq_sum [IsGalois L M]
    (σ : M ≃ₐ[K] M) :
    (ramificationIndex L M : ℕ∞) * lowerIndex 𝒪[L] (σ.restrictNormal L) =
      ∑ τ : M ≃ₐ[L] M, lowerIndex 𝒪[M] (σ * τ.restrictScalars K) := by
  obtain ⟨x, hx⟩ := TauCeti.IsDiscreteValuationRing.exists_adjoin_eq_top (R := 𝒪[K]) (S := 𝒪[M])
  obtain ⟨y, hy⟩ := TauCeti.IsDiscreteValuationRing.exists_adjoin_eq_top (R := 𝒪[K]) (S := 𝒪[L])
  have key : IsDiscreteValuationRing.addVal 𝒪[M]
      (σ • algebraMap 𝒪[L] 𝒪[M] y - algebraMap 𝒪[L] 𝒪[M] y) =
      IsDiscreteValuationRing.addVal 𝒪[M]
        ((σ • MulSemiringAction.charpoly (M ≃ₐ[L] M) x).eval x) :=
    (IsDiscreteValuationRing.addVal_eq_iff_associated _ _).2 <| associated_of_dvd_dvd
      (smul_sub_dvd_eval_smul_charpoly hy σ x)
      (dvd_sub_comm.1 (eval_smul_charpoly_dvd_sub_smul hx y σ))
  simp_rw [lowerIndex_eq_addVal_of_adjoin_singleton_eq_top hy,
    lowerIndex_eq_addVal_of_adjoin_singleton_eq_top hx, ← nsmul_eq_mul,
    ← addVal_algebraMap, map_sub,
    ← AlgEquiv.smul_algebraMap_integerRing, AddValuation.map_sub_swap _ _ x,
    ← AddValuation.map_prod, ← eval_smul_charpoly]
  exact key

open scoped Classical in
/-- **Serre's quotient formula for the lower index**. For an intermediate field `L` of `M/K`
normal over `K` and `σ' : Gal(L/K)`, `e(M/L) · i_{L/K}(σ') = ∑_{σ|_L = σ'} i_{M/K}(σ)`, the sum
running over the automorphisms of `M/K` restricting to `σ'`. -/
theorem ramificationIndex_mul_lowerIndex_eq_sum (σ' : L ≃ₐ[K] L) :
    (ramificationIndex L M : ℕ∞) * lowerIndex 𝒪[L] σ' =
      ∑ σ : M ≃ₐ[K] M with σ.restrictNormal L = σ', lowerIndex 𝒪[M] σ := by
  have : IsGalois L M := IsGalois.tower_top_of_isGalois K L M
  obtain ⟨σ₀, rfl⟩ := AlgEquiv.restrictNormalHom_surjective (F := K) (K₁ := L) (E := M) σ'
  have hmul (ρ₁ ρ₂ : M ≃ₐ[K] M) :
      (ρ₁ * ρ₂).restrictNormal L = ρ₁.restrictNormal L * ρ₂.restrictNormal L :=
    map_mul (AlgEquiv.restrictNormalHom (F := K) (K₁ := M) L) ρ₁ ρ₂
  -- Rewrite only the left side to leave the fibre sum unchanged.
  conv_lhs => rw [AlgEquiv.restrictNormalHom_apply_eq_restrictNormal K L M,
    ramificationIndex_mul_lowerIndex_restrictNormal_eq_sum]
  refine Finset.sum_nbij (fun τ ↦ σ₀ * τ.restrictScalars K) (fun τ _ ↦ ?_) (fun τ₁ _ τ₂ _ h ↦ ?_)
    (fun σ hσ ↦ ?_) fun _ _ ↦ rfl
  · rw [Finset.mem_filter, hmul,
      (AlgEquiv.mem_range_restrictScalarsHom_iff_restrictNormal_eq_one K L M
        (τ.restrictScalars K)).1 ⟨τ, rfl⟩, mul_one]
    exact ⟨Finset.mem_univ _, rfl⟩
  · exact AlgEquiv.restrictScalars_injective K (mul_left_cancel h)
  · have hσ' : (σ₀⁻¹ * σ).restrictNormal L = 1 := by
      rw [hmul, (Finset.mem_filter.1 hσ).2,
        AlgEquiv.restrictNormalHom_apply_eq_restrictNormal K L M, ← hmul, inv_mul_cancel]
      exact map_one (AlgEquiv.restrictNormalHom (F := K) (K₁ := M) L)
    obtain ⟨τ, hτ⟩ :=
      (AlgEquiv.mem_range_restrictScalarsHom_iff_restrictNormal_eq_one K L M (σ₀⁻¹ * σ)).2 hσ'
    have hτ' : τ.restrictScalars K = σ₀⁻¹ * σ := by
      simpa only [AlgEquiv.restrictScalarsHom_apply] using hτ
    exact ⟨τ, Finset.mem_univ _, by
      -- Expose the function supplied to `sum_nbij` before rewriting its value.
      change σ₀ * τ.restrictScalars K = σ
      rw [hτ', mul_inv_cancel_left]⟩

end TauCeti.LocalFieldsRamification
