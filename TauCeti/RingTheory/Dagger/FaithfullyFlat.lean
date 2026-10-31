/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Dagger.MaximalSpectrum
public import Mathlib.RingTheory.RingHom.FaithfullyFlat

import TauCeti.RingTheory.Affinoid.Polyradius
import TauCeti.RingTheory.Affinoid.PowerBounded
import TauCeti.RingTheory.Dagger.Weierstrass
import TauCeti.RingTheory.Flat.QuotientPow
import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.ClosedIdeal
import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.Groebner
import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.UniversalProperty

/-!
# The Tate algebra is faithfully flat over the Monsky–Washnitzer algebra

Let `K` be a complete nontrivially normed ultrametric field, `T = K⟨X₁, …, Xₙ⟩` the Tate algebra
and `W = K⟨X₁, …, Xₙ⟩†` the Monsky–Washnitzer algebra. This file shows that the inclusion
`W → T` is faithfully flat.

The heart of the matter is that `W` and `T` have the same finite quotients: for every ideal `J`
of `W` of finite codimension, `J T ∩ W = J` and `W ⧸ J → T ⧸ J T` is bijective. Surjectivity was
already known from the density of `W` in `T`. For injectivity we construct a retraction
`T → W ⧸ J` of `W → W ⧸ J`.

* For every radius `ρ > 1` the restricted series `K{X/ρ}` lie in `W`, and they surject onto
  `W ⧸ J` because the polynomials already do. So `W ⧸ J` is a quotient of the affinoid algebra
  `K{X/ρ}`, and it inherits a complete ultrametric residue norm.
* The class of each variable `Xᵢ` in `W ⧸ J` has supremum seminorm at most `ρ` for every `ρ > 1`,
  since homomorphisms of affinoid algebras contract the supremum seminorm, hence at most `1`.
  It is therefore power-bounded, and the universal property of `T` gives a continuous
  homomorphism `T → W ⧸ J` sending `Xᵢ` to its class.
* Composed with `W → T`, this homomorphism agrees with the projection `W → W ⧸ J` on the
  variables, so it is the projection: homomorphisms from `W` into a finite-dimensional algebra
  are determined by the variables (`washnitzerAlgebra.algHom_ext_of_isIntegral`).

Taking `J = 𝔪 ^ k` for the maximal ideals `𝔪` of `W`, the infinitesimal neighbourhoods of `W` and
`T` at every classical point agree, which gives flatness by
`Module.Flat.of_bijective_quotientMap_pow`. Faithfulness holds because every maximal ideal of `W`
generates a maximal ideal of `T`.

## Main results

* `TauCeti.Dagger.washnitzerAlgebra.comap_map_toTate_of_finite`: an ideal `J` of `W` of finite
  codimension satisfies `J T ∩ W = J`.
* `TauCeti.Dagger.washnitzerAlgebra.quotientMap_map_toTate_bijective`: for such `J`, the map
  `W ⧸ J → T ⧸ J T` is bijective.
* `TauCeti.Dagger.washnitzerAlgebra.faithfullyFlat_toTate`: `W → T` is faithfully flat.

## References

* E. Grosse-Klönne, *Rigid analytic spaces with overconvergent structure sheaf*,
  J. reine angew. Math. 519 (2000), §1, Proposition 1.5 and its proof.
* [Bosch, Güntzer, Remmert, *Non-Archimedean Analysis*][bosch-guntzer-remmert], §§6.1.1 and
  6.2.3, for the universal property of Tate algebras and power-bounded elements.
-/

public section

namespace TauCeti.Dagger.washnitzerAlgebra

open _root_.MvPowerSeries

variable {K σ : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  [Finite σ]

local notation "W " σ:max => washnitzerAlgebra σ K
local notation "T " σ:max => IsRestricted.subring (R := K) (fun _ : σ ↦ (1 : ℝ))
local notation "T[" ρ "] " σ:max => IsRestricted.subring (R := K) (fun _ : σ ↦ ρ)

/-- The inclusion of the series restricted at a radius `ρ > 1` into `W`, as a `K`-algebra map. -/
private noncomputable def ofRestrictedₐ {ρ : ℝ} (hρ : 1 < ρ) : T[ρ] σ →ₐ[K] W σ where
  __ := ofRestricted hρ fun _ ↦ le_rfl
  commutes' r := Subtype.ext (coe_ofRestricted hρ (fun _ ↦ le_rfl) (algebraMap K _ r))

omit [CompleteSpace K] [Finite σ] in
@[simp]
private theorem coe_ofRestrictedₐ {ρ : ℝ} (hρ : 1 < ρ) (f : T[ρ] σ) :
    (ofRestrictedₐ hρ f : _root_.MvPowerSeries σ K) = f :=
  coe_ofRestricted hρ (fun _ ↦ le_rfl) f

/-- For a radius `ρ > 1`, every class of a finite quotient `W ⧸ J` is represented by a series
restricted at `ρ`, since it is represented by a polynomial. -/
private theorem surjective_mkₐ_comp_ofRestrictedₐ (J : Ideal (W σ))
    [Module.Finite K (W σ ⧸ J)] {ρ : ℝ} (hρ : 1 < ρ) :
    Function.Surjective ((Ideal.Quotient.mkₐ K J).comp (ofRestrictedₐ (σ := σ) hρ)) := by
  have : Algebra.IsIntegral K (W σ ⧸ J) := Algebra.IsIntegral.of_finite K _
  intro x
  obtain ⟨p, rfl⟩ := surjective_mkₐ_comp_ofMvPolynomial J x
  refine ⟨TauCeti.MvPowerSeries.polynomialToRestricted (fun _ ↦ ρ) p, ?_⟩
  simp only [AlgHom.comp_apply]
  congr 1
  exact Subtype.ext (by simp [TauCeti.MvPowerSeries.coe_polynomialToRestricted])

/-- In an affinoid model `S` of a finite quotient `W ⧸ J`, the class of every variable has
supremum seminorm at most `1`: it is the image of the variable of `K{X/r}` for radii `r > 1`
arbitrarily close to `1`. -/
private theorem supSeminorm_le_one (J : Ideal (W σ)) {S : Type*}
    [CommRing S] [Algebra K S] (hS : IsAffinoidAlgebra K S) (e : (W σ ⧸ J) ≃ₐ[K] S) (i : σ) :
    supSeminorm K (e (Ideal.Quotient.mk J (X σ K i))) ≤ 1 := by
  obtain ⟨c, hc⟩ := NormedField.exists_one_lt_norm K
  have hρ0 : 0 < ‖c‖ := zero_lt_one.trans hc
  -- For `m ≠ 0`, the radius `r = ‖c‖ ^ (1 / m)` is affinoid and bounds the seminorm.
  have key (m : ℕ) (hm : m ≠ 0) :
      supSeminorm K (e (Ideal.Quotient.mk J (X σ K i))) ^ m ≤ ‖c‖ := by
    have hr : 1 < ‖c‖ ^ (m : ℝ)⁻¹ := Real.one_lt_rpow hc (by positivity)
    have : Fact (0 < ‖c‖ ^ (m : ℝ)⁻¹) := ⟨zero_lt_one.trans hr⟩
    have hT : IsAffinoidAlgebra K (T[‖c‖ ^ (m : ℝ)⁻¹] σ) :=
      isAffinoidAlgebra_isRestricted_of_pow_eq_norm (r := fun _ : σ ↦ ‖c‖ ^ (m : ℝ)⁻¹)
        fun _ ↦ ⟨m, Nat.pos_of_ne_zero hm, Units.mk0 c (norm_pos_iff.mp hρ0),
          Real.rpow_inv_natCast_pow hρ0.le hm⟩
    let x : T[‖c‖ ^ (m : ℝ)⁻¹] σ := ⟨_root_.MvPowerSeries.X i, isRestricted_X _ i⟩
    let φ : T[‖c‖ ^ (m : ℝ)⁻¹] σ →ₐ[K] S :=
      e.toAlgHom.comp ((Ideal.Quotient.mkₐ K J).comp (ofRestrictedₐ hr))
    have hx : ofRestrictedₐ hr x = X σ K i :=
      Subtype.ext ((coe_ofRestrictedₐ hr x).trans (coe_X (R := K) i).symm)
    have hφ : φ x = e (Ideal.Quotient.mk J (X σ K i)) := by simp [φ, hx]
    have h1 := hT.supSeminorm_map_le hS φ x
    have h2 := hT.supSeminorm_le_norm x
    rw [_root_.MvPowerSeries.norm_X] at h2
    rw [hφ] at h1
    calc _ ≤ (‖c‖ ^ (m : ℝ)⁻¹) ^ m := pow_le_pow_left₀ (supSeminorm_nonneg _) (h1.trans h2) m
      _ = ‖c‖ := Real.rpow_inv_natCast_pow hρ0.le hm
  by_contra! h
  obtain ⟨m, hm⟩ := pow_unbounded_of_one_lt ‖c‖ h
  have hm0 : m ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hm
    exact hm.not_gt hc
  exact (key m hm0).not_gt hm

/-- Given a complete ultrametric normed affinoid model `S` of a finite quotient `W ⧸ J`, the
projection `W → W ⧸ J` extends along `W → T`, by the universal property of `T`. -/
private theorem exists_algHom_comp_toTate_eq_of_algEquiv (J : Ideal (W σ))
    [Module.Finite K (W σ ⧸ J)] {S : Type*} [NormedCommRing S] [NormedAlgebra K S]
    [IsUltrametricDist S] [CompleteSpace S] (hS : IsAffinoidAlgebra K S)
    (e : (W σ ⧸ J) ≃ₐ[K] S) :
    ∃ ψ : T σ →ₐ[K] W σ ⧸ J, ψ.comp (toTate σ K) = Ideal.Quotient.mkₐ K J := by
  have : Algebra.IsIntegral K (W σ ⧸ J) := Algebra.IsIntegral.of_finite K _
  -- Number the variables to apply the universal property of `K⟨X₁, …, Xₙ⟩`.
  let eσ := Finite.equivFin σ
  let b : Fin (Nat.card σ) → S := fun j ↦ e (Ideal.Quotient.mk J (X σ K (eσ.symm j)))
  have hb (j : Fin (Nat.card σ)) : TauCeti.Huber.IsPowerBounded (b j) :=
    (hS.isPowerBounded_iff_supSeminorm_le_one).mpr (supSeminorm_le_one J hS e _)
  let ψ₀ := TauCeti.MvPowerSeries.restrictedLift (continuous_algebraMap K S) hb
  let ren : T σ ≃ₐ[K] T (Fin (Nat.card σ)) := IsRestricted.renameAlgEquiv eσ (fun _ ↦ 1)
  let ψ₁ : T σ →ₐ[K] S :=
    { ψ₀.comp ren.toRingHom with
      commutes' := fun a ↦ by
        simp [ψ₀, TauCeti.MvPowerSeries.restrictedLift_algebraMap] }
  refine ⟨e.symm.toAlgHom.comp ψ₁, algHom_ext_of_isIntegral fun i ↦ ?_⟩
  have hren : ren (toTate σ K (X σ K i)) =
      ⟨_root_.MvPowerSeries.X (eσ i), isRestricted_X _ (eσ i)⟩ :=
    Subtype.ext <| (IsRestricted.coe_renameAlgEquiv eσ (fun _ ↦ (1 : ℝ)) _).trans <| by
      simp [rename_X]
  have hψ₁ : ψ₁ (toTate σ K (X σ K i)) = ψ₀ (ren (toTate σ K (X σ K i))) := rfl
  simp only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, hψ₁, hren,
    TauCeti.MvPowerSeries.restrictedLift_X, ψ₀]
  simp [b]

/-- **A retraction of the Tate algebra onto a finite quotient of `W`.** For an ideal `J` of `W` of
finite codimension, the projection `W → W ⧸ J` extends along `W → T`. -/
private theorem exists_algHom_comp_toTate_eq (J : Ideal (W σ)) [Module.Finite K (W σ ⧸ J)] :
    ∃ ψ : T σ →ₐ[K] W σ ⧸ J, ψ.comp (toTate σ K) = Ideal.Quotient.mkₐ K J := by
  -- `W ⧸ J` is a quotient of the affinoid algebra `K{X/ρ}` for `ρ = ‖c‖ > 1`.
  obtain ⟨c, hc⟩ := NormedField.exists_one_lt_norm K
  have hρ0 : 0 < ‖c‖ := zero_lt_one.trans hc
  have : Fact (0 < ‖c‖) := ⟨hρ0⟩
  let θ := (Ideal.Quotient.mkₐ K J).comp (ofRestrictedₐ (σ := σ) hc)
  have hS : IsAffinoidAlgebra K (T[‖c‖] σ ⧸ RingHom.ker θ) :=
    (isAffinoidAlgebra_isRestricted_of_pow_eq_norm (r := fun _ : σ ↦ ‖c‖) fun _ ↦
      ⟨1, one_pos, Units.mk0 c (norm_pos_iff.mp hρ0), pow_one _⟩).quotient _
  exact exists_algHom_comp_toTate_eq_of_algEquiv J hS
    (Ideal.quotientKerAlgEquivOfSurjective (surjective_mkₐ_comp_ofRestrictedₐ J hc)).symm

/-- **Finite quotients of the Monsky–Washnitzer algebra and of the Tate algebra agree.** An ideal
`J` of `W` whose quotient is finite-dimensional over `K` satisfies `J T ∩ W = J`. -/
@[simp]
theorem comap_map_toTate_of_finite (J : Ideal (W σ)) [Module.Finite K (W σ ⧸ J)] :
    (J.map (toTate σ K)).comap (toTate σ K) = J := by
  refine le_antisymm (fun f hf ↦ ?_) Ideal.le_comap_map
  obtain ⟨ψ, hψ⟩ := exists_algHom_comp_toTate_eq J
  -- `ψ` kills `J T`, because it kills the image of `J`.
  have hker : J.map (toTate σ K) ≤ RingHom.ker ψ :=
    Ideal.map_le_iff_le_comap.mpr fun j hj ↦ by
      rw [Ideal.mem_comap, RingHom.mem_ker, ← AlgHom.comp_apply, hψ,
        Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem]
      exact hj
  have := hker hf
  rwa [RingHom.mem_ker, ← AlgHom.comp_apply, hψ, Ideal.Quotient.mkₐ_eq_mk,
    Ideal.Quotient.eq_zero_iff_mem] at this

/-- **Finite quotients of the Monsky–Washnitzer algebra are quotients of the Tate algebra.** For an
ideal `J` of `W` of finite codimension, the map `W ⧸ J → T ⧸ J T` is bijective. -/
theorem quotientMap_map_toTate_bijective (J : Ideal (W σ)) [Module.Finite K (W σ ⧸ J)] :
    Function.Bijective (Ideal.quotientMap (J.map (toTate σ K)) (toTate σ K).toRingHom
      Ideal.le_comap_map) := by
  refine ⟨Ideal.quotientMap_injective' (comap_map_toTate_of_finite J).le, fun y ↦ ?_⟩
  have : Module.Finite K (W σ ⧸ (J.map (toTate σ K)).comap (toTate σ K)) := by
    rw [comap_map_toTate_of_finite]
    infer_instance
  obtain ⟨x, hx⟩ := (quotientMap_toTate_bijective_of_finite (J.map (toTate σ K))).2 y
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective x
  exact ⟨Ideal.Quotient.mk J f, by simpa using hx⟩

/-- The quotients of `W` by powers of a maximal ideal are finite-dimensional over `K`. -/
private theorem finite_quotient_pow (m : Ideal (W σ)) [m.IsMaximal] (k : ℕ) :
    Module.Finite K (W σ ⧸ m ^ k) := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · have : Subsingleton (W σ ⧸ m ^ 0) := by
      rw [pow_zero, Ideal.one_eq_top]
      exact Ideal.Quotient.subsingleton_iff.mpr rfl
    exact Module.Finite.of_finite
  · have : (m ^ k).radical.IsMaximal := by
      rwa [Ideal.radical_pow m hk.ne', ‹m.IsMaximal›.isPrime.radical]
    exact finite_quotient_of_isMaximal_radical (AlgHom.Finite.id K (W σ)) (m ^ k)

/-- The infinitesimal neighbourhoods of `W` and `T` at a maximal ideal `𝔫` of `T` agree. -/
private theorem quotientMap_map_pow_comap_toTate_bijective (𝔫 : Ideal (T σ)) [𝔫.IsMaximal]
    (k : ℕ) : Function.Bijective (Ideal.quotientMap ((𝔫.comap (toTate σ K) ^ k).map (toTate σ K))
      (toTate σ K).toRingHom Ideal.le_comap_map) := by
  have : (𝔫.comap (toTate σ K)).IsMaximal := isAffinoidAlgebra_tate.comap_isMaximal _ 𝔫
  have := finite_quotient_pow (𝔫.comap (toTate σ K)) k
  exact quotientMap_map_toTate_bijective _

/-- **The Tate algebra is faithfully flat over the Monsky–Washnitzer algebra.** -/
theorem faithfullyFlat_toTate : (toTate σ K).toRingHom.FaithfullyFlat := by
  have : IsNoetherianRing (T σ) := TauCeti.MvPowerSeries.isNoetherianRing_isRestricted_subring
  -- After `algebraize`, `algebraMap (W σ) (T σ)` is `toTate σ K` by definition, so the statements
  -- about `toTate σ K` below are statements about the algebra structure.
  algebraize [(toTate σ K).toRingHom]
  have : Module.Flat (W σ) (T σ) := Module.Flat.of_bijective_quotientMap_pow fun 𝔫 _ k ↦
    quotientMap_map_pow_comap_toTate_bijective 𝔫 k
  refine (Module.FaithfullyFlat.iff_flat_and_proper_ideal _ _).mpr ⟨this, fun I hI h ↦ ?_⟩
  -- A proper ideal lies in a maximal ideal `m`, and `m T` is a maximal ideal of `T`.
  obtain ⟨m, hm, hIm⟩ := I.exists_le_maximal hI
  rw [Ideal.smul_top_eq_map, Submodule.restrictScalars_eq_top_iff] at h
  have h' : I.map (toTate σ K) = ⊤ := h
  exact (isMaximal_map_toTate m).ne_top (top_le_iff.mp (h' ▸ Ideal.map_mono hIm))

end TauCeti.Dagger.washnitzerAlgebra
