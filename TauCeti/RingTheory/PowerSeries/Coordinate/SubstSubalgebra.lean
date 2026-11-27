/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.PowerSeries.PiTopology
public import TauCeti.RingTheory.PowerSeries.Coordinate.Basic
import Mathlib.RingTheory.PowerSeries.Inverse
import TauCeti.RingTheory.PowerSeries.Substitution

/-!
# Power series in a formal coordinate with coefficients in a subring

Let `O → R` be an algebra over a commutative ring `O` and `φ = u X + ⋯` a formal coordinate over
`R` (`TauCeti.FormalCoordinate R`). The series `G(φ)` with `G ∈ O⟦X⟧` form an `O`-subalgebra
`φ.substSubalgebra O` of `R⟦X⟧`, the image of substitution of `φ`: the power series in the
parameter `φ` with coefficients in `O`. It contains `φ`, and as an `O`-subalgebra it is closed
under multiplication by elements of `O`. The main example is a complete nonarchimedean field `R`,
such as `ℂ_p`, with its valuation ring `O`, and a parameter `φ = X + ⋯`: then
`φ.substSubalgebra O` is the ring `O[[φ]]` of integral power series in `φ`. A local coordinate
of an elliptic curve with good reduction, read as a power series in the analytic parameter `z`,
is such a parameter, and integrality statements about its Taylor expansions are statements about
`O[[φ]]`.

Substituting the compositional inverse `φ⁻¹` into `G(φ)` gives back the image of `G` in `R⟦X⟧`.
So when `O → R` is injective, substitution of `φ` is injective
(`TauCeti.FormalCoordinate.subst_injective`) and identifies `O⟦X⟧` with `φ.substSubalgebra O`
(`TauCeti.FormalCoordinate.substSubalgebraEquiv`), and a series `f` lies in
`φ.substSubalgebra O` exactly when `f(φ⁻¹)` has coefficients in `O`. Since `f ↦ f(φ⁻¹)` is
continuous for the coefficientwise topology, `φ.substSubalgebra O` is closed under
coefficientwise limits whenever `O` is closed in `R` (for instance the valuation ring of a valued
field, `Valued.isClosed_valuationSubring`).

The constant coefficient of `G(φ)` is that of `G`, and its linear coefficient is that of `G` times
that of `φ`; so for `φ = X + ⋯` the constant and linear coefficients of the elements of
`φ.substSubalgebra O` lie in `O`, and so does the quadratic coefficient when the linear one
vanishes. The units of `O⟦X⟧` are the series with unit constant coefficient, hence, for injective
`O → R`, an element of `φ.substSubalgebra O` is a unit there exactly when its constant coefficient
is a unit of `O`. A coordinate `ψ = G(φ)` with `G` a formal coordinate over `O` generates the same
subalgebra, and `φ.substSubalgebra O` is stable under every substitution `f ↦ f(a)` that maps
`φ` into it, in particular under rescaling `f(X) ↦ f(c X)`.

## Main definitions

* `TauCeti.FormalCoordinate.substSubalgebra O φ`: the `O`-subalgebra of the series `G(φ)`,
  `G ∈ O⟦X⟧`.
* `TauCeti.FormalCoordinate.substSubalgebraEquiv O φ`: for injective `O → R`, the isomorphism
  `O⟦X⟧ ≃ₐ[O] φ.substSubalgebra O`, `G ↦ G(φ)`.

## Main results

* `TauCeti.FormalCoordinate.subst_injective`: `G ↦ G(φ)` is injective when `O → R` is.
* `TauCeti.FormalCoordinate.mem_substSubalgebra_iff_coeff_subst_inv_mem`: `f ∈ O[[φ]]` exactly
  when `f(φ⁻¹)` has coefficients in `O`.
* `TauCeti.FormalCoordinate.isClosed_substSubalgebra`: `O[[φ]]` is closed in the coefficientwise
  topology when `O` is closed in `R`.
* `TauCeti.FormalCoordinate.constantCoeff_mem_range_of_mem`,
  `TauCeti.FormalCoordinate.coeff_one_mem_range_of_mem`,
  `TauCeti.FormalCoordinate.coeff_two_mem_range_of_mem`: integrality of the low coefficients.
* `TauCeti.FormalCoordinate.isUnit_substSubalgebra_iff`: the units of `O[[φ]]` are the elements
  whose constant coefficient is a unit of `O`.
* `TauCeti.FormalCoordinate.substSubalgebra_eq_iff`: `O[[ψ]] = O[[φ]]` exactly when `ψ ∈ O[[φ]]`
  and the linear coefficients of `ψ` and `φ` differ by a unit of `O`.
* `TauCeti.FormalCoordinate.subst_mem_substSubalgebra_of_mem`,
  `TauCeti.FormalCoordinate.rescale_mem_substSubalgebra_of_mem`: stability of `O[[φ]]` under
  substitutions and rescalings that map `φ` into it.

## References

* J. H. Silverman, *The Arithmetic of Elliptic Curves*, 2nd ed., Graduate Texts in Mathematics
  106, Springer (2009), Chapter IV, §1 (expansions in a local parameter with integral
  coefficients).
* `grh-lean`, https://github.com/lsernau/grh-lean, files
  `src/Lib/CM/FormalGroup/IntegralParameter.lean` (declarations `New.IsSeriesGenerator`,
  `New.IsSeriesGenerator.exists_subst_inverse`, `New.IsSeriesGenerator.smul_mem`,
  `New.IsSeriesGenerator.norm_constantCoeff_le_one_and_norm_coeff_one_le_one`,
  `New.IsSeriesGenerator.of_mem`, `New.IsSeriesGenerator.exists_mul_eq_one`,
  `New.IsSeriesGenerator.rescale_mem`, `New.IsSeriesGenerator.subst_injective`) and
  `src/Lib/CM/Integrality/LogTheta.lean` (`New.IsSeriesGenerator.isClosed`,
  `New.IsSeriesGenerator.norm_coeff_two_le_one`); Apache 2.0, Copyright 2026 Anthropic, PBC. The
  results here correspond to these declarations, which are stated over `ℂ_p`; the proofs follow
  the outline of that formal proof.
-/

public section

open PowerSeries

namespace TauCeti.FormalCoordinate

variable {R : Type*} [CommRing R] (O : Type*) [CommRing O] [Algebra O R]
  (φ : FormalCoordinate R)

/-- The `O`-subalgebra of `R⟦X⟧` of the power series `G(φ)` with `G ∈ O⟦X⟧`, for a formal
coordinate `φ` over `R`: the power series in the parameter `φ` with coefficients in `O`. When `O`
is the valuation ring of a nonarchimedean field `R`, these are the integral power series in `φ`. -/
noncomputable def substSubalgebra : Subalgebra O R⟦X⟧ :=
  (substAlgHom (R := O) φ.hasSubst).range

variable {O φ}

theorem mem_substSubalgebra {f : R⟦X⟧} :
    f ∈ φ.substSubalgebra O ↔ ∃ G : O⟦X⟧, G.subst φ.toPowerSeries = f := by
  simp [substSubalgebra, coe_substAlgHom]

@[simp]
theorem subst_mem_substSubalgebra (G : O⟦X⟧) : G.subst φ.toPowerSeries ∈ φ.substSubalgebra O :=
  mem_substSubalgebra.mpr ⟨G, rfl⟩

/-- The parameter `φ` itself is a power series in `φ`. -/
@[simp]
theorem toPowerSeries_mem_substSubalgebra : φ.toPowerSeries ∈ φ.substSubalgebra O := by
  simpa [subst_X φ.hasSubst] using subst_mem_substSubalgebra (φ := φ) (X : O⟦X⟧)

/-- Substituting the compositional inverse `φ⁻¹` into `G(φ)` gives back `G`, with its
coefficients read in `R`. -/
theorem subst_subst_inv_eq_map (G : O⟦X⟧) :
    PowerSeries.subst φ⁻¹.toPowerSeries (G.subst φ.toPowerSeries) =
      PowerSeries.map (algebraMap O R) G := by
  rw [subst_comp_subst_apply φ.hasSubst φ⁻¹.hasSubst, ← toPowerSeries_mul, mul_inv_cancel,
    toPowerSeries_one, map_algebraMap_eq_subst_X]

/-- **Substitution of a formal coordinate is injective** on power series over `O` when `O → R` is
injective: `G` is recovered from `G(φ)` by substituting `φ⁻¹`. -/
theorem subst_injective [FaithfulSMul O R] :
    Function.Injective fun G : O⟦X⟧ ↦ G.subst φ.toPowerSeries := fun G H h ↦
  map_injective _ (FaithfulSMul.algebraMap_injective O R) <| by
    rw [← subst_subst_inv_eq_map, ← subst_subst_inv_eq_map]
    exact congrArg _ h

/-- A series `f` is a power series in `φ` with coefficients in `O` exactly when `f(φ⁻¹)` has
coefficients in `O`. -/
theorem mem_substSubalgebra_iff_coeff_subst_inv_mem {f : R⟦X⟧} :
    f ∈ φ.substSubalgebra O ↔
      ∀ n, coeff n (f.subst φ⁻¹.toPowerSeries) ∈ Set.range (algebraMap O R) := by
  refine ⟨fun hf n ↦ ?_, fun h ↦ ?_⟩
  · obtain ⟨G, rfl⟩ := mem_substSubalgebra.mp hf
    exact ⟨coeff n G, by rw [subst_subst_inv_eq_map, coeff_map]⟩
  · choose c hc using h
    refine mem_substSubalgebra.mpr ⟨PowerSeries.mk c, φ⁻¹.substAlgEquiv.injective ?_⟩
    rw [substAlgEquiv_apply, substAlgEquiv_apply, subst_subst_inv_eq_map]
    ext n
    simp [hc]

open PowerSeries.WithPiTopology in
/-- **Closure under coefficientwise limits.** If `O` is closed in the topological ring `R`, then
the power series in `φ` with coefficients in `O` form a closed subset of `R⟦X⟧` for the
coefficientwise topology. -/
theorem isClosed_substSubalgebra [TopologicalSpace R] [IsTopologicalRing R]
    (hO : IsClosed (Set.range (algebraMap O R))) :
    IsClosed (φ.substSubalgebra O : Set R⟦X⟧) := by
  have hφ : Continuous fun f : R⟦X⟧ ↦ f.subst φ⁻¹.toPowerSeries :=
    continuous_id.powerSeries_subst continuous_const fun _ ↦ φ⁻¹.constantCoeff_toPowerSeries
  have h : (φ.substSubalgebra O : Set R⟦X⟧) =
      ⋂ n, (fun f : R⟦X⟧ ↦ coeff n (f.subst φ⁻¹.toPowerSeries)) ⁻¹' Set.range (algebraMap O R) :=
    Set.ext fun f ↦ by simp [mem_substSubalgebra_iff_coeff_subst_inv_mem]
  rw [h]
  exact isClosed_iInter fun n ↦ hO.preimage ((continuous_coeff R n).comp hφ)

section Equiv

variable [FaithfulSMul O R]

variable (O φ) in
/-- For injective `O → R`, substitution `G ↦ G(φ)` of a formal coordinate is an isomorphism of
`O`-algebras from `O⟦X⟧` onto the power series in `φ` with coefficients in `O`. -/
noncomputable def substSubalgebraEquiv : O⟦X⟧ ≃ₐ[O] φ.substSubalgebra O :=
  AlgEquiv.ofInjective (substAlgHom φ.hasSubst) (by rw [coe_substAlgHom]; exact subst_injective)

@[simp]
theorem coe_substSubalgebraEquiv_apply (G : O⟦X⟧) :
    (substSubalgebraEquiv O φ G : R⟦X⟧) = G.subst φ.toPowerSeries := by
  exact (AlgEquiv.ofInjective_apply _ _ G).trans (congrFun (coe_substAlgHom _) G)

@[simp]
theorem subst_substSubalgebraEquiv_symm_apply (f : φ.substSubalgebra O) :
    ((substSubalgebraEquiv O φ).symm f).subst φ.toPowerSeries = f := by
  rw [← coe_substSubalgebraEquiv_apply, AlgEquiv.apply_symm_apply]

/-- The series over `O` of an element `f` of `O[[φ]]`, read in `R`, is `f(φ⁻¹)`. -/
theorem map_substSubalgebraEquiv_symm_apply (f : φ.substSubalgebra O) :
    PowerSeries.map (algebraMap O R) ((substSubalgebraEquiv O φ).symm f) =
      (f : R⟦X⟧).subst φ⁻¹.toPowerSeries := by
  rw [← subst_subst_inv_eq_map, subst_substSubalgebraEquiv_symm_apply]

/-- **Units of `O[[φ]]`.** A power series in `φ` with coefficients in `O` is invertible among
them exactly when its constant coefficient is a unit of `O`. -/
theorem isUnit_substSubalgebra_iff {f : φ.substSubalgebra O} :
    IsUnit f ↔ ∃ u : Oˣ, algebraMap O R u = constantCoeff (f : R⟦X⟧) := by
  set G := (substSubalgebraEquiv O φ).symm f
  have hG : constantCoeff (f : R⟦X⟧) = algebraMap O R (constantCoeff G) := by
    rw [← subst_substSubalgebraEquiv_symm_apply f,
      constantCoeff_subst_of_constantCoeff_zero' φ.constantCoeff_toPowerSeries]
  rw [← isUnit_map_iff (substSubalgebraEquiv O φ).symm, hG, PowerSeries.isUnit_iff_constantCoeff]
  simp_rw [(FaithfulSMul.algebraMap_injective O R).eq_iff]
  exact ⟨fun h ↦ ⟨h.unit, rfl⟩, fun ⟨u, hu⟩ ↦ hu ▸ u.isUnit⟩

end Equiv

/-- **Low coefficients.** The constant coefficient of a power series in `φ` with coefficients in
`O` lies in `O`. -/
theorem constantCoeff_mem_range_of_mem {f : R⟦X⟧} (hf : f ∈ φ.substSubalgebra O) :
    constantCoeff f ∈ Set.range (algebraMap O R) := by
  obtain ⟨G, rfl⟩ := mem_substSubalgebra.mp hf
  exact ⟨constantCoeff G,
    (constantCoeff_subst_of_constantCoeff_zero' φ.constantCoeff_toPowerSeries G).symm⟩

/-- **Low coefficients.** If the linear coefficient of `φ` lies in `O`, for instance if
`φ = X + ⋯`, then so does the linear coefficient of every power series in `φ` with coefficients in
`O`. -/
theorem coeff_one_mem_range_of_mem (hφ : coeff 1 φ.toPowerSeries ∈ Set.range (algebraMap O R))
    {f : R⟦X⟧} (hf : f ∈ φ.substSubalgebra O) : coeff 1 f ∈ Set.range (algebraMap O R) := by
  obtain ⟨G, rfl⟩ := mem_substSubalgebra.mp hf
  obtain ⟨u, hu⟩ := hφ
  exact ⟨coeff 1 G * u, by rw [coeff_one_subst φ.constantCoeff_toPowerSeries, map_mul, hu]⟩

/-- **Low coefficients.** If the linear coefficient of `φ` lies in `O`, for instance if
`φ = X + ⋯`, then the quadratic coefficient of a power series in `φ` with coefficients in `O`
lies in `O` as soon as its linear coefficient vanishes. -/
theorem coeff_two_mem_range_of_mem (hφ : coeff 1 φ.toPowerSeries ∈ Set.range (algebraMap O R))
    {f : R⟦X⟧} (hf : f ∈ φ.substSubalgebra O) (hf₁ : coeff 1 f = 0) :
    coeff 2 f ∈ Set.range (algebraMap O R) := by
  obtain ⟨G, rfl⟩ := mem_substSubalgebra.mp hf
  obtain ⟨u, hu⟩ := hφ
  -- the linear coefficient of `G(φ)` is `G₁ φ₁`, with `φ₁` a unit, so `G₁` maps to zero
  rw [coeff_one_subst φ.constantCoeff_toPowerSeries] at hf₁
  have h₁ := φ.isUnit_coeff_one.mul_left_eq_zero.mp hf₁
  -- the quadratic coefficient of `G(φ)` is `G₁ φ₂ + G₂ φ₁²`
  have h₂ : coeff 2 (G.subst φ.toPowerSeries) = algebraMap O R (coeff 1 G) *
      coeff 2 φ.toPowerSeries + algebraMap O R (coeff 2 G) * coeff 1 φ.toPowerSeries ^ 2 := by
    simp [coeff_subst_eq_sum_range _ φ.constantCoeff_toPowerSeries, Finset.sum_range_succ, sq,
      coeff_mul, Finset.Nat.antidiagonal_succ, Algebra.smul_def, coeff_one]
  exact ⟨coeff 2 G * u ^ 2, by rw [h₂, h₁, zero_mul, zero_add, map_mul, map_pow, hu]⟩

/-- An element of `O[[φ]]` without constant coefficient is `G(φ)` for a series `G` over `O`
without constant coefficient. -/
theorem exists_constantCoeff_eq_zero_subst_eq {f : R⟦X⟧} (hf : f ∈ φ.substSubalgebra O)
    (hf₀ : constantCoeff f = 0) :
    ∃ G : O⟦X⟧, constantCoeff G = 0 ∧ G.subst φ.toPowerSeries = f := by
  obtain ⟨G, rfl⟩ := mem_substSubalgebra.mp hf
  rw [constantCoeff_subst_of_constantCoeff_zero' φ.constantCoeff_toPowerSeries] at hf₀
  -- removing the constant term of `G` changes `G(φ)` by its image in `R`, which is zero
  refine ⟨G - C (constantCoeff G), by simp, ?_⟩
  rw [subst_sub φ.hasSubst, C_eq_algebraMap, ← coe_substAlgHom φ.hasSubst, AlgHom.commutes,
    MvPowerSeries.algebraMap_apply, hf₀, map_zero, sub_zero]

/-- **Stability under substitution.** If a substitution `f ↦ f(a)` maps `φ` to a power series in
`φ` with coefficients in `O`, then it maps every power series in `φ` with coefficients in `O` to
one. -/
theorem subst_mem_substSubalgebra_of_mem {a : R⟦X⟧} (ha : constantCoeff a = 0)
    (hφa : φ.toPowerSeries.subst a ∈ φ.substSubalgebra O) {f : R⟦X⟧}
    (hf : f ∈ φ.substSubalgebra O) : f.subst a ∈ φ.substSubalgebra O := by
  obtain ⟨H, hH₀, hH⟩ := exists_constantCoeff_eq_zero_subst_eq hφa
    (constantCoeff_subst_eq_zero ha _ φ.constantCoeff_toPowerSeries)
  obtain ⟨G, rfl⟩ := mem_substSubalgebra.mp hf
  -- `G(φ)(a) = G(φ(a)) = G(H(φ)) = (G(H))(φ)`
  rw [subst_comp_subst_apply φ.hasSubst (.of_constantCoeff_zero' ha), ← hH,
    ← subst_comp_subst_apply (.of_constantCoeff_zero' hH₀) φ.hasSubst]
  exact subst_mem_substSubalgebra _

/-- **Stability under rescaling.** If `φ(c X)` is a power series in `φ` with coefficients in `O`,
then so is `f(c X)` for every power series `f` in `φ` with coefficients in `O`. -/
theorem rescale_mem_substSubalgebra_of_mem {c : R}
    (hc : rescale c φ.toPowerSeries ∈ φ.substSubalgebra O) {f : R⟦X⟧}
    (hf : f ∈ φ.substSubalgebra O) : rescale c f ∈ φ.substSubalgebra O := by
  rw [rescale_eq_subst] at hc ⊢
  exact subst_mem_substSubalgebra_of_mem (by simp) hc hf

/-- If `ψ` is a power series in `φ` with coefficients in `O`, then so is every power series in
`ψ` with coefficients in `O`. -/
theorem substSubalgebra_le_of_mem {ψ : FormalCoordinate R}
    (hψ : ψ.toPowerSeries ∈ φ.substSubalgebra O) : ψ.substSubalgebra O ≤ φ.substSubalgebra O :=
  fun f hf ↦ by
    obtain ⟨G, rfl⟩ := mem_substSubalgebra.mp hf
    obtain ⟨H, hH₀, hH⟩ := exists_constantCoeff_eq_zero_subst_eq hψ ψ.constantCoeff_toPowerSeries
    rw [← hH, ← subst_comp_subst_apply (.of_constantCoeff_zero' hH₀) φ.hasSubst]
    exact subst_mem_substSubalgebra _

/-- **Change of parameter.** For formal coordinates `ψ` and `φ` over `R`, the power series in `ψ`
and in `φ` with coefficients in `O` agree exactly when `ψ` is a power series in `φ` with
coefficients in `O` whose linear coefficient is a unit of `O` times that of `φ`. In particular
`O[[ψ]] = O[[φ]]` when `ψ ∈ O[[φ]]` and `ψ`, `φ` both have linear coefficient `1`. -/
theorem substSubalgebra_eq_iff [FaithfulSMul O R] {ψ : FormalCoordinate R} :
    ψ.substSubalgebra O = φ.substSubalgebra O ↔ ψ.toPowerSeries ∈ φ.substSubalgebra O ∧
      ∃ u : Oˣ, coeff 1 ψ.toPowerSeries = algebraMap O R u * coeff 1 φ.toPowerSeries := by
  have hinj := FaithfulSMul.algebraMap_injective O R
  have hφ₁ := φ.isUnit_coeff_one
  constructor
  · intro h
    have hψ : ψ.toPowerSeries ∈ φ.substSubalgebra O := h ▸ toPowerSeries_mem_substSubalgebra
    refine ⟨hψ, ?_⟩
    obtain ⟨G, hG⟩ := mem_substSubalgebra.mp hψ
    obtain ⟨H, hH⟩ := mem_substSubalgebra.mp (h.symm ▸ toPowerSeries_mem_substSubalgebra)
    -- comparing linear coefficients in `φ = H(G(φ))` shows that `H₁ G₁ = 1`
    have h₁ := congrArg (coeff 1) hH
    rw [coeff_one_subst ψ.constantCoeff_toPowerSeries, ← hG,
      coeff_one_subst φ.constantCoeff_toPowerSeries, ← mul_assoc, ← map_mul] at h₁
    have hHG : coeff 1 H * coeff 1 G = 1 :=
      hinj (by rw [map_one]; exact hφ₁.mul_eq_right.mp h₁)
    exact ⟨(IsUnit.of_mul_eq_one_right _ hHG).unit, by
      rw [IsUnit.unit_spec, ← hG, coeff_one_subst φ.constantCoeff_toPowerSeries]⟩
  · rintro ⟨hψ, u, hu⟩
    refine le_antisymm (substSubalgebra_le_of_mem hψ) (substSubalgebra_le_of_mem ?_)
    obtain ⟨G, hG₀, hG⟩ := exists_constantCoeff_eq_zero_subst_eq hψ ψ.constantCoeff_toPowerSeries
    -- `G` is a formal coordinate over `O`, with linear coefficient `u`
    have hG₁ : coeff 1 G = u := hinj <| hφ₁.mul_right_cancel <| by
      rw [← hu, ← hG, coeff_one_subst φ.constantCoeff_toPowerSeries]
    let Γ : FormalCoordinate O := ⟨G, hG₀, hG₁ ▸ u.isUnit⟩
    have hΓ : Γ.toPowerSeries = G := rfl
    -- `φ = Γ⁻¹(Γ(φ)) = Γ⁻¹(ψ)`
    have hφ : Γ⁻¹.toPowerSeries.subst ψ.toPowerSeries = φ.toPowerSeries := by
      rw [← hG, ← hΓ, ← subst_comp_subst_apply Γ.hasSubst φ.hasSubst, ← toPowerSeries_mul,
        inv_mul_cancel, toPowerSeries_one, subst_X φ.hasSubst]
    exact hφ ▸ subst_mem_substSubalgebra _

end TauCeti.FormalCoordinate
