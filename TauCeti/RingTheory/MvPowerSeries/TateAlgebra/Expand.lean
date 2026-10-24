/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Finiteness.Basic
public import TauCeti.RingTheory.MvPowerSeries.Expand
public import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.Rescale

/-!
# Restricted series at radii in the divisible hull of the value group

Substituting `X i ↦ X i ^ p` multiplies every exponent by `p`, so a series is restricted at the
polyradii `r ^ p` exactly when its expansion is restricted at `r`
(`MvPowerSeries.isRestricted_expand_iff`), with the same Gauss norm. The expansion is therefore
an isometric algebra map

```text
R{X/r^p} → R{X/r},   f(X) ↦ f(X^p).
```

For any set of variables and any exponent `ν`, the component `f_ν` of a restricted series `f` at
`r`, with coefficients `coeff μ f_ν = coeff (p • μ + ν) f`, is restricted at `r ^ p` and
satisfies `‖f_ν‖ r^ν ≤ ‖f‖`, with equality for some `ν` with `ν i < p` for all `i`. In finitely
many variables, every restricted series at `r` is uniquely a sum `∑ X^ν f_ν(X^p)` over the
finitely many exponents `ν` with `ν i < p`, so the expansion is a finite injective map and the
algebra at `r` is free over the algebra at `r ^ p` on these monomials.

Combined with the rescaling `X i ↦ u i * X i` by multiplicative units, this gives the classical
presentation of Tate algebras at radii in the divisible hull of `|K×|`: if `‖u i‖ * r i ^ p = 1`,
then `Y i ↦ u i X i ^ p` is an injective isometric algebra map from the unit-radius Tate algebra
`R⟨Y⟩` to `R{X/r}`, which is finite in finitely many variables. Over a nonarchimedean normed
field `K` and finitely many variables, such `p` and `u` exist as soon as every `r i` has a
positive power in `|K×|`.

## Main definitions

* `TauCeti.MvPowerSeries.restrictedExpand`: the isometric algebra map
  `R{X/r^p} → R{X/r}`, `f(X) ↦ f(X^p)`.
* `TauCeti.MvPowerSeries.restrictedExpandComponent`: the component `f_ν` of `f`, with
  coefficients `coeff μ f_ν = coeff (p • μ + ν) f`.
* `TauCeti.MvPowerSeries.restrictedRescaleExpand`: the algebra map `R⟨Y⟩ → R{X/r}`,
  `Y i ↦ u i X i ^ p`.

## Main results

* `TauCeti.MvPowerSeries.norm_restrictedExpand`: the expansion preserves Gauss norms.
* `TauCeti.MvPowerSeries.sum_monomial_mul_restrictedExpand_component` and
  `TauCeti.MvPowerSeries.restrictedExpandComponent_sum_monomial_mul_restrictedExpand`: existence
  and uniqueness of the decomposition `f = ∑ X^ν f_ν(X^p)` in finitely many variables.
* `TauCeti.MvPowerSeries.exists_norm_restrictedExpandComponent_mul_prod_eq`: the Gauss norm of `f`
  is the largest of the weighted norms `‖f_ν‖ r^ν`.
* `TauCeti.MvPowerSeries.restrictedExpand_finite` and
  `TauCeti.MvPowerSeries.restrictedRescaleExpand_finite`: in finitely many variables, both maps
  are finite.
* `TauCeti.MvPowerSeries.exists_injective_finite_algHom_of_norm_mul_pow_eq_one`: over a normed
  field, if every `r i` has a positive power whose inverse is the norm of a scalar, the algebra
  at `r` is finite over the unit-radius Tate algebra through an injective algebra map.

## References

* Bosch, Güntzer, Remmert, *Non-Archimedean Analysis*, §6.1.5.
-/

public section

namespace TauCeti.MvPowerSeries

open Filter _root_.MvPowerSeries
open scoped Topology

variable {σ R : Type*} [NormedCommRing R] [IsUltrametricDist R] {r t : σ → ℝ}

section Expand

variable (p : ℕ) (hp : p ≠ 0) (ht : ∀ i, r i ^ p = t i)

/-- **Expansion of restricted series.** Substituting `X i ↦ X i ^ p` is an algebra map
`R{X/r^p} → R{X/r}`. -/
noncomputable def restrictedExpand :
    IsRestricted.subring (R := R) t →ₐ[R] IsRestricted.subring (R := R) r where
  toFun f := ⟨expand p hp f, (isRestricted_expand_iff p hp ht).mpr f.2⟩
  map_one' := Subtype.ext (map_one (expand p hp))
  map_mul' f g := Subtype.ext (map_mul (expand p hp) (f : MvPowerSeries σ R) g)
  map_zero' := Subtype.ext (map_zero (expand p hp))
  map_add' f g := Subtype.ext (map_add (expand p hp) (f : MvPowerSeries σ R) g)
  commutes' a := Subtype.ext <| by
    simp only [coe_algebraMap_isRestrictedSubring, expand_C]

/-- The underlying formal series of `restrictedExpand` is Mathlib's expansion. -/
@[simp]
theorem coe_restrictedExpand (f : IsRestricted.subring (R := R) t) :
    (restrictedExpand p hp ht f : MvPowerSeries σ R) = expand p hp f :=
  (rfl)

/-- The expansion sends `X i` to `X i ^ p`. -/
@[simp]
theorem restrictedExpand_X (i : σ) :
    restrictedExpand p hp ht
        (⟨X i, isRestricted_X t i⟩ : IsRestricted.subring (R := R) t) =
      (⟨X i, isRestricted_X r i⟩ : IsRestricted.subring (R := R) r) ^ p :=
  Subtype.ext (by simp)

/-- The expansion is injective. -/
theorem restrictedExpand_injective :
    Function.Injective (restrictedExpand (R := R) p hp ht) := fun f g h ↦ by
  ext μ : 2
  simpa using congr(coeff (p • μ) ($h : MvPowerSeries σ R))

variable [∀ i, Fact (0 < r i)] [∀ i, Fact (0 < t i)]

/-- The expansion preserves the Gauss norms. -/
@[simp]
theorem norm_restrictedExpand (f : IsRestricted.subring (R := R) t) :
    ‖restrictedExpand p hp ht f‖ = ‖f‖ := by
  refine le_antisymm ((norm_le_iff (norm_nonneg f)).2 fun α ↦ ?_)
    ((norm_le_iff (norm_nonneg _)).2 fun μ ↦ ?_)
  · rw [coe_restrictedExpand]
    by_cases hdvd : ∀ i, p ∣ α i
    · obtain ⟨μ, rfl⟩ : ∃ μ, p • μ = α := ⟨_, Finsupp.nsmul_mapRange_div p hdvd⟩
      rw [coeff_expand_smul, prod_pow_nsmul p ht]
      exact norm_coeff_mul_prod_le f μ
    · obtain ⟨i, hi⟩ := not_forall.mp hdvd
      simp [coeff_expand_of_not_dvd p hp _ hi]
  · simpa [prod_pow_nsmul p ht] using norm_coeff_mul_prod_le (restrictedExpand p hp ht f) (p • μ)

/-- The expansion is an isometry for the Gauss norms. -/
theorem isometry_restrictedExpand : Isometry (restrictedExpand (R := R) p hp ht) :=
  AddMonoidHomClass.isometry_iff_norm _ |>.mpr (norm_restrictedExpand p hp ht)

end Expand

section Component

variable {p : ℕ} (hp : p ≠ 0) (ht : ∀ i, r i ^ p = t i) [∀ i, Fact (0 < r i)]

include hp ht in
/-- The coefficient family `μ ↦ coeff (p • μ + ν) f` of a restricted series `f` at the polyradii
`r` is restricted at the polyradii `r ^ p`. -/
private theorem isRestricted_component (ν : σ →₀ ℕ) (f : IsRestricted.subring (R := R) r) :
    IsRestricted t (fun μ ↦ coeff (p • μ + ν) (f : MvPowerSeries σ R) : MvPowerSeries σ R) := by
  have hi : Function.Injective fun μ : σ →₀ ℕ ↦ p • μ + ν :=
    (add_left_injective ν).comp (nsmul_right_injective hp)
  have h := (f.2.comp hi.tendsto_cofinite).const_mul (ν.prod (r · ^ ·))⁻¹
  rw [mul_zero] at h
  refine h.congr fun μ ↦ ?_
  have hc : coeff μ (fun μ ↦ coeff (p • μ + ν) (f : MvPowerSeries σ R) : MvPowerSeries σ R) =
      coeff (p • μ + ν) (f : MvPowerSeries σ R) := coeff_apply _ μ
  rw [hc, Function.comp_apply, prod_pow_add, prod_pow_nsmul p ht]
  field_simp [(prod_pow_pos (c := r) ν).ne']

/-- The component `f_ν` in the decomposition `f = ∑ X^ν f_ν(X^p)` of a restricted series at the
polyradii `r`: the restricted series at the polyradii `r ^ p` whose coefficient at `μ` is the
coefficient of `f` at `p • μ + ν`. -/
noncomputable def restrictedExpandComponent (ν : σ →₀ ℕ) (f : IsRestricted.subring (R := R) r) :
    IsRestricted.subring (R := R) t :=
  ⟨fun μ ↦ coeff (p • μ + ν) (f : MvPowerSeries σ R), isRestricted_component hp ht ν f⟩

/-- The coefficients of the component `f_ν`. -/
@[simp]
theorem coeff_restrictedExpandComponent (ν μ : σ →₀ ℕ) (f : IsRestricted.subring (R := R) r) :
    coeff μ (restrictedExpandComponent hp ht ν f : MvPowerSeries σ R) =
      coeff (p • μ + ν) (f : MvPowerSeries σ R) :=
  coeff_apply _ μ

variable [∀ i, Fact (0 < t i)]

/-- **Norm estimate for the components.** The weighted norm `‖f_ν‖ r^ν` of each component is at
most the Gauss norm of `f`. -/
theorem norm_restrictedExpandComponent_mul_prod_le (ν : σ →₀ ℕ)
    (f : IsRestricted.subring (R := R) r) :
    ‖restrictedExpandComponent hp ht ν f‖ * ν.prod (r · ^ ·) ≤ ‖f‖ := by
  rw [← le_div_iff₀ (prod_pow_pos ν), norm_le_iff (div_nonneg (norm_nonneg f)
    (prod_pow_pos ν).le)]
  intro μ
  rw [le_div_iff₀ (prod_pow_pos ν), coeff_restrictedExpandComponent, mul_assoc,
    ← prod_pow_nsmul p ht, ← prod_pow_add]
  exact norm_coeff_mul_prod_le f _

/-- **The Gauss norm is attained by a component.** Some exponent `ν` with `ν i < p` for all `i`
has `‖f_ν‖ r^ν = ‖f‖`; with `norm_restrictedExpandComponent_mul_prod_le`, the Gauss norm of
`f` is the largest of the weighted norms of its components. -/
theorem exists_norm_restrictedExpandComponent_mul_prod_eq
    (f : IsRestricted.subring (R := R) r) :
    ∃ ν : σ →₀ ℕ, (∀ i, ν i < p) ∧
      ‖restrictedExpandComponent hp ht ν f‖ * ν.prod (r · ^ ·) = ‖f‖ := by
  obtain ⟨α, hα⟩ := exists_achievesGaussNorm f
  set ν := α.mapRange (· % p) (Nat.zero_mod p)
  set μ := α.mapRange (· / p) (Nat.zero_div p)
  refine ⟨ν, fun i ↦ Nat.mod_lt _ (Nat.pos_of_ne_zero hp),
    le_antisymm (norm_restrictedExpandComponent_mul_prod_le hp ht ν f) ?_⟩
  have hμν : p • μ + ν = α := Finsupp.nsmul_mapRange_div_add_mapRange_mod p α
  calc ‖f‖ = ‖coeff α (f : MvPowerSeries σ R)‖ * α.prod (r · ^ ·) := hα.symm
    _ = ‖coeff μ (restrictedExpandComponent hp ht ν f : MvPowerSeries σ R)‖ *
          μ.prod (t · ^ ·) * ν.prod (r · ^ ·) := by
      rw [coeff_restrictedExpandComponent, hμν, ← prod_pow_nsmul p ht, mul_assoc,
        ← prod_pow_add, hμν]
    _ ≤ ‖restrictedExpandComponent hp ht ν f‖ * ν.prod (r · ^ ·) :=
      mul_le_mul_of_nonneg_right (norm_coeff_mul_prod_le _ μ) (prod_pow_pos ν).le

end Component

section Decomposition

variable [Fintype σ] [DecidableEq σ] {p : ℕ} (hp : p ≠ 0) (ht : ∀ i, r i ^ p = t i)
  [∀ i, Fact (0 < r i)]

/-- **Existence of the decomposition.** Every restricted series at the polyradii `r` in finitely
many variables is the sum `∑ X^ν f_ν(X^p)` over the exponents `ν` with `ν i < p`, where `f_ν`
are its components. -/
theorem sum_monomial_mul_restrictedExpand_component (f : IsRestricted.subring (R := R) r) :
    ∑ ν : σ → Fin p, (⟨monomial (Finsupp.equivFunOnFinite.symm (Fin.val ∘ ν)) 1,
      isRestricted_monomial r _ 1⟩ : IsRestricted.subring (R := R) r) * restrictedExpand p hp ht
      (restrictedExpandComponent hp ht (Finsupp.equivFunOnFinite.symm (Fin.val ∘ ν)) f) = f := by
  apply Subtype.ext
  ext α
  set ν : σ → Fin p := fun i ↦ ⟨α i % p, Nat.mod_lt _ (Nat.pos_of_ne_zero hp)⟩
  have hα : p • α.mapRange (· / p) (Nat.zero_div p) +
      Finsupp.equivFunOnFinite.symm (Fin.val ∘ ν) = α := by
    convert Finsupp.nsmul_mapRange_div_add_mapRange_mod p α using 2
    ext i
    simp [ν]
  push_cast
  simp only [coe_restrictedExpand]
  conv_lhs => rw [← hα]
  rw [coeff_sum_monomial_mul_expand p hp, coeff_restrictedExpandComponent, hα]

/-- **Uniqueness of the decomposition.** The components of a sum `∑ X^ν g_ν(X^p)` over the
exponents `ν` with `ν i < p` are the series `g_ν`. -/
theorem restrictedExpandComponent_sum_monomial_mul_restrictedExpand
    (g : (σ → Fin p) → IsRestricted.subring (R := R) t) (ν : σ → Fin p) :
    restrictedExpandComponent hp ht (Finsupp.equivFunOnFinite.symm (Fin.val ∘ ν))
      (∑ ν', (⟨monomial (Finsupp.equivFunOnFinite.symm (Fin.val ∘ ν')) 1,
        isRestricted_monomial r _ 1⟩ : IsRestricted.subring (R := R) r) *
          restrictedExpand p hp ht (g ν')) = g ν := by
  apply Subtype.ext
  ext μ
  rw [coeff_restrictedExpandComponent]
  push_cast
  simp only [coe_restrictedExpand]
  exact coeff_sum_monomial_mul_expand p hp (fun ν' ↦ (g ν' : MvPowerSeries σ R)) μ ν

end Decomposition

section Finite

variable {p : ℕ} (hp : p ≠ 0) (ht : ∀ i, r i ^ p = t i) [∀ i, Fact (0 < r i)]

/-- **The expansion is finite.** In finitely many variables, the algebra of restricted series at
the polyradii `r` is generated as a module over the algebra at the polyradii `r ^ p` by the
monomials `X^ν` with `ν i < p`. -/
theorem restrictedExpand_finite [Finite σ] : (restrictedExpand (R := R) p hp ht).Finite := by
  classical
  have := Fintype.ofFinite σ
  let _ := (restrictedExpand (R := R) p hp ht).toRingHom.toAlgebra
  refine ⟨⟨Finset.univ.image fun ν : σ → Fin p ↦
    (⟨monomial (Finsupp.equivFunOnFinite.symm (Fin.val ∘ ν)) 1, isRestricted_monomial r _ 1⟩ :
      IsRestricted.subring (R := R) r), ?_⟩⟩
  refine Submodule.eq_top_iff'.mpr fun f ↦ ?_
  rw [← sum_monomial_mul_restrictedExpand_component hp ht f]
  refine Submodule.sum_mem _ fun ν _ ↦ ?_
  rw [mul_comm]
  -- for the module structure induced by the expansion, `g • m` is `restrictedExpand g * m` by
  -- `RingHom.smul_toAlgebra`, which holds by definition
  exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))

end Finite

section Rescale

variable (p : ℕ) (hp : p ≠ 0) [∀ i, Fact (0 < r i)] (u : σ → Rˣ)
  (hu : ∀ i, IsNormMulUnit (u i : R)) (hr : ∀ i, ‖(u i : R)‖ * r i ^ p = 1)

/-- The polyradii `r ^ p` are positive. -/
private theorem fact_pow_pos (i : σ) : Fact (0 < r i ^ p) := ⟨pow_pos Fact.out p⟩

/-- If the multiplicative units `u i` satisfy `‖u i‖ * r i ^ p = 1`, substituting
`Y i ↦ u i * X i ^ p` is an algebra map from the unit-radius algebra `R⟨Y⟩` to the restricted
series `R{X/r}`: the rescaling by `u` from the unit radii to the radii `r ^ p`, followed by the
expansion. In finitely many variables it is finite (`restrictedRescaleExpand_finite`). -/
noncomputable def restrictedRescaleExpand :
    IsRestricted.subring (R := R) (fun _ : σ ↦ (1 : ℝ)) →ₐ[R] IsRestricted.subring (R := R) r :=
  letI := fact_pow_pos (r := r) p
  (restrictedExpand p hp fun _ ↦ rfl).comp (restrictedRescaleEquiv u hu hr).toAlgHom

/-- The underlying formal series of `restrictedRescaleExpand u f` is `f(u X^p)`. -/
@[simp]
theorem coe_restrictedRescaleExpand (f : IsRestricted.subring (R := R) (fun _ : σ ↦ (1 : ℝ))) :
    (restrictedRescaleExpand p hp u hu hr f : MvPowerSeries σ R) =
      expand p hp (MvPowerSeries.rescale (fun i ↦ (u i : R)) f) := by
  let _ := fact_pow_pos (r := r) p
  simp [restrictedRescaleExpand]

/-- The map `restrictedRescaleExpand` sends `Y i` to `u i * X i ^ p`. -/
@[simp]
theorem restrictedRescaleExpand_X (i : σ) :
    restrictedRescaleExpand p hp u hu hr
        (⟨X i, isRestricted_X _ i⟩ : IsRestricted.subring (R := R) (fun _ : σ ↦ (1 : ℝ))) =
      algebraMap R (IsRestricted.subring (R := R) r) (u i : R) *
        (⟨X i, isRestricted_X r i⟩ : IsRestricted.subring (R := R) r) ^ p := by
  let _ := fact_pow_pos (r := r) p
  simp [restrictedRescaleExpand]

/-- The map `restrictedRescaleExpand` preserves the Gauss norms. -/
@[simp]
theorem norm_restrictedRescaleExpand
    (f : IsRestricted.subring (R := R) (fun _ : σ ↦ (1 : ℝ))) :
    ‖restrictedRescaleExpand p hp u hu hr f‖ = ‖f‖ := by
  let _ := fact_pow_pos (r := r) p
  simp [restrictedRescaleExpand]

/-- The map `restrictedRescaleExpand` is an isometry for the Gauss norms. -/
theorem isometry_restrictedRescaleExpand :
    Isometry (restrictedRescaleExpand (R := R) p hp u hu hr) :=
  AddMonoidHomClass.isometry_iff_norm _ |>.mpr (norm_restrictedRescaleExpand p hp u hu hr)

/-- The map `restrictedRescaleExpand` is injective. -/
theorem restrictedRescaleExpand_injective :
    Function.Injective (restrictedRescaleExpand (R := R) p hp u hu hr) :=
  (isometry_restrictedRescaleExpand p hp u hu hr).injective

/-- **The restricted series at `r` are finite over the unit Tate algebra** through
`Y i ↦ u i * X i ^ p`, in finitely many variables. -/
theorem restrictedRescaleExpand_finite [Finite σ] :
    (restrictedRescaleExpand (R := R) p hp u hu hr).Finite := by
  let _ := fact_pow_pos (r := r) p
  exact (restrictedExpand_finite hp fun _ ↦ rfl).comp
    (AlgHom.Finite.of_surjective _ (restrictedRescaleEquiv u hu hr).surjective)

end Rescale

/-- **Tate algebras at radii in the divisible hull of the value group.** Over a nonarchimedean
normed field `K` and finitely many variables, if every radius `r i` has a positive power
`r i ^ n` with `‖a‖ * r i ^ n = 1` for some scalar `a`, the restricted series at the polyradii `r`
form a finite algebra over the unit-radius Tate algebra through an injective algebra map. -/
theorem exists_injective_finite_algHom_of_norm_mul_pow_eq_one {K : Type*} [NormedField K]
    [IsUltrametricDist K] [Finite σ] {r : σ → ℝ} [∀ i, Fact (0 < r i)]
    (hr : ∀ i, ∃ n ≠ 0, ∃ a : K, ‖a‖ * r i ^ n = 1) :
    ∃ φ : IsRestricted.subring (R := K) (fun _ : σ ↦ (1 : ℝ)) →ₐ[K]
      IsRestricted.subring (R := K) r, Function.Injective φ ∧ φ.Finite := by
  classical
  have := Fintype.ofFinite σ
  choose n hn a ha using hr
  -- a common exponent `p` and the scalars `a i ^ (p / n i)`
  set p := ∏ i, n i
  have hp : p ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i _ ↦ hn i
  have hdvd (i : σ) : n i ∣ p := Finset.dvd_prod_of_mem n (Finset.mem_univ i)
  have hnorm (i : σ) : ‖a i ^ (p / n i)‖ * r i ^ p = 1 := by
    obtain ⟨k, hk⟩ := hdvd i
    rw [hk, Nat.mul_div_cancel_left k (Nat.pos_of_ne_zero (hn i)), norm_pow, pow_mul, ← mul_pow,
      ha, one_pow]
  have hne (i : σ) : a i ^ (p / n i) ≠ 0 := norm_ne_zero_iff.mp fun h ↦ by
    simpa [h] using hnorm i
  let u (i : σ) : Kˣ := Units.mk0 _ (hne i)
  have hu (i : σ) : IsNormMulUnit (u i : K) := (isNormMulUnit_iff_isUnit _).mpr (u i).isUnit
  exact ⟨restrictedRescaleExpand p hp u hu hnorm,
    restrictedRescaleExpand_injective p hp u hu hnorm,
    restrictedRescaleExpand_finite p hp u hu hnorm⟩

end TauCeti.MvPowerSeries
