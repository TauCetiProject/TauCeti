/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Finiteness.Basic
public import TauCeti.Data.Finsupp.DivMod
public import TauCeti.RingTheory.MvPowerSeries.Expand
public import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.Rescale

import TauCeti.RingTheory.MvPowerSeries.Basic
import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.Map
import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.Module.Basic

/-!
# Restricted series at radii in the divisible hull of the value group

Substituting `X i ↦ X i ^ p` multiplies every exponent by `p`, so a series is restricted at the
polyradii `r ^ p` exactly when its expansion is restricted at `r`
(`MvPowerSeries.isRestricted_expand_iff`), with the same Gauss norm. The expansion is therefore
an isometric algebra map

```text
R{X/r^p} → R{X/r},   f(X) ↦ f(X^p).
```

The coefficient components and their norm estimates work over any ultrametric normed ring. For
any set of variables and any exponent `ν`, the component `f_ν` of a restricted series `f` at `r`,
with coefficients `coeff μ f_ν = coeff (p • μ + ν) f`, is restricted at `r ^ p` and satisfies
`‖f_ν‖ r^ν ≤ ‖f‖`, with equality for some `ν` with `ν i < p` for all `i`. With commutative
coefficients and finitely many variables, every restricted series at `r` is uniquely a sum
`∑ X^ν f_ν(X^p)` over the finitely many exponents `ν` with `ν i < p`, so the expansion is a
finite injective map and the algebra at `r` is free over the algebra at `r ^ p` on these
monomials.

Combined with the rescaling `X i ↦ u i * X i` by multiplicative units, this gives the classical
presentation of Tate algebras at radii in the divisible hull of `|K×|`: if `‖u i‖ * r i ^ p = 1`,
then `Y i ↦ u i X i ^ p` is an injective isometric algebra map from the unit-radius Tate algebra
`R⟨Y⟩` to `R{X/r}`, which is finite in finitely many variables. Over a nonarchimedean normed
field `K` and finitely many variables, such `p` and `u` exist as soon as every `r i` has a
positive power in `|K×|`.

Over a normed field `K` and an ultrametric normed `K`-algebra `K'`, combining coefficient base
change along `algebraMap K K'` with variable expansion `X i ↦ X i ^ q` gives an algebra map
`K{X / c} →ₐ[K] K'{X / r}` (`TauCeti.MvPowerSeries.restrictedExpandAlgebraMap`). For any
`K`-submodule `E ≤ K'`, the series in `K'{X / r}` with coefficients in `E` form a `K`-submodule
`TauCeti.MvPowerSeries.restrictedCoeffSubmodule r E` closed under and reflecting left
multiplication by nonzero expanded scalar series. Composing a `q`-adic component extraction with a
bounded `K`-linear functional `E →ₗ[K] K` yields a norm-bounded `K`-linear map
`TauCeti.MvPowerSeries.restrictedExpandComponentDual` into `K{X / c}` commuting with left
multiplication by `restrictedExpandAlgebraMap`, separating nonzero series whenever bounded
functionals separate `E`.

## Main definitions

* `TauCeti.MvPowerSeries.restrictedExpand`: the isometric algebra map
  `R{X/r^p} → R{X/r}`, `f(X) ↦ f(X^p)`.
* `TauCeti.MvPowerSeries.restrictedExpandComponent`: the component `f_ν` of `f`, with
  coefficients `coeff μ f_ν = coeff (p • μ + ν) f`.
* `TauCeti.MvPowerSeries.restrictedRescaleExpand`: the algebra map `R⟨Y⟩ → R{X/r}`,
  `Y i ↦ u i X i ^ p`.
* `TauCeti.MvPowerSeries.restrictedExpandAlgebraMap`: the `K`-algebra map
  `K{X / c} →ₐ[K] K'{X / r}` combining `algebraMap K K'` with `X i ↦ X i ^ q`.
* `TauCeti.MvPowerSeries.restrictedCoeffSubmodule`: the `K`-submodule of `K'{X / r}` of series
  whose coefficients all lie in a `K`-submodule `E ≤ K'`.
* `TauCeti.MvPowerSeries.restrictedExpandComponentDual`: the `K`-linear map
  `restrictedCoeffSubmodule r E →ₗ[K] K{X / c}` obtained by applying a bounded functional on `E`
  to the `ν`-th `q`-adic component.

## Main results

* `TauCeti.MvPowerSeries.norm_restrictedExpand`: the expansion preserves Gauss norms.
* `TauCeti.MvPowerSeries.sum_monomial_mul_restrictedExpand_restrictedExpandComponent` and
  `TauCeti.MvPowerSeries.restrictedExpandComponent_sum_monomial_mul_restrictedExpand`: existence
  and uniqueness of the decomposition `f = ∑ X^ν f_ν(X^p)` in finitely many variables.
* `TauCeti.MvPowerSeries.exists_norm_restrictedExpandComponent_mul_prod_eq`: the Gauss norm of `f`
  is the largest of the weighted norms `‖f_ν‖ r^ν`.
* `TauCeti.MvPowerSeries.restrictedExpandComponent_restrictedExpand_mul`: multiplying by an
  expanded series `g(X^p)` commutes with extracting the `ν`-th component when `ν i < p`.
* `TauCeti.MvPowerSeries.restrictedExpand_finite` and
  `TauCeti.MvPowerSeries.restrictedRescaleExpand_finite`: in finitely many variables, both maps
  are finite.
* `TauCeti.MvPowerSeries.exists_injective_finite_algHom_of_norm_mul_pow_eq_one`: over a normed
  field, if every `r i` has a positive power whose inverse is the norm of a scalar, the algebra
  at `r` is finite over the unit-radius Tate algebra through an injective algebra map.
* `TauCeti.MvPowerSeries.restrictedExpandAlgebraMap_injective` and
  `TauCeti.MvPowerSeries.norm_restrictedExpandAlgebraMap`: injectivity and Gauss-norm preservation
  for `restrictedExpandAlgebraMap`.
* `TauCeti.MvPowerSeries.mul_mem_restrictedCoeffSubmodule` and
  `TauCeti.MvPowerSeries.mem_restrictedCoeffSubmodule_of_mul_mem`: left multiplication by a
  (nonzero) expanded scalar series preserves and reflects membership in
  `restrictedCoeffSubmodule r E`.
* `TauCeti.MvPowerSeries.restrictedExpandComponentDual_mul` and
  `TauCeti.MvPowerSeries.norm_restrictedExpandComponentDual_le`: compatibility with left
  multiplication by `restrictedExpandAlgebraMap` and the Gauss-norm bound for
  `restrictedExpandComponentDual`.
* `TauCeti.MvPowerSeries.exists_linearMap_restrictedCoeffSubmodule_ne_zero`: separating a nonzero
  series in `restrictedCoeffSubmodule r E` by a norm-bounded `K`-linear map into `K{X / c}`
  commuting with left multiplication by `restrictedExpandAlgebraMap`.

## References

* Bosch, Güntzer, Remmert, *Non-Archimedean Analysis*, §§5.3.1–5.3.2 and §6.1.5.
-/

public section

namespace TauCeti.MvPowerSeries

open _root_.MvPowerSeries

variable {σ R : Type*} {r t : σ → ℝ}

section Expand

variable [NormedCommRing R] [IsUltrametricDist R] (p : ℕ) (hp : p ≠ 0)
  (ht : ∀ i, r i ^ p = t i)

/-- **Expansion of restricted series.** Substituting `X i ↦ X i ^ p` is an algebra map
`R{X/r^p} → R{X/r}`. -/
noncomputable def restrictedExpand :
    IsRestricted.subring (R := R) t →ₐ[R] IsRestricted.subring (R := R) r where
  toFun f := ⟨expand p hp f, (isRestricted_expand_iff p hp ht).mpr f.property⟩
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
  refine le_antisymm (norm_le_iff.2 fun α ↦ ?_)
    (norm_le_iff.2 fun μ ↦ ?_)
  · rw [coe_restrictedExpand]
    by_cases hα0 : coeff α (expand p hp (f : MvPowerSeries σ R)) = 0
    · simp [hα0]
    · obtain ⟨μ, -, rfl⟩ := support_expand_subset p hp _ (a := α) hα0
      rw [coeff_expand_smul, prod_pow_nsmul p ht]
      exact norm_coeff_mul_prod_le f μ
  · simpa [prod_pow_nsmul p ht] using norm_coeff_mul_prod_le (restrictedExpand p hp ht f) (p • μ)

/-- The expansion is an isometry for the Gauss norms. -/
theorem isometry_restrictedExpand : Isometry (restrictedExpand (R := R) p hp ht) :=
  AddMonoidHomClass.isometry_iff_norm _ |>.mpr (norm_restrictedExpand p hp ht)

end Expand

section Component

variable [NormedRing R] [IsUltrametricDist R] {p : ℕ} (hp : p ≠ 0)
  (ht : ∀ i, r i ^ p = t i) [∀ i, Fact (0 < r i)]

/-- The component `f_ν` in the decomposition `f = ∑ X^ν f_ν(X^p)` of a restricted series at the
polyradii `r`: the restricted series at the polyradii `r ^ p` whose coefficient at `μ` is the
coefficient of `f` at `p • μ + ν`. -/
noncomputable def restrictedExpandComponent (ν : σ →₀ ℕ) (f : IsRestricted.subring (R := R) r) :
    IsRestricted.subring (R := R) t :=
  ⟨fun μ ↦ coeff (p • μ + ν) (f : MvPowerSeries σ R), f.property.coeff_nsmul_add hp ht ν⟩

/-- The coefficients of the component `f_ν`. -/
@[simp]
theorem coeff_restrictedExpandComponent (ν μ : σ →₀ ℕ) (f : IsRestricted.subring (R := R) r) :
    coeff μ (restrictedExpandComponent hp ht ν f : MvPowerSeries σ R) =
      coeff (p • μ + ν) (f : MvPowerSeries σ R) :=
  coeff_apply _ μ

/-- Extracting a component sends `0` to `0`. -/
@[simp]
theorem restrictedExpandComponent_zero (ν : σ →₀ ℕ) :
    restrictedExpandComponent hp ht ν (0 : IsRestricted.subring (R := R) r) = 0 := by
  ext μ : 2
  simp

/-- Extracting a component commutes with addition. -/
@[simp]
theorem restrictedExpandComponent_add (ν : σ →₀ ℕ)
    (f g : IsRestricted.subring (R := R) r) :
    restrictedExpandComponent hp ht ν (f + g) =
      restrictedExpandComponent hp ht ν f + restrictedExpandComponent hp ht ν g := by
  ext μ : 2
  simp

/-- Extracting a component commutes with finite sums. -/
theorem restrictedExpandComponent_sum {ι : Type*} (ν : σ →₀ ℕ) (s : Finset ι)
    (f : ι → IsRestricted.subring (R := R) r) :
    restrictedExpandComponent hp ht ν (∑ i ∈ s, f i) =
      ∑ i ∈ s, restrictedExpandComponent hp ht ν (f i) := by
  ext μ : 2
  simp

variable [∀ i, Fact (0 < t i)]

/-- **Norm estimate for the components.** The weighted norm `‖f_ν‖ r^ν` of each component is at
most the Gauss norm of `f`. -/
theorem norm_restrictedExpandComponent_mul_prod_le (ν : σ →₀ ℕ)
    (f : IsRestricted.subring (R := R) r) :
    ‖restrictedExpandComponent hp ht ν f‖ * ν.prod (r · ^ ·) ≤ ‖f‖ := by
  rw [← le_div_iff₀ (prod_pow_pos ν), norm_le_iff]
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
  obtain ⟨α, hα⟩ := f.property.exists_achievesGaussNorm
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

/-- If `p • μ₁ = pq.1` and `pq.1 + pq.2 = p • μ + ν` with `ν i < p` for all `i`, then `μ₁ ≤ μ`
and `p • (μ - μ₁) + ν = pq.2`. -/
private theorem le_and_nsmul_tsub_add_eq_snd {p : ℕ} {μ ν μ₁ : σ →₀ ℕ}
    {pq : (σ →₀ ℕ) × (σ →₀ ℕ)} (hν : ∀ i, ν i < p) (hμ₁ : p • μ₁ = pq.1)
    (hpq : pq.1 + pq.2 = p • μ + ν) :
    μ₁ ≤ μ ∧ p • (μ - μ₁) + ν = pq.2 := by
  have hcoord (i : σ) : p * μ₁ i + pq.2 i = p * μ i + ν i := by
    have hi := congrArg (· i) hpq
    have hμ₁_i := congrArg (· i) hμ₁
    simp only [Finsupp.coe_add, Finsupp.coe_smul, Pi.add_apply, Pi.smul_apply,
      smul_eq_mul] at hi hμ₁_i
    omega
  have hle : μ₁ ≤ μ := fun i ↦ by
    have := hcoord i
    have := hν i
    have hlt : p * μ₁ i < p * (μ i + 1) := by rw [mul_add, mul_one]; omega
    exact Nat.lt_succ_iff.mp (Nat.lt_of_mul_lt_mul_left hlt)
  refine ⟨hle, Finsupp.ext fun i ↦ ?_⟩
  have := hcoord i
  have := Nat.mul_le_mul_left p (hle i)
  simp only [Finsupp.coe_add, Finsupp.coe_smul, Finsupp.coe_tsub, Pi.add_apply, Pi.smul_apply,
    Pi.sub_apply, smul_eq_mul, Nat.mul_sub_left_distrib]
  omega

/-- Multiplying on the left by an expanded series `g(X^p)` commutes with extracting the `ν`-th
component whenever `ν i < p` for all `i`. -/
theorem restrictedExpandComponent_restrictedExpand_mul [NormedCommRing R] [IsUltrametricDist R]
    {p : ℕ} (hp : p ≠ 0) (ht : ∀ i, r i ^ p = t i) [∀ i, Fact (0 < r i)]
    {ν : σ →₀ ℕ} (hν : ∀ i, ν i < p)
    (g : IsRestricted.subring (R := R) t) (f : IsRestricted.subring (R := R) r) :
    restrictedExpandComponent hp ht ν (restrictedExpand p hp ht g * f) =
      g * restrictedExpandComponent hp ht ν f := by
  classical
  apply Subtype.ext
  ext μ
  rw [coeff_restrictedExpandComponent, Subring.coe_mul, coe_restrictedExpand, coeff_mul,
    Subring.coe_mul, coeff_mul]
  -- Reindex `Finset.antidiagonal μ` into `Finset.antidiagonal (p • μ + ν)` along `emb`.
  let emb : (σ →₀ ℕ) × (σ →₀ ℕ) → (σ →₀ ℕ) × (σ →₀ ℕ) := fun ab ↦ (p • ab.1, p • ab.2 + ν)
  have hemb_inj : Function.Injective emb := by
    rintro ⟨a₁, b₁⟩ ⟨a₂, b₂⟩ h
    simp only [emb, Prod.mk.injEq, add_left_inj] at h
    exact Prod.ext (nsmul_right_injective hp h.1) (nsmul_right_injective hp h.2)
  have hsub : (Finset.antidiagonal μ).image emb ⊆ Finset.antidiagonal (p • μ + ν) := by
    rintro _ hpq
    obtain ⟨⟨a, b⟩, hab, rfl⟩ := Finset.mem_image.mp hpq
    rw [Finset.mem_antidiagonal] at hab ⊢
    dsimp only [emb]
    rw [← add_assoc, ← smul_add, hab]
  rw [← Finset.sum_subset hsub]
  · rw [Finset.sum_image hemb_inj.injOn]
    refine Finset.sum_congr rfl fun ab _ ↦ ?_
    dsimp only [emb]
    rw [coeff_expand_smul, coeff_restrictedExpandComponent]
  -- Extra antidiagonal terms vanish since `expand p` is supported on multiples of `p`.
  · intro pq hpq hnot
    by_cases h0 : coeff pq.1 (expand p hp (g : MvPowerSeries σ R)) = 0
    · rw [h0, zero_mul]
    · exfalso
      obtain ⟨μ₁, -, hμ₁⟩ := support_expand_subset p hp _ (a := pq.1) h0
      obtain ⟨hle, hpq2⟩ :=
        le_and_nsmul_tsub_add_eq_snd hν hμ₁ (Finset.mem_antidiagonal.mp hpq)
      exact hnot (Finset.mem_image.mpr
        ⟨(μ₁, μ - μ₁), Finset.mem_antidiagonal.mpr (add_tsub_cancel_of_le hle),
          Prod.ext hμ₁ hpq2⟩)

section Decomposition

variable [NormedCommRing R] [IsUltrametricDist R] [Fintype σ] [DecidableEq σ] {p : ℕ}
  (hp : p ≠ 0) (ht : ∀ i, r i ^ p = t i) [∀ i, Fact (0 < r i)]

/-- **Existence of the decomposition.** Every restricted series at the polyradii `r` in finitely
many variables is the sum `∑ X^ν f_ν(X^p)` over the exponents `ν` with `ν i < p`, where `f_ν`
are its components. -/
theorem sum_monomial_mul_restrictedExpand_restrictedExpandComponent
    (f : IsRestricted.subring (R := R) r) :
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

variable [NormedCommRing R] [IsUltrametricDist R] {p : ℕ} (hp : p ≠ 0)
  (ht : ∀ i, r i ^ p = t i) [∀ i, Fact (0 < r i)]

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
  rw [← sum_monomial_mul_restrictedExpand_restrictedExpandComponent hp ht f]
  refine Submodule.sum_mem _ fun ν _ ↦ ?_
  rw [mul_comm]
  -- for the module structure induced by the expansion, `g • m` is `restrictedExpand g * m` by
  -- `RingHom.smul_toAlgebra`, which holds by definition
  exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))

end Finite

section Rescale

variable [NormedCommRing R] [IsUltrametricDist R] (p : ℕ) (hp : p ≠ 0) (u : σ → Rˣ)
  (hu : ∀ i, IsNormMulUnit (u i : R)) (hr : ∀ i, ‖(u i : R)‖ * r i ^ p = 1)

/-- If the multiplicative units `u i` satisfy `‖u i‖ * r i ^ p = 1`, substituting
`Y i ↦ u i * X i ^ p` is an algebra map from the unit-radius algebra `R⟨Y⟩` to the restricted
series `R{X/r}`: the rescaling by `u` from the unit radii to the radii `r ^ p`, followed by the
expansion. In finitely many variables it is finite (`restrictedRescaleExpand_finite`). -/
noncomputable def restrictedRescaleExpand :
    IsRestricted.subring (R := R) (fun _ : σ ↦ (1 : ℝ)) →ₐ[R] IsRestricted.subring (R := R) r :=
  (restrictedExpand p hp fun _ ↦ rfl).comp (restrictedRescaleEquiv u hu hr).toAlgHom

/-- The underlying formal series of `restrictedRescaleExpand u f` is `f(u X^p)`. -/
@[simp]
theorem coe_restrictedRescaleExpand (f : IsRestricted.subring (R := R) (fun _ : σ ↦ (1 : ℝ))) :
    (restrictedRescaleExpand p hp u hu hr f : MvPowerSeries σ R) =
      expand p hp (MvPowerSeries.rescale (fun i ↦ (u i : R)) f) := by
  simp [restrictedRescaleExpand]

/-- The map `restrictedRescaleExpand` sends `Y i` to `u i * X i ^ p`. -/
@[simp]
theorem restrictedRescaleExpand_X (i : σ) :
    restrictedRescaleExpand p hp u hu hr
        (⟨X i, isRestricted_X _ i⟩ : IsRestricted.subring (R := R) (fun _ : σ ↦ (1 : ℝ))) =
      algebraMap R (IsRestricted.subring (R := R) r) (u i : R) *
        (⟨X i, isRestricted_X r i⟩ : IsRestricted.subring (R := R) r) ^ p := by
  simp [restrictedRescaleExpand]

/-- The map `restrictedRescaleExpand` is injective. -/
theorem restrictedRescaleExpand_injective :
    Function.Injective (restrictedRescaleExpand (R := R) p hp u hu hr) := by
  simpa only [restrictedRescaleExpand, AlgHom.coe_comp, AlgEquiv.coe_toAlgHom] using
    (restrictedExpand_injective (r := r) p hp fun _ ↦ rfl).comp
      (restrictedRescaleEquiv u hu hr).injective

variable [∀ i, Fact (0 < r i)]

/-- The map `restrictedRescaleExpand` preserves the Gauss norms. -/
@[simp]
theorem norm_restrictedRescaleExpand
    (f : IsRestricted.subring (R := R) (fun _ : σ ↦ (1 : ℝ))) :
    ‖restrictedRescaleExpand p hp u hu hr f‖ = ‖f‖ := by
  let (i : σ) : Fact (0 < r i ^ p) := ⟨pow_pos Fact.out p⟩
  simp [restrictedRescaleExpand]

/-- The map `restrictedRescaleExpand` is an isometry for the Gauss norms. -/
theorem isometry_restrictedRescaleExpand :
    Isometry (restrictedRescaleExpand (R := R) p hp u hu hr) :=
  AddMonoidHomClass.isometry_iff_norm _ |>.mpr (norm_restrictedRescaleExpand p hp u hu hr)

/-- **The restricted series at `r` are finite over the unit Tate algebra** through
`Y i ↦ u i * X i ^ p`, in finitely many variables. -/
theorem restrictedRescaleExpand_finite [Finite σ] :
    (restrictedRescaleExpand (R := R) p hp u hu hr).Finite := by
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

section ExpandAlgebraMap

variable {K K' : Type*} [NormedField K] [IsUltrametricDist K]
  [NormedCommRing K'] [IsUltrametricDist K'] [NormedAlgebra K K']
  {c r : σ → ℝ}

/-- Substituting `X i ↦ X i ^ q` and mapping coefficients along `algebraMap K K'` gives a
`K`-algebra homomorphism `K{X / c} →ₐ[K] K'{X / r}` whenever `r i ^ q = c i`. -/
noncomputable def restrictedExpandAlgebraMap (q : ℕ) (hq : q ≠ 0) (hr : ∀ i, r i ^ q = c i) :
    IsRestricted.subring (R := K) c →ₐ[K] IsRestricted.subring (R := K') r where
  toRingHom :=
    (restrictedExpand q hq hr).toRingHom.comp
      (restrictedMap (algebraMap K K') (C := ‖(1 : K')‖) fun a ↦ by
        rw [Algebra.algebraMap_eq_smul_one, mul_comm]
        exact norm_smul_le a (1 : K'))
  commutes' a := Subtype.ext <| by
    rw [RingHom.toFun_eq_coe, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      coe_restrictedExpand, coe_restrictedMap, coe_algebraMap_isRestrictedSubring,
      MvPowerSeries.map_C, expand_C,
      IsScalarTower.algebraMap_apply K K' (IsRestricted.subring (R := K') r),
      coe_algebraMap_isRestrictedSubring]

private theorem restrictedExpandAlgebraMap_eq (q : ℕ) (hq : q ≠ 0) (hr : ∀ i, r i ^ q = c i)
    (f : IsRestricted.subring (R := K) c) :
    restrictedExpandAlgebraMap (K' := K') q hq hr f =
      restrictedExpand q hq hr
        (restrictedMap (algebraMap K K') (C := ‖(1 : K')‖) (fun a ↦ by
          rw [Algebra.algebraMap_eq_smul_one, mul_comm]
          exact norm_smul_le a (1 : K')) f) :=
  rfl

/-- The underlying formal power series of `restrictedExpandAlgebraMap` is `expand q` composed with
`MvPowerSeries.map (algebraMap K K')`. -/
theorem coe_restrictedExpandAlgebraMap (q : ℕ) (hq : q ≠ 0) (hr : ∀ i, r i ^ q = c i)
    (f : IsRestricted.subring (R := K) c) :
    (restrictedExpandAlgebraMap (K' := K') q hq hr f : _root_.MvPowerSeries σ K') =
      expand q hq (MvPowerSeries.map (algebraMap K K') (f : _root_.MvPowerSeries σ K)) := by
  rw [restrictedExpandAlgebraMap_eq, coe_restrictedExpand, coe_restrictedMap]

/-- `restrictedExpandAlgebraMap` sends each coordinate indeterminate `X i` to `X i ^ q`. -/
@[simp]
theorem restrictedExpandAlgebraMap_X (q : ℕ) (hq : q ≠ 0) (hr : ∀ i, r i ^ q = c i) (i : σ) :
    restrictedExpandAlgebraMap (K' := K') q hq hr
        (⟨X i, isRestricted_X c i⟩ : IsRestricted.subring (R := K) c) =
      (⟨X i, isRestricted_X r i⟩ : IsRestricted.subring (R := K') r) ^ q := by
  apply Subtype.ext
  simp [coe_restrictedExpandAlgebraMap]

/-- `restrictedExpandAlgebraMap` is injective whenever `algebraMap K K'` is injective. -/
theorem restrictedExpandAlgebraMap_injective [FaithfulSMul K K']
    (q : ℕ) (hq : q ≠ 0) (hr : ∀ i, r i ^ q = c i) :
    Function.Injective (restrictedExpandAlgebraMap (σ := σ) (K := K) (K' := K') q hq hr) := by
  intro f g h
  apply Subtype.ext
  ext μ
  have hμ := congrArg (fun u : IsRestricted.subring (R := K') r ↦
    coeff (q • μ) (u : _root_.MvPowerSeries σ K')) h
  simp only [coe_restrictedExpandAlgebraMap, coeff_expand_smul, coeff_map] at hμ
  exact FaithfulSMul.algebraMap_injective K K' hμ

/-- Over a normed field `K` and a normed `K`-algebra `K'` with `‖1‖ = 1`,
`restrictedExpandAlgebraMap` preserves the Gauss norm. -/
@[simp]
theorem norm_restrictedExpandAlgebraMap [NormOneClass K']
    [∀ i, Fact (0 < c i)] [∀ i, Fact (0 < r i)]
    (q : ℕ) (hq : q ≠ 0) (hr : ∀ i, r i ^ q = c i)
    (f : IsRestricted.subring (R := K) c) :
    ‖restrictedExpandAlgebraMap (K' := K') q hq hr f‖ = ‖f‖ := by
  rw [restrictedExpandAlgebraMap_eq, norm_restrictedExpand,
    norm_restrictedMap _ _ (norm_algebraMap' K')]

end ExpandAlgebraMap

section ComponentDual

/-- The `K`-submodule of restricted series `K'{X / r}` whose coefficients all lie in `E`. -/
def restrictedCoeffSubmodule {K K' : Type*} [CommSemiring K]
    [NormedCommRing K'] [IsUltrametricDist K'] [Algebra K K']
    (r : σ → ℝ) (E : Submodule K K') :
    Submodule K (IsRestricted.subring (R := K') r) where
  carrier := {u | ∀ α, coeff α (u : _root_.MvPowerSeries σ K') ∈ E}
  zero_mem' _ := by simp
  add_mem' hu hv α := by simpa using E.add_mem (hu α) (hv α)
  smul_mem' a u hu α := by
    rw [coe_smul_isRestrictedSubring, LinearMap.map_smul_of_tower]
    exact E.smul_mem a (hu α)

/-- A restricted series lies in `restrictedCoeffSubmodule r E` if and only if all of its
coefficients lie in `E`. -/
@[simp]
theorem mem_restrictedCoeffSubmodule {K K' : Type*} [CommSemiring K]
    [NormedCommRing K'] [IsUltrametricDist K'] [Algebra K K']
    {r : σ → ℝ} {E : Submodule K K'} {u : IsRestricted.subring (R := K') r} :
    u ∈ restrictedCoeffSubmodule r E ↔ ∀ α, coeff α (u : _root_.MvPowerSeries σ K') ∈ E :=
  Iff.rfl

variable {K K' : Type*} [NormedField K] [IsUltrametricDist K]
  [NormedCommRing K'] [IsUltrametricDist K'] [NormedAlgebra K K']

/-- Left multiplication by an expanded scalar restricted series preserves membership in
`restrictedCoeffSubmodule r E`. -/
theorem mul_mem_restrictedCoeffSubmodule {c r : σ → ℝ} {q : ℕ} (hq : q ≠ 0)
    (hr : ∀ i, r i ^ q = c i) {E : Submodule K K'} (d : IsRestricted.subring (R := K) c)
    {u : IsRestricted.subring (R := K') r} (hu : u ∈ restrictedCoeffSubmodule r E) :
    restrictedExpandAlgebraMap (K' := K') q hq hr d * u ∈ restrictedCoeffSubmodule r E :=
  mem_restrictedCoeffSubmodule.mpr fun β ↦ by
    rw [Subring.coe_mul, coe_restrictedExpandAlgebraMap, ← MvPowerSeries.map_expand]
    exact MvPowerSeries.coeff_map_mul_mem _ (mem_restrictedCoeffSubmodule.mp hu) β

/-- Left multiplication by a nonzero expanded scalar restricted series reflects membership in
`restrictedCoeffSubmodule r E`. -/
theorem mem_restrictedCoeffSubmodule_of_mul_mem {c r : σ → ℝ} {q : ℕ} (hq : q ≠ 0)
    (hr : ∀ i, r i ^ q = c i) {E : Submodule K K'} {d : IsRestricted.subring (R := K) c}
    (hd : d ≠ 0) {u : IsRestricted.subring (R := K') r}
    (hdu : restrictedExpandAlgebraMap (K' := K') q hq hr d * u ∈ restrictedCoeffSubmodule r E) :
    u ∈ restrictedCoeffSubmodule r E := by
  have hexp_ne : MvPowerSeries.expand q hq (d : _root_.MvPowerSeries σ K) ≠ 0 := by
    rw [← coe_restrictedExpand q hq hr d]
    exact Subtype.coe_ne_coe.mpr ((map_ne_zero_iff _ (restrictedExpand_injective q hq hr)).mpr hd)
  refine mem_restrictedCoeffSubmodule.mpr fun α ↦
    MvPowerSeries.coeff_mem_of_coeff_map_mul_mem E hexp_ne (fun β ↦ ?_) α
  simpa only [Subring.coe_mul, coe_restrictedExpandAlgebraMap, ← MvPowerSeries.map_expand] using
    mem_restrictedCoeffSubmodule.mp hdu β

/-- Extracting the `ν`-th `q`-adic component sends `restrictedCoeffSubmodule r E` `K`-linearly into
`IsRestrictedFamily.addSubgroup E c`. -/
private noncomputable def restrictedExpandComponentFamily {c r : σ → ℝ} [∀ i, Fact (0 < r i)]
    {q : ℕ} (hq : q ≠ 0) (hr : ∀ i, r i ^ q = c i) (E : Submodule K K') (ν : σ →₀ ℕ) :
    restrictedCoeffSubmodule r E →ₗ[K] IsRestrictedFamily.addSubgroup E c where
  toFun u :=
    ⟨fun α ↦ ⟨coeff α (restrictedExpandComponent hq hr ν u.val : _root_.MvPowerSeries σ K'), by
        rw [coeff_restrictedExpandComponent]
        exact mem_restrictedCoeffSubmodule.mp u.property (q • α + ν)⟩,
      IsRestrictedFamily.mem_addSubgroup.mpr <|
        ((isRestrictedFamily_coeff_iff _).mpr
          (restrictedExpandComponent hq hr ν u.val).property).of_norm_le (C := 1) fun _ ↦
            (one_mul _).symm.le⟩
  map_add' u v := IsRestrictedFamily.ext fun α ↦ Subtype.ext <| by
    simp [restrictedExpandComponent_add]
  map_smul' a u := IsRestrictedFamily.ext fun α ↦ Subtype.ext <| by
    simp only [RingHom.id_apply, IsRestrictedFamily.coe_smul, Pi.smul_apply, SetLike.val_smul,
      coeff_restrictedExpandComponent, coe_smul_isRestrictedSubring,
      LinearMap.map_smul_of_tower]

/-- Composing the `ν`-th `q`-adic component map with a norm-bounded `K`-linear functional on `E`
yields a `K`-linear map `restrictedCoeffSubmodule r E →ₗ[K] K{X / c}`. -/
noncomputable def restrictedExpandComponentDual {c r : σ → ℝ} [∀ i, Fact (0 < r i)]
    {q : ℕ} (hq : q ≠ 0) (hr : ∀ i, r i ^ q = c i) (E : Submodule K K') (ν : σ →₀ ℕ)
    (f : E →ₗ[K] K) {C : ℝ} (hf : ∀ v : E, ‖f v‖ ≤ C * ‖v‖) :
    restrictedCoeffSubmodule r E →ₗ[K] IsRestricted.subring (R := K) c :=
  (IsRestrictedFamily.subringLinearEquiv.symm.toLinearMap.restrictScalars K).comp
    ((IsRestrictedFamily.mapLinearMap f hf).comp (restrictedExpandComponentFamily hq hr E ν))

/-- The `α`-th coefficient of `restrictedExpandComponentDual` applies `f` to the `(q • α + ν)`-th
coefficient of `u`. -/
@[simp]
theorem coeff_restrictedExpandComponentDual {c r : σ → ℝ} [∀ i, Fact (0 < r i)]
    {q : ℕ} (hq : q ≠ 0) (hr : ∀ i, r i ^ q = c i) {E : Submodule K K'} (ν : σ →₀ ℕ)
    (f : E →ₗ[K] K) {C : ℝ} (hf : ∀ v : E, ‖f v‖ ≤ C * ‖v‖)
    (u : restrictedCoeffSubmodule r E) (α : σ →₀ ℕ) :
    coeff α (restrictedExpandComponentDual hq hr E ν f hf u : _root_.MvPowerSeries σ K) =
      f ⟨coeff (q • α + ν) ((u : IsRestricted.subring (R := K') r) : _root_.MvPowerSeries σ K'),
        mem_restrictedCoeffSubmodule.mp u.property (q • α + ν)⟩ := by
  simp only [restrictedExpandComponentDual, LinearMap.comp_apply, LinearMap.restrictScalars_apply,
    LinearEquiv.coe_toLinearMap, IsRestrictedFamily.coeff_coe_subringLinearEquiv_symm_apply,
    IsRestrictedFamily.coe_mapLinearMap, Function.comp_apply, restrictedExpandComponentFamily,
    LinearMap.coe_mk, AddHom.coe_mk]
  exact congrArg f (Subtype.ext (coeff_restrictedExpandComponent hq hr ν α u.val))

/-- When `ν i < q` for all `i`, `restrictedExpandComponentDual` commutes with left multiplication
by `restrictedExpandAlgebraMap`. -/
theorem restrictedExpandComponentDual_mul {c r : σ → ℝ} [∀ i, Fact (0 < r i)]
    {q : ℕ} (hq : q ≠ 0) (hr : ∀ i, r i ^ q = c i) {E : Submodule K K'}
    {ν : σ →₀ ℕ} (hν : ∀ i, ν i < q)
    (f : E →ₗ[K] K) {C : ℝ} (hf : ∀ v : E, ‖f v‖ ≤ C * ‖v‖)
    (d : IsRestricted.subring (R := K) c) (u : restrictedCoeffSubmodule r E) :
    restrictedExpandComponentDual hq hr E ν f hf
        ⟨restrictedExpandAlgebraMap (K' := K') q hq hr d * u,
          mul_mem_restrictedCoeffSubmodule hq hr d u.property⟩ =
      d * restrictedExpandComponentDual hq hr E ν f hf u := by
  classical
  have hw_mul :
      restrictedExpandComponentFamily hq hr E ν
          ⟨restrictedExpandAlgebraMap (K' := K') q hq hr d * u,
            mul_mem_restrictedCoeffSubmodule hq hr d u.property⟩ =
        d • restrictedExpandComponentFamily hq hr E ν u := by
    apply IsRestrictedFamily.ext
    intro α
    apply Subtype.ext
    dsimp only [restrictedExpandComponentFamily, LinearMap.coe_mk, AddHom.coe_mk]
    rw [restrictedExpandAlgebraMap_eq,
      restrictedExpandComponent_restrictedExpand_mul hq hr hν _ u.val,
      IsRestrictedFamily.coe_isRestrictedSubring_smul, convSMul_apply, Submodule.coe_sum,
      Subring.coe_mul, coeff_mul]
    refine Finset.sum_congr rfl fun pq _ ↦ ?_
    rw [SetLike.val_smul, Algebra.smul_def, coeff_restrictedMap]
  dsimp only [restrictedExpandComponentDual, LinearMap.comp_apply, LinearMap.restrictScalars_apply,
    LinearEquiv.coe_toLinearMap]
  rw [hw_mul, IsRestrictedFamily.mapLinearMap_isRestrictedSubring_smul,
    IsRestrictedFamily.subringLinearEquiv.symm.map_smul, smul_eq_mul]

/-- Gauss-norm bound for `restrictedExpandComponentDual`. -/
theorem norm_restrictedExpandComponentDual_le {c r : σ → ℝ}
    [∀ i, Fact (0 < c i)] [∀ i, Fact (0 < r i)]
    {q : ℕ} (hq : q ≠ 0) (hr : ∀ i, r i ^ q = c i) {E : Submodule K K'} (ν : σ →₀ ℕ)
    (f : E →ₗ[K] K) {C : ℝ} (hC : 0 ≤ C) (hf : ∀ v : E, ‖f v‖ ≤ C * ‖v‖)
    (u : restrictedCoeffSubmodule r E) :
    ‖restrictedExpandComponentDual hq hr E ν f hf u‖ ≤
      (C / ν.prod (r · ^ ·)) * ‖u‖ := by
  calc ‖restrictedExpandComponentDual hq hr E ν f hf u‖
      ≤ C * ‖restrictedExpandComponent hq hr ν u.val‖ := by
        refine norm_le_mul_of_norm_coeff_le fun α ↦ ?_
        rw [coeff_restrictedExpandComponentDual, coeff_restrictedExpandComponent]
        exact hf ⟨coeff (q • α + ν) (u.val : _root_.MvPowerSeries σ K'),
          mem_restrictedCoeffSubmodule.mp u.property (q • α + ν)⟩
    _ ≤ C * (‖u.val‖ / ν.prod (r · ^ ·)) :=
        mul_le_mul_of_nonneg_left ((le_div_iff₀ (prod_pow_pos ν)).mpr
          (norm_restrictedExpandComponent_mul_prod_le hq hr ν u.val)) hC
    _ = (C / ν.prod (r · ^ ·)) * ‖u‖ := by rw [Submodule.norm_coe]; ring

/-- If bounded `K`-linear functionals separate nonzero elements of `E`, then every nonzero element
`u₀` of `restrictedCoeffSubmodule r E` is separated from `0` by a norm-bounded `K`-linear map
`π : restrictedCoeffSubmodule r E →ₗ[K] K{X / c}` commuting with left multiplication by
`restrictedExpandAlgebraMap`. -/
theorem exists_linearMap_restrictedCoeffSubmodule_ne_zero {c r : σ → ℝ}
    [∀ i, Fact (0 < c i)] [∀ i, Fact (0 < r i)]
    {q : ℕ} (hq : q ≠ 0) (hr : ∀ i, r i ^ q = c i) {E : Submodule K K'}
    (hsep : ∀ {x : E}, x ≠ 0 → ∃ (f : E →ₗ[K] K) (C : ℝ),
      0 ≤ C ∧ (∀ v : E, ‖f v‖ ≤ C * ‖v‖) ∧ f x ≠ 0)
    (u₀ : restrictedCoeffSubmodule r E) (hu₀_ne : u₀ ≠ 0) :
    ∃ (π : restrictedCoeffSubmodule r E →ₗ[K] IsRestricted.subring (R := K) c) (C_π : ℝ),
      0 ≤ C_π ∧
      (∀ (d : IsRestricted.subring (R := K) c) (u : restrictedCoeffSubmodule r E),
        π ⟨restrictedExpandAlgebraMap (K' := K') q hq hr d * u,
          mul_mem_restrictedCoeffSubmodule hq hr d u.property⟩ = d * π u) ∧
      (∀ u : restrictedCoeffSubmodule r E, ‖π u‖ ≤ C_π * ‖u‖) ∧
      π u₀ ≠ 0 := by
  obtain ⟨ν, hν, hν_norm⟩ := exists_norm_restrictedExpandComponent_mul_prod_eq hq hr u₀.val
  have hcomp_ne : restrictedExpandComponent hq hr ν u₀.val ≠ 0 := fun h0 ↦ by
    rw [h0, norm_zero, zero_mul] at hν_norm
    exact hu₀_ne (Subtype.ext (norm_eq_zero.mp hν_norm.symm))
  obtain ⟨μ, hμ_ne⟩ :
      ∃ μ, coeff μ (restrictedExpandComponent hq hr ν u₀.val : _root_.MvPowerSeries σ K') ≠ 0 := by
    by_contra! hall
    exact hcomp_ne (Subtype.ext (MvPowerSeries.ext fun μ ↦ by
      rw [ZeroMemClass.coe_zero, map_zero]; exact hall μ))
  have hx_ne : (⟨coeff (q • μ + ν) (u₀.val : _root_.MvPowerSeries σ K'),
      mem_restrictedCoeffSubmodule.mp u₀.property _⟩ : E) ≠ 0 := by
    rw [ne_eq, Submodule.mk_eq_zero, ← coeff_restrictedExpandComponent hq hr ν μ u₀.val]
    exact hμ_ne
  obtain ⟨f, C, hC, hf, hf_ne⟩ := hsep hx_ne
  refine ⟨restrictedExpandComponentDual hq hr E ν f hf, C / ν.prod (r · ^ ·),
    div_nonneg hC (prod_pow_pos ν).le,
    restrictedExpandComponentDual_mul hq hr hν f hf,
    norm_restrictedExpandComponentDual_le hq hr ν f hC hf, fun h0 ↦ hf_ne ?_⟩
  have hcoeff := congrArg (fun t : IsRestricted.subring (R := K) c ↦
    coeff μ (t : _root_.MvPowerSeries σ K)) h0
  simpa only [coeff_restrictedExpandComponentDual, ZeroMemClass.coe_zero, map_zero] using hcoeff

end ComponentDual

end TauCeti.MvPowerSeries
