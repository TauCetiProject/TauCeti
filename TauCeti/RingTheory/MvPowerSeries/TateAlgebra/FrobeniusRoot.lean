/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.PurelyInseparable.Exponent
public import TauCeti.Analysis.Normed.Field.FrobeniusRoot
public import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.Expand
public import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.FractionField
public import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.Map

import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import TauCeti.Analysis.SpecialFunctions.Pow.Real
import TauCeti.FieldTheory.IntermediateField.Adjoin.EqTop
import TauCeti.FieldTheory.PurelyInseparable.Embedding
import TauCeti.FieldTheory.PurelyInseparable.Exponent

/-!
# Frobenius roots of restricted power series and purely inseparable fraction-field embeddings

Let `K` be an ultrametric normed field of exponential characteristic `p` and `e : ℕ`.

1. For a positive polyradius `c : σ → ℝ` and `r i = c i ^ (p ^ e)⁻¹`, applying
   `FrobeniusRoot.root K p e` and `FrobeniusRoot.val K p e` coefficientwise identifies the
   restricted-series rings `K{X / c}` and `(FrobeniusRoot K p e){X / r}` as rings
   (`TauCeti.MvPowerSeries.frobeniusRootRestrictedEquiv`), raising the Gauss norm to `(p ^ e)⁻¹`
   when `r` is positive (`TauCeti.MvPowerSeries.norm_frobeniusRootRestrictedEquiv`).
2. For any polyradii `c, r : σ → ℝ` with `r i ^ p ^ e = c i`, combining coefficientwise scalar
   extension along `algebraMap K (FrobeniusRoot K p e)` with `restrictedExpand (p ^ e)` gives an
   injective ring homomorphism
   `TauCeti.MvPowerSeries.frobeniusRootRestrictedHom : K{X / c} →+* (FrobeniusRoot K p e){X / r}`
   that is isometric when `c` and `r` are positive (`norm_frobeniusRootRestrictedHom`), and whose
   image of `f` is the `p ^ e`-th power of `frobeniusRootRestrictedEquiv p e hr f`.
3. Extending `frobeniusRootRestrictedHom` across fractions embeds any finite purely inseparable
   extension `M` of `GaussFractionField σ K c` of exponent at most `e` into
   `GaussFractionField σ (FrobeniusRoot K p e) r`, sending a denominator-cleared basis of `M` into
   `(FrobeniusRoot K p e){X / r}`
   (`TauCeti.MvPowerSeries.exists_algHom_gaussFractionField_frobeniusRoot_of_isPurelyInseparable`).

The characteristic-free `q`-adic component families and linear-functional projections used alongside
these maps live in `TauCeti.RingTheory.MvPowerSeries.TateAlgebra.Module.Expand` and
`TauCeti.RingTheory.MvPowerSeries.TateAlgebra.Module.Dual`.

## Main definitions and results

* `TauCeti.MvPowerSeries.frobeniusRootRestrictedEquiv`: coefficientwise Frobenius-root ring
  isomorphism `K{X / c} ≃+* (FrobeniusRoot K p e){X / r}`, with Gauss-norm formulas
  `norm_frobeniusRootRestrictedEquiv` and `norm_frobeniusRootRestrictedEquiv_symm`.
* `TauCeti.MvPowerSeries.frobeniusRootRestrictedHom`: injective ring homomorphism
  `K{X / c} →+* (FrobeniusRoot K p e){X / r}` (isometric for positive `c` and `r`) satisfying
  `frobeniusRootRestrictedEquiv_pow`.
* `TauCeti.MvPowerSeries.exists_algHom_gaussFractionField_frobeniusRoot_of_isPurelyInseparable` and
  `TauCeti.MvPowerSeries.algebraMap_sum_mul_eq_mul`: embedding a finite purely inseparable extension
  of `GaussFractionField σ K c` into `GaussFractionField σ (FrobeniusRoot K p e) r` with
  denominator-cleared basis images in `(FrobeniusRoot K p e){X / r}`.

## References

* [Bosch, Güntzer, Remmert, *Non-Archimedean Analysis*][bosch-guntzer-remmert], §§3.5.3 and 5.3.1.
-/

public section

namespace TauCeti.MvPowerSeries

open _root_.MvPowerSeries Filter
open scoped Topology

section FrobeniusRoot

variable {σ K : Type*} [NormedField K] [IsUltrametricDist K]

/-- Applying `FrobeniusRoot.root K p e` coefficientwise identifies `K{X / c}` with
`(FrobeniusRoot K p e){X / r}` as a ring when `r i = c i ^ (p ^ e)⁻¹`. -/
noncomputable def frobeniusRootRestrictedEquiv (p : ℕ) [ExpChar K p] (e : ℕ)
    {c r : σ → ℝ} [∀ i, Fact (0 < c i)] (hr : ∀ i, r i = c i ^ (((p ^ e : ℕ) : ℝ)⁻¹)) :
    IsRestricted.subring (R := K) c ≃+* IsRestricted.subring (R := FrobeniusRoot K p e) r where
  toFun f :=
    ⟨MvPowerSeries.map (FrobeniusRoot.root K p e) (f : _root_.MvPowerSeries σ K), by
      let qR : ℝ := ((p ^ e : ℕ) : ℝ)
      have hq_inv : 0 < qR⁻¹ := inv_pos.mpr (Nat.cast_pos.mpr (pow_pos (expChar_pos K p) e))
      have hlim := (Real.continuousAt_rpow_const 0 qR⁻¹ (Or.inr hq_inv.le)).tendsto.comp f.2
      rw [Real.zero_rpow hq_inv.ne'] at hlim
      refine hlim.congr fun μ ↦ ?_
      dsimp only [Function.comp_apply, qR]
      rw [Real.mul_rpow (norm_nonneg _) (prod_pow_pos μ).le, coeff_map, FrobeniusRoot.norm_root,
        μ.prod_pow_rpow (fun i _ ↦ (Fact.out : 0 < c i).le)]
      congr 1
      exact Finset.prod_congr rfl fun i _ ↦ by simp only [hr]⟩
  invFun g :=
    ⟨MvPowerSeries.map (FrobeniusRoot.val K p e) (g : _root_.MvPowerSeries σ (FrobeniusRoot K p e)),
      by
      let qR : ℝ := ((p ^ e : ℕ) : ℝ)
      have hq : 0 < qR := Nat.cast_pos.mpr (pow_pos (expChar_pos K p) e)
      have hr_nonneg (i : σ) : 0 ≤ r i := by
        rw [hr]; exact Real.rpow_nonneg (Fact.out : 0 < c i).le _
      have hlim := (Real.continuousAt_rpow_const 0 qR (Or.inr hq.le)).tendsto.comp g.2
      rw [Real.zero_rpow hq.ne'] at hlim
      refine hlim.congr fun μ ↦ ?_
      dsimp only [Function.comp_apply, qR]
      have hval_norm (x : FrobeniusRoot K p e) : ‖x‖ ^ qR = ‖FrobeniusRoot.val K p e x‖ := by
        rw [FrobeniusRoot.norm_def, ← Real.rpow_mul (norm_nonneg _), inv_mul_cancel₀ hq.ne',
          Real.rpow_one]
      have hprod_nonneg : 0 ≤ μ.prod (r · ^ ·) :=
        Finset.prod_nonneg fun i _ ↦ pow_nonneg (hr_nonneg i) _
      rw [Real.mul_rpow (norm_nonneg _) hprod_nonneg, coeff_map, hval_norm,
        μ.prod_pow_rpow (fun i _ ↦ hr_nonneg i)]
      congr 1
      refine Finset.prod_congr rfl fun i _ ↦ ?_
      dsimp only [qR]
      rw [hr, ← Real.rpow_mul (Fact.out : 0 < c i).le, inv_mul_cancel₀ hq.ne', Real.rpow_one]⟩
  left_inv f := Subtype.ext <| by
    dsimp only
    rw [MvPowerSeries.map_map]
    have hcomp : (FrobeniusRoot.val K p e).comp (FrobeniusRoot.root K p e) = RingHom.id K :=
      RingHom.ext FrobeniusRoot.val_root
    rw [hcomp, MvPowerSeries.map_id, RingHom.id_apply]
  right_inv g := Subtype.ext <| by
    dsimp only
    rw [MvPowerSeries.map_map]
    have hcomp : (FrobeniusRoot.root K p e).comp (FrobeniusRoot.val K p e) = RingHom.id _ :=
      RingHom.ext FrobeniusRoot.root_val
    rw [hcomp, MvPowerSeries.map_id, RingHom.id_apply]
  map_mul' f g := Subtype.ext (map_mul (MvPowerSeries.map (FrobeniusRoot.root K p e)) f.1 g.1)
  map_add' f g := Subtype.ext (map_add (MvPowerSeries.map (FrobeniusRoot.root K p e)) f.1 g.1)

@[simp]
theorem coe_frobeniusRootRestrictedEquiv (p : ℕ) [ExpChar K p] (e : ℕ)
    {c r : σ → ℝ} [∀ i, Fact (0 < c i)] (hr : ∀ i, r i = c i ^ (((p ^ e : ℕ) : ℝ)⁻¹))
    (f : IsRestricted.subring (R := K) c) :
    (frobeniusRootRestrictedEquiv p e hr f : _root_.MvPowerSeries σ (FrobeniusRoot K p e)) =
      MvPowerSeries.map (FrobeniusRoot.root K p e) (f : _root_.MvPowerSeries σ K) :=
  (rfl)

@[simp]
theorem coe_frobeniusRootRestrictedEquiv_symm (p : ℕ) [ExpChar K p] (e : ℕ)
    {c r : σ → ℝ} [∀ i, Fact (0 < c i)] (hr : ∀ i, r i = c i ^ (((p ^ e : ℕ) : ℝ)⁻¹))
    (g : IsRestricted.subring (R := FrobeniusRoot K p e) r) :
    ((frobeniusRootRestrictedEquiv p e hr).symm g : _root_.MvPowerSeries σ K) =
      MvPowerSeries.map (FrobeniusRoot.val K p e)
        (g : _root_.MvPowerSeries σ (FrobeniusRoot K p e)) :=
  (rfl)

/-- The ring homomorphism `K{X / c} →+* (FrobeniusRoot K p e){X / r}` (`r i ^ p ^ e = c i`)
obtained by composing coefficientwise `e`-fold Frobenius scalar extension with `p ^ e`-adic
variable expansion. When `c` and `r` are positive, this map is isometric for the Gauss norms
(`norm_frobeniusRootRestrictedHom`). -/
noncomputable def frobeniusRootRestrictedHom (p : ℕ) [ExpChar K p] (e : ℕ) {c r : σ → ℝ}
    (hr_pow : ∀ i, r i ^ p ^ e = c i) :
    IsRestricted.subring (R := K) c →+* IsRestricted.subring (R := FrobeniusRoot K p e) r :=
  (restrictedExpand (p ^ e) (pow_pos (expChar_pos K p) e).ne' hr_pow).toRingHom.comp
    (restrictedMap (algebraMap K (FrobeniusRoot K p e)) (C := 1) fun a ↦ by
      rw [one_mul, FrobeniusRoot.norm_algebraMap])

theorem frobeniusRootRestrictedHom_apply (p : ℕ) [ExpChar K p] (e : ℕ) {c r : σ → ℝ}
    (hr_pow : ∀ i, r i ^ p ^ e = c i) (f : IsRestricted.subring (R := K) c) :
    frobeniusRootRestrictedHom p e hr_pow f =
      restrictedExpand (p ^ e) (pow_pos (expChar_pos K p) e).ne' hr_pow
        (restrictedMap (algebraMap K (FrobeniusRoot K p e)) (C := 1)
          (fun a ↦ by rw [one_mul, FrobeniusRoot.norm_algebraMap]) f) :=
  (rfl)

@[simp]
theorem coe_frobeniusRootRestrictedHom (p : ℕ) [ExpChar K p] (e : ℕ) {c r : σ → ℝ}
    (hr_pow : ∀ i, r i ^ p ^ e = c i) (f : IsRestricted.subring (R := K) c) :
    (frobeniusRootRestrictedHom p e hr_pow f : _root_.MvPowerSeries σ (FrobeniusRoot K p e)) =
      MvPowerSeries.map (algebraMap K (FrobeniusRoot K p e))
        (MvPowerSeries.expand (p ^ e) (pow_pos (expChar_pos K p) e).ne'
          (f : _root_.MvPowerSeries σ K)) := by
  rw [frobeniusRootRestrictedHom_apply, coe_restrictedExpand, coe_restrictedMap,
    MvPowerSeries.map_expand]

@[simp]
theorem norm_frobeniusRootRestrictedHom (p : ℕ) [ExpChar K p] (e : ℕ)
    {c r : σ → ℝ} [∀ i, Fact (0 < c i)] [∀ i, Fact (0 < r i)]
    (hr_pow : ∀ i, r i ^ p ^ e = c i) (f : IsRestricted.subring (R := K) c) :
    ‖frobeniusRootRestrictedHom p e hr_pow f‖ = ‖f‖ := by
  rw [frobeniusRootRestrictedHom_apply, norm_restrictedExpand,
    norm_restrictedMap _ _ FrobeniusRoot.norm_algebraMap]

theorem frobeniusRootRestrictedHom_injective (p : ℕ) [ExpChar K p] (e : ℕ)
    {c r : σ → ℝ} (hr_pow : ∀ i, r i ^ p ^ e = c i) :
    Function.Injective (frobeniusRootRestrictedHom (K := K) p e hr_pow) := by
  refine (restrictedExpand_injective (p ^ e) (pow_pos (expChar_pos K p) e).ne' hr_pow).comp ?_
  rw [injective_iff_map_eq_zero]
  intro f hf
  rw [restrictedMap_eq_zero_iff] at hf
  exact Subtype.ext (MvPowerSeries.ext fun t ↦
    (map_eq_zero_iff _ (algebraMap K (FrobeniusRoot K p e)).injective).mp (hf t))

/-- The `p ^ e`-th power of `frobeniusRootRestrictedEquiv p e hr f` is
`frobeniusRootRestrictedHom p e hr_pow f`. -/
theorem frobeniusRootRestrictedEquiv_pow {p : ℕ} [ExpChar K p] {e : ℕ}
    {c r : σ → ℝ} [∀ i, Fact (0 < c i)]
    (hr : ∀ i, r i = c i ^ (((p ^ e : ℕ) : ℝ)⁻¹)) (hr_pow : ∀ i, r i ^ p ^ e = c i)
    (f : IsRestricted.subring (R := K) c) :
    frobeniusRootRestrictedEquiv p e hr f ^ p ^ e = frobeniusRootRestrictedHom p e hr_pow f := by
  have hp : p ≠ 0 := (expChar_pos K p).ne'
  have hhom : (iterateFrobenius (FrobeniusRoot K p e) p e).comp (FrobeniusRoot.root K p e) =
      algebraMap K (FrobeniusRoot K p e) := RingHom.ext FrobeniusRoot.root_pow_expChar_pow
  apply Subtype.ext
  rw [SubmonoidClass.coe_pow, coe_frobeniusRootRestrictedEquiv, coe_frobeniusRootRestrictedHom,
    ← MvPowerSeries.map_iterateFrobenius_expand p hp _ e, ← MvPowerSeries.map_expand,
    MvPowerSeries.map_map, hhom]

@[simp]
theorem norm_frobeniusRootRestrictedEquiv (p : ℕ) [ExpChar K p] (e : ℕ)
    {c r : σ → ℝ} [∀ i, Fact (0 < c i)] [∀ i, Fact (0 < r i)]
    (hr : ∀ i, r i = c i ^ (((p ^ e : ℕ) : ℝ)⁻¹))
    (f : IsRestricted.subring (R := K) c) :
    ‖frobeniusRootRestrictedEquiv p e hr f‖ = ‖f‖ ^ (((p ^ e : ℕ) : ℝ)⁻¹) := by
  have hq : p ^ e ≠ 0 := (pow_pos (expChar_pos K p) e).ne'
  have hqR : ((p ^ e : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hq
  have hr_pow (i : σ) : r i ^ p ^ e = c i := by
    rw [hr, ← Real.rpow_natCast, ← Real.rpow_mul (Fact.out : 0 < c i).le, inv_mul_cancel₀ hqR,
      Real.rpow_one]
  refine (pow_left_inj₀ (norm_nonneg _) (Real.rpow_nonneg (norm_nonneg _) _) hq).mp ?_
  rw [← norm_pow, frobeniusRootRestrictedEquiv_pow hr hr_pow, norm_frobeniusRootRestrictedHom,
    ← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _), inv_mul_cancel₀ hqR, Real.rpow_one]

@[simp]
theorem norm_frobeniusRootRestrictedEquiv_symm (p : ℕ) [ExpChar K p] (e : ℕ)
    {c r : σ → ℝ} [∀ i, Fact (0 < c i)] [∀ i, Fact (0 < r i)]
    (hr : ∀ i, r i = c i ^ (((p ^ e : ℕ) : ℝ)⁻¹))
    (g : IsRestricted.subring (R := FrobeniusRoot K p e) r) :
    ‖(frobeniusRootRestrictedEquiv p e hr).symm g‖ = ‖g‖ ^ p ^ e := by
  have hqR : ((p ^ e : ℕ) : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (pow_pos (expChar_pos K p) e).ne'
  have hg := norm_frobeniusRootRestrictedEquiv p e hr ((frobeniusRootRestrictedEquiv p e hr).symm g)
  rw [RingEquiv.apply_symm_apply] at hg
  rw [hg, ← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _), inv_mul_cancel₀ hqR,
    Real.rpow_one]

end FrobeniusRoot

section PurelyInseparableEmbedding

variable {σ K : Type*} [NormedField K] [IsUltrametricDist K]

/-- For a finite purely inseparable extension `M` of `F = GaussFractionField σ K c` of exponent at
most `e` in exponential characteristic `p`, there exist an `F`-basis `b` of `M`, restricted series
`rootG` in `(FrobeniusRoot K p e){X / r}` (`r i = c i ^ (p ^ e)⁻¹`), and an `F`-algebra embedding
`ι₀ : M →ₐ[F] GaussFractionField σ (FrobeniusRoot K p e) r` (for the `F`-algebra structure induced
by `frobeniusRootRestrictedHom p e hr`) sending `b j` to `rootG j`. -/
theorem exists_algHom_gaussFractionField_frobeniusRoot_of_isPurelyInseparable
    {c r : σ → ℝ} [∀ i, Fact (0 < c i)] [∀ i, Fact (0 < r i)]
    (M : Type*) [Field M] [Algebra (GaussFractionField σ K c) M]
    [FiniteDimensional (GaussFractionField σ K c) M]
    [IsPurelyInseparable (GaussFractionField σ K c) M]
    (p : ℕ) [ExpChar K p] [ExpChar (GaussFractionField σ K c) p]
    (e : ℕ) (he : IsPurelyInseparable.exponent (GaussFractionField σ K c) M ≤ e)
    (hr_def : ∀ i, r i = c i ^ (((p ^ e : ℕ) : ℝ)⁻¹)) (hr : ∀ i, r i ^ p ^ e = c i) :
    let K' := FrobeniusRoot K p e
    let F := GaussFractionField σ K c
    let T' := IsRestricted.subring (R := K') r
    let F' := GaussFractionField σ K' r
    let Ψ := frobeniusRootRestrictedHom (K := K) p e hr
    letI : Algebra F F' :=
      (Ψ.gaussFractionFieldMap (frobeniusRootRestrictedHom_injective p e hr)).toAlgebra
    ∃ (m : ℕ) (b : Module.Basis (Fin m) F M) (rootG : Fin m → T') (ι₀ : M →ₐ[F] F'),
      (∀ t : IsRestricted.subring (R := K) c,
        ι₀ (algebraMap F M (algebraMap _ F t)) = algebraMap T' F' (Ψ t)) ∧
      (∀ j : Fin m, ι₀ (b j) = algebraMap T' F' (rootG j)) := by
  classical
  intro K' F T' F' Ψ
  let T := IsRestricted.subring (R := K) c
  have : ExpChar F' p := expChar_of_injective_algebraMap (algebraMap K' F').injective p
  have hΨ_inj : Function.Injective Ψ := frobeniusRootRestrictedHom_injective p e hr
  let _ : Algebra F F' := (Ψ.gaussFractionFieldMap hΨ_inj).toAlgebra
  have hF_alg : algebraMap F F' = Ψ.gaussFractionFieldMap hΨ_inj := RingHom.algebraMap_toAlgebra _
  let m := Module.finrank F M
  obtain ⟨w, g, hg⟩ :=
    IsPurelyInseparable.exists_iterateFrobenius_unitsSMul_eq_algebraMap T F M p he
      (Module.finBasis F M)
  let b := (Module.finBasis F M).unitsSMul w
  let rootG (j : Fin m) : T' := frobeniusRootRestrictedEquiv p e hr_def (g j)
  have hrootG_pow (j : Fin m) : rootG j ^ p ^ e = Ψ (g j) :=
    frobeniusRootRestrictedEquiv_pow hr_def hr (g j)
  have ⟨ι₀⟩ : Nonempty (M →ₐ[F] F') :=
    IsPurelyInseparable.nonempty_algHom_of_forall_exists_pow_eq F M p he F' b.adjoin_range_eq_top <|
      by
        rintro _ ⟨j, rfl⟩
        exact ⟨algebraMap T' F' (rootG j), by
          rw [← map_pow, hrootG_pow, ← Ψ.gaussFractionFieldMap_algebraMap hΨ_inj, ← hF_alg, ← hg]⟩
  refine ⟨m, b, rootG, ι₀, fun t ↦ ?_, fun j ↦ ?_⟩
  · rw [AlgHom.commutes, hF_alg]
    exact Ψ.gaussFractionFieldMap_algebraMap hΨ_inj t
  · refine iterateFrobenius_inj F' p e ?_
    simp only [iterateFrobenius_def]
    rw [← map_pow, ← IsPurelyInseparable.algebraMap_iterateFrobenius F p he (b j),
      AlgHom.commutes, hF_alg, ← map_pow, hrootG_pow, hg]
    exact Ψ.gaussFractionFieldMap_algebraMap hΨ_inj (g j)

/-- Clearing the denominator `s` of the coordinates of `y` in an `F`-basis `b` whose images under
`ι : M →+* GaussFractionField σ K' r` come from `rootG : Fin m → K'{X / r}` expresses
`algebraMap _ _ (Ψ s) * ι y` as the image of `∑ j, Ψ (a j) * rootG j`. -/
theorem algebraMap_sum_mul_eq_mul
    {K' : Type*} [NormedField K'] [IsUltrametricDist K']
    {c r : σ → ℝ} [∀ i, Fact (0 < c i)] [∀ i, Fact (0 < r i)]
    {M : Type*} [Field M] [Algebra (GaussFractionField σ K c) M]
    {m : ℕ} (b : Module.Basis (Fin m) (GaussFractionField σ K c) M)
    (Ψ : IsRestricted.subring (R := K) c →+* IsRestricted.subring (R := K') r)
    (rootG : Fin m → IsRestricted.subring (R := K') r) (ι : M →+* GaussFractionField σ K' r)
    (hι_alg : ∀ f, ι (algebraMap _ M (algebraMap _ (GaussFractionField σ K c) f)) =
      algebraMap _ (GaussFractionField σ K' r) (Ψ f))
    (hι_b : ∀ j, ι (b j) = algebraMap _ (GaussFractionField σ K' r) (rootG j))
    (y : M) (s : nonZeroDivisors (IsRestricted.subring (R := K) c))
    (a : Fin m → IsRestricted.subring (R := K) c)
    (ha : ∀ j, algebraMap _ (GaussFractionField σ K c) (a j) =
      (s : IsRestricted.subring (R := K) c) • b.repr y j) :
    algebraMap _ (GaussFractionField σ K' r) (∑ j, Ψ (a j) * rootG j) =
      algebraMap _ (GaussFractionField σ K' r) (Ψ s) * ι y := by
  let T := IsRestricted.subring (R := K) c
  let F := GaussFractionField σ K c
  rw [map_sum, ← b.sum_repr y, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  have haj : algebraMap T F (a j) = algebraMap T F s * b.repr y j := by
    simpa only [Algebra.smul_def] using ha j
  rw [map_mul, ← hι_alg (a j), haj, map_mul, map_mul, hι_alg s, ← hι_b j, mul_assoc,
    ← map_mul ι, ← Algebra.smul_def (b.repr y j) (b j)]

end PurelyInseparableEmbedding

end TauCeti.MvPowerSeries
