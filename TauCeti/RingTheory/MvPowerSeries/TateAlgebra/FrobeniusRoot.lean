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
   that is isometric when `c` and `r` are positive (`norm_frobeniusRootRestrictedHom`). In the
   positive-`c`, `r i = c i ^ (p ^ e)⁻¹` setting of item 1, it is the `p ^ e`-th power of
   `frobeniusRootRestrictedEquiv` (`frobeniusRootRestrictedEquiv_pow`).
3. Extending `frobeniusRootRestrictedHom` across fractions embeds any finite purely inseparable
   extension `M` of `GaussFractionField σ K c` of exponent at most `e` into
   `GaussFractionField σ (FrobeniusRoot K p e) r`, sending a denominator-cleared basis of `M` into
   `(FrobeniusRoot K p e){X / r}`
   (`TauCeti.MvPowerSeries.exists_algHom_gaussFractionField_frobeniusRoot_of_isPurelyInseparable`).

These maps feed the purely inseparable reductions in
`TauCeti.RingTheory.MvPowerSeries.TateAlgebra.WeaklyStable` and
`TauCeti.RingTheory.MvPowerSeries.TateAlgebra.Japanese`; the characteristic-free `q`-adic component
families and linear-functional projections used alongside them live in
`TauCeti.RingTheory.MvPowerSeries.TateAlgebra.Module.Expand`.

## Main definitions and results

* `TauCeti.MvPowerSeries.frobeniusRootRestrictedEquiv`: coefficientwise Frobenius-root ring
  isomorphism `K{X / c} ≃+* (FrobeniusRoot K p e){X / r}`, with Gauss-norm formulas
  `norm_frobeniusRootRestrictedEquiv` and `norm_frobeniusRootRestrictedEquiv_symm`.
* `TauCeti.MvPowerSeries.frobeniusRootRestrictedHom`: injective ring homomorphism
  `K{X / c} →+* (FrobeniusRoot K p e){X / r}` (isometric for positive `c` and `r`) satisfying
  `frobeniusRootRestrictedEquiv_pow`.
* `TauCeti.MvPowerSeries.exists_algHom_gaussFractionField_frobeniusRoot_of_isPurelyInseparable`:
  embedding a finite purely inseparable extension of `GaussFractionField σ K c` into
  `GaussFractionField σ (FrobeniusRoot K p e) r` with denominator-cleared basis images in
  `(FrobeniusRoot K p e){X / r}`.

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
noncomputable def frobeniusRootRestrictedEquiv (p : ℕ) [ExpChar K p] (e : ℕ) {c r : σ → ℝ}
    [∀ i, Fact (0 < c i)] (hr : ∀ i, r i = c i ^ (((p ^ e : ℕ) : ℝ)⁻¹)) :
    IsRestricted.subring (R := K) c ≃+* IsRestricted.subring (R := FrobeniusRoot K p e) r where
  toFun f :=
    ⟨MvPowerSeries.map (FrobeniusRoot.root K p e) (f : _root_.MvPowerSeries σ K), by
      have hq : 0 < (((p ^ e : ℕ) : ℝ)⁻¹) :=
        inv_pos.mpr (Nat.cast_pos.mpr (pow_pos (expChar_pos K p) e))
      have hlim := (Real.continuousAt_rpow_const 0 _ (Or.inr hq.le)).tendsto.comp f.property
      rw [Real.zero_rpow hq.ne'] at hlim
      refine hlim.congr fun μ ↦ ?_
      simp only [Function.comp_apply, Real.mul_rpow (norm_nonneg _) (prod_pow_pos μ).le,
        coeff_map, FrobeniusRoot.norm_root, μ.prod_pow_rpow fun i _ ↦ (Fact.out : 0 < c i).le, hr]⟩
  invFun g :=
    ⟨MvPowerSeries.map (FrobeniusRoot.val K p e)
        (g : _root_.MvPowerSeries σ (FrobeniusRoot K p e)), by
      have hq : (0 : ℝ) < (p ^ e : ℕ) := Nat.cast_pos.mpr (pow_pos (expChar_pos K p) e)
      have hr_nn (i : σ) : 0 ≤ r i := hr i ▸ Real.rpow_nonneg (Fact.out : 0 < c i).le _
      have hlim := (Real.continuousAt_rpow_const 0 _ (Or.inr hq.le)).tendsto.comp g.property
      rw [Real.zero_rpow hq.ne'] at hlim
      refine hlim.congr fun μ ↦ ?_
      have hprod : 0 ≤ μ.prod (r · ^ ·) := Finset.prod_nonneg fun i _ ↦ pow_nonneg (hr_nn i) _
      rw [Function.comp_apply, Real.mul_rpow (norm_nonneg _) hprod, coeff_map,
        FrobeniusRoot.norm_def, Real.rpow_inv_rpow (norm_nonneg _) hq.ne',
        μ.prod_pow_rpow fun i _ ↦ hr_nn i]
      congr 1
      refine Finset.prod_congr rfl fun i _ ↦ ?_
      dsimp only
      rw [hr, Real.rpow_inv_rpow (Fact.out : 0 < c i).le hq.ne']⟩
  left_inv _ := Subtype.ext <| MvPowerSeries.ext fun _ ↦ by simp
  right_inv _ := Subtype.ext <| MvPowerSeries.ext fun _ ↦ by simp
  map_mul' f g := Subtype.ext (map_mul (MvPowerSeries.map (FrobeniusRoot.root K p e)) f.val g.val)
  map_add' f g := Subtype.ext (map_add (MvPowerSeries.map (FrobeniusRoot.root K p e)) f.val g.val)

@[simp]
theorem coe_frobeniusRootRestrictedEquiv (p : ℕ) [ExpChar K p] (e : ℕ) {c r : σ → ℝ}
    [∀ i, Fact (0 < c i)] (hr : ∀ i, r i = c i ^ (((p ^ e : ℕ) : ℝ)⁻¹))
    (f : IsRestricted.subring (R := K) c) :
    (frobeniusRootRestrictedEquiv p e hr f : _root_.MvPowerSeries σ (FrobeniusRoot K p e)) =
      MvPowerSeries.map (FrobeniusRoot.root K p e) (f : _root_.MvPowerSeries σ K) :=
  (rfl)

@[simp]
theorem coe_frobeniusRootRestrictedEquiv_symm (p : ℕ) [ExpChar K p] (e : ℕ) {c r : σ → ℝ}
    [∀ i, Fact (0 < c i)] (hr : ∀ i, r i = c i ^ (((p ^ e : ℕ) : ℝ)⁻¹))
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
theorem norm_frobeniusRootRestrictedHom (p : ℕ) [ExpChar K p] (e : ℕ) {c r : σ → ℝ}
    [∀ i, Fact (0 < c i)] [∀ i, Fact (0 < r i)] (hr_pow : ∀ i, r i ^ p ^ e = c i)
    (f : IsRestricted.subring (R := K) c) :
    ‖frobeniusRootRestrictedHom p e hr_pow f‖ = ‖f‖ := by
  rw [frobeniusRootRestrictedHom_apply, norm_restrictedExpand,
    norm_restrictedMap _ _ FrobeniusRoot.norm_algebraMap]

theorem frobeniusRootRestrictedHom_injective (p : ℕ) [ExpChar K p] (e : ℕ) {c r : σ → ℝ}
    (hr_pow : ∀ i, r i ^ p ^ e = c i) :
    Function.Injective (frobeniusRootRestrictedHom (K := K) p e hr_pow) :=
  (restrictedExpand_injective (p ^ e) (pow_pos (expChar_pos K p) e).ne' hr_pow).comp <|
    (injective_iff_map_eq_zero _).mpr fun _ hf ↦ Subtype.ext <| MvPowerSeries.ext fun t ↦
      (map_eq_zero_iff _ (algebraMap K (FrobeniusRoot K p e)).injective).mp
        ((restrictedMap_eq_zero_iff ..).mp hf t)

/-- The `p ^ e`-th power of `frobeniusRootRestrictedEquiv p e hr f` is
`frobeniusRootRestrictedHom p e hr_pow f`. -/
theorem frobeniusRootRestrictedEquiv_pow {p : ℕ} [ExpChar K p] {e : ℕ} {c r : σ → ℝ}
    [∀ i, Fact (0 < c i)] (hr : ∀ i, r i = c i ^ (((p ^ e : ℕ) : ℝ)⁻¹))
    (hr_pow : ∀ i, r i ^ p ^ e = c i) (f : IsRestricted.subring (R := K) c) :
    frobeniusRootRestrictedEquiv p e hr f ^ p ^ e = frobeniusRootRestrictedHom p e hr_pow f := by
  have hhom : (iterateFrobenius (FrobeniusRoot K p e) p e).comp (FrobeniusRoot.root K p e) =
      algebraMap K (FrobeniusRoot K p e) := RingHom.ext FrobeniusRoot.root_pow_expChar_pow
  exact Subtype.ext <| by
    rw [SubmonoidClass.coe_pow, coe_frobeniusRootRestrictedEquiv, coe_frobeniusRootRestrictedHom,
      ← MvPowerSeries.map_iterateFrobenius_expand p (expChar_pos K p).ne' _ e,
      ← MvPowerSeries.map_expand, MvPowerSeries.map_map, hhom]

@[simp]
theorem norm_frobeniusRootRestrictedEquiv (p : ℕ) [ExpChar K p] (e : ℕ) {c r : σ → ℝ}
    [∀ i, Fact (0 < c i)] [∀ i, Fact (0 < r i)] (hr : ∀ i, r i = c i ^ (((p ^ e : ℕ) : ℝ)⁻¹))
    (f : IsRestricted.subring (R := K) c) :
    ‖frobeniusRootRestrictedEquiv p e hr f‖ = ‖f‖ ^ (((p ^ e : ℕ) : ℝ)⁻¹) := by
  have hq : p ^ e ≠ 0 := (pow_pos (expChar_pos K p) e).ne'
  have hr_pow (i : σ) : r i ^ p ^ e = c i := by
    rw [hr, Real.rpow_inv_natCast_pow (Fact.out : 0 < c i).le hq]
  refine (pow_left_inj₀ (norm_nonneg _) (Real.rpow_nonneg (norm_nonneg _) _) hq).mp ?_
  rw [← norm_pow, frobeniusRootRestrictedEquiv_pow hr hr_pow, norm_frobeniusRootRestrictedHom,
    Real.rpow_inv_natCast_pow (norm_nonneg _) hq]

@[simp]
theorem norm_frobeniusRootRestrictedEquiv_symm (p : ℕ) [ExpChar K p] (e : ℕ) {c r : σ → ℝ}
    [∀ i, Fact (0 < c i)] [∀ i, Fact (0 < r i)] (hr : ∀ i, r i = c i ^ (((p ^ e : ℕ) : ℝ)⁻¹))
    (g : IsRestricted.subring (R := FrobeniusRoot K p e) r) :
    ‖(frobeniusRootRestrictedEquiv p e hr).symm g‖ = ‖g‖ ^ p ^ e := by
  have hq : p ^ e ≠ 0 := (pow_pos (expChar_pos K p) e).ne'
  have hg := norm_frobeniusRootRestrictedEquiv p e hr ((frobeniusRootRestrictedEquiv p e hr).symm g)
  rw [RingEquiv.apply_symm_apply] at hg
  rw [hg, Real.rpow_inv_natCast_pow (norm_nonneg _) hq]

end FrobeniusRoot

section PurelyInseparableEmbedding

variable {σ K : Type*} [NormedField K] [IsUltrametricDist K]

/-- For a finite purely inseparable extension `M` of `F = GaussFractionField σ K c` of exponent at
most `e` in exponential characteristic `p`, there exist an `F`-basis `b` of `M`, restricted series
`rootG` in `(FrobeniusRoot K p e){X / r}` (`r i ^ p ^ e = c i`), and an `F`-algebra embedding
`ι₀ : M →ₐ[F] GaussFractionField σ (FrobeniusRoot K p e) r` (for the `F`-algebra structure induced
by `frobeniusRootRestrictedHom p e hr`) sending `b j` to `rootG j`. -/
theorem exists_algHom_gaussFractionField_frobeniusRoot_of_isPurelyInseparable
    {c r : σ → ℝ} [∀ i, Fact (0 < c i)] [∀ i, Fact (0 < r i)]
    (M : Type*) [Field M] [Algebra (GaussFractionField σ K c) M]
    [FiniteDimensional (GaussFractionField σ K c) M]
    [IsPurelyInseparable (GaussFractionField σ K c) M]
    (p : ℕ) [ExpChar K p]
    (e : ℕ) (he : IsPurelyInseparable.exponent (GaussFractionField σ K c) M ≤ e)
    (hr : ∀ i, r i ^ p ^ e = c i) :
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
  have : ExpChar F p := expChar_of_injective_algebraMap (algebraMap K F).injective p
  have : ExpChar F' p := expChar_of_injective_algebraMap (algebraMap K' F').injective p
  have hr_def (i : σ) : r i = c i ^ (((p ^ e : ℕ) : ℝ)⁻¹) := by
    rw [← hr i, Real.pow_rpow_inv_natCast (Fact.out : 0 < r i).le (pow_pos (expChar_pos K p) e).ne']
  have hΨ_inj := frobeniusRootRestrictedHom_injective (K := K) p e hr
  let _ : Algebra F F' := (Ψ.gaussFractionFieldMap hΨ_inj).toAlgebra
  have hF_alg : algebraMap F F' = Ψ.gaussFractionFieldMap hΨ_inj := RingHom.algebraMap_toAlgebra _
  obtain ⟨w, g, hg⟩ := IsPurelyInseparable.exists_iterateFrobenius_unitsSMul_eq_algebraMap
    (IsRestricted.subring (R := K) c) F M p he (Module.finBasis F M)
  let b := (Module.finBasis F M).unitsSMul w
  let rootG (j : Fin _) : T' := frobeniusRootRestrictedEquiv p e hr_def (g j)
  have hrootG_pow (j) : rootG j ^ p ^ e = Ψ (g j) := frobeniusRootRestrictedEquiv_pow hr_def hr _
  have ⟨ι₀⟩ : Nonempty (M →ₐ[F] F') :=
    IsPurelyInseparable.nonempty_algHom_of_forall_exists_pow_eq F M p he F' b.adjoin_range_eq_top
      fun _ ⟨j, hj⟩ ↦ ⟨algebraMap T' F' (rootG j), by
        rw [← hj, ← map_pow, hrootG_pow, ← Ψ.gaussFractionFieldMap_algebraMap hΨ_inj, ← hF_alg,
          ← hg]⟩
  refine ⟨_, b, rootG, ι₀, fun t ↦ by rw [AlgHom.commutes, hF_alg,
      Ψ.gaussFractionFieldMap_algebraMap hΨ_inj], fun j ↦ iterateFrobenius_inj F' p e ?_⟩
  simp only [iterateFrobenius_def]
  rw [← map_pow, ← IsPurelyInseparable.algebraMap_iterateFrobenius F p he (b j), AlgHom.commutes,
    hF_alg, ← map_pow, hrootG_pow, hg, Ψ.gaussFractionFieldMap_algebraMap hΨ_inj]

end PurelyInseparableEmbedding

end TauCeti.MvPowerSeries
