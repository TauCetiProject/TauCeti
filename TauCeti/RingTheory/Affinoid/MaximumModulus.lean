/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Affinoid.SupSeminorm
import Mathlib.FieldTheory.SplittingField.Construction
import TauCeti.RingTheory.Affinoid.Integral
import TauCeti.RingTheory.MvPolynomial.Evaluation.SimpleExtension
import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.Eval
import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.UnitBall

/-!
# The maximum modulus principle for Tate algebras

Let `K` be a complete nontrivially normed ultrametric field and `T = K⟨X₁, …, Xₙ⟩` the Tate
algebra. Every `f : T` attains its Gauss norm at a classical point: there is a maximal ideal `x`
of `T` with `|f(x)| = ‖f‖`, where `|f(x)|` is the absolute value on the finite residue field
`T ⧸ x`. Consequently the supremum seminorm of `T` is its Gauss norm.

After scaling, `‖f‖ = 1`, so the reduction `red f ∈ 𝓀[K][X₁, …, Xₙ]` is nonzero. It need not have a
nonzero value at a point of `𝓀[K]ⁿ` (for example `X ^ p - X` over `ℚ_p`), but it has one at a point
of a finite simple extension `𝓀[K][Y] ⧸ (red g)`, with coordinates `red qᵢ(Y)`. Lift `red g` to a
monic `g` over `𝒪[K]` and the `red qᵢ` to `qᵢ`, and let `α` be a root of `g` in a finite extension
`L` of `K` with its spectral norm. Then `‖α‖ ≤ 1`, and evaluating at `xᵢ = qᵢ(α)` gives a
`K`-algebra map `T → L` whose kernel is a maximal ideal. The value `f(x)` has norm one: modulo the
open unit ball it is computed by a polynomial `h` over `𝒪[K]` whose reduction is coprime to the
irreducible `red g`, and a Bézout relation `u g + v h ≡ 1` evaluated at `α` shows `‖h(α)‖ ≥ 1`.

The coefficient field is not assumed algebraically closed, and its residue field may be finite;
this is why the maximizing point cannot always be chosen `K`-rational.

## Main results

* `TauCeti.MvPowerSeries.exists_pointNorm_eq_norm`: every `f : K⟨X₁, …, Xₙ⟩` has a classical point
  `x` with `|f(x)| = ‖f‖`.
* `TauCeti.MvPowerSeries.supSeminorm_eq_norm`: the supremum seminorm of `K⟨X₁, …, Xₙ⟩` is the
  Gauss norm.

## References

* [Bosch, Güntzer, Remmert, *Non-Archimedean Analysis*][bosch-guntzer-remmert], §5.1.4.
-/

public section

namespace TauCeti.MvPowerSeries

open _root_.MvPowerSeries IsLocalRing Polynomial
open scoped NormedField Valued

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]

section Integral

variable {L : Type*} [NormedField L] [IsUltrametricDist L] [NormedAlgebra K L]

/-- A polynomial over `𝒪[K]` takes values of norm at most one on the closed unit ball of `L`. -/
private theorem norm_eval₂_le_one {α : L} (hα : ‖α‖ ≤ 1) (p : 𝒪[K][X]) :
    ‖p.eval₂ ((algebraMap K L).comp (𝒪[K]).subtype) α‖ ≤ 1 := by
  rw [eval₂_eq_sum_range]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun i _ ↦ ?_
  rw [norm_mul, norm_pow, RingHom.comp_apply, norm_algebraMap']
  exact (mul_le_mul (Valued.integer.norm_le_one _) (pow_le_one₀ (norm_nonneg _) hα)
    (by positivity) zero_le_one).trans_eq (one_mul 1)

/-- A polynomial over `𝒪[K]` with zero reduction takes values of norm less than one on the closed
unit ball of `L`. -/
private theorem norm_eval₂_lt_one {α : L} (hα : ‖α‖ ≤ 1) {p : 𝒪[K][X]}
    (hp : p.map (residue 𝒪[K]) = 0) :
    ‖p.eval₂ ((algebraMap K L).comp (𝒪[K]).subtype) α‖ < 1 := by
  rw [eval₂_eq_sum_range]
  obtain ⟨i, -, hi⟩ := IsUltrametricDist.exists_norm_finsetSum_le
    (Finset.range (p.natDegree + 1))
    fun i ↦ (algebraMap K L).comp (𝒪[K]).subtype (p.coeff i) * α ^ i
  refine hi.trans_lt ?_
  rw [norm_mul, norm_pow, RingHom.comp_apply, norm_algebraMap']
  -- The coefficients of `p` lie in the maximal ideal of `𝒪[K]`, the open unit ball.
  have hi : ‖((p.coeff i : 𝒪[K]) : K)‖ < 1 := by
    have h : residue 𝒪[K] (p.coeff i) = 0 := by simpa using congrArg (Polynomial.coeff · i) hp
    rw [residue_eq_zero_iff, mem_maximalIdeal, mem_nonunits_iff,
      Valued.integer.isUnit_iff_norm_eq_one] at h
    exact (Valued.integer.norm_le_one _).lt_of_ne h
  calc _ ≤ ‖((p.coeff i : 𝒪[K]) : K)‖ * 1 :=
        mul_le_mul_of_nonneg_left (pow_le_one₀ (norm_nonneg _) hα) (norm_nonneg _)
    _ < 1 := by rwa [mul_one]

/-- **Residue nonvanishing at a lifted point.** Let `α` in the closed unit ball of `L` be a root of
`g` over `𝒪[K]` whose reduction `red g` is irreducible. If `red g` does not divide the reduction of
`h`, then `‖h(α)‖ ≥ 1`: its residue is the nonzero value of `red h` at a root of `red g`. -/
private theorem one_le_norm_eval₂ {α : L} (hα : ‖α‖ ≤ 1) {g h : 𝒪[K][X]}
    (hg : g.eval₂ ((algebraMap K L).comp (𝒪[K]).subtype) α = 0)
    (hirr : Irreducible (g.map (residue 𝒪[K])))
    (hdvd : ¬ g.map (residue 𝒪[K]) ∣ h.map (residue 𝒪[K])) :
    1 ≤ ‖h.eval₂ ((algebraMap K L).comp (𝒪[K]).subtype) α‖ := by
  -- Lift a Bézout relation `u₀ * red g + v₀ * red h = 1` and evaluate it at `α`,
  -- where `g` vanishes.
  obtain ⟨u₀, v₀, huv⟩ := (hirr.coprime_iff_not_dvd).mpr hdvd
  obtain ⟨u, rfl⟩ := map_surjective _ residue_surjective u₀
  obtain ⟨v, rfl⟩ := map_surjective _ residue_surjective v₀
  have he : (u * g + v * h - 1).map (residue 𝒪[K]) = 0 := by
    simp only [Polynomial.map_sub, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_one,
      huv, sub_self]
  have hlt := norm_eval₂_lt_one hα he
  simp only [eval₂_sub, eval₂_add, eval₂_mul, hg, mul_zero, zero_add, eval₂_one] at hlt
  set j := (algebraMap K L).comp (𝒪[K]).subtype
  -- So `‖v(α) h(α) - 1‖ < 1`, whence `‖v(α) h(α)‖ = 1` and `‖h(α)‖ ≥ 1` since `‖v(α)‖ ≤ 1`.
  have h1 : ‖v.eval₂ j α * h.eval₂ j α‖ = 1 := by
    have := IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm
      (hlt.trans_eq norm_one.symm).ne
    rwa [sub_add_cancel, norm_one, max_eq_right hlt.le] at this
  calc 1 = ‖v.eval₂ j α‖ * ‖h.eval₂ j α‖ := by rw [← norm_mul, h1]
    _ ≤ 1 * ‖h.eval₂ j α‖ :=
        mul_le_mul_of_nonneg_right (norm_eval₂_le_one hα v) (norm_nonneg _)
    _ = _ := one_mul _

end Integral

variable {n : ℕ}

local notation "T" => IsRestricted.subring (R := K) (fun _ : Fin n ↦ 1)
local notation "T°" => Subring.unitClosedBall (IsRestricted.subring (R := K) (fun _ : Fin n ↦ 1))

/-- A polynomial over `𝒪[K]`, as an element of the Gauss unit ball of `K⟨X₁, …, Xₙ⟩`, reduces to
its coefficientwise reduction. -/
private theorem restrictedReduction_coe_map (P : MvPolynomial (Fin n) 𝒪[K])
    (hP : (⟨(P.map (𝒪[K]).subtype : MvPolynomial (Fin n) K),
      MvPolynomial.isRestricted _ _⟩ : T) ∈ T°) :
    restrictedReduction (⟨_, hP⟩ : T°) = P.map (residue 𝒪[K]) := by
  refine MvPolynomial.ext _ _ fun t ↦ ?_
  rw [coeff_restrictedReduction, MvPolynomial.coeff_map]
  refine congrArg (residue 𝒪[K]) (Subtype.ext ?_)
  exact (MvPolynomial.coeff_coe _ _).trans (MvPolynomial.coeff_map _ _ _)


/-- **Nonvanishing at a lifted point.** Let `α` in the closed unit ball of `L` be a root of `g`
over `𝒪[K]` with irreducible reduction `red g`, and evaluate at `xᵢ = qᵢ(α)` for polynomials `qᵢ`
over `𝒪[K]`. If `red g` does not divide `(red f)(red q)`, where `red f` is the reduction of `f` in
the Gauss unit ball, then `‖f(x)‖ ≥ 1`. -/
private theorem one_le_norm_restrictedEval₂ {L : Type*} [NormedField L] [IsUltrametricDist L]
    [NormedAlgebra K L] [CompleteSpace L] {α : L} (hα : ‖α‖ ≤ 1) {g : 𝒪[K][X]}
    (hg : g.eval₂ ((algebraMap K L).comp (𝒪[K]).subtype) α = 0)
    (hirr : Irreducible (g.map (residue 𝒪[K]))) (q : Fin n → 𝒪[K][X]) {f : T°}
    (hdvd : ¬ g.map (residue 𝒪[K]) ∣
      MvPolynomial.aeval (fun i ↦ (q i).map (residue 𝒪[K])) (restrictedReduction f)) :
    1 ≤ ‖restrictedEval₂ (algebraMap K L)
      (fun i ↦ (q i).eval₂ ((algebraMap K L).comp (𝒪[K]).subtype) α)
      (fun r ↦ (norm_algebraMap' L r).le) (fun i ↦ norm_eval₂_le_one hα (q i)) (f : T)‖ := by
  set j := (algebraMap K L).comp (𝒪[K]).subtype
  set x : Fin n → L := fun i ↦ (q i).eval₂ j α
  have hφ (r : K) : ‖algebraMap K L r‖ ≤ ‖r‖ := (norm_algebraMap' L r).le
  have hx (i : Fin n) : ‖x i‖ ≤ 1 := norm_eval₂_le_one hα (q i)
  -- Split `f = P₁ + R` with `P₁` a lift `P` of the reduction of `f` and `‖R‖ < 1`.
  obtain ⟨P, hP⟩ := MvPolynomial.map_surjective (residue 𝒪[K]) residue_surjective
    (restrictedReduction f)
  have hP₁ : (⟨(P.map (𝒪[K]).subtype : MvPolynomial (Fin n) K),
      MvPolynomial.isRestricted _ _⟩ : T) ∈ T° :=
    mem_unitClosedBall_iff.mpr fun t ↦ by
      simpa [MvPolynomial.coeff_coe, MvPolynomial.coeff_map] using
        Valued.integer.norm_le_one (P.coeff t)
  set P₁ : T° := ⟨_, hP₁⟩
  have hR : ‖restrictedEval₂ (algebraMap K L) x hφ hx ((f - P₁ : T°) : T)‖ < 1 :=
    (norm_restrictedEval₂_le _ _ hφ hx _).trans_lt (restrictedReduction_eq_zero_iff.mp (by
      rw [map_sub, restrictedReduction_coe_map, hP, sub_self]))
  -- The value at `P₁` is `h(α)` for `h = P(q)`, and `red g` does not divide the reduction of `h`.
  have hP₁α : restrictedEval₂ (algebraMap K L) x hφ hx (P₁ : T) =
      (MvPolynomial.aeval q P).eval₂ j α := by
    rw [restrictedEval₂_coe, MvPolynomial.eval₂_map, ← coe_eval₂RingHom, MvPolynomial.map_aeval]
    congr 1
    ext
    simp [j]
  have hred : (MvPolynomial.aeval q P).map (residue 𝒪[K]) =
      MvPolynomial.aeval (fun i ↦ (q i).map (residue 𝒪[K])) (restrictedReduction f) := by
    rw [← coe_mapRingHom, MvPolynomial.map_aeval, ← hP, MvPolynomial.aeval_def,
      MvPolynomial.eval₂_map, MvPolynomial.coe_eval₂Hom]
    congr 1
    ext
    simp
  have h1 := one_le_norm_eval₂ hα hg hirr (hred ▸ hdvd)
  rw [← hP₁α] at h1
  have hsplit : (f : T) = P₁ + (f - P₁ : T°) := by simp
  rw [hsplit, map_add, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (hR.trans_le h1).ne']
  exact h1.trans (le_max_left _ _)

variable [CompleteSpace K]

/-- **Maximum modulus for series of Gauss norm one.** A series in the Gauss unit ball with nonzero
reduction has absolute value at least one at some classical point. -/
private theorem exists_one_le_pointNorm {f : T°} (hf : restrictedReduction f ≠ 0) :
    ∃ x : MaximalSpectrum T, 1 ≤ pointNorm K x (f : T) := by
  -- A point of a finite simple extension of `𝓀[K]` where the reduction does not vanish, lifted
  -- to `𝒪[K]`.
  obtain ⟨g₀, q₀, hg₀m, hg₀i, hdvd⟩ := MvPolynomial.exists_monic_irreducible_not_dvd_aeval hf
  obtain ⟨g, rfl, hgdeg, hgm⟩ := lifts_and_natDegree_eq_and_monic
    (map_surjective _ residue_surjective g₀) hg₀m
  choose q hq using fun i ↦ map_surjective (residue 𝒪[K]) residue_surjective (q₀ i)
  obtain rfl : q₀ = fun i ↦ (q i).map (residue 𝒪[K]) := funext fun i ↦ (hq i).symm
  -- A root `α` of `g` in a finite extension `L` with its spectral norm, of norm at most one.
  set gK := g.map (𝒪[K]).subtype
  let L := SplittingField gK
  let : NormedField L := spectralNorm.normedField K L
  let : NormedAlgebra K L := spectralNorm.normedAlgebra K L
  have : IsUltrametricDist L := IsUltrametricDist.isUltrametricDist_of_isNonarchimedean_norm
    fun a b ↦ isNonarchimedean_spectralNorm (K := K) (L := L) a b
  have : CompleteSpace L := FiniteDimensional.complete K L
  have hdeg : (gK.map (algebraMap K L)).degree ≠ 0 := by
    rw [(hgm.map _).degree_map, hgm.degree_map, degree_eq_natDegree hgm.ne_zero, hgdeg]
    exact_mod_cast hg₀i.natDegree_pos.ne'
  obtain ⟨α, hα⟩ := (SplittingField.splits gK).exists_eval_eq_zero hdeg
  rw [eval_map, ← aeval_def] at hα
  have hαle : ‖α‖ ≤ 1 := (norm_root_le_spectralValue (f := spectralAlgNorm K L)
    isPowMul_spectralNorm isNonarchimedean_spectralNorm (hgm.map _) hα).trans
    ((spectralValue_le_one_iff (hgm.map _)).mpr fun i ↦ by
      simpa using Valued.integer.norm_le_one (g.coeff i))
  have hg : g.eval₂ ((algebraMap K L).comp (𝒪[K]).subtype) α = 0 := by
    rwa [← eval₂_map, ← aeval_def]
  -- Evaluation at `xᵢ = qᵢ(α)` is a `K`-algebra map `ψ : T → L`; its kernel is a maximal ideal.
  let ψ : T →ₐ[K] L :=
    { restrictedEval₂ (algebraMap K L) _ (fun r ↦ (norm_algebraMap' L r).le)
        (fun i ↦ norm_eval₂_le_one hαle (q i)) with
      commutes' := restrictedEval₂_algebraMap _ _ _ _ }
  have hL : IsAffinoidAlgebra K L := isAffinoidAlgebra_self.of_finite
  have hmax : (RingHom.ker ψ).IsMaximal := by
    simpa [RingHom.ker_eq_comap_bot] using hL.comap_isMaximal ψ ⊥
  refine ⟨⟨RingHom.ker ψ, hmax⟩, ?_⟩
  -- `|f(x)|` is the spectral norm of `ψ f`, which is the norm of `L`.
  rw [pointNorm_eq_spectralNorm (ψ := ψ) le_rfl]
  exact one_le_norm_restrictedEval₂ hαle hg hg₀i q hdvd

/-- **Maximum modulus principle for Tate algebras.** Every `f : K⟨X₁, …, Xₙ⟩` attains its Gauss
norm at a classical point: there is a maximal ideal `x` with `|f(x)| = ‖f‖`. The point need not
be `K`-rational. -/
theorem exists_pointNorm_eq_norm (f : T) : ∃ x : MaximalSpectrum T, pointNorm K x f = ‖f‖ := by
  rcases eq_or_ne f 0 with rfl | hf
  · obtain ⟨m, hm⟩ := Ideal.exists_maximal T
    exact ⟨⟨m, hm⟩, by simp⟩
  -- Scale `f` by the inverse of a coefficient attaining the Gauss norm.
  obtain ⟨t, ht⟩ := exists_achievesGaussNorm f
  set a := coeff t (f : _root_.MvPowerSeries (Fin n) K)
  have hfa : ‖f‖ = ‖a‖ := by
    simpa [AchievesGaussNorm, ← norm_eq_gaussNorm] using ht.symm
  have ha : a ≠ 0 := norm_ne_zero_iff.mp (hfa ▸ norm_ne_zero_iff.mpr hf)
  have hnorm : ‖a⁻¹ • f‖ = 1 := by
    rw [norm_smul, norm_inv, hfa, inv_mul_cancel₀ (norm_ne_zero_iff.mpr ha)]
  obtain ⟨x, hx⟩ := exists_one_le_pointNorm (f := ⟨a⁻¹ • f, (Subring.mem_unitClosedBall).mpr
    hnorm.le⟩) (restrictedReduction_ne_zero_iff.mpr hnorm)
  have hx1 : pointNorm K x (a⁻¹ • f) = 1 :=
    le_antisymm ((isAffinoidAlgebra_tate.pointNorm_le_norm x _).trans hnorm.le) hx
  refine ⟨x, ?_⟩
  rw [isAffinoidAlgebra_tate.pointNorm_smul, norm_inv] at hx1
  rw [hfa]
  field_simp at hx1
  exact hx1

/-- **The supremum seminorm of a Tate algebra is the Gauss norm**: `|f|sup = ‖f‖` for every
`f : K⟨X₁, …, Xₙ⟩`. -/
theorem supSeminorm_eq_norm (f : T) : supSeminorm K f = ‖f‖ := by
  obtain ⟨x, hx⟩ := exists_pointNorm_eq_norm f
  exact le_antisymm (isAffinoidAlgebra_tate.supSeminorm_le_norm f)
    (hx ▸ isAffinoidAlgebra_tate.pointNorm_le_supSeminorm x f)

end TauCeti.MvPowerSeries
