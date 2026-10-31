/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.AlgebraicIndependent.Defs
public import TauCeti.RingTheory.FormalGroup.LazardRing.Indecomposable
-- Proof-only: the comparison with `ℚ[b₁, b₂, …]` through changes of coordinates and rescaling,
-- dual numbers, weighted homogeneity and leading monomials.
import Mathlib.Algebra.MvPolynomial.Coeff
import Mathlib.RingTheory.AlgebraicIndependent.Basic
import TauCeti.RingTheory.FormalGroup.Rescale
import TauCeti.RingTheory.MvPolynomial.DualNumber
import TauCeti.RingTheory.MvPolynomial.MonomialOrder
import TauCeti.RingTheory.MvPolynomial.WeightedHomogeneous

/-!
# The generators of the Lazard ring are algebraically independent

The generators `xₙ ∈ L₂ₙ` of the indecomposables of the Lazard ring `L`
(`TauCeti.LazardRing.generator`) are algebraically independent over `ℤ`: the homomorphism
`ℤ[x₁, x₂, …] → L` sending `xₙ` to the generator `xₙ` is injective. This is the integral
independence half of Lazard's theorem that `L` is the polynomial ring `ℤ[x₁, x₂, …]`.

The proof compares `L` with the polynomial ring `ℚ[b₁, b₂, …]` through the homomorphism
`ρ : L → ℚ[b₁, b₂, …]` classifying the additive formal group law transported along the strict
coordinate `f(X) = X + ∑ bᵢ X^(i + 1)`, that is `f(f⁻¹(X) + f⁻¹(Y))`. Giving `bᵢ` the degree `2i`:

* `ρ` is graded. Conjugating `f` by the homothety `X ↦ 4 X` multiplies `bᵢ` by `4ⁱ`, and
  transporting `X + Y` along it rescales the transported law by `4`, which multiplies its
  coefficient of `Xⁱ Yʲ` by `4^(i + j - 1)`. Since the powers of `2` are distinct, the coefficient
  of `Xⁱ Yʲ` is homogeneous of degree `2 (i + j - 1)`, and the graded universal property of `L`
  shows that `ρ` maps `L₂ₙ` to polynomials of degree `2n`.
* The coefficient of `bₙ` in `ρ(xₙ)` is nonzero. Evaluating at `bₙ = ε`, `ε² = 0`, and `bᵢ = 0`
  otherwise reads it off, and turns the transported law into
  `X + Y + ε ((X + Y)^(n + 1) - X^(n + 1) - Y^(n + 1))`. Its coefficient `(n + 1) ε` of `X Yⁿ`
  is the image of `a_{1, n}`, which is a nonzero multiple of `xₙ` modulo decomposables.

A polynomial of degree `2n` is a combination of `bₙ` and of monomials in `b₁, …, bₙ₋₁`, so for the
lexicographic order in which variables of larger index are more significant the leading monomial
of `ρ(xₙ)` is `bₙ`. Polynomials with distinct leading variables are algebraically independent
(`MonomialOrder.algebraicIndependent_of_degree_eq_single`), hence so are the `ρ(xₙ)` and the
`xₙ`.

## Main results

* `TauCeti.LazardRing.algebraicIndependent_generator`: the generators `xₙ` of the Lazard ring are
  algebraically independent over `ℤ`.

## References

* M. Lazard, *Sur les groupes de Lie formels à un paramètre*, Bull. Soc. Math. France 83 (1955).
* J. F. Adams, *Stable Homotopy and Generalised Homology*, Part II, §7.
* D. C. Ravenel, *Complex Cobordism and Stable Homotopy Groups of Spheres*, Appendix A2.1
  (Lazard's theorem A2.1.8).
-/

public section

noncomputable section

open MvPowerSeries Finsupp OrderDual

namespace TauCeti.LazardRing

/-! ### The comparison with `ℚ[b₁, b₂, …]` -/

/-- The polynomial ring `ℚ[b₁, b₂, …]`. Its variables are indexed by `ℕ+ᵒᵈ`, so that the
lexicographic monomial order makes the variables of larger index more significant. -/
private abbrev B : Type := MvPolynomial ℕ+ᵒᵈ ℚ

/-- The strict coordinate `X + ∑ bᵢ X^(i + 1)` over `ℚ[b₁, b₂, …]`. -/
private abbrev coord : FormalCoordinate B :=
  FormalCoordinate.ofStrictCoeffs fun i ↦ MvPolynomial.X (toDual i)

/-- The additive formal group law `f(f⁻¹(X) + f⁻¹(Y))` transported along the strict coordinate
`f = X + ∑ bᵢ X^(i + 1)`. -/
private abbrev transported : FormalGroup B :=
  coord • FormalGroup.𝔾ₐ

/-- The homomorphism `ρ : L →+* ℚ[b₁, b₂, …]` classifying the transported additive law. -/
private def ρ : LazardRing →+* B :=
  lift ⟨transported, inferInstance⟩

private theorem map_ρ : formalGroup.map ρ = transported :=
  map_lift _

/-! ### `ρ` is graded -/

/-- The degree `2i` of the variable `bᵢ`. -/
private abbrev weight : ℕ+ᵒᵈ → ℕ := fun i ↦ 2 * ((ofDual i : ℕ+) : ℕ)

/-- Substituting `4ⁱ bᵢ` for `bᵢ` rescales the transported additive law by `4`. -/
private theorem map_scale_transported :
    transported.map (MvPolynomial.aeval (R := ℚ)
        fun i ↦ MvPolynomial.C ((2 : ℚ) ^ weight i) * MvPolynomial.X i).toRingHom =
      transported.rescale (MvPolynomial.C 4) := by
  let u : Bˣ := Units.map (MvPolynomial.C : ℚ →+* B).toMonoidHom (Units.mk0 4 (by norm_num))
  have hu : (u : B) = MvPolynomial.C 4 := by simp [u]
  rw [← hu, FormalGroup.rescale_smul, FormalGroup.rescale_𝔾ₐ,
    FormalCoordinate.homothety_inv_mul_ofStrictCoeffs_mul_homothety, FormalGroup.map_smul,
    FormalGroup.map_𝔾ₐ, FormalCoordinate.map_ofStrictCoeffs]
  congr 2
  funext i
  rw [Function.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, MvPolynomial.aeval_X, hu,
    ← map_pow]
  norm_num [weight, pow_mul]

/-- The coefficient of `X^(d 0) Y^(d 1)` in the transported additive law is homogeneous of degree
`2 (d 0 + d 1 - 1)`. -/
private theorem isWeightedHomogeneous_coeff_transported (d : Fin 2 →₀ ℕ) :
    MvPolynomial.IsWeightedHomogeneous weight
      (coeff d transported.toPowerSeries) (2 * (d.degree - 1)) := by
  refine MvPolynomial.isWeightedHomogeneous_of_aeval_C_pow_mul_X_eq
    (pow_right_injective₀ (two_pos : (0 : ℚ) < 2) (by norm_num)) ?_
  have h := congrArg (fun F : FormalGroup B ↦ coeff d F.toPowerSeries) map_scale_transported
  simp only [FormalGroup.map_toPowerSeries, coeff_map, FormalGroup.coeff_rescale] at h
  rw [AlgHom.toRingHom_eq_coe, RingHom.coe_coe] at h
  rw [h, ← map_pow, pow_mul]
  norm_num

/-- `ρ` maps the degree `n` part of the Lazard ring to polynomials of degree `n`. -/
private theorem isWeightedHomogeneous_ρ {n : ℕ} {x : LazardRing} (hx : x ∈ grading n) :
    (ρ x).IsWeightedHomogeneous weight n := by
  have := MvPolynomial.WeightedHomogeneousSubmodule.gradedMonoid (R := ℚ) (w := weight)
  refine (MvPolynomial.mem_weightedHomogeneousSubmodule _ _ _ _).1 <|
    (lift_mem_iff (𝒜 := MvPolynomial.weightedHomogeneousSubmodule ℚ weight) (.id ℕ)
      ⟨transported, inferInstance⟩).2 (fun d ↦ ?_) hx
  exact (MvPolynomial.mem_weightedHomogeneousSubmodule _ _ _ _).2
    (isWeightedHomogeneous_coeff_transported d)

/-! ### The linear coefficient of `ρ(xₙ)` -/

/-- `ρ` maps the augmentation ideal to polynomials without constant term. -/
private theorem constantCoeff_ρ_of_mem {x : LazardRing} (hx : x ∈ augmentationIdeal) :
    MvPolynomial.constantCoeff (ρ x) = 0 := by
  have h : MvPolynomial.constantCoeff.comp ρ = (Int.castRingHom ℚ).comp augmentation := by
    refine hom_ext ?_
    have hη : formalGroup.map augmentation = FormalGroup.𝔾ₐ := FormalGroup.ext <| by
      ext d
      rw [FormalGroup.map_toPowerSeries, coeff_map, augmentation_coeff_formalGroup,
        FormalGroup.𝔾ₐ_toPowerSeries]
    have h0 : (MvPolynomial.constantCoeff ∘ fun i : ℕ+ ↦ (MvPolynomial.X (toDual i) : B)) = 0 := by
      funext i
      simp
    rw [← FormalGroup.map_comp, ← FormalGroup.map_comp, map_ρ, hη, FormalGroup.map_smul,
      FormalCoordinate.map_ofStrictCoeffs, h0, FormalCoordinate.ofStrictCoeffs_zero, one_smul,
      FormalGroup.map_𝔾ₐ, FormalGroup.map_𝔾ₐ]
  rw [← RingHom.comp_apply, h, RingHom.comp_apply, mem_augmentationIdeal.1 hx, map_zero]

/-- Evaluation at `bₙ = ε`, `bᵢ = 0` for `i ≠ n`, in the dual numbers `ℚ[ε]`. -/
private abbrev evalEps (n : ℕ+) : B →ₐ[ℚ] DualNumber ℚ :=
  MvPolynomial.aeval (Pi.single (toDual n) DualNumber.eps)

/-- Evaluating `ρ` at `bₙ = ε` kills the square of the augmentation ideal. -/
private theorem evalEps_ρ_eq_zero_of_mem_sq (n : ℕ+) {x : LazardRing}
    (hx : x ∈ augmentationIdeal ^ 2) : evalEps n (ρ x) = 0 := by
  have hfst {y : LazardRing} (hy : y ∈ augmentationIdeal) : (evalEps n (ρ y)).fst = 0 := by
    rw [evalEps, MvPolynomial.aeval_single_eps, constantCoeff_ρ_of_mem hy]
    simp
  rw [pow_two] at hx
  refine Submodule.mul_induction_on hx (fun y hy z hz ↦ ?_) fun y z hy hz ↦ by
    rw [map_add, map_add, hy, hz, add_zero]
  rw [map_mul, map_mul]
  ext <;> simp [hfst hy, hfst hz]

/-- The coefficient of `X Yⁿ` in the transported additive law, evaluated at `bₙ = ε`, is
`(n + 1) ε`. -/
private theorem snd_evalEps_ρ_coeff (n : ℕ+) :
    (evalEps n (ρ (coeff (single 0 1 + single 1 (n : ℕ)) formalGroup.toPowerSeries))).snd =
      (n : ℚ) + 1 := by
  set d : Fin 2 →₀ ℕ := single 0 1 + single 1 (n : ℕ)
  -- Evaluating at `bₙ = ε` transports `X + Y` along `X + ε X^(n + 1)`.
  have hmap : transported.map (evalEps n).toRingHom =
      FormalCoordinate.ofStrictCoeffs (Pi.single n (DualNumber.eps : DualNumber ℚ)) •
        FormalGroup.𝔾ₐ := by
    rw [FormalGroup.map_smul, FormalGroup.map_𝔾ₐ, FormalCoordinate.map_ofStrictCoeffs]
    congr 2
    funext i
    simp [Pi.single_apply]
  have hcoeff : evalEps n (ρ (coeff d formalGroup.toPowerSeries)) =
      coeff d (transported.map (evalEps n).toRingHom).toPowerSeries := by
    rw [← coeff_map, ← FormalGroup.map_toPowerSeries, map_ρ, FormalGroup.map_toPowerSeries,
      coeff_map, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
  have hpow : ((X 0 + X 1) ^ ((n : ℕ) + 1) : MvPowerSeries (Fin 2) (DualNumber ℚ)) =
      ↑((MvPolynomial.X 0 + MvPolynomial.X 1) ^ ((n : ℕ) + 1) :
        MvPolynomial (Fin 2) (DualNumber ℚ)) := by
    simp only [MvPolynomial.coe_pow, MvPolynomial.coe_add, MvPolynomial.coe_X]
  -- Only `ε (X + Y)^(n + 1)` contributes to the coefficient of `X Yⁿ`, with `(n + 1).choose 1`.
  have h0 : d ≠ single 0 1 := fun h ↦ by simpa [d] using DFunLike.congr_fun h 1
  have h1 : d ≠ single 1 1 := fun h ↦ by simpa [d] using DFunLike.congr_fun h 0
  have h2 : d ≠ single 0 ((n : ℕ) + 1) := fun h ↦ by simpa [d] using DFunLike.congr_fun h 1
  have h3 : d ≠ single 1 ((n : ℕ) + 1) := fun h ↦ by simpa [d] using DFunLike.congr_fun h 0
  rw [hcoeff, hmap,
    FormalGroup.ofStrictCoeffs_single_smul_𝔾ₐ_toPowerSeries n DualNumber.eps_mul_eps, hpow,
    map_add, map_add, coeff_X, coeff_X, coeff_C_mul, map_sub, map_sub, MvPolynomial.coeff_coe,
    MvPolynomial.coeff_add_pow, coeff_X_pow, coeff_X_pow, ite_eq_right h0, ite_eq_right h1,
    ite_eq_right h2, ite_eq_right h3]
  simp [d, add_comm 1]

/-- The coefficient of `bₙ` in `ρ(xₙ)` is nonzero. -/
private theorem coeff_ρ_generator_ne_zero (n : ℕ+) :
    (ρ (generator n)).coeff (single (toDual n) 1) ≠ 0 := by
  intro h0
  -- With a zero coefficient of `bₙ`, the generator `xₙ` vanishes at `bₙ = ε`.
  have hx : evalEps n (ρ (generator n)) = 0 := by
    rw [evalEps, MvPolynomial.aeval_single_eps,
      constantCoeff_ρ_of_mem (generator_mem_augmentationIdeal n), h0, zero_smul, map_zero,
      add_zero]
  have hmem := coeff_formalGroup_sub_nsmul_generator_mem_sq n one_pos n.pos
  rw [Nat.add_sub_cancel] at hmem
  -- Modulo decomposables `a_{1, n}` is `((n + 1) / d_{n+1}) • xₙ`, so `n + 1 = 0` in `ℚ`.
  have h := congrArg TrivSqZeroExt.snd (evalEps_ρ_eq_zero_of_mem_sq n hmem)
  rw [map_sub, map_sub, map_nsmul, map_nsmul, hx, smul_zero, sub_zero, snd_evalEps_ρ_coeff,
    TrivSqZeroExt.snd_zero] at h
  exact absurd h (by positivity)

/-! ### The leading monomial of `ρ(xₙ)` -/

/-- A monomial of degree `2n` is `bₙ` or lexicographically smaller than `bₙ`: it only involves
the variables `bᵢ` with `i ≤ n`, and `bₙ` only as the monomial `bₙ` itself. -/
private theorem toLex_le_single_of_weight_eq {n : ℕ+} {d : ℕ+ᵒᵈ →₀ ℕ}
    (hd : Finsupp.weight weight d = 2 * n) : toLex d ≤ toLex (single (toDual n) 1) := by
  by_cases hn : d (toDual n) = 0
  · -- `d` does not involve `bₙ`, nor any `bᵢ` with `i > n`, which would have degree `> 2n`.
    refine le_of_lt (Finsupp.Lex.lt_iff.2 ⟨toDual n, fun j hj ↦ ?_, ?_⟩)
    · have hj' : n < ofDual j := hj
      have hdj : d j = 0 := by
        by_contra hdj
        have := le_weight_of_ne_zero' weight hdj
        simp only [weight] at this
        have : (n : ℕ) < ofDual j := hj'
        omega
      simp [hdj, hj.ne']
    · simp [hn]
  · -- `d - bₙ` has degree `0`, so it is `0`.
    have hsub : d - single (toDual n) 1 = 0 := by
      ext j
      by_contra hj
      have h1 := le_weight_of_ne_zero' weight hj
      have h2 := weight_sub_single_add (w := weight) hn
      simp only [weight, ofDual_toDual] at h1 h2
      have := (ofDual j).pos
      simp only [coe_zero, Pi.zero_apply] at hj
      omega
    rw [← sub_add_single_one_cancel hn, hsub, zero_add]

/-- The leading monomial of `ρ(xₙ)` is `bₙ`. -/
private theorem degree_ρ_generator (n : ℕ+) :
    MonomialOrder.lex.degree (ρ (generator n)) = single (toDual n) 1 := by
  have hp := isWeightedHomogeneous_ρ (generator_mem_grading n)
  have hc := coeff_ρ_generator_ne_zero n
  refine MonomialOrder.lex.toSyn.injective (le_antisymm ?_ ?_)
  · refine MonomialOrder.lex.degree_le_iff.2 fun d hd ↦ ?_
    exact MonomialOrder.lex_le_iff.2
      (toLex_le_single_of_weight_eq (hp (MvPolynomial.mem_support_iff.1 hd)))
  · exact MonomialOrder.lex.le_degree (MvPolynomial.mem_support_iff.2 hc)

/-- **Lazard's theorem, integral independence**: the generators `xₙ ∈ L₂ₙ` of the Lazard ring are
algebraically independent over `ℤ`, that is, the homomorphism `ℤ[x₁, x₂, …] → L` sending `xₙ` to
`TauCeti.LazardRing.generator n` is injective. -/
theorem algebraicIndependent_generator : AlgebraicIndependent ℤ generator := by
  have h : AlgebraicIndependent ℚ fun i : ℕ+ᵒᵈ ↦ ρ (generator (ofDual i)) :=
    MonomialOrder.lex.algebraicIndependent_of_degree_eq_single fun i ↦ degree_ρ_generator _
  have h' := (AlgebraicIndependent.restrictScalars (R := ℤ) Int.cast_injective h).of_comp
    ρ.toIntAlgHom
  exact (algebraicIndependent_equiv toDual).1 h'

end TauCeti.LazardRing
