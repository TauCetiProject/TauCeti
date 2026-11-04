/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
public import TauCeti.RingTheory.FormalGroup.CoordinateChange.Lazard
public import TauCeti.RingTheory.FormalGroup.LazardRing.Indecomposable
-- Proof-only: homogeneity of the transported additive law, and evaluation in the dual numbers.
import Mathlib.Algebra.MvPolynomial.Monad
import TauCeti.RingTheory.FormalGroup.Rescale
import TauCeti.RingTheory.MvPolynomial.DualNumber

/-!
# The Hurewicz homomorphism of the Lazard ring

Let `f(X) = X + ∑_{i ≥ 1} bᵢ X^(i + 1)` be the universal strict coordinate over the polynomial ring
`ℤ[b₁, b₂, …]`. Transporting the additive formal group law along `f` gives the commutative formal
group law `f(f⁻¹(X) + f⁻¹(Y))`, whose exponential is `f`. The **Hurewicz homomorphism**
`TauCeti.LazardRing.hurewicz : L →+* ℤ[b₁, b₂, …]` is the homomorphism classifying this law. It is
the reduction `ℤ ⊗_L L[b₁, b₂, …]` of the right unit of the Hopf algebroid `(L, L[b₁, b₂, …])`
along the augmentation (`TauCeti.LazardRing.map_augmentation_comp_rightUnit`). Through Quillen's
theorem it corresponds to the Hurewicz homomorphism `MU_* → H_*(MU) = ℤ[b₁, b₂, …]`, and the
coefficient of `bₙ` in the image of an element of `MU_{2n}` is, up to sign, its characteristic
number `sₙ`.

Giving `bᵢ` the degree `2i`, the Hurewicz homomorphism is graded
(`TauCeti.LazardRing.isWeightedHomogeneous_hurewicz`): conjugating `f` by the homothety
`X ↦ 2 X` multiplies `bᵢ` by `2ⁱ` and rescales the transported law by `2`
(`FormalGroup.isWeightedHomogeneous_coeff_ofStrictCoeffs_X_smul_𝔾ₐ`).

The linear coefficients of the Hurewicz homomorphism compute the indecomposables of `L`. The
coefficient of `bₙ` kills the square of the augmentation ideal `I`; evaluating at `bₙ = ε`,
`ε² = 0`, turns the transported law into `X + Y + ε ((X + Y)^(n + 1) - X^(n + 1) - Y^(n + 1))`,
whose coefficient of `X Yⁿ` is `(n + 1) ε`, while `a_{1, n} ≡ ((n + 1) / d_{n+1}) • xₙ` modulo
`I²`. Hence the coefficient of `bₙ` in the image of `y ∈ I` is `d_{n+1}` times the `n`-th
coordinate of the class of `y` in the basis `(xₘ mod I²)ₘ` of `I ⧸ I²`
(`TauCeti.LazardRing.coeff_single_hurewicz`). In particular it is divisible by `d_{n+1}` on all of
`L`, and a homogeneous `y ∈ L₂ₙ` is congruent to `c • xₙ` modulo decomposables exactly when this
coefficient is `c d_{n+1}`: the coefficient of `bₙ` detects the polynomial generators of `L` in
degree `2n`.

## Main definitions

* `TauCeti.LazardRing.hurewicz`: the Hurewicz homomorphism `L →+* ℤ[b₁, b₂, …]`.

## Main results

* `TauCeti.LazardRing.map_hurewicz`: it classifies the additive law transported along
  `X + ∑ bᵢ X^(i + 1)`.
* `TauCeti.LazardRing.map_augmentation_comp_rightUnit`: it is the reduction of the right unit
  along the augmentation.
* `TauCeti.LazardRing.isWeightedHomogeneous_hurewicz`: it maps `Lₙ` to polynomials of degree `n`
  for `bᵢ` of degree `2i`.
* `TauCeti.LazardRing.constantCoeff_hurewicz`: its constant coefficient is the augmentation.
* `TauCeti.LazardRing.coeff_single_hurewicz`: on the augmentation ideal, the coefficient of `bₙ`
  is `d_{n+1}` times the `n`-th coordinate in `I ⧸ I²`.
* `TauCeti.LazardRing.coeff_single_hurewicz_generator`: the image of the generator `xₘ` has
  coefficient `d_{n+1}` at `bₙ` when `m = n`, and `0` otherwise.
* `TauCeti.LazardRing.lazardGcd_dvd_coeff_single_hurewicz`: the coefficient of `bₙ` is always
  divisible by `d_{n+1}`.
* `TauCeti.LazardRing.toCotangent_eq_smul_cotangentBasis_iff_coeff_hurewicz`: a homogeneous
  `y ∈ L₂ₙ` is `c • xₙ` modulo decomposables exactly when the coefficient of `bₙ` in its image is
  `c d_{n+1}`.

The injectivity of the Hurewicz homomorphism is
`TauCeti.LazardRing.hurewicz_injective`, in `TauCeti.RingTheory.FormalGroup.LazardRing.Polynomial`.

## References

* D. C. Ravenel, *Complex Cobordism and Stable Homotopy Groups of Spheres*, Appendix A2.1 and
  §3.1.
* J. F. Adams, *Stable Homotopy and Generalised Homology*, Part II, §§6–7.
-/

public section

noncomputable section

open MvPowerSeries Finsupp

namespace TauCeti.LazardRing

/-- The **Hurewicz homomorphism** `L →+* ℤ[b₁, b₂, …]` of the Lazard ring: the homomorphism
classifying the commutative formal group law `f(f⁻¹(X) + f⁻¹(Y))`, the additive law transported
along the strict coordinate `f(X) = X + ∑_{i ≥ 1} bᵢ X^(i + 1)`. Through Quillen's theorem it
corresponds to the Hurewicz homomorphism `MU_* → H_*(MU)`. -/
def hurewicz : LazardRing →+* MvPolynomial ℕ+ ℤ :=
  lift ⟨FormalCoordinate.ofStrictCoeffs (MvPolynomial.X : ℕ+ → MvPolynomial ℕ+ ℤ) • FormalGroup.𝔾ₐ,
    inferInstance⟩

/-- The Hurewicz homomorphism classifies the additive formal group law transported along the
strict coordinate `X + ∑ bᵢ X^(i + 1)`. -/
@[simp]
theorem map_hurewicz :
    formalGroup.map hurewicz =
      FormalCoordinate.ofStrictCoeffs (MvPolynomial.X : ℕ+ → MvPolynomial ℕ+ ℤ) • FormalGroup.𝔾ₐ :=
  map_lift _

/-- The Hurewicz homomorphism is the reduction of the right unit `η_R : L → L[b₁, b₂, …]` along
the augmentation `L → ℤ`. -/
theorem map_augmentation_comp_rightUnit :
    (MvPolynomial.map augmentation).comp rightUnit = hurewicz :=
  hom_ext <| by
    rw [map_comp_rightUnit, MvPolynomial.map_comp_C, ← FormalGroup.map_comp, map_augmentation,
      FormalGroup.map_𝔾ₐ, FormalCoordinate.map_universalStrictCoordinate, map_hurewicz]
    congr 2
    funext i
    simp

/-- The constant coefficient of the image under the Hurewicz homomorphism is the augmentation. -/
@[simp]
theorem constantCoeff_hurewicz (x : LazardRing) :
    MvPolynomial.constantCoeff (hurewicz x) = augmentation x := by
  have h : MvPolynomial.constantCoeff.comp hurewicz = augmentation := by
    refine hom_ext ?_
    rw [← FormalGroup.map_comp, map_hurewicz, FormalGroup.map_ofStrictCoeffs_smul_𝔾ₐ]
    simp [Function.comp_def, ← Pi.zero_def]
  exact RingHom.congr_fun h x

/-! ### The Hurewicz homomorphism is graded -/

/-- **The Hurewicz homomorphism is graded**: it maps the degree-`n` part `Lₙ` of the Lazard ring
to polynomials that are homogeneous of degree `n`, for `bᵢ` of degree `2i`. -/
theorem isWeightedHomogeneous_hurewicz {n : ℕ} {x : LazardRing} (hx : x ∈ grading n) :
    (hurewicz x).IsWeightedHomogeneous (fun i : ℕ+ ↦ 2 * (i : ℕ)) n := by
  -- `lift_mem_iff` is stated for `lift`, so unfold `hurewicz` to the `lift` defining it.
  unfold hurewicz
  have := MvPolynomial.WeightedHomogeneousSubmodule.gradedMonoid (R := ℤ)
    (w := fun i : ℕ+ ↦ 2 * (i : ℕ))
  refine (MvPolynomial.mem_weightedHomogeneousSubmodule _ _ _ _).1 <|
    (lift_mem_iff (𝒜 := MvPolynomial.weightedHomogeneousSubmodule ℤ fun i : ℕ+ ↦ 2 * (i : ℕ))
      (.id ℕ) ⟨_, inferInstance⟩).2 (fun d ↦ ?_) hx
  -- The coefficient of `X^(d 0) Y^(d 1)` has degree `d 0 + d 1 - 1` for `bᵢ` of degree `i`.
  refine (MvPolynomial.mem_weightedHomogeneousSubmodule _ _ _ _).2 fun e he ↦ ?_
  have hw := FormalGroup.isWeightedHomogeneous_coeff_ofStrictCoeffs_X_smul_𝔾ₐ d he
  simp only [Finsupp.weight_apply, Finsupp.sum, smul_eq_mul] at hw ⊢
  rw [← hw, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ ↦ by ring

/-- The coefficient of `bₘ` in the image of a homogeneous element of degree `2n` vanishes for
`m ≠ n`. -/
private theorem coeff_single_hurewicz_eq_zero_of_mem_grading {m n : ℕ+} (hmn : m ≠ n)
    {y : LazardRing} (hy : y ∈ grading (2 * n)) : (hurewicz y).coeff (single m 1) = 0 := by
  by_contra h
  have := isWeightedHomogeneous_hurewicz hy h
  rw [Finsupp.weight_single, one_smul] at this
  exact hmn (PNat.coe_injective (by omega))

/-! ### The linear coefficients -/

/-- The additive formal group law transported along `X + ∑ bᵢ X^(i + 1)` over `ℤ[b₁, b₂, …]`. -/
private abbrev law : FormalGroup (MvPolynomial ℕ+ ℤ) :=
  FormalCoordinate.ofStrictCoeffs (MvPolynomial.X : ℕ+ → MvPolynomial ℕ+ ℤ) • FormalGroup.𝔾ₐ

/-- Evaluation at `bₙ = ε`, `bᵢ = 0` for `i ≠ n`, in the dual numbers `ℤ[ε]`. -/
private abbrev evalEps (n : ℕ+) : MvPolynomial ℕ+ ℤ →ₐ[ℤ] DualNumber ℤ :=
  MvPolynomial.aeval (Pi.single n DualNumber.eps)

/-- The `ε`-component of the evaluation at `bₙ = ε` of the image of `y` is the coefficient of
`bₙ`. -/
private theorem snd_evalEps_hurewicz (n : ℕ+) (y : LazardRing) :
    (evalEps n (hurewicz y)).snd = (hurewicz y).coeff (single n 1) := by
  rw [evalEps, MvPolynomial.aeval_single_eps]
  simp

/-- Evaluating the image at `bₙ = ε` kills the square of the augmentation ideal. -/
private theorem evalEps_hurewicz_eq_zero_of_mem_sq (n : ℕ+) {y : LazardRing}
    (hy : y ∈ augmentationIdeal ^ 2) : evalEps n (hurewicz y) = 0 := by
  have hfst {z : LazardRing} (hz : z ∈ augmentationIdeal) : (evalEps n (hurewicz z)).fst = 0 := by
    rw [evalEps, MvPolynomial.aeval_single_eps, constantCoeff_hurewicz,
      mem_augmentationIdeal.1 hz]
    simp
  rw [pow_two] at hy
  refine Submodule.mul_induction_on hy (fun z hz w hw ↦ ?_) fun z w hz hw ↦ by
    rw [map_add, map_add, hz, hw, add_zero]
  rw [map_mul, map_mul]
  ext <;> simp [hfst hz, hfst hw]

/-- The coefficient of `bₙ` in the image vanishes on the square of the augmentation ideal. -/
private theorem coeff_single_hurewicz_eq_zero_of_mem_sq (n : ℕ+) {y : LazardRing}
    (hy : y ∈ augmentationIdeal ^ 2) : (hurewicz y).coeff (single n 1) = 0 := by
  rw [← snd_evalEps_hurewicz, evalEps_hurewicz_eq_zero_of_mem_sq n hy, TrivSqZeroExt.snd_zero]

/-- The coefficient of `X Yⁿ` in the transported additive law, evaluated at `bₙ = ε`, is
`(n + 1) ε`. -/
private theorem snd_evalEps_hurewicz_coeff (n : ℕ+) :
    (evalEps n (hurewicz (coeff (single 0 1 + single 1 (n : ℕ)) formalGroup.toPowerSeries))).snd =
      (n : ℤ) + 1 := by
  set d : Fin 2 →₀ ℕ := single 0 1 + single 1 (n : ℕ)
  -- Evaluating at `bₙ = ε` transports `X + Y` along `X + ε X^(n + 1)`.
  have hmap : law.map (evalEps n).toRingHom =
      FormalCoordinate.ofStrictCoeffs (Pi.single n (DualNumber.eps : DualNumber ℤ)) •
        FormalGroup.𝔾ₐ := by
    rw [FormalGroup.map_ofStrictCoeffs_smul_𝔾ₐ]
    simp [Function.comp_def]
  have hcoeff : evalEps n (hurewicz (coeff d formalGroup.toPowerSeries)) =
      coeff d (law.map (evalEps n).toRingHom).toPowerSeries := by
    rw [← coeff_map, ← FormalGroup.map_toPowerSeries, map_hurewicz, FormalGroup.map_toPowerSeries,
      coeff_map, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
  have hpow : ((X 0 + X 1) ^ ((n : ℕ) + 1) : MvPowerSeries (Fin 2) (DualNumber ℤ)) =
      ↑((MvPolynomial.X 0 + MvPolynomial.X 1) ^ ((n : ℕ) + 1) :
        MvPolynomial (Fin 2) (DualNumber ℤ)) := by
    simp only [MvPolynomial.coe_pow, MvPolynomial.coe_add, MvPolynomial.coe_X]
  -- Only `ε (X + Y)^(n + 1)` contributes to the coefficient of `X Yⁿ`, with `(n + 1).choose 1`.
  have h0 : d ≠ single 0 1 := fun h ↦ by simpa [d] using DFunLike.congr_fun h 1
  have h1 : d ≠ single 1 1 := fun h ↦ by simpa [d] using DFunLike.congr_fun h 0
  have h2 : d ≠ single 0 ((n : ℕ) + 1) := fun h ↦ by simpa [d] using DFunLike.congr_fun h 1
  have h3 : d ≠ single 1 ((n : ℕ) + 1) := fun h ↦ by simpa [d] using DFunLike.congr_fun h 0
  rw [hcoeff, hmap,
    FormalGroup.ofStrictCoeffs_single_smul_𝔾ₐ_toPowerSeries n DualNumber.eps_mul_eps, hpow]
  simp only [map_add, map_sub, coeff_X, coeff_C_mul, MvPolynomial.coeff_coe,
    MvPolynomial.coeff_add_pow, coeff_X_pow, h0, h1, h2, h3, ↓reduceIte]
  simp [d, add_comm 1]

/-- The image of the generator `xₙ` has coefficient `d_{n+1}` at `bₙ`. -/
private theorem coeff_single_hurewicz_generator_self (n : ℕ+) :
    (hurewicz (generator n)).coeff (single n 1) = lazardGcd (n + 1) := by
  have hmem := coeff_formalGroup_sub_nsmul_generator_mem_sq n one_pos n.pos
  rw [Nat.add_sub_cancel] at hmem
  -- Modulo decomposables `a_{1, n}` is `((n + 1) / d_{n+1}) • xₙ`, and the coefficient of `X Yⁿ`
  -- detected at `bₙ = ε` is `n + 1 = ((n + 1) / d_{n+1}) d_{n+1}`.
  have h := congrArg TrivSqZeroExt.snd (evalEps_hurewicz_eq_zero_of_mem_sq n hmem)
  simp only [map_sub, map_nsmul, TrivSqZeroExt.snd_sub, TrivSqZeroExt.snd_smul,
    TrivSqZeroExt.snd_zero, sub_eq_zero] at h
  rw [snd_evalEps_hurewicz_coeff, snd_evalEps_hurewicz, Nat.choose_one_right, nsmul_eq_mul] at h
  have hd := Nat.div_mul_cancel (lazardGcd_dvd_self (n := (n : ℕ) + 1) (by simp))
  have hq : ((((n : ℕ) + 1) / lazardGcd ((n : ℕ) + 1) : ℕ) : ℤ) ≠ 0 := by
    refine Nat.cast_ne_zero.2 fun h0 ↦ ?_
    rw [h0, zero_mul] at hd
    omega
  refine mul_left_cancel₀ hq ?_
  rw [← h]
  exact_mod_cast hd.symm

/-- **The image of a generator modulo decomposables**: the image of the generator `xₘ` under the
Hurewicz homomorphism has coefficient `d_{n+1}` at `bₙ` when `m = n`, and `0` otherwise. That is,
`xₙ ↦ d_{n+1} bₙ` modulo products of the `bᵢ`. -/
@[simp]
theorem coeff_single_hurewicz_generator (m n : ℕ+) :
    (hurewicz (generator m)).coeff (single n 1) = if n = m then (lazardGcd (n + 1) : ℤ) else 0 := by
  split_ifs with h
  · subst h
    exact coeff_single_hurewicz_generator_self n
  · exact coeff_single_hurewicz_eq_zero_of_mem_grading h (generator_mem_grading m)

/-- **The linear coefficients of the Hurewicz homomorphism compute the indecomposables**: for `y`
in the augmentation ideal `I`, the coefficient of `bₙ` in the image of `y` is `d_{n+1}` times the
`n`-th coordinate of the class of `y` in the basis `(xₘ mod I²)ₘ` of `I ⧸ I²`. -/
theorem coeff_single_hurewicz (n : ℕ+) {y : LazardRing} (hy : y ∈ augmentationIdeal) :
    (hurewicz y).coeff (single n 1) =
      lazardGcd (n + 1) * cotangentBasis.repr (augmentationIdeal.toCotangent ⟨y, hy⟩) n := by
  -- Modulo `I²`, `y` is the combination `∑ cₘ xₘ` of the generators.
  have hcoeff := coeff_single_hurewicz_eq_zero_of_mem_sq n (sub_sum_generator_mem_sq hy)
  rw [map_sub, MvPolynomial.coeff_sub, sub_eq_zero] at hcoeff
  rw [hcoeff]
  simp only [Finsupp.sum, Submodule.coe_sum, Submodule.coe_smul_of_tower, map_sum, map_zsmul,
    MvPolynomial.coeff_sum, MvPolynomial.coeff_smul, coeff_single_hurewicz_generator, smul_eq_mul,
    mul_ite, mul_zero, Finset.sum_ite_eq, Finsupp.mem_support_iff]
  split_ifs with h
  · ring
  · simp [not_not.1 h]

/-- **Divisibility of the linear coefficients**: the coefficient of `bₙ` in the image of any
element of the Lazard ring under the Hurewicz homomorphism is divisible by `d_{n+1}`. -/
theorem lazardGcd_dvd_coeff_single_hurewicz (n : ℕ+) (y : LazardRing) :
    (lazardGcd (n + 1) : ℤ) ∣ (hurewicz y).coeff (single n 1) := by
  have hy : y - augmentation y ∈ augmentationIdeal := by simp
  have h := coeff_single_hurewicz n hy
  simp only [map_sub, MvPolynomial.coeff_sub, map_intCast, ← eq_intCast MvPolynomial.C,
    MvPolynomial.coeff_C, ite_eq_right (single_ne_zero.2 one_ne_zero).symm, sub_zero] at h
  exact h ▸ dvd_mul_right _ _

/-- **The Hurewicz homomorphism detects generators**: a homogeneous element `y ∈ L₂ₙ` is congruent
to `c • xₙ` modulo the square of the augmentation ideal exactly when the coefficient of `bₙ` in
its image under the Hurewicz homomorphism is `c d_{n+1}`. In particular `y` is congruent to `± xₙ`
modulo decomposables exactly when that coefficient is `± d_{n+1}`. -/
theorem toCotangent_eq_smul_cotangentBasis_iff_coeff_hurewicz {n : ℕ+} {y : LazardRing}
    (hy : y ∈ grading (2 * n)) (hyI : y ∈ augmentationIdeal) (c : ℤ) :
    augmentationIdeal.toCotangent ⟨y, hyI⟩ = c • cotangentBasis n ↔
      (hurewicz y).coeff (single n 1) = c * lazardGcd (n + 1) := by
  have hd : (lazardGcd ((n : ℕ) + 1) : ℤ) ≠ 0 :=
    Nat.cast_ne_zero.2 (lazardGcd_succ_ne_zero n.ne_zero)
  refine ⟨fun h ↦ ?_, fun h ↦ cotangentBasis.ext_elem fun m ↦ ?_⟩
  · rw [coeff_single_hurewicz n hyI, h, map_zsmul, Module.Basis.repr_self, Finsupp.smul_apply,
      Finsupp.single_eq_same, smul_eq_mul, mul_one, mul_comm]
  · have hm := coeff_single_hurewicz m hyI
    rw [map_smul, Module.Basis.repr_self, Finsupp.smul_apply, Finsupp.single_apply, smul_eq_mul]
    by_cases hmn : n = m
    · subst hmn
      rw [h, mul_comm] at hm
      simpa using (mul_left_cancel₀ hd hm).symm
    · rw [coeff_single_hurewicz_eq_zero_of_mem_grading (Ne.symm hmn) hy] at hm
      simpa [hmn, lazardGcd_succ_ne_zero m.ne_zero] using hm.symm

end TauCeti.LazardRing
