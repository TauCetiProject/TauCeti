/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Instances
public import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
public import Mathlib.Analysis.InnerProductSpace.StarOrder
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
public import TauCeti.Analysis.InnerProductSpace.LinearPMap.Green
public import TauCeti.Analysis.InnerProductSpace.LinearPMap.Inverse
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
import TauCeti.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Eigenvector
import TauCeti.Analysis.InnerProductSpace.Spectrum
import TauCeti.Analysis.Normed.Operator.Compact.Interpolation
import TauCeti.Analysis.Normed.Operator.Compact.Spectrum

/-!
# Spectral powers of a strictly positive operator with compact resolvent

Let `A` be a self-adjoint partial linear map with compact resolvent on a complex Hilbert space
`H` which is *strictly positive*: `0 ≤ re ⟪A u, u⟫` on its domain and `ker A = 0`. The typical
example is `L = 1 + ∇*∇` on a closed manifold. Its Green operator `G = A⁻¹`
(`LinearPMap.greenOperator`) is then a compact, injective, positive bounded operator, and the
continuous functional calculus of `G` defines the **negative powers**

`A^{-s} = G ^ s` for real `s ≥ 0` (`LinearPMap.negPow`),

and the **positive powers** `A^s` as the inverses of these injective operators, with domain the
range of `A^{-s}` (`LinearPMap.posPow`). On an eigenvector `u` of `A` for the eigenvalue `λ`, the
power `A^{-s}` acts as multiplication by `λ^{-s}` and `A^s` as multiplication by `λ^s`, so that
for a Hilbert basis `(b k)` of eigenvectors, with `A (b k) = λ k b k`, `A^{-s}` has the
eigen-expansion `A^{-s} f = ∑ λ k ^ (-s) ⟪b k, f⟫ b k`
(`LinearPMap.hasSum_negPow_apply`). The identity power is treated separately from the other
powers: `A^{-0} = A^0 = 1` (`LinearPMap.negPow_zero`, `LinearPMap.posPow_zero`), and `A^1 = A`.

For instance, on the circle `L = 1 - ∂²` has the eigenvalues `1 + k²`, and `L^{-1/2}` multiplies
the mode `exp(i k x)` by `(1 + k²)^{-1/2}`, which is `1` at `k = 0`.

## Main definitions and results

* `LinearPMap.negPow`: the negative power `A^{-s}`, a positive (`LinearPMap.negPow_nonneg`),
  injective (`LinearPMap.injective_negPow`) bounded operator, with `A^{-0} = 1`
  (`LinearPMap.negPow_zero`), `A^{-1} = G` (`LinearPMap.negPow_one`) and the semigroup law
  `A^{-(s + t)} = A^{-s} A^{-t}` (`LinearPMap.negPow_add`). It is compact for every `s > 0`
  (`LinearPMap.isCompactOperator_negPow`).
* `LinearPMap.negPow_apply_of_apply_eq_smul`: `A^{-s} u = λ^{-s} u` on eigenvectors.
* `LinearPMap.posPow`: the positive power `A^s`, a self-adjoint operator
  (`LinearPMap.isSelfAdjoint_posPow`) inverse to `A^{-s}`
  (`LinearPMap.posPow_negPow`, `LinearPMap.negPow_posPow`), with `A^1 = A`
  (`LinearPMap.posPow_one`) and `A^s u = λ^s u` on eigenvectors
  (`LinearPMap.posPow_apply_of_apply_eq_smul`).
* `LinearPMap.commute_negPow` and `LinearPMap.posPow_apply_of_commute`: a bounded operator
  commuting with `A`, such as the unitary action of a symmetry group, commutes with every power
  and preserves its domain.

Along the way, `IsCompactOperator.cfc_apply_of_apply_eq_smul` shows that the functional calculus
of a compact self-adjoint operator acts on an eigenvector for a nonzero eigenvalue `μ` as
multiplication by `f μ`, since nonzero spectral values of a compact operator are isolated.

## References

* M. A. Shubin, *Pseudodifferential Operators and Spectral Theory*, Chapter II, §10.
* K. Schmüdgen, *Unbounded Self-adjoint Operators on Hilbert Space*, Chapter 5.
-/

public section

noncomputable section

open Filter Topology
open scoped InnerProductSpace NNReal

namespace IsCompactOperator

/-- The nonzero points of the real spectrum of a compact operator on a complex Banach space are
isolated. -/
theorem eventually_mem_spectrum_real_imp_eq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [CompleteSpace E] {T : E →L[ℂ] E} (hT : IsCompactOperator T) {μ : ℝ}
    (hμ : μ ≠ 0) : ∀ᶠ y in 𝓝 μ, y ∈ spectrum ℝ T → y = μ := by
  have hpos : 0 < |μ| / 2 := by positivity
  set F : Set ℝ := {y | y ∈ spectrum ℝ T ∧ |μ| / 2 ≤ |y|}
  have hF : F.Finite := by
    refine ((hT.finite_spectrum_norm_ge hpos).preimage Complex.ofReal_injective.injOn).subset ?_
    rintro y ⟨hy, hyμ⟩
    refine ⟨?_, by rwa [Complex.norm_real, Real.norm_eq_abs]⟩
    exact (spectrum.algebraMap_mem_iff ℂ).2 hy
  have hnear : ∀ᶠ y in 𝓝 μ, |μ| / 2 < |y| :=
    (isOpen_lt continuous_const continuous_abs).mem_nhds (half_lt_self (abs_pos.2 hμ))
  have havoid : ∀ᶠ y in 𝓝 μ, y ∉ F \ {μ} := hF.sdiff.isClosed.compl_mem_nhds (by simp)
  filter_upwards [hnear, havoid] with y hy hyF hys
  by_contra hne
  exact hyF ⟨⟨hys, hy.le⟩, hne⟩

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- **Eigenvector action of the functional calculus of a compact self-adjoint operator.** If
`T x = μ x` for a real `μ ≠ 0`, then `f(T) x = f(μ) x` for every real function `f` continuous on
the spectrum of `T`. -/
theorem cfc_apply_of_apply_eq_smul {T : H →L[ℂ] H} (hT : IsCompactOperator T) (f : ℝ → ℝ)
    {x : H} {μ : ℝ} (hμ : μ ≠ 0) (hx : T x = (μ : ℂ) • x)
    (hf : ContinuousOn f (spectrum ℝ T) := by cfc_cont_tac)
    (hT' : IsSelfAdjoint T := by cfc_tac) :
    cfc f T x = (f μ : ℂ) • x := by
  have halg (r : ℝ) : algebraMap ℝ (H →L[ℂ] H) r • x = (r : ℂ) • x := by
    rw [ContinuousLinearMap.smul_def, IsScalarTower.algebraMap_apply ℝ ℂ (H →L[ℂ] H),
      ContinuousLinearMap.algebraMap_apply, Complex.coe_algebraMap]
  rw [← ContinuousLinearMap.smul_def, ← halg] at hx ⊢
  exact TauCeti.cfc_smul_of_smul_eq_algebraMap_smul f hx
    (TauCeti.continuousOn_div_sub_of_eventually hf
      (hT.eventually_mem_spectrum_real_imp_eq hμ)) hT'

end IsCompactOperator

namespace LinearPMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A) (h : A.HasCompactResolvent)

/-! ### The Green operator of a strictly positive operator -/

section Green

/-- The Green operator of a self-adjoint operator with compact resolvent and nonnegative quadratic
form is a positive operator. -/
theorem greenOperator_nonneg (hpos : ∀ u : A.domain, 0 ≤ RCLike.re ⟪A u, (u : H)⟫_ℂ) :
    0 ≤ A.greenOperator hA h := by
  have := h.hasOrthogonalProjection_ker
  rw [ContinuousLinearMap.nonneg_iff_isPositive]
  refine ⟨(A.isSelfAdjoint_greenOperator hA h).isSymmetric, fun f ↦ ?_⟩
  set u : A.domain := ⟨A.greenOperator hA h f, A.greenOperator_mem_domain hA h f⟩
  -- Write `f = A (G f) + Π f`; the projection onto the kernel is orthogonal to `G f`.
  have hf : f = A u + A.ker.starProjection f := by
    rw [apply_greenOperator, sub_add_cancel]
  have horth : ⟪A.ker.starProjection f, (u : H)⟫_ℂ = 0 :=
    Submodule.inner_right_of_mem_orthogonal (A.ker.starProjection_apply_mem f)
      (A.greenOperator_mem_orthogonal_ker hA h f)
  have hGf : A.greenOperator hA h f = (u : H) := rfl
  rw [ContinuousLinearMap.reApplyInnerSelf_apply, ← inner_re_symm, hGf, hf, inner_add_left, horth,
    add_zero]
  exact hpos u

variable {hA h}

/-- If `ker A = 0`, the Green operator is a right inverse of `A`: `A (G f) = f`. -/
theorem apply_greenOperator_of_ker_eq_bot (hker : A.ker = ⊥) (f : H) :
    A ⟨A.greenOperator hA h f, A.greenOperator_mem_domain hA h f⟩ = f := by
  have := h.hasOrthogonalProjection_ker
  rw [apply_greenOperator, (A.ker.starProjection_apply_eq_zero_iff).2 (by simp [hker]), sub_zero]

/-- If `ker A = 0`, the Green operator is a left inverse of `A`: `G (A u) = u`. -/
theorem greenOperator_apply_apply_of_ker_eq_bot (hker : A.ker = ⊥) (u : A.domain) :
    A.greenOperator hA h (A u) = u := by
  have := h.hasOrthogonalProjection_ker
  rw [greenOperator_apply_apply, (A.ker.starProjection_apply_eq_zero_iff).2 (by simp [hker]),
    sub_zero]

/-- If `ker A = 0`, the Green operator is injective. -/
theorem injective_greenOperator (hker : A.ker = ⊥) :
    Function.Injective (A.greenOperator hA h) := by
  rw [← ContinuousLinearMap.coe_coe, ← LinearMap.ker_eq_bot, ker_greenOperator, hker]

/-- If `ker A = 0`, the range of the Green operator is the domain of `A`. -/
theorem range_greenOperator_of_ker_eq_bot (hker : A.ker = ⊥) :
    LinearMap.range (A.greenOperator hA h : H →ₗ[ℂ] H) = A.domain := by
  rw [range_greenOperator, hker, Submodule.bot_orthogonal_eq_top, inf_top_eq]

omit [CompleteSpace H] in
/-- The eigenvalues of a strictly positive operator are positive: if `0 ≤ re ⟪A u, u⟫` on the
domain and `ker A = 0`, then `A u = λ u` with `u ≠ 0` forces `0 < λ`. -/
theorem pos_of_apply_eq_smul (hpos : ∀ u : A.domain, 0 ≤ RCLike.re ⟪A u, (u : H)⟫_ℂ)
    (hker : A.ker = ⊥) {u : A.domain} (hu0 : (u : H) ≠ 0) {lam : ℝ}
    (hu : A u = (lam : ℂ) • (u : H)) : 0 < lam := by
  have hnorm : 0 < ‖(u : H)‖ ^ 2 := by positivity
  have hre : RCLike.re ⟪A u, (u : H)⟫_ℂ = lam * ‖(u : H)‖ ^ 2 := by
    rw [hu, inner_smul_left, Complex.conj_ofReal, inner_self_eq_norm_sq_to_K]
    exact Complex.re_ofReal_mul lam _ |>.trans (by norm_cast)
  refine lt_of_le_of_ne (nonneg_of_mul_nonneg_left (hre ▸ hpos u) hnorm) fun hlam ↦ hu0 ?_
  have hmem : (u : H) ∈ A.ker := coe_mem_ker_iff.2 (by rw [hu, ← hlam, Complex.ofReal_zero,
    zero_smul])
  rwa [hker, Submodule.mem_bot] at hmem

end Green

/-! ### Negative powers -/

section NegPow

variable (A) in
/-- The **negative power** `A^{-s}`, for real `s ≥ 0`, of a self-adjoint operator `A` with
compact resolvent: the power `G ^ s` of its Green operator `G` in the continuous functional
calculus. When `A` is strictly positive, `G = A⁻¹`, and `A^{-s}` acts on an eigenvector of `A`
for the eigenvalue `λ` as multiplication by `λ^{-s}` (`LinearPMap.negPow_apply_of_apply_eq_smul`).
The identity power `A^{-0}` is the identity operator (`LinearPMap.negPow_zero`). -/
def negPow (s : ℝ≥0) : H →L[ℂ] H :=
  A.greenOperator hA h ^ (s : ℝ)

variable {hA h}

theorem negPow_def (s : ℝ≥0) : A.negPow hA h s = A.greenOperator hA h ^ (s : ℝ) := (rfl)

/-- The negative powers are positive operators. -/
theorem negPow_nonneg (s : ℝ≥0) : 0 ≤ A.negPow hA h s :=
  CFC.rpow_nonneg

/-- The negative powers are self-adjoint. -/
theorem isSelfAdjoint_negPow (s : ℝ≥0) : IsSelfAdjoint (A.negPow hA h s) :=
  (negPow_nonneg s).isSelfAdjoint

variable (hpos : ∀ u : A.domain, 0 ≤ RCLike.re ⟪A u, (u : H)⟫_ℂ)
include hpos

/-- **The identity power.** `A^{-0} = 1`. -/
theorem negPow_zero : A.negPow hA h 0 = 1 :=
  CFC.rpow_zero _ (greenOperator_nonneg hA h hpos)

/-- `A^{-1}` is the Green operator. -/
theorem negPow_one : A.negPow hA h 1 = A.greenOperator hA h :=
  CFC.rpow_one _ (greenOperator_nonneg hA h hpos)

/-- **The semigroup law** `A^{-(s + t)} = A^{-s} A^{-t}`. -/
theorem negPow_add (s t : ℝ≥0) : A.negPow hA h (s + t) = A.negPow hA h s * A.negPow hA h t := by
  rcases eq_zero_or_pos s with rfl | hs
  · rw [zero_add, negPow_zero hpos, one_mul]
  rcases eq_zero_or_pos t with rfl | ht
  · rw [add_zero, negPow_zero hpos, mul_one]
  simp only [negPow_def]
  rw [← CFC.nnrpow_eq_rpow hs, ← CFC.nnrpow_eq_rpow ht, ← CFC.nnrpow_eq_rpow (add_pos hs ht),
    CFC.nnrpow_add hs ht]

/-- Powers of negative powers: `(A^{-s})^t = A^{-s t}`. -/
theorem negPow_rpow (s : ℝ≥0) (t : ℝ≥0) : A.negPow hA h s ^ (t : ℝ) = A.negPow hA h (s * t) := by
  simp only [negPow_def, NNReal.coe_mul]
  exact CFC.rpow_rpow_of_exponent_nonneg _ _ _ s.2 t.2 (greenOperator_nonneg hA h hpos)

/-- Natural powers: `A^{-n} = G ^ n`. -/
theorem negPow_natCast (n : ℕ) : A.negPow hA h n = A.greenOperator hA h ^ n := by
  rw [negPow_def, NNReal.coe_natCast]
  exact CFC.rpow_natCast _ n (greenOperator_nonneg hA h hpos)

/-- On an eigenvector of `A` for the eigenvalue `λ > 0`, the negative power `A^{-s}` acts as
multiplication by `λ ^ (-s)`. -/
theorem negPow_apply_of_apply_eq_smul (s : ℝ≥0) (u : A.domain) {lam : ℝ} (hlam : 0 < lam)
    (hu : A u = (lam : ℂ) • (u : H)) :
    A.negPow hA h s u = ((lam ^ (-(s : ℝ)) : ℝ) : ℂ) • (u : H) := by
  have hG := greenOperator_nonneg hA h hpos
  have hGu : A.greenOperator hA h u = ((lam⁻¹ : ℝ) : ℂ) • (u : H) := by
    rw [A.greenOperator_apply_of_apply_eq_smul hA h u (by exact_mod_cast hlam.ne') hu,
      Complex.ofReal_inv]
  rw [negPow_def, CFC.rpow_eq_cfc_real hG]
  refine ((A.isCompactOperator_greenOperator hA h).cfc_apply_of_apply_eq_smul
    (fun x : ℝ ↦ x ^ (s : ℝ)) (inv_ne_zero hlam.ne') hGu
    (Real.continuous_rpow_const s.2).continuousOn hG.isSelfAdjoint).trans ?_
  rw [Real.inv_rpow hlam.le, Real.rpow_neg hlam.le]

/-- The negative powers of a strictly positive operator are injective. -/
theorem injective_negPow (hker : A.ker = ⊥) (s : ℝ≥0) : Function.Injective (A.negPow hA h s) := by
  obtain ⟨n, hn⟩ := exists_nat_ge s
  -- `A^{-n} = A^{-(n - s)} A^{-s}` and `A^{-n} = G ^ n` is injective.
  have hfac : A.negPow hA h n = A.negPow hA h (n - s) * A.negPow hA h s := by
    rw [← negPow_add hpos, tsub_add_cancel_of_le hn]
  have hinj : Function.Injective (A.negPow hA h n) := by
    rw [negPow_natCast hpos, FunLike.coe_pow_eq_iterate]
    exact (injective_greenOperator hker).iterate n
  rw [hfac, ContinuousLinearMap.mul_def, ContinuousLinearMap.coe_comp] at hinj
  exact hinj.of_comp

/-- **Compactness.** For `s > 0` the negative power `A^{-s}` is a compact operator. For `s ≥ 1`
this follows from `A^{-s} = A^{-(s - 1)} G`; smaller `s` reduce to larger ones, since a
self-adjoint operator is compact when its square is. -/
theorem isCompactOperator_negPow {s : ℝ≥0} (hs : 0 < s) :
    IsCompactOperator (A.negPow hA h s) := by
  have key : ∀ n : ℕ, ∀ s : ℝ≥0, (1 / 2 : ℝ≥0) ^ n ≤ s →
      IsCompactOperator (A.negPow hA h s) := by
    intro n
    induction n with
    | zero =>
      intro s hs1
      rw [pow_zero] at hs1
      rw [← tsub_add_cancel_of_le hs1, negPow_add hpos, negPow_one hpos,
        ContinuousLinearMap.mul_def, ContinuousLinearMap.coe_comp]
      exact (A.isCompactOperator_greenOperator hA h).clm_comp _
    | succ n ih =>
      intro s hsn
      have h2 : (1 / 2 : ℝ≥0) ^ n ≤ s + s := by
        calc (1 / 2 : ℝ≥0) ^ n = (1 / 2) ^ (n + 1) + (1 / 2) ^ (n + 1) := by ring
          _ ≤ s + s := add_le_add hsn hsn
      have hsq := ih (s + s) h2
      rw [negPow_add hpos, ContinuousLinearMap.mul_def] at hsq
      refine IsCompactOperator.of_adjoint_comp_self ?_
      rwa [(isSelfAdjoint_negPow s).adjoint_eq]
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hs (by norm_num : (1 / 2 : ℝ≥0) < 1)
  exact key n s hn.le

/-- **The eigen-expansion of the negative powers.** If `b` is a Hilbert basis of eigenvectors of
`A`, with `A (b k) = λ k b k`, then `A^{-s} f = ∑ λ k ^ (-s) ⟪b k, f⟫ b k`. -/
theorem hasSum_negPow_apply (hker : A.ker = ⊥) (s : ℝ≥0) {κ : Type*} (b : HilbertBasis κ ℂ H)
    {lam : κ → ℝ} (hb : ∀ k, ∃ hk : b k ∈ A.domain, A ⟨b k, hk⟩ = (lam k : ℂ) • b k) (f : H) :
    HasSum (fun k ↦ ((lam k ^ (-(s : ℝ)) : ℝ) : ℂ) • b.repr f k • b k) (A.negPow hA h s f) := by
  refine ContinuousLinearMap.hasSum_smul_repr_of_apply_eq_smul _ b _ (fun k ↦ ?_) f
  obtain ⟨hk, hAk⟩ := hb k
  have hb0 : b k ≠ 0 := b.orthonormal.ne_zero k
  exact negPow_apply_of_apply_eq_smul hpos s ⟨b k, hk⟩
    (pos_of_apply_eq_smul hpos hker (u := ⟨b k, hk⟩) hb0 hAk) hAk

end NegPow

/-! ### Positive powers -/

section PosPow

variable (A) in
/-- The **positive power** `A^s`, for real `s ≥ 0`, of a strictly positive self-adjoint operator
`A` with compact resolvent: the inverse of the negative power `A^{-s}`, defined on its range. It is
self-adjoint (`LinearPMap.isSelfAdjoint_posPow`), equal to `A` for `s = 1`
(`LinearPMap.posPow_one`), and acts on an eigenvector of `A` for the eigenvalue `λ` as
multiplication by `λ^s` (`LinearPMap.posPow_apply_of_apply_eq_smul`). -/
def posPow (s : ℝ≥0) : H →ₗ.[ℂ] H :=
  ((A.negPow hA h s : H →ₗ[ℂ] H).toPMap ⊤).inverse

variable {hA h}

/-- The domain of `A^s` is the range of `A^{-s}`. -/
theorem posPow_domain (s : ℝ≥0) :
    (A.posPow hA h s).domain = LinearMap.range (A.negPow hA h s : H →ₗ[ℂ] H) := by
  rw [posPow, inverse_domain]
  ext f
  simp only [LinearMap.mem_range, ContinuousLinearMap.coe_coe]
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨x, rfl⟩
  · rintro ⟨x, rfl⟩
    exact ⟨⟨x, Submodule.mem_top⟩, rfl⟩

/-- Every value of `A^{-s}` lies in the domain of `A^s`. -/
theorem negPow_mem_posPow_domain (s : ℝ≥0) (f : H) :
    A.negPow hA h s f ∈ (A.posPow hA h s).domain := by
  rw [posPow_domain]
  exact LinearMap.mem_range_self _ f

variable (hpos : ∀ u : A.domain, 0 ≤ RCLike.re ⟪A u, (u : H)⟫_ℂ) (hker : A.ker = ⊥)
include hpos hker

private theorem ker_toPMap_negPow (s : ℝ≥0) :
    ((A.negPow hA h s : H →ₗ[ℂ] H).toPMap ⊤).ker = ⊥ := by
  rw [eq_bot_iff]
  intro f hf
  obtain ⟨y, rfl, hy⟩ := mem_ker_iff.1 hf
  have hy' : A.negPow hA h s y = A.negPow hA h s 0 :=
    hy.trans (_root_.map_zero (A.negPow hA h s)).symm
  exact (Submodule.mem_bot ℂ).2 (injective_negPow hpos hker s hy')

/-- `A^s A^{-s} = 1`. -/
theorem posPow_negPow (s : ℝ≥0) (f : H) :
    A.posPow hA h s ⟨A.negPow hA h s f, negPow_mem_posPow_domain s f⟩ = f := by
  refine inverse_apply_eq (ker_toPMap_negPow hpos hker s) (x := ⟨f, Submodule.mem_top⟩) ?_
  rfl

/-- `A^{-s} A^s = 1` on the domain of `A^s`. -/
theorem negPow_posPow (s : ℝ≥0) (u : (A.posPow hA h s).domain) :
    A.negPow hA h s (A.posPow hA h s u) = u := by
  obtain ⟨f, hf⟩ := LinearMap.mem_range.1 ((posPow_domain s).le u.2)
  have hu : u = ⟨A.negPow hA h s f, negPow_mem_posPow_domain s f⟩ := Subtype.ext hf.symm
  rw [hu, posPow_negPow hpos hker]

/-- `A^s` is the unique operator on the range of `A^{-s}` inverting it: `A^s u = f` exactly when
`u = A^{-s} f`. -/
theorem posPow_apply_eq_iff (s : ℝ≥0) (u : (A.posPow hA h s).domain) (f : H) :
    A.posPow hA h s u = f ↔ (u : H) = A.negPow hA h s f := by
  constructor
  · rintro rfl
    exact (negPow_posPow hpos hker s u).symm
  · intro hu
    have hu' : u = ⟨A.negPow hA h s f, negPow_mem_posPow_domain s f⟩ := Subtype.ext hu
    rw [hu', posPow_negPow hpos hker]

/-- The positive powers are self-adjoint. -/
theorem isSelfAdjoint_posPow (s : ℝ≥0) : IsSelfAdjoint (A.posPow hA h s) :=
  ContinuousLinearMap.isSelfAdjoint_inverse_toPMap_top _ (isSelfAdjoint_negPow s)
    (injective_negPow hpos hker s)

/-- **The identity power.** `A^0` is defined everywhere and is the identity. -/
theorem posPow_zero : A.posPow hA h 0 = (LinearMap.id : H →ₗ[ℂ] H).toPMap ⊤ := by
  have hdom : (A.posPow hA h 0).domain = ⊤ := by
    rw [posPow_domain, negPow_zero hpos]
    exact LinearMap.range_eq_top.2 fun f ↦ ⟨f, rfl⟩
  refine LinearPMap.ext hdom fun u hu hu' ↦ ?_
  rw [posPow_apply_eq_iff hpos hker, negPow_zero hpos, one_apply_eq_self]
  rfl

/-- **`A^1 = A`.** -/
theorem posPow_one : A.posPow hA h 1 = A := by
  have hdom : (A.posPow hA h 1).domain = A.domain := by
    rw [posPow_domain, negPow_one hpos, range_greenOperator_of_ker_eq_bot hker]
  refine LinearPMap.ext hdom fun u hu hu' ↦ ?_
  rw [posPow_apply_eq_iff hpos hker, negPow_one hpos,
    greenOperator_apply_apply_of_ker_eq_bot hker]

/-- On an eigenvector of `A` for the eigenvalue `λ > 0`, the positive power `A^s` acts as
multiplication by `λ ^ s`. -/
theorem posPow_apply_of_apply_eq_smul (s : ℝ≥0) (u : A.domain) {lam : ℝ} (hlam : 0 < lam)
    (hu : A u = (lam : ℂ) • (u : H)) :
    ∃ hu' : (u : H) ∈ (A.posPow hA h s).domain,
      A.posPow hA h s ⟨u, hu'⟩ = ((lam ^ (s : ℝ) : ℝ) : ℂ) • (u : H) := by
  -- `u = A^{-s} (λ^s u)`.
  have hneg : A.negPow hA h s (((lam ^ (s : ℝ) : ℝ) : ℂ) • (u : H)) = u := by
    rw [ContinuousLinearMap.map_smul, negPow_apply_of_apply_eq_smul hpos s u hlam hu, smul_smul,
      ← Complex.ofReal_mul, ← Real.rpow_add hlam, add_neg_cancel, Real.rpow_zero,
      Complex.ofReal_one, one_smul]
  have hmem : (u : H) ∈ (A.posPow hA h s).domain := hneg ▸ negPow_mem_posPow_domain s _
  exact ⟨hmem, (posPow_apply_eq_iff hpos hker s _ _).2 hneg.symm⟩

end PosPow

/-! ### Operators commuting with `A` -/

section Commute

variable {hA h} {U : H →L[ℂ] H} (hUdom : ∀ u ∈ A.domain, U u ∈ A.domain)
  (hUA : ∀ u : A.domain, A ⟨U u, hUdom u u.2⟩ = U (A u))
include hUA

/-- A bounded operator commuting with a strictly positive operator `A` commutes with its Green
operator. -/
theorem commute_greenOperator (hker : A.ker = ⊥) : Commute (A.greenOperator hA h) U := by
  refine ContinuousLinearMap.ext fun f ↦ ?_
  simp only [ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_apply]
  -- Both `G (U f)` and `U (G f)` solve `A v = U f`.
  set u : A.domain := ⟨A.greenOperator hA h f, A.greenOperator_mem_domain hA h f⟩
  have h1 := greenOperator_apply_apply_of_ker_eq_bot (hA := hA) (h := h) hker
    ⟨U u, hUdom u u.2⟩
  rw [hUA, apply_greenOperator_of_ker_eq_bot hker] at h1
  exact h1

/-- **Equivariance of the negative powers.** A bounded operator commuting with a strictly
positive operator `A`, such as the unitary action of a symmetry group of `A`, commutes with every
negative power `A^{-s}`. -/
theorem commute_negPow (hker : A.ker = ⊥) (s : ℝ≥0) : Commute (A.negPow hA h s) U := by
  rw [negPow_def, CFC.rpow_def]
  exact Commute.cfc_nnreal (commute_greenOperator hUdom hUA hker) _

/-- **Equivariance of the positive powers.** A bounded operator `U` commuting with a strictly
positive operator `A` preserves the domain of every positive power `A^s` and commutes with it. -/
theorem posPow_apply_of_commute (hpos : ∀ u : A.domain, 0 ≤ RCLike.re ⟪A u, (u : H)⟫_ℂ)
    (hker : A.ker = ⊥) (s : ℝ≥0) (u : (A.posPow hA h s).domain) :
    ∃ hu : U u ∈ (A.posPow hA h s).domain,
      A.posPow hA h s ⟨U u, hu⟩ = U (A.posPow hA h s u) := by
  have hneg : A.negPow hA h s (U (A.posPow hA h s u)) = U u := by
    rw [← ContinuousLinearMap.comp_apply, ← ContinuousLinearMap.mul_def,
      (commute_negPow hUdom hUA hker s).eq, ContinuousLinearMap.mul_def,
      ContinuousLinearMap.comp_apply, negPow_posPow hpos hker]
  have hmem : U u ∈ (A.posPow hA h s).domain := hneg ▸ negPow_mem_posPow_domain s _
  exact ⟨hmem, (posPow_apply_eq_iff hpos hker s _ _).2 hneg.symm⟩

end Commute

end LinearPMap
