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
import TauCeti.Analysis.InnerProductSpace.Spectrum
import TauCeti.Analysis.Normed.Operator.Compact.FunctionalCalculus
import TauCeti.Analysis.Normed.Operator.Compact.Interpolation

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
  injective (`LinearPMap.negPow_injective`) bounded operator, with `A^{-0} = 1`
  (`LinearPMap.negPow_zero`), `A^{-1} = G` (`LinearPMap.negPow_one`) and the semigroup law
  `A^{-(s + t)} = A^{-s} A^{-t}` (`LinearPMap.negPow_add`). It is compact for every `s > 0`
  (`LinearPMap.isCompactOperator_negPow`).
* `LinearPMap.negPow_apply_of_apply_eq_smul`: `A^{-s} u = λ^{-s} u` on eigenvectors.
* `LinearPMap.posPow`: the positive power `A^s`, a self-adjoint operator
  (`LinearPMap.isSelfAdjoint_posPow`) inverse to `A^{-s}`
  (`LinearPMap.posPow_negPow`, `LinearPMap.negPow_posPow`), with `A^1 = A`
  (`LinearPMap.posPow_one`) and `A^s u = λ^s u` on eigenvectors
  (`LinearPMap.posPow_apply_of_apply_eq_smul`). Its domains decrease in `s`
  (`LinearPMap.posPow_domain_antitone`), and `A^s A^t = A^{s + t}` on the domain of `A^{s + t}`
  (`LinearPMap.posPow_posPow`).
* `LinearPMap.commute_negPow` and `LinearPMap.posPow_apply_of_commute`: a bounded operator
  commuting with `A`, such as the unitary action of a symmetry group, commutes with every power
  and preserves its domain.

## References

* M. A. Shubin, *Pseudodifferential Operators and Spectral Theory*, Chapter II, §10.
* K. Schmüdgen, *Unbounded Self-adjoint Operators on Hilbert Space*, Chapter 5.
-/

public section

noncomputable section

open scoped InnerProductSpace NNReal

namespace LinearPMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A) (h : A.HasCompactResolvent)

/-! ### Negative powers -/

section NegPow

variable (A) in
/-- The **negative power** `A^{-s}`, for real `s ≥ 0`, of a self-adjoint operator `A` with
compact resolvent: the power `G ^ s` of its Green operator `G` in the continuous functional
calculus. When `A` is strictly positive, `G = A⁻¹`, and `A^{-s}` acts on an eigenvector of `A`
for the eigenvalue `λ` as multiplication by `λ^{-s}` (`LinearPMap.negPow_apply_of_apply_eq_smul`).
When `A` has nonnegative quadratic form, the identity power `A^{-0}` is the identity operator
(`LinearPMap.negPow_zero`). The definition is meaningful only for such `A`: otherwise `G` is not
positive and `A^{-s}` is the junk value `0`. -/
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
  exact CFC.rpow_rpow_of_exponent_nonneg _ _ _ s.property t.property
      (greenOperator_nonneg hA h hpos)

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
    (Real.continuous_rpow_const s.property).continuousOn hG.isSelfAdjoint).trans ?_
  rw [Real.inv_rpow hlam.le, Real.rpow_neg hlam.le]

/-- The negative powers of a strictly positive operator are injective. -/
theorem negPow_injective (hker : A.ker = ⊥) (s : ℝ≥0) : Function.Injective (A.negPow hA h s) := by
  obtain ⟨n, hn⟩ := exists_nat_ge s
  -- `A^{-n} = A^{-(n - s)} A^{-s}` and `A^{-n} = G ^ n` is injective.
  have hfac : A.negPow hA h n = A.negPow hA h (n - s) * A.negPow hA h s := by
    rw [← negPow_add hpos, tsub_add_cancel_of_le hn]
  have hinj : Function.Injective (A.negPow hA h n) := by
    rw [negPow_natCast hpos, FunLike.coe_pow_eq_iterate]
    exact (A.greenOperator_injective hA h hker).iterate n
  rw [hfac, ContinuousLinearMap.mul_def, ContinuousLinearMap.coe_comp] at hinj
  exact hinj.of_comp

/-- **Compactness.** For `s > 0` the negative power `A^{-s}` is a compact operator. -/
theorem isCompactOperator_negPow {s : ℝ≥0} (hs : 0 < s) :
    IsCompactOperator (A.negPow hA h s) := by
  -- For `s ≥ 1` this follows from `A^{-s} = A^{-(s - 1)} G`; smaller `s` reduce to larger ones,
  -- since a self-adjoint operator is compact when its square is.
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
  ext f
  rw [posPow, ContinuousLinearMap.mem_domain_inverse_toPMap_top_iff, LinearMap.mem_range]
  simp only [ContinuousLinearMap.coe_coe]

/-- Every value of `A^{-s}` lies in the domain of `A^s`. -/
theorem negPow_mem_posPow_domain (s : ℝ≥0) (f : H) :
    A.negPow hA h s f ∈ (A.posPow hA h s).domain :=
  ContinuousLinearMap.apply_mem_domain_inverse_toPMap_top _ f

/-- **Nesting of domains.** The domains of the positive powers decrease: for `s ≤ t`, the domain of
`A^t` is contained in that of `A^s`. -/
theorem posPow_domain_antitone (hpos : ∀ u : A.domain, 0 ≤ RCLike.re ⟪A u, (u : H)⟫_ℂ) :
    Antitone fun s ↦ (A.posPow hA h s).domain := by
  intro s t hst
  dsimp only
  rw [posPow_domain, posPow_domain]
  rintro _ ⟨f, rfl⟩
  -- `A^{-t} f = A^{-s} (A^{-(t - s)} f)`.
  refine ⟨A.negPow hA h (t - s) f, ?_⟩
  simp only [ContinuousLinearMap.coe_coe]
  rw [← mul_apply_eq_comp, ← negPow_add hpos, add_tsub_cancel_of_le hst]

/-- **The identity power.** `A^0` is defined everywhere and is the identity. -/
theorem posPow_zero (hpos : ∀ u : A.domain, 0 ≤ RCLike.re ⟪A u, (u : H)⟫_ℂ) :
    A.posPow hA h 0 = (LinearMap.id : H →ₗ[ℂ] H).toPMap ⊤ := by
  have hdom : (A.posPow hA h 0).domain = ⊤ := by
    rw [posPow_domain, negPow_zero hpos, LinearMap.range_eq_top]
    exact fun f ↦ ⟨f, by simp⟩
  have hinj : Function.Injective (A.negPow hA h 0) := by
    rw [negPow_zero hpos]
    exact Function.injective_id
  refine LinearPMap.ext hdom fun x hx₁ hx₂ ↦ ?_
  -- `A^0 x = A^{-0} (A^0 x) = x`, as `A^{-0} = 1`.
  calc A.posPow hA h 0 ⟨x, hx₁⟩ = A.negPow hA h 0 (A.posPow hA h 0 ⟨x, hx₁⟩) := by
        rw [negPow_zero hpos, one_apply_eq_self]
    _ = x := ContinuousLinearMap.apply_inverse_toPMap_top _ hinj _
    _ = (LinearMap.id : H →ₗ[ℂ] H).toPMap ⊤ ⟨x, hx₂⟩ :=
        (LinearMap.id_apply x).symm.trans (LinearMap.toPMap_apply _ ⊤ ⟨x, hx₂⟩).symm

variable (hpos : ∀ u : A.domain, 0 ≤ RCLike.re ⟪A u, (u : H)⟫_ℂ) (hker : A.ker = ⊥)
include hpos hker

/-- `A^s A^{-s} = 1`. -/
theorem posPow_negPow (s : ℝ≥0) (f : H) :
    A.posPow hA h s ⟨A.negPow hA h s f, negPow_mem_posPow_domain s f⟩ = f :=
  ContinuousLinearMap.inverse_toPMap_top_apply _ (negPow_injective hpos hker s) f

/-- `A^{-s} A^s = 1` on the domain of `A^s`. -/
theorem negPow_posPow (s : ℝ≥0) (u : (A.posPow hA h s).domain) :
    A.negPow hA h s (A.posPow hA h s u) = u :=
  ContinuousLinearMap.apply_inverse_toPMap_top _ (negPow_injective hpos hker s) u

/-- If `A^{-s} f = v`, then `v` lies in the domain of `A^s` and `A^s v = f`. -/
theorem posPow_apply_of_negPow_apply_eq {s : ℝ≥0} {f v : H} (hv : A.negPow hA h s f = v) :
    ∃ hv' : v ∈ (A.posPow hA h s).domain, A.posPow hA h s ⟨v, hv'⟩ = f := by
  subst hv
  exact ⟨negPow_mem_posPow_domain s f, posPow_negPow hpos hker s f⟩

/-- `A^s u = f` exactly when `u = A^{-s} f`. -/
theorem posPow_apply_eq_iff (s : ℝ≥0) (u : (A.posPow hA h s).domain) (f : H) :
    A.posPow hA h s u = f ↔ (u : H) = A.negPow hA h s f := by
  constructor
  · rintro rfl
    exact (negPow_posPow hpos hker s u).symm
  · intro hu
    rw [show u = ⟨A.negPow hA h s f, negPow_mem_posPow_domain s f⟩ from Subtype.ext hu,
      posPow_negPow hpos hker]

/-- **The semigroup law for positive powers.** On the domain of `A^{s + t}`, the power `A^t` takes
values in the domain of `A^s`, and `A^s A^t = A^{s + t}`. -/
theorem posPow_posPow (s t : ℝ≥0) (u : (A.posPow hA h (s + t)).domain) :
    ∃ hu : (u : H) ∈ (A.posPow hA h t).domain,
      ∃ hu' : A.posPow hA h t ⟨u, hu⟩ ∈ (A.posPow hA h s).domain,
        A.posPow hA h s ⟨A.posPow hA h t ⟨u, hu⟩, hu'⟩ = A.posPow hA h (s + t) u := by
  -- `u = A^{-t} (A^{-s} f)` for `f = A^{s + t} u`.
  have hneg : A.negPow hA h t (A.negPow hA h s (A.posPow hA h (s + t) u)) = u := by
    rw [← mul_apply_eq_comp, ← negPow_add hpos, add_comm, negPow_posPow hpos hker]
  obtain ⟨hu, htu⟩ := posPow_apply_of_negPow_apply_eq hpos hker hneg
  refine ⟨hu, ?_⟩
  simp_rw [htu]
  exact ⟨negPow_mem_posPow_domain s _, posPow_negPow hpos hker s _⟩

/-- The positive powers are self-adjoint. -/
theorem isSelfAdjoint_posPow (s : ℝ≥0) : IsSelfAdjoint (A.posPow hA h s) :=
  ContinuousLinearMap.isSelfAdjoint_inverse_toPMap_top _ (isSelfAdjoint_negPow s)
    (negPow_injective hpos hker s)

/-- **`A^1 = A`.** -/
theorem posPow_one : A.posPow hA h 1 = A := by
  have hdom : (A.posPow hA h 1).domain = A.domain := by
    rw [posPow_domain, negPow_one hpos, A.range_greenOperator_of_ker_eq_bot hA h hker]
  refine LinearPMap.ext hdom fun x hx₁ hx₂ ↦ ?_
  rw [posPow_apply_eq_iff hpos hker, negPow_one hpos,
    A.greenOperator_apply_apply_of_ker_eq_bot hA h hker]

/-- On an eigenvector of `A` for the eigenvalue `λ > 0`, the positive power `A^s` acts as
multiplication by `λ ^ s`. -/
theorem posPow_apply_of_apply_eq_smul (s : ℝ≥0) (u : A.domain) {lam : ℝ} (hlam : 0 < lam)
    (hu : A u = (lam : ℂ) • (u : H)) :
    ∃ hu' : (u : H) ∈ (A.posPow hA h s).domain,
      A.posPow hA h s ⟨u, hu'⟩ = ((lam ^ (s : ℝ) : ℝ) : ℂ) • (u : H) := by
  -- `u = A^{-s} (λ^s u)`.
  have hneg : A.negPow hA h s (((lam ^ (s : ℝ) : ℝ) : ℂ) • (u : H)) = u := by
    rw [ContinuousLinearMap.map_smul, negPow_apply_of_apply_eq_smul hpos s u hlam hu]
    simp [smul_smul, ← Real.rpow_add hlam]
  exact posPow_apply_of_negPow_apply_eq hpos hker hneg

end PosPow

/-! ### Operators commuting with `A` -/

section Commute

variable {hA h} {U : H →L[ℂ] H} (hUdom : ∀ u ∈ A.domain, U u ∈ A.domain)
  (hUA : ∀ u : A.domain, A ⟨U u, hUdom u u.property⟩ = U (A u))
include hUA

/-- **Equivariance of the negative powers.** A bounded operator commuting with a strictly
positive operator `A`, such as the unitary action of a symmetry group of `A`, commutes with every
negative power `A^{-s}`. -/
theorem commute_negPow (hker : A.ker = ⊥) (s : ℝ≥0) : Commute (A.negPow hA h s) U := by
  rw [negPow_def, CFC.rpow_def]
  exact Commute.cfc_nnreal (A.commute_greenOperator hA h hUdom hUA hker) _

/-- **Equivariance of the positive powers.** A bounded operator `U` commuting with a strictly
positive operator `A` preserves the domain of every positive power `A^s` and commutes with it. -/
theorem posPow_apply_of_commute (hpos : ∀ u : A.domain, 0 ≤ RCLike.re ⟪A u, (u : H)⟫_ℂ)
    (hker : A.ker = ⊥) (s : ℝ≥0) (u : (A.posPow hA h s).domain) :
    ∃ hu : U u ∈ (A.posPow hA h s).domain,
      A.posPow hA h s ⟨U u, hu⟩ = U (A.posPow hA h s u) := by
  have hneg : A.negPow hA h s (U (A.posPow hA h s u)) = U u := by
    simpa [negPow_posPow hpos hker] using
      congr($((commute_negPow (hA := hA) (h := h) hUdom hUA hker s).eq) (A.posPow hA h s u))
  exact posPow_apply_of_negPow_apply_eq hpos hker hneg

end Commute

end LinearPMap
