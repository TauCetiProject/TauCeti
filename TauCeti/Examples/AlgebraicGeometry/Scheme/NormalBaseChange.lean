/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Scheme.Normal
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
public import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Checks for normality under separably generated base change of the ground field

`TauCeti.AlgebraicGeometry.isNormalScheme_pullback_of_isSeparablyGenerated` applies to every
finite extension of `ℚ`, such as `ℚ(i)`, where the base change of `Spec ℚ(i)` is two reduced points,
and to transcendental extensions such as `k(s)` over a perfect field `k`, which are not algebraic,
so that `Algebra.IsSeparable k k(s)` fails: the hypothesis is separable generation, not
separability. In both cases the separable-generation hypothesis is found by instance search from
the perfectness of the ground field.

The conclusion concerns the local rings and cannot be strengthened, nor the hypothesis dropped:

* For `k'/k` containing an element `i ∉ k` with `i² = -1`, the ring `k' ⊗[k] k'` is not a domain
  (`(i ⊗ 1 - 1 ⊗ i)(i ⊗ 1 + 1 ⊗ i) = 0`), so the base change of `Spec k'` along `k'` is not
  integral (`not_isIntegral_pullback_of_mul_self_eq_neg_one`). For `k' = ℚ(i)` it is normal but
  not integral (`isNormalScheme_pullback_rat_adjoin_I`, `not_isIntegral_pullback_rat_adjoin_I`).
* For `k` of characteristic `p` and `k'/k` containing an element `a ∉ k` with `a ^ p ∈ k` (such as
  `k(t ^ (1 / p))` over `𝔽_p(t)`), `a ⊗ 1 - 1 ⊗ a` is a nonzero nilpotent of `k' ⊗[k] k'`, so the
  base change of the normal scheme `Spec k'` along the inseparable `k'/k` is not reduced, hence
  not normal (`not_isNormalScheme_pullback_of_pow_char_mem_range`): separability cannot be
  dropped.
-/

public section

open AlgebraicGeometry CategoryTheory Limits TauCeti.AlgebraicGeometry

universe u

namespace TauCeti.NormalBaseChangeExample

-- Base change of a normal `ℚ`-scheme along a finite extension of `ℚ` (such as `ℚ(i)`) is normal.
example {X : Scheme.{0}} (f : X ⟶ Spec (.of ℚ)) [IsNormalScheme X] (K : Type) [Field K]
    [Algebra ℚ K] [FiniteDimensional ℚ K] :
    IsNormalScheme (pullback f (Spec.map (CommRingCat.ofHom (algebraMap ℚ K)))) :=
  isNormalScheme_pullback_of_isSeparablyGenerated f

-- Base change along the purely transcendental extension `k(s) / k` of a perfect field: not an
-- algebraic extension, but separably generated.
example (k : Type u) [Field k] [PerfectField k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    [IsNormalScheme X] :
    IsNormalScheme (pullback f (Spec.map (CommRingCat.ofHom
      (algebraMap k (FractionRing (Polynomial k)))))) :=
  isNormalScheme_pullback_of_isSeparablyGenerated f

-- The extension `k(s) / k` is not algebraic, so `Algebra.IsSeparable` fails for it.
example (k : Type u) [Field k] : ¬ Algebra.IsSeparable k (FractionRing (Polynomial k)) :=
  fun _ ↦ Polynomial.transcendental_X k <| (isAlgebraic_algHom_iff
    (IsScalarTower.toAlgHom k (Polynomial k) (FractionRing (Polynomial k)))
    (IsFractionRing.injective _ _)).mp (Algebra.IsAlgebraic.isAlgebraic _)

open scoped TensorProduct

section TensorSelf

variable {k K : Type u} [Field k] [CommRing K] [Algebra k K]

/-- If `a ∈ K` is not in the image of `k`, then `a ⊗ 1 + c • (1 ⊗ a)` is nonzero in `K ⊗[k] K`
for every `c : k`: a functional on `K` vanishing at `1` and not at `a`, applied to the left
factor, sends it to a nonzero element. -/
theorem tmul_one_add_smul_one_tmul_ne_zero {a : K} (ha : a ∉ Set.range (algebraMap k K))
    (c : k) : a ⊗ₜ[k] (1 : K) + c • ((1 : K) ⊗ₜ[k] a) ≠ 0 := by
  have hq : (Submodule.span k {(1 : K)}).mkQ a ≠ 0 := by
    rw [Ne, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, Submodule.mem_span_singleton]
    rintro ⟨b, rfl⟩
    exact ha ⟨b, Algebra.algebraMap_eq_smul_one b⟩
  obtain ⟨φ, hφ⟩ := Module.Projective.exists_dual_eq_one k hq
  let f : K →ₗ[k] k := φ ∘ₗ (Submodule.span k {(1 : K)}).mkQ
  have hf1 : f 1 = 0 := by
    simp [f, (Submodule.Quotient.mk_eq_zero _).mpr (Submodule.mem_span_singleton_self (1 : K))]
  have hfa : f a = 1 := hφ
  intro h
  have h' := congrArg ((TensorProduct.lid k K).toLinearMap ∘ₗ TensorProduct.map f LinearMap.id) h
  simp [hf1, hfa] at h'
  exact ha ⟨0, by simp [eq_zero_of_zero_eq_one h'.symm a]⟩

/-- If `K` contains an element `i` not in the image of `k` with `i * i = -1`, then `K ⊗[k] K` is
not a domain: `(i ⊗ 1 - 1 ⊗ i) * (i ⊗ 1 + 1 ⊗ i) = 0`, and both factors are nonzero. -/
theorem not_isDomain_tensorProduct_of_mul_self_eq_neg_one {i : K} (hi : i * i = -1)
    (hik : i ∉ Set.range (algebraMap k K)) : ¬ IsDomain (K ⊗[k] K) := by
  intro _
  have h₁ := tmul_one_add_smul_one_tmul_ne_zero hik (-1)
  have h₂ := tmul_one_add_smul_one_tmul_ne_zero hik 1
  rw [neg_one_smul, ← sub_eq_add_neg] at h₁
  rw [one_smul] at h₂
  refine mul_ne_zero h₁ h₂ ?_
  rw [sub_mul, mul_add, mul_add, Algebra.TensorProduct.tmul_mul_tmul,
    Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul,
    Algebra.TensorProduct.tmul_mul_tmul, hi]
  simp only [mul_one, one_mul, TensorProduct.tmul_neg, TensorProduct.neg_tmul]
  abel

/-- If `k` has prime characteristic `p` and `K` contains an element `a` not in the image of `k`
with `a ^ p` in the image of `k`, then `K ⊗[k] K` is not reduced: `a ⊗ 1 - 1 ⊗ a` is a nonzero
nilpotent, as its `p`-th power is `a ^ p ⊗ 1 - 1 ⊗ a ^ p = 0`. -/
theorem not_isReduced_tensorProduct_of_pow_char_mem_range (p : ℕ) [Fact p.Prime] [CharP k p]
    {a : K} (ha : a ∉ Set.range (algebraMap k K)) (hap : a ^ p ∈ Set.range (algebraMap k K)) :
    ¬ IsReduced (K ⊗[k] K) := by
  intro hred
  have hne := tmul_one_add_smul_one_tmul_ne_zero ha (-1)
  rw [neg_one_smul, ← sub_eq_add_neg] at hne
  have : Nontrivial (K ⊗[k] K) := ⟨⟨_, _, hne⟩⟩
  have : CharP (K ⊗[k] K) p := charP_of_injective_algebraMap' k p
  refine hne (hred.eq_zero _ ⟨p, ?_⟩)
  obtain ⟨c, hc⟩ := hap
  rw [sub_pow_char, Algebra.TensorProduct.tmul_pow, Algebra.TensorProduct.tmul_pow, one_pow,
    ← hc, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul, sub_self]

end TensorSelf

open Limits

/-- **The base change of `Spec K` along `K` need not be integral.** If `K / k` is a field
extension and `K` contains an element `i ∉ k` with `i * i = -1`, then
`Spec K ×_{Spec k} Spec K = Spec (K ⊗[k] K)` is not integral. -/
theorem not_isIntegral_pullback_of_mul_self_eq_neg_one {k K : Type u} [Field k] [Field K]
    [Algebra k K] {i : K} (hi : i * i = -1) (hik : i ∉ Set.range (algebraMap k K)) :
    ¬ IsIntegral (pullback (Spec.map (CommRingCat.ofHom (algebraMap k K)))
      (Spec.map (CommRingCat.ofHom (algebraMap k K)))) := by
  intro _
  have := IsIntegral.of_isIso (pullbackSpecIso k K K).hom
  rw [affine_isIntegral_iff] at this
  exact not_isDomain_tensorProduct_of_mul_self_eq_neg_one hi hik this

/-- **Separability cannot be dropped.** If `k` has prime characteristic `p` and the field
extension `K / k` contains an element `a ∉ k` with `a ^ p ∈ k`, then the base change
`Spec K ×_{Spec k} Spec K = Spec (K ⊗[k] K)` of the normal scheme `Spec K` along the inseparable
extension `K / k` is not reduced, so it is not normal. -/
theorem not_isNormalScheme_pullback_of_pow_char_mem_range {k K : Type u} [Field k] [Field K]
    [Algebra k K] (p : ℕ) [Fact p.Prime] [CharP k p] {a : K}
    (ha : a ∉ Set.range (algebraMap k K)) (hap : a ^ p ∈ Set.range (algebraMap k K)) :
    ¬ IsNormalScheme (pullback (Spec.map (CommRingCat.ofHom (algebraMap k K)))
      (Spec.map (CommRingCat.ofHom (algebraMap k K)))) := by
  intro _
  have : IsReduced (Spec (.of (K ⊗[k] K))) := isReduced_of_isOpenImmersion
    (pullbackSpecIso k K K).inv
  rw [affine_isReduced_iff] at this
  exact not_isReduced_tensorProduct_of_pow_char_mem_range p ha hap this

section GaussianRationals

open IntermediateField

/-- `ℚ(i)` is a finite extension of `ℚ`. -/
instance instFiniteDimensionalRatAdjoinI : FiniteDimensional ℚ ℚ⟮Complex.I⟯ :=
  adjoin.finiteDimensional ⟨Polynomial.X ^ 2 + 1, Polynomial.monic_X_pow_add_C 1 two_ne_zero,
    by simp⟩

/-- The generator `i` of `ℚ(i)` is not rational. -/
theorem gen_notMem_range_algebraMap :
    (AdjoinSimple.gen ℚ Complex.I) ∉ Set.range (algebraMap ℚ ℚ⟮Complex.I⟯) := by
  rintro ⟨q, hq⟩
  have := congrArg (fun x : ℚ⟮Complex.I⟯ ↦ ((x : ℂ)).im) hq
  simp at this

/-- **Check.** Base change of `Spec ℚ(i)` along `ℚ(i) / ℚ` is normal. -/
theorem isNormalScheme_pullback_rat_adjoin_I :
    IsNormalScheme (pullback (Spec.map (CommRingCat.ofHom (algebraMap ℚ ℚ⟮Complex.I⟯)))
      (Spec.map (CommRingCat.ofHom (algebraMap ℚ ℚ⟮Complex.I⟯)))) :=
  isNormalScheme_pullback_of_isSeparablyGenerated _

/-- **Check.** Base change of `Spec ℚ(i)` along `ℚ(i) / ℚ`, which is `Spec (ℚ(i) × ℚ(i))`, is not
integral: the conclusion of `isNormalScheme_pullback_of_isSeparablyGenerated` concerns the local
rings and cannot be strengthened to integrality. -/
theorem not_isIntegral_pullback_rat_adjoin_I :
    ¬ IsIntegral (pullback (Spec.map (CommRingCat.ofHom (algebraMap ℚ ℚ⟮Complex.I⟯)))
      (Spec.map (CommRingCat.ofHom (algebraMap ℚ ℚ⟮Complex.I⟯)))) :=
  not_isIntegral_pullback_of_mul_self_eq_neg_one
    (Subtype.ext (by simp)) gen_notMem_range_algebraMap

end GaussianRationals

end TauCeti.NormalBaseChangeExample
