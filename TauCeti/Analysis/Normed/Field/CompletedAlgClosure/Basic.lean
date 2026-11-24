/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Field.Instances
public import Mathlib.Analysis.Normed.Module.Completion
public import Mathlib.Analysis.Normed.Unbundled.SpectralNorm
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.FieldTheory.KrullTopology
public import Mathlib.FieldTheory.SeparableClosure

import Mathlib.Analysis.Normed.Algebra.Ultra
import Mathlib.Analysis.Normed.Field.Approximation
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.FieldTheory.PurelyInseparable.Basic
import Mathlib.Tactic.ComputeDegree

/-!
# The completed algebraic closure of a complete non-archimedean field

Let `K` be a field complete for a nontrivial ultrametric absolute value. Its algebraic closure
`K^alg` carries the spectral norm, the unique power-multiplicative extension of the absolute value
of `K` (Mathlib's `spectralNorm_unique`), and its uniform completion `C` is a complete normed
field and normed `K`-algebra. This file defines both and proves that the separable closure of
`K` is dense in `K^alg` and in `C`.

## Main definitions

* `TauCeti.SpectralAlgClosure K`: a type synonym of `AlgebraicClosure K` whose normed-field and
  normed-algebra structures are Mathlib's `spectralNorm.normedField` and
  `spectralNorm.normedAlgebra`. The synonym keeps the spectral norm from becoming an instance on
  `AlgebraicClosure K` itself.
* `TauCeti.SpectralAlgClosure.algEquiv K`: the canonical `K`-algebra isomorphism
  `AlgebraicClosure K ≃ₐ[K] SpectralAlgClosure K`.
* `TauCeti.CompletedAlgClosure K`: the field `C`, the uniform completion of
  `SpectralAlgClosure K`.

## Main results

* `TauCeti.dense_separableClosure` and `TauCeti.denseRange_separableClosure_completion`: in an
  algebraically closed normed field algebraic over `K`, and in its completion, the separable
  closure of `K` is dense.
* `TauCeti.SpectralAlgClosure.dense_separableClosure`: `K^sep` is dense in `K^alg`.
* `TauCeti.CompletedAlgClosure.denseRange_separableClosure`: `K^sep` is dense in `C`.

## Implementation notes

In characteristic `p > 0`, an element `a ∈ K^alg` has `a ^ p ^ n = b ∈ K^sep` for some `n ≥ 1`. For
`t ∈ K` nonzero the polynomial `X ^ p ^ n - t X - b` has derivative `-t`, so it is separable over
`K^sep` and its roots in `K^alg` are separable over `K`; by continuity of roots
(`Polynomial.exists_roots_norm_sub_lt_of_norm_coeff_sub_lt`) one of them tends to `a` as
`t → 0`.

## References

* A. J. de Jong and M. van der Put, *Étale cohomology of rigid analytic spaces*, Documenta Math.
  1 (1996), §3.6.
-/

public section

noncomputable section

open Polynomial

namespace TauCeti

universe u

/-- The algebraic closure `K^alg` of a field `K`, as a type synonym of `AlgebraicClosure K`. For a
complete non-archimedean `K` it carries the spectral norm, the unique power-multiplicative
extension of the absolute value of `K`. The synonym keeps that norm from becoming an instance on
`AlgebraicClosure K` itself. -/
@[expose] def SpectralAlgClosure (K : Type u) [Field K] : Type u := AlgebraicClosure K

namespace SpectralAlgClosure

section Field

variable (K : Type u) [Field K]

/-- The field structure of `AlgebraicClosure K`. -/
instance instField : Field (SpectralAlgClosure K) :=
  inferInstanceAs (Field (AlgebraicClosure K))

/-- The `K`-algebra structure of `AlgebraicClosure K`. -/
instance instAlgebra : Algebra K (SpectralAlgClosure K) :=
  inferInstanceAs (Algebra K (AlgebraicClosure K))

/-- `K^alg` is algebraic over `K`. -/
instance instIsAlgebraic : Algebra.IsAlgebraic K (SpectralAlgClosure K) :=
  inferInstanceAs (Algebra.IsAlgebraic K (AlgebraicClosure K))

/-- `K^alg` is algebraically closed. -/
instance instIsAlgClosed : IsAlgClosed (SpectralAlgClosure K) :=
  inferInstanceAs (IsAlgClosed (AlgebraicClosure K))

/-- The canonical `K`-algebra isomorphism from `AlgebraicClosure K` to its type synonym
`SpectralAlgClosure K`, the identity on the underlying type. -/
def algEquiv : AlgebraicClosure K ≃ₐ[K] SpectralAlgClosure K :=
  AlgEquiv.refl

/-- `algEquiv K` is the identity of the underlying type of `AlgebraicClosure K`. -/
theorem algEquiv_apply (x : AlgebraicClosure K) : algEquiv K x = x :=
  (rfl)

/-- The inverse of `algEquiv K` is the identity of the underlying type of `AlgebraicClosure K`. -/
theorem algEquiv_symm_apply (x : SpectralAlgClosure K) : (algEquiv K).symm x = x :=
  (rfl)

/-- `σ ↦ algEquiv K ∘ σ ∘ (algEquiv K)⁻¹` is continuous for the Krull topologies: it is the
identity of the underlying type of `AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K`, and both Krull
topologies are defined from the same intermediate fields. -/
theorem continuous_autCongr_algEquiv : Continuous (AlgEquiv.autCongr (algEquiv K)) :=
  continuous_id

end Field

variable (K : Type u) [NontriviallyNormedField K] [CompleteSpace K] [IsUltrametricDist K]

/-- The spectral norm on `K^alg`, for `K` complete for a nontrivial ultrametric absolute value. -/
instance instNormedField : NormedField (SpectralAlgClosure K) :=
  spectralNorm.normedField K (SpectralAlgClosure K)

/-- `K^alg` with the spectral norm is a normed `K`-algebra. -/
instance instNormedAlgebra : NormedAlgebra K (SpectralAlgClosure K) :=
  spectralNorm.normedAlgebra K (SpectralAlgClosure K)

/-- The spectral norm on `K^alg` is nontrivial, since it extends the norm of `K`. -/
instance instNontriviallyNormedField : NontriviallyNormedField (SpectralAlgClosure K) :=
  spectralNorm.nontriviallyNormedField K (SpectralAlgClosure K)

/-- The spectral norm on `K^alg` is ultrametric. -/
instance instIsUltrametricDist : IsUltrametricDist (SpectralAlgClosure K) :=
  IsUltrametricDist.of_normedAlgebra K

/-- The norm of `K^alg` is the spectral norm. -/
theorem norm_def (x : SpectralAlgClosure K) : ‖x‖ = spectralNorm K (SpectralAlgClosure K) x :=
  rfl

/-- In an extension `L` of a field `K`, a root of `X ^ N - t X - b`, for `N` zero in `K`, `t ∈ K`
nonzero and `b` separable over `K`, is separable over `K`. -/
private theorem mem_separableClosure_of_eq_zero {K' L : Type*} [Field K'] [Field L] [Algebra K' L]
    {N : ℕ} (hN : (N : K') = 0) {t : K'} (ht : t ≠ 0) {b y : L}
    (hb : b ∈ separableClosure K' L) (hy : y ^ N - algebraMap K' L t * y - b = 0) :
    y ∈ separableClosure K' L := by
  set E := separableClosure K' L
  set c := algebraMap K' E t
  have hc : c ≠ 0 := (_root_.map_ne_zero _).2 ht
  let g : E[X] := X ^ N - C c * X - C ⟨b, hb⟩
  have hNE : (N : E) = 0 := by simpa using congr(algebraMap K' E $hN)
  have hg : g.Separable := by
    rw [separable_def]
    have hd : derivative g = -C c := by simp [g, derivative_X_pow, hNE]
    exact hd ▸ isCoprime_one_right.of_isCoprime_of_dvd_right (isUnit_C.2 hc.isUnit).neg.dvd
  have hgy : aeval y g = 0 := by simpa [g, c] using hy
  have hsep : IsSeparable E y := hg.of_dvd (minpoly.dvd E y hgy)
  exact mem_separableClosure_iff.2 (IsSeparable.of_algebra_isSeparable_of_isSeparable K' hsep)

/-- **The separable closure is dense** (de Jong–van der Put, §3.6). In an algebraically closed
normed field `L`, algebraic over a nontrivially normed field `K'`, the separable closure of `K'`
is dense. -/
theorem _root_.TauCeti.dense_separableClosure (K' L : Type*) [NontriviallyNormedField K']
    [NormedField L] [NormedAlgebra K' L] [Algebra.IsAlgebraic K' L] [IsAlgClosed L] :
    Dense (separableClosure K' L : Set L) := by
  set E := separableClosure K' L
  refine Metric.dense_iff.2 fun a δ hδ ↦ ?_
  obtain ⟨q, hq⟩ : ∃ q, ExpChar K' q := ⟨_, ringExpChar.expChar K'⟩
  have : ExpChar L q := expChar_of_injective_algebraMap
    (algebraMap K' _).injective q
  have : ExpChar E q := expChar_of_injective_algebraMap (algebraMap K' E).injective q
  obtain ⟨n, b, hb⟩ := IsPurelyInseparable.pow_mem E q a
  have hbE : a ^ q ^ n ∈ E := hb ▸ b.property
  by_cases hN : q ^ n = 1
  · exact ⟨a, Metric.mem_ball_self hδ, by simpa [hN] using hbE⟩
  set N := q ^ n
  have hN0 : N ≠ 0 := pow_ne_zero _ (expChar_ne_zero K' q)
  have hNK : (N : K') = 0 := by
    obtain _ | ⟨hq⟩ := hq
    · simp [N] at hN
    · have hn : n ≠ 0 := by rintro rfl; simp [N] at hN
      exact (CharP.cast_eq_zero_iff K' q N).2 (dvd_pow_self q hn)
  have hN2 : 1 < N := by omega
  set M := max ‖a‖ 1
  have hM : 0 < M := lt_max_of_lt_right one_pos
  have hε : 0 < (δ / M) ^ N / (N + 1) := by positivity
  obtain ⟨t, ht0, htε⟩ := NormedField.exists_norm_lt K' hε
  let f : L[X] := X ^ N - C (a ^ N)
  let g : L[X] := X ^ N - C (algebraMap K' _ t) * X - C (a ^ N)
  have hfm : f.Monic := monic_X_pow_sub_C _ hN0
  have hfdeg : f.natDegree = N := natDegree_X_pow_sub_C _
  have hgm : g.Monic := by
    simp only [g, sub_sub]
    exact monic_X_pow_sub (by compute_degree!)
  have hgdeg : g.natDegree = N := by
    simp only [g, sub_sub]
    rw [natDegree_sub_eq_left_of_natDegree_lt] <;> rw [natDegree_X_pow]
    exact natDegree_linear_le.trans_lt hN2
  have hcoeff (i : ℕ) : ‖g.coeff i - f.coeff i‖ < (δ / M) ^ N / (N + 1) := by
    rw [← coeff_sub, show g - f = -(C (algebraMap K' _ t) * X) by ring, coeff_neg, coeff_C_mul_X]
    split_ifs
    · rwa [norm_neg, norm_algebraMap']
    · simpa using hε
  obtain ⟨y, hy, hay⟩ := exists_roots_norm_sub_lt_of_norm_coeff_sub_lt hε (f := f) (g := g)
    (a := a) (by simp [f]) hfm hgm (hgdeg.trans hfdeg.symm) hcoeff (IsAlgClosed.splits g)
  refine ⟨y, ?_, mem_separableClosure_of_eq_zero hNK (norm_pos_iff.1 ht0) hbE ?_⟩
  · rw [hfdeg, mul_div_cancel₀ _ (by positivity), Real.pow_rpow_inv_natCast (by positivity) hN0,
      div_mul_cancel₀ _ hM.ne'] at hay
    rwa [Metric.mem_ball, dist_comm, dist_eq_norm]
  · simpa [g, sub_sub] using (mem_roots hgm.ne_zero).1 hy

/-- **`K^sep` is dense in `K^alg`** (de Jong–van der Put, §3.6). -/
theorem dense_separableClosure :
    Dense (separableClosure K (SpectralAlgClosure K) : Set (SpectralAlgClosure K)) :=
  TauCeti.dense_separableClosure K (SpectralAlgClosure K)

end SpectralAlgClosure

/-- The completed algebraic closure `C` of a complete non-archimedean field `K`: the uniform
completion of `K^alg` for the spectral norm, a complete normed field and normed `K`-algebra. For
`K = ℚ_p` this is the construction of Mathlib's `PadicComplex p`. -/
abbrev CompletedAlgClosure (K : Type u) [NontriviallyNormedField K] [CompleteSpace K]
    [IsUltrametricDist K] : Type u :=
  UniformSpace.Completion (SpectralAlgClosure K)

/-- **The separable closure is dense in the completion.** For an algebraically closed normed field
`L`, algebraic over a nontrivially normed field `K'`, the separable closure of `K'` in `L` has
dense image in the completion of `L`. -/
theorem denseRange_separableClosure_completion (K' L : Type*) [NontriviallyNormedField K']
    [NormedField L] [NormedAlgebra K' L] [Algebra.IsAlgebraic K' L] [IsAlgClosed L] :
    DenseRange fun x : separableClosure K' L ↦ ((x : L) : UniformSpace.Completion L) :=
  UniformSpace.Completion.denseRange_coe.comp
    (dense_separableClosure K' L).denseRange_subtypeVal (UniformSpace.Completion.continuous_coe _)

namespace CompletedAlgClosure

variable (K : Type u) [NontriviallyNormedField K] [CompleteSpace K] [IsUltrametricDist K]

/-- The norm of `C` is nontrivial, since it extends the norm of `K`. -/
instance instNontriviallyNormedField : NontriviallyNormedField (CompletedAlgClosure K) where
  non_trivial := by
    obtain ⟨x, hx⟩ := NontriviallyNormedField.non_trivial (α := K)
    exact ⟨algebraMap K _ x, by rwa [norm_algebraMap']⟩

/-- The norm of `C` is ultrametric. -/
instance instIsUltrametricDist : IsUltrametricDist (CompletedAlgClosure K) :=
  IsUltrametricDist.of_normedAlgebra K

/-- **`K^sep` is dense in `C`**. -/
theorem denseRange_separableClosure :
    DenseRange fun x : separableClosure K (SpectralAlgClosure K) ↦
      ((x : SpectralAlgClosure K) : CompletedAlgClosure K) :=
  denseRange_separableClosure_completion K (SpectralAlgClosure K)

end CompletedAlgClosure

end TauCeti
