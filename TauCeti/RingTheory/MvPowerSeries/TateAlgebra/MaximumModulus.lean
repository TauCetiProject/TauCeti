/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.Eval
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

import Mathlib.Analysis.Normed.Unbundled.SpectralNorm
import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots
import Mathlib.Topology.Algebra.Module.FiniteDimension
import TauCeti.Analysis.Normed.Group.NullFamily
import TauCeti.Analysis.Normed.Ring.Ultra
import TauCeti.Data.Nat.ModEq
import TauCeti.RingTheory.RootsOfUnity.Basic

/-!
# Maximum modulus for Tate algebras at roots of unity and at finite-extension points

Let `f = ∑ₜ fₜ Xᵗ` be a restricted power series in `k` variables at unit polyradius over an
ultrametric normed ring `R`, and let `φ : R → S` be an isometric ring homomorphism into a complete
ultrametric normed field. Suppose that `S` contains a primitive `m`-th root of unity `ζ`, where
`‖m‖ = 1` in `S` and `m` exceeds every exponent of every coefficient `fₜ` with `‖fₜ‖ = ‖f‖`.
Then `f` attains its Gauss norm at a point of `S ^ k` whose coordinates are powers of `ζ`.

The proof is discrete Fourier inversion. Let `t₀` be an exponent with `‖fₜ₀‖ = ‖f‖`. Averaging
the values `f(ζʲ)` against the characters `ζ^(-⟨j, t₀⟩)` over `j ∈ (ℤ ⧸ m) ^ k` gives
`m ^ k ∑_{t ≡ t₀} φ(fₜ)`, the sum over the exponents congruent to `t₀` modulo `m`. By the choice of
`m` the term at `t₀` is the only one of norm `‖f‖`, so this sum has norm `‖f‖`, and since
`‖m‖ = 1` the ultrametric inequality forces `‖f(ζʲ)‖ ≥ ‖f‖` for some `j`. The reverse inequality
holds at every point of the closed unit polydisc.

The condition `‖m‖ = 1` excludes multiples of the residue characteristic, so that the reductions of
the `m`-th roots of unity are distinct. Points with coordinates in `R` do not suffice in general:
over `ℚ_p` the polynomial `X ^ p - X` has Gauss norm one but takes values of norm at most `p⁻¹` on
`ℤ_p`.

Over a complete nontrivially normed ultrametric field `K`, the cyclotomic field `K(μₘ)` is a
finite extension of `K` and carries the spectral norm, so every `f ∈ Tₙ = K⟨X₁, …, Xₙ⟩` attains
its Gauss norm at a point of the closed unit polydisc of a finite normed field extension of `K`.
As no such point gives a value of norm above the Gauss norm, the Gauss norm is the largest of the
values `‖f(x)‖` over all finite normed field extensions `L / K` and all `x ∈ (L°)ⁿ`. Evaluation at
any point over an algebraic extension has a field as image, so its kernel is a maximal ideal
(`AlgHom.ker_isMaximal_of_isAlgebraic`); and a nonzero `f` does not vanish at some
finite-extension point. These statements read the maximum principle as evaluation at points,
without passing through maximal ideals of `Tₙ` or through the affinoid Nullstellensatz.

## Main results

* `MvPowerSeries.exists_norm_restrictedEval₂_eq_norm`: a restricted series attains its Gauss norm
  at a point whose coordinates are `m`-th roots of unity.
* `MvPowerSeries.exists_finiteDimensional_norm_restrictedEval₂_eq_norm`: a Tate series attains its
  Gauss norm at a point of the closed unit polydisc over a finite normed field extension of `K`.
* `MvPowerSeries.isGreatest_norm_restrictedEval₂`: the Gauss norm of a Tate series is the greatest
  of its absolute values at such points.
* `MvPowerSeries.exists_finiteDimensional_restrictedEval₂_ne_zero`: finite-extension points
  separate the elements of a Tate algebra.

## References

* [Bosch, Güntzer, Remmert, *Non-Archimedean Analysis*][bosch-guntzer-remmert], §5.1.4.
-/

public section

namespace MvPowerSeries

variable {k : ℕ} {R S : Type*} [NormedCommRing R] [IsUltrametricDist R]
  [NormedField S] [IsUltrametricDist S] [CompleteSpace S] (φ : R →+* S)

/-- **Discrete Fourier inversion for restricted series.** Averaging the values `f(ζʲ)` against
the character `j ↦ ζ ^ (-⟨j, t₀⟩)` over `j ∈ {0, …, m - 1} ^ k` is the sum of `m ^ k φ(fₜ)` over
the exponents `t ≡ t₀` modulo `m`. -/
private theorem hasSum_sum_mul_restrictedEval₂ (hφ : ∀ r, ‖φ r‖ ≤ ‖r‖) {m : ℕ} {ζ : S}
    (hζ : IsPrimitiveRoot ζ m) (hx : ∀ (j : Fin k → Fin m) i, ‖ζ ^ (j i : ℕ)‖ ≤ 1)
    (f : IsRestricted.subring (R := R) (fun _ : Fin k ↦ 1)) (t₀ : Fin k →₀ ℕ) :
    HasSum (fun t ↦ φ (coeff t (f : MvPowerSeries (Fin k) R)) *
        ∏ i, if m ∣ (m - 1) * t₀ i + t i then (m : S) else 0)
      (∑ j : Fin k → Fin m, (∏ i, ζ ^ ((j i : ℕ) * ((m - 1) * t₀ i))) *
        restrictedEval₂ φ (fun i ↦ ζ ^ (j i : ℕ)) hφ (hx j) f) := by
  convert hasSum_sum fun j (_ : j ∈ Finset.univ) ↦
    (hasSum_restrictedEval₂ φ _ hφ (hx j) f).mul_left
      (∏ i, ζ ^ ((j i : ℕ) * ((m - 1) * t₀ i))) using 1
  funext t
  simp only [TauCeti.Huber.weightedEvalTerm_def]
  -- Orthogonality of characters, after merging the character with the monomial.
  rw [← hζ.sum_prod_pow_pow_eq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [mul_left_comm, ← Finset.prod_mul_distrib]
  congr 1
  refine Finset.prod_congr rfl fun i _ ↦ ?_
  ring

omit [IsUltrametricDist S] [CompleteSpace S] in
/-- A coefficient of a restricted series at an exponent other than a dominant one `t₀`, multiplied
by the congruence factor `∏ i, if m ∣ (m - 1) * t₀ i + t i then m else 0` of the Fourier average,
has norm strictly below `‖f‖`, provided that all dominant exponents are bounded by `m`. -/
private theorem norm_coeff_mul_prod_lt (hφ : ∀ r, ‖φ r‖ = ‖r‖) {m : ℕ} (hm : ‖(m : S)‖ = 1)
    (f : IsRestricted.subring (R := R) (fun _ : Fin k ↦ 1))
    (hfm : ∀ t, ‖coeff t (f : MvPowerSeries (Fin k) R)‖ = ‖f‖ → ∀ i, t i < m) (hf : f ≠ 0)
    {t₀ t : Fin k →₀ ℕ}
    (ht₀ : ‖coeff t₀ (f : MvPowerSeries (Fin k) R)‖ = ‖f‖) (ht : t ≠ t₀) :
    ‖φ (coeff t (f : MvPowerSeries (Fin k) R)) *
      ∏ i, if m ∣ (m - 1) * t₀ i + t i then (m : S) else 0‖ < ‖f‖ := by
  rcases (norm_coeff_le_norm f t).lt_or_eq with hlt | heq
  · -- Each factor of the product has norm at most one.
    refine lt_of_le_of_lt ?_ hlt
    rw [norm_mul, hφ, norm_prod]
    refine mul_le_of_le_one_right (norm_nonneg _) <|
      Finset.prod_le_one₀ (fun _ _ ↦ norm_nonneg _) fun i _ ↦ ?_
    split_ifs <;> simp [hm]
  -- A second dominant exponent is not congruent to `t₀`, so its term vanishes.
  obtain ⟨i, hi⟩ : ∃ i, t i ≠ t₀ i := by
    by_contra! h
    exact ht (Finsupp.ext h)
  have hzero : (∏ i, if m ∣ (m - 1) * t₀ i + t i then (m : S) else 0) = 0 := by
    refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
    rw [ite_eq_right_iff]
    exact fun h ↦ absurd (Nat.eq_of_dvd_sub_one_mul_add (hfm t₀ ht₀ i) (hfm t heq i) h) hi
  simpa [hzero] using hf

/-- **Maximum modulus at roots of unity.** Let `φ : R → S` be an isometric ring homomorphism into
a complete ultrametric normed field containing a primitive `m`-th root of unity `ζ`, where
`‖m‖ = 1` in `S` and `m` exceeds every exponent of every coefficient of `f` of norm `‖f‖`. Then
there is a point `x` of the closed unit polydisc of `S ^ k`, with coordinates powers of `ζ`, at
which `‖f(x)‖ = ‖f‖`. -/
theorem exists_norm_restrictedEval₂_eq_norm (hφ : ∀ r, ‖φ r‖ = ‖r‖) {m : ℕ} {ζ : S}
    (hζ : IsPrimitiveRoot ζ m) (hm : ‖(m : S)‖ = 1)
    (f : IsRestricted.subring (R := R) (fun _ : Fin k ↦ 1))
    (hfm : ∀ t, ‖coeff t (f : MvPowerSeries (Fin k) R)‖ = ‖f‖ → ∀ i, t i < m) :
    ∃ (x : Fin k → S) (hx : ∀ i, ‖x i‖ ≤ 1), (∀ i, ∃ a < m, x i = ζ ^ a) ∧
      ‖restrictedEval₂ φ x (fun r ↦ (hφ r).le) hx f‖ = ‖f‖ := by
  classical
  have hm0 : m ≠ 0 := by
    rintro rfl
    simp at hm
  have hζ1 : ‖ζ‖ = 1 :=
    (pow_eq_one_iff_of_nonneg (norm_nonneg ζ) hm0).mp
      (by rw [← norm_pow, hζ.pow_eq_one, norm_one])
  have hζa (a : ℕ) : ‖ζ ^ a‖ = 1 := by rw [norm_pow, hζ1, one_pow]
  -- The point `ζʲ` attached to `j ∈ {0, …, m - 1} ^ k`.
  let x (j : Fin k → Fin m) : Fin k → S := fun i ↦ ζ ^ (j i : ℕ)
  have hx (j : Fin k → Fin m) (i : Fin k) : ‖x j i‖ ≤ 1 := (hζa _).le
  let ev (j : Fin k → Fin m) := restrictedEval₂ φ (x j) (fun r ↦ (hφ r).le) (hx j) f
  suffices H : ∃ j, ‖f‖ ≤ ‖ev j‖ by
    obtain ⟨j, hj⟩ := H
    exact ⟨x j, hx j, fun i ↦ ⟨j i, (j i).isLt, rfl⟩,
      le_antisymm (norm_restrictedEval₂_le _ _ _ _ f) hj⟩
  rcases eq_or_ne f 0 with rfl | hf
  · have : Nonempty (Fin k → Fin m) := ⟨fun _ ↦ ⟨0, Nat.pos_of_ne_zero hm0⟩⟩
    exact ⟨Classical.arbitrary _, by simp⟩
  -- A dominant exponent `t₀`.
  obtain ⟨t₀, ht₀⟩ := exists_norm_coeff_eq_norm f
  -- The character `j ↦ ζ ^ (-⟨j, t₀⟩)`, written with natural exponents.
  let w (j : Fin k → Fin m) : S := ∏ i, ζ ^ ((j i : ℕ) * ((m - 1) * t₀ i))
  have hw (j : Fin k → Fin m) : ‖w j‖ = 1 := by
    simp only [w, norm_prod, hζa, Finset.prod_const_one]
  -- Averaging the values `f(ζʲ)` against the character isolates the coefficients at the exponents
  -- congruent to `t₀` modulo `m`; among them only `t₀` has norm `‖f‖`.
  let g (t : Fin k →₀ ℕ) : S := φ (coeff t (f : MvPowerSeries (Fin k) R)) *
    ∏ i, if m ∣ (m - 1) * t₀ i + t i then (m : S) else 0
  have hsum : HasSum g (∑ j, w j * ev j) := hasSum_sum_mul_restrictedEval₂ φ _ hζ hx f t₀
  have hgt₀ : ‖g t₀‖ = ‖f‖ := by
    have hdvd (i : Fin k) : m ∣ (m - 1) * t₀ i + t₀ i :=
      ⟨t₀ i, by rw [← add_one_mul, Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hm0)]⟩
    simp [g, hdvd, hφ, hm, ht₀]
  have hg (t : Fin k →₀ ℕ) (ht : t ≠ t₀) : ‖g t‖ < ‖g t₀‖ := by
    rw [hgt₀]
    exact norm_coeff_mul_prod_lt φ hφ hm f hfm hf ht₀ ht
  have htotal : ‖∑ j, w j * ev j‖ = ‖f‖ := (hsum.norm_eq_of_forall_norm_lt t₀ hg).trans hgt₀
  -- Some term of the average has norm at least `‖f‖`.
  have : Nonempty (Fin k → Fin m) := ⟨fun _ ↦ ⟨0, Nat.pos_of_ne_zero hm0⟩⟩
  obtain ⟨j, -, hj⟩ := IsUltrametricDist.exists_norm_finsetSum_le Finset.univ
    fun j ↦ w j * ev j
  refine ⟨j, ?_⟩
  rwa [htotal, norm_mul, hw, one_mul] at hj

section FiniteExtension

universe u

variable {K : Type u} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] {n : ℕ}

local notation "T" => IsRestricted.subring (R := K) (fun _ : Fin n ↦ 1)

/-- **Maximum principle at finite-extension points.** Every `f ∈ K⟨X₁, …, Xₙ⟩` attains its Gauss
norm at a point of the closed unit polydisc over a finite normed field extension of `K`: there are
a finite extension `L / K`, with a norm extending that of `K`, and `x ∈ Lⁿ` with every `‖x i‖ ≤ 1`
and `‖f(x)‖ = ‖f‖`. -/
theorem exists_finiteDimensional_norm_restrictedEval₂_eq_norm (f : T) :
    ∃ (L : Type u) (_ : NormedField L) (_ : IsUltrametricDist L) (_ : CompleteSpace L)
      (_ : NormedAlgebra K L) (_ : FiniteDimensional K L) (x : Fin n → L)
      (hx : ∀ i, ‖x i‖ ≤ 1),
      ‖restrictedEval₂ (algebraMap K L) x (fun r ↦ (norm_algebraMap' L r).le) hx f‖ = ‖f‖ := by
  classical
  rcases eq_or_ne f 0 with rfl | hf
  · exact ⟨K, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, 0,
      fun _ ↦ by simp, by simp⟩
  -- Choose `m` of norm one exceeding every exponent of every coefficient of norm `‖f‖`; there are
  -- finitely many such coefficients since `f` is restricted and nonzero.
  have hD : {t : Fin n →₀ ℕ | ‖coeff t (f : MvPowerSeries (Fin n) K)‖ = ‖f‖}.Finite :=
    (f.property.finite_setOfPred_achievesGaussNorm (by simpa using hf)).subset fun t ht ↦ by
      simpa [AchievesGaussNorm, norm_eq_gaussNorm] using ht
  obtain ⟨m, hNm, hm⟩ := IsUltrametricDist.exists_lt_norm_natCast_eq_one K
    (hD.toFinset.sup Finsupp.degree)
  have hfm (t : Fin n →₀ ℕ) (ht : ‖coeff t (f : MvPowerSeries (Fin n) K)‖ = ‖f‖) (i : Fin n) :
      t i < m :=
    (Finsupp.le_degree i t).trans_lt ((Finset.le_sup (hD.mem_toFinset.mpr ht)).trans_lt hNm)
  -- Evaluate at roots of unity in the cyclotomic extension `E = K(μₘ)` with its spectral norm.
  have : NeZero (m : K) := ⟨fun h ↦ by simp [h] at hm⟩
  have : NeZero m := ⟨fun h ↦ by simp [h] at hm⟩
  let E := CyclotomicField m K
  have : FiniteDimensional K E := IsCyclotomicExtension.finiteDimensional {m} K E
  let : NormedField E := spectralNorm.normedField K E
  let : NormedAlgebra K E := spectralNorm.normedAlgebra K E
  have : IsUltrametricDist E :=
    IsUltrametricDist.isUltrametricDist_of_isNonarchimedean_norm fun a b ↦
      isNonarchimedean_spectralNorm (K := K) (L := E) a b
  have : CompleteSpace E := FiniteDimensional.completeSpace K E
  have hφ (r : K) : ‖algebraMap K E r‖ = ‖r‖ := norm_algebraMap' E r
  have hmE : ‖(m : E)‖ = 1 := by rw [← map_natCast (algebraMap K E), hφ, hm]
  obtain ⟨x, hx, -, hfx⟩ := exists_norm_restrictedEval₂_eq_norm (algebraMap K E) hφ
    (IsCyclotomicExtension.zeta_spec m K E) hmE f hfm
  exact ⟨E, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, x, hx, hfx⟩

/-- **The Gauss norm as a maximum over finite-extension points.** The Gauss norm of
`f ∈ K⟨X₁, …, Xₙ⟩` is the greatest of the values `‖f(x)‖`, over all finite normed field
extensions `L / K` and all `x ∈ Lⁿ` with every `‖x i‖ ≤ 1`. -/
theorem isGreatest_norm_restrictedEval₂ (f : T) :
    IsGreatest {a : ℝ | ∃ (L : Type u) (_ : NormedField L) (_ : IsUltrametricDist L)
      (_ : CompleteSpace L) (_ : NormedAlgebra K L) (_ : FiniteDimensional K L) (x : Fin n → L)
      (hx : ∀ i, ‖x i‖ ≤ 1),
      ‖restrictedEval₂ (algebraMap K L) x (fun r ↦ (norm_algebraMap' L r).le) hx f‖ = a} ‖f‖ :=
  ⟨exists_finiteDimensional_norm_restrictedEval₂_eq_norm f, by
    rintro _ ⟨L, _, _, _, _, _, x, hx, rfl⟩
    exact norm_restrictedEval₂_le _ _ _ _ f⟩

/-- **Finite-extension points separate the elements of a Tate algebra.** A nonzero
`f ∈ K⟨X₁, …, Xₙ⟩` does not vanish at some point of the closed unit polydisc over a finite normed
field extension of `K`. The kernel of evaluation at such a point is a maximal ideal
(`AlgHom.ker_isMaximal_of_isAlgebraic`). -/
theorem exists_finiteDimensional_restrictedEval₂_ne_zero {f : T} (hf : f ≠ 0) :
    ∃ (L : Type u) (_ : NormedField L) (_ : IsUltrametricDist L) (_ : CompleteSpace L)
      (_ : NormedAlgebra K L) (_ : FiniteDimensional K L) (x : Fin n → L)
      (hx : ∀ i, ‖x i‖ ≤ 1),
      restrictedEval₂ (algebraMap K L) x (fun r ↦ (norm_algebraMap' L r).le) hx f ≠ 0 := by
  obtain ⟨L, _, _, _, _, _, x, hx, hfx⟩ :=
    exists_finiteDimensional_norm_restrictedEval₂_eq_norm f
  exact ⟨L, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, x, hx,
    norm_ne_zero_iff.mp (hfx ▸ norm_ne_zero_iff.mpr hf)⟩

end FiniteExtension

end MvPowerSeries
