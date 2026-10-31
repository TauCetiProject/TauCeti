/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.DedekindDomain.SInteger.Spectrum

/-!
# Primitive tuples of `S`-integers

Let `R` be a Dedekind domain with fraction field `K` and `S` a set of height one primes of `R`.
A tuple `x : ι → K` is **`S`-primitive** (`Set.IsPrimitive`) when its coordinates are `S`-integers
which generate the unit ideal of the ring `𝒪_S = S.integer K`. These are the normalised
representatives of the points of projective space over `K` with respect to `S`: when `𝒪_S` is a
principal ideal domain every nonzero finite tuple has an `S`-primitive scalar multiple
(`Set.exists_isPrimitive_smul`), and for a number field the height of an `S`-primitive tuple is
the product of its local sup norms over the infinite places and the places of `S`.

Primitivity is a local condition away from `S`
(`Set.isPrimitive_iff_forall_exists_valuation_eq_one`): a nonzero tuple of `S`-integers is
`S`-primitive exactly when, at every prime `v ∉ S`, some coordinate is a `v`-adic unit. Both
directions go through the primes of `𝒪_S`, which are the primes of `R` outside `S`
(`IsDedekindDomain.integerHeightOneSpectrumEquiv`), with the same valuations.

## Main definitions

* `Set.IsPrimitive S x`: the coordinates of `x` are `S`-integers and `1` is an `𝒪_S`-linear
  combination of them.

## Main results

* `Set.isPrimitive_coe_iff_span_eq_top`: a tuple of elements of `𝒪_S` is `S`-primitive exactly
  when its coordinates generate the unit ideal of `𝒪_S`; `Set.isPrimitive_iff_span_eq_top` is the
  same for a tuple of `K`.
* `Set.isPrimitive_iff_exists_sum_mul_eq_one`: the same with the linear combination written out.
* `Set.IsPrimitive.unit_smul` and `Set.isPrimitive_unit_smul_iff`: `S`-primitivity is invariant
  under scaling by an `S`-unit.
* `Set.IsPrimitive.exists_valuation_eq_one` and
  `Set.isPrimitive_iff_forall_exists_valuation_eq_one`: the local characterisation.
* `Set.exists_isPrimitive_smul`: over a principal `𝒪_S`, every nonzero finite tuple has an
  `S`-primitive scalar multiple.

## References

* E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press, 2006,
  §1.5.10 and the proof of Theorem 7.2.6, where points are normalised to be `S`-primitive.

The definition and the construction of the primitive multiple follow Ralf Stephan's
`DiophantineApproximation/SAdicHeight.lean` in `rwst/Subspace-Theorems` at
`09835cb23557ae5ae0cf55a9c4ab9055f5d60338` (Apache 2.0), generalised from rings of integers of
number fields to Dedekind domains.
-/

public section

open IsDedekindDomain
open scoped nonZeroDivisors

namespace Set

variable {R : Type*} [CommRing R] [IsDedekindDomain R] {K : Type*} [Field K] [Algebra R K]
  [IsFractionRing R K] {ι : Type*}

/-- **An `S`-primitive tuple**: its coordinates are `S`-integers and generate the unit ideal of
the ring of `S`-integers, that is, `1` is a linear combination of them with `S`-integral
coefficients. -/
def IsPrimitive (S : Set (HeightOneSpectrum R)) (x : ι → K) : Prop :=
  (∀ i, x i ∈ S.integer K) ∧ (1 : K) ∈ Submodule.span (S.integer K) (range x)

variable {S : Set (HeightOneSpectrum R)} {x : ι → K}

/-- The coordinates of an `S`-primitive tuple are `S`-integers. -/
theorem IsPrimitive.mem_integer (h : S.IsPrimitive x) (i : ι) : x i ∈ S.integer K :=
  h.1 i

/-- **A tuple of `S`-integers is `S`-primitive exactly when its coordinates generate the unit
ideal of the ring of `S`-integers.** -/
theorem isPrimitive_coe_iff_span_eq_top (a : ι → S.integer K) :
    S.IsPrimitive (fun i ↦ (a i : K)) ↔ Ideal.span (range a) = ⊤ := by
  have hrange : (range fun i ↦ (a i : K)) = Algebra.linearMap (S.integer K) K '' range a := by
    rw [← range_comp]
    simp [Function.comp_def]
  rw [IsPrimitive, hrange, ← Submodule.map_span, Ideal.eq_top_iff_one, Submodule.mem_map]
  refine ⟨fun ⟨_, b, hb, hb1⟩ ↦ ?_, fun h ↦ ⟨fun i ↦ (a i).2, 1, h, by simp⟩⟩
  have hb1' : b = 1 := Subtype.ext (by simpa using hb1)
  rwa [hb1'] at hb

/-- The ideal form of `Set.IsPrimitive` for a tuple of `K`. -/
theorem isPrimitive_iff_span_eq_top :
    S.IsPrimitive x ↔ ∃ h : ∀ i, x i ∈ S.integer K,
      Ideal.span (range fun i ↦ (⟨x i, h i⟩ : S.integer K)) = ⊤ :=
  ⟨fun hx ↦ ⟨hx.1, (isPrimitive_coe_iff_span_eq_top fun i ↦ ⟨x i, hx.1 i⟩).mp hx⟩,
    fun ⟨h, hspan⟩ ↦ (isPrimitive_coe_iff_span_eq_top fun i ↦ ⟨x i, h i⟩).mpr hspan⟩

/-- `Set.IsPrimitive` for a finite tuple, with the linear combination written out. -/
theorem isPrimitive_iff_exists_sum_mul_eq_one [Fintype ι] :
    S.IsPrimitive x ↔ (∀ i, x i ∈ S.integer K) ∧
      ∃ c : ι → K, (∀ i, c i ∈ S.integer K) ∧ ∑ i, c i * x i = 1 := by
  refine and_congr_right fun _ ↦ ?_
  rw [Submodule.mem_span_range_iff_exists_fun]
  refine ⟨fun ⟨c, hc⟩ ↦ ⟨fun i ↦ c i, fun i ↦ (c i).2, by simpa [Algebra.smul_def] using hc⟩,
    fun ⟨c, hcS, hc⟩ ↦ ⟨fun i ↦ ⟨c i, hcS i⟩, by simpa [Algebra.smul_def] using hc⟩⟩

/-- **Scaling by an `S`-unit preserves `S`-primitivity**: an `S`-unit is a unit of the ring of
`S`-integers, so it keeps the coordinates `S`-integral and the ideal they generate unchanged. -/
theorem IsPrimitive.unit_smul (h : S.IsPrimitive x) (u : S.unit K) :
    S.IsPrimitive (((u : Kˣ) : K) • x) := by
  let w := unitEquivUnitsInteger S K u
  have hw : ((u : Kˣ) : K) • x = fun i ↦ (w : S.integer K) • x i := by
    funext i
    rw [Pi.smul_apply, Subalgebra.smul_def, val_unitEquivUnitsInteger_apply_coe]
  refine ⟨fun i ↦ mul_mem (w : S.integer K).2 (h.1 i), ?_⟩
  rw [hw, ← smul_set_range, Submodule.span_smul_eq_of_isUnit _ _ w.isUnit]
  exact h.2

/-- **`S`-primitivity is invariant under scaling by an `S`-unit.** -/
@[simp]
theorem isPrimitive_unit_smul_iff (u : S.unit K) :
    S.IsPrimitive (((u : Kˣ) : K) • x) ↔ S.IsPrimitive x :=
  ⟨fun h ↦ by simpa [smul_smul] using h.unit_smul u⁻¹, fun h ↦ h.unit_smul u⟩

/-- An `S`-primitive tuple is nonzero. -/
theorem IsPrimitive.ne_zero (h : S.IsPrimitive x) : x ≠ 0 := by
  rintro rfl
  have hle : Submodule.span (S.integer K) (range (0 : ι → K)) ≤ ⊥ :=
    Submodule.span_le.mpr (by rintro _ ⟨i, rfl⟩; simp)
  simpa using hle h.2

/-- **An `S`-primitive tuple has a `v`-adic unit among its coordinates at every prime `v ∉ S`**:
otherwise every coordinate lies in the prime of `𝒪_S` above `v`, and so does `1`. -/
theorem IsPrimitive.exists_valuation_eq_one (h : S.IsPrimitive x) {v : HeightOneSpectrum R}
    (hv : v ∉ S) : ∃ i, v.valuation K (x i) = 1 := by
  obtain ⟨hint, hspan⟩ := isPrimitive_iff_span_eq_top.mp h
  by_contra! hne
  let P := integerPrimeOverOfNotMem K S hv
  refine P.isPrime.ne_top (top_le_iff.mp (hspan ▸ Ideal.span_le.mpr ?_))
  rintro _ ⟨i, rfl⟩
  by_contra hi
  have hval := (P.valuation_eq_one_iff_notMem (K := K)).mpr hi
  rw [valuation_integerPrimeOverOfNotMem] at hval
  exact hne i hval

/-- **Primitivity is local away from `S`**: a nonzero tuple is `S`-primitive exactly when its
coordinates are `S`-integers and, at every prime `v ∉ S`, one of them is a `v`-adic unit. The
hypothesis `x ≠ 0` is needed when every prime lies in `S`: then the right-hand side holds for the
zero tuple. -/
theorem isPrimitive_iff_forall_exists_valuation_eq_one (hx : x ≠ 0) :
    S.IsPrimitive x ↔
      (∀ i, x i ∈ S.integer K) ∧ ∀ v ∉ S, ∃ i, v.valuation K (x i) = 1 := by
  refine ⟨fun h ↦ ⟨h.1, fun v hv ↦ h.exists_valuation_eq_one hv⟩, fun ⟨hint, h⟩ ↦ ?_⟩
  refine isPrimitive_iff_span_eq_top.mpr ⟨hint, ?_⟩
  -- A proper ideal generated by the coordinates lies in a maximal ideal `M` of `𝒪_S`, which is
  -- nonzero because some coordinate is; the prime of `R` under `M` is outside `S`, and there
  -- every coordinate has valuation `< 1`.
  by_contra hI
  obtain ⟨M, hM, hIM⟩ := Ideal.exists_le_maximal _ hI
  obtain ⟨i₀, hi₀⟩ := Function.ne_iff.mp hx
  have hM0 : M ≠ ⊥ := by
    rintro rfl
    exact hi₀ (congrArg Subtype.val ((Ideal.mem_bot).mp (hIM (Ideal.subset_span ⟨i₀, rfl⟩))))
  let P : HeightOneSpectrum (S.integer K) := ⟨M, hM.isPrime, hM0⟩
  obtain ⟨i, hi⟩ := h _ (integerPrimeUnder_notMem K S P)
  rw [← valuation_integerPrimeUnder] at hi
  exact (P.valuation_eq_one_iff_notMem (r := ⟨x i, hint i⟩)).mp hi
    (hIM (Ideal.subset_span ⟨i, rfl⟩))

/-- **Over a principal ring of `S`-integers every nonzero finite tuple has an `S`-primitive scalar
multiple.** Clear denominators, and divide by a generator of the ideal of `𝒪_S` that the
coordinates generate. -/
theorem exists_isPrimitive_smul [Finite ι] [IsPrincipalIdealRing (S.integer K)] (hx : x ≠ 0) :
    ∃ c : K, c ≠ 0 ∧ S.IsPrimitive (c • x) := by
  classical
  have := Fintype.ofFinite ι
  -- `y = b • x` has coordinates in `𝒪_S`
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples (S.integer K)⁰ Finset.univ x
  choose y hy using fun i ↦ hb i (Finset.mem_univ i)
  have hy' : ∀ i, (y i : K) = b * x i := fun i ↦ by simpa [Algebra.smul_def] using hy i
  have hb0 : (b : K) ≠ 0 := by
    simp
  -- the ideal the coordinates of `y` generate is principal, `= (g)`, with `y = a * g`
  obtain ⟨g, hg⟩ := Submodule.IsPrincipal.principal (Ideal.span (range y))
  have hgy : ∀ i, y i ∈ Ideal.span {g} := fun i ↦ by
    rw [← Ideal.submodule_span_eq, ← hg]
    exact Ideal.subset_span ⟨i, rfl⟩
  choose a ha using fun i ↦ Ideal.mem_span_singleton'.mp (hgy i)
  have hg0 : g ≠ 0 := by
    rintro rfl
    obtain ⟨i₀, hi₀⟩ := Function.ne_iff.mp hx
    have h0 := hy' i₀
    have hy0 : y i₀ = 0 := by simpa using hgy i₀
    rw [hy0] at h0
    exact hi₀ ((mul_eq_zero.mp (by exact_mod_cast h0.symm)).resolve_left hb0)
  have hgK : (g : K) ≠ 0 := by simpa using hg0
  -- `g⁻¹ • y = a`, and `1` is a combination of the `a i` because `g` is one of the `y i`
  have hcx : ((g : K)⁻¹ * b) • x = fun i ↦ (a i : K) := by
    funext i
    have hyi : (y i : K) = a i * g := by rw [← ha i, MulMemClass.coe_mul]
    rw [Pi.smul_apply, smul_eq_mul, mul_assoc, ← hy' i, hyi]
    field_simp
  refine ⟨(g : K)⁻¹ * b, mul_ne_zero (inv_ne_zero hgK) hb0, ?_⟩
  rw [hcx, isPrimitive_coe_iff_span_eq_top, Ideal.eq_top_iff_one]
  have hgmem : g ∈ Ideal.span (range y) := by
    rw [hg]
    exact Submodule.mem_span_singleton_self g
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun (S.integer K)).mp hgmem
  have hsum : (∑ i, c i * a i) * g = 1 * g := by
    rw [Finset.sum_mul, one_mul]
    conv_rhs => rw [← hc]
    exact Finset.sum_congr rfl fun i _ ↦ by rw [smul_eq_mul, ← ha i, mul_assoc]
  rw [← mul_right_cancel₀ hg0 hsum]
  exact Ideal.sum_mem _ fun i _ ↦ Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i, rfl⟩)

/-- A tuple of `S`-integers with a coordinate equal to `1` is `S`-primitive: the affine points
`(1, x₁, …, xₙ)` with `S`-integral `xᵢ` are `S`-primitive. -/
example (hx : ∀ i, x i ∈ S.integer K) {i₀ : ι} (h : x i₀ = 1) : S.IsPrimitive x :=
  ⟨hx, h ▸ Submodule.subset_span ⟨i₀, rfl⟩⟩

end Set
