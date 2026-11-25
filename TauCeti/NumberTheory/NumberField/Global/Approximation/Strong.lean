/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.Global.Approximation.SInteger
public import TauCeti.NumberTheory.NumberField.Global.Approximation.Weak
public import TauCeti.NumberTheory.NumberField.Global.Places.Basic
import Mathlib.NumberTheory.NumberField.ClassNumber
import TauCeti.NumberTheory.NumberField.CanonicalEmbedding.SmallInteger
import TauCeti.NumberTheory.NumberField.FinitePlace.Basic
import TauCeti.NumberTheory.NumberField.InfinitePlace.Completion.Basic
import TauCeti.RingTheory.DedekindDomain.SInteger.Localization

/-!
# Strong approximation away from one place

Let `K` be a number field and `w` a place of `K`, finite or infinite. The diagonal copy of `K`
is dense in the restricted product of the completions `K_v` over the places `v ≠ w`, taken with
respect to the rings of integers `𝒪_v` at the finite places. In finite terms: given nonempty open
sets in `K_v` at finitely many places `v ≠ w`, some `x ∈ K` lies in each of them and is integral
at every other finite place `v ≠ w`
(`TauCeti.GlobalNumberFields.exists_forall_algebraMap_mem_and_forall_norm_le_one`). This is the
input from which Moret-Bailly's integral-point theorem gets its approximation step, through the
corresponding statement for torsors under finite projective modules.

Some place must be omitted: for `K = ℚ`, the open interval `(1/4, 3/4)` at the real place
together with integrality at every prime would ask for an integer in that interval. For `K = ℚ`
and `w` the real place the statement is the density of `ℚ` in the finite adeles; for `K = ℚ` and
`w = 2`, elements of `ℤ[1/2]` approximate any real number.

The proof scales the `S`-integer approximation `NumberField.exists_forall_apply_add_le`, which
loses a factor `A` depending only on `K` at the infinite places, by an element `β ∈ K` that is
small at every infinite place other than `w` and at finitely many prescribed finite places, and
integral at every finite place other than `w`
(`TauCeti.GlobalNumberFields.exists_ne_zero_forall_norm_le_one_and_lt`).
* If `w` is infinite, `β` is a nonzero algebraic integer, small at finitely many finite places,
  multiplied by an algebraic integer whose size Minkowski's theorem concentrates at `w`
  (`TauCeti.NumberField.exists_ne_zero_forall_infinitePlace_mul_le`).
* If `w` is finite, the class group is finite, so some nonzero algebraic integer `π` lies in the
  prime of `w` and in no other prime (`IsDedekindDomain.exists_mem_submonoid_mem_asIdeal`). As
  `π` is not a unit, `∏_u |π|_u ^ mult u > 1` over the infinite places `u`
  (`TauCeti.GlobalNumberFields.one_lt_prod_infinitePlace_pow_mult`), so for large `m`
  Minkowski's theorem gives a nonzero algebraic integer `a` with `|a|_u` smaller than `|π|_u ^ m`
  by any prescribed factor, and `β` is a multiple of `a / π ^ m`.

## Main results

* `TauCeti.GlobalNumberFields.exists_ne_zero_forall_norm_le_one_and_lt`: a nonzero element of `K`
  integral at every finite place other than `w` and as small as prescribed at every infinite
  place other than `w` and at finitely many finite places other than `w`.
* `TauCeti.GlobalNumberFields.exists_forall_algebraMap_mem_and_forall_norm_le_one`: additive
  strong approximation away from `w`.

## References

* J. W. S. Cassels and A. Fröhlich, eds., *Algebraic Number Theory*, Chapter II, §15.
* L. Moret-Bailly, *Groupes de Picard et problèmes de Skolem II*, Ann. Sci. ÉNS 22 (1989),
  proof of Lemme 3.8.
-/

public section

open IsDedekindDomain NumberField NumberField.InfinitePlace
open scoped NumberField

namespace TauCeti.GlobalNumberFields

variable {K : Type*} [Field K] [NumberField K]

/-- The case `S = ∅` of `exists_ne_zero_forall_norm_le_one_and_lt` at a finite place `v₀`: some
nonzero `γ ∈ K` is integral at every finite place other than `v₀` and smaller than `δ` at every
infinite place. -/
private theorem exists_ne_zero_forall_apply_le_one_and_lt_of_finite
    (v₀ : HeightOneSpectrum (𝓞 K)) {δ : ℝ} (hδ : 0 < δ) :
    ∃ γ : K, γ ≠ 0 ∧ (∀ v : HeightOneSpectrum (𝓞 K), v ≠ v₀ → FinitePlace.mk v γ ≤ 1) ∧
      ∀ u : InfinitePlace K, u γ < δ := by
  -- An algebraic integer `π` whose only prime factor is `v₀`, which exists since the class group
  -- is finite.
  have : Fact (IsMulTorsion (ClassGroup (𝓞 K))) := ⟨isMulTorsion_of_finite⟩
  obtain ⟨π, hπmem, hπv₀⟩ := exists_mem_submonoid_mem_asIdeal {v₀} (Set.mem_singleton v₀)
  obtain ⟨hπ, hπnz⟩ := (Localization.mem_submonoid_iff _).1 hπmem
  have hπ0 : π ≠ 0 := nonZeroDivisors.ne_zero hπnz
  replace hπ (v : HeightOneSpectrum (𝓞 K)) (hv : v ≠ v₀) : π ∉ v.asIdeal :=
    hπ v (Set.notMem_singleton_iff.2 hv)
  have hπ0' : (π : K) ≠ 0 := RingOfIntegers.coe_ne_zero_iff.2 hπ0
  have hπu (u : InfinitePlace K) : 0 < u (π : K) := InfinitePlace.pos_iff.2 hπ0'
  -- Minkowski's theorem gives a nonzero algebraic integer `a` with `|a|_u < δ |π|_u ^ m` at every
  -- infinite place `u`, once `m` is large; then `γ = a / π ^ m`.
  set q := ∏ u : InfinitePlace K, u (π : K) ^ mult u
  have hπunit : ¬IsUnit π := fun h ↦ v₀.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hπv₀ h)
  obtain ⟨m, hm⟩ : ∃ m : ℕ, TauCeti.NumberField.unitConst K / δ ^ Module.finrank ℚ K ≤ q ^ m :=
    ((tendsto_pow_atTop_atTop_of_one_lt
      (one_lt_prod_infinitePlace_pow_mult hπ0 hπunit)).eventually_ge_atTop _).exists
  obtain ⟨a, ha0, ha⟩ := TauCeti.NumberField.exists_ne_zero_forall_infinitePlace_lt
    (f := fun u ↦ δ * u (π : K) ^ m) (fun u ↦ by have := hπu u; positivity) <| by
      have hprod : ∏ u : InfinitePlace K, (δ * u (π : K) ^ m) ^ mult u =
          δ ^ Module.finrank ℚ K * q ^ m := by
        simp only [mul_pow, pow_right_comm _ m, Finset.prod_mul_distrib,
          Finset.prod_pow_eq_pow_sum, sum_mult_eq, Finset.prod_pow, q]
      rwa [hprod, ← div_le_iff₀' (pow_pos hδ _)]
  refine ⟨a / π ^ m, div_ne_zero (RingOfIntegers.coe_ne_zero_iff.2 ha0) (pow_ne_zero _ hπ0'),
    fun v hv ↦ ?_, fun u ↦ ?_⟩
  · have hπ1 : FinitePlace.mk v (π : K) = 1 :=
      (FinitePlace.mk_apply_coe_eq_one_iff _ _).2 (hπ v hv)
    rw [map_div₀, map_pow, hπ1, one_pow, div_one]
    exact FinitePlace.apply_le_one _ a
  · rw [map_div₀, map_pow, div_lt_iff₀ (pow_pos (hπu u) _)]
    exact ha u

/-- The case `S = ∅` of `exists_ne_zero_forall_norm_le_one_and_lt` at an infinite place `w₀`:
some nonzero `γ ∈ K` is integral at every finite place and smaller than `δ` at every infinite
place other than `w₀`. -/
private theorem exists_ne_zero_forall_apply_le_one_and_lt_of_infinite (w₀ : InfinitePlace K)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ γ : K, γ ≠ 0 ∧ (∀ v : HeightOneSpectrum (𝓞 K), FinitePlace.mk v γ ≤ 1) ∧
      ∀ u : InfinitePlace K, u ≠ w₀ → u γ < δ := by
  -- Minkowski's theorem concentrates the size of a nonzero algebraic integer `a` at `w₀`:
  -- `|a|_u * t ≤ c` at every other infinite place, with `t = 2 * c / δ`.
  set c := TauCeti.NumberField.unitConst K ^ ((Module.finrank ℚ K : ℝ)⁻¹)
  have hc : 0 < c := Real.rpow_pos_of_pos (TauCeti.NumberField.unitConst_pos K) _
  obtain ⟨a, ha0, ha, -⟩ := TauCeti.NumberField.exists_ne_zero_forall_infinitePlace_mul_le w₀
    (t := 2 * c / δ) (by positivity)
  refine ⟨a, RingOfIntegers.coe_ne_zero_iff.2 ha0, fun v ↦ FinitePlace.apply_le_one _ a,
    fun u hu ↦ ?_⟩
  have h : u (a : K) * (2 * c) ≤ c * δ := by
    rw [← div_le_iff₀ hδ, mul_div_assoc]
    exact ha u hu
  nlinarith [apply_nonneg u (a : K)]

/-- **Small elements away from one place.** For a place `w` of `K`, a finite set `S` of finite
places and `ε > 0`, some nonzero `β ∈ K` is integral at every finite place other than `w`, has
absolute value less than `ε` at every place of `S` other than `w`, and has absolute value less
than `ε` at every infinite place other than `w`. -/
theorem exists_ne_zero_forall_norm_le_one_and_lt (w : Place K)
    (S : Finset (HeightOneSpectrum (𝓞 K))) {ε : ℝ} (hε : 0 < ε) :
    ∃ β : K, β ≠ 0 ∧
      (∀ v : HeightOneSpectrum (𝓞 K), Sum.inl v ≠ w →
        ‖algebraMap K (v.adicCompletion K) β‖ ≤ 1) ∧
      (∀ v ∈ S, Sum.inl v ≠ w → ‖algebraMap K (v.adicCompletion K) β‖ < ε) ∧
      ∀ u : InfinitePlace K, Sum.inr u ≠ w → u β < ε := by
  classical
  simp_rw [FinitePlace.norm_algebraMap_adicCompletion]
  -- `β = d * γ`, where `d` is a nonzero algebraic integer that is small at the places of `S` and
  -- `γ` is the case `S = ∅`, chosen smaller than `ε / M` with `M > |d|_u` at every infinite `u`.
  obtain ⟨d, hd0, hd⟩ := FinitePlace.exists_ne_zero_forall_apply_le (S.image FinitePlace.mk)
    (ε := fun _ ↦ ε / 2) fun _ _ ↦ half_pos hε
  have hd0' : (d : K) ≠ 0 := RingOfIntegers.coe_ne_zero_iff.2 hd0
  set M := ∑ u : InfinitePlace K, u (d : K) + 1
  have hdM (u : InfinitePlace K) : u (d : K) < M :=
    (Finset.single_le_sum (fun u _ ↦ apply_nonneg u (d : K)) (Finset.mem_univ u)).trans_lt
      (lt_add_one _)
  have hM : 0 < M := (apply_nonneg _ _).trans_lt (hdM (Classical.arbitrary _))
  obtain ⟨γ, hγ0, hγint, hγinf⟩ : ∃ γ : K, γ ≠ 0 ∧
      (∀ v : HeightOneSpectrum (𝓞 K), Sum.inl v ≠ w → FinitePlace.mk v γ ≤ 1) ∧
      ∀ u : InfinitePlace K, Sum.inr u ≠ w → u γ < ε / M := by
    rcases w with v₀ | w₀
    · obtain ⟨γ, hγ0, hγint, hγinf⟩ :=
        exists_ne_zero_forall_apply_le_one_and_lt_of_finite v₀ (div_pos hε hM)
      exact ⟨γ, hγ0, fun v hv ↦ hγint v fun h ↦ hv (h ▸ rfl), fun u _ ↦ hγinf u⟩
    · obtain ⟨γ, hγ0, hγint, hγinf⟩ :=
        exists_ne_zero_forall_apply_le_one_and_lt_of_infinite w₀ (div_pos hε hM)
      exact ⟨γ, hγ0, fun v _ ↦ hγint v, fun u hu ↦ hγinf u fun h ↦ hu (h ▸ rfl)⟩
  refine ⟨d * γ, mul_ne_zero hd0' hγ0, fun v hv ↦ ?_, fun v hv hvw ↦ ?_, fun u hu ↦ ?_⟩
  · rw [map_mul]
    exact (mul_le_of_le_one_right (apply_nonneg _ _) (hγint v hv)).trans
      (FinitePlace.apply_le_one _ d)
  · rw [map_mul]
    exact (mul_le_of_le_one_right (apply_nonneg _ _) (hγint v hvw)).trans_lt
      ((hd _ (Finset.mem_image_of_mem _ hv)).trans_lt (half_lt_self hε))
  · rw [map_mul]
    calc u (d : K) * u γ ≤ M * u γ := by gcongr; exact (hdM u).le
      _ < M * (ε / M) := by gcongr; exact hγinf u hu
      _ = ε := mul_div_cancel₀ ε hM.ne'

/-- **Additive strong approximation away from one place** (Cassels–Fröhlich II §15). Let `w` be a
place of `K`, finite or infinite, `S` a finite set of finite places and `T` a finite set of
infinite places, none of them equal to `w`. For nonempty open sets `U v ⊆ K_v` at the places of
`S` and `V v ⊆ K_v` at the places of `T`, some `x ∈ K` lies in every `U v` and every `V v` and is
integral at every finite place outside `S` other than `w`.

Equivalently, `K` is dense in the restricted product of the completions `K_v`, `v ≠ w`, with
respect to the rings of integers at the finite places. An infinite place outside `T` carries no
condition. -/
theorem exists_forall_algebraMap_mem_and_forall_norm_le_one (w : Place K)
    (S : Finset (HeightOneSpectrum (𝓞 K))) (T : Finset (InfinitePlace K))
    (hS : ∀ v ∈ S, Sum.inl v ≠ w) (hT : ∀ v ∈ T, Sum.inr v ≠ w)
    (U : (v : HeightOneSpectrum (𝓞 K)) → Set (v.adicCompletion K))
    (V : (v : InfinitePlace K) → Set v.Completion)
    (hU : ∀ v ∈ S, IsOpen (U v) ∧ (U v).Nonempty)
    (hV : ∀ v ∈ T, IsOpen (V v) ∧ (V v).Nonempty) :
    ∃ x : K, (∀ v ∈ S, algebraMap K (v.adicCompletion K) x ∈ U v) ∧
      (∀ v ∈ T, algebraMap K v.Completion x ∈ V v) ∧
      ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → Sum.inl v ≠ w →
        ‖algebraMap K (v.adicCompletion K) x‖ ≤ 1 := by
  classical
  -- The product `O` of the `U v` and the `V v` is open in the product of the completions, and by
  -- weak approximation it contains the image of some `y ∈ K`. A ball of radius `r > 0` around
  -- that image lies in `O`.
  set O := (Set.univ.pi fun v : S ↦ U v.val) ×ˢ (Set.univ.pi fun v : T ↦ V v.val)
  have hO : IsOpen O := (isOpen_set_pi Set.finite_univ fun v _ ↦ (hU v.val v.property).1).prod
    (isOpen_set_pi Set.finite_univ fun v _ ↦ (hV v.val v.property).1)
  obtain ⟨y, hy⟩ := (weakApproximation_denseRange S T).exists_mem_open hO
    ⟨(fun v ↦ (hU v.val v.property).2.some, fun v ↦ (hV v.val v.property).2.some),
      fun v _ ↦ (hU v.val v.property).2.some_mem, fun v _ ↦ (hV v.val v.property).2.some_mem⟩
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hO _ hy
  -- The `S`-integer approximation loses at most `A` at the infinite places.
  obtain ⟨A, hA⟩ := NumberField.exists_forall_apply_add_le (K := K)
  -- An element `β ≠ 0`, integral at the finite places other than `w`, with `|β|_v < r` at the
  -- places of `S` and `|β|_u * A < r` at the infinite places other than `w`.
  obtain ⟨β, hβ0, hβint, hβS, hβT⟩ :=
    exists_ne_zero_forall_norm_le_one_and_lt w S (ε := r / (|A| + 1)) (by positivity)
  simp_rw [FinitePlace.norm_algebraMap_adicCompletion] at hβint hβS ⊢
  have hrA : r / (|A| + 1) ≤ r := div_le_self hr.le (le_add_of_nonneg_left (abs_nonneg A))
  -- Approximate `y / β` by an element `ξ` integral outside `S` and `w`; then `x = β * ξ`.
  set S' : Finset (FinitePlace K) := (S ∪ w.getLeft?.toFinset).image FinitePlace.mk
  have hS' (v : HeightOneSpectrum (𝓞 K)) : FinitePlace.mk v ∈ S' ↔ v ∈ S ∨ Sum.inl v = w := by
    simp [S', FinitePlace.mk_injective.mem_finset_image, Sum.getLeft?_eq_some_iff,
      @eq_comm _ (Sum.inl v)]
  obtain ⟨ξ, hξint, hξS, hξT⟩ := hA S' fun _ ↦ -(y / β)
  have hxy : β * ξ - y = β * (ξ + -(y / β)) := by
    field_simp
    ring
  -- `β * ξ` is within `r` of `y` at every place of `S` and of `T`, so it lies in `O`.
  have hmem : ((fun v : S ↦ algebraMap K (v.val.adicCompletion K) (β * ξ)),
      fun v : T ↦ algebraMap K v.val.Completion (β * ξ)) ∈ O := hball <| by
    rw [Metric.mem_ball, Prod.dist_eq, max_lt_iff, dist_pi_lt_iff hr, dist_pi_lt_iff hr]
    refine ⟨fun ⟨v, hv⟩ ↦ ?_, fun ⟨v, hv⟩ ↦ ?_⟩
    · rw [dist_eq_norm, ← map_sub, FinitePlace.norm_algebraMap_adicCompletion, hxy, map_mul]
      exact (mul_le_of_le_one_right (apply_nonneg _ _) (hξS _ ((hS' v).2 (.inl hv)))).trans_lt
        ((hβS v hv (hS v hv)).trans_le hrA)
    · rw [dist_eq_norm, ← map_sub, Completion.norm_algebraMap, hxy, map_mul]
      have hβv := hβT v (hT v hv)
      rw [lt_div_iff₀ (by positivity)] at hβv
      calc v β * v (ξ + -(y / β)) ≤ v β * |A| :=
            mul_le_mul_of_nonneg_left ((hξT v).trans (le_abs_self A)) (apply_nonneg _ _)
        _ ≤ v β * (|A| + 1) := by linarith [apply_nonneg v β]
        _ < r := hβv
  refine ⟨β * ξ, fun v hv ↦ hmem.1 ⟨v, hv⟩ (Set.mem_univ _),
    fun v hv ↦ hmem.2 ⟨v, hv⟩ (Set.mem_univ _), fun v hv hvw ↦ ?_⟩
  rw [map_mul]
  exact (mul_le_of_le_one_right (apply_nonneg _ _)
    (hξint _ fun h ↦ ((hS' v).1 h).elim hv hvw)).trans (hβint v hvw)

end TauCeti.GlobalNumberFields
