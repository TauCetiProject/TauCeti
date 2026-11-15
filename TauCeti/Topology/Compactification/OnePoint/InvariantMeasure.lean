/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Typeclasses.NullSingletonClass
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
public import TauCeti.MeasureTheory.Constructions.BorelSpace.OnePoint
public import TauCeti.Topology.Compactification.OnePoint.Amenable

import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.Sequences
import TauCeti.Geometry.Manifold.Instances.OnePoint.Moebius
import TauCeti.GroupTheory.Amenable.Extension
import TauCeti.GroupTheory.Amenable.Finite
import TauCeti.Topology.Compactification.OnePoint.Nhds

/-!
# Furstenberg's lemma for invariant measures on the projective line

Let `G` be a group acting by Möbius transformations on the projective line `OnePoint ℝ` through a
discrete-image representation in `SL(2, ℝ)` (for example, an injective homomorphism
`G →* SL(2, ℤ)`). Furstenberg's lemma states that if `OnePoint ℝ` admits a `G`-invariant Borel
probability measure, then `G` is amenable for every group topology; when the invariant probability
measure vanishes on singletons, `G` is in fact finite. Over an arbitrary field `K`, an injective
representation into `GL(2, K)` preserving singleton masses of a finite measure with an atom also
forces `G` to be amenable.

These rigidity statements rule out invariant projective measures for nonamenable subgroups of
`SL(2, ℤ)` and serve as the geometric endgame in Burger's spectral characterization of relative
property (T) for `(ℤ² ⋊ G, ℤ²)`.

## Main results

* `MonoidHom.amenable_of_onePoint_measure_singleton_ne_zero`: an injective representation into
  `GL(2, K)` preserving singleton masses of a finite measure on `OnePoint K` that charges a
  singleton has amenable domain.
* `MonoidHom.finite_of_nullSingletonClass_of_map_onePoint_measure_eq`: a homomorphism into
  `SL(2, ℝ)` with finite entrywise balls preserving a singleton-null Borel probability measure on
  `OnePoint ℝ` has finite domain.
* `MonoidHom.amenable_of_map_onePoint_measure_eq`: an injective homomorphism into `SL(2, ℝ)` with
  finite entrywise balls preserving a Borel probability measure on `OnePoint ℝ` has amenable
  domain.
* `MonoidHom.amenable_of_injective_slTwo_of_map_onePoint_measure_eq`: any group embedding in
  `SL(2, ℤ)` and preserving a Borel probability measure on `OnePoint ℝ` is amenable.

## References

* H. Furstenberg, *A Poisson formula for semi-simple Lie groups*, Ann. of Math. (2) 77 (1963),
  335–386, Lemma 1.5.
* B. Bekka, P. de la Harpe, A. Valette, *Kazhdan's Property (T)*, Cambridge University Press
  (2008), Lemma 4.2.3.
* C. Anantharaman, S. Popa, *An Introduction to II₁ Factors*, Example 14.2.8.
-/

public section

open Filter Matrix MeasureTheory MulAction OnePoint Set Topology
open scoped MatrixGroups OnePoint

namespace MonoidHom

section Atomic

-- Atomic case: an atom `x` with `ν {x} ≠ 0` has finite `G`-orbit `O` because distinct points in `O`
-- carry equal positive mass inside `ν Set.univ < ∞`; the kernel of `G →* Equiv.Perm O` lies in the
-- stabilizer of `x`, which is amenable by `MonoidHom.amenable_comap_onePoint_stabilizer`.

variable {K G : Type*} [Field K] [DecidableEq K] [Group G]

private theorem finite_orbit_of_measure_singleton_ne_zero (φ : G →* GL (Fin 2) K)
    [MeasurableSpace (OnePoint K)] [MeasurableSingletonClass (OnePoint K)]
    {ν : Measure (OnePoint K)} [IsFiniteMeasure ν]
    (hν : ∀ (g : G) (y : OnePoint K), ν {φ g • y} = ν {y}) {x : OnePoint K} (hx : ν {x} ≠ 0) :
    {y : OnePoint K | ∃ g : G, φ g • x = y}.Finite := by
  by_contra hinf
  have hx_pos : 0 < (ν {x}).toReal := ENNReal.toReal_pos hx (measure_ne_top ν _)
  let N : ℕ := ⌊(ν univ).toReal / (ν {x}).toReal⌋₊ + 1
  obtain ⟨s, hs, hcard⟩ := Set.Infinite.exists_subset_card_eq hinf N
  have hsum : ∑ y ∈ s, ν {y} = N * ν {x} := by
    calc ∑ y ∈ s, ν {y}
        = ∑ _y ∈ s, ν {x} := Finset.sum_congr rfl fun y hy ↦ by
          obtain ⟨g, rfl⟩ := hs hy
          exact hν g x
      _ = N * ν {x} := by simp [hcard]
  have hle : ∑ y ∈ s, ν {y} ≤ ν univ := by
    rw [← measure_biUnion_finset (fun y _ z _ hyz ↦ disjoint_singleton.mpr hyz)
      fun _ _ ↦ measurableSet_singleton _]
    exact measure_mono (subset_univ _)
  rw [hsum] at hle
  have hreal := (ENNReal.toReal_le_toReal (ENNReal.mul_ne_top (ENNReal.natCast_ne_top N)
    (measure_ne_top ν _)) (measure_ne_top ν _)).mpr hle
  rw [ENNReal.toReal_mul, ENNReal.toReal_natCast] at hreal
  have hlt : (ν univ).toReal / (ν {x}).toReal < N := by
    dsimp [N]
    push_cast
    exact Nat.lt_floor_add_one _
  exact not_lt_of_ge hreal ((div_lt_iff₀ hx_pos).mp hlt)

/-- If an injective matrix representation `φ : G →* GL(2, K)` preserves singleton masses of a
finite measure `ν` on `OnePoint K` and `ν` charges a singleton, then `G` is amenable for every
group topology. -/
theorem amenable_of_onePoint_measure_singleton_ne_zero [TopologicalSpace G] [IsTopologicalGroup G]
    (φ : G →* GL (Fin 2) K) (hφ : Function.Injective φ)
    [MeasurableSpace (OnePoint K)] [MeasurableSingletonClass (OnePoint K)]
    {ν : Measure (OnePoint K)} [IsFiniteMeasure ν]
    (hν : ∀ (g : G) (y : OnePoint K), ν {φ g • y} = ν {y}) {x : OnePoint K} (hx : ν {x} ≠ 0) :
    TauCeti.Amenable G := by
  apply TauCeti.Amenable.of_discrete
  let : TopologicalSpace G := ⊥
  let : DiscreteTopology G := ⟨rfl⟩
  let O : Set (OnePoint K) := {y | ∃ g : G, φ g • x = y}
  have : Finite O := (finite_orbit_of_measure_singleton_ne_zero φ hν hx).to_subtype
  let : TopologicalSpace (Equiv.Perm O) := ⊥
  let : DiscreteTopology (Equiv.Perm O) := ⟨rfl⟩
  let π : G →* Equiv.Perm O :=
    { toFun := fun g ↦
        { toFun := fun y ↦
            ⟨φ g • y.1, by obtain ⟨h, hh⟩ := y.2; exact ⟨g * h, by rw [← hh, map_mul, mul_smul]⟩⟩
          invFun := fun y ↦
            ⟨φ g⁻¹ • y.1, by
              obtain ⟨h, hh⟩ := y.2; exact ⟨g⁻¹ * h, by rw [← hh, map_mul, mul_smul]⟩⟩
          left_inv := fun y ↦ Subtype.ext (by simp)
          right_inv := fun y ↦ Subtype.ext (by simp) }
      map_one' := Equiv.ext fun y ↦ Subtype.ext (by simp)
      map_mul' := fun g h ↦ Equiv.ext fun y ↦ Subtype.ext (by simp [mul_smul]) }
  let S : Subgroup G := (stabilizer (GL (Fin 2) K) x).comap φ
  have : TauCeti.Amenable S := φ.amenable_comap_onePoint_stabilizer hφ x
  refine TauCeti.Amenable.of_ker_le_range S.subtype π fun g hg ↦ ?_
  rw [Subgroup.range_subtype]
  exact congrArg Subtype.val (Equiv.congr_fun (MonoidHom.mem_ker.mp hg) ⟨x, ⟨1, by simp⟩⟩)

end Atomic

section RealProjectiveLine

-- Atomless case: an unbounded sequence in `SL(2, ℝ)`, rescaled by its `L^∞` matrix norm, admits a
-- subsequence converging to a nonzero determinant-zero matrix `A`. The Möbius action along that
-- subsequence contracts `OnePoint ℝ \ {p₋}` pointwise to a single limit `p₊`, which is
-- incompatible with an atomless invariant probability measure by dominated convergence.

private theorem tendsto_smul_coe_of_tendsto_rescaled {g : ℕ → SL(2, ℝ)} {M : ℕ → ℝ}
    (hM : ∀ n, 0 < M n) {A : Matrix (Fin 2) (Fin 2) ℝ}
    (hA : ∀ i j, Tendsto (fun n ↦ (M n)⁻¹ * (g n : Matrix (Fin 2) (Fin 2) ℝ) i j)
      atTop (𝓝 (A i j)))
    {t : ℝ} (hden : A 1 0 * t + A 1 1 ≠ 0) :
    Tendsto (fun n ↦ (g n : GL (Fin 2) ℝ) • (t : OnePoint ℝ)) atTop
      (𝓝 (((A 0 0 * t + A 0 1) / (A 1 0 * t + A 1 1) : ℝ) : OnePoint ℝ)) := by
  have hlim_num : Tendsto (fun n ↦ (M n)⁻¹ * g n 0 0 * t + (M n)⁻¹ * g n 0 1)
      atTop (𝓝 (A 0 0 * t + A 0 1)) := ((hA 0 0).mul_const t).add (hA 0 1)
  have hlim_den : Tendsto (fun n ↦ (M n)⁻¹ * g n 1 0 * t + (M n)⁻¹ * g n 1 1)
      atTop (𝓝 (A 1 0 * t + A 1 1)) := ((hA 1 0).mul_const t).add (hA 1 1)
  have hev : (fun n ↦ (g n : GL (Fin 2) ℝ) • (t : OnePoint ℝ)) =ᶠ[atTop] fun n ↦
      ((((M n)⁻¹ * g n 0 0 * t + (M n)⁻¹ * g n 0 1) /
        ((M n)⁻¹ * g n 1 0 * t + (M n)⁻¹ * g n 1 1) : ℝ) : OnePoint ℝ) := by
    filter_upwards [hlim_den.eventually_ne hden] with n hn
    have hMinv : (M n)⁻¹ ≠ 0 := inv_ne_zero (hM n).ne'
    have hraw : (g n : Matrix (Fin 2) (Fin 2) ℝ) 1 0 * t + g n 1 1 ≠ 0 := fun h0 ↦
      hn (by linear_combination (M n)⁻¹ * h0)
    rw [smul_some_eq_ite]
    split_ifs with hbad
    · exact absurd hbad hraw
    · rw [OnePoint.coe_eq_coe]
      calc (g n 0 0 * t + g n 0 1) / (g n 1 0 * t + g n 1 1)
          = (M n)⁻¹ * (g n 0 0 * t + g n 0 1) / ((M n)⁻¹ * (g n 1 0 * t + g n 1 1)) :=
            (mul_div_mul_left _ _ hMinv).symm
        _ = _ := by ring
  exact (OnePoint.continuous_coe.continuousAt.tendsto.comp
    (hlim_num.div hlim_den hden)).congr' hev.symm

private theorem exists_tendsto_smul_onePoint_of_row_one_ne_zero {g : ℕ → SL(2, ℝ)} {M : ℕ → ℝ}
    (hM : ∀ n, 0 < M n) {A : Matrix (Fin 2) (Fin 2) ℝ} (hdet : A.det = 0)
    (hrow : A 1 0 ≠ 0 ∨ A 1 1 ≠ 0)
    (hA : ∀ i j, Tendsto (fun n ↦ (M n)⁻¹ * (g n : Matrix (Fin 2) (Fin 2) ℝ) i j)
      atTop (𝓝 (A i j))) :
    ∃ p_minus p_plus : OnePoint ℝ, ∀ x : OnePoint ℝ, x ≠ p_minus →
      Tendsto (fun n ↦ (g n : GL (Fin 2) ℝ) • x) atTop (𝓝 p_plus) := by
  have hdet' : A 0 0 * A 1 1 - A 0 1 * A 1 0 = 0 := by simpa [det_fin_two] using hdet
  by_cases hc : A 1 0 ≠ 0
  · refine ⟨((-A 1 1 / A 1 0 : ℝ) : OnePoint ℝ), ((A 0 0 / A 1 0 : ℝ) : OnePoint ℝ),
      fun x hx ↦ ?_⟩
    induction x using OnePoint.rec with
    | infty =>
      have hev : (fun n ↦ (g n : GL (Fin 2) ℝ) • (∞ : OnePoint ℝ)) =ᶠ[atTop]
          fun n ↦ ((((M n)⁻¹ * g n 0 0) / ((M n)⁻¹ * g n 1 0) : ℝ) : OnePoint ℝ) := by
        filter_upwards [(hA 1 0).eventually_ne hc] with n hn
        have hg10 : (g n : Matrix (Fin 2) (Fin 2) ℝ) 1 0 ≠ 0 := right_ne_zero_of_mul hn
        have hMinv : (M n)⁻¹ ≠ 0 := inv_ne_zero (hM n).ne'
        rw [smul_infty_eq_ite]
        simp [hg10, mul_div_mul_left _ _ hMinv]
      exact (OnePoint.continuous_coe.continuousAt.tendsto.comp
        ((hA 0 0).div (hA 1 0) hc)).congr' hev.symm
    | coe t =>
      have hden : A 1 0 * t + A 1 1 ≠ 0 := fun h0 ↦ hx <| by
        rw [OnePoint.coe_eq_coe]
        field_simp [hc]
        linarith
      have hquot : (A 0 0 * t + A 0 1) / (A 1 0 * t + A 1 1) = A 0 0 / A 1 0 := by
        rw [div_eq_div_iff hden hc]
        linear_combination -hdet'
      rw [← hquot]
      exact tendsto_smul_coe_of_tendsto_rescaled hM hA hden
  · push Not at hc
    have hd : A 1 1 ≠ 0 := hrow.resolve_left (not_not.mpr hc)
    have ha : A 0 0 = 0 := by
      have : A 0 0 * A 1 1 = 0 := by linear_combination hdet' + A 0 1 * hc
      exact (mul_eq_zero.mp this).resolve_right hd
    refine ⟨∞, ((A 0 1 / A 1 1 : ℝ) : OnePoint ℝ), fun x hx ↦ ?_⟩
    induction x using OnePoint.rec with
    | infty => exact (hx rfl).elim
    | coe t =>
      have hden : A 1 0 * t + A 1 1 ≠ 0 := by simpa [hc] using hd
      have hquot : (A 0 0 * t + A 0 1) / (A 1 0 * t + A 1 1) = A 0 1 / A 1 1 := by simp [ha, hc]
      rw [← hquot]
      exact tendsto_smul_coe_of_tendsto_rescaled hM hA hden

private theorem exists_tendsto_smul_onePoint_of_det_eq_zero {g : ℕ → SL(2, ℝ)} {M : ℕ → ℝ}
    (hM : ∀ n, 0 < M n) {A : Matrix (Fin 2) (Fin 2) ℝ} (hAne : A ≠ 0) (hdet : A.det = 0)
    (hA : ∀ i j, Tendsto (fun n ↦ (M n)⁻¹ * (g n : Matrix (Fin 2) (Fin 2) ℝ) i j)
      atTop (𝓝 (A i j))) :
    ∃ p_minus p_plus : OnePoint ℝ, ∀ x : OnePoint ℝ, x ≠ p_minus →
      Tendsto (fun n ↦ (g n : GL (Fin 2) ℝ) • x) atTop (𝓝 p_plus) := by
  by_cases hrow : A 1 0 ≠ 0 ∨ A 1 1 ≠ 0
  · exact exists_tendsto_smul_onePoint_of_row_one_ne_zero hM hdet hrow hA
  · push Not at hrow
    -- Left-multiplying by `J = !![0, 1; -1, 0]` moves the nonzero top row of `A` to the bottom.
    have hrow0 : A 0 0 ≠ 0 ∨ A 0 1 ≠ 0 := by
      by_contra h0
      push Not at h0
      exact hAne (Matrix.ext fun i j ↦ by fin_cases i <;> fin_cases j <;> simp [h0, hrow])
    let J : SL(2, ℝ) := ⟨!![0, 1; -1, 0], by simp⟩
    have hJ0 (B : Matrix (Fin 2) (Fin 2) ℝ) (j : Fin 2) :
        ((J : Matrix (Fin 2) (Fin 2) ℝ) * B) 0 j = B 1 j := by
      simp [Matrix.mul_apply, Fin.sum_univ_two, J]
    have hJ1 (B : Matrix (Fin 2) (Fin 2) ℝ) (j : Fin 2) :
        ((J : Matrix (Fin 2) (Fin 2) ℝ) * B) 1 j = -B 0 j := by
      simp [Matrix.mul_apply, Fin.sum_univ_two, J]
    let A' : Matrix (Fin 2) (Fin 2) ℝ := (J : Matrix (Fin 2) (Fin 2) ℝ) * A
    have hdet' : A'.det = 0 := by simp [A', hdet]
    have hrow' : A' 1 0 ≠ 0 ∨ A' 1 1 ≠ 0 := by
      rcases hrow0 with h00 | h01
      · exact Or.inl (by simpa [A', hJ1] using h00)
      · exact Or.inr (by simpa [A', hJ1] using h01)
    have hA' (i j : Fin 2) :
        Tendsto (fun n ↦ (M n)⁻¹ * ((J * g n : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ) i j)
          atTop (𝓝 (A' i j)) := by
      fin_cases i
      · simpa [A', SpecialLinearGroup.coe_mul, hJ0] using hA 1 j
      · simpa [A', SpecialLinearGroup.coe_mul, hJ1, mul_neg] using (hA 0 j).neg
    obtain ⟨p_minus, p_plus, hp⟩ :=
      exists_tendsto_smul_onePoint_of_row_one_ne_zero hM hdet' hrow' hA'
    refine ⟨p_minus, SpecialLinearGroup.toGL J⁻¹ • p_plus, fun x hx ↦ ?_⟩
    have hcont : Continuous (SpecialLinearGroup.toGL J⁻¹ • · : OnePoint ℝ → OnePoint ℝ) :=
      continuous_const_smul _
    have hcongr (n : ℕ) :
        SpecialLinearGroup.toGL J⁻¹ • ((J * g n : SL(2, ℝ)) : GL (Fin 2) ℝ) • x =
          (g n : GL (Fin 2) ℝ) • x := by
      rw [← mul_smul, ← map_mul SpecialLinearGroup.toGL, inv_mul_cancel_left]
    exact (hcont.continuousAt.tendsto.comp (hp x hx)).congr hcongr

private noncomputable def zeroAtInftyProfile (x : OnePoint ℝ) : ℝ :=
  x.elim 0 fun t ↦ (1 + t ^ 2)⁻¹

private theorem exists_continuous_nonneg_eq_zero_iff (p : OnePoint ℝ) :
    ∃ f : OnePoint ℝ → ℝ, Continuous f ∧ (∀ x, 0 ≤ f x) ∧ (∀ x, f x ≤ 1) ∧
      ∀ x, f x = 0 ↔ x = p := by
  have hf₀_cont : Continuous zeroAtInftyProfile := by
    rw [OnePoint.continuous_iff]
    refine ⟨?_, (continuous_const.add (continuous_pow 2)).inv₀ fun t ↦
      (by positivity : 0 < 1 + t ^ 2).ne'⟩
    rw [coclosedCompact_eq_cocompact]
    have hgrowth : Tendsto (fun t : ℝ ↦ 1 + t ^ 2) (cocompact ℝ) atTop :=
      tendsto_atTop_mono
        (fun t ↦ by rw [dist_zero_left, Real.norm_eq_abs]; nlinarith [sq_abs t, abs_nonneg t])
        (tendsto_dist_left_cocompact_atTop (0 : ℝ))
    simpa [Function.comp_def, zeroAtInftyProfile] using tendsto_inv_atTop_zero.comp hgrowth
  have hf₀_nonneg (y : OnePoint ℝ) : 0 ≤ zeroAtInftyProfile y := by
    induction y using OnePoint.rec with
    | infty => exact le_rfl
    | coe t => exact inv_nonneg.mpr (by positivity)
  have hf₀_le (y : OnePoint ℝ) : zeroAtInftyProfile y ≤ 1 := by
    induction y using OnePoint.rec with
    | infty => exact zero_le_one
    | coe t => exact inv_le_one_of_one_le₀ (by linarith [sq_nonneg t])
  have hf₀_zero (y : OnePoint ℝ) : zeroAtInftyProfile y = 0 ↔ y = ∞ := by
    induction y using OnePoint.rec with
    | infty => simp [zeroAtInftyProfile]
    | coe t => simp [zeroAtInftyProfile, (by positivity : (1 : ℝ) + t ^ 2 ≠ 0)]
  have : IsPretransitive (GL (Fin 2) ℝ) (OnePoint ℝ) :=
    isPretransitive_of_is_two_pretransitive
  obtain ⟨σ, hσ⟩ := exists_smul_eq (GL (Fin 2) ℝ) p (∞ : OnePoint ℝ)
  refine ⟨fun x ↦ zeroAtInftyProfile (σ • x), hf₀_cont.comp (continuous_const_smul σ),
    fun x ↦ hf₀_nonneg (σ • x), fun x ↦ hf₀_le (σ • x), fun x ↦ ?_⟩
  rw [hf₀_zero, ← hσ, (MulAction.injective σ).eq_iff]

private theorem exists_subseq_tendsto_rescaled_det_eq_zero {G : Type*} [Group G] [Infinite G]
    (φ : G →* SL(2, ℝ))
    (hfin : ∀ R : ℝ, {g : G | ∀ i j, |(φ g : Matrix (Fin 2) (Fin 2) ℝ) i j| ≤ R}.Finite) :
    ∃ (u : ℕ → G) (M : ℕ → ℝ) (A : Matrix (Fin 2) (Fin 2) ℝ),
      (∀ k, 0 < M k) ∧ A ≠ 0 ∧ A.det = 0 ∧
      ∀ i j, Tendsto (fun k ↦ (M k)⁻¹ * (φ (u k) : Matrix (Fin 2) (Fin 2) ℝ) i j)
        atTop (𝓝 (A i j)) := by
  let raw : G → Fin 2 → Fin 2 → ℝ := fun g i j ↦ (φ g : Matrix (Fin 2) (Fin 2) ℝ) i j
  have hex (n : ℕ) : ∃ g : G, (n : ℝ) + 1 < ‖raw g‖ := by
    obtain ⟨g, -, hg⟩ := (Set.infinite_univ.sdiff (hfin (n + 1))).nonempty
    simp only [mem_ofPred_eq, not_forall, not_le] at hg
    obtain ⟨i, j, hij⟩ := hg
    refine ⟨g, hij.trans_le ?_⟩
    rw [← Real.norm_eq_abs]
    exact (norm_le_pi_norm (raw g i) j).trans (norm_le_pi_norm (raw g) i)
  choose g hg using hex
  have hnorm_pos (n : ℕ) : 0 < ‖raw (g n)‖ := by linarith [hg n]
  let B : ℕ → Fin 2 → Fin 2 → ℝ := fun n ↦ ‖raw (g n)‖⁻¹ • raw (g n)
  have hB_norm (n : ℕ) : ‖B n‖ = 1 := by
    simp [B, norm_smul, inv_mul_cancel₀ (hnorm_pos n).ne']
  let K : Set (Fin 2 → Fin 2 → ℝ) := univ.pi fun _ ↦ univ.pi fun _ ↦ Icc (-1 : ℝ) 1
  have hK : IsCompact K := isCompact_univ_pi fun _ ↦ isCompact_univ_pi fun _ ↦ isCompact_Icc
  have hBK (n : ℕ) : B n ∈ K := fun i _ j _ ↦ abs_le.mp <| by
    rw [← Real.norm_eq_abs]
    exact ((norm_le_pi_norm (B n i) j).trans (norm_le_pi_norm (B n) i)).trans_eq (hB_norm n)
  obtain ⟨A₀, -, ns, hns, hlim⟩ := hK.tendsto_subseq hBK
  have hA₀_norm : ‖A₀‖ = 1 :=
    tendsto_nhds_unique hlim.norm ((tendsto_const_nhds (x := (1 : ℝ))).congr fun k ↦
      (hB_norm (ns k)).symm)
  let A : Matrix (Fin 2) (Fin 2) ℝ := Matrix.of A₀
  have hAne : A ≠ 0 := fun h0 ↦ by
    have : A₀ = 0 := funext fun i ↦ funext fun j ↦ congrFun (congrFun h0 i) j
    simp [this] at hA₀_norm
  have hAentry (i j : Fin 2) :
      Tendsto (fun k ↦ ‖raw (g (ns k))‖⁻¹ * (φ (g (ns k)) : Matrix (Fin 2) (Fin 2) ℝ) i j)
        atTop (𝓝 (A i j)) := by
    simpa [Function.comp_def, A, B, raw] using
      ((continuous_apply j).comp (continuous_apply i)).continuousAt.tendsto.comp hlim
  have hMinv : Tendsto (fun k ↦ ‖raw (g (ns k))‖⁻¹) atTop (𝓝 0) := by
    refine tendsto_inv_atTop_zero.comp (tendsto_atTop_mono (fun k ↦ ?_) tendsto_natCast_atTop_atTop)
    have hk : (k : ℝ) ≤ ns k := by exact_mod_cast hns.id_le k
    linarith [hg (ns k)]
  have hAdet : A.det = 0 := by
    rw [det_fin_two]
    refine tendsto_nhds_unique
      (((hAentry 0 0).mul (hAentry 1 1)).sub ((hAentry 0 1).mul (hAentry 1 0))) ?_
    have hdetB (k : ℕ) :
        ‖raw (g (ns k))‖⁻¹ * (φ (g (ns k)) : Matrix (Fin 2) (Fin 2) ℝ) 0 0 *
          (‖raw (g (ns k))‖⁻¹ * (φ (g (ns k)) : Matrix (Fin 2) (Fin 2) ℝ) 1 1) -
        ‖raw (g (ns k))‖⁻¹ * (φ (g (ns k)) : Matrix (Fin 2) (Fin 2) ℝ) 0 1 *
          (‖raw (g (ns k))‖⁻¹ * (φ (g (ns k)) : Matrix (Fin 2) (Fin 2) ℝ) 1 0) =
        ‖raw (g (ns k))‖⁻¹ ^ 2 * (φ (g (ns k)) : Matrix (Fin 2) (Fin 2) ℝ).det := by
      rw [det_fin_two]
      ring
    simpa [hdetB] using (by simpa using hMinv.pow 2 :
      Tendsto (fun k ↦ ‖raw (g (ns k))‖⁻¹ ^ 2) atTop (𝓝 0))
  exact ⟨fun k ↦ g (ns k), fun k ↦ ‖raw (g (ns k))‖, A, fun k ↦ hnorm_pos (ns k),
    hAne, hAdet, hAentry⟩

/-- A group `G` admitting a homomorphism `φ : G →* SL(2, ℝ)` with finite preimages of entrywise
balls and preserving a Borel probability measure on `OnePoint ℝ` that vanishes on singletons is
finite. -/
theorem finite_of_nullSingletonClass_of_map_onePoint_measure_eq {G : Type*} [Group G]
    (φ : G →* SL(2, ℝ))
    (hfin : ∀ R : ℝ, {g : G | ∀ i j, |(φ g : Matrix (Fin 2) (Fin 2) ℝ) i j| ≤ R}.Finite)
    {ν : Measure (OnePoint ℝ)} [IsProbabilityMeasure ν] [NullSingletonClass ν]
    (hν : ∀ g : G, Measure.map ((φ g : GL (Fin 2) ℝ) • ·) ν = ν) :
    Finite G := by
  by_contra! hinf
  obtain ⟨u, M, A, hM, hAne, hAdet, hAentry⟩ :=
    exists_subseq_tendsto_rescaled_det_eq_zero φ hfin
  obtain ⟨p_minus, p_plus, hp⟩ :=
    exists_tendsto_smul_onePoint_of_det_eq_zero hM hAne hAdet hAentry
  obtain ⟨f, hf_cont, hf_nonneg, hf_le, hf_zero⟩ := exists_continuous_nonneg_eq_zero_iff p_plus
  have hae : ∀ᵐ x ∂ν, Tendsto (fun k ↦ f ((φ (u k) : GL (Fin 2) ℝ) • x)) atTop (𝓝 0) := by
    filter_upwards [ν.ae_ne p_minus] with x hx
    simpa [Function.comp_def, (hf_zero p_plus).mpr rfl] using
      hf_cont.continuousAt.tendsto.comp (hp x hx)
  have hdom : Tendsto (fun k ↦ ∫ x, f ((φ (u k) : GL (Fin 2) ℝ) • x) ∂ν) atTop (𝓝 0) := by
    simpa using tendsto_integral_of_dominated_convergence (fun _ ↦ (1 : ℝ))
      (fun k ↦ (hf_cont.comp (continuous_const_smul _)).aestronglyMeasurable)
      (integrable_const (1 : ℝ))
      (fun k ↦ .of_forall fun x ↦ by
        dsimp only [Function.comp_def]
        rw [Real.norm_eq_abs, abs_of_nonneg (hf_nonneg _)]
        exact hf_le _) hae
  have hinv (k : ℕ) : ∫ x, f ((φ (u k) : GL (Fin 2) ℝ) • x) ∂ν = ∫ x, f x ∂ν := by
    have hm : AEMeasurable ((φ (u k) : GL (Fin 2) ℝ) • · : OnePoint ℝ → OnePoint ℝ) ν :=
      (continuous_const_smul _).measurable.aemeasurable
    rw [← integral_map hm hf_cont.aestronglyMeasurable, hν]
  have hint0 : ∫ x, f x ∂ν = 0 :=
    tendsto_nhds_unique (tendsto_const_nhds.congr fun k ↦ (hinv k).symm) hdom
  have hf_int : Integrable f ν :=
    (integrable_const (1 : ℝ)).mono' hf_cont.aestronglyMeasurable
      (.of_forall fun x ↦ by rw [Real.norm_eq_abs, abs_of_nonneg (hf_nonneg x)]; exact hf_le x)
  have hf_ae : f =ᵐ[ν] 0 := (integral_eq_zero_iff_of_nonneg hf_nonneg hf_int).mp hint0
  have hcompl : ν {p_plus}ᶜ = 0 := by
    have : {p_plus}ᶜ = {x : OnePoint ℝ | f x ≠ 0} := by ext x; simp [hf_zero]
    rw [this]
    exact ae_iff.mp hf_ae
  have huniv : ν univ = 0 := by
    rw [← union_compl_self {p_plus}]
    exact measure_union_null (measure_singleton p_plus) hcompl
  exact one_ne_zero ((measure_univ (μ := ν)).symm.trans huniv)

/-- **Furstenberg's lemma on the real projective line.** If `φ : G →* SL(2, ℝ)` is injective, has
finite preimages of entrywise balls, and preserves a Borel probability measure `ν` on `OnePoint ℝ`,
then `G` is amenable for every group topology. -/
theorem amenable_of_map_onePoint_measure_eq {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] (φ : G →* SL(2, ℝ)) (hφ : Function.Injective φ)
    (hfin : ∀ R : ℝ, {g : G | ∀ i j, |(φ g : Matrix (Fin 2) (Fin 2) ℝ) i j| ≤ R}.Finite)
    {ν : Measure (OnePoint ℝ)} [IsProbabilityMeasure ν]
    (hν : ∀ g : G, Measure.map ((φ g : GL (Fin 2) ℝ) • ·) ν = ν) :
    TauCeti.Amenable G := by
  by_cases hatom : ∃ x : OnePoint ℝ, ν {x} ≠ 0
  · obtain ⟨x, hx⟩ := hatom
    let φGL : G →* GL (Fin 2) ℝ := SpecialLinearGroup.toGL.comp φ
    have hφGL : Function.Injective φGL := SpecialLinearGroup.toGL_injective.comp hφ
    have hcoe (h : G) : (φ h : GL (Fin 2) ℝ) = φGL h := rfl
    refine φGL.amenable_of_onePoint_measure_singleton_ne_zero hφGL (fun g y ↦ ?_) hx
    have hpre : ((φ g⁻¹ : GL (Fin 2) ℝ) • ·) ⁻¹' {y} = {φGL g • y} := by
      ext z
      rw [mem_preimage, mem_singleton_iff, mem_singleton_iff, hcoe, map_inv,
        inv_smul_eq_iff, eq_comm]
    calc ν {φGL g • y}
        = ν (((φ g⁻¹ : GL (Fin 2) ℝ) • ·) ⁻¹' {y}) := by rw [hpre]
      _ = (Measure.map ((φ g⁻¹ : GL (Fin 2) ℝ) • ·) ν) {y} :=
          (Measure.map_apply (continuous_const_smul _).measurable (measurableSet_singleton y)).symm
      _ = ν {y} := by rw [hν]
  · push Not at hatom
    have : NullSingletonClass ν := ⟨hatom⟩
    have : Finite G := φ.finite_of_nullSingletonClass_of_map_onePoint_measure_eq hfin hν
    exact TauCeti.Amenable.of_finite

/-- Every group embedding in `SL(2, ℤ)` and preserving a Borel probability measure on `OnePoint ℝ`
is amenable for every group topology. -/
theorem amenable_of_injective_slTwo_of_map_onePoint_measure_eq {G : Type*} [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G] (ψ : G →* SL(2, ℤ)) (hψ : Function.Injective ψ)
    {ν : Measure (OnePoint ℝ)} [IsProbabilityMeasure ν]
    (hν : ∀ g : G, Measure.map (SpecialLinearGroup.mapGL ℝ (ψ g) • ·) ν = ν) :
    TauCeti.Amenable G := by
  let φ : G →* SL(2, ℝ) := (SpecialLinearGroup.map (algebraMap ℤ ℝ)).comp ψ
  have hφ : Function.Injective φ :=
    (SpecialLinearGroup.map_injective Int.cast_injective).comp hψ
  refine φ.amenable_of_map_onePoint_measure_eq hφ (fun R ↦ ?_) hν
  -- Integer entries bounded in real absolute value by `R` lie in `[-⌈max R 0⌉, ⌈max R 0⌉]`.
  let cube : Set (Fin 2 → Fin 2 → ℤ) :=
    univ.pi fun _ ↦ univ.pi fun _ ↦ Icc (-⌈max R 0⌉) ⌈max R 0⌉
  have hcube : cube.Finite :=
    Set.Finite.pi fun _ ↦ Set.Finite.pi fun _ ↦ finite_Icc _ _
  have hinj :
      Function.Injective fun g : G ↦ ((ψ g : Matrix (Fin 2) (Fin 2) ℤ) : Fin 2 → Fin 2 → ℤ) :=
    Subtype.val_injective.comp hψ
  refine (hcube.preimage hinj.injOn).subset fun g hg i _ j _ ↦ ?_
  let m : ℤ := (ψ g : Matrix (Fin 2) (Fin 2) ℤ) i j
  have hij : |(m : ℝ)| ≤ max R 0 := by
    have h1 : |(φ g : Matrix (Fin 2) (Fin 2) ℝ) i j| ≤ R := hg i j
    simpa [φ, m] using h1.trans (le_max_left R 0)
  have hB : ((|m| : ℤ) : ℝ) ≤ (⌈max R 0⌉ : ℤ) := by
    rw [Int.cast_abs]
    exact hij.trans (Int.le_ceil _)
  exact abs_le.mp (Int.cast_le.mp hB)

end RealProjectiveLine

end MonoidHom
