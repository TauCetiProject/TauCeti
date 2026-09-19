/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.WeightedRestrictedSeries.Rename
import Mathlib.Data.Finsupp.Interval
import Mathlib.Tactic.LinearCombination
import Mathlib.Topology.Algebra.InfiniteSum.Nonarchimedean
import TauCeti.Topology.Algebra.Nonarchimedean.ZeroAtFilter

/-!
# `A⟨X, Y⟩` modulo `1 - XY`

Let `A` be a nonarchimedean ring and write `j₁, j₂ : A⟨Z⟩ → A⟨X, Y⟩` for the maps of restricted
power series sending `Z` to `X` and to `Y` (`TauCeti.Huber.weightedRename` along
`Fin.castSuccEmb` and `Fin.succEmb 1`). In the proof of Lemma 8.33 Wedhorn considers the row

```text
0 → A → A⟨ζ⟩ × A⟨η⟩ → A⟨ζ, ζ⁻¹⟩ → 0,        λ(g, h) = g(ζ) - h(ζ⁻¹),
```

and in (8.2.1) writes the ring of the overlap as `A⟨ζ, η⟩ ⧸ (f - ζ, 1 - ζη) = A⟨ζ, ζ⁻¹⟩ ⧸ (f - ζ)`.
Read in `A⟨ζ, ζ⁻¹⟩ = A⟨X, Y⟩ ⧸ (1 - XY)`, `λ` is induced by `j₁ - j₂`, and the two facts about the
row that the proof uses become statements about `A⟨X, Y⟩`:

* `A⟨ζ, ζ⁻¹⟩ = A⟨ζ⟩ + ζ⁻¹ A⟨ζ⁻¹⟩`: every `u ∈ A⟨X, Y⟩` is `j₁ a + Y · j₂ b + (1 - XY) · w` with
  `a, b, w` restricted, when `A` is complete and separated;
* `im ι = ker λ`: if `j₁ a - j₂ b = (1 - XY) · w` with `w` restricted, then `a` and `b` are the same
  constant, when `A` is separated.

In the second statement `w` ranges over `A⟨X, Y⟩`, not over all of `A[[X, Y]]`, where `1 - XY` is a
unit.

The same decomposition, read on coefficients rather than in `A⟨X, Y⟩`, is
`TauCeti.Huber.twoSidedRestrictedSubmodule_eq_sup` for two-sided restricted series.

## Main results

* `TauCeti.Huber.exists_eq_weightedRename_add_weightedX_mul_weightedRename_add_one_sub_mul`: the
  decomposition, hence the surjectivity of `λ`.
* `TauCeti.Huber.exists_eq_weightedC_of_weightedRename_sub_weightedRename_eq_one_sub_mul`: the
  kernel of `λ` is the image of `A`.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), (8.2.1) and the proof of
  Lemma 8.33, p. 84. This serves §4.1 step 5 of `TauCetiRoadmap/AdicSpaces/README.md`.

## Provenance

AINTLIB (`github.com/CBirkbeck/AINTLIB`, Apache-2.0) at commit `37bbdaeb9`,
`projects/AdicSpaces/Adic spaces/LaurentCoverExact.lean`, states both facts for its
`LaurentTateAlgebra A := TateAlgebra₂ A ⧸ (XY - 1)`: `ker_lambdaMap_le_range_iotaHom` (the kernel,
with the diagonal-constancy argument used here) and `lambdaMap_surjective` (the decomposition by
diagonal sums, in the variant `j₁ a + j₂ b` with `b` having zero constant term). They were
consulted; nothing was copied. The statements here are about `A⟨X, Y⟩` itself rather than a
quotient, over this repository's `weightedRestrictedSubring`.
-/

public section

open Filter Topology Finsupp MvPowerSeries

namespace TauCeti.Huber

variable {A : Type*} [CommRing A]

/-! ### Renamed series off the image of the variables -/

section Rename

variable {σ τ : Type*}

private theorem coeff_rename_eq_zero_of_apply_ne_zero (e : σ ↪ τ) (p : MvPowerSeries σ A)
    {ν : τ →₀ ℕ} {j : τ} (hj : j ∉ Set.range e) (hν : ν j ≠ 0) : coeff ν (rename e p) = 0 :=
  coeff_rename_eq_zero _ _ fun ⟨s, hs⟩ ↦ hν (hs ▸ mapDomain_of_notMem_range s j hj)

private theorem eq_C_of_rename_eq_rename {e₁ e₂ : σ ↪ τ} (hdisj : ∀ i j, e₁ i ≠ e₂ j)
    {a b : MvPowerSeries σ A} (h : rename e₁ a = rename e₂ b) : a = C (constantCoeff a) := by
  classical
  ext s
  rw [coeff_C]
  split_ifs with hs
  · rw [hs, coeff_zero_eq_constantCoeff_apply]
  obtain ⟨i, hi⟩ := Finsupp.ne_iff.mp hs
  rw [← coeff_embDomain_rename e₁, h, coeff_rename_eq_zero_of_apply_ne_zero e₂ b
    (j := e₁ i) (fun ⟨j, hj⟩ ↦ hdisj i j hj.symm) (by simpa using hi)]

end Rename

/-! ### Sums along a diagonal -/

section DiagonalSum

variable {σ : Type*}

private theorem tendsto_tsum_coeff_add_nsmul [TopologicalSpace A] [NonarchimedeanAddGroup A]
    {u : MvPowerSeries σ A} (hu : Tendsto (coeff · u) cofinite (𝓝 0)) (d : σ →₀ ℕ) :
    Tendsto (fun ν ↦ ∑' n : ℕ, coeff (ν + n • d) u) cofinite (𝓝 0) := by
  classical
  refine NonarchimedeanAddGroup.zeroAtFilter_cofinite_iff_finite_notMem.mpr fun W ↦ ?_
  refine ((NonarchimedeanAddGroup.zeroAtFilter_cofinite_iff_finite_notMem.mp hu W).biUnion
    fun μ _ ↦ Set.finite_Iic μ).subset fun ν hν ↦ ?_
  -- `W` is closed, so a ray sum outside `W` has a term outside `W`, and `ν` lies below its index
  obtain ⟨n, hn⟩ := not_forall.mp (mt (tsum_mem W.isClosed) hν)
  exact Set.mem_biUnion hn (Set.mem_Iic.mpr le_self_add)

private theorem tendsto_coeff_add_nsmul [TopologicalSpace A] {u : MvPowerSeries σ A}
    (hu : Tendsto (coeff · u) cofinite (𝓝 0)) {d : σ →₀ ℕ} (hd : d ≠ 0) (ν : σ →₀ ℕ) :
    Tendsto (fun n : ℕ ↦ coeff (ν + n • d) u) cofinite (𝓝 0) :=
  hu.comp ((nsmul_left_strictMono hd.bot_lt).const_add ν).injective.tendsto_cofinite

private theorem tsum_coeff_add_nsmul_eq [UniformSpace A] [IsUniformAddGroup A]
    [NonarchimedeanAddGroup A] [CompleteSpace A] [T0Space A] {u : MvPowerSeries σ A}
    (hu : Tendsto (coeff · u) cofinite (𝓝 0)) {d : σ →₀ ℕ} (hd : d ≠ 0) (ν : σ →₀ ℕ) :
    ∑' n : ℕ, coeff (ν + n • d) u = coeff ν u + ∑' n : ℕ, coeff (ν + d + n • d) u := by
  simpa [succ_nsmul', add_assoc] using (NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero
    (tendsto_coeff_add_nsmul hu hd ν)).tsum_eq_zero_add

end DiagonalSum

/-! ### Coefficients in two variables -/

/-- The multi-index of `XY`. -/
private noncomputable abbrev diagStep : Fin 2 →₀ ℕ := single 0 1 + single 1 1

private theorem index_cases (ν : Fin 2 →₀ ℕ) :
    (∃ μ, ν = μ + diagStep) ∨ (∃ s : Fin 1 →₀ ℕ, ν = embDomain Fin.castSuccEmb s) ∨
      ∃ s : Fin 1 →₀ ℕ, ν = embDomain (Fin.succEmb 1) s + single 1 1 := by
  simp only [Finsupp.ext_iff, Fin.forall_fin_two]
  rcases ν 1 with _ | k
  · -- on the `X`-axis
    exact .inr (.inl ⟨single 0 (ν 0), by simp⟩)
  rcases ν 0 with _ | m
  · -- on the `Y`-axis, away from the origin
    exact .inr (.inr ⟨single 0 k, by simp⟩)
  · -- off both axes
    exact .inl ⟨single 0 m + single 1 k, by simp⟩

private theorem coeff_one_sub_X_mul_X_mul (w : MvPowerSeries (Fin 2) A) (ν : Fin 2 →₀ ℕ) :
    coeff ν ((1 - X 0 * X 1) * w) =
      coeff ν w - if diagStep ≤ ν then coeff (ν - diagStep) w else 0 := by
  simp [sub_mul, X_def, monomial_mul_monomial, coeff_monomial_mul]

private theorem coeff_rename_castSuccEmb_eq_zero (p : MvPowerSeries (Fin 1) A) {ν : Fin 2 →₀ ℕ}
    (hν : ν 1 ≠ 0) : coeff ν (rename Fin.castSuccEmb p) = 0 :=
  coeff_rename_eq_zero_of_apply_ne_zero _ p (by simp) hν

private theorem coeff_rename_succEmb_eq_zero (p : MvPowerSeries (Fin 1) A) {ν : Fin 2 →₀ ℕ}
    (hν : ν 0 ≠ 0) : coeff ν (rename (Fin.succEmb 1) p) = 0 :=
  coeff_rename_eq_zero_of_apply_ne_zero _ p (by simp) hν

private theorem coeff_X_one_mul_rename_succEmb_eq_zero (p : MvPowerSeries (Fin 1) A)
    {ν : Fin 2 →₀ ℕ} (hν : ν 0 ≠ 0) : coeff ν (X 1 * rename (Fin.succEmb 1) p) = 0 := by
  rw [X_def, coeff_monomial_mul, one_mul, ite_eq_right_iff]
  exact fun _ ↦ coeff_rename_succEmb_eq_zero p (by simpa using hν)

private theorem coeff_add_single_X_one_mul (q : MvPowerSeries (Fin 2) A) (μ : Fin 2 →₀ ℕ) :
    coeff (μ + single 1 1) (X 1 * q) = coeff μ q := by
  rw [add_comm, X_def, coeff_add_monomial_mul, one_mul]

private theorem coeff_add_diagStep_one_sub_X_mul_X_mul (w : MvPowerSeries (Fin 2) A)
    (μ : Fin 2 →₀ ℕ) :
    coeff (μ + diagStep) ((1 - X 0 * X 1) * w) = coeff (μ + diagStep) w - coeff μ w := by
  rw [coeff_one_sub_X_mul_X_mul, ite_eq_left le_add_self, add_tsub_cancel_right]

private theorem coeff_one_sub_X_mul_X_mul_of_eq_zero (w : MvPowerSeries (Fin 2) A) {ν : Fin 2 →₀ ℕ}
    (hν : ν 0 = 0 ∨ ν 1 = 0) : coeff ν ((1 - X 0 * X 1) * w) = coeff ν w := by
  rw [coeff_one_sub_X_mul_X_mul, ite_eq_right, sub_zero]
  rcases hν with hν | hν <;> simp [Finsupp.le_def, Fin.forall_fin_two, hν]

/-! ### The two statements for power series -/

private theorem eq_rename_add_X_mul_rename_add_one_sub_mul_of_coeff_eq
    {u w : MvPowerSeries (Fin 2) A} {a b : MvPowerSeries (Fin 1) A} {S : (Fin 2 →₀ ℕ) → A}
    (hS : ∀ ν, S ν = coeff ν u + S (ν + diagStep))
    (ha : ∀ s, coeff s a = S (embDomain Fin.castSuccEmb s))
    (hb : ∀ s, coeff s b = S (embDomain (Fin.succEmb 1) s + single 1 1))
    (hw : ∀ ν, coeff ν w = -S (ν + diagStep)) :
    u = rename Fin.castSuccEmb a + X 1 * rename (Fin.succEmb 1) b + (1 - X 0 * X 1) * w := by
  ext ν
  rw [map_add, map_add]
  rcases index_cases ν with ⟨μ, rfl⟩ | ⟨s, rfl⟩ | ⟨s, rfl⟩
  · -- off both axes, only `w` contributes
    rw [coeff_rename_castSuccEmb_eq_zero _ (by simp),
      coeff_X_one_mul_rename_succEmb_eq_zero _ (by simp),
      coeff_add_diagStep_one_sub_X_mul_X_mul, hw, hw]
    linear_combination -hS (μ + diagStep)
  · -- on the `X`-axis, `a` and `w` contribute
    rw [coeff_embDomain_rename,
      X_dvd_iff.mp (dvd_mul_right _ _) _ (by simp [embDomain_of_notMem_range]),
      coeff_one_sub_X_mul_X_mul_of_eq_zero _ (.inr (by simp [embDomain_of_notMem_range])), ha, hw]
    linear_combination -hS (embDomain Fin.castSuccEmb s)
  · -- on the `Y`-axis away from the origin, `b` and `w` contribute
    rw [coeff_rename_castSuccEmb_eq_zero _ (by simp), coeff_add_single_X_one_mul,
      coeff_embDomain_rename,
      coeff_one_sub_X_mul_X_mul_of_eq_zero _ (.inl (by simp [embDomain_of_notMem_range])), hb, hw]
    linear_combination -hS (embDomain (Fin.succEmb 1) s + single 1 1)

private theorem exists_eq_rename_add_X_mul_rename_add_one_sub_mul [UniformSpace A]
    [IsUniformAddGroup A] [NonarchimedeanAddGroup A] [CompleteSpace A] [T0Space A]
    {u : MvPowerSeries (Fin 2) A} (hu : Tendsto (coeff · u) cofinite (𝓝 0)) :
    ∃ a b : MvPowerSeries (Fin 1) A, ∃ w : MvPowerSeries (Fin 2) A,
      Tendsto (coeff · a) cofinite (𝓝 0) ∧ Tendsto (coeff · b) cofinite (𝓝 0) ∧
      Tendsto (coeff · w) cofinite (𝓝 0) ∧
      u = rename Fin.castSuccEmb a + X 1 * rename (Fin.succEmb 1) b + (1 - X 0 * X 1) * w := by
  -- `S ν` sums the coefficients of `u` along the diagonal ray from `ν`; `a` reads `S` on the
  -- `X`-axis, `b` on the `Y`-axis past the origin, and `-w` one diagonal step further on
  set S : (Fin 2 →₀ ℕ) → A := fun ν ↦ ∑' n : ℕ, coeff (ν + n • diagStep) u
  have hSt : Tendsto S cofinite (𝓝 0) := tendsto_tsum_coeff_add_nsmul hu diagStep
  exact ⟨fun s ↦ S (embDomain Fin.castSuccEmb s),
    fun s ↦ S (embDomain (Fin.succEmb 1) s + single 1 1), fun ν ↦ -S (ν + diagStep),
    hSt.comp (embDomain_injective _).tendsto_cofinite,
    hSt.comp ((add_left_injective _).comp (embDomain_injective _)).tendsto_cofinite,
    ZeroAtFilter.neg (hSt.comp (add_left_injective diagStep).tendsto_cofinite),
    eq_rename_add_X_mul_rename_add_one_sub_mul_of_coeff_eq (tsum_coeff_add_nsmul_eq hu (by simp))
      (fun _ ↦ rfl) (fun _ ↦ rfl) (fun _ ↦ rfl)⟩

private theorem eq_zero_of_rename_sub_rename_eq_one_sub_mul [TopologicalSpace A] [T1Space A]
    {a b : MvPowerSeries (Fin 1) A} {w : MvPowerSeries (Fin 2) A}
    (hw : Tendsto (coeff · w) cofinite (𝓝 0))
    (h : rename Fin.castSuccEmb a - rename (Fin.succEmb 1) b = (1 - X 0 * X 1) * w) : w = 0 := by
  -- off both axes the series in `X` and in `Y` vanish, so the coefficients of `w` are constant
  -- along every diagonal
  have hstep : Function.Periodic (coeff · w) diagStep := fun μ ↦ sub_eq_zero.mp <| by
    rw [← coeff_add_diagStep_one_sub_X_mul_X_mul, ← h, map_sub,
      coeff_rename_castSuccEmb_eq_zero _ (by simp), coeff_rename_succEmb_eq_zero _ (by simp),
      sub_zero]
  ext μ
  -- along the diagonal through `μ` they also tend to zero, so in the T1 space `A` they are zero
  simpa using tendsto_const_nhds_iff.mp
    ((tendsto_coeff_add_nsmul hw (by simp) μ).congr fun n ↦ hstep.nsmul n μ)

private theorem exists_eq_C_of_rename_sub_rename_eq_one_sub_mul [TopologicalSpace A] [T1Space A]
    {a b : MvPowerSeries (Fin 1) A} {w : MvPowerSeries (Fin 2) A}
    (hw : Tendsto (coeff · w) cofinite (𝓝 0))
    (h : rename Fin.castSuccEmb a - rename (Fin.succEmb 1) b = (1 - X 0 * X 1) * w) :
    ∃ c : A, a = C c ∧ b = C c := by
  -- `w = 0`, and a series in `X` that is also a series in `Y` is constant
  rw [eq_zero_of_rename_sub_rename_eq_one_sub_mul hw h, mul_zero, sub_eq_zero] at h
  have ha := eq_C_of_rename_eq_rename (by decide) h
  exact ⟨_, ha, rename_injective (Fin.succEmb 1) (by rw [← h, ha]; simp)⟩

/-! ### The two statements in `A⟨X, Y⟩` -/

/-- **Every element of `A⟨X, Y⟩` is `a(X) + Y · b(Y)` modulo `1 - XY`**, with `a, b ∈ A⟨Z⟩` and
the multiple of `1 - XY` restricted, when `A` is complete and separated. This is Wedhorn's
`A⟨ζ, ζ⁻¹⟩ = A⟨ζ⟩ + ζ⁻¹ A⟨ζ⁻¹⟩` in the proof of Lemma 8.33, the surjectivity of `λ`; its kernel is
`TauCeti.Huber.exists_eq_weightedC_of_weightedRename_sub_weightedRename_eq_one_sub_mul`. -/
theorem exists_eq_weightedRename_add_weightedX_mul_weightedRename_add_one_sub_mul [UniformSpace A]
    [IsUniformAddGroup A] [NonarchimedeanRing A] [CompleteSpace A] [T0Space A]
    (u : weightedRestrictedSubring (fun _ : Fin 2 ↦ ({1} : Set A)) isWeightFamily_one_weight) :
    ∃ (a b : weightedRestrictedSubring (fun _ : Fin 1 ↦ ({1} : Set A)) isWeightFamily_one_weight)
      (w : weightedRestrictedSubring (fun _ : Fin 2 ↦ ({1} : Set A)) isWeightFamily_one_weight),
      u = weightedRename Fin.castSuccEmb isWeightFamily_one_weight isWeightFamily_one_weight
            (fun _ ↦ subset_rfl) a +
          weightedX _ isWeightFamily_one_weight 1 *
            weightedRename (Fin.succEmb 1) isWeightFamily_one_weight isWeightFamily_one_weight
              (fun _ ↦ subset_rfl) b +
          (1 - weightedX _ isWeightFamily_one_weight 0 * weightedX _ isWeightFamily_one_weight 1) *
            w := by
  obtain ⟨a, b, w, ha, hb, hw, h⟩ := exists_eq_rename_add_X_mul_rename_add_one_sub_mul
    (isWeightedRestricted_one_weight_iff.mp (mem_weightedRestrictedSubring.mp u.2))
  refine ⟨⟨a, ?_⟩, ⟨b, ?_⟩, ⟨w, ?_⟩, Subtype.ext <| by simpa using h⟩ <;>
    simpa [isWeightedRestricted_one_weight_iff]

/-- **A series in `X` and a series in `Y` that agree modulo `1 - XY` in `A⟨X, Y⟩` are the same
constant**: if `a(X) - b(Y) = (1 - XY) · w` with `a, b ∈ A⟨Z⟩` and `w ∈ A⟨X, Y⟩`, then
`a = b = c` for some `c ∈ A`, when `A` is separated. This is the inclusion `ker λ ⊆ im ι` in the
proof of Wedhorn's Lemma 8.33; the other inclusion follows from
`TauCeti.Huber.weightedRename_weightedC`. -/
theorem exists_eq_weightedC_of_weightedRename_sub_weightedRename_eq_one_sub_mul [TopologicalSpace A]
    [NonarchimedeanRing A] [T0Space A]
    {a b : weightedRestrictedSubring (fun _ : Fin 1 ↦ ({1} : Set A)) isWeightFamily_one_weight}
    {w : weightedRestrictedSubring (fun _ : Fin 2 ↦ ({1} : Set A)) isWeightFamily_one_weight}
    (h : weightedRename Fin.castSuccEmb isWeightFamily_one_weight isWeightFamily_one_weight
          (fun _ ↦ subset_rfl) a -
        weightedRename (Fin.succEmb 1) isWeightFamily_one_weight isWeightFamily_one_weight
          (fun _ ↦ subset_rfl) b =
      (1 - weightedX _ isWeightFamily_one_weight 0 * weightedX _ isWeightFamily_one_weight 1) * w) :
    ∃ c : A, a = weightedC _ isWeightFamily_one_weight c ∧
      b = weightedC _ isWeightFamily_one_weight c := by
  obtain ⟨c, ha, hb⟩ := exists_eq_C_of_rename_sub_rename_eq_one_sub_mul (a := a) (b := b)
    (isWeightedRestricted_one_weight_iff.mp (mem_weightedRestrictedSubring.mp w.2))
    (by simpa using congrArg Subtype.val h)
  exact ⟨c, Subtype.ext (by simp [ha]), Subtype.ext (by simp [hb])⟩

end TauCeti.Huber
