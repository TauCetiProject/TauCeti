/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
public import Mathlib.FieldTheory.Relrank
public import TauCeti.Algebra.Algebra.Subalgebra.Lattice

/-!
# Degrees of composita of intermediate fields

The degree of the compositum of two intermediate fields is at most the product of their degrees
(`IntermediateField.finrank_sup_le`). This file iterates that bound over finitely many
intermediate fields, and deduces that adjoining finitely many elements gives an extension of
degree at most the product of the degrees of their minimal polynomials.

Neither bound needs an algebraicity hypothesis: an infinite-dimensional compositum has `finrank`
equal to `0`, and so does the minimal polynomial of a transcendental element.

Along a nested sequence of intermediate fields `Eₙ`, the relative degree `[Eₙ(M) : Eₙ]` of the
compositum with a fixed finite extension `M` can only decrease, so it stabilizes: the degrees
`[Eₙ(M) : K]` are ultimately a fixed positive multiple of the degrees `[Eₙ : K]`. No normality
assumption is needed.

The file also shows that degrees of composita descend to finite subextensions: if `L / K` is
algebraic and `F` is a finite subextension of `M / K`, then `[L(F) : L]` is already attained as
`[L₀(F) : L₀]` for some finite subextension `L₀` of `L / K`. Unlike the bounds above, this
result needs the algebraicity hypothesis. It is the step used in the tower law for
`P`-extensions.

## Main results

* `IntermediateField.finrank_biSup_le_prod`, `IntermediateField.finrank_iSup_le_prod`:
  `[⨆ i, Eᵢ : K] ≤ ∏ i, [Eᵢ : K]` for finitely many intermediate fields `Eᵢ`.
* `IntermediateField.finrank_adjoin_range_le_prod`: `[K(x₁, …, xₙ) : K] ≤ ∏ i, deg xᵢ`.
* `IntermediateField.relfinrank_sup_le_of_le`: if `A ≤ B` with `[B : A]` finite, then
  `[B(M) : B] ≤ [A(M) : A]`.
* `IntermediateField.exists_finrank_sup_eq_mul_finrank`: along a nested sequence `Eₙ`, eventually
  `[Eₙ(M) : K] = c * [Eₙ : K]` for a fixed `c` with `1 ≤ c ≤ [M : K]`.
* `IntermediateField.finrank_adjoin_eq_finrank_span`: if `s` spans the algebraic intermediate field
  `F` over `K`, then `[A(F) : A]` is the dimension of the `A`-span of `s`.
* `IntermediateField.exists_finiteDimensional_finrank_adjoin_eq`: for an algebraic extension
  `L / K` inside `M` and a finite subextension `F` of `M / K`, some finite subextension `L₀` of
  `L / K` has `[L₀(F) : L₀] = [L(F) : L]`.
-/

public section

open Module

namespace IntermediateField

variable {K L : Type*} [Field K] [Field L] [Algebra K L] {ι : Type*}

/-- The degree of the compositum of the intermediate fields `Eᵢ`, `i ∈ s`, is at most the product
of their degrees. -/
theorem finrank_biSup_le_prod (E : ι → IntermediateField K L) (s : Finset ι) :
    finrank K ↥(⨆ i ∈ s, E i) ≤ ∏ i ∈ s, finrank K (E i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [show ⨆ i ∈ (∅ : Finset ι), E i = ⊥ by simp, IntermediateField.finrank_bot,
      Finset.prod_empty]
  | insert a s ha ih =>
    rw [Finset.iSup_insert, Finset.prod_insert ha]
    exact (finrank_sup_le _ _).trans (Nat.mul_le_mul_left _ ih)

/-- The degree of the compositum of finitely many intermediate fields `Eᵢ` is at most the product
of their degrees. -/
theorem finrank_iSup_le_prod [Fintype ι] (E : ι → IntermediateField K L) :
    finrank K ↥(⨆ i, E i) ≤ ∏ i, finrank K (E i) := by
  rw [show ⨆ i, E i = ⨆ i ∈ Finset.univ, E i by simp]
  exact finrank_biSup_le_prod E Finset.univ

/-- Adjoining finitely many elements `xᵢ` gives an extension of degree at most the product of the
degrees of their minimal polynomials. If some `xᵢ` is transcendental, both sides are `0`. -/
theorem finrank_adjoin_range_le_prod [Fintype ι] (x : ι → L) :
    finrank K (adjoin K (Set.range x)) ≤ ∏ i, (minpoly K (x i)).natDegree := by
  rw [← Set.iUnion_singleton_eq_range, adjoin_iUnion]
  refine (finrank_iSup_le_prod _).trans (Finset.prod_le_prod fun i _ ↦ ?_)
  by_cases hx : IsIntegral K (x i)
  · exact (adjoin.finrank hx).le
  · -- A transcendental element generates an infinite-dimensional extension.
    have : ¬FiniteDimensional K K⟮x i⟯ := fun h ↦ hx <| by
      simpa using (IsIntegral.of_finite K (AdjoinSimple.gen K (x i))).map (val K⟮x i⟯)
    rw [finrank_of_not_finite this]
    exact Nat.zero_le _

section Tower

/-- A finite enlargement of the base cannot increase the relative degree of a compositum. -/
theorem relfinrank_sup_le_of_le {A B M : IntermediateField K L} (hAB : A ≤ B)
    (hpos : 0 < A.relfinrank B) : B.relfinrank (B ⊔ M) ≤ A.relfinrank (A ⊔ M) := by
  have hsup : B ⊔ (A ⊔ M) = B ⊔ M := by
    rw [← sup_assoc, sup_eq_left.mpr hAB]
  have hdeg := finrank_sup_le (extendScalars hAB) (extendScalars (le_sup_left : A ≤ A ⊔ M))
  rw [extendScalars_sup] at hdeg
  simp only [← relfinrank_eq_finrank_of_le, hsup] at hdeg
  rw [← relfinrank_mul_relfinrank hAB (le_sup_left : B ≤ B ⊔ M)] at hdeg
  exact Nat.le_of_mul_le_mul_left hdeg hpos

/-- Over a nested sequence of extensions, the degree of the compositum with a fixed finite
extension `M` is ultimately a fixed positive multiple of the degree of the base layer.
If a layer has infinite degree, both finranks are zero from that layer onward. -/
theorem exists_finrank_sup_eq_mul_finrank (M : IntermediateField K L) [FiniteDimensional K M]
    (E : ℕ → IntermediateField K L) (hE : Monotone E) :
    ∃ c : ℕ, 1 ≤ c ∧ c ≤ Module.finrank K M ∧ ∃ n₀ : ℕ, ∀ n ≥ n₀,
      Module.finrank K ↥(E n ⊔ M) = c * Module.finrank K (E n) := by
  classical
  by_cases hInf : ∃ n, ¬ FiniteDimensional K (E n)
  · obtain ⟨n₀, hn₀⟩ := hInf
    refine ⟨1, le_rfl, Module.finrank_pos, n₀, fun n hn ↦ ?_⟩
    have finrank_eq_zero (F : IntermediateField K L) (hF : E n₀ ≤ F) :
        Module.finrank K F = 0 := by
      apply Module.finrank_of_infinite_dimensional
      intro h
      exact hn₀ (FiniteDimensional.of_injective (inclusion hF).toLinearMap (inclusion hF).injective)
    rw [finrank_eq_zero _ (hE hn), finrank_eq_zero _ ((hE hn).trans le_sup_left), mul_zero]
  have : ∀ n, FiniteDimensional K (E n) := fun n ↦ not_not.mp (fun hn ↦ hInf ⟨n, hn⟩)
  let f (n : ℕ) := (E n).relfinrank (E n ⊔ M)
  have hanti : Antitone f := fun i j h ↦
    relfinrank_sup_le_of_le (hE h)
      (Nat.pos_of_dvd_of_pos ((E i).relfinrank_dvd_finrank_bot (E j)) Module.finrank_pos)
  let he : ∃ c : ℕ, c ∈ Set.range f := ⟨f 0, 0, rfl⟩
  obtain ⟨n₀, hn₀⟩ := Nat.find_spec he
  have h₀ (n : ℕ) (hn : n₀ ≤ n) : f n = f n₀ :=
    (hanti hn).antisymm (hn₀ ▸ Nat.find_min' he (Set.mem_range_self n))
  have hdeg (n : ℕ) : Module.finrank K ↥(E n ⊔ M) = Module.finrank K (E n) * f n :=
    (finrank_bot_mul_relfinrank le_sup_left).symm
  have hpos : 1 ≤ f n₀ := by
    have hdim := Module.finrank_pos (R := K) (M := ↥(E n₀ ⊔ M))
    by_contra! hn
    have hz : f n₀ = 0 := Nat.lt_one_iff.mp hn
    simp [hdeg, hz] at hdim
  have hbound : f n₀ ≤ Module.finrank K M := by
    refine (relfinrank_sup_le_of_le (M := M) (bot_le : ⊥ ≤ E n₀) ?_).trans_eq ?_
    · simpa using (Module.finrank_pos : 0 < Module.finrank K (E n₀))
    · simp
  exact ⟨f n₀, hpos, hbound, n₀, fun n hn ↦ by rw [hdeg, h₀ n hn, mul_comm]⟩

end Tower

section Descent

variable {M : Type*} [Field M] [Algebra K M] [Algebra L M] [IsScalarTower K L M]

/-- If `s` spans the algebraic intermediate field `F` of `M / K` over `K`, then `[A(F) : A]` is
the dimension of the `A`-span of `s`, for every field `A` between `K` and `M`. -/
theorem finrank_adjoin_eq_finrank_span {A : Type*} [Field A] [Algebra K A] [Algebra A M]
    [IsScalarTower K A M] (F : IntermediateField K M) [Algebra.IsAlgebraic K F] {s : Set M}
    (hs : Submodule.span K s = Subalgebra.toSubmodule F.toSubalgebra) :
    finrank A (adjoin A (F : Set M)) = finrank A (Submodule.span A s) := by
  have hF : (F : Set M) = Submodule.span K s := by
    rw [hs, Subalgebra.coe_toSubmodule, IntermediateField.coe_toSubalgebra]
  rw [← finrank_eq_finrank_subalgebra, ← Subalgebra.finrank_toSubmodule,
    adjoin_intermediateField_toSubalgebra_of_isAlgebraic_right, Algebra.adjoin_coe_eq_span, hF,
    Submodule.span_span_of_tower]

/-- **Descent of the degree of a compositum.** Let `L / K` be algebraic, with `L ⊆ M`, and let `F`
be a finite subextension of `M / K`. Then some finite subextension `L₀` of `L / K` satisfies
`[L₀(F) : L₀] = [L(F) : L]`.

The hypothesis that `L / K` is algebraic is needed: for `K = 𝔽_p(x, y)` and
`L = K(t, (x + tᵖy)^{1/p})`, the field `K` is algebraically closed in `L`, while
`F = K(x^{1/p}, y^{1/p})` has `[L(F) : L] = p < p² = [F : K]`. -/
theorem exists_finiteDimensional_finrank_adjoin_eq [Algebra.IsAlgebraic K L]
    (F : IntermediateField K M) [FiniteDimensional K F] :
    ∃ L₀ : IntermediateField K L, FiniteDimensional K L₀ ∧
      finrank L₀ (adjoin L₀ (F : Set M)) = finrank L (adjoin L (F : Set M)) := by
  classical
  -- Take a finite `K`-spanning set `s` of `F` and a subset `b ⊆ s` that is an `L`-basis of
  -- `L(F)`; then `L₀` is generated by the coordinates in `b` of the elements of `s`.
  have hfin : Module.Finite K (Subalgebra.toSubmodule F.toSubalgebra) :=
    FiniteDimensional.subalgebra_toSubmodule inferInstance
  obtain ⟨s, hs, hsF⟩ := Submodule.fg_def.1 (Module.Finite.iff_fg.1 hfin)
  obtain ⟨b, hbs, hspan, hli⟩ := exists_linearIndependent L s
  have hb : b.Finite := hs.subset hbs
  have hc (x : s) : ∃ c : M → L, ∑ y ∈ hb.toFinset, c y • y = x := by
    refine (Submodule.mem_span_finset.1 ?_).imp fun _ h ↦ h.2
    rw [hb.coe_toFinset, hspan]
    exact Submodule.subset_span x.property
  choose c hcx using hc
  have : Finite s := hs.to_subtype
  let L₀ := adjoin K (Set.range fun p : s × hb.toFinset ↦ c p.1 p.2)
  have hL₀ : FiniteDimensional K L₀ :=
    finiteDimensional_adjoin fun x _ ↦ Algebra.IsIntegral.isIntegral x
  refine ⟨L₀, hL₀, ?_⟩
  have hspan₀ : Submodule.span L₀ s = Submodule.span L₀ b := by
    refine le_antisymm (Submodule.span_le.2 fun x hx ↦ ?_) (Submodule.span_mono hbs)
    have hsum : ∑ y ∈ hb.toFinset, c ⟨x, hx⟩ y • y = x := hcx ⟨x, hx⟩
    rw [SetLike.mem_coe, ← hsum]
    refine Submodule.sum_mem _ fun y hy ↦ ?_
    have hmem : c ⟨x, hx⟩ y ∈ L₀ := subset_adjoin K _ ⟨(⟨x, hx⟩, ⟨y, hy⟩), rfl⟩
    exact Submodule.smul_of_tower_mem _ (⟨_, hmem⟩ : L₀)
      (Submodule.subset_span (hb.mem_toFinset.1 hy))
  rw [finrank_adjoin_eq_finrank_span F hsF, finrank_adjoin_eq_finrank_span F hsF, hspan₀,
    ← hspan, finrank_span_set_eq_ncard hli,
    finrank_span_set_eq_ncard (hli.restrict_scalars' (R := L₀))]

end Descent

end IntermediateField
