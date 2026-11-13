/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.FiniteType
import Mathlib.Data.Fintype.Order
import TauCeti.Algebra.BigOperators.Finset.Range
import TauCeti.Algebra.MvPolynomial.Monad
import TauCeti.RingTheory.AdicCompletion.Nilpotent

/-!
# The Monsky–Washnitzer weak completion

Let `O` be a commutative ring, `π ∈ O`, and `S` a finitely generated `O`-algebra with
`π`-adic completion `S^∧ = lim_m S ⧸ πᵐ S`. Choose generators `x₁, …, xₙ` of `S`. The *weak
completion* `S† ⊆ S^∧` of Monsky and Washnitzer consists of the elements

```text
z = ∑_{j ≥ 0} πʲ Pⱼ(x₁, …, xₙ),   Pⱼ ∈ O[X₁, …, Xₙ],   deg Pⱼ ≤ c (j + 1)
```

for some constant `c`, the series converging `π`-adically. Membership is stated through the
truncations: the image of `z` in `S ⧸ πᵏ S` is the partial sum over `j < k`. Over a complete
discrete valuation ring `O` with uniformiser `π`, Monsky and Washnitzer describe these as the
images of the overconvergent series with integral coefficients
(`TauCeti.Dagger.intWashnitzerAlgebra`) under `Xᵢ ↦ xᵢ`. In that setting, for a smooth
`O`-algebra `S`, the de Rham cohomology of `S† ⊗_O K`, where `K` is the fraction field of `O`,
is the Monsky–Washnitzer cohomology of the reduction `S ⊗_O k` over the residue field `k`.

The growth condition is invariant under a change of generators. If every `xᵢ` is a polynomial of
degree at most `D` in other generators `y`, then `Pⱼ(x) = Qⱼ(y)` with `deg Qⱼ ≤ D c (j + 1)`
(`MvPolynomial.totalDegree_bind₁_le`). Truncated products of such series are the truncations of
their Cauchy products, so the degree-growth set is closed under multiplication. Hence `S†` is
an `O`-subalgebra of `S^∧` which does not depend on the chosen generators.

Nothing here assumes that `O` is a discrete valuation ring or that `π` is a uniformiser. For
`π = 0` the map `S → S^∧` is bijective, so `S† = S^∧` by `weakCompletion_eq_top_of_surjective`; for
`π` a unit the completion is the zero ring.

## Main definitions

* `TauCeti.Dagger.piAdicCompletion π S`: the `π`-adic completion `S^∧` of `S`.
* `TauCeti.Dagger.weakCompletionSet π x`: the elements of `S^∧` with a degree-growth expansion
  in a family `x` of elements of `S`.
* `TauCeti.Dagger.weakCompletion π S`: the weak completion `S†`, the subalgebra of `S^∧` given by
  the degree-growth set of a chosen finite generating family.
* `TauCeti.Dagger.weakCompletion.of π S`: the map `S → S†`.

## Main results

* `TauCeti.Dagger.weakCompletionSet_subset_of_forall_mem_adjoin`: the degree-growth set grows
  along a change of generators.
* `TauCeti.Dagger.coe_weakCompletion`: `S†` is the degree-growth set of every finite generating
  family of `S`; in particular it does not depend on the generators.
* `TauCeti.Dagger.algebraMap_mem_weakCompletion`: `S†` contains the image of `S`.
* `TauCeti.Dagger.weakCompletion.of_injective_iff`: `S → S†` is injective iff `S` is
  `π`-adically separated.
* `TauCeti.Dagger.weakCompletion_eq_top_of_surjective`: if `S → S^∧` is surjective, `S† = S^∧`.
* `TauCeti.Dagger.weakCompletion_eq_top_of_finite` and
  `TauCeti.Dagger.weakCompletion_self_eq_top`: if `S` is module-finite over `O` (in particular for
  `S = O`), `S† = S^∧`.
* `TauCeti.Dagger.weakCompletion.of_bijective_of_isAdicComplete` and
  `TauCeti.Dagger.weakCompletion.of_bijective_of_isNilpotent`: if `S` is `π`-adically complete (in
  particular if the image of `π` in `S` is nilpotent), `S → S†` is bijective.
* `TauCeti.Dagger.weakCompletion.of_bijective_iff_of_finite` and
  `TauCeti.Dagger.weakCompletion.of_self_bijective_iff`: for module-finite `S` over `O` (in
  particular for `S = O`), `S → S†` is bijective iff `S` is `π`-adically complete.

## References

* P. Monsky and G. Washnitzer, *Formal cohomology. I*, Ann. of Math. 88 (1968), §2.
* M. van der Put, *The cohomology of Monsky and Washnitzer*, Mém. Soc. Math. France 23 (1986),
  §2.
* K. Kedlaya, *Counting points on hyperelliptic curves using Monsky–Washnitzer cohomology*,
  J. Ramanujan Math. Soc. 16 (2001), §2.
-/

public section

namespace TauCeti.Dagger

open Finset MvPolynomial

variable {O : Type*} [CommRing O] (π : O) (S : Type*) [CommRing S] [Algebra O S]

/-- The `π`-adic completion `S^∧ = lim_m S ⧸ πᵐ S` of an `O`-algebra `S`. -/
abbrev piAdicCompletion : Type _ :=
  AdicCompletion (Ideal.span {algebraMap O S π}) S

variable {S}

/-- The degree-growth set of a family `x` of elements of `S`: the elements `z` of the `π`-adic
completion with an expansion `z = ∑ⱼ πʲ Pⱼ(x)` for polynomials `Pⱼ` of total degree at most
`c (j + 1)`, for some `c`. The expansion is recorded by its truncations: the image of `z` in
`S ⧸ πᵏ S` is the partial sum over `j < k`. -/
def weakCompletionSet {ι : Type*} (x : ι → S) : Set (piAdicCompletion π S) :=
  {z | ∃ (c : ℕ) (P : ℕ → MvPolynomial ι O), (∀ j, (P j).totalDegree ≤ c * (j + 1)) ∧
    ∀ k, AdicCompletion.evalₐ _ k z =
      Ideal.Quotient.mk _ (∑ j ∈ range k, algebraMap O S π ^ j * aeval x (P j))}

section WeakCompletionSet

variable {π} {ι : Type*} {x : ι → S} {z z' : piAdicCompletion π S}

theorem mem_weakCompletionSet_iff :
    z ∈ weakCompletionSet π x ↔
      ∃ (c : ℕ) (P : ℕ → MvPolynomial ι O), (∀ j, (P j).totalDegree ≤ c * (j + 1)) ∧
        ∀ k, AdicCompletion.evalₐ _ k z =
          Ideal.Quotient.mk _ (∑ j ∈ range k, algebraMap O S π ^ j * aeval x (P j)) :=
  Iff.rfl

variable (π) in
/-- The image of every element of the subalgebra generated by `x` has a degree-growth
expansion in `x`, with a single nonzero term. -/
theorem algebraMap_mem_weakCompletionSet_of_mem_adjoin {s : S}
    (hs : s ∈ Algebra.adjoin O (Set.range x)) :
    algebraMap S (piAdicCompletion π S) s ∈ weakCompletionSet π x := by
  rw [Algebra.adjoin_range_eq_range_aeval] at hs
  obtain ⟨Q, rfl⟩ := hs
  refine ⟨Q.totalDegree, fun j ↦ if j = 0 then Q else 0, fun j ↦ ?_, fun k ↦ ?_⟩
  · rcases j with _ | j <;> simp
  · rw [AdicCompletion.algebraMap_apply, Algebra.algebraMap_self_apply, AdicCompletion.evalₐ_of]
    rcases k with _ | k
    · rw [Ideal.Quotient.eq]
      simp
    · simp [Finset.sum_range_succ']

variable (π x) in
theorem algebraMap_mem_weakCompletionSet (a : O) :
    algebraMap O (piAdicCompletion π S) a ∈ weakCompletionSet π x := by
  simpa [AdicCompletion.algebraMap_apply] using
    algebraMap_mem_weakCompletionSet_of_mem_adjoin π
      (algebraMap_mem (Algebra.adjoin O (Set.range x)) a)

theorem add_mem_weakCompletionSet (hz : z ∈ weakCompletionSet π x)
    (hz' : z' ∈ weakCompletionSet π x) : z + z' ∈ weakCompletionSet π x := by
  obtain ⟨c, P, hP, hz⟩ := hz
  obtain ⟨c', P', hP', hz'⟩ := hz'
  refine ⟨c + c', P + P', fun j ↦ ?_, fun k ↦ ?_⟩
  · refine (totalDegree_add _ _).trans (max_le ((hP j).trans ?_) ((hP' j).trans ?_)) <;>
      gcongr <;> omega
  · simp [hz k, hz' k, mul_add, sum_add_distrib]

/-- The degree-growth set is closed under multiplication: the product of two expansions is
the expansion whose terms are the Cauchy products of their terms. -/
theorem mul_mem_weakCompletionSet (hz : z ∈ weakCompletionSet π x)
    (hz' : z' ∈ weakCompletionSet π x) : z * z' ∈ weakCompletionSet π x := by
  obtain ⟨c, P, hP, hz⟩ := hz
  obtain ⟨c', P', hP', hz'⟩ := hz'
  refine ⟨c + c', fun j ↦ ∑ ab ∈ antidiagonal j, P ab.1 * P' ab.2, fun j ↦ ?_, fun k ↦ ?_⟩
  · refine (totalDegree_finsetSum _ _).trans (Finset.sup_le fun ab hab ↦ ?_)
    rw [mem_antidiagonal] at hab
    refine (totalDegree_mul _ _).trans ((add_le_add (hP ab.1) (hP' ab.2)).trans ?_)
    rw [add_mul]
    gcongr <;> omega
  · have hπ :
        Ideal.Quotient.mk (Ideal.span {algebraMap O S π} ^ k) (algebraMap O S π) ^ k = 0 := by
      rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.pow_mem_pow (Ideal.subset_span rfl) k
    rw [map_mul, hz k, hz' k]
    simp only [map_sum, map_mul, map_pow]
    exact TauCeti.sum_range_pow_mul_mul_sum_range_pow_mul_of_pow_eq_zero hπ _ _

/-- The degree-growth set grows along a change of generators: if every `xᵢ` lies in the
subalgebra generated by `y`, then an expansion in `x` is also one in `y`. -/
theorem weakCompletionSet_subset_of_forall_mem_adjoin [Finite ι] {κ : Type*} {y : κ → S}
    (h : ∀ i, x i ∈ Algebra.adjoin O (Set.range y)) :
    weakCompletionSet π x ⊆ weakCompletionSet π y := by
  simp_rw [Algebra.adjoin_range_eq_range_aeval] at h
  choose Q hQ using h
  obtain ⟨D, hD⟩ := Finite.exists_le fun i ↦ (Q i).totalDegree
  rintro z ⟨c, P, hP, hz⟩
  refine ⟨c * D, fun j ↦ bind₁ Q (P j), fun j ↦ ?_, fun k ↦ ?_⟩
  · refine (totalDegree_bind₁_le hD _).trans ?_
    calc (P j).totalDegree * D ≤ c * (j + 1) * D := Nat.mul_le_mul_right _ (hP j)
      _ = c * D * (j + 1) := by ring
  · have hQ' : (fun i ↦ aeval y (Q i)) = x := funext hQ
    simp only [hz k, aeval_bind₁, hQ']

/-- Two finite generating families of the same subalgebra have the same degree-growth set. -/
theorem weakCompletionSet_eq_of_adjoin_eq [Finite ι] {κ : Type*} [Finite κ] {y : κ → S}
    (h : Algebra.adjoin O (Set.range x) = Algebra.adjoin O (Set.range y)) :
    weakCompletionSet π x = weakCompletionSet π y :=
  (weakCompletionSet_subset_of_forall_mem_adjoin fun i ↦
      h ▸ Algebra.subset_adjoin (Set.mem_range_self i)).antisymm
    (weakCompletionSet_subset_of_forall_mem_adjoin fun i ↦
      h ▸ Algebra.subset_adjoin (Set.mem_range_self i))

end WeakCompletionSet

/-- A polynomial expansion with a linear degree bound defines an element of the
corresponding degree-growth set, with the prescribed truncations. -/
theorem exists_mem_weakCompletionSet_of_degree_le {ι : Type*} (x : ι → S)
    (P : ℕ → MvPolynomial ι O) {c : ℕ}
    (hP : ∀ j, (P j).totalDegree ≤ c * (j + 1)) :
    ∃ z ∈ weakCompletionSet π x, ∀ k, AdicCompletion.evalₐ _ k z =
      Ideal.Quotient.mk _ (∑ j ∈ range k, algebraMap O S π ^ j * aeval x (P j)) := by
  let a (k : ℕ) := ∑ j ∈ range k, algebraMap O S π ^ j * aeval x (P j)
  have ha (k : ℕ) : a k ≡ a (k + 1)
      [SMOD (Ideal.span {algebraMap O S π} ^ k • ⊤ : Ideal S)] := by
    rw [SModEq.sub_mem]
    simp only [a, sum_range_succ, sub_add_cancel_left]
    apply Submodule.neg_mem
    rw [smul_eq_mul, Ideal.mul_top]
    exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow (Ideal.subset_span rfl) k)
  let z := AdicCompletion.mk _ S (AdicCompletion.AdicCauchySequence.mk _ S a ha)
  have hz (k : ℕ) : AdicCompletion.evalₐ _ k z = Ideal.Quotient.mk _ (a k) :=
    AdicCompletion.evalₐ_mk _ k _
  exact ⟨z, mem_weakCompletionSet_iff.mpr ⟨c, P, hP, hz⟩, hz⟩

section FiniteType

variable (S) [Algebra.FiniteType O S]

/-- The weak completion `S† ⊆ S^∧` of a finitely generated `O`-algebra `S`: the degree-growth set
of a chosen finite generating family, an `O`-subalgebra of the `π`-adic completion. By
`coe_weakCompletion` it is the degree-growth set of every finite generating family. -/
noncomputable def weakCompletion : Subalgebra O (piAdicCompletion π S) where
  carrier := weakCompletionSet π
    ((↑) : (Algebra.FiniteType.out (R := O) (A := S)).choose → S)
  add_mem' := add_mem_weakCompletionSet
  mul_mem' := mul_mem_weakCompletionSet
  algebraMap_mem' := algebraMap_mem_weakCompletionSet π _

variable {S}

/-- The weak completion is the degree-growth set of every finite generating family. In
particular it does not depend on the generators. -/
theorem coe_weakCompletion {ι : Type*} [Finite ι] (x : ι → S)
    (hx : Algebra.adjoin O (Set.range x) = ⊤) :
    (weakCompletion π S : Set (piAdicCompletion π S)) = weakCompletionSet π x :=
  weakCompletionSet_eq_of_adjoin_eq <| by
    rw [hx, Subtype.range_coe_subtype, Finset.setOfPred_mem]
    exact (Algebra.FiniteType.out (R := O) (A := S)).choose_spec

/-- Membership in the weak completion, in terms of the expansions in a finite generating
family `x`. -/
theorem mem_weakCompletion_iff {ι : Type*} [Finite ι] {x : ι → S}
    (hx : Algebra.adjoin O (Set.range x) = ⊤) {z : piAdicCompletion π S} :
    z ∈ weakCompletion π S ↔
      ∃ (c : ℕ) (P : ℕ → MvPolynomial ι O), (∀ j, (P j).totalDegree ≤ c * (j + 1)) ∧
        ∀ k, AdicCompletion.evalₐ _ k z =
          Ideal.Quotient.mk _ (∑ j ∈ range k, algebraMap O S π ^ j * aeval x (P j)) := by
  rw [← SetLike.mem_coe, coe_weakCompletion π x hx, mem_weakCompletionSet_iff]

/-- The weak completion contains the image of `S` in its `π`-adic completion. -/
theorem algebraMap_mem_weakCompletion (s : S) :
    algebraMap S (piAdicCompletion π S) s ∈ weakCompletion π S :=
  algebraMap_mem_weakCompletionSet_of_mem_adjoin π <| by
    rw [Subtype.range_coe_subtype, Finset.setOfPred_mem,
      (Algebra.FiniteType.out (R := O) (A := S)).choose_spec]
    exact Algebra.mem_top

variable (S) in
/-- The map `S → S†` into the weak completion. Its composite with the inclusion `S† ⊆ S^∧` is
the map of `S` to its `π`-adic completion. -/
noncomputable def weakCompletion.of : S →ₐ[O] weakCompletion π S :=
  (IsScalarTower.toAlgHom O S (piAdicCompletion π S)).codRestrict _
    (algebraMap_mem_weakCompletion π)

@[simp]
theorem weakCompletion.coe_of (s : S) :
    (weakCompletion.of π S s : piAdicCompletion π S) = AdicCompletion.of _ S s := by
  rfl

/-- The map `S → S†` is injective exactly when `S` is `π`-adically separated, that is, when
`⋂ₘ πᵐ S = 0`. -/
theorem weakCompletion.of_injective_iff :
    Function.Injective (weakCompletion.of π S) ↔
      IsHausdorff (Ideal.span {algebraMap O S π}) S := by
  rw [← AdicCompletion.of_injective_iff]
  refine ⟨fun h s t hst ↦ h (Subtype.ext hst), fun h s t hst ↦ h ?_⟩
  simpa using congrArg Subtype.val hst

/-- If every element of the `π`-adic completion comes from `S`, then the weak completion is the
whole completion. -/
theorem weakCompletion_eq_top_of_surjective
    (h : Function.Surjective (AdicCompletion.of (Ideal.span {algebraMap O S π}) S)) :
    weakCompletion π S = ⊤ := by
  refine eq_top_iff.mpr fun z _ ↦ ?_
  obtain ⟨s, rfl⟩ := h z
  exact algebraMap_mem_weakCompletion π s

/-- If `S` is `π`-adically complete, the canonical map `S → S†` is bijective. -/
theorem weakCompletion.of_bijective_of_isAdicComplete
    [IsAdicComplete (Ideal.span {algebraMap O S π}) S] :
    Function.Bijective (weakCompletion.of π S) := by
  have hbij := AdicCompletion.of_bijective (Ideal.span {algebraMap O S π}) S
  refine ⟨(weakCompletion.of_injective_iff π).mpr inferInstance, fun z ↦ ?_⟩
  obtain ⟨s, hs⟩ := hbij.2 (z : piAdicCompletion π S)
  exact ⟨s, Subtype.ext ((weakCompletion.coe_of π s).trans hs)⟩

/-- If the image of `π` in `S` is nilpotent, the canonical map `S → S†` is bijective. -/
theorem weakCompletion.of_bijective_of_isNilpotent {π : O}
    (hπ : IsNilpotent (algebraMap O S π)) :
    Function.Bijective (weakCompletion.of π S) := by
  obtain ⟨n, hn⟩ := hπ
  have hpow : Ideal.span {algebraMap O S π} ^ n = ⊥ := by
    rw [Ideal.span_singleton_pow, hn, Ideal.span_singleton_eq_bot]
  have : IsAdicComplete (Ideal.span {algebraMap O S π}) S :=
    TauCeti.isAdicComplete_of_pow_smul_eq_bot (by rw [hpow, Submodule.bot_smul])
  exact weakCompletion.of_bijective_of_isAdicComplete π

end FiniteType

private theorem exists_totalDegree_le_one_aeval_eq {s : Finset S}
    (hs : Submodule.span O (s : Set S) = ⊤) (t : S) :
    ∃ P : MvPolynomial s O, P.totalDegree ≤ 1 ∧ aeval ((↑) : s → S) P = t := by
  have ht : t ∈ Submodule.span O (s : Set S) := hs.symm ▸ Submodule.mem_top
  obtain ⟨c, rfl⟩ := Submodule.mem_span_finset'.mp ht
  refine ⟨∑ i : s, monomial (Finsupp.single i 1) (c i), ?_, ?_⟩
  · exact (totalDegree_finsetSum _ _).trans
      (Finset.sup_le fun i _ ↦ (totalDegree_monomial_le _ _).trans (by simp))
  · simp [aeval_monomial, Algebra.smul_def]

/-- For any module-finite `O`-algebra `S`, the weak completion `S†` is the entire `π`-adic
completion `S^∧`. -/
theorem weakCompletion_eq_top_of_finite [Module.Finite O S] : weakCompletion π S = ⊤ := by
  rw [eq_top_iff]
  intro z _
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := O) (M := S)
  let x : s → S := (↑)
  have hgen : Algebra.adjoin O (Set.range x) = ⊤ := by
    rw [eq_top_iff]
    intro y _
    have hy : y ∈ Submodule.span O (Set.range x) := by
      simp [x, Subtype.range_coe_subtype, hs]
    exact (Submodule.span_le (p := (Algebra.adjoin O (Set.range x)).toSubmodule)).mpr
      Algebra.subset_adjoin hy
  rw [mem_weakCompletion_iff π hgen]
  let I : Ideal S := Ideal.span {algebraMap O S π}
  obtain ⟨f, rfl⟩ := AdicCompletion.mk_surjective I S z
  -- Set `b 0 = 0` and `b (k + 1) = f.val (k + 1)`, then telescope consecutive differences.
  let b : ℕ → S := fun k ↦ if k = 0 then 0 else f.val k
  have hstep (j : ℕ) : ∃ t : S, b (j + 1) - b j = algebraMap O S π ^ j * t := by
    rcases j with _ | j
    · exact ⟨f.val 1, by simp [b]⟩
    · have htr := SModEq.sub_mem.mp (f.property (Nat.le_succ (j + 1))).symm
      rw [smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at htr
      obtain ⟨t, ht⟩ := htr
      exact ⟨t, by simpa [b] using ht⟩
  choose t ht using hstep
  choose P hPdeg hPev using fun j ↦ exists_totalDegree_le_one_aeval_eq hs (t j)
  refine ⟨1, P, fun j ↦ (hPdeg j).trans (by omega), fun k ↦ ?_⟩
  rw [AdicCompletion.evalₐ_mk]
  rcases k with _ | k
  · have : Subsingleton (S ⧸ I ^ 0) := Ideal.Quotient.subsingleton_iff.mpr (by simp)
    exact Subsingleton.elim _ _
  · congr 1
    simpa [x, hPev, ← ht, b] using (sum_range_sub b (k + 1)).symm

/-- For the base ring itself, the weak completion `O†` is the entire `π`-adic completion `Ô`. -/
theorem weakCompletion_self_eq_top : weakCompletion π O = ⊤ :=
  weakCompletion_eq_top_of_finite π

namespace weakCompletion

/-- For a module-finite `O`-algebra `S`, the canonical map `S → S†` is bijective if and only if
`S` is `π`-adically complete. -/
theorem of_bijective_iff_of_finite [Module.Finite O S] :
    Function.Bijective (of π S) ↔ IsAdicComplete (Ideal.span {algebraMap O S π}) S := by
  refine ⟨fun h ↦ ?_, fun _ ↦ of_bijective_of_isAdicComplete π⟩
  rw [← AdicCompletion.of_bijective_iff]
  have htop := weakCompletion_eq_top_of_finite (S := S) π
  refine ⟨fun a b hab ↦ h.1 (Subtype.ext ((coe_of π a).trans (hab.trans (coe_of π b).symm))),
    fun z ↦ ?_⟩
  obtain ⟨a, ha⟩ := h.2 ⟨z, htop.symm ▸ Algebra.mem_top⟩
  exact ⟨a, (coe_of π a).symm.trans (congrArg Subtype.val ha)⟩

/-- For the base ring `O` itself, `O → O†` is bijective if and only if `O` is `π`-adically
complete. -/
theorem of_self_bijective_iff :
    Function.Bijective (of π O) ↔ IsAdicComplete (Ideal.span {π}) O := by
  simpa using of_bijective_iff_of_finite (S := O) π

end weakCompletion

end TauCeti.Dagger
