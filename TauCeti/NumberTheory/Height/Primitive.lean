/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.ClassNumber
public import TauCeti.NumberTheory.Height.SInteger
public import TauCeti.RingTheory.DedekindDomain.SInteger.ClassGroup
public import TauCeti.RingTheory.DedekindDomain.SInteger.Primitive

/-!
# The height of a point through finitely many places

Let `K` be a number field and `S` a finite set of finite places of `K`, carried as a `Finset` of
height one primes of `𝓞 K`. For a nonzero finite tuple `x : ι → K` of `S`-integers, every local
sup norm `⨆ i, |x i|_v` at a finite place `v ∉ S` is at most `1`, so

`mulHeight x ≤ (∏_{v | ∞} (⨆ i, v (x i)) ^ mult v) * ∏_{v ∈ S} ⨆ i, |x i|_v`,

with equality as soon as those local sup norms are all `1`. For a nonzero finite tuple this
happens exactly when `x` is `S`-primitive (`Set.isPrimitive_iff_finitePlace`), its coordinates
being `S`-integers that generate the unit ideal of `S.integer K`. Enlarging `S` until
`S.integer K` is a principal ideal domain makes every nonzero finite tuple `S`-primitive after one
scaling, so the height of every point of projective space over `K` is computed by the infinite
places and a single finite set of finite places
(`NumberField.exists_finset_superset_forall_exists_mulHeight_eq`). This is the normalisation with
which Bombieri and Gubler open the proof of the `S`-integral form of the Subspace Theorem.

## Main results

* `Set.isPrimitive_iff_finitePlace`: a nonzero tuple is `S`-primitive exactly when its local sup
  norms at the finite places outside `S` are `1`.
* `NumberField.mulHeight_le_prod`: the height of a nonzero tuple of `S`-integers is at most the
  product of its local sup norms over the infinite places and `S`.
* `NumberField.mulHeight_eq_prod_of_forall_iSup_eq_one` and
  `NumberField.mulHeight_eq_prod_of_isPrimitive`: equality when the local sup norms outside `S`
  are `1`, in particular for an `S`-primitive tuple.
* `NumberField.exists_finset_superset_forall_exists_mulHeight_eq`: every finite `S` is contained
  in a finite `S'` such that every nonzero finite tuple has a nonzero scalar multiple which is
  `S'`-primitive, and whose local sup norms over the infinite places and `S'` multiply to the
  height.

## References

* E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press, 2006,
  §1.5.10, Proposition 5.3.6 and the proof of Theorem 7.2.6.

The statements follow Ralf Stephan's `DiophantineApproximation/SAdicHeight.lean` in
`rwst/Subspace-Theorems` at `09835cb23557ae5ae0cf55a9c4ab9055f5d60338` (Apache 2.0).
-/

public section

open Height IsDedekindDomain

namespace NumberField

variable {K : Type*} [Field K] [NumberField K] {ι : Type*} {x : ι → K}

/-- **A nonzero tuple is `S`-primitive exactly when its local sup norms at the finite places
outside `S` are all `1`.** This is the `S`-primitive counterpart of
`Set.mem_integer_iff_finitePlace`. -/
theorem _root_.Set.isPrimitive_iff_finitePlace [Finite ι] (S : Set (HeightOneSpectrum (𝓞 K)))
    (hx : x ≠ 0) :
    S.IsPrimitive x ↔ ∀ v ∉ S, ⨆ i, FinitePlace.mk v (x i) = 1 := by
  obtain ⟨i₀, -⟩ := Function.ne_iff.mp hx
  have : Nonempty ι := ⟨i₀⟩
  simp only [Set.isPrimitive_iff_forall_exists_valuation_eq_one hx, Set.mem_integer_iff_finitePlace,
    ← FinitePlace.mk_apply_eq_one_iff]
  refine ⟨fun ⟨hint, h⟩ v hv ↦ ?_, fun h ↦ ⟨fun i v hv ↦ ?_, fun v hv ↦ ?_⟩⟩
  · obtain ⟨i, hi⟩ := h v hv
    exact le_antisymm (ciSup_le fun j ↦ hint j v hv) (hi ▸ Finite.le_ciSup_of_le i le_rfl)
  · exact (Finite.le_ciSup_of_le i le_rfl).trans (h v hv).le
  · obtain ⟨i, hi⟩ := exists_eq_ciSup_of_finite (f := fun i ↦ FinitePlace.mk v (x i))
    exact ⟨i, hi.trans (h v hv)⟩

/-- **The height of a nonzero tuple whose local sup norms at the finite places outside `S` are
all `1` is the product of its local sup norms over the infinite places and the places of `S`.** -/
theorem mulHeight_eq_prod_of_forall_iSup_eq_one (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hx : x ≠ 0) (h : ∀ v ∉ S, ⨆ i, FinitePlace.mk v (x i) = 1) :
    mulHeight x = (∏ v : InfinitePlace K, (⨆ i, v (x i)) ^ v.mult)
      * ∏ v ∈ S, ⨆ i, FinitePlace.mk v (x i) := by
  rw [NumberField.mulHeight_eq hx, ← FinitePlace.finprod_comp_mk]
  congr 1
  refine finprod_eq_finsetProd_of_mulSupport_subset _ fun v hv ↦ ?_
  by_contra hvS
  exact hv (h v hvS)

variable [Finite ι]

/-- **The height of a nonzero tuple of `S`-integers is at most the product of its local sup norms
over the infinite places and the places of `S`.** The local sup norms at the other finite places
are at most `1`. -/
theorem mulHeight_le_prod (S : Finset (HeightOneSpectrum (𝓞 K))) (hx : x ≠ 0)
    (hxS : ∀ i, x i ∈ (S : Set (HeightOneSpectrum (𝓞 K))).integer K) :
    mulHeight x ≤ (∏ v : InfinitePlace K, (⨆ i, v (x i)) ^ v.mult)
      * ∏ v ∈ S, ⨆ i, FinitePlace.mk v (x i) := by
  classical
  rw [NumberField.mulHeight_eq hx, ← FinitePlace.finprod_comp_mk]
  refine mul_le_mul_of_nonneg_left ?_
    (Finset.prod_nonneg fun v _ ↦ pow_nonneg (Real.iSup_nonneg fun i ↦ apply_nonneg _ _) _)
  set F : HeightOneSpectrum (𝓞 K) → ℝ := fun v ↦ ⨆ i, FinitePlace.mk v (x i)
  -- compare with the function equal to `F` on `S` and to `1` outside it
  have hle : ∀ v, F v ≤ (S : Set (HeightOneSpectrum (𝓞 K))).mulIndicator F v := fun v ↦ by
    rw [Set.mulIndicator_apply]
    split_ifs with hv
    · exact le_rfl
    · exact Real.iSup_le (fun i ↦ (Set.mem_integer_iff_finitePlace _ _).mp (hxS i) v hv)
        zero_le_one
  have hFfin : Function.HasFiniteMulSupport F :=
    (FinitePlace.hasFiniteMulSupport_iSup hx).comp_of_injective
      (g := (FinitePlace.equivHeightOneSpectrum (K := K)).symm)
      (FinitePlace.equivHeightOneSpectrum (K := K)).symm.injective
  calc ∏ᶠ v, F v ≤ ∏ᶠ v, (S : Set (HeightOneSpectrum (𝓞 K))).mulIndicator F v :=
        finprod_le_finprod₀ hFfin (fun v ↦ Real.iSup_nonneg fun i ↦ apply_nonneg _ _)
          (S.finite_toSet.subset (Set.mulSupport_mulIndicator_subset)) hle
    _ = ∏ v ∈ S, F v := by rw [← finprod_mem_def, finprod_mem_coe_finset]

/-- **The height of an `S`-primitive tuple is the product of its local sup norms over the
infinite places and the places of `S`.** -/
theorem mulHeight_eq_prod_of_isPrimitive (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hx : (S : Set (HeightOneSpectrum (𝓞 K))).IsPrimitive x) :
    mulHeight x = (∏ v : InfinitePlace K, (⨆ i, v (x i)) ^ v.mult)
      * ∏ v ∈ S, ⨆ i, FinitePlace.mk v (x i) :=
  mulHeight_eq_prod_of_forall_iSup_eq_one S hx.ne_zero fun v hv ↦
    (Set.isPrimitive_iff_finitePlace _ hx.ne_zero).mp hx v (by simpa using hv)

/-- **The height of every point is computed by finitely many places.** Every finite set `S` of
finite places is contained in a finite set `S'` such that every nonzero finite tuple has a nonzero
scalar multiple `c • x` which is `S'`-primitive, so that the height of `x` is the product of the
local sup norms of `c • x` over the infinite places and the places of `S'`. One may take any `S'`
whose `S'`-integers are a principal ideal domain. -/
theorem exists_finset_superset_forall_exists_mulHeight_eq (S : Finset (HeightOneSpectrum (𝓞 K))) :
    ∃ S' : Finset (HeightOneSpectrum (𝓞 K)), S ⊆ S' ∧ ∀ x : ι → K, x ≠ 0 →
      ∃ c : K, c ≠ 0 ∧ (S' : Set (HeightOneSpectrum (𝓞 K))).IsPrimitive (c • x) ∧
        mulHeight x = (∏ v : InfinitePlace K, (⨆ i, v (c * x i)) ^ v.mult)
          * ∏ v ∈ S', ⨆ i, FinitePlace.mk v (c * x i) := by
  obtain ⟨S', hSS', hS'⟩ := exists_finset_superset_isPrincipalIdealRing_integer K S
  refine ⟨S', hSS', fun x hx ↦ ?_⟩
  obtain ⟨c, hc, hprim⟩ :=
    Set.exists_isPrimitive_smul (S := (S' : Set (HeightOneSpectrum (𝓞 K)))) hx
  refine ⟨c, hc, hprim, ?_⟩
  rw [← mulHeight_smul_eq_mulHeight x hc]
  exact mulHeight_eq_prod_of_isPrimitive S' hprim

/-- `S`-integrality alone does not give the equality of
`NumberField.mulHeight_eq_prod_of_isPrimitive`. The tuple `(2, …, 2)` has algebraic-integer
coordinates and height `1`, but its local sup norms over the infinite places multiply to
`2 ^ [K : ℚ]`: the missing factor sits at the places above `2`, where its local sup norm is less
than `1`. -/
example [Nonempty ι] :
    mulHeight (fun _ : ι ↦ (2 : K)) ≠
      (∏ v : InfinitePlace K, (⨆ _ : ι, v (2 : K)) ^ v.mult) *
        ∏ v ∈ (∅ : Finset (HeightOneSpectrum (𝓞 K))), ⨆ _ : ι, FinitePlace.mk v (2 : K) := by
  have h2 : ∀ w : InfinitePlace K, w (2 : K) = 2 := fun w ↦ by simpa using w.map_natCast 2
  have hlhs : mulHeight (fun _ : ι ↦ (2 : K)) = 1 := by
    have h2one : (fun _ : ι ↦ (2 : K)) = (2 : K) • (1 : ι → K) := by
      funext
      simp
    rw [h2one, mulHeight_smul_eq_mulHeight _ two_ne_zero, mulHeight_one]
  rw [hlhs, Finset.prod_empty, mul_one]
  simp_rw [ciSup_const, h2]
  rw [Finset.prod_pow_eq_pow_sum, ← totalWeight_eq_sum_mult, totalWeight_eq_finrank]
  exact (one_lt_pow₀ one_lt_two Module.finrank_pos.ne').ne

end NumberField
