/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.DiophantineApproximation.Subspace.Classes

import Mathlib.NumberTheory.NumberField.ClassNumber
import TauCeti.NumberTheory.NumberField.InfinitePlace.Basic
import TauCeti.RingTheory.DedekindDomain.SInteger.ClassGroup

/-!
# Reduction of the Subspace Theorem to approximation domains

Let `K` be a number field, `Sinf` a finite set of infinite places and `Sfin` a finite set of
finite places of `K`, and `L v i` linear forms on `ι → K` at these places. The Subspace Theorem
with coefficients in `K` concerns the nonzero `x` with

`approxProd Sinf Sfin id L x ≤ mulHeight x ^ (-card ι - ε)`.

This file reduces it to statements about approximation domains, which is how Schmidt's proof
proceeds (Bombieri–Gubler, Theorem 7.2.6 and 7.5.6). First, `Sfin` is enlarged to a finite set
`S₀` of finite places whose `S₀`-integers form a principal ideal domain, so that every nonzero
point has an `S₀`-primitive scalar multiple, and the missing infinite places are added. Both kinds
of new places carry the coordinate forms, whose local factor is at most `1`, so the inequality
persists for the enlarged system (`NumberField.approxProd_le_approxProd_of_subset`). Then the
classes of `TauCeti.NumberField.exists_finset_forall_exists_smul_mem_approxDomain` apply to the
primitive multiple.

The result, `TauCeti.NumberField.exists_forall_approxProd_le_imp`, says that every solution of
large height at which none of the enlarged forms vanishes has a nonzero scalar multiple in one of
finitely many approximation domains of weight at most `-ε / 2`, at the level `mulHeight x`. Since
subspaces are closed under scaling, a subspace containing such a domain contains the solution.
The solutions at which a form vanishes lie in the kernel of that form.

## Main results

* `TauCeti.NumberField.exists_forall_approxProd_le_imp`: the solutions of the inequality of the
  Subspace Theorem of large height, and at which no form vanishes, lie up to scaling in finitely
  many approximation domains of weight at most `-ε / 2`.

## References

* E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press (2006),
  Theorem 7.2.6 and 7.5.6.
-/

public section

open Finset Height IsDedekindDomain Module

namespace TauCeti.NumberField

open _root_.NumberField

variable {K : Type*} [Field K] [NumberField K] {ι : Type*} [Fintype ι]

/-- **Reduction of the Subspace Theorem to approximation domains** (Bombieri–Gubler, Theorem 7.2.6
and 7.5.6). Let `L v i` be linear forms at the places of `Sinf` and `Sfin`, and `ε > 0`. There
are a finite set `S₀ ⊇ Sfin` of finite places, forms `L'` agreeing with `L` at the places of
`Sinf` and `Sfin` and equal to the coordinate forms at the other infinite places and the other
places of `S₀`, finitely many exponent families `c` of weight `approxWeight S₀ c ≤ -ε / 2`, and a
level `Q₀`, such that every nonzero `x` with `Q₀ ≤ mulHeight x`, at which no form `L'` vanishes
and with `approxProd Sinf Sfin id L x ≤ mulHeight x ^ (-card ι - ε)`, has a nonzero scalar
multiple `a • x` in `approxDomain S₀ L' c (mulHeight x)` for one of these `c`. -/
theorem exists_forall_approxProd_le_imp (Sinf : Finset (InfinitePlace K))
    (Sfin : Finset (FinitePlace K)) (L : AbsoluteValue K ℝ → ι → Dual K (ι → K)) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ (S₀ : Finset (FinitePlace K)) (L' : AbsoluteValue K ℝ → ι → Dual K (ι → K))
      (T : Finset (AbsoluteValue K ℝ → ι → ℝ)) (Q₀ : ℝ),
      Sfin ⊆ S₀ ∧ (∀ v ∈ Sinf, L' v.1 = L v.1) ∧ (∀ v ∈ Sfin, L' v.1 = L v.1) ∧
      (∀ v : InfinitePlace K, v ∉ Sinf → ∀ i, L' v.1 i = LinearMap.proj i) ∧
      (∀ v ∈ S₀, v ∉ Sfin → ∀ i, L' v.1 i = LinearMap.proj i) ∧
      (∀ c ∈ T, approxWeight S₀ c ≤ -(ε / 2)) ∧
      ∀ x : ι → K, x ≠ 0 → Q₀ ≤ mulHeight x →
        (∀ (v : InfinitePlace K) (i : ι), L' v.1 i x ≠ 0) → (∀ v ∈ S₀, ∀ i, L' v.1 i x ≠ 0) →
        approxProd Sinf Sfin id L x ≤ mulHeight x ^ (-(Fintype.card ι : ℝ) - ε) →
        ∃ a : K, a ≠ 0 ∧ ∃ c ∈ T, a • x ∈ approxDomain S₀ L' c (mulHeight x) := by
  classical
  -- enlarge `Sfin` to `S₀` with principal `S₀`-integers
  obtain ⟨S', hSS', hS'⟩ :=
    exists_finset_superset_isPrincipalIdealRing_integer K (Sfin.image FinitePlace.maximalIdeal)
  set S₀ : Finset (FinitePlace K) := S'.image FinitePlace.mk with hS₀_def
  have hS₀ : FinitePlace.maximalIdeal '' (S₀ : Set (FinitePlace K)) = S' := by
    simp [hS₀_def, Set.image_image, FinitePlace.maximalIdeal_mk]
  have hsub : Sfin ⊆ S₀ := fun v hv ↦ mem_image.mpr
    ⟨v.maximalIdeal, hSS' (mem_image_of_mem _ hv), FinitePlace.mk_maximalIdeal v⟩
  -- keep `L` at the places of `Sinf` and `Sfin`, and put the coordinate forms everywhere else;
  -- this is consistent since an infinite place is archimedean and a finite place is not
  have hne (v : InfinitePlace K) (u : FinitePlace K) : v.1 ≠ u.1 := fun h ↦
    v.not_isNonarchimedean (h ▸ fun x y ↦ u.add_le x y)
  set L' : AbsoluteValue K ℝ → ι → Dual K (ι → K) := fun v ↦
    if (∃ u ∈ Sinf, u.1 = v) ∨ ∃ u ∈ Sfin, u.1 = v then L v else fun i ↦ LinearMap.proj i
  have hL'inf : ∀ v ∈ Sinf, L' v.1 = L v.1 := fun v hv ↦ ite_eq_left (Or.inl ⟨v, hv, rfl⟩)
  have hL'fin : ∀ v ∈ Sfin, L' v.1 = L v.1 := fun v hv ↦ ite_eq_left (Or.inr ⟨v, hv, rfl⟩)
  have hL'inf' : ∀ v : InfinitePlace K, v ∉ Sinf → ∀ i, L' v.1 i = LinearMap.proj i := by
    intro v hv i
    refine congrFun (ite_eq_right ?_) i
    rintro (⟨u, hu, huv⟩ | ⟨u, -, huv⟩)
    · exact hv (Subtype.ext huv ▸ hu)
    · exact hne v u huv.symm
  have hL'fin' : ∀ v ∈ S₀, v ∉ Sfin → ∀ i, L' v.1 i = LinearMap.proj i := by
    intro v _ hv i
    refine congrFun (ite_eq_right ?_) i
    rintro (⟨u, -, huv⟩ | ⟨u, hu, huv⟩)
    · exact hne u v huv
    · exact hv (Subtype.ext huv ▸ hu)
  obtain ⟨T, Q₀, hT, hsol⟩ := exists_finset_forall_exists_smul_mem_approxDomain S₀ L' hε
  refine ⟨S₀, L', T, Q₀, hsub, hL'inf, hL'fin, hL'inf', hL'fin', hT, ?_⟩
  intro x hx hQ hLinf hLfin happrox
  -- pass to an `S₀`-primitive multiple `a • x`, which has the same height
  obtain ⟨a, ha, hprim⟩ := Set.exists_isPrimitive_smul (S := (S' : Set (HeightOneSpectrum (𝓞 K))))
    hx
  have hH : mulHeight (a • x) = mulHeight x := mulHeight_smul_eq_mulHeight x ha
  have hL {v : AbsoluteValue K ℝ} {i : ι} (h : L' v i x ≠ 0) : L' v i (a • x) ≠ 0 := by
    simpa [ha] using h
  -- the inequality persists for the enlarged system and for `a • x`
  have hid {v : AbsoluteValue K ℝ} : (id v).LiesOver v := ⟨by ext; simp⟩
  have happrox' :
      approxProd univ S₀ id L' (a • x) ≤ mulHeight (a • x) ^ (-(Fintype.card ι : ℝ) - ε) := by
    rw [approxProd_smul (fun _ _ ↦ hid) (fun _ _ ↦ hid) ha, hH]
    calc approxProd univ S₀ id L' x ≤ approxProd Sinf Sfin id L' x :=
          approxProd_le_approxProd_of_subset (subset_univ _) hsub (fun _ _ _ ↦ hid)
            (fun _ _ _ ↦ hid) (fun v _ hv ↦ hL'inf' v hv) (fun v hv hv' ↦ hL'fin' v hv hv') x
      _ = approxProd Sinf Sfin id L x := approxProd_congr hL'inf hL'fin x
      _ ≤ _ := happrox
  obtain ⟨u, c, hc, hmem⟩ := hsol (a • x) (hS₀ ▸ hprim) (hH ▸ hQ) (fun v i ↦ hL (hLinf v i))
    (fun v hv i ↦ hL (hLfin v hv i)) happrox'
  refine ⟨((u : Kˣ) : K) * a, mul_ne_zero (Units.ne_zero _) ha, c, hc, ?_⟩
  rw [mul_smul, ← hH]
  exact hmem

end TauCeti.NumberField
