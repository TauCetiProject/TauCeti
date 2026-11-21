/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.DiophantineApproximation.Subspace.Classes

import Mathlib.NumberTheory.NumberField.ClassNumber
import TauCeti.LinearAlgebra.Dual.Lemmas
import TauCeti.NumberTheory.Height.Northcott
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

The solutions left out are covered by finitely many proper subspaces when `ι` has at least two
elements and the forms are linearly independent at each place: those at which a form vanishes lie
in the kernel of that form, which is proper because the form is nonzero, and those of small height
are finitely many projective points by Northcott's theorem, each contributing the line it spans.
`TauCeti.NumberField.exists_finset_submodule_forall_mem_or_smul_mem_approxDomain` records the
resulting dichotomy, above an arbitrary level. With it, the Subspace Theorem with coefficients in
`K` follows from the parametric Subspace Theorem for the finitely many exponent families it
produces, whose forms it shows to be linearly independent at the infinite places and the places of
`S₀`: taking the level above all the levels the parametric theorem gives for these families, every
solution lies in one of finitely many proper subspaces.

## Main results

* `TauCeti.NumberField.exists_forall_approxProd_le_imp`: the solutions of the inequality of the
  Subspace Theorem of large height, and at which no form vanishes, lie up to scaling in finitely
  many approximation domains of weight at most `-ε / 2`.
* `TauCeti.NumberField.exists_finset_submodule_forall_mem_or_smul_mem_approxDomain`: for any
  level `Q₀`, every solution lies in one of finitely many proper subspaces or has height at least
  `Q₀` and a nonzero scalar multiple in one of these approximation domains.

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
      Sfin ⊆ S₀ ∧ (∀ v ∈ Sinf, L' v.val = L v.val) ∧ (∀ v ∈ Sfin, L' v.val = L v.val) ∧
      (∀ v : InfinitePlace K, v ∉ Sinf → ∀ i, L' v.val i = LinearMap.proj i) ∧
      (∀ v ∈ S₀, v ∉ Sfin → ∀ i, L' v.val i = LinearMap.proj i) ∧
      (∀ c ∈ T, approxWeight S₀ c ≤ -(ε / 2)) ∧
      ∀ x : ι → K, x ≠ 0 → Q₀ ≤ mulHeight x →
        (∀ (v : InfinitePlace K) (i : ι), L' v.val i x ≠ 0) → (∀ v ∈ S₀, ∀ i, L' v.val i x ≠ 0) →
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
  have hne (v : InfinitePlace K) (u : FinitePlace K) : v.val ≠ u.val := fun h ↦
    v.not_isNonarchimedean (h ▸ fun x y ↦ u.add_le x y)
  set L' : AbsoluteValue K ℝ → ι → Dual K (ι → K) := fun v ↦
    if (∃ u ∈ Sinf, u.val = v) ∨ ∃ u ∈ Sfin, u.val = v then L v else fun i ↦ LinearMap.proj i
  have hL'inf : ∀ v ∈ Sinf, L' v.val = L v.val := fun v hv ↦ ite_eq_left (Or.inl ⟨v, hv, rfl⟩)
  have hL'fin : ∀ v ∈ Sfin, L' v.val = L v.val := fun v hv ↦ ite_eq_left (Or.inr ⟨v, hv, rfl⟩)
  have hL'inf' : ∀ v : InfinitePlace K, v ∉ Sinf → ∀ i, L' v.val i = LinearMap.proj i := by
    intro v hv i
    refine congrFun (ite_eq_right ?_) i
    rintro (⟨u, hu, huv⟩ | ⟨u, -, huv⟩)
    · exact hv (Subtype.ext huv ▸ hu)
    · exact hne v u huv.symm
  have hL'fin' : ∀ v ∈ S₀, v ∉ Sfin → ∀ i, L' v.val i = LinearMap.proj i := by
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

/-- **Reduction of the Subspace Theorem to approximation domains, with the remaining solutions
covered by subspaces** (Bombieri–Gubler, Theorem 7.2.6 and 7.5.6). Let `ι` have at least two
elements, let `L v i` be linear forms, linearly independent at each place of `Sinf` and `Sfin`,
and let `ε > 0`. There are a finite set `S₀` of finite places, forms `L'` linearly independent at
every infinite place and every place of `S₀`, and finitely many exponent families `c` of weight
`approxWeight S₀ c ≤ -ε / 2` with the following property. For every level `Q₀` there are finitely
many proper subspaces of `ι → K` such that every nonzero `x` with
`approxProd Sinf Sfin id L x ≤ mulHeight x ^ (-card ι - ε)` lies in one of them, or has
`Q₀ ≤ mulHeight x` and a nonzero scalar multiple `a • x` in `approxDomain S₀ L' c (mulHeight x)`
for one of these `c`. -/
theorem exists_finset_submodule_forall_mem_or_smul_mem_approxDomain [Nontrivial ι]
    (Sinf : Finset (InfinitePlace K)) (Sfin : Finset (FinitePlace K))
    (L : AbsoluteValue K ℝ → ι → Dual K (ι → K))
    (hLInf : ∀ v ∈ Sinf, LinearIndependent K (L v.val))
    (hLFin : ∀ v ∈ Sfin, LinearIndependent K (L v.val)) {ε : ℝ} (hε : 0 < ε) :
    ∃ (S₀ : Finset (FinitePlace K)) (L' : AbsoluteValue K ℝ → ι → Dual K (ι → K))
      (T : Finset (AbsoluteValue K ℝ → ι → ℝ)),
      (∀ v : InfinitePlace K, LinearIndependent K (L' v.val)) ∧
      (∀ v ∈ S₀, LinearIndependent K (L' v.val)) ∧
      (∀ c ∈ T, approxWeight S₀ c ≤ -(ε / 2)) ∧
      ∀ Q₀ : ℝ, ∃ U : Finset (Submodule K (ι → K)), (∀ W ∈ U, W ≠ ⊤) ∧
        ∀ x : ι → K, x ≠ 0 →
          approxProd Sinf Sfin id L x ≤ mulHeight x ^ (-(Fintype.card ι : ℝ) - ε) →
          (∃ W ∈ U, x ∈ W) ∨ (Q₀ ≤ mulHeight x ∧
            ∃ a : K, a ≠ 0 ∧ ∃ c ∈ T, a • x ∈ approxDomain S₀ L' c (mulHeight x)) := by
  classical
  obtain ⟨S₀, L', T, Q₁, -, hinf, hfin, hinf', hfin', hT, hsol⟩ :=
    exists_forall_approxProd_le_imp Sinf Sfin L hε
  -- `L'` is `L` at the places of `Sinf` and `Sfin` and the coordinate forms elsewhere
  have hindInf (v : InfinitePlace K) : LinearIndependent K (L' v.val) := by
    by_cases hv : v ∈ Sinf
    · exact hinf v hv ▸ hLInf v hv
    · exact (funext (hinf' v hv)).symm ▸ Module.Dual.linearIndependent_proj K ι
  have hindFin (v : FinitePlace K) (hv : v ∈ S₀) : LinearIndependent K (L' v.val) := by
    by_cases hv' : v ∈ Sfin
    · exact hfin v hv' ▸ hLFin v hv'
    · exact (funext (hfin' v hv hv')).symm ▸ Module.Dual.linearIndependent_proj K ι
  refine ⟨S₀, L', T, hindInf, hindFin, hT, fun Q₀ ↦ ?_⟩
  -- the lines through the points of height at most `max Q₀ Q₁`, and the kernels of the forms at
  -- the infinite places and the places of `S₀`
  obtain ⟨T₁, hT₁, hlines⟩ := exists_finset_finrank_eq_one_of_mulHeight_le (K := K) (ι := ι)
    (max Q₀ Q₁)
  refine ⟨T₁ ∪ (univ ×ˢ univ).image (fun p : InfinitePlace K × ι ↦
    LinearMap.ker (L' p.1.val p.2)) ∪ (S₀ ×ˢ univ).image (fun p : FinitePlace K × ι ↦
    LinearMap.ker (L' p.1.val p.2)), fun W hW ↦ ?_, fun x hx happrox ↦ ?_⟩
  · simp only [mem_union, mem_image, mem_product, mem_univ, and_true, true_and,
      Prod.exists] at hW
    rcases hW with (hW | ⟨v, i, rfl⟩) | ⟨v, i, hv, rfl⟩
    · -- a line is proper because `ι` has at least two elements
      intro h
      have h1 := hT₁ W hW
      rw [h, finrank_top, Module.finrank_fintype_fun_eq_card] at h1
      exact (Fintype.one_lt_card (α := ι)).ne' h1
    · exact LinearMap.ker_eq_top.not.mpr ((hindInf v).ne_zero i)
    · exact LinearMap.ker_eq_top.not.mpr ((hindFin v hv).ne_zero i)
  by_cases hQ : mulHeight x ≤ max Q₀ Q₁
  · obtain ⟨W, hW, hxW⟩ := hlines x hx hQ
    exact Or.inl ⟨W, mem_union_left _ (mem_union_left _ hW), hxW⟩
  rw [not_le, max_lt_iff] at hQ
  by_cases hInf : ∃ (v : InfinitePlace K) (i : ι), L' v.val i x = 0
  · obtain ⟨v, i, hvi⟩ := hInf
    refine Or.inl ⟨LinearMap.ker (L' v.val i), mem_union_left _ (mem_union_right _ ?_),
      LinearMap.mem_ker.mpr hvi⟩
    exact mem_image.mpr ⟨(v, i), mem_product.mpr ⟨mem_univ v, mem_univ i⟩, rfl⟩
  by_cases hFin : ∃ v ∈ S₀, ∃ i : ι, L' v.val i x = 0
  · obtain ⟨v, hv, i, hvi⟩ := hFin
    exact Or.inl ⟨LinearMap.ker (L' v.val i), mem_union_right _
      (mem_image.mpr ⟨(v, i), mem_product.mpr ⟨hv, mem_univ i⟩, rfl⟩), LinearMap.mem_ker.mpr hvi⟩
  push Not at hInf hFin
  exact Or.inr ⟨hQ.1.le, hsol x hx hQ.2.le hInf hFin happrox⟩

end TauCeti.NumberField
