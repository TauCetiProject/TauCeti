/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.TemperleyLieb.Basic

/-!
# The Temperley–Lieb tower

The Temperley–Lieb algebras form a tower along the strand inclusion
`TauCeti.TemperleyLieb.strandIncl : TemperleyLieb R δ (n + 1) →ₐ[R] TemperleyLieb R δ (n + 2)`,
and each stage is generated over the previous one by the single new generator
`E = e δ (Fin.last n)`, which caps the last two strands. This file proves Jones' description of
how: every element on `n + 2` strands is an `R`-linear combination of elements `strandIncl a`
and of products `strandIncl a * E * strandIncl b`, with `a b` on `n + 1` strands,

`TL(n + 2) = TL(n + 1) + TL(n + 1) · E · TL(n + 1)`.

The engine is the sandwich identity: sandwiching an element of the previous stage between two
copies of the last generator gives an element of the stage before that, times the last generator,

`E * strandIncl x * E = strandIncl (strandIncl y) * E`.

Geometrically, `E * x * E` closes off the last strand of `x` and leaves a cup and a cap on the
last two strands. The two statements are proved together by induction along the tower.

This normal form is what makes traces on the tower computable by recursion: a Markov trace is
determined on `strandIncl a` by the strand-inclusion compatibility and on
`strandIncl a * E * strandIncl b` by the Markov property, which is how
`TauCeti.TemperleyLieb.IsMarkovTrace.unique` proves that there is at most one Markov trace.

## Main results

* `TauCeti.TemperleyLieb.span_strandIncl_union_strandIncl_mul_e_last_mul_eq_top`: the
  elements `strandIncl a` and `strandIncl a * e δ (Fin.last n) * strandIncl b` span
  `TemperleyLieb R δ (n + 2)`.
* `TauCeti.TemperleyLieb.exists_e_last_mul_strandIncl_mul_e_last_eq`: the sandwich identity.

## References

* V. F. R. Jones, *Index for subfactors*, Invent. Math. 72 (1983), 1–25.
* F. M. Goodman, P. de la Harpe and V. F. R. Jones, *Coxeter graphs and towers of algebras*,
  MSRI Publications 14, Springer, 1989.
-/

public section

namespace TauCeti.TemperleyLieb

variable {R : Type*} [CommSemiring R] {δ : R} {n : ℕ}

/-- The elements `strandIncl a` and `strandIncl a * e δ (Fin.last n) * strandIncl b` on `n + 2`
strands, with `a b` on `n + 1` strands. -/
private abbrev towerSpanningSet (R : Type*) [CommSemiring R] (δ : R) (n : ℕ) :
    Set (TemperleyLieb R δ (n + 2)) :=
  Set.range (strandIncl (R := R) (δ := δ) (n := n)) ∪
    Set.range fun p : TemperleyLieb R δ (n + 1) × TemperleyLieb R δ (n + 1) ↦
      strandIncl p.1 * e δ (Fin.last n) * strandIncl p.2

/-- The span step: if sandwiching between two last generators on `n + 2` strands stays in
`strandIncl (TemperleyLieb R δ (n + 1)) * e δ (Fin.last n)`, then the tower spanning set spans.
The span `M` contains `1 = strandIncl 1`, and is stable under right multiplication by every
generator: by `strandIncl c` directly, and by the last generator thanks to the hypothesis. -/
private theorem span_towerSpanningSet_eq_top_of_sandwich
    (h : ∀ x : TemperleyLieb R δ (n + 1), ∃ y : TemperleyLieb R δ (n + 1),
      e δ (Fin.last n) * strandIncl x * e δ (Fin.last n) = strandIncl y * e δ (Fin.last n)) :
    Submodule.span R (towerSpanningSet R δ n) = ⊤ := by
  set M := Submodule.span R (towerSpanningSet R δ n)
  have hincl (a : TemperleyLieb R δ (n + 1)) : strandIncl a ∈ M :=
    Submodule.subset_span (Or.inl ⟨a, rfl⟩)
  have hcap (a b : TemperleyLieb R δ (n + 1)) :
      strandIncl a * e δ (Fin.last n) * strandIncl b ∈ M :=
    Submodule.subset_span (Or.inr ⟨(a, b), rfl⟩)
  -- Right multiplication by `y` preserves `M` as soon as it maps the spanning set into `M`.
  have hright (y : TemperleyLieb R δ (n + 2)) (hy : ∀ s ∈ towerSpanningSet R δ n, s * y ∈ M)
      (m : TemperleyLieb R δ (n + 2)) (hm : m ∈ M) : m * y ∈ M :=
    (Submodule.image_span_subset (LinearMap.mulRight R y) _ M).2 hy ⟨m, hm, rfl⟩
  have hstrand (c : TemperleyLieb R δ (n + 1)) (m : TemperleyLieb R δ (n + 2)) (hm : m ∈ M) :
      m * strandIncl c ∈ M := by
    refine hright _ ?_ m hm
    rintro _ (⟨a, rfl⟩ | ⟨⟨a, b⟩, rfl⟩)
    · simpa only [map_mul] using hincl (a * c)
    · simpa only [map_mul, mul_assoc] using hcap a (b * c)
  have hlast (m : TemperleyLieb R δ (n + 2)) (hm : m ∈ M) : m * e δ (Fin.last n) ∈ M := by
    refine hright _ ?_ m hm
    rintro _ (⟨a, rfl⟩ | ⟨⟨a, b⟩, rfl⟩)
    · simpa using hcap a 1
    · obtain ⟨y, hy⟩ := h b
      have : strandIncl a * e δ (Fin.last n) * strandIncl b * e δ (Fin.last n) =
          strandIncl (a * y) * e δ (Fin.last n) * strandIncl 1 := by
        rw [map_one, mul_one, map_mul, mul_assoc (strandIncl a), mul_assoc (strandIncl a), hy,
          mul_assoc]
      exact this ▸ hcap (a * y) 1
  -- Every element `x` lies in `M` because `1 * x` does, by induction on `x` in the generators.
  refine Submodule.eq_top_iff'.2 fun x ↦ ?_
  suffices ∀ m ∈ M, m * x ∈ M by simpa using this 1 (by simpa using hincl 1)
  induction x using TemperleyLieb.induction with
  | e i =>
    induction i using Fin.lastCases with
    | last => exact hlast
    | cast j => simpa only [strandIncl_e] using hstrand (e δ j)
  | algebraMap r => simpa only [AlgHom.commutes] using hstrand (algebraMap R _ r)
  | add x z hx hz => exact fun m hm ↦ by simpa [mul_add] using M.add_mem (hx m hm) (hz m hm)
  | mul x z hx hz => exact fun m hm ↦ by simpa [mul_assoc] using hz _ (hx m hm)

/-- The sandwich step: if the tower spanning set spans `TemperleyLieb R δ (n + 2)`, then
sandwiching `strandIncl x` between two last generators on `n + 3` strands gives an element of the
stage two levels down times the last generator. It suffices to check this on the spanning set,
where it follows from the commutation of the last generator with `strandIncl (strandIncl _)`, the
quadratic relation, and the zigzag relation with the second to last generator. -/
private theorem sandwich_of_span_towerSpanningSet_eq_top
    (h : Submodule.span R (towerSpanningSet R δ n) = ⊤) (x : TemperleyLieb R δ (n + 2)) :
    ∃ y : TemperleyLieb R δ (n + 1),
      e δ (Fin.last (n + 1)) * strandIncl x * e δ (Fin.last (n + 1)) =
        strandIncl (strandIncl y) * e δ (Fin.last (n + 1)) := by
  have hx : x ∈ Submodule.span R (towerSpanningSet R δ n) := h ▸ Submodule.mem_top
  induction hx using Submodule.span_induction with
  | mem s hs =>
    rcases hs with ⟨a, rfl⟩ | ⟨⟨a, b⟩, rfl⟩
    · refine ⟨δ • a, ?_⟩
      rw [(commute_e_last_strandIncl_strandIncl a).eq, mul_assoc, e_mul_self, map_smul,
        map_smul, mul_smul_comm, smul_mul_assoc]
    · refine ⟨a * b, ?_⟩
      have hadj : e δ (Fin.last (n + 1)) * e δ (Fin.last n).castSucc * e δ (Fin.last (n + 1)) =
          e (R := R) (n := n + 3) δ (Fin.last (n + 1)) :=
        e_mul_e_mul_e (Or.inr (by simp))
      have ha := (commute_e_last_strandIncl_strandIncl (δ := δ) a).eq
      have hb := (commute_e_last_strandIncl_strandIncl (δ := δ) b).eq
      simp only [map_mul, strandIncl_e]
      -- Move both copies of the last generator inward, past `strandIncl (strandIncl _)`, and
      -- straighten the zigzag they form with the second to last generator.
      calc e δ (Fin.last (n + 1)) * (strandIncl (strandIncl a) * e δ (Fin.last n).castSucc *
            strandIncl (strandIncl b)) * e δ (Fin.last (n + 1))
          = strandIncl (strandIncl a) * (e δ (Fin.last (n + 1)) * e δ (Fin.last n).castSucc *
              e δ (Fin.last (n + 1))) * strandIncl (strandIncl b) := by
            simp only [← mul_assoc, ha]
            simp only [mul_assoc, ← hb]
        _ = strandIncl (strandIncl a) * strandIncl (strandIncl b) * e δ (Fin.last (n + 1)) := by
            rw [hadj, mul_assoc, hb, ← mul_assoc]
  | zero => exact ⟨0, by simp⟩
  | add x z _ _ hx hz =>
    obtain ⟨y, hy⟩ := hx
    obtain ⟨w, hw⟩ := hz
    exact ⟨y + w, by simp only [map_add, mul_add, add_mul, hy, hw]⟩
  | smul r x _ hx =>
    obtain ⟨y, hy⟩ := hx
    exact ⟨r • y, by simp only [map_smul, mul_smul_comm, smul_mul_assoc, hy]⟩

/-- The sandwich identity on two strands: the previous stage is the base ring, so sandwiching it
between two copies of the generator gives a scalar multiple of the generator. -/
private theorem sandwich_two (x : TemperleyLieb R δ 1) :
    ∃ y : TemperleyLieb R δ 1,
      e δ (Fin.last 0) * strandIncl x * e δ (Fin.last 0) = strandIncl y * e δ (Fin.last 0) := by
  refine ⟨δ • x, ?_⟩
  rw [← (algEquivOfLeOne δ le_rfl).symm_apply_apply x, algEquivOfLeOne_symm_apply]
  simp only [Algebra.algebraMap_eq_smul_one, map_smul, map_one, mul_smul_comm, mul_one,
    smul_mul_assoc, one_mul, e_mul_self, smul_comm δ]

private theorem span_towerSpanningSet_eq_top :
    ∀ n, Submodule.span R (towerSpanningSet R δ n) = ⊤
  | 0 => span_towerSpanningSet_eq_top_of_sandwich sandwich_two
  | n + 1 => span_towerSpanningSet_eq_top_of_sandwich fun x ↦
    let ⟨y, hy⟩ := sandwich_of_span_towerSpanningSet_eq_top (span_towerSpanningSet_eq_top n) x
    ⟨strandIncl y, hy⟩

/-- **The tower normal form.** The Temperley–Lieb algebra on `n + 2` strands is spanned by the
image `strandIncl a` of the algebra on `n + 1` strands, together with the products
`strandIncl a * e δ (Fin.last n) * strandIncl b`: as `R`-modules,
`TL(n + 2) = TL(n + 1) + TL(n + 1) · e (Fin.last n) · TL(n + 1)`. -/
theorem span_strandIncl_union_strandIncl_mul_e_last_mul_eq_top (n : ℕ) :
    Submodule.span R (Set.range (strandIncl (R := R) (δ := δ) (n := n)) ∪
      Set.range fun p : TemperleyLieb R δ (n + 1) × TemperleyLieb R δ (n + 1) ↦
        strandIncl p.1 * e δ (Fin.last n) * strandIncl p.2) = ⊤ :=
  span_towerSpanningSet_eq_top n

/-- **The sandwich identity.** Sandwiching an element of the algebra on `n + 2` strands, included
on `n + 3` strands, between two copies of the last generator gives an element coming from
`n + 1` strands times the last generator: closing the last strand of `x` leaves an element of
the stage two levels down. -/
theorem exists_e_last_mul_strandIncl_mul_e_last_eq (x : TemperleyLieb R δ (n + 2)) :
    ∃ y : TemperleyLieb R δ (n + 1),
      e δ (Fin.last (n + 1)) * strandIncl x * e δ (Fin.last (n + 1)) =
        strandIncl (strandIncl y) * e δ (Fin.last (n + 1)) :=
  sandwich_of_span_towerSpanningSet_eq_top (span_towerSpanningSet_eq_top n) x

end TauCeti.TemperleyLieb
