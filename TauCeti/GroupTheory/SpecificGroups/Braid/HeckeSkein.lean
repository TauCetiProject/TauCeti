/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Algebra.MonoidAlgebra.MapDomain
public import TauCeti.GroupTheory.SpecificGroups.Braid.Basic
import Mathlib.Tactic.Abel

/-!
# The Hecke skein relation on braid group algebras

Over a commutative ring `S` with a parameter `z`, the Hecke skein submodule of the group algebra
`S[BraidGroup n]` is spanned by the elements `b * σᵢ * c - b * σᵢ⁻¹ * c - z • (b * c)`. It is a
two-sided ideal, and the quotient by it is the Iwahori-Hecke algebra of type `A` in the skein
normalization `gᵢ - gᵢ⁻¹ = z`.

The main result is the spanning half of the inductive structure of these Hecke algebras, the
decomposition `H(n + 2) = H(n + 1) + H(n + 1) σ H(n + 1)` with `σ` the last elementary braid:
modulo the Hecke skein submodule, every element
of `S[BraidGroup (n + 2)]` is an `S`-linear combination of braids of the forms `ι b` and
`ι b * σ * ι c`, where `ι` adds an uncrossed last strand and `σ` is the last elementary braid
(`TauCeti.BraidGroup.strandSpan_sup_heckeSkein_eq_top`). This is the input to the trace-theoretic
construction of the HOMFLY polynomial: a Markov trace is determined on the second kind of braid by
its value on `c * b`, and on the first by its value on `b`, so induction on the number of strands
evaluates it everywhere.

## Main definitions

* `TauCeti.BraidGroup.heckeSkein S z n`: the span of the Hecke skein relators in all braid
  contexts.
* `TauCeti.BraidGroup.strandSpan S n`: the span of the braids `ι b` and `ι b * σ * ι c` in
  `S[BraidGroup (n + 2)]`.

## Main results

* `TauCeti.BraidGroup.mul_mem_heckeSkein` and `TauCeti.BraidGroup.mem_heckeSkein_mul`: the Hecke
  skein submodule is a two-sided ideal.
* `TauCeti.BraidGroup.strandSpan_sup_heckeSkein_eq_top`: the spanning decomposition.

## References

* V. F. R. Jones, *Hecke algebra representations of braid groups and link polynomials*,
  Ann. of Math. 126 (1987), 335–388, Section 4 (the decomposition of the Hecke algebras used
  for the Ocneanu trace).
* C. Kassel, V. Turaev, *Braid Groups*, Graduate Texts in Mathematics 247, Springer (2008),
  Section 4.2.
-/

public section

noncomputable section

open MonoidAlgebra

namespace TauCeti

namespace BraidGroup

variable (S : Type*) [CommRing S] (z : S) {n : ℕ}

/-- The Hecke skein relator `b * σᵢ * c - b * σᵢ⁻¹ * c - z • (b * c)` in the group algebra. -/
def heckeRelator (b c : BraidGroup n) (i : Fin (n - 1)) : S[BraidGroup n] :=
  single (b * sigma i * c) 1 - single (b * (sigma i)⁻¹ * c) 1 - single (b * c) z

/-- The defining formula of a Hecke skein relator. -/
theorem heckeRelator_def (b c : BraidGroup n) (i : Fin (n - 1)) :
    heckeRelator S z b c i =
      single (b * sigma i * c) 1 - single (b * (sigma i)⁻¹ * c) 1 - single (b * c) z :=
  (rfl)

variable (n) in
/-- The Hecke skein submodule of `S[BraidGroup n]`: the `S`-span of the Hecke skein relators
`b * σᵢ * c - b * σᵢ⁻¹ * c - z • (b * c)` over all braids `b`, `c` and elementary braids `σᵢ`.
It is a two-sided ideal (`mul_mem_heckeSkein`, `mem_heckeSkein_mul`). -/
def heckeSkein : Submodule S S[BraidGroup n] :=
  Submodule.span S (Set.range fun p : BraidGroup n × BraidGroup n × Fin (n - 1) ↦
    heckeRelator S z p.1 p.2.1 p.2.2)

/-- Every Hecke skein relator lies in the Hecke skein submodule. -/
theorem heckeRelator_mem_heckeSkein (b c : BraidGroup n) (i : Fin (n - 1)) :
    heckeRelator S z b c i ∈ heckeSkein S z n :=
  Submodule.subset_span ⟨(b, c, i), rfl⟩

/-- A submodule contains the Hecke skein submodule exactly when it contains every relator. -/
theorem heckeSkein_le_iff {p : Submodule S S[BraidGroup n]} :
    heckeSkein S z n ≤ p ↔ ∀ b c i, heckeRelator S z b c i ∈ p := by
  rw [heckeSkein, Submodule.span_le, Set.range_subset_iff]
  exact ⟨fun h b c i ↦ h (b, c, i), fun h q ↦ h q.1 q.2.1 q.2.2⟩

private theorem single_mul_heckeRelator (g b c : BraidGroup n) (i : Fin (n - 1)) :
    single g 1 * heckeRelator S z b c i = heckeRelator S z (g * b) c i := by
  simp only [heckeRelator_def, mul_sub, single_mul_single, one_mul, mul_assoc]

private theorem heckeRelator_mul_single (g b c : BraidGroup n) (i : Fin (n - 1)) :
    heckeRelator S z b c i * single g 1 = heckeRelator S z b (c * g) i := by
  simp only [heckeRelator_def, sub_mul, single_mul_single, mul_one, mul_assoc]

/-- The Hecke skein submodule is a left ideal. -/
theorem mul_mem_heckeSkein (x : S[BraidGroup n]) {y : S[BraidGroup n]}
    (hy : y ∈ heckeSkein S z n) : x * y ∈ heckeSkein S z n := by
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨⟨b, c, i⟩, rfl⟩ := hy
    induction x using MonoidAlgebra.induction_on with
    | of g =>
      rw [of_apply, single_mul_heckeRelator]
      exact heckeRelator_mem_heckeSkein S z _ _ _
    | add x x' hx hx' => rw [add_mul]; exact add_mem hx hx'
    | smul r x hx => rw [smul_mul_assoc]; exact Submodule.smul_mem _ r hx
  | zero => rw [mul_zero]; exact zero_mem _
  | add y y' _ _ hy hy' => rw [mul_add]; exact add_mem hy hy'
  | smul r y _ hy => rw [mul_smul_comm]; exact Submodule.smul_mem _ r hy

/-- The Hecke skein submodule is a right ideal. -/
theorem mem_heckeSkein_mul {x : S[BraidGroup n]} (hx : x ∈ heckeSkein S z n)
    (y : S[BraidGroup n]) : x * y ∈ heckeSkein S z n := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨⟨b, c, i⟩, rfl⟩ := hx
    induction y using MonoidAlgebra.induction_on with
    | of g =>
      rw [of_apply, heckeRelator_mul_single]
      exact heckeRelator_mem_heckeSkein S z _ _ _
    | add y y' hy hy' => rw [mul_add]; exact add_mem hy hy'
    | smul r y hy => rw [mul_smul_comm]; exact Submodule.smul_mem _ r hy
  | zero => rw [zero_mul]; exact zero_mem _
  | add x x' _ _ hx hx' => rw [add_mul]; exact add_mem hx hx'
  | smul r x _ hx => rw [smul_mul_assoc]; exact Submodule.smul_mem _ r hx

/-- Adding an uncrossed strand carries the Hecke skein submodule into the Hecke skein submodule
of the larger braid group. -/
theorem mapDomain_strandIncl_mem_heckeSkein {x : S[BraidGroup (n + 1)]}
    (hx : x ∈ heckeSkein S z (n + 1)) :
    mapDomainAlgHom S S strandIncl x ∈ heckeSkein S z (n + 2) := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨⟨b, c, i⟩, rfl⟩ := hx
    have h : mapDomainAlgHom S S strandIncl (heckeRelator S z b c i) =
        heckeRelator S z (strandIncl b) (strandIncl c) (n := n + 2) i.castSucc := by
      simp only [heckeRelator_def, map_sub, mapDomainAlgHom_apply, mapDomain_single, map_mul,
        map_inv, strandIncl_sigma]
    rw [h]
    exact heckeRelator_mem_heckeSkein S z _ _ _
  | zero => rw [map_zero]; exact zero_mem _
  | add x x' _ _ hx hx' => rw [map_add]; exact add_mem hx hx'
  | smul r x _ hx => rw [map_smul]; exact Submodule.smul_mem _ r hx

variable (n) in
/-- The span in `S[BraidGroup (n + 2)]` of the braids `ι b` and `ι b * σ * ι c`, where `ι` adds an
uncrossed last strand and `σ` is the last elementary braid, crossing the new strand. -/
def strandSpan : Submodule S S[BraidGroup (n + 2)] :=
  Submodule.span S
    (Set.range (fun b : BraidGroup (n + 1) ↦ single (strandIncl b) (1 : S)) ∪
      Set.range fun p : BraidGroup (n + 1) × BraidGroup (n + 1) ↦
        single (strandIncl p.1 * sigma (n := n + 2) (Fin.last n) * strandIncl p.2) (1 : S))

/-- A submodule contains `strandSpan` exactly when it contains the braids `ι b` and
`ι b * σ * ι c`. -/
theorem strandSpan_le_iff {p : Submodule S S[BraidGroup (n + 2)]} :
    strandSpan S n ≤ p ↔ (∀ b, single (strandIncl b) (1 : S) ∈ p) ∧
      ∀ b c, single (strandIncl b * sigma (n := n + 2) (Fin.last n) * strandIncl c) (1 : S) ∈
        p := by
  rw [strandSpan, Submodule.span_le, Set.union_subset_iff, Set.range_subset_iff,
    Set.range_subset_iff]
  exact and_congr Iff.rfl ⟨fun h b c ↦ h (b, c), fun h q ↦ h q.1 q.2⟩

/-- A braid with an uncrossed last strand lies in `strandSpan`. -/
theorem single_strandIncl_mem_strandSpan (b : BraidGroup (n + 1)) :
    single (strandIncl b) (1 : S) ∈ strandSpan S n :=
  Submodule.subset_span (Or.inl ⟨b, rfl⟩)

/-- A braid crossing the last strand once, at the last elementary braid, lies in `strandSpan`. -/
theorem single_strandIncl_mul_sigma_mul_strandIncl_mem_strandSpan (b c : BraidGroup (n + 1)) :
    single (strandIncl b * sigma (n := n + 2) (Fin.last n) * strandIncl c) (1 : S) ∈
      strandSpan S n :=
  Submodule.subset_span (Or.inr ⟨(b, c), rfl⟩)

/-! ### The spanning decomposition -/

/-- Conjugating `ι d` past the last crossing on both sides doubles that crossing. -/
private theorem mul_sigma_mul_strandIncl_strandIncl_mul_sigma (g : BraidGroup (n + 3))
    (d : BraidGroup (n + 1)) :
    g * sigma (Fin.last (n + 1)) * strandIncl (strandIncl d) * sigma (Fin.last (n + 1)) =
      g * strandIncl (strandIncl d) * sigma (Fin.last (n + 1)) * sigma (Fin.last (n + 1)) := by
  rw [mul_assoc g, (commute_sigma_last_strandIncl_strandIncl d).eq, ← mul_assoc]

/-- Conjugating `ι d * σ' * ι e` past the last crossing `σ` on both sides, where `σ'` is the
crossing below it, moves `σ` between two copies of `σ'` by the braid relation. -/
private theorem mul_sigma_mul_strandIncl_mul_sigma (g : BraidGroup (n + 3))
    (d e : BraidGroup (n + 1)) :
    g * sigma (Fin.last (n + 1)) *
        strandIncl (strandIncl d * sigma (n := n + 2) (Fin.last n) * strandIncl e) *
        sigma (Fin.last (n + 1)) =
      g * strandIncl (strandIncl d * sigma (n := n + 2) (Fin.last n)) * sigma (Fin.last (n + 1)) *
        strandIncl (sigma (n := n + 2) (Fin.last n) * strandIncl e) := by
  have hbraid (x : BraidGroup (n + 3)) :
      sigma (Fin.last (n + 1)) * (strandIncl (sigma (n := n + 2) (Fin.last n)) *
        (sigma (Fin.last (n + 1)) * x)) =
      strandIncl (sigma (n := n + 2) (Fin.last n)) * (sigma (Fin.last (n + 1)) *
        (strandIncl (sigma (n := n + 2) (Fin.last n)) * x)) := by
    rw [strandIncl_sigma, ← mul_assoc, ← mul_assoc, sigma_braid (Or.inr (by simp)), mul_assoc,
      mul_assoc]
  have hd := (commute_sigma_last_strandIncl_strandIncl d).eq
  have he := (commute_sigma_last_strandIncl_strandIncl e).eq
  simp only [map_mul, mul_assoc]
  rw [← mul_assoc (sigma _) (strandIncl (strandIncl d)), hd, ← he]
  simp only [mul_assoc]
  rw [hbraid]

variable {S z}

/-- Removing a doubled crossing: `g * σ * σ = g + z • (g * σ)` modulo the Hecke skein submodule. -/
private theorem single_mul_sigma_mul_sigma_mem (g : BraidGroup (n + 1)) :
    single (strandIncl g * sigma (n := n + 2) (Fin.last n) * sigma (Fin.last n)) (1 : S) ∈
      strandSpan S n ⊔ heckeSkein S z (n + 2) := by
  have h : single (strandIncl g * sigma (n := n + 2) (Fin.last n) * sigma (Fin.last n)) (1 : S) =
      heckeRelator S z (strandIncl g * sigma (Fin.last n)) 1 (Fin.last n) +
        single (strandIncl g) 1 +
        z • single (strandIncl g * sigma (n := n + 2) (Fin.last n) * strandIncl 1) 1 := by
    simp [heckeRelator_def]
    abel
  rw [h]
  refine add_mem (add_mem (Submodule.mem_sup_right (heckeRelator_mem_heckeSkein S z _ _ _))
    (Submodule.mem_sup_left (single_strandIncl_mem_strandSpan S g))) ?_
  exact Submodule.smul_mem _ z (Submodule.mem_sup_left
    (single_strandIncl_mul_sigma_mul_strandIncl_mem_strandSpan S g 1))

/-- Right multiplication by an elementary braid preserves `strandSpan ⊔ heckeSkein`, once the
products `ι b * σ * ι c * σ` are known to lie in it. -/
private theorem mul_single_sigma_mem
    (h : ∀ b c : BraidGroup (n + 1),
      single (strandIncl b * sigma (n := n + 2) (Fin.last n) * strandIncl c *
        sigma (Fin.last n)) (1 : S) ∈ strandSpan S n ⊔ heckeSkein S z (n + 2))
    (i : Fin (n + 1)) {x : S[BraidGroup (n + 2)]}
    (hx : x ∈ strandSpan S n ⊔ heckeSkein S z (n + 2)) :
    x * single (sigma (n := n + 2) i) 1 ∈ strandSpan S n ⊔ heckeSkein S z (n + 2) := by
  obtain ⟨m, hm, r, hr, rfl⟩ := Submodule.mem_sup.mp hx
  clear hx
  rw [add_mul]
  refine add_mem ?_ (Submodule.mem_sup_right (mem_heckeSkein_mul S z hr _))
  induction hm using Submodule.span_induction with
  | mem m hm =>
    rcases hm with ⟨b, rfl⟩ | ⟨⟨b, c⟩, rfl⟩
    · rw [single_mul_single, one_mul]
      induction i using Fin.lastCases with
      | last =>
        simpa using Submodule.mem_sup_left
          (single_strandIncl_mul_sigma_mul_strandIncl_mem_strandSpan S b 1)
      | cast j =>
        rw [← strandIncl_sigma, ← map_mul]
        exact Submodule.mem_sup_left (single_strandIncl_mem_strandSpan S _)
    · rw [single_mul_single, one_mul]
      induction i using Fin.lastCases with
      | last => exact h b c
      | cast j =>
        rw [← strandIncl_sigma, mul_assoc _ (strandIncl c), ← map_mul]
        exact Submodule.mem_sup_left
          (single_strandIncl_mul_sigma_mul_strandIncl_mem_strandSpan S b _)
  | zero => rw [zero_mul]; exact zero_mem _
  | add m m' _ _ hm hm' => rw [add_mul]; exact add_mem hm hm'
  | smul r m _ hm => rw [smul_mul_assoc]; exact Submodule.smul_mem _ r hm

/-- The step of the decomposition: once the products `ι b * σ * ι c * σ` are known to decompose,
every element does. -/
private theorem strandSpan_sup_heckeSkein_eq_top_of_forall
    (h : ∀ b c : BraidGroup (n + 1),
      single (strandIncl b * sigma (n := n + 2) (Fin.last n) * strandIncl c *
        sigma (Fin.last n)) (1 : S) ∈ strandSpan S n ⊔ heckeSkein S z (n + 2)) :
    strandSpan S n ⊔ heckeSkein S z (n + 2) = ⊤ := by
  set T := strandSpan S n ⊔ heckeSkein S z (n + 2)
  -- Right multiplication by an inverse elementary braid preserves `T`, by the skein relation.
  have hsigmaInv (i : Fin (n + 1)) {x : S[BraidGroup (n + 2)]} (hx : x ∈ T) :
      x * single (sigma (n := n + 2) i)⁻¹ 1 ∈ T := by
    have hinv : single (sigma (n := n + 2) i)⁻¹ (1 : S) =
        single (sigma i) 1 - z • 1 - heckeRelator S z 1 1 i := by
      simp [heckeRelator_def, one_def]
    rw [hinv, mul_sub, mul_sub, mul_smul_comm, mul_one]
    exact sub_mem (sub_mem (mul_single_sigma_mem h i hx) (Submodule.smul_mem _ z hx))
      (Submodule.mem_sup_right (mul_mem_heckeSkein S z _ (heckeRelator_mem_heckeSkein S z _ _ _)))
  -- Hence right multiplication by every braid preserves `T`.
  have hbraid (g : BraidGroup (n + 2)) : ∀ x ∈ T,
      x * single g 1 ∈ T ∧ x * single g⁻¹ 1 ∈ T := by
    induction g using sigma_induction_on with
    | sigma i => exact fun x hx ↦ ⟨mul_single_sigma_mem h i hx, hsigmaInv i hx⟩
    | one => simp [← one_def]
    | mul g g' hg hg' =>
      intro x hx
      refine ⟨?_, ?_⟩
      · rw [← mul_one (1 : S), ← single_mul_single, ← mul_assoc]
        exact (hg' _ (hg x hx).1).1
      · rw [mul_inv_rev, ← mul_one (1 : S), ← single_mul_single, ← mul_assoc]
        exact (hg _ (hg' x hx).2).2
    | inv g hg => exact fun x hx ↦ ⟨(hg x hx).2, by simpa using (hg x hx).1⟩
  rw [eq_top_iff]
  rintro x -
  induction x using MonoidAlgebra.induction_on with
  | of g =>
    have h1 : single (1 : BraidGroup (n + 2)) (1 : S) ∈ T := by
      simpa using Submodule.mem_sup_left
        (single_strandIncl_mem_strandSpan S (1 : BraidGroup (n + 1)))
    simpa [of_apply] using (hbraid g _ h1).1
  | add x x' hx hx' => exact add_mem hx hx'
  | smul r x hx => exact Submodule.smul_mem _ r hx

/-- The decomposition one level down survives conjugation past the two new crossings: if `y`
decomposes in `S[BraidGroup (n + 2)]`, then `ι b * σ * ι y * σ` decomposes one level up. -/
private theorem single_mul_mapDomain_mul_single_mem (b : BraidGroup (n + 2))
    {y : S[BraidGroup (n + 2)]} (hy : y ∈ strandSpan S n ⊔ heckeSkein S z (n + 2)) :
    single (strandIncl b * sigma (n := n + 3) (Fin.last (n + 1))) 1 *
        mapDomainAlgHom S S strandIncl y * single (sigma (n := n + 3) (Fin.last (n + 1))) 1 ∈
      strandSpan S (n + 1) ⊔ heckeSkein S z (n + 3) := by
  let L : S[BraidGroup (n + 2)] →ₗ[S] S[BraidGroup (n + 3)] :=
    LinearMap.mulRight S (single (sigma (n := n + 3) (Fin.last (n + 1))) 1) ∘ₗ
      LinearMap.mulLeft S (single (strandIncl b * sigma (n := n + 3) (Fin.last (n + 1))) 1) ∘ₗ
        (mapDomainAlgHom S S strandIncl).toLinearMap
  have hL (y : S[BraidGroup (n + 2)]) : L y =
      single (strandIncl b * sigma (n := n + 3) (Fin.last (n + 1))) 1 *
        mapDomainAlgHom S S strandIncl y * single (sigma (n := n + 3) (Fin.last (n + 1))) 1 :=
    (rfl)
  have hle : strandSpan S n ⊔ heckeSkein S z (n + 2) ≤
      (strandSpan S (n + 1) ⊔ heckeSkein S z (n + 3)).comap L := by
    refine sup_le ((strandSpan_le_iff S).mpr ⟨fun d ↦ ?_, fun d e ↦ ?_⟩)
      ((heckeSkein_le_iff S z).mpr fun d e i ↦ ?_) <;> rw [Submodule.mem_comap, hL]
    · simp only [mapDomainAlgHom_apply, mapDomain_single, single_mul_single, one_mul]
      rw [mul_sigma_mul_strandIncl_strandIncl_mul_sigma, ← map_mul]
      exact single_mul_sigma_mul_sigma_mem (b * strandIncl d)
    · simp only [mapDomainAlgHom_apply, mapDomain_single, single_mul_single, one_mul]
      rw [mul_sigma_mul_strandIncl_mul_sigma, ← map_mul]
      exact Submodule.mem_sup_left
        (single_strandIncl_mul_sigma_mul_strandIncl_mem_strandSpan S _ _)
    · exact Submodule.mem_sup_right (mem_heckeSkein_mul S z (mul_mem_heckeSkein S z _
        (mapDomain_strandIncl_mem_heckeSkein S z (heckeRelator_mem_heckeSkein S z d e i))) _)
  exact hle hy

variable (S z)

/-- **The spanning decomposition of the braid group algebra modulo the Hecke skein relation.**
Every element of `S[BraidGroup (n + 2)]` is, modulo the Hecke skein submodule, an `S`-linear
combination of braids `ι b` and `ι b * σ * ι c`, where `ι` adds an uncrossed last strand and `σ`
is the last elementary braid. -/
theorem strandSpan_sup_heckeSkein_eq_top (n : ℕ) :
    strandSpan S n ⊔ heckeSkein S z (n + 2) = ⊤ := by
  induction n with
  | zero =>
    refine strandSpan_sup_heckeSkein_eq_top_of_forall fun b c ↦ ?_
    have hc : c = 1 := by
      have h : MonoidHom.id (BraidGroup 1) = 1 := hom_ext fun i ↦ i.elim0
      exact DFunLike.congr_fun h c
    simpa [hc] using single_mul_sigma_mul_sigma_mem (S := S) (z := z) b
  | succ m ih =>
    refine strandSpan_sup_heckeSkein_eq_top_of_forall fun b c ↦ ?_
    simpa [mapDomain_single, single_mul_single, mul_assoc] using
      single_mul_mapDomain_mul_single_mem b (ih ▸ Submodule.mem_top : single c (1 : S) ∈ _)

end BraidGroup

end TauCeti
