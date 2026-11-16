/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.Ideal.Colon
public import Mathlib.RingTheory.Localization.Ideal

/-!
# Colon ideals and quotient annihilators

For an `R`-algebra `S`, the ideal `(N : x)` of a submodule `N` of an `S`-module commutes with
restricting scalars to `R`.

For an ideal `I` and an element `f` of a commutative ring, `I ∩ (f) = f · (I : f)`. When `f` is
regular this determines `(I : f)`: generators of `I ∩ (f)`, which an intersection computation
supplies, divided by `f` generate `(I : f)`. Colon ideals with finitely generated denominators also
commute with localization: `(I : J) S = (I S : J S)`.

## Main results

* `Submodule.le_annihilator_quotient_iff`: an ideal annihilates a quotient exactly when its
  multiples of the ambient module lie in the submodule.
* `Submodule.comap_colon_singleton`: the ideal `(N : x)` of `R` is the preimage of the ideal
  `(N : x)` of `S`.
* `Ideal.inf_span_singleton_eq_span_singleton_mul_colon`: `I ∩ (f) = f · (I : f)`.
* `Ideal.colon_singleton_eq_of_inf_span_singleton_eq`: for regular `f`, if `I ∩ (f) = f · J`
  then `(I : f) = J`.
* `Ideal.colon_span_singleton_mul_of_isLeftRegular`: for regular `f`, `((f) · J : (f)) = J`.
* `Ideal.exists_eq_span_pow_mul_colon_not_le`: an ideal not contained in every power of `(f)` is
  `(f ^ k) · (I : f ^ k)` with `(I : f ^ k)` not contained in `(f)`.
* `Ideal.map_colon_of_isLocalization`: for finitely generated `J`, colon ideals commute with
  localization.

## References

* D. Cox, J. Little, D. O'Shea, *Ideals, Varieties, and Algorithms*, Chapter 4, §4,
  computing ideal quotients from intersections.
-/

public section

open scoped Pointwise

/-- An ideal annihilates a quotient exactly when its multiples of the ambient module lie in
the submodule being quotiented out. -/
theorem Submodule.le_annihilator_quotient_iff {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]
    {I : Ideal R} {N : Submodule R M} :
    I ≤ Module.annihilator R (M ⧸ N) ↔ I • (⊤ : Submodule R M) ≤ N := by
  rw [Submodule.annihilator_quotient, Submodule.smul_le]
  simp only [IsConcreteLE.le_iff, Submodule.mem_colon, Submodule.mem_top, Set.mem_univ,
    forall_true_left]

variable {R S M : Type*} [CommSemiring R] [CommSemiring S] [Algebra R S] [AddCommMonoid M]
  [Module R M] [Module S M] [IsScalarTower R S M]

/-- For a submodule `N` of an `S`-module `M` and `x ∈ M`, the ideal `(N : x)` of `R` is the
preimage of the ideal `(N : x)` of `S`. -/
theorem Submodule.comap_colon_singleton (N : Submodule S M) (x : M) :
    (N.colon {x}).comap (algebraMap R S) = (N.restrictScalars R).colon {x} := by
  ext r
  simp [Submodule.mem_colon_singleton]

namespace Ideal

variable {R : Type*} [CommSemiring R] {I J : Ideal R} {f : R}

/-- The intersection of an ideal `I` with the principal ideal `(f)` is `f` times the colon ideal
`(I : f)`. -/
theorem inf_span_singleton_eq_span_singleton_mul_colon (I : Ideal R) (f : R) :
    I ⊓ span {f} = span {f} * I.colon {f} := by
  ext x
  simp only [mem_inf, mem_span_singleton_mul, mem_span_singleton', Submodule.mem_colon_singleton,
    smul_eq_mul]
  constructor
  · rintro ⟨hx, a, rfl⟩
    exact ⟨a, hx, mul_comm f a⟩
  · rintro ⟨a, ha, rfl⟩
    exact ⟨mul_comm f a ▸ ha, a, mul_comm a f⟩

/-- **Colon ideals from intersections.** If `f` is regular and `I ∩ (f) = f · J`, then the colon
ideal `(I : f)` is `J`. -/
theorem colon_singleton_eq_of_inf_span_singleton_eq (hf : IsLeftRegular f)
    (h : I ⊓ span {f} = span {f} * J) : I.colon {f} = J := by
  rw [inf_span_singleton_eq_span_singleton_mul_colon, span_singleton_mul_eq_span_singleton_mul]
    at h
  refine le_antisymm (fun x hx ↦ ?_) fun y hy ↦ ?_
  · obtain ⟨y, hy, hxy⟩ := h.1 x hx
    exact hf hxy ▸ hy
  · obtain ⟨x, hx, hxy⟩ := h.2 y hy
    exact hf hxy ▸ hx

/-- **Extracting a power of a principal ideal.** If an ideal `I` does not lie in every power of
`(f)`, then `I = (f ^ k) · (I : f ^ k)` for some `k`, where the colon ideal `(I : f ^ k)` does not
lie in `(f)`. -/
theorem exists_eq_span_pow_mul_colon_not_le (h : ∃ n, ¬ I ≤ span {f ^ n}) :
    ∃ k, I = span {f ^ k} * I.colon {f ^ k} ∧ ¬ I.colon {f ^ k} ≤ span {f} := by
  classical
  have h' : ∃ k, ¬ I ≤ span {f ^ (k + 1)} := by
    obtain ⟨n, hn⟩ := h
    exact ⟨n, fun hle ↦ hn (hle.trans
      (span_singleton_le_span_singleton.2 (pow_dvd_pow f n.le_succ)))⟩
  have hIk : I ≤ span {f ^ Nat.find h'} := by
    rcases hk : Nat.find h' with _ | j
    · simp
    · exact not_not.1 (Nat.find_min h' (by omega))
  refine ⟨Nat.find h', ?_, fun hle ↦ Nat.find_spec h' fun x hx ↦ ?_⟩
  · rw [← inf_span_singleton_eq_span_singleton_mul_colon, inf_eq_left.2 hIk]
  · obtain ⟨a, rfl⟩ := mem_span_singleton'.1 (hIk hx)
    obtain ⟨d, rfl⟩ := mem_span_singleton'.1 (hle (Submodule.mem_colon_singleton.2 hx))
    exact mem_span_singleton'.2 ⟨d, by ring⟩

/-- For a left-regular element `f`, dividing the product `(f) · J` by `(f)` recovers `J`. -/
theorem colon_span_singleton_mul_of_isLeftRegular (hf : IsLeftRegular f) :
    (span {f} * J).colon (span {f} : Set R) = J := by
  rw [colon_span]
  exact colon_singleton_eq_of_inf_span_singleton_eq hf (inf_eq_left.mpr mul_le_left)

/-- **Colon ideals commute with localization for finitely generated denominators.** If `J` is a
finitely generated ideal of `R` and `S` is a localization of `R` at a submonoid `M`, then
`(I : J) S = (I S : J S)`. -/
theorem map_colon_of_isLocalization (M : Submonoid R) (S : Type*) [CommSemiring S]
    [Algebra R S] [IsLocalization M S] (hJ : J.FG) :
    (I.colon (J : Set R)).map (algebraMap R S) =
      (I.map (algebraMap R S)).colon (J.map (algebraMap R S) : Set S) := by
  classical
  refine le_antisymm (map_le_iff_le_comap.mpr fun r hr ↦ Submodule.mem_colon.mpr fun y hy ↦ ?_) ?_
  · rw [Ideal.map] at hy
    induction hy using Submodule.span_induction with
    | mem _ h =>
      obtain ⟨j, hj, rfl⟩ := h
      rw [smul_eq_mul, ← map_mul]
      exact mem_map_of_mem _ (Submodule.mem_colon.mp hr j hj)
    | zero => rw [smul_zero]; exact zero_mem _
    | add _ _ _ _ hx hy => simpa only [smul_add] using add_mem hx hy
    | smul c _ _ hx => rw [smul_comm]; exact Submodule.smul_mem _ c hx
  · intro z hz
    obtain ⟨s, rfl⟩ := hJ
    obtain ⟨x, m, rfl⟩ := IsLocalization.exists_mk'_eq M z
    have hmul (j : s) : ∃ c : M, (c : R) * (x * j.1) ∈ I := by
      have hmem : IsLocalization.mk' S x m * algebraMap R S j.1 ∈ I.map (algebraMap R S) :=
        Submodule.mem_colon.mp hz _ (mem_map_of_mem _ (subset_span j.2))
      rw [mul_comm, IsLocalization.mul_mk'_eq_mk'_of_mul, mul_comm j.1 x,
        IsLocalization.mk'_mem_map_algebraMap_iff] at hmem
      obtain ⟨c, hcM, hcI⟩ := hmem
      exact ⟨⟨c, hcM⟩, hcI⟩
    choose c hc using hmul
    let C : M := ∏ j : s, c j
    have hCx : (C : R) * x ∈ I.colon (span (s : Set R) : Set R) := by
      rw [colon_span, Submodule.mem_colon]
      intro j hj
      let j' : s := ⟨j, hj⟩
      have hC : (C : R) = (c j' : R) * (∏ k ∈ Finset.univ.erase j', (c k : R)) := by
        simpa [C] using
          congrArg Subtype.val (Finset.mul_prod_erase Finset.univ c (Finset.mem_univ j')).symm
      rw [smul_eq_mul, hC, mul_comm (c j' : R), mul_assoc, mul_assoc]
      exact mul_mem_left I _ (hc j')
    have hmk : IsLocalization.mk' S x m = IsLocalization.mk' S ((C : R) * x) (C * m) :=
      IsLocalization.mk'_eq_of_eq (by simp [mul_left_comm, mul_comm])
    rw [hmk, IsLocalization.mk'_mem_map_algebraMap_iff]
    exact ⟨1, one_mem M, by simpa using hCx⟩

end Ideal
