/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Int.Basic
public import TauCeti.Algebra.Module.ZLattice.Basic

/-!
# The content of a lattice

The *content* `c_L` of a lattice `L` is the greatest common divisor of the half-norms `‖x‖² / 2`
of the vectors `x ∈ L`. It governs the level of the Fricke partner `√N • L^∨` of an even lattice
of level `N`, which is `N / gcd (N, c_L)`.

Like the level `ZLattice.level`, the content is defined directly on the real model, for every
`ℤ`-submodule of a seminormed group, so it needs no integrality hypothesis to state: it is the
nonnegative generator of the ideal of `ℤ` spanned by the half-norms of the vectors of even squared
norm. For an even lattice every vector qualifies. The content is the half-norm counterpart of the
norm ideal `TauCeti.IntegralLattice.normIdeal` of a rational lattice, the ideal spanned by the
full norms.

## Main definitions

* `ZLattice.content L`: the nonnegative generator of the ideal of `ℤ` spanned by the half-norms
  `‖x‖² / 2` of the vectors `x ∈ L` of even squared norm.

## Main statements

* `ZLattice.span_natCast_content`: the content generates the ideal spanned by the half-norms.
* `ZLattice.dvd_content_iff`: `d` divides the content exactly when it divides every half-norm.
* `ZLattice.dvd_mul_content`: if `n` divides `k` times every half-norm, it divides `k` times the
  content.
* `ZLattice.content_comap`: the content is invariant under linear isometry equivalences.
* `ZLattice.content_span_two`: the lattice `2 ℤ ⊆ ℝ` has content `2`.

## References

* W. Ebeling, *Lattices and Codes*, 3rd ed., Springer, 2013, Chapter 3.
-/

public section

open Submodule

namespace ZLattice

section Seminormed

variable {E : Type*} [SeminormedAddCommGroup E]

/-- The ideal of `ℤ` spanned by the half-norms `‖x‖² / 2` of the vectors `x ∈ L` of even squared
norm. Its nonnegative generator is the content. -/
private def halfNormIdeal (L : Submodule ℤ E) : Ideal ℤ :=
  Ideal.span {m : ℤ | ∃ x ∈ L, ‖x‖ ^ 2 = 2 * m}

/-- The **content** of a lattice `L`: the nonnegative generator of the ideal of `ℤ` spanned by the
half-norms `‖x‖² / 2` of the vectors `x ∈ L` whose squared norm is an even integer. For an even
lattice every vector qualifies, and the content is the greatest common divisor of all half-norms
of `L` (`dvd_content_iff`). -/
noncomputable def content (L : Submodule ℤ E) : ℕ :=
  (Submodule.IsPrincipal.generator (halfNormIdeal L)).natAbs

variable {L : Submodule ℤ E}

/-- The content of `L` generates the ideal of `ℤ` spanned by the half-norms `‖x‖² / 2` of the
vectors `x ∈ L` of even squared norm. -/
theorem span_natCast_content :
    Ideal.span {(content L : ℤ)} = Ideal.span {m : ℤ | ∃ x ∈ L, ‖x‖ ^ 2 = 2 * m} := by
  rw [content, Int.span_natAbs]
  exact Submodule.IsPrincipal.span_singleton_generator (halfNormIdeal L)

/-- The content is an integer combination of half-norms: it lies in the ideal they span. -/
theorem natCast_content_mem_span :
    (content L : ℤ) ∈ Ideal.span {m : ℤ | ∃ x ∈ L, ‖x‖ ^ 2 = 2 * m} :=
  span_natCast_content (L := L) ▸ Ideal.mem_span_singleton_self _

/-- `d` divides the content of `L` exactly when `d` divides every half-norm `‖x‖² / 2` of a vector
`x ∈ L` of even squared norm. -/
theorem dvd_content_iff {d : ℤ} :
    d ∣ content L ↔ ∀ x ∈ L, ∀ m : ℤ, ‖x‖ ^ 2 = 2 * m → d ∣ m := by
  rw [← Ideal.span_singleton_le_span_singleton, span_natCast_content, Ideal.span_le]
  refine ⟨fun h x hx m hm ↦ ?_, fun h m ⟨x, hx, hm⟩ ↦ ?_⟩
  · exact Ideal.mem_span_singleton.mp (h ⟨x, hx, hm⟩)
  · exact Ideal.mem_span_singleton.mpr (h x hx m hm)

/-- The content of `L` divides every half-norm `‖x‖² / 2` of a vector `x ∈ L` of even squared
norm. -/
theorem content_dvd {x : E} (hx : x ∈ L) {m : ℤ} (hm : ‖x‖ ^ 2 = 2 * m) : (content L : ℤ) ∣ m :=
  dvd_content_iff.mp dvd_rfl x hx m hm

/-- If `n` divides `k` times every half-norm `‖x‖² / 2` of a vector `x ∈ L` of even squared norm,
then it divides `k` times the content. -/
theorem dvd_mul_content {n k : ℤ} (h : ∀ x ∈ L, ∀ m : ℤ, ‖x‖ ^ 2 = 2 * m → n ∣ k * m) :
    n ∣ k * content L := by
  refine Submodule.span_induction (p := fun z _ ↦ n ∣ k * z) ?_ ?_ ?_ ?_
    (natCast_content_mem_span (L := L))
  · rintro m ⟨x, hx, hm⟩
    exact h x hx m hm
  · simp
  · intro a b _ _ ha hb
    simpa [mul_add] using dvd_add ha hb
  · intro a b _ hb
    simpa [mul_left_comm k a] using dvd_mul_of_dvd_right hb a

end Seminormed

section Normed

variable {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedSpace ℝ E]
  [NormedSpace ℝ F] {L : Submodule ℤ E}

/-- The content is invariant under linear isometry equivalences. -/
@[simp]
theorem content_comap (e : F ≃ₗᵢ[ℝ] E) :
    content (ZLattice.comap ℝ L e.toLinearEquiv.toLinearMap) = content L := by
  refine Int.natCast_dvd_natCast.mp ?_ |>.antisymm (Int.natCast_dvd_natCast.mp ?_)
  · refine dvd_content_iff.mpr fun x hx m hm ↦ content_dvd (x := e.symm x) ?_ ?_
    · simpa using hx
    · simpa using hm
  · refine dvd_content_iff.mpr fun x hx m hm ↦ content_dvd (x := e x) ?_ ?_
    · simpa using hx
    · simpa using hm

end Normed

/-! ### An example -/

/-- The lattice `2 ℤ ⊆ ℝ` has content `2`: its half-norms are the integers `2 k²`. -/
theorem content_span_two : content (span ℤ {2} : Submodule ℤ ℝ) = 2 := by
  refine Nat.dvd_antisymm (Int.natCast_dvd_natCast.mp ?_) (Int.natCast_dvd_natCast.mp ?_)
  · exact content_dvd (x := 2) (mem_span_singleton_self _) (by norm_num)
  · refine dvd_content_iff.mpr fun x hx m hm ↦ ?_
    obtain ⟨k, rfl⟩ := mem_span_singleton.mp hx
    have hk : ‖k • (2 : ℝ)‖ ^ 2 = 4 * k ^ 2 := by
      norm_num [zsmul_eq_mul, mul_pow, mul_comm]
    refine ⟨k ^ 2, Int.cast_injective (α := ℝ) ?_⟩
    push_cast
    linarith

end ZLattice
