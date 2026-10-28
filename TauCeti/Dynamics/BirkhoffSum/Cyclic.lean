/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Dynamics.BirkhoffSum.Average
public import Mathlib.Dynamics.PeriodicPts.Defs
import Mathlib.Tactic.Abel

/-!
# The cohomological equation for a finite cyclic orbit

For a self-map `r` with `r^[m] = id`, the orbit sum of a function `b` is invariant under `r`.
If `m` is invertible in the scalar field, an explicit weighted orbit sum gives a correction `c`
satisfying `b + c ∘ r - c = birkhoffAverage 𝕜 r b m`. In particular, an invariant function `a`
can be obtained by this change of coordinates exactly when the orbit sum of `b` is `m • a`.

Applied to a lifted translation section over a rotated disc, this normalizes the translation
part to its invariant average without replacing a varying period lattice by a constant one.
The correction is a finite linear combination of compositions, so it also preserves regularity.

The normalization is the finite cyclic averaging calculation in the logarithmic-transform
construction of Barth--Hulek--Peters--Van de Ven, *Compact Complex Surfaces*, second edition,
Chapter V, section on logarithmic transformations.
-/

public section

open Function Finset

/-- The orbit sum at a periodic point is invariant under the generator. -/
theorem Function.IsPeriodicPt.birkhoffSum_apply_eq {X E : Type*} [AddCommMonoid E]
    {r : X → X} {m : ℕ} {x : X} (hx : IsPeriodicPt r m x) (b : X → E) :
    birkhoffSum r b m (r x) = birkhoffSum r b m x := by
  cases m with
  | zero => simp
  | succ n =>
    rw [birkhoffSum_succ_apply, ← iterate_succ_apply, hx.eq,
      birkhoffSum_succ_apply', add_comm]

/-- The difference of weighted orbit sums telescopes at a periodic point. -/
theorem Function.IsPeriodicPt.sum_range_nsmul_iterate_apply_sub {X E : Type*}
    [AddCommGroup E] {r : X → X} {m : ℕ} {x : X} (hx : IsPeriodicPt r m x) (b : X → E) :
    (∑ j ∈ range m, j • b (r^[j] (r x))) - (∑ j ∈ range m, j • b (r^[j] x)) =
      m • b x - birkhoffSum r b m x := by
  have hterm (j : ℕ) :
      j • b (r^[j] (r x)) - j • b (r^[j] x) =
        ((j + 1) • b (r^[j + 1] x) - j • b (r^[j] x)) - b (r^[j + 1] x) := by
    simp only [iterate_succ_apply, add_nsmul, one_nsmul]
    abel
  rw [← sum_sub_distrib]
  simp_rw [hterm]
  rw [sum_sub_distrib, sum_range_sub (fun j ↦ j • b (r^[j] x))]
  simpa [birkhoffSum, hx.eq, iterate_succ_apply] using
    congrArg (m • b x - ·) (hx.birkhoffSum_apply_eq b)

namespace TauCeti

/-- An orbit average equals a prescribed value when the orbit sum is `m` times that value. -/
theorem birkhoffAverage_eq_of_birkhoffSum_eq_nsmul {𝕜 X E : Type*}
    [DivisionSemiring 𝕜] [AddCommMonoid E] [Module 𝕜 E]
    {r : X → X} {b : X → E} {m : ℕ} {x : X} {a : E}
    (hm : (m : 𝕜) ≠ 0) (hsum : birkhoffSum r b m x = m • a) :
    birkhoffAverage 𝕜 r b m x = a := by
  simp [birkhoffAverage, hsum, ← Nat.cast_smul_eq_nsmul 𝕜, smul_smul, hm]

variable {𝕜 X E : Type*} [DivisionRing 𝕜] [AddCommGroup E] [Module 𝕜 E]

/-- The weighted orbit correction `-(1/m) ∑ j < m, j • b (r^[j] x)` for a cyclic translation
section. Its definition needs no periodicity or nonzero assumption on `m`. -/
noncomputable def cyclicCorrection (𝕜 : Type*) [DivisionRing 𝕜] [Module 𝕜 E]
    (r : X → X) (b : X → E) (m : ℕ) (x : X) : E :=
  -(m : 𝕜)⁻¹ • ∑ j ∈ range m, j • b (r^[j] x)

/-- The explicit weighted orbit formula for the cyclic correction. -/
theorem cyclicCorrection_apply (r : X → X) (b : X → E) (m : ℕ) (x : X) :
    cyclicCorrection 𝕜 r b m x = -(m : 𝕜)⁻¹ • ∑ j ∈ range m, j • b (r^[j] x) := (rfl)

/-- Adding translation sections adds their cyclic corrections. -/
@[simp]
theorem cyclicCorrection_add (r : X → X) (b d : X → E) (m : ℕ) :
    cyclicCorrection 𝕜 r (b + d) m = cyclicCorrection 𝕜 r b m + cyclicCorrection 𝕜 r d m := by
  ext x
  simp [cyclicCorrection_apply, sum_add_distrib, smul_add]

/-- Subtracting sections subtracts their cyclic corrections. -/
@[simp]
theorem cyclicCorrection_sub (r : X → X) (b d : X → E) (m : ℕ) :
    cyclicCorrection 𝕜 r (b - d) m = cyclicCorrection 𝕜 r b m - cyclicCorrection 𝕜 r d m := by
  ext x
  simp [cyclicCorrection_apply, sum_sub_distrib, smul_sub]

/-- The zero section has zero correction. -/
@[simp]
theorem cyclicCorrection_zero (r : X → X) (m : ℕ) :
    cyclicCorrection 𝕜 r (0 : X → E) m = 0 := by
  ext x
  simp [cyclicCorrection_apply]

/-- Negating a translation section negates its correction. -/
@[simp]
theorem cyclicCorrection_neg (r : X → X) (b : X → E) (m : ℕ) :
    cyclicCorrection 𝕜 r (-b) m = -cyclicCorrection 𝕜 r b m := by
  simpa using cyclicCorrection_sub (𝕜 := 𝕜) r 0 b m

/-- At a periodic point, the weighted orbit correction changes a section into its cyclic
average. -/
theorem cyclicCorrection_apply_sub_cyclicCorrection (r : X → X) (b : X → E) {m : ℕ}
    {x : X} (hx : IsPeriodicPt r m x) (hm : (m : 𝕜) ≠ 0) :
    cyclicCorrection 𝕜 r b m (r x) - cyclicCorrection 𝕜 r b m x =
      birkhoffAverage 𝕜 r b m x - b x := by
  rw [cyclicCorrection_apply, cyclicCorrection_apply, ← smul_sub,
    hx.sum_range_nsmul_iterate_apply_sub b]
  simp [birkhoffAverage, ← Nat.cast_smul_eq_nsmul 𝕜, smul_add, smul_smul, hm,
    neg_smul, sub_eq_add_neg, add_comm]

/-- If the cyclic sum of a section is `m • a` for a section `a`, the weighted
correction normalizes it to `a`. -/
theorem add_cyclicCorrection_apply_sub (r : X → X) (b a : X → E) {m : ℕ}
    (hr : r^[m] = id) (hm : (m : 𝕜) ≠ 0)
    (hsum : ∀ x, birkhoffSum r b m x = m • a x) (x : X) :
    b x + cyclicCorrection 𝕜 r b m (r x) - cyclicCorrection 𝕜 r b m x = a x := by
  have hx : IsPeriodicPt r m x := congrFun hr x
  rw [add_sub_assoc, cyclicCorrection_apply_sub_cyclicCorrection r b hx hm,
    birkhoffAverage_eq_of_birkhoffSum_eq_nsmul hm (hsum x)]
  abel

/-- A section can be normalized to an invariant section by a change of fibre coordinates
exactly when its orbit sum is `m` times that invariant section. -/
theorem exists_add_apply_sub_eq_iff (r : X → X) (b a : X → E) {m : ℕ}
    (hr : r^[m] = id) (hm : (m : 𝕜) ≠ 0) (ha : a ∘ r = a) :
    (∃ c : X → E, ∀ x, b x + c (r x) - c x = a x) ↔
      ∀ x, birkhoffSum r b m x = m • a x := by
  constructor
  · rintro ⟨c, hc⟩ x
    have hx : IsPeriodicPt r m x := congrFun hr x
    have hb : b = a - (c ∘ r - c) := by
      ext y
      have h := hc y
      simp only [Pi.sub_apply, comp_apply]
      calc
        b y = (b y + c (r y) - c y) - (c (r y) - c y) := by abel
        _ = a y - (c (r y) - c y) := by rw [h]
    rw [hb, birkhoffSum_sub_apply, birkhoffSum_sub_apply, birkhoffSum_comp_apply,
      hx.birkhoffSum_apply_eq c, sub_self, sub_zero]
    exact birkhoffSum_apply_of_comp_eq ha m x
  · intro hsum
    exact ⟨cyclicCorrection 𝕜 r b m, add_cyclicCorrection_apply_sub r b a hr hm hsum⟩

/-- Two changes of fibre coordinates give the same normalized translation section exactly when
their difference is invariant under the generator. -/
theorem add_apply_sub_eq_iff_sub_comp_eq (r : X → X) (b a c d : X → E)
    (hc : ∀ x, b x + c (r x) - c x = a x) :
    (∀ x, b x + d (r x) - d x = a x) ↔ (d - c) ∘ r = d - c := by
  constructor
  · intro hd
    ext x
    simp only [comp_apply, Pi.sub_apply]
    calc
      d (r x) - c (r x) =
          (b x + d (r x) - d x) - (b x + c (r x) - c x) + (d x - c x) := by abel
      _ = d x - c x := by rw [hc, hd]; abel
  · intro hd x
    have h := congrFun hd x
    simp only [comp_apply, Pi.sub_apply] at h
    calc
      b x + d (r x) - d x =
          (b x + c (r x) - c x) + ((d (r x) - c (r x)) - (d x - c x)) := by abel
      _ = a x := by rw [hc, h]; abel

end TauCeti
