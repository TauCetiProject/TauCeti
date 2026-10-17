/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Tropical.BigOperators
public import Mathlib.RingTheory.PowerSeries.Basic
public import TauCeti.Analysis.Convex.Sequence.Supporting

/-!
# Minkowski sums of height sequences

The Minkowski sum of two one-sided height sequences is their finite min-convolution
`minkowski h g n = min_{i + j = n} (h i + g j)`. For convex heights it is the height
function of the Minkowski sum of the two polygons; it is the operation through which
Newton polygons of products of polynomials and power series are described.

Under `trop`, a height sequence is the coefficient sequence of a power series over the
min-tropical semiring `MinTropical (WithTop ℝ)`, and `minkowski` becomes multiplication of
power series (`mk_trop_minkowski`). This transports commutativity and associativity, the
identity element (the singleton polygon at the origin) and the absorbing element (the empty
polygon) from the power-series ring.

The finite domain of the sum is the sumset of the two finite domains, so the anchors add.
Convexity is preserved by an exchange argument based on
`isConvexSeq_iff_add_le_add`, and for nonempty sequences the supporting values add in
`EReal`.

## Main results

* `minkowski`: the min-convolution of two height sequences.
* `mk_trop_minkowski`: the min-convolution is power-series multiplication over
  `MinTropical (WithTop ℝ)`.
* `minkowski_comm`, `minkowski_assoc`, `ite_minkowski`, `top_minkowski`: the algebraic laws.
* `minkowski_ne_top_iff`, `minkowski_add_eq_of_forall_lt`: domains and anchors add.
* `IsConvexSeq.minkowski`: the Minkowski sum of convex height sequences is convex.
* `supportingValue_minkowski`: supporting values of nonempty sequences add.

## References

* N. Koblitz, *p-adic Numbers, p-adic Analysis, and Zeta-Functions*, second edition,
  Graduate Texts in Mathematics 58, Springer, 1984, Chapter IV §3.
* M. Lazard, *Les zéros d'une fonction analytique d'une variable sur un corps valué
  complet*, Publications Mathématiques de l'IHÉS 14 (1962), 47–75, §1 and Proposition 1.
-/

public section

open Finset MinTropical

namespace TauCeti

variable {h g : ℕ → WithTop ℝ} {n : ℕ}

/-- The Minkowski sum of two one-sided height sequences: the finite min-convolution
`n ↦ min_{i + j = n} (h i + g j)`. An infinite height contributes nothing to the
minimum, and the sum of a sequence with the empty sequence is empty. -/
def minkowski (h g : ℕ → WithTop ℝ) (n : ℕ) : WithTop ℝ :=
  (antidiagonal n).inf fun p => h p.1 + g p.2

/-- The Minkowski sum at `n` is the infimum over the splittings `i + j = n`. -/
theorem minkowski_def (h g : ℕ → WithTop ℝ) (n : ℕ) :
    minkowski h g n = (antidiagonal n).inf fun p => h p.1 + g p.2 := (rfl)

/-- A lower bound for the Minkowski sum at `n` is a lower bound for every splitting. -/
theorem le_minkowski_iff {r : WithTop ℝ} :
    r ≤ minkowski h g n ↔ ∀ i j, i + j = n → r ≤ h i + g j := by
  simp [minkowski, Finset.le_inf_iff]

/-- The Minkowski sum lies below every splitting. -/
theorem minkowski_le {i j : ℕ} (hij : i + j = n) : minkowski h g n ≤ h i + g j :=
  le_minkowski_iff.mp le_rfl i j hij

/-- The minimum defining the Minkowski sum is attained at some splitting. -/
theorem exists_minkowski_eq (h g : ℕ → WithTop ℝ) (n : ℕ) :
    ∃ i j, i + j = n ∧ minkowski h g n = h i + g j := by
  obtain ⟨p, hp, hpeq⟩ := exists_mem_eq_inf (antidiagonal n)
    ⟨(0, n), by simp⟩ fun p => h p.1 + g p.2
  exact ⟨p.1, p.2, mem_antidiagonal.mp hp, hpeq⟩

/-- A Minkowski sum is finite exactly at sums of finite indices of the two summands. -/
theorem minkowski_ne_top_iff :
    minkowski h g n ≠ ⊤ ↔ ∃ i j, i + j = n ∧ h i ≠ ⊤ ∧ g j ≠ ⊤ := by
  constructor
  · intro hn
    obtain ⟨i, j, hij, heq⟩ := exists_minkowski_eq h g n
    exact ⟨i, j, hij, WithTop.add_ne_top.mp (heq ▸ hn)⟩
  · rintro ⟨i, j, hij, hi, hj⟩
    exact ne_top_of_le_ne_top (WithTop.add_ne_top.mpr ⟨hi, hj⟩) (minkowski_le hij)

/-- The Minkowski sum is monotone in both height sequences. -/
theorem minkowski_mono {h' g' : ℕ → WithTop ℝ} (hh : h ≤ h') (hg : g ≤ g') :
    minkowski h g ≤ minkowski h' g' := fun _ =>
  le_minkowski_iff.mpr fun i j hij => (minkowski_le hij).trans (add_le_add (hh i) (hg j))

/-! ### Tropical power series -/

/-- Under `trop`, the Minkowski sum is the product of power series over the min-tropical
semiring `MinTropical (WithTop ℝ)`, whose addition is `min` and whose multiplication is
`+`. -/
theorem mk_trop_minkowski (h g : ℕ → WithTop ℝ) :
    (PowerSeries.mk fun n => trop (minkowski h g n)) =
      (PowerSeries.mk fun n => trop (h n)) * PowerSeries.mk fun n => trop (g n) := by
  ext n
  simp [PowerSeries.coeff_mul, minkowski, Finset.trop_inf, trop_add]

/-- Height sequences are recovered from their tropical power series. -/
theorem mk_trop_injective :
    Function.Injective fun h : ℕ → WithTop ℝ => PowerSeries.mk fun n => trop (h n) :=
  fun h g hhg => funext fun n => trop_injective (by
    simpa using congrArg (PowerSeries.coeff n) hhg)

/-- The Minkowski sum is commutative. -/
theorem minkowski_comm (h g : ℕ → WithTop ℝ) : minkowski h g = minkowski g h :=
  mk_trop_injective (by simp only [mk_trop_minkowski, mul_comm])

/-- The Minkowski sum is associative. -/
theorem minkowski_assoc (h g k : ℕ → WithTop ℝ) :
    minkowski (minkowski h g) k = minkowski h (minkowski g k) :=
  mk_trop_injective (by simp only [mk_trop_minkowski, mul_assoc])

/-- The singleton polygon at the origin is a left identity for the Minkowski sum. -/
@[simp]
theorem ite_minkowski (h : ℕ → WithTop ℝ) :
    minkowski (fun n => if n = 0 then 0 else ⊤) h = h := by
  have hone : (PowerSeries.mk fun n => trop (if n = 0 then (0 : WithTop ℝ) else ⊤)) = 1 := by
    ext n
    simp only [PowerSeries.coeff_mk, PowerSeries.coeff_one]
    split_ifs <;> simp
  exact mk_trop_injective (by simp only [mk_trop_minkowski, hone, one_mul])

/-- The singleton polygon at the origin is a right identity for the Minkowski sum. -/
@[simp]
theorem minkowski_ite (h : ℕ → WithTop ℝ) :
    minkowski h (fun n => if n = 0 then 0 else ⊤) = h := by
  rw [minkowski_comm, ite_minkowski]

/-- The empty polygon is absorbing on the left. -/
@[simp]
theorem top_minkowski (g : ℕ → WithTop ℝ) : minkowski ⊤ g = ⊤ := by
  funext n
  simp [minkowski]

/-- The empty polygon is absorbing on the right. -/
@[simp]
theorem minkowski_top (h : ℕ → WithTop ℝ) : minkowski h ⊤ = ⊤ := by
  rw [minkowski_comm, top_minkowski]

/-! ### Anchors -/

/-- If `l` and `l'` are the first finite indices of `h` and `g`, then the Minkowski sum
is infinite before `l + l'`. -/
theorem minkowski_eq_top_of_lt {l l' : ℕ} (hl : ∀ i < l, h i = ⊤) (hl' : ∀ j < l', g j = ⊤)
    (hn : n < l + l') : minkowski h g n = ⊤ := by
  by_contra hne
  obtain ⟨i, j, hij, hi, hj⟩ := minkowski_ne_top_iff.mp hne
  rcases lt_or_ge i l with hil | hil
  · exact hi (hl i hil)
  · exact hj (hl' j (by omega))

/-- If `l` and `l'` are the first finite indices of `h` and `g`, then the Minkowski sum
takes the value `h l + g l'` at `l + l'`: the anchors of the polygons add. -/
theorem minkowski_add_eq_of_forall_lt {l l' : ℕ} (hl : ∀ i < l, h i = ⊤)
    (hl' : ∀ j < l', g j = ⊤) : minkowski h g (l + l') = h l + g l' := by
  refine le_antisymm (minkowski_le rfl) (le_minkowski_iff.mpr fun i j hij => ?_)
  rcases lt_trichotomy i l with hil | rfl | hil
  · simp [hl i hil]
  · obtain rfl : j = l' := by omega
    exact le_rfl
  · simp [hl' j (by omega)]

/-! ### Convexity -/

/-- The exchange step for convexity of a Minkowski sum: if the splittings `i + i' = m`
and `j + j' = k + 1` have `i < j`, moving one unit of the first summand between them
does not increase the total, by convexity of `h` alone. -/
private theorem minkowski_add_minkowski_le (hh : IsConvexSeq h) {m k i i' j j' : ℕ}
    (hi : i + i' = m) (hj : j + j' = k + 1) (hij : i < j) :
    minkowski h g (m + 1) + minkowski h g k ≤ (h i + g i') + (h j + g j') := by
  have hex := isConvexSeq_iff_add_le_add.mp hh i (j - 1) (by omega)
  rw [Nat.sub_add_cancel (by omega)] at hex
  calc minkowski h g (m + 1) + minkowski h g k
      ≤ (h (i + 1) + g i') + (h (j - 1) + g j') :=
        add_le_add (minkowski_le (by omega)) (minkowski_le (by omega))
    _ = (h (i + 1) + h (j - 1)) + (g i' + g j') := add_add_add_comm _ _ _ _
    _ ≤ (h i + h j) + (g i' + g j') := add_le_add_left hex _
    _ = (h i + g i') + (h j + g j') := add_add_add_comm _ _ _ _

/-- The Minkowski sum of two convex height sequences is convex. This includes the empty
and singleton cases and bounded or unbounded finite domains. -/
theorem IsConvexSeq.minkowski (hh : IsConvexSeq h) (hg : IsConvexSeq g) :
    IsConvexSeq (TauCeti.minkowski h g) := by
  refine isConvexSeq_iff_add_le_add.mpr fun m k hmk => ?_
  obtain ⟨i, i', hi, hieq⟩ := exists_minkowski_eq h g m
  obtain ⟨j, j', hj, hjeq⟩ := exists_minkowski_eq h g (k + 1)
  rw [hieq, hjeq]
  rcases lt_or_ge i j with hij | hij
  · exact minkowski_add_minkowski_le hh hi hj hij
  · -- Otherwise the second summand has `i' < j'`, and the exchange is made in `g`.
    have := minkowski_add_minkowski_le (g := h) hg (add_comm i i' ▸ hi)
      (add_comm j j' ▸ hj) (by omega)
    rw [minkowski_comm g h] at this
    simpa only [add_comm (g _)] using this

/-! ### Supporting values -/

/-- The supporting values of a Minkowski sum of nonempty sequences are the sums of the
supporting values of the summands, in `EReal`. Nonemptiness excludes the sum `⊤ + ⊥`,
which would arise from an empty sequence and a vertical one. -/
theorem supportingValue_minkowski (hh : ∃ n, h n ≠ ⊤) (hg : ∃ n, g n ≠ ⊤) (σ : ℝ) :
    supportingValue (minkowski h g) σ = supportingValue h σ + supportingValue g σ := by
  refine le_antisymm ?_ (le_supportingValue_iff.mpr fun n => ?_)
  · -- Every splitting bounds the supporting value of the sum; take the infimum over the
    -- second index, then over the first.
    have hsplit (i j : ℕ) : supportingValue (minkowski h g) σ ≤
        ((h i).toEReal - ((σ * i : ℝ) : EReal)) + ((g j).toEReal - ((σ * j : ℝ) : EReal)) := by
      rw [← EReal.add_sub_coe_add, ← mul_add, ← Nat.cast_add, ← WithTop.toEReal_add]
      exact (supportingValue_le _ σ (i + j)).trans (EReal.sub_le_sub
        (WithTop.toEReal_le_toEReal_iff.mpr (minkowski_le rfl)) le_rfl)
    have hrow (i : ℕ) (hi : h i ≠ ⊤) : supportingValue (minkowski h g) σ ≤
        ((h i).toEReal - ((σ * i : ℝ) : EReal)) + supportingValue g σ := by
      obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.mp hi
      rw [← hr, WithTop.toEReal_coe, ← EReal.coe_sub, add_comm, supportingValue_def g σ,
        ← EReal.iInf_add_coe]
      exact le_iInf fun j => by
        rw [add_comm, EReal.coe_sub, ← WithTop.toEReal_coe, hr]
        exact hsplit i j
    obtain ⟨i₀, hi₀⟩ := hh
    by_cases hbot : supportingValue g σ = ⊥
    · have := hrow i₀ hi₀
      rw [hbot, EReal.add_bot] at this
      rw [le_bot_iff.mp this]
      exact bot_le
    obtain ⟨y, hy⟩ : ∃ y : ℝ, (y : EReal) = supportingValue g σ :=
      ⟨_, EReal.coe_toReal (supportingValue_lt_top_iff.mpr hg).ne hbot⟩
    rw [← hy, supportingValue_def h σ, ← EReal.iInf_add_coe]
    refine le_iInf fun i => ?_
    by_cases hi : h i = ⊤
    · rw [hi, WithTop.toEReal_top, EReal.top_sub_coe, EReal.top_add_coe]
      exact le_top
    · exact hy ▸ hrow i hi
  · obtain ⟨i, j, hij, heq⟩ := exists_minkowski_eq h g n
    rw [heq, ← hij, WithTop.toEReal_add, Nat.cast_add, mul_add, EReal.add_sub_coe_add]
    exact add_le_add (supportingValue_le h σ i) (supportingValue_le g σ j)

end TauCeti
