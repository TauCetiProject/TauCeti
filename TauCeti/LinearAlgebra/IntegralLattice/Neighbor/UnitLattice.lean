/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.Index.Two
public import TauCeti.InformationTheory.Coding.Equivalence
public import TauCeti.LinearAlgebra.IntegralLattice.Neighbor.Basic
public import TauCeti.LinearAlgebra.IntegralLattice.RootLattice.D8Plus.Isometry
public import TauCeti.LinearAlgebra.IntegralLattice.Unit
import Mathlib.Algebra.BigOperators.Field

/-!
# Two-neighbors of the standard lattice without unit vectors

Let `L` be an integral lattice on `ℚⁿ`, with the dot product, which is a Kneser two-neighbor of
the standard lattice `Iₙ = ℤⁿ` and contains none of the coordinate vectors `eᵢ`. Then:

* `L ∩ ℤⁿ` is the checkerboard lattice `Dₙ` of integral vectors with even coordinate sum;
* `L = Dₙ ∪ (y + Dₙ)` for a vector `y` whose coordinates all lie in `ℤ + 1/2`;
* `4 ∣ n`, because `y · y ∈ ℤ` while `4 (y · y) = ∑ (2 yᵢ)² ≡ n (mod 4)`;
* if `8 ∣ n`, then `L` is isometric to the spinor glue lattice `Dₙ⁺`, and in rank eight it is
  isometric to the `E₈` root lattice.

Besides integrality, the argument only uses that `L ∩ ℤⁿ` has index two in both lattices. As
neither `eᵢ` nor `eⱼ` lies in `L`, their sum does, so `yᵢ + yⱼ` is an integer for every
`y ∈ L`; a vector `y ∈ L ∖ ℤⁿ` is therefore half-integral in every coordinate. Pairing with `y`
then shows that a vector of `L ∩ ℤⁿ` has even coordinate sum, and index two gives the reverse
inclusion. Finally `y` is congruent modulo `Dₙ` to the spinor `(1/2, …, 1/2)` or becomes so after
changing the sign of one coordinate, and such a sign change preserves `Dₙ` and the dot product.

The same statements hold for a two-neighbor `L` of any lattice `N` given with an isometry
`Iₙ ≅ N`, provided `L` has no vectors of norm one: moving both lattices to `ℚⁿ` along the isometry
turns the vectors `eᵢ` into vectors of norm one. A positive definite unimodular lattice with a
vector of norm one splits off `I₁`, and a two-neighbor along a vector of norm four acquires such a
vector, so these statements identify a lattice without vectors of norm one from a neighbor
isometric to `Iₙ`.

## Main results

* `TauCeti.IntegralLattice.exists_forall_mem_carrier_iff_of_isNeighbor_unitLattice`:
  `L = Dₙ ∪ (y + Dₙ)` with `y` half-integral.
* `TauCeti.IntegralLattice.carrier_inf_eq_checkerboardCarrier_of_isNeighbor_unitLattice`:
  `L ∩ ℤⁿ = Dₙ`.
* `TauCeti.IntegralLattice.four_dvd_of_isNeighbor_unitLattice`: `4 ∣ n`.
* `TauCeti.IntegralLattice.nonempty_isometry_checkerboardPlusLattice_of_isNeighbor_unitLattice`:
  `L ≅ Dₙ⁺` when `8 ∣ n`.
* `TauCeti.IntegralLattice.nonempty_isometry_typeE₈RootLattice_of_isNeighbor_unitLattice`:
  `L ≅ E₈` in rank eight.
* `TauCeti.IntegralLattice.four_dvd_of_isNeighbor_of_isometry_unitLattice` and its companions
  `nonempty_isometry_checkerboardPlusLattice_of_isNeighbor_of_isometry_unitLattice` and
  `nonempty_isometry_typeE₈RootLattice_of_isNeighbor_of_isometry_unitLattice`: the same for a
  two-neighbor without vectors of norm one of a lattice isometric to `Iₙ`.

## References

* M. Kneser, *Klassenzahlen definiter quadratischer Formen*, Arch. Math. 8 (1957), 241--250.
* J. H. Conway and N. J. A. Sloane, *Sphere Packings, Lattices and Groups*, Chapter 16, §1, and
  Chapter 4, §7.3, for the lattices `Dₙ⁺`.
-/

public section

namespace TauCeti.IntegralLattice

variable {n : ℕ} {L : IntegralLattice (Fin n → ℚ)}

/-- The coordinate vector `eᵢ` is not in the checkerboard lattice, its coordinate sum being one. -/
private theorem single_one_notMem_checkerboardCarrier (i : Fin n) :
    Pi.single i (1 : ℚ) ∉ checkerboardCarrier n := by
  rw [mem_checkerboardCarrier_iff]
  rintro ⟨-, m, hm⟩
  rw [Finset.sum_pi_single'] at hm
  simp only [Finset.mem_univ, ite_true] at hm
  have h : (1 : ℤ) = 2 * m := by exact_mod_cast hm
  omega

/-- The checkerboard lattice lies in the standard lattice. -/
private theorem mem_unitLattice_carrier_of_mem_checkerboardCarrier {x : Fin n → ℚ}
    (hx : x ∈ checkerboardCarrier n) : x ∈ (unitLattice (Fin n)).carrier :=
  (mem_unitLattice_carrier_iff _ x).2 fun i ↦
    (((mem_checkerboardCarrier_iff x).1 hx).1 i).imp fun _ h ↦ h.symm

/-- The coordinate vector `eᵢ` lies in the standard lattice. -/
private theorem single_one_mem_unitLattice_carrier (i : Fin n) :
    Pi.single i (1 : ℚ) ∈ (unitLattice (Fin n)).carrier := by
  simpa using (unitLatticeBasis (Fin n) i).2

section

variable (h : L.IsNeighbor (unitLattice (Fin n)) 2)
include h

/-- The dot product of two vectors of a neighbor of `Iₙ` is an integer. -/
private theorem exists_intCast_eq_sum_mul {x y : Fin n → ℚ} (hx : x ∈ L.carrier)
    (hy : y ∈ L.carrier) : ∃ z : ℤ, (z : ℚ) = ∑ i, x i * y i := by
  obtain ⟨z, hz⟩ := Submodule.mem_one.1 (L.form_mem_one ⟨x, hx⟩ ⟨y, hy⟩)
  refine ⟨z, ?_⟩
  rw [← unitLattice_form_apply, ← h.form_eq]
  exact hz

/-- Two vectors of `ℤⁿ` outside the neighbor `L` add up to a vector of `L`. -/
private theorem add_mem_carrier_of_notMem {a b : Fin n → ℚ}
    (ha : a ∈ (unitLattice (Fin n)).carrier) (hb : b ∈ (unitLattice (Fin n)).carrier)
    (haL : a ∉ L.carrier) (hbL : b ∉ L.carrier) : a + b ∈ L.carrier := by
  have := (AddSubgroup.add_mem_iff_of_relIndex_eq_two h.relIndex_inf_right ha hb).2
    (iff_of_false (fun h' ↦ haL h'.1) fun h' ↦ hbL h'.1)
  exact this.1

/-- A neighbor of `Iₙ` has a vector outside `ℤⁿ`. -/
private theorem exists_mem_carrier_notMem_unitLattice :
    ∃ y ∈ L.carrier, y ∉ (unitLattice (Fin n)).carrier := by
  by_contra! hle
  have h1 := AddSubgroup.relIndex_eq_one.2 (show L.carrier.toAddSubgroup ≤
    (L.carrier ⊓ (unitLattice (Fin n)).carrier).toAddSubgroup from fun x hx ↦ ⟨hx, hle x hx⟩)
  rw [h.relIndex_inf_left] at h1
  exact absurd h1 (by norm_num)

/-- A vector of `L ∩ ℤⁿ` has even coordinate sum: pairing it with a half-integral `y ∈ L` gives
an integer. -/
private theorem mem_checkerboardCarrier_of_mem {y : Fin n → ℚ} (hy : y ∈ L.carrier)
    (hyk : ∀ i, ∃ k : ℤ, y i = k + 1 / 2) {x : Fin n → ℚ} (hx : x ∈ L.carrier)
    (hxZ : x ∈ (unitLattice (Fin n)).carrier) : x ∈ checkerboardCarrier n := by
  choose w hw using (mem_unitLattice_carrier_iff _ x).1 hxZ
  choose k hk using hyk
  obtain ⟨z, hz⟩ := exists_intCast_eq_sum_mul h hx hy
  refine (mem_checkerboardCarrier_iff x).2 ⟨fun i ↦ ⟨w i, (hw i).symm⟩, z - ∑ i, w i * k i, ?_⟩
  have hsum : ∑ i, x i * y i = ∑ i, (w i : ℚ) * k i + (∑ i, x i) / 2 := by
    rw [Finset.sum_div, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [hk i, ← hw i]
    ring
  push_cast
  linarith

variable (h₁ : ∀ i, Pi.single i (1 : ℚ) ∉ L.carrier)
include h₁

/-- A vector of a neighbor of `Iₙ` without coordinate vectors which is not in `ℤⁿ` is
half-integral in every coordinate. -/
private theorem exists_eq_add_half_of_notMem_unitLattice {y : Fin n → ℚ} (hy : y ∈ L.carrier)
    (hyZ : y ∉ (unitLattice (Fin n)).carrier) (i : Fin n) : ∃ k : ℤ, y i = k + 1 / 2 := by
  -- `yᵢ + yⱼ` is an integer, because `eᵢ + eⱼ` lies in `L`.
  have hpair (i j : Fin n) : ∃ z : ℤ, (z : ℚ) = y i + y j := by
    obtain ⟨z, hz⟩ := exists_intCast_eq_sum_mul h
      (add_mem_carrier_of_notMem h (single_one_mem_unitLattice_carrier i)
        (single_one_mem_unitLattice_carrier j) (h₁ i) (h₁ j)) hy
    refine ⟨z, ?_⟩
    rw [hz]
    simp [add_mul, Finset.sum_add_distrib, Pi.single_apply]
  obtain ⟨j, hj⟩ : ∃ j, ∀ z : ℤ, (z : ℚ) ≠ y j := by
    by_contra! hall
    exact hyZ ((mem_unitLattice_carrier_iff _ y).2 hall)
  obtain ⟨m, hm⟩ := hpair j j
  obtain ⟨k, rfl | rfl⟩ := m.even_or_odd'
  · exact absurd (by push_cast at hm; linarith) (hj k)
  obtain ⟨z, hz⟩ := hpair i j
  refine ⟨z - k - 1, ?_⟩
  push_cast at hm ⊢
  linarith

/-- **The intersection of `Iₙ` with a two-neighbor without coordinate vectors is `Dₙ`.** -/
theorem carrier_inf_eq_checkerboardCarrier_of_isNeighbor_unitLattice :
    L.carrier ⊓ (unitLattice (Fin n)).carrier = checkerboardCarrier n := by
  obtain ⟨y, hy, hyZ⟩ := exists_mem_carrier_notMem_unitLattice h
  obtain ⟨j, -⟩ : ∃ j, ∀ z : ℤ, (z : ℚ) ≠ y j := by
    by_contra! hall
    exact hyZ ((mem_unitLattice_carrier_iff _ y).2 hall)
  have hD {x : Fin n → ℚ} : x ∈ L.carrier → x ∈ (unitLattice (Fin n)).carrier →
      x ∈ checkerboardCarrier n :=
    mem_checkerboardCarrier_of_mem h hy (exists_eq_add_half_of_notMem_unitLattice h h₁ hy hyZ)
  refine le_antisymm (fun x hx ↦ hD hx.1 hx.2) fun x hx ↦
    ⟨?_, mem_unitLattice_carrier_of_mem_checkerboardCarrier hx⟩
  -- If `x ∈ Dₙ` were outside `L`, then `x + eⱼ ∈ L ∩ ℤⁿ ⊆ Dₙ` would put `eⱼ` in `Dₙ`.
  by_contra hxL
  have hxZ := mem_unitLattice_carrier_of_mem_checkerboardCarrier hx
  have hej := single_one_mem_unitLattice_carrier j
  have hsum := hD (add_mem_carrier_of_notMem h hxZ hej hxL (h₁ j))
    ((unitLattice (Fin n)).carrier.add_mem hxZ hej)
  exact single_one_notMem_checkerboardCarrier j <| by
    simpa using (checkerboardCarrier n).sub_mem hsum hx

/-- **The two-neighbors of `Iₙ` without coordinate vectors.** If `L` is a Kneser two-neighbor of
the standard lattice `ℤⁿ` containing no coordinate vector `eᵢ`, then `L = Dₙ ∪ (y + Dₙ)` for a
vector `y` whose coordinates all lie in `ℤ + 1/2`. -/
theorem exists_forall_mem_carrier_iff_of_isNeighbor_unitLattice :
    ∃ y : Fin n → ℚ, (∀ i, ∃ k : ℤ, y i = k + 1 / 2) ∧
      ∀ x, x ∈ L.carrier ↔ x ∈ checkerboardCarrier n ∨ x - y ∈ checkerboardCarrier n := by
  obtain ⟨y, hy, hyZ⟩ := exists_mem_carrier_notMem_unitLattice h
  have hinf := carrier_inf_eq_checkerboardCarrier_of_isNeighbor_unitLattice h h₁
  refine ⟨y, exists_eq_add_half_of_notMem_unitLattice h h₁ hy hyZ, fun x ↦ ⟨fun hx ↦ ?_, ?_⟩⟩
  · by_cases hxZ : x ∈ (unitLattice (Fin n)).carrier
    · exact Or.inl (hinf ▸ ⟨hx, hxZ⟩)
    -- Two vectors of `L ∖ ℤⁿ` differ by a vector of `L ∩ ℤⁿ`, which has index two in `L`.
    have hxy := (AddSubgroup.add_mem_iff_of_relIndex_eq_two h.relIndex_inf_left hx
      (L.carrier.neg_mem hy)).2 (iff_of_false (fun h' ↦ hxZ h'.2) fun h' ↦
        hyZ (by simpa using (unitLattice (Fin n)).carrier.neg_mem h'.2))
    rw [← sub_eq_add_neg] at hxy
    exact Or.inr (hinf ▸ hxy)
  · have hDL {x : Fin n → ℚ} (hx : x ∈ checkerboardCarrier n) : x ∈ L.carrier :=
      (hinf.symm ▸ hx : x ∈ L.carrier ⊓ _).1
    rintro (hx | hx)
    · exact hDL hx
    · simpa using L.carrier.add_mem (hDL hx) hy

/-- **A two-neighbor of `Iₙ` without coordinate vectors has rank divisible by four.** The glue
vector `y` has half-integral coordinates, so `y · y = ∑ (kᵢ² + kᵢ) + n / 4` must be an integer. -/
theorem four_dvd_of_isNeighbor_unitLattice : 4 ∣ n := by
  obtain ⟨y, hyk, hL⟩ := exists_forall_mem_carrier_iff_of_isNeighbor_unitLattice h h₁
  have hy : y ∈ L.carrier := (hL y).2 (Or.inr (by simp))
  obtain ⟨z, hz⟩ := exists_intCast_eq_sum_mul h hy hy
  choose k hk using hyk
  have hsum : ∑ i, y i * y i = ∑ i, ((k i : ℚ) ^ 2 + k i) + n / 4 := by
    rw [Finset.sum_congr rfl fun i _ ↦ show y i * y i = ((k i : ℚ) ^ 2 + k i) + 1 / 4 by
      rw [hk i]; ring, Finset.sum_add_distrib]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring
  have hn : ((n : ℤ) : ℚ) = ((4 * (z - ∑ i, (k i ^ 2 + k i)) : ℤ) : ℚ) := by
    push_cast
    linarith
  exact Int.natCast_dvd_natCast.mp ⟨_, Int.cast_injective hn⟩

end

/-! ### The isometry with `Dₙ⁺` -/

/-- A signed change of coordinates of `ℚⁿ` is an involution. -/
private theorem signedEquiv_signedEquiv (u : Fin n → ℤˣ) (x : Fin n → ℚ) :
    signedEquiv u (Equiv.refl _) (signedEquiv u (Equiv.refl _) x) = x := by
  ext i
  simp only [signedEquiv_apply, Equiv.refl_symm, Equiv.refl_apply, ← mul_assoc]
  norm_cast
  simp

/-- A signed change of coordinates maps `Dₙ` into itself: it changes the coordinate sum by an even
integer. -/
private theorem signedEquiv_mem_checkerboardCarrier (u : Fin n → ℤˣ) {x : Fin n → ℚ}
    (hx : x ∈ checkerboardCarrier n) : signedEquiv u (Equiv.refl _) x ∈ checkerboardCarrier n := by
  obtain ⟨hxZ, m, hm⟩ := (mem_checkerboardCarrier_iff x).1 hx
  choose w hw using hxZ
  refine mem_checkerboardCarrier_of (fun i ↦ u i * w i) (fun i ↦ by simp [hw i]) ?_
  have hw2 : ∑ i, w i = 2 * m := by
    have : ((∑ i, w i : ℤ) : ℚ) = ((2 * m : ℤ) : ℚ) := by
      push_cast
      rw [← hm]
      exact Finset.sum_congr rfl fun i _ ↦ (hw i).symm
    exact_mod_cast this
  have hsum : ∑ i, (u i : ℤ) * w i = ∑ i, w i + ∑ i, ((u i : ℤ) - 1) * w i := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ ↦ by ring
  rw [hsum, hw2]
  refine (even_two_mul m).add (Finset.even_sum _ fun i _ ↦ (Even.mul_right ?_ _))
  rcases Int.units_eq_one_or (u i) with hu | hu <;> simp [hu]

private theorem signedEquiv_mem_checkerboardCarrier_iff (u : Fin n → ℤˣ) (x : Fin n → ℚ) :
    signedEquiv u (Equiv.refl _) x ∈ checkerboardCarrier n ↔ x ∈ checkerboardCarrier n :=
  ⟨fun hx ↦ signedEquiv_signedEquiv u x ▸ signedEquiv_mem_checkerboardCarrier u hx,
    signedEquiv_mem_checkerboardCarrier u⟩

/-- The carrier of `Dₙ⁺` is `Dₙ ∪ (g + Dₙ)` for any `g` congruent to the spinor modulo `Dₙ`. -/
private theorem mem_checkerboardPlusCarrier_iff_of_sub_mem (heven : Even n) {g : Fin n → ℚ}
    (hg : g - checkerboardSpinor n ∈ checkerboardCarrier n) (x : Fin n → ℚ) :
    x ∈ (checkerboardPlusCarrier n).1 ↔
      x ∈ checkerboardCarrier n ∨ x - g ∈ checkerboardCarrier n := by
  rw [mem_checkerboardPlusCarrier_iff n heven, checkerboardLattice_carrier,
    show x - checkerboardSpinor n = (x - g) + (g - checkerboardSpinor n) by abel,
    Submodule.add_mem_iff_left _ hg]

/-- The form of a lattice with the dot product is the form of `Dₙ⁺`. -/
private theorem form_eq_checkerboardPlusLattice_form (hn : 8 ∣ n)
    (hform : L.form = (unitLattice (Fin n)).form) :
    L.form = (checkerboardPlusLattice n hn).form := by
  rw [hform, checkerboardPlusLattice_form]
  exact LinearMap.ext fun x ↦ LinearMap.ext fun x' ↦ by
    rw [unitLattice_form_apply, checkerboardLattice_form_apply]

/-- A lattice with the dot product of the form `Dₙ ∪ (y + Dₙ)`, where a signed change of
coordinates carries `y` into the spinor coset, is the image of `Dₙ⁺` under that change. -/
private theorem nonempty_isometry_checkerboardPlusLattice_of_signedEquiv (hn : 8 ∣ n)
    (hform : L.form = (unitLattice (Fin n)).form) {y : Fin n → ℚ}
    (hL : ∀ x, x ∈ L.carrier ↔ x ∈ checkerboardCarrier n ∨ x - y ∈ checkerboardCarrier n)
    (u : Fin n → ℤˣ)
    (hy : signedEquiv u (Equiv.refl _) y - checkerboardSpinor n ∈ checkerboardCarrier n) :
    Nonempty (Isometry (checkerboardPlusLattice n hn) L) := by
  set τ : (Fin n → ℚ) ≃ₗ[ℚ] (Fin n → ℚ) := signedEquiv u (Equiv.refl _)
  have hτform (x x' : Fin n → ℚ) :
      L.form (τ x) (τ x') = (checkerboardPlusLattice n hn).form x x' := by
    rw [← form_eq_checkerboardPlusLattice_form hn hform, hform, unitLattice_form_apply,
      unitLattice_form_apply]
    simpa only [dotProduct] using dotProduct_signedEquiv u (Equiv.refl _) x x'
  have hτcarrier : (checkerboardPlusLattice n hn).carrier.map
      (τ.restrictScalars ℤ).toLinearMap = L.carrier := by
    ext x
    have hsymm : (τ.restrictScalars ℤ).symm x = τ x :=
      (LinearEquiv.symm_apply_eq _).2 (signedEquiv_signedEquiv u x).symm
    rw [Submodule.mem_map_equiv, checkerboardPlusLattice_carrier,
      mem_checkerboardPlusCarrier_iff_of_sub_mem (even_iff_two_dvd.2 (dvd_trans (by norm_num) hn))
        hy, hL, hsymm, ← map_sub, signedEquiv_mem_checkerboardCarrier_iff,
      signedEquiv_mem_checkerboardCarrier_iff]
  exact ⟨⟨⟨τ, hτform⟩, hτcarrier⟩⟩

section

variable (h : L.IsNeighbor (unitLattice (Fin n)) 2) (h₁ : ∀ i, Pi.single i (1 : ℚ) ∉ L.carrier)
include h h₁

/-- **A two-neighbor of `Iₙ` without coordinate vectors is `Dₙ⁺`**, for `8 ∣ n`. Its glue vector
is congruent modulo `Dₙ` either to the spinor `(1/2, …, 1/2)` or, after changing the sign of one
coordinate, to it. -/
theorem nonempty_isometry_checkerboardPlusLattice_of_isNeighbor_unitLattice (hn : 8 ∣ n) :
    Nonempty (Isometry (checkerboardPlusLattice n hn) L) := by
  obtain ⟨y, hyk, hL⟩ := exists_forall_mem_carrier_iff_of_isNeighbor_unitLattice h h₁
  choose k hk using hyk
  rcases Int.even_or_odd (∑ i, k i) with hk2 | hk2
  · -- The glue vector is congruent to the spinor: `L` is `Dₙ⁺` itself.
    refine nonempty_isometry_checkerboardPlusLattice_of_signedEquiv hn h.form_eq hL 1
      (mem_checkerboardCarrier_of k (fun i ↦ ?_) hk2)
    simp [hk i]
  -- Otherwise changing the sign of the first coordinate carries it into the spinor coset.
  have hpos : 0 < n := by
    rcases Nat.eq_zero_or_pos n with rfl | hpos
    · simp at hk2
    · exact hpos
  refine nonempty_isometry_checkerboardPlusLattice_of_signedEquiv hn h.form_eq hL
    (Pi.mulSingle ⟨0, hpos⟩ (-1))
    (mem_checkerboardCarrier_of (k - Pi.single ⟨0, hpos⟩ (2 * k ⟨0, hpos⟩ + 1))
      (fun i ↦ ?_) ?_)
  · rw [Pi.sub_apply, signedEquiv_apply, checkerboardSpinor_apply]
    rcases eq_or_ne i ⟨0, hpos⟩ with rfl | hij
    · simp [hk]
      ring
    · simp [hk, hij]
  · obtain ⟨m, hm⟩ := hk2
    refine ⟨m - k ⟨0, hpos⟩, ?_⟩
    simp only [Pi.sub_apply, Finset.sum_sub_distrib, Finset.sum_pi_single', Finset.mem_univ,
      ite_true, hm]
    ring

end

/-- **A two-neighbor of `I₈` without coordinate vectors is `E₈`.** -/
theorem nonempty_isometry_typeE₈RootLattice_of_isNeighbor_unitLattice
    {L : IntegralLattice (Fin 8 → ℚ)} (h : L.IsNeighbor (unitLattice (Fin 8)) 2)
    (h₁ : ∀ i, Pi.single i (1 : ℚ) ∉ L.carrier) : Nonempty (Isometry typeE₈RootLattice L) :=
  (nonempty_isometry_checkerboardPlusLattice_of_isNeighbor_unitLattice h h₁ (by decide)).map
    typeE₈IsometryD8Plus.trans

/-! ### Two-neighbors of a lattice isometric to `Iₙ` -/

section Isometry

variable {V : Type*} [AddCommGroup V] [Module ℚ V] {L N : IntegralLattice V}

/-- Moving a two-neighbor of a lattice isometric to `Iₙ` to `ℚⁿ` gives a two-neighbor of `Iₙ`. -/
private theorem isNeighbor_transport_symm (e : Isometry (unitLattice (Fin n)) N)
    (h : L.IsNeighbor N 2) :
    (L.transport (e : (Fin n → ℚ) ≃ₗ[ℚ] V).symm).IsNeighbor (unitLattice (Fin n)) 2 := by
  have hN : N.transport (e : (Fin n → ℚ) ≃ₗ[ℚ] V).symm = unitLattice (Fin n) := by
    refine IntegralLattice.ext ?_ (LinearMap.ext fun x ↦ LinearMap.ext fun x' ↦ ?_)
    · ext x
      rw [transport_carrier, Submodule.mem_map_equiv]
      exact e.apply_mem_carrier_iff x
    · simp
  have h' := h.transport (e : (Fin n → ℚ) ≃ₗ[ℚ] V).symm
  rwa [hN] at h'

/-- A two-neighbor without vectors of norm one of a lattice isometric to `Iₙ`, moved to `ℚⁿ` along
that isometry, contains no coordinate vector. -/
private theorem single_one_notMem_transport_symm (e : Isometry (unitLattice (Fin n)) N)
    (h : L.IsNeighbor N 2) (h₁ : L.vectorsOfNorm 1 = ∅) (i : Fin n) :
    Pi.single i (1 : ℚ) ∉ (L.transport (e : (Fin n → ℚ) ≃ₗ[ℚ] V).symm).carrier := by
  intro hi
  rw [transport_carrier, Submodule.mem_map_equiv] at hi
  have hnorm : (⟨_, hi⟩ : L) ∈ L.vectorsOfNorm 1 := by
    rw [mem_vectorsOfNorm, norm_apply, h.form_eq]
    simp [Pi.single_apply]
  simp [h₁] at hnorm

variable (e : Isometry (unitLattice (Fin n)) N) (h : L.IsNeighbor N 2)
  (h₁ : L.vectorsOfNorm 1 = ∅)
include e h h₁

/-- **A two-neighbor of `Iₙ` without vectors of norm one has rank divisible by four.** Here `Iₙ`
is any lattice `N` given with an isometry from the standard lattice. -/
theorem four_dvd_of_isNeighbor_of_isometry_unitLattice : 4 ∣ n :=
  four_dvd_of_isNeighbor_unitLattice (isNeighbor_transport_symm e h)
    (single_one_notMem_transport_symm e h h₁)

/-- **A two-neighbor of `Iₙ` without vectors of norm one is `Dₙ⁺`**, for `8 ∣ n`. Here `Iₙ` is
any lattice `N` given with an isometry from the standard lattice. -/
theorem nonempty_isometry_checkerboardPlusLattice_of_isNeighbor_of_isometry_unitLattice
    (hn : 8 ∣ n) : Nonempty (Isometry (checkerboardPlusLattice n hn) L) :=
  (nonempty_isometry_checkerboardPlusLattice_of_isNeighbor_unitLattice
    (isNeighbor_transport_symm e h) (single_one_notMem_transport_symm e h h₁) hn).map
      fun f ↦ f.trans (L.transportIsometry _).symm

end Isometry

/-- **A two-neighbor of `I₈` without vectors of norm one is `E₈`.** Here `I₈` is any lattice `N`
given with an isometry from the standard lattice. -/
theorem nonempty_isometry_typeE₈RootLattice_of_isNeighbor_of_isometry_unitLattice
    {V : Type*} [AddCommGroup V] [Module ℚ V] {L N : IntegralLattice V}
    (e : Isometry (unitLattice (Fin 8)) N) (h : L.IsNeighbor N 2) (h₁ : L.vectorsOfNorm 1 = ∅) :
    Nonempty (Isometry typeE₈RootLattice L) :=
  (nonempty_isometry_checkerboardPlusLattice_of_isNeighbor_of_isometry_unitLattice e h h₁
    (by decide)).map typeE₈IsometryD8Plus.trans

end TauCeti.IntegralLattice
