/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Steinberg.Symbol
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Steinberg.Weyl

/-!
# Dennis–Stein symbols in the Steinberg group

Let `R` be an associative unital ring and let `r, s ∈ R` commute, with `u = 1 - r s` a unit. For
distinct indices `i ≠ j` the **Dennis–Stein word** is
`⟨r, s⟩_{ij} = x_{ji}(-s u⁻¹) x_{ij}(-r) x_{ji}(s) x_{ij}(u⁻¹ r) h_{ij}(u)⁻¹`,
where `h_{ij}(u) = w_{ij}(u) w_{ij}(-1)` is the diagonal element of `TauCeti.IndexedSteinbergGroup`.
In the `2 × 2` block at `(i, j)` the four elementary factors multiply to `diag(u, u⁻¹)`, which is
the image of `h_{ij}(u)`, so the word lies in the kernel of the map to the general linear group.
In the stable Steinberg group `St(R)` that kernel is `K₂(R)`, which is central; conjugating by
Weyl elements then shows that the word does not depend on the indices. The resulting element of
`K₂(R)` is the **Dennis–Stein symbol** `⟨r, s⟩` (`TauCeti.dennisSteinSymbol`).

The convention is the modern one, in which `⟨r, s⟩` is defined when `1 - r s` is a unit. The
pre-1980 symbol, defined when `1 + r s` is a unit, is `⟨-r, s⟩` in this notation. The symbol is
trivial when `r = 0` or `s = 0`, and for a unit `r` it is the Steinberg symbol `{r, 1 - r s}`; in
particular every Steinberg symbol `{u, v}` of commuting units is `⟨u, u⁻¹ (1 - v)⟩`. These symbols
are the images of the generators of the Dennis–Stein presentation group `TauCeti.DennisSteinGroup`
of a commutative ring.

## Main definitions

* `TauCeti.IndexedSteinbergGroup.dennisStein`: the Dennis–Stein word `⟨r, s⟩_{ij}` in `St_ι(R)`.
* `TauCeti.dennisSteinSymbol`: the Dennis–Stein symbol `⟨r, s⟩ ∈ K₂(R)`.

## Main results

* `TauCeti.IndexedSteinbergGroup.toGL_dennisStein_mul_h`: the four elementary factors of the word
  map to `diag(u, u⁻¹)` at `(i, j)`; `TauCeti.IndexedSteinbergGroup.toGL_dennisStein`: the word
  maps to `1`.
* `TauCeti.IndexedSteinbergGroup.dennisStein_eq_commutatorElement_h_h`: for a unit `r`, the word
  at `(i, j)` is the commutator `⁅h_{ik}(r), h_{ij}(1 - r s)⁆`.
* `TauCeti.SteinbergGroup.dennisStein_eq_dennisStein`: in `St(R)` the word does not depend on the
  indices.
* `TauCeti.coe_dennisSteinSymbol`: `⟨r, s⟩` is the word at any pair of distinct indices.
* `TauCeti.dennisSteinSymbol_zero_left`, `TauCeti.dennisSteinSymbol_zero_right`: `⟨0, s⟩ = 1` and
  `⟨r, 0⟩ = 1`.
* `TauCeti.dennisSteinSymbol_eq_steinbergSymbol`: `⟨r, s⟩ = {r, 1 - r s}` for a unit `r`.
* `TauCeti.steinbergSymbol_eq_dennisSteinSymbol`: `{u, v} = ⟨u, u⁻¹ (1 - v)⟩` for commuting units.
* `TauCeti.AlgebraicK2.map_dennisSteinSymbol`: naturality in ring homomorphisms.

## References

* R. K. Dennis, M. R. Stein, *K₂ of radical ideals and semi-local rings*, in *Algebraic K-theory
  II*, Lecture Notes in Math. 342 (1973), §1 and Proposition 1.1.
* C. A. Weibel, *The K-book: An Introduction to Algebraic K-Theory*, Graduate Studies in
  Mathematics 145 (2013), Chapter III, 5.11.
-/

public section

noncomputable section

open Matrix

open scoped commutatorElement

namespace TauCeti

namespace IndexedSteinbergGroup

variable {ι R : Type*} [Ring R]

/-! ### The Dennis–Stein word -/

/-- The **Dennis–Stein word**
`⟨r, s⟩_{ij} = x_{ji}(-s u⁻¹) x_{ij}(-r) x_{ji}(s) x_{ij}(u⁻¹ r) h_{ij}(u)⁻¹` in the Steinberg
group, for distinct indices `i ≠ j` and `r, s ∈ R` with `u = 1 - r s` a unit. When `r` and `s`
commute it lies in the kernel of the map to the general linear group (`toGL_dennisStein`). -/
def dennisStein {i j : ι} (hij : i ≠ j) (r s : R) (hu : IsUnit (1 - r * s)) :
    IndexedSteinbergGroup ι R :=
  x hij.symm (-(s * (hu.unit⁻¹ : Rˣ))) * x hij (-r) * x hij.symm s *
    x hij ((hu.unit⁻¹ : Rˣ) * r) * (h hij hu.unit)⁻¹

theorem dennisStein_def {i j : ι} (hij : i ≠ j) (r s : R) (hu : IsUnit (1 - r * s)) :
    dennisStein hij r s hu = x hij.symm (-(s * (hu.unit⁻¹ : Rˣ))) * x hij (-r) * x hij.symm s *
      x hij ((hu.unit⁻¹ : Rˣ) * r) * (h hij hu.unit)⁻¹ :=
  (rfl)

/-- The Dennis–Stein word `⟨0, s⟩_{ij}` is trivial. -/
@[simp]
theorem dennisStein_zero_left {i j : ι} (hij : i ≠ j) (s : R) (hu : IsUnit (1 - 0 * s)) :
    dennisStein hij 0 s hu = 1 := by
  simp [dennisStein_def, ← x_add]

/-- The Dennis–Stein word `⟨r, 0⟩_{ij}` is trivial. -/
@[simp]
theorem dennisStein_zero_right {i j : ι} (hij : i ≠ j) (r : R) (hu : IsUnit (1 - r * 0)) :
    dennisStein hij r 0 hu = 1 := by
  simp [dennisStein_def, ← x_add]

/-- **Naturality of the Dennis–Stein word**: a ring homomorphism `f` sends `⟨r, s⟩_{ij}` to
`⟨f r, f s⟩_{ij}`. -/
@[simp]
theorem map_dennisStein {S : Type*} [Ring S] (f : R →+* S) {i j : ι} (hij : i ≠ j) (r s : R)
    (hu : IsUnit (1 - r * s)) :
    map f (dennisStein hij r s hu) =
      dennisStein hij (f r) (f s) (by simpa using hu.map f) := by
  have hunit : Units.map (f : R →* S) hu.unit = (by simpa using hu.map f :
      IsUnit (1 - f r * f s)).unit := Units.ext (by simp)
  simp only [dennisStein_def, map_mul, map_inv, map_x, map_h, map_neg, hunit]
  simp [← hunit]

/-- **Reindexing the Dennis–Stein word**: an embedding `e` of index types sends `⟨r, s⟩_{ij}` to
`⟨r, s⟩_{e i, e j}`. -/
@[simp]
theorem mapIndex_dennisStein {κ : Type*} (e : ι ↪ κ) {i j : ι} (hij : i ≠ j) (r s : R)
    (hu : IsUnit (1 - r * s)) :
    mapIndex (R := R) e (dennisStein hij r s hu) = dennisStein (e.injective.ne hij) r s hu := by
  simp [dennisStein_def]

/-! ### Conjugation by Weyl elements -/

/-- A conjugation of the Steinberg group that carries the root subgroups at `(i, j)` and `(j, i)`
onto those at `(p, q)` and `(q, p)`, parameter by parameter, carries `⟨r, s⟩_{ij}` to
`⟨r, s⟩_{pq}`. -/
private theorem conj_dennisStein_of_conj_x {i j p q : ι} (hij : i ≠ j) (hpq : p ≠ q)
    (g : IndexedSteinbergGroup ι R) (hx : ∀ a, g * x hij a * g⁻¹ = x hpq a)
    (hy : ∀ a, g * x hij.symm a * g⁻¹ = x hpq.symm a) (r s : R) (hu : IsUnit (1 - r * s)) :
    g * dennisStein hij r s hu * g⁻¹ = dennisStein hpq r s hu := by
  simp only [← MulAut.conj_apply] at hx hy ⊢
  simp only [dennisStein_def, h_def, w_def, map_mul, map_inv, hx, hy]

/-- Conjugation by `w_{kj}(1)` carries the Dennis–Stein word at `(i, j)` to the one at `(i, k)`,
for pairwise distinct `i, j, k`. -/
theorem w_one_mul_dennisStein_mul_inv {i j k : ι} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (r s : R) (hu : IsUnit (1 - r * s)) :
    w hjk.symm 1 * dennisStein hij r s hu * (w hjk.symm 1)⁻¹ = dennisStein hik r s hu := by
  refine conj_dennisStein_of_conj_x hij hik _ (fun a ↦ ?_) (fun a ↦ ?_) r s hu
  · rw [w_mul_x_mul_inv_kj hjk.symm hik.symm hij.symm]
    simp
  · rw [w_mul_x_mul_inv_jk hjk.symm hik.symm hij.symm]
    simp

/-- Conjugation by `w_{ik}(-1)` carries the Dennis–Stein word at `(i, j)` to the one at `(k, j)`,
for pairwise distinct `i, j, k`. -/
theorem w_neg_one_mul_dennisStein_mul_inv {i j k : ι} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (r s : R) (hu : IsUnit (1 - r * s)) :
    w hik (-1) * dennisStein hij r s hu * (w hik (-1))⁻¹ =
      dennisStein (hjk.symm : k ≠ j) r s hu := by
  refine conj_dennisStein_of_conj_x hij hjk.symm _ (fun a ↦ ?_) (fun a ↦ ?_) r s hu
  · rw [w_mul_x_mul_inv_ik hik hij hjk.symm]
    simp
  · rw [w_mul_x_mul_inv_ki hik hij hjk.symm]
    simp

/-! ### The image in the general linear group -/

section FiniteIndex

variable [Fintype ι] [DecidableEq ι]

/-- The four elementary matrices of the Dennis–Stein word multiply to `diag(u, u⁻¹)` in the
`2 × 2` block at `(i, j)`, written as `1 + (u - 1) E_{ii} + (u⁻¹ - 1) E_{jj}`. -/
private theorem one_add_single_dennisStein {i j : ι} (hij : i ≠ j) {r s : R}
    (hrs : Commute r s) {u : Rˣ} (hu : (u : R) = 1 - r * s) :
    (1 + single j i (-(s * (u⁻¹ : Rˣ)))) * (1 + single i j (-r)) * (1 + single j i s) *
        (1 + single i j ((u⁻¹ : Rˣ) * r)) =
      1 + single i i ((u : R) - 1) + single j j (((u⁻¹ : Rˣ) : R) - 1) := by
  -- the product `(1 + a E_{ji}) (1 + b E_{ij}) (1 + c E_{ji}) (1 + d E_{ij})` in general
  have expand (a b c d : R) :
      (1 + single j i a) * (1 + single i j b) * (1 + single j i c) * (1 + single i j d) =
        1 + single j i (a + c + a * b * c) + single i j (b + d + b * c * d) + single i i (b * c) +
          single j j (a * b + (a + c + a * b * c) * d) := by
    simp only [mul_add, add_mul, one_mul, mul_one, single_mul_single_same,
      single_mul_single_of_ne, hij, hij.symm, ne_eq, not_false_eq_true, add_zero,
      single_add, mul_assoc]
    abel
  set v : R := ((u⁻¹ : Rˣ) : R)
  have hvu : v * u = 1 := u.inv_mul
  have huv : (u : R) * v = 1 := u.mul_inv
  have hsv : Commute s v := by
    refine Commute.units_inv_right (Commute.symm ?_)
    rw [hu]
    exact (Commute.one_left s).sub_left (hrs.mul_left (Commute.refl s))
  -- the coefficients of `E_{ji}` and `E_{ij}` vanish
  have h₁ : -(s * v) + s + -(s * v) * -r * s = 0 := by
    have e : s * v - s * v * (r * s) = s := by
      calc s * v - s * v * (r * s) = s * v * (1 - r * s) := by rw [mul_sub, mul_one]
        _ = s := by rw [← hu, mul_assoc, hvu, mul_one]
    calc -(s * v) + s + -(s * v) * -r * s = -(s * v) + (s * v - s * v * (r * s)) +
          s * v * (r * s) := by rw [e]; noncomm_ring
      _ = 0 := by abel
  have h₂ : -r + v * r + -r * s * (v * r) = 0 := by
    have e : v * r - r * s * (v * r) = r := by
      calc v * r - r * s * (v * r) = (1 - r * s) * (v * r) := by rw [sub_mul, one_mul]
        _ = r := by rw [← hu, ← mul_assoc, huv, one_mul]
    calc -r + v * r + -r * s * (v * r) = -r + (v * r - r * s * (v * r)) := by noncomm_ring
      _ = 0 := by rw [e]; abel
  -- the diagonal coefficients are `u - 1` and `u⁻¹ - 1`
  have h₃ : -(s * v) * -r = v - 1 := by
    calc -(s * v) * -r = v * (r * s) := by rw [neg_mul_neg, hsv.eq, mul_assoc, ← hrs.eq]
      _ = v - 1 := by rw [← hvu, hu, mul_sub, mul_one, sub_sub_cancel]
  have h₄ : -r * s = u - 1 := by rw [hu, sub_sub_cancel_left, neg_mul]
  rw [expand, h₁, h₂, h₃, h₄, zero_mul, add_zero, single_zero,
    single_zero, add_zero, add_zero]

/-- The four elementary factors `x_{ji}(-s u⁻¹) x_{ij}(-r) x_{ji}(s) x_{ij}(u⁻¹ r)` of the
Dennis–Stein word map to the diagonal matrix `diag(u, u⁻¹)` at `(i, j)`, where `u = 1 - r s`. -/
theorem toGL_dennisStein_mul_h {i j : ι} (hij : i ≠ j) {r s : R} (hrs : Commute r s)
    (hu : IsUnit (1 - r * s)) :
    toGL (dennisStein hij r s hu * h hij hu.unit) =
      diagGL (Pi.mulSingle i hu.unit * Pi.mulSingle j hu.unit⁻¹) := by
  -- `diag(u, u⁻¹)` at `(i, j)` is `1 + (u - 1) E_{ii} + (u⁻¹ - 1) E_{jj}`
  have hdiag (u : Rˣ) : (diagGL (Pi.mulSingle i u * Pi.mulSingle j u⁻¹) : Matrix ι ι R) =
      1 + single i i ((u : R) - 1) + single j j (((u⁻¹ : Rˣ) : R) - 1) := by
    rw [diagGL_coe]
    ext p q
    by_cases hpq : p = q
    · subst hpq
      by_cases hpi : p = i
      · subst hpi
        simp [hij, hij.symm]
      · by_cases hpj : p = j
        · subst hpj
          simp [hij, hpi]
        · simp [hpi, hpj, Ne.symm hpi, Ne.symm hpj]
    · have hi : ¬(i = p ∧ i = q) := fun h ↦ hpq (h.1.symm.trans h.2)
      have hj : ¬(j = p ∧ j = q) := fun h ↦ hpq (h.1.symm.trans h.2)
      simp [hpq, hi, hj]
  rw [dennisStein_def, inv_mul_cancel_right]
  apply Units.ext
  rw [hdiag]
  simp only [map_mul, Units.val_mul, toGL_x, coe_transvectionUnit_eq_one_add_single]
  exact one_add_single_dennisStein hij hrs hu.unit_spec

/-- When `r` and `s` commute, the Dennis–Stein word `⟨r, s⟩_{ij}` maps to the identity of
`GL ι R`. -/
@[simp]
theorem toGL_dennisStein {i j : ι} (hij : i ≠ j) {r s : R} (hrs : Commute r s)
    (hu : IsUnit (1 - r * s)) : toGL (dennisStein hij r s hu) = 1 := by
  have key := toGL_dennisStein_mul_h hij hrs hu
  rwa [map_mul, toGL_h, mul_eq_right] at key

end FiniteIndex

/-! ### The Dennis–Stein word of a unit -/

/-- For a unit `r` and a unit `u = 1 - r s`, the four elementary factors of the Dennis–Stein word
are the product `w_{ij}(-r) w_{ij}(u⁻¹ r)` of two Weyl elements, in the presence of a third index
`k`. -/
private theorem x_mul_x_mul_x_mul_x_eq_w_mul_w {i j k : ι} (hij : i ≠ j) (hik : i ≠ k)
    (hjk : j ≠ k) (r u : Rˣ) {s : R} (hu : (u : R) = 1 - r * s) :
    x hij.symm (-(s * (u⁻¹ : Rˣ))) * x hij (-(r : R)) * x hij.symm s *
      x hij ((u⁻¹ : Rˣ) * (r : R)) = w hij (-r) * w hij (u⁻¹ * r) := by
  set c : Rˣ := u⁻¹ * r
  have hcval : (c : R) = (u⁻¹ : Rˣ) * r := Units.val_mul _ _
  -- scalar identities: `c⁻¹ = r⁻¹ - s` and `r⁻¹ (c - r) r⁻¹ = s u⁻¹`
  have hru : ((r⁻¹ : Rˣ) : R) * u + s = (r⁻¹ : Rˣ) := by
    rw [hu, mul_sub, mul_one, ← mul_assoc, Units.inv_mul, one_mul, sub_add_cancel]
  have hc : ((c⁻¹ : Rˣ) : R) = (r⁻¹ : Rˣ) - s := by
    rw [_root_.mul_inv_rev, inv_inv, Units.val_mul]
    exact eq_sub_of_add_eq hru
  have hcr : ((r⁻¹ : Rˣ) : R) * ((c : R) - r) * (r⁻¹ : Rˣ) = s * (u⁻¹ : Rˣ) := by
    have e : ((r⁻¹ : Rˣ) : R) * (u⁻¹ : Rˣ) = (r⁻¹ : Rˣ) + s * (u⁻¹ : Rˣ) := by
      calc ((r⁻¹ : Rˣ) : R) * (u⁻¹ : Rˣ) = (((r⁻¹ : Rˣ) : R) * u + s) * (u⁻¹ : Rˣ) := by
            rw [hru]
        _ = (r⁻¹ : Rˣ) + s * (u⁻¹ : Rˣ) := by rw [add_mul, mul_assoc, Units.mul_inv, mul_one]
    rw [mul_sub, sub_mul, Units.inv_mul, one_mul, hcval, ← mul_assoc, mul_assoc _ (r : R),
      Units.mul_inv, mul_one, e, add_sub_cancel_left]
  -- `w_{ij}(-r) x_{ij}(c - r) w_{ij}(-r)⁻¹ = x_{ji}(-s u⁻¹)`
  have hconj : w hij (-r) * x hij ((c : R) - r) = x hij.symm (-(s * (u⁻¹ : Rˣ))) * w hij (-r) := by
    refine mul_inv_eq_iff_eq_mul.mp ?_
    rw [w_mul_x_mul_inv_ij hij hik hjk, ← hcr]
    simp only [inv_neg, Units.val_neg, neg_mul, mul_neg, neg_neg]
  have hw : w hij (-r) = x hij (-(r : R)) * x hij.symm ((r⁻¹ : Rˣ) : R) * x hij (-(r : R)) := by
    simp [w_def]
  have hs : x hij.symm s = x hij.symm ((r⁻¹ : Rˣ) : R) * x hij.symm (-((c⁻¹ : Rˣ) : R)) := by
    rw [← x_add, hc]
    congr 1
    abel
  -- split `x_{ji}(s)` and `x_{ij}(c)`, and move `x_{ij}(c - r)` across `w_{ij}(-r)`
  rw [w_def hij c, ← hcval, hs, ← sub_add_cancel (c : R) r, x_add]
  simp only [← mul_assoc]
  rw [hconj, hw]
  simp only [mul_assoc, ← x_add, neg_add_cancel, x_zero, one_mul]

/-- **The Dennis–Stein word of a unit is a symbol.** If `r` is a unit commuting with `s` and
`u = 1 - r s` is a unit, then `⟨r, s⟩_{ij} = ⁅h_{ik}(r), h_{ij}(u)⁆` for pairwise distinct
`i, j, k`. -/
theorem dennisStein_eq_commutatorElement_h_h {i j k : ι} (hij : i ≠ j) (hik : i ≠ k)
    (hjk : j ≠ k) (r : Rˣ) {s : R} (hrs : Commute (r : R) s) (hu : IsUnit (1 - r * s)) :
    dennisStein hij (r : R) s hu = ⁅h hik r, h hij hu.unit⁆ := by
  rw [dennisStein_def, x_mul_x_mul_x_mul_x_eq_w_mul_w hij hik hjk r hu.unit hu.unit_spec]
  set u := hu.unit
  -- conjugating `w_{ij}(u⁻¹ r)` by `w_{ij}(-r)` gives `w_{ij}(u r)`
  have key := w_mul_w_mul_inv hij hik hjk (-r) (u⁻¹ * r)
  rw [show -r * (u⁻¹ * r)⁻¹ * -r = u * r by
    simp only [_root_.mul_inv_rev, inv_inv, neg_mul, mul_neg, neg_neg, mul_inv_cancel_left]] at key
  have hru : r * u = u * r := Units.ext (by
    rw [Units.val_mul, Units.val_mul, hu.unit_spec]
    exact ((Commute.one_right _).sub_right ((Commute.refl _).mul_right hrs)).eq)
  rw [mul_inv_eq_iff_eq_mul.mp key, w_mul_w, neg_neg, ← commutatorElement_inv,
    commutatorElement_h_h hij hik hjk, hru]
  group

end IndexedSteinbergGroup

/-! ### The Dennis–Stein word in the stable Steinberg group -/

namespace SteinbergGroup

open IndexedSteinbergGroup

variable {R : Type*} [Ring R]

/-- When `r` and `s` commute, the Dennis–Stein word `⟨r, s⟩_{ij}` of `St(R)` lies in the kernel
`K₂(R)` of `St(R) → GL_∞(R)`. -/
@[simp]
theorem toStableGL_dennisStein {i j : ℕ} (hij : i ≠ j) {r s : R} (hrs : Commute r s)
    (hu : IsUnit (1 - r * s)) : toStableGL R (dennisStein hij r s hu) = 1 := by
  have hi : i < max i j + 1 := by omega
  have hj : j < max i j + 1 := by omega
  have hij' : (⟨i, hi⟩ : Fin (max i j + 1)) ≠ ⟨j, hj⟩ := fun e ↦ hij (congrArg Fin.val e)
  have key : ofFin R _ (dennisStein hij' r s hu) = dennisStein hij r s hu := by
    simp [dennisStein_def]
  rw [← key, toStableGL_ofFin, toGL_dennisStein hij' hrs, map_one]

/-- When `r` and `s` commute, the Dennis–Stein word `⟨r, s⟩_{ij}` is central in `St(R)`. -/
theorem dennisStein_mem_center {i j : ℕ} (hij : i ≠ j) {r s : R} (hrs : Commute r s)
    (hu : IsUnit (1 - r * s)) : dennisStein hij r s hu ∈ Subgroup.center (SteinbergGroup R) :=
  ker_toStableGL_le_center (toStableGL_dennisStein hij hrs hu)

/-- Changing the second index: `⟨r, s⟩_{ij} = ⟨r, s⟩_{ik}` in `St(R)` for pairwise distinct
`i, j, k`. -/
private theorem dennisStein_eq_dennisStein_snd {i j k : ℕ} (hij : i ≠ j) (hik : i ≠ k)
    (hjk : j ≠ k) {r s : R} (hrs : Commute r s) (hu : IsUnit (1 - r * s)) :
    dennisStein hij r s hu = dennisStein hik r s hu := by
  rw [← w_one_mul_dennisStein_mul_inv hij hik hjk,
    Subgroup.mem_center_iff.mp (dennisStein_mem_center hij hrs hu), mul_inv_cancel_right]

/-- Changing the first index: `⟨r, s⟩_{ij} = ⟨r, s⟩_{kj}` in `St(R)` for pairwise distinct
`i, j, k`. -/
private theorem dennisStein_eq_dennisStein_fst {i j k : ℕ} (hij : i ≠ j) (hik : i ≠ k)
    (hjk : j ≠ k) {r s : R} (hrs : Commute r s) (hu : IsUnit (1 - r * s)) :
    dennisStein hij r s hu = dennisStein (hjk.symm : k ≠ j) r s hu := by
  rw [← w_neg_one_mul_dennisStein_mul_inv hij hik hjk,
    Subgroup.mem_center_iff.mp (dennisStein_mem_center hij hrs hu), mul_inv_cancel_right]

/-- **Index independence of the Dennis–Stein word**: when `r` and `s` commute, the words
`⟨r, s⟩_{ij}` and `⟨r, s⟩_{kl}` agree in `St(R)` for any `i ≠ j` and `k ≠ l`. -/
theorem dennisStein_eq_dennisStein {i j k l : ℕ} (hij : i ≠ j) (hkl : k ≠ l) {r s : R}
    (hrs : Commute r s) (hu : IsUnit (1 - r * s)) :
    dennisStein hij r s hu = dennisStein hkl r s hu := by
  -- route both words through the pair `(m + 1, m)` of fresh indices
  obtain ⟨m, hm⟩ : ∃ m, m = i + j + k + l + 1 := ⟨_, rfl⟩
  have hm' : m + 1 ≠ m := by omega
  have route {p q : ℕ} (hpq : p ≠ q) (hp : p < m) (hq : q < m) :
      dennisStein hpq r s hu = dennisStein hm' r s hu :=
    (dennisStein_eq_dennisStein_snd hpq (k := m) (by omega) (by omega) hrs hu).trans
      (dennisStein_eq_dennisStein_fst (i := p) (j := m) (k := m + 1) (by omega) (by omega)
        (by omega) hrs hu)
  exact (route hij (by omega) (by omega)).trans (route hkl (by omega) (by omega)).symm

end SteinbergGroup

/-! ### Dennis–Stein symbols in `K₂` -/

section Symbol

open IndexedSteinbergGroup SteinbergGroup

variable {R : Type*} [Ring R]

/-- The **Dennis–Stein symbol** `⟨r, s⟩ ∈ K₂(R)` of commuting elements `r, s` of `R` with
`1 - r s` a unit: the Dennis–Stein word `⟨r, s⟩_{ij}` of `St(R)`, which lies in `K₂(R)` and does
not depend on the distinct indices `i, j` (`TauCeti.coe_dennisSteinSymbol`). -/
def dennisSteinSymbol (r s : R) (hrs : Commute r s) (hu : IsUnit (1 - r * s)) : AlgebraicK2 R :=
  ⟨dennisStein zero_ne_one r s hu, toStableGL_dennisStein zero_ne_one hrs hu⟩

/-- The Dennis–Stein symbol `⟨r, s⟩` is the Dennis–Stein word `⟨r, s⟩_{ij}` at any pair of
distinct indices `i, j`. -/
theorem coe_dennisSteinSymbol {r s : R} (hrs : Commute r s) (hu : IsUnit (1 - r * s)) {i j : ℕ}
    (hij : i ≠ j) : (dennisSteinSymbol r s hrs hu : SteinbergGroup R) = dennisStein hij r s hu :=
  dennisStein_eq_dennisStein zero_ne_one hij hrs hu

/-- The Dennis–Stein symbol `⟨0, s⟩` is trivial. -/
@[simp]
theorem dennisSteinSymbol_zero_left (s : R) (hrs : Commute 0 s) (hu : IsUnit (1 - 0 * s)) :
    dennisSteinSymbol 0 s hrs hu = 1 :=
  Subtype.ext (dennisStein_zero_left _ s hu)

/-- The Dennis–Stein symbol `⟨r, 0⟩` is trivial. -/
@[simp]
theorem dennisSteinSymbol_zero_right (r : R) (hrs : Commute r 0) (hu : IsUnit (1 - r * 0)) :
    dennisSteinSymbol r 0 hrs hu = 1 :=
  Subtype.ext (dennisStein_zero_right _ r hu)

/-- **The Dennis–Stein symbol of a unit**: if `r` is a unit commuting with `s` and `1 - r s` is a
unit, then `⟨r, s⟩ = {r, 1 - r s}`. -/
theorem dennisSteinSymbol_eq_steinbergSymbol (r : Rˣ) {s : R} (hrs : Commute (r : R) s)
    (hu : IsUnit (1 - r * s)) :
    dennisSteinSymbol (r : R) s hrs hu = steinbergSymbol r hu.unit (Commute.units_val_iff.mp (by
      rw [hu.unit_spec]
      exact (Commute.one_right _).sub_right ((Commute.refl _).mul_right hrs))) := by
  refine Subtype.ext ?_
  rw [coe_dennisSteinSymbol hrs hu (by decide : (0 : ℕ) ≠ 2),
    dennisStein_eq_commutatorElement_h_h _ (by decide : (0 : ℕ) ≠ 1) (by decide) r hrs hu]
  refine (coe_steinbergSymbol_eq_commutatorElement _ ?_ ?_).symm
  · rw [toStableGL_h _ r (n := 3) (by decide) (by decide)]
    congr 2
    funext p
    fin_cases p <;> simp
  · rw [toStableGL_h _ hu.unit (n := 3) (by decide) (by decide)]
    congr 2
    funext p
    fin_cases p <;> simp

/-- **Steinberg symbols are Dennis–Stein symbols**: for commuting units `u` and `v`,
`{u, v} = ⟨u, u⁻¹ (1 - v)⟩`. -/
theorem steinbergSymbol_eq_dennisSteinSymbol {u v : Rˣ} (huv : Commute u v) :
    steinbergSymbol u v huv = dennisSteinSymbol (u : R) ((u⁻¹ : Rˣ) * (1 - v))
      ((Commute.refl (u : R)).units_inv_right.mul_right
        ((Commute.one_right _).sub_right huv.units_val))
      (by simp [← mul_assoc]) := by
  rw [dennisSteinSymbol_eq_steinbergSymbol]
  congr
  ext
  simp [← mul_assoc]

/-- **Naturality of Dennis–Stein symbols**: the homomorphism of `K₂` induced by a ring
homomorphism `f` sends `⟨r, s⟩` to `⟨f r, f s⟩`. -/
@[simp]
theorem AlgebraicK2.map_dennisSteinSymbol {S : Type*} [Ring S] (f : R →+* S) {r s : R}
    (hrs : Commute r s) (hu : IsUnit (1 - r * s)) :
    AlgebraicK2.map f (dennisSteinSymbol r s hrs hu) =
      dennisSteinSymbol (f r) (f s) (hrs.map f) (by simpa using hu.map f) :=
  Subtype.ext (by simp [dennisSteinSymbol])

end Symbol

end TauCeti
