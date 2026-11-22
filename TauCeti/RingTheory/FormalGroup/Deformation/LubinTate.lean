/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.FormalGroup.LazardRing.Generators

/-!
# The generic Lubin–Tate law

Let `F` be a commutative formal group law over a commutative ring `R` and `h` a natural number.
Lubin and Tate deform `F` over the power series ring `R⟦t₁, …, t_{h-1}⟧` by moving its Lazard
coordinates `x_{pⁱ - 1}`, `0 < i < h`, by the independent parameters `tᵢ`
(`FormalGroup.lubinTateLaw`). Setting every `tᵢ` to zero gives back `F`, so when `F` lifts a law
`F₀` over a field `k` along `ρ : R →+* k`, the generic law reduces to `F₀` along `ρ` composed with
the constant coefficient. Every commutative law over `k` has such a lift when `ρ` is surjective
(`FormalGroup.exists_map_eq_of_surjective`). Lubin and Tate show that, for `F₀` of height `h`,
such a law is a universal deformation of `F₀`; that theorem is not proved here.

The parameter `tᵢ` enters the law in degree `pⁱ` and not before, through the Lazard cocycle
`C_{pⁱ}`, since the Lazard coordinate `x_{pⁱ - 1}` does
(`TauCeti.LazardRing.homogeneousComponent_map_sub_map`). Precisely, if two specializations `g` and
`g'` of the parameters agree on the coefficients and on `t_j`, `j < i`, then the two specialized
laws agree below degree `pⁱ` and differ by `(g tᵢ - g' tᵢ) C_{pⁱ}` in degree `pⁱ`. Over the dual
numbers `k[ε]`, with `g tᵢ = g' tᵢ + ε`, this says that the derivative of the law in the
direction `tᵢ` has leading term `C_{pⁱ}`. In the proof of the Lubin–Tate theorem these leading
terms show that the derivatives of the generic law in the directions `tᵢ` give a basis of the
symmetric 2-cocycles of `F₀` modulo coboundaries.

The variable `i : Fin (h - 1)` of `R⟦t₁, …, t_{h-1}⟧` stands for `t_{i+1}`, and moves the Lazard
generator of index `TauCeti.lubinTateIndex hp i = p ^ (i + 1) - 1`. Only `1 < p` is needed for
the construction.

## Main definitions

* `TauCeti.lubinTateIndex hp i`: the index `p ^ (i + 1) - 1` of the Lazard generator moved by
  `t_{i+1}`.
* `FormalGroup.lubinTateLaw F hp h`: the generic Lubin–Tate deformation of `F` over
  `R⟦t₁, …, t_{h-1}⟧`.

## Main results

* `FormalGroup.lift_lubinTateLaw_generator_lubinTateIndex` and
  `FormalGroup.lift_lubinTateLaw_generator_of_forall_ne`: the Lazard coordinates of the generic
  law.
* `FormalGroup.map_constantCoeff_lubinTateLaw`: setting the parameters to zero gives back `F`.
* `FormalGroup.map_lubinTateLaw`: the generic law is natural in the coefficient ring.
* `FormalGroup.lubinTateLaw_of_le_one`: in height at most one there are no parameters.
* `FormalGroup.le_order_map_lubinTateLaw_sub_map` and
  `FormalGroup.homogeneousComponent_map_lubinTateLaw_sub_map`: specializations differing first in
  `tᵢ` agree below degree `pⁱ` and differ by a multiple of `C_{pⁱ}` in degree `pⁱ`.

## References

* J. Lubin and J. Tate, *Formal moduli for one-parameter formal Lie groups*, Bull. Soc. Math.
  France 94 (1966), §1 and §3.
-/

public section

noncomputable section

open MvPowerSeries TauCeti TauCeti.LazardRing

namespace TauCeti

variable {p : ℕ}

/-- The index `p ^ (i + 1) - 1` of the Lazard generator moved by the Lubin–Tate parameter
`t_{i+1}`. The generator of this index governs the part of degree `p ^ (i + 1)` of a formal group
law. -/
def lubinTateIndex (hp : 1 < p) (i : ℕ) : ℕ+ :=
  ⟨p ^ (i + 1) - 1, Nat.sub_pos_of_lt (Nat.one_lt_pow (Nat.succ_ne_zero i) hp)⟩

theorem coe_lubinTateIndex (hp : 1 < p) (i : ℕ) : (lubinTateIndex hp i : ℕ) = p ^ (i + 1) - 1 :=
  (rfl)

/-- The degree governed by the generator `lubinTateIndex hp i` is `p ^ (i + 1)`. -/
theorem coe_lubinTateIndex_add_one (hp : 1 < p) (i : ℕ) :
    (lubinTateIndex hp i : ℕ) + 1 = p ^ (i + 1) := by
  rw [coe_lubinTateIndex, Nat.sub_add_cancel (Nat.one_le_pow _ _ (by omega))]

theorem lubinTateIndex_strictMono (hp : 1 < p) : StrictMono (lubinTateIndex hp) := fun i j hij ↦ by
  rw [← PNat.coe_lt_coe, ← Nat.add_lt_add_iff_right (k := 1), coe_lubinTateIndex_add_one,
    coe_lubinTateIndex_add_one]
  exact Nat.pow_lt_pow_right hp (by omega)

@[simp]
theorem lubinTateIndex_lt_lubinTateIndex_iff (hp : 1 < p) {i j : ℕ} :
    lubinTateIndex hp i < lubinTateIndex hp j ↔ i < j :=
  (lubinTateIndex_strictMono hp).lt_iff_lt

theorem lubinTateIndex_injective (hp : 1 < p) : Function.Injective (lubinTateIndex hp) :=
  (lubinTateIndex_strictMono hp).injective

end TauCeti

namespace FormalGroup

variable {R S A : Type*} [CommRing R] [CommRing S] [CommRing A] {p : ℕ} {h : ℕ}

/-- The movement of the Lazard coordinates in the generic Lubin–Tate law: `t_{i+1}` on the
generator of index `lubinTateIndex hp i`, and `0` on the others. -/
private def lubinTateShift (hp : 1 < p) (h : ℕ) : ℕ+ → MvPowerSeries (Fin (h - 1)) R :=
  Function.extend (fun i : Fin (h - 1) ↦ lubinTateIndex hp i) X 0

private theorem lubinTateShift_lubinTateIndex (hp : 1 < p) (i : Fin (h - 1)) :
    lubinTateShift (R := R) hp h (lubinTateIndex hp i) = X i :=
  ((lubinTateIndex_injective hp).comp Fin.val_injective).extend_apply _ _ i

private theorem lubinTateShift_of_forall_ne (hp : 1 < p) {n : ℕ+}
    (hn : ∀ i : Fin (h - 1), lubinTateIndex hp i ≠ n) :
    lubinTateShift (R := R) hp h n = 0 :=
  Function.extend_apply' _ _ _ fun ⟨i, hi⟩ ↦ hn i hi

private theorem constantCoeff_lubinTateShift (hp : 1 < p) (n : ℕ+) :
    constantCoeff (lubinTateShift (R := R) hp h n) = 0 := by
  by_cases hn : ∃ i : Fin (h - 1), lubinTateIndex hp i = n
  · obtain ⟨i, rfl⟩ := hn
    rw [lubinTateShift_lubinTateIndex, constantCoeff_X]
  · rw [lubinTateShift_of_forall_ne hp (not_exists.1 hn), map_zero]

private theorem map_lubinTateShift (hp : 1 < p) (g : R →+* S) (n : ℕ+) :
    MvPowerSeries.map g (lubinTateShift (R := R) hp h n) = lubinTateShift hp h n := by
  by_cases hn : ∃ i : Fin (h - 1), lubinTateIndex hp i = n
  · obtain ⟨i, rfl⟩ := hn
    rw [lubinTateShift_lubinTateIndex, lubinTateShift_lubinTateIndex, map_X]
  · rw [lubinTateShift_of_forall_ne hp (not_exists.1 hn),
      lubinTateShift_of_forall_ne hp (not_exists.1 hn), map_zero]

variable (F : FormalGroup R) [F.IsComm] (hp : 1 < p)

/-- **The generic Lubin–Tate law.** The commutative formal group law over `R⟦t₁, …, t_{h-1}⟧` whose
Lazard coordinates are those of `F`, except that the coordinate `x_{pⁱ - 1}` is moved by `tᵢ`
for `0 < i < h`; the variable `i : Fin (h - 1)` stands for `t_{i+1}`. -/
def lubinTateLaw (h : ℕ) : FormalGroup (MvPowerSeries (Fin (h - 1)) R) :=
  LazardRing.formalGroup.map (homEquiv.symm fun n ↦
    C (LazardRing.lift ⟨F, inferInstance⟩ (generator n)) + lubinTateShift hp h n)

instance : (F.lubinTateLaw hp h).IsComm :=
  isComm_map _ _

/-- The homomorphism out of the Lazard ring classifying the generic Lubin–Tate law. -/
private theorem lift_lubinTateLaw :
    LazardRing.lift ⟨F.lubinTateLaw hp h, inferInstance⟩ = homEquiv.symm fun n ↦
      C (LazardRing.lift ⟨F, inferInstance⟩ (generator n)) + lubinTateShift hp h n := by
  rw [← Equiv.eq_symm_apply]
  exact Subtype.ext (LazardRing.coe_lift_symm _).symm

/-- The Lazard coordinate `x_{p^(i+1) - 1}` of the generic Lubin–Tate law is that of `F` plus the
parameter `t_{i+1}`. -/
@[simp]
theorem lift_lubinTateLaw_generator_lubinTateIndex (i : Fin (h - 1)) :
    LazardRing.lift ⟨F.lubinTateLaw hp h, inferInstance⟩ (generator (lubinTateIndex hp i)) =
      C (LazardRing.lift ⟨F, inferInstance⟩ (generator (lubinTateIndex hp i))) + X i := by
  rw [lift_lubinTateLaw, homEquiv_symm_apply_generator, lubinTateShift_lubinTateIndex]

/-- The Lazard coordinates of the generic Lubin–Tate law at generators other than the
`x_{pⁱ - 1}`, `0 < i < h`, are those of `F`. -/
theorem lift_lubinTateLaw_generator_of_forall_ne {n : ℕ+}
    (hn : ∀ i : Fin (h - 1), lubinTateIndex hp i ≠ n) :
    LazardRing.lift ⟨F.lubinTateLaw hp h, inferInstance⟩ (generator n) =
      C (LazardRing.lift ⟨F, inferInstance⟩ (generator n)) := by
  rw [lift_lubinTateLaw, homEquiv_symm_apply_generator, lubinTateShift_of_forall_ne hp hn,
    _root_.add_zero]

/-- Setting the Lubin–Tate parameters to zero gives back `F`. -/
@[simp]
theorem map_constantCoeff_lubinTateLaw : (F.lubinTateLaw hp h).map constantCoeff = F := by
  have h₁ : constantCoeff.comp (homEquiv.symm fun n ↦
      C (LazardRing.lift ⟨F, inferInstance⟩ (generator n)) + lubinTateShift hp h n) =
      LazardRing.lift ⟨F, inferInstance⟩ :=
    ringHom_ext fun n ↦ by simp [constantCoeff_lubinTateShift]
  rw [lubinTateLaw, map_comp, h₁, map_lift]

/-- The generic Lubin–Tate law is natural in the coefficient ring: its base change along the
coefficientwise map of `g` is the generic law of the base change of `F` along `g`. -/
theorem map_lubinTateLaw (g : R →+* S) :
    (F.lubinTateLaw hp h).map (MvPowerSeries.map g) = (F.map g).lubinTateLaw hp h := by
  rw [lubinTateLaw, lubinTateLaw, map_comp, comp_homEquiv_symm, LazardRing.lift_map]
  congr 2
  ext n
  simp [map_lubinTateShift]

/-- In height at most one the generic Lubin–Tate law has no parameters: it is `F` over the power
series ring in no variables. -/
theorem lubinTateLaw_of_le_one (hh : h ≤ 1) : F.lubinTateLaw hp h = F.map C := by
  have h₁ : (homEquiv.symm fun n ↦
      C (LazardRing.lift ⟨F, inferInstance⟩ (generator n)) + lubinTateShift hp h n) =
      C.comp (LazardRing.lift ⟨F, inferInstance⟩) :=
    ringHom_ext fun n ↦ by
      rw [homEquiv_symm_apply_generator,
        lubinTateShift_of_forall_ne hp fun i ↦ absurd i.isLt (by omega), _root_.add_zero,
        RingHom.comp_apply]
  rw [lubinTateLaw, h₁, ← map_comp, map_lift]

variable {F hp}

/-- Specializations agreeing on the coefficients and on `t_j`, `j < i`, agree on the Lazard
coordinates of the generic law below the index `lubinTateIndex hp i`. -/
private theorem apply_lubinTateLaw_coordinate_eq {g g' : MvPowerSeries (Fin (h - 1)) R →+* A}
    (hC : g.comp C = g'.comp C) {i : Fin (h - 1)} (hX : ∀ j < i, g (X j) = g' (X j)) {m : ℕ+}
    (hm : m < lubinTateIndex hp i) :
    g (C (LazardRing.lift ⟨F, inferInstance⟩ (generator m)) + lubinTateShift hp h m) =
      g' (C (LazardRing.lift ⟨F, inferInstance⟩ (generator m)) + lubinTateShift hp h m) := by
  rw [map_add, map_add, ← RingHom.comp_apply, hC, RingHom.comp_apply]
  congr 1
  by_cases hn : ∃ j : Fin (h - 1), lubinTateIndex hp j = m
  · obtain ⟨j, rfl⟩ := hn
    rw [lubinTateShift_lubinTateIndex]
    exact hX j (Fin.lt_def.2 ((lubinTateIndex_lt_lubinTateIndex_iff hp).1 hm))
  · rw [lubinTateShift_of_forall_ne hp (not_exists.1 hn), map_zero, map_zero]

/-- **The parameter `tᵢ` does not enter below degree `pⁱ`.** If two specializations `g` and `g'`
of the generic Lubin–Tate law agree on the coefficients and on the parameters `t_j`, `j < i`, the
specialized laws agree below degree `pⁱ`. Here `i : Fin (h - 1)` stands for `t_{i+1}`. -/
theorem le_order_map_lubinTateLaw_sub_map {g g' : MvPowerSeries (Fin (h - 1)) R →+* A}
    (hC : g.comp C = g'.comp C) {i : Fin (h - 1)} (hX : ∀ j < i, g (X j) = g' (X j)) :
    ((p ^ (i + 1 : ℕ) : ℕ) : ℕ∞) ≤
      (((F.lubinTateLaw hp h).map g).toPowerSeries -
        ((F.lubinTateLaw hp h).map g').toPowerSeries).order := by
  rw [lubinTateLaw, map_comp, map_comp, ← coe_lubinTateIndex_add_one hp]
  exact succ_le_order_map_sub_map fun m hm ↦ by
    simpa using apply_lubinTateLaw_coordinate_eq hC hX hm

/-- **The parameter `tᵢ` enters through `C_{pⁱ}`.** If two specializations `g` and `g'` of the
generic Lubin–Tate law agree on the coefficients and on the parameters `t_j`, `j < i`, the
specialized laws differ by `(g tᵢ - g' tᵢ) C_{pⁱ}` in degree `pⁱ`. Here `i : Fin (h - 1)` stands
for `t_{i+1}`. -/
theorem homogeneousComponent_map_lubinTateLaw_sub_map {g g' : MvPowerSeries (Fin (h - 1)) R →+* A}
    (hC : g.comp C = g'.comp C) {i : Fin (h - 1)} (hX : ∀ j < i, g (X j) = g' (X j)) :
    homogeneousComponent (p ^ (i + 1 : ℕ))
        (((F.lubinTateLaw hp h).map g).toPowerSeries -
          ((F.lubinTateLaw hp h).map g').toPowerSeries) =
      ↑((g (X i) - g' (X i)) • lazardCocycle (p ^ (i + 1 : ℕ)) A) := by
  rw [lubinTateLaw, map_comp, map_comp, ← coe_lubinTateIndex_add_one hp,
    homogeneousComponent_map_sub_map fun m hm ↦ by
      simpa using apply_lubinTateLaw_coordinate_eq hC hX hm]
  have hc := RingHom.congr_fun hC
    (LazardRing.lift ⟨F, inferInstance⟩ (generator (lubinTateIndex hp i)))
  simp only [RingHom.comp_apply] at hc
  simp only [RingHom.comp_apply, homEquiv_symm_apply_generator, lubinTateShift_lubinTateIndex,
    map_add, hc, add_sub_add_left_eq_sub]

end FormalGroup
