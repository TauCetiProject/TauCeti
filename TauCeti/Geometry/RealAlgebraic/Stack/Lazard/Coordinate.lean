/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.RealAlgebraic.Stack.Lazard.Basic
import TauCeti.Geometry.RealAlgebraic.Stack.Lazard.Product
import TauCeti.Geometry.RealAlgebraic.Stack.Sign

/-!
# Lazard delineation of the distinguished coordinate

Every nonzero constant multiple of the last coordinate polynomial has one constant root section,
at zero, over every nonempty base. Its Lazard evaluation in the base variables is the corresponding
constant multiple of the univariate polynomial `X`: no base power is removed, and its root has
multiplicity one. This supplies the exceptional coordinate factor in Lazard lifting, for which the
usual nonzero-trailing-coefficient preparation does not apply.

Such coordinate members can be adjoined to a Lazard delineation of the remaining members over a
preconnected base, provided that for each remaining member, `0` is a root of its Lazard
evaluations either over every base point or over none. Then either some root function vanishes
identically, and the root list is kept, or `0` lies in one fixed sector over every base point
(since no root function changes sign), and the zero section is inserted there. Without the
hypothesis on the root `0`, a root function could cross zero, as for `Xₙ - X₀` over `ℝ`.
The hypothesis holds for every member whose formal constant coefficient has constant Lazard
valuation on the base. In particular, a Lazard delineation of `q` gives one of `X * q` when the
constant coefficient of `q` has constant Lazard valuation.

## Main results

* `TauCeti.lazardDelineationCMulLastCoordinate`: the one-section Lazard delineation of a
  nonzero constant multiple of the last coordinate polynomial.
* `TauCeti.nonempty_lazardDelineation_lastCoordinate`: the specialization to the monic coordinate.
* `TauCeti.nonempty_lazardDelineation_of_comp`: adjoining nonzero multiples of the last
  coordinate to a family with a Lazard delineation.
* `TauCeti.LazardDelineation.isRoot_zero_of_lazardValuation_coeff_zero_eq`: constant valuation
  of the constant coefficient decides the root `0` uniformly.
* `TauCeti.nonempty_lazardDelineation_X_mul`: multiplying a delineated polynomial by the
  distinguished coordinate.

## References

S. McCallum, A. Parusiński, L. Paunescu, *Validity proof of Lazard's method for CAD
construction*, Journal of Symbolic Computation 92 (2019), Section 5.
-/

public section

open MvPolynomial Polynomial Set

namespace TauCeti

variable {n : ℕ} {S : Set (Fin n → ℝ)}

private theorem optionEquivRight_C_mul_lastCoordinate (a : ℝ) :
    optionEquivRight ℝ (Fin n)
        (rename finSuccEquivLast (MvPolynomial.C a * X (Fin.last n))) =
      MvPolynomial.C (Polynomial.C a * Polynomial.X) := by
  simp

/-- Over every base point, the Lazard evaluation of `a` times the last coordinate is `a * X`. -/
private theorem lazardEval_C_mul_lastCoordinate (a : ℝ) (x : Fin n → ℝ) :
    (optionEquivRight ℝ (Fin n)
        (rename finSuccEquivLast (MvPolynomial.C a * X (Fin.last n)))).lazardEval
      (Polynomial.C ∘ x) = Polynomial.C a * Polynomial.X := by
  rw [optionEquivRight_C_mul_lastCoordinate, MvPolynomial.lazardEval_C]

/-- For `a ≠ 0`, Lazard evaluation of `a` times the last coordinate removes no base power. -/
private theorem lazardExponent_C_mul_lastCoordinate {a : ℝ} (ha : a ≠ 0) (x : Fin n → ℝ) :
    (optionEquivRight ℝ (Fin n)
        (rename finSuccEquivLast (MvPolynomial.C a * X (Fin.last n)))).lazardExponent
      (Polynomial.C ∘ x) = 0 := by
  rw [optionEquivRight_C_mul_lastCoordinate]
  exact lazardExponent_eq_zero_of_eval_ne_zero (by simp [ha])

/-- For `a ≠ 0`, the Lazard evaluation of `a` times the last coordinate has the single root `0`,
which is simple. -/
private theorem rootMultiplicity_lazardEval_C_mul_lastCoordinate {a : ℝ} (ha : a ≠ 0)
    (x : Fin n → ℝ) (t : ℝ) :
    ((optionEquivRight ℝ (Fin n)
        (rename finSuccEquivLast (MvPolynomial.C a * X (Fin.last n)))).lazardEval
      (Polynomial.C ∘ x)).rootMultiplicity t = if t = 0 then 1 else 0 := by
  rw [lazardEval_C_mul_lastCoordinate, Polynomial.rootMultiplicity_mul (mul_ne_zero
    (Polynomial.C_ne_zero.mpr ha) Polynomial.X_ne_zero), Polynomial.rootMultiplicity_C, zero_add,
    ← sub_zero Polynomial.X, ← map_zero Polynomial.C, Polynomial.rootMultiplicity_X_sub_C]

private theorem isRoot_lazardEval_C_mul_lastCoordinate {a : ℝ} (ha : a ≠ 0) (x : Fin n → ℝ)
    {t : ℝ} :
    ((optionEquivRight ℝ (Fin n)
        (rename finSuccEquivLast (MvPolynomial.C a * X (Fin.last n)))).lazardEval
      (Polynomial.C ∘ x)).IsRoot t ↔ t = 0 := by
  rw [lazardEval_C_mul_lastCoordinate]
  simp [ha]

/-- A nonzero constant multiple of the distinguished (last) coordinate polynomial has the
constant root section zero as its Lazard delineation over every nonempty base. No base-variable
powers are removed, and the root has multiplicity one. This includes every associate of the
coordinate polynomial over `ℝ`. -/
noncomputable def lazardDelineationCMulLastCoordinate (hS : S.Nonempty) {a : ℝ} (ha : a ≠ 0) :
    LazardDelineation (fun _ : Unit ↦ MvPolynomial.C a * X (Fin.last n)) S :=
    { nonempty := hS
      count := 1
      root := fun _ _ ↦ 0
      continuous_root := fun _ ↦ continuous_const
      strictMono_root := fun _ ↦ Fin.strictMono_iff_lt_succ.mpr fun i ↦ Fin.elim0 i
      exponent := fun _ ↦ 0
      lazardExponent_eq := fun _ x ↦ lazardExponent_C_mul_lastCoordinate ha x.1
      multiplicity := fun _ _ ↦ 1
      rootMultiplicity_root := by
        intro _ _ x
        rw [rootMultiplicity_lazardEval_C_mul_lastCoordinate ha]
        simp
      exists_root_eq := fun _ x _ _ ht ↦
        ⟨0, ((isRoot_lazardEval_C_mul_lastCoordinate ha x.1).1 ht).symm⟩
      exists_multiplicity_pos := by
        intro _
        exact ⟨(), by simp⟩ }

@[simp]
theorem lazardDelineationCMulLastCoordinate_count (hS : S.Nonempty) {a : ℝ} (ha : a ≠ 0) :
    (lazardDelineationCMulLastCoordinate hS ha).count = 1 := (rfl)

@[simp]
theorem lazardDelineationCMulLastCoordinate_root (hS : S.Nonempty) {a : ℝ} (ha : a ≠ 0)
    (i : Fin (lazardDelineationCMulLastCoordinate hS ha).count) (x : S) :
    (lazardDelineationCMulLastCoordinate hS ha).root i x = 0 := (rfl)

@[simp]
theorem lazardDelineationCMulLastCoordinate_exponent (hS : S.Nonempty) {a : ℝ}
    (ha : a ≠ 0) (k : Unit) :
    (lazardDelineationCMulLastCoordinate hS ha).exponent k = 0 := (rfl)

@[simp]
theorem lazardDelineationCMulLastCoordinate_multiplicity (hS : S.Nonempty) {a : ℝ}
    (ha : a ≠ 0) (k : Unit) (i : Fin (lazardDelineationCMulLastCoordinate hS ha).count) :
    (lazardDelineationCMulLastCoordinate hS ha).multiplicity k i = 1 := (rfl)

/-- The distinguished coordinate itself has the constant root section zero over every nonempty
base. -/
theorem nonempty_lazardDelineation_lastCoordinate (hS : S.Nonempty) :
    Nonempty (LazardDelineation (fun _ : Unit ↦ X (Fin.last n)) S) := by
  simpa only [map_one, one_mul] using
    Nonempty.intro (lazardDelineationCMulLastCoordinate hS one_ne_zero)

section Adjoin

variable {ι κ : Type*} {F : ι → MvPolynomial (Fin (n + 1)) ℝ} {f : κ → ι}

/-- If the members outside the range of `f` are nonzero multiples of the last coordinate, every
member of `F` has the same removed base exponents over all points of the base of a Lazard
delineation of `F ∘ f`. -/
private theorem lazardExponent_eq_of_comp (D : LazardDelineation (F ∘ f) S)
    (hcoord : ∀ k, k ∉ range f → ∃ a ≠ 0, F k = MvPolynomial.C a * X (Fin.last n)) (k : ι)
    (x y : S) :
    (optionEquivRight ℝ (Fin n) (rename finSuccEquivLast (F k))).lazardExponent
        (Polynomial.C ∘ x.1) =
      (optionEquivRight ℝ (Fin n) (rename finSuccEquivLast (F k))).lazardExponent
        (Polynomial.C ∘ y.1) := by
  by_cases hk : k ∈ range f
  · obtain ⟨j, rfl⟩ := hk
    exact (D.lazardExponent_eq j x).trans (D.lazardExponent_eq j y).symm
  · obtain ⟨a, ha, hF⟩ := hcoord k hk
    rw [hF, lazardExponent_C_mul_lastCoordinate ha, lazardExponent_C_mul_lastCoordinate ha]

/-- The root multiplicities of a nonzero multiple of the last coordinate depend only on whether
the point is `0`. -/
private theorem rootMultiplicity_eq_of_eq_C_mul_lastCoordinate
    {p : MvPolynomial (Fin (n + 1)) ℝ} (hp : ∃ a ≠ 0, p = MvPolynomial.C a * X (Fin.last n))
    (x y : Fin n → ℝ) {t t' : ℝ} (h : t = 0 ↔ t' = 0) :
    ((optionEquivRight ℝ (Fin n) (rename finSuccEquivLast p)).lazardEval
        (Polynomial.C ∘ x)).rootMultiplicity t =
      ((optionEquivRight ℝ (Fin n) (rename finSuccEquivLast p)).lazardEval
        (Polynomial.C ∘ y)).rootMultiplicity t' := by
  obtain ⟨a, ha, rfl⟩ := hp
  rw [rootMultiplicity_lazardEval_C_mul_lastCoordinate ha,
    rootMultiplicity_lazardEval_C_mul_lastCoordinate ha]
  simp only [h]

/-- Adjoining coordinate members when each of them has `0` as a root function of `D`, which then
already delineates the whole family. -/
private theorem nonempty_lazardDelineation_of_comp_of_forall_eq_zero
    (D : LazardDelineation (F ∘ f) S)
    (hcoord : ∀ k, k ∉ range f → ∃ a ≠ 0, F k = MvPolynomial.C a * X (Fin.last n))
    (hR : ∀ k, k ∉ range f → ∃ i, ∀ x, D.root i x = 0) :
    Nonempty (LazardDelineation F S) := by
  let x₀ : S := ⟨D.nonempty.some, D.nonempty.some_mem⟩
  let Q (k : ι) (x : S) :=
    (optionEquivRight ℝ (Fin n) (rename finSuccEquivLast (F k))).lazardEval (Polynomial.C ∘ x.1)
  refine ⟨{ nonempty := D.nonempty
            count := D.count
            root := D.root
            continuous_root := D.continuous_root
            strictMono_root := D.strictMono_root
            exponent := fun k ↦ (optionEquivRight ℝ (Fin n)
              (rename finSuccEquivLast (F k))).lazardExponent (Polynomial.C ∘ x₀.1)
            lazardExponent_eq := fun k x ↦ lazardExponent_eq_of_comp D hcoord k x x₀
            multiplicity := fun k i ↦ (Q k x₀).rootMultiplicity (D.root i x₀)
            rootMultiplicity_root := fun k i x ↦ ?_
            exists_root_eq := fun k x hk t ht ↦ ?_
            exists_multiplicity_pos := fun i ↦ ?_ }⟩
  · by_cases hk : k ∈ range f
    · obtain ⟨j, rfl⟩ := hk
      exact (D.rootMultiplicity_root j i x).trans (D.rootMultiplicity_root j i x₀).symm
    · obtain ⟨i₀, hi₀⟩ := hR k hk
      have hi (y : S) : D.root i y = 0 ↔ i = i₀ :=
        ⟨fun h ↦ (D.strictMono_root y).injective (h.trans (hi₀ y).symm), fun h ↦ h ▸ hi₀ y⟩
      exact rootMultiplicity_eq_of_eq_C_mul_lastCoordinate (hcoord k hk) x.1 x₀.1
        ((hi x).trans (hi x₀).symm)
  · by_cases hk' : k ∈ range f
    · obtain ⟨j, rfl⟩ := hk'
      exact D.exists_root_eq j x hk t ht
    · obtain ⟨i₀, hi₀⟩ := hR k hk'
      obtain ⟨a, ha, hF⟩ := hcoord k hk'
      rw [hF, isRoot_lazardEval_C_mul_lastCoordinate ha] at ht
      exact ⟨i₀, (hi₀ x).trans ht.symm⟩
  · obtain ⟨j, hj⟩ := D.exists_multiplicity_pos i
    exact ⟨f j, (D.rootMultiplicity_root j i x₀).symm ▸ hj⟩

/-- Adjoining coordinate members when `0` lies in the sector `p` of `D` over every base point:
the zero section is inserted at position `p`. -/
private theorem nonempty_lazardDelineation_of_comp_of_mem_sectorSet
    (D : LazardDelineation (F ∘ f) S)
    (hcoord : ∀ k, k ∉ range f → ∃ a ≠ 0, F k = MvPolynomial.C a * X (Fin.last n))
    {p : Fin (D.count + 1)} (hp : ∀ x, (x, (0 : ℝ)) ∈ sectorSet D.root p) {k₀ : ι}
    (hk₀ : k₀ ∉ range f) :
    Nonempty (LazardDelineation F S) := by
  let x₀ : S := ⟨D.nonempty.some, D.nonempty.some_mem⟩
  let Q (k : ι) (x : S) :=
    (optionEquivRight ℝ (Fin n) (rename finSuccEquivLast (F k))).lazardEval (Polynomial.C ∘ x.1)
  have hne (i : Fin D.count) (x : S) : D.root i x ≠ 0 := fun hx ↦
    disjoint_left.1 (disjoint_sectionSet_sectorSet D.root i p) (mem_sectionSet.2 hx) (hp x)
  -- No member of `F ∘ f` has the root `0`.
  have hzmult (j : κ) (x : S) : (Q (f j) x).rootMultiplicity 0 = 0 := by
    by_cases hF : F (f j) = 0
    · simp [Q, hF]
    refine Polynomial.rootMultiplicity_eq_zero fun hroot ↦ ?_
    obtain ⟨i, hi⟩ := D.exists_root_eq j x hF 0 hroot
    exact hne i x hi
  let root (l : Fin (D.count + 1)) (x : S) : ℝ :=
    Fin.insertNth (α := fun _ ↦ ℝ) p 0 (fun i ↦ D.root i x) l
  have hroot_p (x : S) : root p x = 0 := Fin.insertNth_apply_same _ _ _
  have hroot_succAbove (i : Fin D.count) (x : S) : root (p.succAbove i) x = D.root i x :=
    Fin.insertNth_apply_succAbove _ _ _ _
  refine ⟨{ nonempty := D.nonempty
            count := D.count + 1
            root := root
            continuous_root := fun l ↦ ?_
            strictMono_root := fun x l l' hll' ↦ ?_
            exponent := fun k ↦ (optionEquivRight ℝ (Fin n)
              (rename finSuccEquivLast (F k))).lazardExponent (Polynomial.C ∘ x₀.1)
            lazardExponent_eq := fun k x ↦ lazardExponent_eq_of_comp D hcoord k x x₀
            multiplicity := fun k l ↦ (Q k x₀).rootMultiplicity (root l x₀)
            rootMultiplicity_root := fun k l x ↦ ?_
            exists_root_eq := fun k x hk t ht ↦ ?_
            exists_multiplicity_pos := fun l ↦ ?_ }⟩
  · rcases Fin.eq_self_or_eq_succAbove p l with rfl | ⟨i, rfl⟩
    · exact (continuous_congr hroot_p).2 continuous_const
    · exact (continuous_congr (hroot_succAbove i)).2 (D.continuous_root i)
  · -- The inserted zero lies above the sections below sector `p` and below the others.
    dsimp only
    rcases Fin.eq_self_or_eq_succAbove p l with hl | ⟨i, rfl⟩ <;>
      rcases Fin.eq_self_or_eq_succAbove p l' with hl' | ⟨i', rfl⟩
    · exact absurd (hl.trans hl'.symm) hll'.ne
    · rw [hl] at hll' ⊢
      rw [hroot_p, hroot_succAbove]
      exact (mem_sectorSet.1 (hp x)).2 i' ((Fin.lt_succAbove_iff_le_castSucc p i').1 hll')
    · rw [hl'] at hll' ⊢
      rw [hroot_p, hroot_succAbove]
      exact (mem_sectorSet.1 (hp x)).1 i ((Fin.succAbove_lt_iff_castSucc_lt p i).1 hll')
    · rw [hroot_succAbove, hroot_succAbove]
      exact D.strictMono_root x (Fin.succAbove_lt_succAbove_iff.1 hll')
  · rcases Fin.eq_self_or_eq_succAbove p l with hl | ⟨i, rfl⟩ <;> by_cases hk : k ∈ range f
    · obtain ⟨j, rfl⟩ := hk
      rw [hl, hroot_p, hroot_p]
      exact (hzmult j x).trans (hzmult j x₀).symm
    · rw [hl, hroot_p, hroot_p]
      exact rootMultiplicity_eq_of_eq_C_mul_lastCoordinate (hcoord k hk) x.1 x₀.1 Iff.rfl
    · obtain ⟨j, rfl⟩ := hk
      rw [hroot_succAbove, hroot_succAbove]
      exact (D.rootMultiplicity_root j i x).trans (D.rootMultiplicity_root j i x₀).symm
    · rw [hroot_succAbove, hroot_succAbove]
      exact rootMultiplicity_eq_of_eq_C_mul_lastCoordinate (hcoord k hk) x.1 x₀.1
        (iff_of_false (hne i x) (hne i x₀))
  · by_cases hk' : k ∈ range f
    · obtain ⟨j, rfl⟩ := hk'
      obtain ⟨i, hi⟩ := D.exists_root_eq j x hk t ht
      exact ⟨p.succAbove i, (hroot_succAbove i x).trans hi⟩
    · obtain ⟨a, ha, hF⟩ := hcoord k hk'
      rw [hF, isRoot_lazardEval_C_mul_lastCoordinate ha] at ht
      exact ⟨p, (hroot_p x).trans ht.symm⟩
  · rcases Fin.eq_self_or_eq_succAbove p l with hl | ⟨i, rfl⟩
    · obtain ⟨a, ha, hF⟩ := hcoord k₀ hk₀
      refine ⟨k₀, ?_⟩
      simp only [hl, hroot_p, Q, hF, rootMultiplicity_lazardEval_C_mul_lastCoordinate ha,
        ite_true, Nat.one_pos]
    · obtain ⟨j, hj⟩ := D.exists_multiplicity_pos i
      refine ⟨f j, ?_⟩
      rw [hroot_succAbove]
      exact (D.rootMultiplicity_root j i x₀).symm ▸ hj

/-- **Adjoining the distinguished coordinate.** Let `D` be a Lazard delineation of the members
`F ∘ f` of a family over a preconnected base, and suppose every member of `F` outside the range
of `f` is a nonzero constant multiple of the last coordinate polynomial. If, for each member of
`F ∘ f`, whether `0` is a root of its Lazard evaluation does not depend on the base point, then
the whole family `F` has a Lazard delineation over the base.

Its root functions are those of `D`, together with the zero section when coordinate members
occur and `0` is not already a root function of `D`. -/
theorem nonempty_lazardDelineation_of_comp (D : LazardDelineation (F ∘ f) S)
    (hS : IsPreconnected S)
    (hcoord : ∀ k, k ∉ range f → ∃ a ≠ 0, F k = MvPolynomial.C a * X (Fin.last n))
    (hzero : ∀ j (x y : S),
      ((optionEquivRight ℝ (Fin n) (rename finSuccEquivLast (F (f j)))).lazardEval
        (Polynomial.C ∘ x.1)).IsRoot 0 →
      ((optionEquivRight ℝ (Fin n) (rename finSuccEquivLast (F (f j)))).lazardEval
        (Polynomial.C ∘ y.1)).IsRoot 0) :
    Nonempty (LazardDelineation F S) := by
  have : PreconnectedSpace S := isPreconnected_iff_preconnectedSpace.1 hS
  -- Whether `0` is a value of a root function of `D` does not depend on the base point.
  have h0 (x y : S) : (∃ i, D.root i x = 0) → ∃ i, D.root i y = 0 := by
    rintro ⟨i, hi⟩
    obtain ⟨j, hj⟩ := D.exists_multiplicity_pos i
    rw [← D.rootMultiplicity_root j i x, hi] at hj
    obtain ⟨hne, hroot⟩ := Polynomial.rootMultiplicity_pos'.1 hj
    refine D.exists_root_eq j y (fun hF ↦ hne ?_) 0 (hzero j x y hroot)
    simp only [Function.comp_apply] at hF
    simp [hF]
  obtain hR | ⟨p, hp⟩ := exists_forall_eq_zero_or_exists_forall_mem_sectorSet D.continuous_root
    D.strictMono_root h0 ⟨D.nonempty.some, D.nonempty.some_mem⟩
  · exact nonempty_lazardDelineation_of_comp_of_forall_eq_zero D hcoord fun _ _ ↦ hR
  by_cases hc : ∃ k₀, k₀ ∉ range f
  · obtain ⟨k₀, hk₀⟩ := hc
    exact nonempty_lazardDelineation_of_comp_of_mem_sectorSet D hcoord hp hk₀
  · exact nonempty_lazardDelineation_of_comp_of_forall_eq_zero D hcoord fun k hk ↦
      absurd ⟨k, hk⟩ hc

/-- **The root `0` from the constant coefficient.** Let `F k` be the polynomial in `n + 1`
variables corresponding to a polynomial `f` in the distinguished variable. Over the base of a
Lazard delineation of `F`, if the formal constant coefficient of `f` has constant Lazard
valuation, then `0` is a root of the Lazard evaluations of `F k` over every base point or over
none. -/
theorem LazardDelineation.isRoot_zero_of_lazardValuation_coeff_zero_eq
    (D : LazardDelineation F S) {k : ι} {f : Polynomial (MvPolynomial (Fin n) ℝ)}
    (hf : F k = rename finSuccEquivLast.symm ((optionEquivLeft ℝ (Fin n)).symm f))
    (hval : ∀ x ∈ S, ∀ y ∈ S, (f.coeff 0).lazardValuation x = (f.coeff 0).lazardValuation y)
    (x y : S)
    (hx : ((optionEquivRight ℝ (Fin n) (rename finSuccEquivLast (F k))).lazardEval
      (Polynomial.C ∘ x.1)).IsRoot 0) :
    ((optionEquivRight ℝ (Fin n) (rename finSuccEquivLast (F k))).lazardEval
      (Polynomial.C ∘ y.1)).IsRoot 0 := by
  -- Putting the distinguished variable last and moving it back into the coefficients is the
  -- coefficient swap of the two `Option` equivalences.
  have hswap : optionEquivRight ℝ (Fin n) (rename finSuccEquivLast (F k)) =
      ((optionEquivLeft ℝ (Fin n)).symm.trans (optionEquivRight ℝ (Fin n))) f := by
    rw [hf, rename_rename, Equiv.self_comp_symm, rename_id_apply, AlgEquiv.trans_apply]
  have hv := hval x x.2 y y.2
  rw [← map_constantCoeff_optionEquivRight_optionEquivLeft_symm] at hv
  have hexp := (D.lazardExponent_eq k x).trans (D.lazardExponent_eq k y).symm
  rw [hswap] at hx hexp ⊢
  by_contra hy
  rw [← lazardValuation_map_constantCoeff_eq_iff] at hy
  exact (lazardValuation_map_constantCoeff_eq_iff _ _).1 (by rw [hv, hy, hexp]) hx

end Adjoin

/-- **Multiplying by the distinguished coordinate.** Let `q` be a nonzero polynomial in the
distinguished variable whose formal constant coefficient has constant Lazard valuation on a
preconnected base. A Lazard delineation of `q` over the base gives one of `X * q`: the zero
section is adjoined unless `0` is already a root function. -/
theorem nonempty_lazardDelineation_X_mul {q : Polynomial (MvPolynomial (Fin n) ℝ)} (hq : q ≠ 0)
    (D : LazardDelineation
      (fun _ : Unit ↦ rename finSuccEquivLast.symm ((optionEquivLeft ℝ (Fin n)).symm q)) S)
    (hS : IsPreconnected S)
    (hval : ∀ x ∈ S, ∀ y ∈ S, (q.coeff 0).lazardValuation x = (q.coeff 0).lazardValuation y) :
    Nonempty (LazardDelineation (fun _ : Unit ↦
      rename finSuccEquivLast.symm ((optionEquivLeft ℝ (Fin n)).symm (Polynomial.X * q))) S) := by
  classical
  -- Adjoin the coordinate to the delineation of `q`, then pass to the product.
  let G : Option Unit → MvPolynomial (Fin (n + 1)) ℝ := fun k ↦
    k.elim (X (Fin.last n)) fun _ ↦
      rename finSuccEquivLast.symm ((optionEquivLeft ℝ (Fin n)).symm q)
  obtain ⟨E⟩ := nonempty_lazardDelineation_of_comp (F := G) (f := some) D hS
    (fun k hk ↦ ⟨1, one_ne_zero, by
      obtain rfl : k = none := Option.eq_none_iff_forall_ne_some.2 fun j hj ↦ hk ⟨j, hj.symm⟩
      simp [G]⟩)
    (fun j ↦ D.isRoot_zero_of_lazardValuation_coeff_zero_eq (k := j) rfl hval)
  have hG : ∏ k, G k =
      rename finSuccEquivLast.symm ((optionEquivLeft ℝ (Fin n)).symm (Polynomial.X * q)) := by
    simp [G, Fintype.prod_option]
  rw [← hG]
  refine ⟨E.prod ?_⟩
  rw [hG]
  exact (map_ne_zero_iff _ (rename_injective _ finSuccEquivLast.symm.injective)).2
    (EmbeddingLike.map_ne_zero_iff.2 (mul_ne_zero Polynomial.X_ne_zero hq))

end TauCeti
