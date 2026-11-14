/-
Copyright (c) 2026 Tau Ceti. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Ring.Subring.Basic
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Algebra.Ring.Action.ConjAct
import Mathlib.Tactic.NoncommRing

/-!
# Unit constant terms in an embedded skew polynomial ring

Let `C` be a subring of a ring and write `P = Subring.closure (insert z C)`.
If coefficients can be moved past `z` to the right, the elements `c * (1 + z * w)`,
with `c` a unit of `C` and `w ∈ P`, form a multiplicative set. Ring maps preserving
`C` and sending `z` into `z * P` preserve this set. In particular, this applies to
conjugations that preserve the coefficient ring and the positive direction.
Every such element has a right inverse modulo `z ^ n * P`, for every natural `n`.

These statements concern the generated subring inside the ambient ring: neither
algebraic independence nor the existence of a division ring is needed. They supply
the finite denominator corrections used when patching skew Laurent charts.
The normalizing-variable argument is the unit-constant-term step of
Berenstein–Zelevinsky, *Quantum cluster algebras*, §5.
-/

public section

namespace Subring

variable {R S : Type*} [Ring R] [Ring S]

/-- Moving elements past `z` extends from generators to the generated subring.
Only the indicated direction of normalization is needed. -/
theorem exists_mul_eq_mul_of_mem_closure {s : Set R} {z a : R}
    (hz : ∀ a ∈ s, ∃ b ∈ closure s, a * z = z * b) (ha : a ∈ closure s) :
    ∃ b ∈ closure s, a * z = z * b := by
  induction ha using closure_induction with
  | mem a ha => exact hz a ha
  | zero => exact ⟨0, zero_mem _, by simp⟩
  | one => exact ⟨1, one_mem _, by simp⟩
  | add a b _ _ ha hb =>
    obtain ⟨c, hc, he⟩ := ha
    obtain ⟨d, hd, hf⟩ := hb
    exact ⟨c + d, (closure _).add_mem hc hd, by simp [add_mul, mul_add, he, hf]⟩
  | neg a _ ha =>
    obtain ⟨b, hb, he⟩ := ha
    exact ⟨-b, (closure _).neg_mem hb, by simp [he]⟩
  | mul a b _ _ ha hb =>
    obtain ⟨c, hc, he⟩ := ha
    obtain ⟨d, hd, hf⟩ := hb
    refine ⟨c * d, (closure _).mul_mem hc hd, ?_⟩
    calc
      a * b * z = a * (b * z) := mul_assoc _ _ _
      _ = a * (z * d) := by rw [hf]
      _ = (a * z) * d := (mul_assoc _ _ _).symm
      _ = z * (c * d) := by rw [he, mul_assoc]

/-- Moving coefficients past `z` extends from a coefficient set to the subring it
generates together with `z`. -/
theorem exists_mul_eq_mul_of_mem_closure_insert {s : Set R} {z a : R}
    (hz : ∀ a ∈ s, ∃ b ∈ s, a * z = z * b)
    (ha : a ∈ closure (insert z s)) :
    ∃ b ∈ closure (insert z s), a * z = z * b := by
  refine exists_mul_eq_mul_of_mem_closure ?_ ha
  rintro a (rfl | ha)
  · exact ⟨a, subset_closure (Set.mem_insert _ _), rfl⟩
  · obtain ⟨b, hb, h⟩ := hz a ha
    exact ⟨b, subset_closure (Set.mem_insert_of_mem _ hb), h⟩

end Subring

namespace SubmonoidClass

variable {M S : Type*} [Monoid M] [SetLike S M] [SubmonoidClass S M]

/-- Extracting one factor of `z` at a time gives `z ^ n` times a cofactor in `P`. -/
theorem exists_mul_pow_eq_pow_mul {P : S} {z w : M}
    (hz : ∀ a ∈ P, ∃ b ∈ P, a * z = z * b) (hw : w ∈ P) (n : ℕ) :
    ∃ v ∈ P, (z * w) ^ n = z ^ n * v := by
  induction n with
  | zero => exact ⟨1, one_mem _, by simp⟩
  | succ n ih =>
    obtain ⟨v, hv, he⟩ := ih
    obtain ⟨b, hb, hf⟩ := hz v hv
    refine ⟨b * w, mul_mem hb hw, ?_⟩
    calc
      (z * w) ^ (n + 1) = z ^ n * (v * z) * w := by rw [pow_succ, he]; simp [mul_assoc]
      _ = z ^ (n + 1) * (b * w) := by rw [hf, pow_succ]; simp [mul_assoc]

end SubmonoidClass

namespace Subring

variable {R S : Type*} [Ring R] [Ring S]

/-- A power of an element in `z * C[z]` lies in `z ^ n * C[z]`, even when
`z` does not commute with the coefficients. -/
theorem exists_mul_pow_eq_pow_mul_of_mem_closure_insert {s : Set R} {z w : R}
    (hz : ∀ a ∈ s, ∃ b ∈ s, a * z = z * b)
    (hw : w ∈ closure (insert z s)) (n : ℕ) :
    ∃ v ∈ closure (insert z s), (z * w) ^ n = z ^ n * v :=
  SubmonoidClass.exists_mul_pow_eq_pow_mul
    (fun _ ha ↦ exists_mul_eq_mul_of_mem_closure_insert hz ha) hw n

private theorem conj_mul_one_add_mul_eq_one_add_mul (C : Subring R) {z w : R}
    (hz : ∀ a ∈ C, ∃ b ∈ C, a * z = z * b)
    (hw : w ∈ closure (insert z (C : Set R))) (c : Cˣ) :
    ∃ t ∈ closure (insert z (C : Set R)),
      (c : C) * (1 + z * w) * ((c⁻¹ : Cˣ) : C) = 1 + z * t := by
  obtain ⟨b, hb, he⟩ := hz (c : C) (c : C).property
  let P := closure (insert z (C : Set R))
  have hcP {x : R} (hx : x ∈ C) : x ∈ P := subset_closure (Set.mem_insert_of_mem _ hx)
  let t : R := b * w * ((c⁻¹ : Cˣ) : C)
  refine ⟨t, P.mul_mem (P.mul_mem (hcP hb) hw) (hcP ((c⁻¹ : Cˣ) : C).property), ?_⟩
  simp only [mul_add, mul_one, add_mul, t]
  rw [← mul_assoc (((c : Cˣ) : C) : R) z w, he]
  simp only [← mul_assoc, ← C.coe_mul, Units.mul_inv, C.coe_one]

private theorem mul_unitConstantTerms (C : Subring R) {z : R}
    (hz : ∀ a ∈ C, ∃ b ∈ C, a * z = z * b)
    {a b : R}
    (ha : ∃ c : Cˣ, ∃ w ∈ closure (insert z (C : Set R)),
      a = (c : C) * (1 + z * w))
    (hb : ∃ c : Cˣ, ∃ w ∈ closure (insert z (C : Set R)),
      b = (c : C) * (1 + z * w)) :
    ∃ c : Cˣ, ∃ w ∈ closure (insert z (C : Set R)),
      a * b = (c : C) * (1 + z * w) := by
  obtain ⟨c, w, hw, rfl⟩ := ha
  obtain ⟨d, v, hv, rfl⟩ := hb
  obtain ⟨t, ht, hd⟩ := conj_mul_one_add_mul_eq_one_add_mul C hz hw d⁻¹
  simp only [inv_inv] at hd
  let P := closure (insert z (C : Set R))
  refine ⟨c * d, t + v + t * z * v,
    P.add_mem (P.add_mem ht hv)
      (P.mul_mem (P.mul_mem ht (subset_closure (Set.mem_insert _ _))) hv), ?_⟩
  calc
    (c : C) * (1 + z * w) * ((d : C) * (1 + z * v)) =
        ((c * d : Cˣ) : C) *
          (((d⁻¹ : Cˣ) : C) * (1 + z * w) * (d : C)) * (1 + z * v) := by
      simp only [← mul_assoc, ← C.coe_mul, Units.val_mul, Units.mul_inv_cancel_right]
    _ = ((c * d : Cˣ) : C) * (1 + z * (t + v + t * z * v)) := by
      rw [hd]
      noncomm_ring

/-- Elements with a unit constant term in the subring generated by `C` and `z`.
The normalization hypothesis expresses `C * z ⊆ z * C`; a variable normalizing `C`
satisfies it. When expansions in `z` have unique coefficients, the displayed unit is
the constant coefficient; the definition itself requires no independence hypothesis. -/
def unitConstantTerms (C : Subring R) (z : R)
    (hz : ∀ a ∈ C, ∃ b ∈ C, a * z = z * b) : Submonoid R where
  carrier := {a | ∃ c : Cˣ, ∃ w ∈ closure (insert z (C : Set R)),
    a = (c : C) * (1 + z * w)}
  one_mem' := ⟨1, 0, zero_mem _, by simp⟩
  mul_mem' := mul_unitConstantTerms C hz

/-- Membership records the unit coefficient and the finite positive correction. -/
theorem mem_unitConstantTerms (C : Subring R) {z a : R}
    {hz : ∀ a ∈ C, ∃ b ∈ C, a * z = z * b} :
    a ∈ C.unitConstantTerms z hz ↔
      ∃ c : Cˣ, ∃ w ∈ closure (insert z (C : Set R)),
        a = (c : C) * (1 + z * w) := Iff.rfl

/-- A unit of the coefficient ring has a unit constant term. -/
@[simp]
theorem coe_unit_mem_unitConstantTerms (C : Subring R) (z : R)
    (hz : ∀ a ∈ C, ∃ b ∈ C, a * z = z * b) (c : Cˣ) :
    ((c : C) : R) ∈ C.unitConstantTerms z hz :=
  ⟨c, 0, zero_mem _, by simp⟩

/-- The positive correction `1 + z * w` has a unit constant term. -/
theorem one_add_mul_mem_unitConstantTerms (C : Subring R) {z w : R}
    (hz : ∀ a ∈ C, ∃ b ∈ C, a * z = z * b)
    (hw : w ∈ closure (insert z (C : Set R))) :
    1 + z * w ∈ C.unitConstantTerms z hz :=
  ⟨1, w, hw, by simp⟩

/-- The linear skew polynomial `1 + z` has a unit constant term. -/
@[simp]
theorem one_add_mem_unitConstantTerms (C : Subring R) (z : R)
    (hz : ∀ a ∈ C, ∃ b ∈ C, a * z = z * b) :
    1 + z ∈ C.unitConstantTerms z hz := by
  simpa using C.one_add_mul_mem_unitConstantTerms (w := 1) hz
    ((closure (insert z (C : Set R))).one_mem)

/-- Unit-constant-term elements belong to the generated skew polynomial subring. -/
theorem unitConstantTerms_le_closure (C : Subring R) (z : R)
    (hz : ∀ a ∈ C, ∃ b ∈ C, a * z = z * b) :
    C.unitConstantTerms z hz ≤ (closure (insert z (C : Set R))).toSubmonoid := by
  rintro a ⟨c, w, hw, rfl⟩
  exact (closure _).mul_mem (subset_closure (Set.mem_insert_of_mem _ (c : C).property))
    ((closure _).add_mem (one_mem _)
      ((closure _).mul_mem (subset_closure (Set.mem_insert _ _)) hw))

/-- Maps preserving coefficients and sending `z` into `z' * P'` preserve unit
constant terms, where `P'` is generated by `C'` and `z'`. -/
theorem map_unitConstantTerms_le {F : Type*} [FunLike F R S] [RingHomClass F R S]
    (C : Subring R) (C' : Subring S) (f : F) {z : R} {z' : S}
    (hz : ∀ a ∈ C, ∃ b ∈ C, a * z = z * b)
    (hz' : ∀ a ∈ C', ∃ b ∈ C', a * z' = z' * b)
    (hf : ∀ a ∈ C, f a ∈ C')
    (h : ∃ b ∈ closure (insert z' (C' : Set S)), f z = z' * b) :
    (C.unitConstantTerms z hz).map (f : R →+* S) ≤ C'.unitConstantTerms z' hz' := by
  obtain ⟨b, hb, he⟩ := h
  let f' : R →+* S := f
  let P' := closure (insert z' (C' : Set S))
  have hP : closure (insert z (C : Set R)) ≤ P'.comap f' := by
    rw [closure_le]
    rintro a (rfl | ha)
    · exact mem_comap.mpr (he.symm ▸ P'.mul_mem
        (subset_closure (Set.mem_insert _ _)) hb)
    · exact mem_comap.mpr (subset_closure (Set.mem_insert_of_mem _ (hf a ha)))
  rintro _ ⟨a, ⟨c, w, hw, rfl⟩, rfl⟩
  refine ⟨Units.map (f'.restrict C C' hf) c, b * f w,
    P'.mul_mem hb (mem_comap.mp (hP hw)), ?_⟩
  have hc : (((Units.map (f'.restrict C C' hf) c : C'ˣ) : C') : S) = f (c : C) := by
    rw [Units.coe_map]
    exact RingHom.coe_restrict_apply f' C C' hf c
  simp only [RingHom.coe_coe, map_mul, map_add, map_one, he, hc, mul_assoc]

/-- Conjugations preserving the coefficient subring and sending `z` into `z * P`,
where `P` is generated by `C` and `z`, preserve the multiplicative set of unit constant terms.
One-sided preservation suffices. -/
theorem conj_mem_unitConstantTerms (C : Subring R) {z a : R}
    (hz : ∀ a ∈ C, ∃ b ∈ C, a * z = z * b) (g : Rˣ)
    (hg : ∀ c ∈ C, (g : R) * c * (↑g⁻¹ : R) ∈ C)
    (hgz : ∃ b ∈ closure (insert z (C : Set R)), (g : R) * z * (↑g⁻¹ : R) = z * b)
    (ha : a ∈ C.unitConstantTerms z hz) :
    (g : R) * a * (↑g⁻¹ : R) ∈ C.unitConstantTerms z hz := by
  let f := MulSemiringAction.toRingHom (ConjAct Rˣ) R (ConjAct.toConjAct g)
  have hf (x : R) : f x = (g : R) * x * (↑g⁻¹ : R) := by
    simp [f, ConjAct.units_smul_def]
  have hm := C.map_unitConstantTerms_le C f hz hz (by simpa only [hf] using hg)
    (by simpa only [hf] using hgz)
  exact hm (Submonoid.mem_map.mpr ⟨a, ha, hf a⟩)

/-- Every unit-constant-term element has a right inverse modulo `z ^ n * C[z]`.
The inverse and its error coefficient both belong to the generated subring. -/
theorem exists_mul_eq_one_add_pow_mul_of_mem_unitConstantTerms (C : Subring R)
    {z a : R} (hz : ∀ a ∈ C, ∃ b ∈ C, a * z = z * b)
    (ha : a ∈ C.unitConstantTerms z hz) (n : ℕ) :
    ∃ q ∈ closure (insert z (C : Set R)),
      ∃ r ∈ closure (insert z (C : Set R)), a * q = 1 + z ^ n * r := by
  classical
  obtain ⟨c, w, hw, rfl⟩ := ha
  obtain ⟨t, ht, hct⟩ := conj_mul_one_add_mul_eq_one_add_mul C hz hw c
  let P := closure (insert z (C : Set R))
  have hcP {x : R} (hx : x ∈ C) : x ∈ P := subset_closure (Set.mem_insert_of_mem _ hx)
  obtain ⟨v, hv, hpow⟩ :=
    exists_mul_pow_eq_pow_mul_of_mem_closure_insert hz (P.neg_mem ht) n
  refine ⟨((c⁻¹ : Cˣ) : C) * ∑ i ∈ Finset.range n, (-(z * t)) ^ i,
    P.mul_mem (hcP ((c⁻¹ : Cˣ) : C).property)
      (P.sum_mem fun i _ ↦ P.pow_mem (P.neg_mem
        (P.mul_mem (subset_closure (Set.mem_insert _ _)) ht)) i),
    -v, P.neg_mem hv, ?_⟩
  calc
    (c : C) * (1 + z * w) *
        (((c⁻¹ : Cˣ) : C) * ∑ i ∈ Finset.range n, (-(z * t)) ^ i) =
        (1 + z * t) * ∑ i ∈ Finset.range n, (-(z * t)) ^ i := by
      rw [← mul_assoc, hct]
    _ = 1 - (-(z * t)) ^ n := by
      simpa using mul_neg_geom_sum (-(z * t)) n
    _ = 1 + z ^ n * -v := by rw [← mul_neg, hpow, sub_eq_add_neg, mul_neg]

end Subring
