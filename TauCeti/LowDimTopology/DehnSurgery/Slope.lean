/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Data.Rat.Lemmas
public import Mathlib.RingTheory.Int.Basic
public import Mathlib.Topology.Compactification.OnePoint.Basic

/-!
# Slopes on a framed boundary torus

A *slope* on the boundary torus `T` of a knot or link complement is the datum needed to specify a
Dehn filling: the isotopy class of an unoriented essential simple closed curve on `T`, equivalently
a primitive class in `H₁(T; ℤ)` taken modulo sign (Rolfsen, *Knots and Links*, Chapter 9). Once `T`
is *framed* by an ordered basis `(μ, λ)` of meridian and longitude, `H₁(T; ℤ)` is identified with
`ℤ × ℤ` (first coordinate the `μ`-coefficient, second the `λ`-coefficient) and every slope acquires
a value `p / q ∈ ℚ ∪ {∞}`, the ratio of its coordinates; the filling then sends the solid torus's
meridian to `p · μ + q · λ`.

This file builds the slope arithmetic for the framed model, the first piece of the
geometric-topology roadmap's Dehn-surgery layer (`TauCetiRoadmap/GeometricTopology/README.md`,
layer 5, "Dehn surgery": "Slopes, with the primitive pinned … give a `FramedBoundaryTorus` an
ordered basis `(μ, λ)` … and the resulting bijection `Slope T ≃ ℚ ∪ {∞}`"). Concretely, `H₁(T; ℤ)`
is modelled by `ℤ × ℤ` with the
framing basis already chosen, so `TauCeti.Slope` is the basis-free set (primitive classes modulo
sign) and `TauCeti.slopeEquiv` is the basis-dependent parametrisation. The identification with an
abstract rank-two homology group, and the boundary torus of a genuine link complement, are later
layer-5 work that consumes this arithmetic; that is why the layer asks for the two objects — the
sign-quotient `Slope` and the `ℚ ∪ {∞}` parametrisation — to be kept distinct, exactly as here.

## Main definitions

* `TauCeti.IsPrimitive v`: the class `v : ℤ × ℤ` is primitive, i.e. its coordinates are coprime.
* `TauCeti.slopeValue v`: the value `p / q ∈ ℚ ∪ {∞}` of a class `v = (p, q)`, being `∞` when
  `q = 0`.
* `TauCeti.Slope`: primitive classes modulo the sign action `v ↦ -v`.
* `TauCeti.Slope.meridian` / `TauCeti.Slope.longitude`: the slopes `(1, 0)` and `(0, 1)`.
* `TauCeti.Slope.value`: the well-defined `ℚ ∪ {∞}` value of a slope.
* `TauCeti.slopeEquiv`: the bijection `Slope ≃ ℚ ∪ {∞}`.

## Main results

* `TauCeti.Slope.value_meridian` / `TauCeti.Slope.value_longitude`: the meridian is `∞` and the
  longitude is `0`, fixing the meridian-longitude convention.
* `TauCeti.slopeEquiv`: primitive classes modulo sign biject with `ℚ ∪ {∞}`, a reduced fraction
  `p / q` corresponding to the primitive pair `(p, q)`.

`ℚ ∪ {∞}` is Mathlib's one-point extension `OnePoint ℚ` from
`Mathlib/Topology/Compactification/OnePoint/Basic.lean`; the reduced-fraction bookkeeping reuses
Mathlib's `Rat` normalisation (`Rat.num_div_den`, `Rat.num_div_eq_of_coprime`,
`Rat.den_div_eq_of_coprime`).
-/

public section

open scoped OnePoint

namespace TauCeti

/-- A homology class `v : ℤ × ℤ` on a framed boundary torus is **primitive** when its
meridian- and longitude-coordinates are coprime; equivalently, it is not a proper multiple of
another class, so it is represented by an unoriented essential simple closed curve. -/
def IsPrimitive (v : ℤ × ℤ) : Prop := IsCoprime v.1 v.2

theorem isPrimitive_iff_natCoprime {v : ℤ × ℤ} :
    IsPrimitive v ↔ Nat.Coprime v.1.natAbs v.2.natAbs :=
  Int.isCoprime_iff_nat_coprime

theorem IsPrimitive.neg {v : ℤ × ℤ} (h : IsPrimitive v) : IsPrimitive (-v) := by
  simpa only [IsPrimitive, Prod.fst_neg, Prod.snd_neg] using h.neg_left.neg_right

theorem isPrimitive_meridian : IsPrimitive (1, 0) := isCoprime_one_left

theorem isPrimitive_longitude : IsPrimitive (0, 1) := isCoprime_one_right

/-- The reduced form `(r.num, r.den)` of a rational is a primitive class. -/
theorem isPrimitive_num_den (r : ℚ) : IsPrimitive (r.num, (r.den : ℤ)) := by
  rw [isPrimitive_iff_natCoprime, Int.natAbs_natCast]
  exact r.reduced

/-- A primitive class with vanishing longitude-coordinate has meridian-coordinate `±1`. -/
theorem IsPrimitive.fst_eq_of_snd_eq_zero {v : ℤ × ℤ} (h : IsPrimitive v) (hq : v.2 = 0) :
    v.1 = 1 ∨ v.1 = -1 := by
  rw [IsPrimitive, hq, isCoprime_zero_right, Int.isUnit_iff] at h
  exact h

/-- The value `p / q ∈ ℚ ∪ {∞}` of a class `v = (p, q)`, taken to be `∞` when `q = 0`. This is the
ratio of the meridian- and longitude-coordinates in a framing. -/
def slopeValue (v : ℤ × ℤ) : OnePoint ℚ :=
  if v.2 = 0 then ∞ else ((v.1 : ℚ) / (v.2 : ℚ) : ℚ)

@[simp]
theorem slopeValue_of_snd_eq_zero {v : ℤ × ℤ} (hq : v.2 = 0) : slopeValue v = ∞ := if_pos hq

theorem slopeValue_of_snd_ne_zero {v : ℤ × ℤ} (hq : v.2 ≠ 0) :
    slopeValue v = ((v.1 : ℚ) / (v.2 : ℚ) : ℚ) := if_neg hq

/-- The value of a class is unchanged by the sign action `v ↦ -v`. -/
theorem slopeValue_neg (v : ℤ × ℤ) : slopeValue (-v) = slopeValue v := by
  simp only [slopeValue, Prod.fst_neg, Prod.snd_neg, neg_eq_zero]
  split_ifs with h
  · rfl
  · congr 1
    push_cast
    rw [neg_div_neg_eq]

/-- Two primitive classes represent the same slope when they agree up to sign. This is an
equivalence relation on primitive classes. -/
def slopeSetoid : Setoid {v : ℤ × ℤ // IsPrimitive v} where
  r a b := a.1 = b.1 ∨ a.1 = -b.1
  iseqv :=
    { refl := fun _ => Or.inl rfl
      symm := fun {a b} h => h.imp Eq.symm fun hab => by rw [hab, neg_neg]
      trans := fun {a b c} hab hbc => by
        rcases hab with hab | hab <;> rcases hbc with hbc | hbc
        · exact Or.inl (hab.trans hbc)
        · exact Or.inr (hab.trans hbc)
        · exact Or.inr (by rw [hab, hbc])
        · exact Or.inl (by rw [hab, hbc, neg_neg]) }

/-- A **slope** on a framed boundary torus: a primitive homology class in `ℤ × ℤ` taken modulo the
sign action, i.e. an unoriented essential simple closed curve up to isotopy. -/
@[expose] def Slope : Type := Quotient slopeSetoid

namespace Slope

/-- The slope represented by a primitive class `v : ℤ × ℤ`. -/
@[expose] def mk (v : ℤ × ℤ) (h : IsPrimitive v) : Slope := Quotient.mk slopeSetoid ⟨v, h⟩

theorem mk_eq_mk {v w : ℤ × ℤ} (hv : IsPrimitive v) (hw : IsPrimitive w)
    (h : v = w ∨ v = -w) : mk v hv = mk w hw :=
  Quotient.sound h

@[elab_as_elim]
theorem inductionOn {C : Slope → Prop} (s : Slope)
    (h : ∀ (v : ℤ × ℤ) (hv : IsPrimitive v), C (mk v hv)) : C s :=
  Quotient.inductionOn s fun v => h v.1 v.2

/-- The meridian slope `μ = (1, 0)`. -/
def meridian : Slope := mk (1, 0) isPrimitive_meridian

/-- The longitude slope `λ = (0, 1)`. -/
def longitude : Slope := mk (0, 1) isPrimitive_longitude

/-- The well-defined value `p / q ∈ ℚ ∪ {∞}` of a slope. -/
@[expose] def value : Slope → OnePoint ℚ :=
  Quotient.lift (fun v => slopeValue v.1) fun _ _ h => by
    rcases h with h | h
    · rw [h]
    · rw [h, slopeValue_neg]

@[simp]
theorem value_mk (v : ℤ × ℤ) (h : IsPrimitive v) : value (mk v h) = slopeValue v := rfl

@[simp]
theorem value_meridian : value meridian = ∞ := by
  rw [meridian, value_mk, slopeValue_of_snd_eq_zero rfl]

@[simp]
theorem value_longitude : value longitude = (0 : ℚ) := by
  rw [longitude, value_mk, slopeValue_of_snd_ne_zero one_ne_zero]
  norm_num

end Slope

/-- The primitive class attached to a value in `ℚ ∪ {∞}`: the meridian for `∞`, and the reduced
fraction `(r.num, r.den)` for a rational `r`. -/
@[expose] def slopeOfValue : OnePoint ℚ → Slope
  | ∞ => Slope.meridian
  | (r : ℚ) => Slope.mk (r.num, (r.den : ℤ)) (isPrimitive_num_den r)

@[simp]
theorem slopeOfValue_infty : slopeOfValue ∞ = Slope.meridian := rfl

@[simp]
theorem slopeOfValue_coe (r : ℚ) :
    slopeOfValue (r : OnePoint ℚ) = Slope.mk (r.num, (r.den : ℤ)) (isPrimitive_num_den r) := rfl

theorem slopeOfValue_value (s : Slope) : slopeOfValue s.value = s := by
  induction s using Slope.inductionOn with
  | h v hv =>
    obtain ⟨p, q⟩ := v
    by_cases hq : q = 0
    · subst hq
      rw [Slope.value_mk, slopeValue_of_snd_eq_zero rfl, slopeOfValue_infty, Slope.meridian]
      rcases hv.fst_eq_of_snd_eq_zero rfl with hp | hp <;> subst hp
      · rfl
      · exact Slope.mk_eq_mk _ _ (Or.inr rfl)
    · rw [Slope.value_mk, slopeValue_of_snd_ne_zero hq, slopeOfValue_coe]
      have hcop : Nat.Coprime p.natAbs q.natAbs := isPrimitive_iff_natCoprime.mp hv
      rcases lt_or_gt_of_ne hq with hqneg | hqpos
      · -- `q < 0`: the reduced form of `p / q` is `(-p, -q)`, agreeing with `(p, q)` up to sign.
        have hpos : (0 : ℤ) < -q := by omega
        have hcop' : Nat.Coprime (-p).natAbs (-q).natAbs := by
          rwa [Int.natAbs_neg, Int.natAbs_neg]
        have hval : ((p : ℚ) / (q : ℚ)) = ((-p : ℤ) : ℚ) / ((-q : ℤ) : ℚ) := by
          push_cast; rw [neg_div_neg_eq]
        rw [hval]
        refine Slope.mk_eq_mk _ _ (Or.inr ?_)
        rw [Rat.num_div_eq_of_coprime hpos hcop', Rat.den_div_eq_of_coprime hpos hcop']
        simp
      · -- `q > 0`: the reduced form of `p / q` is exactly `(p, q)`.
        refine Slope.mk_eq_mk _ _ (Or.inl ?_)
        rw [Rat.num_div_eq_of_coprime hqpos hcop, Rat.den_div_eq_of_coprime hqpos hcop]

theorem value_slopeOfValue (x : OnePoint ℚ) : (slopeOfValue x).value = x := by
  induction x with
  | infty => rw [slopeOfValue_infty, Slope.value_meridian]
  | coe r =>
    have hd : ((r.den : ℤ)) ≠ 0 := Int.natCast_ne_zero.mpr r.den_ne_zero
    rw [slopeOfValue_coe, Slope.value_mk, slopeValue_of_snd_ne_zero hd,
      Int.cast_natCast, Rat.num_div_den]

/-- **The framed slope parametrisation.** On a framed boundary torus, primitive homology classes
modulo sign biject with `ℚ ∪ {∞}`: a reduced fraction `p / q` corresponds to the primitive class
`(p, q)`, with `∞` the meridian. -/
@[expose] def slopeEquiv : Slope ≃ OnePoint ℚ where
  toFun := Slope.value
  invFun := slopeOfValue
  left_inv := slopeOfValue_value
  right_inv := value_slopeOfValue

@[simp]
theorem slopeEquiv_apply (s : Slope) : slopeEquiv s = s.value := rfl

@[simp]
theorem slopeEquiv_symm_apply (x : OnePoint ℚ) : slopeEquiv.symm x = slopeOfValue x := rfl

end TauCeti
