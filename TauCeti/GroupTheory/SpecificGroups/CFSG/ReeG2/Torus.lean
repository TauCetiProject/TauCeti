/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.SpecificGroups.CFSG.ReeG2.Basic

/-!
# The split torus in the Ree G₂ fixed-point group

For `q = 3^(2m+1)`, the Steinberg map sends weight-torus parameters `(x,y)` to
`(y^(3^m), x^(3^(m+1)))`. Its fixed points in the ambient weight torus are therefore
exactly `(t, t^(3^(m+1)))` with `t` a nonzero element of the fixed field.

We embed the units of that field into the actual Steinberg fixed-point group. The embedding
exhausts its intersection with the ambient weight torus, and its image has order `q - 1`.
This gives the torus factor for constructing the Borel subgroup and the rank-one Bruhat
cells of the Ree group. No comparison with a different group realization is used.

## References

* R. W. Carter, *Simple Groups of Lie Type*, Wiley (1972), §12.4.
* R. Steinberg, *Endomorphisms of linear algebraic groups*, Memoirs AMS **80** (1968), §11.
-/

public section

noncomputable section

namespace TauCeti.ReeG2LieIndex

open G2ShortRoot.PrimeField

variable (d : ReeG2LieIndex)

private theorem halfFrobenius_pow_odd_weightTorusPoints (n : ℕ) (x y : d.1.Closureˣ) :
    d.halfFrobenius^[2 * n + 1] (weightTorusPoints d.1.Closure ![x, y]) =
      weightTorusPoints d.1.Closure ![y ^ (3 ^ n), x ^ (3 ^ (n + 1))] := by
  induction n with
  | zero => simp [halfFrobenius_def, specialIsogeny_weightTorusPoints]
  | succ n ih =>
    have hn : 2 * (n + 1) + 1 = (2 * n + 1) + 1 + 1 := by omega
    rw [hn, Function.iterate_succ_apply', Function.iterate_succ_apply', ih]
    simp only [halfFrobenius_def, specialIsogeny_weightTorusPoints,
      Matrix.cons_val_zero, Matrix.cons_val_one]
    apply congrArg (weightTorusPoints d.1.Closure)
    simp only [← pow_mul, ← pow_succ]

/-- The Ree Steinberg map exchanges the two weight-torus coordinates, with exponents
`3^m` and `3^(m+1)` for the parameter `q = 3^(2m+1)`. -/
theorem steinberg_weightTorusPoints (x y : d.1.Closureˣ) :
    d.steinberg (weightTorusPoints d.1.Closure ![x, y]) =
      weightTorusPoints d.1.Closure
        ![y ^ (3 ^ d.toSuzukiReeIndex.halfExponent),
          x ^ (3 ^ (d.toSuzukiReeIndex.halfExponent + 1))] := by
  rw [steinberg_def, d.toSuzukiReeIndex.fieldExponent_eq_two_mul_halfExponent_add_one]
  exact (congrFun (Monoid.End.coe_pow (M := d.AmbientGroup) d.halfFrobenius _)
    (weightTorusPoints d.1.Closure ![x, y])).trans
      (d.halfFrobenius_pow_odd_weightTorusPoints _ x y)

private theorem parameter_exponents :
    3 ^ (d.toSuzukiReeIndex.halfExponent + 1) *
      3 ^ d.toSuzukiReeIndex.halfExponent = d.1.fieldOrder := by
  rw [← pow_add, d.fieldOrder_eq_three_pow,
    d.toSuzukiReeIndex.fieldExponent_eq_two_mul_halfExponent_add_one]
  congr 1
  omega

/-- An ambient weight-torus point is fixed precisely when its first parameter is
`q`-rational and its second is the `3^(m+1)`-st power of the first. -/
theorem weightTorusPoints_mem_fixedSubgroup_iff (x y : d.1.Closureˣ) :
    weightTorusPoints d.1.Closure ![x, y] ∈ fixedSubgroup d.steinberg ↔
      x ^ d.1.fieldOrder = x ∧
        y = x ^ (3 ^ (d.toSuzukiReeIndex.halfExponent + 1)) := by
  rw [mem_fixedSubgroup, steinberg_weightTorusPoints,
    (weightTorusPoints_injective d.1.Closure).eq_iff]
  constructor
  · intro h
    have h0 := congrFun h 0
    have h1 := congrFun h 1
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h0 h1
    refine ⟨?_, h1.symm⟩
    rw [← h1, ← pow_mul, d.parameter_exponents] at h0
    exact h0
  · rintro ⟨hx, rfl⟩
    ext i
    fin_cases i <;> simp [← pow_mul, d.parameter_exponents, hx]

private def torusParameters : d.1.fixedFieldˣ →* (Fin 2 → d.1.Closureˣ) :=
  MonoidHom.pi ![Units.map d.1.fixedField.subtype.toMonoidHom,
    (powMonoidHom (3 ^ (d.toSuzukiReeIndex.halfExponent + 1))).comp
      (Units.map d.1.fixedField.subtype.toMonoidHom)]

private theorem torusParameters_apply (t : d.1.fixedFieldˣ) :
    d.torusParameters t = ![Units.map d.1.fixedField.subtype.toMonoidHom t,
      (Units.map d.1.fixedField.subtype.toMonoidHom t) ^
        (3 ^ (d.toSuzukiReeIndex.halfExponent + 1))] := by
  funext i
  fin_cases i <;> rfl

/-- The torus of the Ree fixed-point group, parametrized faithfully by the nonzero elements
of its fixed field. Its ambient fundamental-weight coordinates are `(t, t^(3^(m+1)))`. -/
def fixedTorus : d.1.fixedFieldˣ →* d.FixedPoints :=
  ((weightTorusPoints d.1.Closure).comp d.torusParameters).codRestrict
    (fixedSubgroup d.steinberg) fun t ↦ by
      rw [MonoidHom.comp_apply, torusParameters_apply]
      apply (d.weightTorusPoints_mem_fixedSubgroup_iff _ _).mpr
      refine ⟨?_, rfl⟩
      apply Units.ext
      simpa using d.1.mem_fixedField.mp (t : d.1.fixedField).property

/-- The torus embedding has the specified fundamental-weight coordinates in the actual
algebraic-closure carrier. -/
@[simp]
theorem coe_fixedTorus (t : d.1.fixedFieldˣ) :
    (d.fixedTorus t : d.AmbientGroup) = weightTorusPoints d.1.Closure
      ![Units.map d.1.fixedField.subtype.toMonoidHom t,
        (Units.map d.1.fixedField.subtype.toMonoidHom t) ^
          (3 ^ (d.toSuzukiReeIndex.halfExponent + 1))] := by
  exact congrArg (weightTorusPoints d.1.Closure) (d.torusParameters_apply t)

/-- Distinct nonzero fixed-field parameters give distinct Ree torus elements. -/
theorem fixedTorus_injective : Function.Injective d.fixedTorus := by
  intro t u h
  have hp := weightTorusPoints_injective d.1.Closure
    (congrArg (fun g : d.FixedPoints ↦ (g : d.AmbientGroup)) h)
  have h0 := congrFun hp 0
  exact Units.map_injective (f := d.1.fixedField.subtype.toMonoidHom)
    Subtype.val_injective h0

/-- The embedded Ree torus is exactly the intersection of the ambient weight torus with the
Steinberg fixed points. -/
theorem mem_range_fixedTorus_iff (g : d.FixedPoints) :
    g ∈ d.fixedTorus.range ↔ (g : d.AmbientGroup) ∈ (weightTorusPoints d.1.Closure).range := by
  constructor
  · rintro ⟨t, rfl⟩
    exact ⟨_, (d.coe_fixedTorus t).symm⟩
  · rintro ⟨s, hs⟩
    have heta : ![s 0, s 1] = s := by ext i; fin_cases i <;> rfl
    have hf := (d.weightTorusPoints_mem_fixedSubgroup_iff (s 0) (s 1)).mp
      (heta.symm ▸ hs.symm ▸ g.property)
    let t : d.1.fixedField := ⟨(s 0 : d.1.Closure), d.1.mem_fixedField.mpr
      (congrArg Units.val hf.1)⟩
    have ht : t ≠ 0 := by
      intro h
      exact (s 0).ne_zero (congrArg Subtype.val h)
    refine ⟨Units.mk0 t ht, ?_⟩
    apply Subtype.ext
    rw [coe_fixedTorus, ← hs]
    apply congrArg (weightTorusPoints d.1.Closure)
    ext i
    fin_cases i
    · rfl
    · simpa [t] using (congrArg Units.val hf.2).symm

/-- The torus in the Ree fixed-point group has order `q - 1`. -/
theorem natCard_range_fixedTorus : Nat.card d.fixedTorus.range = d.1.fieldOrder - 1 := by
  rw [← Nat.card_congr (MonoidHom.ofInjective d.fixedTorus_injective).toEquiv,
    Nat.card_units, d.1.card_fixedField]

end TauCeti.ReeG2LieIndex
