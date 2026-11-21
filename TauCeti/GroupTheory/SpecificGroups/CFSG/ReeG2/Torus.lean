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

/-- The indexed weight torus has unique fundamental-weight parameters. -/
theorem weightTorus_injective : Function.Injective d.weightTorus := by
  intro s t h
  rw [weightTorus_apply, weightTorus_apply] at h
  exact (MulEquiv.arrowCongr (finCongr d.rank_eq_two) (MulEquiv.refl _)).injective
    (weightTorusPoints_injective d.1.Closure h)

/-- The half-Frobenius swaps the two weight-torus coordinates and cubes the one
that moves to the second coordinate. -/
@[simp]
theorem halfFrobenius_weightTorus (s : Fin d.1.rank → d.1.Closureˣ) :
    d.halfFrobenius (d.weightTorus s) = d.weightTorus
      (![s ((finCongr d.rank_eq_two).symm 1), s ((finCongr d.rank_eq_two).symm 0) ^ 3] ∘
        finCongr d.rank_eq_two) := by
  rw [halfFrobenius_def, weightTorus_apply, specialIsogeny_weightTorusPoints, weightTorus_apply]
  simp only [Function.comp_apply, Equiv.apply_symm_apply]

/-- The Ree Steinberg map exchanges the two weight-torus coordinates, with exponents
`3^m` and `3^(m+1)` for the parameter `q = 3^(2m+1)`. -/
@[simp]
theorem steinberg_weightTorus (s : Fin d.1.rank → d.1.Closureˣ) :
    d.steinberg (d.weightTorus s) = d.weightTorus
      (![s ((finCongr d.rank_eq_two).symm 1) ^ (3 ^ d.toSuzukiReeIndex.halfExponent),
        s ((finCongr d.rank_eq_two).symm 0) ^ (3 ^ (d.toSuzukiReeIndex.halfExponent + 1))] ∘
          finCongr d.rank_eq_two) := by
  let swapCube (t : Fin d.1.rank → d.1.Closureˣ) :=
    ![t ((finCongr d.rank_eq_two).symm 1), t ((finCongr d.rank_eq_two).symm 0) ^ 3] ∘
      finCongr d.rank_eq_two
  -- The odd-power lemma uses the composition monoid; the pointwise rules use `MonoidHom`.
  have h := d.toSuzukiReeIndex.pow_fieldExponent_apply_pow
    (τ := d.halfFrobenius) (x := fun t ↦ d.weightTorus t)
    (y := fun t ↦ d.weightTorus (swapCube t)) (c := 1)
    (fun t ↦ by simpa only [pow_one, swapCube] using! d.halfFrobenius_weightTorus t)
    (fun t ↦ by
      change d.halfFrobenius (d.halfFrobenius (d.weightTorus (swapCube t))) = _
      rw [d.halfFrobenius_halfFrobenius, primeFrobenius_def, weightTorus_apply,
        frobenius_weightTorusPoints, weightTorus_apply]
      apply congrArg (weightTorusPoints d.1.Closure)
      funext i
      simp only [swapCube, Function.comp_apply, Equiv.apply_symm_apply, Pi.pow_apply,
        characteristic_eq_three, pow_one]
      fin_cases i <;> rfl) s
  simpa only [← steinberg_def, swapCube, characteristic_eq_three, mul_one, Pi.pow_apply,
    ← pow_mul, ← pow_succ] using! h

private theorem parameter_exponents :
    3 ^ (d.toSuzukiReeIndex.halfExponent + 1) *
      3 ^ d.toSuzukiReeIndex.halfExponent = d.1.fieldOrder := by
  rw [← pow_add, d.fieldOrder_eq_three_pow,
    d.toSuzukiReeIndex.fieldExponent_eq_two_mul_halfExponent_add_one]
  congr 1
  omega

/-- An ambient weight-torus point is fixed precisely when its first parameter is
`q`-rational and its second is the `3^(m+1)`-st power of the first. -/
theorem weightTorus_mem_fixedSubgroup_steinberg_iff (s : Fin d.1.rank → d.1.Closureˣ) :
    d.weightTorus s ∈ fixedSubgroup d.steinberg ↔
      s ((finCongr d.rank_eq_two).symm 0) ^ d.1.fieldOrder = s ((finCongr d.rank_eq_two).symm 0) ∧
        s ((finCongr d.rank_eq_two).symm 1) =
          s ((finCongr d.rank_eq_two).symm 0) ^ (3 ^ (d.toSuzukiReeIndex.halfExponent + 1)) := by
  rw [mem_fixedSubgroup, steinberg_weightTorus, d.weightTorus_injective.eq_iff]
  constructor
  · intro h
    have h0 := congrFun h ((finCongr d.rank_eq_two).symm 0)
    have h1 := congrFun h ((finCongr d.rank_eq_two).symm 1)
    simp only [Function.comp_apply, Equiv.apply_symm_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one] at h0 h1
    refine ⟨?_, h1.symm⟩
    rw [← h1, ← pow_mul, d.parameter_exponents] at h0
    exact h0
  · rintro ⟨hx, hy⟩
    funext i
    obtain ⟨j, rfl⟩ := (finCongr d.rank_eq_two).symm.surjective i
    simp only [Function.comp_apply, Equiv.apply_symm_apply]
    fin_cases j
    · -- Evaluate the vector at the `Fin` constructor produced by `fin_cases` before rewriting.
      change s ((finCongr d.rank_eq_two).symm 1) ^ (3 ^ d.toSuzukiReeIndex.halfExponent) =
        s ((finCongr d.rank_eq_two).symm 0)
      rw [hy, ← pow_mul, d.parameter_exponents, hx]
    · exact hy.symm

private def torusParameters : d.1.fixedFieldˣ →* (Fin d.1.rank → d.1.Closureˣ) :=
  MonoidHom.pi (![Units.map d.1.fixedField.subtype.toMonoidHom,
    (powMonoidHom (3 ^ (d.toSuzukiReeIndex.halfExponent + 1))).comp
      (Units.map d.1.fixedField.subtype.toMonoidHom)] ∘ finCongr d.rank_eq_two)

private theorem torusParameters_apply (t : d.1.fixedFieldˣ) :
    d.torusParameters t = ![Units.map d.1.fixedField.subtype.toMonoidHom t,
      (Units.map d.1.fixedField.subtype.toMonoidHom t) ^
        (3 ^ (d.toSuzukiReeIndex.halfExponent + 1))] ∘ finCongr d.rank_eq_two := by
  funext i
  obtain ⟨j, rfl⟩ := (finCongr d.rank_eq_two).symm.surjective i
  rw [torusParameters, MonoidHom.pi_apply]
  simp only [Function.comp_apply, Equiv.apply_symm_apply]
  fin_cases j <;> rfl

/-- The torus of the Ree fixed-point group, parametrized faithfully by the nonzero elements
of its fixed field. Its ambient fundamental-weight coordinates are `(t, t^(3^(m+1)))`. -/
def fixedTorus : d.1.fixedFieldˣ →* d.FixedPoints :=
  (d.weightTorus.comp d.torusParameters).codRestrict
    (fixedSubgroup d.steinberg) fun t ↦ by
      rw [MonoidHom.comp_apply, torusParameters_apply, weightTorus_mem_fixedSubgroup_steinberg_iff]
      simp only [Function.comp_apply, Equiv.apply_symm_apply,
        Matrix.cons_val_zero, Matrix.cons_val_one, and_true]
      apply Units.ext
      simpa using d.1.mem_fixedField.mp (t : d.1.fixedField).property

/-- The torus embedding has the specified fundamental-weight coordinates in the actual
algebraic-closure carrier. -/
@[simp]
theorem coe_fixedTorus (t : d.1.fixedFieldˣ) :
    (d.fixedTorus t : d.AmbientGroup) = d.weightTorus
      (![Units.map d.1.fixedField.subtype.toMonoidHom t,
        (Units.map d.1.fixedField.subtype.toMonoidHom t) ^
          (3 ^ (d.toSuzukiReeIndex.halfExponent + 1))] ∘ finCongr d.rank_eq_two) := by
  exact congrArg d.weightTorus (d.torusParameters_apply t)

/-- Distinct nonzero fixed-field parameters give distinct Ree torus elements. -/
theorem fixedTorus_injective : Function.Injective d.fixedTorus := by
  intro t u h
  have hp := d.weightTorus_injective (congrArg (fun g : d.FixedPoints ↦ (g : d.AmbientGroup)) h)
  have h0 := congrFun hp ((finCongr d.rank_eq_two).symm 0)
  apply Units.map_injective (f := d.1.fixedField.subtype.toMonoidHom) Subtype.val_injective
  simpa only [torusParameters_apply, Function.comp_apply, Equiv.apply_symm_apply,
    Matrix.cons_val_zero] using h0

/-- The embedded Ree torus is exactly the intersection of the ambient weight torus with the
Steinberg fixed points. -/
theorem mem_range_fixedTorus_iff (g : d.FixedPoints) :
    g ∈ d.fixedTorus.range ↔ (g : d.AmbientGroup) ∈ d.weightTorus.range := by
  constructor
  · rintro ⟨t, rfl⟩
    exact ⟨_, (d.coe_fixedTorus t).symm⟩
  · rintro ⟨s, hs⟩
    have hmem : d.weightTorus s ∈ fixedSubgroup d.steinberg := by
      rw [hs]
      exact g.property
    have hf := (d.weightTorus_mem_fixedSubgroup_steinberg_iff s).mp hmem
    let t : d.1.fixedField := ⟨s ((finCongr d.rank_eq_two).symm 0), d.1.mem_fixedField.mpr
      (congrArg Units.val hf.1)⟩
    have ht : t ≠ 0 := by
      intro h
      exact (s ((finCongr d.rank_eq_two).symm 0)).ne_zero (congrArg Subtype.val h)
    refine ⟨Units.mk0 t ht, ?_⟩
    apply Subtype.ext
    rw [coe_fixedTorus, ← hs]
    apply congrArg d.weightTorus
    funext i
    obtain ⟨j, rfl⟩ := (finCongr d.rank_eq_two).symm.surjective i
    simp only [Function.comp_apply, Equiv.apply_symm_apply]
    fin_cases j
    · exact Units.ext rfl
    · exact Units.ext (congrArg Units.val hf.2).symm

/-- The torus in the Ree fixed-point group has order `q - 1`. -/
theorem natCard_range_fixedTorus : Nat.card d.fixedTorus.range = d.1.fieldOrder - 1 := by
  rw [← Nat.card_congr (MonoidHom.ofInjective d.fixedTorus_injective).toEquiv,
    Nat.card_units, d.1.card_fixedField]

end TauCeti.ReeG2LieIndex
