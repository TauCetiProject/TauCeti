/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.IntegralLattice.AntipodalPairs.ModTwo
public import TauCeti.LinearAlgebra.IntegralLattice.Characteristic.Unimodular
public import TauCeti.LinearAlgebra.IntegralLattice.Examples

/-!
# Norms in the classes modulo two of `U ⊕ N`

Let `U` be the hyperbolic plane and `N` an even unimodular lattice, and put `M = U ⊕ N`. For every
integral lattice the norm modulo four is constant on each class of `M / 2M`
(`TauCeti.IntegralLattice.integralNorm_modEq_of_mk_eq`). For `M` this is the only restriction:
every nonzero class of `M / 2M` contains vectors of every norm `t` congruent modulo four to the
norms of its members. In particular, every class whose norms are `2` modulo four, that is, every
class on which the mod-two quadratic form `Q(x mod 2M) = B(x, x) / 2 mod 2` takes the value `1`,
is the class of a vector of norm `-2`, a root of `M` when `N` is negative definite.

The proof only adjusts the vector inside its class. Write a class representative as
`x = α e + β f + y` with `e`, `f` the isotropic basis of `U` and `y ∈ N`. Translating by twice
`w = a e + b f + z` changes the norm by `4 (B(x, w) + B(w, w) / 2)`, and the integer
`B(x, w) + B(w, w) / 2 = α b + β a + 2 a b + B(y, z) + B(z, z) / 2` takes every value: if `α` or
`β` is odd this is already so for `z = 0`, by solving a linear equation in `b` or `a`. If both are
even, after normalizing `a` it remains to control the parity of `B(y, z) + B(z, z) / 2`, which is
the parity of `B(y, z)` because `N` is even. If every `B(y, z)` were even, then `y` would be a
characteristic vector of the even unimodular lattice `N`, hence lie in `2N`, and the class of `x`
would be zero.

For `M = U ⊕ E₈(-1)` this is the statement that every class of `M / 2M` with `Q = 1` contains a
root of `M`. Since the orthogonal transvections of the quadratic space `M / 2M` over `𝔽₂` are
indexed by the classes with `Q = 1`, this is what lets the reflections in the roots of `M` reach
every orthogonal transvection of `M / 2M`.

## Main results

* `TauCeti.IntegralLattice.mk_mem_normClassesModTwo_hyperbolicPlane_orthogonalSum_iff`: a
  nonzero class of `(U ⊕ N) / 2(U ⊕ N)` contains a vector of norm `t` if and only if `t` is
  congruent modulo four to the norms of its members.
* `TauCeti.IntegralLattice.mk_mem_normClassesModTwo_neg_two_hyperbolicPlane_orthogonalSum_iff`:
  a class contains a vector of norm `-2` if and only if its norms are `2` modulo four.

## References

* V. Gritsenko and K. Hulek, *Moduli of polarized Enriques surfaces*, §2, for the roots of
  `U ⊕ E₈(-1)` modulo two and the orthogonal group of the discriminant form of `U(2) ⊕ E₈(-2)`.
-/

public section

namespace TauCeti.IntegralLattice

variable {W : Type*} [AddCommGroup W] [Module ℚ W] {N : IntegralLattice W}

/-- The vector `a e + b f + z` of `U ⊕ N`, where `e` and `f` are the isotropic basis vectors of
the hyperbolic plane. -/
private noncomputable def hyperbolicVector (a b : ℤ) (z : N) : hyperbolicPlane.orthogonalSum N :=
  ⟨(![(a : ℚ), b], z), by
    rw [orthogonalSum_carrier, Submodule.mem_prod, mem_hyperbolicPlane_carrier_iff]
    exact ⟨fun i ↦ by fin_cases i <;> simp, z.property⟩⟩

/-- The ambient vector of `a e + b f + z`. -/
private theorem coe_hyperbolicVector (a b : ℤ) (z : N) :
    (hyperbolicVector a b z : (Fin 2 → ℚ) × W) = (![(a : ℚ), b], (z : W)) :=
  (rfl)

/-- Every vector of `U ⊕ N` is `α e + β f + y` with integer coordinates `α` and `β`. -/
private theorem exists_eq_hyperbolicVector (x : hyperbolicPlane.orthogonalSum N) :
    ∃ (α β : ℤ) (y : N), x = hyperbolicVector α β y := by
  have hx : (x : (Fin 2 → ℚ) × W) ∈ hyperbolicPlane.carrier.prod N.carrier := by
    rw [← orthogonalSum_carrier]
    exact x.property
  rw [Submodule.mem_prod] at hx
  obtain ⟨α, hα⟩ := (mem_hyperbolicPlane_carrier_iff _).mp hx.1 0
  obtain ⟨β, hβ⟩ := (mem_hyperbolicPlane_carrier_iff _).mp hx.1 1
  refine ⟨α, β, ⟨(x : (Fin 2 → ℚ) × W).2, hx.2⟩, Subtype.ext (Prod.ext ?_ rfl)⟩
  ext i
  fin_cases i
  · exact hα.symm
  · exact hβ.symm

/-- The integer `B(x, w) + B(w, w) / 2` for `x = α e + β f + y` and `w = a e + b f + z`. -/
private theorem integralForm_add_integralNorm_hyperbolicVector (α β a b : ℤ) (y z : N) :
    (hyperbolicPlane.orthogonalSum N).integralForm (hyperbolicVector α β y)
        (hyperbolicVector a b z) +
      (hyperbolicPlane.orthogonalSum N).integralNorm (hyperbolicVector a b z) =
      α * b + β * a + 2 * a * b + N.integralForm y z + N.integralNorm z := by
  apply Int.cast_injective (α := ℚ)
  simp only [Int.cast_add, Int.cast_mul, Int.cast_ofNat, integralForm_cast, integralNorm_cast,
    norm_apply, orthogonalSum_form, LinearMap.BilinForm.prod_apply, coe_hyperbolicVector,
    hyperbolicPlane_form_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

/-- A vector of `U ⊕ N` with even hyperbolic coordinates and component in `2N` is zero
modulo `2(U ⊕ N)`. -/
private theorem mk_hyperbolicVector_eq_zero (k m : ℤ) (v : N) :
    (Submodule.Quotient.mk (hyperbolicVector (k + k) (m + m) ((2 : ℤ) • v)) :
      QuotSMulTop (2 : ℤ) (hyperbolicPlane.orthogonalSum N)) = 0 := by
  have h : hyperbolicVector (k + k) (m + m) ((2 : ℤ) • v) = (2 : ℤ) • hyperbolicVector k m v := by
    apply Subtype.ext
    apply Prod.ext
    · ext i
      fin_cases i <;> simp [coe_hyperbolicVector, two_mul]
    · simp [coe_hyperbolicVector]
  rw [h, Submodule.Quotient.mk_eq_zero]
  exact Submodule.smul_mem_pointwise_smul _ _ _ Submodule.mem_top

/-- For a vector `x` of `U ⊕ N` outside `2(U ⊕ N)`, the integer `B(x, w) + B(w, w) / 2` takes
every value as `w` runs over `U ⊕ N`. -/
private theorem exists_integralForm_add_integralNorm_eq (hN : N.IsEven) (hNu : N.IsUnimodular)
    {x : hyperbolicPlane.orthogonalSum N}
    (hx : (Submodule.Quotient.mk x : QuotSMulTop (2 : ℤ) (hyperbolicPlane.orthogonalSum N)) ≠ 0)
    (d : ℤ) :
    ∃ w, (hyperbolicPlane.orthogonalSum N).integralForm x w +
      (hyperbolicPlane.orthogonalSum N).integralNorm w = d := by
  obtain ⟨α, β, y, rfl⟩ := exists_eq_hyperbolicVector x
  suffices ∃ (a b : ℤ) (z : N),
      α * b + β * a + 2 * a * b + N.integralForm y z + N.integralNorm z = d by
    obtain ⟨a, b, z, h⟩ := this
    exact ⟨hyperbolicVector a b z, by rw [integralForm_add_integralNorm_hyperbolicVector, h]⟩
  have hNz (z : N) : Even (N.integralNorm z) :=
    (N.even_integralNorm_iff z).mpr (hN.exists_norm_eq_two_mul z)
  rcases Int.even_or_odd α with ⟨k, rfl⟩ | ⟨k, rfl⟩
  · rcases Int.even_or_odd β with ⟨m, rfl⟩ | ⟨m, rfl⟩
    · -- Both coordinates are even, so only the parity of `B(y, z) + B(z, z) / 2` matters.
      obtain ⟨z, c, hc⟩ : ∃ z : N, Even (d - N.integralForm y z - N.integralNorm z) := by
        by_cases hd : Even d
        · exact ⟨0, by simpa using hd⟩
        -- If every `B(y, z)` were even, `y` would be characteristic, hence in `2N`, and the
        -- class of `x` would vanish.
        obtain ⟨z, hz⟩ : ∃ z : N, Odd (N.integralForm y z) := by
          by_contra! hz
          have hy : N.IsCharacteristicVector y := (N.isCharacteristicVector_iff y).mpr
            fun z ↦ Int.modEq_iff_dvd.mpr
              (even_iff_two_dvd.mp ((hNz z).sub (hz z)))
          obtain ⟨v, hv⟩ := hNu.exists_characteristicVector_sub_eq_two_smul hy
            ((N.isEven_iff_isCharacteristicVector_zero).mp hN)
          rw [sub_zero] at hv
          rw [hv] at hx
          exact hx (mk_hyperbolicVector_eq_zero k m v)
        exact ⟨z, ((Int.not_even_iff_odd.mp hd).sub_odd hz).sub (hNz z)⟩
      exact ⟨1 - k, c - m * (1 - k), z, by linear_combination -hc⟩
    · exact ⟨d - (k + k) * -m, -m, 0, by simp only [map_zero, add_zero]; ring⟩
  · exact ⟨-k, d + β * k, 0, by simp only [map_zero, add_zero]; ring⟩

/-- **Norms in a nonzero class modulo two of `U ⊕ N`.** For an even unimodular lattice `N`, a
nonzero class of `(U ⊕ N) / 2(U ⊕ N)` contains a vector of norm `t` if and only if `t` is
congruent modulo four to the norm of one, hence every, member of the class. -/
theorem mk_mem_normClassesModTwo_hyperbolicPlane_orthogonalSum_iff (hN : N.IsEven)
    (hNu : N.IsUnimodular) {x : hyperbolicPlane.orthogonalSum N}
    (hx : (Submodule.Quotient.mk x : QuotSMulTop (2 : ℤ) (hyperbolicPlane.orthogonalSum N)) ≠ 0)
    (t : ℤ) :
    (Submodule.Quotient.mk x : QuotSMulTop (2 : ℤ) (hyperbolicPlane.orthogonalSum N)) ∈
        (hyperbolicPlane.orthogonalSum N).normClassesModTwo t ↔
      t ≡ (hyperbolicPlane.orthogonalSum N).integralNorm x [ZMOD 4] := by
  refine ⟨modEq_integralNorm_of_mk_mem_normClassesModTwo _, fun ht ↦ ?_⟩
  obtain ⟨d, hd⟩ := ht.symm.dvd
  obtain ⟨w, hw⟩ := exists_integralForm_add_integralNorm_eq hN hNu hx d
  refine (hyperbolicPlane.orthogonalSum N).mem_normClassesModTwo.mpr
    ⟨x + (2 : ℤ) • w, ?_, ?_⟩
  · rw [mem_vectorsOfNorm_intCast, integralNorm_add_two_smul, hw]
    linarith
  · rw [Submodule.Quotient.eq, add_sub_cancel_left]
    exact Submodule.smul_mem_pointwise_smul _ _ _ Submodule.mem_top

/-- **Roots in the classes modulo two of `U ⊕ N`.** For an even unimodular lattice `N`, a class of
`(U ⊕ N) / 2(U ⊕ N)` contains a vector of norm `-2` if and only if the norms of its members are
`2` modulo four, that is, if and only if the mod-two quadratic form `B(x, x) / 2 mod 2` is `1` on
it. -/
theorem mk_mem_normClassesModTwo_neg_two_hyperbolicPlane_orthogonalSum_iff (hN : N.IsEven)
    (hNu : N.IsUnimodular) (x : hyperbolicPlane.orthogonalSum N) :
    (Submodule.Quotient.mk x : QuotSMulTop (2 : ℤ) (hyperbolicPlane.orthogonalSum N)) ∈
        (hyperbolicPlane.orthogonalSum N).normClassesModTwo (-2) ↔
      (hyperbolicPlane.orthogonalSum N).integralNorm x ≡ 2 [ZMOD 4] := by
  have hcast : ((-2 : ℤ) : ℚ) = -2 := by norm_num
  have h2 : (-2 : ℤ) ≡ 2 [ZMOD 4] := by decide
  constructor
  · intro h
    rw [← hcast] at h
    exact (modEq_integralNorm_of_mk_mem_normClassesModTwo _ h).symm.trans h2
  · intro h
    have hx : (Submodule.Quotient.mk x :
        QuotSMulTop (2 : ℤ) (hyperbolicPlane.orthogonalSum N)) ≠ 0 := by
      intro h0
      have h0' := integralNorm_modEq_of_mk_eq _ (h0.trans (Submodule.Quotient.mk_zero _).symm)
      rw [QuadraticMap.map_zero] at h0'
      exact absurd (h.symm.trans h0') (by decide)
    rw [← hcast]
    exact (mk_mem_normClassesModTwo_hyperbolicPlane_orthogonalSum_iff hN hNu hx (-2)).mpr
      (h2.trans h.symm)

end TauCeti.IntegralLattice
