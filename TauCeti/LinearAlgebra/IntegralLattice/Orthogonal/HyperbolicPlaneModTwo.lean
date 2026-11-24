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
`w = a e + b f + z` changes the norm by `4 (B(x, w) + B(w, w))`, and the integer
`B(x, w) + B(w, w) = α b + β a + 2 a b + B(y, z) + B(z, z)` takes every value: if `α` or `β` is
odd this is already so for `z = 0`, by solving a linear equation in `b` or `a`. If both are even,
after normalizing `a` it remains to control the parity of `B(y, z) + B(z, z)`, which is the parity
of `B(y, z)` because `B(z, z)` is even, `N` being even. If every `B(y, z)` were even, then `y`
would be a characteristic vector of the even unimodular lattice `N`, hence lie in `2N`, and the
class of `x` would be zero.

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

/-- Every vector of `U ⊕ N` is `α e + β f + y` with integer coordinates `α` and `β` and `y ∈ N`. -/
private theorem exists_eq_inl_add_inr (x : hyperbolicPlane.orthogonalSum N) :
    ∃ (α β : ℤ) (y : N), x = orthogonalSumInl hyperbolicPlane N
      (α • hyperbolicPlaneBasis 0 + β • hyperbolicPlaneBasis 1) +
        orthogonalSumInr hyperbolicPlane N y := by
  refine ⟨hyperbolicPlaneBasis.repr (orthogonalSumFst hyperbolicPlane N x) 0,
    hyperbolicPlaneBasis.repr (orthogonalSumFst hyperbolicPlane N x) 1,
    orthogonalSumSnd hyperbolicPlane N x, ?_⟩
  rw [← Fin.sum_univ_two (fun i ↦
      hyperbolicPlaneBasis.repr (orthogonalSumFst hyperbolicPlane N x) i • hyperbolicPlaneBasis i),
    hyperbolicPlaneBasis.sum_repr, orthogonalSumInl_fst_add_inr_snd_eq]

/-- The integer `B(x, w) + B(w, w)` for `x = α e + β f + y` and `w = a e + b f + z`. -/
private theorem integralForm_add_integralNorm_inl_add_inr (α β a b : ℤ) (y z : N) :
    (hyperbolicPlane.orthogonalSum N).integralForm
        (orthogonalSumInl hyperbolicPlane N
          (α • hyperbolicPlaneBasis 0 + β • hyperbolicPlaneBasis 1) +
            orthogonalSumInr hyperbolicPlane N y)
        (orthogonalSumInl hyperbolicPlane N
          (a • hyperbolicPlaneBasis 0 + b • hyperbolicPlaneBasis 1) +
            orthogonalSumInr hyperbolicPlane N z) +
      (hyperbolicPlane.orthogonalSum N).integralNorm
        (orthogonalSumInl hyperbolicPlane N
          (a • hyperbolicPlaneBasis 0 + b • hyperbolicPlaneBasis 1) +
            orthogonalSumInr hyperbolicPlane N z) =
      α * b + β * a + 2 * a * b + N.integralForm y z + N.integralNorm z := by
  rw [integralForm_orthogonalSum, integralNorm_orthogonalSum]
  simp only [map_add (orthogonalSumFst hyperbolicPlane N),
    map_add (orthogonalSumSnd hyperbolicPlane N), orthogonalSumFst_inl, orthogonalSumFst_inr,
    orthogonalSumSnd_inl, orthogonalSumSnd_inr, add_zero, zero_add, integralNorm_apply]
  rw [integralForm_hyperbolicPlaneBasis, integralForm_hyperbolicPlaneBasis]
  ring

/-- For a vector `x` of `U ⊕ N` outside `2(U ⊕ N)`, the integer `B(x, w) + B(w, w)` takes every
value as `w` runs over `U ⊕ N`. -/
private theorem exists_integralForm_add_integralNorm_eq (hN : N.IsEven) (hNu : N.IsUnimodular)
    {x : hyperbolicPlane.orthogonalSum N}
    (hx : (Submodule.Quotient.mk x : QuotSMulTop (2 : ℤ) (hyperbolicPlane.orthogonalSum N)) ≠ 0)
    (d : ℤ) :
    ∃ w, (hyperbolicPlane.orthogonalSum N).integralForm x w +
      (hyperbolicPlane.orthogonalSum N).integralNorm w = d := by
  obtain ⟨α, β, y, rfl⟩ := exists_eq_inl_add_inr x
  suffices ∃ (a b : ℤ) (z : N),
      α * b + β * a + 2 * a * b + N.integralForm y z + N.integralNorm z = d by
    obtain ⟨a, b, z, h⟩ := this
    exact ⟨_, by rw [integralForm_add_integralNorm_inl_add_inr α β a b y z, h]⟩
  have hNz (z : N) : Even (N.integralNorm z) :=
    (N.even_integralNorm_iff z).mpr (hN.exists_norm_eq_two_mul z)
  rcases Int.even_or_odd α with ⟨k, rfl⟩ | ⟨k, rfl⟩
  · rcases Int.even_or_odd β with ⟨m, rfl⟩ | ⟨m, rfl⟩
    · -- Both coordinates are even, so only the parity of `B(y, z) + B(z, z)` matters.
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
          have hx2 : orthogonalSumInl hyperbolicPlane N
                ((k + k) • hyperbolicPlaneBasis 0 + (m + m) • hyperbolicPlaneBasis 1) +
              orthogonalSumInr hyperbolicPlane N y = (2 : ℤ) • (orthogonalSumInl hyperbolicPlane N
                (k • hyperbolicPlaneBasis 0 + m • hyperbolicPlaneBasis 1) +
              orthogonalSumInr hyperbolicPlane N v) := by
            rw [hv]
            simp only [map_add, map_zsmul]
            module
          apply hx
          rw [Submodule.Quotient.mk_eq_zero, hx2]
          exact Submodule.smul_mem_pointwise_smul _ _ _ Submodule.mem_top
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
