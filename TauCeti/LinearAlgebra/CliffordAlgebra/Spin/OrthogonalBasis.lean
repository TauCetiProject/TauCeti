/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.OrthogonalBasis
public import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.Action

/-!
# The vector action of signed even basis monomials

Let `b` be an orthogonal basis of a quadratic space `(M, Q)` and let `e_s` be the Clifford basis
monomial of a finite index set `s` (`CliffordAlgebra.basis`). When `s` has even cardinality, a
generator `ι Q (b i)` crosses `e_s` with the sign `-1` if `i ∈ s` and `+1` otherwise
(`CliffordAlgebra.basis_mul_ι_of_mem`, `CliffordAlgebra.basis_mul_ι_of_notMem`). So a Spin element
`g = ±e_s` acts on the quadratic space by the reflection in the coordinates of `s`: it negates the
basis vectors `b i` with `i ∈ s` and fixes the others
(`CliffordAlgebra.spinVectorAction_basis_of_coe_eq`). In coordinates, it multiplies the
coordinate at `i` by `-1` for `i ∈ s` and by `1` otherwise
(`CliffordAlgebra.basis_repr_spinVectorAction_of_coe_eq`).

These diagonal sign actions describe the Spin elements that are signed basis monomials, for
instance the elements of finite elementary abelian `2`-subgroups of Spin groups built from
orthogonal bases.

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I, §2.
-/

public section

namespace CliffordAlgebra

variable {R M I : Type*} [CommRing R] [AddCommGroup M] [Module R M] [Invertible (2 : R)]
  [LinearOrder I] {Q : QuadraticForm R M} {b : Module.Basis I R M}

/-- **A signed even basis monomial acts by the reflection in its coordinates**: for an orthogonal
basis `b` and a Spin element `g = ±e_s` with `s` of even cardinality, `g` negates `b i` for
`i ∈ s` and fixes `b i` for `i ∉ s`. -/
theorem spinVectorAction_basis_of_coe_eq (hb : (QuadraticMap.associated Q).IsOrthoᵢ b)
    {g : spinGroup Q} {s : Finset I} (hs : Even s.card)
    (hg : (g : CliffordAlgebra Q) = basis Q b s ∨ (g : CliffordAlgebra Q) = -basis Q b s)
    (i : I) :
    spinVectorAction Q g (b i) = if i ∈ s then -b i else b i := by
  apply spinVectorAction_eq_of_mul_ι_eq
  have key : basis Q b s * ι Q (b i) = ι Q (if i ∈ s then -b i else b i) * basis Q b s := by
    split_ifs with hi
    · obtain ⟨k, hk⟩ := hs
      have hodd : Odd (s.card - 1) := ⟨k - 1, by have := Finset.card_pos.mpr ⟨i, hi⟩; omega⟩
      rw [basis_mul_ι_of_mem hb hi, hodd.neg_one_pow, neg_one_smul, map_neg, neg_mul]
    · rw [basis_mul_ι_of_notMem hb hi, hs.neg_one_pow, one_smul]
  rcases hg with hg | hg <;> rw [hg]
  · exact key
  · rw [neg_mul, key, mul_neg]

/-- **A signed even basis monomial acts diagonally in coordinates**: for an orthogonal basis `b`
and a Spin element `g = ±e_s` with `s` of even cardinality, the `i`-th coordinate of `g • v` is
`-1` or `1` times that of `v`, according as `i ∈ s` or not. -/
theorem basis_repr_spinVectorAction_of_coe_eq (hb : (QuadraticMap.associated Q).IsOrthoᵢ b)
    {g : spinGroup Q} {s : Finset I} (hs : Even s.card)
    (hg : (g : CliffordAlgebra Q) = basis Q b s ∨ (g : CliffordAlgebra Q) = -basis Q b s)
    (v : M) (i : I) :
    b.repr (spinVectorAction Q g v) i = (if i ∈ s then -1 else 1) * b.repr v i := by
  refine LinearMap.congr_fun (b.ext (f₁ := b.coord i ∘ₗ (spinVectorAction Q g).toLinearMap)
    (f₂ := (if i ∈ s then -1 else 1 : R) • b.coord i) fun j ↦ ?_) v
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, spinVectorAction_basis_of_coe_eq hb hs hg,
    LinearMap.smul_apply, Module.Basis.coord_apply, Module.Basis.repr_self, smul_eq_mul]
  by_cases hij : i = j
  · subst hij
    split_ifs <;> simp
  · split_ifs <;> simp [Ne.symm hij]

end CliffordAlgebra
