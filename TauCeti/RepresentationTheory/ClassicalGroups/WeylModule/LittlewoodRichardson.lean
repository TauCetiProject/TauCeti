/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.ClassicalGroups.UnitaryTrick
public import TauCeti.RepresentationTheory.ClassicalGroups.WeylModule.Character
public import TauCeti.RepresentationTheory.ClassicalGroups.WeylModule.Laurent
public import TauCeti.RepresentationTheory.ClassicalGroups.WeylModule.Rationality
public import TauCeti.RepresentationTheory.Rep.DirectSum.Character
public import TauCeti.RingTheory.MvPolynomial.Symmetric.Schur.LittlewoodRichardson

/-!
# Tensor products of Weyl modules: the Littlewood–Richardson rule for `GL n ℂ`

For Young diagrams `λ` and `μ`, the tensor product of the Weyl modules
`𝕊^λ(ℂⁿ) = TauCeti.weylModuleOfShape ℂ n λ` and `𝕊^μ(ℂⁿ)`, as a representation of `GL n ℂ`,
decomposes as

`𝕊^λ(ℂⁿ) ⊗ 𝕊^μ(ℂⁿ) ≅ ⨁_ν 𝕊^ν(ℂⁿ) ^ c_ν`,

the sum running over the partitions `ν` of `|λ| + |μ|`, where `c_ν` is the number of
`λ`-Yamanouchi semistandard tableaux `T` of shape `μ` with entries below `n` whose content added
to `λ` is `ν` (`TauCeti.nonempty_equiv_tprod_weylRepOfShape`). The decomposition is indexed by
these tableaux themselves, each contributing one copy of `𝕊^ν(ℂⁿ)`.

When `ν` has at most `n` rows, the entries of such a tableau are row indices of `ν`, so they are
automatically below `n` and `c_ν` is the Littlewood–Richardson coefficient `c^ν_{λμ}` in
Stembridge's form. The Littlewood–Richardson coefficients `c^ν_{λμ}` for `ν` with at most `n` rows
are thus the tensor-product multiplicities of the polynomial irreducible representations of
`GL n ℂ`. For `ν` with more than `n` rows the bounded count `c_ν` can be smaller than `c^ν_{λμ}`
(for `n = 1` and `λ = μ = (1)`, it is `0` for `ν = (1, 1)` while `c^ν_{λμ} = 1`), but this does
not affect the decomposition: Weyl modules of diagrams with more than `n` rows are zero, as is
`𝕊^λ(ℂⁿ)` itself when `λ` has more than `n` rows, so no bound on the number of rows is needed in
the statement.

Both sides are rational representations of `GL n ℂ` (`TauCeti.IsRationalRep.tprod` and
`TauCeti.IsRationalRep.directSum`), and rational representations whose characters agree on the
diagonal torus are equivalent
(`TauCeti.IsRationalRep.nonempty_equiv_of_forall_character_diagGL_eq`). On the torus the character
of a Weyl module is its Schur polynomial
(`TauCeti.char_weylRepOfShape_diagonal_eq_eval_diagramSchurPoly`), and the character of a tensor
product is the product of the characters, so the two characters agree by the Littlewood–Richardson
rule for Schur polynomials, `TauCeti.diagramSchurPoly_mul_diagramSchurPoly`.

The same holds for the rational Weyl modules `V_λ = TauCeti.rationalWeylRep ℂ n λ` of arbitrary
dominant weights, whose entries may be negative. Writing `λ = λ₀ + a·(1, …, 1)` and
`μ = μ₀ + b·(1, …, 1)` with polynomial parts `λ₀`, `μ₀` and `a = λₙ`, `b = μₙ`, the tensor product
`V_λ ⊗ V_μ` is the determinant twist by `det ^ (a + b)` of `𝕊^{λ₀}(ℂⁿ) ⊗ 𝕊^{μ₀}(ℂⁿ)`, so

`V_λ ⊗ V_μ ≅ ⨁_ν V_{ν + (a + b)·(1, …, 1)} ^ c^ν_{λ₀μ₀}`

(`TauCeti.nonempty_equiv_tprod_rationalWeylRep`). Here, unlike in the polynomial form, the sum has
to be restricted to the partitions `ν` with at most `n` rows: the weight `TauCeti.weightOfShape n ν`
records only the first `n` rows of `ν`, so its rational Weyl module is not zero when `ν` has more
rows. Those partitions contribute nothing to the character, since their Schur polynomials in `n`
variables vanish. On the torus the character of `V_λ` is the Laurent polynomial
`(∏ᵢ tᵢ) ^ a · s_{λ₀}(t)` (`TauCeti.char_rationalWeylRep_diagonal_eq_eval_diagramSchurPoly`), and
the proof is otherwise the one above.

## Main results

* `TauCeti.nonempty_equiv_tprod_weylRepOfShape`: **the Littlewood–Richardson rule for `GL n ℂ`**,
  the decomposition of `𝕊^λ(ℂⁿ) ⊗ 𝕊^μ(ℂⁿ)` as an equivalence of representations.
* `TauCeti.nonempty_equiv_tprod_rationalWeylRep`: the Littlewood–Richardson rule for the rational
  Weyl modules `V_λ ⊗ V_μ` of two dominant weights.

## References

* W. Fulton and J. Harris, *Representation Theory: A First Course* (1991), Lecture 6, §6.1, and
  Appendix A.1.
* J. R. Stembridge, *A concise proof of the Littlewood–Richardson rule*, Electron. J. Combin.
  **9** (2002), Note 5.
-/

public section

namespace TauCeti

open Finset MvPolynomial YoungDiagram

variable (n : ℕ)

open scoped Classical in
/-- **The Littlewood–Richardson rule for `GL n ℂ`.** The tensor product of the Weyl modules of
two Young diagrams `λ` and `μ` is equivalent to the direct sum of the Weyl modules `𝕊^ν(ℂⁿ)`, one
for each `λ`-Yamanouchi semistandard tableau `T` of shape `μ` with entries below `n`, where `ν` is
the partition of `|λ| + |μ|` with `λ + c(T) = ν`. So when `ν` has at most `n` rows, `𝕊^ν(ℂⁿ)`
occurs with multiplicity the Littlewood–Richardson coefficient `c^ν_{λμ}`; the summands for `ν` with
more than `n` rows are zero. -/
theorem nonempty_equiv_tprod_weylRepOfShape (lam μ : YoungDiagram) :
    Nonempty (Representation.Equiv ((weylRepOfShape ℂ n lam).tprod (weylRepOfShape ℂ n μ))
      (Representation.directSum fun p : Σ ν : (lam.card + μ.card).Partition,
          {T : BoundedSSYT n μ // T.1.IsYamanouchi lam ∧
            ∀ i, lam.rowLen i + T.1.content i = (ofPartition ν).rowLen i} =>
        weylRepOfShape ℂ n (ofPartition p.1))) := by
  -- Instance search does not find the additive groups of the summands under the binder of the
  -- direct sum, through the tensor power they are submodules of, so they are supplied here.
  let _ (p : Σ ν : (lam.card + μ.card).Partition,
      {T : BoundedSSYT n μ // T.1.IsYamanouchi lam ∧
        ∀ i, lam.rowLen i + T.1.content i = (ofPartition ν).rowLen i}) :
      AddCommGroup (weylModuleOfShape ℂ n (ofPartition p.1)).toSubmodule :=
    inferInstance
  -- Nor does it find the additive group of the tensor product: its additive monoid is built from
  -- those of the two submodules, which unification cannot recognize as coming from additive
  -- groups. The two agree up to instance unfolding, so the group is given explicitly.
  let _ : AddCommGroup (TensorProduct ℂ (weylModuleOfShape ℂ n lam).toSubmodule
      (weylModuleOfShape ℂ n μ).toSubmodule) :=
    TensorProduct.addCommGroup (R := ℂ) (M := (weylModuleOfShape ℂ n lam).toSubmodule)
      (N := (weylModuleOfShape ℂ n μ).toSubmodule)
  refine IsRationalRep.nonempty_equiv_of_forall_character_diagGL_eq
    ((isPolynomialRep_weylRepOfShape n lam).tprod
      (isPolynomialRep_weylRepOfShape n μ)).isRationalRep
    (IsRationalRep.directSum fun p =>
      (isPolynomialRep_weylRepOfShape n (ofPartition p.1)).isRationalRep)
    fun t => ?_
  -- Both characters are sums of Schur polynomials: on the left by the Littlewood–Richardson rule
  -- for the product `s_λ s_μ`, on the right one summand per tableau.
  -- `Representation.char_tensor` is stated for the additive group of the tensor product given
  -- above, which `rw` does not match syntactically, so it is applied up to unfolding.
  refine (congrFun (Representation.char_tensor (V := (weylModuleOfShape ℂ n lam).toSubmodule)
    (W := (weylModuleOfShape ℂ n μ).toSubmodule) (weylRepOfShape ℂ n lam)
    (weylRepOfShape ℂ n μ)) (diagGL t)).trans ?_
  rw [Pi.mul_apply, char_weylRepOfShape_diagonal_eq_eval_diagramSchurPoly,
    char_weylRepOfShape_diagonal_eq_eval_diagramSchurPoly, ← eval_mul,
    diagramSchurPoly_mul_diagramSchurPoly, map_sum, Representation.char_directSum,
    Fintype.sum_sigma]
  refine sum_congr rfl fun ν _ => ?_
  simp only [map_nsmul, char_weylRepOfShape_diagonal_eq_eval_diagramSchurPoly, sum_const,
    card_univ, Fintype.card_subtype]

open scoped Classical in
/-- **The Littlewood–Richardson rule for the rational representations of `GL n ℂ`.** Write the
dominant weights `λ` and `μ` as `λ₀ + a·(1, …, 1)` and `μ₀ + b·(1, …, 1)` with `a = λₙ`,
`b = μₙ` and polynomial parts `λ₀ = λ.detShiftShape`, `μ₀ = μ.detShiftShape`. The tensor product
of the rational Weyl modules `V_λ ⊗ V_μ` is equivalent to the direct sum of the rational Weyl
modules `V_{ν + (a + b)·(1, …, 1)}`, one for each partition `ν` of `|λ₀| + |μ₀|` with at most `n`
rows and each `λ₀`-Yamanouchi semistandard tableau `T` of shape `μ₀` with entries below `n` with
`λ₀ + c(T) = ν`. So `V_{ν + (a + b)·(1, …, 1)}` occurs with multiplicity the Littlewood–Richardson
coefficient `c^ν_{λ₀μ₀}`; each summand is irreducible by `TauCeti.isIrreducible_rationalWeylRep`.
-/
theorem nonempty_equiv_tprod_rationalWeylRep (l m : DominantWeight n) :
    Nonempty (Representation.Equiv ((rationalWeylRep ℂ n l).tprod (rationalWeylRep ℂ n m))
      (Representation.directSum fun p : Σ ν : {ν : (l.detShiftShape.card +
            m.detShiftShape.card).Partition // (ofPartition ν).colLen 0 ≤ n},
          {T : BoundedSSYT n m.detShiftShape // T.1.IsYamanouchi l.detShiftShape ∧
            ∀ i, l.detShiftShape.rowLen i + T.1.content i = (ofPartition ν.1).rowLen i} =>
        rationalWeylRep ℂ n ((weightOfShape n (ofPartition p.1.1)).shift
          (l.detShift + m.detShift)))) := by
  -- The additive groups are supplied as in `TauCeti.nonempty_equiv_tprod_weylRepOfShape`.
  let _ (p : Σ ν : {ν : (l.detShiftShape.card + m.detShiftShape.card).Partition //
        (ofPartition ν).colLen 0 ≤ n},
      {T : BoundedSSYT n m.detShiftShape // T.1.IsYamanouchi l.detShiftShape ∧
        ∀ i, l.detShiftShape.rowLen i + T.1.content i = (ofPartition ν.1).rowLen i}) :
      AddCommGroup (weylModuleOfShape ℂ n
        ((weightOfShape n (ofPartition p.1.1)).shift (l.detShift + m.detShift)).detShiftShape
        ).toSubmodule :=
    inferInstance
  let _ : AddCommGroup (TensorProduct ℂ (weylModuleOfShape ℂ n l.detShiftShape).toSubmodule
      (weylModuleOfShape ℂ n m.detShiftShape).toSubmodule) :=
    TensorProduct.addCommGroup (R := ℂ) (M := (weylModuleOfShape ℂ n l.detShiftShape).toSubmodule)
      (N := (weylModuleOfShape ℂ n m.detShiftShape).toSubmodule)
  refine IsRationalRep.nonempty_equiv_of_forall_character_diagGL_eq
    ((isRationalRep_rationalWeylRep n l).tprod (isRationalRep_rationalWeylRep n m))
    (IsRationalRep.directSum fun p => isRationalRep_rationalWeylRep n _) fun t => ?_
  refine (congrFun (Representation.char_tensor
    (V := (weylModuleOfShape ℂ n l.detShiftShape).toSubmodule)
    (W := (weylModuleOfShape ℂ n m.detShiftShape).toSubmodule) (rationalWeylRep ℂ n l)
    (rationalWeylRep ℂ n m)) (diagGL t)).trans ?_
  rw [Pi.mul_apply, char_rationalWeylRep_diagonal_eq_eval_diagramSchurPoly,
    char_rationalWeylRep_diagonal_eq_eval_diagramSchurPoly, mul_mul_mul_comm, ← eval_mul,
    diagramSchurPoly_mul_diagramSchurPoly, ← Units.val_mul, ← zpow_add, map_sum, mul_sum,
    Representation.char_directSum, Fintype.sum_sigma,
    ← Fintype.sum_subtype_add_sum_subtype fun ν => (ofPartition ν).colLen 0 ≤ n]
  -- The partitions with more than `n` rows contribute nothing: their Schur polynomials vanish.
  rw [Fintype.sum_eq_zero (fun ν : {ν // ¬(ofPartition ν).colLen 0 ≤ n} => _) fun ν => by
      rw [diagramSchurPoly_eq_zero_of_lt_colLen (not_le.mp ν.2), smul_zero, map_zero, mul_zero],
    add_zero]
  refine Fintype.sum_congr _ _ fun ν => ?_
  simp only [char_rationalWeylRep_shift_weightOfShape_diagonal ℂ n ν.2, sum_const, card_univ,
    Fintype.card_subtype, map_nsmul, mul_smul_comm]

end TauCeti
