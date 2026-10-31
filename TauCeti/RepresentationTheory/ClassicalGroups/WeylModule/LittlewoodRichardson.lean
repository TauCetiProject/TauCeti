/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.ClassicalGroups.UnitaryTrick
public import TauCeti.RepresentationTheory.ClassicalGroups.WeylModule.Character
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

## Main results

* `TauCeti.nonempty_equiv_tprod_weylRepOfShape`: **the Littlewood–Richardson rule for `GL n ℂ`**,
  the decomposition of `𝕊^λ(ℂⁿ) ⊗ 𝕊^μ(ℂⁿ)` as an equivalence of representations.

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

end TauCeti
