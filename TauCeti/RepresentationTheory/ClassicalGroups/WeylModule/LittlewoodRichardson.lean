/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Multiplicity
public import TauCeti.RepresentationTheory.ClassicalGroups.UnitaryTrick
public import TauCeti.RepresentationTheory.ClassicalGroups.WeylModule.Character
public import TauCeti.RepresentationTheory.ClassicalGroups.WeylModule.Differential
public import TauCeti.RepresentationTheory.ClassicalGroups.WeylModule.Laurent
public import TauCeti.RepresentationTheory.ClassicalGroups.WeylModule.Rationality
public import TauCeti.RepresentationTheory.Rep.DirectSum.Character
public import TauCeti.RingTheory.MvPolynomial.Symmetric.Schur.LittlewoodRichardson

/-!
# Tensor products of Weyl modules: the Littlewood–Richardson rule for `GL n ℂ` and `𝔤𝔩ₙ`

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

Indexing the decomposition by Littlewood–Richardson tableaux instead
(`TauCeti.nonempty_equiv_tprod_weylRepOfShape_lrTableau`) and restricting it to the partitions `ν`
with at most `n` rows, it differentiates to the Lie algebra `𝔤𝔩ₙ(ℂ)`. A rational representation
differentiates to a `𝔤𝔩ₙ`-module (`TauCeti.IsRationalRep.differential`), compatibly with
equivalences, tensor products and direct sums, and the Weyl module `𝕊^ν(ℂⁿ)` of a diagram with at
most `n` rows differentiates to the named irreducible `L(ν) = TauCeti.glIrreducible n ν` of highest
weight the row lengths of `ν`. This gives **the Littlewood–Richardson rule for `𝔤𝔩ₙ`**: for Young
diagrams `λ` and `μ` with at most `n` rows,

`L(λ) ⊗ L(μ) ≅ ⨁_ν L(ν) ^ c^ν_{λμ}`, with `c^ν_{λμ} = Nat.card (LRTableau λ ν μ)`,

the sum running over the partitions `ν` of `|λ| + |μ|` with at most `n` rows
(`TauCeti.nonempty_lieModuleEquiv_tensorProduct_glIrreducible`). Since the `L(ν)` of distinct
diagrams with at most `n` rows are not isomorphic, the multiplicity of `L(ν)` in `L(λ) ⊗ L(μ)` is
the Littlewood–Richardson coefficient for every diagram `ν` with at most `n` rows, and in particular
vanishes unless `λ ⊆ ν` and `|ν| = |λ| + |μ|`
(`TauCeti.isotypicMultiplicity_tensorProduct_glIrreducible`).

## Main results

* `TauCeti.nonempty_equiv_tprod_weylRepOfShape`: **the Littlewood–Richardson rule for `GL n ℂ`**,
  the decomposition of `𝕊^λ(ℂⁿ) ⊗ 𝕊^μ(ℂⁿ)` as an equivalence of representations;
  `TauCeti.nonempty_equiv_tprod_weylRepOfShape_lrTableau` is the same decomposition indexed by
  Littlewood–Richardson tableaux.
* `TauCeti.nonempty_equiv_tprod_rationalWeylRep`: the Littlewood–Richardson rule for the rational
  Weyl modules `V_λ ⊗ V_μ` of two dominant weights.
* `TauCeti.nonempty_lieModuleEquiv_tensorProduct_glIrreducible`: **the Littlewood–Richardson rule
  for `𝔤𝔩ₙ`**, the decomposition of `L(λ) ⊗ L(μ)` as an equivalence of `𝔤𝔩ₙ`-modules.
* `TauCeti.isotypicMultiplicity_tensorProduct_glIrreducible`: **the multiplicity of `L(ν)` in
  `L(λ) ⊗ L(μ)` is `Nat.card (LRTableau λ ν μ)`.**

## References

* W. Fulton and J. Harris, *Representation Theory: A First Course* (1991), Lecture 6, §6.1, and
  Appendix A.1.
* J. R. Stembridge, *A concise proof of the Littlewood–Richardson rule*, Electron. J. Combin.
  **9** (2002), Note 5.
-/

public section

namespace TauCeti

open Finset MvPolynomial YoungDiagram TensorProduct

open scoped DirectSum

variable (n : ℕ)

variable {n} in
/-- The common step of the decompositions below: the tensor product of two rational representations
on Weyl modules is equivalent to a finite direct sum of rational representations on Weyl modules as
soon as, on the diagonal torus, the product of the two characters is the sum of the characters of
the summands. -/
private theorem nonempty_equiv_tprod_directSum_of_forall_character_diagGL_eq
    {a b : YoungDiagram} {ι : Type*} [Fintype ι] {c : ι → YoungDiagram}
    {ρ : Representation ℂ (GL (Fin n) ℂ) (weylModuleOfShape ℂ n a).toSubmodule}
    {σ : Representation ℂ (GL (Fin n) ℂ) (weylModuleOfShape ℂ n b).toSubmodule}
    {τ : ∀ i, Representation ℂ (GL (Fin n) ℂ) (weylModuleOfShape ℂ n (c i)).toSubmodule}
    (hρ : IsRationalRep ρ) (hσ : IsRationalRep σ) (hτ : ∀ i, IsRationalRep (τ i))
    (h : letI : AddCommGroup (weylModuleOfShape ℂ n a).toSubmodule := inferInstance
      letI : AddCommGroup (weylModuleOfShape ℂ n b).toSubmodule := inferInstance
      letI (i : ι) : AddCommGroup (weylModuleOfShape ℂ n (c i)).toSubmodule := inferInstance
      ∀ t : Fin n → ℂˣ, ρ.character (diagGL t) * σ.character (diagGL t) =
        ∑ i, (τ i).character (diagGL t)) :
    Nonempty (Representation.Equiv (ρ.tprod σ) (Representation.directSum τ)) := by
  -- Instance search does not find the additive groups of the summands under the binder of the
  -- direct sum, through the tensor power they are submodules of, so they are supplied here.
  let _ (i : ι) : AddCommGroup (weylModuleOfShape ℂ n (c i)).toSubmodule := inferInstance
  -- Nor does it find the additive group of the tensor product: its additive monoid is built from
  -- those of the two submodules, which unification cannot recognize as coming from additive
  -- groups. The two agree up to instance unfolding, so the group is given explicitly.
  let _ : AddCommGroup (TensorProduct ℂ (weylModuleOfShape ℂ n a).toSubmodule
      (weylModuleOfShape ℂ n b).toSubmodule) :=
    TensorProduct.addCommGroup (R := ℂ) (M := (weylModuleOfShape ℂ n a).toSubmodule)
      (N := (weylModuleOfShape ℂ n b).toSubmodule)
  refine IsRationalRep.nonempty_equiv_of_forall_character_diagGL_eq (hρ.tprod hσ)
    (IsRationalRep.directSum hτ) fun t => ?_
  -- `Representation.char_tensor` is stated for the additive group of the tensor product given
  -- above, which `rw` does not match syntactically, so it is applied up to unfolding.
  refine (congrFun (Representation.char_tensor (V := (weylModuleOfShape ℂ n a).toSubmodule)
    (W := (weylModuleOfShape ℂ n b).toSubmodule) ρ σ) (diagGL t)).trans ?_
  rw [Pi.mul_apply, Representation.char_directSum, h]

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
  refine nonempty_equiv_tprod_directSum_of_forall_character_diagGL_eq
    (isPolynomialRep_weylRepOfShape n lam).isRationalRep
    (isPolynomialRep_weylRepOfShape n μ).isRationalRep ?_ fun t => ?_
  · exact fun p => (isPolynomialRep_weylRepOfShape n (ofPartition p.1)).isRationalRep
  -- Both characters are sums of Schur polynomials: on the left by the Littlewood–Richardson rule
  -- for the product `s_λ s_μ`, on the right one summand per tableau.
  rw [char_weylRepOfShape_diagonal_eq_eval_diagramSchurPoly,
    char_weylRepOfShape_diagonal_eq_eval_diagramSchurPoly, ← eval_mul,
    diagramSchurPoly_mul_diagramSchurPoly, map_sum, Fintype.sum_sigma]
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
  refine nonempty_equiv_tprod_directSum_of_forall_character_diagGL_eq
    (isRationalRep_rationalWeylRep n l) (isRationalRep_rationalWeylRep n m) ?_ fun t => ?_
  · exact fun p => isRationalRep_rationalWeylRep n _
  -- The character of `V_λ ⊗ V_μ` on the torus is `(∏ᵢ tᵢ) ^ (a + b) · (s_{λ₀} s_{μ₀})(t)`: the two
  -- determinant twists combine into one.
  rw [char_rationalWeylRep_diagonal_eq_eval_diagramSchurPoly,
    char_rationalWeylRep_diagonal_eq_eval_diagramSchurPoly, mul_mul_mul_comm, ← eval_mul,
    ← Units.val_mul, ← zpow_add]
  -- Expand `s_{λ₀} s_{μ₀}` by the Littlewood–Richardson rule for Schur polynomials, over the
  -- partitions with at most `n` rows, and the sum of characters over partitions and then tableaux.
  rw [diagramSchurPoly_mul_diagramSchurPoly, sum_nsmul_diagramSchurPoly_eq_sum_colLen_le, map_sum,
    mul_sum, Fintype.sum_sigma]
  refine Fintype.sum_congr _ _ fun ν => ?_
  simp only [char_rationalWeylRep_shift_weightOfShape_diagonal ℂ n ν.2, sum_const, card_univ,
    Fintype.card_subtype, map_nsmul, mul_smul_comm]

/-- **The Littlewood–Richardson rule for `GL n ℂ`, with Littlewood–Richardson tableaux.** The
tensor product of the Weyl modules of two Young diagrams `λ` and `μ` is equivalent to the direct
sum of the Weyl modules `𝕊^ν(ℂⁿ)`, one for each partition `ν` of `|λ| + |μ|` with at most `n` rows
and each Littlewood–Richardson tableau of shape `ν / λ` and content `μ`. So `𝕊^ν(ℂⁿ)` occurs with
multiplicity the Littlewood–Richardson coefficient `c^ν_{λμ} = Nat.card (LRTableau λ ν μ)`. -/
theorem nonempty_equiv_tprod_weylRepOfShape_lrTableau (lam μ : YoungDiagram) :
    Nonempty (Representation.Equiv ((weylRepOfShape ℂ n lam).tprod (weylRepOfShape ℂ n μ))
      (Representation.directSum fun p : Σ ν : {ν : (lam.card + μ.card).Partition //
            (ofPartition ν).colLen 0 ≤ n}, LRTableau lam (ofPartition ν.1) μ =>
        weylRepOfShape ℂ n (ofPartition p.1.1))) := by
  let _ (ν : (lam.card + μ.card).Partition) : Fintype (LRTableau lam (ofPartition ν) μ) :=
    Fintype.ofFinite _
  refine nonempty_equiv_tprod_directSum_of_forall_character_diagGL_eq
    (isPolynomialRep_weylRepOfShape n lam).isRationalRep
    (isPolynomialRep_weylRepOfShape n μ).isRationalRep ?_ fun t => ?_
  · exact fun p => (isPolynomialRep_weylRepOfShape n (ofPartition p.1.1)).isRationalRep
  rw [char_weylRepOfShape_diagonal_eq_eval_diagramSchurPoly,
    char_weylRepOfShape_diagonal_eq_eval_diagramSchurPoly, ← eval_mul,
    diagramSchurPoly_mul_diagramSchurPoly_eq_sum_natCard_lrTableau,
    sum_nsmul_diagramSchurPoly_eq_sum_colLen_le, map_sum, Fintype.sum_sigma]
  refine Fintype.sum_congr _ _ fun ν => ?_
  simp only [map_nsmul, char_weylRepOfShape_diagonal_eq_eval_diagramSchurPoly, sum_const,
    card_univ, Nat.card_eq_fintype_card]

attribute [local instance 100] LieRing.ofAssociativeRing in
/-- **The Littlewood–Richardson rule for `𝔤𝔩ₙ`.** For Young diagrams `λ` and `μ` with at most `n`
rows, the tensor product of the irreducible `𝔤𝔩ₙ(ℂ)`-modules `L(λ) = glIrreducible n λ` and `L(μ)`
of highest weights the row-length vectors of `λ` and `μ` is the direct sum of the modules `L(ν)`,
one for each partition `ν` of `|λ| + |μ|` with at most `n` rows and each Littlewood–Richardson
tableau of shape `ν / λ` and content `μ`. So `L(ν)` occurs with multiplicity the
Littlewood–Richardson coefficient `c^ν_{λμ} = Nat.card (LRTableau λ ν μ)`. -/
theorem nonempty_lieModuleEquiv_tensorProduct_glIrreducible {lam μ : YoungDiagram}
    (hlam : lam.colLen 0 ≤ n) (hμ : μ.colLen 0 ≤ n) :
    Nonempty ((glIrreducible n fun i ↦ (lam.rowLen i : ℂ)) ⊗[ℂ]
        (glIrreducible n fun i ↦ (μ.rowLen i : ℂ)) ≃ₗ⁅ℂ,Matrix (Fin n) (Fin n) ℂ⁆
      ⨁ p : Σ ν : {ν : (lam.card + μ.card).Partition // (ofPartition ν).colLen 0 ≤ n},
          LRTableau lam (ofPartition ν.1) μ,
        glIrreducible n fun i ↦ ((ofPartition p.1.1).rowLen i : ℂ)) := by
  let ι := Σ ν : {ν : (lam.card + μ.card).Partition // (ofPartition ν).colLen 0 ≤ n},
    LRTableau lam (ofPartition ν.1) μ
  let _ (p : ι) : AddCommGroup (weylModuleOfShape ℂ n (ofPartition p.1.1)).toSubmodule :=
    inferInstance
  let _ : AddCommGroup (weylModuleOfShape ℂ n lam).toSubmodule := inferInstance
  let _ : AddCommGroup (weylModuleOfShape ℂ n μ).toSubmodule := inferInstance
  have hlam' := (isPolynomialRep_weylRepOfShape n lam).isRationalRep
  have hμ' := (isPolynomialRep_weylRepOfShape n μ).isRationalRep
  have hν (p : ι) := (isPolynomialRep_weylRepOfShape n (ofPartition p.1.1)).isRationalRep
  obtain ⟨φ⟩ := nonempty_equiv_tprod_weylRepOfShape_lrTableau n lam μ
  obtain ⟨e₁⟩ := nonempty_lieModuleEquiv_weylRepOfShape_glIrreducible hlam
  obtain ⟨e₂⟩ := nonempty_lieModuleEquiv_weylRepOfShape_glIrreducible hμ
  have e (p : ι) := (nonempty_lieModuleEquiv_weylRepOfShape_glIrreducible p.1.2).some
  -- Differentiate: `L(λ) ⊗ L(μ) ≅ 𝕊^λ ⊗ 𝕊^μ ≅ ⨁ 𝕊^ν ≅ ⨁ L(ν)`, the two middle modules carrying the
  -- differentials of the tensor product and of the direct sum.
  let _ := LieRingModule.compLieHom
    ((weylModuleOfShape ℂ n lam).toSubmodule ⊗[ℂ] (weylModuleOfShape ℂ n μ).toSubmodule)
    (hlam'.tprod hμ').differential
  let _ := LieRingModule.compLieHom
    (⨁ p : ι, (weylModuleOfShape ℂ n (ofPartition p.1.1)).toSubmodule)
    (IsRationalRep.directSum hν).differential
  exact ⟨((hlam'.tprodLieModuleEquiv hμ' e₁ e₂).symm.trans
    (IsRationalRep.lieModuleEquivOfEquiv (hlam'.tprod hμ') (IsRationalRep.directSum hν) φ)).trans
    (IsRationalRep.directSumLieModuleEquiv hν e)⟩

attribute [local instance 100] LieRing.ofAssociativeRing in
/-- **The Littlewood–Richardson coefficients are the tensor-product multiplicities of `𝔤𝔩ₙ`.** For
Young diagrams `λ`, `μ` and `ν` with at most `n` rows, the irreducible `𝔤𝔩ₙ(ℂ)`-module
`L(ν) = glIrreducible n ν` occurs in `L(λ) ⊗ L(μ)` with multiplicity the Littlewood–Richardson
coefficient `c^ν_{λμ} = Nat.card (LRTableau λ ν μ)`: this is the dimension of the space of
`𝔤𝔩ₙ`-module maps `L(ν) → L(λ) ⊗ L(μ)`. In particular it is zero unless `λ ⊆ ν` and
`|ν| = |λ| + |μ|`. -/
theorem isotypicMultiplicity_tensorProduct_glIrreducible {lam μ ν : YoungDiagram}
    (hlam : lam.colLen 0 ≤ n) (hμ : μ.colLen 0 ≤ n) (hν : ν.colLen 0 ≤ n) :
    LieModule.isotypicMultiplicity ℂ (Matrix (Fin n) (Fin n) ℂ)
      ((glIrreducible n fun i ↦ (lam.rowLen i : ℂ)) ⊗[ℂ]
        glIrreducible n fun i ↦ (μ.rowLen i : ℂ))
      (glIrreducible n fun i ↦ (ν.rowLen i : ℂ)) = Nat.card (LRTableau lam ν μ) := by
  classical
  have hirr (κ : YoungDiagram) :=
    isIrreducible_glIrreducible (K := ℂ) (isGlDominantIntegral_rowLen (n := n) κ)
  let _ (ν' : (lam.card + μ.card).Partition) : Fintype (LRTableau lam (ofPartition ν') μ) :=
    Fintype.ofFinite _
  -- Pass to the direct sum decomposition, where each summand `L(ν')` contributes `1` if `ν' = ν`
  -- and `0` otherwise.
  obtain ⟨e⟩ := nonempty_lieModuleEquiv_tensorProduct_glIrreducible n hlam hμ
  rw [LieModule.isotypicMultiplicity_eq_of_lieModuleEquiv e,
    LieModule.isotypicMultiplicity_directSum _ fun p ↦
      have := hirr ν
      have := hirr (ofPartition p.1.1)
      TauCeti.LieModule.finite_lieModuleHom_of_isIrreducible,
    Fintype.sum_sigma]
  have hterm (ν' : {ν' : (lam.card + μ.card).Partition // (ofPartition ν').colLen 0 ≤ n}) :
      LieModule.isotypicMultiplicity ℂ (Matrix (Fin n) (Fin n) ℂ)
          (glIrreducible n fun i ↦ ((ofPartition ν'.1).rowLen i : ℂ))
          (glIrreducible n fun i ↦ (ν.rowLen i : ℂ)) =
        if ofPartition ν'.1 = ν then 1 else 0 := by
    have := hirr ν
    have := hirr (ofPartition ν'.1)
    rw [LieModule.isotypicMultiplicity_def, TauCeti.LieModule.finrank_lieModuleHom]
    exact if_congr ((nonempty_lieModuleEquiv_glIrreducible_rowLen_iff hν ν'.2).trans eq_comm)
      rfl rfl
  simp only [hterm, sum_const, card_univ, ← Nat.card_eq_fintype_card, smul_eq_mul, mul_ite,
    mul_one, mul_zero]
  by_cases hcard : ν.card = lam.card + μ.card
  · -- Exactly one summand has shape `ν`.
    let ν₀ : {ν' : (lam.card + μ.card).Partition // (ofPartition ν').colLen 0 ≤ n} :=
      ⟨ν.toPartition hcard, by rwa [ofPartition_toPartition]⟩
    rw [Fintype.sum_eq_single ν₀ fun ν' hne ↦ ite_eq_right_iff.mpr fun h ↦ (hne (Subtype.ext
      (ofPartition_injective (h.trans (ofPartition_toPartition hcard).symm)))).elim]
    simp only [ν₀, ofPartition_toPartition hcard, ↓reduceIte]
  · -- No summand has shape `ν`, and there is no tableau of shape `ν / λ` and content `μ`.
    rw [@Nat.card_of_isEmpty _ (isEmpty_lrTableau_of_card_ne hcard)]
    refine Fintype.sum_eq_zero _ fun ν' ↦ ite_eq_right_iff.mpr fun h ↦ (hcard ?_).elim
    rw [← h, card_ofPartition]

end TauCeti
