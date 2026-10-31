/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.ClassicalGroups.Branching.Rational
public import TauCeti.RepresentationTheory.ClassicalGroups.Branching.Rationality
public import TauCeti.RepresentationTheory.ClassicalGroups.UnitaryTrick
public import TauCeti.RepresentationTheory.ClassicalGroups.WeylModule.Rationality
public import TauCeti.RepresentationTheory.Rep.DirectSum.Character

/-!
# The branching rule from `GL (n + 1) ℂ` to `GL n ℂ`

Restrict an irreducible rational representation `V_λ` of `GL (n + 1) ℂ` along the block inclusion
`TauCeti.glBlockSucc : GL n ℂ →* GL (n + 1) ℂ`, `g ↦ diag(g, 1)`. The **branching rule** says that
the restriction is multiplicity free,

`V_λ|_{GL n} ≅ ⨁_{μ ≺ λ} V_μ`,

the sum running over the dominant weights `μ` of `GL n` interlacing `λ`
(`λᵢ ≥ μᵢ ≥ λᵢ₊₁`, `TauCeti.interlacingWeights`), each once. This file proves it as an
equivalence of representations (`TauCeti.nonempty_equiv_rationalWeylRep_comp_glBlockSucc`), and
in the polynomial form for the Weyl module of a Young diagram
(`TauCeti.nonempty_equiv_weylRepOfShape_comp_glBlockSucc`), where the sum runs over the diagrams
interlacing the given one with at most `n` rows.

Both sides are rational representations of `GL n ℂ`: the restriction by
`TauCeti.IsRationalRep.comp_glBlockSucc`, the direct sum by `TauCeti.IsRationalRep.directSum`.
Their characters agree on the diagonal torus by the branching rule for characters
(`TauCeti.char_rationalWeylRep_glBlockSucc_diagGL` and
`TauCeti.char_weylRepOfShape_glBlockSucc_diagGL`), and rational representations with equal
characters on the diagonal torus are equivalent
(`TauCeti.IsRationalRep.nonempty_equiv_of_forall_character_diagGL_eq`).

## Main results

* `TauCeti.nonempty_equiv_rationalWeylRep_comp_glBlockSucc`: **the branching rule** for the
  rational Weyl modules, indexed by dominant weights.
* `TauCeti.nonempty_equiv_weylRepOfShape_comp_glBlockSucc`: the branching rule for the polynomial
  Weyl modules, indexed by Young diagrams.

Both are equivalences of representations; `TauCeti.nonempty_fdRepIso_iff` reads them as
isomorphisms of the corresponding objects of `FDRep ℂ (GL (Fin n) ℂ)`.

## References

* W. Fulton and J. Harris, *Representation Theory: A First Course* (1991), Lecture 15.
* R. Goodman and N. R. Wallach, *Symmetry, Representations, and Invariants* (2009), Section 8.1:
  the branching law from `GL n` to `GL (n - 1)`.
-/

public section

namespace TauCeti

variable (n : ℕ)

/-- **The branching rule from `GL (n + 1) ℂ` to `GL n ℂ`.** The rational Weyl module `V_λ` of a
dominant weight `λ` of `GL (n + 1)`, restricted along the block inclusion `g ↦ diag(g, 1)`, is the
direct sum of the rational Weyl modules `V_μ` of the dominant weights `μ` of `GL n` interlacing
`λ`, each occurring once. -/
theorem nonempty_equiv_rationalWeylRep_comp_glBlockSucc (l : DominantWeight (n + 1)) :
    Nonempty (Representation.Equiv ((rationalWeylRep ℂ (n + 1) l).comp (glBlockSucc ℂ n))
      (Representation.directSum fun m : interlacingWeights l => rationalWeylRep ℂ n m)) := by
  -- Instance search does not find the additive groups of the summands under the binder of the
  -- direct sum, through the tensor power they are submodules of, so they are supplied here.
  let _ (m : interlacingWeights l) :
      AddCommGroup (weylModuleOfShape ℂ n (m : DominantWeight n).detShiftShape).toSubmodule :=
    inferInstance
  refine IsRationalRep.nonempty_equiv_of_forall_character_diagGL_eq
    (W := (weylModuleOfShape ℂ (n + 1) l.detShiftShape).toSubmodule)
    (isRationalRep_rationalWeylRep_comp_glBlockSucc n l)
    (IsRationalRep.directSum fun m => isRationalRep_rationalWeylRep n m) fun t => ?_
  rw [Representation.char_directSum]
  exact (char_rationalWeylRep_glBlockSucc_diagGL ℂ n l t).trans
    (Finset.sum_coe_sort (interlacingWeights l) _).symm

/-- **The branching rule for polynomial representations.** The Weyl module of a Young diagram `μ`
for `GL (n + 1) ℂ`, restricted along the block inclusion `g ↦ diag(g, 1)`, is the direct sum of the
Weyl modules for `GL n ℂ` of the diagrams with at most `n` rows interlacing `μ`, each occurring
once. -/
theorem nonempty_equiv_weylRepOfShape_comp_glBlockSucc (μ : YoungDiagram) :
    Nonempty (Representation.Equiv ((weylRepOfShape ℂ (n + 1) μ).comp (glBlockSucc ℂ n))
      (Representation.directSum fun ν : YoungDiagram.interlacingShapes n μ =>
        weylRepOfShape ℂ n ν)) := by
  -- The additive groups of the summands are supplied as in
  -- `TauCeti.nonempty_equiv_rationalWeylRep_comp_glBlockSucc`.
  let _ (ν : YoungDiagram.interlacingShapes n μ) :
      AddCommGroup (weylModuleOfShape ℂ n (ν : YoungDiagram)).toSubmodule :=
    inferInstance
  refine IsRationalRep.nonempty_equiv_of_forall_character_diagGL_eq
    (W := (weylModuleOfShape ℂ (n + 1) μ).toSubmodule)
    (isPolynomialRep_weylRepOfShape (n + 1) μ).isRationalRep.comp_glBlockSucc
    (IsRationalRep.directSum fun ν => (isPolynomialRep_weylRepOfShape n ν).isRationalRep)
    fun t => ?_
  rw [Representation.char_directSum]
  exact (char_weylRepOfShape_glBlockSucc_diagGL ℂ n μ t).trans
    (Finset.sum_coe_sort (YoungDiagram.interlacingShapes n μ) _).symm

end TauCeti
