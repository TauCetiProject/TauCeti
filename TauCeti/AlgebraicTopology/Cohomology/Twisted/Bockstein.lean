/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.HomologySequenceLemmas
public import TauCeti.AlgebraicTopology.Cohomology.Twisted.Basic

/-!
# The long exact sequence of twisted cohomology in the module of values

Let `L` be a local coefficient system of `R`-modules on a space `X` whose fibres are projective,
and let `0 ⟶ M₁ ⟶ M₂ ⟶ M₃ ⟶ 0` be a short exact sequence of `R`-modules. The twisted singular
`n`-chains of `X` are the coproduct of the fibres of `L` at the initial vertices of the singular
`n`-simplices, so they are projective
(`TauCeti.LocalCoefficientSystem.projective_twistedChainComplex_X`) and `Hom(C(X; L), -)` is
exact. This gives a short exact sequence of twisted cochain complexes

`0 ⟶ Hom(C(X; L), M₁) ⟶ Hom(C(X; L), M₂) ⟶ Hom(C(X; L), M₃) ⟶ 0`,

whose connecting morphism is the Bockstein homomorphism `Hⁿ(X; L, M₃) ⟶ Hⁿ⁺¹(X; L, M₁)` of twisted
cohomology, and whose long exact cohomology sequence is the long exact sequence of twisted
cohomology in the module of values. It is the twisted counterpart of the coefficient long exact
sequence of ordinary singular cohomology (`TopCat.singularCohomologyBockstein`).

The projectivity hypothesis cannot be dropped: over a point, the twisted chains in each degree are
the single fibre `F` of `L`, and `Hom(F, -)` is exact only for projective `F`.

## Main declarations

* `TauCeti.LocalCoefficientSystem.twistedCochainComplexValueShortComplex` and
  `TauCeti.LocalCoefficientSystem.shortExact_twistedCochainComplexValueShortComplex`: the short
  exact sequence of twisted cochain complexes induced by a short exact sequence of modules of
  values.
* `TauCeti.LocalCoefficientSystem.twistedCohomologyBockstein`: the Bockstein homomorphism
  `Hⁿ(X; L, M₃) ⟶ Hᵐ(X; L, M₁)` for `n + 1 = m`, with the exactness statements
  `TauCeti.LocalCoefficientSystem.twistedCohomology_exact_value₁`, `twistedCohomology_exact_value₂`
  and `twistedCohomology_exact_value₃`, and its naturality in morphisms of short exact sequences
  `TauCeti.LocalCoefficientSystem.twistedCohomologyBockstein_naturality_values`.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Sections 3.E and 3.H.
-/

public section

noncomputable section

open CategoryTheory

universe u v w

namespace TauCeti

namespace LocalCoefficientSystem

variable {R : Type u} [Ring R] (k : Type*) [Ring k] [Linear k (ModuleCat.{max v w} R)]
  {X : TopCat.{v}} (L : LocalCoefficientSystem.{u, v, max v w} R X)

/-- The sequence of twisted cochain complexes
`Hom(C(X; L), S.X₁) ⟶ Hom(C(X; L), S.X₂) ⟶ Hom(C(X; L), S.X₃)` induced by a short complex `S` of
modules of values: its maps are postcomposition with the maps of `S`. -/
abbrev twistedCochainComplexValueShortComplex (S : ShortComplex (ModuleCat.{max v w} R)) :
    ShortComplex (CochainComplex (ModuleCat.{max v w} k) ℕ) :=
  S.map (L.twistedChainComplex.linearYonedaObjFunctor k)

variable [∀ x, Projective (L.obj x)] {S : ShortComplex (ModuleCat.{max v w} R)}
  (hS : S.ShortExact)

include hS in
/-- If the fibres of `L` are projective, a short exact sequence `0 ⟶ M₁ ⟶ M₂ ⟶ M₃ ⟶ 0` of modules
of values induces a short exact sequence of twisted cochain complexes. -/
lemma shortExact_twistedCochainComplexValueShortComplex :
    (L.twistedCochainComplexValueShortComplex k S).ShortExact :=
  L.twistedChainComplex.shortExact_map_linearYonedaObjFunctor k hS

include hS in
/-- The Bockstein homomorphism `Hⁿ(X; L, M₃) ⟶ Hᵐ(X; L, M₁)`, for `n + 1 = m`, of a short exact
sequence `0 ⟶ M₁ ⟶ M₂ ⟶ M₃ ⟶ 0` of modules of values, when the fibres of `L` are projective: the
connecting morphism of the long exact cohomology sequence of the short exact sequence of twisted
cochain complexes. -/
def twistedCohomologyBockstein (n m : ℕ) (h : n + 1 = m := by lia) :
    L.twistedCohomology k S.X₃ n ⟶ L.twistedCohomology k S.X₁ m :=
  (L.shortExact_twistedCochainComplexValueShortComplex k hS).δ n m (by simpa)

/-- The Bockstein homomorphism is, by definition, the connecting morphism of the short exact
sequence of twisted cochain complexes. -/
lemma twistedCohomologyBockstein_eq_δ (n m : ℕ) (h : n + 1 = m := by lia) :
    L.twistedCohomologyBockstein k hS n m h =
      (L.shortExact_twistedCochainComplexValueShortComplex k hS).δ n m (by simpa) :=
  (rfl)

section Exactness

@[reassoc (attr := simp)]
lemma comp_twistedCohomologyBockstein (n m : ℕ) (h : n + 1 = m := by lia) :
    HomologicalComplex.homologyMap (L.twistedChainComplex.linearYonedaObjMap k S.g) n ≫
      L.twistedCohomologyBockstein k hS n m h = 0 :=
  (L.shortExact_twistedCochainComplexValueShortComplex k hS).comp_δ n m (by simpa)

@[reassoc (attr := simp)]
lemma twistedCohomologyBockstein_comp (n m : ℕ) (h : n + 1 = m := by lia) :
    L.twistedCohomologyBockstein k hS n m h ≫
      HomologicalComplex.homologyMap (L.twistedChainComplex.linearYonedaObjMap k S.f) m = 0 :=
  (L.shortExact_twistedCochainComplexValueShortComplex k hS).δ_comp n m (by simpa)

/-- Exactness at `Hᵐ(X; L, M₁)`: `Hⁿ(X; L, M₃) ⟶ Hᵐ(X; L, M₁) ⟶ Hᵐ(X; L, M₂)` is exact for
`n + 1 = m`. -/
lemma twistedCohomology_exact_value₁ (n m : ℕ) (h : n + 1 = m := by lia) :
    (ShortComplex.mk _ _ (L.twistedCohomologyBockstein_comp k hS n m h)).Exact :=
  (L.shortExact_twistedCochainComplexValueShortComplex k hS).homology_exact₁ n m (by simpa)

include hS in
/-- Exactness at `Hⁿ(X; L, M₂)`: `Hⁿ(X; L, M₁) ⟶ Hⁿ(X; L, M₂) ⟶ Hⁿ(X; L, M₃)` is exact. -/
lemma twistedCohomology_exact_value₂ (n : ℕ) :
    ((L.twistedCochainComplexValueShortComplex k S).map
      (HomologicalComplex.homologyFunctor _ _ n)).Exact :=
  (L.shortExact_twistedCochainComplexValueShortComplex k hS).homology_exact₂ n

/-- Exactness at `Hⁿ(X; L, M₃)`: `Hⁿ(X; L, M₂) ⟶ Hⁿ(X; L, M₃) ⟶ Hᵐ(X; L, M₁)` is exact for
`n + 1 = m`. -/
lemma twistedCohomology_exact_value₃ (n m : ℕ) (h : n + 1 = m := by lia) :
    (ShortComplex.mk _ _ (L.comp_twistedCohomologyBockstein k hS n m h)).Exact :=
  (L.shortExact_twistedCochainComplexValueShortComplex k hS).homology_exact₃ n m (by simpa)

end Exactness

/-- The Bockstein homomorphism is natural in the short exact sequence of modules of values: a
morphism `φ : S ⟶ S'` of short exact sequences commutes with the Bockstein homomorphisms of `S`
and `S'` and the maps on twisted cohomology given by postcomposition with its components. -/
@[reassoc]
lemma twistedCohomologyBockstein_naturality_values {S' : ShortComplex (ModuleCat.{max v w} R)}
    (hS' : S'.ShortExact) (φ : S ⟶ S') (n m : ℕ) (h : n + 1 = m := by lia) :
    L.twistedCohomologyBockstein k hS n m h ≫
        HomologicalComplex.homologyMap (L.twistedChainComplex.linearYonedaObjMap k φ.τ₁) m =
      HomologicalComplex.homologyMap (L.twistedChainComplex.linearYonedaObjMap k φ.τ₃) n ≫
        L.twistedCohomologyBockstein k hS' n m h :=
  HomologicalComplex.HomologySequence.δ_naturality
    ((L.twistedChainComplex.linearYonedaObjFunctor k).mapShortComplex.map φ)
    (L.shortExact_twistedCochainComplexValueShortComplex k hS)
    (L.shortExact_twistedCochainComplexValueShortComplex k hS') n m (by simpa)

end LocalCoefficientSystem

end TauCeti
