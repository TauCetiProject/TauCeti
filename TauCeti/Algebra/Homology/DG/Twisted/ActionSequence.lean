/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.DG.Twisted.Restrict
public import Mathlib.Algebra.Homology.HomologySequenceLemmas

/-!
# Naturality of the action exact sequence under continuation maps

Let `m` be a twisting cocycle on a finite set `P` of generators, and `S ⊆ P` a set of generators
which the twisted differential never leaves, with complement `T`. The twisted complex of `m` is an
extension of the twisted complex on `T` by the twisted complex on `S`
(`TauCeti.TwistingCocycle.restrictShortComplex_shortExact`), so it has a long exact sequence in
cohomology. In Floer theory `S` is the set of generators of action `< a`, and this is the long exact
sequence `H(< a) → H → H(≥ a) → H(< a)[1]` between the parts of action below and above `a`
(`TauCeti.TwistingCocycle.actionShortComplex_shortExact`), the algebraic content of Proposition 3.45
of the reference. This file shows that the sequence is natural for continuation maps.

Let `ν : mP → mQ` be a continuation cocycle which never leaves the subcomplexes, `ν x y = 0` for
`x ∈ S` and `y ∉ S'`. Then `ν` also restricts to the quotient complexes, the twisted complexes on
the complements `T` and `T'` (`TauCeti.ContinuationCocycle.restrictQuotient`), and the projections
onto them commute with the continuation maps
(`TauCeti.ContinuationCocycle.toRestrict_continuationHom_comp`). Together with the inclusions of
the subcomplexes (`TauCeti.ContinuationCocycle.ofRestrict_continuationHom_comp`) this gives a
morphism of short exact sequences (`TauCeti.ContinuationCocycle.restrictShortComplexMap`), so the
connecting morphisms of the two long exact sequences commute with the maps induced by `ν`
(`TauCeti.ContinuationCocycle.restrictShortComplexMap_δ`). The restrictions themselves, and their
functoriality, are in `TauCeti.Algebra.Homology.DG.Twisted.Restrict`.

For action windows: if the twisted differentials do not raise the actions and `ν` raises the action
by at most `δ`, then `ν` maps the sequence at level `a` to the sequence at level `a + δ`
(`TauCeti.ContinuationCocycle.actionShortComplexMap`), through its restrictions to the generators
of action `< a` (`TauCeti.ContinuationCocycle.actionSublevel`) and of action `≥ a`
(`TauCeti.ContinuationCocycle.actionSuperlevel`), and the connecting morphisms commute with these
maps (`TauCeti.ContinuationCocycle.actionShortComplexMap_δ`). For `δ = 0`, the case of monotone
homotopies of Hamiltonians, the long exact sequence between the zero-energy and positive-energy
parts is therefore natural in the continuation maps along which symplectic homology is the direct
limit over the slopes. A parametrized cocycle which raises the action by at most `δ` makes the
maps on the parts below and above the action level homotopic
(`TauCeti.ParametrizedCocycle.homologyMap_actionSublevel_eq`,
`TauCeti.ParametrizedCocycle.homologyMap_actionSuperlevel_eq`).

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, §3, Propositions 3.22 and 3.45.
-/

public section

open CategoryTheory

namespace TauCeti

universe uR uA uM uP

/-! ### The morphism of short exact sequences -/

section ShortComplexMap

variable {R : Type uR} {A : Type uA} {M : Type uM}
  [CommRing R] [Ring A] [Algebra R A] [AddCommGroup M] [Module R M]
  {P Q : Type uP} {ind : P → ℤ} {indQ : Q → ℤ} [Fintype P] [Fintype Q]
  [DecidableEq P] [DecidableEq Q]
  [Module Aᵐᵒᵖ M] [IsScalarTower R Aᵐᵒᵖ M] [SMulCommClass R Aᵐᵒᵖ M]
  {𝒜 : ℤ → Submodule R A} [GradedAlgebra 𝒜] {d : A →ₗ[R] A} (h : IsDGAlgebra 𝒜 d)
  {ℳ : ℤ → Submodule R M} [DirectSum.Decomposition ℳ]
  [SetLike.GradedSMul (InternalGrading.ofDecomposition 𝒜).opposite.piece ℳ] {dM : M →ₗ[R] M}
  (hM : IsDGRightModule h ℳ dM)
  {mP : TwistingCocycle 𝒜 d P ind} {mQ : TwistingCocycle 𝒜 d Q indQ}
  (ν : ContinuationCocycle mP mQ)

namespace ContinuationCocycle

variable (S T : Set P) [DecidablePred (· ∈ S)] [DecidablePred (· ∈ T)]
  (hS : ∀ x y, x ∈ S → y ∉ S → mP.m x y = 0) (hST : ∀ x, x ∈ T ↔ x ∉ S)
  (S' T' : Set Q) [DecidablePred (· ∈ S')] [DecidablePred (· ∈ T')]
  (hS' : ∀ x y, x ∈ S' → y ∉ S' → mQ.m x y = 0) (hST' : ∀ x, x ∈ T' ↔ x ∉ S')
  (hν : ∀ x y, x ∈ S → y ∉ S' → ν.ν x y = 0)

/-- **The morphism of short exact sequences of a continuation cocycle.** If `ν` never leaves the
subcomplexes of `S` and `S'`, its restriction to them, its continuation morphism and its
restriction to the quotient complexes of their complements form a morphism from the short exact
sequence of the subcomplex of `S` to that of the subcomplex of `S'`. -/
noncomputable def restrictShortComplexMap :
    mP.restrictShortComplex hM S T hS hST ⟶ mQ.restrictShortComplex hM S' T' hS' hST' where
  τ₁ := (ν.restrictSubcomplex S hS S' hS' hν).continuationHom hM
  τ₂ := ν.continuationHom hM
  τ₃ := (ν.restrictQuotient T (mP.forall_eq_zero_of_compl hS hST) T'
    (mQ.forall_eq_zero_of_compl hS' hST')
    (ν.forall_eq_zero_of_compl hν hST hST')).continuationHom hM
  comm₁₂ := (ν.ofRestrict_continuationHom_comp h S hS S' hS' hν hM).symm
  comm₂₃ := (ν.toRestrict_continuationHom_comp h hM T _ T' _ _).symm

@[simp]
theorem restrictShortComplexMap_τ₁ :
    (ν.restrictShortComplexMap h hM S T hS hST S' T' hS' hST' hν).τ₁ =
      (ν.restrictSubcomplex S hS S' hS' hν).continuationHom hM :=
  (rfl)

@[simp]
theorem restrictShortComplexMap_τ₂ :
    (ν.restrictShortComplexMap h hM S T hS hST S' T' hS' hST' hν).τ₂ = ν.continuationHom hM :=
  (rfl)

@[simp]
theorem restrictShortComplexMap_τ₃ :
    (ν.restrictShortComplexMap h hM S T hS hST S' T' hS' hST' hν).τ₃ =
      (ν.restrictQuotient T (mP.forall_eq_zero_of_compl hS hST) T'
        (mQ.forall_eq_zero_of_compl hS' hST')
        (ν.forall_eq_zero_of_compl hν hST hST')).continuationHom hM :=
  (rfl)

/-- **The connecting morphisms are natural in the continuation cocycle.** If `ν` never leaves the
subcomplexes of `S` and `S'`, the connecting morphisms `H^i(T) ⟶ H^(i+1)(S)` and
`H^i(T') ⟶ H^(i+1)(S')` of the two long exact sequences commute with the maps induced by the
restrictions of `ν`. -/
@[reassoc]
theorem restrictShortComplexMap_δ (i j : ℤ) (hij : i + 1 = j) :
    (mP.restrictShortComplex_shortExact hM S T hS hST).δ i j hij ≫
        HomologicalComplex.homologyMap ((ν.restrictSubcomplex S hS S' hS' hν).continuationHom hM)
          j =
      HomologicalComplex.homologyMap ((ν.restrictQuotient T (mP.forall_eq_zero_of_compl hS hST) T'
          (mQ.forall_eq_zero_of_compl hS' hST')
          (ν.forall_eq_zero_of_compl hν hST hST')).continuationHom hM) i ≫
        (mQ.restrictShortComplex_shortExact hM S' T' hS' hST').δ i j hij :=
  HomologicalComplex.HomologySequence.δ_naturality
    (ν.restrictShortComplexMap h hM S T hS hST S' T' hS' hST' hν) _ _ i j hij

end ContinuationCocycle

end ShortComplexMap

/-! ### Action windows -/

section ActionShortComplexMap

variable {R : Type uR} {A : Type uA} {M : Type uM}
  [CommRing R] [Ring A] [Algebra R A] [AddCommGroup M] [Module R M]
  {P Q : Type uP} {ind : P → ℤ} {indQ : Q → ℤ} [Fintype P] [Fintype Q]
  [DecidableEq P] [DecidableEq Q]
  [Module Aᵐᵒᵖ M] [IsScalarTower R Aᵐᵒᵖ M] [SMulCommClass R Aᵐᵒᵖ M]
  {𝒜 : ℤ → Submodule R A} [GradedAlgebra 𝒜] {d : A →ₗ[R] A} (h : IsDGAlgebra 𝒜 d)
  {ℳ : ℤ → Submodule R M} [DirectSum.Decomposition ℳ]
  [SetLike.GradedSMul (InternalGrading.ofDecomposition 𝒜).opposite.piece ℳ] {dM : M →ₗ[R] M}
  (hM : IsDGRightModule h ℳ dM)
  {Γ : Type*} [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]
  {mP : TwistingCocycle 𝒜 d P ind} {mQ : TwistingCocycle 𝒜 d Q indQ}
  {actP : P → Γ} {actQ : Q → Γ}
  (hmP : ∀ x y, actP x < actP y → mP.m x y = 0) (hmQ : ∀ x y, actQ x < actQ y → mQ.m x y = 0)
  {δ : Γ} (a : Γ)

namespace ContinuationCocycle

variable (ν : ContinuationCocycle mP mQ) (hν : ∀ x y, actP x + δ < actQ y → ν.ν x y = 0)

/-- **The morphism of action exact sequences of a continuation map.** If the twisted differentials
of `mP` and `mQ` do not raise the actions and the continuation cocycle `ν` raises the action by at
most `δ`, then its action sublevel, its continuation morphism and its action superlevel form a
morphism from the action short exact sequence of `mP` at level `a` to that of `mQ` at level
`a + δ`. -/
noncomputable def actionShortComplexMap :
    mP.actionShortComplex hmP hM a ⟶ mQ.actionShortComplex hmQ hM (a + δ) :=
  ν.restrictShortComplexMap h hM _ _ _ _ _ _ _ _ (ν.ν_eq_zero_of_mem_setOf_lt hν)

@[simp]
theorem actionShortComplexMap_τ₁ :
    (ν.actionShortComplexMap h hM hmP hmQ a hν).τ₁ =
      (ν.actionSublevel hmP hmQ hν a).continuationHom hM :=
  (rfl)

@[simp]
theorem actionShortComplexMap_τ₂ :
    (ν.actionShortComplexMap h hM hmP hmQ a hν).τ₂ = ν.continuationHom hM :=
  (rfl)

@[simp]
theorem actionShortComplexMap_τ₃ :
    (ν.actionShortComplexMap h hM hmP hmQ a hν).τ₃ =
      (ν.actionSuperlevel hmP hmQ hν a).continuationHom hM :=
  (rfl)

/-- **Naturality of the action long exact sequence.** If the twisted differentials do not raise
the actions and the continuation cocycle `ν` raises the action by at most `δ`, the connecting
morphisms `H^i(≥ a) ⟶ H^(i+1)(< a)` of `mP` and `H^i(≥ a + δ) ⟶ H^(i+1)(< a + δ)` of `mQ`
commute with the maps induced by the action superlevel and the action sublevel of `ν`. -/
@[reassoc]
theorem actionShortComplexMap_δ (i j : ℤ) (hij : i + 1 = j) :
    (mP.actionShortComplex_shortExact hmP hM a).δ i j hij ≫
        HomologicalComplex.homologyMap ((ν.actionSublevel hmP hmQ hν a).continuationHom hM) j =
      HomologicalComplex.homologyMap ((ν.actionSuperlevel hmP hmQ hν a).continuationHom hM) i ≫
        (mQ.actionShortComplex_shortExact hmQ hM (a + δ)).δ i j hij :=
  HomologicalComplex.HomologySequence.δ_naturality (ν.actionShortComplexMap h hM hmP hmQ a hν)
    _ _ i j hij

end ContinuationCocycle

namespace ParametrizedCocycle

variable {ν₀ ν₁ : ContinuationCocycle mP mQ}
  (hν₀ : ∀ x y, actP x + δ < actQ y → ν₀.ν x y = 0)
  (hν₁ : ∀ x y, actP x + δ < actQ y → ν₁.ν x y = 0) (η : ParametrizedCocycle ν₀ ν₁)
  (hη : ∀ x y, actP x + δ < actQ y → η.h x y = 0)
include η hη

omit [DecidableEq P] [DecidableEq Q] in
/-- **Homotopic continuation maps agree below the action level.** A parametrized cocycle between
`ν₀` and `ν₁` which raises the action by at most `δ` makes their action sublevels induce the same
map from the cohomology of the generators of action `< a` to that of the generators of action
`< a + δ`. -/
theorem homologyMap_actionSublevel_eq (n : ℤ) :
    HomologicalComplex.homologyMap ((ν₀.actionSublevel hmP hmQ hν₀ a).continuationHom hM) n =
      HomologicalComplex.homologyMap ((ν₁.actionSublevel hmP hmQ hν₁ a).continuationHom hM) n :=
  (((η.actionSublevel hmP hmQ hν₀ hν₁ hη a).homotopy hM).homologyMap_eq n).symm

omit [DecidableEq P] [DecidableEq Q] in
/-- **Homotopic continuation maps agree above the action level.** A parametrized cocycle between
`ν₀` and `ν₁` which raises the action by at most `δ` makes their action superlevels induce the same
map from the cohomology of the generators of action `≥ a` to that of the generators of action
`≥ a + δ`. -/
theorem homologyMap_actionSuperlevel_eq (n : ℤ) :
    HomologicalComplex.homologyMap ((ν₀.actionSuperlevel hmP hmQ hν₀ a).continuationHom hM) n =
      HomologicalComplex.homologyMap
        ((ν₁.actionSuperlevel hmP hmQ hν₁ a).continuationHom hM) n :=
  (((η.actionSuperlevel hmP hmQ hν₀ hν₁ hη a).homotopy hM).homologyMap_eq n).symm

end ParametrizedCocycle

end ActionShortComplexMap

end TauCeti
