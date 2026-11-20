/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.DG.Twisted.Homotopy
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
(`TauCeti.ContinuationCocycle.restrictShortComplexMap_δ`).

Both restrictions are functorial: they send the Kronecker cocycle to the Kronecker cocycle and
composites to composites (`TauCeti.ContinuationCocycle.restrictSubcomplex_comp`,
`TauCeti.ContinuationCocycle.restrictQuotient_comp`). A parametrized cocycle between two such
continuation cocycles which itself never leaves the subcomplexes restricts to both
(`TauCeti.ParametrizedCocycle.restrictSubcomplex`,
`TauCeti.ParametrizedCocycle.restrictQuotient`), so the maps induced on the cohomology of the
subcomplexes and of the quotients depend only on the homotopy class of the continuation cocycle in
this sense.

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

/-! ### Restriction of continuation cocycles to quotient complexes -/

section Cocycle

variable {R : Type uR} {A : Type uA} [CommRing R] [Ring A] [Algebra R A]
  {P Q W : Type uP} {ind : P → ℤ} {indQ : Q → ℤ} {indW : W → ℤ} [Fintype P] [Fintype Q]
  [Fintype W] {𝒜 : ℤ → Submodule R A} {d : A →ₗ[R] A}
  {mP : TwistingCocycle 𝒜 d P ind} {mQ : TwistingCocycle 𝒜 d Q indQ}
  {mW : TwistingCocycle 𝒜 d W indW}

namespace ContinuationCocycle

/-- The **restriction of a continuation cocycle to quotient complexes.** For sets `T ⊆ P` and
`T' ⊆ Q` of generators which the twisted differentials never enter from outside, and a
continuation cocycle `ν : mP → mQ` which never enters `T'` from outside `T`, `ν x y = 0` for
`x ∉ T` and `y ∈ T'`, the entries of `ν` from `T` to `T'` form a continuation cocycle between the
restrictions of `mP` and `mQ` to `T` and `T'`. -/
def restrictQuotient (ν : ContinuationCocycle mP mQ) (T : Set P) [DecidablePred (· ∈ T)]
    (hT : ∀ x y, x ∉ T → y ∈ T → mP.m x y = 0) (T' : Set Q) [DecidablePred (· ∈ T')]
    (hT' : ∀ x y, x ∉ T' → y ∈ T' → mQ.m x y = 0)
    (hν : ∀ x y, x ∉ T → y ∈ T' → ν.ν x y = 0) :
    ContinuationCocycle (mP.restrict T (mP.mul_eq_zero_of_forall_eq_zero' hT))
      (mQ.restrict T' (mQ.mul_eq_zero_of_forall_eq_zero' hT')) :=
  ν.restrict T _ T' _ (fun _ z y _ hz hy ↦ by rw [hν z y hz hy, mul_zero])
    (fun _ z y _ hz hy ↦ by rw [hT' z y hz hy, mul_zero])

@[simp]
theorem restrictQuotient_ν (ν : ContinuationCocycle mP mQ) (T : Set P) [DecidablePred (· ∈ T)]
    (hT : ∀ x y, x ∉ T → y ∈ T → mP.m x y = 0) (T' : Set Q) [DecidablePred (· ∈ T')]
    (hT' : ∀ x y, x ∉ T' → y ∈ T' → mQ.m x y = 0)
    (hν : ∀ x y, x ∉ T → y ∈ T' → ν.ν x y = 0) (x : T) (y : T') :
    (ν.restrictQuotient T hT T' hT' hν).ν x y = ν.ν x y :=
  ν.restrict_ν T _ T' _ _ _ x y

/-- If `ν` never leaves the subcomplexes of `S` and `S'`, it never enters their complements `T` and
`T'` from outside. -/
theorem forall_eq_zero_of_compl (ν : ContinuationCocycle mP mQ) {S T : Set P} {S' T' : Set Q}
    (hν : ∀ x y, x ∈ S → y ∉ S' → ν.ν x y = 0) (hST : ∀ x, x ∈ T ↔ x ∉ S)
    (hST' : ∀ x, x ∈ T' ↔ x ∉ S') : ∀ x y, x ∉ T → y ∈ T' → ν.ν x y = 0 :=
  fun x y hx hy ↦ hν x y (not_not.1 ((hST x).not.1 hx)) ((hST' y).1 hy)

variable [GradedAlgebra 𝒜] (h : IsDGAlgebra 𝒜 d)

/-- If `ν₁` never leaves the subcomplexes of `S₁` and `S₂` and `ν₂` those of `S₂` and `S₃`, then
their composite never leaves the subcomplexes of `S₁` and `S₃`. -/
theorem comp_ν_eq_zero_of_forall_eq_zero (ν₁ : ContinuationCocycle mP mQ)
    (ν₂ : ContinuationCocycle mQ mW) {S₁ : Set P} {S₂ : Set Q} {S₃ : Set W}
    (hν₁ : ∀ x y, x ∈ S₁ → y ∉ S₂ → ν₁.ν x y = 0) (hν₂ : ∀ x y, x ∈ S₂ → y ∉ S₃ → ν₂.ν x y = 0) :
    ∀ x y, x ∈ S₁ → y ∉ S₃ → (ν₁.comp h ν₂).ν x y = 0 := by
  intro x y hx hy
  rw [comp_ν, Matrix.mul_apply]
  refine Finset.sum_eq_zero fun z _ ↦ ?_
  by_cases hz : z ∈ S₂
  · simp [hν₂ z y hz hy]
  · simp [hν₁ x z hx hz]

/-- The restriction of the Kronecker cocycle to a subcomplex is the Kronecker cocycle. -/
@[simp]
theorem restrictSubcomplex_refl [DecidableEq P] (S : Set P) [DecidablePred (· ∈ S)]
    (hS : ∀ x y, x ∈ S → y ∉ S → mP.m x y = 0)
    (hν : ∀ x y, x ∈ S → y ∉ S → (refl h.map_one_eq_zero mP).ν x y = 0) :
    (refl h.map_one_eq_zero mP).restrictSubcomplex S hS S hS hν = refl h.map_one_eq_zero _ := by
  ext x y
  simp [Matrix.one_apply, Subtype.ext_iff]

/-- The restriction of the Kronecker cocycle to a quotient complex is the Kronecker cocycle. -/
@[simp]
theorem restrictQuotient_refl [DecidableEq P] (T : Set P) [DecidablePred (· ∈ T)]
    (hT : ∀ x y, x ∉ T → y ∈ T → mP.m x y = 0)
    (hν : ∀ x y, x ∉ T → y ∈ T → (refl h.map_one_eq_zero mP).ν x y = 0) :
    (refl h.map_one_eq_zero mP).restrictQuotient T hT T hT hν = refl h.map_one_eq_zero _ := by
  ext x y
  simp [Matrix.one_apply, Subtype.ext_iff]

/-- **Restriction to subcomplexes is functorial**: the restriction of a composite is the composite
of the restrictions. -/
theorem restrictSubcomplex_comp (ν₁ : ContinuationCocycle mP mQ) (ν₂ : ContinuationCocycle mQ mW)
    (S₁ : Set P) [DecidablePred (· ∈ S₁)] (hS₁ : ∀ x y, x ∈ S₁ → y ∉ S₁ → mP.m x y = 0)
    (S₂ : Set Q) [DecidablePred (· ∈ S₂)] (hS₂ : ∀ x y, x ∈ S₂ → y ∉ S₂ → mQ.m x y = 0)
    (S₃ : Set W) [DecidablePred (· ∈ S₃)] (hS₃ : ∀ x y, x ∈ S₃ → y ∉ S₃ → mW.m x y = 0)
    (hν₁ : ∀ x y, x ∈ S₁ → y ∉ S₂ → ν₁.ν x y = 0) (hν₂ : ∀ x y, x ∈ S₂ → y ∉ S₃ → ν₂.ν x y = 0)
    (hν : ∀ x y, x ∈ S₁ → y ∉ S₃ → (ν₁.comp h ν₂).ν x y = 0) :
    (ν₁.comp h ν₂).restrictSubcomplex S₁ hS₁ S₃ hS₃ hν =
      (ν₁.restrictSubcomplex S₁ hS₁ S₂ hS₂ hν₁).comp h
        (ν₂.restrictSubcomplex S₂ hS₂ S₃ hS₃ hν₂) := by
  ext x y
  simp only [restrictSubcomplex_ν, comp_ν, Matrix.mul_apply, Matrix.of_apply]
  -- The intermediate generators outside `S₂` contribute nothing, since `ν₁` never leaves `S₂`.
  exact Finset.sum_congr_set S₂ _ _ (fun _ _ ↦ rfl) fun z hz ↦ by rw [hν₁ x z x.2 hz, zero_mul]

/-- **Restriction to quotient complexes is functorial**: the restriction of a composite is the
composite of the restrictions. -/
theorem restrictQuotient_comp (ν₁ : ContinuationCocycle mP mQ) (ν₂ : ContinuationCocycle mQ mW)
    (T₁ : Set P) [DecidablePred (· ∈ T₁)] (hT₁ : ∀ x y, x ∉ T₁ → y ∈ T₁ → mP.m x y = 0)
    (T₂ : Set Q) [DecidablePred (· ∈ T₂)] (hT₂ : ∀ x y, x ∉ T₂ → y ∈ T₂ → mQ.m x y = 0)
    (T₃ : Set W) [DecidablePred (· ∈ T₃)] (hT₃ : ∀ x y, x ∉ T₃ → y ∈ T₃ → mW.m x y = 0)
    (hν₁ : ∀ x y, x ∉ T₁ → y ∈ T₂ → ν₁.ν x y = 0) (hν₂ : ∀ x y, x ∉ T₂ → y ∈ T₃ → ν₂.ν x y = 0)
    (hν : ∀ x y, x ∉ T₁ → y ∈ T₃ → (ν₁.comp h ν₂).ν x y = 0) :
    (ν₁.comp h ν₂).restrictQuotient T₁ hT₁ T₃ hT₃ hν =
      (ν₁.restrictQuotient T₁ hT₁ T₂ hT₂ hν₁).comp h
        (ν₂.restrictQuotient T₂ hT₂ T₃ hT₃ hν₂) := by
  ext x y
  simp only [restrictQuotient_ν, comp_ν, Matrix.mul_apply, Matrix.of_apply]
  -- The intermediate generators outside `T₂` contribute nothing, since `ν₂` never enters `T₃`
  -- from outside `T₂`.
  exact Finset.sum_congr_set T₂ _ _ (fun _ _ ↦ rfl) fun z hz ↦ by rw [hν₂ z y hz y.2, mul_zero]

variable [DecidableEq P] [DecidableEq Q]

/-- **Continuation maps commute with the projections onto quotient complexes.** If `ν` never
enters `T'` from outside `T`, the projection onto the quotient complex of `T` followed by the
restriction of `ν` is `ν` followed by the projection onto the quotient complex of `T'`. -/
theorem toRestrict_comp (ν : ContinuationCocycle mP mQ) (T : Set P) [DecidablePred (· ∈ T)]
    (hT : ∀ x y, x ∉ T → y ∈ T → mP.m x y = 0) (T' : Set Q) [DecidablePred (· ∈ T')]
    (hT' : ∀ x y, x ∉ T' → y ∈ T' → mQ.m x y = 0)
    (hν : ∀ x y, x ∉ T → y ∈ T' → ν.ν x y = 0) :
    (toRestrict mP h.map_one_eq_zero T hT).comp h (ν.restrictQuotient T hT T' hT' hν) =
      ν.comp h (toRestrict mQ h.map_one_eq_zero T' hT') := by
  ext x y
  simp only [comp_ν, Matrix.mul_apply, Matrix.of_apply, toRestrict_ν, restrictQuotient_ν]
  rw [Finset.sum_eq_single_of_mem (y : Q) (Finset.mem_univ _) fun z _ hz ↦ by
    rw [Matrix.one_apply_ne hz, mul_zero], Matrix.one_apply_eq, mul_one]
  -- Both sides are `ν x y` when `x ∈ T`, and both vanish otherwise.
  by_cases hx : x ∈ T
  · rw [Finset.sum_eq_single_of_mem (⟨x, hx⟩ : T) (Finset.mem_univ _) fun z _ hz ↦ by
      rw [Matrix.one_apply_ne fun h ↦ hz (Subtype.ext h.symm), zero_mul]]
    simp
  · rw [hν x y hx y.2]
    exact Finset.sum_eq_zero fun z _ ↦ by
      rw [Matrix.one_apply_ne fun h ↦ hx (by rw [h]; exact z.2), zero_mul]

end ContinuationCocycle

/-! ### Restriction of parametrized cocycles -/

namespace ParametrizedCocycle

variable {ν₀ ν₁ : ContinuationCocycle mP mQ}

/-- The **restriction of a parametrized cocycle to subcomplexes.** If the parametrized cocycle `η`
between `ν₀` and `ν₁` never leaves the subcomplexes of `S` and `S'`, `η.h x y = 0` for `x ∈ S` and
`y ∉ S'`, its entries between them form a parametrized cocycle between the restrictions of `ν₀`
and `ν₁`. -/
def restrictSubcomplex (η : ParametrizedCocycle ν₀ ν₁) (S : Set P) [DecidablePred (· ∈ S)]
    (hS : ∀ x y, x ∈ S → y ∉ S → mP.m x y = 0) (S' : Set Q) [DecidablePred (· ∈ S')]
    (hS' : ∀ x y, x ∈ S' → y ∉ S' → mQ.m x y = 0) (hν₀ : ∀ x y, x ∈ S → y ∉ S' → ν₀.ν x y = 0)
    (hν₁ : ∀ x y, x ∈ S → y ∉ S' → ν₁.ν x y = 0) (hη : ∀ x y, x ∈ S → y ∉ S' → η.h x y = 0) :
    ParametrizedCocycle (ν₀.restrictSubcomplex S hS S' hS' hν₀)
      (ν₁.restrictSubcomplex S hS S' hS' hν₁) where
  h x y := η.h x y
  mem_graded x y := η.mem_graded x y
  parametrized x y := by
    rw [η.parametrized]
    simp only [ContinuationCocycle.restrictSubcomplex_ν, TwistingCocycle.restrict_m]
    -- The generators outside `S` and `S'` contribute nothing to either sum.
    congr 1
    · congr 1
      exact Finset.sum_congr_set S _ _ (fun _ _ ↦ rfl) fun z hz ↦ by
        rw [hS x z x.2 hz, zero_mul, smul_zero]
    · exact Finset.sum_congr_set S' _ _ (fun _ _ ↦ rfl) fun z hz ↦ by
        rw [hη x z x.2 hz, zero_mul, smul_zero]

@[simp]
theorem restrictSubcomplex_h (η : ParametrizedCocycle ν₀ ν₁) (S : Set P) [DecidablePred (· ∈ S)]
    (hS : ∀ x y, x ∈ S → y ∉ S → mP.m x y = 0) (S' : Set Q) [DecidablePred (· ∈ S')]
    (hS' : ∀ x y, x ∈ S' → y ∉ S' → mQ.m x y = 0) (hν₀ : ∀ x y, x ∈ S → y ∉ S' → ν₀.ν x y = 0)
    (hν₁ : ∀ x y, x ∈ S → y ∉ S' → ν₁.ν x y = 0) (hη : ∀ x y, x ∈ S → y ∉ S' → η.h x y = 0)
    (x : S) (y : S') : (η.restrictSubcomplex S hS S' hS' hν₀ hν₁ hη).h x y = η.h x y :=
  (rfl)

/-- The **restriction of a parametrized cocycle to quotient complexes.** If the parametrized
cocycle `η` between `ν₀` and `ν₁` never enters `T'` from outside `T`, `η.h x y = 0` for `x ∉ T`
and `y ∈ T'`, its entries between them form a parametrized cocycle between the restrictions of
`ν₀` and `ν₁`. -/
def restrictQuotient (η : ParametrizedCocycle ν₀ ν₁) (T : Set P) [DecidablePred (· ∈ T)]
    (hT : ∀ x y, x ∉ T → y ∈ T → mP.m x y = 0) (T' : Set Q) [DecidablePred (· ∈ T')]
    (hT' : ∀ x y, x ∉ T' → y ∈ T' → mQ.m x y = 0) (hν₀ : ∀ x y, x ∉ T → y ∈ T' → ν₀.ν x y = 0)
    (hν₁ : ∀ x y, x ∉ T → y ∈ T' → ν₁.ν x y = 0) (hη : ∀ x y, x ∉ T → y ∈ T' → η.h x y = 0) :
    ParametrizedCocycle (ν₀.restrictQuotient T hT T' hT' hν₀)
      (ν₁.restrictQuotient T hT T' hT' hν₁) where
  h x y := η.h x y
  mem_graded x y := η.mem_graded x y
  parametrized x y := by
    rw [η.parametrized]
    simp only [ContinuationCocycle.restrictQuotient_ν, TwistingCocycle.restrict_m]
    -- The generators outside `T` and `T'` contribute nothing to either sum.
    congr 1
    · congr 1
      exact Finset.sum_congr_set T _ _ (fun _ _ ↦ rfl) fun z hz ↦ by
        rw [hη z y hz y.2, mul_zero, smul_zero]
    · exact Finset.sum_congr_set T' _ _ (fun _ _ ↦ rfl) fun z hz ↦ by
        rw [hT' z y hz y.2, mul_zero, smul_zero]

@[simp]
theorem restrictQuotient_h (η : ParametrizedCocycle ν₀ ν₁) (T : Set P) [DecidablePred (· ∈ T)]
    (hT : ∀ x y, x ∉ T → y ∈ T → mP.m x y = 0) (T' : Set Q) [DecidablePred (· ∈ T')]
    (hT' : ∀ x y, x ∉ T' → y ∈ T' → mQ.m x y = 0) (hν₀ : ∀ x y, x ∉ T → y ∈ T' → ν₀.ν x y = 0)
    (hν₁ : ∀ x y, x ∉ T → y ∈ T' → ν₁.ν x y = 0) (hη : ∀ x y, x ∉ T → y ∈ T' → η.h x y = 0)
    (x : T) (y : T') : (η.restrictQuotient T hT T' hT' hν₀ hν₁ hη).h x y = η.h x y :=
  (rfl)

end ParametrizedCocycle

end Cocycle

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

/-- **The continuation morphism commutes with the projections onto quotient complexes**, when `ν`
never enters `T'` from outside `T`: the square of twisted cochain complexes formed by the two
projections, the continuation morphism of `ν` and that of its restriction commutes. -/
@[reassoc]
theorem toRestrict_continuationHom_comp (T : Set P) [DecidablePred (· ∈ T)]
    (hT : ∀ x y, x ∉ T → y ∈ T → mP.m x y = 0) (T' : Set Q) [DecidablePred (· ∈ T')]
    (hT' : ∀ x y, x ∉ T' → y ∈ T' → mQ.m x y = 0)
    (hν : ∀ x y, x ∉ T → y ∈ T' → ν.ν x y = 0) :
    (toRestrict mP h.map_one_eq_zero T hT).continuationHom hM ≫
        (ν.restrictQuotient T hT T' hT' hν).continuationHom hM =
      ν.continuationHom hM ≫ (toRestrict mQ h.map_one_eq_zero T' hT').continuationHom hM := by
  rw [← continuationHom_comp, ← continuationHom_comp, toRestrict_comp h ν T hT T' hT' hν]

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

section Action

variable {R : Type uR} {A : Type uA} [CommRing R] [Ring A] [Algebra R A]
  {P Q : Type uP} {ind : P → ℤ} {indQ : Q → ℤ} [Fintype P] [Fintype Q]
  {𝒜 : ℤ → Submodule R A} {d : A →ₗ[R] A}
  {Γ : Type*} [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]
  {mP : TwistingCocycle 𝒜 d P ind} {mQ : TwistingCocycle 𝒜 d Q indQ}
  {actP : P → Γ} {actQ : Q → Γ}
  (hmP : ∀ x y, actP x < actP y → mP.m x y = 0) (hmQ : ∀ x y, actQ x < actQ y → mQ.m x y = 0)
  {δ : Γ} (a : Γ)

namespace ContinuationCocycle

variable (ν : ContinuationCocycle mP mQ) (hν : ∀ x y, actP x + δ < actQ y → ν.ν x y = 0)

/-- **The action superlevel of a continuation map.** If the twisted differentials of `mP` and `mQ`
do not raise the actions and the continuation cocycle `ν` raises the action by at most `δ`, then
`ν` restricts to a continuation cocycle from the quotient complex of the generators of action
`≥ a` to that of the generators of action `≥ a + δ`. -/
def actionSuperlevel :
    ContinuationCocycle
      (mP.restrict {x | a ≤ actP x} (mP.mul_eq_zero_of_forall_eq_zero'
        (mP.forall_eq_zero_of_compl (mP.m_eq_zero_of_mem_setOf_lt hmP) fun _ ↦ not_lt.symm)))
      (mQ.restrict {x | a + δ ≤ actQ x} (mQ.mul_eq_zero_of_forall_eq_zero'
        (mQ.forall_eq_zero_of_compl (mQ.m_eq_zero_of_mem_setOf_lt hmQ) fun _ ↦ not_lt.symm))) :=
  ν.restrictQuotient _
    (mP.forall_eq_zero_of_compl (mP.m_eq_zero_of_mem_setOf_lt hmP) fun _ ↦ not_lt.symm) _
    (mQ.forall_eq_zero_of_compl (mQ.m_eq_zero_of_mem_setOf_lt hmQ) fun _ ↦ not_lt.symm)
    (ν.forall_eq_zero_of_compl (ν.ν_eq_zero_of_mem_setOf_lt hν) (fun _ ↦ not_lt.symm)
      fun _ ↦ not_lt.symm)

@[simp]
theorem actionSuperlevel_ν (x : {x | a ≤ actP x}) (y : {x | a + δ ≤ actQ x}) :
    (ν.actionSuperlevel hmP hmQ a hν).ν x y = ν.ν x y :=
  restrictQuotient_ν _ _ _ _ _ _ x y

end ContinuationCocycle

namespace ParametrizedCocycle

variable {ν₀ ν₁ : ContinuationCocycle mP mQ}
  (hν₀ : ∀ x y, actP x + δ < actQ y → ν₀.ν x y = 0)
  (hν₁ : ∀ x y, actP x + δ < actQ y → ν₁.ν x y = 0) (η : ParametrizedCocycle ν₀ ν₁)
  (hη : ∀ x y, actP x + δ < actQ y → η.h x y = 0)

/-- The restriction of a parametrized cocycle which raises the action by at most `δ` to the
generators of action `< a` and `< a + δ`, a parametrized cocycle between the action sublevels. -/
def actionSublevel :
    ParametrizedCocycle (ν₀.actionSublevel hmP hmQ hν₀ a) (ν₁.actionSublevel hmP hmQ hν₁ a) :=
  η.restrictSubcomplex _ _ _ _ _ _ fun x y hx hy ↦ hη x y <| by
    calc actP x + δ < a + δ := add_lt_add_left hx δ
      _ ≤ actQ y := not_lt.1 hy

/-- The restriction of a parametrized cocycle which raises the action by at most `δ` to the
generators of action `≥ a` and `≥ a + δ`, a parametrized cocycle between the action
superlevels. -/
def actionSuperlevel :
    ParametrizedCocycle (ν₀.actionSuperlevel hmP hmQ a hν₀)
      (ν₁.actionSuperlevel hmP hmQ a hν₁) :=
  η.restrictQuotient _ _ _ _ _ _ fun x y hx hy ↦ hη x y <| by
    calc actP x + δ < a + δ := add_lt_add_left (not_le.1 hx) δ
      _ ≤ actQ y := hy

end ParametrizedCocycle

end Action

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
      (ν.actionSuperlevel hmP hmQ a hν).continuationHom hM :=
  (rfl)

/-- **Naturality of the action long exact sequence.** If the twisted differentials do not raise
the actions and the continuation cocycle `ν` raises the action by at most `δ`, the connecting
morphisms `H^i(≥ a) ⟶ H^(i+1)(< a)` of `mP` and `H^i(≥ a + δ) ⟶ H^(i+1)(< a + δ)` of `mQ`
commute with the maps induced by the action superlevel and the action sublevel of `ν`. -/
@[reassoc]
theorem actionShortComplexMap_δ (i j : ℤ) (hij : i + 1 = j) :
    (mP.actionShortComplex_shortExact hmP hM a).δ i j hij ≫
        HomologicalComplex.homologyMap ((ν.actionSublevel hmP hmQ hν a).continuationHom hM) j =
      HomologicalComplex.homologyMap ((ν.actionSuperlevel hmP hmQ a hν).continuationHom hM) i ≫
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
  (((η.actionSublevel hmP hmQ a hν₀ hν₁ hη).homotopy hM).homologyMap_eq n).symm

omit [DecidableEq P] [DecidableEq Q] in
/-- **Homotopic continuation maps agree above the action level.** A parametrized cocycle between
`ν₀` and `ν₁` which raises the action by at most `δ` makes their action superlevels induce the same
map from the cohomology of the generators of action `≥ a` to that of the generators of action
`≥ a + δ`. -/
theorem homologyMap_actionSuperlevel_eq (n : ℤ) :
    HomologicalComplex.homologyMap ((ν₀.actionSuperlevel hmP hmQ a hν₀).continuationHom hM) n =
      HomologicalComplex.homologyMap
        ((ν₁.actionSuperlevel hmP hmQ a hν₁).continuationHom hM) n :=
  (((η.actionSuperlevel hmP hmQ a hν₀ hν₁ hη).homotopy hM).homologyMap_eq n).symm

end ParametrizedCocycle

end ActionShortComplexMap

end TauCeti
