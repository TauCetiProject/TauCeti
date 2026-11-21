/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.ConstantExtension.Degree
import Mathlib.LinearAlgebra.Dimension.OrzechProperty
import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
import TauCeti.FieldTheory.FunctionField.ConstantExtension.Algebraic
import TauCeti.FieldTheory.IntermediateField.Adjoin.Basic
import TauCeti.FieldTheory.IntermediateField.LinearDisjoint
import TauCeti.FieldTheory.IntermediateField.ScalarTower
import TauCeti.FieldTheory.RatFunc.Transcendental

/-!
# Degrees after a linearly disjoint extension of constants

Let `F' = F · k'` in a common overfield, with `F` and `k'` linearly disjoint over `k`.
For every intermediate field `C` of `F/k` with `F/C` algebraic, a `C`-basis of `F` remains a
basis of `F'` over `k' · C`. In particular, `[F' : k'(x)] = [F : k(x)]`.
The extension `k'/k` can be transcendental; no perfectness or exact-constants hypothesis
is needed once linear disjointness is supplied.

Linear independence is transported by
`IntermediateField.LinearDisjoint.linearIndependent_adjoin_algebraMap_comp`.
Spanning uses algebraicity of `F/C`: adjoining the algebraic image of `F` to `k' · C`
already gives the whole field compositum. A transcendental element also remains
transcendental, so a linearly disjoint extension of constants of a one-variable function
field is again a one-variable function field. Conversely, preserving the finite degree over
a shared transcendental parameter `x` (or over `k(t)`) recovers linear disjointness.

## Main results

* `TauCeti.constantExtensionBasisOfLinearDisjoint`: transport a basis over `C`.
* `TauCeti.finrank_over_adjoin_simple_eq_of_linearDisjoint`: preserve the degree over `k(x)`.
* `TauCeti.IsFunctionField.of_constantCompositum_eq_top_of_linearDisjoint`: preserve the
  one-variable function-field property under an arbitrary linearly disjoint extension of constants.
* `TauCeti.linearDisjoint_of_transcendental_of_finrank_eq` and
  `TauCeti.linearDisjoint_of_finrank_ratFunc_eq`: degree preservation over a shared parameter or
  `k(t)` implies linear disjointness of constants.
* `TauCeti.exists_finiteDimensional_linearDisjoint_of_constantCompositum_eq_top`: linear
  disjointness stabilizes after a finite subextension `L` of `k' / k`.

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, second edition, Section III.6,
  Proposition 3.6.1(c), for the algebraic constant-extension specialization.
* S. Lang, *Algebra*, the theory of linearly disjoint field extensions.
-/

public section

open scoped IntermediateField

namespace TauCeti

universe u u' v v'

variable {k : Type u} {k' : Type u'} {F : Type v} {F' : Type v'}
variable [Field k] [Field k'] [Field F] [Field F']
variable [Algebra k k'] [Algebra k F] [Algebra k F'] [Algebra k' F'] [Algebra F F']
variable [IsScalarTower k k' F'] [IsScalarTower k F F']

/-- A basis of an algebraic extension `F/C` stays a basis over `k' · C` in the linearly disjoint
constant compositum `F' = F · k'`. The constants `k'/k` need not be algebraic. -/
noncomputable def constantExtensionBasisOfLinearDisjoint
    (H : (IsScalarTower.toAlgHom k k' F').fieldRange.LinearDisjoint F)
    (h : constantCompositum F k' F' = ⊤) (C : IntermediateField k F)
    [Algebra.IsAlgebraic C F] {ι : Type*} (b : Module.Basis ι C F) :
    Module.Basis ι (IntermediateField.adjoin k' (Set.range (algebraMap C F'))) F' :=
  Module.Basis.mk (H.linearIndependent_adjoin_algebraMap_comp C b.linearIndependent)
    (span_range_basis_of_isAlgebraic_constantCompositum h C b).ge

/-- The transported basis consists of the images of the original basis vectors. -/
@[simp]
theorem constantExtensionBasisOfLinearDisjoint_apply
    (H : (IsScalarTower.toAlgHom k k' F').fieldRange.LinearDisjoint F)
    (h : constantCompositum F k' F' = ⊤) (C : IntermediateField k F)
    [Algebra.IsAlgebraic C F] {ι : Type*} (b : Module.Basis ι C F) (i : ι) :
    constantExtensionBasisOfLinearDisjoint H h C b i = algebraMap F F' (b i) :=
  Module.Basis.mk_apply _ _ i

/-- An arbitrary linearly disjoint extension of constants preserves the finite degree over a
simple intermediate field: `[F · k' : k'(x)] = [F : k(x)]`. -/
theorem finrank_over_adjoin_simple_eq_of_linearDisjoint
    (H : (IsScalarTower.toAlgHom k k' F').fieldRange.LinearDisjoint F)
    (h : constantCompositum F k' F' = ⊤) (x : F) [FiniteDimensional k⟮x⟯ F] :
    Module.finrank k'⟮algebraMap F F' x⟯ F' = Module.finrank k⟮x⟯ F := by
  let b := Module.finBasis k⟮x⟯ F
  have hdegree := Module.finrank_eq_card_basis (constantExtensionBasisOfLinearDisjoint H h k⟮x⟯ b)
  rwa [IntermediateField.range_algebraMap_adjoin_simple,
    IntermediateField.adjoin_adjoin_right, Fintype.card_fin] at hdegree

/-- Extending constants linearly disjointly, even transcendently, preserves the one-variable
function-field property. -/
theorem IsFunctionField.of_constantCompositum_eq_top_of_linearDisjoint
    (hF : IsFunctionField k F)
    (H : (IsScalarTower.toAlgHom k k' F').fieldRange.LinearDisjoint F)
    (h : constantCompositum F k' F' = ⊤) : IsFunctionField k' F' := by
  obtain ⟨x, hx⟩ := hF.exists_transcendental
  have := hF.finiteDimensional_adjoin hx
  have := finiteDimensional_adjoin_simple_of_constantCompositum_eq_top (k := k) h x
  exact (H.transcendental_algebraMap hx).isFunctionField_adjoin.finite_extension

/-- **Linear disjointness over a shared parameter from degree preservation.** -/
theorem linearDisjoint_of_transcendental_of_finrank_eq (h : constantCompositum F k' F' = ⊤) {x : F}
    (hx' : Transcendental k' (algebraMap F F' x)) [FiniteDimensional k⟮x⟯ F]
    (hn : Module.finrank k'⟮algebraMap F F' x⟯ F' = Module.finrank k⟮x⟯ F) :
    (IsScalarTower.toAlgHom k k' F').fieldRange.LinearDisjoint F := by
  let b := Module.finBasis k⟮x⟯ F
  have hspan := span_range_basis_of_isAlgebraic_constantCompositum h k⟮x⟯ b
  rw [IntermediateField.range_algebraMap_adjoin_simple,
    IntermediateField.adjoin_adjoin_right] at hspan
  exact IntermediateField.linearDisjoint_of_transcendental_of_linearIndependent hx' b
    (linearIndependent_of_top_le_span_of_card_eq_finrank hspan.ge (by rw [Fintype.card_fin, ← hn]))

omit [Algebra k F] [Algebra k F'] [IsScalarTower k k' F'] [IsScalarTower k F F'] in
/-- Transport `LinearDisjoint` along `N ↦ N.restrictScalars k` and the tower identity
`((F · L) · N).restrictScalars F = F · (N.restrictScalars k)`. -/
private theorem linearDisjoint_fieldRange_restrictScalars (L : IntermediateField k k')
    [FiniteDimensional k L] (N : IntermediateField L k') [FiniteDimensional L N]
    (H : letI := constantCompositumAlgebra F L F'
      letI := constantCompositumAlgebra (constantCompositum F L F') N F'
      haveI := isScalarTower_constantCompositum (constantCompositum F L F') N F'
      (IsScalarTower.toAlgHom N k' F').fieldRange.LinearDisjoint
        (constantCompositum (constantCompositum F L F') N F')) :
    let M := N.restrictScalars k
    FiniteDimensional k M ∧
      letI := constantCompositumAlgebra F M F'
      haveI := isScalarTower_constantCompositum F M F'
      (IsScalarTower.toAlgHom M k' F').fieldRange.LinearDisjoint (constantCompositum F M F') := by
  let FL := constantCompositum F L F'
  let FLN := constantCompositum FL N F'
  let := constantCompositumAlgebra FL N F'
  have := isScalarTower_constantCompositum FL N F'
  let M := N.restrictScalars k
  let FM := constantCompositum F M F'
  let := constantCompositumAlgebra F M F'
  have := isScalarTower_constantCompositum F M F'
  have : FiniteDimensional k N := Module.Finite.trans L N
  let eN := (IntermediateField.restrictScalarsAlgEquiv k N).symm
  have hfin : FiniteDimensional k M := eN.toLinearEquiv.finiteDimensional
  let eF := (IntermediateField.restrictScalarsAlgEquiv F FLN).symm.trans
    (IntermediateField.equivOfEq (restrictScalars_constantCompositum_eq L N))
  have hσ (c : N) : algebraMap M F' (eN.toRingEquiv c) = algebraMap N F' c := by
    rw [AlgEquiv.coe_toRingEquiv, IsScalarTower.algebraMap_apply M k' F',
      IsScalarTower.algebraMap_apply N k' F', IntermediateField.algebraMap_apply,
      IntermediateField.algebraMap_apply,
      IntermediateField.coe_restrictScalarsAlgEquiv_symm_apply]
  have hτ (x : FLN) : algebraMap FM F' (eF.toRingEquiv x) = algebraMap FLN F' x := by
    simp [eF, IntermediateField.algebraMap_apply]
  exact ⟨hfin, linearDisjoint_fieldRange_of_ringEquiv eN.toRingEquiv eF.toRingEquiv hσ hτ H⟩

/-- Strong induction on `[E : K(x)]`: some finite subextension `L` of `k' / K` makes `k'` and
`E · L` linearly disjoint over `L`. -/
private theorem exists_finiteDimensional_linearDisjoint_aux (n : ℕ) :
    ∀ (K : Type u') (E : Type v') [Field K] [Field E] [Algebra K k'] [Algebra K E]
      [Algebra K F'] [Algebra E F'] [IsScalarTower K k' F'] [IsScalarTower K E F']
      [Algebra.IsAlgebraic K k'], IsFunctionField K E → constantCompositum E k' F' = ⊤ →
      ∀ x : E, Transcendental K x → Module.finrank K⟮x⟯ E = n →
      ∃ L : IntermediateField K k', FiniteDimensional K L ∧
        letI := constantCompositumAlgebra E L F'
        haveI := isScalarTower_constantCompositum E L F'
        (IsScalarTower.toAlgHom L k' F').fieldRange.LinearDisjoint
          (constantCompositum E L F') := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro K E _ _ _ _ _ _ _ _ _ hE h x hx hn
  by_cases hdisj : ∀ M : IntermediateField K k', FiniteDimensional K M →
      Module.finrank E (constantCompositum E M F') = Module.finrank K M
  · have H := linearDisjoint_fieldRange_of_forall_finrank_constantCompositum_eq hdisj
    let L : IntermediateField K k' := ⊥
    let EL := constantCompositum E L F'
    let := constantCompositumAlgebra E L F'
    have := isScalarTower_constantCompositum E L F'
    have hbot : EL = ⊥ := constantCompositum_bot
    let eK := (IntermediateField.botEquiv K k').symm
    let eE := (IntermediateField.botEquiv E F').symm.trans (IntermediateField.equivOfEq hbot.symm)
    have hσ (c : K) : algebraMap L F' (eK.toRingEquiv c) = algebraMap K F' c := by
      have hc : eK c = algebraMap K L c := by simpa using eK.commutes c
      rw [AlgEquiv.coe_toRingEquiv, hc, ← IsScalarTower.algebraMap_apply K L F']
    have hτ (y : E) : algebraMap EL F' (eE.toRingEquiv y) = algebraMap E F' y := by
      have hy : eE y = algebraMap E EL y := by simpa using eE.commutes y
      rw [AlgEquiv.coe_toRingEquiv, hy, ← IsScalarTower.algebraMap_apply E EL F']
    exact ⟨L, inferInstance,
      linearDisjoint_fieldRange_of_ringEquiv eK.toRingEquiv eE.toRingEquiv hσ hτ H⟩
  push Not at hdisj
  obtain ⟨M, _, hM⟩ := hdisj
  let EM := constantCompositum E M F'
  let := constantCompositumAlgebra E M F'
  have := isScalarTower_constantCompositum E M F'
  have := isScalarTower_base_constantCompositum K E M F'
  have hEM : constantCompositum E M EM = ⊤ := (constantCompositum_eq_top_iff E M F' EM).2 rfl
  have hFEM : IsFunctionField M EM := hE.of_constantCompositum_eq_top hEM
  have : Algebra.IsAlgebraic M k' := .tower_top (K := K) M
  have hx' : Transcendental M (algebraMap E EM x) := hx.algebraMap_of_isAlgebraic
  have := hE.finiteDimensional_adjoin hx
  have hlt : Module.finrank M⟮algebraMap E EM x⟯ EM < n :=
    hn ▸ finrank_adjoin_simple_lt_of_finrank_ne (F' := F') hx hM
  obtain ⟨N, _, HN⟩ :=
    ih _ hlt M EM hFEM (constantCompositum_eq_top_of_eq_top E k' F' EM h) _ hx' rfl
  obtain ⟨hfin, H'⟩ := linearDisjoint_fieldRange_restrictScalars M N HN
  exact ⟨N.restrictScalars K, hfin, H'⟩

/-- **Linear-disjointness stabilization under an algebraic constant field extension**: if
`F' = F · k'` for an algebraic extension `k' / k`, finite or not, then there exists a finite
intermediate field `L` of `k' / k` such that `k'` and `F · L` are linearly disjoint over `L`
inside `F'`. -/
theorem exists_finiteDimensional_linearDisjoint_of_constantCompositum_eq_top
    [Algebra.IsAlgebraic k k'] (hF : IsFunctionField k F)
    (h : constantCompositum F k' F' = ⊤) :
    ∃ L : IntermediateField k k', FiniteDimensional k L ∧
      letI := constantCompositumAlgebra F L F'
      haveI := isScalarTower_constantCompositum F L F'
      (IsScalarTower.toAlgHom L k' F').fieldRange.LinearDisjoint (constantCompositum F L F') := by
  let L₀ : IntermediateField k k' := ⊥
  let E₀ := constantCompositum F L₀ F'
  let := constantCompositumAlgebra F L₀ F'
  have := isScalarTower_constantCompositum F L₀ F'
  have := isScalarTower_base_constantCompositum k F L₀ F'
  have hE₀ : constantCompositum F L₀ E₀ = ⊤ := (constantCompositum_eq_top_iff F L₀ F' E₀).2 rfl
  have hFE₀ : IsFunctionField L₀ E₀ := hF.of_constantCompositum_eq_top hE₀
  have : Algebra.IsAlgebraic L₀ k' := .tower_top (K := k) L₀
  obtain ⟨x, hx⟩ := hF.exists_transcendental
  have hx₀ : Transcendental L₀ (algebraMap F E₀ x) := hx.algebraMap_of_isAlgebraic
  obtain ⟨N, _, HN⟩ := exists_finiteDimensional_linearDisjoint_aux _ L₀ E₀ hFE₀
    (constantCompositum_eq_top_of_eq_top F k' F' E₀ h) _ hx₀ rfl
  obtain ⟨hfin, H'⟩ := linearDisjoint_fieldRange_restrictScalars L₀ N HN
  exact ⟨N.restrictScalars k, hfin, H'⟩

section RatFunc

variable [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F]
  [Algebra (RatFunc k') F'] [IsScalarTower k' (RatFunc k') F']

/-- **Degree preservation over `k(t)` implies linear disjointness of constants.** -/
theorem linearDisjoint_of_finrank_ratFunc_eq [FiniteDimensional (RatFunc k) F]
    (h : constantCompositum F k' F' = ⊤)
    (hX : algebraMap F F' (algebraMap (RatFunc k) F RatFunc.X) =
      algebraMap (RatFunc k') F' RatFunc.X)
    (hn : Module.finrank (RatFunc k') F' = Module.finrank (RatFunc k) F) :
    (IsScalarTower.toAlgHom k k' F').fieldRange.LinearDisjoint F := by
  have hx' : Transcendental k' (algebraMap F F' (algebraMap (RatFunc k) F RatFunc.X)) :=
    hX ▸ (transcendental_algebraMap_iff
      (FaithfulSMul.algebraMap_injective (RatFunc k') F')).mpr RatFunc.transcendental_X
  have : FiniteDimensional k⟮algebraMap (RatFunc k) F RatFunc.X⟯ F :=
    Module.finite_of_finrank_pos
      (finrank_adjoin_algebraMap_X (k := k) (F := F) ▸ Module.finrank_pos)
  refine linearDisjoint_of_transcendental_of_finrank_eq h hx' ?_
  rw [hX, finrank_adjoin_algebraMap_X, finrank_adjoin_algebraMap_X, hn]

end RatFunc

end TauCeti
