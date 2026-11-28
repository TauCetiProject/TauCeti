/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.ConstantExtension.Degree
import TauCeti.FieldTheory.FunctionField.ConstantExtension.Algebraic
import TauCeti.FieldTheory.IntermediateField.ScalarTower

/-!
# Finite stabilization of linear disjointness under algebraic constant extensions

Let `F / k` be an algebraic function field and let `F' = F · k'` be an algebraic extension of
constants, finite or infinite, separable or inseparable. Then there exists a finite intermediate
field `L` of `k' / k` such that `F · L` and `k'` are linearly disjoint over `L` inside `F'`.

The proof proceeds by strong induction on `[F : k(x)]` for a transcendental element `x ∈ F`:
whenever linear disjointness fails over the current base, some finite constant extension strictly
lowers the degree over `k(x)` (`TauCeti.finrank_adjoin_simple_lt_of_finrank_ne`).

## Main results

* `TauCeti.exists_finiteDimensional_linearDisjoint_of_constantCompositum_eq_top`: linear
  disjointness stabilizes after a finite subextension `L` of `k' / k`.

## References

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
  let FL := constantCompositum F L F'; let FLN := constantCompositum FL N F'
  let := constantCompositumAlgebra FL N F'; have := isScalarTower_constantCompositum FL N F'
  let M := N.restrictScalars k; let FM := constantCompositum F M F'
  let := constantCompositumAlgebra F M F'; have := isScalarTower_constantCompositum F M F'
  have : FiniteDimensional k N := Module.Finite.trans L N
  let eN := (IntermediateField.restrictScalarsAlgEquiv k N).symm
  let eF := restrictScalarsConstantCompositumEquiv F F' L N
  have hσ (c : N) : algebraMap M F' (eN.toRingEquiv c) = algebraMap N F' c := by
    rw [AlgEquiv.coe_toRingEquiv, IsScalarTower.algebraMap_apply M k' F',
      IsScalarTower.algebraMap_apply N k' F', IntermediateField.algebraMap_apply,
      IntermediateField.algebraMap_apply, IntermediateField.coe_restrictScalarsAlgEquiv_symm_apply]
  have hτ (x : FLN) : algebraMap FM F' (eF.toRingEquiv x) = algebraMap FLN F' x := by
    simp [eF, IntermediateField.algebraMap_apply]
  exact ⟨eN.toLinearEquiv.finiteDimensional,
    linearDisjoint_fieldRange_of_ringEquiv eN.toRingEquiv eF.toRingEquiv hσ hτ H⟩

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
    let L : IntermediateField K k' := ⊥; let EL := constantCompositum E L F'
    let := constantCompositumAlgebra E L F'; have := isScalarTower_constantCompositum E L F'
    let eK := (IntermediateField.botEquiv K k').symm
    let eE := constantCompositumBotEquiv E k' F' (k := K)
    have hσ (c : K) : algebraMap L F' (eK.toRingEquiv c) = algebraMap K F' c := by
      rw [AlgEquiv.coe_toRingEquiv, IntermediateField.botEquiv_symm,
        ← IsScalarTower.algebraMap_apply K L F']
    have hτ (y : E) : algebraMap EL F' (eE.toRingEquiv y) = algebraMap E F' y := by
      simp [eE, IntermediateField.algebraMap_apply]
    exact ⟨L, inferInstance,
      linearDisjoint_fieldRange_of_ringEquiv eK.toRingEquiv eE.toRingEquiv hσ hτ H⟩
  push Not at hdisj; obtain ⟨M, _, hM⟩ := hdisj
  let EM := constantCompositum E M F'; let := constantCompositumAlgebra E M F'
  have := isScalarTower_constantCompositum E M F'
  have := isScalarTower_base_constantCompositum K E M F'
  have hEM : constantCompositum E M EM = ⊤ := (constantCompositum_eq_top_iff E M F' EM).2 rfl
  have := hE.finiteDimensional_adjoin hx
  have hlt : Module.finrank M⟮algebraMap E EM x⟯ EM < n :=
    hn ▸ finrank_adjoin_simple_lt_of_finrank_ne (F' := F') hx hM
  have : Algebra.IsAlgebraic M k' := .tower_top (K := K) M
  obtain ⟨N, _, HN⟩ := ih _ hlt M EM (hE.of_constantCompositum_eq_top hEM)
    (constantCompositum_eq_top_of_eq_top E k' F' EM h) _ (hx.algebraMap_of_isAlgebraic) rfl
  exact ⟨N.restrictScalars K, linearDisjoint_fieldRange_restrictScalars M N HN⟩

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
  let L₀ : IntermediateField k k' := ⊥; let E₀ := constantCompositum F L₀ F'
  let := constantCompositumAlgebra F L₀ F'; have := isScalarTower_constantCompositum F L₀ F'
  have := isScalarTower_base_constantCompositum k F L₀ F'
  have hE₀ : constantCompositum F L₀ E₀ = ⊤ := (constantCompositum_eq_top_iff F L₀ F' E₀).2 rfl
  have : Algebra.IsAlgebraic L₀ k' := .tower_top (K := k) L₀
  obtain ⟨x, hx⟩ := hF.exists_transcendental
  obtain ⟨N, _, HN⟩ := exists_finiteDimensional_linearDisjoint_aux _ L₀ E₀
    (hF.of_constantCompositum_eq_top hE₀) (constantCompositum_eq_top_of_eq_top F k' F' E₀ h)
    _ (hx.algebraMap_of_isAlgebraic) rfl
  exact ⟨N.restrictScalars k, linearDisjoint_fieldRange_restrictScalars L₀ N HN⟩

end TauCeti
