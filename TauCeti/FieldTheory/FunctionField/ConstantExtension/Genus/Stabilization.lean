/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.ConstantExtension.Genus.Basic
import TauCeti.FieldTheory.FunctionField.Consequences.HighDegree
import TauCeti.FieldTheory.FunctionField.ConstantExtension.LinearDisjoint.Stabilization
import TauCeti.FieldTheory.FunctionField.ConstantExtension.PoleDegree
import TauCeti.FieldTheory.FunctionField.RiemannRoch.Equiv
import TauCeti.FieldTheory.IntermediateField.ScalarTower

/-!
# Genus stabilization under algebraic constant field extensions

Let `F' = F · k'` be an algebraic constant field extension (finite or infinite, separable or not) of
an algebraic function field `F / k`, and assume `k'` is the exact constant field of `F'`. Then there
already exists a finite intermediate field `L` of `k' / k` such that `L` is exact in `F · L` and
`g(F · L / L) = g(F' / k')`.

The proof combines linear-disjointness stabilization from
`TauCeti.FieldTheory.FunctionField.ConstantExtension.LinearDisjoint.Stabilization` with a single
nonspecial multiple `l • (z)_∞` of a pole divisor whose Riemann–Roch space is spanned by elements
already defined over a finite constant subextension `M`
(`TauCeti.Divisor.dim_nsmul_poles_le_of_forall_exists`).

## Main results

* `TauCeti.exists_finiteDimensional_isIntegrallyClosedIn_genus_eq`: for any algebraic constant
  extension `F' = F · k'` with `k'` exact in `F'`, the genus already stabilizes at a finite
  constant subextension `L` exact in `F · L`.
-/

public section

open Module
open scoped IntermediateField

namespace TauCeti

universe u u' v v'

variable {k : Type u} {k' : Type u'} {F : Type v} {F' : Type v'}
variable [Field k] [Field k'] [Field F] [Field F']
variable [Algebra k k'] [Algebra k F] [Algebra k F'] [Algebra k' F'] [Algebra F F']
variable [IsScalarTower k k' F'] [IsScalarTower k F F']

omit [Algebra k F] [Algebra k F'] [IsScalarTower k k' F'] [IsScalarTower k F F'] in
/-- Transport exactness of constants and the genus from `(N, (F · L) · N)` to
`(N.restrictScalars k, F · (N.restrictScalars k))`. -/
private theorem isIntegrallyClosedIn_and_genus_restrictScalars (L : IntermediateField k k')
    [FiniteDimensional k L] (N : IntermediateField L k') [FiniteDimensional L N] {g : ℕ}
    (hexN : letI := constantCompositumAlgebra F L F'
      letI := constantCompositumAlgebra (constantCompositum F L F') N F'
      IsIntegrallyClosedIn N (constantCompositum (constantCompositum F L F') N F'))
    (hgN : letI := constantCompositumAlgebra F L F'
      letI := constantCompositumAlgebra (constantCompositum F L F') N F'
      genus N (constantCompositum (constantCompositum F L F') N F') = g) :
    let M := N.restrictScalars k
    FiniteDimensional k M ∧
      letI := constantCompositumAlgebra F M F'
      IsIntegrallyClosedIn M (constantCompositum F M F') ∧
        genus M (constantCompositum F M F') = g := by
  let FL := constantCompositum F L F'
  let := constantCompositumAlgebra F L F'
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
  let σ : N ≃+* M := eN.toRingEquiv
  let eF := (IntermediateField.restrictScalarsAlgEquiv F FLN).symm.trans
    (IntermediateField.equivOfEq (restrictScalars_constantCompositum_eq L N))
  let τ : FLN ≃+* FM := eF.toRingEquiv
  have hστ (c : N) : τ (algebraMap N FLN c) = algebraMap M FM (σ c) := by
    apply Subtype.ext
    have hτ : (eF (algebraMap N FLN c) : F') = algebraMap N FLN c := by
      simp [eF, IntermediateField.coe_restrictScalarsAlgEquiv_symm_apply]
    have hσ : (σ c : k') = c := IntermediateField.coe_restrictScalarsAlgEquiv_symm_apply k N c
    rw [AlgEquiv.coe_toRingEquiv, hτ, ← IntermediateField.algebraMap_apply,
      ← IsScalarTower.algebraMap_apply N FLN F', IsScalarTower.algebraMap_apply N k' F',
      ← IntermediateField.algebraMap_apply, ← IsScalarTower.algebraMap_apply M FM F',
      IsScalarTower.algebraMap_apply M k' F', IntermediateField.algebraMap_apply,
      IntermediateField.algebraMap_apply, hσ]
  exact ⟨hfin, hexN.of_ringEquiv σ τ hστ, (genus_eq_of_ringEquiv σ τ hστ).trans hgN⟩

/-- Under linear disjointness, a single finite constant subextension containing a `k'`-basis of a
nonspecial multiple of a pole divisor already stabilizes the genus and keeps exact constants. -/
private theorem exists_finiteDimensional_isIntegrallyClosedIn_genus_eq_of_linearDisjoint
    [Algebra.IsAlgebraic k k'] (hF : IsFunctionField k F) (h : constantCompositum F k' F' = ⊤)
    (H : (IsScalarTower.toAlgHom k k' F').fieldRange.LinearDisjoint F)
    (hex' : IsIntegrallyClosedIn k' F') :
    ∃ M : IntermediateField k k', FiniteDimensional k M ∧
      letI := constantCompositumAlgebra F M F'
      IsIntegrallyClosedIn M (constantCompositum F M F') ∧
        genus M (constantCompositum F M F') = genus k' F' := by
  classical
  have hF' : IsFunctionField k' F' := hF.of_constantCompositum_eq_top h
  obtain ⟨x, hx⟩ := hF.exists_transcendental
  have := hF.finiteDimensional_adjoin hx
  set z := Units.mk0 x hx.ne_zero
  set B' := Divisor.poles hF' (Units.map (algebraMap F F' : F →* F') z)
  have hdegB' : Divisor.degree B' = finrank k⟮x⟯ F :=
    Divisor.degree_poles_eq_of_linearDisjoint hF h H hF' hx
  have hpos : 1 ≤ Divisor.degree B' := by
    rw [hdegB']
    exact_mod_cast Nat.succ_le_of_lt (finrank_pos (R := k⟮x⟯) (M := F))
  let l : ℕ := 2 * genus k F
  have := finiteDimensional_riemannRochSpace hF' (l • B')
  let b := Module.finBasis k' (riemannRochSpace (l • B'))
  obtain ⟨M, _, hbM⟩ :=
    exists_finiteDimensional_constantSubfield_of_finset_subset_constantCompositum (k := k) (F := F)
      (Finset.univ.image fun i ↦ (b i : F')) fun _ _ ↦ h ▸ IntermediateField.mem_top
  let FM := constantCompositum F M F'
  let := constantCompositumAlgebra F M F'
  have := isScalarTower_constantCompositum F M F'
  have := isScalarTower_base_constantCompositum k F M F'
  have hFM : constantCompositum F M FM = ⊤ := (constantCompositum_eq_top_iff F M F' FM).2 rfl
  have hFFM : IsFunctionField M FM := hF.of_constantCompositum_eq_top hFM
  have : Algebra.IsAlgebraic M k' := .tower_top (K := k) M
  have hFM_top := constantCompositum_eq_top_of_eq_top F k' F' FM h
  have := (isAlgebraic_of_constantCompositum_eq_top (k := M) hFM_top).isIntegral
  have hexM := isIntegrallyClosedIn_constantCompositum_of_linearDisjoint H hex' M
  set BM := Divisor.poles hFFM (Units.map (algebraMap F FM : F →* FM) z)
  have hHM : (IsScalarTower.toAlgHom k M FM).fieldRange.LinearDisjoint F :=
    linearDisjoint_fieldRange_of_finrank_constantCompositum_eq (by
      rw [hFM, IntermediateField.finrank_top']
      exact finrank_constantCompositum_eq_finrank_of_linearDisjoint F M F'
        (H.fieldRange_intermediateField M))
  have hdegBM : Divisor.degree BM = Divisor.degree B' :=
    (Divisor.degree_poles_eq_of_linearDisjoint hF hFM hHM hFFM hx).trans hdegB'.symm
  have hdim_le : (l • B').dim ≤ (l • BM).dim :=
    Divisor.dim_nsmul_poles_le_of_forall_exists hFFM hF' z l b fun i ↦
      ⟨⟨b i, hbM _ (Finset.mem_image_of_mem _ (Finset.mem_univ i))⟩, rfl⟩
  have hgM_le : genus M FM ≤ genus k F := genus_le_genus_of_constantCompositum_eq_top hF hFM
  have hg'_le : genus k' F' ≤ genus M FM := genus_le_genus_of_constantCompositum_eq_top hFFM hFM_top
  have hl_deg : 2 * (genus k F : ℤ) - 1 ≤ Divisor.degree (l • B') := by
    rw [map_nsmul, nsmul_eq_mul]; push_cast [l]; nlinarith
  have hdim' := Divisor.dim_eq_degree_add_one_sub_genus_of_two_mul_genus_sub_one_le_degree hF' hex'
    (D := l • B') (by omega)
  have hdimM := Divisor.dim_eq_degree_add_one_sub_genus_of_two_mul_genus_sub_one_le_degree hFFM hexM
    (D := l • BM) (by rw [map_nsmul, hdegBM, ← map_nsmul]; omega)
  rw [map_nsmul, hdegBM, ← map_nsmul] at hdimM
  have hgM_eq : genus M FM = genus k' F' := by omega
  exact ⟨M, ‹_›, hexM, hgM_eq⟩

/-- **Genus stabilization under an algebraic constant field extension**: if `F' = F · k'` for an
algebraic extension `k' / k`, finite or not, and `k'` is the exact constant field of `F'`, then
some finite subextension `L` of `k' / k` already has `L` exact in `F · L` and
`g(F · L / L) = g(F' / k')`. -/
theorem exists_finiteDimensional_isIntegrallyClosedIn_genus_eq [Algebra.IsAlgebraic k k']
    (hF : IsFunctionField k F) (h : constantCompositum F k' F' = ⊤)
    (hex' : IsIntegrallyClosedIn k' F') :
    ∃ L : IntermediateField k k', FiniteDimensional k L ∧
      letI := constantCompositumAlgebra F L F'
      IsIntegrallyClosedIn L (constantCompositum F L F') ∧
        genus L (constantCompositum F L F') = genus k' F' := by
  obtain ⟨L, _, H⟩ := exists_finiteDimensional_linearDisjoint_of_constantCompositum_eq_top hF h
  let FL := constantCompositum F L F'
  let := constantCompositumAlgebra F L F'
  have := isScalarTower_constantCompositum F L F'
  have := isScalarTower_base_constantCompositum k F L F'
  have hFL : constantCompositum F L FL = ⊤ := (constantCompositum_eq_top_iff F L F' FL).2 rfl
  have hFFL : IsFunctionField L FL := hF.of_constantCompositum_eq_top hFL
  have : Algebra.IsAlgebraic L k' := .tower_top (K := k) L
  obtain ⟨N, _, hexN, hgN⟩ :=
    exists_finiteDimensional_isIntegrallyClosedIn_genus_eq_of_linearDisjoint hFFL
      (constantCompositum_eq_top_of_eq_top F k' F' FL h) H hex'
  obtain ⟨hfin, hexM, hgM⟩ := isIntegrallyClosedIn_and_genus_restrictScalars L N hexN hgN
  exact ⟨N.restrictScalars k, hfin, hexM, hgM⟩

end TauCeti
