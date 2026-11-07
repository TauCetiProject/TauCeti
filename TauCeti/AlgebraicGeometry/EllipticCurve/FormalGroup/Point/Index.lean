/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.FormalGroup.Point.Filtration
public import TauCeti.AlgebraicGeometry.EllipticCurve.Tamagawa.Local
import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Point.Index.NSmul

/-!
# Indices of the formal filtration in the local point group

For an integral Weierstrass equation `C` over the completed valuation ring `O_u`, elliptic
on the fraction field `F_u`, the image of the formal parameters in `𝔪_u ^ k` is a subgroup
`C.formalPointFiltration u k` of `E(F_u)`. At `k = 1` it is the kernel of reduction `E₁(F_u)`.
For positive `k` these are the usual subgroups `E_k(F_u)`; the level zero here is also `E₁`,
not the subgroup `E₀` of points with nonsingular reduction.

Write `q = #κ(u)` and let `E_ns` be the nonsingular points of the reduced equation. Then

`[E(F_u) : E_(k+1)(F_u)] = q^k · #E_ns(κ(u)) · [E(F_u) : E₀(F_u)]`.

For a minimal equation the last factor is the local Tamagawa number. This formula separates
the formal, reduced, and component-group factors in the index, as needed when comparing the
local cokernel of an isogeny with its effect on deep formal subgroups. No minimality is needed
for the index formula for an integral equation; minimality enters the Tamagawa interpretation
and the finite-index instance. The equalities use `Nat.card` and remain valid without assuming
the residue field finite.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], IV.3, VII.2 and VII.6.
* J. W. S. Cassels, *Arithmetic on curves of genus 1. VIII. On conjectures of Birch and
  Swinnerton-Dyer*, J. Reine Angew. Math. 217 (1965), 180–199.
-/

public section

namespace WeierstrassCurve

open IsDedekindDomain IsLocalRing

variable {A : Type*} [CommRing A] [IsDedekindDomain A]
  {F : Type*} [Field F] [Algebra A F] [IsFractionRing A F]
  (u : HeightOneSpectrum A)

local notation "O_u" => u.adicCompletionIntegers F
local notation "F_u" => u.adicCompletion F
local notation "m_u" => maximalIdeal O_u
local notation "R_u" =>
  Valuation.valuationSubring
    (Valued.v : Valuation (u.adicCompletion F) (WithZero (Multiplicative ℤ)))

local instance isLinearTopology_index : IsLinearTopology O_u O_u :=
  u.isAdic_maximalIdeal_adicCompletionIntegers (K := F) ▸ Ideal.isLinearTopology m_u

private local instance fact_isAdic_index : Fact (IsAdic m_u) :=
  ⟨u.isAdic_maximalIdeal_adicCompletionIntegers (K := F)⟩

variable (C : WeierstrassCurve (u.adicCompletionIntegers F))
  [(C.baseChange (u.adicCompletion F)).IsElliptic]

open scoped Classical in
/-- The image in the local point group of formal parameters in `𝔪_u ^ k`. For `k ≥ 1` this
is the usual `E_k(F_u)`. Levels zero and one both equal the kernel of reduction. -/
noncomputable def formalPointFiltration (k : ℕ) : AddSubgroup (C.baseChange F_u).toAffine.Point :=
  (FormalGroupPoint.filtration C m_u k).map (C.formalPointHomAdicCompletion u)

open scoped Classical in
/-- Membership in a formal level means having a formal parameter in that ideal power. -/
theorem mem_formalPointFiltration_iff (k : ℕ) (P : (C.baseChange F_u).toAffine.Point) :
    P ∈ C.formalPointFiltration u k ↔
      ∃ t : FormalGroupPoint C m_u, (t : O_u) ∈ m_u ^ k ∧
        C.formalPointHomAdicCompletion u t = P := by
  simp only [formalPointFiltration, AddSubgroup.mem_map, FormalGroupPoint.mem_filtration]

open scoped Classical in
/-- The formal parametrisation preserves and reflects the depth of a parameter. -/
@[simp]
theorem formalPoint_mem_formalPointFiltration_iff (k : ℕ)
    (t : FormalGroupPoint C m_u) :
    C.formalPoint (K := F_u) (u.isAdic_maximalIdeal_adicCompletionIntegers (K := F)) t.property ∈
        C.formalPointFiltration u k ↔ (t : O_u) ∈ m_u ^ k := by
  rw [← C.formalPointHomAdicCompletion_apply u t, C.mem_formalPointFiltration_iff u]
  simp only [(C.formalPointHomAdicCompletion_injective u).eq_iff, exists_eq_right]

open scoped Classical in
/-- Formal levels decrease as their depth increases. -/
theorem formalPointFiltration_antitone : Antitone (C.formalPointFiltration u) :=
  fun _ _ hjk ↦ AddSubgroup.map_mono (FormalGroupPoint.filtration_antitone hjk)

open scoped Classical in
@[simp]
theorem formalPointFiltration_zero : C.formalPointFiltration u 0 = C.kerReduction u := by
  rw [formalPointFiltration, FormalGroupPoint.filtration_zero, AddSubgroup.map_top,
    range_formalPointHomAdicCompletion_eq_kerReduction]

open scoped Classical in
@[simp]
theorem formalPointFiltration_one : C.formalPointFiltration u 1 = C.kerReduction u := by
  rw [formalPointFiltration, FormalGroupPoint.filtration_one, AddSubgroup.map_top,
    range_formalPointHomAdicCompletion_eq_kerReduction]

open scoped Classical in
/-- Every formal level is contained in the kernel of reduction. -/
theorem formalPointFiltration_le_kerReduction (k : ℕ) :
    C.formalPointFiltration u k ≤ C.kerReduction u := by
  rw [← C.formalPointFiltration_zero u]
  exact C.formalPointFiltration_antitone u (Nat.zero_le k)

open scoped Classical in
/-- The relative index of two positive formal levels is a power of the residue cardinality. -/
theorem relIndex_formalPointFiltration {j : ℕ} (hj : j ≠ 0) (k : ℕ) :
    (C.formalPointFiltration u (j + k)).relIndex (C.formalPointFiltration u j) =
      Nat.card (ResidueField O_u) ^ k := by
  rw [formalPointFiltration, formalPointFiltration,
    AddSubgroup.relIndex_map_map_of_injective _ _ (C.formalPointHomAdicCompletion_injective u),
    FormalGroupPoint.relIndex_filtration hj (Nat.le_add_right j k),
    TauCeti.IsDiscreteValuationRing.relIndex_maximalIdeal_pow_add]

open scoped Classical in
/-- The reduction exact sequence computes the index of `E₁` in the whole point group. This
holds for any integral equation, including one with bad or nonminimal reduction. -/
theorem index_kerReduction :
    (C.kerReduction u).index =
      Nat.card ((integralModel R_u (C.baseChange F_u)).map (residue R_u)).toAffine.Point *
        ((C.baseChange F_u).toAffine.nonsingularReduction Valued.v).index := by
  have : IsIntegral O_u (C.baseChange F_u) := ⟨C, rfl⟩
  have : HenselianLocalRing R_u := inferInstanceAs (HenselianLocalRing O_u)
  let W := (C.baseChange F_u).toAffine
  have hle : C.kerReduction u ≤ W.nonsingularReduction Valued.v := by
    intro P hP
    rw [Affine.mem_nonsingularReduction_iff, C.mem_kerReduction_iff u |>.mp hP,
      Projective.nonsingularLift_iff]
    exact Projective.nonsingular_zero
  have hker : (C.kerReduction u).addSubgroupOf (W.nonsingularReduction Valued.v) =
      (W.nonsingularReductionHom Valued.v).ker := by
    ext P
    rw [AddSubgroup.mem_addSubgroupOf, Affine.mem_ker_nonsingularReductionHom_iff,
      C.mem_kerReduction_iff u, Affine.Point.reduction_eq_zero_iff]
  rw [← AddSubgroup.relIndex_mul_index hle, AddSubgroup.relIndex, hker,
    AddSubgroup.index_ker, AddMonoidHom.range_eq_top.mpr
      (Affine.nonsingularReductionHom_surjective Valued.v), AddSubgroup.card_top]

open scoped Classical in
/-- Each step beyond `E₁` contributes one residue-field factor to the index. -/
theorem index_formalPointFiltration_eq_mul_index_kerReduction (k : ℕ) :
    (C.formalPointFiltration u (k + 1)).index =
      Nat.card (ResidueField O_u) ^ k * (C.kerReduction u).index := by
  rw [← AddSubgroup.relIndex_mul_index (C.formalPointFiltration_le_kerReduction u (k + 1)),
    ← C.formalPointFiltration_one u, Nat.add_comm k 1,
    C.relIndex_formalPointFiltration u one_ne_zero k, C.formalPointFiltration_one u]

open scoped Classical in
/-- The index of a positive formal level separates into the residue-field power, the
nonsingular reduction count, and the component-group index. -/
theorem index_formalPointFiltration (k : ℕ) :
    (C.formalPointFiltration u (k + 1)).index =
      Nat.card (ResidueField O_u) ^ k *
        Nat.card ((integralModel R_u (C.baseChange F_u)).map (residue R_u)).toAffine.Point *
        ((C.baseChange F_u).toAffine.nonsingularReduction Valued.v).index := by
  rw [C.index_formalPointFiltration_eq_mul_index_kerReduction u, C.index_kerReduction u,
    mul_assoc]

open scoped Classical in
/-- On a minimal equation the component-group factor in the formal-level index is the
local Tamagawa number. -/
theorem index_formalPointFiltration_eq_tamagawaNumber [IsMinimal O_u (C.baseChange F_u)]
    (k : ℕ) :
    (C.formalPointFiltration u (k + 1)).index =
      Nat.card (ResidueField O_u) ^ k *
        Nat.card ((integralModel R_u (C.baseChange F_u)).map (residue R_u)).toAffine.Point *
        (C.baseChange F_u).tamagawaNumber Valued.v := by
  have : IsMinimal R_u (C.baseChange F_u) := inferInstanceAs (IsMinimal O_u (C.baseChange F_u))
  rw [C.index_formalPointFiltration u, tamagawaNumber_eq_index]

open scoped Classical in
/-- Over a finite residue field every formal level of a minimal equation has finite index
in the local point group. -/
instance finiteIndex_formalPointFiltration [Finite (A ⧸ u.asIdeal)]
    [IsMinimal O_u (C.baseChange F_u)] (k : ℕ) :
    (C.formalPointFiltration u k).FiniteIndex := by
  cases k with
  | zero => rw [C.formalPointFiltration_zero u]; infer_instance
  | succ k =>
    refine ⟨?_⟩
    rw [C.index_formalPointFiltration_eq_mul_index_kerReduction u]
    exact mul_ne_zero (pow_ne_zero _ Nat.card_pos.ne') AddSubgroup.FiniteIndex.index_ne_zero

end WeierstrassCurve

end
