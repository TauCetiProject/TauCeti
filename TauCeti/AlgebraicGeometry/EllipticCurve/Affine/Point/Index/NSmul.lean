/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.FormalGroup.Point.KerReduction
-- Proof-only: `E₀(F_u)` has finite index, by Tate's algorithm.
import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Point.Index.Bound
-- Proof-only: the reduced curve over a finite residue field has finitely many points.
import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.FinitePoint
-- Proof-only: multiplication by `n` is bijective on `E₁(F_u)`.
import TauCeti.AlgebraicGeometry.EllipticCurve.FormalGroup.Point.Division
-- Proof-only: the residue field of `O_u` is finite, and `O_u` is Henselian.
import TauCeti.RingTheory.DedekindDomain.AdicValuation.Completion
-- Proof-only: the ratio of `(G : nG)` to `#G[n]` is unchanged on a finite-index subgroup.
import TauCeti.GroupTheory.Index.NSmul

/-!
# The index of `n E(F_u)` at a place prime to `n`

Let `A` be a Dedekind domain with fraction field `F`, let `u` be a height-one prime of `A` with
finite residue field, and let `E` be an elliptic curve over the completion `F_u`. For an integer
`n` prime to `u`, multiplication by `n` has finite cokernel on `E(F_u)`, of the same order as its
kernel:

`#(E(F_u) ⧸ n E(F_u)) = #E(F_u)[n]`.

Through the Kummer map `E(F_u) ⧸ n E(F_u) ↪ H¹(F_u, E[n])` (`WeierstrassCurve.kummerClassMap`)
the left side is the order of the local condition at `u` of the `n`-Selmer group. An isogeny
`φ : E → E'` has the local factor `#(E'(F_u) ⧸ φ E(F_u)) / #E(F_u)[φ]`, and the product of these
factors over all places enters Cassels' proof that the Birch–Swinnerton-Dyer quotient is an
isogeny invariant. For `φ = [n]` the equality above says that this factor is `1` at every place
not above `n`.

The proof compares `E(F_u)` with the kernel of reduction `E₁(F_u)` of a minimal equation. The
subgroup `E₁(F_u)` has finite index: the index of the subgroup `E₀(F_u)` of points with
nonsingular reduction is finite by Tate's algorithm
(`WeierstrassCurve.Affine.finiteIndex_nonsingularReduction`), and `E₀(F_u) ⧸ E₁(F_u)` embeds in
the nonsingular points of the reduced curve over the finite residue field. On `E₁(F_u)`, which is
the formal group, multiplication by `n` is bijective
(`WeierstrassCurve.nsmul_kerReduction_bijective`). Passing to a finite-index subgroup does not
change the ratio of the index of `n G` to `#G[n]` (`AddSubgroup.index_range_nsmul_add_card_ker`),
and on `E₁(F_u)` both are `1`.

## Main results

* `WeierstrassCurve.finiteIndex_kerReduction`: the kernel of reduction of a minimal equation over
  `O_u` has finite index in `E(F_u)` when the residue field is finite.
* `WeierstrassCurve.finiteIndex_range_nsmul`: `n E(F_u)` has finite index for `n` prime to `u`.
* `WeierstrassCurve.index_range_nsmul_eq_natCard_torsionBy`: its index is `#E(F_u)[n]`.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], VII.2, VII.6 and X.4.
* J. W. S. Cassels, *Arithmetic on curves of genus 1. VIII. On conjectures of Birch and
  Swinnerton-Dyer*, J. Reine Angew. Math. 217 (1965), 180–199.
-/

public section

open IsDedekindDomain IsLocalRing

namespace WeierstrassCurve

variable {A : Type*} [CommRing A] [IsDedekindDomain A]
  {F : Type*} [Field F] [Algebra A F] [IsFractionRing A F]
  (u : HeightOneSpectrum A) [Finite (A ⧸ u.asIdeal)]

local notation "O_u" => u.adicCompletionIntegers F
local notation "F_u" => u.adicCompletion F
local notation "R_u" =>
  Valuation.valuationSubring
    (Valued.v : Valuation (u.adicCompletion F) (WithZero (Multiplicative ℤ)))

section KerReduction

variable (C : WeierstrassCurve (u.adicCompletionIntegers F))
  [(C.baseChange (u.adicCompletion F)).IsElliptic]

open scoped Classical in
/-- **`E₁(F_u)` has finite index in `E(F_u)`**: the kernel of reduction of a minimal equation over
`O_u` has finite index in the points over `F_u` when the residue field is finite. -/
instance finiteIndex_kerReduction [IsMinimal O_u (C.baseChange F_u)] :
    (C.kerReduction u).FiniteIndex := by
  have : IsDiscreteValuationRing R_u := inferInstanceAs (IsDiscreteValuationRing O_u)
  have : HenselianLocalRing R_u := inferInstanceAs (HenselianLocalRing O_u)
  have : Finite (ResidueField R_u) := inferInstanceAs (Finite (ResidueField O_u))
  have : IsMinimal R_u (C.baseChange F_u) := inferInstanceAs (IsMinimal O_u (C.baseChange F_u))
  let W := (C.baseChange F_u).toAffine
  have hle : C.kerReduction u ≤ W.nonsingularReduction Valued.v := by
    intro P hP
    rcases (Affine.Point.reduction_eq_zero_iff Valued.v P).mp ((C.mem_kerReduction_iff u).mp hP)
      with rfl | hP
    · exact zero_mem _
    · exact Affine.mem_nonsingularReduction_of_one_lt Valued.v hP
  have hker : (C.kerReduction u).addSubgroupOf (W.nonsingularReduction Valued.v) =
      (W.nonsingularReductionHom Valued.v).ker := by
    ext P
    rw [AddSubgroup.mem_addSubgroupOf, Affine.mem_ker_nonsingularReductionHom_iff,
      C.mem_kerReduction_iff u, Affine.Point.reduction_eq_zero_iff]
  refine ⟨?_⟩
  rw [← AddSubgroup.relIndex_mul_index hle, AddSubgroup.relIndex, hker, AddSubgroup.index_ker]
  exact mul_ne_zero Nat.card_pos.ne' AddSubgroup.FiniteIndex.index_ne_zero

open scoped Classical in
/-- For a minimal equation over `O_u`, `n E(F_u)` has finite index `#E(F_u)[n]`. -/
private theorem finiteIndex_and_index_eq_of_isMinimal [IsMinimal O_u (C.baseChange F_u)] {n : ℕ}
    (hn : (n : A) ∉ u.asIdeal) :
    (nsmulAddMonoidHom (α := (C.baseChange F_u).toAffine.Point) n).range.FiniteIndex ∧
      (nsmulAddMonoidHom (α := (C.baseChange F_u).toAffine.Point) n).range.index =
        Nat.card (nsmulAddMonoidHom (α := (C.baseChange F_u).toAffine.Point) n).ker := by
  have hbij := C.nsmul_kerReduction_bijective u hn
  have hrange : (nsmulAddMonoidHom (α := C.kerReduction u) n).range = ⊤ :=
    AddMonoidHom.range_eq_top.mpr hbij.2
  have hkerU : (nsmulAddMonoidHom (α := C.kerReduction u) n).ker = ⊥ :=
    (AddMonoidHom.ker_eq_bot_iff _).mpr hbij.1
  refine ⟨AddSubgroup.finiteIndex_of_le (H := C.kerReduction u) ?_, ?_⟩
  · intro P hP
    obtain ⟨Q, hQ⟩ := hbij.2 ⟨P, hP⟩
    exact ⟨Q, congrArg Subtype.val hQ⟩
  · simpa [hrange, hkerU] using AddSubgroup.index_range_nsmul_add_card_ker (C.kerReduction u) n

end KerReduction

variable (W : WeierstrassCurve (u.adicCompletion F)) [W.IsElliptic]
  [DecidableEq (u.adicCompletion F)] {n : ℕ}

/-- `n E(F_u)` has finite index `#E(F_u)[n]`, stated with the kernel of multiplication by `n`. -/
private theorem finiteIndex_and_index_eq (hn : (n : A) ∉ u.asIdeal) :
    (nsmulAddMonoidHom (α := W.toAffine.Point) n).range.FiniteIndex ∧
      (nsmulAddMonoidHom (α := W.toAffine.Point) n).range.index =
        Nat.card (nsmulAddMonoidHom (α := W.toAffine.Point) n).ker := by
  -- The minimal-model results fix classical equality decisions; equality decisions are unique.
  cases Subsingleton.elim ‹DecidableEq F_u› (fun a b ↦ Classical.propDecidable (a = b))
  classical
  obtain ⟨V, hV⟩ := W.exists_isMinimal O_u
  let e := Affine.Point.addEquivVariableChange W V
  have key : ∀ (W' : WeierstrassCurve F_u) [W'.IsElliptic] [IsMinimal O_u W'],
      (nsmulAddMonoidHom (α := W'.toAffine.Point) n).range.FiniteIndex ∧
        (nsmulAddMonoidHom (α := W'.toAffine.Point) n).range.index =
          Nat.card (nsmulAddMonoidHom (α := W'.toAffine.Point) n).ker := by
    intro W' _ hW'
    obtain ⟨C, rfl⟩ := (inferInstance : IsIntegral O_u W').integral
    exact finiteIndex_and_index_eq_of_isMinimal u C hn
  obtain ⟨hfin, hidx⟩ := key (V • W)
  have hker : Nat.card (nsmulAddMonoidHom (α := (V • W).toAffine.Point) n).ker =
      Nat.card (nsmulAddMonoidHom (α := W.toAffine.Point) n).ker := by
    rw [← e.map_ker_nsmulAddMonoidHom n]
    exact (AddSubgroup.card_map_of_injective (f := e.toAddMonoidHom) e.injective).symm
  refine ⟨⟨?_⟩, ?_⟩
  · rw [← e.index_range_nsmulAddMonoidHom n]
    exact hfin.index_ne_zero
  · rw [← e.index_range_nsmulAddMonoidHom n, hidx, hker]

/-- **`n E(F_u)` has finite index in `E(F_u)`** for an elliptic curve over the completion at a
height-one prime `u` with finite residue field, and an integer `n` prime to `u`. -/
theorem finiteIndex_range_nsmul (hn : (n : A) ∉ u.asIdeal) :
    (nsmulAddMonoidHom (α := W.toAffine.Point) n).range.FiniteIndex :=
  (finiteIndex_and_index_eq u W hn).1

/-- **The local Kummer index at a place prime to `n`**: for an elliptic curve over the completion
at a height-one prime `u` with finite residue field, and an integer `n` prime to `u`,

`#(E(F_u) ⧸ n E(F_u)) = #E(F_u)[n]`.

Both sides are finite (`WeierstrassCurve.finiteIndex_range_nsmul`). -/
theorem index_range_nsmul_eq_natCard_torsionBy (hn : (n : A) ∉ u.asIdeal) :
    (nsmulAddMonoidHom (α := W.toAffine.Point) n).range.index =
      Nat.card (Submodule.torsionBy ℤ W.toAffine.Point n) := by
  rw [(finiteIndex_and_index_eq u W hn).2]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun P ↦ by
    rw [AddMonoidHom.mem_ker, nsmulAddMonoidHom_apply, Submodule.mem_torsionBy_iff,
      natCast_zsmul])

end WeierstrassCurve
