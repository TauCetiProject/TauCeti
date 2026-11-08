/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.FormalGroup.Point.Index
-- Proof-only: the ratio of `(G : nG)` to `#G[n]` is unchanged on a finite-index subgroup.
import TauCeti.GroupTheory.Index.NSmul
-- Proof-only: the `n`-primary component is finite over a uniquely `n`-divisible subgroup.
import TauCeti.GroupTheory.Index.PrimaryComponent

/-!
# The index of `n E(F_u)`

Let `A` be a Dedekind domain with fraction field `F`, let `u` be a height-one prime of `A` with
finite residue field, and let `E` be an elliptic curve over the completion `F_u`, with ring of
integers `O_u`. For an integer `n` nonzero in `A`, the index of `n E(F_u)` is

`#(E(F_u) ⧸ n E(F_u)) = #E(F_u)[n] · #(O_u ⧸ n O_u)`.

The last factor is `1` when `n` is prime to `u`, so there the cokernel and the kernel of
multiplication by `n` have the same order; at a place above `n` it is the inverse of the
normalised absolute value of `n`; compare Silverman AEC VII.6.3, by which `E(F_u)` has a subgroup
of finite index isomorphic to `O_u` when `F_u` is a `p`-adic field.

Through the Kummer map `E(F_u) ⧸ n E(F_u) ↪ H¹(F_u, E[n])` (`WeierstrassCurve.kummerClassMap`)
the left side is the order of the local condition at `u` of the `n`-Selmer group. An isogeny
`φ : E → E'` has the local factor `#(E'(F_u) ⧸ φ E(F_u)) / #E(F_u)[φ]`, and the product of these
factors over all places enters Cassels' proof that the Birch–Swinnerton-Dyer quotient is an
isogeny invariant. For `φ = [n]` the formula above says that this factor is `#(O_u ⧸ n O_u)`; in
particular it is `1` at every place not above `n`.

The proof compares `E(F_u)` with a level of the formal group of a minimal equation. The kernel of
reduction `E₁(F_u)` has finite index: the index of the subgroup `E₀(F_u)` of points with
nonsingular reduction is finite by Tate's algorithm
(`WeierstrassCurve.Affine.finiteIndex_nonsingularReduction`), and `E₀(F_u) ⧸ E₁(F_u)` embeds in
the nonsingular points of the reduced curve over the finite residue field. `E₁(F_u)` is the
formal group `Ê(𝔪_u)`, and if `n O_u = 𝔪_u ^ e`, multiplication by `n` carries the level
`Ê(𝔪_u ^ (e + 1))`, of finite index, injectively onto `Ê(𝔪_u ^ (2 e + 1))`
(`WeierstrassCurve.FormalGroupPoint.map_nsmul_filtration`), which has index `#(O_u ⧸ 𝔪_u) ^ e`
in it. Passing to a finite-index subgroup does not change the ratio of the index of `n G` to
`#G[n]` (`AddSubgroup.index_range_nsmul_add_card_ker`).

When `n` is prime to `u`, the level is `E₁(F_u)` itself, on which multiplication by `n` is then
bijective. For every `n` nonzero in `A`, the points of `E(F_u)` killed by a power of `n` form a
finite group, since they meet the level trivially.

## Main results

* `WeierstrassCurve.exists_finiteIndex_injective_nsmul`: `E(F_u)` has a subgroup `U` of finite
  index without `n`-torsion, with `[U : n U] = #(O_u ⧸ n O_u)`.
* `WeierstrassCurve.index_range_nsmul_eq_natCard_torsionBy_mul`: the index of `n E(F_u)` is
  `#E(F_u)[n] · #(O_u ⧸ n O_u)`.
* `WeierstrassCurve.exists_finiteIndex_bijective_nsmul`: `E(F_u)` has a subgroup of finite index
  on which multiplication by `n` is bijective, for `n` prime to `u`.
* `WeierstrassCurve.finiteIndex_range_nsmul`: `n E(F_u)` has finite index.
* `WeierstrassCurve.index_range_nsmul_eq_natCard_torsionBy`: its index is `#E(F_u)[n]` for `n`
  prime to `u`.
* `WeierstrassCurve.finite_primaryComponent`: the `n`-primary component of `E(F_u)` is finite.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], IV.6, VII.2, VII.6 and X.4.
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
section DividingN

local notation "m_u" => maximalIdeal O_u

-- Named: anonymous `local instance`s here get the same generated names as the ones in
-- `FormalGroup/Point/Torsion/Basic.lean`, and the names used in
-- `FormalGroup/Point/Torsion/Free.lean` are already taken in this module's imports.
private local instance isLinearTopology_adicCompletionIntegers_dividingN :
    IsLinearTopology O_u O_u :=
  u.isAdic_maximalIdeal_adicCompletionIntegers (K := F) ▸ Ideal.isLinearTopology m_u

private local instance fact_isAdic_maximalIdeal_dividingN : Fact (IsAdic m_u) :=
  ⟨u.isAdic_maximalIdeal_adicCompletionIntegers (K := F)⟩

open scoped Classical in
/-- On a minimal integral model `C`, the image of `Ê(𝔪_u ^ (e + 1))` in `E₁(F_u)`, where
`(n) = 𝔪_u ^ e`, has finite index, has no nonzero `n`-torsion, and contains `n` times itself with
index `#(O_u ⧸ n O_u)`. -/
private theorem exists_finiteIndex_injective_nsmul_of_isMinimal
    {n e : ℕ} (C : WeierstrassCurve O_u) [(C.baseChange F_u).IsElliptic]
    [IsMinimal O_u (C.baseChange F_u)]
    (hne : Ideal.span {(n : O_u)} = m_u ^ e) :
    ∃ U : AddSubgroup (C.baseChange F_u).toAffine.Point, U.FiniteIndex ∧
      Function.Injective (fun P : U ↦ n • P) ∧
      (nsmulAddMonoidHom (α := U) n).range.index = Nat.card (O_u ⧸ Ideal.span {(n : O_u)}) := by
  let V := FormalGroupPoint.filtration C m_u (e + 1)
  let ι := C.formalPointHomAdicCompletion u
  have hι : Function.Injective ι := C.formalPointHomAdicCompletion_injective u
  have hmap : V.map ι = C.formalPointFiltration u (e + 1) := by
    ext P
    simp only [V, ι, AddSubgroup.mem_map, FormalGroupPoint.mem_filtration,
      C.mem_formalPointFiltration_iff u]
  let φ : V ≃+ C.formalPointFiltration u (e + 1) :=
    (V.equivMapOfInjective ι hι).trans (AddEquiv.addSubgroupCongr hmap)
  refine ⟨C.formalPointFiltration u (e + 1), inferInstance, ?_, ?_⟩
  · exact (φ.injective_nsmul_iff n).mp
      (FormalGroupPoint.nsmul_filtration_injective hne (Nat.lt_succ_self e))
  · rw [← AddEquiv.index_range_nsmulAddMonoidHom φ,
      FormalGroupPoint.index_range_nsmul_filtration hne (Nat.lt_succ_self e), hne,
      TauCeti.IsDiscreteValuationRing.natCard_quotient_maximalIdeal_pow]

end DividingN

variable (W : WeierstrassCurve (u.adicCompletion F)) [W.IsElliptic]
  [DecidableEq (u.adicCompletion F)] {n : ℕ}

/-- **`E(F_u)` has a subgroup `U` of finite index without `n`-torsion, with
`[U : n U] = #(O_u ⧸ n O_u)`**, for every `n` nonzero in `A`: the image of a deep enough level of
the formal group of a minimal model, transported to `E(F_u)`. -/
theorem exists_finiteIndex_injective_nsmul (hn : (n : A) ≠ 0) :
    ∃ U : AddSubgroup W.toAffine.Point, U.FiniteIndex ∧ Function.Injective (fun P : U ↦ n • P) ∧
      (nsmulAddMonoidHom (α := U) n).range.index = Nat.card (O_u ⧸ Ideal.span {(n : O_u)}) := by
  -- The minimal-model results fix classical equality decisions; equality decisions are unique.
  cases Subsingleton.elim ‹DecidableEq F_u› (fun a b ↦ Classical.propDecidable (a = b))
  classical
  obtain ⟨e, hne⟩ := u.exists_span_algebraMap_adicCompletionIntegers_eq_maximalIdeal_pow (K := F) hn
  rw [map_natCast] at hne
  -- on a minimal model `C.baseChange F_u`, take a level of the formal group
  have key : ∀ (W' : WeierstrassCurve F_u) [W'.IsElliptic] [IsMinimal O_u W'],
      ∃ U : AddSubgroup W'.toAffine.Point, U.FiniteIndex ∧
        Function.Injective (fun P : U ↦ n • P) ∧
        (nsmulAddMonoidHom (α := U) n).range.index =
          Nat.card (O_u ⧸ Ideal.span {(n : O_u)}) := by
    intro W' _ _
    obtain ⟨C, rfl⟩ := (inferInstance : IsIntegral O_u W').integral
    exact exists_finiteIndex_injective_nsmul_of_isMinimal u C hne
  obtain ⟨V, hV⟩ := W.exists_isMinimal O_u
  obtain ⟨U, hU, hinj, hidx⟩ := key (V • W)
  -- and transport it along the change of variables
  let e := Affine.Point.addEquivVariableChange W V
  let φ := e.addSubgroupMap U
  refine ⟨U.map (e : (V • W).toAffine.Point →+ W.toAffine.Point),
    ⟨by rw [AddSubgroup.index_map_equiv]; exact hU.index_ne_zero⟩, ?_, ?_⟩
  · exact (φ.injective_nsmul_iff n).mp hinj
  · rw [← AddEquiv.index_range_nsmulAddMonoidHom φ, hidx]

/-- **The local Kummer index**: for an elliptic curve over the completion at a height-one prime
`u` with finite residue field, and an integer `n` nonzero in `A`,

`#(E(F_u) ⧸ n E(F_u)) = #E(F_u)[n] · #(O_u ⧸ n O_u)`.

At a place prime to `n` the last factor is `1`; at a place above `n` it is the inverse of the
normalised absolute value of `n`. -/
theorem index_range_nsmul_eq_natCard_torsionBy_mul (hn : (n : A) ≠ 0) :
    (nsmulAddMonoidHom (α := W.toAffine.Point) n).range.index =
      Nat.card (Submodule.torsionBy ℤ W.toAffine.Point n) *
        Nat.card (O_u ⧸ Ideal.span {(n : O_u)}) := by
  obtain ⟨U, _, hinj, hidx⟩ := W.exists_finiteIndex_injective_nsmul u hn
  have hkerU : (nsmulAddMonoidHom (α := U) n).ker = ⊥ :=
    (AddMonoidHom.ker_eq_bot_iff _).mpr hinj
  -- `(E : n E) · #U[n] = #E[n] · (U : n U)`, and `#U[n] = 1`
  have h := AddSubgroup.index_range_nsmul_add_card_ker U n
  rw [hkerU, AddSubgroup.card_bot, mul_one, hidx] at h
  have hker : Nat.card (nsmulAddMonoidHom (α := W.toAffine.Point) n).ker =
      Nat.card (Submodule.torsionBy ℤ W.toAffine.Point n) :=
    Nat.card_congr (Equiv.subtypeEquivRight fun P ↦ by
      rw [AddMonoidHom.mem_ker, nsmulAddMonoidHom_apply, Submodule.mem_torsionBy_iff,
        natCast_zsmul])
  rw [h, hker]

/-- **`E(F_u)` has a uniquely `n`-divisible subgroup of finite index** for `n` prime to `u`. -/
theorem exists_finiteIndex_bijective_nsmul (hn : (n : A) ∉ u.asIdeal) :
    ∃ U : AddSubgroup W.toAffine.Point, U.FiniteIndex ∧ Function.Bijective (fun P : U ↦ n • P) := by
  obtain ⟨U, hU, hinj, hidx⟩ :=
    W.exists_finiteIndex_injective_nsmul u (ne_of_mem_of_not_mem u.asIdeal.zero_mem hn).symm
  rw [← map_natCast (algebraMap A O_u),
    u.natCard_quotient_span_algebraMap_adicCompletionIntegers hn, AddSubgroup.index_eq_one,
    AddMonoidHom.range_eq_top] at hidx
  exact ⟨U, hU, hinj, hidx⟩

/-- **`n E(F_u)` has finite index in `E(F_u)`** for an elliptic curve over the completion at a
height-one prime `u` with finite residue field, and an integer `n` nonzero in `A`: it contains
`n U` for the subgroup `U` of `WeierstrassCurve.exists_finiteIndex_injective_nsmul`. -/
theorem finiteIndex_range_nsmul (hn : (n : A) ≠ 0) :
    (nsmulAddMonoidHom (α := W.toAffine.Point) n).range.FiniteIndex := by
  obtain ⟨U, hU, -, hidx⟩ := W.exists_finiteIndex_injective_nsmul u hn
  -- `O_u ⧸ n O_u` is finite, as `n O_u` contains a power of the maximal ideal
  have hfin : Finite (O_u ⧸ Ideal.span {(n : O_u)}) := by
    obtain ⟨e, hne⟩ :=
      u.exists_span_algebraMap_adicCompletionIntegers_eq_maximalIdeal_pow (K := F) hn
    rw [map_natCast] at hne
    exact finite_quotient_iff.mpr ⟨e, hne.ge⟩
  have hnU : ((nsmulAddMonoidHom (α := U) n).range.map U.subtype).FiniteIndex := by
    refine ⟨?_⟩
    rw [AddSubgroup.index_map_subtype, hidx]
    exact mul_ne_zero Nat.card_pos.ne' hU.index_ne_zero
  refine AddSubgroup.finiteIndex_of_le
    (H := (nsmulAddMonoidHom (α := U) n).range.map U.subtype) ?_
  rintro _ ⟨_, ⟨Q, rfl⟩, rfl⟩
  exact ⟨Q, (AddSubgroup.coe_nsmul _ _ _).symm⟩

/-- **The local Kummer index at a place prime to `n`**: for an elliptic curve over the completion
at a height-one prime `u` with finite residue field, and an integer `n` prime to `u`,

`#(E(F_u) ⧸ n E(F_u)) = #E(F_u)[n]`.

Both sides are finite (`WeierstrassCurve.finiteIndex_range_nsmul`). -/
theorem index_range_nsmul_eq_natCard_torsionBy (hn : (n : A) ∉ u.asIdeal) :
    (nsmulAddMonoidHom (α := W.toAffine.Point) n).range.index =
      Nat.card (Submodule.torsionBy ℤ W.toAffine.Point n) := by
  rw [W.index_range_nsmul_eq_natCard_torsionBy_mul u
      (ne_of_mem_of_not_mem u.asIdeal.zero_mem hn).symm,
    ← map_natCast (algebraMap A O_u),
    u.natCard_quotient_span_algebraMap_adicCompletionIntegers hn, mul_one]

/-- **The `n`-primary component of `E(F_u)` is finite** for `n` nonzero in `A`: the points killed
by a power of `n` meet the subgroup of `WeierstrassCurve.exists_finiteIndex_injective_nsmul`, which
has finite index and no nonzero `n`-torsion, trivially. -/
theorem finite_primaryComponent (hn : (n : A) ≠ 0) :
    Finite (AddCommGroup.primaryComponent W.toAffine.Point n) := by
  obtain ⟨U, _, hinj, -⟩ := W.exists_finiteIndex_injective_nsmul u hn
  exact U.finite_primaryComponent_of_injective hinj

end WeierstrassCurve
