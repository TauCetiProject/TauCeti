/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.DiscreteValuationRing.IntegrallyClosed
public import TauCeti.RingTheory.Henselian.Integral
public import Mathlib.RingTheory.AdicCompletion.Basic
public import TauCeti.RingTheory.Nagata
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.LocalRing.Module
import Mathlib.RingTheory.Localization.Module
import TauCeti.RingTheory.AdicCompletion.Pi
import TauCeti.RingTheory.DedekindDomain.IntegralClosure

/-!
# Integral closures of henselian and complete discrete valuation rings

The integral closure of a henselian DVR in a finite extension of its fraction field is again
a DVR, without a separability assumption. No finiteness or perfection of the residue field,
and no normality of the field extension, is needed. Completeness of integral closures is treated
separately in `TauCeti/RingTheory/AdicCompletion/IntegralClosure.lean`.

These results provide integer rings for ramification theory over complete discretely valued
fields with arbitrary residue fields. When `L / K` is separable (`Algebra.IsSeparable K L`),
finiteness, freeness and rank are already supplied by Mathlib's `IsIntegralClosure.finite`,
`IsIntegralClosure.module_free` and `IsIntegralClosure.rank`; the additional step here is locality.
A domain integral over a henselian local ring is local, and a local Dedekind domain that is not a
field is a DVR.
Krull–Akizuki supplies Dedekindness even without separability.

Over a complete DVR the integral closure is moreover a finite free module without any separability
assumption, on `L / K` or on the residue field extension. This covers, for instance, the
inseparable extensions of `k((t))` for an imperfect field `k`, where the trace form vanishes and
Mathlib's argument does not apply. Determinant norms of the integer ring of such an extension, and
its finite filtrations by powers of the maximal ideal, need this finiteness. Consequently a
complete DVR is a Japanese ring and a Nagata ring.

`TauCeti.IsIntegralClosure.isDiscreteValuationRing` allows any model of the integral closure
and any chosen fraction field. `TauCeti.integralClosure.isDiscreteValuationRing` specializes to
`integralClosure A L`, still allowing a chosen fraction field. The instance
`TauCeti.integralClosure.isDiscreteValuationRing_fractionRing` uses `FractionRing A`, as do
Mathlib's integral-closure instances.

## Main results

* `TauCeti.IsIntegralClosure.isDiscreteValuationRing`: over a henselian DVR the integral closure
  in a finite extension is a DVR.
* `TauCeti.IsIntegralClosure.finite_of_isAdicComplete` and
  `TauCeti.IsIntegralClosure.free_of_isAdicComplete`: over a complete DVR it is a finite free
  module. The instances `TauCeti.integralClosure.finite_of_isAdicComplete` and
  `TauCeti.integralClosure.free_of_isAdicComplete` give this for `integralClosure A L` over
  `FractionRing A`.
* `TauCeti.Ring.IsJapanese.of_isAdicComplete` and `TauCeti.Ring.IsNagata.of_isAdicComplete`: a
  complete DVR is Japanese and Nagata.

## References

* J.-P. Serre, *Local Fields*, Chapter I, §4 and Chapter II, §2, Proposition 3.
* [Stacks Project, Lemma 10.162.8 (032W)](https://stacks.math.columbia.edu/tag/032W): a complete
  Noetherian local ring is Nagata; here only the DVR case is proved.
-/

public section

namespace TauCeti

/-- The integral closure of a henselian DVR in a finite extension of its fraction field is a
DVR, without a separability assumption. The closure may be any model of `IsIntegralClosure`. -/
theorem IsIntegralClosure.isDiscreteValuationRing
    (A K L B : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [HenselianRing A (IsLocalRing.maximalIdeal A)] [Field K] [Algebra A K] [IsFractionRing A K]
    [Field L] [Algebra K L] [FiniteDimensional K L]
    [Algebra A L] [IsScalarTower A K L]
    [CommRing B] [IsDomain B] [Algebra A B] [Algebra B L] [IsScalarTower A B L]
    [IsIntegralClosure B A L] : IsDiscreteValuationRing B := by
  have := IsIntegralClosure.isDedekindDomain A K L B
  have := _root_.IsIntegralClosure.isIntegral_algebra A L (A := B)
  have := IsIntegralClosure.isLocalRing A L B
  apply IsDiscreteValuationRing.of_krullDimLE_one
  intro hB
  exact IsDiscreteValuationRing.not_isField A
    (isField_of_isIntegral_of_isField (algebraMap_injective_of_field_isFractionRing A B K L) hB)

namespace integralClosure

/-- The integral closure of a henselian DVR in a finite extension of a chosen fraction field is
a DVR, without a separability assumption. This is not an instance because `K` cannot be inferred;
see `isDiscreteValuationRing_fractionRing` for the instance using `FractionRing A`. -/
theorem isDiscreteValuationRing (A K L : Type*) [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A] [HenselianRing A (IsLocalRing.maximalIdeal A)]
    [Field K] [Algebra A K] [IsFractionRing A K]
    [Field L] [Algebra A L] [Algebra K L] [IsScalarTower A K L] [FiniteDimensional K L] :
    IsDiscreteValuationRing (integralClosure A L) :=
  IsIntegralClosure.isDiscreteValuationRing A K L _

variable (A L : Type*) [CommRing A] [IsDomain A]
  [Field L] [Algebra A L] [Algebra (FractionRing A) L]
  [IsScalarTower A (FractionRing A) L] [FiniteDimensional (FractionRing A) L]

/-- The integral closure of a henselian DVR in a finite field extension is a DVR, without a
separability assumption. -/
instance isDiscreteValuationRing_fractionRing [IsDiscreteValuationRing A]
    [HenselianRing A (IsLocalRing.maximalIdeal A)] :
    IsDiscreteValuationRing (integralClosure A L) :=
  isDiscreteValuationRing A (FractionRing A) L

end integralClosure

section Complete

/-! ### Finiteness over a complete DVR

Over a complete DVR `A` the integral closure `B` of `A` in a finite extension `L` of its fraction
field `K` is a finite free `A`-module, again without a separability assumption.

The residue field `k` of `A` controls the size of `B`. Since `B` is torsion-free over the
Dedekind domain `A`, it is flat, so a family in `B` whose image in `k ⊗[A] B` is `k`-linearly
independent is `A`-linearly independent, hence `K`-linearly independent in `L`. So `k ⊗[A] B` has
dimension at most `[L : K]` over `k`. A spanning family of `k ⊗[A] B` lifts to a family in `B`
spanning `B` modulo `𝔪_A B`. As `B` is a DVR it is `𝔪_A`-adically separated, and `A` is complete,
so by the complete Nakayama lemma the lifted family spans `B`. -/

open IsLocalRing TensorProduct

variable (A K L B : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  [Field K] [Algebra A K] [IsFractionRing A K]
  [Field L] [Algebra K L] [Algebra A L] [IsScalarTower A K L]
  [CommRing B] [Algebra A B] [Algebra B L] [IsScalarTower A B L] [IsIntegralClosure B A L]

/-- Over a DVR `A` with residue field `k`, the reduction `k ⊗[A] B` of the integral closure `B` of
`A` in an extension `L` of `K = Frac A` has `k`-dimension at most `[L : K]`. -/
private theorem rank_residueField_tensorProduct_le [FiniteDimensional K L] :
    Module.rank (ResidueField A) (ResidueField A ⊗[A] B) ≤ Module.finrank K L := by
  have : Module.IsTorsionFree A L := .trans_faithfulSMul A K L
  have : Module.IsTorsionFree A B := IsIntegralClosure.isTorsionFree A L
  apply rank_le
  intro s hs
  choose v hv using fun i : s ↦
    TensorProduct.mk_surjective A B (ResidueField A) residue_surjective (i : ResidueField A ⊗[A] B)
  have hvA : LinearIndependent A v :=
    Module.IsLocalRing.linearIndependent_of_flat v (by convert hs using 1; ext i; exact hv i)
  have hvL : LinearIndependent A (algebraMap B L ∘ v) :=
    hvA.map' (IsScalarTower.toAlgHom A B L).toLinearMap
      (LinearMap.ker_eq_bot.mpr (IsIntegralClosure.algebraMap_injective B A L))
  simpa using ((LinearIndependent.iff_fractionRing A K).mp hvL).fintype_card_le_finrank

/-- **The integral closure of a complete DVR is finite.** Let `A` be a complete DVR with fraction
field `K` and `L` a finite extension of `K`. The integral closure of `A` in `L`, in any model `B`,
is a finite `A`-module. Neither `L / K` nor the residue field extension needs to be separable. -/
theorem IsIntegralClosure.finite_of_isAdicComplete [IsAdicComplete (maximalIdeal A) A]
    [FiniteDimensional K L] : Module.Finite A B := by
  have : IsDomain B :=
    (_root_.IsIntegralClosure.equiv A B L (integralClosure A L)).toMulEquiv.isDomain _
  have : IsDiscreteValuationRing B := IsIntegralClosure.isDiscreteValuationRing A K L B
  have : Algebra.IsIntegral A B := _root_.IsIntegralClosure.isIntegral_algebra A L
  have : FaithfulSMul A L := .trans A K L
  have : FaithfulSMul A B := .tower_bot A B L
  have : IsHausdorff (maximalIdeal A) B :=
    .of_map (J := maximalIdeal B) (map_maximalIdeal_le (algebraMap A B))
  -- The reduction `k ⊗[A] B` is finite-dimensional over the residue field `k`.
  have : Module.Finite (ResidueField A) (ResidueField A ⊗[A] B) :=
    Module.rank_lt_aleph0_iff.mp <| (rank_residueField_tensorProduct_le A K L B).trans_lt <|
      Cardinal.natCast_lt_aleph0
  obtain ⟨n, s, hs⟩ := Module.Finite.exists_fin (R := ResidueField A) (M := ResidueField A ⊗[A] B)
  choose b hb using fun i ↦
    TensorProduct.mk_surjective A B (ResidueField A) residue_surjective (s i)
  refine .of_surjective (Fintype.linearCombination A b)
    (surjective_of_mkQ_comp_surjective (I := maximalIdeal A) fun y ↦ ?_)
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  -- Lift the coefficients of `1 ⊗ y` in the spanning family `s = 1 ⊗ b`.
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun _).mp
    (hs ▸ Submodule.mem_top : (1 : ResidueField A) ⊗ₜ[A] y ∈ Submodule.span _ (Set.range s))
  choose a ha using fun i ↦ residue_surjective (c i)
  refine ⟨a, (Submodule.Quotient.eq _).mpr ?_⟩
  -- `ResidueField A` is by definition the quotient `A ⧸ 𝔪_A`.
  have hker : LinearMap.ker (TensorProduct.mk A (ResidueField A) B 1) = maximalIdeal A • ⊤ :=
    LinearMap.ker_tensorProductMk B
  rw [← hker, LinearMap.mem_ker, map_sub, sub_eq_zero, TensorProduct.mk_apply _ y, ← hc]
  simp [Fintype.linearCombination_apply, ← hb, ← ha, ← ResidueField.algebraMap_eq]

/-- **The integral closure of a complete DVR is free.** Let `A` be a complete DVR with fraction
field `K` and `L` a finite extension of `K`. The integral closure of `A` in `L`, in any model `B`,
is a finite free `A`-module, without any separability assumption. -/
theorem IsIntegralClosure.free_of_isAdicComplete [IsAdicComplete (maximalIdeal A) A]
    [FiniteDimensional K L] : Module.Free A B :=
  have := IsIntegralClosure.finite_of_isAdicComplete A K L B
  have : Module.IsTorsionFree A L := .trans_faithfulSMul A K L
  have : Module.IsTorsionFree A B := _root_.IsIntegralClosure.isTorsionFree A L
  inferInstance

end Complete

namespace integralClosure

open IsLocalRing

variable (A L : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  [IsAdicComplete (maximalIdeal A) A]
  [Field L] [Algebra A L] [Algebra (FractionRing A) L]
  [IsScalarTower A (FractionRing A) L] [FiniteDimensional (FractionRing A) L]

/-- The integral closure of a complete DVR in a finite field extension is a finite module, without
a separability assumption. -/
instance finite_of_isAdicComplete : Module.Finite A (integralClosure A L) :=
  IsIntegralClosure.finite_of_isAdicComplete A (FractionRing A) L _

/-- The integral closure of a complete DVR in a finite field extension is a free module, without
a separability assumption. -/
instance free_of_isAdicComplete : Module.Free A (integralClosure A L) :=
  IsIntegralClosure.free_of_isAdicComplete A (FractionRing A) L _

end integralClosure

namespace Ring

open IsLocalRing

variable (A : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  [IsAdicComplete (maximalIdeal A) A]

/-- A complete DVR is Japanese: its integral closure in every finite extension of its fraction
field is a finite module, by `TauCeti.IsIntegralClosure.finite_of_isAdicComplete`. -/
instance IsJapanese.of_isAdicComplete : IsJapanese A :=
  .of_finite_integralClosure (FractionRing A) fun L _ _ _ _ _ ↦
    IsIntegralClosure.finite_of_isAdicComplete A (FractionRing A) L (integralClosure A L)

/-- A complete DVR is a Nagata ring. -/
instance IsNagata.of_isAdicComplete : IsNagata A :=
  .of_isJapanese

end Ring

end TauCeti
