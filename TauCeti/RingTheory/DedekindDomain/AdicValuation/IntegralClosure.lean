/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.FiniteExtension
public import TauCeti.NumberTheory.LocalField.IntegerRing
public import TauCeti.RingTheory.DedekindDomain.AdicValuation.IntegersExtension
public import TauCeti.RingTheory.DedekindDomain.AdicValuation.ValuativeExtension

/-!
# The completed integer rings are an integral closure

Let `R ⊆ B` be Dedekind domains with fraction fields `K ⊆ L`, and let `w` be a height-one prime of
`B` lying over the height-one prime `v` of `R`, both with finite residue fields. The completions
`K_v` and `L_w` are then nonarchimedean local fields and the canonical map `K_v → L_w` makes `L_w`
a valuative extension of `K_v`, inside which the completed integer rings sit as `𝒪_v ⊆ 𝒪_w`.

This file proves that `L_w` is a finite extension of `K_v`, that `𝒪_w` is the integral closure of
`𝒪_v` in `L_w`, and that `𝒪_w` is a finite `𝒪_v`-module of rank `[L_w : K_v]`. Together with the
algebra structure, the scalar towers and the torsion-freeness of `𝒪_w` over `𝒪_v`, and with the
`IsFractionRing`, `IsIntegrallyClosed` and `IsDedekindDomain` instances that the valuation subring
of a complete discretely valued field already carries, these are the hypotheses that the different
ideal and the conductor of the local extension `𝒪_w / 𝒪_v` take, so that those objects can be
formed at all.

The integrality criterion is that of a complete discretely valued field: the valuation of `L_w` is
the unique extension of the valuation of `K_v`, so an element of `L_w` is integral over `𝒪_v`
exactly when its valuation is at most `1`. The finiteness of `𝒪_w` over `𝒪_v` is transported from
`TauCeti.integerRingModuleFinite`, which is proved for the ring of integers of a valuative
relation, rather than deduced from the integral closure by `IsIntegralClosure.finite`: the latter
assumes separability of `L_w / K_v`, which holds for a number field but not for a local field of
equal characteristic, whereas the transport is unconditional.

## Main results

* `IsDedekindDomain.HeightOneSpectrum.adicCompletion_moduleFinite`: `L_w` is a finite `K_v`-module
  for the canonical algebra structure.
* `IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers_isIntegralClosure`: `𝒪_w` is the
  integral closure of `𝒪_v` in `L_w`.
* `IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers_moduleFinite` and
  `IsDedekindDomain.HeightOneSpectrum.finrank_adicCompletionIntegers`: `𝒪_w` is a finite
  `𝒪_v`-module, of rank `[L_w : K_v]`.
* `IsDedekindDomain.HeightOneSpectrum.integerEquivAdicCompletionIntegers_algebraMap`: the
  identifications `𝒪[K_v] = 𝒪_v` and `𝒪[L_w] = 𝒪_w` commute with the two maps between the integer
  rings.

## References

* [J. Neukirch, *Algebraic Number Theory*][Neukirch1992], Chapter II, §4 and §6.
* [J.-P. Serre, *Corps Locaux*][serre1968], Chapter II, §2.
-/

public section
noncomputable section

open IsDedekindDomain ValuativeRel
open scoped AdicCompletionExtension

namespace IsDedekindDomain.HeightOneSpectrum

variable {R : Type*} [CommRing R] [IsDedekindDomain R]
  {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
  {B : Type*} [CommRing B] [IsDedekindDomain B] [Algebra R B]
  {L : Type*} [Field L] [Algebra K L] [Algebra R L] [IsScalarTower R K L]
  [Algebra B L] [IsFractionRing B L] [IsScalarTower R B L]
  (v : HeightOneSpectrum R) (w : HeightOneSpectrum B) [w.asIdeal.LiesOver v.asIdeal]
  [Finite (R ⧸ v.asIdeal)] [Finite (B ⧸ w.asIdeal)]

variable (K L)

/-- **A completion of an extension is a finite extension of completions.** For the canonical
algebra structure of `adicCompletionExtension`, `L_w` is a finite `K_v`-module. Mathlib's
instance for an adic completion assumes that `K` and `L` are number fields and holds for an
arbitrary compatible algebra structure; this one is about the canonical structure over an
arbitrary Dedekind base. -/
theorem adicCompletion_moduleFinite :
    Module.Finite (v.adicCompletion K) (w.adicCompletion L) :=
  TauCeti.finite_of_valuativeExtension _ _

scoped[AdicCompletionExtension] attribute [instance]
  IsDedekindDomain.HeightOneSpectrum.adicCompletion_moduleFinite

/-- **`𝒪_w` is the integral closure of `𝒪_v` in `L_w`.** An element of `L_w` is integral over
`𝒪_v` exactly when its valuation is at most `1`, because the valuation of `L_w` is the unique
extension of the valuation of `K_v`. -/
theorem adicCompletionIntegers_isIntegralClosure :
    IsIntegralClosure (w.adicCompletionIntegers L) (v.adicCompletionIntegers K)
      (w.adicCompletion L) where
  algebraMap_injective := Subtype.val_injective
  isIntegral_iff := by
    intro x
    rw [Valuation.Integers.isIntegral_iff_valuation_le_one
        (v.valuation_integers_adicCompletionIntegers (K := K)) x,
      ← w.mem_adicCompletionIntegers_iff_valuation_le_one (K := L) x]
    exact ⟨fun h ↦ ⟨⟨x, h⟩, rfl⟩, fun ⟨y, hy⟩ ↦ hy ▸ y.2⟩

scoped[AdicCompletionExtension] attribute [instance]
  IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers_isIntegralClosure

omit [Finite (R ⧸ v.asIdeal)] [Finite (B ⧸ w.asIdeal)] in
/-- **The identifications of the integer rings are natural.** The identifications
`𝒪[K_v] = 𝒪_v` and `𝒪[L_w] = 𝒪_w` commute with the map `𝒪[K_v] → 𝒪[L_w]` of the valuative
extension and the map `𝒪_v → 𝒪_w` of `adicCompletionIntegersExtension`, both of which are
restrictions of the canonical map `K_v → L_w`. -/
@[simp]
theorem integerEquivAdicCompletionIntegers_algebraMap (x : 𝒪[v.adicCompletion K]) :
    w.integerEquivAdicCompletionIntegers (K := L)
        (algebraMap 𝒪[v.adicCompletion K] 𝒪[w.adicCompletion L] x) =
      algebraMap (v.adicCompletionIntegers K) (w.adicCompletionIntegers L)
        (v.integerEquivAdicCompletionIntegers (K := K) x) :=
  Subtype.val_injective <| by
    -- both sides are the canonical map `K_v → L_w` applied to `x`, read through the two
    -- coercions into `L_w`
    rw [coe_integerEquivAdicCompletionIntegers, algebraMap_adicCompletionIntegersExtensionAlgebra,
      coe_adicCompletionIntegersExtension, coe_integerEquivAdicCompletionIntegers,
      TauCeti.coe_algebraMap_integerRing, algebraMap_adicCompletionExtensionAlgebra]

omit [Finite (R ⧸ v.asIdeal)] [Finite (B ⧸ w.asIdeal)] in
/-- The naturality square of the previous lemma, in the composed form that
`Module.Finite.of_equiv_equiv` and `Algebra.finrank_eq_of_equiv_equiv` take. -/
private theorem integerEquivAdicCompletionIntegers_comp :
    (algebraMap (v.adicCompletionIntegers K) (w.adicCompletionIntegers L)).comp
        ((v.integerEquivAdicCompletionIntegers (K := K)) : _ →+* _) =
      ((w.integerEquivAdicCompletionIntegers (K := L)) : _ →+* _).comp
        (algebraMap 𝒪[v.adicCompletion K] 𝒪[w.adicCompletion L]) :=
  RingHom.ext fun x ↦ (integerEquivAdicCompletionIntegers_algebraMap K L v w x).symm

/-- **`𝒪_w` is a finite `𝒪_v`-module.** The identifications `𝒪[K_v] = 𝒪_v` and `𝒪[L_w] = 𝒪_w`
carry `TauCeti.integerRingModuleFinite` over to the completed integer rings. -/
theorem adicCompletionIntegers_moduleFinite :
    Module.Finite (v.adicCompletionIntegers K) (w.adicCompletionIntegers L) :=
  Module.Finite.of_equiv_equiv (v.integerEquivAdicCompletionIntegers (K := K))
    (w.integerEquivAdicCompletionIntegers (K := L))
    (integerEquivAdicCompletionIntegers_comp K L v w)

scoped[AdicCompletionExtension] attribute [instance]
  IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers_moduleFinite

/-- **`𝒪_w` is a lattice of full rank in `L_w`.** Its rank as an `𝒪_v`-module is the degree
`[L_w : K_v]` of the local extension. -/
@[simp]
theorem finrank_adicCompletionIntegers :
    Module.finrank (v.adicCompletionIntegers K) (w.adicCompletionIntegers L) =
      Module.finrank (v.adicCompletion K) (w.adicCompletion L) := by
  rw [← TauCeti.finrank_integerRing (v.adicCompletion K) (w.adicCompletion L)]
  exact (Algebra.finrank_eq_of_equiv_equiv (v.integerEquivAdicCompletionIntegers (K := K))
    (w.integerEquivAdicCompletionIntegers (K := L))
    (integerEquivAdicCompletionIntegers_comp K L v w)).symm

end IsDedekindDomain.HeightOneSpectrum

end

end
