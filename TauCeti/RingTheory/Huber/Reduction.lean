/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.Normed
public import TauCeti.Topology.Algebra.Valued.Integer
public import Mathlib.RingTheory.Ideal.Quotient.Nilpotent
public import Mathlib.RingTheory.Ideal.Quotient.Operations
import TauCeti.Topology.Algebra.TopologicallyNilpotent.Basic

/-!
# Canonical reduction of a nonarchimedean topological ring

The canonical reduction is `A° / A°°`, using the native power-bounded subring and its
ideal of topologically nilpotent elements. It is always reduced, even when `A` is not:
topological nilpotence of a positive power implies topological nilpotence of the element.
No completeness, uniformity or noetherianity is required. A topological ring isomorphism
induces a ring isomorphism of canonical reductions.

For an ultrametric normed field `K`, `K°` is a local ring with maximal ideal `K°°`, canonically
isomorphic to the valuation ring `𝒪[K]`, so `CanonicalReduction K ≃+* 𝓀[K]`. When `K` is
nontrivially normed, the canonical reduction of any nonarchimedean topological `K`-algebra with
continuous scalar multiplication inherits a natural `𝓀[K]`-algebra structure, under which
`CanonicalReduction K ≃ₐ[𝓀[K]] 𝓀[K]`.

## Main definitions

* `TauCeti.Huber.CanonicalReduction`: the quotient `A° / A°°`.
* `TauCeti.Huber.CanonicalReduction.ringEquiv`: ring isomorphism on canonical reductions induced by
  a topological ring isomorphism.
* `TauCeti.Huber.canonicalReductionRingEquivResidueField`: `CanonicalReduction K ≃+* 𝓀[K]` for an
  ultrametric normed field `K`.
* `TauCeti.Huber.instAlgebraResidueFieldCanonicalReduction` and
  `TauCeti.Huber.canonicalReductionAlgEquivResidueField`: the natural `𝓀[K]`-algebra structure on
  `CanonicalReduction A` and `CanonicalReduction K ≃ₐ[𝓀[K]] 𝓀[K]`.

## References

* [Bosch, Güntzer, Remmert, *Non-Archimedean Analysis*][bosch-guntzer-remmert], §§6.3.1.
-/

public section

open Filter Topology IsLocalRing
open scoped NormedField Valued

namespace TauCeti.Huber

section Basic

variable (A : Type*) [CommRing A] [TopologicalSpace A] [NonarchimedeanAddGroup A]
    [ContinuousMul A]

/-- The ideal of topologically nilpotent elements in the power-bounded subring is radical. -/
theorem isRadical_topologicallyNilpotentIdeal : (topologicallyNilpotentIdeal A).IsRadical := by
  apply (Ideal.isRadical_iff_pow_one_lt 2 (by decide)).mpr
  intro a ha
  rw [mem_topologicallyNilpotentIdeal] at ha ⊢
  exact IsTopologicallyNilpotent.of_pow (by decide : 2 ≠ 0) ha

/-- The canonical reduction `A° / A°°` of a nonarchimedean topological ring. -/
abbrev CanonicalReduction := powerBoundedSubring A ⧸ topologicallyNilpotentIdeal A

instance : IsReduced (CanonicalReduction A) :=
  (Ideal.isRadical_iff_quotient_reduced _).mp (isRadical_topologicallyNilpotentIdeal A)

end Basic

section Equiv

variable {A B : Type*} [CommRing A] [TopologicalSpace A] [NonarchimedeanAddGroup A]
    [ContinuousMul A] [CommRing B] [TopologicalSpace B] [NonarchimedeanAddGroup B]
    [ContinuousMul B]

/-- A topological ring isomorphism induces a ring isomorphism of canonical reductions. -/
def CanonicalReduction.ringEquiv (e : A ≃+* B) (he : Continuous e)
    (he' : Continuous e.symm) : CanonicalReduction A ≃+* CanonicalReduction B :=
  Ideal.quotientEquiv (topologicallyNilpotentIdeal A) (topologicallyNilpotentIdeal B)
    (powerBoundedSubringEquiv e he he') (map_topologicallyNilpotentIdeal e he he').symm

@[simp]
theorem CanonicalReduction.ringEquiv_mk (e : A ≃+* B) (he : Continuous e)
    (he' : Continuous e.symm) (a : powerBoundedSubring A) :
    CanonicalReduction.ringEquiv e he he' (Ideal.Quotient.mk _ a) =
      Ideal.Quotient.mk _ (powerBoundedSubringEquiv e he he' a) :=
  Ideal.quotientEquiv_mk _ _ _ _ a

@[simp]
theorem CanonicalReduction.ringEquiv_symm_mk (e : A ≃+* B) (he : Continuous e)
    (he' : Continuous e.symm) (b : powerBoundedSubring B) :
    (CanonicalReduction.ringEquiv e he he').symm (Ideal.Quotient.mk _ b) =
      Ideal.Quotient.mk _ ((powerBoundedSubringEquiv e he he').symm b) :=
  (CanonicalReduction.ringEquiv e he he').symm_apply_eq.mpr <| by
    rw [CanonicalReduction.ringEquiv_mk, RingEquiv.apply_symm_apply]

theorem CanonicalReduction.ringEquiv_symm (e : A ≃+* B) (he : Continuous e)
    (he' : Continuous e.symm) :
    (CanonicalReduction.ringEquiv e he he').symm =
      CanonicalReduction.ringEquiv e.symm he' (by simpa using he) := by
  ext x
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective x
  refine (CanonicalReduction.ringEquiv e he he').symm_apply_eq.mpr ?_
  simp only [CanonicalReduction.ringEquiv_mk]
  exact congrArg (Ideal.Quotient.mk _) (Subtype.ext (by simp))

end Equiv

section NormedField

variable {K : Type*} [NormedField K] [IsUltrametricDist K]

/-- **The canonical reduction of an ultrametric normed field `K` is its valuation residue field
`𝓀[K]`.** -/
noncomputable def canonicalReductionRingEquivResidueField : CanonicalReduction K ≃+* 𝓀[K] :=
  Ideal.quotientEquiv (topologicallyNilpotentIdeal K) (maximalIdeal 𝒪[K])
    powerBoundedSubringEquivInteger
    (by
      rw [← maximalIdeal_powerBoundedSubring,
        IsLocalRing.map_maximalIdeal_of_surjective _ powerBoundedSubringEquivInteger.surjective])

@[simp]
theorem canonicalReductionRingEquivResidueField_mk (x : powerBoundedSubring K) :
    canonicalReductionRingEquivResidueField (Ideal.Quotient.mk _ x) =
      residue 𝒪[K] (powerBoundedSubringEquivInteger x) :=
  Ideal.quotientEquiv_mk _ _ _ _ x

@[simp]
theorem canonicalReductionRingEquivResidueField_symm_residue (c : 𝒪[K]) :
    canonicalReductionRingEquivResidueField.symm (residue 𝒪[K] c) =
      Ideal.Quotient.mk _ (powerBoundedSubringEquivInteger.symm c) :=
  canonicalReductionRingEquivResidueField.symm_apply_eq.mpr
    (((canonicalReductionRingEquivResidueField_mk _).trans
      (congrArg (residue 𝒪[K]) (powerBoundedSubringEquivInteger.apply_symm_apply c))).symm)

end NormedField

section Algebra

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]

section TopologicalAlgebra

variable {A : Type*} [CommRing A] [TopologicalSpace A] [NonarchimedeanAddGroup A]
  [ContinuousMul A] [Algebra K A] [ContinuousSMul K A]

/-- **Natural `𝓀[K]`-algebra structure on `CanonicalReduction A`.** For a nontrivially normed
ultrametric field `K` and any nonarchimedean topological `K`-algebra `A` with continuous scalar
multiplication, `𝒪[K] → A°` sends `𝓂[K]` into `A°°`, inducing `𝓀[K] →+* CanonicalReduction A`.
Nontriviality of the norm on `K` is needed: `ℚ` with the trivial norm is discrete (`𝓀[ℚ] = ℚ`)
and acts continuously on `ℚ_[p]`, whose canonical reduction `𝔽_p` admits no ring map from `ℚ`. -/
noncomputable instance instAlgebraResidueFieldCanonicalReduction :
    Algebra 𝓀[K] (CanonicalReduction A) :=
  RingHom.toAlgebra <|
    Ideal.Quotient.lift (maximalIdeal 𝒪[K])
      ((Ideal.Quotient.mk (topologicallyNilpotentIdeal A)).comp (integerToPowerBounded K A))
      fun c hc ↦ by
        rw [RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem,
          mem_topologicallyNilpotentIdeal, coe_integerToPowerBounded]
        exact IsTopologicallyNilpotent.map (continuous_algebraMap K A)
          (tendsto_pow_atTop_nhds_zero_of_norm_lt_one (Valued.integer.mem_maximalIdeal_iff.mp hc))

@[simp]
theorem algebraMap_canonicalReduction_residue (c : 𝒪[K]) :
    algebraMap 𝓀[K] (CanonicalReduction A) (residue 𝒪[K] c) =
      Ideal.Quotient.mk _ (integerToPowerBounded K A c) := (rfl)

end TopologicalAlgebra

/-- For a nontrivially normed ultrametric field `K`, `CanonicalReduction K ≃ₐ[𝓀[K]] 𝓀[K]` as
`𝓀[K]`-algebras. -/
noncomputable def canonicalReductionAlgEquivResidueField : CanonicalReduction K ≃ₐ[𝓀[K]] 𝓀[K] :=
  AlgEquiv.ofRingEquiv (f := canonicalReductionRingEquivResidueField (K := K)) fun x ↦ by
    obtain ⟨c, rfl⟩ := residue_surjective (R := 𝒪[K]) x
    rw [algebraMap_canonicalReduction_residue, canonicalReductionRingEquivResidueField_mk,
      Algebra.algebraMap_self, RingHom.id_apply]
    exact congrArg (residue 𝒪[K]) (Subtype.ext (by simp))

@[simp]
theorem coe_canonicalReductionAlgEquivResidueField :
    ⇑(canonicalReductionAlgEquivResidueField (K := K)) =
      ⇑(canonicalReductionRingEquivResidueField (K := K)) :=
  funext fun _ ↦ AlgEquiv.ofRingEquiv_apply _ _

@[simp]
theorem coe_canonicalReductionAlgEquivResidueField_symm :
    ⇑(canonicalReductionAlgEquivResidueField (K := K)).symm =
      ⇑(canonicalReductionRingEquivResidueField (K := K)).symm :=
  funext fun _ ↦ AlgEquiv.ofRingEquiv_symm_apply _ _

@[simp]
theorem toRingEquiv_canonicalReductionAlgEquivResidueField :
    (canonicalReductionAlgEquivResidueField (K := K) : CanonicalReduction K ≃+* 𝓀[K]) =
      canonicalReductionRingEquivResidueField := by
  ext x
  simp [coe_canonicalReductionAlgEquivResidueField]

theorem canonicalReductionAlgEquivResidueField_mk (x : powerBoundedSubring K) :
    canonicalReductionAlgEquivResidueField (Ideal.Quotient.mk _ x) =
      residue 𝒪[K] (powerBoundedSubringEquivInteger x) :=
  (AlgEquiv.ofRingEquiv_apply _ _).trans (canonicalReductionRingEquivResidueField_mk x)

theorem canonicalReductionAlgEquivResidueField_symm_residue (c : 𝒪[K]) :
    canonicalReductionAlgEquivResidueField.symm (residue 𝒪[K] c) =
      Ideal.Quotient.mk _ (powerBoundedSubringEquivInteger.symm c) :=
  (AlgEquiv.ofRingEquiv_symm_apply _ _).trans
    (canonicalReductionRingEquivResidueField_symm_residue c)

end Algebra

end TauCeti.Huber
