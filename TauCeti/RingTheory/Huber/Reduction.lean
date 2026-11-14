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
* `TauCeti.Huber.powerBoundedSubringEquivInteger` and
  `TauCeti.Huber.canonicalReductionRingEquivResidueField`: `K° ≃+* 𝒪[K]` and
  `CanonicalReduction K ≃+* 𝓀[K]` for an ultrametric normed field `K`.
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
      Ideal.Quotient.mk _ (powerBoundedSubringEquiv e he he' a) := (rfl)

@[simp]
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

/-- In an ultrametric normed field, an element of `K°` is a unit of `K°` exactly when its norm in
`K` is one. -/
theorem powerBoundedSubring.isUnit_iff_norm_eq_one {x : powerBoundedSubring K} :
    IsUnit x ↔ ‖(x : K)‖ = 1 := by
  refine ⟨fun ⟨u, hu⟩ ↦ ?_, fun hx ↦ ?_⟩
  · have hle1 : ‖(u : K)‖ ≤ 1 :=
      isPowerBounded_iff_norm_le_one.mp (mem_powerBoundedSubring.mp (u : powerBoundedSubring K).2)
    have hle2 : ‖((↑u⁻¹ : powerBoundedSubring K) : K)‖ ≤ 1 :=
      isPowerBounded_iff_norm_le_one.mp
        (mem_powerBoundedSubring.mp (↑u⁻¹ : powerBoundedSubring K).2)
    have hmul : ‖(u : K)‖ * ‖((↑u⁻¹ : powerBoundedSubring K) : K)‖ = 1 := by
      rw [← norm_mul, ← Subring.coe_mul, Units.mul_inv, OneMemClass.coe_one, norm_one]
    have hge1 : 1 ≤ ‖(u : K)‖ := by
      rw [← hmul]
      exact mul_le_of_le_one_right (norm_nonneg _) hle2
    exact hu ▸ hle1.antisymm hge1
  · have hx0 : (x : K) ≠ 0 := by
      intro h0
      simp [h0] at hx
    have hinv : (x : K)⁻¹ ∈ powerBoundedSubring K :=
      mem_powerBoundedSubring.mpr <| isPowerBounded_iff_norm_le_one.mpr <| by
        rw [norm_inv, hx, inv_one]
    exact ⟨⟨x, ⟨(x : K)⁻¹, hinv⟩, Subtype.ext (mul_inv_cancel₀ hx0),
      Subtype.ext (inv_mul_cancel₀ hx0)⟩, rfl⟩

/-- The power-bounded subring `K°` of an ultrametric normed field is a local ring. -/
instance isLocalRing_powerBoundedSubring : IsLocalRing (powerBoundedSubring K) := by
  refine .of_nonunits_add fun a b ha hb ↦ ?_
  rw [mem_nonunits_iff, powerBoundedSubring.isUnit_iff_norm_eq_one] at ha hb ⊢
  have ha1 : ‖(a : K)‖ < 1 :=
    (isPowerBounded_iff_norm_le_one.mp (mem_powerBoundedSubring.mp a.2)).lt_of_ne ha
  have hb1 : ‖(b : K)‖ < 1 :=
    (isPowerBounded_iff_norm_le_one.mp (mem_powerBoundedSubring.mp b.2)).lt_of_ne hb
  exact ((IsUltrametricDist.norm_add_le_max (a : K) (b : K)).trans_lt (max_lt ha1 hb1)).ne

/-- The maximal ideal of `K°` is the ideal `K°°` of topologically nilpotent elements. -/
theorem maximalIdeal_powerBoundedSubring :
    maximalIdeal (powerBoundedSubring K) = topologicallyNilpotentIdeal K := by
  ext x
  rw [mem_maximalIdeal, mem_nonunits_iff, powerBoundedSubring.isUnit_iff_norm_eq_one,
    mem_topologicallyNilpotentIdeal, IsTopologicallyNilpotent,
    tendsto_pow_atTop_nhds_zero_iff_norm_lt_one,
    (isPowerBounded_iff_norm_le_one.mp (mem_powerBoundedSubring.mp x.2)).lt_iff_ne]

/-- For an ultrametric normed field `K`, `K°°` is a maximal ideal of `K°`, so `CanonicalReduction K`
is a field. -/
instance isMaximal_topologicallyNilpotentIdeal : (topologicallyNilpotentIdeal K).IsMaximal :=
  maximalIdeal_powerBoundedSubring (K := K) ▸ maximalIdeal.isMaximal (powerBoundedSubring K)

/-- The canonical ring isomorphism `K° ≃+* 𝒪[K]` between the power-bounded subring and the
valuation ring of an ultrametric normed field. -/
noncomputable def powerBoundedSubringEquivInteger : powerBoundedSubring K ≃+* 𝒪[K] where
  toFun x := ⟨x.1, by
    change NormedField.valuation x.1 ≤ 1
    exact NNReal.coe_le_coe.mp (isPowerBounded_iff_norm_le_one.mp (mem_powerBoundedSubring.mp x.2))⟩
  invFun x := ⟨x.1, mem_powerBoundedSubring.mpr <| isPowerBounded_iff_norm_le_one.mpr <| by
    exact NNReal.coe_le_coe.mpr (show NormedField.valuation x.1 ≤ 1 from x.2)⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl

/-- **The canonical reduction of an ultrametric normed field `K` is its valuation residue field
`𝓀[K]`.** -/
noncomputable def canonicalReductionRingEquivResidueField : CanonicalReduction K ≃+* 𝓀[K] := by
  refine Ideal.quotientEquiv (topologicallyNilpotentIdeal K) (maximalIdeal 𝒪[K])
    powerBoundedSubringEquivInteger ?_
  refine le_antisymm ?_ (Ideal.map_le_iff_le_comap.mpr fun x hx ↦ ?_)
  · intro y hy
    rw [mem_maximalIdeal, mem_nonunits_iff] at hy
    have hx : powerBoundedSubringEquivInteger.symm y ∈ topologicallyNilpotentIdeal K := by
      rw [← maximalIdeal_powerBoundedSubring, mem_maximalIdeal, mem_nonunits_iff]
      exact fun hu ↦ hy (by simpa using hu.map powerBoundedSubringEquivInteger.toRingHom)
    simpa using Ideal.mem_map_of_mem powerBoundedSubringEquivInteger.toRingHom hx
  · rw [Ideal.mem_comap, mem_maximalIdeal, mem_nonunits_iff]
    rw [← maximalIdeal_powerBoundedSubring, mem_maximalIdeal, mem_nonunits_iff] at hx
    exact fun hu ↦ hx (by simpa using hu.map powerBoundedSubringEquivInteger.symm.toRingHom)

@[simp]
theorem canonicalReductionRingEquivResidueField_mk (x : powerBoundedSubring K) :
    canonicalReductionRingEquivResidueField (Ideal.Quotient.mk _ x) =
      residue 𝒪[K] (powerBoundedSubringEquivInteger x) := (rfl)

@[simp]
theorem canonicalReductionRingEquivResidueField_symm_residue (c : 𝒪[K]) :
    canonicalReductionRingEquivResidueField.symm (residue 𝒪[K] c) =
      Ideal.Quotient.mk _ (powerBoundedSubringEquivInteger.symm c) :=
  canonicalReductionRingEquivResidueField.symm_apply_eq.mpr rfl

end NormedField

section Algebra

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]

section TopologicalAlgebra

variable {A : Type*} [CommRing A] [TopologicalSpace A] [NonarchimedeanAddGroup A]
  [Algebra K A] [ContinuousSMul K A]

variable (K A) in
/-- Scalars in the valuation ring `𝒪[K]` map into the power-bounded subring `A°` of any
nonarchimedean topological `K`-algebra with continuous scalar multiplication. -/
noncomputable def integerToPowerBounded : 𝒪[K] →+* powerBoundedSubring A :=
  (algebraMap K A).comp (Subring.subtype 𝒪[K]) |>.codRestrict (powerBoundedSubring A) fun c ↦
    mem_powerBoundedSubring.mpr
      (isPowerBounded_algebraMap_of_norm_le_one (Valued.integer.norm_le_one c))

@[simp]
theorem coe_integerToPowerBounded (c : 𝒪[K]) :
    (integerToPowerBounded K A c : A) = algebraMap K A c := (rfl)

variable [ContinuousMul A]

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
        have hc1 : ‖(c : K)‖ < 1 := Valued.integer.mem_maximalIdeal_iff.mp hc
        have hcont : Continuous (algebraMap K A) := by
          rw [show ⇑(algebraMap K A) = fun x : K ↦ x • (1 : A) from
            funext Algebra.algebraMap_eq_smul_one]
          exact continuous_id.smul continuous_const
        have h0 : Tendsto (algebraMap K A) (𝓝 0) (𝓝 0) := by
          simpa only [map_zero] using hcont.tendsto 0
        simpa only [IsTopologicallyNilpotent, Function.comp_def, map_pow] using
          h0.comp (tendsto_pow_atTop_nhds_zero_of_norm_lt_one hc1)

@[simp]
theorem algebraMap_canonicalReduction_residue (c : 𝒪[K]) :
    algebraMap 𝓀[K] (CanonicalReduction A) (residue 𝒪[K] c) =
      Ideal.Quotient.mk _ (integerToPowerBounded K A c) := (rfl)

end TopologicalAlgebra

/-- For a nontrivially normed ultrametric field `K`, `CanonicalReduction K ≃ₐ[𝓀[K]] 𝓀[K]` as
`𝓀[K]`-algebras. -/
noncomputable def canonicalReductionAlgEquivResidueField : CanonicalReduction K ≃ₐ[𝓀[K]] 𝓀[K] := by
  refine AlgEquiv.ofRingEquiv (f := canonicalReductionRingEquivResidueField (K := K)) fun x ↦ ?_
  obtain ⟨c, rfl⟩ := residue_surjective (R := 𝒪[K]) x
  rw [algebraMap_canonicalReduction_residue, canonicalReductionRingEquivResidueField_mk,
    Algebra.algebraMap_self, RingHom.id_apply]
  exact congrArg (residue 𝒪[K]) (Subtype.ext rfl)

@[simp]
theorem canonicalReductionAlgEquivResidueField_mk (x : powerBoundedSubring K) :
    canonicalReductionAlgEquivResidueField (Ideal.Quotient.mk _ x) =
      residue 𝒪[K] (powerBoundedSubringEquivInteger x) := (rfl)

end Algebra

end TauCeti.Huber
