/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.AlmostComplex.Topology
public import TauCeti.Geometry.Symplectic.Cayley.Smooth
public import TauCeti.Geometry.Symplectic.ExistsCompatible
public import Mathlib.Topology.Homotopy.Contractible

/-!
# The tame and compatible complex structures form contractible spaces

Let `ω` be a symplectic form on a finite-dimensional real normed space `V`. The complex
structures of `V` carry the operator-norm topology of their endomorphisms
(`TauCeti/Geometry/Symplectic/AlmostComplex/Topology.lean`). For an
`ω`-compatible `J₀`, the Cayley transform at `J₀` identifies the `ω`-tame structures with a
convex ball containing `0`, the coordinate of `J₀`, and the `ω`-compatible structures with a
convex part of that ball (`TauCeti/Geometry/Symplectic/Cayley/Basic.lean`). Shrinking the
coordinate radially, `J ↦ (1 - t) • C(J)`, therefore deforms the space of `ω`-tame structures
onto `J₀` through `ω`-tame structures, preserves compatibility, and keeps `J₀` fixed throughout.
In operator-norm coordinates the deformation is the rational expression
`TauCeti.cayleyPathFormula`, which is continuous jointly in the time and the structure, so the
deformation is a homotopy relative to `J₀` from the identity to the constant map.

Since every symplectic vector space carries a compatible structure
(`TauCeti.SymplecticForm.exists_compatible`), both spaces are contractible. This is the
pointwise linear algebra behind the contractibility of the spaces of tame and compatible almost
complex structures on a symplectic manifold: choices of such structures can always be connected,
and families of them can be deformed to a given one.

## Main definitions

* `TauCeti.SymplecticForm.Compatible.cayleyContraction`: for compatible `J₀`, the deformation of
  the tame structures onto `J₀`, as a homotopy relative to `{J₀}`.
* `TauCeti.SymplecticForm.Compatible.compatibleCayleyContraction`: its restriction to the
  compatible structures.

## Main results

* `TauCeti.SymplecticForm.Compatible.cayley_cayleyContraction`: at time `t` the deformation
  multiplies the Cayley coordinate by `1 - t`.
* `TauCeti.SymplecticForm.Compatible.toContinuousLinearMap_cayleyContraction`: in operator-norm
  coordinates it is `J₀ (1 + (1 - t) C)(1 - (1 - t) C)⁻¹`.
* `TauCeti.SymplecticForm.Compatible.compatible_cayleyContraction`: it keeps compatible
  structures compatible.
* `TauCeti.SymplecticForm.instContractibleSpaceTames` and
  `TauCeti.SymplecticForm.instContractibleSpaceCompatible`: the spaces of `ω`-tame and of
  `ω`-compatible complex structures are contractible.

## References

* D. McDuff and D. Salamon, *Introduction to Symplectic Topology*, third edition, Section 2.5
  (contractibility of the spaces of tame and compatible linear complex structures).
-/

public noncomputable section

open Topology unitInterval

namespace TauCeti

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

namespace SymplecticForm

variable {ω : SymplecticForm V} {J₀ : AlmostComplexStructure V}

/-- The underlying map of `Compatible.cayleyContraction`: the tame structure whose Cayley
coordinate at `J₀` is `1 - t` times that of `J`. -/
private def Compatible.cayleyContractionFun (h₀ : ω.Compatible J₀) (t : I)
    (J : {J : AlmostComplexStructure V // ω.Tames J}) :
    {J : AlmostComplexStructure V // ω.Tames J} :=
  h₀.cayleyEquiv.symm ⟨(σ t : ℝ) • J₀.cayley J, h₀.smul_cayley_mem_cayleyBall J.2 (σ t).2⟩

private theorem Compatible.cayley_cayleyContractionFun (h₀ : ω.Compatible J₀) (t : I)
    (J : {J : AlmostComplexStructure V // ω.Tames J}) :
    J₀.cayley (h₀.cayleyContractionFun t J) = (σ t : ℝ) • J₀.cayley J := by
  have h := congrArg Subtype.val (h₀.cayleyEquiv.apply_symm_apply
    ⟨(σ t : ℝ) • J₀.cayley J, h₀.smul_cayley_mem_cayleyBall J.2 (σ t).2⟩)
  rw [Compatible.cayleyEquiv_apply_coe] at h
  rw [Compatible.cayleyContractionFun]
  exact h

/-- In operator-norm coordinates `Compatible.cayleyContractionFun` is continuous jointly in the
time and the structure. -/
private theorem Compatible.continuous_cayleyContractionFun (h₀ : ω.Compatible J₀) :
    Continuous fun p : I × {J : AlmostComplexStructure V // ω.Tames J} ↦
      h₀.cayleyContractionFun p.1 p.2 := by
  refine Continuous.subtype_mk ?_ _
  rw [AlmostComplexStructure.continuous_iff, continuous_iff_continuousAt]
  rintro ⟨t, J⟩
  set A := LinearMap.toContinuousLinearMap J₀.toLinearMap
  set B := LinearMap.toContinuousLinearMap J.1.toLinearMap
  have hA : A.toLinearMap = J₀.toLinearMap := LinearMap.coe_toContinuousLinearMap _
  have hB : B.toLinearMap = J.1.toLinearMap := LinearMap.coe_toContinuousLinearMap _
  have hcont := (contDiffAt_cayleyPathFormula (n := 0)
    (h₀.tames.isUnit_one_sub_mul_of_toLinearMap J.2 hA hB)
    (h₀.isUnit_one_sub_smul_cayleyFormula J.2 (σ t).2 hA hB)).continuousAt
  have hin : Continuous fun p : I × {J : AlmostComplexStructure V // ω.Tames J} ↦
      ((σ p.1 : ℝ), A, LinearMap.toContinuousLinearMap p.2.1.toLinearMap) :=
    (continuous_subtype_val.comp (continuous_symm.comp continuous_fst)).prodMk
      (continuous_const.prodMk
        (AlmostComplexStructure.isEmbedding_toContinuousLinearMap.continuous.comp
          (continuous_subtype_val.comp continuous_snd)))
  refine (hcont.comp (f := fun p : I × {J : AlmostComplexStructure V // ω.Tames J} ↦
      ((σ p.1 : ℝ), A, LinearMap.toContinuousLinearMap p.2.1.toLinearMap))
    hin.continuousAt).congr (Filter.Eventually.of_forall fun p ↦ ?_)
  exact (h₀.toContinuousLinearMap_cayleyEquiv_symm_smul_cayley p.2.2 (σ p.1).2 hA
    (LinearMap.coe_toContinuousLinearMap _)).symm

/-- For an `ω`-compatible `J₀`, the deformation of the `ω`-tame complex structures onto `J₀`:
at time `t` it sends `J` to the tame structure whose Cayley coordinate at `J₀` is `1 - t` times
that of `J`. It is a homotopy from the identity to the constant map at `J₀` which fixes `J₀`. -/
def Compatible.cayleyContraction (h₀ : ω.Compatible J₀) :
    ContinuousMap.HomotopyRel (ContinuousMap.id {J : AlmostComplexStructure V // ω.Tames J})
      (ContinuousMap.const _ ⟨J₀, h₀.tames⟩) {⟨J₀, h₀.tames⟩} where
  toFun p := h₀.cayleyContractionFun p.1 p.2
  continuous_toFun := h₀.continuous_cayleyContractionFun
  map_zero_left J := Subtype.ext <| h₀.eq_of_cayley_eq (h₀.cayleyContractionFun 0 J).2 J.2 <| by
    simp [h₀.cayley_cayleyContractionFun]
  map_one_left J := Subtype.ext <| h₀.eq_of_cayley_eq (h₀.cayleyContractionFun 1 J).2 h₀.tames <|
    by simp [h₀.cayley_cayleyContractionFun]
  prop' t J hJ := by
    rw [Set.mem_singleton_iff] at hJ
    subst hJ
    exact Subtype.ext <| h₀.eq_of_cayley_eq (h₀.cayleyContractionFun t _).2 h₀.tames <| by
      simp [h₀.cayley_cayleyContractionFun]

/-- At time `t` the deformation `Compatible.cayleyContraction` multiplies the Cayley coordinate
at `J₀` by `1 - t`. -/
@[simp]
theorem Compatible.cayley_cayleyContraction (h₀ : ω.Compatible J₀) (t : I)
    (J : {J : AlmostComplexStructure V // ω.Tames J}) :
    J₀.cayley (h₀.cayleyContraction (t, J)) = (σ t : ℝ) • J₀.cayley J :=
  h₀.cayley_cayleyContractionFun t J

/-- In operator-norm coordinates, the deformation `Compatible.cayleyContraction` at time `t` is
`J₀ (1 + (1 - t) C)(1 - (1 - t) C)⁻¹`, where `C` is the Cayley coordinate of `J` at `J₀`. -/
theorem Compatible.toContinuousLinearMap_cayleyContraction (h₀ : ω.Compatible J₀) (t : I)
    (J : {J : AlmostComplexStructure V // ω.Tames J}) {A B : V →L[ℝ] V}
    (hA : A.toLinearMap = J₀.toLinearMap) (hB : B.toLinearMap = J.1.toLinearMap) :
    LinearMap.toContinuousLinearMap (h₀.cayleyContraction (t, J)).1.toLinearMap =
      cayleyPathFormula (σ t) A B :=
  h₀.toContinuousLinearMap_cayleyEquiv_symm_smul_cayley J.2 (σ t).2 hA hB

/-- The deformation `Compatible.cayleyContraction` keeps `ω`-compatible structures compatible. -/
theorem Compatible.compatible_cayleyContraction (h₀ : ω.Compatible J₀) (t : I)
    {J : {J : AlmostComplexStructure V // ω.Tames J}} (hJ : ω.Compatible J) :
    ω.Compatible (h₀.cayleyContraction (t, J)) := by
  rw [← h₀.cayley_mem_compatibleCayleyBall_iff (h₀.cayleyContraction (t, J)).2,
    h₀.cayley_cayleyContraction]
  exact h₀.smul_cayley_mem_compatibleCayleyBall hJ (σ t).2

/-- For an `ω`-compatible `J₀`, the deformation of the `ω`-compatible complex structures onto
`J₀` obtained by restricting `Compatible.cayleyContraction`. It is a homotopy from the identity to
the constant map at `J₀` which fixes `J₀`. -/
def Compatible.compatibleCayleyContraction (h₀ : ω.Compatible J₀) :
    ContinuousMap.HomotopyRel
      (ContinuousMap.id {J : AlmostComplexStructure V // ω.Compatible J})
      (ContinuousMap.const _ ⟨J₀, h₀⟩) {⟨J₀, h₀⟩} where
  toFun p := ⟨h₀.cayleyContraction (p.1, ⟨p.2, p.2.2.tames⟩),
    h₀.compatible_cayleyContraction p.1 p.2.2⟩
  continuous_toFun := by
    refine Continuous.subtype_mk (continuous_subtype_val.comp
      (h₀.cayleyContraction.continuous.comp (continuous_fst.prodMk ?_))) _
    exact (continuous_subtype_val.comp continuous_snd).subtype_mk _
  map_zero_left J := Subtype.ext (by simp)
  map_one_left J := Subtype.ext (by simp)
  prop' t J hJ := by
    rw [Set.mem_singleton_iff] at hJ
    subst hJ
    exact Subtype.ext <| by
      simpa using congrArg Subtype.val (h₀.cayleyContraction.eq_fst t rfl)

/-- The deformation `Compatible.compatibleCayleyContraction` is `Compatible.cayleyContraction`
on the compatible structures. -/
@[simp]
theorem Compatible.coe_compatibleCayleyContraction (h₀ : ω.Compatible J₀) (t : I)
    (J : {J : AlmostComplexStructure V // ω.Compatible J}) :
    (h₀.compatibleCayleyContraction (t, J) : AlmostComplexStructure V) =
      h₀.cayleyContraction (t, ⟨J, J.2.tames⟩) :=
  (rfl)

/-- The `ω`-tame complex structures on a finite-dimensional symplectic vector space form a
contractible space. -/
instance instContractibleSpaceTames :
    ContractibleSpace {J : AlmostComplexStructure V // ω.Tames J} :=
  let ⟨J₀, h₀⟩ := ω.exists_compatible
  (contractible_iff_id_nullhomotopic _).2 ⟨⟨J₀, h₀.tames⟩, ⟨h₀.cayleyContraction.toHomotopy⟩⟩

/-- The `ω`-compatible complex structures on a finite-dimensional symplectic vector space form
a contractible space. -/
instance instContractibleSpaceCompatible :
    ContractibleSpace {J : AlmostComplexStructure V // ω.Compatible J} :=
  let ⟨J₀, h₀⟩ := ω.exists_compatible
  (contractible_iff_id_nullhomotopic _).2
    ⟨⟨J₀, h₀⟩, ⟨h₀.compatibleCayleyContraction.toHomotopy⟩⟩

end SymplecticForm

end TauCeti
