/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cohomology.Local.Basic
public import TauCeti.AlgebraicTopology.Singular.LocalHomology.Orientation.Basic

/-!
# Local cohomology dual to an orientation

A local homology orientation determines an integral local cohomology generator: the unique
class whose Kronecker pairing with that orientation is one. More generally, evaluation on the
orientation identifies top-degree local cohomology with any coefficient module. This
identification uses the relative universal coefficient theorem and imposes no injectivity or
freeness assumption on that module. It reuses
`TopPair.singularKronecker_bijective_of_projective_homology` and
`TauCeti.singularHomologyComplSingletonFinrankIso`.

`TauCeti.LocalOrientation.cohomologyClass` is characterized by its pairing, independently of the
chart used to construct it. Reversing the orientation negates the class. Pullback along a map of
local pairs carrying one orientation to another preserves their dual classes. These are the
normalized fibre classes used in constructing Thom classes of oriented vector bundles. The
statements include dimension zero and retain both orientation signs there.

## References

* A. Hatcher, *Algebraic Topology*, Sections 3.1 and 3.3 (universal coefficients and local
  orientations).
* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Section 10 (the fibre normalization
  of the Thom class).
-/

public noncomputable section

open CategoryTheory Module

universe w

namespace TauCeti.LocalOrientation

variable {M E : Type w} [TopologicalSpace M] [T1Space M]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {x : M} (o : LocalOrientation M x (finrank ℝ E))
  (φ : OpenPartialHomeomorph M E) (hx : x ∈ φ.source)

/-- Evaluation on a local orientation identifies top-degree local cohomology with any integral
coefficient module. -/
def cohomologyEquiv (N : ModuleCat.{w} ℤ) :
    (TopPair.ofSubset ({x}ᶜ : Set (TopCat.of M))).singularCohomology
      (ModuleCat.of ℤ (ULift.{w} ℤ)) ℤ N (finrank ℝ E) ≃ₗ[ℤ] N := by
  let H := localHomology (ModuleCat.of ℤ (ULift.{w} ℤ)) ({x} : Set M) (finrank ℝ E)
  let e₀ := singularHomologyComplSingletonFinrankIso
    (ModuleCat.of ℤ (ULift.{w} ℤ)) φ hx
  have hinj : Function.Injective (LinearMap.toSpanSingleton ℤ H o.val) := by
    apply (LinearMap.ker_eq_bot).mp
    apply LinearMap.ker_eq_bot'.mpr
    intro c hc
    exact (o.property.zsmul_eq_zero_iff e₀).mp
      ((int_smul_eq_zsmul _ c o.val).symm.trans hc)
  let e : ℤ ≃ₗ[ℤ] H := LinearEquiv.ofBijective
    (LinearMap.toSpanSingleton ℤ H o.val) ⟨hinj, fun y => by
      obtain ⟨c, hc⟩ := (isLocalOrientation_iff _ _ _).mp o.property y
      exact ⟨c, (int_smul_eq_zsmul _ c o.val).trans hc⟩⟩
  let P := TopPair.ofSubset ({x}ᶜ : Set (TopCat.of M))
  let L : P.singularCohomology (ModuleCat.of ℤ (ULift.{w} ℤ)) ℤ N (finrank ℝ E) →+ N :=
    { toFun α := (P.singularKronecker ℤ (finrank ℝ E) α).hom o.val
      map_zero' := by simp
      map_add' _ _ := by simp }
  haveI := projective_singularHomology_complSingleton (ModuleCat.of ℤ (ULift.{w} ℤ)) φ hx
  have hk := P.singularKronecker_bijective_of_projective_homology
    (ModuleCat.of ℤ (ULift.{w} ℤ)) N (finrank ℝ E)
  -- Recover integer linearity after constructing the additive equivalence, so the given
  -- module actions and canonical integer actions on hom groups can be compared explicitly.
  refine (AddEquiv.ofBijective L ⟨?_, ?_⟩).toIntLinearEquiv
  · intro α β hab
    apply hk.injective
    apply ModuleCat.hom_ext
    ext v
    obtain ⟨c, rfl⟩ := (isLocalOrientation_iff _ _ _).mp o.property v
    simpa only [L, AddMonoidHom.coe_mk, ZeroHom.coe_mk, map_zsmul]
      using congrArg (c • ·) hab
  · intro y
    let f : H →ₗ[ℤ] N := (LinearMap.toSpanSingleton ℤ N y).comp e.symm.toLinearMap
    obtain ⟨α, hα⟩ := hk.surjective (ModuleCat.ofHom f)
    refine ⟨α, ?_⟩
    have he : e.symm o.val = 1 := by
      apply e.injective
      rw [e.apply_symm_apply]
      exact (LinearMap.toSpanSingleton_apply_one ℤ H o.val).symm
    dsimp only [L, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
    rw [hα]
    exact (congrArg (fun g : H →ₗ[ℤ] N => g o.val) (ModuleCat.hom_ofHom f)).trans (by
      dsimp only [f]
      rw [LinearMap.comp_apply, LinearEquiv.coe_coe, he]
      exact LinearMap.toSpanSingleton_apply_one ℤ N y)

/-- The local cohomology identification is evaluation of the Kronecker map on the chosen
orientation. -/
@[simp]
theorem cohomologyEquiv_apply (N : ModuleCat.{w} ℤ)
    (α : (TopPair.ofSubset ({x}ᶜ : Set (TopCat.of M))).singularCohomology
      (ModuleCat.of ℤ (ULift.{w} ℤ)) ℤ N (finrank ℝ E)) :
    cohomologyEquiv o φ hx N α =
      ((TopPair.ofSubset ({x}ᶜ : Set (TopCat.of M))).singularKronecker ℤ
        (finrank ℝ E) α).hom o.val := by
  -- The equivalence is built from this evaluation map by `AddEquiv.ofBijective`.
  rfl

include φ hx in
/-- A local cohomology class is determined by its pairing with one local orientation. -/
theorem cohomology_ext (N : ModuleCat.{w} ℤ)
    {α β : (TopPair.ofSubset ({x}ᶜ : Set (TopCat.of M))).singularCohomology
      (ModuleCat.of ℤ (ULift.{w} ℤ)) ℤ N (finrank ℝ E)}
    (h : ((TopPair.ofSubset ({x}ᶜ : Set (TopCat.of M))).singularKronecker ℤ
        (finrank ℝ E) α).hom o.val =
      ((TopPair.ofSubset ({x}ᶜ : Set (TopCat.of M))).singularKronecker ℤ
        (finrank ℝ E) β).hom o.val) :
    α = β :=
  (cohomologyEquiv o φ hx N).injective (by
    rw [cohomologyEquiv_apply, cohomologyEquiv_apply]
    exact h)

/-- The integral local cohomology class dual to a local homology orientation. Its pairing with
that orientation is one. -/
def cohomologyClass :
    (TopPair.ofSubset ({x}ᶜ : Set (TopCat.of M))).singularCohomology
      (ModuleCat.of ℤ (ULift.{w} ℤ)) ℤ (ModuleCat.of ℤ (ULift.{w} ℤ)) (finrank ℝ E) :=
  (cohomologyEquiv o φ hx (ModuleCat.of ℤ (ULift.{w} ℤ))).symm 1

/-- The dual class evaluates to one on its local orientation. -/
@[simp]
theorem kronecker_cohomologyClass :
    ((TopPair.ofSubset ({x}ᶜ : Set (TopCat.of M))).singularKronecker ℤ (finrank ℝ E)
      (cohomologyClass o φ hx)).hom o.val = 1 := by
  rw [← cohomologyEquiv_apply]
  exact (cohomologyEquiv o φ hx _).apply_symm_apply 1

/-- The pairing normalization characterizes the dual local cohomology class uniquely. -/
theorem eq_cohomologyClass_iff
    (α : (TopPair.ofSubset ({x}ᶜ : Set (TopCat.of M))).singularCohomology
      (ModuleCat.of ℤ (ULift.{w} ℤ)) ℤ (ModuleCat.of ℤ (ULift.{w} ℤ)) (finrank ℝ E)) :
    α = cohomologyClass o φ hx ↔
      ((TopPair.ofSubset ({x}ᶜ : Set (TopCat.of M))).singularKronecker ℤ
        (finrank ℝ E) α).hom o.val = 1 := by
  constructor
  · rintro rfl
    exact kronecker_cohomologyClass o φ hx
  · intro h
    apply cohomology_ext o φ hx
    rw [h, kronecker_cohomologyClass]

/-- The dual class generates integral local cohomology. -/
theorem span_cohomologyClass :
    Submodule.span ℤ {cohomologyClass o φ hx} = ⊤ := by
  let e := cohomologyEquiv o φ hx (ModuleCat.of ℤ (ULift.{w} ℤ))
  apply Submodule.eq_top_iff'.mpr
  intro α
  refine Submodule.mem_span_singleton.mpr ⟨(e α).down, ?_⟩
  apply e.injective
  rw [e.map_smul]
  have hone : e (cohomologyClass o φ hx) = 1 := e.apply_symm_apply 1
  rw [hone]
  apply ULift.ext
  simp

/-- Reversing a local homology orientation negates its dual cohomology class. -/
@[simp]
theorem cohomologyClass_neg :
    cohomologyClass (-o) φ hx = -cohomologyClass o φ hx := by
  symm
  apply (eq_cohomologyClass_iff (-o) φ hx _).mpr
  simp only [map_neg, ModuleCat.hom_neg, LinearMap.neg_apply, coe_neg, neg_neg]
  exact kronecker_cohomologyClass o φ hx

/-- The dual cohomology class is independent of the chart used in its construction. -/
theorem cohomologyClass_eq (ψ : OpenPartialHomeomorph M E) (hx' : x ∈ ψ.source) :
    cohomologyClass o φ hx = cohomologyClass o ψ hx' := by
  apply cohomology_ext o φ hx
  rw [kronecker_cohomologyClass, kronecker_cohomologyClass]

/-- Pullback carries the cohomology class dual to a target orientation to the class dual to a
source orientation whenever the induced homology map carries the source orientation to the
specified target orientation. -/
theorem singularCohomologyMap_cohomologyClass
    {N : Type w} [TopologicalSpace N] [T1Space N] {y : N}
    (o' : LocalOrientation N y (finrank ℝ E))
    (ψ : OpenPartialHomeomorph N E) (hy : y ∈ ψ.source)
    (f : TopPair.ofSubset ({x}ᶜ : Set (TopCat.of M)) ⟶
      TopPair.ofSubset ({y}ᶜ : Set (TopCat.of N)))
    (hf : ((TopPair.ofSubset ({x}ᶜ : Set (TopCat.of M))).singularHomologyMap f
      (ModuleCat.of ℤ (ULift.{w} ℤ)) (finrank ℝ E)).hom o.val = o'.val) :
    TopPair.singularCohomologyMap f (finrank ℝ E) (cohomologyClass o' ψ hy) =
      cohomologyClass o φ hx := by
  apply (eq_cohomologyClass_iff o φ hx _).mpr
  rw [TopPair.singularKronecker_naturality]
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, hf]
  exact kronecker_cohomologyClass o' ψ hy

end TauCeti.LocalOrientation
