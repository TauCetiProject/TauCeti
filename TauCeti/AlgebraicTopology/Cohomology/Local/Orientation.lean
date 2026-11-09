/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cohomology.Local.Basic
public import TauCeti.AlgebraicTopology.Singular.LocalHomology.Orientation.Linear

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

An orientation `ω` of a real normed space `F` of dimension `n + 1` selects a local orientation of
`F` at the origin (`Orientation.localOrientation`), and so an integral generator of
`Hⁿ⁺¹(F, F ∖ {0}; ℤ)` (`Orientation.localCohomologyClass`), indexed in the same degree. The
opposite orientation selects the opposite generator, and a continuous linear equivalence
`f : F ≃L[ℝ] G` pulls the generator selected by `ω.map f` back to the generator selected by `ω`
(`Orientation.singularCohomologyMap_localCohomologyClass`), so an orientation-preserving
automorphism fixes it. These are the normalized fibre values of the integral Thom class of an
oriented real vector bundle, read in local trivializations: on the overlap of two trivializations,
the fibre transition is such an automorphism. Accordingly, for an orientation of a topological
vector space `V` that need not be normed, pulling back along `f : V ≃L[ℝ] F` the generator selected
by the transported orientation does not depend on `f`
(`Orientation.singularCohomologyMap_localCohomologyClass_map_eq`).

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
  simp only [_root_.map_neg, ModuleCat.hom_neg, LinearMap.neg_apply, coe_neg, neg_neg]
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

namespace Orientation

open TauCeti

variable {F G : Type w} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G] {n : ℕ}

/-- The integral class dual to a local orientation of `F` at the origin, in a degree `d` equal to
`finrank ℝ F`. -/
private def dualClass [FiniteDimensional ℝ F] {d : ℕ} (hd : finrank ℝ F = d)
    (o : LocalOrientation F 0 d) :
    (TopPair.ofSubset ({0}ᶜ : Set (TopCat.of F))).singularCohomology
      (ModuleCat.of ℤ (ULift.{w} ℤ)) ℤ (ModuleCat.of ℤ (ULift.{w} ℤ)) d := by
  subst hd
  exact o.cohomologyClass (OpenPartialHomeomorph.refl F)
    (by rw [OpenPartialHomeomorph.refl_source]; exact Set.mem_univ _)

private theorem eq_dualClass_iff [FiniteDimensional ℝ F] {d : ℕ} (hd : finrank ℝ F = d)
    (o : LocalOrientation F 0 d)
    (α : (TopPair.ofSubset ({0}ᶜ : Set (TopCat.of F))).singularCohomology
      (ModuleCat.of ℤ (ULift.{w} ℤ)) ℤ (ModuleCat.of ℤ (ULift.{w} ℤ)) d) :
    α = dualClass hd o ↔
      ((TopPair.ofSubset ({0}ᶜ : Set (TopCat.of F))).singularKronecker ℤ d α).hom o.val = 1 := by
  subst hd
  exact LocalOrientation.eq_cohomologyClass_iff _ _ _ α

private theorem span_dualClass [FiniteDimensional ℝ F] {d : ℕ} (hd : finrank ℝ F = d)
    (o : LocalOrientation F 0 d) : Submodule.span ℤ {dualClass hd o} = ⊤ := by
  subst hd
  exact LocalOrientation.span_cohomologyClass _ _ _

/-- **The local cohomology generator selected by an orientation.** An orientation `ω` of a real
normed space `F` of dimension `n + 1` selects the integral class of `Hⁿ⁺¹(F, F ∖ {0}; ℤ)` whose
Kronecker pairing with the local orientation `ω.localOrientation hF` is one. It generates
`Hⁿ⁺¹(F, F ∖ {0}; ℤ)` (`Orientation.span_localCohomologyClass`). -/
def localCohomologyClass (ω : Orientation ℝ F (Fin (n + 1))) (hF : finrank ℝ F = n + 1) :
    (TopPair.ofSubset ({0}ᶜ : Set (TopCat.of F))).singularCohomology
      (ModuleCat.of ℤ (ULift.{w} ℤ)) ℤ (ModuleCat.of ℤ (ULift.{w} ℤ)) (n + 1) :=
  haveI := FiniteDimensional.of_finrank_eq_succ hF
  dualClass hF (ω.localOrientation hF)

/-- The generator selected by `ω` is the unique class whose pairing with the local orientation
selected by `ω` is one. -/
theorem eq_localCohomologyClass_iff (ω : Orientation ℝ F (Fin (n + 1)))
    (hF : finrank ℝ F = n + 1)
    (α : (TopPair.ofSubset ({0}ᶜ : Set (TopCat.of F))).singularCohomology
      (ModuleCat.of ℤ (ULift.{w} ℤ)) ℤ (ModuleCat.of ℤ (ULift.{w} ℤ)) (n + 1)) :
    α = ω.localCohomologyClass hF ↔
      ((TopPair.ofSubset ({0}ᶜ : Set (TopCat.of F))).singularKronecker ℤ (n + 1) α).hom
        (ω.localOrientation hF).val = 1 :=
  haveI := FiniteDimensional.of_finrank_eq_succ hF
  eq_dualClass_iff hF _ α

/-- The generator selected by `ω` evaluates to one on the local orientation selected by `ω`. -/
@[simp]
theorem kronecker_localCohomologyClass (ω : Orientation ℝ F (Fin (n + 1)))
    (hF : finrank ℝ F = n + 1) :
    ((TopPair.ofSubset ({0}ᶜ : Set (TopCat.of F))).singularKronecker ℤ (n + 1)
      (ω.localCohomologyClass hF)).hom (ω.localOrientation hF).val = 1 :=
  (ω.eq_localCohomologyClass_iff hF _).1 rfl

/-- The generator selected by an orientation generates integral local cohomology. -/
theorem span_localCohomologyClass (ω : Orientation ℝ F (Fin (n + 1)))
    (hF : finrank ℝ F = n + 1) :
    Submodule.span ℤ {ω.localCohomologyClass hF} = ⊤ :=
  haveI := FiniteDimensional.of_finrank_eq_succ hF
  span_dualClass hF _

/-- Reversing an orientation negates the local cohomology generator it selects. -/
@[simp]
theorem localCohomologyClass_neg (ω : Orientation ℝ F (Fin (n + 1)))
    (hF : finrank ℝ F = n + 1) :
    (-ω).localCohomologyClass hF = -ω.localCohomologyClass hF := by
  symm
  rw [eq_localCohomologyClass_iff, localOrientation_neg]
  simp only [map_neg, ModuleCat.hom_neg, LinearMap.neg_apply, LocalOrientation.coe_neg, neg_neg]
  exact ω.kronecker_localCohomologyClass hF

/-- **Naturality of the selected generators.** A continuous linear equivalence `f : F ≃L[ℝ] G`
pulls the local cohomology generator selected by the transported orientation `ω.map f` back to the
generator selected by `ω`. In particular an orientation-preserving automorphism of `F` fixes the
generator, and an orientation-reversing one negates it. -/
theorem singularCohomologyMap_localCohomologyClass (f : F ≃L[ℝ] G)
    (ω : Orientation ℝ F (Fin (n + 1))) (hF : finrank ℝ F = n + 1) (hG : finrank ℝ G = n + 1) :
    TopPair.singularCohomologyMap f.complZeroPairIso.hom (n + 1)
        ((ω.map _ f.toLinearEquiv).localCohomologyClass hG) =
      ω.localCohomologyClass hF := by
  rw [eq_localCohomologyClass_iff, TopPair.singularKronecker_naturality, ModuleCat.hom_comp,
    LinearMap.comp_apply, ← LocalOrientation.coe_map, ← localOrientation_map f ω hF hG]
  exact (ω.map _ f.toLinearEquiv).kronecker_localCohomologyClass hG

/-- **The selected generator read through a linear equivalence.** Let `ω` be an orientation of a
real topological vector space `V`, not necessarily normed. Pulling back, along a continuous linear
equivalence `f : V ≃L[ℝ] F` onto a normed space of dimension `n + 1`, the generator of
`Hⁿ⁺¹(F, F ∖ {0}; ℤ)` selected by the transported orientation `ω.map f` gives a class of
`Hⁿ⁺¹(V, V ∖ {0}; ℤ)` that does not depend on `f`. This is how an orientation of a fibre of a
vector bundle selects a generator through any trivialization. -/
theorem singularCohomologyMap_localCohomologyClass_map_eq {V : Type w} [TopologicalSpace V]
    [AddCommMonoid V] [Module ℝ V] (ω : Orientation ℝ V (Fin (n + 1))) (f f' : V ≃L[ℝ] F)
    (hF : finrank ℝ F = n + 1) :
    TopPair.singularCohomologyMap f.complZeroPairIso.hom (n + 1)
        ((ω.map _ f.toLinearEquiv).localCohomologyClass hF) =
      TopPair.singularCohomologyMap f'.complZeroPairIso.hom (n + 1)
        ((ω.map _ f'.toLinearEquiv).localCohomologyClass hF) := by
  -- `f'` is `f` followed by the automorphism `h = f⁻¹ ≫ f'` of `F`, which carries the generator
  -- selected by `ω.map f'` back to the one selected by `ω.map f`.
  obtain ⟨h, rfl⟩ : ∃ h : F ≃L[ℝ] F, f' = f.trans h := ⟨f.symm.trans f', by ext; simp⟩
  have hmap : ω.map _ (f.trans h).toLinearEquiv =
      (ω.map _ f.toLinearEquiv).map _ h.toLinearEquiv :=
    Orientation.map_trans f.toLinearEquiv h.toLinearEquiv ω
  rw [hmap, ContinuousLinearEquiv.complZeroPairIso_trans, Iso.trans_hom,
    TopPair.singularCohomologyMap_comp_apply,
    singularCohomologyMap_localCohomologyClass h _ hF hF]

end Orientation
