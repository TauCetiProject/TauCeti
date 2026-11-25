/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.Topology.FiberBundle.Pullback

public import TauCeti.LinearAlgebra.ExteriorPower.Conjugate
public import TauCeti.Topology.VectorBundle.Conjugate
public import TauCeti.Topology.VectorBundle.Determinant

/-!
# The determinant of a conjugate bundle

The canonical exterior comparison identifies the actual native determinant line of the conjugate
bundle with the conjugate of the actual native determinant line. The pure comparison is linear on
each fibre without fibre norms or finite-dimensionality assumptions. For vector bundles with a
finite-dimensional model, it induces a homeomorphism on total spaces over any topological base,
including an empty base. Rank zero is included.

## Main constructions

* `conjugateLinearEquiv` and `conjugateEquiv` are the native fibre comparisons, with the exterior
  generator formula `conjugateLinearEquiv_ιMulti`.
* `conjugateModelEquiv` records the change between independently chosen model bases. Its nonzero
  coefficient `conjugateModelCoefficient` is retained in `chartCoord_conjugateLinearEquiv`.
* `conjugateHomeomorph` is continuous on the whole native total space, with forward, inverse and
  projection formulas.
* `conjugateLinearEquiv_naturality` is the square for every linear fibre map between equal-rank
  model presentations in independent universes, with their degree casts explicit. The corollary
  `conjugateLinearEquiv_bundleIso_naturality` states it for fibrewise isomorphisms through the
  determinant transport `congrModelEquiv`.
* The fibre comparisons commute with determinant pullback (`conjugateLinearEquiv_pullback`,
  `conjugateEquiv_pullback`). The source side uses the canonical `pullbackHomeomorph` directly;
  `conjugateTargetPullbackHomeomorph` conjugates that comparison on the target side.
  The full square is `conjugateHomeomorph_pullback`.
* `doubleConjugateLinearEquiv` is defined directly by the exterior functor on the canonical
  double-conjugation cancellation. Its native total-space form `doubleConjugateHomeomorph` agrees
  with applying the conjugation comparison twice (`conjugateHomeomorph_double`).

Model bases may be chosen independently. The pure all-degree comparison is owned by
`TauCeti.LinearAlgebra.ExteriorPower.Conjugate`.

-/

public section

noncomputable section

open Bundle Module TauCeti.Conjugate

namespace TauCeti.DetBundle

universe uB uF uE

variable {B : Type uB} {F : Type uF} [NormedAddCommGroup F] [NormedSpace ℂ F]
  {E : B → Type uE} [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]

/-- The determinant of the conjugate fibre is the conjugate of the determinant fibre.
This is the actual exterior-power comparison, independently of all bundle charts. -/
def conjugateLinearEquiv (x : B) :
    DetBundle ℂ (Conjugate F) (ConjugateBundle E) x ≃ₗ[ℂ]
      Conjugate (DetBundle ℂ F E x) :=
  (linearEquiv ℂ (Conjugate F) (ConjugateBundle E) x) ≪≫ₗ
    LinearEquiv.ofEq _ _ (congrArg (fun n => ⋀[ℂ]^n (Conjugate (E x)))
      (finrank_complex (V := F))) ≪≫ₗ
    exteriorPower.conjugateEquiv (finrank ℂ F) ≪≫ₗ
    (linearEquiv ℂ F E x).symm.conjugate

theorem conjugateLinearEquiv_apply (x : B)
    (v : DetBundle ℂ (Conjugate F) (ConjugateBundle E) x) :
    conjugateLinearEquiv (F := F) (E := E) x v =
      toConj ((linearEquiv ℂ F E x).symm (ofConj
        (exteriorPower.conjugateEquiv (finrank ℂ F)
          (LinearEquiv.ofEq _ _ (congrArg (fun n => ⋀[ℂ]^n (Conjugate (E x)))
            (finrank_complex (V := F)))
              (linearEquiv ℂ (Conjugate F) (ConjugateBundle E) x v))))) := by
  simp only [conjugateLinearEquiv, LinearEquiv.trans_apply, LinearEquiv.conjugate_apply]

/-- The generator formula includes the dimension cast rather than identifying the two
model bases or their coordinate determinants. -/
theorem conjugateLinearEquiv_ιMulti (x : B)
    (a : Fin (finrank ℂ (Conjugate F)) → Conjugate (E x)) :
    conjugateLinearEquiv (F := F) (E := E) x
      ((linearEquiv ℂ (Conjugate F) (ConjugateBundle E) x).symm
        (exteriorPower.ιMulti ℂ _ a)) =
      toConj ((linearEquiv ℂ F E x).symm
        (exteriorPower.ιMulti ℂ _
          (fun i => ofConj (a (Fin.cast (finrank_complex (V := F)).symm i))))) := by
  simp only [conjugateLinearEquiv, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply,
    LinearEquiv.conjugate_apply]
  rw [exteriorPower.ofEq_ιMulti (R := ℂ) (M := Conjugate (E x))
    (finrank_complex (V := F)) a, exteriorPower.conjugateEquiv_ιMulti, ofConj_toConj]
  simp only [Function.comp_def]

/-- The inverse native comparison sends a conjugated exterior generator to the conjugate
vectors, with the inverse degree identification explicit. -/
theorem conjugateLinearEquiv_symm_ιMulti (x : B) (a : Fin (finrank ℂ F) → E x) :
    (conjugateLinearEquiv (F := F) (E := E) x).symm
      (toConj ((linearEquiv ℂ F E x).symm (exteriorPower.ιMulti ℂ _ a))) =
      (linearEquiv ℂ (Conjugate F) (ConjugateBundle E) x).symm
        (exteriorPower.ιMulti ℂ _
          (fun i => toConj (a (Fin.cast (finrank_complex (V := F)) i)))) := by
  simp only [conjugateLinearEquiv, LinearEquiv.symm_trans_apply,
    LinearEquiv.conjugate_symm, LinearEquiv.symm_symm, LinearEquiv.conjugate_apply,
    ofConj_toConj, LinearEquiv.apply_symm_apply,
    exteriorPower.conjugateEquiv_symm_ιMulti]
  rw [LinearEquiv.ofEq_symm, exteriorPower.ofEq_ιMulti
    (finrank_complex (V := F)).symm]
  simp only [Function.comp_def]

/-- The native fibre comparison is a continuous linear equivalence for the actual module
topologies on the determinant fibres and the inherited conjugate topology. -/
def conjugateEquiv (x : B) :
    DetBundle ℂ (Conjugate F) (ConjugateBundle E) x ≃L[ℂ]
      Conjugate (DetBundle ℂ F E x) := by
  letI : IsModuleTopology ℂ (Conjugate (DetBundle ℂ F E x)) :=
    IsModuleTopology.isoₛₗ Complex.continuous_conj Complex.continuous_conj
      (toConjL : DetBundle ℂ F E x ≃L⋆[ℂ] Conjugate (DetBundle ℂ F E x))
  exact (conjugateLinearEquiv (F := F) (E := E) x).toContinuousLinearEquivOfIsModuleTopology

@[simp] theorem conjugateEquiv_apply (x : B)
    (v : DetBundle ℂ (Conjugate F) (ConjugateBundle E) x) :
    conjugateEquiv (F := F) (E := E) x v = conjugateLinearEquiv (F := F) (E := E) x v := by
  simp only [conjugateEquiv, LinearEquiv.coe_toContinuousLinearEquivOfIsModuleTopology]

/-- The inverse continuous fibre comparison is the inverse algebraic comparison. -/
@[simp] theorem conjugateEquiv_symm_apply (x : B)
    (w : Conjugate (DetBundle ℂ F E x)) :
    (conjugateEquiv (F := F) (E := E) x).symm w =
      (conjugateLinearEquiv (F := F) (E := E) x).symm w := by
  simp only [conjugateEquiv, LinearEquiv.symm_toContinuousLinearEquivOfIsModuleTopology,
    LinearEquiv.coe_toContinuousLinearEquivOfIsModuleTopology]

/-- Naturality on actual native determinant fibres, for arbitrary linear maps and model
presentations in independent universes. The two model ranks agree, but their bases need not. -/
theorem conjugateLinearEquiv_naturality {G : Type*} [NormedAddCommGroup G] [NormedSpace ℂ G]
    {E' : B → Type*} [∀ x, AddCommGroup (E' x)] [∀ x, Module ℂ (E' x)]
    (h : finrank ℂ F = finrank ℂ G) (x : B) (f : E x →ₗ[ℂ] E' x)
    (v : DetBundle ℂ (Conjugate F) (ConjugateBundle E) x) :
    let hc := (finrank_complex (V := F)).trans (h.trans (finrank_complex (V := G)).symm)
    conjugateLinearEquiv (F := G) (E := E') x
      ((linearEquiv ℂ (Conjugate G) (ConjugateBundle E') x).symm
        (LinearEquiv.ofEq _ _ (congrArg (fun n => ⋀[ℂ]^n (Conjugate (E' x))) hc)
          (exteriorPower.map (finrank ℂ (Conjugate F)) f.conjugate
            (linearEquiv ℂ (Conjugate F) (ConjugateBundle E) x v)))) =
    toConj ((linearEquiv ℂ G E' x).symm
      (LinearEquiv.ofEq _ _ (congrArg (fun n => ⋀[ℂ]^n (E' x)) h)
        (exteriorPower.map (finrank ℂ F) f
          (linearEquiv ℂ F E x
            (ofConj (conjugateLinearEquiv (F := F) (E := E) x v)))))) := by
  dsimp only
  have hc := (finrank_complex (V := F)).trans (h.trans (finrank_complex (V := G)).symm)
  have hn := exteriorPower.conjugateEquiv_ofEq_naturality
    (finrank_complex (V := F)) (finrank_complex (V := G)) h hc f
    (linearEquiv ℂ (Conjugate F) (ConjugateBundle E) x v)
  have hn' := congrArg (fun a => toConj ((linearEquiv ℂ G E' x).symm (ofConj a))) hn
  simpa only [conjugateLinearEquiv_apply, LinearEquiv.apply_symm_apply,
    LinearEquiv.symm_apply_apply, ofConj_toConj] using hn'

/-- Naturality for fibrewise isomorphisms between independently presented finite-dimensional
models, through the determinant transport `congrModelEquiv`. No inhabited or nonempty base is
assumed; the models and fibres may lie in independent universes. -/
theorem conjugateLinearEquiv_bundleIso_naturality {G : Type*}
    [NormedAddCommGroup G] [NormedSpace ℂ G] [FiniteDimensional ℂ F] [FiniteDimensional ℂ G]
    {E' : B → Type*} [∀ x, AddCommGroup (E' x)] [∀ x, Module ℂ (E' x)]
    [TopologicalSpace B] [∀ x, TopologicalSpace (E x)]
    [TopologicalSpace (TotalSpace F E)] [FiberBundle F E] [VectorBundle ℂ F E]
    [∀ x, TopologicalSpace (E' x)] [TopologicalSpace (TotalSpace G E')]
    [FiberBundle G E'] [VectorBundle ℂ G E']
    (e : ∀ x, E x ≃L[ℂ] E' x) (x : B)
    (v : DetBundle ℂ (Conjugate F) (ConjugateBundle E) x) :
    conjugateLinearEquiv (F := G) (E := E') x
      (congrModelEquiv (F₁ := Conjugate F) (F' := Conjugate G)
        (fun x => (e x).conjugate) x v) =
      toConj (congrModelEquiv (F₁ := F) (F' := G) e x
        (ofConj (conjugateLinearEquiv (F := F) (E := E) x v))) := by
  have h : finrank ℂ F = finrank ℂ G :=
    ((VectorBundle.continuousLinearEquivAt ℂ F E x).symm.trans
      ((e x).trans (VectorBundle.continuousLinearEquivAt ℂ G E' x))).toLinearEquiv.finrank_eq
  have hc := (finrank_complex (V := F)).trans (h.trans (finrank_complex (V := G)).symm)
  -- `congrModelEquiv` is the exterior power of the fibre map, read through the rank equality.
  have hT : congrModelEquiv (F₁ := F) (F' := G) e x
      (ofConj (conjugateLinearEquiv (F := F) (E := E) x v)) =
      (linearEquiv ℂ G E' x).symm (LinearEquiv.ofEq _ _ (congrArg (fun n => ⋀[ℂ]^n (E' x)) h)
        (exteriorPower.map (finrank ℂ F) (e x).toLinearEquiv.toLinearMap
          (linearEquiv ℂ F E x (ofConj (conjugateLinearEquiv (F := F) (E := E) x v))))) := by
    apply (linearEquiv ℂ G E' x).injective
    apply Subtype.ext
    rw [coe_congrModelEquiv, LinearEquiv.apply_symm_apply, LinearEquiv.coe_ofEq_apply,
      exteriorPower.coe_map]
  have hS : congrModelEquiv (F₁ := Conjugate F) (F' := Conjugate G)
      (fun x => (e x).conjugate) x v =
      (linearEquiv ℂ (Conjugate G) (ConjugateBundle E') x).symm
        (LinearEquiv.ofEq _ _ (congrArg (fun n => ⋀[ℂ]^n (Conjugate (E' x))) hc)
          (exteriorPower.map (finrank ℂ (Conjugate F)) (e x).toLinearEquiv.toLinearMap.conjugate
            (linearEquiv ℂ (Conjugate F) (ConjugateBundle E) x v))) := by
    apply (linearEquiv ℂ (Conjugate G) (ConjugateBundle E') x).injective
    apply Subtype.ext
    rw [coe_congrModelEquiv, LinearEquiv.apply_symm_apply, LinearEquiv.coe_ofEq_apply,
      exteriorPower.coe_map]
    congr 2
    exact LinearMap.ext fun w => by simp
  rw [hS, hT]
  exact conjugateLinearEquiv_naturality h x (e x).toLinearEquiv.toLinearMap v

/-- The native determinant transport induced by cancelling two conjugations on the original
fibre. It is defined directly by the exterior functor, independently of `conjugateLinearEquiv`. -/
def doubleConjugateLinearEquiv (x : B) :
    DetBundle ℂ (Conjugate (Conjugate F)) (ConjugateBundle (ConjugateBundle E)) x ≃ₗ[ℂ]
      DetBundle ℂ F E x :=
  linearEquiv ℂ (Conjugate (Conjugate F)) (ConjugateBundle (ConjugateBundle E)) x ≪≫ₗ
    (TauCeti.Conjugate.doubleConjugateLinearEquiv :
      Conjugate (Conjugate (E x)) ≃ₗ[ℂ] E x).exteriorPower (finrank ℂ (Conjugate (Conjugate F))) ≪≫ₗ
    LinearEquiv.ofEq _ _ (congrArg (fun n => ⋀[ℂ]^n (E x))
      ((finrank_complex (V := Conjugate F)).trans (finrank_complex (V := F)))) ≪≫ₗ
    (linearEquiv ℂ F E x).symm

theorem doubleConjugateLinearEquiv_apply (x : B)
    (v : DetBundle ℂ (Conjugate (Conjugate F)) (ConjugateBundle (ConjugateBundle E)) x) :
    doubleConjugateLinearEquiv (F := F) (E := E) x v =
      (linearEquiv ℂ F E x).symm
        (LinearEquiv.ofEq _ _ (congrArg (fun n => ⋀[ℂ]^n (E x))
          ((finrank_complex (V := Conjugate F)).trans (finrank_complex (V := F))))
          (exteriorPower.map (finrank ℂ (Conjugate (Conjugate F)))
            (TauCeti.Conjugate.doubleConjugateLinearEquiv :
              Conjugate (Conjugate (E x)) ≃ₗ[ℂ] E x).toLinearMap
            (linearEquiv ℂ (Conjugate (Conjugate F))
              (ConjugateBundle (ConjugateBundle E)) x v))) := by
  simp only [doubleConjugateLinearEquiv, LinearEquiv.trans_apply,
    ← LinearEquiv.coe_toLinearMap, LinearEquiv.exteriorPower_toLinearMap]

/-- The inverse double-conjugation transport uses the inverse fibre cancellation and reverses
the identification of exterior degrees. -/
theorem doubleConjugateLinearEquiv_symm_apply (x : B) (v : DetBundle ℂ F E x) :
    (doubleConjugateLinearEquiv (F := F) (E := E) x).symm v =
      (linearEquiv ℂ (Conjugate (Conjugate F))
        (ConjugateBundle (ConjugateBundle E)) x).symm
        (exteriorPower.map (finrank ℂ (Conjugate (Conjugate F)))
          (TauCeti.Conjugate.doubleConjugateLinearEquiv :
            Conjugate (Conjugate (E x)) ≃ₗ[ℂ] E x).symm.toLinearMap
          ((LinearEquiv.ofEq _ _ (congrArg (fun n => ⋀[ℂ]^n (E x))
            ((finrank_complex (V := Conjugate F)).trans (finrank_complex (V := F))))).symm
              (linearEquiv ℂ F E x v))) := by
  simp only [doubleConjugateLinearEquiv, LinearEquiv.symm_trans_apply,
    LinearEquiv.symm_symm, LinearEquiv.exteriorPower_symm,
    ← LinearEquiv.coe_toLinearMap, LinearEquiv.exteriorPower_toLinearMap]

/-- Cancelling two conjugations of the native determinant agrees with taking the determinant
of the canonical cancellation of two conjugations on the original fibre. -/
theorem conjugateLinearEquiv_double (x : B)
    (v : DetBundle ℂ (Conjugate (Conjugate F)) (ConjugateBundle (ConjugateBundle E)) x) :
    (TauCeti.Conjugate.doubleConjugateLinearEquiv :
      Conjugate (Conjugate (DetBundle ℂ F E x)) ≃ₗ[ℂ] DetBundle ℂ F E x)
      ((conjugateLinearEquiv (F := F) (E := E) x).conjugate
        (conjugateLinearEquiv (F := Conjugate F) (E := ConjugateBundle E) x v)) =
      doubleConjugateLinearEquiv (F := F) (E := E) x v := by
  have hd := exteriorPower.conjugateEquiv_ofEq_double
    (finrank_complex (V := Conjugate F)) (finrank_complex (V := F))
    (linearEquiv ℂ (Conjugate (Conjugate F)) (ConjugateBundle (ConjugateBundle E)) x v)
  simpa only [LinearEquiv.conjugate_apply,
    TauCeti.Conjugate.doubleConjugateLinearEquiv_apply, conjugateLinearEquiv_apply,
    doubleConjugateLinearEquiv_apply, ofConj_toConj, LinearEquiv.apply_symm_apply] using
    congrArg (linearEquiv ℂ F E x).symm hd

/-- The independent native double-conjugation transport is continuous on each determinant fibre. -/
def doubleConjugateEquiv (x : B) :
    DetBundle ℂ (Conjugate (Conjugate F)) (ConjugateBundle (ConjugateBundle E)) x ≃L[ℂ]
      DetBundle ℂ F E x :=
  (doubleConjugateLinearEquiv (F := F) (E := E) x).toContinuousLinearEquivOfIsModuleTopology

@[simp] theorem doubleConjugateEquiv_apply (x : B)
    (v : DetBundle ℂ (Conjugate (Conjugate F)) (ConjugateBundle (ConjugateBundle E)) x) :
    doubleConjugateEquiv (F := F) (E := E) x v =
      doubleConjugateLinearEquiv (F := F) (E := E) x v := by
  simp only [doubleConjugateEquiv, LinearEquiv.coe_toContinuousLinearEquivOfIsModuleTopology]

/-- The inverse continuous double-conjugation map is the inverse algebraic transport. -/
@[simp] theorem doubleConjugateEquiv_symm_apply (x : B) (v : DetBundle ℂ F E x) :
    (doubleConjugateEquiv (F := F) (E := E) x).symm v =
      (doubleConjugateLinearEquiv (F := F) (E := E) x).symm v := by
  simp only [doubleConjugateEquiv,
    LinearEquiv.symm_toContinuousLinearEquivOfIsModuleTopology,
    LinearEquiv.coe_toContinuousLinearEquivOfIsModuleTopology]

/-- The continuous native fibre comparisons satisfy the full double-conjugation law. -/
theorem conjugateEquiv_double (x : B)
    (v : DetBundle ℂ (Conjugate (Conjugate F)) (ConjugateBundle (ConjugateBundle E)) x) :
    ofConj (conjugateEquiv (F := F) (E := E) x
      (ofConj (conjugateEquiv (F := Conjugate F) (E := ConjugateBundle E) x v))) =
      doubleConjugateEquiv (F := F) (E := E) x v := by
  simpa only [LinearEquiv.conjugate_apply,
    TauCeti.Conjugate.doubleConjugateLinearEquiv_apply, ofConj_toConj,
    conjugateEquiv_apply, doubleConjugateEquiv_apply] using
    conjugateLinearEquiv_double (F := F) (E := E) x v

section Pullback

variable {B' : Type*}

/-- The native exterior comparison commutes with the canonical determinant-pullback maps,
along any map of bases. -/
theorem conjugateLinearEquiv_pullback (f : B' → B) (y : B')
    (v : (f *ᵖ (DetBundle ℂ (Conjugate F) (ConjugateBundle E))) y) :
    conjugateLinearEquiv (F := F) (E := f *ᵖ E) y
      (pullbackEquiv (𝕜 := ℂ) (F := Conjugate F) (E := ConjugateBundle E) f y v) =
      toConj (pullbackEquiv (𝕜 := ℂ) (F := F) (E := E) f y
        (ofConj (conjugateLinearEquiv (F := F) (E := E) (f y) v))) := by
  -- Both sides are complex-linear in `v`; compare them on exterior generators.
  have h : (conjugateLinearEquiv (F := F) (E := f *ᵖ E) y).toLinearMap ∘ₗ
      (pullbackEquiv (𝕜 := ℂ) (F := Conjugate F) (E := ConjugateBundle E) f y).toLinearMap ∘ₗ
        (linearEquiv ℂ (Conjugate F) (ConjugateBundle E) (f y)).symm.toLinearMap =
      (pullbackEquiv (𝕜 := ℂ) (F := F) (E := E) f y).toLinearEquiv.conjugate.toLinearMap ∘ₗ
        (conjugateLinearEquiv (F := F) (E := E) (f y)).toLinearMap ∘ₗ
          (linearEquiv ℂ (Conjugate F) (ConjugateBundle E) (f y)).symm.toLinearMap := by
    refine exteriorPower.linearMap_ext (AlternatingMap.ext fun a => ?_)
    simp only [LinearMap.compAlternatingMap_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearEquiv.conjugate_apply, ContinuousLinearEquiv.coe_toLinearEquiv]
    have hl := (congrArg (conjugateLinearEquiv (F := F) (E := f *ᵖ E) y)
      (pullbackEquiv_ιMulti (𝕜 := ℂ) (F := Conjugate F) (E := ConjugateBundle E) f y a)).trans
      (conjugateLinearEquiv_ιMulti (F := F) (E := f *ᵖ E) y a)
    have hr := congrArg (fun z => toConj (pullbackEquiv (𝕜 := ℂ) (F := F) (E := E) f y
      (ofConj z))) (conjugateLinearEquiv_ιMulti (F := F) (E := E) (f y) a)
    exact hl.trans ((hr.trans (congrArg toConj (pullbackEquiv_ιMulti (𝕜 := ℂ) (F := F) (E := E)
      f y (fun i => ofConj (a (Fin.cast (finrank_complex (V := F)).symm i)))))).symm)
  have hv := LinearMap.congr_fun h (linearEquiv ℂ (Conjugate F) (ConjugateBundle E) (f y) v)
  rw [LinearMap.comp_apply
    (f := (pullbackEquiv (𝕜 := ℂ) (F := F) (E := E) f y).toLinearEquiv.conjugate.toLinearMap),
    LinearEquiv.coe_coe, LinearEquiv.conjugate_apply] at hv
  exact hv

/-- Conjugation of native determinant fibres commutes with canonical determinant pullback,
along any map of bases. -/
theorem conjugateEquiv_pullback (f : B' → B) (y : B')
    (v : (f *ᵖ (DetBundle ℂ (Conjugate F) (ConjugateBundle E))) y) :
    conjugateEquiv (F := F) (E := f *ᵖ E) y
      (pullbackEquiv (𝕜 := ℂ) (F := Conjugate F) (E := ConjugateBundle E) f y v) =
      toConj (pullbackEquiv (𝕜 := ℂ) (F := F) (E := E) f y
        (ofConj (conjugateEquiv (F := F) (E := E) (f y) v))) :=
  (conjugateEquiv_apply y _).trans ((conjugateLinearEquiv_pullback f y v).trans
    (congrArg (fun a => toConj (pullbackEquiv (𝕜 := ℂ) (F := F) (E := E) f y (ofConj a)))
      (conjugateEquiv_apply (f y) v)).symm)

end Pullback

section Model

variable [FiniteDimensional ℂ F]

/-- The comparison in scalar model coordinates. Both determinant coordinates use their actual
independently chosen model bases, so this equivalence need not send `1` to `toConj 1`. -/
def conjugateModelEquiv : ℂ ≃ₗ[ℂ] Conjugate ℂ :=
  (modelCoord (Conjugate F)).symm ≪≫ₗ
    (linearEquiv ℂ (Conjugate F) (ConjugateBundle (fun _ : Unit => F)) ()).symm ≪≫ₗ
    conjugateLinearEquiv (F := F) (E := fun _ : Unit => F) () ≪≫ₗ
    (linearEquiv ℂ F (fun _ : Unit => F) ()).conjugate ≪≫ₗ
    (modelCoord F).conjugate

theorem conjugateModelEquiv_def (c : ℂ) :
    conjugateModelEquiv (F := F) c =
      toConj (modelCoord F (linearEquiv ℂ F (fun _ : Unit => F) () (ofConj
        (conjugateLinearEquiv (F := F) (E := fun _ : Unit => F) ()
          ((linearEquiv ℂ (Conjugate F) (ConjugateBundle (fun _ : Unit => F)) ()).symm
            ((modelCoord (Conjugate F)).symm c)))))) := by
  simp only [conjugateModelEquiv, LinearEquiv.trans_apply, LinearEquiv.conjugate_apply,
    ofConj_toConj]

/-- The model-dependent coefficient of the conjugate determinant comparison. -/
def conjugateModelCoefficient : Conjugate ℂ := conjugateModelEquiv (F := F) 1

theorem conjugateModelEquiv_apply (c : ℂ) :
    conjugateModelEquiv (F := F) c = c • conjugateModelCoefficient (F := F) := by
  simpa [conjugateModelCoefficient] using
    (conjugateModelEquiv (F := F)).map_smul c (1 : ℂ)

theorem conjugateModelCoefficient_ne_zero : conjugateModelCoefficient (F := F) ≠ 0 := by
  simpa only [conjugateModelCoefficient, map_zero] using
    (conjugateModelEquiv (F := F)).injective.ne (one_ne_zero : (1 : ℂ) ≠ 0)

end Model


section Chart

variable [TopologicalSpace B] [TopologicalSpace (TotalSpace F E)] [FiniteDimensional ℂ F]

/-- The full coordinate square for the independently defined native fibre comparison.
The scalar-model comparison retains the coefficient arising from the two model bases. -/
theorem chartCoord_conjugateLinearEquiv (e : Trivialization F (π F E)) [e.IsLinear ℂ]
    {x : B} (hx : x ∈ e.baseSet)
    (v : DetBundle ℂ (Conjugate F) (ConjugateBundle E) x) :
    toConj (chartCoord e hx (ofConj (conjugateLinearEquiv (F := F) (E := E) x v))) =
      conjugateModelEquiv (F := F) (chartCoord e.conjugate
        (e.baseSet_conjugate.symm ▸ hx) v) := by
  have h := exteriorPower.conjugateEquiv_ofEq_map (finrank_complex (V := F))
    (e.linearEquivAt ℂ x hx).toLinearMap
    (linearEquiv ℂ (Conjugate F) (ConjugateBundle E) x v)
  rw [← Trivialization.linearEquivAt_conjugate e hx] at h
  have h' := congrArg (fun a : Conjugate (⋀[ℂ]^(finrank ℂ F) F) =>
    toConj (modelCoord F (ofConj a))) h
  simp only [conjugateLinearEquiv_apply, conjugateModelEquiv_def, chartCoord_apply,
    LinearEquiv.apply_symm_apply, LinearEquiv.symm_apply_apply,
    ofConj_toConj]
  simpa only [linearEquiv_apply, LinearMap.conjugate_apply, ofConj_toConj,
    LinearEquiv.coe_toLinearMap,
    ← LinearEquiv.coe_toLinearMap ((e.linearEquivAt ℂ x hx).exteriorPower (finrank ℂ F)),
    ← LinearEquiv.coe_toLinearMap ((e.conjugate.linearEquivAt ℂ x
      (e.baseSet_conjugate.symm ▸ hx)).exteriorPower
        (finrank ℂ (Conjugate F))), LinearEquiv.exteriorPower_toLinearMap] using h'.symm

/-- The inverse chart formula retains the inverse of the actual model comparison. -/
theorem chartCoord_conjugateLinearEquiv_symm
    (e : Trivialization F (π F E)) [e.IsLinear ℂ] {x : B} (hx : x ∈ e.baseSet)
    (w : Conjugate (DetBundle ℂ F E x)) :
    chartCoord e.conjugate
      (e.baseSet_conjugate.symm ▸ hx)
      ((conjugateLinearEquiv (F := F) (E := E) x).symm w) =
    (conjugateModelEquiv (F := F)).symm (toConj (chartCoord e hx (ofConj w))) := by
  apply (conjugateModelEquiv (F := F)).injective
  rw [LinearEquiv.apply_symm_apply]
  simpa only [LinearEquiv.apply_symm_apply] using
    (chartCoord_conjugateLinearEquiv e hx
      ((conjugateLinearEquiv (F := F) (E := E) x).symm w)).symm

end Chart

section TotalSpace

variable [TopologicalSpace B] [FiniteDimensional ℂ F]
  [∀ x, TopologicalSpace (E x)] [TopologicalSpace (TotalSpace F E)]
  [FiberBundle F E] [VectorBundle ℂ F E]

/-- Continuity of the actual native determinant-conjugation map on total spaces. -/
theorem continuous_conjugateEquiv :
    Continuous (fun p : TotalSpace ℂ (DetBundle ℂ (Conjugate F) (ConjugateBundle E)) =>
      (TotalSpace.mk' (Conjugate ℂ) p.proj (conjugateEquiv (F := F) (E := E) p.proj p.snd) :
        TotalSpace (Conjugate ℂ) (ConjugateBundle (DetBundle ℂ F E)))) := by
  refine FiberBundle.continuous_of_forall_trivialization _ (fun _ => rfl) fun p => ?_
  let e := trivializationAt F E p.proj
  let eS := trivialization (𝕜 := ℂ) e.conjugate
  let eT := (trivialization (𝕜 := ℂ) e).conjugate
  have hx : p.proj ∈ e.baseSet := mem_baseSet_trivializationAt F E p.proj
  have hs : p.proj ∈ eS.baseSet := by
    simpa only [eS, trivialization_baseSet, Trivialization.baseSet_conjugate] using hx
  have ht : p.proj ∈ eT.baseSet := by
    simpa only [eT, Trivialization.baseSet_conjugate, trivialization_baseSet] using hx
  refine ⟨eS, eT, fun _ c => conjugateModelEquiv (F := F) c, hs, ht, ?_, ?_⟩
  · exact (conjugateModelEquiv (F := F)).toContinuousLinearEquiv.continuous.continuousAt.comp
      ((eS.continuousOn.continuousAt
        (eS.open_source.mem_nhds (eS.mem_source.mpr hs))).snd)
  · rintro ⟨x, v⟩ hxS _
    have hxe : x ∈ e.baseSet := by
      simpa only [eS, trivialization_baseSet, Trivialization.baseSet_conjugate] using hxS
    have hxc : x ∈ e.conjugate.baseSet :=
      e.baseSet_conjugate.symm ▸ hxe
    simp only [eS, eT, Trivialization.conjugate_apply,
      ConjugateBundle.toConjHomeomorph_symm_apply, conjugateEquiv_apply]
    rw [trivialization_apply_mk e hxe, trivialization_apply_mk e.conjugate hxc]
    exact chartCoord_conjugateLinearEquiv e hxe v

/-- The determinant of the conjugate bundle is the conjugate of the determinant bundle,
as a homeomorphism on the actual total spaces and a linear equivalence on every fibre. -/
def conjugateHomeomorph :
    TotalSpace ℂ (DetBundle ℂ (Conjugate F) (ConjugateBundle E)) ≃ₜ
      TotalSpace (Conjugate ℂ) (ConjugateBundle (DetBundle ℂ F E)) :=
  bundleHomeomorph (conjugateEquiv (F := F) (E := E)) continuous_conjugateEquiv

@[simp] theorem conjugateHomeomorph_apply
    (p : TotalSpace ℂ (DetBundle ℂ (Conjugate F) (ConjugateBundle E))) :
    conjugateHomeomorph (F := F) (E := E) p =
      ⟨p.proj, conjugateEquiv (F := F) (E := E) p.proj p.snd⟩ := by
  rw [conjugateHomeomorph, bundleHomeomorph_apply]

@[simp] theorem conjugateHomeomorph_symm_apply
    (p : TotalSpace (Conjugate ℂ) (ConjugateBundle (DetBundle ℂ F E))) :
    (conjugateHomeomorph (F := F) (E := E)).symm p =
      ⟨p.proj, (conjugateEquiv (F := F) (E := E) p.proj).symm p.snd⟩ := by
  rw [conjugateHomeomorph, bundleHomeomorph_symm_apply]

theorem proj_conjugateHomeomorph
    (p : TotalSpace ℂ (DetBundle ℂ (Conjugate F) (ConjugateBundle E))) :
    (conjugateHomeomorph (F := F) (E := E) p).proj = p.proj := by
  rw [conjugateHomeomorph_apply]

/-- The composite of the two conjugation comparisons with the canonical double-conjugation
cancellation, evaluated at a point. -/
private theorem doubleConjugationComposite_apply
    (p : TotalSpace ℂ (DetBundle ℂ (Conjugate (Conjugate F))
      (ConjugateBundle (ConjugateBundle E)))) :
    ((conjugateHomeomorph (F := Conjugate F) (E := ConjugateBundle E)).trans
    (((ConjugateBundle.toConjHomeomorph ℂ
      (DetBundle ℂ (Conjugate F) (ConjugateBundle E))).symm).trans
      ((conjugateHomeomorph (F := F) (E := E)).trans
        ((ConjugateBundle.toConjHomeomorph (Conjugate ℂ)
          (ConjugateBundle (DetBundle ℂ F E))).trans
            (ConjugateBundle.doubleConjugateHomeomorph ℂ (DetBundle ℂ F E)))))) p =
      (⟨p.proj, doubleConjugateEquiv (F := F) (E := E) p.proj p.snd⟩ :
        TotalSpace ℂ (DetBundle ℂ F E)) := by
  simp only [Homeomorph.trans_apply, conjugateHomeomorph_apply,
    ConjugateBundle.toConjHomeomorph_symm_apply, ConjugateBundle.toConjHomeomorph_apply,
    ConjugateBundle.doubleConjugateHomeomorph_apply, ofConj_toConj]
  exact congrArg (fun v => (⟨p.proj, v⟩ : TotalSpace ℂ (DetBundle ℂ F E)))
    (conjugateEquiv_double p.proj p.snd)

/-- Continuity of the independently defined native double-conjugation transport. -/
theorem continuous_doubleConjugateEquiv :
    Continuous (fun p : TotalSpace ℂ (DetBundle ℂ (Conjugate (Conjugate F))
      (ConjugateBundle (ConjugateBundle E))) =>
        (⟨p.proj, doubleConjugateEquiv (F := F) (E := E) p.proj p.snd⟩ :
          TotalSpace ℂ (DetBundle ℂ F E))) :=
  ((conjugateHomeomorph (F := Conjugate F) (E := ConjugateBundle E)).trans
    (((ConjugateBundle.toConjHomeomorph ℂ
      (DetBundle ℂ (Conjugate F) (ConjugateBundle E))).symm).trans
      ((conjugateHomeomorph (F := F) (E := E)).trans
        ((ConjugateBundle.toConjHomeomorph (Conjugate ℂ)
          (ConjugateBundle (DetBundle ℂ F E))).trans
            (ConjugateBundle.doubleConjugateHomeomorph ℂ (DetBundle ℂ F E)))))).continuous.congr
    (doubleConjugationComposite_apply (F := F) (E := E))

/-- Taking the determinant of the canonical double-conjugation cancellation, on the actual
native total spaces. Its fibre map is the independent exterior-functor transport above. -/
def doubleConjugateHomeomorph :
    TotalSpace ℂ (DetBundle ℂ (Conjugate (Conjugate F))
      (ConjugateBundle (ConjugateBundle E))) ≃ₜ TotalSpace ℂ (DetBundle ℂ F E) :=
  bundleHomeomorph (doubleConjugateEquiv (F := F) (E := E)) continuous_doubleConjugateEquiv

@[simp] theorem doubleConjugateHomeomorph_apply
    (p : TotalSpace ℂ (DetBundle ℂ (Conjugate (Conjugate F))
      (ConjugateBundle (ConjugateBundle E)))) :
    doubleConjugateHomeomorph (F := F) (E := E) p =
      ⟨p.proj, doubleConjugateEquiv (F := F) (E := E) p.proj p.snd⟩ := by
  rw [doubleConjugateHomeomorph, bundleHomeomorph_apply]

@[simp] theorem doubleConjugateHomeomorph_symm_apply
    (p : TotalSpace ℂ (DetBundle ℂ F E)) :
    (doubleConjugateHomeomorph (F := F) (E := E)).symm p =
      ⟨p.proj, (doubleConjugateEquiv (F := F) (E := E) p.proj).symm p.snd⟩ := by
  rw [doubleConjugateHomeomorph, bundleHomeomorph_symm_apply]

/-- Applying determinant conjugation twice agrees with the determinant of the canonical
cancellation of two conjugations on `E`, as an equality of native total-space maps. -/
theorem conjugateHomeomorph_double :
    (conjugateHomeomorph (F := Conjugate F) (E := ConjugateBundle E)).trans
      (((ConjugateBundle.toConjHomeomorph ℂ
        (DetBundle ℂ (Conjugate F) (ConjugateBundle E))).symm).trans
        ((conjugateHomeomorph (F := F) (E := E)).trans
          ((ConjugateBundle.toConjHomeomorph (Conjugate ℂ)
            (ConjugateBundle (DetBundle ℂ F E))).trans
              (ConjugateBundle.doubleConjugateHomeomorph ℂ (DetBundle ℂ F E))))) =
      doubleConjugateHomeomorph (F := F) (E := E) := by
  ext p : 1
  -- Instantiate the pointwise formula before unifying with the type of `p`, which would
  -- otherwise fix the fibre dictionaries of `E` in a form that instance search does not recognise.
  have h := doubleConjugationComposite_apply (F := F) (E := E)
  rw [doubleConjugateHomeomorph_apply]
  exact h p

end TotalSpace

section Pullback

universe uX

variable [TopologicalSpace B] [FiniteDimensional ℂ F]
  [∀ x, TopologicalSpace (E x)] [TopologicalSpace (TotalSpace F E)]
  [FiberBundle F E] [VectorBundle ℂ F E]
  {X : Type uX} [TopologicalSpace X]

/-- Pull back the native conjugation homeomorphism. This uses only the induced topology on
pullback total spaces and is defined independently of the determinant-pullback comparisons. -/
def pulledConjugateHomeomorph (f : X → B) :
    TotalSpace ℂ (f *ᵖ (DetBundle ℂ (Conjugate F) (ConjugateBundle E))) ≃ₜ
      TotalSpace (Conjugate ℂ) (f *ᵖ (ConjugateBundle (DetBundle ℂ F E))) where
  toFun p := ⟨p.proj, conjugateEquiv (F := F) (E := E) (f p.proj) p.snd⟩
  invFun p := ⟨p.proj, (conjugateEquiv (F := F) (E := E) (f p.proj)).symm p.snd⟩
  left_inv p := by
    rcases p with ⟨x, v⟩
    apply TotalSpace.mk_inj.mpr
    exact (conjugateEquiv (F := F) (E := E) (f x)).symm_apply_apply v
  right_inv p := by
    rcases p with ⟨x, v⟩
    apply TotalSpace.mk_inj.mpr
    exact (conjugateEquiv (F := F) (E := E) (f x)).apply_symm_apply v
  continuous_toFun :=
    Pullback.continuous_fiberwise (Φ := fun x => conjugateEquiv (F := F) (E := E) x)
      continuous_conjugateEquiv f
  continuous_invFun :=
    Pullback.continuous_fiberwise (Φ := fun x => (conjugateEquiv (F := F) (E := E) x).symm)
      ((conjugateHomeomorph (F := F) (E := E)).symm.continuous.congr
        conjugateHomeomorph_symm_apply) f

@[simp] theorem pulledConjugateHomeomorph_apply (f : X → B)
    (p : TotalSpace ℂ (f *ᵖ (DetBundle ℂ (Conjugate F) (ConjugateBundle E)))) :
    pulledConjugateHomeomorph (F := F) (E := E) f p =
      ⟨p.proj, conjugateEquiv (F := F) (E := E) (f p.proj) p.snd⟩ := by rfl

@[simp] theorem pulledConjugateHomeomorph_symm_apply (f : X → B)
    (p : TotalSpace (Conjugate ℂ) (f *ᵖ (ConjugateBundle (DetBundle ℂ F E)))) :
    (pulledConjugateHomeomorph (F := F) (E := E) f).symm p =
      ⟨p.proj, (conjugateEquiv (F := F) (E := E) (f p.proj)).symm p.snd⟩ := by rfl

variable {K : Type*} [FunLike K X B] [ContinuousMapClass K X B]

/-- The target-side comparison is the conjugate of the canonical determinant-pullback
homeomorphism, using the independently defined conjugation homeomorphisms of total spaces. -/
def conjugateTargetPullbackHomeomorph (f : K) :
    TotalSpace (Conjugate ℂ) ((f : X → B) *ᵖ (ConjugateBundle (DetBundle ℂ F E))) ≃ₜ
      TotalSpace (Conjugate ℂ) (ConjugateBundle (DetBundle ℂ F ((f : X → B) *ᵖ E))) :=
  (ConjugateBundle.pullbackHomeomorph ℂ (DetBundle ℂ F E) (f : X → B)).trans
    (((ConjugateBundle.toConjHomeomorph ℂ ((f : X → B) *ᵖ (DetBundle ℂ F E))).symm.trans
      (pullbackHomeomorph (𝕜 := ℂ) (F := F) (E := E) f)).trans
        (ConjugateBundle.toConjHomeomorph ℂ (DetBundle ℂ F ((f : X → B) *ᵖ E))))

@[simp] theorem conjugateTargetPullbackHomeomorph_apply (f : K)
    (p : TotalSpace (Conjugate ℂ)
      ((f : X → B) *ᵖ (ConjugateBundle (DetBundle ℂ F E)))) :
    conjugateTargetPullbackHomeomorph (F := F) (E := E) f p =
      ⟨p.proj, toConj (pullbackEquiv (𝕜 := ℂ) (F := F) (E := E)
        (f : X → B) p.proj (ofConj p.snd))⟩ := by
  rw [conjugateTargetPullbackHomeomorph, Homeomorph.trans_apply,
    ConjugateBundle.pullbackHomeomorph_apply, Homeomorph.trans_apply,
    Homeomorph.trans_apply, ConjugateBundle.toConjHomeomorph_symm_apply,
    pullbackHomeomorph_apply, ConjugateBundle.toConjHomeomorph_apply]

/-- The inverse target comparison conjugates the inverse canonical determinant pullback. -/
@[simp↓] theorem conjugateTargetPullbackHomeomorph_symm_apply (f : K)
    (p : TotalSpace (Conjugate ℂ)
      (ConjugateBundle (DetBundle ℂ F ((f : X → B) *ᵖ E)))) :
    (conjugateTargetPullbackHomeomorph (F := F) (E := E) f).symm p =
      ⟨p.proj, toConj ((pullbackEquiv (𝕜 := ℂ) (F := F) (E := E)
        (f : X → B) p.proj).symm (ofConj p.snd))⟩ := by
  simp only [conjugateTargetPullbackHomeomorph, Homeomorph.symm_trans_apply,
    Homeomorph.symm_symm, ConjugateBundle.toConjHomeomorph_symm_apply,
    pullbackHomeomorph_symm_apply, ConjugateBundle.toConjHomeomorph_apply,
    ConjugateBundle.pullbackHomeomorph_symm_apply]
  -- The component formulas leave only the definitionally equal reindexed fibre presentations.
  rfl

/-- The full pullback square of native total-space homeomorphisms commutes. -/
theorem conjugateHomeomorph_pullback (f : K) :
    (pullbackHomeomorph (𝕜 := ℂ) (F := Conjugate F) (E := ConjugateBundle E) f).trans
      (conjugateHomeomorph (F := F) (E := (f : X → B) *ᵖ E)) =
    (pulledConjugateHomeomorph (F := F) (E := E) (f : X → B)).trans
      (conjugateTargetPullbackHomeomorph (F := F) (E := E) f) := by
  ext p : 1
  conv_rhs =>
    rw [Homeomorph.trans_apply, pulledConjugateHomeomorph_apply,
      conjugateTargetPullbackHomeomorph_apply]
  -- The left composite passes through two presentations of the same fibres:
  -- `pullbackHomeomorph` lands in `DetBundle ℂ (Conjugate F) (f *ᵖ ConjugateBundle E)`, while
  -- `conjugateHomeomorph` starts from `DetBundle ℂ (Conjugate F) (ConjugateBundle (f *ᵖ E))`.
  -- They agree only up to unfolding the pullback and conjugate fibre aliases, so `erw` is needed.
  erw [Homeomorph.trans_apply,
    pullbackHomeomorph_apply (𝕜 := ℂ) (F := Conjugate F) (E := ConjugateBundle E) f,
    conjugateHomeomorph_apply (F := F) (E := (f : X → B) *ᵖ E)]
  exact congrArg (fun z => (⟨p.proj, z⟩ :
    TotalSpace (Conjugate ℂ) (ConjugateBundle (DetBundle ℂ F ((f : X → B) *ᵖ E)))))
    (conjugateEquiv_pullback (f : X → B) p.proj p.snd)

end Pullback

end TauCeti.DetBundle
