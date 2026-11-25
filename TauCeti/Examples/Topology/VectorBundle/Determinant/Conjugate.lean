/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.VectorBundle.Determinant.Conjugate

/-!
# Clients of native determinant conjugation

These clients exercise nonreal scalar conjugation on an infinite complex module, the nonzero
zeroth exterior product, native rank-two and rank-zero bundles, an empty base, a model in an
independent universe, pullback along a nonidentity continuous map and double conjugation.
-/

public section

noncomputable section

open Bundle Module TauCeti TauCeti.Conjugate

namespace TauCeti.Examples.DetBundleConjugate

universe u

/-- The scalar `I` really becomes `-I` after forgetting a conjugate scalar action, even on
an exterior power of an infinite-dimensional module. -/
theorem nonrealScalar_on_infiniteModule (a : Fin 2 → (ℕ → ℂ)) :
    ofConj (exteriorPower.conjugateEquiv 2
      (Complex.I • exteriorPower.ιMulti ℂ 2 (fun i => toConj (a i)))) =
      -Complex.I • exteriorPower.ιMulti ℂ 2 a := by
  simp only [map_smul, exteriorPower.conjugateEquiv_ιMulti, ofConj_smul,
    ofConj_toConj, Complex.conj_I, Function.comp_def]

/-- The degree-zero comparison preserves the exterior unit, which does not vanish. -/
theorem zerothExteriorUnit_ne_zero : exteriorPower.conjugateEquiv 0
    (exteriorPower.ιMulti ℂ 0 (fun i : Fin 0 => (Fin.elim0 i : Conjugate (Fin 0 → ℂ)))) ≠
      0 := by
  intro h
  have ha := (exteriorPower.conjugateEquiv 0 (V := Fin 0 → ℂ)).injective
    (h.trans (map_zero (exteriorPower.conjugateEquiv 0)).symm)
  have hz := congrArg (exteriorPower.zeroEquiv ℂ (Conjugate (Fin 0 → ℂ))) ha
  exact one_ne_zero (by simpa only [exteriorPower.zeroEquiv_ιMulti, map_zero] using hz)

local notation "Plane" => (Fin 2 → ℂ)
local notation "ZeroModel" => (Fin 0 → ℂ)

/-- The concrete rank-two model really has complex dimension two. -/
theorem plane_finrank : finrank ℂ Plane = 2 := by
  simp only [Module.finrank_pi, Fintype.card_fin]

/-- The zero model has rank zero; its determinant below is still a line. -/
theorem zeroModel_finrank : finrank ℂ ZeroModel = 0 := by simp


/-- Actual rank-two native determinant vectors use the transported exterior generator. -/
theorem rankTwo_generator (a : Fin (finrank ℂ (Conjugate Plane)) → Conjugate Plane) :
    DetBundle.conjugateLinearEquiv (F := Plane) (E := Trivial Unit Plane) ()
      ((DetBundle.linearEquiv ℂ (Conjugate Plane) (ConjugateBundle (Trivial Unit Plane))
          ()).symm (exteriorPower.ιMulti ℂ _ a)) =
      toConj ((DetBundle.linearEquiv ℂ Plane (Trivial Unit Plane) ()).symm
        (exteriorPower.ιMulti ℂ _ (fun i =>
          ofConj (a (Fin.cast (finrank_complex (V := Plane)).symm i))))) :=
  DetBundle.conjugateLinearEquiv_ιMulti (F := Plane) (E := Trivial Unit Plane) () a

/-- The rank-two chart factor is nonzero, in its actual model coordinates. -/
theorem rankTwo_modelCoefficient_ne_zero : DetBundle.conjugateModelCoefficient (F := Plane) ≠ 0 :=
  DetBundle.conjugateModelCoefficient_ne_zero

/-- Rank zero still has a native determinant line and a total-space comparison. -/
theorem rankZero_totalSpaceComparison : Nonempty
    (TotalSpace ℂ
      (DetBundle ℂ (Conjugate ZeroModel) (ConjugateBundle (Trivial Unit ZeroModel))) ≃ₜ
      TotalSpace (Conjugate ℂ)
        (ConjugateBundle (DetBundle ℂ ZeroModel (Trivial Unit ZeroModel)))) :=
  ⟨DetBundle.conjugateHomeomorph (F := ZeroModel) (E := Trivial Unit ZeroModel)⟩

/-- Formation of the native total-space comparison imposes no inhabited-base hypothesis. -/
theorem emptyBase_totalSpaceComparison : Nonempty
    (TotalSpace ℂ (DetBundle ℂ (Conjugate Plane) (ConjugateBundle (Trivial Empty Plane))) ≃ₜ
      TotalSpace (Conjugate ℂ) (ConjugateBundle (DetBundle ℂ Plane (Trivial Empty Plane)))) :=
  ⟨DetBundle.conjugateHomeomorph (F := Plane) (E := Trivial Empty Plane)⟩

/-- A noninvertible fibre map is allowed, and its target model lives in an independent universe. -/
theorem zeroMap_independentModel_naturality
    (v : DetBundle ℂ (Conjugate Plane) (ConjugateBundle (Trivial Unit Plane)) ()) :
    let h : finrank ℂ Plane = finrank ℂ (ULift.{u} Plane) := by simp
    let hc := (finrank_complex (V := Plane)).trans
      (h.trans (finrank_complex (V := ULift.{u} Plane)).symm)
    DetBundle.conjugateLinearEquiv (F := ULift.{u} Plane) (E := Trivial Unit Plane) ()
      ((DetBundle.linearEquiv ℂ (Conjugate (ULift.{u} Plane))
        (ConjugateBundle (Trivial Unit Plane)) ()).symm
          (LinearEquiv.ofEq _ _ (congrArg (fun n => ⋀[ℂ]^n (Conjugate Plane)) hc)
            (exteriorPower.map (finrank ℂ (Conjugate Plane))
              (0 : Plane →ₗ[ℂ] Plane).conjugate
              (DetBundle.linearEquiv ℂ (Conjugate Plane)
                (ConjugateBundle (Trivial Unit Plane)) () v)))) =
      toConj ((DetBundle.linearEquiv ℂ (ULift.{u} Plane) (Trivial Unit Plane) ()).symm
        (LinearEquiv.ofEq _ _ (congrArg (fun n => ⋀[ℂ]^n Plane) h)
          (exteriorPower.map (finrank ℂ Plane) (0 : Plane →ₗ[ℂ] Plane)
            (DetBundle.linearEquiv ℂ Plane (Trivial Unit Plane) ()
              (ofConj (DetBundle.conjugateLinearEquiv (F := Plane)
                (E := Trivial Unit Plane) () v)))))) := by
  exact DetBundle.conjugateLinearEquiv_naturality (F := Plane) (G := ULift.{u} Plane)
    (E := Trivial Unit Plane) (E' := Trivial Unit Plane)
    (by simp) () (0 : Plane →ₗ[ℂ] Plane) v

/-- Pullback along `z ↦ z²` commutes on the actual native total spaces. -/
theorem square_pullback :
    let f : C(ℂ, ℂ) := ⟨fun z => z ^ 2, continuous_id.pow 2⟩
    (DetBundle.pullbackHomeomorph (𝕜 := ℂ) (F := Conjugate Plane)
      (E := ConjugateBundle (Trivial ℂ Plane)) f).trans
      (DetBundle.conjugateHomeomorph (F := Plane)
        (E := (f : ℂ → ℂ) *ᵖ (Trivial ℂ Plane))) =
    (DetBundle.pulledConjugateHomeomorph (F := Plane) (E := Trivial ℂ Plane)
      (f : ℂ → ℂ)).trans
      (DetBundle.conjugateTargetPullbackHomeomorph (F := Plane) (E := Trivial ℂ Plane) f) :=
  DetBundle.conjugateHomeomorph_pullback (F := Plane) (E := Trivial ℂ Plane)
    (⟨fun z => z ^ 2, continuous_id.pow 2⟩ : C(ℂ, ℂ))

/-- Applying the comparison twice returns the independently transported rank-two vector. -/
theorem double_rankTwo (v : DetBundle ℂ (Conjugate (Conjugate Plane))
    (ConjugateBundle (ConjugateBundle (Trivial Unit Plane))) ()) :
    ofConj (DetBundle.conjugateEquiv (F := Plane) (E := Trivial Unit Plane) ()
      (ofConj (DetBundle.conjugateEquiv (F := Conjugate Plane)
        (E := ConjugateBundle (Trivial Unit Plane)) () v))) =
      DetBundle.doubleConjugateEquiv (F := Plane) (E := Trivial Unit Plane) () v :=
  DetBundle.conjugateEquiv_double () v

/-- A nonreal native inverse coordinate uses the true inverse model factor. -/
theorem rankTwo_nonreal_inverse_chart :
    let e := Trivial.trivialization Unit Plane
    let hx : () ∈ e.baseSet := by simp [e]
    DetBundle.chartCoord e.conjugate
      (by simpa only [Trivialization.baseSet_conjugate] using hx)
      ((DetBundle.conjugateLinearEquiv (F := Plane) (E := Trivial Unit Plane) ()).symm
        (toConj ((DetBundle.chartCoord e hx).symm Complex.I))) =
      (DetBundle.conjugateModelEquiv (F := Plane)).symm (toConj Complex.I) := by
  dsimp only
  simpa only [ofConj_toConj, LinearEquiv.apply_symm_apply] using
    DetBundle.chartCoord_conjugateLinearEquiv_symm
      (Trivial.trivialization Unit Plane) (by simp)
      (toConj ((DetBundle.chartCoord (Trivial.trivialization Unit Plane) (by simp)).symm
        Complex.I))

/-- The pointwise bundle-isomorphism corollary elaborates over an empty base without a
`Nonempty` hypothesis, with model presentations in independent universes. -/
theorem emptyBase_bundleIso_naturality (x : Empty)
    (v : DetBundle ℂ (Conjugate Plane) (ConjugateBundle (Trivial Empty Plane)) x) :
    let e : ∀ _ : Empty, Plane ≃L[ℂ] ULift.{u} Plane := fun _ =>
      (ULift.moduleEquiv (R := ℂ) (M := Plane)).symm.toContinuousLinearEquiv
    DetBundle.conjugateLinearEquiv (F := ULift.{u} Plane)
      (E := Trivial Empty (ULift.{u} Plane)) x
      (DetBundle.congrModelEquiv (F₁ := Conjugate Plane) (F' := Conjugate (ULift.{u} Plane))
        (fun x => (e x).conjugate) x v) =
      toConj (DetBundle.congrModelEquiv (F₁ := Plane) (F' := ULift.{u} Plane) e x
        (ofConj (DetBundle.conjugateLinearEquiv (F := Plane) (E := Trivial Empty Plane) x v))) :=
  DetBundle.conjugateLinearEquiv_bundleIso_naturality _ x v

/-- Pointwise bundle-isomorphism naturality at a point of a nonempty base, with independent
model universes and an arbitrary determinant vector. -/
theorem unitBase_bundleIso_naturality (x : Unit)
    (v : DetBundle ℂ (Conjugate Plane) (ConjugateBundle (Trivial Unit Plane)) x) :
    let e : ∀ _ : Unit, Plane ≃L[ℂ] ULift.{u} Plane := fun _ =>
      (ULift.moduleEquiv (R := ℂ) (M := Plane)).symm.toContinuousLinearEquiv
    DetBundle.conjugateLinearEquiv (F := ULift.{u} Plane)
      (E := Trivial Unit (ULift.{u} Plane)) x
      (DetBundle.congrModelEquiv (F₁ := Conjugate Plane) (F' := Conjugate (ULift.{u} Plane))
        (fun x => (e x).conjugate) x v) =
      toConj (DetBundle.congrModelEquiv (F₁ := Plane) (F' := ULift.{u} Plane) e x
        (ofConj (DetBundle.conjugateLinearEquiv (F := Plane) (E := Trivial Unit Plane) x v))) :=
  DetBundle.conjugateLinearEquiv_bundleIso_naturality _ x v

/-- The inverse target comparison conjugates the inverse determinant pullback on arbitrary
rank-two vectors over the pullback along `z ↦ z²`. -/
theorem square_pullback_target_inverse :
    let f : C(ℂ, ℂ) := ⟨fun z => z ^ 2, continuous_id.pow 2⟩
    ∀ p : TotalSpace (Conjugate ℂ)
      (ConjugateBundle (DetBundle ℂ Plane ((f : ℂ → ℂ) *ᵖ (Trivial ℂ Plane)))),
    (DetBundle.conjugateTargetPullbackHomeomorph (F := Plane)
      (E := Trivial ℂ Plane) f).symm p =
      ⟨p.proj, toConj ((DetBundle.pullbackEquiv (𝕜 := ℂ) (F := Plane)
        (E := Trivial ℂ Plane) (f : ℂ → ℂ) p.proj).symm (ofConj p.snd))⟩ := by
  dsimp only
  intro p
  simp

/-- On the rank-two trivial bundle, the inverse determinant conjugation sends conjugated
exterior generators to the exterior product of the conjugated vectors. -/
theorem rankTwo_inverse_generator (a : Fin (finrank ℂ Plane) → Plane) :
    (DetBundle.conjugateLinearEquiv (F := Plane) (E := Trivial Unit Plane) ()).symm
      (toConj ((DetBundle.linearEquiv ℂ Plane (Trivial Unit Plane) ()).symm
        (exteriorPower.ιMulti ℂ _ a))) =
      (DetBundle.linearEquiv ℂ (Conjugate Plane)
        (ConjugateBundle (Trivial Unit Plane)) ()).symm
        (exteriorPower.ιMulti ℂ _
          (fun i => toConj (a (Fin.cast (finrank_complex (V := Plane)) i)))) :=
  DetBundle.conjugateLinearEquiv_symm_ιMulti
    (F := Plane) (E := Trivial Unit Plane) () a

end TauCeti.Examples.DetBundleConjugate
