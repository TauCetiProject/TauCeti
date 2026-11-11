/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.AdicRing.CompletedAway

/-!
# Completed localisations of completed localisations

Let `A` be an adic ring of finite ideal type and `f, g ∈ A`. The completed localisation `A_{f}` is
again an adic ring of finite ideal type, so it has its own completed localisation `(A_{f})_{g}`
away from the image of `g`. This file identifies it with the completed localisation `A_{f g}`: both
are complete, receive a continuous map from `A` inverting `f` and `g`, and are universal with this
property. On formal spectra this says that the basic open set `D(g)` of `Spf A_{f}` is the basic
open set `D(f g)` of `Spf A`, which is how the restriction of `Spf A` to `D(f)` is compared with
`Spf A_{f}`.

The isomorphism is continuous in both directions, fixes the image of `A`, and is compatible with
the restriction maps of completed localisations.

## Main definitions

* `TauCeti.AdicRing.CompletedAway.iterateEquiv`: the isomorphism `(A_{f})_{g} ≃ A_{f g}`.

## Main results

* `TauCeti.AdicRing.CompletedAway.iterateEquiv_algebraMap`: on `A_{f}` it is the restriction map
  `A_{f} → A_{f g}`.
* `TauCeti.AdicRing.CompletedAway.iterateEquiv_symm_algebraMap`: its inverse fixes the image of `A`.
* `TauCeti.AdicRing.CompletedAway.continuous_iterateEquiv`,
  `TauCeti.AdicRing.CompletedAway.continuous_iterateEquiv_symm`: it is a homeomorphism.
* `TauCeti.AdicRing.CompletedAway.iterateEquiv_symm_restrict`: it is compatible with the
  restriction maps.

## References

* A. Grothendieck and J. Dieudonné, *Éléments de géométrie algébrique I*, Ch. 0, §7.6, and
  Ch. I, 10.1.4.
-/

public section

namespace TauCeti.AdicRing.CompletedAway

variable {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsAdicRing A]
  (f g : A)

/-- `f g` lies in the radical of `f A + I`, so there is a restriction map `A_{f} → A_{f g}`. -/
private theorem mul_mem_radical : f * g ∈ (Ideal.span {f} ⊔ IsAdicRing.ideal A).radical :=
  Ideal.le_radical (Ideal.mem_sup_left (Ideal.mem_span_singleton.mpr (dvd_mul_right f g)))

private theorem isUnit_algebraMap_comp_algebraMap :
    IsUnit (((algebraMap (CompletedAway A f)
      (CompletedAway (CompletedAway A f) (algebraMap A (CompletedAway A f) g))).comp
        (algebraMap A (CompletedAway A f))) (f * g)) := by
  rw [RingHom.comp_apply, map_mul, map_mul]
  exact ((isUnit_algebraMap_self A f).map _).mul (isUnit_algebraMap_self _ _)

private theorem isUnit_restrict_algebraMap :
    IsUnit ((restrict (mul_mem_radical f g)).toRingHom (algebraMap A (CompletedAway A f) g)) := by
  rw [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, AlgHom.commutes]
  refine isUnit_of_mul_isUnit_right (x := algebraMap A (CompletedAway A (f * g)) f) ?_
  rw [← map_mul]
  exact isUnit_algebraMap_self A _

/-- The map `A_{f g} → (A_{f})_{g}` induced by the canonical map `A → A_{f} → (A_{f})_{g}`. -/
private noncomputable def toCompletedAway :
    CompletedAway A (f * g) →+*
      CompletedAway (CompletedAway A f) (algebraMap A (CompletedAway A f) g) :=
  lift ((algebraMap (CompletedAway A f) _).comp (algebraMap A (CompletedAway A f)))
    ((continuous_algebraMap _ _).comp (continuous_algebraMap A f))
    (isUnit_algebraMap_comp_algebraMap f g)

/-- The map `(A_{f})_{g} → A_{f g}` induced by the restriction map `A_{f} → A_{f g}`. -/
private noncomputable def ofCompletedAway :
    CompletedAway (CompletedAway A f) (algebraMap A (CompletedAway A f) g) →+*
      CompletedAway A (f * g) :=
  lift (restrict (mul_mem_radical f g)).toRingHom (continuous_restrict (mul_mem_radical f g))
    (isUnit_restrict_algebraMap f g)

private theorem toCompletedAway_algebraMap (a : A) :
    toCompletedAway f g (algebraMap A (CompletedAway A (f * g)) a) =
      algebraMap (CompletedAway A f) _ (algebraMap A (CompletedAway A f) a) := by
  simp [toCompletedAway]

private theorem ofCompletedAway_algebraMap (x : CompletedAway A f) :
    ofCompletedAway f g (algebraMap (CompletedAway A f) _ x) =
      restrict (mul_mem_radical f g) x := by
  simp [ofCompletedAway]

/-- The **completed localisation of a completed localisation**: completing the localisation of
`A_{f}` away from the image of `g` gives the completed localisation `A_{f g}`. The isomorphism is
continuous in both directions and fixes the image of `A`. -/
noncomputable def iterateEquiv :
    CompletedAway (CompletedAway A f) (algebraMap A (CompletedAway A f) g) ≃+*
      CompletedAway A (f * g) :=
  RingEquiv.ofRingHom (ofCompletedAway f g) (toCompletedAway f g)
    (ringHom_ext A (f * g) ((continuous_lift _ _ _).comp (continuous_lift _ _ _)) continuous_id <|
      RingHom.ext fun a ↦ by simp [toCompletedAway_algebraMap, ofCompletedAway_algebraMap])
    -- maps out of `(A_{f})_{g}` are determined on `A_{f}`, and maps out of `A_{f}` on `A`
    (ringHom_ext _ _ ((continuous_lift _ _ _).comp (continuous_lift _ _ _)) continuous_id <|
      ringHom_ext A f ((continuous_lift _ _ _).comp
        ((continuous_lift _ _ _).comp (continuous_algebraMap _ _))) (continuous_algebraMap _ _) <|
        RingHom.ext fun a ↦ by simp [toCompletedAway_algebraMap, ofCompletedAway_algebraMap])

/-- On `A_{f}`, the isomorphism `(A_{f})_{g} ≃ A_{f g}` is the restriction map
`A_{f} → A_{f g}`. -/
theorem iterateEquiv_algebraMap
    (h : f * g ∈ (Ideal.span {f} ⊔ IsAdicRing.ideal A).radical) (x : CompletedAway A f) :
    iterateEquiv f g (algebraMap (CompletedAway A f) _ x) = restrict h x :=
  ofCompletedAway_algebraMap f g x

/-- The inverse of the isomorphism `(A_{f})_{g} ≃ A_{f g}` fixes the image of `A`. -/
@[simp]
theorem iterateEquiv_symm_algebraMap (a : A) :
    (iterateEquiv f g).symm (algebraMap A (CompletedAway A (f * g)) a) =
      algebraMap (CompletedAway A f) _ (algebraMap A (CompletedAway A f) a) :=
  toCompletedAway_algebraMap f g a

/-- The isomorphism `(A_{f})_{g} ≃ A_{f g}` is continuous. -/
theorem continuous_iterateEquiv : Continuous (iterateEquiv f g) :=
  continuous_lift _ _ _

/-- The inverse of the isomorphism `(A_{f})_{g} ≃ A_{f g}` is continuous. -/
theorem continuous_iterateEquiv_symm :
    Continuous (iterateEquiv f g).symm :=
  continuous_lift _ _ _

/-- The isomorphisms `(A_{f})_{g} ≃ A_{f g}` are compatible with the restriction maps: for
`D(f g') ⊆ D(f g)`, restricting from `A_{f g}` to `A_{f g'}` corresponds to restricting from
`(A_{f})_{g}` to `(A_{f})_{g'}`. -/
theorem iterateEquiv_symm_restrict {g' : A}
    (h : f * g' ∈ (Ideal.span {f * g} ⊔ IsAdicRing.ideal A).radical)
    (h' : algebraMap A (CompletedAway A f) g' ∈
      (Ideal.span {algebraMap A (CompletedAway A f) g} ⊔
        IsAdicRing.ideal (CompletedAway A f)).radical)
    (x : CompletedAway A (f * g)) :
    (iterateEquiv f g').symm (restrict h x) =
      restrict h' ((iterateEquiv f g).symm x) := by
  -- both sides are continuous ring homomorphisms out of `A_{f g}` that fix the image of `A`
  have := ringHom_ext A (f * g)
    (g₁ := (iterateEquiv f g').symm.toRingHom.comp (restrict h).toRingHom)
    (g₂ := (restrict h').toRingHom.comp (iterateEquiv f g).symm.toRingHom)
    ((continuous_iterateEquiv_symm f g').comp (continuous_restrict h))
    ((continuous_restrict h').comp (continuous_iterateEquiv_symm f g)) <|
    RingHom.ext fun a ↦ by simp
  exact congr($this x)

end TauCeti.AdicRing.CompletedAway
