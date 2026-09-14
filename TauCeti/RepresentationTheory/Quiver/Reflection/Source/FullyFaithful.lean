/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Quiver.Reflection.Indecomposable
public import TauCeti.RepresentationTheory.Quiver.Reflection.Source.Basic
import Mathlib.CategoryTheory.PathCategory.MorphismProperty
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-!
# Source reflection preserves indecomposability

The Bernstein--Gelfand--Ponomarev reflection `C⁻ᵢ` at a source `i` replaces `Mᵢ` by the
cokernel of the outgoing map

`Mᵢ → ∏_{a : i ⟶ b} M_b`.

This file proves that source reflection is fully faithful on morphisms whose target has injective
outgoing map. Faithfulness follows directly from naturality of the outgoing map. For fullness, a
morphism of reflected representations determines the components away from `i`. Naturality along
the reversed arrows says that their product map carries the range of the outgoing map of the source
into the range for the target. A linear retraction of the target's injective outgoing map then
recovers the missing component at `i`.

The finite-arrow hypothesis is essential to this argument: it lets a vector in the product be
written as the sum of its coordinate vectors, so naturality along each reversed arrow determines
the induced map on the whole quotient. This is automatic for the finite quivers used in Gabriel's
theorem.

As a consequence, source reflection preserves indecomposability whenever the outgoing map is
injective. This is the source-side reverse step needed to reconstruct indecomposables along an
admissible reflection sequence.

## Main results

* `TauCeti.sourceReflectionFunctor_map_injective`,
  `TauCeti.sourceReflectionFunctor_map_surjective`, and
  `TauCeti.sourceReflectionFunctor_map_bijective`: source reflection is fully faithful when the
  outgoing map of the target is injective.
* `TauCeti.nonempty_iso_of_nonempty_iso_sourceReflectRep`: source reflection reflects
  isomorphisms under injectivity of both outgoing maps.
* `TauCeti.indecomposable_sourceReflectRep`: source reflection preserves indecomposability when
  the outgoing map is injective.

## Implementation notes

A vertex `i : Q` is used both as an object of `CategoryTheory.Paths` and as a vertex of
`TauCeti.Quiver.Reflect Q i`, identifications that hold only by unfolding semireducible
definitions, so a goal mentioning both is not type-correct at the transparency `rw` and `simp`
build motives with. Every step that strips a conjugation by `eqToHom` is therefore factored
through the general transport lemmas `TauCeti.eq_of_eqToHom_conjugate` and
`TauCeti.eqToHom_conjugate_vertical_square_of_horizontal_square` of
`TauCeti.CategoryTheory.EqToHom`, which `subst` the object equalities away in an abstract category,
where no such identification is in play.

## References

See Bernstein--Gelfand--Ponomarev, *Coxeter functors and Gabriel's theorem*, and Derksen--Weyman,
*An Introduction to Quiver Representations*, Ch. 2. The formal template is the sink-side argument
in `TauCeti.RepresentationTheory.Quiver.Reflection.FullyFaithful`.
-/

public section

namespace TauCeti

open CategoryTheory
open _root_.TauCeti.Quiver

universe u v w x

variable {k : Type u} {Q : Type v} [Field k] [Quiver.{w} Q]
variable {M N : QuiverRep.{u, v, w, max v w x} k Q} {i : Q}

/-! ### Transport helpers -/

variable (M) in
private theorem sourceReflectObj_self (hi : IsSource i) :
    ((sourceReflectionFunctor i hi).obj M).obj i = ModuleCat.of k
      (((e : Σ b : Q, (i ⟶ b)) → M.obj e.1) ⧸ LinearMap.range (outgoingMap M i)) :=
  (congrArg (fun R : QuiverRep k (Reflect Q i) ↦ R.obj i)
    (sourceReflectionFunctor_obj i hi M)).trans (sourceReflectRep_obj_self M hi)

variable (M) in
private theorem sourceReflectObj_of_ne (hi : IsSource i) {j : Q} (hj : j ≠ i) :
    ((sourceReflectionFunctor i hi).obj M).obj j = M.obj j :=
  (congrArg (fun R : QuiverRep k (Reflect Q i) ↦ R.obj j)
    (sourceReflectionFunctor_obj i hi M)).trans (sourceReflectRep_obj_of_ne M hi hj)

/-! ### Faithfulness -/

/-- **Source reflection is faithful** on morphisms whose target has injective outgoing map. -/
theorem sourceReflectionFunctor_map_injective (hi : IsSource i)
    (hinj : Function.Injective (outgoingMap N i)) :
    Function.Injective fun η : M ⟶ N ↦ (sourceReflectionFunctor i hi).map η := by
  intro η η' h
  have haway : ∀ j : Q, j ≠ i → η.app j = η'.app j := by
    intro j hj
    have h1 := congrArg
      (fun α : (sourceReflectionFunctor i hi).obj M ⟶
          (sourceReflectionFunctor i hi).obj N ↦ α.app j) h
    simp only at h1
    rw [sourceReflectionFunctor_map_app_of_ne η hi hj,
      sourceReflectionFunctor_map_app_of_ne η' hi hj] at h1
    exact eq_of_eqToHom_conjugate _ _ h1
  refine NatTrans.ext (funext fun j ↦ ?_)
  rcases eq_or_ne j i with rfl | hj
  · refine ModuleCat.hom_ext (LinearMap.ext fun y ↦ hinj ?_)
    rw [← outgoingMap_naturality η j y, ← outgoingMap_naturality η' j y]
    exact funext fun e ↦ congrArg
      (fun g : M.obj e.1 ⟶ N.obj e.1 ↦ g (outgoingMap M j y e))
      (haway e.1 (hi.ne_of_hom e.2))
  · exact haway j hj

/-! ### Fullness -/

variable {hi : IsSource i}
  (θ : (sourceReflectionFunctor i hi).obj M ⟶ (sourceReflectionFunctor i hi).obj N)

/-- The component of a reflected morphism away from the source, transported back to the original
vertex spaces. -/
private noncomputable def sourceHomAway {j : Q} (hj : j ≠ i) : M.obj j ⟶ N.obj j :=
  eqToHom (sourceReflectObj_of_ne M hi hj).symm ≫ θ.app j ≫
    eqToHom (sourceReflectObj_of_ne N hi hj)

/-- The component of a reflected morphism at the source, transported to a map of cokernels. -/
private noncomputable def sourceHomQuot :
    (((e : Σ b : Q, (i ⟶ b)) → M.obj e.1) ⧸ LinearMap.range (outgoingMap M i)) →ₗ[k]
      (((e : Σ b : Q, (i ⟶ b)) → N.obj e.1) ⧸ LinearMap.range (outgoingMap N i)) :=
  (eqToHom (sourceReflectObj_self M hi).symm ≫ θ.app i ≫
    eqToHom (sourceReflectObj_self N hi)).hom

/-- `TauCeti.sourceHomQuot` is the underlying linear map of the component of `θ` at the source,
conjugated by the two transports of the vertex spaces there. -/
private theorem sourceHomQuot_apply
    (q : ((e : Σ b : Q, (i ⟶ b)) → M.obj e.1) ⧸ LinearMap.range (outgoingMap M i)) :
    sourceHomQuot θ q =
      (eqToHom (sourceReflectObj_self M hi).symm ≫ θ.app i ≫
        eqToHom (sourceReflectObj_self N hi)).hom q := rfl

variable (M) in
open scoped Classical in
private theorem sourceFunctorObj_map_reflectArrow (hi : IsSource i) {b : Q} (e : i ⟶ b) :
    ((sourceReflectionFunctor i hi).obj M).map (reflectArrowSource i e).toPath =
      eqToHom (sourceReflectObj_of_ne M hi (hi.ne_of_hom e)) ≫
        ModuleCat.ofHom ((LinearMap.range (outgoingMap M i)).mkQ.comp
          (LinearMap.single k (fun e : Σ b : Q, (i ⟶ b) ↦ M.obj e.1) ⟨b, e⟩)) ≫
        eqToHom (sourceReflectObj_self M hi).symm := by
  rw [Functor.congr_hom (sourceReflectionFunctor_obj i hi M) (reflectArrowSource i e).toPath,
    sourceReflectRep_map_reflectArrowSource M hi e]
  simp

variable (M) in
private theorem sourceFunctorObj_map_reflectArrowOfNeOfNe (hi : IsSource i) {a b : Q}
    (ha : a ≠ i) (hb : b ≠ i) (e : a ⟶ b) :
    ((sourceReflectionFunctor i hi).obj M).map (reflectArrowOfNeOfNe ha hb e).toPath =
      eqToHom (sourceReflectObj_of_ne M hi ha) ≫ M.map e.toPath ≫
        eqToHom (sourceReflectObj_of_ne M hi hb).symm := by
  rw [Functor.congr_hom (sourceReflectionFunctor_obj i hi M)
      (reflectArrowOfNeOfNe ha hb e).toPath,
    sourceReflectRep_map_reflectArrowOfNeOfNe M hi ha hb e]
  simp

open scoped Classical in
/-- Naturality along a reversed arrow identifies the corresponding coordinate of the quotient
map. -/
private theorem sourceHomQuot_mk_single {b : Q} (e : i ⟶ b) (y : M.obj b) :
    sourceHomQuot θ
        ((LinearMap.range (outgoingMap M i)).mkQ (Pi.single ⟨b, e⟩ y)) =
      (LinearMap.range (outgoingMap N i)).mkQ
        (Pi.single ⟨b, e⟩ (sourceHomAway θ (hi.ne_of_hom e) y)) := by
  have hnat := θ.naturality (reflectArrowSource i e).toPath
  rw [sourceFunctorObj_map_reflectArrow M hi e,
    sourceFunctorObj_map_reflectArrow N hi e] at hnat
  have hstrip := eqToHom_conjugate_vertical_square_of_horizontal_square
    (sourceReflectObj_of_ne M hi (hi.ne_of_hom e)) (sourceReflectObj_self M hi)
    (sourceReflectObj_self N hi) (sourceReflectObj_of_ne N hi (hi.ne_of_hom e))
    _ _ (θ.app i) (θ.app b) hnat
  exact congrArg
    (fun g : M.obj b ⟶ ModuleCat.of k
        (((e : Σ b : Q, (i ⟶ b)) → N.obj e.1) ⧸ LinearMap.range (outgoingMap N i)) ↦ g y)
    hstrip

/-- The components away from the source, assembled coordinatewise. -/
private noncomputable def sourceHomPi :
    ((e : Σ b : Q, (i ⟶ b)) → M.obj e.1) →ₗ[k]
      ((e : Σ b : Q, (i ⟶ b)) → N.obj e.1) where
  toFun f e := sourceHomAway θ (hi.ne_of_hom e.2) (f e)
  map_add' f g := by ext e; simp
  map_smul' r f := by ext e; simp

private theorem sourceHomPi_apply (f : (e : Σ b : Q, (i ⟶ b)) → M.obj e.1)
    (e : Σ b : Q, (i ⟶ b)) :
    sourceHomPi θ f e = sourceHomAway θ (hi.ne_of_hom e.2) (f e) := rfl

/-- Naturality on the reversed arrows determines the map on every quotient class. -/
private theorem sourceHomQuot_mk [Finite (Σ b : Q, (i ⟶ b))]
    (f : (e : Σ b : Q, (i ⟶ b)) → M.obj e.1) :
    sourceHomQuot θ ((LinearMap.range (outgoingMap M i)).mkQ f) =
      (LinearMap.range (outgoingMap N i)).mkQ (sourceHomPi θ f) := by
  classical
  let _ : Fintype (Σ b : Q, (i ⟶ b)) := Fintype.ofFinite (Σ b : Q, (i ⟶ b))
  have hsumM : ∑ e, Pi.single e (f e) = f := by
    funext e
    simpa only [Finset.sum_apply] using Fintype.sum_pi_single e f
  have hsumN : ∑ e, Pi.single e (sourceHomPi θ f e) = sourceHomPi θ f := by
    funext e
    simpa only [Finset.sum_apply] using Fintype.sum_pi_single e (sourceHomPi θ f)
  conv_lhs => rw [← hsumM]
  conv_rhs => rw [← hsumN]
  simp only [map_sum]
  apply Finset.sum_congr rfl
  intro e _
  rw [sourceHomQuot_mk_single θ e.2 (f e)]
  congr 2

/-- A linear retraction of an injective outgoing map. -/
private noncomputable def sourceRetraction (_hinj : Function.Injective (outgoingMap N i)) :
    ((e : Σ b : Q, (i ⟶ b)) → N.obj e.1) →ₗ[k] N.obj i :=
  (outgoingMap N i).leftInverse

private theorem sourceRetraction_outgoingMap (hinj : Function.Injective (outgoingMap N i))
    (y : N.obj i) : sourceRetraction hinj (outgoingMap N i y) = y :=
  LinearMap.leftInverse_apply_of_inj (LinearMap.ker_eq_bot.mpr hinj) y

/-- The missing component at the source, recovered by retracting the coordinatewise map into the
injective outgoing map of the target. -/
private noncomputable def sourceHomSource (hinj : Function.Injective (outgoingMap N i)) :
    M.obj i →ₗ[k] N.obj i :=
  (sourceRetraction hinj).comp ((sourceHomPi θ).comp (outgoingMap M i))

/-- The recovered source component makes the square of outgoing maps commute. -/
private theorem outgoingMap_sourceHomSource [Finite (Σ b : Q, (i ⟶ b))]
    (hinj : Function.Injective (outgoingMap N i))
    (y : M.obj i) :
    outgoingMap N i (sourceHomSource θ hinj y) = sourceHomPi θ (outgoingMap M i y) := by
  have hq : (LinearMap.range (outgoingMap N i)).mkQ
      (sourceHomPi θ (outgoingMap M i y)) = 0 := by
    rw [← sourceHomQuot_mk θ]
    rw [Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero _).mpr
      (LinearMap.mem_range_self (outgoingMap M i) y), map_zero]
  obtain ⟨z, hz⟩ := (Submodule.Quotient.mk_eq_zero _).mp (by
    simpa only [Submodule.mkQ_apply] using hq)
  have hsource : sourceHomSource θ hinj y = z := by
    rw [sourceHomSource, LinearMap.comp_apply, LinearMap.comp_apply, ← hz,
      sourceRetraction_outgoingMap hinj]
  rw [hsource, hz]

open scoped Classical in
private noncomputable def sourceHomPreimageApp
    (hinj : Function.Injective (outgoingMap N i)) (j : Q) : M.obj j ⟶ N.obj j :=
  if hj : j = i then
    eqToHom (by rw [hj]) ≫ ModuleCat.ofHom (sourceHomSource θ hinj) ≫ eqToHom (by rw [hj])
  else sourceHomAway θ hj

private theorem sourceHomPreimageApp_self (hinj : Function.Injective (outgoingMap N i)) :
    sourceHomPreimageApp θ hinj i = ModuleCat.ofHom (sourceHomSource θ hinj) := by
  classical
  simp [sourceHomPreimageApp]

private theorem sourceHomPreimageApp_of_ne (hinj : Function.Injective (outgoingMap N i))
    {j : Q} (hj : j ≠ i) : sourceHomPreimageApp θ hinj j = sourceHomAway θ hj := by
  classical
  simp [sourceHomPreimageApp, hj]

/-- Every coordinate of the outgoing product is indexed by an arrow out of the source, so on that
product the reconstructed morphism acts coordinatewise as `TauCeti.sourceHomPi`. -/
private theorem sourceHomPreimageApp_coord (hinj : Function.Injective (outgoingMap N i))
    (f : (e : Σ b : Q, (i ⟶ b)) → M.obj e.1) :
    (fun e ↦ sourceHomPreimageApp θ hinj e.1 (f e)) = sourceHomPi θ f :=
  funext fun e ↦ by
    rw [sourceHomPreimageApp_of_ne θ hinj (hi.ne_of_hom e.2), sourceHomPi_apply]

private theorem sourceHomPreimageApp_naturality
    [Finite (Σ b : Q, (i ⟶ b))] (hinj : Function.Injective (outgoingMap N i))
    {a b : Q} (e : a ⟶ b) :
    M.map e.toPath ≫ sourceHomPreimageApp θ hinj b =
      sourceHomPreimageApp θ hinj a ≫ N.map e.toPath := by
  rcases eq_or_ne a i with rfl | ha
  · rw [sourceHomPreimageApp_self, sourceHomPreimageApp_of_ne θ hinj (hi.ne_of_hom e)]
    refine ModuleCat.hom_ext (LinearMap.ext fun y ↦ ?_)
    have hcoord := congrFun (outgoingMap_sourceHomSource θ hinj y) ⟨b, e⟩
    simpa [outgoingMap_apply, sourceHomPi_apply] using hcoord.symm
  · rw [sourceHomPreimageApp_of_ne θ hinj ha]
    rcases eq_or_ne b i with rfl | hb
    · exact (hi.isEmpty_hom a).elim e
    · rw [sourceHomPreimageApp_of_ne θ hinj hb]
      have hnat := θ.naturality (reflectArrowOfNeOfNe ha hb e).toPath
      rw [sourceFunctorObj_map_reflectArrowOfNeOfNe M hi ha hb e,
        sourceFunctorObj_map_reflectArrowOfNeOfNe N hi ha hb e] at hnat
      exact eqToHom_conjugate_vertical_square_of_horizontal_square
        (sourceReflectObj_of_ne M hi ha)
        (sourceReflectObj_of_ne M hi hb) (sourceReflectObj_of_ne N hi hb)
        (sourceReflectObj_of_ne N hi ha) _ _ (θ.app b) (θ.app a) hnat

private noncomputable def sourceHomPreimage [Finite (Σ b : Q, (i ⟶ b))]
    (hinj : Function.Injective (outgoingMap N i)) : M ⟶ N :=
  Paths.liftNatTrans (sourceHomPreimageApp θ hinj)
    fun e ↦ sourceHomPreimageApp_naturality θ hinj e

private theorem sourceHomPreimage_app [Finite (Σ b : Q, (i ⟶ b))]
    (hinj : Function.Injective (outgoingMap N i)) (j : Q) :
    (sourceHomPreimage (θ := θ) hinj).app j = sourceHomPreimageApp θ hinj j := rfl

private theorem sourceReflectionFunctor_map_sourceHomPreimage
    [Finite (Σ b : Q, (i ⟶ b))] (hinj : Function.Injective (outgoingMap N i)) :
    (sourceReflectionFunctor i hi).map (sourceHomPreimage (θ := θ) hinj) = θ := by
  refine NatTrans.ext (funext fun j ↦ ?_)
  by_cases hj : j = i
  · subst j
    refine eq_of_eqToHom_conjugate (sourceReflectObj_self M hi).symm
      (sourceReflectObj_self N hi) ?_
    refine ModuleCat.hom_ext (LinearMap.ext fun q ↦ ?_)
    rw [← sourceHomQuot_apply θ q]
    induction q using Submodule.Quotient.induction_on with
    | _ f =>
      simp only [ModuleCat.hom_comp, LinearMap.comp_apply]
      rw [sourceReflectionFunctor_map_app_self_mk (sourceHomPreimage (θ := θ) hinj) hi f]
      simp only [sourceHomPreimage_app]
      rw [sourceHomPreimageApp_coord θ hinj f,
        ← Submodule.mkQ_apply (LinearMap.range (outgoingMap M i)) f, sourceHomQuot_mk θ f]
  · have happ : (sourceHomPreimage (θ := θ) hinj).app j =
        eqToHom (sourceReflectObj_of_ne M hi hj).symm ≫ θ.app j ≫
          eqToHom (sourceReflectObj_of_ne N hi hj) :=
      (sourceHomPreimage_app (θ := θ) hinj j).trans (sourceHomPreimageApp_of_ne θ hinj hj)
    refine (sourceReflectionFunctor_map_app_of_ne (sourceHomPreimage (θ := θ) hinj) hi hj).trans ?_
    exact (congrArg
      (fun g : M.obj j ⟶ N.obj j ↦ eqToHom (sourceReflectObj_of_ne M hi hj) ≫ g ≫
        eqToHom (sourceReflectObj_of_ne N hi hj).symm) happ).trans
      (eqToHom_conjugate_cancel (sourceReflectObj_of_ne M hi hj).symm
        (sourceReflectObj_of_ne N hi hj).symm (θ.app j))

/-! ### Full faithfulness and indecomposability -/

variable (hi)

/-- **Source reflection is full** on morphisms whose target has injective outgoing map. -/
theorem sourceReflectionFunctor_map_surjective [Finite (Σ b : Q, (i ⟶ b))]
    (hinj : Function.Injective (outgoingMap N i)) :
    Function.Surjective fun η : M ⟶ N ↦ (sourceReflectionFunctor i hi).map η :=
  fun θ ↦ ⟨sourceHomPreimage (θ := θ) hinj,
    sourceReflectionFunctor_map_sourceHomPreimage θ hinj⟩

/-- **Source reflection is fully faithful** on morphisms whose target has injective outgoing
map. -/
theorem sourceReflectionFunctor_map_bijective [Finite (Σ b : Q, (i ⟶ b))]
    (hinj : Function.Injective (outgoingMap N i)) :
    Function.Bijective fun η : M ⟶ N ↦ (sourceReflectionFunctor i hi).map η :=
  ⟨sourceReflectionFunctor_map_injective hi hinj,
    sourceReflectionFunctor_map_surjective hi hinj⟩

/-- **Source reflection reflects isomorphisms** when both outgoing maps are injective. -/
theorem nonempty_iso_of_nonempty_iso_sourceReflectRep
    [Finite (Σ b : Q, (i ⟶ b))]
    (hinjM : Function.Injective (outgoingMap M i))
    (hinjN : Function.Injective (outgoingMap N i))
    (h : Nonempty (sourceReflectRep M hi ≅ sourceReflectRep N hi)) : Nonempty (M ≅ N) := by
  obtain ⟨θ⟩ := h
  have θ' : (sourceReflectionFunctor i hi).obj M ≅ (sourceReflectionFunctor i hi).obj N :=
    eqToIso (sourceReflectionFunctor_obj i hi M) ≪≫ θ ≪≫
      eqToIso (sourceReflectionFunctor_obj i hi N).symm
  obtain ⟨f, hf⟩ := sourceReflectionFunctor_map_surjective (M := M) (N := N) hi hinjN θ'.hom
  obtain ⟨g, hg⟩ := sourceReflectionFunctor_map_surjective (M := N) (N := M) hi hinjM θ'.inv
  refine ⟨⟨f, g, ?_, ?_⟩⟩
  · refine sourceReflectionFunctor_map_injective (M := M) (N := M) hi hinjM ?_
    simp only [Functor.map_comp, hf, hg]
    exact θ'.hom_inv_id.trans ((sourceReflectionFunctor i hi).map_id M).symm
  · refine sourceReflectionFunctor_map_injective (M := N) (N := N) hi hinjN ?_
    simp only [Functor.map_comp, hf, hg]
    exact θ'.inv_hom_id.trans ((sourceReflectionFunctor i hi).map_id N).symm

/-- **Reflection at a source preserves indecomposability** when the outgoing map is injective. -/
theorem indecomposable_sourceReflectRep [Finite (Σ b : Q, (i ⟶ b))]
    (hM : Indecomposable M)
    (hinj : Function.Injective (outgoingMap M i)) : Indecomposable (sourceReflectRep M hi) := by
  have hbij := sourceReflectionFunctor_map_bijective (M := M) (N := M) hi hinj
  have hzero : (sourceReflectionFunctor i hi).map (0 : M ⟶ M) = 0 :=
    CategoryTheory.Functor.map_zero (sourceReflectionFunctor i hi) M M
  refine sourceReflectionFunctor_obj i hi M ▸ indecomposable_of_idempotent_eq_zero_or_id ?_ ?_
  · intro h0
    have h1 : (sourceReflectionFunctor i hi).map (𝟙 M) =
        (sourceReflectionFunctor i hi).map (0 : M ⟶ M) :=
      ((sourceReflectionFunctor i hi).map_id M).trans
        (((Limits.IsZero.iff_id_eq_zero _).mp h0).trans hzero.symm)
    exact hM.1 ((Limits.IsZero.iff_id_eq_zero M).mpr (hbij.1 h1))
  · intro e he
    obtain ⟨η, rfl⟩ := hbij.2 e
    have hidem : η ≫ η = η := hbij.1 (((sourceReflectionFunctor i hi).map_comp η η).trans he)
    rcases idempotent_eq_zero_or_id_of_indecomposable hM hidem with h | h
    · exact Or.inl (by rw [h]; exact hzero)
    · exact Or.inr (by rw [h]; exact (sourceReflectionFunctor i hi).map_id M)

end TauCeti
