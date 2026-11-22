/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.Category.Idempotent
public import TauCeti.CategoryTheory.Dagger.Karoubi
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute

/-!
# The dagger Karoubi envelope of a C*-category

The dagger Karoubi envelope `TauCeti.DaggerKaroubi C` of a C*-category `C`, whose objects are
pairs `(X, p)` of an object and a self-adjoint idempotent, is again a C*-category. A morphism
`(X, p) ⟶ (Y, q)` is an arrow `f : X ⟶ Y` with `p ≫ f ≫ q = f`, and its norm is the norm of `f`.
These arrows form a closed subspace of the Hom space of `C`, and for such `f` the positive
endomorphism `f†f` of `X` commutes with `p`, so its square root does too and lies in the corner
of `End X` cut out by `p`.

In a C*-category every idempotent `e` is isomorphic in `Karoubi C` to its range projection `p`:
the arrows `e` and `p` are mutually inverse isomorphisms `(X, e) ≅ (X, p)`. Hence the inclusion of
`DaggerKaroubi C` into the idempotent completion `Karoubi C` is an equivalence of categories, and
`DaggerKaroubi C` is idempotent complete. The embedding `TauCeti.toDaggerKaroubi C` is an
equivalence exactly when `C` is idempotent complete, and then every object of the envelope is
unitarily isomorphic to an object of `C`.

## Main declarations

* `TauCeti.DaggerKaroubi.instCStarCategory`: the dagger Karoubi envelope of a C*-category is a
  C*-category, with the norms of the underlying arrows.
* `TauCeti.CStarCategory.karoubiIsoRangeProjection`: an object `(X, e)` of `Karoubi C` is
  isomorphic to `(X, p)` for the range projection `p` of `e`.
* `TauCeti.CStarCategory.daggerKaroubiEquivalence`: the equivalence `DaggerKaroubi C ≌ Karoubi C`
  given by the inclusion.
* `TauCeti.CStarCategory.exists_isUnitary_toDaggerKaroubi_obj`: in an idempotent complete
  C*-category, every object of the envelope is unitarily isomorphic to an object of `C`.
* `TauCeti.CStarCategory.isEquivalence_toDaggerKaroubi_iff`: the embedding `toDaggerKaroubi C`
  is an equivalence exactly when `C` is idempotent complete.

## References

* P. Ghez, R. Lima, J. E. Roberts, *W*-categories*, Pacific J. Math. 120 (1985), 79–109.
* P. Selinger, *Idempotents in dagger categories*, Electron. Notes Theor. Comput. Sci. 210
  (2008), 107–122.
-/

public section

noncomputable section

open CategoryTheory Idempotents

universe v u

namespace TauCeti.DaggerKaroubi

variable {C : Type u} [Category.{v} C] [DaggerCategory C]

section Norm

variable [∀ X Y : C, Norm (X ⟶ Y)]

/-- A morphism of the dagger Karoubi envelope has the norm of its underlying arrow. -/
instance instNorm (P Q : DaggerKaroubi C) : Norm (P ⟶ Q) where
  norm f := ‖f.hom.f‖

/-- The norm of a morphism of the dagger Karoubi envelope is the norm of its underlying arrow. -/
theorem norm_def {P Q : DaggerKaroubi C} (f : P ⟶ Q) : ‖f‖ = ‖f.hom.f‖ := (rfl)

end Norm

variable [Preadditive C] [Linear ℂ C] [DaggerPreadditive C] [DaggerLinear ℂ C]
  [∀ X Y : C, Norm (X ⟶ Y)] [CStarCategory C]

/-- The normed space axioms for the Hom spaces of the dagger Karoubi envelope, transported from
those of `C`. -/
theorem normedSpaceCore (P Q : DaggerKaroubi C) : NormedSpace.Core ℂ (P ⟶ Q) where
  norm_nonneg f := CStarCategory.norm_nonneg f.hom.f
  norm_smul c f := CStarCategory.norm_smul c f.hom.f
  norm_triangle f g := CStarCategory.norm_add_le f.hom.f g.hom.f
  norm_eq_zero_iff f := by
    rw [norm_def, CStarCategory.norm_eq_zero]
    exact ⟨fun h => hom_ext h, fun h => by rw [h, zero_hom_f]⟩

/-- The Hom spaces of the dagger Karoubi envelope are complete: they are isometric to the closed
subspaces of arrows `f` of `C` with `p ≫ f ≫ q = f`. -/
private theorem completeSpace (P Q : DaggerKaroubi C) :
    letI := NormedAddCommGroup.ofCore (normedSpaceCore P Q)
    CompleteSpace (P ⟶ Q) := by
  let := NormedAddCommGroup.ofCore (normedSpaceCore P Q)
  let := CStarCategory.normedAddCommGroup P.obj.X Q.obj.X
  have : CompleteSpace (P.obj.X ⟶ Q.obj.X) := CStarCategory.completeSpace _ _
  -- The underlying arrows are the fixed points of the bounded map `g ↦ p ≫ g ≫ q`.
  let φ : (P.obj.X ⟶ Q.obj.X) →+ (P.obj.X ⟶ Q.obj.X) :=
    (Preadditive.leftComp _ P.obj.p).comp (Preadditive.rightComp _ Q.obj.p)
  have hφ : Continuous φ :=
    AddMonoidHomClass.continuous_of_bound φ (‖P.obj.p‖ * ‖Q.obj.p‖) fun g =>
      calc ‖P.obj.p ≫ g ≫ Q.obj.p‖ ≤ ‖P.obj.p‖ * (‖g‖ * ‖Q.obj.p‖) :=
            (CStarCategory.norm_comp_le _ _).trans <| mul_le_mul_of_nonneg_left
              (CStarCategory.norm_comp_le _ _) (CStarCategory.norm_nonneg _)
        _ = ‖P.obj.p‖ * ‖Q.obj.p‖ * ‖g‖ := by ring
  let ι : (P ⟶ Q) →+ (P.obj.X ⟶ Q.obj.X) := AddMonoidHom.mk' (fun f => f.hom.f) fun _ _ => rfl
  have hι : Isometry ι := AddMonoidHomClass.isometry_of_norm ι fun _ => rfl
  have hrange : Set.range ι = {g | φ g = g} := by
    ext g
    refine ⟨?_, fun hg => ⟨ObjectProperty.homMk ⟨g, hg⟩, rfl⟩⟩
    rintro ⟨f, rfl⟩
    exact f.hom.comm
  rw [completeSpace_iff_isComplete_range hι.isUniformInducing, hrange]
  exact (isClosed_eq hφ continuous_id).isComplete

/-- Positivity of `f†f` in the dagger Karoubi envelope. For `f : (X, p) ⟶ (Y, q)` the positive
endomorphism `a = f ≫ dagger f` of `X` commutes with `p`, hence so does its square root `s`, and
`g = s ≫ p` is an endomorphism of `(X, p)` with `g ≫ dagger g = a`. -/
private theorem exists_self_comp_dagger_eq {P Q : DaggerKaroubi C} (f : P ⟶ Q) :
    ∃ g : P ⟶ P, f ≫ dagger f = g ≫ dagger g := by
  obtain ⟨a, ha⟩ : ∃ a : End P.obj.X, a = End.of (f.hom.f ≫ dagger f.hom.f) := ⟨_, rfl⟩
  obtain ⟨p, hp⟩ : ∃ p : End P.obj.X, p = End.of P.obj.p := ⟨_, rfl⟩
  have hpf : P.obj.p ≫ f.hom.f = f.hom.f := Karoubi.p_comp f.hom
  have hfp : dagger f.hom.f ≫ P.obj.p = dagger f.hom.f := by
    rw [← P.dagger_p, ← dagger_comp, hpf]
  have hpa : p * a = a := by
    ext
    simp [hp, ha, hfp]
  have hap : a * p = a := by
    ext
    simp [hp, ha, reassoc_of% hpf]
  have hpp : p * p = p := by
    ext
    simp [hp]
  have hps : IsSelfAdjoint p := End.ext (by simp [hp])
  have hs : Commute (CFC.sqrt a) p := Commute.cfcₙ_nnreal (hap.trans hpa.symm) _
  have hss : star (CFC.sqrt a) = CFC.sqrt a := (CFC.sqrt_nonneg a).isSelfAdjoint.star_eq
  have hsa : CFC.sqrt a * CFC.sqrt a = a := CFC.sqrt_mul_sqrt_self a <| by
    rw [ha]
    exact End.self_comp_dagger_nonneg _
  -- The endomorphism `g = s * p` of `End X` lies in the corner `p * End X * p`.
  have hg : p * (CFC.sqrt a * p) * p = CFC.sqrt a * p := by
    simp only [mul_assoc, hpp]
    rw [← mul_assoc, ← hs.eq, mul_assoc, hpp]
  have hgg : star (CFC.sqrt a * p) * (CFC.sqrt a * p) = a := by
    rw [star_mul, hss, hps.star_eq, mul_assoc, ← mul_assoc (CFC.sqrt a), hsa, ← mul_assoc, hpa,
      hap]
  refine ⟨ObjectProperty.homMk ⟨(CFC.sqrt a * p).asHom, ?_⟩, ?_⟩
  · simpa only [End.mul_asHom, hp, Category.assoc] using congrArg End.asHom hg
  · ext
    simpa only [ha, End.mul_asHom, End.star_asHom, comp_hom_f, dagger_hom_f,
      ObjectProperty.homMk_hom] using
      congrArg End.asHom hgg.symm

/-- The dagger Karoubi envelope of a C*-category is a C*-category, with the norms of the
underlying arrows. -/
instance instCStarCategory : CStarCategory (DaggerKaroubi C) where
  normedSpaceCore := normedSpaceCore
  completeSpace := completeSpace
  norm_comp_le f g := CStarCategory.norm_comp_le f.hom.f g.hom.f
  norm_mul_self_le f := CStarCategory.norm_mul_self_le f.hom.f
  exists_self_comp_dagger_eq := exists_self_comp_dagger_eq

end TauCeti.DaggerKaroubi

namespace TauCeti.CStarCategory

variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℂ C]
  [DaggerCategory C] [DaggerPreadditive C] [DaggerLinear ℂ C]
  [∀ X Y : C, Norm (X ⟶ Y)] [CStarCategory C]

/-- In a C*-category, an object `(X, e)` of `Karoubi C` is isomorphic to `(X, p)` for the range
projection `p` of `e`: the arrows `e` and `p` are mutually inverse morphisms. -/
def karoubiIsoRangeProjection (P : Karoubi C) :
    P ≅ ⟨P.X, idempotentRangeProjection P.p, idempotentRangeProjection_comp_self P.idem⟩ where
  hom := ⟨P.p, by simp [comp_idempotentRangeProjection P.idem]⟩
  inv := ⟨idempotentRangeProjection P.p, by simp [idempotentRangeProjection_comp P.idem]⟩
  hom_inv_id := by
    ext
    exact comp_idempotentRangeProjection P.idem
  inv_hom_id := by
    ext
    exact idempotentRangeProjection_comp P.idem

/-- The isomorphism `(X, e) ≅ (X, p)` has underlying arrow `e`. -/
@[simp] theorem karoubiIsoRangeProjection_hom_f (P : Karoubi C) :
    (karoubiIsoRangeProjection P).hom.f = P.p := (rfl)

/-- The inverse isomorphism `(X, p) ≅ (X, e)` has underlying arrow `p`. -/
@[simp] theorem karoubiIsoRangeProjection_inv_f (P : Karoubi C) :
    (karoubiIsoRangeProjection P).inv.f = idempotentRangeProjection P.p := (rfl)

/-- In a C*-category, every object of `Karoubi C` is isomorphic to one with a self-adjoint
idempotent. -/
instance : (isSelfAdjointKaroubi C).ι.EssSurj where
  mem_essImage P :=
    ⟨⟨⟨P.X, idempotentRangeProjection P.p, idempotentRangeProjection_comp_self P.idem⟩,
      dagger_idempotentRangeProjection P.idem⟩, ⟨(karoubiIsoRangeProjection P).symm⟩⟩

/-- In a C*-category, the inclusion of the dagger Karoubi envelope into `Karoubi C` is an
equivalence. -/
instance : (isSelfAdjointKaroubi C).ι.IsEquivalence where

variable (C) in
/-- The dagger Karoubi envelope of a C*-category is equivalent to its idempotent completion
`Karoubi C`, through the inclusion. -/
def daggerKaroubiEquivalence : DaggerKaroubi C ≌ Karoubi C :=
  (isSelfAdjointKaroubi C).ι.asEquivalence

/-- The functor of `daggerKaroubiEquivalence C` is the inclusion. -/
@[simp] theorem daggerKaroubiEquivalence_functor :
    (daggerKaroubiEquivalence C).functor = (isSelfAdjointKaroubi C).ι := (rfl)

/-- The dagger Karoubi envelope of a C*-category is idempotent complete. -/
instance : IsIdempotentComplete (DaggerKaroubi C) :=
  (isIdempotentComplete_iff_of_equivalence (daggerKaroubiEquivalence C)).2 inferInstance

/-- In an idempotent complete C*-category, every object of the dagger Karoubi envelope is unitarily
isomorphic to the image of an object of `C`. -/
theorem exists_isUnitary_toDaggerKaroubi_obj [IsIdempotentComplete C] (P : DaggerKaroubi C) :
    ∃ (Y : C) (u : (toDaggerKaroubi C).obj Y ⟶ P), IsUnitary u :=
  exists_isUnitary_toDaggerKaroubi_obj_iff.2 (isIdempotentComplete_iff.1 ‹_›) P

/-- The embedding of an idempotent complete C*-category into its dagger Karoubi envelope is
essentially surjective. -/
instance [IsIdempotentComplete C] : (toDaggerKaroubi C).EssSurj where
  mem_essImage P :=
    have ⟨Y, _, hu⟩ := exists_isUnitary_toDaggerKaroubi_obj P
    ⟨Y, ⟨hu.toIso⟩⟩

/-- The embedding of an idempotent complete C*-category into its dagger Karoubi envelope is an
equivalence. -/
instance [IsIdempotentComplete C] : (toDaggerKaroubi C).IsEquivalence where

variable (C) in
/-- The embedding of a C*-category into its dagger Karoubi envelope is an equivalence exactly when
the C*-category is idempotent complete. -/
theorem isEquivalence_toDaggerKaroubi_iff :
    (toDaggerKaroubi C).IsEquivalence ↔ IsIdempotentComplete C :=
  ⟨fun _ => (isIdempotentComplete_iff_of_equivalence (toDaggerKaroubi C).asEquivalence).2
    inferInstance, fun _ => inferInstance⟩

end TauCeti.CStarCategory
