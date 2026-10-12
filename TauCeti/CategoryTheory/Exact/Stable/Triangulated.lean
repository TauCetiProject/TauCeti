/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Exact.BaseChange
public import TauCeti.CategoryTheory.Exact.Stable.Pretriangulated
public import Mathlib.CategoryTheory.Triangulated.Triangulated

/-!
# The stable category of a Frobenius exact category is triangulated

Let `E` be a Frobenius exact structure. Its projective stable category is pretriangulated, with
the triangles isomorphic to standard triangles `X ⟶ Y ⟶ Z ⟶ X⟦1⟧` of conflations. This file
proves the octahedral axiom, completing Happel's theorem that the stable category is
triangulated.

The octahedron comes from Noether's isomorphism in the exact category. Given conflations
`X₁ ⟶ X₂ ⟶ Z₁₂` and `X₂ ⟶ X₃ ⟶ Z₂₃`, the composite `X₁ ⟶ X₃` is the inflation of a conflation
`X₁ ⟶ X₃ ⟶ Z₁₃`, and the induced maps form a conflation `Z₁₂ ⟶ Z₁₃ ⟶ Z₂₃`
(`TauCeti.ExactStructure.exists_conflation_comp`). The standard triangles of these four
conflations form an octahedron: its commutativity conditions are the naturality of connecting
morphisms along the three evident morphisms of conflations. Every composable pair of stable
morphisms is isomorphic to the image of a composable pair of inflations, by replacing a morphism
`f : X ⟶ Y` with the inflation `X ⟶ I(X) ⊞ Y` of its cone conflation; since the octahedral axiom
is invariant under isomorphism of the diagram, this proves it in general.

As with the pretriangulated structure, the Frobenius hypothesis `hE` is a proposition, so the
result is a theorem rather than an instance.

## Main definitions

* `TauCeti.ExactStructure.IsFrobenius.stableConflationOctahedron`: the octahedron formed by the
  standard triangles of two composable conflations, their composite, and the Noether
  conflation.

## Main results

* `TauCeti.ExactStructure.IsFrobenius.mk_distinguished_of_conflation`: the standard triangle
  of a conflation, written with its three arrows, is distinguished.
* `TauCeti.ExactStructure.IsFrobenius.stableIsTriangulated`: **Happel's theorem**, the stable
  category of a Frobenius exact category is triangulated.

## References

* Dieter Happel, *Triangulated Categories in the Representation Theory of Finite Dimensional
  Algebras*, Chapter I, Section 2, Theorem 2.6.
* Theo Bühler, *Exact Categories*, Expositiones Mathematicae **28** (2010), 1–69, Lemma 3.5.
-/

public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace TauCeti.ExactStructure.IsFrobenius

universe v u

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]
  [HasBinaryBiproducts C] {E : ExactStructure C} (hE : E.IsFrobenius)

/-- The standard triangle `X ⟶ Y ⟶ Z ⟶ X⟦1⟧` of a conflation `X ⟶ Y ⟶ Z`, written with its three
arrows, is a distinguished stable triangle. The first arrow may be given by any expression equal
to the image of the inflation. -/
theorem mk_distinguished_of_conflation {X Y Z : C} {f : X ⟶ Y} {g : Y ⟶ Z} {w : f ≫ g = 0}
    (hS : E.Conflation (ShortComplex.mk f g w))
    {u : E.projectiveStableFunctor.obj X ⟶ E.projectiveStableFunctor.obj Y}
    (hu : E.projectiveStableFunctor.map f = u) :
    letI := hE.stableHasShift
    letI : ∀ n : ℤ, (shiftFunctor E.ProjectiveStableCategory n).Additive :=
      hE.stableShiftFunctor_additive
    letI := hE.stablePretriangulated
    Triangle.mk u (E.projectiveStableFunctor.map g)
        (E.projectiveStableFunctor.map (hE.connectingMap hS) ≫
          (hE.stableSuspensionObjIsoShift X).hom) ∈ distTriang E.ProjectiveStableCategory := by
  subst hu
  have h := hE.stableConflationTriangle_mem _ hS
  rw [stableConflationTriangle_eq_mk] at h
  simpa only [stablePretriangulated_distinguishedTriangles, stableSuspensionObjIsoShift_hom]
    using h

section Octahedron

variable {X₁ X₂ X₃ Z₁₂ Z₂₃ Z₁₃ : C} {i : X₁ ⟶ X₂} {p : X₂ ⟶ Z₁₂} {hip : i ≫ p = 0}
  {j : X₂ ⟶ X₃} {v : X₃ ⟶ Z₂₃} {hjv : j ≫ v = 0} {c : X₃ ⟶ Z₁₃} {hc : (i ≫ j) ≫ c = 0}
  {α : Z₁₂ ⟶ Z₁₃} {β : Z₁₃ ⟶ Z₂₃} {hαβ : α ≫ β = 0}
  (h₁₂ : E.Conflation (ShortComplex.mk i p hip)) (h₂₃ : E.Conflation (ShortComplex.mk j v hjv))
  (h₁₃ : E.Conflation (ShortComplex.mk (i ≫ j) c hc))
  (hN : E.Conflation (ShortComplex.mk α β hαβ))

/-- **Happel's octahedron.** For conflations `X₁ ⟶ X₂ ⟶ Z₁₂`, `X₂ ⟶ X₃ ⟶ Z₂₃` and
`X₁ ⟶ X₃ ⟶ Z₁₃` on a composable pair of inflations and its composite, a conflation
`Z₁₂ ⟶ Z₁₃ ⟶ Z₂₃` compatible with the three deflations makes their standard triangles an
octahedron, whose two new arrows are the images of the maps of the fourth conflation. Such a
fourth conflation always exists, by `TauCeti.ExactStructure.exists_conflation_comp`. -/
noncomputable def stableConflationOctahedron (hjc : j ≫ c = p ≫ α) (hcβ : c ≫ β = v) :
    letI := hE.stableHasShift
    letI : ∀ n : ℤ, (shiftFunctor E.ProjectiveStableCategory n).Additive :=
      hE.stableShiftFunctor_additive
    letI := hE.stablePretriangulated
    Triangulated.Octahedron rfl (hE.mk_distinguished_of_conflation h₁₂ rfl)
      (hE.mk_distinguished_of_conflation h₂₃ rfl)
      (hE.mk_distinguished_of_conflation h₁₃ (E.projectiveStableFunctor.map_comp i j)) := by
  letI := hE.stableHasShift
  letI : ∀ n : ℤ, (shiftFunctor E.ProjectiveStableCategory n).Additive :=
    hE.stableShiftFunctor_additive
  letI := hE.stablePretriangulated
  -- The three morphisms of conflations whose connecting squares are the octahedron's
  -- commutativity conditions.
  let φ₁ : ShortComplex.mk i p hip ⟶ ShortComplex.mk (i ≫ j) c hc :=
    { τ₁ := 𝟙 _, τ₂ := j, τ₃ := α, comm₂₃ := hjc }
  let φ₂ : ShortComplex.mk (i ≫ j) c hc ⟶ ShortComplex.mk j v hjv :=
    { τ₁ := i, τ₂ := 𝟙 _, τ₃ := β, comm₂₃ := by simpa using hcβ.symm }
  let φ₃ : ShortComplex.mk j v hjv ⟶ ShortComplex.mk α β hαβ :=
    { τ₁ := p, τ₂ := c, τ₃ := 𝟙 _, comm₁₂ := hjc.symm, comm₂₃ := by simpa using hcβ }
  have n₁ : E.projectiveStableFunctor.map α ≫
      E.projectiveStableFunctor.map (hE.connectingMap h₁₃) =
        E.projectiveStableFunctor.map (hE.connectingMap h₁₂) := by
    simpa [φ₁, E.projectiveStableFunctor_map_cokernelMap_id _
      (hE.isProjective_I (hE.suspensionPresentation X₁))] using
      hE.projectiveStableFunctor_map_connectingMap_naturality h₁₂ h₁₃ φ₁
  have n₂ : E.projectiveStableFunctor.map β ≫
      E.projectiveStableFunctor.map (hE.connectingMap h₂₃) =
        E.projectiveStableFunctor.map (hE.connectingMap h₁₃) ≫
          E.projectiveStableFunctor.map
            ((hE.suspensionPresentation X₁).cokernelMap (hE.suspensionPresentation X₂) i) := by
    simpa [φ₂] using hE.projectiveStableFunctor_map_connectingMap_naturality h₁₃ h₂₃ φ₂
  have n₃ : E.projectiveStableFunctor.map (hE.connectingMap hN) =
      E.projectiveStableFunctor.map (hE.connectingMap h₂₃) ≫
        E.projectiveStableFunctor.map
          ((hE.suspensionPresentation X₂).cokernelMap (hE.suspensionPresentation Z₁₂) p) := by
    simpa [φ₃] using hE.projectiveStableFunctor_map_connectingMap_naturality h₂₃ hN φ₃
  refine
    { m₁ := E.projectiveStableFunctor.map α
      m₃ := E.projectiveStableFunctor.map β
      comm₁ := by simp only [← Functor.map_comp, hjc]
      comm₂ := by simp only [reassoc_of% n₁]
      comm₃ := by simp only [← Functor.map_comp, hcβ]
      comm₄ := by
        simp only [Category.assoc, reassoc_of% n₂,
          hE.stableSuspensionObjIsoShift_hom_naturality]
      mem := ?_ }
  -- The third arrow of the new triangle is the connecting morphism of the Noether conflation.
  have h₃ : (E.projectiveStableFunctor.map (hE.connectingMap h₂₃) ≫
      (hE.stableSuspensionObjIsoShift X₂).hom) ≫ (E.projectiveStableFunctor.map p)⟦(1 : ℤ)⟧' =
        E.projectiveStableFunctor.map (hE.connectingMap hN) ≫
          (hE.stableSuspensionObjIsoShift Z₁₂).hom := by
    rw [n₃, Category.assoc, Category.assoc, hE.stableSuspensionObjIsoShift_hom_naturality]
  simpa only [Triangle.mk_mor₃, h₃] using hE.mk_distinguished_of_conflation hN rfl

/-- The first new arrow `Z₁₂ ⟶ Z₁₃` of the octahedron is the image of the first map of the
Noether conflation. -/
@[simp]
theorem stableConflationOctahedron_m₁ (hjc : j ≫ c = p ≫ α) (hcβ : c ≫ β = v) :
    letI := hE.stableHasShift
    letI : ∀ n : ℤ, (shiftFunctor E.ProjectiveStableCategory n).Additive :=
      hE.stableShiftFunctor_additive
    letI := hE.stablePretriangulated
    (hE.stableConflationOctahedron h₁₂ h₂₃ h₁₃ hN hjc hcβ).m₁ =
      E.projectiveStableFunctor.map α :=
  (rfl)

/-- The second new arrow `Z₁₃ ⟶ Z₂₃` of the octahedron is the image of the second map of the
Noether conflation. -/
@[simp]
theorem stableConflationOctahedron_m₃ (hjc : j ≫ c = p ≫ α) (hcβ : c ≫ β = v) :
    letI := hE.stableHasShift
    letI : ∀ n : ℤ, (shiftFunctor E.ProjectiveStableCategory n).Additive :=
      hE.stableShiftFunctor_additive
    letI := hE.stablePretriangulated
    (hE.stableConflationOctahedron h₁₂ h₂₃ h₁₃ hN hjc hcβ).m₃ =
      E.projectiveStableFunctor.map β :=
  (rfl)

end Octahedron

include hE in
/-- A composable pair of morphisms in the stable category is isomorphic to the image of a
composable pair of inflations of conflations: replace each morphism `f : X ⟶ Y` by the
inflation `X ⟶ I(X) ⊞ Y` of its cone conflation. -/
private theorem exists_iso_conflations {X₁ X₂ X₃ : C} (f : X₁ ⟶ X₂) (g : X₂ ⟶ X₃) :
    ∃ (Y₂ Y₃ Z₁₂ Z₂₃ : C) (i : X₁ ⟶ Y₂) (p : Y₂ ⟶ Z₁₂) (hip : i ≫ p = 0)
      (j : Y₂ ⟶ Y₃) (w : Y₃ ⟶ Z₂₃) (hjw : j ≫ w = 0)
      (e₂ : E.projectiveStableFunctor.obj X₂ ≅ E.projectiveStableFunctor.obj Y₂)
      (e₃ : E.projectiveStableFunctor.obj X₃ ≅ E.projectiveStableFunctor.obj Y₃),
      E.Conflation (ShortComplex.mk i p hip) ∧ E.Conflation (ShortComplex.mk j w hjw) ∧
      E.projectiveStableFunctor.map f ≫ e₂.hom = E.projectiveStableFunctor.map i ∧
      E.projectiveStableFunctor.map g ≫ e₃.hom = e₂.hom ≫ E.projectiveStableFunctor.map j := by
  let e₂ := E.projectiveStableIsoBiprod (hE.isProjective_I (hE.suspensionPresentation X₁)) X₂
  let g' : hE.suspensionInjective X₁ ⊞ X₂ ⟶ X₃ := biprod.snd ≫ g
  let e₃ := E.projectiveStableIsoBiprod
    (hE.isProjective_I (hE.suspensionPresentation (hE.suspensionInjective X₁ ⊞ X₂))) X₃
  refine ⟨_, _, _, _, hE.coneInflation f, hE.coneDeflation f,
    hE.coneInflation_comp_coneDeflation f, hE.coneInflation g', hE.coneDeflation g',
    hE.coneInflation_comp_coneDeflation g', e₂, e₃, hE.conflation_cone f, hE.conflation_cone g',
    (hE.projectiveStableFunctor_map_coneInflation f).symm, ?_⟩
  rw [hE.projectiveStableFunctor_map_coneInflation]
  simp only [e₂, e₃, g', projectiveStableIsoBiprod_hom]
  rw [← Functor.map_comp_assoc, biprod.inr_snd_assoc]

/-- **Happel's theorem.** The stable category of a Frobenius exact category, with the shift
generated by stable suspension and the triangles generated by conflations, is triangulated. -/
theorem stableIsTriangulated :
    letI := hE.stableHasShift
    letI : ∀ n : ℤ, (shiftFunctor E.ProjectiveStableCategory n).Additive :=
      hE.stableShiftFunctor_additive
    letI := hE.stablePretriangulated
    IsTriangulated E.ProjectiveStableCategory := by
  let := hE.stableHasShift
  let : ∀ n : ℤ, (shiftFunctor E.ProjectiveStableCategory n).Additive :=
    hE.stableShiftFunctor_additive
  let := hE.stablePretriangulated
  refine IsTriangulated.mk' ?_
  rintro ⟨X₁⟩ ⟨X₂⟩ ⟨X₃⟩ f g
  obtain ⟨f, rfl⟩ := E.projectiveStableFunctor.map_surjective f
  obtain ⟨g, rfl⟩ := E.projectiveStableFunctor.map_surjective g
  obtain ⟨Y₂, Y₃, Z₁₂, Z₂₃, i, p, hip, j, w, hjw, e₂, e₃, h₁₂, h₂₃, hi, hj⟩ :=
    hE.exists_iso_conflations f g
  obtain ⟨Z₁₃, c, α, β, hc, hαβ, h₁₃, hN, hjc, hcβ⟩ := E.exists_conflation_comp h₁₂ h₂₃
  exact ⟨_, _, _, _, _, _, _, _, Iso.refl _, e₂, e₃, by simpa using hi, hj, _, _,
    hE.mk_distinguished_of_conflation h₁₂ rfl, _, _,
    hE.mk_distinguished_of_conflation h₂₃ rfl, _, _,
    hE.mk_distinguished_of_conflation h₁₃ (E.projectiveStableFunctor.map_comp i j),
    ⟨hE.stableConflationOctahedron h₁₂ h₂₃ h₁₃ hN hjc hcβ⟩⟩

end TauCeti.ExactStructure.IsFrobenius
