/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Triangulated.Functor
public import TauCeti.CategoryTheory.Idempotents.Karoubi
public import TauCeti.CategoryTheory.Idempotents.Shift
public import TauCeti.CategoryTheory.Triangulated.Idempotent

/-!
# The idempotent completion of a pretriangulated category

Let `C` be a pretriangulated category. Its idempotent completion `Karoubi C` carries the shift
`(X, e)⟦n⟧ = (X⟦n⟧, e⟦n⟧')` (`TauCeti/CategoryTheory/Idempotents/Shift.lean`). Following Balmer and
Schlichting, a triangle of `Karoubi C` is declared distinguished when it is a retract, in the
category of triangles, of the image under `toKaroubi C` of a distinguished triangle of `C`. This
is a pretriangulation of `Karoubi C`, for which `toKaroubi C` is a triangulated functor which
reflects distinguished triangles.

Retracts make the isomorphism, rotation and morphism axioms formal consequences of those of `C`.
For the existence of cones, let `f : (X, p) ⟶ (Y, q)`. Its underlying morphism lies on a
distinguished triangle `X ⟶ Y ⟶ Z ⟶ X⟦1⟧` of `C`, and `(p, q)` extends to an idempotent
endomorphism `(p, q, r)` of this triangle (`Pretriangulated.Triangle.exists_idempotent_hom₃`).
The triangle `(X, p) ⟶ (Y, q) ⟶ (Z, r) ⟶ (X, p)⟦1⟧` it cuts out is then a retract of the image of
the triangle of `C`.

## Main definitions

* `CategoryTheory.Idempotents.Karoubi.triangleOfIdempotent`: the triangle of `Karoubi C` cut out
  of a triangle of `C` by an idempotent endomorphism, and `retractTriangleOfIdempotent`, which
  exhibits it as a retract of the image of that triangle.
* `CategoryTheory.Idempotents.Karoubi.distinguishedTriangles`: the retracts of images of
  distinguished triangles of `C`.
* The instance `Pretriangulated (Karoubi C)`, whose axioms are
  `CategoryTheory.Idempotents.Karoubi.isomorphic_distinguished`, `contractible_distinguished`,
  `distinguished_cocone_triangle`, `rotate_distinguished_triangle` and
  `complete_distinguished_triangle_morphism`.

## Main results

* `CategoryTheory.Idempotents.Karoubi.mem_distTriang_iff`: the distinguished triangles of
  `Karoubi C` are the retracts of images of distinguished triangles of `C`.
* `CategoryTheory.Idempotents.Karoubi.distinguished_of_retract`: distinguished triangles of
  `Karoubi C` are closed under retracts.
* `CategoryTheory.Idempotents.Karoubi.triangleOfIdempotent_distinguished`: the triangle cut out of
  a distinguished triangle of `C` by an idempotent endomorphism is distinguished.
* The instance `(toKaroubi C).IsTriangulated`. As `toKaroubi C` is fully faithful, Mathlib's
  `CategoryTheory.Functor.map_distinguished_iff` then shows that a triangle of `C` is
  distinguished exactly when its image in `Karoubi C` is.

## References

* P. Balmer and M. Schlichting, *Idempotent completion of triangulated categories*, J. Algebra
  236 (2001), Definition 1.10 and Theorem 1.12.
-/

public section

namespace CategoryTheory

open Category Limits Pretriangulated

universe v u

variable {C : Type u} [Category.{v} C] [HasShift C ℤ]

namespace Idempotents.Karoubi

section TriangleOfIdempotent

variable (T : Triangle C) (e : T ⟶ T) (he : e ≫ e = e)
include he

@[reassoc]
private theorem idem₁ : e.hom₁ ≫ e.hom₁ = e.hom₁ := congr_arg TriangleMorphism.hom₁ he

@[reassoc]
private theorem idem₂ : e.hom₂ ≫ e.hom₂ = e.hom₂ := congr_arg TriangleMorphism.hom₂ he

@[reassoc]
private theorem idem₃ : e.hom₃ ≫ e.hom₃ = e.hom₃ := congr_arg TriangleMorphism.hom₃ he

/-- The triangle of `Karoubi C` cut out of a triangle `T` of `C` by an idempotent endomorphism `e`
of `T`: its objects are `(T.objᵢ, e.homᵢ)` and its morphisms are those of `T`, cut down by `e`. -/
noncomputable abbrev triangleOfIdempotent : Triangle (Karoubi C) :=
  Triangle.mk (X := ⟨T.obj₁, e.hom₁, congr_arg TriangleMorphism.hom₁ he⟩)
    (Y := ⟨T.obj₂, e.hom₂, congr_arg TriangleMorphism.hom₂ he⟩)
    (Z := ⟨T.obj₃, e.hom₃, congr_arg TriangleMorphism.hom₃ he⟩)
    ⟨e.hom₁ ≫ T.mor₁, by simp [idem₁_assoc T e he]⟩ ⟨e.hom₂ ≫ T.mor₂, by simp [idem₂_assoc T e he]⟩
    ⟨e.hom₃ ≫ T.mor₃, by simp only [shiftFunctor_obj_p, assoc, e.comm₃, idem₃_assoc T e he]⟩

/-- The triangle cut out of `T` by an idempotent endomorphism is a retract of the image of `T`. -/
noncomputable def retractTriangleOfIdempotent :
    Retract (triangleOfIdempotent T e he) ((toKaroubi C).mapTriangle.obj T) where
  i := Triangle.homMk _ _ ⟨e.hom₁, by simp [idem₁ T e he]⟩ ⟨e.hom₂, by simp [idem₂ T e he]⟩
    ⟨e.hom₃, by simp [idem₃ T e he]⟩
    (by ext; simp [e.comm₁, idem₁_assoc T e he])
    (by ext; simp [e.comm₂, idem₂_assoc T e he])
    (by ext; simp [e.comm₃, idem₃_assoc T e he])
  r := Triangle.homMk _ _ ⟨e.hom₁, by simp [idem₁ T e he]⟩ ⟨e.hom₂, by simp [idem₂ T e he]⟩
    ⟨e.hom₃, by simp [idem₃ T e he]⟩
    (by ext; simp [idem₁_assoc T e he])
    (by ext; simp [idem₂_assoc T e he])
    (by ext; simp [idem₃_assoc T e he])
  retract := by
    ext
    · exact idem₁ T e he
    · exact idem₂ T e he
    · exact idem₃ T e he

end TriangleOfIdempotent

variable [Preadditive C] [HasZeroObject C] [∀ n : ℤ, (CategoryTheory.shiftFunctor C n).Additive]
  [Pretriangulated C]

/-- The distinguished triangles of the idempotent completion: the retracts of images of
distinguished triangles of `C`. -/
def distinguishedTriangles : Set (Triangle (Karoubi C)) :=
  {T | ∃ D ∈ distTriang C, Nonempty (Retract T ((toKaroubi C).mapTriangle.obj D))}

/-- Distinguished triangles of `Karoubi C` are closed under isomorphism. -/
theorem isomorphic_distinguished (T₁ : Triangle (Karoubi C))
    (h : T₁ ∈ distinguishedTriangles) (T₂ : Triangle (Karoubi C)) (e : T₂ ≅ T₁) :
    T₂ ∈ distinguishedTriangles := by
  obtain ⟨D, hD, ⟨r⟩⟩ := h
  exact ⟨D, hD, ⟨(Retract.ofIso e).trans r⟩⟩

/-- The contractible triangle `P ⟶ P ⟶ 0 ⟶ P⟦1⟧` of `Karoubi C` is distinguished. -/
theorem contractible_distinguished (P : Karoubi C) :
    contractibleTriangle P ∈ distinguishedTriangles := by
  -- It is cut out of the contractible triangle on `P.X` by the idempotent endomorphism
  -- `(P.p, P.p, 0)`.
  let e : contractibleTriangle P.X ⟶ contractibleTriangle P.X :=
    { hom₁ := P.p, hom₂ := P.p, hom₃ := 0 }
  have he : e ≫ e = e := by ext <;> simp [e]
  have hZ : IsZero (triangleOfIdempotent _ e he).obj₃ := by
    rw [IsZero.iff_id_eq_zero]
    ext
    simp [e]
  refine isomorphic_distinguished _ ⟨_, Pretriangulated.contractible_distinguished P.X,
    ⟨retractTriangleOfIdempotent _ e he⟩⟩ _
    (Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) ((isZero_zero _).iso hZ) ?_
      (hZ.eq_of_tgt _ _) ((isZero_zero _).eq_of_src _ _))
  ext
  simp [e]

/-- Every morphism of `Karoubi C` is the first morphism of a distinguished triangle. -/
theorem distinguished_cocone_triangle {P Q : Karoubi C} (f : P ⟶ Q) :
    ∃ (Z : Karoubi C) (g : Q ⟶ Z) (h : Z ⟶ P⟦(1 : ℤ)⟧),
      Triangle.mk f g h ∈ distinguishedTriangles := by
  obtain ⟨Z, g, h, hD⟩ := Pretriangulated.distinguished_cocone_triangle f.f
  obtain ⟨r, hr, hr₂, hr₃⟩ :=
    Triangle.exists_idempotent_hom₃ _ hD P.idem Q.idem (by simp)
  let e : Triangle.mk f.f g h ⟶ Triangle.mk f.f g h :=
    { hom₁ := P.p, hom₂ := Q.p, hom₃ := r, comm₂ := hr₂, comm₃ := hr₃ }
  have he : e ≫ e = e := by ext <;> simp [e, hr]
  let T := triangleOfIdempotent _ e he
  -- The triangle cut out by `e` has first morphism `P.p ≫ f.f = f`.
  have hf : f = T.mor₁ := by
    ext
    simp [T, e]
  refine ⟨T.obj₃, T.mor₂, T.mor₃, ?_⟩
  rw [hf]
  -- `Triangle.mk T.mor₁ T.mor₂ T.mor₃` is `T` by structure eta.
  exact ⟨_, hD, ⟨retractTriangleOfIdempotent _ e he⟩⟩

/-- A triangle of `Karoubi C` is distinguished exactly when its rotation is. -/
theorem rotate_distinguished_triangle (T : Triangle (Karoubi C)) :
    T ∈ distinguishedTriangles ↔ T.rotate ∈ distinguishedTriangles := by
  constructor
  · rintro ⟨D, hD, ⟨r⟩⟩
    exact ⟨D.rotate, rot_of_distTriang D hD, ⟨(r.map (rotate (Karoubi C))).trans
      (Retract.ofIso ((toKaroubi C).mapTriangleRotateIso.app D))⟩⟩
  · rintro ⟨D, hD, ⟨r⟩⟩
    exact ⟨D.invRotate, inv_rot_of_distTriang D hD,
      ⟨(Retract.ofIso ((rotCompInvRot (C := Karoubi C)).app T)).trans
        ((r.map (invRotate (Karoubi C))).trans
          (Retract.ofIso ((toKaroubi C).mapTriangleInvRotateIso.app D)))⟩⟩

/-- A commutative square between the bases of two distinguished triangles of `Karoubi C` extends to
a morphism of triangles. -/
theorem complete_distinguished_triangle_morphism (T₁ T₂ : Triangle (Karoubi C))
    (h₁ : T₁ ∈ distinguishedTriangles) (h₂ : T₂ ∈ distinguishedTriangles)
    (a : T₁.obj₁ ⟶ T₂.obj₁) (b : T₁.obj₂ ⟶ T₂.obj₂) (comm : T₁.mor₁ ≫ b = a ≫ T₂.mor₁) :
    ∃ c : T₁.obj₃ ⟶ T₂.obj₃, T₁.mor₂ ≫ c = b ≫ T₂.mor₂ ∧ T₁.mor₃ ≫ a⟦1⟧' = c ≫ T₂.mor₃ := by
  obtain ⟨D₁, hD₁, ⟨r₁⟩⟩ := h₁
  obtain ⟨D₂, hD₂, ⟨r₂⟩⟩ := h₂
  -- Transport the square to the triangles `D₁` and `D₂` of `C` through the retractions.
  let a' := r₁.r.hom₁ ≫ a ≫ r₂.i.hom₁
  let b' := r₁.r.hom₂ ≫ b ≫ r₂.i.hom₂
  have comm' : ((toKaroubi C).mapTriangle.obj D₁).mor₁ ≫ b' =
      a' ≫ ((toKaroubi C).mapTriangle.obj D₂).mor₁ := by
    simp only [a', b', TriangleMorphism.comm₁, TriangleMorphism.comm₁_assoc, reassoc_of% comm,
      assoc]
  have hc₁ : D₁.mor₁ ≫ b'.f = a'.f ≫ D₂.mor₁ := by simpa using congr_arg Hom.f comm'
  obtain ⟨c', hc₂, hc₃⟩ :=
    Pretriangulated.complete_distinguished_triangle_morphism D₁ D₂ hD₁ hD₂ a'.f b'.f hc₁
  let φ := (toKaroubi C).mapTriangle.map (Triangle.homMk _ _ a'.f b'.f c' hc₁ hc₂ hc₃)
  have hφ₁ : φ.hom₁ = a' := by ext; simp [φ]
  have hφ₂ : φ.hom₂ = b' := by ext; simp [φ]
  -- Composing with the sections and retractions recovers `a` and `b`.
  let ψ := r₁.i ≫ φ ≫ r₂.r
  have h₁₁ : r₁.i.hom₁ ≫ r₁.r.hom₁ = 𝟙 _ := congr_arg TriangleMorphism.hom₁ r₁.retract
  have h₁₂ : r₁.i.hom₂ ≫ r₁.r.hom₂ = 𝟙 _ := congr_arg TriangleMorphism.hom₂ r₁.retract
  have h₂₁ : r₂.i.hom₁ ≫ r₂.r.hom₁ = 𝟙 _ := congr_arg TriangleMorphism.hom₁ r₂.retract
  have h₂₂ : r₂.i.hom₂ ≫ r₂.r.hom₂ = 𝟙 _ := congr_arg TriangleMorphism.hom₂ r₂.retract
  have hψ₁ : ψ.hom₁ = a := by simp [ψ, hφ₁, a', reassoc_of% h₁₁, h₂₁]
  have hψ₂ : ψ.hom₂ = b := by simp [ψ, hφ₂, b', reassoc_of% h₁₂, h₂₂]
  exact ⟨ψ.hom₃, hψ₂ ▸ ψ.comm₂, hψ₁ ▸ ψ.comm₃⟩

/-- The idempotent completion of a pretriangulated category is pretriangulated: a triangle is
distinguished when it is a retract of the image of a distinguished triangle of `C`. -/
instance instPretriangulated : Pretriangulated (Karoubi C) where
  distinguishedTriangles := distinguishedTriangles
  isomorphic_distinguished := isomorphic_distinguished
  contractible_distinguished := contractible_distinguished
  distinguished_cocone_triangle := distinguished_cocone_triangle
  rotate_distinguished_triangle := rotate_distinguished_triangle
  complete_distinguished_triangle_morphism := complete_distinguished_triangle_morphism

/-- The distinguished triangles of `Karoubi C` are the retracts of images of distinguished
triangles of `C`. -/
theorem mem_distTriang_iff (T : Triangle (Karoubi C)) :
    T ∈ distTriang (Karoubi C) ↔
      ∃ D ∈ distTriang C, Nonempty (Retract T ((toKaroubi C).mapTriangle.obj D)) :=
  Iff.rfl

/-- Distinguished triangles of `Karoubi C` are closed under retracts. -/
theorem distinguished_of_retract {T T' : Triangle (Karoubi C)} (r : Retract T T')
    (h : T' ∈ distTriang (Karoubi C)) : T ∈ distTriang (Karoubi C) := by
  obtain ⟨D, hD, ⟨r'⟩⟩ := h
  exact ⟨D, hD, ⟨r.trans r'⟩⟩

/-- The triangle cut out of a distinguished triangle of `C` by an idempotent endomorphism is
distinguished. -/
theorem triangleOfIdempotent_distinguished {T : Triangle C} (hT : T ∈ distTriang C) (e : T ⟶ T)
    (he : e ≫ e = e) : triangleOfIdempotent T e he ∈ distTriang (Karoubi C) :=
  ⟨T, hT, ⟨retractTriangleOfIdempotent T e he⟩⟩

/-- The embedding of a pretriangulated category in its idempotent completion is triangulated. -/
instance : (toKaroubi C).IsTriangulated where
  map_distinguished T hT := ⟨T, hT, ⟨Retract.refl _⟩⟩

end Idempotents.Karoubi

end CategoryTheory
