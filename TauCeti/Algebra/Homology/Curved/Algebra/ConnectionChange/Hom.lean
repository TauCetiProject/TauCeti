/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.RingTheory.GradedAlgebra.AlgHom
public import TauCeti.Algebra.Homology.Curved.Algebra.ConnectionChange.Basic

/-!
# Change-of-connection morphisms of curved DG algebras

A change-of-connection morphism consists of a graded algebra map `f` and a degree-one element
`a` of the target, with

`f (dA x) = dB (f x) + a * f x - (-1)^|x| • (f x * a)` and
`f wA = wB - dB a - a * a`.

Thus `f` intertwines the source differential and curvature with the target connection changed
by `a`. The curvature equation uses the stored right-module convention `w = -h`. Composition
of `(f, a)` followed by `(g, b)` has algebra map `g ∘ f` and form `b + g a`.

These morphisms retain their connection form as data. They are not coerced to functions or to
strict curved morphisms: equal underlying algebra maps can have different connection forms.
Extensionality therefore requires agreement on both the algebra map and the form. The canonical
morphism from a changed connection to the original one, and its inverse, verify both compatibility
equations and show that changing a connection is invertible in this sense.

## References

* L. Positselski, *Differential graded Koszul duality: an introductory survey*, Section 6.2,
  for CDG-ring morphisms and changes of connection, translated by `w = -h`.

The underlying maps and their composition are Mathlib's `GradedAlgHom`; the connection change
is `TauCeti.IsCurvedDGAlgebra.connectionChange`.
-/

public section

namespace TauCeti

universe uR uA uB uC

variable {R : Type uR} {A : Type uA} {B : Type uB} {C : Type uC}
  [CommRing R] [Ring A] [Ring B] [Ring C]
  [Algebra R A] [Algebra R B] [Algebra R C]
  {𝒜 : ℤ → Submodule R A} {ℬ : ℤ → Submodule R B} {𝒞 : ℤ → Submodule R C}
  [GradedAlgebra 𝒜] [GradedAlgebra ℬ] [GradedAlgebra 𝒞]
  {dA : A →ₗ[R] A} {dB : B →ₗ[R] B} {dC : C →ₗ[R] C}
  {wA : A} {wB : B} {wC : C}

/-- A graded algebra map intertwining the source curved DG structure with a change of the
target connection. The connection form is part of the morphism, not just an existence proof. -/
structure CurvedDGConnectionHom (hA : IsCurvedDGAlgebra 𝒜 dA wA)
    (hB : IsCurvedDGAlgebra ℬ dB wB) where
  /-- The underlying degree-zero graded algebra homomorphism. -/
  hom : 𝒜 →ₐᵍ[R] ℬ
  /-- The degree-one connection form in the target. -/
  form : ℬ 1
  /-- Differential compatibility after changing the target connection. -/
  map_d : ∀ {p : ℤ} {x : A}, x ∈ 𝒜 p →
    hom (dA x) = dB (hom x) + (form : B) * hom x - p.negOnePow • (hom x * form)
  /-- Curvature compatibility in the right-module convention. -/
  map_curvature : hom wA = wB - dB form - (form : B) * form

namespace CurvedDGConnectionHom

variable {hA : IsCurvedDGAlgebra 𝒜 dA wA} {hB : IsCurvedDGAlgebra ℬ dB wB}
  {hC : IsCurvedDGAlgebra 𝒞 dC wC}

/-- Connection morphisms are determined by their graded algebra map and connection form. -/
@[ext]
theorem ext {f g : CurvedDGConnectionHom hA hB} (hh : f.hom = g.hom)
    (ha : f.form = g.form) : f = g := by
  cases f
  cases g
  cases hh
  cases ha
  rfl

/-- A connection morphism intertwines the source differential with the changed target
differential on all elements, not just homogeneous elements. -/
theorem map_d_eq_connectionChange (f : CurvedDGConnectionHom hA hB) (x : A) :
    f.hom (dA x) = connectionChange ℬ dB f.form (f.hom x) := by
  induction x using DirectSum.Decomposition.inductionOn 𝒜 with
  | zero => simp
  | @homogeneous p x =>
    exact (f.map_d x.property).trans
      (connectionChange_apply_of_mem ℬ (f.hom.map_mem x.property) dB f.form).symm
  | add x y hx hy => simp only [map_add, hx, hy]

/-- The identity connection morphism has zero connection form. -/
protected def id (hA : IsCurvedDGAlgebra 𝒜 dA wA) : CurvedDGConnectionHom hA hA where
  hom := GradedAlgHom.id R 𝒜
  form := 0
  map_d _ := by simp
  map_curvature := by simp

@[simp]
theorem id_hom (hA : IsCurvedDGAlgebra 𝒜 dA wA) :
    (CurvedDGConnectionHom.id hA).hom = GradedAlgHom.id R 𝒜 := (rfl)

@[simp]
theorem id_form (hA : IsCurvedDGAlgebra 𝒜 dA wA) :
    (CurvedDGConnectionHom.id hA).form = 0 := (rfl)

/-- Compose connection morphisms. The new form is the second form plus the image of the first.
No centrality assumption on either curvature is required. -/
def comp (g : CurvedDGConnectionHom hB hC) (f : CurvedDGConnectionHom hA hB) :
    CurvedDGConnectionHom hA hC where
  hom := g.hom.comp f.hom
  form := ⟨(g.form : C) + g.hom f.form, add_mem g.form.property
    (g.hom.map_mem f.form.property)⟩
  map_d {p x} hx := by
    simp only [GradedAlgHom.comp_apply]
    rw [f.map_d hx]
    simp only [Units.smul_def, map_sub, map_add, map_mul, map_zsmul]
    rw [g.map_d (x := f.hom x) (GradedFunLike.map_mem f.hom hx)]
    simp only [Units.smul_def]
    rcases Int.units_eq_one_or p.negOnePow with hp | hp <;>
      simp only [hp, Units.val_one, Units.val_neg, one_zsmul, neg_one_zsmul] <;>
      noncomm_ring
  map_curvature := by
    simp only [GradedAlgHom.comp_apply]
    rw [f.map_curvature, map_sub, map_sub, map_mul, g.map_curvature,
      g.map_d f.form.property, Int.negOnePow_one, Units.neg_smul, one_smul]
    simp only [map_add]
    noncomm_ring

@[simp]
theorem comp_hom (g : CurvedDGConnectionHom hB hC) (f : CurvedDGConnectionHom hA hB) :
    (g.comp f).hom = g.hom.comp f.hom := (rfl)

@[simp]
theorem comp_form (g : CurvedDGConnectionHom hB hC) (f : CurvedDGConnectionHom hA hB) :
    ((g.comp f).form : C) = (g.form : C) + g.hom f.form := (rfl)

@[simp]
theorem comp_id (f : CurvedDGConnectionHom hA hB) :
    f.comp (CurvedDGConnectionHom.id hA) = f := by
  apply ext
  · simp
  · apply Subtype.ext
    simp

@[simp]
theorem id_comp (f : CurvedDGConnectionHom hA hB) :
    (CurvedDGConnectionHom.id hB).comp f = f := by
  apply ext
  · simp
  · apply Subtype.ext
    simp

/-- Composition of connection morphisms is associative, including its connection forms. -/
theorem comp_assoc {D : Type*} [Ring D] [Algebra R D]
    {𝒟 : ℤ → Submodule R D} [GradedAlgebra 𝒟] {dD : D →ₗ[R] D} {wD : D}
    {hD : IsCurvedDGAlgebra 𝒟 dD wD} (k : CurvedDGConnectionHom hC hD)
    (g : CurvedDGConnectionHom hB hC) (f : CurvedDGConnectionHom hA hB) :
    (k.comp g).comp f = k.comp (g.comp f) := by
  apply ext
  · exact GradedAlgHom.comp_assoc _ _ _
  · apply Subtype.ext
    simp [add_assoc]

/-! ### Changing a connection and changing it back -/

/-- The identity algebra map with connection form `a`, from the connection changed by `a`
to the original curved DG algebra. -/
def fromConnectionChange (hA : IsCurvedDGAlgebra 𝒜 dA wA) (a : 𝒜 1) :
    CurvedDGConnectionHom (hA.connectionChange a.property) hA where
  hom := GradedAlgHom.id R 𝒜
  form := a
  map_d hx := connectionChange_apply_of_mem 𝒜 hx dA a
  map_curvature := rfl

@[simp]
theorem fromConnectionChange_hom (hA : IsCurvedDGAlgebra 𝒜 dA wA) (a : 𝒜 1) :
    (fromConnectionChange hA a).hom = GradedAlgHom.id R 𝒜 := (rfl)

@[simp]
theorem fromConnectionChange_form (hA : IsCurvedDGAlgebra 𝒜 dA wA) (a : 𝒜 1) :
    (fromConnectionChange hA a).form = a := (rfl)

/-- The inverse connection morphism, with form `-a`, from the original algebra to its
connection changed by `a`. -/
def toConnectionChange (hA : IsCurvedDGAlgebra 𝒜 dA wA) (a : 𝒜 1) :
    CurvedDGConnectionHom hA (hA.connectionChange a.property) where
  hom := GradedAlgHom.id R 𝒜
  form := -a
  map_d {p x} hx := by
    simp only [GradedAlgHom.id_apply]
    rw [connectionChange_apply_of_mem 𝒜 hx dA a]
    simp only [Submodule.coe_neg, neg_mul, mul_neg, smul_neg, sub_neg_eq_add]
    abel
  map_curvature := by
    simp only [GradedAlgHom.id_apply, Submodule.coe_neg, map_neg]
    rw [connectionChange_apply_of_mem 𝒜 a.property, Int.negOnePow_one,
      Units.neg_smul, one_smul]
    noncomm_ring

@[simp]
theorem toConnectionChange_hom (hA : IsCurvedDGAlgebra 𝒜 dA wA) (a : 𝒜 1) :
    (toConnectionChange hA a).hom = GradedAlgHom.id R 𝒜 := (rfl)

@[simp]
theorem toConnectionChange_form (hA : IsCurvedDGAlgebra 𝒜 dA wA) (a : 𝒜 1) :
    (toConnectionChange hA a).form = -a := (rfl)

/-- Changing a connection and returning to the original one gives the identity morphism. -/
@[simp]
theorem fromConnectionChange_comp_toConnectionChange
    (hA : IsCurvedDGAlgebra 𝒜 dA wA) (a : 𝒜 1) :
    (fromConnectionChange hA a).comp (toConnectionChange hA a) =
      CurvedDGConnectionHom.id hA := by
  apply ext
  · simp
  · apply Subtype.ext
    simp

/-- Returning to the original connection and changing it again gives the identity morphism. -/
@[simp]
theorem toConnectionChange_comp_fromConnectionChange
    (hA : IsCurvedDGAlgebra 𝒜 dA wA) (a : 𝒜 1) :
    (toConnectionChange hA a).comp (fromConnectionChange hA a) =
      CurvedDGConnectionHom.id (hA.connectionChange a.property) := by
  apply ext
  · simp
  · apply Subtype.ext
    simp

end CurvedDGConnectionHom

end TauCeti
