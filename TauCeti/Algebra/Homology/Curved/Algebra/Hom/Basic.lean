/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.Homology.Curved.Algebra.Defs
public import TauCeti.Algebra.Homology.DG.Algebra.Hom.Basic

/-!
# Strict morphisms of curved differential graded algebras

A strict morphism preserves the grading, differential, and stored right-module curvature.
Preserving curvature is a separate condition: commuting with the differential only forces the
difference of the curvatures to commute with the image, and does not force that difference to
vanish. These morphisms provide the algebra maps along which curved modules can be restricted.

`CurvedDGAlgHom` extends Mathlib's `GradedAlgHom`, with extensionality, identities and composition.
At zero curvature, `DGAlgHom.curvedEquiv` identifies strict curved morphisms with the existing
ordinary DG algebra morphisms. This equivalence preserves identities and composition.

The interface follows `TauCeti.DGAlgHom`.

## References

* L. Positselski, *Differential graded Koszul duality: an introductory survey*, Section 6.2.
  The curvature here is the negative of his curvature, as in `IsCurvedDGAlgebra`.
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

/-- A strict morphism of curved differential graded algebras: a graded algebra homomorphism
commuting with the differentials and preserving the right-module curvature. -/
structure CurvedDGAlgHom (hA : IsCurvedDGAlgebra 𝒜 dA wA)
    (hB : IsCurvedDGAlgebra ℬ dB wB) extends 𝒜 →ₐᵍ[R] ℬ where
  /-- The map commutes with the differentials. -/
  map_d' (a : A) : dB (toGradedAlgHom a) = toGradedAlgHom (dA a)
  /-- The map preserves the stored right-module curvature. -/
  map_curvature' : toGradedAlgHom wA = wB

namespace CurvedDGAlgHom

variable {hA : IsCurvedDGAlgebra 𝒜 dA wA} {hB : IsCurvedDGAlgebra ℬ dB wB}
  {hC : IsCurvedDGAlgebra 𝒞 dC wC}

/-- Strict curved morphisms are determined by their underlying graded algebra homomorphisms. -/
theorem toGradedAlgHom_injective :
    Function.Injective (toGradedAlgHom : CurvedDGAlgHom hA hB → 𝒜 →ₐᵍ[R] ℬ) := by
  rintro ⟨f, hf, hwf⟩ ⟨g, hg, hwg⟩ h
  cases h
  rfl

instance : FunLike (CurvedDGAlgHom hA hB) A B where
  coe f := f.toGradedAlgHom
  coe_injective _ _ h := toGradedAlgHom_injective <| GradedAlgHom.ext fun a ↦ congrFun h a

instance : GradedFunLike (CurvedDGAlgHom hA hB) 𝒜 ℬ where
  map_mem f := f.toGradedAlgHom.map_mem

instance : AlgHomClass (CurvedDGAlgHom hA hB) R A B where
  map_add f := f.toGradedAlgHom.map_add
  map_zero f := f.toGradedAlgHom.map_zero
  map_mul f := f.toGradedAlgHom.map_mul
  map_one f := f.toGradedAlgHom.map_one
  commutes f := f.toGradedAlgHom.commutes

instance : CoeOut (CurvedDGAlgHom hA hB) (𝒜 →ₐᵍ[R] ℬ) := ⟨toGradedAlgHom⟩

@[simp]
theorem coe_toGradedAlgHom (f : CurvedDGAlgHom hA hB) : ⇑f.toGradedAlgHom = f := (rfl)

@[simp]
theorem coe_mk (f : 𝒜 →ₐᵍ[R] ℬ) (hf) (hw) :
    ⇑(CurvedDGAlgHom.mk f hf hw : CurvedDGAlgHom hA hB) = f := (rfl)

/-- Two strict curved morphisms are equal if they agree on every element. -/
@[ext]
theorem ext {f g : CurvedDGAlgHom hA hB} (h : ∀ a, f a = g a) : f = g :=
  toGradedAlgHom_injective <| GradedAlgHom.ext h

/-- A strict curved morphism commutes with the differentials. -/
@[simp]
theorem map_d (f : CurvedDGAlgHom hA hB) (a : A) : dB (f a) = f (dA a) := f.map_d' a

/-- A strict curved morphism preserves the curvature. -/
@[simp]
theorem map_curvature (f : CurvedDGAlgHom hA hB) : f wA = wB := f.map_curvature'

/-- The identity strict morphism of a curved differential graded algebra. -/
-- Expose identity and composition so simultaneous connection changes have literal target
-- differentials: the target connection form is the image under the morphism being changed.
@[expose] protected def id (hA : IsCurvedDGAlgebra 𝒜 dA wA) : CurvedDGAlgHom hA hA where
  toGradedAlgHom := GradedAlgHom.id R 𝒜
  map_d' _ := rfl
  map_curvature' := rfl

@[simp]
theorem id_toGradedAlgHom (hA : IsCurvedDGAlgebra 𝒜 dA wA) :
    (CurvedDGAlgHom.id hA).toGradedAlgHom = GradedAlgHom.id R 𝒜 := (rfl)

@[simp]
theorem coe_id (hA : IsCurvedDGAlgebra 𝒜 dA wA) :
    ⇑(CurvedDGAlgHom.id hA) = _root_.id := (rfl)

@[simp]
theorem id_apply (hA : IsCurvedDGAlgebra 𝒜 dA wA) (a : A) : CurvedDGAlgHom.id hA a = a :=
  (rfl)

/-- Composition of strict curved differential graded algebra morphisms. -/
@[expose]
def comp (g : CurvedDGAlgHom hB hC) (f : CurvedDGAlgHom hA hB) : CurvedDGAlgHom hA hC where
  toGradedAlgHom := g.toGradedAlgHom.comp f.toGradedAlgHom
  map_d' a := by
    rw [GradedAlgHom.comp_apply, GradedAlgHom.comp_apply, g.map_d', f.map_d']
  map_curvature' := by
    rw [GradedAlgHom.comp_apply, f.map_curvature', g.map_curvature']

@[simp]
theorem comp_toGradedAlgHom (g : CurvedDGAlgHom hB hC) (f : CurvedDGAlgHom hA hB) :
    (g.comp f).toGradedAlgHom = g.toGradedAlgHom.comp f.toGradedAlgHom := (rfl)

@[simp]
theorem coe_comp (g : CurvedDGAlgHom hB hC) (f : CurvedDGAlgHom hA hB) :
    ⇑(g.comp f) = g ∘ f := (rfl)

@[simp]
theorem comp_apply (g : CurvedDGAlgHom hB hC) (f : CurvedDGAlgHom hA hB) (a : A) :
    g.comp f a = g (f a) := (rfl)

@[simp]
theorem comp_id (f : CurvedDGAlgHom hA hB) : f.comp (CurvedDGAlgHom.id hA) = f := by
  ext a
  simp

@[simp]
theorem id_comp (f : CurvedDGAlgHom hA hB) : (CurvedDGAlgHom.id hB).comp f = f := by
  ext a
  simp

/-- Composition of strict curved morphisms is associative. -/
@[simp]
theorem comp_assoc {D : Type*} [Ring D] [Algebra R D]
    {𝒟 : ℤ → Submodule R D} [GradedAlgebra 𝒟] {dD : D →ₗ[R] D} {wD : D}
    {hD : IsCurvedDGAlgebra 𝒟 dD wD} (k : CurvedDGAlgHom hC hD)
    (g : CurvedDGAlgHom hB hC) (f : CurvedDGAlgHom hA hB) :
    (k.comp g).comp f = k.comp (g.comp f) := by
  ext a
  simp

end CurvedDGAlgHom

namespace DGAlgHom

variable (hA : IsDGAlgebra 𝒜 dA) (hB : IsDGAlgebra ℬ dB)

/-- Ordinary DG algebra morphisms are exactly strict curved morphisms at zero curvature. -/
def curvedEquiv : DGAlgHom hA hB ≃ CurvedDGAlgHom hA.isCurvedDGAlgebra_zero
    hB.isCurvedDGAlgebra_zero where
  toFun f :=
    { toGradedAlgHom := f.toGradedAlgHom
      map_d' := f.map_d
      map_curvature' := map_zero f }
  invFun f := { toGradedAlgHom := f.toGradedAlgHom, map_d' := f.map_d }
  left_inv _ := rfl
  right_inv _ := rfl

@[simp]
theorem curvedEquiv_apply (f : DGAlgHom hA hB) (a : A) : curvedEquiv hA hB f a = f a := (rfl)

@[simp]
theorem curvedEquiv_symm_apply
    (f : CurvedDGAlgHom hA.isCurvedDGAlgebra_zero hB.isCurvedDGAlgebra_zero) (a : A) :
    (curvedEquiv hA hB).symm f a = f a := (rfl)

@[simp]
theorem curvedEquiv_toGradedAlgHom (f : DGAlgHom hA hB) :
    (curvedEquiv hA hB f).toGradedAlgHom = f.toGradedAlgHom := (rfl)

@[simp]
theorem curvedEquiv_symm_toGradedAlgHom
    (f : CurvedDGAlgHom hA.isCurvedDGAlgebra_zero hB.isCurvedDGAlgebra_zero) :
    ((curvedEquiv hA hB).symm f).toGradedAlgHom = f.toGradedAlgHom := (rfl)

@[simp]
theorem curvedEquiv_id : curvedEquiv hA hA (DGAlgHom.id hA) =
    CurvedDGAlgHom.id hA.isCurvedDGAlgebra_zero := by
  ext a
  simp

@[simp]
theorem curvedEquiv_comp (hC : IsDGAlgebra 𝒞 dC) (g : DGAlgHom hB hC) (f : DGAlgHom hA hB) :
    curvedEquiv hA hC (g.comp f) = (curvedEquiv hB hC g).comp (curvedEquiv hA hB f) := by
  ext a
  simp

end DGAlgHom

end TauCeti
