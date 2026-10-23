/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import TauCeti.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
public import Mathlib.CategoryTheory.Category.Factorisation
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

/-!
# Scheme compactifications

A compactification of a scheme morphism is a factorization through a quasi-compact open
immersion followed by a proper morphism. Morphisms fix the source and lie over the base.
We realize this category as a full subcategory of Mathlib's `CategoryTheory.Factorisation`,
so its morphisms and category laws are inherited rather than reconstructed.
As in the Stacks Project's category of compactifications, density is not required.
These definitions impose no quasi-compactness or quasi-separatedness condition on the base.

The dense compactifications form the further full subcategory where the open immersion is
scheme-theoretically dominant. This condition retains the scheme structure, including
nilpotents. No existence theorem or reducedness assumption is part of these definitions.
Every map from a dense compactification lifts along a closed immersion of compactifications
(`Compactification.liftOfIsClosedImmersion`).

## References

* The Stacks Project, Section 38.32, *Compactifications* (tag 0ATT).
-/

public section

open CategoryTheory AlgebraicGeometry

universe u

namespace TauCeti

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- Factorizations with a quasi-compact open first map and proper second map. -/
def compactificationProperty : ObjectProperty (Factorisation f) :=
  fun C ↦ IsOpenImmersion C.ι ∧ QuasiCompact C.ι ∧ IsProper C.π

@[simp]
theorem compactificationProperty_iff (C : Factorisation f) :
    compactificationProperty f C ↔ IsOpenImmersion C.ι ∧ QuasiCompact C.ι ∧ IsProper C.π :=
  (Iff.rfl)

/-- Compactifications of `f`, with maps fixing `X` and lying over `S`. -/
abbrev Compactification := (compactificationProperty f).FullSubcategory

namespace Compactification

variable {f}

/-- The ambient proper scheme of a compactification. -/
abbrev Xbar (C : Compactification f) : Scheme.{u} := C.obj.mid

/-- The open immersion of the source into its compactification. -/
abbrev j (C : Compactification f) : X ⟶ C.Xbar := C.obj.ι

/-- The proper structure map of a compactification. -/
abbrev p (C : Compactification f) : C.Xbar ⟶ S := C.obj.π

instance (C : Compactification f) : IsOpenImmersion C.j := C.property.1

instance (C : Compactification f) : QuasiCompact C.j := C.property.2.1

instance (C : Compactification f) : IsProper C.p := C.property.2.2

/-- Bundle a quasi-compact open immersion and a proper map as a compactification. -/
@[simps obj_mid obj_ι obj_π]
abbrev ofHom {Y : Scheme.{u}} (j : X ⟶ Y) (p : Y ⟶ S)
    [IsOpenImmersion j] [QuasiCompact j] [IsProper p] (fac : j ≫ p = f) :
    Compactification f :=
  ⟨⟨Y, j, p, fac⟩, (compactificationProperty_iff f _).mpr
    ⟨inferInstance, inferInstance, inferInstance⟩⟩

/-- A morphism of compactifications fixes the source and lies over the base. -/
abbrev Hom (C D : Compactification f) : Type _ := C ⟶ D

namespace Hom

/-- Every morphism of compactifications is proper. -/
instance proper {C D : Compactification f} (h : Hom C D) : IsProper h.hom.h := by
  have : IsProper (h.hom.h ≫ D.p) := by
    rw [h.hom.h_π]
    infer_instance
  exact IsProper.of_comp h.hom.h D.p

/-- A morphism of compactifications is a monomorphism when its map of ambient schemes is. -/
theorem mono_of_mono_h {C D : Compactification f} (h : Hom C D) [Mono h.hom.h] : Mono h :=
  ⟨fun a b hab ↦ ObjectProperty.hom_ext _ <| Factorisation.Hom.ext <| by
    rw [← cancel_mono h.hom.h]
    simpa using congrArg (fun k ↦ k.hom.h) hab⟩

instance {C D : Compactification f} (h : Hom C D) [IsClosedImmersion h.hom.h] : Mono h :=
  mono_of_mono_h h

/-- The map of ambient schemes underlying an isomorphism of compactifications is an
isomorphism. -/
instance isIso_hom_h {C D : Compactification f} (h : Hom C D) [IsIso h] : IsIso h.hom.h :=
  ⟨(inv h).hom.h, congrArg (fun k ↦ k.hom.h) (IsIso.hom_inv_id h),
    congrArg (fun k ↦ k.hom.h) (IsIso.inv_hom_id h)⟩

end Hom

/-- A compactifiable morphism is separated. -/
theorem isSeparated (C : Compactification f) : IsSeparated f := by
  rw [← C.obj.ι_π]
  infer_instance

/-- A compactifiable morphism is locally of finite type. -/
theorem locallyOfFiniteType (C : Compactification f) : LocallyOfFiniteType f := by
  rw [← C.obj.ι_π]
  infer_instance

/-- A compactifiable morphism is quasi-compact. -/
theorem quasiCompact (C : Compactification f) : QuasiCompact f := by
  rw [← C.obj.ι_π]
  infer_instance

variable (f)

/-- The identity compactification of a proper morphism. -/
abbrev identity [IsProper f] : Compactification f :=
  ofHom (𝟙 X) f (by simp)

/-- The identity compactification is initial: its map to any compactification is the
specified open immersion. -/
noncomputable def isInitialIdentity [IsProper f] : Limits.IsInitial (identity f) := by
  apply Limits.IsInitial.isInitialOfObj (compactificationProperty f).ι
  exact Factorisation.IsInitial_initial (f := f)

@[simp]
theorem isInitialIdentity_to_hom_h [IsProper f] (C : Compactification f) :
    ((isInitialIdentity f).to C).hom.h = C.j := by
  simpa using ((isInitialIdentity f).to C).hom.ι_h

end Compactification

/-- Scheme-theoretic density of the interior of a compactification. -/
def denseCompactificationProperty : ObjectProperty (Compactification f) :=
  fun C ↦ IsSchemeTheoreticallyDominant C.j

@[simp]
theorem denseCompactificationProperty_iff (C : Compactification f) :
    denseCompactificationProperty f C ↔ IsSchemeTheoreticallyDominant C.j :=
  (Iff.rfl)

/-- The full subcategory of compactifications with scheme-theoretically dense interior. -/
abbrev DenseCompactification := (denseCompactificationProperty f).FullSubcategory

namespace DenseCompactification

variable {f}

instance (C : DenseCompactification f) : IsSchemeTheoreticallyDominant C.obj.j := C.property

/-- A proper morphism has a dense identity compactification. -/
@[simps obj]
abbrev identity [IsProper f] : DenseCompactification f :=
  ⟨Compactification.identity f, (denseCompactificationProperty_iff f _).mpr
    (inferInstanceAs (IsSchemeTheoreticallyDominant (𝟙 X)))⟩

end DenseCompactification

namespace Compactification

variable {f}

/-- A map out of a dense compactification into `C` lifts along a closed immersion `φ : D ⟶ C`
of compactifications: the interior of `E` is scheme-theoretically dense and lands in the
closed subscheme `D.Xbar` of `C.Xbar`. -/
noncomputable def liftOfIsClosedImmersion {C D : Compactification f} (φ : D ⟶ C)
    [IsClosedImmersion φ.hom.h] (E : DenseCompactification f) (h : E.obj ⟶ C) : E.obj ⟶ D :=
  have H : φ.hom.h.ker ≤ h.hom.h.ker := by
    rw [← E.obj.j.ker_comp_of_isSchemeTheoreticallyDominant h.hom.h, h.hom.ι_h, ← φ.hom.ι_h]
    exact Scheme.Hom.le_ker_comp D.j φ.hom.h
  ObjectProperty.homMk
    { h := IsClosedImmersion.lift φ.hom.h h.hom.h H
      ι_h := by
        rw [← cancel_mono φ.hom.h, Category.assoc, IsClosedImmersion.lift_fac, h.hom.ι_h,
          φ.hom.ι_h]
      h_π := by
        rw [← φ.hom.h_π, IsClosedImmersion.lift_fac_assoc, h.hom.h_π] }

@[reassoc (attr := simp)]
theorem liftOfIsClosedImmersion_comp {C D : Compactification f} (φ : D ⟶ C)
    [IsClosedImmersion φ.hom.h] (E : DenseCompactification f) (h : E.obj ⟶ C) :
    liftOfIsClosedImmersion φ E h ≫ φ = h :=
  ObjectProperty.hom_ext _ <| Factorisation.Hom.ext <| IsClosedImmersion.lift_fac _ _ _

@[reassoc (attr := simp)]
theorem liftOfIsClosedImmersion_hom_h_comp {C D : Compactification f} (φ : D ⟶ C)
    [IsClosedImmersion φ.hom.h] (E : DenseCompactification f) (h : E.obj ⟶ C) :
    (liftOfIsClosedImmersion φ E h).hom.h ≫ φ.hom.h = h.hom.h :=
  IsClosedImmersion.lift_fac _ _ _

end Compactification

end TauCeti
