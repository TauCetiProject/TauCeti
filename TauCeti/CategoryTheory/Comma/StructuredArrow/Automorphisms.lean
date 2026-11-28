/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Comma.StructuredArrow.Basic
public import Mathlib.CategoryTheory.Endomorphism
public import Mathlib.Algebra.Group.Subgroup.Ker

/-!
# Automorphisms in a fibre of a functor

For a monic costructured arrow `F.obj x ⟶ y`, its automorphisms are exactly the
kernel of `Aut x → Aut (F.obj x)`. This describes the inertia of a fibre groupoid, for
example the groupoid of roots of a line bundle under the tensor-power functor.
-/

public section

namespace CategoryTheory.CostructuredArrow

variable {C D : Type*} [Category C] [Category D] {F : C ⥤ D} {Y : D}

/-- The automorphisms of a monic costructured arrow are the kernel of the induced
homomorphism on automorphism groups. -/
noncomputable def autMulEquivKer (R : CostructuredArrow F Y) [Mono R.hom] :
    Aut R ≃* (F.mapAut R.left).ker := by
  let p := (proj F Y).mapAut R
  have hp (a : Aut R) : p a ∈ (F.mapAut R.left).ker := by
    apply MonoidHom.mem_ker.mpr
    apply Aut.ext
    apply Iso.ext
    apply (cancel_mono R.hom).mp
    simpa only [p, Functor.mapAut_apply_asIso, Functor.mapIso_hom,
      proj_map, Aut.one_asIso, Iso.refl_hom, Category.id_comp] using w a.asIso.hom
  refine MulEquiv.ofBijective (p.codRestrict _ hp) ⟨?_, ?_⟩
  · intro a b h
    apply Aut.ext
    apply Iso.ext
    apply hom_ext
    exact congrArg (fun e : Aut R.left ↦ e.asIso.hom) (congrArg Subtype.val h)
  · rintro ⟨a, ha⟩
    have h : F.map a.asIso.hom = 𝟙 _ :=
      congrArg (fun e : Aut (F.obj R.left) ↦ e.asIso.hom) (MonoidHom.mem_ker.mp ha)
    refine ⟨⟨isoMk a.asIso (by simp [h])⟩, ?_⟩
    apply Subtype.ext
    apply Aut.ext
    apply Iso.ext
    rfl

/-- The kernel identification sends an automorphism to its image under the projection. -/
@[simp]
lemma coe_autMulEquivKer (R : CostructuredArrow F Y) [Mono R.hom] (a : Aut R) :
    (autMulEquivKer R a : Aut R.left) = (proj F Y).mapAut R a := (rfl)

end CategoryTheory.CostructuredArrow
