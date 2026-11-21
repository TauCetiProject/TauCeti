/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Scheme.BaseAlgebra

/-!
# Field-valued points over an affine base via residue fields

The field-valued points of a scheme over `Spec k` are pairs of an underlying point `x` and
an embedding of `κ(x)` into the test field over `k`. This is the relative form of Mathlib's
`Scheme.SpecToEquivOfField` (Hartshorne, *Algebraic Geometry*, Exercise II.2.7).
-/

public section

open CategoryTheory

namespace AlgebraicGeometry.Scheme

universe u

variable {k L : Type u} [CommRing k] [Field L] [Algebra k L]
  (X : Scheme.{u}) [X.Over (Spec (.of k))]

/-- A point of `X` with values in `L` over `Spec k` is a point `x` of `X` together with a
`k`-algebra map `κ(x) → L`. -/
noncomputable def pointsEquivSigmaResidueFieldAlgHom :
    {g : Spec (.of L) ⟶ X // g ≫ (X ↘ Spec (.of k)) = Spec.algebraMap k L} ≃
      Σ x : X, X.residueField x →ₐ[k] L := by
  let e := X.SpecToEquivOfField L
  have over_iff (x : X) (φ : X.residueField x ⟶ CommRingCat.of L) :
      (∀ c : k, φ (algebraMap k (X.residueField x) c) = algebraMap k L c) ↔
        e.symm ⟨x, φ⟩ ≫ (X ↘ Spec (.of k)) = Spec.algebraMap k L := by
    dsimp only [e]
    rw [SpecToEquivOfField_symm_apply, Category.assoc, fromSpecResidueField_comp_over,
      ← Spec.map_comp, Spec.map_inj, CommRingCat.hom_ext_iff]
    exact ⟨fun h ↦ RingHom.ext h, fun h c ↦ congrArg (fun f : k →+* L ↦ f c) h⟩
  refine (Equiv.ofBijective (fun (x : Σ x : X, X.residueField x →ₐ[k] L) ↦
    ⟨e.symm ⟨x.1, CommRingCat.ofHom x.2.toRingHom⟩, (over_iff _ _).mp x.2.commutes⟩) ?_).symm
  constructor
  · rintro ⟨x, φ⟩ ⟨y, ψ⟩ h
    have he := e.symm.injective (congrArg Subtype.val h)
    obtain ⟨(rfl : x = y), hφψ⟩ := SpecToEquivOfField_eq_iff.mp he
    have hφψ' : φ.toRingHom = ψ.toRingHom := by
      rw [residueFieldCongr_refl, Iso.refl_hom] at hφψ
      exact congrArg CommRingCat.Hom.hom hφψ
    exact congrArg (Sigma.mk x) (AlgHom.toRingHom_injective hφψ')
  · rintro ⟨g, hg⟩
    obtain ⟨⟨x, φ⟩, rfl⟩ := e.symm.surjective g
    exact ⟨⟨x, ⟨φ.hom, (over_iff x φ).mpr hg⟩⟩, rfl⟩

/-- The point attached to a residue-field embedding is the spectrum of the embedding followed by
the canonical map from the residue-field spectrum into `X`. -/
@[simp]
theorem pointsEquivSigmaResidueFieldAlgHom_symm_apply_coe
    (x : Σ x : X, X.residueField x →ₐ[k] L) :
    (X.pointsEquivSigmaResidueFieldAlgHom.symm x).val =
      Spec.map (CommRingCat.ofHom x.2.toRingHom) ≫ X.fromSpecResidueField x.1 :=
  (rfl)

/-- The underlying point in the residue-field description is the image of the unique point of
`Spec L`. -/
@[simp]
theorem pointsEquivSigmaResidueFieldAlgHom_apply_fst
    (g : {g : Spec (.of L) ⟶ X // g ≫ (X ↘ Spec (.of k)) = Spec.algebraMap k L}) :
    (X.pointsEquivSigmaResidueFieldAlgHom g).1 = g.val (default : ↥(Spec (.of L))) := by
  obtain ⟨x, rfl⟩ := X.pointsEquivSigmaResidueFieldAlgHom.symm.surjective g
  rw [Equiv.apply_symm_apply, pointsEquivSigmaResidueFieldAlgHom_symm_apply_coe,
    Hom.comp_apply, fromSpecResidueField_apply]

end AlgebraicGeometry.Scheme
