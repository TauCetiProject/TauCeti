/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Group.Affine

/-!
# Global sections of affine group schemes

Mathlib equips the global sections of an affine group scheme with a Hopf algebra
structure by transporting its group operations through `Scheme.isoSpec`. Here we
identify the resulting Hopf spectrum with the original group scheme, with underlying
map exactly `Scheme.isoSpec`. In particular, global sections of the spectrum of a
commutative Hopf algebra recover that Hopf algebra, including its coalgebra structure.

These comparisons use Mathlib's native global-sections Hopf structure and
`AlgebraicGeometry.hopfSpec.fullyFaithful`. They supplement the abstract affine
anti-equivalence with computation on actual global sections. The base ring is arbitrary;
no finite-type, flatness or smoothness hypothesis is required.
-/

public section

open CategoryTheory AlgebraicGeometry Scheme Opposite MonoidalCategory
open scoped CategoryTheory.MonObj

universe u

namespace CommRingCat

variable (R : CommRingCat.{u}) (G : Scheme.{u}) [G.Over (Spec R)]
  [GrpObj (G.asOver (Spec R))] [IsAffine G]

/-- The canonical affine-scheme isomorphism respects the group law when global sections
carry Mathlib's native Hopf structure. -/
noncomputable def globalSectionsSpecIso :
    Grp.mk (G.asOver (Spec R)) ≅
      (hopfSpec R).obj (op (CommHopfAlgCat.of R Γ(G, ⊤))) := by
  -- Fix the target as an `algSpec` object before exposing its transported operations.
  let e : G.asOver (Spec R) ≅ (algSpec R).obj (op (CommAlgCat.of R Γ(G, ⊤))) :=
    G.isoSpec.asOver (Spec R)
  refine Grp.mkIso e ?_ ?_
  -- The native Hopf structure pulls the transported group object back along `algSpec`.
  -- Expose that pullback once: mapping its operations forwards cancels the preimages.
  · change η ≫ _ =
      Functor.LaxMonoidal.ε (algSpec R) ≫
        (algSpec R).map (algSpec.fullyFaithful.preimage
          (X := 𝟙_ (CommAlgCat R)ᵒᵖ) (Y := op (CommAlgCat.of R Γ(G, ⊤)))
          (Functor.OplaxMonoidal.η (algSpec R) ≫
            (η[G.asOver (Spec R)] ≫ e.hom)))
    simp
  · change μ ≫ _ = (_ ⊗ₘ _) ≫
      (Functor.LaxMonoidal.μ (algSpec R) _ _ ≫
        (algSpec R).map (algSpec.fullyFaithful.preimage
          (X := op (CommAlgCat.of R Γ(G, ⊤)) ⊗ op (CommAlgCat.of R Γ(G, ⊤)))
          (Y := op (CommAlgCat.of R Γ(G, ⊤)))
          (Functor.OplaxMonoidal.δ (algSpec R) _ _ ≫
            ((e.inv ⊗ₘ e.inv) ≫
              μ[G.asOver (Spec R)] ≫ e.hom))))
    simp only [Functor.FullyFaithful.map_preimage, Functor.Monoidal.μ_δ_assoc]
    rw [← Category.assoc, tensorHom_comp_tensorHom]
    simp only [Iso.hom_inv_id, id_tensorHom_id, Category.id_comp]

/-- The global-sections comparison is the usual affine-scheme isomorphism on schemes. -/
@[simp]
theorem globalSectionsSpecIso_hom_left :
    (globalSectionsSpecIso R G).hom.hom.hom.left = G.isoSpec.hom := (rfl)

/-- The inverse global-sections comparison is the inverse affine-scheme isomorphism. -/
@[simp]
theorem globalSectionsSpecIso_inv_left :
    (globalSectionsSpecIso R G).inv.hom.hom.left = G.isoSpec.inv := (rfl)

variable (H : CommHopfAlgCat.{u} R)

/-- Global sections of a Hopf spectrum recover the original commutative Hopf algebra,
with the native global-sections Hopf structure. -/
noncomputable def globalSectionsHopfSpecIso :
    CommHopfAlgCat.of R Γ(Spec (CommRingCat.of H), ⊤) ≅ H :=
  (hopfSpec.fullyFaithful.preimageIso
    (globalSectionsSpecIso R (Spec (CommRingCat.of H)))).unop

/-- Taking the Hopf spectrum of the coordinate comparison gives the affine-scheme unit. -/
private theorem hopfSpec_map_globalSectionsHopfSpecIso_hom :
    ((hopfSpec R).map (globalSectionsHopfSpecIso R H).hom.op).hom.hom.left =
      (Spec (CommRingCat.of H)).isoSpec.hom := by
  unfold globalSectionsHopfSpecIso
  rw [Iso.unop_hom, Quiver.Hom.op_unop]
  exact congrArg (fun f ↦ f.hom.hom.left)
    (hopfSpec.fullyFaithful.map_preimage (X := op H)
      (Y := op (CommHopfAlgCat.of R Γ(Spec (CommRingCat.of H), ⊤)))
      (globalSectionsSpecIso R (Spec (CommRingCat.of H))).hom)

/-- The coordinate comparison on Hopf spectra is the usual `ΓSpecIso` on rings. -/
private theorem globalSectionsHopfSpecIso_hom_toRingHom :
    CommRingCat.ofHom (RingHomClass.toRingHom (globalSectionsHopfSpecIso R H).hom.hom) =
      (Scheme.ΓSpecIso (CommRingCat.of H)).hom := by
  apply Spec.map_injective
  erw [← Scheme.isoSpec_Spec_hom]
  -- The forgetful functor and `hopfSpec` have the same underlying ring map;
  -- this projection of the definition is not exposed by a public Mathlib lemma.
  exact hopfSpec_map_globalSectionsHopfSpecIso_hom R H

/-- The inverse coordinate comparison is the inverse of the usual `ΓSpecIso` on rings. -/
private theorem globalSectionsHopfSpecIso_inv_toRingHom :
    CommRingCat.ofHom (RingHomClass.toRingHom (globalSectionsHopfSpecIso R H).inv.hom) =
      (Scheme.ΓSpecIso (CommRingCat.of H)).inv := by
  have h :
      (((forget₂ (CommHopfAlgCat R) (CommBialgCat R)) ⋙
        (forget₂ (CommBialgCat R) (CommAlgCat R)) ⋙
        forget₂ (CommAlgCat R) CommRingCat).mapIso (globalSectionsHopfSpecIso R H)) =
        Scheme.ΓSpecIso (CommRingCat.of H) :=
    Iso.ext (globalSectionsHopfSpecIso_hom_toRingHom R H)
  exact congrArg Iso.inv h

/-- The Hopf-algebra comparison evaluates by the canonical global-sections map. -/
@[simp]
theorem globalSectionsHopfSpecIso_hom_apply (x : Γ(Spec (CommRingCat.of H), ⊤)) :
    (globalSectionsHopfSpecIso R H).hom x =
      (Scheme.ΓSpecIso (CommRingCat.of H)).hom x := by
  exact congrArg (fun f : Γ(Spec (CommRingCat.of H), ⊤) ⟶ CommRingCat.of H ↦ f x)
    (globalSectionsHopfSpecIso_hom_toRingHom R H)

/-- The inverse Hopf-algebra comparison evaluates by the inverse global-sections map. -/
@[simp]
theorem globalSectionsHopfSpecIso_inv_apply (x : H) :
    (globalSectionsHopfSpecIso R H).inv x =
      (Scheme.ΓSpecIso (CommRingCat.of H)).inv x := by
  exact congrArg (fun f : CommRingCat.of H ⟶ Γ(Spec (CommRingCat.of H), ⊤) ↦ f x)
    (globalSectionsHopfSpecIso_inv_toRingHom R H)

end CommRingCat
