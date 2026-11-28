/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Jie Xu, Shitan Xu
-/
module

public import Mathlib.AlgebraicGeometry.Group.Affine

/-!
# The relative Γ–Spec hom equivalence over an affine scheme

Transporting the relative Γ–Spec adjunction along an affine base's spectrum isomorphism
identifies morphisms into a relative affine spectrum with algebra maps on global sections.
-/

public section

open CategoryTheory Limits Opposite

universe schemeUniverse

namespace AlgebraicGeometry

/-- The relative global-section algebra over an affine base agrees with the algebra induced
by the original structure morphism. -/
noncomputable def Scheme.overAffineGammaIso {base : Scheme.{schemeUniverse}} [IsAffine base]
    (test : Over base) :
    letI := test.hom.appTop.hom.toAlgebra
    ((algΓ Γ(base, ⊤)).obj ((Over.map base.isoSpec.hom).obj test)).unop ≅
      CommAlgCat.of Γ(base, ⊤) Γ(test.left, ⊤) := by
  letI := test.hom.appTop.hom.toAlgebra
  refine CommAlgCat.isoMk { toRingEquiv := RingEquiv.refl _, commutes' := ?_ }
  intro r
  -- The transported scalar action is the global section map composed with the inverse Γ–Spec
  -- comparison. Writing this composite exposes the cancellation of the two Γ–Spec maps.
  change (((Scheme.ΓSpecIso Γ(base, ⊤)).inv ≫
    (test.hom ≫ base.isoSpec.hom).appTop).hom) r = test.hom.appTop.hom r
  rw [Scheme.Hom.comp_appTop]
  simp only [Scheme.isoSpec, asIso_hom, Scheme.toSpecΓ_appTop, Iso.inv_hom_id_assoc]


/-- Relative Γ–Spec adjunction over an affine base, transported along its spectrum
isomorphism and read as algebra homomorphisms. -/
noncomputable def Scheme.overAffineHomEquivAlgHom
    {base : Scheme.{schemeUniverse}} [IsAffine base] (test : Over base)
    (A : CommAlgCat Γ(base, ⊤)) :
    letI := test.hom.appTop.hom.toAlgebra
    (test ⟶ Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Γ(base, ⊤) A)) ≫
      base.isoSpec.inv)) ≃ (A →ₐ[Γ(base, ⊤)] Γ(test.left, ⊤)) := by
  letI := test.hom.appTop.hom.toAlgebra
  let q := (Over.map base.isoSpec.hom).obj test
  let chart := Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Γ(base, ⊤) A)) ≫
    base.isoSpec.inv)
  let chartIso : (Over.map base.isoSpec.hom).obj chart ≅
      (algSpec Γ(base, ⊤)).obj (op A) :=
    Over.isoMk (Iso.refl _) (by
      -- The isomorphism has identity underlying scheme map. Its structural equation compares
      -- the affine spectrum map with the same map transported along the base isomorphism.
      change (𝟙 (Spec (CommRingCat.of A))) ≫
        Spec.map (CommRingCat.ofHom (algebraMap Γ(base, ⊤) A)) = _
      rw [Category.id_comp]
      change _ = (Spec.map (CommRingCat.ofHom (algebraMap Γ(base, ⊤) A)) ≫
        base.isoSpec.inv) ≫ base.isoSpec.hom
      rw [Category.assoc, base.isoSpec.inv_hom_id]
      exact (Category.comp_id _).symm)
  exact (Over.mapIso base.isoSpec).fullyFaithfulFunctor.homEquiv |>.trans
    (Iso.homCongr (Iso.refl q) chartIso) |>.trans
    ((algΓAlgSpecAdjunction Γ(base, ⊤)).homEquiv q (op A)).symm |>.trans
    (opEquiv _ _) |>.trans
    (Iso.homCongr (Iso.refl A) (Scheme.overAffineGammaIso test)) |>.trans
    (ConcreteCategory.homEquiv (C := CommAlgCat Γ(base, ⊤)))

/-- The relative hom equivalence sends a scheme morphism to its induced map on global
sections, with the canonical spectrum coordinate isomorphism. -/
theorem Scheme.overAffineHomEquivAlgHom_toRingHom
    {base : Scheme.{schemeUniverse}} [IsAffine base] (test : Over base)
    (A : CommAlgCat Γ(base, ⊤))
    (a : test ⟶ Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Γ(base, ⊤) A)) ≫
      base.isoSpec.inv)) :
    letI := test.hom.appTop.hom.toAlgebra
    (Scheme.overAffineHomEquivAlgHom test A a : A →+* Γ(test.left, ⊤)) =
      ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ a.left.appTop).hom := by
  unfold Scheme.overAffineHomEquivAlgHom Scheme.overAffineGammaIso
  rfl

end AlgebraicGeometry
