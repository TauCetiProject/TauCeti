/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.RingTheory.Henselian
import TauCeti.RingTheory.Henselian.Section

/-!
# Lifting morphisms from henselian local rings along étale morphisms

A morphism `Spec A ⟶ X` from the spectrum of a local ring `A` is a point `x` of `X` with a local
homomorphism `𝒪_{X,x} → A`. When `A` is henselian, such a morphism lifts along every étale
morphism `f : U ⟶ X` which has a point `u` over `x` with `κ(x) ≅ κ(u)`.

## Main results

* `AlgebraicGeometry.Scheme.Hom.exists_lift_of_isIso_residueFieldMap`: morphisms from the
  spectrum of a henselian local ring lift along étale morphisms through a point with unchanged
  residue field.

## References

* [Stacks Project, Lemma 15.11.6](https://stacks.math.columbia.edu/tag/09XI)
-/

public section

open CategoryTheory IsLocalRing

universe u

namespace AlgebraicGeometry

variable {X U : Scheme.{u}}

/-- Morphisms from the spectrum of a henselian local ring lift along étale morphisms through a
point with unchanged residue field: if `f : U ⟶ X` is étale, `κ(f u) ≅ κ(u)`, and `A` is a
henselian local ring with a local homomorphism `φ : 𝒪_{X, f u} → A`, then the morphism
`Spec A ⟶ X` given by `φ` factors through `f`. -/
theorem Scheme.Hom.exists_lift_of_isIso_residueFieldMap (f : U ⟶ X) [Etale f] (u : U)
    [IsIso (f.residueFieldMap u)] {A : Type u} [CommRing A] [HenselianLocalRing A]
    (φ : X.presheaf.stalk (f u) ⟶ CommRingCat.of A) [IsLocalHom φ.hom] :
    ∃ s : Spec (.of A) ⟶ U, s ≫ f = Spec.map φ ≫ X.fromSpecStalk (f u) := by
  -- Choose affine opens `W ∋ f u` and `V ∋ u` with `f(V) ⊆ W`.
  obtain ⟨_, ⟨W, hW, rfl⟩, hxW, -⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ (f u)) isOpen_univ
  obtain ⟨_, ⟨V, hV, rfl⟩, huV, hVW⟩ := U.isBasis_affineOpens.exists_subset_of_mem_open
    (show u ∈ f ⁻¹ᵁ W from hxW) (f ⁻¹ᵁ W).isOpen
  have e : V ≤ f ⁻¹ᵁ W := hVW
  -- On sections, `f` is an étale ring map `Γ(X, W) → Γ(U, V)`.
  have ha : (f.appLE W V e).hom.Etale :=
    HasRingHomProperty.appLE (P := @Etale) f ‹_› ⟨W, hW⟩ ⟨V, hV⟩ e
  let ψ : Γ(X, W) ⟶ CommRingCat.of A := X.presheaf.germ W (f u) hxW ≫ φ
  let : Algebra Γ(X, W) Γ(U, V) := (f.appLE W V e).hom.toAlgebra
  let : Algebra Γ(X, W) A := ψ.hom.toAlgebra
  have : Algebra.Etale Γ(X, W) Γ(U, V) := ha
  -- Evaluation at `u`, followed by `κ(u) ≅ κ(f u) → κ(A)`, is a section modulo `𝔪_A`.
  let ρ : Γ(U, V) →ₐ[Γ(X, W)] A ⧸ maximalIdeal A :=
    { toRingHom := (U.evaluation V u huV ≫ inv (f.residueFieldMap u) ≫
        CommRingCat.ofHom (ResidueField.map φ.hom)).hom
      commutes' r := by
        -- Evaluation at `u` of `f^* r` is the image of the value of `r` at `f u`.
        have key : U.evaluation V u huV (f.appLE W V e r) =
            f.residueFieldMap u (X.evaluation W (f u) hxW r) := by
          rw [Scheme.evaluation_naturality_apply, Scheme.Hom.appLE]
          simp [Scheme.evaluation]
        have hinv : inv (f.residueFieldMap u) (f.residueFieldMap u (X.evaluation W (f u) hxW r)) =
            X.evaluation W (f u) hxW r := by
          rw [← CommRingCat.comp_apply, IsIso.hom_inv_id, CommRingCat.id_apply]
        -- Unfold the bundled composite defining `ρ` and the algebra map `Γ(X, W) → A ⧸ 𝔪_A`,
        -- which is `ψ` followed by the quotient map, so that `key` applies.
        change ResidueField.map φ.hom (inv (f.residueFieldMap u)
          (U.evaluation V u huV (f.appLE W V e r))) =
            Ideal.Quotient.mk _ (φ (X.presheaf.germ W (f u) hxW r))
        rw [key, hinv]
        exact ResidueField.map_residue _ _ }
  obtain ⟨χ, -⟩ := (TauCeti.HenselianRing.comp_bijective_of_algebra (maximalIdeal A)).2 ρ
  refine ⟨Spec.map (CommRingCat.ofHom χ.toRingHom) ≫ hV.fromSpec, ?_⟩
  rw [Category.assoc, ← IsAffineOpen.SpecMap_appLE_fromSpec f hW hV e, ← Category.assoc,
    ← Spec.map_comp, ← hW.fromSpecStalk_eq_fromSpecStalk hxW]
  unfold IsAffineOpen.fromSpecStalk
  rw [← Category.assoc, ← Spec.map_comp]
  congr 2
  ext r
  exact χ.commutes r

end AlgebraicGeometry
