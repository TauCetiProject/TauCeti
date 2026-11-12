/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Center.Basic
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Quotient.Kernel.Basic

/-!
# Centers under dominant affine-group homomorphisms

A schematically dominant homomorphism of affine groups over a field carries the source center
into the target center. This gives a restricted homomorphism of the represented centers,
compatible with identity and composition. Dominance is essential: an arbitrary subgroup's
center need not be central in the ambient group.

Consequently, a dominant homomorphism with central kernel and centerless target has kernel
equal to the full scheme-theoretic source center. In particular, a central isogeny onto an
adjoint semisimple group is a quotient by the source center. The argument retains infinitesimal
centers and kernels and does not require smoothness, connectedness, or finite type.

The conjugation-defect argument follows the normal-image proof in
`TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Normal.Image`, using triviality of the action rather
than stability of an ideal.

## References

* J. S. Milne, *Algebraic Groups* (2017), §§1.k and 21, centers and adjoint groups.
-/

public section

open _root_.CommHopfAlgCat

open CategoryTheory

namespace TauCeti.CommHopfAlgCat

universe u v

variable {k : Type u} [Field k] {H K L : _root_.CommHopfAlgCat.{v} k}

/-- A dominant affine-group homomorphism carries the source center into the target center.
In coordinate rings, subgroup containment reverses and the center ideal pulls back along `f`. -/
theorem centerDefiningIdeal_le_comap (f : H ⟶ K) (hf : Function.Injective f.hom) :
    centerDefiningIdeal H ≤ (centerDefiningIdeal K).comap f.hom :=
  (centerDefiningIdeal_le_iff H _).mpr
    ((isCentral_centerDefiningIdeal K).comap_of_injective f.hom hf)

/-- The coordinate morphism of the restriction of a dominant homomorphism to the represented
centers. As usual, the coordinate arrow points opposite to the group homomorphism. -/
noncomputable def mapCenter (f : H ⟶ K) (hf : Function.Injective f.hom) :
    quotient H (centerDefiningIdeal H) ⟶ quotient K (centerDefiningIdeal K) :=
  liftQuotient (centerDefiningIdeal H) (f ≫ mkQuotient K (centerDefiningIdeal K)) (by
    intro x hx
    simp only [RingHom.mem_ker, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      BialgHom.coe_toAlgHom, _root_.CommHopfAlgCat.hom_comp, BialgHom.comp_apply]
    rw [mkQuotient_eq_zero_iff]
    exact HopfIdeal.mem_comap.mp (centerDefiningIdeal_le_comap f hf hx))

/-- Restriction to the centers commutes with their inclusions into the ambient groups. -/
@[reassoc (attr := simp)]
theorem mkQuotient_comp_mapCenter (f : H ⟶ K) (hf : Function.Injective f.hom) :
    mkQuotient H (centerDefiningIdeal H) ≫ mapCenter f hf =
      f ≫ mkQuotient K (centerDefiningIdeal K) := by
  rw [mapCenter, mkQuotient_comp_liftQuotient]

/-- The restricted coordinate map sends the class of a function to the class of its image. -/
-- Rewrite before simplification unfolds the bundled quotient morphisms.
@[simp↓]
theorem mapCenter_mkQuotient (f : H ⟶ K) (hf : Function.Injective f.hom) (x : H) :
    (mapCenter f hf).hom ((mkQuotient H (centerDefiningIdeal H)).hom x) =
      (mkQuotient K (centerDefiningIdeal K)).hom (f.hom x) := by
  have h := congrArg (fun g ↦ g.hom x) (mkQuotient_comp_mapCenter f hf)
  simpa only [_root_.CommHopfAlgCat.hom_comp, BialgHom.comp_apply] using h

/-- A morphism of centers is determined by compatibility with the ambient homomorphism. -/
theorem mapCenter_unique (f : H ⟶ K) (hf : Function.Injective f.hom)
    (g : quotient H (centerDefiningIdeal H) ⟶ quotient K (centerDefiningIdeal K))
    (hg : mkQuotient H (centerDefiningIdeal H) ≫ g =
      f ≫ mkQuotient K (centerDefiningIdeal K)) :
    g = mapCenter f hf := by
  apply (cancel_epi (mkQuotient H (centerDefiningIdeal H))).mp
  rw [hg, mkQuotient_comp_mapCenter]

/-- The identity homomorphism restricts to the identity on the represented center. -/
@[simp]
theorem mapCenter_id :
    mapCenter (𝟙 H) Function.injective_id = 𝟙 _ := by
  symm
  apply mapCenter_unique
  simp

/-- Restricting a composite of dominant homomorphisms to centers commutes with composition. -/
@[simp]
theorem mapCenter_comp (f : H ⟶ K) (g : K ⟶ L)
    (hf : Function.Injective f.hom) (hg : Function.Injective g.hom) :
    mapCenter (f ≫ g) (hg.comp hf) = mapCenter f hf ≫ mapCenter g hg := by
  symm
  apply mapCenter_unique
  simp

/-- A dominant homomorphism with central kernel and centerless target has kernel exactly the
full scheme-theoretic source center. This applies, in particular, to central isogenies onto
adjoint semisimple groups, including those with nonreduced kernels. -/
theorem kernelHopfIdeal_eq_centerDefiningIdeal_of_injective (f : H ⟶ K)
    (hf : Function.Injective f.hom) (hcentral : (kernelHopfIdeal f).IsCentral)
    (hH : centerDefiningIdeal H = HopfIdeal.augmentation k H) :
    kernelHopfIdeal f = centerDefiningIdeal K := by
  apply le_antisymm
  · rw [kernelHopfIdeal_def, HopfIdeal.map_le_iff]
    have hle := centerDefiningIdeal_le_comap f hf
    rw [hH] at hle
    intro x hx
    exact HopfIdeal.mem_comap.mp (hle hx)
  · exact (centerDefiningIdeal_le_iff K _).mpr hcentral

end TauCeti.CommHopfAlgCat
