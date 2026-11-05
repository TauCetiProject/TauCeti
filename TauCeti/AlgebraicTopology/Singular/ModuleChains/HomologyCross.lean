/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.CrossProduct

/-!
# The bilinear cross product with coefficients in a commutative ring

The singular homology cross product lands in homology with coefficients in `k ⊗ k`.
Identifying these coefficients with `k` by multiplication gives a bilinear map on the
homology of the singular chain complexes with coefficients in `k`. This form of the API
lets one use linearity to track multiplicities of parametrized products of cycles.

The construction uses `TopCat.singularHomologyCross` and its naturality, without choosing
cycle representatives or another shuffle map.

## References

* A. Hatcher, *Algebraic Topology*, Section 3.B (the homology cross product).
-/

public noncomputable section

open CategoryTheory MonoidalCategory AlgebraicTopology

universe w

namespace TopCat

open TensorProduct

variable (k : Type w) [CommRing k] (X Y : TopCat.{w})

/-- The cross product with coefficients in a commutative ring, as a bilinear map. The
coefficient identification `k ⊗ k ≅ k` is the left unitor, so it multiplies coefficients. -/
def singularHomologyCrossBilinear (p q n : ℕ) (h : p + q = n) :
    ((singularHomologyFunctor (ModuleCat.{w} k) p).obj (𝟙_ _)).obj X →ₗ[k]
      ((singularHomologyFunctor (ModuleCat.{w} k) q).obj (𝟙_ _)).obj Y →ₗ[k]
        ((singularHomologyFunctor (ModuleCat.{w} k) n).obj (𝟙_ _)).obj (X ⊗ Y) :=
  TensorProduct.curry (singularHomologyCross X Y (𝟙_ (ModuleCat.{w} k)) (𝟙_ _) p q n h ≫
    ((singularHomologyFunctor (ModuleCat.{w} k) n).map (λ_ (𝟙_ _)).hom).app (X ⊗ Y)).hom

/-- The bilinear cross product is the categorical cross product followed by the coefficient
identification `k ⊗ k ≅ k`. -/
theorem singularHomologyCrossBilinear_apply (p q n : ℕ) (h : p + q = n)
    (a : ((singularHomologyFunctor (ModuleCat.{w} k) p).obj (𝟙_ _)).obj X)
    (b : ((singularHomologyFunctor (ModuleCat.{w} k) q).obj (𝟙_ _)).obj Y) :
    singularHomologyCrossBilinear k X Y p q n h a b =
      ((singularHomologyFunctor (ModuleCat.{w} k) n).map (λ_ (𝟙_ _)).hom).app (X ⊗ Y)
        (singularHomologyCross X Y (𝟙_ (ModuleCat.{w} k)) (𝟙_ _) p q n h (a ⊗ₜ b)) := (rfl)

variable {X Y} {X' Y' : TopCat.{w}}

/-- Naturality of the bilinear cross product in both spaces. -/
theorem singularHomologyCrossBilinear_naturality (f : X ⟶ X') (g : Y ⟶ Y')
    (p q n : ℕ) (h : p + q = n)
    (a : ((singularHomologyFunctor (ModuleCat.{w} k) p).obj (𝟙_ _)).obj X)
    (b : ((singularHomologyFunctor (ModuleCat.{w} k) q).obj (𝟙_ _)).obj Y) :
    ((singularHomologyFunctor (ModuleCat.{w} k) n).obj (𝟙_ _)).map (f ⊗ₘ g)
        (singularHomologyCrossBilinear k X Y p q n h a b) =
      singularHomologyCrossBilinear k X' Y' p q n h
        (((singularHomologyFunctor (ModuleCat.{w} k) p).obj (𝟙_ _)).map f a)
        (((singularHomologyFunctor (ModuleCat.{w} k) q).obj (𝟙_ _)).map g b) := by
  have hn := singularHomologyCross_naturality_assoc f g (𝟙_ (ModuleCat.{w} k))
    (𝟙_ _) p q n h
    (((singularHomologyFunctor (ModuleCat.{w} k) n).map (λ_ (𝟙_ _)).hom).app (X' ⊗ Y'))
  rw [NatTrans.naturality] at hn
  simpa only [CategoryTheory.comp_apply, ModuleCat.MonoidalCategory.tensorHom_tmul,
    singularHomologyCrossBilinear_apply] using
      (congrArg (fun t ↦ t (a ⊗ₜ[k] b)) hn).symm

end TopCat
