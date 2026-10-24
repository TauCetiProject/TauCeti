/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import TauCeti.AlgebraicGeometry.Cohomology.HigherDirectImage.Basic
public import TauCeti.AlgebraicGeometry.Cohomology.OpenImmersion
import TauCeti.Algebra.Category.ModuleCat.Sheaf.FinitePresentation
import TauCeti.Algebra.Category.ModuleCat.Sheaf.Free.Basic
import TauCeti.AlgebraicGeometry.Cohomology.Flasque
import TauCeti.AlgebraicGeometry.Modules.Quasicoherent.Pushforward.Finite
import TauCeti.CategoryTheory.Sites.SheafCohomology.AcyclicResolution
import TauCeti.Topology.Sheaves.Exact

/-!
# Higher direct images along affine morphisms

Let `f : X ⟶ Y` be a morphism of schemes and `M` a sheaf of modules on `X`. The higher direct
image `R^{q+1} f_* M` vanishes as soon as the cohomology `H^{q+1}(f⁻¹ V, M)` vanishes for the
members `V` of a basis of the topology of `Y`
(`Scheme.Hom.isZero_higherDirectImage_succ_of_isBasis`). For an affine morphism `f` with locally
Noetherian source and a quasi-coherent `M`, the preimages of the affine opens of `Y` are affine
with Noetherian rings of sections, on which quasi-coherent sheaves have no higher cohomology. So
all positive higher direct images vanish
(`Scheme.Hom.isZero_higherDirectImage_succ_of_isAffineHom`). Consequently the higher direct
images of a coherent sheaf along a finite morphism to a locally Noetherian scheme are coherent:
the direct image is, and the higher ones are zero
(`Scheme.Hom.isFinitePresentation_higherDirectImage_of_isFinite`). This is the finite case of the
coherence of higher direct images along proper morphisms; neither the morphism nor the
coefficients need to be flat.

`R^q f_* M` is computed from an injective resolution `M ⟶ I^•` in the category of sheaves of
modules on `X`, as the homology of the complex `f_* I^•`. Its sections over an open `V` form the
complex `I^•(f⁻¹ V)`. The terms of `I^•` are flasque
(`AlgebraicGeometry.Scheme.Modules.isFlasque_of_injective`), so they are acyclic on every open,
and the complex `I^•(f⁻¹ V)` is exact in degree `q + 1` when `H^{q+1}(f⁻¹ V, M) = 0`
(`CategoryTheory.Sheaf.H'.exists_d_hom_app_eq_of_resolution`). Exactness of the complex of
sheaves `f_* I^•` can be checked on sections over a basis (`TopCat.Sheaf.exact_of_isBasis`).
This is the vanishing half of the description of `R^q f_* M` as the sheaf associated to
`V ↦ H^q(f⁻¹ V, M)`.

## Main declarations

* `AlgebraicGeometry.Scheme.Hom.isZero_higherDirectImage_succ_of_isBasis`: `R^{q+1} f_* M = 0`
  when `H^{q+1}(f⁻¹ V, M) = 0` for the members `V` of a basis of `Y`;
* `AlgebraicGeometry.Scheme.Hom.isZero_higherDirectImage_succ_of_isAffineHom`: positive higher
  direct images of quasi-coherent sheaves along affine morphisms with locally Noetherian source
  vanish;
* `AlgebraicGeometry.Scheme.Hom.isFinitePresentation_higherDirectImage_of_isFinite`: higher
  direct images of coherent sheaves along finite morphisms to locally Noetherian schemes are
  coherent.

## References

* R. Hartshorne, *Algebraic Geometry*, GTM 52, Springer, 1977, Proposition III.8.1 and
  Exercise III.8.2.
-/

public section

open CategoryTheory Limits TopologicalSpace AlgebraicGeometry

universe u

noncomputable section

namespace AlgebraicGeometry.Scheme.Hom

open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme.Modules

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- **Vanishing of higher direct images on a basis.** If the cohomology `H^{q+1}(f⁻¹ V, M)`
vanishes for every member `V` of a basis of the topology of `Y`, then the higher direct image
`R^{q+1} f_* M` vanishes. -/
theorem isZero_higherDirectImage_succ_of_isBasis (M : X.Modules) (q : ℕ) {B : Set Y.Opens}
    (hB : Opens.IsBasis B) (hM : ∀ V ∈ B, Subsingleton (cohomologyOn M (q + 1) (f ⁻¹ᵁ V))) :
    IsZero ((f.higherDirectImage (q + 1)).obj M) := by
  have := (Scheme.Modules.pushforward f).additive_of_preserves_binary_products
  let P := injectiveResolution M
  refine IsZero.of_iso ?_ (P.isoRightDerivedObj (Scheme.Modules.pushforward f) (q + 1))
  rw [HomologicalComplex.homologyFunctor_obj, ← HomologicalComplex.exactAt_iff_isZero_homology,
    HomologicalComplex.exactAt_iff' _ q (q + 1) (q + 2) (by simp) (by simp)]
  refine (toSheaf Y).reflects_exact_of_faithful _ (TopCat.Sheaf.exact_of_isBasis hB ?_)
  intro V hV s hs
  -- the image `K` of the resolution `I^•` under `toSheaf X` resolves the abelian sheaf of `M`,
  -- and its terms are flasque, hence acyclic on `f⁻¹ V`
  let K := ((toSheaf X).mapHomologicalComplex _).obj P.cocomplex
  have hι : (toSheaf X).map (P.ι.f 0) ≫ K.d 0 1 = 0 := by
    rw [Functor.mapHomologicalComplex_obj_d, ← Functor.map_comp, P.ι_f_zero_comp_complex_d,
      Functor.map_zero]
  have hι' : (ShortComplex.mk _ _ hι).Exact :=
    (ShortComplex.exact_of_f_is_kernel (S := ShortComplex.mk _ _ P.ι_f_zero_comp_complex_d)
      P.isLimitKernelFork).map (toSheaf X)
  have hK (j : ℕ) : K.ExactAt (j + 1) :=
    (K.exactAt_iff' j (j + 1) (j + 2) (by simp) (by simp)).2 ((P.exact_succ j).map (toSheaf X))
  have hKV (j k : ℕ) : Subsingleton ((K.X j).H' (k + 1) (f ⁻¹ᵁ V)) :=
    Scheme.Modules.subsingleton_cohomologyOn_succ_of_isFlasque (P.cocomplex.X j) k (f ⁻¹ᵁ V)
  have : Mono ((toSheaf X).map (P.ι.f 0)) := Functor.map_mono _ _
  -- the sections over `V` of `f_* I^•` are by definition the sections over `f⁻¹ V` of `I^•`
  exact Sheaf.H'.exists_d_hom_app_eq_of_resolution (K := K) ((toSheaf X).map (P.ι.f 0)) hι hι' hK
    (f ⁻¹ᵁ V) hKV q (hM V hV) s hs

/-- **Higher direct images along affine morphisms vanish.** For an affine morphism `f : X ⟶ Y`
with locally Noetherian source and a quasi-coherent sheaf `M` on `X`, every positive higher direct
image `R^{q+1} f_* M` vanishes. -/
theorem isZero_higherDirectImage_succ_of_isAffineHom [IsAffineHom f] [IsLocallyNoetherian X]
    (M : X.Modules) [M.IsQuasicoherent] (q : ℕ) :
    IsZero ((f.higherDirectImage (q + 1)).obj M) :=
  f.isZero_higherDirectImage_succ_of_isBasis M q Y.isBasis_affineOpens fun V hV ↦ by
    -- the preimage of an affine open is affine, with Noetherian ring of sections
    have hW : IsAffineOpen (f ⁻¹ᵁ V) := IsAffineOpen.preimage hV f
    have : IsNoetherianRing Γ(X, f ⁻¹ᵁ V) := IsLocallyNoetherian.component_noetherian ⟨_, hW⟩
    exact Scheme.Modules.subsingleton_cohomologyOn_succ_of_isAffineOpen M hW q

/-- **Higher direct images along finite morphisms are coherent.** For a finite morphism
`f : X ⟶ Y` to a locally Noetherian scheme and a quasi-coherent sheaf `M` of finite type on `X`,
every higher direct image `R^q f_* M` is finitely presented: in degree zero this is the coherence
of the direct image, and in positive degrees the higher direct images vanish. -/
theorem isFinitePresentation_higherDirectImage_of_isFinite [IsFinite f] [IsLocallyNoetherian Y]
    (M : X.Modules) [M.IsQuasicoherent] [M.IsFiniteType] (q : ℕ) :
    ((f.higherDirectImage q).obj M).IsFinitePresentation := by
  cases q with
  | zero =>
    exact (SheafOfModules.isFinitePresentation Y.ringCatSheaf).prop_of_iso
      ((f.higherDirectImageZeroIso).app M).symm inferInstance
  | succ q =>
    have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
    have hZ := TauCeti.SheafOfModules.isZero_free (S := Y.ringCatSheaf) PEmpty.{u + 1}
    exact (SheafOfModules.isFinitePresentation Y.ringCatSheaf).prop_of_iso
      (hZ.iso (f.isZero_higherDirectImage_succ_of_isAffineHom M q)) inferInstance

end AlgebraicGeometry.Scheme.Hom
