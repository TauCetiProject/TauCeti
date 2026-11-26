/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Cohomology.Pullback.Resolution
public import TauCeti.AlgebraicGeometry.Cohomology.Flasque
public import TauCeti.AlgebraicGeometry.Modules.Restriction.Basic
import TauCeti.AlgebraicGeometry.Cohomology.InjectiveResolution

/-!
# Cohomology of an open as cohomology of the open subscheme

Let `W` be an open of a scheme `X` and `M` a sheaf of modules on `X`. Pullback along the inclusion
`W.ι : W ⟶ X`, followed by restriction to all of `W`, is a map
`Scheme.Opens.cohomologyOnPullbackι W M n : Hⁿ(W, M) ⟶ Hⁿ(W, M|_W)` from the cohomology of `M` over
the open `W` to the cohomology of the open subscheme `W` with coefficients in the pullback of `M`.
It is injective (`AlgebraicGeometry.Scheme.Opens.cohomologyOnPullbackι_injective`).

The target is a module over the global functions of the open subscheme `W`, which are the
functions on the open `W` of `X` (`AlgebraicGeometry.Scheme.Opens.topIso`). The library's
`Module` instance on the source `cohomologyOn M n W` is over the global functions `Γ(X, ⊤)`
only (`AlgebraicGeometry.Scheme.Modules.cohomologyOnModule`), so this map is how functions on `W`
are made to act on `Hⁿ(W, M)` here. On classes of sections of an injective resolution `P` of `M`,
the action is multiplication of sections
(`AlgebraicGeometry.Scheme.Opens.cohomologyOnPullbackι_resolutionClass_smul`), because pullback
along `W.ι` sends the class of a section of `P` to the class of its pullback
(`AlgebraicGeometry.Scheme.Opens.cohomologyOnPullbackι_resolutionClass`), and global functions act
on classes of sections by multiplication
(`AlgebraicGeometry.Scheme.Modules.cohomologyOnMap_globalSectionsSmul_resolutionClass`, in
`TauCeti.AlgebraicGeometry.Cohomology.InjectiveResolution`).

Module pullback along an open immersion is restriction, so it is exact
(`AlgebraicGeometry.Scheme.Hom.preservesLimits_pullback_of_isOpenImmersion`) and preserves
injective modules (`AlgebraicGeometry.Scheme.Modules.injective_pullback_obj_of_isOpenImmersion`).
-/

public section

open CategoryTheory Limits TopologicalSpace Opposite
open TauCeti.AlgebraicGeometry.Scheme.Modules

universe u

noncomputable section

namespace AlgebraicGeometry.Scheme.Opens

variable {X : Scheme.{u}} (W : X.Opens)

/-- Pullback `Hⁿ(W, M) ⟶ Hⁿ(W, M|_W)` from the cohomology of `M` over an open `W` of `X` to the
cohomology of the open subscheme `W` with coefficients in the pullback of `M` along the inclusion
`W.ι`: pullback on cohomology (`AlgebraicGeometry.Scheme.Hom.cohomologyOnPullback`), followed by
restriction from `W.ι⁻¹ W` to all of `W`. -/
def cohomologyOnPullbackι (M : X.Modules) (n : ℕ) :
    cohomologyOn M n W ⟶ cohomologyOn ((Scheme.Modules.pullback W.ι).obj M) n ⊤ :=
  W.ι.cohomologyOnPullback M n W ≫ cohomologyOnRes _ n W.ι_preimage_self.ge

/-- Unfolding `cohomologyOnPullbackι`: pullback on cohomology along `W.ι`, then restriction from
`W.ι⁻¹ W` to all of `W`. -/
lemma cohomologyOnPullbackι_def (M : X.Modules) (n : ℕ) :
    W.cohomologyOnPullbackι M n =
      W.ι.cohomologyOnPullback M n W ≫ cohomologyOnRes _ n W.ι_preimage_self.ge :=
  (rfl)

/-- `cohomologyOnPullbackι_def` evaluated at a class `x`. -/
lemma cohomologyOnPullbackι_apply (M : X.Modules) (n : ℕ) (x : cohomologyOn M n W) :
    W.cohomologyOnPullbackι M n x =
      cohomologyOnRes _ n W.ι_preimage_self.ge (W.ι.cohomologyOnPullback M n W x) :=
  (rfl)

/-- Pullback along the inclusion of an open `W` sends the class of a section `s` of the term `Pⁿ`
of an injective resolution to the class of the pullback of `s`, restricted to all of `W`. -/
lemma cohomologyOnPullbackι_resolutionClass {M : X.Modules} (P : InjectiveResolution M) {n : ℕ}
    (s : Γ(P.cocomplex.X n, W)) (hs : (P.cocomplex.d n (n + 1)).app W s = 0) :
    W.cohomologyOnPullbackι M n
        (CategoryTheory.Sheaf.H'.resolutionClass
          (K := ((toSheaf X).mapHomologicalComplex _).obj P.cocomplex) ((toSheaf X).map (P.ι.f 0))
          (CochainComplex.map_augmentation_comp_d _ P.ι_f_zero_comp_complex_d)
          (CochainComplex.map_augmentation_exact _ P.exact₀)
          (CochainComplex.map_exactAt_succ _ P.cocomplex_exactAt_succ) W s hs) =
      CategoryTheory.Sheaf.H'.resolutionClass
        (K := ((Scheme.Modules.pullback W.ι ⋙ toSheaf W).mapHomologicalComplex _).obj P.cocomplex)
        ((Scheme.Modules.pullback W.ι ⋙ toSheaf W).map (P.ι.f 0))
        (CochainComplex.map_augmentation_comp_d _ P.ι_f_zero_comp_complex_d)
        (CochainComplex.map_augmentation_exact _ P.exact₀)
        (CochainComplex.map_exactAt_succ _ P.cocomplex_exactAt_succ) ⊤
        (((Scheme.Modules.pullback W.ι).obj (P.cocomplex.X n)).presheaf.map
          (homOfLE W.ι_preimage_self.ge).op (W.ι.pullbackSections (P.cocomplex.X n) W s)) (by
          refine (ConcreteCategory.congr_hom (((Scheme.Modules.pullback W.ι).map
            (P.cocomplex.d n (n + 1))).mapPresheaf.naturality
              (homOfLE W.ι_preimage_self.ge).op) _).trans ?_
          -- The naturality square is stated for the underlying presheaf map `mapPresheaf`; its
          -- components are definitionally the `Hom.app` of the module map.
          change ((Scheme.Modules.pullback W.ι).obj (P.cocomplex.X (n + 1))).presheaf.map _
            (((Scheme.Modules.pullback W.ι).map (P.cocomplex.d n (n + 1))).app _
              (W.ι.pullbackSections (P.cocomplex.X n) W s)) = 0
          rw [W.ι.pullbackSections_naturality (M := P.cocomplex.X n) (U := W), hs, map_zero,
            map_zero]) := by
  refine (cohomologyOnPullbackι_apply W M n _).trans ?_
  refine (congrArg (cohomologyOnRes _ n _)
    (Scheme.Hom.cohomologyOnPullback_resolutionClass W.ι P W s hs)).trans ?_
  exact CategoryTheory.Sheaf.H'.cohomologyPresheaf_map_resolutionClass
    (K := ((Scheme.Modules.pullback W.ι ⋙ toSheaf W).mapHomologicalComplex _).obj P.cocomplex)
    ((Scheme.Modules.pullback W.ι ⋙ toSheaf W).map (P.ι.f 0))
    (CochainComplex.map_augmentation_comp_d _ P.ι_f_zero_comp_complex_d)
    (CochainComplex.map_augmentation_exact _ P.exact₀)
    (CochainComplex.map_exactAt_succ _ P.cocomplex_exactAt_succ) _ (homOfLE W.ι_preimage_self.ge) _
    _

/-- **Functions on `W` act through the open subscheme.** Pullback along the inclusion of an open
`W` sends the class in `Hⁿ(W, M)` of `a • s`, for a function `a` on `W` and a section `s` of a
term of an injective resolution of `M`, to `a • y`, where `y` is the image of the class of `s` and
`a` acts on `Hⁿ(W, M|_W)` as a global function of the open subscheme `W`. -/
lemma cohomologyOnPullbackι_resolutionClass_smul {M : X.Modules} (P : InjectiveResolution M)
    {n : ℕ} (a : Γ(X, W)) (s : Γ(P.cocomplex.X n, W)) (hs : (P.cocomplex.d n (n + 1)).app W s = 0) :
    W.cohomologyOnPullbackι M n
        (CategoryTheory.Sheaf.H'.resolutionClass
          (K := ((toSheaf X).mapHomologicalComplex _).obj P.cocomplex) ((toSheaf X).map (P.ι.f 0))
          (CochainComplex.map_augmentation_comp_d _ P.ι_f_zero_comp_complex_d)
          (CochainComplex.map_augmentation_exact _ P.exact₀)
          (CochainComplex.map_exactAt_succ _ P.cocomplex_exactAt_succ) W (a • s)
          (by
            -- The differential of the complex of abelian sheaves is, by definition, `Hom.app`
            -- of the module differential, which is linear over functions on `W`.
            change (P.cocomplex.d n (n + 1)).app W (a • s) = 0
            rw [Scheme.Modules.Hom.app_smul, hs, smul_zero])) =
      W.topIso.inv a • W.cohomologyOnPullbackι M n
        (CategoryTheory.Sheaf.H'.resolutionClass
          (K := ((toSheaf X).mapHomologicalComplex _).obj P.cocomplex) ((toSheaf X).map (P.ι.f 0))
          (CochainComplex.map_augmentation_comp_d _ P.ι_f_zero_comp_complex_d)
          (CochainComplex.map_augmentation_exact _ P.exact₀)
          (CochainComplex.map_exactAt_succ _ P.cocomplex_exactAt_succ) W s hs) := by
  have hsc : W.toScheme.presheaf.map (homOfLE W.ι_preimage_self.ge).op ((W.ι.app W).hom a) =
      W.toScheme.presheaf.map (⊤ : W.toScheme.Opens).leTop.op (W.topIso.inv a) := by
    simp only [Scheme.Opens.toScheme_presheaf_map, Scheme.Opens.ι_app, Scheme.Opens.topIso_inv]
    -- Both sides are restrictions of `a` along composites of inclusions of opens of `X`. The
    -- first map is applied through `CommRingCat.Hom.hom` and the others through
    -- `ConcreteCategory.hom`, which agree only up to unfolding, so `erw` is needed to combine the
    -- maps; the resulting inclusions of opens are then equal since `X.Opens` is a preorder.
    erw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, ← Functor.map_comp,
      ← Functor.map_comp]
    rfl
  refine (cohomologyOnPullbackι_resolutionClass W P (a • s) _).trans ?_
  rw [Scheme.Modules.cohomologyOn_smul_def]
  refine Eq.trans ?_ (congrArg _ (cohomologyOnPullbackι_resolutionClass W P s hs)).symm
  refine Eq.trans ?_ (Scheme.Modules.cohomologyOnMap_globalSectionsSmul_resolutionClass
    (Scheme.Modules.pullback W.ι) P ⊤ (W.topIso.inv a) _ _).symm
  congr 1
  rw [(W.ι.pullbackSections (P.cocomplex.X n) W).map_smulₛₗ, Scheme.Modules.map_smul]
  exact congrArg (· • _) hsc

/-- Pullback along the inclusion of an open `W` is injective on the cohomology of `W`. -/
theorem cohomologyOnPullbackι_injective (M : X.Modules) (n : ℕ) :
    Function.Injective (W.cohomologyOnPullbackι M n) := by
  let P := injectiveResolution M
  refine (injective_iff_map_eq_zero _).2 fun x hx ↦ ?_
  obtain ⟨s, hs, rfl⟩ := CategoryTheory.Sheaf.H'.resolutionClass_surjective
    (K := ((toSheaf X).mapHomologicalComplex _).obj P.cocomplex) ((toSheaf X).map (P.ι.f 0))
    (CochainComplex.map_augmentation_comp_d _ P.ι_f_zero_comp_complex_d)
    (CochainComplex.map_augmentation_exact _ P.exact₀)
    (CochainComplex.map_exactAt_succ _ P.cocomplex_exactAt_succ) W
    (fun j k ↦ Scheme.Modules.subsingleton_cohomologyOn_succ_of_isFlasque (P.cocomplex.X j) k W) x
  have hQ : ∀ j k, Subsingleton ((((Scheme.Modules.pullback W.ι ⋙ toSheaf W).mapHomologicalComplex
      _).obj P.cocomplex).X j |>.H' (k + 1) ⊤) := fun j k ↦
    Scheme.Modules.subsingleton_cohomologyOn_succ_of_isFlasque
      ((Scheme.Modules.pullback W.ι).obj (P.cocomplex.X j)) k ⊤
  have hx' := (cohomologyOnPullbackι_resolutionClass W P s hs).symm.trans hx
  have hP := fun j k ↦
    Scheme.Modules.subsingleton_cohomologyOn_succ_of_isFlasque (P.cocomplex.X j) k W
  cases n with
  | zero =>
    have h0 := (CategoryTheory.Sheaf.H'.resolutionClass_zero_eq_zero_iff _ _ _ _ _ _ _).1 hx'
    have hs0 : s = 0 := (Scheme.Modules.bijective_pullbackSectionsLE_ι (P.cocomplex.X 0) W ⊤
      rfl).1 ((Scheme.Hom.pullbackSectionsLE_apply W.ι _ W ⊤ _ s).trans
        (h0.trans (map_zero _).symm))
    exact (CategoryTheory.Sheaf.H'.resolutionClass_zero_eq_zero_iff _ _ _ _ _ _ _).2 hs0
  | succ m =>
    obtain ⟨t', ht'⟩ := (CategoryTheory.Sheaf.H'.resolutionClass_succ_eq_zero_iff _ _ _ _ ⊤ hQ
      _ _).1 hx'
    obtain ⟨t, rfl⟩ := (Scheme.Modules.bijective_pullbackSectionsLE_ι (P.cocomplex.X m) W ⊤
      rfl).2 t'
    refine (CategoryTheory.Sheaf.H'.resolutionClass_succ_eq_zero_iff _ _ _ _ W hP _ _).2
      ⟨t, (Scheme.Modules.bijective_pullbackSectionsLE_ι (P.cocomplex.X (m + 1)) W ⊤ rfl).1 ?_⟩
    exact (Scheme.Hom.pullbackSectionsLE_naturality _ _ _ _ _ _ _).symm.trans
      (ht'.trans (Scheme.Hom.pullbackSectionsLE_apply W.ι _ W ⊤ _ s).symm)

end AlgebraicGeometry.Scheme.Opens
