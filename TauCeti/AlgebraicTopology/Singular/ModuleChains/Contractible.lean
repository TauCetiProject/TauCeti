/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Algebra.Homology.SingleHomology
public import TauCeti.AlgebraicTopology.Singular.Contractible
public import TauCeti.AlgebraicTopology.Singular.ModuleChains.Basic

/-!
# Acyclicity of the singular chains of a contractible space

The singular homology of a contractible space vanishes in positive degrees, and the reduced
homology of a path-connected space vanishes in degree zero.  For chains with coefficients in a
ring, this file states these facts on elements: a cycle of positive degree is a boundary, and a
`0`-chain of augmentation zero is a boundary.  It also states them for the whole complex: the
augmented singular chain complex of a contractible space is exact, that is, the augmentation onto
the coefficient ring in degree `0` is a quasi-isomorphism (a `QuasiIso` instance).

## Main results

* `TauCeti.singularChains_exists_d_eq_of_d_eq_zero`: positive-degree cycles of a contractible
  space are boundaries.
* `TauCeti.singularChains_exists_d_eq_of_augment_eq_zero`: `0`-chains of augmentation zero of a
  path-connected space are boundaries.
* `TauCeti.quasiIso_singularChainsAugmentation`: the augmented singular chain complex of a
  contractible space is exact.
-/

public section

noncomputable section

open CategoryTheory Limits AlgebraicTopology Simplicial

universe u

namespace TauCeti

variable {k : Type u} [Ring k]

/-- The positive-degree cycles of the simplicial singular chains of a contractible space are
boundaries. -/
theorem singularChains_exists_d_eq_of_d_eq_zero (X : TopCat.{u}) [ContractibleSpace X] (q : ℕ)
    (z : ((singularChains k).obj X).X (q + 1))
    (hz : ((singularChains k).obj X).d (q + 1) q z = 0) :
    ∃ b, ((singularChains k).obj X).d (q + 2) (q + 1) b = z := by
  have hzero := isZero_singularHomologyFunctor_of_contractibleSpace (C := ModuleCat.{u} k)
    (ModuleCat.of k k) X (n := q + 1) (Nat.succ_ne_zero q)
  have hexact : ((singularChains k).obj X).ExactAt (q + 1) :=
    (HomologicalComplex.exactAt_iff_isZero_homology _ _).2 hzero
  rw [HomologicalComplex.exactAt_iff' _ (q + 2) (q + 1) q (by simp) (by simp),
    ShortComplex.moduleCat_exact_iff] at hexact
  exact hexact z hz

/-- In a connected simplicial set, the map from `0`-chains to the coproduct over the path
components followed by the codiagonal is the augmentation, and the codiagonal is injective. -/
private theorem singularAugment_eq_zero {X : TopCat.{u}} [PathConnectedSpace X]
    {z : ((TopCat.toSSet.obj X).chainComplex (ModuleCat.of k k)).X 0}
    (hz : singularAugment k X z = 0) :
    SSet.π₀.fromChainComplexXZero (TopCat.toSSet.obj X) (ModuleCat.of k k) z = 0 := by
  let D : (∐ fun _ : (TopCat.toSSet.obj X).π₀ ↦ ModuleCat.of k k) ⟶ ModuleCat.of k k :=
    Sigma.desc fun _ ↦ 𝟙 _
  have hD : SSet.π₀.fromChainComplexXZero (TopCat.toSSet.obj X) (ModuleCat.of k k) ≫ D =
      ModuleCat.ofHom (singularAugment k X) := by
    refine SSet.chainComplex_hom_ext fun σ ↦ ModuleCat.hom_ext (LinearMap.ext_ring ?_)
    simp only [SSet.π₀.comp_fromChainComplexXZero_assoc, Sigma.ι_comp_desc, D]
    exact (singularAugment_simplexChain X σ 1).symm
  obtain ⟨c⟩ : Nonempty (TopCat.toSSet.obj X).π₀ := inferInstance
  let ιc : ModuleCat.of k k ⟶ ∐ fun _ : (TopCat.toSSet.obj X).π₀ ↦ ModuleCat.of k k :=
    Sigma.ι (fun _ : (TopCat.toSSet.obj X).π₀ ↦ ModuleCat.of k k) c
  have hsec : D ≫ ιc = 𝟙 _ := by
    refine Sigma.hom_ext _ _ fun c' ↦ ?_
    obtain rfl : c = c' := Subsingleton.elim _ _
    simp [D, ιc]
  set w := SSet.π₀.fromChainComplexXZero (TopCat.toSSet.obj X) (ModuleCat.of k k) z
  have h1 : D w = 0 := by
    have := congrArg (fun g ↦ g.hom z) hD
    simp only [ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply] at this
    exact this.trans hz
  calc w = (D ≫ ιc) w := by rw [hsec]; rfl
    _ = 0 := by rw [ModuleCat.comp_apply, h1, map_zero]

/-- A `0`-chain of augmentation zero of the simplicial singular chains of a path-connected space
is a boundary. -/
theorem singularChains_exists_d_eq_of_augment_eq_zero (X : TopCat.{u}) [PathConnectedSpace X]
    (z : ((singularChains k).obj X).X 0) (hz : singularAugment k X z = 0) :
    ∃ b, ((singularChains k).obj X).d 1 0 b = z := by
  have hexact := ShortComplex.exact_of_g_is_cokernel
    (ShortComplex.mk _ _ (SSet.π₀.d_fromChainComplexXZero (TopCat.toSSet.obj X)
      (ModuleCat.of k k) 1))
    (SSet.isColimitCokernelCoforkChainComplexDOneZero _ _)
  rw [ShortComplex.moduleCat_exact_iff] at hexact
  exact hexact z (singularAugment_eq_zero hz)

variable (k) in
/-- **The augmented singular chain complex of a contractible space is exact**: the augmentation
is a quasi-isomorphism onto the coefficient ring in degree `0`. -/
instance quasiIso_singularChainsAugmentation (X : TopCat.{u}) [ContractibleSpace X] :
    QuasiIso (singularChainsAugmentation k X) where
  quasiIsoAt m := by
    cases m with
    | zero =>
      rw [ChainComplex.quasiIsoAt₀_iff,
        ShortComplex.quasiIso_iff_of_zeros' _ (by simp) rfl rfl]
      have hε : ((singularChains k).obj X).d 1 0 ≫ ModuleCat.ofHom (singularAugment k X) = 0 := by
        ext x
        exact singularAugment_d X x
      have hex : (ShortComplex.mk _ _ hε).Exact := by
        rw [ShortComplex.moduleCat_exact_iff]
        exact fun z hz ↦ singularChains_exists_d_eq_of_augment_eq_zero X z hz
      obtain ⟨x⟩ := (inferInstance : Nonempty X)
      refine ⟨(ShortComplex.exact_iff_of_iso ?_).1 hex, ?_⟩
      · exact ShortComplex.isoMk (Iso.refl _) (Iso.refl _)
          (HomologicalComplex.singleObjXSelf (ComplexShape.down ℕ) 0 _).symm (by simp)
          (by
            simp only [HomologicalComplex.shortComplexFunctor'_map_τ₂, Iso.refl_hom,
              singularChainsAugmentation_f_zero, ChainComplex.single₀ObjXSelf]
            exact (Category.comp_id _).symm)
      · rw [HomologicalComplex.shortComplexFunctor'_map_τ₂, singularChainsAugmentation_f_zero]
        -- In degree `0` the single complex is `k` by definition, so an element of it is a scalar.
        exact (ModuleCat.epi_iff_surjective _).2 fun (a : k) ↦
          ⟨simplexChain (TopCat.toSSetObj₀Equiv.symm x) a, singularAugment_simplexChain X _ a⟩
    | succ m =>
      rw [quasiIsoAt_iff_exactAt' (hL := ChainComplex.exactAt_succ_single_obj ..)]
      exact (HomologicalComplex.exactAt_iff_isZero_homology _ _).2
        (isZero_singularHomologyFunctor_of_contractibleSpace (ModuleCat.of k k) X
          (Nat.succ_ne_zero m))

end TauCeti
