/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.DG.Module.Right.Truncation
public import TauCeti.Algebra.Homology.DG.Twisted.DirectLimit.Basic
public import TauCeti.Algebra.Homology.DG.Twisted.DirectedUnion
public import TauCeti.Algebra.Homology.DG.Twisted.Functor
import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic

/-!
# Direct limits along continuation maps as functors of the coefficients

Let `S` be a continuation system over a preorder `ι` (`TauCeti.ContinuationSystem`): twisting
cocycles `m i` on finite sets of generators, connected by continuation cocycles which compose up
to homotopy. For a DG right module `M` the cohomology of the twisted complexes `M ⊗ ⟨P i⟩` forms a
functor on `ι` (`TauCeti.ContinuationSystem.homologyFunctor`), and its colimit is the direct limit
of the system, the algebraic shape of symplectic homology with DG coefficients.

This file makes the direct limit a functor of the coefficient module. A morphism `f : M ⟶ N` of DG
right modules, applied to every coefficient, commutes with the continuation maps, so it induces a
natural transformation of the cohomology functors
(`TauCeti.ContinuationSystem.homologyFunctorMap`); this makes the cohomology functors a functor of
the coefficients (`TauCeti.ContinuationSystem.coefficientHomologyFunctor`), and their colimit the
**direct-limit functor** `M ↦ colim_i H^n(M ⊗ ⟨P i⟩)`
(`TauCeti.ContinuationSystem.directLimitFunctor`).

The direct limit commutes with directed unions of coefficient modules. Let `M` be the directed
union of injective morphisms `j k : N k ⟶ M`: every finite set of elements of `M` lies in the image
of one `j k`. The cohomology of the twisted complex of `M` is then the directed union of that of
the `N k` (`TauCeti.TwistingCocycle.exists_homologyMap_twistedCochainComplexMap_eq`,
`TauCeti.TwistingCocycle.exists_homologyMap_twistedCochainComplexMap_eq_zero`). Over a filtered
`ι`, colimits of modules commute with these unions too:

* every element of the direct limit for `M` comes from the direct limit for some `N k`
  (`TauCeti.ContinuationSystem.exists_directLimitFunctor_map_eq`);
* an element of the direct limit for `N k` which vanishes in the direct limit for `M` already
  vanishes in the direct limit for some `N k'` with `k ≤ k'`
  (`TauCeti.ContinuationSystem.exists_directLimitFunctor_map_eq_zero`).

Over a DG algebra concentrated in nonpositive cohomological degrees, such as the chains on Moore
loops, the canonical truncations `τ^{≤ k} M` (`TauCeti.DGRightModuleCat.truncLE`) are such a
directed union, and each has cohomology bounded above, that is, homology bounded below. Hence a
natural transformation between the direct-limit functors of two continuation systems which is an
isomorphism on every DG right module with cohomology bounded above is an isomorphism on every DG
right module (`TauCeti.ContinuationSystem.isIso_app_of_forall_cohomologyGrading_eq_bot`).

Barraud, Damian, Humilière and Oancea prove their Viterbo isomorphism with DG coefficients
(Theorem K) through convergent index spectral sequences for coefficients with homology bounded
below, and pass to arbitrary DG local systems in their Corollary 4.17 through the good truncations,
which have homology bounded below. This file supplies that passage for comparisons whose two sides
are direct-limit functors of continuation systems over the same DG algebra. A comparison whose
sides are not of this form, such as one with the Morse side over the finite approximations `𝓛ʳQ`,
which changes the algebra by restriction of scalars, needs the abstract
`TauCeti.DGRightModuleCat.isIso_app_of_forall_cohomologyGrading_eq_bot` instead, with the
exhaustion conditions proved for that side.

## Main definitions

* `TauCeti.ContinuationSystem.homologyFunctorMap`: the natural transformation of cohomology
  functors induced by a morphism of coefficients.
* `TauCeti.ContinuationSystem.coefficientHomologyFunctor`: the cohomology functors of a
  continuation system as a functor of the coefficients.
* `TauCeti.ContinuationSystem.directLimitFunctor`: the direct limit as a functor of the
  coefficients.

## Main results

* `TauCeti.ContinuationSystem.exists_directLimitFunctor_map_eq`,
  `TauCeti.ContinuationSystem.exists_directLimitFunctor_map_eq_zero`: the direct limit along a
  continuation system over a filtered preorder of a directed union of coefficient modules is the
  directed union of the direct limits for the pieces.
* `TauCeti.ContinuationSystem.isIso_app_of_forall_cohomologyGrading_eq_bot`: a natural
  transformation between the direct-limit functors of two continuation systems extends from
  coefficients with cohomology bounded above to arbitrary coefficients.

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, Theorem K and Corollary 4.17.
-/

public section

open CategoryTheory CategoryTheory.Limits

namespace TauCeti

universe w w' uR uA uM uP

variable {R : Type uR} {A : Type uA} [CommRing R] [Ring A] [Algebra R A]
  {𝒜 : ℤ → Submodule R A} [GradedAlgebra 𝒜] {d : A →ₗ[R] A} {h : IsDGAlgebra 𝒜 d}

/-! ### The direct limit as a functor of the coefficients -/

namespace ContinuationSystem

variable {ι : Type w} [Preorder ι] (S : ContinuationSystem.{w, uR, uA, uP} 𝒜 d h ι)

/-- **The maps of cohomology functors induced by the coefficients.** A morphism `f : M ⟶ N` of DG
right modules, applied to every coefficient of the twisted complexes of a continuation system,
commutes with the continuation maps, so it is a natural transformation between the cohomology
functors with coefficients in `M` and in `N`. -/
noncomputable def homologyFunctorMap {M N : DGRightModuleCat.{uR, uA, uM} h} (f : M ⟶ N) (n : ℤ) :
    S.homologyFunctor M.isDGRightModule n ⟶ S.homologyFunctor N.isDGRightModule n where
  app i := HomologicalComplex.homologyMap (((S.m i).twistedCochainComplexFunctor h).map f) n
  -- The objects of the cohomology functors are the cohomology of the twisted complexes only up to
  -- unfolding, so `rw` and `simp` cannot rewrite with `homologyMap_comp` here; the composites are
  -- matched by unification instead.
  naturality _ _ g :=
    ((HomologicalComplex.homologyMap_comp _ _ n).symm.trans (congrArg
      (HomologicalComplex.homologyMap · n)
      (ContinuationCocycle.continuationHom_twistedCochainComplexMap M.isDGRightModule
        N.isDGRightModule (S.ν (leOfHom g)) f))).trans (HomologicalComplex.homologyMap_comp _ _ n)

@[simp]
theorem homologyFunctorMap_app {M N : DGRightModuleCat.{uR, uA, uM} h} (f : M ⟶ N) (n : ℤ)
    (i : ι) :
    (S.homologyFunctorMap f n).app i =
      HomologicalComplex.homologyMap (((S.m i).twistedCochainComplexFunctor h).map f) n :=
  (rfl)

@[simp]
theorem homologyFunctorMap_id (M : DGRightModuleCat.{uR, uA, uM} h) (n : ℤ) :
    S.homologyFunctorMap (𝟙 M) n = 𝟙 _ := by
  ext i : 2
  simp only [homologyFunctorMap_app, CategoryTheory.Functor.map_id,
    HomologicalComplex.homologyMap_id, NatTrans.id_app]
  rfl

@[simp]
theorem homologyFunctorMap_comp {M N L : DGRightModuleCat.{uR, uA, uM} h} (f : M ⟶ N)
    (g : N ⟶ L) (n : ℤ) :
    S.homologyFunctorMap (f ≫ g) n = S.homologyFunctorMap f n ≫ S.homologyFunctorMap g n := by
  ext i : 2
  simp only [homologyFunctorMap_app, CategoryTheory.Functor.map_comp,
    HomologicalComplex.homologyMap_comp, NatTrans.comp_app]
  rfl

/-- **The cohomology functors of a continuation system as a functor of the coefficients**:
`M ↦ (i ↦ H^n(M ⊗ ⟨P i⟩))`. The body is exposed: its objects are the cohomology functors, which the
statements about its maps need to unfold. -/
@[expose]
noncomputable def coefficientHomologyFunctor (n : ℤ) :
    DGRightModuleCat.{uR, uA, uM} h ⥤ ι ⥤ ModuleCat.{max uP uM} R where
  obj M := S.homologyFunctor M.isDGRightModule n
  map f := S.homologyFunctorMap f n
  map_id M := S.homologyFunctorMap_id M n
  map_comp f g := S.homologyFunctorMap_comp f g n

@[simp]
theorem coefficientHomologyFunctor_obj (n : ℤ) (M : DGRightModuleCat.{uR, uA, uM} h) :
    (S.coefficientHomologyFunctor n).obj M = S.homologyFunctor M.isDGRightModule n :=
  (rfl)

@[simp]
theorem coefficientHomologyFunctor_map (n : ℤ) {M N : DGRightModuleCat.{uR, uA, uM} h}
    (f : M ⟶ N) : (S.coefficientHomologyFunctor n).map f = S.homologyFunctorMap f n :=
  (rfl)

variable [HasColimitsOfShape ι (ModuleCat.{max uP uM} R)]

/-- **The direct limit of a continuation system as a functor of the coefficients**:
`M ↦ colim_i H^n(M ⊗ ⟨P i⟩)`, the colimit of the cohomology functor with coefficients in `M`. The
body is exposed: its objects are colimits, which the statements about its maps need to unfold. -/
@[expose]
noncomputable def directLimitFunctor (n : ℤ) :
    DGRightModuleCat.{uR, uA, uM} h ⥤ ModuleCat.{max uP uM} R :=
  S.coefficientHomologyFunctor n ⋙ colim

@[simp]
theorem directLimitFunctor_obj (n : ℤ) (M : DGRightModuleCat.{uR, uA, uM} h) :
    (S.directLimitFunctor n).obj M = colim.obj (S.homologyFunctor M.isDGRightModule n) :=
  (rfl)

@[simp]
theorem directLimitFunctor_map (n : ℤ) {M N : DGRightModuleCat.{uR, uA, uM} h} (f : M ⟶ N) :
    (S.directLimitFunctor n).map f = colim.map (S.homologyFunctorMap f n) :=
  (rfl)

/-- The direct limit of a morphism of coefficients is induced by the maps of cohomology at each
stage: Mathlib's `colimit.ι_map`, read through `directLimitFunctor`. The colimit instances are
hypotheses: instance search for the colimits of `ModuleCat.{max uP uM} R` gets stuck on universe
constraints, so callers supply them by hand. -/
@[reassoc]
theorem ι_directLimitFunctor_map (n : ℤ) {M N : DGRightModuleCat.{uR, uA, uM} h} (f : M ⟶ N)
    (i : ι) [HasColimit ((S.coefficientHomologyFunctor n).obj M)]
    [HasColimit ((S.coefficientHomologyFunctor n).obj N)] :
    colimit.ι ((S.coefficientHomologyFunctor n).obj M) i ≫ (S.directLimitFunctor n).map f =
      (S.homologyFunctorMap f n).app i ≫ colimit.ι ((S.coefficientHomologyFunctor n).obj N) i :=
  colimit.ι_map (S.homologyFunctorMap f n) i

/-- The direct limit of a morphism of coefficients is induced by the maps of cohomology at each
stage, on elements: Mathlib's `colimit.ι_map_apply`, read through `directLimitFunctor`. The colimit
instances are hypotheses: instance search for the colimits of `ModuleCat.{max uP uM} R` gets stuck
on universe constraints, so callers supply them by hand. -/
theorem directLimitFunctor_map_ι_apply (n : ℤ) {M N : DGRightModuleCat.{uR, uA, uM} h}
    (f : M ⟶ N) (i : ι) [HasColimit ((S.coefficientHomologyFunctor n).obj M)]
    [HasColimit ((S.coefficientHomologyFunctor n).obj N)]
    (y : ((S.coefficientHomologyFunctor n).obj M).obj i) :
    (S.directLimitFunctor n).map f (colimit.ι ((S.coefficientHomologyFunctor n).obj M) i y) =
      colimit.ι ((S.coefficientHomologyFunctor n).obj N) i
        (((S.coefficientHomologyFunctor n).map f).app i y) :=
  ConcreteCategory.congr_hom (S.ι_directLimitFunctor_map n f i) y

/-! ### Directed unions of coefficients -/

section DirectedUnion

variable [PreservesColimitsOfShape ι (forget (ModuleCat.{max uP uM} R))]
  {κ : Type*} {M : DGRightModuleCat.{uR, uA, uM} h} {N : κ → DGRightModuleCat.{uR, uA, uM} h}
  {j : ∀ k, N k ⟶ M} (hj : ∀ k, Function.Injective (j k))
  (hN : ∀ s : Finset M, ∃ k, ∀ x ∈ s, x ∈ Set.range (j k))

include hj hN in
/-- **Every element of the direct limit for a directed union comes from a piece.** Let `M` be the
directed union of injective morphisms `j k : N k ⟶ M` of DG right modules. Then every element of
the direct limit `colim_i H^n(M ⊗ ⟨P i⟩)` is the image of an element of the direct limit for some
`N k`. -/
theorem exists_directLimitFunctor_map_eq (n : ℤ) (x : (S.directLimitFunctor n).obj M) :
    ∃ k, ∃ y : (S.directLimitFunctor n).obj (N k), (S.directLimitFunctor n).map (j k) y = x := by
  -- Instance search for the colimits of `ModuleCat.{max uP uM} R` gets stuck on universe
  -- constraints, so the instances are supplied by hand.
  have (L : DGRightModuleCat.{uR, uA, uM} h) :
      HasColimit ((S.coefficientHomologyFunctor n).obj L) := HasColimitsOfShape.has_colimit _
  have : PreservesColimit ((S.coefficientHomologyFunctor n).obj M) (forget _) :=
    PreservesColimitsOfShape.preservesColimit
  obtain ⟨i, z, rfl⟩ := Concrete.colimit_exists_rep ((S.coefficientHomologyFunctor n).obj M) x
  obtain ⟨k, y, rfl⟩ := (S.m i).exists_homologyMap_twistedCochainComplexMap_eq hj hN n z
  exact ⟨k, colimit.ι ((S.coefficientHomologyFunctor n).obj (N k)) i y,
    S.directLimitFunctor_map_ι_apply n (j k) i y⟩

include hj hN in
/-- **An element of the direct limit for a piece which dies in a directed union dies in a later
piece.** Let `M` be the directed union of injective morphisms `j k : N k ⟶ M` of DG right
modules, indexed by a directed preorder and compatible with morphisms `t : N k ⟶ N k'` for
`k ≤ k'`, and let the continuation system be indexed by a filtered preorder. If an element of the
direct limit for `N k` maps to zero in the direct limit for `M`, then it maps to zero in the direct
limit for some `N k'` with `k ≤ k'`: it vanishes in the cohomology of some stage `i'` of the
system, and there in the cohomology of some `N k' ⊗ ⟨P i'⟩`. -/
theorem exists_directLimitFunctor_map_eq_zero [IsFiltered ι] [Preorder κ] [IsDirectedOrder κ]
    (t : ∀ ⦃k k'⦄, k ≤ k' → (N k ⟶ N k')) (ht : ∀ ⦃k k'⦄ (hkk' : k ≤ k'), t hkk' ≫ j k' = j k)
    {n : ℤ} {k : κ} (y : (S.directLimitFunctor n).obj (N k))
    (hy : (S.directLimitFunctor n).map (j k) y = 0) :
    ∃ k', ∃ hkk' : k ≤ k', (S.directLimitFunctor n).map (t hkk') y = 0 := by
  -- Instance search for the colimits of `ModuleCat.{max uP uM} R` gets stuck on universe
  -- constraints, so the instances are supplied by hand.
  have (L : DGRightModuleCat.{uR, uA, uM} h) :
      HasColimit ((S.coefficientHomologyFunctor n).obj L) := HasColimitsOfShape.has_colimit _
  have : PreservesColimit ((S.coefficientHomologyFunctor n).obj M) (forget _) :=
    PreservesColimitsOfShape.preservesColimit
  have : PreservesColimit ((S.coefficientHomologyFunctor n).obj (N k)) (forget _) :=
    PreservesColimitsOfShape.preservesColimit
  obtain ⟨i, z, rfl⟩ := Concrete.colimit_exists_rep ((S.coefficientHomologyFunctor n).obj (N k)) y
  rw [S.directLimitFunctor_map_ι_apply] at hy
  have hy' : colimit.ι ((S.coefficientHomologyFunctor n).obj M) i
      (((S.coefficientHomologyFunctor n).map (j k)).app i z) =
        colimit.ι ((S.coefficientHomologyFunctor n).obj M) i 0 :=
    hy.trans (map_zero _).symm
  obtain ⟨i', g, g', hg⟩ := (Concrete.colimit_rep_eq_iff_exists _ _ _).1 hy'
  -- The image of `z` at the stage `i'` already dies in the cohomology with coefficients in `M`.
  rw [map_zero, ← NatTrans.naturality_apply] at hg
  obtain ⟨k', hkk', hk'⟩ := (S.m i').exists_homologyMap_twistedCochainComplexMap_eq_zero hj hN t ht
    (((S.coefficientHomologyFunctor n).obj (N k)).map g z) hg
  refine ⟨k', hkk', ?_⟩
  rw [S.directLimitFunctor_map_ι_apply, ← colimit.w_apply _ g, ← NatTrans.naturality_apply]
  exact (congrArg _ hk').trans (map_zero _)

end DirectedUnion

/-! ### Extension from bounded coefficients -/

section Truncation

variable [PreservesColimitsOfShape ι (forget (ModuleCat.{max uP uM} R))]
  (h𝒜 : ∀ n, 0 < n → 𝒜 n = ⊥)

include h𝒜 in
/-- Every element of the direct limit for a DG right module over a nonpositively graded DG algebra
comes from the direct limit for one of its canonical truncations. -/
theorem exists_directLimitFunctor_map_ιTruncLE_eq (n : ℤ) {M : DGRightModuleCat.{uR, uA, uM} h}
    (x : (S.directLimitFunctor n).obj M) :
    ∃ k, ∃ y : (S.directLimitFunctor n).obj (M.truncLE h𝒜 k),
      (S.directLimitFunctor n).map (M.ιTruncLE h𝒜 k) y = x :=
  S.exists_directLimitFunctor_map_eq (fun k ↦ M.ιTruncLE_injective k)
    (M.exists_forall_mem_range_ιTruncLE (h𝒜 := h𝒜)) n x

include h𝒜 in
/-- An element of the direct limit for a canonical truncation `τ^{≤ k} M` of a DG right module
over a nonpositively graded DG algebra which vanishes in the direct limit for `M` already vanishes
in the direct limit for some `τ^{≤ k'} M` with `k ≤ k'`. -/
theorem exists_directLimitFunctor_map_truncLEInclusion_eq_zero [IsFiltered ι] {n : ℤ}
    {M : DGRightModuleCat.{uR, uA, uM} h} {k : ℤ}
    (y : (S.directLimitFunctor n).obj (M.truncLE h𝒜 k))
    (hy : (S.directLimitFunctor n).map (M.ιTruncLE h𝒜 k) y = 0) :
    ∃ k', ∃ hkk' : k ≤ k', (S.directLimitFunctor n).map (M.truncLEInclusion h𝒜 hkk') y = 0 :=
  S.exists_directLimitFunctor_map_eq_zero (fun k ↦ M.ιTruncLE_injective k)
    (M.exists_forall_mem_range_ιTruncLE (h𝒜 := h𝒜))
    (fun _ _ hkk' ↦ M.truncLEInclusion h𝒜 hkk') (fun _ _ hkk' ↦ M.truncLEInclusion_ιTruncLE hkk')
    y hy

include h𝒜 in
/-- **Comparisons of direct limits extend from bounded-below to arbitrary coefficients.** Over a DG
algebra concentrated in nonpositive cohomological degrees, let `S` and `S'` be continuation systems,
`S'` over a filtered preorder, and let `α` be a natural transformation between their direct-limit
functors in degrees `n` and `n'`. If `α` is an isomorphism on every DG right module whose
cohomology vanishes above some degree, then it is an isomorphism on every DG right module.

This is the passage from DG local systems with homology bounded below to all DG local systems in
Corollary 4.17 of Barraud, Damian, Humilière and Oancea, for comparisons both of whose sides are
direct-limit functors of continuation systems over `𝒜`. It does not apply to sides of another
form, such as the Morse side over the finite approximations `𝓛ʳQ`; for those, use
`TauCeti.DGRightModuleCat.isIso_app_of_forall_cohomologyGrading_eq_bot` directly. -/
theorem isIso_app_of_forall_cohomologyGrading_eq_bot {ι' : Type w'} [Preorder ι']
    [IsFiltered ι'] (S' : ContinuationSystem.{w', uR, uA, uP} 𝒜 d h ι')
    [HasColimitsOfShape ι' (ModuleCat.{max uP uM} R)]
    [PreservesColimitsOfShape ι' (forget (ModuleCat.{max uP uM} R))] {n n' : ℤ}
    (α : S.directLimitFunctor.{w, uR, uA, uM} n ⟶ S'.directLimitFunctor n')
    (hα : ∀ N : DGRightModuleCat.{uR, uA, uM} h,
      (∃ k, ∀ p, k < p → N.isDGRightModule.cohomologyGrading p = ⊥) → IsIso (α.app N))
    (M : DGRightModuleCat.{uR, uA, uM} h) :
    IsIso (α.app M) :=
  DGRightModuleCat.isIso_app_of_forall_cohomologyGrading_eq_bot α hα
    (S.exists_directLimitFunctor_map_ιTruncLE_eq h𝒜 n)
    (S'.exists_directLimitFunctor_map_ιTruncLE_eq h𝒜 n')
    fun _ ↦ S'.exists_directLimitFunctor_map_truncLEInclusion_eq_zero h𝒜

end Truncation

end ContinuationSystem

end TauCeti
