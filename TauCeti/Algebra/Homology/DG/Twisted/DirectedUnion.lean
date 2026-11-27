/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.DG.Module.Right.Category
public import TauCeti.Algebra.Homology.DG.Twisted.Coefficients
import TauCeti.Algebra.Homology.ModuleCat.Basic

/-!
# Twisted complexes of directed unions of DG modules

Let `m` be a twisting cocycle on a finite graded set `P`, so that every DG right module `M` has the
twisted complex `M ⊗ ⟨P⟩` (`TauCeti.TwistingCocycle.twistedCochainComplex`). Let `M` be the
directed union of injective morphisms `j k : N k ⟶ M` of DG right modules: every finite set of
elements of `M` lies in the image of one `j k`. An element of a twisted complex has finitely many
coefficients, so the twisted complex of `M` is the directed union of those of the `N k`, and
homology commutes with directed unions (`HomologicalComplex.exists_homologyMap_eq_of_injective`,
`HomologicalComplex.exists_homologyMap_eq_zero_of_injective`):

* every cohomology class of `M ⊗ ⟨P⟩` comes from some `N k ⊗ ⟨P⟩`
  (`TauCeti.TwistingCocycle.exists_homologyMap_twistedCochainComplexMap_eq`);
* a cohomology class of `N k ⊗ ⟨P⟩` which vanishes in `M ⊗ ⟨P⟩` already vanishes in some
  `N k' ⊗ ⟨P⟩` with `k ≤ k'`
  (`TauCeti.TwistingCocycle.exists_homologyMap_twistedCochainComplexMap_eq_zero`).

`TauCeti.Algebra.Homology.DG.Twisted.RowFinite.DirectedUnion` treats the row-finite twisted
complexes in the same way, and `TauCeti.Algebra.Homology.DG.Twisted.DirectLimit.Coefficients`
passes these statements to direct limits along continuation maps.

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, Theorem K and Corollary 4.17.
-/

public section

open CategoryTheory

namespace TauCeti

universe uR uA uM uP

variable {R : Type uR} {A : Type uA} [CommRing R] [Ring A] [Algebra R A]
  {𝒜 : ℤ → Submodule R A} [GradedAlgebra 𝒜] {d : A →ₗ[R] A} {h : IsDGAlgebra 𝒜 d}

namespace TwistingCocycle

variable {P : Type uP} [Fintype P] {ind : P → ℤ} (m : TwistingCocycle 𝒜 d P ind)
  {κ : Type*} {M : DGRightModuleCat.{uR, uA, uM} h} {N : κ → DGRightModuleCat.{uR, uA, uM} h}
  {j : ∀ k, N k ⟶ M} (hj : ∀ k, Function.Injective (j k))
  (hN : ∀ s : Finset M, ∃ k, ∀ x ∈ s, x ∈ Set.range (j k))

include hj hN in
/-- Every element of the twisted complex of a directed union of DG right modules comes from the
twisted complex of one of the pieces: it has finitely many coefficients. -/
private theorem exists_twistedCochainComplexMap_f_eq_of_directed (n : ℤ)
    (x : (m.twistedCochainComplex M.differential M.isDGRightModule).X n) :
    ∃ k x', (m.twistedCochainComplexMap (N k).isDGRightModule M.isDGRightModule (j k)).f n x' =
      x := by
  classical
  set g := (twistedCochainComplexXEquiv m.mem_graded m.twisting M.isDGRightModule n x : P → M)
  obtain ⟨k, hk⟩ := hN (Finset.univ.image g)
  exact ⟨k, m.exists_twistedCochainComplexMap_f_eq _ _ (hj k) x fun p ↦
    hk _ (Finset.mem_image_of_mem g (Finset.mem_univ p))⟩

include hj hN in
/-- **Every cohomology class of the twisted complex of a directed union comes from a piece.** Let
`M` be the directed union of injective morphisms `j k : N k ⟶ M` of DG right modules. Then every
cohomology class of the twisted complex `M ⊗ ⟨P⟩` is the image of a class of some `N k ⊗ ⟨P⟩`. -/
theorem exists_homologyMap_twistedCochainComplexMap_eq (n : ℤ)
    (z : (m.twistedCochainComplex M.differential M.isDGRightModule).homology n) :
    ∃ k, ∃ y : (m.twistedCochainComplex (N k).differential (N k).isDGRightModule).homology n,
      HomologicalComplex.homologyMap
        (m.twistedCochainComplexMap (N k).isDGRightModule M.isDGRightModule (j k)) n y = z :=
  HomologicalComplex.exists_homologyMap_eq_of_injective n _
    (fun k ↦ m.injective_twistedCochainComplexMap_f _ _ (hj k) _)
    (m.exists_twistedCochainComplexMap_f_eq_of_directed hj hN n) z

include hj hN in
/-- **A cohomology class of a piece which dies in a directed union dies in a later piece.** Let
`M` be the directed union of injective morphisms `j k : N k ⟶ M` of DG right modules, indexed by a
directed preorder and compatible with morphisms `t : N k ⟶ N k'` for `k ≤ k'`. If a cohomology
class of the twisted complex `N k ⊗ ⟨P⟩` maps to zero in `M ⊗ ⟨P⟩`, then it maps to zero in some
`N k' ⊗ ⟨P⟩` with `k ≤ k'`. -/
theorem exists_homologyMap_twistedCochainComplexMap_eq_zero [Preorder κ] [IsDirectedOrder κ]
    (t : ∀ ⦃k k'⦄, k ≤ k' → (N k ⟶ N k')) (ht : ∀ ⦃k k'⦄ (hkk' : k ≤ k'), t hkk' ≫ j k' = j k)
    {n : ℤ} {k : κ}
    (y : (m.twistedCochainComplex (N k).differential (N k).isDGRightModule).homology n)
    (hy : HomologicalComplex.homologyMap
      (m.twistedCochainComplexMap (N k).isDGRightModule M.isDGRightModule (j k)) n y = 0) :
    ∃ k', ∃ hkk' : k ≤ k', HomologicalComplex.homologyMap
      (m.twistedCochainComplexMap (N k).isDGRightModule (N k').isDGRightModule (t hkk')) n y =
        0 :=
  HomologicalComplex.exists_homologyMap_eq_zero_of_injective n
    (L := fun k ↦ m.twistedCochainComplex (N k).differential (N k).isDGRightModule)
    (fun k ↦ m.twistedCochainComplexMap _ _ (j k))
    (fun k ↦ m.injective_twistedCochainComplexMap_f _ _ (hj k) n) (CochainComplex.prev ℤ n)
    (P := (k ≤ ·)) (fun _ hkk' ↦ m.twistedCochainComplexMap _ _ (t hkk'))
    (fun _ hkk' ↦ by
      rw [← twistedCochainComplexMap_comp]
      exact congrArg (m.twistedCochainComplexMap _ _) (ht hkk'))
    (fun x ↦ by
      -- The coefficients of `x` lie in some piece, hence in every later piece above `k`.
      obtain ⟨k'', x'', rfl⟩ := m.exists_twistedCochainComplexMap_f_eq_of_directed hj hN _ x
      obtain ⟨k', hkk', hk''k'⟩ := directed_of (· ≤ ·) k k''
      refine ⟨k', hkk', (m.twistedCochainComplexMap _ _ (t hk''k')).f _ x'', ?_⟩
      rw [← ModuleCat.comp_apply, ← HomologicalComplex.comp_f, ← twistedCochainComplexMap_comp]
      exact congrArg (fun φ ↦ ((m.twistedCochainComplexMap _ _ φ).f _) x'') (ht hk''k'))
    y hy

end TwistingCocycle

end TauCeti
