/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.DG.Module.Right.Hom.Cohomology
public import TauCeti.Algebra.Homology.DG.Module.Right.Category

/-!
# Quasi-isomorphisms of differential graded right modules

A morphism of differential graded right modules is a **quasi-isomorphism** when it induces a
bijection on cohomology.  A morphism with an inverse up to homotopy, where the inverse and the
homotopies need only be linear over the ground ring and the inverse commute with the
differentials, is a quasi-isomorphism (`TauCeti.DGRightModuleHom.isQuasiIso_of_homotopyInverse`):
this is the form in which chain homotopy equivalences of underlying complexes are used.

A **roof of quasi-isomorphisms** `M ← P → N` (`TauCeti.DGRightModuleCat.QuasiIsoRoof`) records
two DG modules that are isomorphic in the derived category, through a specified zigzag.

## Main definitions

* `TauCeti.DGRightModuleHom.IsQuasiIso`, `TauCeti.DGRightModuleCat.IsQuasiIso`: quasi-isomorphisms.
* `TauCeti.DGRightModuleCat.QuasiIsoRoof M N`: a roof `M ← P → N` of quasi-isomorphisms.

## Main results

* `TauCeti.DGRightModuleHom.isQuasiIso_of_homotopyInverse`: a morphism with a homotopy inverse
  over the ground ring is a quasi-isomorphism.

## References

* B. Keller, *Deriving DG categories*, Section 3.
-/

public section

open CategoryTheory

namespace TauCeti

universe uR uA uM uN

variable {R : Type uR} {A : Type uA} [CommRing R] [Ring A] [Algebra R A]
  {𝒜 : ℤ → Submodule R A} [GradedAlgebra 𝒜] {d : A →ₗ[R] A}
  {h : IsDGAlgebra 𝒜 d}

namespace DGRightModuleHom

variable {M : Type uM} {N : Type uN}
  [AddCommGroup M] [Module R M] [Module Aᵐᵒᵖ M] [IsScalarTower R Aᵐᵒᵖ M]
  [AddCommGroup N] [Module R N] [Module Aᵐᵒᵖ N] [IsScalarTower R Aᵐᵒᵖ N]
  {ℳ : ℤ → Submodule R M} {𝒩 : ℤ → Submodule R N}
  [DirectSum.Decomposition ℳ] [DirectSum.Decomposition 𝒩]
  [SetLike.GradedSMul (InternalGrading.ofDecomposition 𝒜).opposite.piece ℳ]
  [SetLike.GradedSMul (InternalGrading.ofDecomposition 𝒜).opposite.piece 𝒩]
  {dM : M →ₗ[R] M} {dN : N →ₗ[R] N}
  {hM : IsDGRightModule h ℳ dM} {hN : IsDGRightModule h 𝒩 dN}

/-- A morphism of DG right modules is a **quasi-isomorphism** when it induces a bijection on
cohomology. -/
def IsQuasiIso (f : DGRightModuleHom hM hN) : Prop :=
  Function.Bijective f.cohomologyMap

/-- **A morphism with a homotopy inverse is a quasi-isomorphism.**  The inverse `g` and the
homotopies `K` and `L`, with `g ∘ f = 1 + d K + K d` and `f ∘ g = 1 + d L + L d`, need only be
linear over the ground ring, and `g` must commute with the differentials. -/
theorem isQuasiIso_of_homotopyInverse (f : DGRightModuleHom hM hN) (g : N →ₗ[R] M)
    (K : M →ₗ[R] M) (L : N →ₗ[R] N) (hg : ∀ y, dM (g y) = g (dN y))
    (hK : ∀ x, g (f x) = x + dM (K x) + K (dM x))
    (hL : ∀ y, f (g y) = y + dN (L y) + L (dN y)) : f.IsQuasiIso := by
  constructor
  · rw [injective_iff_map_eq_zero]
    intro c hc
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ c
    rw [cohomologyMap_mk, hN.quotientMk_eq_zero_iff, hN.mem_boundaries, cyclesMap_apply_coe]
      at hc
    obtain ⟨y, hy⟩ := hc
    rw [hM.quotientMk_eq_zero_iff, hM.mem_boundaries]
    have hz : dM (z : M) = 0 := hM.mem_cycles.mp z.2
    refine ⟨g y - K z, ?_⟩
    have key := hK z
    rw [hz, map_zero, add_zero, ← hy, ← hg] at key
    rw [map_sub, key]
    abel
  · intro c
    obtain ⟨w, rfl⟩ := Submodule.Quotient.mk_surjective _ c
    have hw : dN (w : N) = 0 := hN.mem_cycles.mp w.2
    have hgw : g (w : N) ∈ hM.cycles := by
      rw [hM.mem_cycles, hg, hw, map_zero]
    refine ⟨Submodule.Quotient.mk ⟨g w, hgw⟩, ?_⟩
    rw [cohomologyMap_mk, Submodule.Quotient.eq, hN.mem_boundaries]
    refine ⟨L w, ?_⟩
    rw [Submodule.coe_sub, cyclesMap_apply_coe, hL, hw, map_zero, add_zero]
    abel

end DGRightModuleHom

namespace DGRightModuleCat

/-- A morphism of bundled DG right modules is a **quasi-isomorphism** when it induces a bijection
on cohomology. -/
abbrev IsQuasiIso {M N : DGRightModuleCat.{uR, uA, uM} h} (f : M ⟶ N) : Prop :=
  DGRightModuleHom.IsQuasiIso f

/-- A **roof of quasi-isomorphisms** `M ← P → N` between DG right modules: two quasi-isomorphisms
out of a common DG module, which make `M` and `N` isomorphic in the derived category. -/
structure QuasiIsoRoof (M N : DGRightModuleCat.{uR, uA, uM} h) where
  /-- The common source of the two quasi-isomorphisms. -/
  apex : DGRightModuleCat.{uR, uA, uM} h
  /-- The quasi-isomorphism to `M`. -/
  left : apex ⟶ M
  /-- The quasi-isomorphism to `N`. -/
  right : apex ⟶ N
  /-- The map to `M` is a quasi-isomorphism. -/
  isQuasiIso_left : IsQuasiIso left
  /-- The map to `N` is a quasi-isomorphism. -/
  isQuasiIso_right : IsQuasiIso right

end DGRightModuleCat

end TauCeti
