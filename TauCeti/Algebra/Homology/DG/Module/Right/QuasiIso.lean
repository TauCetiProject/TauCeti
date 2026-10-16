/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.ConcreteCategory.EpiMono
public import Mathlib.CategoryTheory.Localization.CalculusOfFractions
public import TauCeti.Algebra.Homology.DG.Module.Right.Hom.Cohomology

/-!
# Quasi-isomorphisms of differential graded right modules

A morphism of differential graded right modules is a **quasi-isomorphism** when it induces a
bijection on cohomology.  A morphism with an inverse up to homotopy, where the inverse and the
homotopies need only be linear over the ground ring and the inverse commute with the
differentials, is a quasi-isomorphism (`TauCeti.DGRightModuleHom.isQuasiIso_of_homotopyInverse`):
this is the form in which chain homotopy equivalences of underlying complexes are used.

The quasi-isomorphisms form the morphism property `TauCeti.DGRightModuleCat.quasiIsos`, so that
roofs `M ← P → N` are Mathlib's right fractions for it.

## Main definitions

* `TauCeti.DGRightModuleHom.IsQuasiIso`, `TauCeti.DGRightModuleCat.IsQuasiIso`: quasi-isomorphisms.
* `TauCeti.DGRightModuleCat.quasiIsos h`: the quasi-isomorphisms, as a `MorphismProperty`.

## Main results

* `TauCeti.DGRightModuleHom.isQuasiIso_id`, `TauCeti.DGRightModuleHom.IsQuasiIso.comp`,
  `IsQuasiIso.of_comp_left`, `IsQuasiIso.of_comp_right`: identity, composition and two out of
  three.
* `TauCeti.DGRightModuleHom.IsQuasiIso.cohomologyLinearEquiv`: the induced isomorphism of
  cohomology.
* `TauCeti.DGRightModuleHom.isQuasiIso_of_homotopyInverse`: a morphism with a homotopy inverse
  over the ground ring is a quasi-isomorphism.

## References

* B. Keller, *Deriving DG categories*, Section 3.
-/

public section

open CategoryTheory

namespace TauCeti

universe uR uA uM uN uP

variable {R : Type uR} {A : Type uA} [CommRing R] [Ring A] [Algebra R A]
  {𝒜 : ℤ → Submodule R A} [GradedAlgebra 𝒜] {d : A →ₗ[R] A}
  {h : IsDGAlgebra 𝒜 d}

namespace DGRightModuleHom

variable {M : Type uM} {N : Type uN} {P : Type uP}
  [AddCommGroup M] [Module R M] [Module Aᵐᵒᵖ M] [IsScalarTower R Aᵐᵒᵖ M]
  [AddCommGroup N] [Module R N] [Module Aᵐᵒᵖ N] [IsScalarTower R Aᵐᵒᵖ N]
  [AddCommGroup P] [Module R P] [Module Aᵐᵒᵖ P] [IsScalarTower R Aᵐᵒᵖ P]
  {ℳ : ℤ → Submodule R M} {𝒩 : ℤ → Submodule R N} {ℳP : ℤ → Submodule R P}
  [DirectSum.Decomposition ℳ] [DirectSum.Decomposition 𝒩] [DirectSum.Decomposition ℳP]
  [SetLike.GradedSMul (InternalGrading.ofDecomposition 𝒜).opposite.piece ℳ]
  [SetLike.GradedSMul (InternalGrading.ofDecomposition 𝒜).opposite.piece 𝒩]
  [SetLike.GradedSMul (InternalGrading.ofDecomposition 𝒜).opposite.piece ℳP]
  {dM : M →ₗ[R] M} {dN : N →ₗ[R] N} {dP : P →ₗ[R] P}
  {hM : IsDGRightModule h ℳ dM} {hN : IsDGRightModule h 𝒩 dN} {hP : IsDGRightModule h ℳP dP}

/-- A morphism of DG right modules is a **quasi-isomorphism** when it induces a bijection on
cohomology. -/
def IsQuasiIso (f : DGRightModuleHom hM hN) : Prop :=
  Function.Bijective f.cohomologyMap

/-- A morphism is a quasi-isomorphism exactly when its map on cohomology is bijective. -/
theorem isQuasiIso_iff (f : DGRightModuleHom hM hN) :
    f.IsQuasiIso ↔ Function.Bijective f.cohomologyMap :=
  Iff.rfl

/-- The identity is a quasi-isomorphism. -/
@[simp]
theorem isQuasiIso_id : (DGRightModuleHom.id hM).IsQuasiIso := by
  rw [isQuasiIso_iff, cohomologyMap_id]
  exact Function.bijective_id

/-- A composite of quasi-isomorphisms is a quasi-isomorphism. -/
theorem IsQuasiIso.comp {g : DGRightModuleHom hN hP} {f : DGRightModuleHom hM hN}
    (hg : g.IsQuasiIso) (hf : f.IsQuasiIso) : (g.comp f).IsQuasiIso := by
  rw [isQuasiIso_iff, cohomologyMap_comp, LinearMap.coe_comp]
  exact Function.Bijective.comp hg hf

/-- Two out of three: if `g` and `g ∘ f` are quasi-isomorphisms, so is `f`. -/
theorem IsQuasiIso.of_comp_left {g : DGRightModuleHom hN hP} {f : DGRightModuleHom hM hN}
    (hg : g.IsQuasiIso) (hgf : (g.comp f).IsQuasiIso) : f.IsQuasiIso := by
  rw [isQuasiIso_iff, cohomologyMap_comp, LinearMap.coe_comp] at hgf
  exact (Function.Bijective.of_comp_iff' hg _).1 hgf

/-- Two out of three: if `f` and `g ∘ f` are quasi-isomorphisms, so is `g`. -/
theorem IsQuasiIso.of_comp_right {g : DGRightModuleHom hN hP} {f : DGRightModuleHom hM hN}
    (hf : f.IsQuasiIso) (hgf : (g.comp f).IsQuasiIso) : g.IsQuasiIso := by
  rw [isQuasiIso_iff, cohomologyMap_comp, LinearMap.coe_comp] at hgf
  exact (Function.Bijective.of_comp_iff _ hf).1 hgf

/-- The isomorphism of cohomology induced by a quasi-isomorphism. -/
noncomputable def IsQuasiIso.cohomologyLinearEquiv {f : DGRightModuleHom hM hN}
    (hf : f.IsQuasiIso) : hM.Cohomology ≃ₗ[(h.Cohomology)ᵐᵒᵖ] hN.Cohomology :=
  LinearEquiv.ofBijective f.cohomologyMap hf

/-- The isomorphism of cohomology of a quasi-isomorphism is its map on cohomology. -/
@[simp]
theorem IsQuasiIso.cohomologyLinearEquiv_apply {f : DGRightModuleHom hM hN}
    (hf : f.IsQuasiIso) (x : hM.Cohomology) : hf.cohomologyLinearEquiv x = f.cohomologyMap x :=
  (rfl)

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

variable (h) in
/-- The **quasi-isomorphisms** of DG right modules over `h`, as a morphism property: the morphisms
sent to isomorphisms by the cohomology functor.  A roof `M ← P → N` whose left leg is a
quasi-isomorphism is a Mathlib right fraction `(quasiIsos h).RightFraction M N`. -/
def quasiIsos : MorphismProperty (DGRightModuleCat.{uR, uA, uM} h) :=
  (MorphismProperty.isomorphisms _).inverseImage cohomologyFunctor

/-- A morphism is in `quasiIsos` exactly when it is a quasi-isomorphism. -/
theorem quasiIsos_iff {M N : DGRightModuleCat.{uR, uA, uM} h} (f : M ⟶ N) :
    quasiIsos h f ↔ IsQuasiIso f := by
  rw [quasiIsos, MorphismProperty.inverseImage_iff, MorphismProperty.isomorphisms.iff,
    CategoryTheory.ConcreteCategory.isIso_iff_bijective]
  exact Iff.rfl

end DGRightModuleCat

end TauCeti
