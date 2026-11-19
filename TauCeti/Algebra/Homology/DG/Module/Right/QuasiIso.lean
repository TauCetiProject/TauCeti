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
Equivalently, a morphism `f` is a quasi-isomorphism exactly when every relative cycle `(x, y)`,
with `dM x = 0` and `f x = dN y`, is a relative boundary `(dM u, f u + dN v)`
(`TauCeti.DGRightModuleHom.isQuasiIso_iff_forall_exists`): this is the acyclicity of the
mapping cone of `f`, written on elements, and it is the form in which a quasi-isomorphism is
propagated along a filtration.

The quasi-isomorphisms form the morphism property `TauCeti.DGRightModuleCat.quasiIsos`, so that
roofs `M ← P → N` are Mathlib's right fractions for it.

## Main definitions

* `TauCeti.DGRightModuleHom.IsQuasiIso`, `TauCeti.DGRightModuleCat.IsQuasiIso`: quasi-isomorphisms.
* `TauCeti.DGRightModuleCat.quasiIsos h`: the quasi-isomorphisms, as a `MorphismProperty`.

## Main results

* `TauCeti.DGRightModuleHom.isQuasiIso_id`, `TauCeti.DGRightModuleHom.IsQuasiIso.comp`,
  `IsQuasiIso.of_comp_left`, `IsQuasiIso.of_comp_right`: identity, composition and two out of
  three.
* `TauCeti.DGRightModuleCat.IsQuasiIso.comp`, `TauCeti.DGRightModuleCat.isQuasiIso_of_isIso`:
  composites of quasi-isomorphisms and isomorphisms of bundled modules are quasi-isomorphisms.
* `TauCeti.DGRightModuleHom.IsQuasiIso.cohomologyLinearEquiv`: the induced isomorphism of
  cohomology.
* `TauCeti.DGRightModuleHom.isQuasiIso_of_homotopyInverse`,
  `TauCeti.DGRightModuleCat.isQuasiIso_of_homotopyInverse`: a morphism with a homotopy inverse
  over the ground ring is a quasi-isomorphism.
* `TauCeti.DGRightModuleHom.isQuasiIso_iff_forall_exists`: quasi-isomorphisms are the morphisms
  whose relative cycles are relative boundaries.
* `TauCeti.DGRightModuleHom.isQuasiIso_of_subsingleton`: a morphism between modules without
  nonzero elements is a quasi-isomorphism.
* `TauCeti.DGRightModuleHom.isQuasiIso_of_homotopyRetract`: a morphism is a quasi-isomorphism
  when it is, compatibly, a homotopy retract of a map whose relative cycles are relative
  boundaries.

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
    have hz : dM (z : M) = 0 := hM.mem_cycles.mp z.property
    refine ⟨g y - K z, ?_⟩
    have key := hK z
    rw [hz, map_zero, add_zero, ← hy, ← hg] at key
    rw [map_sub, key]
    abel
  · intro c
    obtain ⟨w, rfl⟩ := Submodule.Quotient.mk_surjective _ c
    have hw : dN (w : N) = 0 := hN.mem_cycles.mp w.property
    have hgw : g (w : N) ∈ hM.cycles := by
      rw [hM.mem_cycles, hg, hw, map_zero]
    refine ⟨Submodule.Quotient.mk ⟨g w, hgw⟩, ?_⟩
    rw [cohomologyMap_mk, Submodule.Quotient.eq, hN.mem_boundaries]
    refine ⟨L w, ?_⟩
    rw [Submodule.coe_sub, cyclesMap_apply_coe, hL, hw, map_zero, add_zero]
    abel

/-- **Quasi-isomorphisms on elements.** A morphism `f` of DG right modules is a
quasi-isomorphism exactly when every relative cycle is a relative boundary: whenever `dM x = 0`
and `f x = dN y`, there are `u` and `v` with `dM u = x` and `f u + dN v = y`. This is the
acyclicity of the mapping cone of `f`, written without constructing the cone. -/
theorem isQuasiIso_iff_forall_exists (f : DGRightModuleHom hM hN) :
    f.IsQuasiIso ↔ ∀ x y, dM x = 0 → f x = dN y → ∃ u v, dM u = x ∧ f u + dN v = y := by
  rw [isQuasiIso_iff]
  constructor
  · rintro ⟨hinj, hsurj⟩ x y hx hfx
    -- The cycle `x` has a boundary as image, so it is itself a boundary `dM u₀`.
    have hb : (⟨x, hM.mem_cycles.mpr hx⟩ : hM.cycles) ∈ hM.boundaries := by
      rw [← hM.quotientMk_eq_zero_iff]
      apply hinj
      rw [cohomologyMap_mk, map_zero, hN.quotientMk_eq_zero_iff, hN.mem_boundaries,
        cyclesMap_apply_coe]
      exact ⟨y, hfx.symm⟩
    obtain ⟨u₀, hu₀⟩ := hM.mem_boundaries.mp hb
    have hu₀' : dM u₀ = x := hu₀
    -- Then `y - f u₀` is a cycle, so it is `f c + dN v` for a cycle `c`.
    have hy : y - f u₀ ∈ hN.cycles := by
      rw [hN.mem_cycles, map_sub, map_d, hu₀', hfx, sub_self]
    obtain ⟨c, hc⟩ := hsurj (Submodule.Quotient.mk ⟨y - f u₀, hy⟩)
    obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ c
    rw [cohomologyMap_mk, Submodule.Quotient.eq, hN.mem_boundaries] at hc
    obtain ⟨v, hv⟩ := hc
    rw [Submodule.coe_sub, cyclesMap_apply_coe] at hv
    have hv' : dN v = f c - (y - f u₀) := hv
    refine ⟨u₀ + c, -v, ?_, ?_⟩
    · rw [map_add, hu₀', hM.mem_cycles.mp c.property, add_zero]
    · rw [map_add, map_neg, hv']
      abel
  · intro H
    constructor
    · rw [injective_iff_map_eq_zero]
      intro z hz
      obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ z
      rw [cohomologyMap_mk, hN.quotientMk_eq_zero_iff, hN.mem_boundaries, cyclesMap_apply_coe]
        at hz
      obtain ⟨y, hy⟩ := hz
      obtain ⟨u, -, hu, -⟩ := H z y (hM.mem_cycles.mp z.property) hy.symm
      rw [hM.quotientMk_eq_zero_iff, hM.mem_boundaries]
      exact ⟨u, hu⟩
    · intro w
      obtain ⟨w, rfl⟩ := Submodule.Quotient.mk_surjective _ w
      obtain ⟨u, v, hu, huv⟩ := H 0 w (map_zero dM) (by rw [map_zero, hN.mem_cycles.mp w.property])
      refine ⟨Submodule.Quotient.mk ⟨u, hM.mem_cycles.mpr hu⟩, ?_⟩
      rw [cohomologyMap_mk, Submodule.Quotient.eq, hN.mem_boundaries]
      refine ⟨-v, ?_⟩
      rw [Submodule.coe_sub, cyclesMap_apply_coe, map_neg, ← huv]
      exact (sub_add_cancel_left _ _).symm

/-- A morphism between DG right modules without nonzero elements is a quasi-isomorphism. -/
theorem isQuasiIso_of_subsingleton [Subsingleton M] [Subsingleton N]
    (f : DGRightModuleHom hM hN) : f.IsQuasiIso := by
  rw [isQuasiIso_iff_forall_exists]
  exact fun _ _ _ _ ↦ ⟨0, 0, Subsingleton.elim _ _, Subsingleton.elim _ _⟩

/-- **Quasi-isomorphisms through homotopy retracts.** Let `f₀ : M₀ → N₀` be a map of complexes
over the ground ring whose relative cycles are relative boundaries, as for a quasi-isomorphism
(`isQuasiIso_iff_forall_exists`). If `M` and `N` are homotopy retracts of `M₀` and `N₀`, through
chain maps `i : M → M₀` and `r : M₀ → M` with `r ∘ i = 1 + d K + K d`, and `f` commutes with `f₀`
along both `i` and `r`, then `f` is a quasi-isomorphism. Only the composite `r ∘ i` needs to be
homotopic to the identity, none of the maps `i`, `r`, `K` needs to be linear over the algebra,
and the homotopies need not be compatible with `f`. -/
theorem isQuasiIso_of_homotopyRetract (f : DGRightModuleHom hM hN)
    {M₀ N₀ : Type*} [AddCommGroup M₀] [Module R M₀] [AddCommGroup N₀] [Module R N₀]
    {dM₀ : M₀ →ₗ[R] M₀} {dN₀ : N₀ →ₗ[R] N₀} (f₀ : M₀ →ₗ[R] N₀)
    (h₀ : ∀ x y, dM₀ x = 0 → f₀ x = dN₀ y → ∃ u v, dM₀ u = x ∧ f₀ u + dN₀ v = y)
    (iM : M →ₗ[R] M₀) (rM : M₀ →ₗ[R] M) (KM : M →ₗ[R] M)
    (iN : N →ₗ[R] N₀) (rN : N₀ →ₗ[R] N) (KN : N →ₗ[R] N)
    (hiM : ∀ x, dM₀ (iM x) = iM (dM x)) (hrM : ∀ x, dM (rM x) = rM (dM₀ x))
    (hiN : ∀ y, dN₀ (iN y) = iN (dN y)) (hrN : ∀ y, dN (rN y) = rN (dN₀ y))
    (hKM : ∀ x, rM (iM x) = x + dM (KM x) + KM (dM x))
    (hKN : ∀ y, rN (iN y) = y + dN (KN y) + KN (dN y))
    (hi : ∀ x, iN (f x) = f₀ (iM x)) (hr : ∀ x, f (rM x) = rN (f₀ x)) : f.IsQuasiIso := by
  rw [isQuasiIso_iff_forall_exists]
  intro x y hx hfx
  -- Bound `x` by solving the problem for `f₀` and pulling the primitive back along `r`,
  -- corrected by the homotopy of `M`.
  obtain ⟨u₀, -, hu₀, -⟩ := h₀ (iM x) (iN y) (by rw [hiM, hx, map_zero])
    (by rw [← hi, hfx, hiN])
  have hu₁ : dM (rM u₀ - KM x) = x := by
    rw [map_sub, hrM, hu₀, hKM, hx, map_zero, add_zero, add_sub_cancel_right]
  -- The defect `y - f (r u₀ - K x)` is a cycle of `N`; solve for it in `N₀` and pull the
  -- solution back along `r`, corrected by the homotopy of `N`.
  have hw : dN (y - f (rM u₀ - KM x)) = 0 := by rw [map_sub, map_d, hu₁, hfx, sub_self]
  obtain ⟨c₀, v₀, hc₀, hcv₀⟩ := h₀ 0 (iN (y - f (rM u₀ - KM x))) (map_zero dM₀)
    (by rw [map_zero, hiN, hw, map_zero])
  have hv₀ : rN (f₀ c₀) + rN (dN₀ v₀) =
      y - f (rM u₀ - KM x) + dN (KN (y - f (rM u₀ - KM x))) := by
    rw [← map_add, hcv₀, hKN, hw, map_zero, add_zero]
  refine ⟨rM u₀ - KM x + rM c₀, rN v₀ - KN (y - f (rM u₀ - KM x)), ?_, ?_⟩
  · rw [map_add, hu₁, hrM, hc₀, map_zero, add_zero]
  · rw [map_add f, hr, map_sub dN, hrN, ← add_sub_assoc, add_assoc (f _), hv₀]
    abel

end DGRightModuleHom

namespace DGRightModuleCat

/-- A morphism of bundled DG right modules is a **quasi-isomorphism** when it induces a bijection
on cohomology. -/
abbrev IsQuasiIso {M N : DGRightModuleCat.{uR, uA, uM} h} (f : M ⟶ N) : Prop :=
  DGRightModuleHom.IsQuasiIso f

/-- **A morphism of bundled DG right modules with a homotopy inverse is a quasi-isomorphism.**
The inverse `g` and the homotopies `K` and `L`, with `g ∘ f = 1 + d K + K d` and
`f ∘ g = 1 + d L + L d`, need only be linear over the ground ring, and `g` must commute with the
differentials. This is `TauCeti.DGRightModuleHom.isQuasiIso_of_homotopyInverse` stated with the
differentials of the bundled modules, so that no instance search on their carriers is needed. -/
theorem isQuasiIso_of_homotopyInverse {M N : DGRightModuleCat.{uR, uA, uM} h} (f : M ⟶ N)
    (g : N →ₗ[R] M) (K : M →ₗ[R] M) (L : N →ₗ[R] N)
    (hg : ∀ y, M.differential (g y) = g (N.differential y))
    (hK : ∀ x, g (f x) = x + M.differential (K x) + K (M.differential x))
    (hL : ∀ y, f (g y) = y + N.differential (L y) + L (N.differential y)) : IsQuasiIso f :=
  DGRightModuleHom.isQuasiIso_of_homotopyInverse f g K L hg hK hL

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

/-- A morphism is a quasi-isomorphism exactly when its map on cohomology is an isomorphism. -/
theorem isQuasiIso_iff_isIso_cohomologyFunctor_map {M N : DGRightModuleCat.{uR, uA, uM} h}
    (f : M ⟶ N) : IsQuasiIso f ↔ IsIso (cohomologyFunctor.map f) :=
  (quasiIsos_iff f).symm

/-- A composite of quasi-isomorphisms of bundled DG right modules is a quasi-isomorphism. This is
`TauCeti.DGRightModuleHom.IsQuasiIso.comp` in diagrammatic order, stated for bundled modules so
that no instance search on their carriers is needed. -/
theorem IsQuasiIso.comp {M N P : DGRightModuleCat.{uR, uA, uM} h} {f : M ⟶ N} {g : N ⟶ P}
    (hf : IsQuasiIso f) (hg : IsQuasiIso g) : IsQuasiIso (f ≫ g) :=
  DGRightModuleHom.IsQuasiIso.comp hg hf

/-- An isomorphism of bundled DG right modules is a quasi-isomorphism. -/
theorem isQuasiIso_of_isIso {M N : DGRightModuleCat.{uR, uA, uM} h} (f : M ⟶ N) [IsIso f] :
    IsQuasiIso f :=
  (isQuasiIso_iff_isIso_cohomologyFunctor_map f).2 inferInstance

end DGRightModuleCat

end TauCeti
