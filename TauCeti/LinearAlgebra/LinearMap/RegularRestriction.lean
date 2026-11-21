/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import TauCeti.LinearAlgebra.LinearMap.Ker
public import TauCeti.LinearAlgebra.LinearMap.Range

/-!
# Kernels and cokernels of regular restrictions

Let `f : M → N` and `g : M' → N'` be linear maps and `e : M → M'`, `e' : N → N'` injective linear
maps with `e' ∘ f = g ∘ e`. Think of `f` as the restriction of `g` to subspaces of more regular
elements, for instance a differential operator acting on `C¹` maps and on Sobolev maps. Then `e`
sends the kernel of `f` into the kernel of `g`, and `e'` induces a map of cokernels
`N ⧸ range f → N' ⧸ range g`. Call `g` *regular* with respect to the square when `g x ∈ range e'`
implies `x ∈ range e`, as elliptic regularity says for elliptic operators. This file shows:

* for regular `g`, `e` restricts to an isomorphism of kernels (`LinearMap.kerEquivOfRegular`) and
  the map of cokernels is injective (`LinearMap.injective_mapQ_of_regular`);
* the map of cokernels is onto exactly when `range e' ⊔ range g = ⊤`
  (`LinearMap.surjective_mapQ_iff_sup_range_eq_top`), and then it is an isomorphism
  (`LinearMap.cokerEquivOfRegular`). Over a division ring this holds as soon as the cokernel of
  `g` is finite-dimensional, of dimension at most that of the cokernel of `f`
  (`LinearMap.sup_range_eq_top_of_finrank_le`), since an injective map into a finite-dimensional
  space of no larger dimension is onto. For Fredholm operators this dimension condition comes from
  an index computation.

So kernels and cokernels, and hence determinant lines, computed in different function spaces
agree. When `e` and `e'` are linear isomorphisms the square is regular and these are the
isomorphisms `LinearMap.kerEquivOfComp` and `LinearMap.cokerEquivOfComp`.
-/

public section

namespace LinearMap

variable {R : Type*} [Ring R] {M N M' N' : Type*} [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N] [AddCommGroup M'] [Module R M'] [AddCommGroup N'] [Module R N']
  {f : M →ₗ[R] N} {g : M' →ₗ[R] N'} {e : M →ₗ[R] M'} {e' : N →ₗ[R] N'}

/-- **Kernels of a regular restriction.** Let `e' ∘ f = g ∘ e` with `e` and `e'` injective, and
let `g` be regular: `g x ∈ range e'` implies `x ∈ range e`. Then `e` restricts to a linear
equivalence from the kernel of `f` onto the kernel of `g`. -/
noncomputable def kerEquivOfRegular (h : e' ∘ₗ f = g ∘ₗ e) (he : Function.Injective e)
    (he' : Function.Injective e') (hreg : ∀ x, g x ∈ range e' → x ∈ range e) :
    ker f ≃ₗ[R] ker g :=
  LinearEquiv.ofBijective (e.restrict fun _ hx ↦ map_mem_ker_of_comp_eq e h hx) <| by
    refine ⟨fun x y hxy ↦ Subtype.ext (he (congrArg Subtype.val hxy)), fun x ↦ ?_⟩
    obtain ⟨y, hy⟩ := hreg x (by rw [mem_ker.mp x.property]; exact zero_mem _)
    refine ⟨⟨y, he' ?_⟩, Subtype.ext hy⟩
    rw [map_zero, ← comp_apply, h, comp_apply, hy, mem_ker.mp x.property]

@[simp]
theorem coe_kerEquivOfRegular_apply (h : e' ∘ₗ f = g ∘ₗ e) (he : Function.Injective e)
    (he' : Function.Injective e') (hreg : ∀ x, g x ∈ range e' → x ∈ range e) (x : ker f) :
    (kerEquivOfRegular h he he' hreg x : M') = e x :=
  (rfl)

@[simp]
theorem apply_coe_kerEquivOfRegular_symm_apply (h : e' ∘ₗ f = g ∘ₗ e)
    (he : Function.Injective e) (he' : Function.Injective e')
    (hreg : ∀ x, g x ∈ range e' → x ∈ range e) (x : ker g) :
    e ((kerEquivOfRegular h he he' hreg).symm x : M) = x := by
  rw [← coe_kerEquivOfRegular_apply h he he' hreg, LinearEquiv.apply_symm_apply]

/-- The map of cokernels induced by `e'` in a commuting square `e' ∘ f = g ∘ e` is injective when
`e'` is injective and `g` is regular: `g x ∈ range e'` implies `x ∈ range e`. -/
theorem injective_mapQ_of_regular (h : e' ∘ₗ f = g ∘ₗ e) (he' : Function.Injective e')
    (hreg : ∀ x, g x ∈ range e' → x ∈ range e) :
    Function.Injective ((range f).mapQ (range g) e' (range_le_comap_range_of_comp_eq h)) := by
  rw [← ker_eq_bot, Submodule.eq_bot_iff]
  intro y hy
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  rw [mem_ker, Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero] at hy
  obtain ⟨x, hx⟩ := hy
  obtain ⟨x', rfl⟩ := hreg x ⟨y, hx.symm⟩
  rw [Submodule.Quotient.mk_eq_zero]
  refine ⟨x', he' ?_⟩
  rw [← comp_apply, h, comp_apply, hx]

/-- The map of cokernels induced by `e'` in a commuting square `e' ∘ f = g ∘ e` is onto exactly
when the ranges of `e'` and `g` span the target of `g`. -/
theorem surjective_mapQ_iff_sup_range_eq_top (h : e' ∘ₗ f = g ∘ₗ e) :
    Function.Surjective ((range f).mapQ (range g) e' (range_le_comap_range_of_comp_eq h)) ↔
      range e' ⊔ range g = ⊤ := by
  rw [← range_eq_top, Submodule.range_mapQ, Submodule.map_mkQ_eq_top, sup_comm]

/-- **Cokernels of a regular restriction.** Let `e' ∘ f = g ∘ e` with `e'` injective, let `g` be
regular: `g x ∈ range e'` implies `x ∈ range e`, and let the ranges of `e'` and `g` span the target
of `g`. Then `e'` induces a linear equivalence from the cokernel of `f` onto the cokernel of `g`. -/
noncomputable def cokerEquivOfRegular (h : e' ∘ₗ f = g ∘ₗ e) (he' : Function.Injective e')
    (hreg : ∀ x, g x ∈ range e' → x ∈ range e) (hsup : range e' ⊔ range g = ⊤) :
    (N ⧸ range f) ≃ₗ[R] N' ⧸ range g :=
  LinearEquiv.ofBijective ((range f).mapQ (range g) e' (range_le_comap_range_of_comp_eq h))
    ⟨injective_mapQ_of_regular h he' hreg, (surjective_mapQ_iff_sup_range_eq_top h).2 hsup⟩

@[simp]
theorem cokerEquivOfRegular_mk (h : e' ∘ₗ f = g ∘ₗ e) (he' : Function.Injective e')
    (hreg : ∀ x, g x ∈ range e' → x ∈ range e) (hsup : range e' ⊔ range g = ⊤) (y : N) :
    cokerEquivOfRegular h he' hreg hsup (Submodule.Quotient.mk y) =
      Submodule.Quotient.mk (e' y) :=
  (rfl)

@[simp]
theorem cokerEquivOfRegular_symm_mk (h : e' ∘ₗ f = g ∘ₗ e) (he' : Function.Injective e')
    (hreg : ∀ x, g x ∈ range e' → x ∈ range e) (hsup : range e' ⊔ range g = ⊤) (y : N) :
    (cokerEquivOfRegular h he' hreg hsup).symm (Submodule.Quotient.mk (e' y)) =
      Submodule.Quotient.mk y := by
  rw [LinearEquiv.symm_apply_eq, cokerEquivOfRegular_mk]

/-- **The dimension criterion.** Over a division ring, let `e' ∘ f = g ∘ e` with `e'` injective
and `g` regular: `g x ∈ range e'` implies `x ∈ range e`. If the cokernel of `g` is
finite-dimensional, of dimension at most that of the cokernel of `f`, then the ranges of `e'` and
`g` span the target of `g`, so the cokernels of `f` and `g` are isomorphic
(`LinearMap.cokerEquivOfRegular`). -/
theorem sup_range_eq_top_of_finrank_le {K : Type*} [DivisionRing K] [Module K M] [Module K N]
    [Module K M'] [Module K N'] {f : M →ₗ[K] N} {g : M' →ₗ[K] N'} {e : M →ₗ[K] M'}
    {e' : N →ₗ[K] N'} (h : e' ∘ₗ f = g ∘ₗ e) (he' : Function.Injective e')
    (hreg : ∀ x, g x ∈ range e' → x ∈ range e) [FiniteDimensional K (N' ⧸ range g)]
    (hle : Module.finrank K (N' ⧸ range g) ≤ Module.finrank K (N ⧸ range f)) :
    range e' ⊔ range g = ⊤ := by
  set φ := (range f).mapQ (range g) e' (range_le_comap_range_of_comp_eq h)
  have hinj := injective_mapQ_of_regular h he' hreg
  -- `φ` embeds the cokernel of `f` into the finite-dimensional cokernel of `g`.
  have : FiniteDimensional K (N ⧸ range f) := Module.Finite.of_injective φ hinj
  have hrank : Module.finrank K (N ⧸ range f) = Module.finrank K (N' ⧸ range g) :=
    le_antisymm (finrank_le_finrank_of_injective hinj) hle
  exact (surjective_mapQ_iff_sup_range_eq_top h).1
    ((injective_iff_surjective_of_finrank_eq_finrank hrank).1 hinj)

end LinearMap
