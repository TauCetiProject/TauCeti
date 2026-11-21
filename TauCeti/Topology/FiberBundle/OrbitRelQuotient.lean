/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.ConstMulAction
public import Mathlib.Topology.FiberBundle.Trivialization
public import TauCeti.Algebra.GroupAction.OrbitRelQuotient
public import TauCeti.Topology.Algebra.ConstMulAction

/-!
# Descending trivializations to orbit spaces

Let a group `G` act by homeomorphisms on spaces `M` and `N`, and let `φ : M → N` be equivariant,
so that it induces a map `φ' : M/G → N/G` of orbit spaces (`MulActionHom.orbitRelQuotientMap`).
This file descends a trivialization `e : M ⊇ φ⁻¹(U) ≃ U × F` of `φ` to a trivialization of `φ'`
over the image `[U]` of `U` in `N/G` (`Bundle.Trivialization.orbitRelQuotient`). Two conditions on
the base set `U` are needed:

* the orbit projection `N → N/G` is injective on `U`, so that it identifies `U` with `[U]`;
* `G` acts freely at the points of `U`.

Together they make the orbit projection `M → M/G` injective on `φ⁻¹(U)`: two points of `φ⁻¹(U)`
in one orbit, `x' = g • x`, have images `φ x` and `g • φ x` in `U` with the same orbit, so
`g • φ x = φ x` and `g = 1`. Its image is `φ'⁻¹[U]`, and the orbit projections are open maps, so
both restrict to homeomorphisms `φ⁻¹(U) ≃ φ'⁻¹[U]` and `U ≃ [U]`. The descended trivialization
is `e` read through them: it sends the orbit of `x ∈ φ⁻¹(U)` to the orbit of `φ x` and the fibre
coordinate of `x` (`Bundle.Trivialization.orbitRelQuotient_apply_mk`).

For a free properly discontinuous action, every point of `N` has a neighbourhood on which the
orbit projection is injective, so a locally trivial equivariant map descends to a locally
trivial map of orbit spaces with the same fibre. Freeness on the base is genuinely needed, even
when the orbit projection of `N` is injective and `G` acts freely on `M`: for `G = ℤ/2` acting
trivially on a point `N` and by swapping on `M = ℤ/2`, the map `M → N` is trivial with a two-point
fibre, but the induced map `M/G → N/G` has one point in its fibre.

## Main definitions

* `Bundle.Trivialization.orbitRelQuotient`: the trivialization of `φ' : M/G → N/G` over `[U]`
  induced by a trivialization of `φ` over `U`.

## Main results

* `Bundle.Trivialization.orbitRelQuotient_baseSet`, `Bundle.Trivialization.orbitRelQuotient_source`:
  its base set is the image of `U`, and its source consists of the orbits of points of `φ⁻¹(U)`.
* `Bundle.Trivialization.orbitRelQuotient_apply_mk`,
  `Bundle.Trivialization.orbitRelQuotient_symm_apply_mk`: the trivialization and its inverse on
  representatives over `U`.
* `Bundle.Trivialization.coe_orbitRelQuotient`, `Bundle.Trivialization.coe_orbitRelQuotient_symm`:
  the trivialization and its inverse as composites of `e`, its inverse, the orbit projections and
  their inverses on `φ⁻¹(U)` and `U`.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, second edition, Graduate Texts in Mathematics
  218, Springer, 2013, Chapter 21 (quotients by discrete group actions).
-/

public section

noncomputable section

open Function Set

namespace Bundle.Trivialization

variable {G M N F : Type*} [Group G] [MulAction G M] [MulAction G N] [TopologicalSpace M]
  [TopologicalSpace N] [TopologicalSpace F] {φ : M →[G] N} (e : Trivialization F φ)

/-- If the orbit projection of `N` is injective on the base set of `e` and `G` acts freely at the
points of the base set, the orbit projection of `M` is injective on the source of `e`. -/
theorem injOn_quotientMk_source (hinj : InjOn (Quotient.mk (MulAction.orbitRel G N)) e.baseSet)
    (hfree : ∀ y ∈ e.baseSet, ∀ g : G, g • y = y → g = 1) :
    InjOn (Quotient.mk (MulAction.orbitRel G M)) e.source := by
  intro x hx x' hx' hxx'
  obtain ⟨g, rfl⟩ := MulAction.orbitRel_apply.1 (Quotient.exact hxx')
  have hx : g • φ x' ∈ e.baseSet := by simpa [e.mem_source] using hx
  have hx'' := e.mem_source.1 hx'
  have hg : g • φ x' = φ x' := hinj hx hx'' MulAction.orbitRel.Quotient.quotient_smul_eq
  simp [hfree _ hx'' g hg]

/-- The orbits of points of the source of `e` are the orbits lying over the image of the base set
of `e`. -/
theorem image_quotientMk_source :
    Quotient.mk (MulAction.orbitRel G M) '' e.source =
      MulActionHom.orbitRelQuotientMap φ ⁻¹'
        (Quotient.mk (MulAction.orbitRel G N) '' e.baseSet) := by
  ext z
  induction z using Quotient.inductionOn with
  | h x =>
    simp only [mem_image, mem_preimage, MulActionHom.orbitRelQuotientMap_mk, e.mem_source]
    constructor
    · rintro ⟨x', hx', hxx'⟩
      obtain ⟨g, rfl⟩ := MulAction.orbitRel_apply.1 (Quotient.exact hxx')
      exact ⟨_, hx', by rw [map_smulₛₗ]; exact MulAction.orbitRel.Quotient.quotient_smul_eq⟩
    · rintro ⟨y, hy, hyx⟩
      obtain ⟨g, rfl⟩ := MulAction.orbitRel_apply.1 (Quotient.exact hyx)
      exact ⟨g • x, by simpa using hy, MulAction.orbitRel.Quotient.quotient_smul_eq⟩

variable [ContinuousConstSMul G M] [ContinuousConstSMul G N]

variable [Nonempty M]

/-- **A trivialization descends to orbit spaces.** Let `e` be a trivialization of an equivariant
map `φ : M → N` over `U`, such that the orbit projection of `N` is injective on `U` and `G` acts
freely at the points of `U`. Then the map `φ' : M/G → N/G` induced by `φ` is trivial over the image
`[U]` of `U`, with the same fibre: the orbit of `x ∈ φ⁻¹(U)` goes to the orbit of `φ x` and the
fibre coordinate of `x` (`Bundle.Trivialization.orbitRelQuotient_apply_mk`). -/
def orbitRelQuotient (hinj : InjOn (Quotient.mk (MulAction.orbitRel G N)) e.baseSet)
    (hfree : ∀ y ∈ e.baseSet, ∀ g : G, g • y = y → g = 1) :
    Trivialization F (MulActionHom.orbitRelQuotientMap φ) :=
  haveI : Nonempty N := ⟨φ (Classical.arbitrary M)⟩
  { toOpenPartialHomeomorph :=
      (((TauCeti.quotientMkOn e.open_source (e.injOn_quotientMk_source hinj hfree)).symm.trans'
        e.toOpenPartialHomeomorph (by simp)).trans'
        ((TauCeti.quotientMkOn e.open_baseSet hinj).prod (OpenPartialHomeomorph.refl F))
        (by simp [e.target_eq]))
    baseSet := Quotient.mk (MulAction.orbitRel G N) '' e.baseSet
    open_baseSet := isOpenMap_quotient_mk'_mul _ e.open_baseSet
    source_eq := e.image_quotientMk_source
    target_eq := by simp
    proj_toFun := by
      rintro _ ⟨x, hx, rfl⟩
      have hx' := (e.injOn_quotientMk_source hinj hfree).leftInvOn_invFunOn hx
      simp [OpenPartialHomeomorph.trans'_apply, hx', e.coe_fst hx] }

variable (hinj : InjOn (Quotient.mk (MulAction.orbitRel G N)) e.baseSet)
  (hfree : ∀ y ∈ e.baseSet, ∀ g : G, g • y = y → g = 1)

/-- The base set of the descended trivialization is the image of the base set of `e`. -/
@[simp]
theorem orbitRelQuotient_baseSet :
    (e.orbitRelQuotient hinj hfree).baseSet = Quotient.mk (MulAction.orbitRel G N) '' e.baseSet :=
  (rfl)

/-- The source of the descended trivialization consists of the orbits of the points of the source
of `e`. -/
theorem orbitRelQuotient_source :
    (e.orbitRelQuotient hinj hfree).source = Quotient.mk (MulAction.orbitRel G M) '' e.source :=
  (rfl)

/-- The descended trivialization is `e`, read through the inverse of the orbit projection of `M`
on the source of `e` and the orbit projection of `N`. -/
theorem coe_orbitRelQuotient :
    ⇑(e.orbitRelQuotient hinj hfree) =
      Prod.map (Quotient.mk (MulAction.orbitRel G N)) id ∘ e ∘
        invFunOn (Quotient.mk (MulAction.orbitRel G M)) e.source :=
  (rfl)

/-- The inverse of the descended trivialization is the inverse of `e`, read through the inverse
of the orbit projection of `N` on the base set of `e` and the orbit projection of `M`. -/
theorem coe_orbitRelQuotient_symm :
    haveI : Nonempty N := ⟨φ (Classical.arbitrary M)⟩
    ⇑(e.orbitRelQuotient hinj hfree).toOpenPartialHomeomorph.symm =
      Quotient.mk (MulAction.orbitRel G M) ∘ e.toOpenPartialHomeomorph.symm ∘
        Prod.map (invFunOn (Quotient.mk (MulAction.orbitRel G N)) e.baseSet) id :=
  (rfl)

/-- The descended trivialization sends the orbit of a point `x` over the base set of `e` to the
orbit of `φ x` and the fibre coordinate of `x` in `e`. -/
@[simp]
theorem orbitRelQuotient_apply_mk {x : M} (hx : x ∈ e.source) :
    e.orbitRelQuotient hinj hfree (Quotient.mk _ x) = (Quotient.mk _ (φ x), (e x).2) := by
  rw [coe_orbitRelQuotient, comp_apply, comp_apply,
    (e.injOn_quotientMk_source hinj hfree).leftInvOn_invFunOn hx, Prod.map_apply, e.coe_fst hx,
    id_eq]

/-- The inverse of the descended trivialization sends the orbit of a point `y` of the base set of
`e` and `f : F` to the orbit of `e.symm (y, f)`. -/
@[simp]
theorem orbitRelQuotient_symm_apply_mk {y : N} (hy : y ∈ e.baseSet) (f : F) :
    (e.orbitRelQuotient hinj hfree).toOpenPartialHomeomorph.symm (Quotient.mk _ y, f) =
      Quotient.mk _ (e.toOpenPartialHomeomorph.symm (y, f)) := by
  have : Nonempty N := ⟨φ (Classical.arbitrary M)⟩
  rw [coe_orbitRelQuotient_symm, comp_apply, comp_apply, Prod.map_apply,
    hinj.leftInvOn_invFunOn hy, id_eq]

end Bundle.Trivialization
