/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Submodule.Map
public import Mathlib.Algebra.Module.Submodule.Range
public import Mathlib.Order.SupIndep
public import Mathlib.LinearAlgebra.Span.Basic

/-!
# Submodules under a linear map

`Submodule.map` preserves arbitrary suprema (`Submodule.map_iSup`), and along an injective map it
also preserves infima (`Submodule.map_inf`) and hence disjointness (`Submodule.disjoint_map`).  This
file records what those facts say about a family of submodules indexed by a `Finset`: pushing it
forward along a (semi)linear map turns a spanning family into one spanning the range of the map,
and along an injective map it leaves an independent family independent.

The finite-set form is what a decomposition of a module into a `Finset` of submodules needs, as in
`TauCeti/RingTheory/KrullSchmidt/Existence.lean`, when it is transported along a linear map.

The file also describes two maps between submodule lattices: the inverse of the interval
isomorphism `Submodule.mapIic` is the inverse image along the inclusion, and an injective map
restricted to `B` carries the trace `A.comap B.subtype` of `A` in `B` onto the trace of `A.map f`
in `B.map f`. The subquotient identifications in `TauCeti/Algebra/Module/Submodule/Quotient.lean`
use both.

## Main results

* `LinearMap.sup_image_map_eq_range_of_sup_eq_top`: a finite family of submodules spanning the
  whole module is carried to one spanning the range of the map.
* `LinearMap.supIndep_image_map`: an injective linear map carries an independent finite
  family of submodules to an independent one.
* `Submodule.map_eq_span_of_span_eq_top`: the image of a submodule spanned by a family of its
  vectors (for instance a basis, via `Module.Basis.span_eq`) is spanned by the images of those
  vectors.
* `Submodule.mapIic_symm_apply`: the inverse of `Submodule.mapIic` takes inverse images along the
  inclusion.
* `LinearMap.map_equivMapOfInjective_comap_subtype`: the restriction of an injective map to `B`
  carries the trace of `A` in `B` onto the trace of `A.map f` in `B.map f`.
-/

public section

namespace Submodule

variable {R R₂ M M₂ ι : Type*} [Semiring R] [Semiring R₂]
variable [AddCommMonoid M] [Module R M] [AddCommMonoid M₂] [Module R₂ M₂]
variable {σ₁₂ : R →+* R₂} [RingHomSurjective σ₁₂]

/-- The image of a submodule spanned by a family of its vectors is spanned by the images of those
vectors. -/
theorem map_eq_span_of_span_eq_top (p : Submodule R M) {v : ι → p}
    (hv : span R (Set.range v) = ⊤) (f : M →ₛₗ[σ₁₂] M₂) :
    p.map f = span R₂ (Set.range fun i ↦ f (v i)) := by
  conv_lhs => rw [← (span_range_subtype_eq_top_iff p fun i ↦ (v i).2).1 hv]
  rw [map_span, ← Set.range_comp, Function.comp_def]

/-- The inverse of `Submodule.mapIic` takes the inverse image along the inclusion.  This is the
`symm`-side counterpart of Mathlib's `Submodule.coe_mapIic_apply`.

This is not a simp lemma: unfolding the inverse prevents simplification by the order
isomorphism's round-trip laws. -/
theorem mapIic_symm_apply (p : Submodule R M) (N : Set.Iic p) :
    p.mapIic.symm N = (N : Submodule R M).comap p.subtype :=
  rfl

end Submodule

namespace LinearMap

variable {R R₂ M M₂ : Type*} [Semiring R] [Semiring R₂]
variable [AddCommMonoid M] [Module R M] [AddCommMonoid M₂] [Module R₂ M₂]
variable {σ₁₂ : R →+* R₂} [RingHomSurjective σ₁₂]

/-- **A linear map carries a spanning finite family of submodules to a family spanning its
range**: the images of the members of a finite family with supremum `⊤` have supremum
`LinearMap.range f`. -/
theorem sup_image_map_eq_range_of_sup_eq_top [DecidableEq (Submodule R₂ M₂)]
    (f : M →ₛₗ[σ₁₂] M₂) {s : Finset (Submodule R M)} (hs : s.sup _root_.id = ⊤) :
    (s.image (Submodule.map f)).sup _root_.id = LinearMap.range f := by
  rw [Finset.sup_image]
  simpa only [Function.comp_def, id_eq, Finset.sup_eq_iSup, Submodule.map_iSup,
    Submodule.map_top] using congrArg (Submodule.map f) hs

/-- **An injective linear map preserves independence of a finite family of submodules**: the images
of the members are again independent. -/
theorem supIndep_image_map [DecidableEq (Submodule R₂ M₂)] (f : M →ₛₗ[σ₁₂] M₂)
    (hf : Function.Injective f) {s : Finset (Submodule R M)} (hs : s.SupIndep _root_.id) :
    (s.image (Submodule.map f)).SupIndep _root_.id := by
  refine Finset.SupIndep.image fun t hts P hP hPt ↦ ?_
  simpa only [Function.comp_def, id_eq, Finset.sup_eq_iSup, Submodule.map_iSup] using
    Submodule.disjoint_map hf (hs hts hP hPt)

/-- An injective linear map carries the trace of `A` in `B` onto the trace of `A.map f` in
`B.map f`, so it descends to the subquotients. -/
@[simp]
theorem map_equivMapOfInjective_comap_subtype {N : Type*} [AddCommMonoid N] [Module R N]
    (f : M →ₗ[R] N) (hf : Function.Injective f) (A B : Submodule R M) :
    Submodule.map (B.equivMapOfInjective f hf : ↥B →ₗ[R] ↥(B.map f))
        (Submodule.comap B.subtype A) =
      Submodule.comap (B.map f).subtype (A.map f) := by
  refine Submodule.map_injective_of_injective (B.map f).injective_subtype ?_
  have hcomp : (B.map f).subtype ∘ₗ (B.equivMapOfInjective f hf : ↥B →ₗ[R] ↥(B.map f)) =
      f ∘ₗ B.subtype :=
    LinearMap.ext fun x => Submodule.coe_equivMapOfInjective_apply f hf B x
  rw [← Submodule.map_comp, hcomp, Submodule.map_comp, Submodule.map_comap_subtype,
    Submodule.map_comap_subtype, Submodule.map_inf f hf]

end LinearMap
