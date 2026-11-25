/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Determinant.Comp.Basic
import TauCeti.Algebra.Module.Submodule.LinearMap
import TauCeti.Data.Fin.Tuple.Basic
import TauCeti.LinearAlgebra.LinearIndependent.Fin
import TauCeti.RingTheory.PicardGroup.Contraction

/-!
# Associativity of the composition law of determinant lines

Let `f : M → N`, `g : N → P` and `h : P → Q` be linear maps between vector spaces over a field,
with finite-dimensional kernels and cokernels. The composition law
`det (g ∘ f) ≃ det f ⊗ det g` (`LinearMap.detLineCompEquiv`) splits `det (h ∘ g ∘ f)` into
`det f ⊗ det g ⊗ det h` in two ways: first off `h`, through `det (g ∘ f) ⊗ det h`, or first off
`f`, through `det f ⊗ det (h ∘ g)`. This file proves that the two splittings agree up to an
explicit sign (`LinearMap.detLineCompEquiv_assoc`):

`assoc ((c(f, g) ⊗ 1) (c(g ∘ f, h) x)) = (-1) ^ (r₁ r₂ + r₃ r₄) • (1 ⊗ c(g, h)) (c(f, h ∘ g) x)`,

where `c` is the composition law, `r₁` and `r₄` are the ranks of the connecting maps
`ker g → coker f` and `ker h → coker g`, `r₂` is the rank of `ker (h ∘ g ∘ f) → ker h` and `r₃`
that of `coker f → coker (h ∘ g ∘ f)`.

The sign is genuine. Take `f : K → K²` the inclusion of the first coordinate line, `g : K² → K²`
the projection onto it and `h : K² → K` the second coordinate. Then `ker g → coker f` and
`ker (h ∘ g ∘ f) = K → ker h` are nonzero, so `r₁ = r₂ = 1`, while `h ∘ g = 0` and `ker h` is the
range of `g`, so `r₃ = r₄ = 0`: the two splittings differ by `-1`, a genuine sign unless `K` has
characteristic two.

The proof evaluates both sides with `LinearMap.detLineCompEquiv_tmul` on one exterior product
`β ⊗ φ`, where `β` spans `det (ker (h ∘ g ∘ f))`. It uses families of vectors adapted to all four
kernel–cokernel sequences at once, recorded in the private structure `AssocData`: a basis `u` of
`ker f` completed by `v` to `ker (g ∘ f)` and by `b` to `ker (h ∘ g ∘ f)`, vectors `w` of `ker g`
and `w₂` of `ker (h ∘ g)` whose classes, together with vectors `x`, form a basis of `coker f`,
vectors `c` of `ker h`, and lifts `y` and `e` completing bases of the cokernels of `g ∘ f`, `g`,
`h ∘ g` and `h`. The exterior products of these families, with functionals normalized on them, are
recorded in the private structure `AssocElems`. Both sides then become the same tensor of exterior
products and normalized functionals, except that the factors are listed in different orders in two
places. Splitting off `h` first lists the cokernel of `g ∘ f` through the classes of `w₂`, `c`,
`x`, `y`, while splitting `g ∘ f` lists it through `w₂`, `x`, `c`, `y`. Splitting off `f` first
lists `ker (h ∘ g)` through `v`, `b`, `w`, `w₂`, while splitting `h ∘ g` lists it through `v`, `w`,
`b`, `w₂`. Exchanging the two middle blocks costs `(-1) ^ (r₃ r₄)` and `(-1) ^ (r₂ r₁)`
respectively.

## Main results

* `LinearMap.detLineCompEquiv_assoc`: associativity of the composition law of determinant lines,
  up to the sign `(-1) ^ (r₁ r₂ + r₃ r₄)`.

## References

* A. Zinger, *The determinant line bundle for Fredholm operators: construction, properties,
  and classification*, Math. Scand. **118** (2016), 203–268, arXiv:1304.6368 (the compatibility
  of the composition isomorphisms with triple composites, and its signs).
* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., AMS
  Colloquium Publications **52**, 2012, Appendix A.2 (determinant lines of exact sequences).
-/

public section

noncomputable section

open Module TensorProduct

namespace LinearMap

variable {K : Type*} [Field K]

section Assoc

variable {M N P Q : Type*} [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N]
  [AddCommGroup P] [Module K P] [AddCommGroup Q] [Module K Q]
  (f : M →ₗ[K] N) (g : N →ₗ[K] P) (h : P →ₗ[K] Q)

/-! ### Adapted families -/

/-- The kernel part of the adapted families: a basis of `ker f`, completed to bases of
`ker (g ∘ f)` and of `ker (h ∘ g ∘ f)`. -/
private theorem exists_linearIndependent_ker [FiniteDimensional K (ker f)]
    [FiniteDimensional K (ker g)]
    [FiniteDimensional K (ker h)] :
    ∃ (v : Fin (finrank K (range (f.kerCompToKer g))) → ker (g ∘ₗ f))
      (b : Fin (finrank K (range ((g ∘ₗ f).kerCompToKer h))) → ker (h ∘ₗ g ∘ₗ f)),
      LinearIndependent K (Fin.append (Submodule.inclusion (ker_le_ker_comp (g ∘ₗ f) h) ∘
        Fin.append (Submodule.inclusion (ker_le_ker_comp f g) ∘ Module.finBasis K (ker f)) v)
          b) := by
  obtain ⟨v, hv⟩ := exists_linearIndependent_comp (f.kerCompToKer g)
  obtain ⟨b, hb⟩ := exists_linearIndependent_comp ((g ∘ₗ f).kerCompToKer h)
  refine ⟨v, b, LinearIndependent.fin_append_of_linearIndependent_comp ?_ _
    (fun _ ↦ ((g ∘ₗ f).exact_inclusion_kerCompToKer h).apply_apply_eq_zero _) hb⟩
  refine LinearIndependent.map' (LinearIndependent.fin_append_of_linearIndependent_comp ?_ _
    (fun _ ↦ (f.exact_inclusion_kerCompToKer g).apply_apply_eq_zero _) hv) _
    (Submodule.ker_inclusion _ _ _)
  exact (Module.finBasis K _).linearIndependent.map' _ (Submodule.ker_inclusion _ _ _)

variable [FiniteDimensional K (ker f)] [FiniteDimensional K (ker g)] [FiniteDimensional K (ker h)]
  [FiniteDimensional K (N ⧸ range f)] [FiniteDimensional K (P ⧸ range g)]
  [FiniteDimensional K (Q ⧸ range h)] [FiniteDimensional K (ker (h ∘ₗ g))]
  [FiniteDimensional K (Q ⧸ range (h ∘ₗ g))]

/-- Families of vectors adapted to the kernel–cokernel sequences of the four composites
`g ∘ f`, `h ∘ (g ∘ f)`, `(h ∘ g) ∘ f` and `h ∘ g`, with the linear independence statements that
make the exterior products built from them nonzero. -/
private structure AssocData where
  v : Fin (finrank K (range (f.kerCompToKer g))) → ker (g ∘ₗ f)
  b : Fin (finrank K (range ((g ∘ₗ f).kerCompToKer h))) → ker (h ∘ₗ g ∘ₗ f)
  w : Fin (finrank K (range (f.kerToCoker g))) → ker g
  w₂ : Fin (finrank K (range (f.cokerToCokerComp g ∘ₗ f.kerToCoker (h ∘ₗ g)))) → ker (h ∘ₗ g)
  x : Fin (finrank K (range (f.cokerToCokerComp (h ∘ₗ g)))) → N ⧸ range f
  c : Fin (finrank K (range (g.kerToCoker h))) → ker h
  y : Fin (finrank K (range (g.cokerToCokerComp h))) → P ⧸ range (g ∘ₗ f)
  e : Fin (finrank K (Q ⧸ range h)) → Q ⧸ range (h ∘ₗ g ∘ₗ f)
  li_ker : LinearIndependent K (Fin.append (Submodule.inclusion (ker_le_ker_comp (g ∘ₗ f) h) ∘
    Fin.append (Submodule.inclusion (ker_le_ker_comp f g) ∘ Module.finBasis K (ker f)) v) b)
  li_cokerf : LinearIndependent K
    (Fin.append (f.kerToCoker g ∘ w) (Fin.append (f.kerToCoker (h ∘ₗ g) ∘ w₂) x))
  li_cokergf : LinearIndependent K (Fin.append
    (Fin.append (f.cokerToCokerComp g ∘ f.kerToCoker (h ∘ₗ g) ∘ w₂) (f.cokerToCokerComp g ∘ x))
    (Fin.append ((g ∘ₗ f).kerToCoker h ∘ c) y))
  li_cokerg : LinearIndependent K
    (Fin.append (g.kerToCoker h ∘ c) (Submodule.factor (range_comp_le_range f g) ∘ y))
  li_cokerhg : LinearIndependent K (Fin.append
    (Submodule.factor (range_comp_le_range f (h ∘ₗ g)) ∘ (g ∘ₗ f).cokerToCokerComp h ∘ y)
    (Submodule.factor (range_comp_le_range f (h ∘ₗ g)) ∘ e))
  li_cokerh : LinearIndependent K (Submodule.factor (range_comp_le_range (g ∘ₗ f) h) ∘ e)

private theorem nonempty_assocData : Nonempty (AssocData f g h) := by
  have : FiniteDimensional K (Q ⧸ range ((h ∘ₗ g) ∘ₗ f)) :=
    Module.Finite.quotient_range_comp f (h ∘ₗ g)
  obtain ⟨v, b, hvb⟩ := exists_linearIndependent_ker f g h
  obtain ⟨w, hw⟩ := exists_linearIndependent_comp (f.kerToCoker g)
  obtain ⟨w₂, hw₂⟩ :=
    exists_linearIndependent_comp (f.cokerToCokerComp g ∘ₗ f.kerToCoker (h ∘ₗ g))
  rw [LinearMap.coe_comp] at hw₂
  obtain ⟨x, hx⟩ := exists_linearIndependent_comp (f.cokerToCokerComp (h ∘ₗ g))
  obtain ⟨c, hc⟩ := exists_linearIndependent_comp (g.kerToCoker h)
  obtain ⟨y', hy'⟩ := exists_linearIndependent_comp (g.cokerToCokerComp h)
  choose y hy using fun i ↦ Submodule.factor_surjective (range_comp_le_range f g) (y' i)
  obtain ⟨e, he⟩ := exists_linearIndependent_comp_of_surjective
    (Submodule.factor_surjective (range_comp_le_range (g ∘ₗ f) h))
  have hy₁ : ⇑(Submodule.factor (range_comp_le_range f g)) ∘ y = y' := funext hy
  -- In `coker (g ∘ f)`: the images of `w₂` and `x`, which lie in the image of `coker f`.
  have hin := hw₂.fin_append_of_linearIndependent_comp ((g ∘ₗ f).cokerToCokerComp h)
    (y := f.cokerToCokerComp g ∘ x)
    (fun i ↦ by
      rw [Function.comp_apply, Function.comp_apply,
        ← LinearMap.comp_apply ((g ∘ₗ f).cokerToCokerComp h),
        cokerToCokerComp_comp_cokerToCokerComp]
      exact (f.exact_kerToCoker_cokerToCokerComp (h ∘ₗ g)).apply_apply_eq_zero _)
    (by rwa [← Function.comp_assoc, ← LinearMap.coe_comp, cokerToCokerComp_comp_cokerToCokerComp])
  -- In `coker g`: the images of `c` and of `y`.
  have hcg := hc.fin_append_of_linearIndependent_comp (g.cokerToCokerComp h)
    (y := ⇑(Submodule.factor (range_comp_le_range f g)) ∘ y)
    (fun _ ↦ (g.exact_kerToCoker_cokerToCokerComp h).apply_apply_eq_zero _) (by rwa [hy₁])
  refine ⟨⟨v, b, w, w₂, x, c, y, e, hvb, ?_, ?_, hcg, ?_, he⟩⟩
  · refine hw.fin_append_of_linearIndependent_comp (f.cokerToCokerComp g)
      (fun _ ↦ (f.exact_kerToCoker_cokerToCokerComp g).apply_apply_eq_zero _) ?_
    rwa [Fin.comp_append, ← Function.comp_assoc]
  · refine hin.fin_append_of_linearIndependent_comp
      (Submodule.factor (range_comp_le_range f g))
      (fun i ↦ ?_) ?_
    · refine Fin.addCases (fun j ↦ ?_) (fun j ↦ ?_) i <;>
        simp only [Fin.append_left, Fin.append_right, Function.comp_apply] <;>
        exact (f.exact_cokerToCokerComp_factor g).apply_apply_eq_zero _
    · rwa [Fin.comp_append, ← Function.comp_assoc, ← LinearMap.coe_comp, factor_comp_kerToCoker]
  · refine LinearIndependent.fin_append_of_linearIndependent_comp ?_
      (Submodule.factor (range_comp_le_range g h)) (fun i ↦ ?_) ?_
    · rwa [← Function.comp_assoc, ← LinearMap.coe_comp, factor_comp_cokerToCokerComp,
        LinearMap.coe_comp, Function.comp_assoc, hy₁]
    · rw [Function.comp_apply, Function.comp_apply,
        ← LinearMap.comp_apply (Submodule.factor (range_comp_le_range f (h ∘ₗ g))),
        factor_comp_cokerToCokerComp, LinearMap.comp_apply]
      exact (g.exact_cokerToCokerComp_factor h).apply_apply_eq_zero _
    · rwa [← Function.comp_assoc, ← LinearMap.coe_comp, Submodule.factor_comp]

/-- The dimension counts relating the four kernel–cokernel sequences. -/
private theorem finrank_assoc :
    finrank K (range ((g ∘ₗ f).kerToCoker h)) =
        finrank K (range (f.cokerToCokerComp g ∘ₗ f.kerToCoker (h ∘ₗ g))) +
          finrank K (range (g.kerToCoker h)) ∧
      finrank K (range ((g ∘ₗ f).cokerToCokerComp h)) =
        finrank K (range (f.cokerToCokerComp (h ∘ₗ g))) +
          finrank K (range (g.cokerToCokerComp h)) ∧
      finrank K (range (f.cokerToCokerComp g)) =
        finrank K (range (f.cokerToCokerComp g ∘ₗ f.kerToCoker (h ∘ₗ g))) +
          finrank K (range (f.cokerToCokerComp (h ∘ₗ g))) ∧
      finrank K (range (f.kerCompToKer (h ∘ₗ g))) =
        finrank K (range (f.kerCompToKer g)) + finrank K (range ((g ∘ₗ f).kerCompToKer h)) ∧
      finrank K (range (g.kerCompToKer h)) =
        finrank K (range ((g ∘ₗ f).kerCompToKer h)) +
          finrank K (range (f.cokerToCokerComp g ∘ₗ f.kerToCoker (h ∘ₗ g))) := by
  have : FiniteDimensional K (ker (g ∘ₗ f)) := Module.Finite.ker_comp f g
  have : FiniteDimensional K (P ⧸ range (g ∘ₗ f)) := Module.Finite.quotient_range_comp f g
  have : FiniteDimensional K (ker (h ∘ₗ g ∘ₗ f)) := Module.Finite.ker_comp (g ∘ₗ f) h
  have : FiniteDimensional K (Q ⧸ range (h ∘ₗ g ∘ₗ f)) :=
    Module.Finite.quotient_range_comp (g ∘ₗ f) h
  have : FiniteDimensional K (ker ((h ∘ₗ g) ∘ₗ f)) := Module.Finite.ker_comp f (h ∘ₗ g)
  have : FiniteDimensional K (Q ⧸ range ((h ∘ₗ g) ∘ₗ f)) :=
    Module.Finite.quotient_range_comp f (h ∘ₗ g)
  -- The six-term sequences of `g ∘ f`, `h ∘ (g ∘ f)`, `(h ∘ g) ∘ f` and `h ∘ g`. The composites
  -- `(h ∘ g) ∘ f` and `h ∘ (g ∘ f)` are the same map (`LinearMap.comp_assoc` holds by `rfl`); the
  -- type ascriptions below spell the kernel and cokernel of the former as those of the latter, so
  -- that `omega` sees the same atoms.
  have := f.finrank_ker_comp_eq_finrank_ker_add g
  have := f.finrank_ker_eq_finrank_range_kerCompToKer_add g
  have := f.finrank_quotient_range_eq_finrank_range_kerToCoker_add g
  have := f.finrank_quotient_range_comp_eq_finrank_range_cokerToCokerComp_add g
  have := (g ∘ₗ f).finrank_ker_comp_eq_finrank_ker_add h
  have := (g ∘ₗ f).finrank_ker_eq_finrank_range_kerCompToKer_add h
  have := (g ∘ₗ f).finrank_quotient_range_eq_finrank_range_kerToCoker_add h
  have := (g ∘ₗ f).finrank_quotient_range_comp_eq_finrank_range_cokerToCokerComp_add h
  have : finrank K (ker (h ∘ₗ g ∘ₗ f)) =
      finrank K (ker f) + finrank K (range (f.kerCompToKer (h ∘ₗ g))) :=
    f.finrank_ker_comp_eq_finrank_ker_add (h ∘ₗ g)
  have := f.finrank_ker_eq_finrank_range_kerCompToKer_add (h ∘ₗ g)
  have := f.finrank_quotient_range_eq_finrank_range_kerToCoker_add (h ∘ₗ g)
  have : finrank K (Q ⧸ range (h ∘ₗ g ∘ₗ f)) =
      finrank K (range (f.cokerToCokerComp (h ∘ₗ g))) + finrank K (Q ⧸ range (h ∘ₗ g)) :=
    f.finrank_quotient_range_comp_eq_finrank_range_cokerToCokerComp_add (h ∘ₗ g)
  have := g.finrank_ker_comp_eq_finrank_ker_add h
  have := g.finrank_ker_eq_finrank_range_kerCompToKer_add h
  have := g.finrank_quotient_range_eq_finrank_range_kerToCoker_add h
  have := g.finrank_quotient_range_comp_eq_finrank_range_cokerToCokerComp_add h
  have := f.finrank_range_kerToCoker_comp_eq_add g h
  omega

/-! ### Evaluating the two composites -/

/-- Elements of the determinant lines that both composites involve, written as exterior products
of the adapted families `d`, together with functionals normalized on them. Both composites are
evaluated on `β ⊗ φ`; `η` normalized on `β` reduces every element of `det (ker (h ∘ g ∘ f))` to
a multiple of `β`. -/
private structure AssocElems (d : AssocData f g h) where
  β : TauCeti.detLine K (ker (h ∘ₗ g ∘ₗ f))
  η : Dual K (TauCeti.detLine K (ker (h ∘ₗ g ∘ₗ f)))
  γ₂ : TauCeti.detLine K (ker g)
  γ₃ : TauCeti.detLine K (ker h)
  ε : TauCeti.detLine K (Q ⧸ range (h ∘ₗ g ∘ₗ f))
  δ₁ : TauCeti.detLine K (N ⧸ range f)
  ψ₁ : Dual K (TauCeti.detLine K (N ⧸ range f))
  δ₂ : TauCeti.detLine K (P ⧸ range g)
  ψ₂ : Dual K (TauCeti.detLine K (P ⧸ range g))
  χ : Dual K (TauCeti.detLine K (Q ⧸ range h))
  hβ : (β : ExteriorAlgebra K (ker (h ∘ₗ g ∘ₗ f))) = ExteriorAlgebra.ιMulti K _
    (Fin.append (Submodule.inclusion (ker_le_ker_comp (g ∘ₗ f) h) ∘
      Fin.append (Submodule.inclusion (ker_le_ker_comp f g) ∘ Module.finBasis K (ker f)) d.v) d.b)
  hη : η β = 1
  hγ₂ : (γ₂ : ExteriorAlgebra K (ker g)) =
    ExteriorAlgebra.ιMulti K _ (Fin.append (f.kerCompToKer g ∘ d.v) d.w)
  hγ₃ : (γ₃ : ExteriorAlgebra K (ker h)) = ExteriorAlgebra.ιMulti K _
    (Fin.append ((g ∘ₗ f).kerCompToKer h ∘ d.b) (Fin.append (g.kerCompToKer h ∘ d.w₂) d.c))
  hε : (ε : ExteriorAlgebra K (Q ⧸ range (h ∘ₗ g ∘ₗ f))) = ExteriorAlgebra.ιMulti K _
    (Fin.append ((g ∘ₗ f).cokerToCokerComp h ∘ Fin.append (f.cokerToCokerComp g ∘ d.x) d.y) d.e)
  hδ₁ : (δ₁ : ExteriorAlgebra K (N ⧸ range f)) = ExteriorAlgebra.ιMulti K _
    (Fin.append (f.kerToCoker g ∘ d.w) (Fin.append (f.kerToCoker (h ∘ₗ g) ∘ d.w₂) d.x))
  hψ₁ : ψ₁ δ₁ = 1
  hδ₂ : (δ₂ : ExteriorAlgebra K (P ⧸ range g)) = ExteriorAlgebra.ιMulti K _
    (Fin.append (g.kerToCoker h ∘ d.c) (Submodule.factor (range_comp_le_range f g) ∘ d.y))
  hψ₂ : ψ₂ δ₂ = 1
  hχ : χ (exteriorPower.ιMulti K _ (Submodule.factor (range_comp_le_range (g ∘ₗ f) h) ∘ d.e)) = 1

/-- The composition law of `g ∘ f` on `α ⊗ ψ₀`: the second step of the left composite. -/
private theorem assoc_left_tmul₂ {d : AssocData f g h} (E : AssocElems f g h d)
    {α : TauCeti.detLine K (ker (g ∘ₗ f))}
    (hα : (α : ExteriorAlgebra K (ker (g ∘ₗ f))) = ExteriorAlgebra.ιMulti K _
      (Fin.append (Submodule.inclusion (ker_le_ker_comp f g) ∘ Module.finBasis K (ker f)) d.v))
    {δ₀ : TauCeti.detLine K (P ⧸ range (g ∘ₗ f))}
    (hδ₀ : (δ₀ : ExteriorAlgebra K (P ⧸ range (g ∘ₗ f))) = ExteriorAlgebra.ιMulti K _ (Fin.append
      (Fin.append (f.cokerToCokerComp g ∘ f.kerToCoker (h ∘ₗ g) ∘ d.w₂)
        (f.cokerToCokerComp g ∘ d.x)) (Fin.append ((g ∘ₗ f).kerToCoker h ∘ d.c) d.y)))
    (ψ₀ : Dual K (TauCeti.detLine K (P ⧸ range (g ∘ₗ f)))) :
    f.detLineCompEquiv g (α ⊗ₜ ψ₀) = ψ₀ δ₀ •
      ((exteriorPower.ιMulti K _ (Module.finBasis K (ker f)) ⊗ₜ E.ψ₁) ⊗ₜ (E.γ₂ ⊗ₜ E.ψ₂)) := by
  have d₃ := g.finrank_quotient_range_eq_finrank_range_kerToCoker_add h
  obtain ⟨-, -, c₄, -, -⟩ := finrank_assoc f g h
  have hδ₁' : (E.δ₁ : ExteriorAlgebra K (N ⧸ range f)) = ExteriorAlgebra.ιMulti K _
      (Fin.append (f.kerToCoker g ∘ d.w)
        (Fin.append (f.kerToCoker (h ∘ₗ g) ∘ d.w₂) d.x ∘ Fin.cast c₄)) := by
    rw [E.hδ₁]
    simp only [← ExteriorAlgebra.ιMulti_mul_ιMulti, TauCeti.ExteriorAlgebra.ιMulti_comp_cast]
  have hδ₀' : (δ₀ : ExteriorAlgebra K (P ⧸ range (g ∘ₗ f))) = ExteriorAlgebra.ιMulti K _
      (Fin.append (f.cokerToCokerComp g ∘
        (Fin.append (f.kerToCoker (h ∘ₗ g) ∘ d.w₂) d.x ∘ Fin.cast c₄))
        (Fin.append ((g ∘ₗ f).kerToCoker h ∘ d.c) d.y ∘ Fin.cast d₃)) := by
    rw [hδ₀]
    simp only [← ExteriorAlgebra.ιMulti_mul_ιMulti, TauCeti.ExteriorAlgebra.ιMulti_comp_cast,
      Fin.comp_append, ← Function.comp_assoc]
  have hδ₂' : exteriorPower.ιMulti K _ (Submodule.factor (range_comp_le_range f g) ∘
      (Fin.append ((g ∘ₗ f).kerToCoker h ∘ d.c) d.y ∘ Fin.cast d₃)) = E.δ₂ := by
    refine Subtype.ext ?_
    rw [exteriorPower.ιMulti_apply_coe, E.hδ₂]
    simp only [← ExteriorAlgebra.ιMulti_mul_ιMulti, TauCeti.ExteriorAlgebra.ιMulti_comp_cast,
      Fin.comp_append, ← Function.comp_assoc, ← LinearMap.coe_comp, factor_comp_kerToCoker]
  rw [f.detLineCompEquiv_tmul g _ _ _ _ _ hα E.hγ₂ hδ₁' hδ₀' ψ₀ E.hψ₁
    (by rw [hδ₂']; exact E.hψ₂)]

/-- The composition law of `(h ∘ g) ∘ f` on `β ⊗ φ`: the first step of the right composite. The
domain `det ((h ∘ g) ∘ f)` of `f.detLineCompEquiv (h ∘ g)` is `det (h ∘ g ∘ f)`, since
`LinearMap.comp_assoc` holds by `rfl`. -/
private theorem assoc_right_tmul₁ {d : AssocData f g h} (E : AssocElems f g h d)
    {β₂ : TauCeti.detLine K (ker (h ∘ₗ g))}
    (hβ₂ : (β₂ : ExteriorAlgebra K (ker (h ∘ₗ g))) = ExteriorAlgebra.ιMulti K _
      (Fin.append (Submodule.inclusion (ker_le_ker_comp g h) ∘
        Fin.append (f.kerCompToKer g ∘ d.v) d.w) (Fin.append (f.kerCompToKer (h ∘ₗ g) ∘ d.b) d.w₂)))
    {δ₃ : TauCeti.detLine K (Q ⧸ range (h ∘ₗ g))}
    (hδ₃ : (δ₃ : ExteriorAlgebra K (Q ⧸ range (h ∘ₗ g))) = ExteriorAlgebra.ιMulti K _ (Fin.append
      (Submodule.factor (range_comp_le_range f (h ∘ₗ g)) ∘ (g ∘ₗ f).cokerToCokerComp h ∘ d.y)
      (Submodule.factor (range_comp_le_range f (h ∘ₗ g)) ∘ d.e)))
    {χ₃ : Dual K (TauCeti.detLine K (Q ⧸ range (h ∘ₗ g)))} (hχ₃ : χ₃ δ₃ = 1)
    (φ : Dual K (TauCeti.detLine K (Q ⧸ range (h ∘ₗ g ∘ₗ f)))) :
    f.detLineCompEquiv (h ∘ₗ g) (E.β ⊗ₜ φ) = φ E.ε •
      ((exteriorPower.ιMulti K _ (Module.finBasis K (ker f)) ⊗ₜ E.ψ₁) ⊗ₜ
        (((-1 : K) ^ (finrank K (range (f.kerToCoker g)) *
          finrank K (range ((g ∘ₗ f).kerCompToKer h))) • β₂) ⊗ₜ χ₃)) := by
  have d₄ := g.finrank_quotient_range_comp_eq_finrank_range_cokerToCokerComp_add h
  obtain ⟨-, -, -, c₆, -⟩ := finrank_assoc f g h
  have c₇ := f.finrank_range_kerToCoker_comp_eq_add g h
  have hβ' : (E.β : ExteriorAlgebra K (ker (h ∘ₗ g ∘ₗ f))) = ExteriorAlgebra.ιMulti K _
      (Fin.append (Submodule.inclusion (ker_le_ker_comp f (h ∘ₗ g)) ∘ Module.finBasis K (ker f))
        (Fin.append (Submodule.inclusion (ker_le_ker_comp (g ∘ₗ f) h) ∘ d.v) d.b ∘
          Fin.cast c₆)) := by
    rw [E.hβ]
    simp only [← ExteriorAlgebra.ιMulti_mul_ιMulti, TauCeti.ExteriorAlgebra.ιMulti_comp_cast,
      Fin.comp_append, ← Function.comp_assoc, mul_assoc, ← LinearMap.coe_comp,
      Submodule.inclusion_comp_inclusion]
  -- `β₂` lists the images of `v`, `w`, `b` and `w₂`; the composition law wants `v`, `b`, `w`, `w₂`.
  have hβ₂' : ((((-1 : K) ^ (finrank K (range (f.kerToCoker g)) *
      finrank K (range ((g ∘ₗ f).kerCompToKer h)))) • β₂ : TauCeti.detLine K (ker (h ∘ₗ g))) :
        ExteriorAlgebra K (ker (h ∘ₗ g))) = ExteriorAlgebra.ιMulti K _
      (Fin.append (f.kerCompToKer (h ∘ₗ g) ∘ (Fin.append
        (Submodule.inclusion (ker_le_ker_comp (g ∘ₗ f) h) ∘ d.v) d.b ∘ Fin.cast c₆))
        (Fin.append (Submodule.inclusion (ker_le_ker_comp g h) ∘ d.w) d.w₂ ∘ Fin.cast c₇)) := by
    rw [Submodule.coe_smul, hβ₂]
    simp only [← ExteriorAlgebra.ιMulti_mul_ιMulti, TauCeti.ExteriorAlgebra.ιMulti_comp_cast,
      Fin.comp_append, ← Function.comp_assoc, mul_assoc, ← LinearMap.coe_comp,
      kerCompToKer_comp_inclusion]
    rw [ExteriorAlgebra.ιMulti_mul_ιMulti_mul_eq_neg_one_pow_smul
      (i := finrank K (range ((g ∘ₗ f).kerCompToKer h))), mul_smul_comm]
  have hδ₁' : (E.δ₁ : ExteriorAlgebra K (N ⧸ range f)) = ExteriorAlgebra.ιMulti K _
      (Fin.append (f.kerToCoker (h ∘ₗ g) ∘
        (Fin.append (Submodule.inclusion (ker_le_ker_comp g h) ∘ d.w) d.w₂ ∘ Fin.cast c₇))
        d.x) := by
    rw [E.hδ₁]
    simp only [← ExteriorAlgebra.ιMulti_mul_ιMulti, TauCeti.ExteriorAlgebra.ιMulti_comp_cast,
      Fin.comp_append, ← Function.comp_assoc, mul_assoc, ← LinearMap.coe_comp,
      kerToCoker_comp_inclusion]
  have hε' : (E.ε : ExteriorAlgebra K (Q ⧸ range (h ∘ₗ g ∘ₗ f))) = ExteriorAlgebra.ιMulti K _
      (Fin.append (f.cokerToCokerComp (h ∘ₗ g) ∘ d.x)
        (Fin.append ((g ∘ₗ f).cokerToCokerComp h ∘ d.y) d.e ∘ Fin.cast d₄)) := by
    rw [E.hε]
    simp only [← ExteriorAlgebra.ιMulti_mul_ιMulti, TauCeti.ExteriorAlgebra.ιMulti_comp_cast,
      Fin.comp_append, ← Function.comp_assoc, mul_assoc, ← LinearMap.coe_comp,
      cokerToCokerComp_comp_cokerToCokerComp]
  have hδ₃' : exteriorPower.ιMulti K _ (Submodule.factor (range_comp_le_range f (h ∘ₗ g)) ∘
      (Fin.append ((g ∘ₗ f).cokerToCokerComp h ∘ d.y) d.e ∘ Fin.cast d₄)) = δ₃ := by
    refine Subtype.ext ?_
    rw [exteriorPower.ιMulti_apply_coe, hδ₃]
    simp only [← ExteriorAlgebra.ιMulti_mul_ιMulti, TauCeti.ExteriorAlgebra.ιMulti_comp_cast,
      Fin.comp_append, ← Function.comp_assoc]
  rw [f.detLineCompEquiv_tmul (h ∘ₗ g) _ _ _ _ _ hβ' hβ₂' hδ₁' hε' φ E.hψ₁
    (by rw [hδ₃']; exact hχ₃)]

/-- The composition law of `h ∘ g` on `β₂ ⊗ χ₃`: the second step of the right composite. -/
private theorem assoc_right_tmul₂ {d : AssocData f g h} (E : AssocElems f g h d)
    {β₂ : TauCeti.detLine K (ker (h ∘ₗ g))}
    (hβ₂ : (β₂ : ExteriorAlgebra K (ker (h ∘ₗ g))) = ExteriorAlgebra.ιMulti K _
      (Fin.append (Submodule.inclusion (ker_le_ker_comp g h) ∘
        Fin.append (f.kerCompToKer g ∘ d.v) d.w) (Fin.append (f.kerCompToKer (h ∘ₗ g) ∘ d.b) d.w₂)))
    {δ₃ : TauCeti.detLine K (Q ⧸ range (h ∘ₗ g))}
    (hδ₃ : (δ₃ : ExteriorAlgebra K (Q ⧸ range (h ∘ₗ g))) = ExteriorAlgebra.ιMulti K _ (Fin.append
      (Submodule.factor (range_comp_le_range f (h ∘ₗ g)) ∘ (g ∘ₗ f).cokerToCokerComp h ∘ d.y)
      (Submodule.factor (range_comp_le_range f (h ∘ₗ g)) ∘ d.e)))
    (χ₃ : Dual K (TauCeti.detLine K (Q ⧸ range (h ∘ₗ g)))) :
    g.detLineCompEquiv h (β₂ ⊗ₜ χ₃) = χ₃ δ₃ • ((E.γ₂ ⊗ₜ E.ψ₂) ⊗ₜ (E.γ₃ ⊗ₜ E.χ)) := by
  have a₂ := f.finrank_ker_eq_finrank_range_kerCompToKer_add g
  obtain ⟨-, -, -, -, c₁₀⟩ := finrank_assoc f g h
  have hβ₂' : (β₂ : ExteriorAlgebra K (ker (h ∘ₗ g))) = ExteriorAlgebra.ιMulti K _
      (Fin.append (Submodule.inclusion (ker_le_ker_comp g h) ∘
        (Fin.append (f.kerCompToKer g ∘ d.v) d.w ∘ Fin.cast a₂))
        (Fin.append (f.kerCompToKer (h ∘ₗ g) ∘ d.b) d.w₂ ∘ Fin.cast c₁₀)) := by
    rw [hβ₂]
    simp only [← ExteriorAlgebra.ιMulti_mul_ιMulti, TauCeti.ExteriorAlgebra.ιMulti_comp_cast,
      Fin.comp_append, ← Function.comp_assoc]
  have hγ₃' : (E.γ₃ : ExteriorAlgebra K (ker h)) = ExteriorAlgebra.ιMulti K _
      (Fin.append (g.kerCompToKer h ∘
        (Fin.append (f.kerCompToKer (h ∘ₗ g) ∘ d.b) d.w₂ ∘ Fin.cast c₁₀)) d.c) := by
    rw [E.hγ₃]
    simp only [← ExteriorAlgebra.ιMulti_mul_ιMulti, TauCeti.ExteriorAlgebra.ιMulti_comp_cast,
      Fin.comp_append, ← Function.comp_assoc, mul_assoc, ← LinearMap.coe_comp,
      kerCompToKer_comp_kerCompToKer]
  have hδ₃' : (δ₃ : ExteriorAlgebra K (Q ⧸ range (h ∘ₗ g))) = ExteriorAlgebra.ιMulti K _
      (Fin.append (g.cokerToCokerComp h ∘ (Submodule.factor (range_comp_le_range f g) ∘ d.y))
        (Submodule.factor (range_comp_le_range f (h ∘ₗ g)) ∘ d.e)) := by
    rw [hδ₃]
    simp only [← Function.comp_assoc, ← LinearMap.coe_comp, factor_comp_cokerToCokerComp]
  have hγ₂' : exteriorPower.ιMulti K _ (Fin.append (f.kerCompToKer g ∘ d.v) d.w ∘ Fin.cast a₂) =
      E.γ₂ :=
    Subtype.ext (by rw [exteriorPower.ιMulti_apply_coe, TauCeti.ExteriorAlgebra.ιMulti_comp_cast,
      E.hγ₂])
  rw [g.detLineCompEquiv_tmul h _ _ _ _ _ hβ₂' hγ₃' E.hδ₂ hδ₃' χ₃ E.hψ₂
      (by rw [← Function.comp_assoc, ← LinearMap.coe_comp, Submodule.factor_comp]; exact E.hχ),
    hγ₂']

/-- The right composite `det ((h ∘ g) ∘ f) → det f ⊗ det (h ∘ g) → det f ⊗ (det g ⊗ det h)` on
`β ⊗ φ`. -/
private theorem assoc_right_tmul {d : AssocData f g h} (E : AssocElems f g h d)
    (φ : Dual K (TauCeti.detLine K (Q ⧸ range (h ∘ₗ g ∘ₗ f)))) :
    (g.detLineCompEquiv h).lTensor f.detLine (f.detLineCompEquiv (h ∘ₗ g) (E.β ⊗ₜ φ)) =
      (φ E.ε * (-1) ^ (finrank K (range (f.kerToCoker g)) *
          finrank K (range ((g ∘ₗ f).kerCompToKer h)))) •
        ((exteriorPower.ιMulti K _ (Module.finBasis K (ker f)) ⊗ₜ E.ψ₁) ⊗ₜ
          ((E.γ₂ ⊗ₜ E.ψ₂) ⊗ₜ (E.γ₃ ⊗ₜ E.χ))) := by
  have a₂ := f.finrank_ker_eq_finrank_range_kerCompToKer_add g
  have d₁ := g.finrank_ker_comp_eq_finrank_ker_add h
  have d₄ := g.finrank_quotient_range_comp_eq_finrank_range_cokerToCokerComp_add h
  obtain ⟨-, -, -, -, c₁₀⟩ := finrank_assoc f g h
  obtain ⟨δ₃, χ₃, hδ₃, hχ₃⟩ := TauCeti.exists_detLine_coe_eq_ιMulti_and_apply_eq_one d₄ d.li_cokerhg
  obtain ⟨β₂, hβ₂⟩ := TauCeti.exists_detLine_coe_eq_ιMulti (R := K) (V := ker (h ∘ₗ g)) (by omega)
    (Fin.append (Submodule.inclusion (ker_le_ker_comp g h) ∘
      Fin.append (f.kerCompToKer g ∘ d.v) d.w) (Fin.append (f.kerCompToKer (h ∘ₗ g) ∘ d.b) d.w₂))
  rw [assoc_right_tmul₁ f g h E hβ₂ hδ₃ hχ₃ φ, map_smul, LinearEquiv.lTensor_tmul,
    ← TensorProduct.smul_tmul', map_smul, assoc_right_tmul₂ f g h E hβ₂ hδ₃ χ₃, hχ₃, one_smul,
    TensorProduct.tmul_smul, smul_smul]

variable [FiniteDimensional K (ker (g ∘ₗ f))] [FiniteDimensional K (P ⧸ range (g ∘ₗ f))]

/-- The composition law of `h ∘ (g ∘ f)` on `β ⊗ φ`: the first step of the left composite. -/
private theorem assoc_left_tmul₁ {d : AssocData f g h} (E : AssocElems f g h d)
    {α : TauCeti.detLine K (ker (g ∘ₗ f))}
    (hα : (α : ExteriorAlgebra K (ker (g ∘ₗ f))) = ExteriorAlgebra.ιMulti K _
      (Fin.append (Submodule.inclusion (ker_le_ker_comp f g) ∘ Module.finBasis K (ker f)) d.v))
    {δ₀ : TauCeti.detLine K (P ⧸ range (g ∘ₗ f))}
    (hδ₀ : (δ₀ : ExteriorAlgebra K (P ⧸ range (g ∘ₗ f))) = ExteriorAlgebra.ιMulti K _ (Fin.append
      (Fin.append (f.cokerToCokerComp g ∘ f.kerToCoker (h ∘ₗ g) ∘ d.w₂)
        (f.cokerToCokerComp g ∘ d.x)) (Fin.append ((g ∘ₗ f).kerToCoker h ∘ d.c) d.y)))
    {ψ₀ : Dual K (TauCeti.detLine K (P ⧸ range (g ∘ₗ f)))} (hψ₀ : ψ₀ δ₀ = 1)
    (φ : Dual K (TauCeti.detLine K (Q ⧸ range (h ∘ₗ g ∘ₗ f)))) :
    (g ∘ₗ f).detLineCompEquiv h (E.β ⊗ₜ φ) =
      φ E.ε • ((α ⊗ₜ ((-1 : K) ^ (finrank K (range (f.cokerToCokerComp (h ∘ₗ g))) *
        finrank K (range (g.kerToCoker h))) • ψ₀)) ⊗ₜ (E.γ₃ ⊗ₜ E.χ)) := by
  have a₁ := f.finrank_ker_comp_eq_finrank_ker_add g
  obtain ⟨c₂, c₃, -, -, -⟩ := finrank_assoc f g h
  have hβ' : (E.β : ExteriorAlgebra K (ker (h ∘ₗ g ∘ₗ f))) = ExteriorAlgebra.ιMulti K _
      (Fin.append (Submodule.inclusion (ker_le_ker_comp (g ∘ₗ f) h) ∘ (Fin.append
        (Submodule.inclusion (ker_le_ker_comp f g) ∘ Module.finBasis K (ker f)) d.v ∘
          Fin.cast a₁)) d.b) := by
    rw [E.hβ]
    simp only [← ExteriorAlgebra.ιMulti_mul_ιMulti, TauCeti.ExteriorAlgebra.ιMulti_comp_cast,
      Fin.comp_append, ← Function.comp_assoc]
  have hγ₃' : (E.γ₃ : ExteriorAlgebra K (ker h)) = ExteriorAlgebra.ιMulti K _
      (Fin.append ((g ∘ₗ f).kerCompToKer h ∘ d.b)
        (Fin.append (g.kerCompToKer h ∘ d.w₂) d.c ∘ Fin.cast c₂)) := by
    rw [E.hγ₃]
    simp only [← ExteriorAlgebra.ιMulti_mul_ιMulti, TauCeti.ExteriorAlgebra.ιMulti_comp_cast]
  -- `δ₀` lists the images of `w₂`, `x`, `c` and `y`; the composition law wants `w₂`, `c`, `x`, `y`.
  have hδ₀' : ((((-1 : K) ^ (finrank K (range (f.cokerToCokerComp (h ∘ₗ g))) *
      finrank K (range (g.kerToCoker h)))) • δ₀ : TauCeti.detLine K (P ⧸ range (g ∘ₗ f))) :
        ExteriorAlgebra K (P ⧸ range (g ∘ₗ f))) = ExteriorAlgebra.ιMulti K _
      (Fin.append ((g ∘ₗ f).kerToCoker h ∘ (Fin.append (g.kerCompToKer h ∘ d.w₂) d.c ∘
        Fin.cast c₂)) (Fin.append (f.cokerToCokerComp g ∘ d.x) d.y ∘ Fin.cast c₃)) := by
    rw [Submodule.coe_smul, hδ₀]
    simp only [← ExteriorAlgebra.ιMulti_mul_ιMulti, TauCeti.ExteriorAlgebra.ιMulti_comp_cast,
      Fin.comp_append, ← Function.comp_assoc, mul_assoc, ← LinearMap.coe_comp,
      kerToCoker_comp_kerCompToKer]
    rw [ExteriorAlgebra.ιMulti_mul_ιMulti_mul_eq_neg_one_pow_smul
      (i := finrank K (range (g.kerToCoker h))), mul_smul_comm]
  have hε' : (E.ε : ExteriorAlgebra K (Q ⧸ range (h ∘ₗ g ∘ₗ f))) = ExteriorAlgebra.ιMulti K _
      (Fin.append ((g ∘ₗ f).cokerToCokerComp h ∘
        (Fin.append (f.cokerToCokerComp g ∘ d.x) d.y ∘ Fin.cast c₃)) d.e) := by
    rw [E.hε]
    simp only [← ExteriorAlgebra.ιMulti_mul_ιMulti, TauCeti.ExteriorAlgebra.ιMulti_comp_cast,
      Fin.comp_append, ← Function.comp_assoc]
  have hψ₀' : ((-1 : K) ^ (finrank K (range (f.cokerToCokerComp (h ∘ₗ g))) *
      finrank K (range (g.kerToCoker h))) • ψ₀)
        ((-1 : K) ^ (finrank K (range (f.cokerToCokerComp (h ∘ₗ g))) *
          finrank K (range (g.kerToCoker h))) • δ₀) = 1 := by
    simp [hψ₀, ← mul_pow]
  have hα' : exteriorPower.ιMulti K _ (Fin.append (Submodule.inclusion (ker_le_ker_comp f g) ∘
      Module.finBasis K (ker f)) d.v ∘ Fin.cast a₁) = α :=
    Subtype.ext (by rw [exteriorPower.ιMulti_apply_coe, TauCeti.ExteriorAlgebra.ιMulti_comp_cast,
      hα])
  rw [(g ∘ₗ f).detLineCompEquiv_tmul h _ _ _ _ _ hβ' hγ₃' hδ₀' hε' φ hψ₀' E.hχ, hα']

/-- The left composite `det (h ∘ g ∘ f) → det (g ∘ f) ⊗ det h → (det f ⊗ det g) ⊗ det h`, followed
by the associator, on `β ⊗ φ`. -/
private theorem assoc_left_tmul {d : AssocData f g h} (E : AssocElems f g h d)
    (φ : Dual K (TauCeti.detLine K (Q ⧸ range (h ∘ₗ g ∘ₗ f)))) :
    TensorProduct.assoc K _ _ _
        ((f.detLineCompEquiv g).rTensor h.detLine ((g ∘ₗ f).detLineCompEquiv h (E.β ⊗ₜ φ))) =
      (φ E.ε * (-1) ^ (finrank K (range (f.cokerToCokerComp (h ∘ₗ g))) *
          finrank K (range (g.kerToCoker h)))) •
        ((exteriorPower.ιMulti K _ (Module.finBasis K (ker f)) ⊗ₜ E.ψ₁) ⊗ₜ
          ((E.γ₂ ⊗ₜ E.ψ₂) ⊗ₜ (E.γ₃ ⊗ₜ E.χ))) := by
  have a₁ := f.finrank_ker_comp_eq_finrank_ker_add g
  have b₃ := (g ∘ₗ f).finrank_quotient_range_eq_finrank_range_kerToCoker_add h
  obtain ⟨c₂, c₃, -, -, -⟩ := finrank_assoc f g h
  obtain ⟨δ₀, ψ₀, hδ₀, hψ₀⟩ :=
    TauCeti.exists_detLine_coe_eq_ιMulti_and_apply_eq_one (by omega) d.li_cokergf
  obtain ⟨α, hα⟩ := TauCeti.exists_detLine_coe_eq_ιMulti (R := K) (V := ker (g ∘ₗ f)) a₁
    (Fin.append (Submodule.inclusion (ker_le_ker_comp f g) ∘ Module.finBasis K (ker f)) d.v)
  rw [assoc_left_tmul₁ f g h E hα hδ₀ hψ₀ φ, map_smul, LinearEquiv.rTensor_tmul,
    assoc_left_tmul₂ f g h E hα hδ₀]
  simp only [map_smul, ← TensorProduct.smul_tmul', TensorProduct.assoc_tmul, LinearMap.smul_apply,
    hψ₀, smul_smul, smul_eq_mul, mul_one]

/-- Elements of the determinant lines adapted to `d` exist. -/
private theorem nonempty_assocElems (d : AssocData f g h) : Nonempty (AssocElems f g h d) := by
  have : FiniteDimensional K (ker (h ∘ₗ g ∘ₗ f)) := Module.Finite.ker_comp (g ∘ₗ f) h
  have : FiniteDimensional K (Q ⧸ range (h ∘ₗ g ∘ₗ f)) :=
    Module.Finite.quotient_range_comp (g ∘ₗ f) h
  have a₁ := f.finrank_ker_comp_eq_finrank_ker_add g
  have a₂ := f.finrank_ker_eq_finrank_range_kerCompToKer_add g
  have a₃ := f.finrank_quotient_range_eq_finrank_range_kerToCoker_add g
  have b₁ := (g ∘ₗ f).finrank_ker_comp_eq_finrank_ker_add h
  have b₂ := (g ∘ₗ f).finrank_ker_eq_finrank_range_kerCompToKer_add h
  have b₄ := (g ∘ₗ f).finrank_quotient_range_comp_eq_finrank_range_cokerToCokerComp_add h
  have d₃ := g.finrank_quotient_range_eq_finrank_range_kerToCoker_add h
  obtain ⟨c₂, c₃, c₄, -, -⟩ := finrank_assoc f g h
  obtain ⟨β, η, hβ, hη⟩ := TauCeti.exists_detLine_coe_eq_ιMulti_and_apply_eq_one (by omega) d.li_ker
  obtain ⟨γ₂, hγ₂⟩ := TauCeti.exists_detLine_coe_eq_ιMulti (R := K) (V := ker g) (by omega)
    (Fin.append (f.kerCompToKer g ∘ d.v) d.w)
  obtain ⟨γ₃, hγ₃⟩ := TauCeti.exists_detLine_coe_eq_ιMulti (R := K) (V := ker h) (by omega)
    (Fin.append ((g ∘ₗ f).kerCompToKer h ∘ d.b) (Fin.append (g.kerCompToKer h ∘ d.w₂) d.c))
  obtain ⟨ε, hε⟩ := TauCeti.exists_detLine_coe_eq_ιMulti (R := K) (V := Q ⧸ range (h ∘ₗ g ∘ₗ f))
    (by omega) (Fin.append ((g ∘ₗ f).cokerToCokerComp h ∘
      Fin.append (f.cokerToCokerComp g ∘ d.x) d.y) d.e)
  obtain ⟨δ₁, ψ₁, hδ₁, hψ₁⟩ :=
    TauCeti.exists_detLine_coe_eq_ιMulti_and_apply_eq_one (by omega) d.li_cokerf
  obtain ⟨δ₂, ψ₂, hδ₂, hψ₂⟩ := TauCeti.exists_detLine_coe_eq_ιMulti_and_apply_eq_one d₃ d.li_cokerg
  obtain ⟨χ, hχ⟩ :=
    Projective.exists_dual_eq_one K ((exteriorPower.ιMulti_ne_zero_iff _).2 d.li_cokerh)
  exact ⟨⟨β, η, γ₂, γ₃, ε, δ₁, ψ₁, δ₂, ψ₂, χ, hβ, hη, hγ₂, hγ₃, hε, hδ₁, hψ₁, hδ₂, hψ₂, hχ⟩⟩

/-! ### Associativity -/

/-- **Associativity of the composition law of determinant lines.** For linear maps
`f : M → N`, `g : N → P` and `h : P → Q` with finite-dimensional kernels and cokernels, the two
ways of splitting `det (h ∘ g ∘ f)` with the composition law (`LinearMap.detLineCompEquiv`), first
off `h` and then off `f`, or first off `f` and then off `h`, agree up to the Koszul sign
`(-1) ^ (r₁ r₂ + r₃ r₄)`. Here `r₁` and `r₂` are the ranks of the connecting map
`ker g → coker f` and of `ker (h ∘ g ∘ f) → ker h`, and `r₃` and `r₄` those of
`coker f → coker (h ∘ g ∘ f)` and of the connecting map `ker h → coker g`.

The sign can be nontrivial. For `f : K → K²` the first inclusion, `g` the projection of `K²` onto
the first coordinate line and `h : K² → K` the second coordinate, `r₁ = r₂ = 1` and `r₃ = 0`, so
the two isomorphisms differ by `-1`, which is not `1` unless `K` has characteristic two.

The composite maps `g ∘ f` and `h ∘ g` need finite-dimensional kernels and cokernels for their
composition laws to be defined. These are instance arguments that the caller must supply; they
follow from the assumptions on `f`, `g` and `h` by `Module.Finite.ker_comp` and
`Module.Finite.quotient_range_comp`, for instance `haveI := Module.Finite.ker_comp g h`.

The statement applies `f.detLineCompEquiv (h ∘ g)`, whose domain is `det ((h ∘ g) ∘ f)`, to
`x : det (h ∘ g ∘ f)`: it type-checks because `(h ∘ g) ∘ f` and `h ∘ (g ∘ f)` are definitionally
equal (`LinearMap.comp_assoc` holds by `rfl`). -/
theorem detLineCompEquiv_assoc (x : (h ∘ₗ g ∘ₗ f).detLine) :
    TensorProduct.assoc K _ _ _
        ((f.detLineCompEquiv g).rTensor h.detLine ((g ∘ₗ f).detLineCompEquiv h x)) =
      (-1 : K) ^ (finrank K (range (f.kerToCoker g)) *
          finrank K (range ((g ∘ₗ f).kerCompToKer h)) +
        finrank K (range (f.cokerToCokerComp (h ∘ₗ g))) * finrank K (range (g.kerToCoker h))) •
        (g.detLineCompEquiv h).lTensor f.detLine (f.detLineCompEquiv (h ∘ₗ g) x) := by
  have : FiniteDimensional K (ker (h ∘ₗ g ∘ₗ f)) := Module.Finite.ker_comp (g ∘ₗ f) h
  obtain ⟨d⟩ := nonempty_assocData f g h
  obtain ⟨E⟩ := nonempty_assocElems f g h d
  -- Both sides are linear in `x`; by `η z • β = z`, it suffices to compare them on `β ⊗ φ`.
  induction x using TensorProduct.inductionOn with
  | add x₁ x₂ h₁ h₂ => simp only [map_add, h₁, h₂, smul_add]
  | tmul z φ =>
    rw [← Module.Invertible.apply_smul_eq_self E.hη z, ← TensorProduct.smul_tmul', map_smul,
      map_smul, map_smul, map_smul, map_smul, assoc_left_tmul f g h E φ,
      assoc_right_tmul f g h E φ, smul_smul, smul_smul, smul_smul]
    congr 1
    have hsq : ((-1 : K) ^ (finrank K (range (f.kerToCoker g)) *
        finrank K (range ((g ∘ₗ f).kerCompToKer h)))) * (-1) ^ (finrank K
          (range (f.kerToCoker g)) * finrank K (range ((g ∘ₗ f).kerCompToKer h))) = 1 := by
      simp [← mul_pow]
    rw [pow_add]
    linear_combination (-(E.η z * φ E.ε * (-1) ^ (finrank K (range (f.cokerToCokerComp (h ∘ₗ g))) *
      finrank K (range (g.kerToCoker h))))) * hsq

end Assoc

end LinearMap
