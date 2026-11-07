/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Determinant.Exact
public import TauCeti.LinearAlgebra.Exact
public import TauCeti.RingTheory.Finiteness.Finsupp

/-!
# The determinant line of a composition

For linear maps `f : M → N` and `g : N → P` between vector spaces whose kernels and cokernels
are finite-dimensional, the kernels and cokernels of `f`, `g` and `g ∘ f` form the exact sequence

`0 → ker f → ker (g ∘ f) → ker g → coker f → coker (g ∘ f) → coker g → 0`

(`LinearMap.kerCompToKer`, `LinearMap.kerToCoker`, `LinearMap.cokerToCokerComp`, with the
inclusion of kernels first and the quotient map of cokernels last). Its alternating sum of
dimensions is the additivity of the index under composition (`LinearMap.index_comp`). Its
determinant lines give the finer, canonical statement

`det (g ∘ f) ≃ det f ⊗ det g`

for the determinant lines `det f = det (ker f) ⊗ (det (coker f))^*` (`LinearMap.detLine`), with no
choice of bases or complements (`LinearMap.detLineCompEquiv`). This is
`TauCeti.detLineSixTermEquiv` for that sequence.

For Fredholm operators this is the composition law of determinant lines. It is how orientations of
the determinant lines of two operators, for instance of the linearized operators along two
pieces of a broken trajectory or of a change of trivialization, orient the determinant line of
their composite.

## Main declarations

* `LinearMap.detLineCompEquiv`: the isomorphism `det (g ∘ f) ≃ det f ⊗ det g`.
* `LinearMap.detLineCompEquiv_tmul`: its value on exterior products.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., AMS
  Colloquium Publications **52**, 2012, Appendix A.2 (determinant lines of exact sequences).
* A. Zinger, *The determinant line bundle for Fredholm operators: construction, properties,
  and classification*, Math. Scand. **118** (2016), 203–268, arXiv:1304.6368.
-/

public section

noncomputable section

open Module TensorProduct

namespace LinearMap

variable {K : Type*} [Field K] {M N P : Type*} [AddCommGroup M] [Module K M] [AddCommGroup N]
  [Module K N] [AddCommGroup P] [Module K P] (f : M →ₗ[K] N) (g : N →ₗ[K] P)
  [FiniteDimensional K (ker f)] [FiniteDimensional K (ker g)]
  [FiniteDimensional K (N ⧸ range f)] [FiniteDimensional K (P ⧸ range g)]

/-- **The determinant line of a composition.** For linear maps `f : M → N` and `g : N → P` with
finite-dimensional kernels and cokernels, the canonical isomorphism
`det (g ∘ f) ≃ det f ⊗ det g` of determinant lines. It is `TauCeti.detLineSixTermEquiv` for the
exact sequence `0 → ker f → ker (g ∘ f) → ker g → coker f → coker (g ∘ f) → coker g → 0`; its value
on exterior products is `LinearMap.detLineCompEquiv_tmul`. -/
def detLineCompEquiv : (g ∘ₗ f).detLine ≃ₗ[K] f.detLine ⊗[K] g.detLine :=
  have : FiniteDimensional K (P ⧸ range (g ∘ₗ f)) := Module.Finite.quotient_range_comp f g
  TauCeti.detLineSixTermEquiv (Submodule.inclusion_injective (ker_le_ker_comp f g))
    (f.exact_inclusion_kerCompToKer g) (f.exact_kerCompToKer_kerToCoker g)
    (f.exact_kerToCoker_cokerToCokerComp g) (exact_mapQ_range_factor f g)
    (Submodule.factor_surjective _)

/-- **The value of `LinearMap.detLineCompEquiv` on exterior products.** Choose `u`, a family of
`dim (ker f)` vectors of `ker f`, and families `v`, `w`, `x` and `y` in `ker (g ∘ f)`, `ker g`,
`coker f` and `coker (g ∘ f)` whose images complete them along the exact sequence
`0 → ker f → ker (g ∘ f) → ker g → coker f → coker (g ∘ f) → coker g → 0`. Let `β`, `γ`, `δ` and
`ε` be the exterior products in `ker (g ∘ f)`, `ker g`, `coker f` and `coker (g ∘ f)` of the
images of `u`, `v`, `w` and `x` followed by `v`, `w`, `x` and `y`. If `ψ` takes the value `1` at
`δ` and `χ` takes the value `1` at the exterior product of the classes of `y` in `coker g`, then
`β ⊗ φ` goes to `φ ε • ((α ⊗ ψ) ⊗ (γ ⊗ χ))`, with `α` the exterior product of `u`. -/
theorem detLineCompEquiv_tmul (u : Fin (finrank K (ker f)) → ker f)
    (v : Fin (finrank K (range (f.kerCompToKer g))) → ker (g ∘ₗ f))
    (w : Fin (finrank K (range (f.kerToCoker g))) → ker g)
    (x : Fin (finrank K (range (f.cokerToCokerComp g))) → N ⧸ range f)
    (y : Fin (finrank K (P ⧸ range g)) → P ⧸ range (g ∘ₗ f))
    {β : TauCeti.detLine K (ker (g ∘ₗ f))} (hβ : (β : ExteriorAlgebra K (ker (g ∘ₗ f))) =
      ExteriorAlgebra.ιMulti K _ (Fin.append (Submodule.inclusion (ker_le_ker_comp f g) ∘ u) v))
    {γ : TauCeti.detLine K (ker g)} (hγ : (γ : ExteriorAlgebra K (ker g)) =
      ExteriorAlgebra.ιMulti K _ (Fin.append (f.kerCompToKer g ∘ v) w))
    {δ : TauCeti.detLine K (N ⧸ range f)} (hδ : (δ : ExteriorAlgebra K (N ⧸ range f)) =
      ExteriorAlgebra.ιMulti K _ (Fin.append (f.kerToCoker g ∘ w) x))
    {ε : TauCeti.detLine K (P ⧸ range (g ∘ₗ f))}
    (hε : (ε : ExteriorAlgebra K (P ⧸ range (g ∘ₗ f))) =
      ExteriorAlgebra.ιMulti K _ (Fin.append (f.cokerToCokerComp g ∘ x) y))
    (φ : Dual K (TauCeti.detLine K (P ⧸ range (g ∘ₗ f))))
    {ψ : Dual K (TauCeti.detLine K (N ⧸ range f))} (hψ : ψ δ = 1)
    {χ : Dual K (TauCeti.detLine K (P ⧸ range g))}
    (hχ : χ (exteriorPower.ιMulti K _ (Submodule.factor (range_comp_le_range f g) ∘ y)) = 1) :
    f.detLineCompEquiv g (β ⊗ₜ φ) = φ ε • ((exteriorPower.ιMulti K _ u ⊗ₜ ψ) ⊗ₜ (γ ⊗ₜ χ)) :=
  have : FiniteDimensional K (P ⧸ range (g ∘ₗ f)) := Module.Finite.quotient_range_comp f g
  TauCeti.detLineSixTermEquiv_tmul _ _ _ _ _ _ u v w x y hβ hγ hδ hε φ hψ hχ

end LinearMap
