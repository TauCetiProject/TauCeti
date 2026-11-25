/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.BilinearMap.Splitting
public import TauCeti.RepresentationTheory.Subrepresentation

/-!
# Equivariant splitting along a perfect pairing

Let `G` be a group, `a : U → V` and `b : U' → V'` intertwining maps of representations of `G`, and
`q : V →ₗ V' →ₗ W'` a `G`-equivariant pairing with values in a representation `σ` of `G`, i.e.
`q (g • v) (g • v') = σ g (q v v')`. This is encoded as an intertwining map
`q : ρV → linHom ρV' σ`. If `a` and `b` are compatible with a perfect pairing
`p : U →ₗ U' →ₗ W` and a linear isomorphism `φ : W → W'`, meaning `q (a x) (b y) = φ (p x y)`,
then the range of `a` and the annihilator `{v | ∀ y, q v (b y) = 0}` of the range of `b` are
complementary subrepresentations of `V`.

The annihilator is the kernel of the intertwining map `(b.lcomp σ).comp q : ρV → linHom ρU' σ`,
so it is a subrepresentation without further work. The values of `q` may carry a nontrivial
action: for a one-dimensional `W'` this is a character `χ` with
`q (g • v) (g • v') = χ g * q v v'`, as for the top degree of a cohomology ring with Galois
action. No equivariance of `p` or `φ` is needed.

For a multiplicative, `G`-equivariant map `f : A → B` of graded algebras satisfying Poincaré
duality that is an isomorphism in the top degree `n`, apply this with `a` and `b` the components
of `f` in degrees `i` and `n - i`: it gives the `G`-stable decomposition
`Bⁱ = f(Aⁱ) ⊕ f(Aⁿ⁻ⁱ)^⊥`. The underlying linear algebra is
`LinearMap.isCompl_range_ker_compl₂_of_compl₁₂_eq_compr₂`.

## Main results

* `Representation.IntertwiningMap.mem_ker_lcomp_comp`: membership in the annihilator
  subrepresentation.
* `Representation.IntertwiningMap.isCompl_range_ker_lcomp_comp`: the range of `a` and the
  annihilator of the range of `b` are complementary subrepresentations.

## References

* P. Scholze, *Perfectoid spaces*, Publ. Math. IHÉS 116 (2012), conclusion of the proof of
  Theorem 9.6.
-/

public section

namespace Representation.IntertwiningMap

section CommSemiring

variable {R G U' V V' W' : Type*} [CommSemiring R] [Group G]
  [AddCommMonoid U'] [Module R U'] [AddCommMonoid V] [Module R V]
  [AddCommMonoid V'] [Module R V'] [AddCommMonoid W'] [Module R W']
  {ρU' : Representation R G U'} {ρV : Representation R G V} {ρV' : Representation R G V'}
  {σ : Representation R G W'}

/-- The kernel of `(b.lcomp σ).comp q` is the annihilator of the range of `b` in the first
argument of the pairing `q`. -/
theorem mem_ker_lcomp_comp (b : IntertwiningMap ρU' ρV') (q : IntertwiningMap ρV (linHom ρV' σ))
    {v : V} : v ∈ ((b.lcomp σ).comp q).ker ↔ ∀ y, q v (b y) = 0 := by
  simp [LinearMap.ext_iff]

end CommSemiring

section CommRing

variable {R G U U' V V' W W' : Type*} [CommRing R] [Group G]
  [AddCommGroup U] [Module R U] [AddCommGroup U'] [Module R U']
  [AddCommGroup V] [Module R V] [AddCommGroup V'] [Module R V']
  [AddCommGroup W] [Module R W] [AddCommGroup W'] [Module R W']
  {ρU : Representation R G U} {ρU' : Representation R G U'}
  {ρV : Representation R G V} {ρV' : Representation R G V'} {σ : Representation R G W'}

/-- **Equivariant splitting along a perfect pairing.** If the intertwining maps `a` and `b` satisfy
`q (a x) (b y) = φ (p x y)` for an equivariant pairing `q`, a pairing `p` bijective onto
`U' →ₗ W` and a linear isomorphism `φ`, then the range of `a` and the annihilator
`{v | ∀ y, q v (b y) = 0}` of the range of `b` are complementary subrepresentations. -/
theorem isCompl_range_ker_lcomp_comp {p : U →ₗ[R] U' →ₗ[R] W} {φ : W ≃ₗ[R] W'}
    {a : IntertwiningMap ρU ρV} {b : IntertwiningMap ρU' ρV'}
    {q : IntertwiningMap ρV (linHom ρV' σ)}
    (h : q.toLinearMap.compl₁₂ a.toLinearMap b.toLinearMap = p.compr₂ φ.toLinearMap)
    (hp : Function.Bijective p) :
    IsCompl a.range ((b.lcomp σ).comp q).ker := by
  rw [← Subrepresentation.isCompl_toSubmodule, range_toSubmodule, ker_toSubmodule,
    lcomp_comp_toLinearMap]
  exact LinearMap.isCompl_range_ker_compl₂_of_compl₁₂_eq_compr₂ h hp

end CommRing

end Representation.IntertwiningMap
