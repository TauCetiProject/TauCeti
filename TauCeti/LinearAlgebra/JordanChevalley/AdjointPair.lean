/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.JordanChevalley
public import TauCeti.LinearAlgebra.SesquilinearForm.AdjointPair

/-!
# Jordan–Chevalley decompositions of adjoint pairs

Let `B` be a bilinear map on a module `V` which is right-separating, `B v w = 0` for all `v` only
when `w = 0`, and let `(f, g)` be an adjoint pair of endomorphisms, `B (f v) w = B v (g w)`
(`LinearMap.IsAdjointPair B B f g`). Since `p(f)` and `p(g)` are adjoint for every polynomial `p`
(`LinearMap.IsAdjointPair.aeval`), `B` determines `g` from `f`
(`LinearMap.IsAdjointPair.right_unique`), every polynomial killing `f` kills `g`
(`LinearMap.IsAdjointPair.aeval_eq_zero`), and if a polynomial in `f` is nilpotent then so is the
same polynomial in `g` (`LinearMap.IsAdjointPair.isNilpotent_aeval`). For a finite-dimensional
vector space the same holds for semisimplicity (`LinearMap.IsAdjointPair.isSemisimple_aeval`).

Over a perfect field the nilpotent and semisimple parts of the Jordan–Chevalley decomposition
`f = n + s` are polynomials in `f`. Applying the same polynomials to `g` gives a commuting nilpotent
and semisimple pair adding up to `g`, so by uniqueness of the decomposition **the adjoint of the
nilpotent part is the nilpotent part of the adjoint, and likewise for the semisimple part**
(`LinearMap.IsAdjointPair.isAdjointPair_of_isNilpotent_of_add`,
`LinearMap.IsAdjointPair.isAdjointPair_of_isSemisimple_of_add`).

For a skew-adjoint endomorphism `f`, whose adjoint is `-f` with decomposition `-n + -s`, this says
that both parts of `f` are again skew-adjoint
(`LinearMap.IsSkewAdjoint.of_isNilpotent_of_add`, `LinearMap.IsSkewAdjoint.of_isSemisimple_of_add`).
So the Lie algebra of skew-adjoint endomorphisms of a nondegenerate form, such as a symplectic Lie
algebra `sp(V, ω)` or an orthogonal Lie algebra, contains the Jordan–Chevalley parts of its
elements.

## Main results

* `LinearMap.IsAdjointPair.isAdjointPair_of_isNilpotent_of_add`,
  `LinearMap.IsAdjointPair.isAdjointPair_of_isSemisimple_of_add`: the Jordan–Chevalley parts of an
  adjoint pair are adjoint pairs.
* `LinearMap.IsSkewAdjoint.of_isNilpotent_of_add`, `LinearMap.IsSkewAdjoint.of_isSemisimple_of_add`:
  the Jordan–Chevalley parts of a skew-adjoint endomorphism are skew-adjoint.

## References

* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, GTM 9, §4.2 (the
  Jordan–Chevalley decomposition) and §1.2 (the classical Lie algebras as skew-adjoint
  endomorphisms).
-/

public section

open Module Module.End Polynomial

namespace LinearMap

namespace IsAdjointPair

section Field

variable {K V M : Type*} [Field K] [AddCommGroup V] [Module K V] [AddCommGroup M] [Module K M]
  {B : V →ₗ[K] V →ₗ[K] M} {f g : Module.End K V}

/-- For a right-separating bilinear map on a finite-dimensional space, if `p(f)` is semisimple
then so is `p(g)` for the adjoint `g` of `f`: the squarefree minimal polynomial of `p(f)` also
kills `p(g)`. -/
theorem isSemisimple_aeval [FiniteDimensional K V] (hB : B.SeparatingRight)
    (h : IsAdjointPair B B f g) {p : K[X]} (hp : (Polynomial.aeval f p).IsSemisimple) :
    (Polynomial.aeval g p).IsSemisimple := by
  refine isSemisimple_of_squarefree_aeval_eq_zero hp.minpoly_squarefree ?_
  rw [← Polynomial.aeval_comp]
  exact h.aeval_eq_zero hB (by rw [Polynomial.aeval_comp, minpoly.aeval])

variable [PerfectField K] [FiniteDimensional K V]

/-- Both Jordan–Chevalley parts of an adjoint pair are adjoint pairs. -/
private theorem isAdjointPair_and_isAdjointPair_of_add (hB : B.SeparatingRight)
    (h : IsAdjointPair B B f g) {n s n' s' : Module.End K V} (hc : Commute n s)
    (hn : IsNilpotent n) (hs : s.IsSemisimple) (hf : f = n + s) (hc' : Commute n' s')
    (hn' : IsNilpotent n') (hs' : s'.IsSemisimple) (hg : g = n' + s') :
    IsAdjointPair B B n n' ∧ IsAdjointPair B B s s' := by
  -- By uniqueness of the decomposition, `n` and `s` are polynomials `p(f)` and `q(f)`.
  obtain ⟨n₀, hn₀, s₀, hs₀, hn₀nil, hs₀ss, hf₀⟩ := f.exists_isNilpotent_isSemisimple
  have hc₀ : Commute n₀ s₀ := Algebra.commute_of_mem_adjoin_singleton_of_commute hs₀
    (Algebra.commute_of_mem_adjoin_self hn₀).symm
  obtain ⟨rfl, rfl⟩ := isNilpotent_isSemisimple_unique hn₀nil hs₀ss hn hs hc₀ hc
    (hf₀.symm.trans hf)
  rw [Algebra.adjoin_singleton_eq_range_aeval, AlgHom.mem_range] at hn₀ hs₀
  obtain ⟨p, rfl⟩ := hn₀
  obtain ⟨q, rfl⟩ := hs₀
  -- Then `p(g)` and `q(g)` are a nilpotent and a semisimple commuting pair adding up to `g`.
  have hsum : Polynomial.aeval g p + Polynomial.aeval g q = g := by
    have h₀ := h.aeval (p + q)
    rw [map_add, ← hf] at h₀
    rw [← map_add]
    exact (right_unique hB h h₀).symm
  have hcomm : Commute (Polynomial.aeval g p) (Polynomial.aeval g q) := by
    rw [commute_iff_eq, ← map_mul, ← map_mul, mul_comm]
  obtain ⟨hp, hq⟩ := isNilpotent_isSemisimple_unique (h.isNilpotent_aeval hB hn)
    (h.isSemisimple_aeval hB hs) hn' hs' hcomm hc' (hsum.trans hg)
  exact ⟨hp ▸ h.aeval p, hq ▸ h.aeval q⟩

/-- **The adjoint of the nilpotent part is the nilpotent part of the adjoint.** If `(f, g)` is an
adjoint pair for a right-separating `B` and `f = n + s`, `g = n' + s'` are Jordan–Chevalley
decompositions, then `(n, n')` is an adjoint pair. -/
theorem isAdjointPair_of_isNilpotent_of_add (hB : B.SeparatingRight) (h : IsAdjointPair B B f g)
    {n s n' s' : Module.End K V} (hc : Commute n s) (hn : IsNilpotent n) (hs : s.IsSemisimple)
    (hf : f = n + s) (hc' : Commute n' s') (hn' : IsNilpotent n') (hs' : s'.IsSemisimple)
    (hg : g = n' + s') : IsAdjointPair B B n n' :=
  (isAdjointPair_and_isAdjointPair_of_add hB h hc hn hs hf hc' hn' hs' hg).1

/-- **The adjoint of the semisimple part is the semisimple part of the adjoint.** If `(f, g)` is
an adjoint pair for a right-separating `B` and `f = n + s`, `g = n' + s'` are Jordan–Chevalley
decompositions, then `(s, s')` is an adjoint pair. -/
theorem isAdjointPair_of_isSemisimple_of_add (hB : B.SeparatingRight) (h : IsAdjointPair B B f g)
    {n s n' s' : Module.End K V} (hc : Commute n s) (hn : IsNilpotent n) (hs : s.IsSemisimple)
    (hf : f = n + s) (hc' : Commute n' s') (hn' : IsNilpotent n') (hs' : s'.IsSemisimple)
    (hg : g = n' + s') : IsAdjointPair B B s s' :=
  (isAdjointPair_and_isAdjointPair_of_add hB h hc hn hs hf hc' hn' hs' hg).2

end Field

end IsAdjointPair

namespace IsSkewAdjoint

variable {K V M : Type*} [Field K] [PerfectField K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [AddCommGroup M] [Module K M] {B : V →ₗ[K] V →ₗ[K] M}

/-- Both Jordan–Chevalley parts of a skew-adjoint endomorphism are skew-adjoint. -/
private theorem isSkewAdjoint_and_isSkewAdjoint_of_add (hB : B.SeparatingRight)
    {n s : Module.End K V} (hc : Commute n s) (hn : IsNilpotent n) (hs : s.IsSemisimple)
    (h : B.IsSkewAdjoint ⇑(n + s)) : B.IsSkewAdjoint ⇑n ∧ B.IsSkewAdjoint ⇑s := by
  have h' : IsAdjointPair B B ⇑(n + s) ⇑(-(n + s)) := by simpa [IsSkewAdjoint] using h
  simpa [IsSkewAdjoint] using IsAdjointPair.isAdjointPair_and_isAdjointPair_of_add hB h' hc hn hs
    rfl hc.neg_left.neg_right hn.neg (by simpa using IsSemisimple_smul (-1 : K) hs) (neg_add n s)

/-- **The nilpotent part of a skew-adjoint endomorphism is skew-adjoint**, for a right-separating
bilinear map: if `n + s` is skew-adjoint, with `n` nilpotent, `s` semisimple and `n`, `s`
commuting, then `n` is skew-adjoint. -/
theorem of_isNilpotent_of_add (hB : B.SeparatingRight) {n s : Module.End K V} (hc : Commute n s)
    (hn : IsNilpotent n) (hs : s.IsSemisimple) (h : B.IsSkewAdjoint ⇑(n + s)) :
    B.IsSkewAdjoint ⇑n :=
  (isSkewAdjoint_and_isSkewAdjoint_of_add hB hc hn hs h).1

/-- **The semisimple part of a skew-adjoint endomorphism is skew-adjoint**, for a right-separating
bilinear map: if `n + s` is skew-adjoint, with `n` nilpotent, `s` semisimple and `n`, `s`
commuting, then `s` is skew-adjoint. -/
theorem of_isSemisimple_of_add (hB : B.SeparatingRight) {n s : Module.End K V} (hc : Commute n s)
    (hn : IsNilpotent n) (hs : s.IsSemisimple) (h : B.IsSkewAdjoint ⇑(n + s)) :
    B.IsSkewAdjoint ⇑s :=
  (isSkewAdjoint_and_isSkewAdjoint_of_add hB hc hn hs h).2

end IsSkewAdjoint

end LinearMap
