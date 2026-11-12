/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.JordanChevalley
public import TauCeti.LinearAlgebra.SesquilinearForm.AdjointPair
import TauCeti.LinearAlgebra.End.Prod

/-!
# Jordan–Chevalley decompositions of adjoint pairs

Let `B` be a bilinear map on a finite-dimensional vector space `V` over a perfect field, and let
`(f, g)` be an adjoint pair of endomorphisms, `B (f v) w = B v (g w)`
(`LinearMap.IsAdjointPair B B f g`). Then `p(f)` and `p(g)` are adjoint for every polynomial `p`
(`LinearMap.IsAdjointPair.aeval`).

The Jordan–Chevalley decomposition of `f × g` on `V × V` is the product of those of `f = n + s`
and `g = n' + s'`, since products of nilpotent and of semisimple endomorphisms are again
nilpotent and semisimple (`IsNilpotent.prodMap`, `Module.End.IsSemisimple.prodMap`). Its parts are
polynomials `p(f × g) = p(f) × p(g)` and `q(f × g) = q(f) × q(g)`, so `n = p(f)`, `n' = p(g)`,
`s = q(f)` and `s' = q(g)` for the same polynomials `p` and `q`. Hence **the adjoint of the
nilpotent part is the nilpotent part of the adjoint, and likewise for the semisimple part**
(`LinearMap.IsAdjointPair.isAdjointPair_of_isNilpotent_of_add`,
`LinearMap.IsAdjointPair.isAdjointPair_of_isSemisimple_of_add`). No nondegeneracy of `B` is
needed.

For a skew-adjoint endomorphism `f`, whose adjoint is `-f` with decomposition `-n + -s`, this says
that both parts of `f` are again skew-adjoint
(`LinearMap.IsSkewAdjoint.of_isNilpotent_of_add`, `LinearMap.IsSkewAdjoint.of_isSemisimple_of_add`).
So the Lie algebra of skew-adjoint endomorphisms of a bilinear form, such as a symplectic Lie
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

variable {K V M : Type*} [Field K] [PerfectField K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [AddCommGroup M] [Module K M] {B : V →ₗ[K] V →ₗ[K] M}
  {f g : Module.End K V}

/-- Both Jordan–Chevalley parts of an adjoint pair are adjoint pairs. -/
private theorem isAdjointPair_and_isAdjointPair_of_add (h : IsAdjointPair B B f g)
    {n s n' s' : Module.End K V} (hc : Commute n s) (hn : IsNilpotent n) (hs : s.IsSemisimple)
    (hf : f = n + s) (hc' : Commute n' s') (hn' : IsNilpotent n') (hs' : s'.IsSemisimple)
    (hg : g = n' + s') : IsAdjointPair B B n n' ∧ IsAdjointPair B B s s' := by
  -- By uniqueness of the decomposition of `f × g`, `n × n'` and `s × s'` are polynomials in it.
  obtain ⟨n₀, hn₀, s₀, hs₀, hn₀nil, hs₀ss, hfg₀⟩ :=
    Module.End.exists_isNilpotent_isSemisimple (f := f.prodMap g)
  have hc₀ : Commute n₀ s₀ := Algebra.commute_of_mem_adjoin_singleton_of_commute hs₀
    (Algebra.commute_of_mem_adjoin_self hn₀).symm
  have hcp : Commute (n.prodMap n') (s.prodMap s') := by
    rw [commute_iff_eq, prodMap_mul, prodMap_mul, hc.eq, hc'.eq]
  obtain ⟨rfl, rfl⟩ := isNilpotent_isSemisimple_unique hn₀nil hs₀ss (hn.prodMap hn')
    (hs.prodMap hs') hc₀ hcp (by rw [← hfg₀, hf, hg, prodMap_add])
  rw [Algebra.adjoin_singleton_eq_range_aeval, AlgHom.mem_range] at hn₀ hs₀
  -- A polynomial `r` with `r(f × g) = a × b` has `a = r(f)` and `b = r(g)`, an adjoint pair.
  have key {a b : Module.End K V} {r : K[X]} (hr : Polynomial.aeval (f.prodMap g) r = a.prodMap b) :
      IsAdjointPair B B a b := by
    rw [Module.End.aeval_prodMap] at hr
    have ha : Polynomial.aeval f r = a :=
      LinearMap.ext fun v ↦ by simpa using congrArg Prod.fst (LinearMap.congr_fun hr (v, 0))
    have hb : Polynomial.aeval g r = b :=
      LinearMap.ext fun v ↦ by simpa using congrArg Prod.snd (LinearMap.congr_fun hr (0, v))
    exact ha ▸ hb ▸ h.aeval r
  obtain ⟨p, hp⟩ := hn₀
  obtain ⟨q, hq⟩ := hs₀
  exact ⟨key hp, key hq⟩

/-- **The adjoint of the nilpotent part is the nilpotent part of the adjoint.** If `(f, g)` is an
adjoint pair and `f = n + s`, `g = n' + s'` are Jordan–Chevalley decompositions, then `(n, n')` is
an adjoint pair. -/
theorem isAdjointPair_of_isNilpotent_of_add (h : IsAdjointPair B B f g)
    {n s n' s' : Module.End K V} (hc : Commute n s) (hn : IsNilpotent n) (hs : s.IsSemisimple)
    (hf : f = n + s) (hc' : Commute n' s') (hn' : IsNilpotent n') (hs' : s'.IsSemisimple)
    (hg : g = n' + s') : IsAdjointPair B B n n' :=
  (isAdjointPair_and_isAdjointPair_of_add h hc hn hs hf hc' hn' hs' hg).1

/-- **The adjoint of the semisimple part is the semisimple part of the adjoint.** If `(f, g)` is
an adjoint pair and `f = n + s`, `g = n' + s'` are Jordan–Chevalley decompositions, then `(s, s')`
is an adjoint pair. -/
theorem isAdjointPair_of_isSemisimple_of_add (h : IsAdjointPair B B f g)
    {n s n' s' : Module.End K V} (hc : Commute n s) (hn : IsNilpotent n) (hs : s.IsSemisimple)
    (hf : f = n + s) (hc' : Commute n' s') (hn' : IsNilpotent n') (hs' : s'.IsSemisimple)
    (hg : g = n' + s') : IsAdjointPair B B s s' :=
  (isAdjointPair_and_isAdjointPair_of_add h hc hn hs hf hc' hn' hs' hg).2

end IsAdjointPair

namespace IsSkewAdjoint

variable {K V M : Type*} [Field K] [PerfectField K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [AddCommGroup M] [Module K M] {B : V →ₗ[K] V →ₗ[K] M}

/-- Both Jordan–Chevalley parts of a skew-adjoint endomorphism are skew-adjoint. -/
private theorem isSkewAdjoint_and_isSkewAdjoint_of_add {n s : Module.End K V} (hc : Commute n s)
    (hn : IsNilpotent n) (hs : s.IsSemisimple) (h : B.IsSkewAdjoint ⇑(n + s)) :
    B.IsSkewAdjoint ⇑n ∧ B.IsSkewAdjoint ⇑s := by
  have h' : IsAdjointPair B B ⇑(n + s) ⇑(-(n + s)) := by simpa [IsSkewAdjoint] using h
  simpa [IsSkewAdjoint] using IsAdjointPair.isAdjointPair_and_isAdjointPair_of_add h' hc hn hs
    rfl hc.neg_left.neg_right hn.neg (by simpa using IsSemisimple_smul (-1 : K) hs) (neg_add n s)

/-- **The nilpotent part of a skew-adjoint endomorphism is skew-adjoint**: if `n + s` is
skew-adjoint, with `n` nilpotent, `s` semisimple and `n`, `s` commuting, then `n` is
skew-adjoint. -/
theorem of_isNilpotent_of_add {n s : Module.End K V} (hc : Commute n s) (hn : IsNilpotent n)
    (hs : s.IsSemisimple) (h : B.IsSkewAdjoint ⇑(n + s)) : B.IsSkewAdjoint ⇑n :=
  (isSkewAdjoint_and_isSkewAdjoint_of_add hc hn hs h).1

/-- **The semisimple part of a skew-adjoint endomorphism is skew-adjoint**: if `n + s` is
skew-adjoint, with `n` nilpotent, `s` semisimple and `n`, `s` commuting, then `s` is
skew-adjoint. -/
theorem of_isSemisimple_of_add {n s : Module.End K V} (hc : Commute n s) (hn : IsNilpotent n)
    (hs : s.IsSemisimple) (h : B.IsSkewAdjoint ⇑(n + s)) : B.IsSkewAdjoint ⇑s :=
  (isSkewAdjoint_and_isSkewAdjoint_of_add hc hn hs h).2

end IsSkewAdjoint

end LinearMap
