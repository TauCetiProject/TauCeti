/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.RatFunc.Transcendental
import TauCeti.FieldTheory.RatFunc.Automorphism

/-!
# Morphisms of polynomial extensions of the rational function field

Let `q ∈ k[X]` be a polynomial over a field `k`, and let `F = k(x)` be a field generated over `k`
by an element `x` on which the variable `t` of `k(t)` acts as `q(x)`. Geometrically this is the
polynomial map `x ↦ q(x)` of the projective line, the source of a polynomial Belyi map when the
critical values of `q` lie in `{0, 1}`. This file determines the morphisms between two such
extensions over `k(t)`.

A morphism `F → F'` over `k(t)`, where `t` acts on `F' = k(x')` as `q'(x')`, sends `x` to
`s(x')` for a **polynomial** `s` (`AlgHom.exists_apply_eq_aeval`), and when `F = k(x)` a polynomial
`s` arises this way exactly when `q ∘ s = q'` (`AlgHom.comp_eq_of_apply_eq_aeval` and
`TauCeti.exists_algHom_apply_eq_aeval_iff`). That `s` is a polynomial, rather than an arbitrary
rational function of `x'`, reflects that `q` and `q'` have their only pole at `∞`: a rational
function `r` with `q(r)` a polynomial is itself a polynomial
(`RatFunc.exists_algebraMap_eq_of_aeval_eq_algebraMap`), since `r` is integral over `k[X]`.

An isomorphism has an inverse of the same kind, so its polynomial `s` has degree one:
**isomorphisms are affine changes of variable**. The extensions defined by `q` and `q'` are
isomorphic over `k(t)` exactly when `q' = q(a X + b)` for some `a ≠ 0` and `b`
(`TauCeti.nonempty_algEquiv_iff_exists_comp_eq`). For polynomial Belyi maps, whose dessins are
plane trees, this is the classical statement that isomorphic Shabat polynomials differ by an affine
change of variable; it turns an isomorphism of polynomial Belyi pairs into an identity of
polynomials, as needed to compare a polynomial Belyi pair with its Galois conjugates.

## Main results

* `RatFunc.exists_algebraMap_eq_of_aeval_eq_algebraMap`: if a nonconstant polynomial sends a
  rational function to a polynomial, that rational function is a polynomial.
* `AlgHom.exists_apply_eq_aeval`: every morphism `k(x) → k(x')` over `k(t)` sends `x` to a
  polynomial `s(x')`.
* `AlgHom.comp_eq_of_apply_eq_aeval` and `TauCeti.exists_algHom_apply_eq_aeval_iff`: a polynomial
  `s` describes a morphism over `k(t)` exactly when `q ∘ s = q'`.
* `AlgEquiv.exists_apply_eq_mul_add_and_comp_eq`: every isomorphism over `k(t)` is an affine
  change of variable `x ↦ a x' + b`, with `q(a X + b) = q'`.
* `TauCeti.nonempty_algEquiv_iff_exists_comp_eq`: the extensions defined by `q` and `q'` are
  isomorphic over `k(t)` exactly when `q' = q(a X + b)` with `a ≠ 0`.

## References

* S. K. Lando and A. K. Zvonkin, *Graphs on Surfaces and Their Applications*, Encyclopaedia of
  Mathematical Sciences 141, Springer, 2004, §2.2, for Shabat polynomials and their equivalence.
* E. Girondo and G. González-Diez, *Introduction to Compact Riemann Surfaces and Dessins
  d'Enfants*, LMS Student Texts 79, Cambridge University Press, 2012, proof of Theorem 4.49,
  where an isomorphism of polynomial Belyi maps is seen to be affine.
-/

public section

open Polynomial

open scoped IntermediateField

namespace RatFunc

variable {k : Type*} [Field k]

/-- **A rational function sent to a polynomial by a nonconstant polynomial is a polynomial**: if
`q ∈ k[X]` has positive degree and `q(r) ∈ k[X]` for some `r ∈ k(X)`, then `r ∈ k[X]`. -/
theorem exists_algebraMap_eq_of_aeval_eq_algebraMap {q : k[X]} (hq : 0 < q.natDegree)
    {r : RatFunc k} {p : k[X]} (h : aeval r q = algebraMap k[X] (RatFunc k) p) :
    ∃ s : k[X], algebraMap k[X] (RatFunc k) s = r := by
  have hq0 : q ≠ 0 := ne_zero_of_natDegree_gt hq
  have hc : (q.leadingCoeff)⁻¹ ≠ 0 := inv_ne_zero (leadingCoeff_ne_zero.mpr hq0)
  refine IsIntegrallyClosed.isIntegral_iff.mp <| IsIntegral.of_aeval_monic
    ((monic_mul_leadingCoeff_inv hq0).map (algebraMap k k[X])) ?_ ?_
  · rw [natDegree_map, natDegree_mul_C hc]
    exact hq.ne'
  · rw [aeval_map_algebraMap, map_mul, h, aeval_C, IsScalarTower.algebraMap_apply k k[X]]
    exact isIntegral_algebraMap.mul isIntegral_algebraMap

end RatFunc

variable {k F F' : Type*} [Field k] [Field F] [Field F'] [Algebra k F] [Algebra k F']
  [Algebra (RatFunc k) F] [Algebra (RatFunc k) F'] [IsScalarTower k (RatFunc k) F]
  [IsScalarTower k (RatFunc k) F'] {x : F} {x' : F'} {q q' : k[X]}

namespace AlgHom

/-- **A substitution describing a morphism factors the polynomials**: let `t` act as `q(x)` on `F`
and as `q'(x')` on `F'`. If a morphism `F → F'` over `k(t)` sends `x` to `s(x')` for a polynomial
`s`, then `q ∘ s = q'`. -/
theorem comp_eq_of_apply_eq_aeval (f : F →ₐ[RatFunc k] F')
    (hq : algebraMap (RatFunc k) F RatFunc.X = aeval x q)
    (hq' : algebraMap (RatFunc k) F' RatFunc.X = aeval x' q') {s : k[X]}
    (hf : f x = aeval x' s) : q.comp s = q' := by
  refine transcendental_iff_injective.mp (TauCeti.transcendental_of_aeval_eq hq') ?_
  rw [aeval_comp, ← hf, ← hq', ← f.commutes, hq]
  exact aeval_algHom_apply (f.restrictScalars k) x q

/-- **Morphisms of polynomial extensions are polynomial substitutions**: let `t` act as `q(x)` on
`F` and as `q'(x')` on `F' = k(x')`. Every morphism `F → F'` over `k(t)` sends `x` to `s(x')` for a
polynomial `s`, which then satisfies `q ∘ s = q'` (`AlgHom.comp_eq_of_apply_eq_aeval`). -/
theorem exists_apply_eq_aeval (f : F →ₐ[RatFunc k] F') (hx' : k⟮x'⟯ = ⊤)
    (hq : algebraMap (RatFunc k) F RatFunc.X = aeval x q)
    (hq' : algebraMap (RatFunc k) F' RatFunc.X = aeval x' q') :
    ∃ s : k[X], f x = aeval x' s := by
  -- identify `F'` with `k(X)`, sending `x'` to `X`
  let ψ : RatFunc k ≃ₐ[k] F' :=
    (RatFunc.algEquivOfTranscendental x' (TauCeti.transcendental_of_aeval_eq hq')).trans
      ((IntermediateField.equivOfEq hx').trans IntermediateField.topEquiv)
  have hψ : ψ RatFunc.X = x' := by simp [ψ, IntermediateField.equivOfEq_apply]
  have hψp (p : k[X]) : ψ (algebraMap k[X] (RatFunc k) p) = aeval x' p := by
    rw [← RatFunc.aeval_X_left_eq_algebraMap, ← hψ, aeval_algHom_apply]
  -- the image of `x`, read in `k(X)`, is sent by `q` to the polynomial `q'`
  have hr : aeval (ψ.symm (f x)) q = algebraMap k[X] (RatFunc k) q' := by
    refine ψ.injective ?_
    calc ψ (aeval (ψ.symm (f x)) q) = aeval (f x) q := by
          rw [← aeval_algHom_apply, AlgEquiv.apply_symm_apply]
      _ = f (aeval x q) := aeval_algHom_apply (f.restrictScalars k) x q
      _ = ψ (algebraMap k[X] (RatFunc k) q') := by rw [← hq, f.commutes, hq', hψp]
  obtain ⟨s, hs⟩ := RatFunc.exists_algebraMap_eq_of_aeval_eq_algebraMap
    (TauCeti.natDegree_pos_of_aeval_eq hq) hr
  exact ⟨s, by rw [← hψp, hs, AlgEquiv.apply_symm_apply]⟩

end AlgHom

namespace AlgEquiv

/-- **Isomorphisms of polynomial extensions are affine**: let `t` act as `q(x)` on `F = k(x)` and as
`q'(x')` on `F' = k(x')`. Every isomorphism `F ≃ F'` over `k(t)` sends `x` to `a x' + b` for some
`a ≠ 0` and `b` in `k`, and then `q(a X + b) = q'`. -/
theorem exists_apply_eq_mul_add_and_comp_eq (e : F ≃ₐ[RatFunc k] F') (hx : k⟮x⟯ = ⊤)
    (hx' : k⟮x'⟯ = ⊤) (hq : algebraMap (RatFunc k) F RatFunc.X = aeval x q)
    (hq' : algebraMap (RatFunc k) F' RatFunc.X = aeval x' q') :
    ∃ a b : k, a ≠ 0 ∧ e x = algebraMap k F' a * x' + algebraMap k F' b ∧
      q.comp (C a * X + C b) = q' := by
  obtain ⟨s, hs⟩ := e.toAlgHom.exists_apply_eq_aeval hx' hq hq'
  obtain ⟨s', hs'⟩ := e.symm.toAlgHom.exists_apply_eq_aeval hx hq' hq
  -- the polynomials of `e` and of its inverse are inverse under composition
  have hss' : s.comp s' = X := by
    refine transcendental_iff_injective.mp (TauCeti.transcendental_of_aeval_eq hq) ?_
    rw [aeval_comp, aeval_X, ← hs']
    refine (aeval_algHom_apply (e.symm.toAlgHom.restrictScalars k) x' s).trans ?_
    rw [← hs]
    simp
  have hdeg : s.natDegree = 1 :=
    Nat.eq_one_of_mul_eq_one_right (by rw [← natDegree_comp, hss', natDegree_X])
  obtain ⟨a, b, rfl⟩ := exists_eq_X_add_C_of_natDegree_le_one hdeg.le
  have ha : a ≠ 0 := by
    rintro rfl
    simp at hdeg
  exact ⟨a, b, ha, by simpa using hs, e.toAlgHom.comp_eq_of_apply_eq_aeval hq hq' hs⟩

end AlgEquiv

namespace TauCeti

/-- **Morphisms of polynomial extensions are factorizations**: let `t` act as `q(x)` on `F = k(x)`
and as `q'(x')` on `F'`. A polynomial `s` describes a morphism `F → F'` over `k(t)`, sending `x` to
`s(x')`, exactly when `q ∘ s = q'`. -/
theorem exists_algHom_apply_eq_aeval_iff (hx : k⟮x⟯ = ⊤)
    (hq : algebraMap (RatFunc k) F RatFunc.X = aeval x q)
    (hq' : algebraMap (RatFunc k) F' RatFunc.X = aeval x' q') {s : k[X]} :
    (∃ f : F →ₐ[RatFunc k] F', f x = aeval x' s) ↔ q.comp s = q' := by
  refine ⟨fun ⟨f, hf⟩ ↦ f.comp_eq_of_apply_eq_aeval hq hq' hf, fun h ↦ ?_⟩
  have hs0 : s.natDegree ≠ 0 := fun hs ↦ (natDegree_pos_of_aeval_eq hq').ne' <| by
    rw [← h, natDegree_comp, hs, mul_zero]
  have hs : Transcendental k (aeval x' s) := (transcendental_of_aeval_eq hq').aeval s hs0 <|
    mem_nonZeroDivisors_of_ne_zero <| leadingCoeff_ne_zero.mpr <|
      ne_zero_of_natDegree_gt (Nat.pos_of_ne_zero hs0)
  -- the `k`-algebra map `F = k⟮x⟯ → F'` sending `x` to `s(x')`
  let g : F →ₐ[k] F' := ((transcendental_of_aeval_eq hq).algHomAdjoin hs).comp
    ((IntermediateField.equivOfEq hx.symm).toAlgHom.comp IntermediateField.topEquiv.symm.toAlgHom)
  have hgx : g x = aeval x' s := by
    have : IntermediateField.equivOfEq hx.symm (IntermediateField.topEquiv.symm x) =
        IntermediateField.AdjoinSimple.gen k x := by
      ext
      simp [IntermediateField.equivOfEq_apply]
    simp [g, this]
  -- it fixes `t`, hence is a morphism over `k(t)`
  have hgt : g.comp (IsScalarTower.toAlgHom k (RatFunc k) F) =
      IsScalarTower.toAlgHom k (RatFunc k) F' := by
    refine RatFunc.algHom_ext ?_
    rw [AlgHom.comp_apply, IsScalarTower.toAlgHom_apply, IsScalarTower.toAlgHom_apply, hq,
      ← aeval_algHom_apply, hgx, ← aeval_comp, h, hq']
  exact ⟨{ g with commutes' := fun r ↦ DFunLike.congr_fun hgt r }, hgx⟩

/-- **Polynomial extensions are isomorphic exactly when the polynomials differ by an affine
change of variable**: let `t` act as `q(x)` on `F = k(x)` and as `q'(x')` on `F' = k(x')`. Then
`F` and `F'` are isomorphic over `k(t)` exactly when `q' = q(a X + b)` for some `a ≠ 0` and `b`. -/
theorem nonempty_algEquiv_iff_exists_comp_eq (hx : k⟮x⟯ = ⊤) (hx' : k⟮x'⟯ = ⊤)
    (hq : algebraMap (RatFunc k) F RatFunc.X = aeval x q)
    (hq' : algebraMap (RatFunc k) F' RatFunc.X = aeval x' q') :
    Nonempty (F ≃ₐ[RatFunc k] F') ↔ ∃ a b : k, a ≠ 0 ∧ q.comp (C a * X + C b) = q' := by
  refine ⟨fun ⟨e⟩ ↦ ?_, fun ⟨a, b, ha, h⟩ ↦ ?_⟩
  · obtain ⟨a, b, ha, -, h⟩ := e.exists_apply_eq_mul_add_and_comp_eq hx hx' hq hq'
    exact ⟨a, b, ha, h⟩
  obtain ⟨f, hf⟩ := (exists_algHom_apply_eq_aeval_iff hx hq hq').mpr h
  -- `f` is onto, since its image contains `x' = (f x - b) / a`
  have hx'f : x' ∈ (f.restrictScalars k).fieldRange := by
    have hfk (c : k) : f (algebraMap k F c) = algebraMap k F' c := (f.restrictScalars k).commutes c
    refine AlgHom.mem_fieldRange.mpr ⟨algebraMap k F a⁻¹ * (x - algebraMap k F b), ?_⟩
    simp [hf, hfk, ha]
  have hsurj : Function.Surjective f := fun y ↦ AlgHom.mem_fieldRange.mp <|
    IntermediateField.adjoin_simple_le_iff.mpr hx'f (hx' ▸ IntermediateField.mem_top)
  exact ⟨AlgEquiv.ofBijective f ⟨f.toRingHom.injective, hsurj⟩⟩

end TauCeti
