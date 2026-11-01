/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Defs
public import Mathlib.RingTheory.PowerSeries.Expand
public import TauCeti.RingTheory.FormalGroup.Height
-- Proof-only: the residue field, base change of formal group laws and of `[n]`, the Frobenius
-- factorization of `[p]`, substitution modulo an ideal, square-zero reductions, injectivity of
-- expansion, the first-order Taylor formula and the derivative of a base change.
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import TauCeti.RingTheory.FormalGroup.BaseChange
import TauCeti.RingTheory.FormalGroup.Frobenius.Factorization
import TauCeti.RingTheory.FormalGroup.NSMul.BaseChange
import TauCeti.RingTheory.MvPowerSeries.Substitution
import TauCeti.RingTheory.PowerSeries.Derivative
import TauCeti.RingTheory.PowerSeries.Expand
import TauCeti.RingTheory.PowerSeries.Ideal
import TauCeti.RingTheory.PowerSeries.Substitution

/-!
# Rigidity of homomorphisms of formal group laws

Let `A` be a commutative ring, Hausdorff for the `I`-adic topology of an ideal `I`, and let `F`
and `G` be formal group laws over `A` with `G` commutative. Suppose that some integer `n` lies in
`I` and that modulo `I` the series `[n]_F` is a formal coordinate `u` composed with `X ↦ X ^ q`:

  `[n]_F(X) ≡ u(X ^ q) mod I`.

Then a homomorphism from `F` to `G` is determined by its reduction modulo `I`: two
homomorphisms `f` and `g` that agree modulo `I` are equal. The standard case is a local ring `A`
whose residue field has characteristic `p`, with `n = p`, where the hypothesis says that the
reduction of `F` has finite height `h` and `q = p ^ h`; this is the rigidity on which Lubin–Tate
deformation theory rests. It shows that a ⋆-isomorphism between two deformations of a formal
group law of finite height, an isomorphism reducing to the identity, is unique when it exists,
so that deformations form a set-valued functor rather than a groupoid.

The proof shows that if `f ≡ g` modulo an ideal `J ⊆ I`, then `f ≡ g` modulo `I J`, and
iterates from `J = I`. Work over `B = A ⧸ I J`, where `d = f - g` has coefficients killed by `I`,
hence `d ^ 2 = 0`. Since `f` and `g` commute with multiplication by `n`,

  `d ∘ [n]_F = [n]_G ∘ (g + d) - [n]_G ∘ g`.

By the first-order Taylor formula the right side is `d · [n]_G'(g)`, which vanishes because `n`
divides the derivative of `[n]_G` and `n d = 0`. On the left, the coefficients of `d` are killed
by `I`, so `[n]_F` may be replaced by `u(X ^ q)`. Thus `(d ∘ u)(X ^ q) = 0`, hence `d ∘ u = 0`, and
`d = 0` because `u` has a compositional inverse.

## Main results

* `TauCeti.FormalGroupHom.eq_of_map_mk_eq`: homomorphisms out of `F` that agree modulo `I` are
  equal, when `[n]_F ≡ u(X ^ q)` modulo `I` for some `n ∈ I` and formal coordinate `u`.
* `TauCeti.FormalGroupHom.eq_of_map_residue_eq`: over an `𝔪`-adically Hausdorff local ring whose
  residue field has characteristic `p`, homomorphisms out of a commutative formal group law of
  finite height modulo `𝔪` are determined by their reductions.
* `TauCeti.FormalGroupIso.eq_of_map_residue_eq`: in the same situation, isomorphisms with the
  same reduction are equal; in particular ⋆-isomorphisms are unique.

## References

* J. Lubin and J. Tate, *Formal moduli for one-parameter formal Lie groups*, Bull. Soc. Math.
  France 94 (1966).
-/

public section

open PowerSeries

namespace TauCeti

namespace FormalGroupHom

variable {A : Type*} [CommRing A] {F G : FormalGroup A}

/-- Reduce modulo `I J` a series `D` whose coefficients lie in `J`: the coefficients of the
reduction are killed by the image of `I`. -/
private theorem coeff_map_mul_eq_zero {D : A⟦X⟧} {I J : Ideal A} (hD : ∀ k, coeff k D ∈ J) (e : ℕ)
    {x : A ⧸ I * J} (hx : x ∈ I.map (Ideal.Quotient.mk (I * J))) :
    coeff e (D.map (Ideal.Quotient.mk (I * J))) * x = 0 := by
  obtain ⟨y, hy, rfl⟩ := (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).1 hx
  rw [coeff_map, ← map_mul, Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.mul_mem_mul_rev hy (hD e)

/-- One step of the rigidity argument: if `f ≡ g` modulo `J ⊆ I`, then `f ≡ g` modulo `I J`. -/
private theorem coeff_sub_mem_mul [G.IsComm] (f g : FormalGroupHom F G) {I J : Ideal A}
    (hJI : J ≤ I) {n q : ℕ} (hq : q ≠ 0) (hn : (n : A) ∈ I) (u : FormalCoordinate A)
    (hF : ∀ k, coeff k (F.nsmulSeries n - expand q hq u.toPowerSeries) ∈ I)
    (hfg : ∀ k, coeff k (f.toPowerSeries - g.toPowerSeries) ∈ J) (k : ℕ) :
    coeff k (f.toPowerSeries - g.toPowerSeries) ∈ I * J := by
  set D := f.toPowerSeries - g.toPowerSeries with hD
  set π := Ideal.Quotient.mk (I * J)
  set d := D.map π with hd
  -- In `B = A ⧸ I J` the image `d` of `f - g` is killed by `I`, and so by `n`.
  have hnd : (n : (A ⧸ I * J)⟦X⟧) * d = 0 := by
    ext e
    rw [← map_natCast C, coeff_C_mul, (coeff e).map_zero, mul_comm (n : A ⧸ I * J)]
    exact coeff_map_mul_eq_zero hfg e (by simpa using Ideal.mem_map_of_mem π hn)
  -- `(f - g) ∘ [n]_F = [n]_G ∘ f - [n]_G ∘ g`, reduced modulo `I J`.
  have hsub : PowerSeries.subst (F.nsmulSeries n) D =
      PowerSeries.subst f.toPowerSeries (G.nsmulSeries n) -
        PowerSeries.subst g.toPowerSeries (G.nsmulSeries n) := by
    rw [hD, subst_sub (.of_constantCoeff_zero' (F.constantCoeff_nsmulSeries n)),
      f.subst_nsmulSeries, g.subst_nsmulSeries]
  -- `PowerSeries.map` is `MvPowerSeries.map` in the unique variable, so `map_subst` applies.
  have hmap {a : A⟦X⟧} (ha : HasSubst a) (P : A⟦X⟧) :
      PowerSeries.map π (P.subst a) = (P.map π).subst (a.map π) :=
    PowerSeries.map_subst ha P
  have hsubπ := congrArg (PowerSeries.map π) hsub
  rw [map_sub, hmap (.of_constantCoeff_zero' (F.constantCoeff_nsmulSeries n)),
    hmap f.hasSubst, hmap g.hasSubst] at hsubπ
  -- The right side vanishes: by the first-order Taylor formula it is `d · [n]_G'(g)`, and
  -- `n` divides `[n]_G'` while `n d = 0`.
  have hfπ : f.toPowerSeries.map π = g.toPowerSeries.map π + d := by
    rw [hd, hD, map_sub, add_sub_cancel]
  obtain ⟨V, hV⟩ := G.natCast_dvd_derivative_nsmulSeries n
  have hg' : HasSubst (g.toPowerSeries.map π) := g.hasSubst.map π
  have hTaylor : d * (d⁄dX ((G.nsmulSeries n).map π)).subst (g.toPowerSeries.map π) = 0 := by
    rw [derivative_map, hV]
    simp only [← coe_substAlgHom hg', map_mul, map_natCast]
    linear_combination substAlgHom hg' (V.map π) * hnd
  rw [hfπ, subst_add_of_sq_eq_zero hg'
    (sq_map_mk_eq_zero_of_coeff_mem (Ideal.mul_mono_left hJI) hfg), hTaylor, add_zero,
    sub_self] at hsubπ
  -- The left side only sees `[n]_F` modulo `I`, where it is `u (X ^ q)`.
  have hu0 : constantCoeff (expand q hq u.toPowerSeries) = 0 := by
    rw [constantCoeff_expand, u.constantCoeff_toPowerSeries]
  have hcongr : (d.subst ((F.nsmulSeries n).map π) : (A ⧸ I * J)⟦X⟧) =
      d.subst ((expand q hq u.toPowerSeries).map π) :=
    MvPowerSeries.subst_eq_subst_of_coeff_mem
      (HasSubst.const ((HasSubst.of_constantCoeff_zero' (F.constantCoeff_nsmulSeries n)).map π))
      (HasSubst.const ((HasSubst.of_constantCoeff_zero' hu0).map π)) (J := I.map π)
      (fun _ e ↦ by
        rw [← coeff_def rfl, ← map_sub, coeff_map]
        exact Ideal.mem_map_of_mem π (hF _))
      (fun e x hx ↦ by rw [← coeff_def rfl]; exact coeff_map_mul_eq_zero hfg _ hx)
  rw [← hd, hcongr, map_expand, ← FormalCoordinate.toPowerSeries_map] at hsubπ
  -- `X ↦ X ^ q` and substitution of the coordinate `u` are both injective, so `d = 0`.
  set v := FormalCoordinate.map π u
  have hd0 : v.substAlgEquiv d = 0 := by
    refine expand_injective q hq ?_
    rw [FormalCoordinate.substAlgEquiv_apply, map_zero]
    exact (expand_subst q hq v.hasSubst d).trans hsubπ
  rw [map_eq_zero_iff _ v.substAlgEquiv.injective] at hd0
  simpa [hd, ← Ideal.Quotient.eq_zero_iff_mem] using congrArg (coeff k) hd0

/-- **Rigidity of homomorphisms of formal group laws.** Let `A` be `I`-adically Hausdorff, let
`G` be commutative, and suppose that `[n]_F ≡ u(X ^ q)` modulo `I` for some integer `n ∈ I` and
formal coordinate `u`. Then two homomorphisms from `F` to `G` that agree modulo `I` are equal. -/
theorem eq_of_map_mk_eq [G.IsComm] (f g : FormalGroupHom F G) {I : Ideal A} [IsHausdorff I A]
    {n q : ℕ} (hq : q ≠ 0) (hn : (n : A) ∈ I) (u : FormalCoordinate A)
    (hF : (F.nsmulSeries n).map (Ideal.Quotient.mk I) =
      (expand q hq u.toPowerSeries).map (Ideal.Quotient.mk I))
    (hfg : f.toPowerSeries.map (Ideal.Quotient.mk I) = g.toPowerSeries.map (Ideal.Quotient.mk I)) :
    f = g := by
  have hF' (k : ℕ) : coeff k (F.nsmulSeries n - expand q hq u.toPowerSeries) ∈ I := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, ← coeff_map, map_sub, hF, sub_self, map_zero]
  -- `f - g` vanishes modulo every power of `I`.
  have key (m : ℕ) : ∀ k, coeff k (f.toPowerSeries - g.toPowerSeries) ∈ I ^ (m + 1) := by
    induction m with
    | zero =>
      intro k
      rw [zero_add, pow_one, ← Ideal.Quotient.eq_zero_iff_mem, ← coeff_map, map_sub, hfg,
        sub_self, map_zero]
    | succ m ih =>
      rw [pow_succ']
      exact coeff_sub_mem_mul f g (Ideal.pow_le_self m.succ_ne_zero) hq hn u hF' ih
  ext k
  rw [← sub_eq_zero, ← map_sub]
  refine IsHausdorff.haus ‹_› _ fun m ↦ ?_
  rw [SModEq.zero, smul_eq_mul, Ideal.mul_top]
  exact Ideal.pow_le_pow_right m.le_succ (key m k)

open IsLocalRing

variable [IsLocalRing A] [IsHausdorff (maximalIdeal A) A] [G.IsComm] {p : ℕ} [hp : Fact p.Prime]
  [CharP (ResidueField A) p]

/-- **Lubin–Tate rigidity.** Let `A` be an `𝔪`-adically Hausdorff local ring whose residue field
has characteristic `p`, and let `F` and `G` be commutative formal group laws over `A` such that
the reduction of `F` has finite height. Then a homomorphism from `F` to `G` is determined by its
reduction to the residue field. -/
theorem eq_of_map_residue_eq [F.IsComm] (f g : FormalGroupHom F G) {h : ℕ}
    (hF : (F.map (residue A)).height p = h)
    (hfg : f.toPowerSeries.map (residue A) = g.toPowerSeries.map (residue A)) : f = g := by
  -- Over the residue field, `[p]` is the `h`-fold Frobenius followed by a coordinate.
  set e := (F.map (residue A)).heightFrobeniusIso hF
  have he : (F.map (residue A)).nsmulSeries p =
      expand (p ^ h) (pow_ne_zero h hp.out.ne_zero) e.toHom.toPowerSeries := by
    rw [← comp_iterateFrobeniusHom_toPowerSeries,
      FormalGroup.heightFrobeniusIso_comp_iterateFrobeniusHom, FormalGroup.nsmulHom_toPowerSeries]
  -- Lift that coordinate to a coordinate `u` over `A`.
  obtain ⟨u', hu'⟩ := map_surjective (residue A) residue_surjective e.toHom.toPowerSeries
  have hu'0 : residue A (constantCoeff u') = 0 := by
    rw [← coeff_zero_eq_constantCoeff_apply, ← coeff_map, hu', coeff_zero_eq_constantCoeff_apply,
      e.toHom.zero_constantCoeff]
  let u : FormalCoordinate A :=
    { toPowerSeries := u' - C (constantCoeff u')
      constantCoeff_toPowerSeries := by simp
      isUnit_coeff_one := by
        simp only [map_sub, coeff_C, one_ne_zero, ↓reduceIte, sub_zero]
        refine isUnit_of_map_unit (residue A) _ ?_
        rw [← coeff_map, hu']
        exact e.isUnit_coeff_one }
  have hu : u.toPowerSeries.map (residue A) = e.toHom.toPowerSeries := by
    rw [map_sub, hu', map_C, hu'0, map_zero, sub_zero]
  refine f.eq_of_map_mk_eq g (pow_ne_zero h hp.out.ne_zero) (n := p) ?_ u ?_ hfg
  · rw [← residue_eq_zero_iff, map_natCast, CharP.cast_eq_zero]
  -- `residue A` is by definition `Ideal.Quotient.mk (maximalIdeal A)`.
  · change (F.nsmulSeries p).map (residue A) = (expand _ _ u.toPowerSeries).map (residue A)
    rw [map_expand, hu, FormalGroup.map_nsmulSeries, he]

end FormalGroupHom

namespace FormalGroupIso

open IsLocalRing

variable {A : Type*} [CommRing A] [IsLocalRing A] [IsHausdorff (maximalIdeal A) A]
  {F G : FormalGroup A} [F.IsComm] [G.IsComm] {p : ℕ} [Fact p.Prime] [CharP (ResidueField A) p]

/-- **Uniqueness of ⋆-isomorphisms.** Over an `𝔪`-adically Hausdorff local ring whose residue
field has characteristic `p`, two isomorphisms between commutative formal group laws that have
the same reduction to the residue field are equal, provided the reduction of the source has
finite height. -/
theorem eq_of_map_residue_eq (e₁ e₂ : FormalGroupIso F G) {h : ℕ}
    (hF : (F.map (residue A)).height p = h)
    (he : e₁.toHom.toPowerSeries.map (residue A) = e₂.toHom.toPowerSeries.map (residue A)) :
    e₁ = e₂ :=
  ext (e₁.toHom.eq_of_map_residue_eq e₂.toHom hF he)

end FormalGroupIso

end TauCeti
