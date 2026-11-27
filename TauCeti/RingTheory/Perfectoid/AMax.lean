/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Perfectoid.Cyclotomic.Period
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.Localization.Away.Basic

import Mathlib.RingTheory.AdicCompletion.LocalRing
import Mathlib.RingTheory.AdjoinRoot
import TauCeti.RingTheory.AdicCompletion.AlgHom
import TauCeti.RingTheory.AdicCompletion.Algebra
import TauCeti.RingTheory.AdicCompletion.Regular.Basic
import TauCeti.RingTheory.AdjoinRoot.Basic
import TauCeti.RingTheory.Perfectoid.Cyclotomic.Regular
import TauCeti.RingTheory.WittVector.Frobenius

/-!
# Colmez's period rings `A_max`, `B⁺_max` and `B_max`

Let `S` be a perfect ring of characteristic `p`, `ε ∈ S`, and `ξ = ∑ j < p, [ε^(1/p)]^j` the
cyclotomic period in `W(S)`. Colmez's ring `A_max` is the `p`-adic completion of
`W(S)[X] ⧸ (p X - ξ)`, in which the class of `X` is a quotient `ξ/p`. Inverting `p` gives
`B⁺_max = A_max[1/p]`, and inverting the period `μ = [ε] - 1` as well gives
`B_max = B⁺_max[1/μ]`. For `S` the tilt of the ring of integers of `ℂ_p` and `ε` a compatible
system of primitive `p`-power roots of unity, `A_max` and `B⁺_max` are Colmez's rings of
crystalline periods, and `B_max` is a ring through which crystalline representations can be
defined in place of Fontaine's `B_cris`.

The ring `A_max` is `p`-adically complete, and it is universal among `p`-adically complete rings
`R` with a ring map `f : W(S) → R` and an element `x` with `f(ξ) = p x`. In particular every
ring endomorphism `σ` of `W(S)` with `σ(ξ) ∈ (p, ξ)` extends to `A_max`: this applies to the
Witt vector Frobenius, since `φ(ξ) ≡ ξ ^ p` modulo `p`, and to every `σ` with `ξ ∣ σ(ξ)`, such
as the Galois automorphisms. When `S = A♭` for a `p`-adically complete ring `A` and Fontaine's
map `θ : W(A♭) → A` kills `ξ`, the map `θ` extends to `A_max` with `ξ/p ↦ 0`.

If `S` is a domain and `ε ≠ 1`, then `p, ξ` is a weakly regular sequence of `W(S)`, so `p` is a
nonzerodivisor on `W(S)[X] ⧸ (p X - ξ)` and hence on its `p`-adic completion `A_max`. No
Noetherian hypothesis is needed. Consequently `A_max` embeds in `B⁺_max`, and the extended
endomorphisms are unique and compose.

## Main definitions

* `TauCeti.Perfectoid.AMax p ε`: the ring `A_max`, a `W(S)`-algebra, with the element
  `TauCeti.Perfectoid.AMax.xiDivP p ε` satisfying `p * (ξ/p) = ξ`.
* `TauCeti.Perfectoid.AMax.lift`: the map `A_max → R` extending `f : W(S) → R` with `ξ/p ↦ x`,
  for a `p`-adically complete `R` and `f(ξ) = p x`.
* `TauCeti.Perfectoid.AMax.map`: the extension `A_max(ε) → A_max(ε')` of a ring map
  `σ : W(S) → W(S')` with `σ(ξ) ∈ (p, ξ')`; `TauCeti.Perfectoid.AMax.frobenius` is the
  extension of the Witt vector Frobenius.
* `TauCeti.Perfectoid.AMax.theta`: Fontaine's map extended to `A_max → A`, with `ξ/p ↦ 0`.
* `TauCeti.Perfectoid.BMaxPlus p ε = A_max[1/p]` and `TauCeti.Perfectoid.BMax p ε = B⁺_max[1/μ]`,
  with `TauCeti.Perfectoid.BMaxPlus.map`, `TauCeti.Perfectoid.BMaxPlus.frobenius` and Fontaine's
  map `TauCeti.Perfectoid.BMaxPlus.theta`, with values in any `A`-algebra in which `p` is a unit.

## Main results

* `TauCeti.Perfectoid.AMax.instIsAdicComplete`: `A_max` is `p`-adically complete.
* `TauCeti.Perfectoid.AMax.lift_algebraMap`, `TauCeti.Perfectoid.AMax.lift_xiDivP` and
  `TauCeti.Perfectoid.AMax.ringHom_ext`: the universal property of `A_max`.
* `TauCeti.Perfectoid.AMax.natCast_mem_nonZeroDivisors`: for a perfect domain `S` and `ε ≠ 1`,
  `p` is a nonzerodivisor of `A_max`.
* `TauCeti.Perfectoid.AMax.map_span_natCast_xi` and
  `TauCeti.Perfectoid.AMax.natCast_pow_dvd_algebraMap_of_mem_pow`: the ideal `(p, ξ)` generates
  `p A_max`, so `p ^ n` divides in `A_max` every element of `(p, ξ) ^ n`.
* `TauCeti.Perfectoid.AMax.exists_mem_adjoin_sub_mem_span_pow` and
  `TauCeti.Perfectoid.AMax.exists_natCast_pow_mul_eq_algebraMap`: polynomials in `ξ / p` over
  `W(S)` are `p`-adically dense in `A_max`, and each of them has a multiple `p ^ k` in `W(S)`.
* `TauCeti.Perfectoid.frobenius_xi_mem_span`: the Witt vector Frobenius carries `ξ` into `(p, ξ)`,
  so it extends to `A_max` and `B⁺_max` (`TauCeti.Perfectoid.AMax.frobenius_eq_map`,
  `TauCeti.Perfectoid.BMaxPlus.frobenius_eq_map`).
* `TauCeti.Perfectoid.AMax.map_comp`, `TauCeti.Perfectoid.BMaxPlus.map_comp`: the extensions to
  `A_max` and to `B⁺_max` compose, when `p` is a nonzerodivisor of `A_max`.
* `TauCeti.Perfectoid.BMaxPlus.algebraMap_injective`: `A_max → B⁺_max` is injective.
* `TauCeti.Perfectoid.BMax.isUnit_algebraMap_mu`: `μ` is a unit of `B_max`.

## References

* P. Colmez, *Théorie d'Iwasawa des représentations de de Rham d'un corps local*, Ann. of Math.
  148 (1998), for the rings `A_max`, `B⁺_max` and `B_max`.
* J.-M. Fontaine, *Le corps des périodes p-adiques*, Astérisque 223 (1994), for Fontaine's map
  `θ` and the analogous ring `A_cris`.
* `grh-lean`, https://github.com/lsernau/grh-lean, file
  `src/Lib/PadicHodge/PeriodRings/CrystallineRings.lean` (declarations `New.Period.Amax`,
  `New.Period.Amax.xiDivP`, `New.Period.BPlus`, `New.Period.Bmax`); Apache 2.0, Copyright 2026
  Anthropic, PBC. The presentation of `A_max` as the `p`-adic completion of `A_inf[X] ⧸ (pX − ξ)`
  follows it.
-/

public section

open Polynomial _root_.WittVector
open scoped nonZeroDivisors

namespace TauCeti.Perfectoid

section AMax

variable (p : ℕ) [Fact p.Prime] {S : Type*} [CommRing S] [CharP S p] [PerfectRing S p]

-- The body is exposed so that the ring structure can be transported from the completion.
/-- **Colmez's ring `A_max`**: the `p`-adic completion of `W(S)[X] ⧸ (p X - ξ)`, where
`ξ = ∑ j < p, [ε^(1/p)]^j`. The class of `X` is the element `AMax.xiDivP p ε`, a quotient
`ξ / p`. For `S` the tilt of the integers of `ℂ_p` and `ε` a compatible system of primitive
`p`-power roots of unity, this is the period ring `A_max` of crystalline `p`-adic Hodge
theory. -/
@[expose] noncomputable def AMax (ε : S) : Type _ :=
  AdicCompletion
    (Ideal.span {(p : AdjoinRoot (C (p : WittVector p S) * X - C (xi p ε)))})
    (AdjoinRoot (C (p : WittVector p S) * X - C (xi p ε)))

/-- `A_max` is a commutative ring, as an adic completion of a commutative ring. -/
noncomputable instance (ε : S) : CommRing (AMax p ε) :=
  inferInstanceAs (CommRing (AdicCompletion _ _))

/-- `A_max` is a `W(S)`-algebra through `W(S) → W(S)[X] ⧸ (p X - ξ)`. -/
noncomputable instance (ε : S) : Algebra (WittVector p S) (AMax p ε) :=
  inferInstanceAs (Algebra (WittVector p S) (AdicCompletion _ _))

/-- The Witt vector Frobenius carries `ξ` into the ideal `(p, ξ)` of `W(S)`, since
`φ(ξ) ≡ ξ ^ p` modulo `p`. -/
theorem frobenius_xi_mem_span (ε : S) :
    _root_.WittVector.frobenius (xi p ε) ∈ Ideal.span {(p : WittVector p S), xi p ε} := by
  obtain ⟨y, hy⟩ := (isFrobeniusLift_frobenius p S).dvd_sub_pow (xi p ε)
  refine Ideal.mem_span_pair.mpr ⟨y, xi p ε ^ (p - 1), ?_⟩
  rw [← pow_succ, Nat.sub_add_cancel (Fact.out : p.Prime).one_le]
  linear_combination -hy

namespace AMax

variable {p}

variable (p) in
/-- The relation `p X - ξ` over `W(S)`. -/
private noncomputable abbrev rel (ε : S) : (WittVector p S)[X] :=
  C (p : WittVector p S) * X - C (xi p ε)

variable (p) in
/-- The ring `W(S)[X] ⧸ (p X - ξ)` whose completion is `A_max`. -/
private abbrev Pre (ε : S) : Type _ := AdjoinRoot (rel p ε)

variable (p) in
/-- The ideal `(p)` of `W(S)[X] ⧸ (p X - ξ)`. -/
private noncomputable abbrev preIdeal (ε : S) : Ideal (Pre p ε) :=
  Ideal.span {(p : Pre p ε)}

/-- The canonical map from `W(S)[X] ⧸ (p X - ξ)` to its `p`-adic completion `A_max`. -/
private noncomputable def ofPre (ε : S) : Pre p ε →+* AMax p ε :=
  algebraMap (Pre p ε) (AdicCompletion (preIdeal p ε) (Pre p ε))

variable (p) in
/-- The element `ξ / p` of `A_max`, the class of `X` in `W(S)[X] ⧸ (p X - ξ)`. -/
noncomputable def xiDivP (ε : S) : AMax p ε :=
  ofPre ε (AdjoinRoot.root _)

variable {ε : S}

-- Both sides are the class in the completion of `AdjoinRoot.of _ a`: the `W(S)`-algebra structure
-- of `A_max` is that of the completion (`AdicCompletion.algebraMap_apply`), which is the class of
-- the image under the algebra map of `W(S)[X] ⧸ (p X - ξ)`, namely `AdjoinRoot.of`
-- (`AdjoinRoot.algebraMap_eq`). Both lemmas are proved by `rfl`.
private theorem ofPre_of (a : WittVector p S) :
    ofPre ε (AdjoinRoot.of _ a) = algebraMap (WittVector p S) (AMax p ε) a :=
  (rfl)

private theorem ofPre_root : ofPre ε (AdjoinRoot.root (rel p ε)) = xiDivP p ε :=
  (rfl)

/-- **The defining relation of `ξ / p`**: `p * (ξ / p) = ξ` in `A_max`. -/
@[simp]
theorem natCast_mul_xiDivP :
    (p : AMax p ε) * xiDivP p ε = algebraMap (WittVector p S) (AMax p ε) (xi p ε) := by
  have h := congrArg (ofPre ε) (AdjoinRoot.mk_self (f := rel p ε))
  simpa [sub_eq_zero, ofPre_of, ofPre_root, -AdjoinRoot.mk_self] using h

/-- **`A_max` is `p`-adically complete.** -/
instance instIsAdicComplete : IsAdicComplete (Ideal.span {(p : AMax p ε)}) (AMax p ε) := by
  have h := AdicCompletion.isAdicComplete_self (preIdeal p ε) (Submodule.fg_span_singleton _)
  rwa [preIdeal, Ideal.map_span, Set.image_singleton, map_natCast] at h

/-- **`p` is a nonzerodivisor of `A_max`** when `S` is a domain and `ε ≠ 1`: then `p, ξ` is a
weakly regular sequence of `W(S)`, so `p` is a nonzerodivisor on `W(S)[X] ⧸ (p X - ξ)`, and
hence on its `p`-adic completion. -/
theorem natCast_mem_nonZeroDivisors [IsDomain S] (hε : ε ≠ 1) :
    (p : AMax p ε) ∈ (AMax p ε)⁰ := by
  have h := (isWeaklyRegular_natCast_xi p hε).isSMulRegular_adjoinRoot_C_mul_X_sub_C
  replace h := (isSMulRegular_algebraMap_iff (A := Pre p ε)).mpr h
  rw [map_natCast (algebraMap (WittVector p S) (Pre p ε))] at h
  have hreg := IsRegular.adicCompletion
    ((Commute.isRegular_iff fun _ ↦ Commute.all _ _).mpr (isLeftRegular_iff.mpr h))
  rw [map_natCast (algebraMap (Pre p ε) (AdicCompletion (preIdeal p ε) (Pre p ε)))] at hreg
  exact isRegular_iff_mem_nonZeroDivisors.mp hreg

/-- In `A_max` the ideal generated by `p` and `ξ` is generated by `p`, since `ξ = p * (ξ / p)`. -/
theorem map_span_natCast_xi :
    (Ideal.span {(p : WittVector p S), xi p ε}).map (algebraMap (WittVector p S) (AMax p ε)) =
      Ideal.span {(p : AMax p ε)} := by
  rw [Ideal.map_span, Set.image_pair, map_natCast, ← natCast_mul_xiDivP, Set.pair_comm]
  exact Submodule.span_insert_eq_span (Ideal.mem_span_singleton.mpr (dvd_mul_right _ _))

/-- **Divisibility by powers of `p`**: if `a ∈ (p, ξ) ^ n` in `W(S)`, then `p ^ n` divides the
image of `a` in `A_max`. -/
theorem natCast_pow_dvd_algebraMap_of_mem_pow {a : WittVector p S} {n : ℕ}
    (ha : a ∈ Ideal.span {(p : WittVector p S), xi p ε} ^ n) :
    (p : AMax p ε) ^ n ∣ algebraMap (WittVector p S) (AMax p ε) a := by
  have h := Ideal.mem_map_of_mem (algebraMap (WittVector p S) (AMax p ε)) ha
  rwa [Ideal.map_pow, map_span_natCast_xi, Ideal.span_singleton_pow,
    Ideal.mem_span_singleton] at h

section Lift

variable {R : Type*} [CommRing R] [IsAdicComplete (Ideal.span {(p : R)}) R]

/-- The map `W(S)[X] ⧸ (p X - ξ) → R` extending `f` with `X ↦ x`. -/
private noncomputable def liftPre (f : WittVector p S →+* R) (x : R)
    (hx : f (xi p ε) = p * x) : Pre p ε →+* R :=
  AdjoinRoot.lift f x (by simp [hx])

/-- **The universal property of `A_max`.** A ring map `f : W(S) → R` to a `p`-adically complete
ring, together with an element `x` such that `f(ξ) = p * x`, extends to a ring map `A_max → R`
sending `ξ / p` to `x`. If `p` is a nonzerodivisor of `R`, then `x` is determined by `f`. -/
noncomputable def lift (f : WittVector p S →+* R) (x : R) (hx : f (xi p ε) = p * x) :
    AMax p ε →+* R :=
  ((AdicCompletion.ofAlgEquiv (Ideal.span {(p : R)})).symm : _ →+* R).comp
    (AdicCompletion.mapₐ (liftPre f x hx).toIntAlgHom (Ideal.map_le_iff_le_comap.mp
      (by rw [Ideal.map_span, Set.image_singleton, map_natCast]))).toRingHom

private theorem lift_ofPre (f : WittVector p S →+* R) (x : R) (hx : f (xi p ε) = p * x)
    (y : Pre p ε) : lift f x hx (ofPre ε y) = liftPre f x hx y := by
  -- `ofPre ε y` is the class of `y` in the completion, on which `AdicCompletion.mapₐ` is known.
  exact (congrArg (AdicCompletion.ofAlgEquiv _).symm (AdicCompletion.mapₐ_of _ _ y)).trans
    (AdicCompletion.ofAlgEquiv_symm_of _ _)

/-- The extension `AMax.lift f x hx` restricts to `f` on `W(S)`. -/
@[simp]
theorem lift_algebraMap (f : WittVector p S →+* R) (x : R) (hx : f (xi p ε) = p * x)
    (a : WittVector p S) : lift f x hx (algebraMap (WittVector p S) (AMax p ε) a) = f a := by
  rw [← ofPre_of, lift_ofPre, liftPre, AdjoinRoot.lift_of]

/-- The extension `AMax.lift f x hx` sends `ξ / p` to `x`. -/
@[simp]
theorem lift_xiDivP (f : WittVector p S →+* R) (x : R) (hx : f (xi p ε) = p * x) :
    lift f x hx (xiDivP p ε) = x := by
  rw [← ofPre_root, lift_ofPre, liftPre, AdjoinRoot.lift_root]

/-- The extension `AMax.lift f x hx` restricts to `f` on `W(S)`. -/
@[simp]
theorem lift_comp_algebraMap (f : WittVector p S →+* R) (x : R) (hx : f (xi p ε) = p * x) :
    (lift f x hx).comp (algebraMap (WittVector p S) (AMax p ε)) = f :=
  RingHom.ext (lift_algebraMap f x hx)

end Lift

/-- **Uniqueness in the universal property of `A_max`.** Two ring maps from `A_max` to a
`p`-adically separated ring that agree on `W(S)` and on `ξ / p` are equal. -/
theorem ringHom_ext {R : Type*} [CommRing R] [IsHausdorff (Ideal.span {(p : R)}) R]
    {f g : AMax p ε →+* R}
    (h : f.comp (algebraMap (WittVector p S) (AMax p ε)) =
      g.comp (algebraMap (WittVector p S) (AMax p ε)))
    (hx : f (xiDivP p ε) = g (xiDivP p ε)) : f = g := by
  have hle (k : AMax p ε →+* R) :
      (preIdeal p ε).map (algebraMap (Pre p ε) (AdicCompletion (preIdeal p ε) (Pre p ε))) ≤
        (Ideal.span {(p : R)}).comap k := by
    have hk : Ideal.span {(p : AMax p ε)} ≤ (Ideal.span {(p : R)}).comap k :=
      Ideal.map_le_iff_le_comap.mp (by rw [Ideal.map_span, Set.image_singleton, map_natCast])
    rw [Ideal.map_span, Set.image_singleton, map_natCast]
    exact hk
  refine AdicCompletion.ringHom_ext (Submodule.fg_span_singleton _) (hle f) (hle g) ?_
  exact AdjoinRoot.ringHom_ext (RingHom.ext fun a ↦ congr($h a)) hx

/-- Two ring maps from `A_max` to a `p`-adically separated ring in which `p` is a nonzerodivisor
are equal as soon as they agree on `W(S)`: their values at `ξ / p` are both the quotient of the
common value at `ξ` by `p`. -/
theorem ringHom_ext_of_natCast_mem_nonZeroDivisors {R : Type*} [CommRing R]
    [IsHausdorff (Ideal.span {(p : R)}) R] (hp : (p : R) ∈ R⁰) {f g : AMax p ε →+* R}
    (h : f.comp (algebraMap (WittVector p S) (AMax p ε)) =
      g.comp (algebraMap (WittVector p S) (AMax p ε))) : f = g := by
  refine ringHom_ext h ((mul_cancel_left_mem_nonZeroDivisors hp).mp ?_)
  have := congr($h (xi p ε))
  simp only [RingHom.comp_apply, ← natCast_mul_xiDivP, map_mul, map_natCast] at this
  exact this

section Density

/-- The canonical map `W(S)[X] ⧸ (p X - ξ) → A_max` as a `W(S)`-algebra map. -/
private noncomputable def ofPreₐ (ε : S) : Pre p ε →ₐ[WittVector p S] AMax p ε :=
  { ofPre ε with commutes' := ofPre_of }

/-- The image of `W(S)[X] ⧸ (p X - ξ)` in `A_max` is the subalgebra generated by `ξ / p`. -/
private theorem range_ofPreₐ :
    (ofPreₐ (p := p) ε).range = Algebra.adjoin (WittVector p S) {xiDivP p ε} := by
  rw [← Algebra.map_top, ← AdjoinRoot.adjoinRoot_eq_top, AlgHom.map_adjoin_singleton]
  exact congrArg (Algebra.adjoin _ {·}) ofPre_root

/-- **Polynomials in `ξ / p` are dense in `A_max`**: every element of `A_max` is congruent
modulo `p ^ n` to an element of the `W(S)`-subalgebra generated by `ξ / p`. -/
theorem exists_mem_adjoin_sub_mem_span_pow (x : AMax p ε) (n : ℕ) :
    ∃ y ∈ Algebra.adjoin (WittVector p S) {xiDivP p ε},
      x - y ∈ Ideal.span {(p : AMax p ε) ^ n} := by
  obtain ⟨y, hy⟩ :=
    AdicCompletion.exists_sub_algebraMap_mem_map_pow (Submodule.fg_span_singleton _) n x
  rw [Ideal.span_singleton_pow, Ideal.map_span, Set.image_singleton, map_pow,
    map_natCast (algebraMap (Pre p ε) (AdicCompletion (preIdeal p ε) (Pre p ε)))] at hy
  exact ⟨ofPre ε y, range_ofPreₐ (p := p) (ε := ε) ▸ ⟨y, rfl⟩, hy⟩

/-- Every element of the `W(S)`-subalgebra of `A_max` generated by `ξ / p` becomes an element of
`W(S)` after multiplication by a power of `p`. -/
theorem exists_natCast_pow_mul_eq_algebraMap {y : AMax p ε}
    (hy : y ∈ Algebra.adjoin (WittVector p S) {xiDivP p ε}) :
    ∃ (k : ℕ) (a : WittVector p S), (p : AMax p ε) ^ k * y = algebraMap _ _ a := by
  rw [← range_ofPreₐ] at hy
  obtain ⟨z, rfl⟩ := hy
  obtain ⟨k, a, h⟩ := AdjoinRoot.exists_of_pow_mul_eq_of_C_mul_X_sub_C z
  refine ⟨k, a, ?_⟩
  have h' := congrArg (ofPre ε) h
  rwa [map_mul, ofPre_of, ofPre_of, map_pow, map_natCast] at h'

end Density

section Map

variable {S' : Type*} [CommRing S'] [CharP S' p] [PerfectRing S' p] {ε' : S'}

/-- **Extension of ring maps to `A_max`.** A ring map `σ : W(S) → W(S')` carrying `ξ` into the
ideal `(p, ξ')` extends to a ring map `A_max(ε) → A_max(ε')`. This applies to the Witt vector
Frobenius (`AMax.frobenius`) and to every `σ` with `ξ' ∣ σ(ξ)`, such as the automorphisms of
`W(S)` induced by Galois automorphisms. The value at `ξ / p` is a quotient of `σ(ξ)` by `p`
(`AMax.natCast_mul_map_xiDivP`), unique when `p` is a nonzerodivisor of `A_max(ε')`. -/
noncomputable def map (σ : WittVector p S →+* WittVector p S')
    (hσ : σ (xi p ε) ∈ Ideal.span {(p : WittVector p S'), xi p ε'}) : AMax p ε →+* AMax p ε' :=
  have h : (p : AMax p ε') ∣ algebraMap (WittVector p S') (AMax p ε') (σ (xi p ε)) := by
    simpa using natCast_pow_dvd_algebraMap_of_mem_pow (a := σ (xi p ε)) (n := 1)
      (by rwa [pow_one])
  lift ((algebraMap (WittVector p S') (AMax p ε')).comp σ) (dvd_def.mp h).choose
    (dvd_def.mp h).choose_spec

variable (σ : WittVector p S →+* WittVector p S')
  (hσ : σ (xi p ε) ∈ Ideal.span {(p : WittVector p S'), xi p ε'})

/-- The extension `AMax.map σ hσ` restricts to `σ` on `W(S)`. -/
@[simp]
theorem map_algebraMap (a : WittVector p S) :
    map σ hσ (algebraMap (WittVector p S) (AMax p ε) a) =
      algebraMap (WittVector p S') (AMax p ε') (σ a) :=
  lift_algebraMap _ _ _ a

/-- The extension `AMax.map σ hσ` restricts to `σ` on `W(S)`. -/
@[simp]
theorem map_comp_algebraMap :
    (map σ hσ).comp (algebraMap (WittVector p S) (AMax p ε)) =
      (algebraMap (WittVector p S') (AMax p ε')).comp σ :=
  RingHom.ext (map_algebraMap σ hσ)

/-- The extension `AMax.map σ hσ` sends `ξ / p` to a quotient of `σ(ξ)` by `p`. -/
theorem natCast_mul_map_xiDivP :
    (p : AMax p ε') * map σ hσ (xiDivP p ε) =
      algebraMap (WittVector p S') (AMax p ε') (σ (xi p ε)) := by
  simp only [map, lift_xiDivP]
  generalize_proofs h
  exact h.choose_spec.symm

/-- The extension of the identity is the identity, when `p` is a nonzerodivisor of `A_max`. -/
theorem map_id (hp : (p : AMax p ε) ∈ (AMax p ε)⁰)
    (h : RingHom.id (WittVector p S) (xi p ε) ∈ Ideal.span {(p : WittVector p S), xi p ε}) :
    map (RingHom.id _) h = RingHom.id (AMax p ε) :=
  ringHom_ext_of_natCast_mem_nonZeroDivisors hp (by ext; simp)

/-- **Extension to `A_max` is functorial**, when `p` is a nonzerodivisor of the target. -/
theorem map_comp {S'' : Type*} [CommRing S''] [CharP S'' p] [PerfectRing S'' p] {ε'' : S''}
    (hp : (p : AMax p ε'') ∈ (AMax p ε'')⁰) (τ : WittVector p S' →+* WittVector p S'')
    (hτ : τ (xi p ε') ∈ Ideal.span {(p : WittVector p S''), xi p ε''})
    (hτσ : (τ.comp σ) (xi p ε) ∈ Ideal.span {(p : WittVector p S''), xi p ε''}) :
    (map τ hτ).comp (map σ hσ) = map (τ.comp σ) hτσ :=
  ringHom_ext_of_natCast_mem_nonZeroDivisors hp (by ext; simp)

end Map

section Frobenius

variable (p) in
/-- **The Frobenius of `A_max`**: the extension of the Witt vector Frobenius `φ` of `W(S)`, which
carries `ξ` into `(p, ξ)` since `φ(ξ) ≡ ξ ^ p` modulo `p`. -/
noncomputable def frobenius (ε : S) : AMax p ε →+* AMax p ε :=
  map _root_.WittVector.frobenius (frobenius_xi_mem_span p ε)

/-- The Frobenius of `A_max` is the extension `AMax.map` of the Witt vector Frobenius, so that
`AMax.map_comp` applies to its composites. -/
theorem frobenius_eq_map
    (h : _root_.WittVector.frobenius (xi p ε) ∈ Ideal.span {(p : WittVector p S), xi p ε}) :
    frobenius p ε = map _root_.WittVector.frobenius h :=
  (rfl)

/-- The Frobenius of `A_max` restricts to the Witt vector Frobenius on `W(S)`. -/
@[simp]
theorem frobenius_algebraMap (a : WittVector p S) :
    frobenius p ε (algebraMap (WittVector p S) (AMax p ε) a) =
      algebraMap (WittVector p S) (AMax p ε) (_root_.WittVector.frobenius a) :=
  map_algebraMap _ _ a

/-- The Frobenius of `A_max` sends `ξ / p` to a quotient of `φ(ξ)` by `p`. -/
theorem natCast_mul_frobenius_xiDivP :
    (p : AMax p ε) * frobenius p ε (xiDivP p ε) =
      algebraMap (WittVector p S) (AMax p ε) (_root_.WittVector.frobenius (xi p ε)) :=
  natCast_mul_map_xiDivP _ _

end Frobenius

section Theta

variable {A : Type*} [CommRing A] [Fact ¬IsUnit (p : A)] [IsAdicComplete (Ideal.span {(p : A)}) A]
  {ε : PreTilt A p}

/-- **Fontaine's map on `A_max`**: when `θ : W(A♭) → A` kills `ξ`, it extends to a ring map
`A_max → A` sending `ξ / p` to `0`. By `PreTilt.fontaineTheta_xi_eq_zero`, `θ` kills `ξ` when
`A` is a domain and the sharp of `ε ^ (1 / p)` is a primitive `p`-th root of unity. -/
noncomputable def theta (hξ : fontaineTheta A p (xi p ε) = 0) : AMax p ε →+* A :=
  lift (fontaineTheta A p) 0 (by rw [hξ, mul_zero])

variable (hξ : fontaineTheta A p (xi p ε) = 0)

/-- Fontaine's map on `A_max` restricts to Fontaine's map on `W(A♭)`. -/
@[simp]
theorem theta_algebraMap (a : WittVector p (PreTilt A p)) :
    theta hξ (algebraMap _ (AMax p ε) a) = fontaineTheta A p a :=
  lift_algebraMap _ _ _ a

/-- Fontaine's map on `A_max` restricts to Fontaine's map on `W(A♭)`. -/
@[simp]
theorem theta_comp_algebraMap :
    (theta hξ).comp (algebraMap _ (AMax p ε)) = fontaineTheta A p :=
  lift_comp_algebraMap _ _ _

/-- Fontaine's map on `A_max` kills `ξ / p`. -/
@[simp]
theorem theta_xiDivP : theta hξ (xiDivP p ε) = 0 :=
  lift_xiDivP _ _ _

end Theta

end AMax

-- The body is exposed so that the ring structure can be transported from the localization.
/-- **Colmez's ring `B⁺_max = A_max[1/p]`**, the localization of `A_max` away from `p`. -/
@[expose] noncomputable def BMaxPlus (ε : S) : Type _ :=
  Localization.Away (p : AMax p ε)

noncomputable instance (ε : S) : CommRing (BMaxPlus p ε) :=
  inferInstanceAs (CommRing (Localization.Away _))

noncomputable instance (ε : S) : Algebra (AMax p ε) (BMaxPlus p ε) :=
  inferInstanceAs (Algebra (AMax p ε) (Localization.Away (p : AMax p ε)))

instance (ε : S) : IsLocalization.Away (p : AMax p ε) (BMaxPlus p ε) :=
  inferInstanceAs (IsLocalization.Away (p : AMax p ε) (Localization.Away (p : AMax p ε)))

noncomputable instance (ε : S) : Algebra (WittVector p S) (BMaxPlus p ε) :=
  inferInstanceAs (Algebra _ (Localization.Away (p : AMax p ε)))

instance (ε : S) : IsScalarTower (WittVector p S) (AMax p ε) (BMaxPlus p ε) :=
  inferInstanceAs (IsScalarTower _ _ (Localization.Away (p : AMax p ε)))

namespace BMaxPlus

variable {p} {ε : S}

/-- **`A_max` embeds in `B⁺_max`** when `S` is a domain and `ε ≠ 1`, as `p` is then a
nonzerodivisor of `A_max`. -/
theorem algebraMap_injective [IsDomain S] (hε : ε ≠ 1) :
    Function.Injective (algebraMap (AMax p ε) (BMaxPlus p ε)) :=
  IsLocalization.injective _ (Submonoid.powers_le.mpr (AMax.natCast_mem_nonZeroDivisors hε))

/-- A ring map from `A_max` maps the powers of `p` into the powers of `p`. -/
private theorem powers_le_comap {T : Type*} [CommRing T] (g : AMax p ε →+* T) :
    Submonoid.powers (p : AMax p ε) ≤ (Submonoid.powers (p : T)).comap g :=
  Submonoid.powers_le.mpr (by simp [Submonoid.mem_comap])

section Map

variable {S' : Type*} [CommRing S'] [CharP S' p] [PerfectRing S' p] {ε' : S'}
  (σ : WittVector p S →+* WittVector p S')
  (hσ : σ (xi p ε) ∈ Ideal.span {(p : WittVector p S'), xi p ε'})

/-- The extension `B⁺_max(ε) → B⁺_max(ε')` of a ring map `σ : W(S) → W(S')` with
`σ(ξ) ∈ (p, ξ')`, obtained from `AMax.map σ hσ` by inverting `p`. -/
noncomputable def map : BMaxPlus p ε →+* BMaxPlus p ε' :=
  IsLocalization.map (M := Submonoid.powers (p : AMax p ε))
    (T := Submonoid.powers (p : AMax p ε')) _ (AMax.map σ hσ) (powers_le_comap _)

/-- The extension `BMaxPlus.map σ hσ` restricts to `AMax.map σ hσ` on `A_max`. -/
@[simp]
theorem map_algebraMap (x : AMax p ε) :
    map σ hσ (algebraMap (AMax p ε) (BMaxPlus p ε) x) =
      algebraMap (AMax p ε') (BMaxPlus p ε') (AMax.map σ hσ x) :=
  IsLocalization.map_eq _ _

/-- The extension `BMaxPlus.map σ hσ` restricts to `σ` on `W(S)`. -/
@[simp]
theorem map_algebraMap_wittVector (a : WittVector p S) :
    map σ hσ (algebraMap (WittVector p S) (BMaxPlus p ε) a) =
      algebraMap (WittVector p S') (BMaxPlus p ε') (σ a) := by
  rw [IsScalarTower.algebraMap_apply (WittVector p S) (AMax p ε), map_algebraMap,
    AMax.map_algebraMap, ← IsScalarTower.algebraMap_apply]

/-- The extension of the identity to `B⁺_max` is the identity, when `p` is a nonzerodivisor of
`A_max`. -/
theorem map_id (hp : (p : AMax p ε) ∈ (AMax p ε)⁰)
    (h : RingHom.id (WittVector p S) (xi p ε) ∈ Ideal.span {(p : WittVector p S), xi p ε}) :
    map (RingHom.id _) h = RingHom.id (BMaxPlus p ε) :=
  IsLocalization.ringHom_ext (Submonoid.powers (p : AMax p ε)) <| by
    ext x
    simp [AMax.map_id hp h]

/-- **Extension to `B⁺_max` is functorial**, when `p` is a nonzerodivisor of the target. -/
theorem map_comp {S'' : Type*} [CommRing S''] [CharP S'' p] [PerfectRing S'' p] {ε'' : S''}
    (hp : (p : AMax p ε'') ∈ (AMax p ε'')⁰) (τ : WittVector p S' →+* WittVector p S'')
    (hτ : τ (xi p ε') ∈ Ideal.span {(p : WittVector p S''), xi p ε''})
    (hτσ : (τ.comp σ) (xi p ε) ∈ Ideal.span {(p : WittVector p S''), xi p ε''}) :
    (map τ hτ).comp (map σ hσ) = map (τ.comp σ) hτσ :=
  IsLocalization.ringHom_ext (Submonoid.powers (p : AMax p ε)) <| by
    ext x
    simp [← AMax.map_comp σ hσ hp τ hτ hτσ]

end Map

variable (p) in
/-- **The Frobenius of `B⁺_max`**: the extension `BMaxPlus.map` of the Witt vector Frobenius,
which restricts to the Frobenius of `A_max`. -/
noncomputable def frobenius (ε : S) : BMaxPlus p ε →+* BMaxPlus p ε :=
  map _root_.WittVector.frobenius (frobenius_xi_mem_span p ε)

/-- The Frobenius of `B⁺_max` is the extension `BMaxPlus.map` of the Witt vector Frobenius, so
that `BMaxPlus.map_comp` applies to its composites. -/
theorem frobenius_eq_map
    (h : _root_.WittVector.frobenius (xi p ε) ∈ Ideal.span {(p : WittVector p S), xi p ε}) :
    frobenius p ε = map _root_.WittVector.frobenius h :=
  (rfl)

/-- The Frobenius of `B⁺_max` restricts to the Frobenius of `A_max`. -/
@[simp]
theorem frobenius_algebraMap (x : AMax p ε) :
    frobenius p ε (algebraMap (AMax p ε) (BMaxPlus p ε) x) =
      algebraMap (AMax p ε) (BMaxPlus p ε) (AMax.frobenius p ε x) :=
  map_algebraMap _ _ x

/-- The Frobenius of `B⁺_max` restricts to the Witt vector Frobenius on `W(S)`. -/
@[simp]
theorem frobenius_algebraMap_wittVector (a : WittVector p S) :
    frobenius p ε (algebraMap (WittVector p S) (BMaxPlus p ε) a) =
      algebraMap (WittVector p S) (BMaxPlus p ε) (_root_.WittVector.frobenius a) :=
  map_algebraMap_wittVector _ _ a

section Theta

variable {A : Type*} [CommRing A] [Fact ¬IsUnit (p : A)] [IsAdicComplete (Ideal.span {(p : A)}) A]
  {ε : PreTilt A p}

/-- **Fontaine's map on `B⁺_max`**: Fontaine's map on `A_max` (`AMax.theta`), with values in an
`A`-algebra `K` in which `p` is a unit, extended to `B⁺_max = A_max[1/p]`. For the integers `A`
of `ℂ_p`, one may take `K = ℂ_p`, or `K = A[1/p]`. -/
noncomputable def theta (hξ : fontaineTheta A p (xi p ε) = 0) {K : Type*} [CommRing K]
    [Algebra A K] (hp : IsUnit (p : K)) : BMaxPlus p ε →+* K :=
  IsLocalization.Away.lift (p : AMax p ε) (g := (algebraMap A K).comp (AMax.theta hξ))
    (by rwa [RingHom.comp_apply, map_natCast, map_natCast])

/-- Fontaine's map on `B⁺_max` restricts to Fontaine's map on `A_max`. -/
@[simp]
theorem theta_algebraMap (hξ : fontaineTheta A p (xi p ε) = 0) {K : Type*} [CommRing K]
    [Algebra A K] (hp : IsUnit (p : K)) (x : AMax p ε) :
    theta hξ hp (algebraMap (AMax p ε) (BMaxPlus p ε) x) = algebraMap A K (AMax.theta hξ x) :=
  IsLocalization.Away.lift_eq _ _ _

/-- Fontaine's map on `B⁺_max` restricts to Fontaine's map on `W(A♭)`. -/
@[simp]
theorem theta_algebraMap_wittVector (hξ : fontaineTheta A p (xi p ε) = 0) {K : Type*}
    [CommRing K] [Algebra A K] (hp : IsUnit (p : K)) (a : WittVector p (PreTilt A p)) :
    theta hξ hp (algebraMap _ (BMaxPlus p ε) a) = algebraMap A K (fontaineTheta A p a) := by
  rw [IsScalarTower.algebraMap_apply _ (AMax p ε), theta_algebraMap, AMax.theta_algebraMap]

end Theta

end BMaxPlus

-- The body is exposed so that the ring structure can be transported from the localization.
/-- **The ring `B_max = B⁺_max[1/μ]`**, the localization of `B⁺_max` away from the period
`μ = [ε] - 1`. -/
@[expose] noncomputable def BMax (ε : S) : Type _ :=
  Localization.Away (algebraMap (WittVector p S) (BMaxPlus p ε) (mu p ε))

noncomputable instance (ε : S) : CommRing (BMax p ε) :=
  inferInstanceAs (CommRing (Localization.Away _))

noncomputable instance (ε : S) : Algebra (BMaxPlus p ε) (BMax p ε) :=
  inferInstanceAs (Algebra (BMaxPlus p ε)
    (Localization.Away (algebraMap (WittVector p S) (BMaxPlus p ε) (mu p ε))))

instance (ε : S) :
    IsLocalization.Away (algebraMap (WittVector p S) (BMaxPlus p ε) (mu p ε)) (BMax p ε) :=
  inferInstanceAs (IsLocalization.Away (algebraMap (WittVector p S) (BMaxPlus p ε) (mu p ε))
    (Localization.Away (algebraMap (WittVector p S) (BMaxPlus p ε) (mu p ε))))

noncomputable instance (ε : S) : Algebra (WittVector p S) (BMax p ε) :=
  inferInstanceAs (Algebra _ (Localization.Away (algebraMap (WittVector p S) (BMaxPlus p ε)
    (mu p ε))))

instance (ε : S) : IsScalarTower (WittVector p S) (BMaxPlus p ε) (BMax p ε) :=
  inferInstanceAs (IsScalarTower _ _ (Localization.Away (algebraMap (WittVector p S)
    (BMaxPlus p ε) (mu p ε))))

/-- The period `μ = [ε] - 1` is a unit of `B_max`. -/
theorem BMax.isUnit_algebraMap_mu (ε : S) :
    IsUnit (algebraMap (WittVector p S) (BMax p ε) (mu p ε)) := by
  rw [IsScalarTower.algebraMap_apply (WittVector p S) (BMaxPlus p ε)]
  exact IsLocalization.Away.algebraMap_isUnit _

end AMax

end TauCeti.Perfectoid
