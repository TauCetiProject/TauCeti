/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.GroupTheory.OrderOfElement
public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Point.MapEquiv

/-!
# The twisted Frobenius kernel of a Weierstrass curve over a finite field

Let `k` be a finite field with `q` elements and characteristic `p`, let `W` be a Weierstrass curve
over `k`, let `L` be a field extension of `k` and let `π` be the `q`-power map on the points of `W`
over `L`, that is Mathlib's `WeierstrassCurve.Affine.Point.map` along
`FiniteField.frobeniusAlgHom k L`. For `i : ℕ` the *twisted Frobenius kernel* is the subgroup

`B_i(W, L) = {P | P is killed by some m > 0 prime to p, and q ^ i • π P = P}`

of the points of `W` over `L`. When `L` is an algebraic closure of `k`, it is the group of
invariants of the arithmetic Frobenius acting on the prime-to-`p` torsion with its action
multiplied by `q ^ i`, the `i`-th Tate twist; for `i ≥ 1` and `W` elliptic, the computation of
the K-theory of curves over finite fields identifies it with the even K-group `K_{2i}` of the
elliptic curve (Weibel, Theorem VI.6.7). Its order is computed in
`TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Frobenius.TwistedKernel`.

This file defines the subgroup and proves its elementary properties: a `k`-rational point lies in
it exactly when it is prime-to-`p` torsion killed by `q ^ i - 1`, its only `p`-torsion point is
zero, and it is transported by every `k`-algebra map of fields.

## Main definitions

* `WeierstrassCurve.twistedFrobeniusKernel W L i`: the subgroup `B_i(W, L)`.
* `WeierstrassCurve.twistedFrobeniusKernelEquiv W i e`: the additive equivalence
  `B_i(W, L) ≃+ B_i(W, L')` induced by a `k`-algebra equivalence `e : L ≃ₐ[k] L'`.

## Main results

* `WeierstrassCurve.mem_twistedFrobeniusKernel_iff`: the defining membership condition.
* `WeierstrassCurve.baseChange_mem_twistedFrobeniusKernel_iff`: a base-changed rational point
  lies in `B_i` exactly when it is prime-to-`p` torsion and killed by `q ^ i - 1`;
  `baseChange_mem_twistedFrobeniusKernel_iff_of_one_le` drops the torsion condition when
  `i ≥ 1`.
* `WeierstrassCurve.eq_zero_of_mem_twistedFrobeniusKernel_of_ringChar_nsmul_eq_zero`: the only
  point of `B_i` killed by `p` is zero.
* `WeierstrassCurve.map_mem_twistedFrobeniusKernel_iff` and
  `WeierstrassCurve.comap_twistedFrobeniusKernel`: a `k`-algebra map `L →ₐ[k] L'` pulls
  `B_i(W, L')` back to `B_i(W, L)`.

## References

* C. A. Weibel, *The K-book*, VI.6.4 and Theorem VI.6.7.
-/

public section

open scoped WeierstrassCurve

namespace WeierstrassCurve

open Affine

variable {k : Type*} [Field k] [Fintype k] (W : WeierstrassCurve k)
  (L : Type*) [Field L] [DecidableEq L] [Algebra k L]
  {L' : Type*} [Field L'] [DecidableEq L'] [Algebra k L'] (i : ℕ)

/-- **The twisted Frobenius kernel** `B_i(W, L)`: the points of `W` over `L` that are killed by a
positive integer prime to the characteristic `p` of `k` and satisfy `q ^ i • π P = P`, where `q`
is the cardinality of `k` and `π` is the `q`-power map on points.

For `L` an algebraic closure of `k` this is the subgroup of the prime-to-`p` torsion fixed by the
arithmetic Frobenius twisted by the `i`-th power of the cyclotomic character. -/
noncomputable def twistedFrobeniusKernel : AddSubgroup (W⁄L).toAffine.Point where
  carrier := {P | (∃ m : ℕ, 0 < m ∧ m.Coprime (ringChar k) ∧ m • P = 0) ∧
    (Nat.card k ^ i) • Point.map (W' := W) (FiniteField.frobeniusAlgHom k L) P = P}
  zero_mem' := ⟨⟨1, one_pos, Nat.coprime_one_left _, one_nsmul _⟩, by simp⟩
  add_mem' := by
    rintro P Q ⟨⟨m, hm, hmp, hmP⟩, hP⟩ ⟨⟨n, hn, hnp, hnQ⟩, hQ⟩
    refine ⟨⟨m * n, Nat.mul_pos hm hn, Nat.Coprime.mul_left hmp hnp, ?_⟩, ?_⟩
    · rw [smul_add, mul_nsmul P, hmP, mul_nsmul' Q, hnQ, nsmul_zero, nsmul_zero, add_zero]
    · rw [map_add, smul_add, hP, hQ]
  neg_mem' := by
    rintro P ⟨⟨m, hm, hmp, hmP⟩, hP⟩
    exact ⟨⟨m, hm, hmp, by rw [smul_neg, hmP, neg_zero]⟩, by rw [map_neg, smul_neg, hP]⟩

variable {W L i}

/-- Membership in the twisted Frobenius kernel: prime-to-`p` torsion fixed by `q ^ i • π`. Not
`@[simp]`: unfolding membership would preempt `map_mem_twistedFrobeniusKernel_iff`. -/
theorem mem_twistedFrobeniusKernel_iff {P : (W⁄L).toAffine.Point} :
    P ∈ W.twistedFrobeniusKernel L i ↔
      (∃ m : ℕ, 0 < m ∧ m.Coprime (ringChar k) ∧ m • P = 0) ∧
        (Nat.card k ^ i) • Point.map (W' := W) (FiniteField.frobeniusAlgHom k L) P = P :=
  Iff.rfl

/-- **A point of the twisted Frobenius kernel killed by the characteristic is zero**: its order
divides both `p` and an integer prime to `p`. -/
theorem eq_zero_of_mem_twistedFrobeniusKernel_of_ringChar_nsmul_eq_zero
    {P : (W⁄L).toAffine.Point} (hP : P ∈ W.twistedFrobeniusKernel L i)
    (hp : ringChar k • P = 0) : P = 0 := by
  obtain ⟨⟨m, -, hmp, hmP⟩, -⟩ := hP
  rw [← AddMonoid.addOrderOf_eq_one_iff]
  exact Nat.eq_one_of_dvd_coprimes hmp (addOrderOf_dvd_of_nsmul_eq_zero hmP)
    (addOrderOf_dvd_of_nsmul_eq_zero hp)

section Rational

variable [DecidableEq k]

variable (W L) in
/-- The `q`-power map fixes every point coming from the base field. -/
private theorem map_frobeniusAlgHom_baseChange (P : (W⁄k).toAffine.Point) :
    Point.map (W' := W) (FiniteField.frobeniusAlgHom k L) (Point.baseChange (W' := W) k L P) =
      Point.baseChange (W' := W) k L P :=
  Point.map_baseChange (W' := W) (FiniteField.frobeniusAlgHom k L) P

/-- **A rational point lies in the twisted Frobenius kernel** after base change exactly when it is
killed by a positive integer prime to `p` and by `q ^ i - 1`, the `q`-power map fixing it. -/
theorem baseChange_mem_twistedFrobeniusKernel_iff (P : (W⁄k).toAffine.Point) :
    Point.baseChange (W' := W) k L P ∈ W.twistedFrobeniusKernel L i ↔
      (∃ m : ℕ, 0 < m ∧ m.Coprime (ringChar k) ∧ m • P = 0) ∧ (Nat.card k ^ i - 1) • P = 0 := by
  have hinj := Point.map_injective (W' := W) (Algebra.ofId k L)
  have hq : 1 ≤ Nat.card k ^ i := Nat.one_le_pow _ _ Nat.card_pos
  rw [mem_twistedFrobeniusKernel_iff, map_frobeniusAlgHom_baseChange]
  refine and_congr (exists_congr fun m ↦ and_congr_right' <| and_congr_right' ?_) ?_
  · rw [← map_nsmul, ← map_zero (Point.baseChange (W' := W) k L), hinj.eq_iff]
  · conv_lhs => rw [← Nat.sub_add_cancel hq, add_nsmul, one_nsmul, add_eq_right, ← map_nsmul,
      ← map_zero (Point.baseChange (W' := W) k L), hinj.eq_iff]

/-- For a rational point killed by a positive integer prime to `p`, membership of its base change
in the twisted Frobenius kernel is being killed by `q ^ i - 1`. -/
theorem baseChange_mem_twistedFrobeniusKernel_iff_of_exists {P : (W⁄k).toAffine.Point}
    (hP : ∃ m : ℕ, 0 < m ∧ m.Coprime (ringChar k) ∧ m • P = 0) :
    Point.baseChange (W' := W) k L P ∈ W.twistedFrobeniusKernel L i ↔
      (Nat.card k ^ i - 1) • P = 0 := by
  rw [baseChange_mem_twistedFrobeniusKernel_iff, and_iff_right hP]

/-- For `i ≥ 1`, a rational point lies in the twisted Frobenius kernel after base change exactly
when it is killed by `q ^ i - 1`, which is then automatically prime to `p`. -/
theorem baseChange_mem_twistedFrobeniusKernel_iff_of_one_le
    (hi : 1 ≤ i) (P : (W⁄k).toAffine.Point) :
    Point.baseChange (W' := W) k L P ∈ W.twistedFrobeniusKernel L i ↔
      (Nat.card k ^ i - 1) • P = 0 := by
  rw [baseChange_mem_twistedFrobeniusKernel_iff, and_iff_right_iff_imp]
  intro hP
  refine ⟨Nat.card k ^ i - 1, ?_, ?_, hP⟩
  · have := Nat.one_lt_pow (Nat.one_le_iff_ne_zero.mp hi) (Fintype.one_lt_card (α := k))
    rw [Nat.card_eq_fintype_card]
    omega
  · -- `q ^ i - 1` is `-1` in `k`, so the characteristic does not divide it.
    refine ((CharP.prime_ringChar k).coprime_iff_not_dvd.2 fun h ↦ ?_).symm
    have h0 := (ringChar.spec k _).2 h
    rw [Nat.cast_sub (Nat.one_le_pow _ _ Nat.card_pos), Nat.cast_pow, Nat.card_eq_fintype_card,
      FiniteField.cast_card_eq_zero, zero_pow (Nat.one_le_iff_ne_zero.mp hi), Nat.cast_one,
      zero_sub, neg_eq_zero] at h0
    exact one_ne_zero h0

end Rational

/-- A `k`-algebra map of fields commutes with the `q`-power maps on points. -/
private theorem map_map_frobeniusAlgHom (g : L →ₐ[k] L') (P : (W⁄L).toAffine.Point) :
    Point.map (W' := W) g (Point.map (W' := W) (FiniteField.frobeniusAlgHom k L) P) =
      Point.map (W' := W) (FiniteField.frobeniusAlgHom k L') (Point.map (W' := W) g P) := by
  have h : g.comp (FiniteField.frobeniusAlgHom k L) = (FiniteField.frobeniusAlgHom k L').comp g :=
    AlgHom.ext fun x ↦ by simp
  rw [Point.map_map, Point.map_map, h]

/-- **A `k`-algebra map of fields detects the twisted Frobenius kernel**: a point lies in it
exactly when its image under the induced point map does. -/
@[simp]
theorem map_mem_twistedFrobeniusKernel_iff (g : L →ₐ[k] L') {P : (W⁄L).toAffine.Point} :
    Point.map (W' := W) g P ∈ W.twistedFrobeniusKernel L' i ↔ P ∈ W.twistedFrobeniusKernel L i := by
  have hinj := Point.map_injective (W' := W) g
  simp only [mem_twistedFrobeniusKernel_iff, ← map_map_frobeniusAlgHom, ← map_nsmul,
    ← map_zero (Point.map (W' := W) g), hinj.eq_iff]

/-- The twisted Frobenius kernel over `L` is the preimage of the one over `L'` under the point map
of a `k`-algebra map `L →ₐ[k] L'`. -/
theorem comap_twistedFrobeniusKernel (g : L →ₐ[k] L') :
    (W.twistedFrobeniusKernel L' i).comap (Point.map (W' := W) g) =
      W.twistedFrobeniusKernel L i :=
  AddSubgroup.ext fun _ ↦ map_mem_twistedFrobeniusKernel_iff g

variable (W i) in
/-- **The twisted Frobenius kernels over isomorphic fields are isomorphic**, through the point map
`WeierstrassCurve.Affine.Point.mapEquiv` of a `k`-algebra equivalence. -/
noncomputable def twistedFrobeniusKernelEquiv (e : L ≃ₐ[k] L') :
    W.twistedFrobeniusKernel L i ≃+ W.twistedFrobeniusKernel L' i where
  toFun P := ⟨Point.mapEquiv W e P, by
    rw [Point.mapEquiv_apply, map_mem_twistedFrobeniusKernel_iff]
    exact P.property⟩
  invFun P := ⟨(Point.mapEquiv W e).symm P, by
    rw [← map_mem_twistedFrobeniusKernel_iff e.toAlgHom, ← Point.mapEquiv_apply,
      AddEquiv.apply_symm_apply]
    exact P.property⟩
  left_inv P := Subtype.ext <| (Point.mapEquiv W e).symm_apply_apply P
  right_inv P := Subtype.ext <| (Point.mapEquiv W e).apply_symm_apply P
  map_add' P Q := Subtype.ext <| map_add (Point.mapEquiv W e) (P : (W⁄L).toAffine.Point) Q

/-- The equivalence `twistedFrobeniusKernelEquiv W i e` is the point map along `e`. -/
@[simp]
theorem coe_twistedFrobeniusKernelEquiv_apply (e : L ≃ₐ[k] L')
    (P : W.twistedFrobeniusKernel L i) :
    (twistedFrobeniusKernelEquiv W i e P : (W⁄L').toAffine.Point) =
      Point.map (W' := W) e.toAlgHom P :=
  Point.mapEquiv_apply W e (P : (W⁄L).toAffine.Point)

end WeierstrassCurve

end
