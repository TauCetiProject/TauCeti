/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Teichmuller
public import TauCeti.RingTheory.Huber.Pair
public import TauCeti.RingTheory.Perfectoid.UniformTilt

/-!
# The integral tilt of a complete uniform Tate ring

Let `B` be a complete Hausdorff uniform Tate ring in which `p` is topologically nilpotent, with
tilt `B♭ = uniformTilt p B`, and let `B⁺ ⊆ B°` be a ring of integral elements. The *integral tilt*
`B♭⁺ = lim_{x ↦ x ^ p} B⁺` is the set of elements of `B♭` all of whose coordinates lie in `B⁺`; it
is a subring of `B♭`, and it is the set of `x` with `x⁽⁰⁾ ∈ B⁺`.

The coordinates are additive modulo `p` on `B♭⁺`: `(x + y)⁽ⁱ⁾ - x⁽ⁱ⁾ - y⁽ⁱ⁾ ∈ p • B⁺`
(`TauCeti.Perfectoid.uniformTilt.coeff_add_sub_mem_of_forall_mem`). Consequently, for an ideal
`I` of `B⁺` such that `B⁺` is `I`-adically complete and `B⁺ ⧸ I` has characteristic `p` (for
instance an ideal of definition containing `p`), reducing every coordinate modulo `I` is a ring
isomorphism `B♭⁺ ≃+* lim_{x ↦ x ^ p} B⁺ ⧸ I` onto the perfection of `B⁺ ⧸ I`. Its multiplicative
part is Mathlib's `Perfection.quotientMulEquiv`, whose inverse is built from the Teichmüller map;
the ring structure on the target is the coordinatewise one of Mathlib's `Perfection`. So the ring
structure of the tilt, defined through limits, is identified on `B♭⁺` with an algebraically defined
one; for `I = (p)` the target is Mathlib's `PreTilt B⁺ p = Perfection (ModP B⁺ p) p`.

## Main definitions

* `TauCeti.Perfectoid.uniformTilt.plusSubring h`: the integral tilt `B♭⁺ = lim_{x ↦ x ^ p} B⁺` of a
  ring of integral elements `B⁺` (given by `h : IsRingOfIntegralElements B⁺`), as a subring of the
  tilt.
* `TauCeti.Perfectoid.uniformTilt.plusEquiv h I`: the ring isomorphism
  `B♭⁺ ≃+* Perfection (B⁺ ⧸ I) p`, `x ↦ (x⁽ⁿ⁾ mod I)ₙ`.

## Main results

* `TauCeti.Perfectoid.uniformTilt.mem_plusSubring_iff_coeff_zero`: `x ∈ B♭⁺` iff `x⁽⁰⁾ ∈ B⁺`.
* `TauCeti.Perfectoid.uniformTilt.coeff_plusEquiv`: `plusEquiv` reduces every coordinate modulo `I`.
* `TauCeti.Perfectoid.uniformTilt.coeff_zero_plusEquiv_symm`: the zeroth coordinate of the inverse
  is the Teichmüller map `Perfection (B⁺ ⧸ I) p → B⁺`.

## References

* K. S. Kedlaya, *Nonarchimedean geometry of Witt vectors and the tilting equivalence*, in
  *Perfectoid Spaces: Lectures from the 2017 Arizona Winter School*, Lemma 2.7.1(b).
* P. Scholze, *Étale cohomology of diamonds*, Lemma 3.10 and its proof.
* B. Bhatt, M. Morrow, P. Scholze, *Integral p-adic Hodge theory*, Lemma 3.2(i).
-/

public section

open Filter Pointwise TauCeti.Huber

namespace TauCeti.Perfectoid.uniformTilt

variable {p : ℕ} {B : Type*} [CommRing B] [hp : Fact p.Prime] [UniformSpace B]
  [IsUniformAddGroup B] [IsTopologicalRing B] [IsTateRing B] [CompleteSpace B] [T2Space B]
  [IsUniform B] [hpn : Fact (IsTopologicallyNilpotent (p : B))]

variable {Bplus : Subring B}

variable (p) in
/-- The *integral tilt* `B♭⁺ = lim_{x ↦ x ^ p} B⁺` of a ring of integral elements `B⁺ ⊆ B°`: the
subring of the tilt of elements all of whose coordinates lie in `B⁺`. -/
noncomputable def plusSubring (h : IsRingOfIntegralElements Bplus) :
    Subring (uniformTilt p B) where
  carrier := {x | ∀ n, coeff p B n x ∈ Bplus}
  mul_mem' hx hy n := by
    rw [map_mul]
    exact mul_mem (hx n) (hy n)
  one_mem' n := by
    rw [map_one]
    exact one_mem _
  add_mem' {x y} hx hy n := by
    obtain ⟨z, hz, he⟩ := Set.mem_smul_set.mp <| coeff_add_sub_mem_of_forall_mem
      (Bplus.toAddSubgroup.isClosed_of_isOpen h.isOpen) h.le_powerBoundedSubring hx hy n
    rw [smul_eq_mul] at he
    have hsum : coeff p B n (x + y) = p * z + coeff p B n x + coeff p B n y := by
      linear_combination -he
    rw [hsum]
    exact add_mem (add_mem (mul_mem (natCast_mem _ p) hz) (hx n)) (hy n)
  zero_mem' n := by
    rw [coeff_zero]
    exact zero_mem _
  neg_mem' {x} hx n := by
    -- `-x = (-1) * x`, and the coordinates of `-1` square to `1`, so are integral over `B⁺`
    have h1 : coeff p B n (-1 : uniformTilt p B) ∈ Bplus :=
      h.mem_of_pow_mem two_pos (by rw [← map_pow, neg_one_sq, map_one]; exact one_mem _)
    rw [← neg_one_mul, map_mul]
    exact mul_mem h1 (hx n)

/-- An element lies in the integral tilt iff all of its coordinates lie in `B⁺`. -/
theorem mem_plusSubring_iff {h : IsRingOfIntegralElements Bplus} {x : uniformTilt p B} :
    x ∈ plusSubring p h ↔ ∀ n, coeff p B n x ∈ Bplus := Iff.rfl

/-- An element lies in the integral tilt iff its zeroth coordinate `x⁽⁰⁾` lies in `B⁺`. -/
@[simp]
theorem mem_plusSubring_iff_coeff_zero {h : IsRingOfIntegralElements Bplus}
    {x : uniformTilt p B} : x ∈ plusSubring p h ↔ coeff p B 0 x ∈ Bplus := by
  refine ⟨fun hx ↦ hx 0, fun hx n ↦ h.mem_of_pow_mem (pow_pos hp.out.pos n) ?_⟩
  have hn := coeff_pow_p_pow x 0 n
  rw [zero_add] at hn
  rwa [hn]

/-- The integral tilt is multiplicatively the perfection of the monoid `B⁺`. -/
private noncomputable def plusMulEquiv (h : IsRingOfIntegralElements Bplus) :
    plusSubring p h ≃* Perfection Bplus p where
  toFun x := ⟨fun n ↦ ⟨coeff p B n x, mem_plusSubring_iff.mp x.2 n⟩,
    fun n ↦ Subtype.ext (coeff_pow_p _ n)⟩
  invFun y := ⟨mk (fun n ↦ (y.1 n : B)) fun n ↦ congrArg Subtype.val (y.2 n),
    mem_plusSubring_iff.mpr fun n ↦ by rw [coeff_mk]; exact (y.1 n).2⟩
  left_inv x := Subtype.ext <| ext fun n ↦ by rw [coeff_mk]
  right_inv y := Perfection.extMonoid fun n ↦ Subtype.ext (coeff_mk _ _ n)
  map_mul' x y :=
    Perfection.extMonoid fun n ↦ Subtype.ext (map_mul (coeff p B n) (x : uniformTilt p B) y)

private theorem coeffMonoidHom_plusMulEquiv (h : IsRingOfIntegralElements Bplus)
    (x : plusSubring p h) (n : ℕ) :
    Perfection.coeffMonoidHom Bplus p n (plusMulEquiv h x) =
      ⟨coeff p B n x, mem_plusSubring_iff.mp x.2 n⟩ := rfl

private theorem coeff_plusMulEquiv_symm (h : IsRingOfIntegralElements Bplus)
    (y : Perfection Bplus p) (n : ℕ) :
    coeff p B n ((plusMulEquiv h).symm y : uniformTilt p B) =
      Perfection.coeffMonoidHom Bplus p n y :=
  coeff_mk _ _ n

variable (h : IsRingOfIntegralElements Bplus) (I : Ideal Bplus) [CharP (Bplus ⧸ I) p]
  [IsAdicComplete I Bplus]

/-- **The integral tilt is the perfection of `B⁺ ⧸ I`**: for an ideal `I` of `B⁺` such that `B⁺` is
`I`-adically complete and `B⁺ ⧸ I` has characteristic `p`, reducing every coordinate modulo `I` is
a ring isomorphism `B♭⁺ ≃+* Perfection (B⁺ ⧸ I) p`. -/
noncomputable def plusEquiv : plusSubring p h ≃+* Perfection (Bplus ⧸ I) p :=
  { (plusMulEquiv h).trans (Perfection.quotientMulEquiv p I) with
    map_add' x y := by
      refine Perfection.ext fun n ↦ ?_
      simp only [MulEquiv.toEquiv_eq_coe, Equiv.toFun_as_coe, EquivLike.coe_coe,
        MulEquiv.trans_apply, Perfection.coeff_quotientMulEquiv, map_add]
      rw [← map_add, Ideal.Quotient.eq]
      -- the coordinates of `x + y` and of `x`, `y` differ by an element of `p • B⁺ ⊆ I`
      obtain ⟨z, hz, he⟩ := Set.mem_smul_set.mp <| coeff_add_sub_mem_of_forall_mem
        (Bplus.toAddSubgroup.isClosed_of_isOpen h.isOpen) h.le_powerBoundedSubring
        (mem_plusSubring_iff.mp x.2) (mem_plusSubring_iff.mp y.2) n
      rw [smul_eq_mul] at he
      have he' : Perfection.coeffMonoidHom Bplus p n (plusMulEquiv h (x + y)) -
          (Perfection.coeffMonoidHom Bplus p n (plusMulEquiv h x) +
            Perfection.coeffMonoidHom Bplus p n (plusMulEquiv h y)) = (p : Bplus) * ⟨z, hz⟩ :=
        Subtype.ext <| by
          push_cast [coeffMonoidHom_plusMulEquiv]
          linear_combination -he
      rw [he']
      exact I.mul_mem_right _ (I.natCast_mem_of_charP_quotient p) }

private theorem plusEquiv_symm_apply (y : Perfection (Bplus ⧸ I) p) :
    (plusEquiv h I).symm y = (plusMulEquiv h).symm ((Perfection.quotientMulEquiv p I).symm y) :=
  rfl

/-- `plusEquiv` reduces every coordinate modulo `I`. -/
@[simp]
theorem coeff_plusEquiv (x : plusSubring p h) (n : ℕ) :
    Perfection.coeff (Bplus ⧸ I) p n (plusEquiv h I x) =
      Ideal.Quotient.mk I ⟨coeff p B n x, mem_plusSubring_iff.mp x.2 n⟩ := by
  simp [plusEquiv, coeffMonoidHom_plusMulEquiv]

/-- The zeroth coordinate of the inverse of `plusEquiv` is the Teichmüller map
`Perfection (B⁺ ⧸ I) p → B⁺`. -/
@[simp]
theorem coeff_zero_plusEquiv_symm (y : Perfection (Bplus ⧸ I) p) :
    coeff p B 0 ((plusEquiv h I).symm y : uniformTilt p B) = Perfection.teichmuller₀ p I y := by
  rw [plusEquiv_symm_apply, coeff_plusMulEquiv_symm,
    Perfection.coeff_zero_symm_quotientMulEquiv]

end TauCeti.Perfectoid.uniformTilt
