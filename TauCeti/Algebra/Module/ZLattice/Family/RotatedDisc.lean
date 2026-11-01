/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.ZLattice.Family.Stabilizer
public import TauCeti.Analysis.Complex.RootsOfUnity.Quotient

/-!
# Cyclic affine actions on families of tori over a rotated disc

Let `D = TauCeti.rootsOfUnityBall m r` be the open disc of radius `r` about `0` in `ℂ`, on which
the group `C_m = rootsOfUnity m ℂ` of `m`-th roots of unity acts by the rotations `z ↦ ζ z`. Let
`P : D → (Λ →ₗ[ℤ] E)` be a period family over the disc, and let `C_m` act on the family of tori
`X = (D × E)/Λ → D` by an affine cocycle, `ζ • [z, v] = R ζ z v +ᵥ b ζ z`
(`TauCeti.torusFamilyAffineMulAction`), lifting the rotations. This is the setting of the local
construction of multiple fibres, in which the quotient `X / C_m` lies over the quotient of the
disc by the rotations, itself a disc with coordinate `t = z ^ m`
(`TauCeti.rootsOfUnityBallQuotientHomeomorph`). Forming `X / C_m` as a manifold requires the
action on `X` to be free, which is what this file characterizes.

Away from the centre the rotations act freely on the disc
(`TauCeti.stabilizer_rootsOfUnityBall_of_coe_ne_zero`), while the centre `u₀` is fixed by every
rotation. So the affine action on the total space `X` is free exactly when the generator acts
without fixed points on the central torus `T₀ = E / LinearMap.range (P u₀)` in every nonidentity
power: if a primitive `m`-th root of unity `ζ` acts on `T₀` by `x ↦ A x + t`, the condition is
that for every `0 < k < m` the partial norm `N_{A,k}(t) = ∑ i < k, A^i t` does not lie in the
image of `1 - A^k` (`TauCeti.isCancelSMul_torusFamilyAffineMulAction_rootsOfUnityBall_iff`). For
composite `m` every such `k` must be checked. The total action also has exact order `m`: a
primitive `m`-th root of unity acts on `X` by a permutation of order exactly `m`
(`TauCeti.orderOf_toPerm_torusFamilyAffineMulAction_rootsOfUnityBall`), because the rotations act
faithfully on a disc of positive radius and the affine action lifts them.

The fixed-point condition concerns only the action on the central fibre, so it is the cyclic
fixed-point criterion for the affine automorphism `x ↦ A x + t` of the additive group `T₀`
(`AddEquiv.exists_affineEquiv_iterate_apply_eq_self_iff`).

## Main results

* `TauCeti.isCancelSMul_torusFamilyAffineMulAction_rootsOfUnityBall_iff`: the affine action on the
  total space is free exactly when no nonidentity power of a primitive root of unity has a fixed
  point on the central torus.
* `TauCeti.orderOf_toPerm_torusFamilyAffineMulAction_rootsOfUnityBall`: a primitive `m`-th root of
  unity acts on the total space with exact order `m`.

## References

* W. P. Barth, K. Hulek, C. A. M. Peters, A. Van de Ven, *Compact Complex Surfaces*, second
  edition, Springer (2004), Chapter V, section *Logarithmic transformations*, for the cyclic
  quotients of families of tori over a disc.
-/

public section

open MulAction

namespace TauCeti

variable {m : ℕ} [NeZero m] {r : ℝ}

variable {Λ E : Type*} [AddCommGroup Λ] [AddCommGroup E]
  (R : rootsOfUnity m ℂ → rootsOfUnityBall m r → E →+ E)
  (hone : ∀ (z : rootsOfUnityBall m r) (v : E), R 1 z v = v)
  (hmul : ∀ (g h : rootsOfUnity m ℂ) (z : rootsOfUnityBall m r) (v : E),
    R (g * h) z v = R g (h • z) (R h z v))
  (P : rootsOfUnityBall m r → Λ →ₗ[ℤ] E) (ρ : Representation ℤ (rootsOfUnity m ℂ) Λ)
  (hP : ∀ (g : rootsOfUnity m ℂ) (z : rootsOfUnityBall m r) (l : Λ),
    P (g • z) (ρ g l) = R g z (P z l))
  (b : rootsOfUnity m ℂ → rootsOfUnityBall m r →
    letI := periodAddAction P; AddAction.orbitRel.Quotient Λ (rootsOfUnityBall m r × E))
  (hb : ∀ (g : rootsOfUnity m ℂ) (z : rootsOfUnityBall m r),
    torusFamilyProjection P (b g z) = g • z)
  (hbone : ∀ z : rootsOfUnityBall m r, b 1 z = Quotient.mk _ (z, 0))
  (hbmul : ∀ (g h : rootsOfUnity m ℂ) (z : rootsOfUnityBall m r),
    b (g * h) z = torusFamilyAffineMap R P ρ hP b hb g (b h z))

/-- **Freeness of a cyclic affine action over the rotated disc.** Let `ζ` be a primitive `m`-th
root of unity and `u₀` the centre of the disc. The affine action of the rotations on the total
space of the family of tori is free exactly when, for every `0 < k < m`, the `k`-th partial norm
`N_{A,k}(t)` of the translation part `t` of `ζ` on the central torus does not lie in the image of
`1 - A^k`, where `A` is the linear part of `ζ` there. -/
theorem isCancelSMul_torusFamilyAffineMulAction_rootsOfUnityBall_iff
    {u₀ : rootsOfUnityBall m r} (hu₀ : (u₀ : ℂ) = 0) {ζ : rootsOfUnity m ℂ}
    (hζ : IsPrimitiveRoot ζ m) :
    letI := periodAddAction P
    letI := torusFamilyAffineMulAction R hone hmul P ρ hP b hb hbone hbmul
    IsCancelSMul (rootsOfUnity m ℂ) (AddAction.orbitRel.Quotient Λ (rootsOfUnityBall m r × E)) ↔
      ∀ k : ℕ, 0 < k → k < m →
        ∀ c, c - (⇑(torusFamilyFiberLinearPart R hone hmul P ρ hP
          (smul_rootsOfUnityBall_of_coe_eq_zero hu₀ ζ)))^[k] c ≠
          AddEquiv.partialNorm (torusFamilyFiberLinearPart R hone hmul P ρ hP
            (smul_rootsOfUnityBall_of_coe_eq_zero hu₀ ζ)) k
            (torusFamilyFiberTranslationPart P b hb
              (smul_rootsOfUnityBall_of_coe_eq_zero hu₀ ζ)) := by
  -- `ζ` generates the group of `m`-th roots of unity, which has `m` elements.
  have hgen : Subgroup.zpowers ζ = ⊤ := Subgroup.eq_top_of_card_eq _ <| by
    rw [Nat.card_zpowers, ← hζ.eq_orderOf, Complex.card_rootsOfUnity]
  have h := isCancelSMul_torusFamilyAffineMulAction_iff_of_stabilizer_eq_bot R hone hmul P ρ hP b
    hb hbone hbmul (smul_rootsOfUnityBall_of_coe_eq_zero hu₀ ζ) (hgen ▸ le_top)
    (isOfFinOrder_of_finite ζ) fun u hu ↦
      stabilizer_rootsOfUnityBall_of_coe_ne_zero fun h ↦ hu (Subtype.ext (h.trans hu₀.symm))
  rwa [← hζ.eq_orderOf] at h

/-- **Exact order of a cyclic affine action over the rotated disc.** Over a disc of positive
radius, a primitive `m`-th root of unity acts on the total space of the family of tori by a
permutation of exact order `m`: the affine action lifts the rotations, which act faithfully. -/
theorem orderOf_toPerm_torusFamilyAffineMulAction_rootsOfUnityBall (hr : 0 < r)
    {ζ : rootsOfUnity m ℂ} (hζ : IsPrimitiveRoot ζ m) :
    letI := periodAddAction P
    letI := torusFamilyAffineMulAction R hone hmul P ρ hP b hb hbone hbmul
    orderOf (toPerm ζ : Equiv.Perm
      (AddAction.orbitRel.Quotient Λ (rootsOfUnityBall m r × E))) = m := by
  let _ := periodAddAction P
  let _ := torusFamilyAffineMulAction R hone hmul P ρ hP b hb hbone hbmul
  have := faithfulSMul_rootsOfUnityBall (m := m) hr
  have := faithfulSMul_torusFamilyAffineMulAction R hone hmul P ρ hP b hb hbone hbmul
  exact (orderOf_injective (toPermHom _ _) toPerm_injective ζ).trans hζ.eq_orderOf.symm

end TauCeti
