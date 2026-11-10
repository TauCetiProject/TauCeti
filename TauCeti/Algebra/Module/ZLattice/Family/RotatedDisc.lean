/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Analytic.Order
public import TauCeti.Algebra.Module.Torsion.Snake
public import TauCeti.Algebra.Module.ZLattice.Family.AffineQuotient
public import TauCeti.Algebra.Module.ZLattice.Family.Stabilizer
public import TauCeti.Analysis.Complex.RootsOfUnity.Manifold

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

When the linear part of `ζ` at the centre is the identity, `ζ` acts on `T₀` by the translation by
an `m`-torsion point `t`, and the action is free exactly when `t` has exact order `m`
(`TauCeti.isCancelSMul_torusFamilyAffineMulAction_rootsOfUnityBall_iff_addOrderOf_eq`). Write
`t = [β]` with `m • β = P u₀ l` for a lattice vector `l : Λ`. The class of `l` in `Λ ⧸ mΛ` is the
image of `t` under the connecting map `T₀[m] → Λ ⧸ mΛ` of `0 → Λ → E → T₀ → 0`
(`LinearMap.orbitRelQuotientTorsionByδ`), so it does not depend on `β`. When multiplication by `m`
is injective on `E`, freeness means that this class has exact order `m`
(`TauCeti.isCancelSMul_torusFamilyAffineMulAction_rootsOfUnityBall_iff_addOrderOf_mk_eq`). For the
trivial action of the cyclic group of order `m`, `T₀[m]` is its first cohomology with coefficients
in `T₀` and `Λ ⧸ mΛ` its second cohomology with coefficients in `Λ`
(`TauCeti.groupCohomologyOddEquivTorsionBy`, `TauCeti.groupCohomologyEvenEquivQuotSMulTop`), and
the connecting map is the connecting homomorphism of group cohomology
(`TauCeti.groupCohomologyEvenEquivQuotSMulTop_δ`).

When the action on `X` is free, the orbit space `X / C_m` is a complex manifold
(`TauCeti.isManifold_torusFamilyAffineQuotient`), and `z ↦ z ^ m` induces the map
`p_Q : X / C_m → ℂ` (`TauCeti.torusFamilyAffineQuotientLift`), the projection of the cyclic
quotient onto the quotient disc, of radius `r ^ m` when `D` has radius `r`. It is a holomorphic
submersion off its fibre over `0`, which is the image of the central torus. This is the local
construction of multiple fibres in the reference below.

The charts of the quotient atlas of `X / C_m` are local sections of the orbit map followed by
charts of `X`, whose first coordinate is the coordinate `z` of the disc. So in every chart the map
`p_Q` is `(u, v) ↦ u ^ m`, with no unit factor
(`TauCeti.torusFamilyAffineQuotientLift_rootsOfUnityBall_eq_pow`). Its fibre over `0`, the
central fibre, is therefore cut out in each chart by the first coordinate: it is an embedded
hypersurface of `X / C_m`, with the charts of the quotient atlas as slice charts. Along the
first coordinate line of such a chart, transverse to it, `p_Q` vanishes to order exactly `m`: the
central fibre has multiplicity `m`.
With holomorphic data these charts are holomorphic charts of the complex manifold `X / C_m`.

## Main results

* `TauCeti.isCancelSMul_torusFamilyAffineMulAction_rootsOfUnityBall_iff`: the affine action on the
  total space is free exactly when no nonidentity power of a primitive root of unity has a fixed
  point on the central torus.
* `TauCeti.isCancelSMul_torusFamilyAffineMulAction_rootsOfUnityBall_iff_addOrderOf_eq`: when the
  linear part at the centre is the identity, the action is free exactly when its translation part
  on the central torus has exact order `m`.
* `TauCeti.isCancelSMul_torusFamilyAffineMulAction_rootsOfUnityBall_iff_addOrderOf_mk_eq`: the
  same criterion read on a lattice vector `l` with `m • β = P u₀ l` for a representative `β` of the
  translation part: the class of `l` in `Λ ⧸ mΛ` has exact order `m`.
* `TauCeti.orderOf_toPerm_torusFamilyAffineMulAction_rootsOfUnityBall`: a primitive `m`-th root of
  unity acts on the total space with exact order `m`.
* `TauCeti.isSubmersionAtOfComplement_torusFamilyAffineQuotientLift_rootsOfUnityBall`: over the
  rotated disc, the map `X / C_m → ℂ` induced by `z ↦ z ^ m` is a holomorphic submersion off its
  fibre over `0`.
* `TauCeti.range_torusFamilyAffineQuotientLift_rootsOfUnityBall`,
  `TauCeti.preimage_torusFamilyAffineQuotientLift_rootsOfUnityBall_zero`: its image is the disc of
  radius `r ^ m`, and its fibre over `0` is the image of the central torus.
* `TauCeti.torusFamilyAffineQuotientLift_rootsOfUnityBall_eq_pow`,
  `TauCeti.torusFamilyAffineQuotientLift_rootsOfUnityBall_symm_eq_pow`: in every chart of the
  quotient atlas, this map is `(u, v) ↦ u ^ m`.
* `TauCeti.image_source_inter_preimage_torusFamilyAffineQuotientLift_rootsOfUnityBall_zero`: in
  every chart of the quotient atlas, its fibre over `0` is the slice where the first coordinate
  vanishes.
* `TauCeti.analyticOrderAt_torusFamilyAffineQuotientLift_rootsOfUnityBall`: along a transverse
  line through a point of the central fibre, it vanishes to order exactly `m`.

## References

* W. P. Barth, K. Hulek, C. A. M. Peters, A. Van de Ven, *Compact Complex Surfaces*, second
  edition, Springer (2004), Chapter V, section *Logarithmic transformations*, for the cyclic
  quotients of families of tori over a disc.
-/

public section

open Manifold MulAction
open scoped Manifold ContDiff

namespace TauCeti

section Freeness

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
  have h := isCancelSMul_torusFamilyAffineMulAction_iff_of_stabilizer_le_zpowers_of_eq_bot_of_ne
    R hone hmul P ρ hP b hb hbone hbmul (smul_rootsOfUnityBall_of_coe_eq_zero hu₀ ζ) (hgen ▸ le_top)
    (isOfFinOrder_of_finite ζ) fun u hu ↦
      stabilizer_rootsOfUnityBall_of_coe_ne_zero fun h ↦ hu (Subtype.ext (h.trans hu₀.symm))
  rwa [← hζ.eq_orderOf] at h

/-- **Freeness of a translation over the rotated disc.** Let `ζ` be a primitive `m`-th root of
unity whose linear part `R ζ u₀` at the centre `u₀` of the disc is the identity, so that `ζ` acts on
the central torus `T₀` by the translation by a point `t`. The affine action of the rotations on the
total space is free exactly when `t` has exact additive order `m`. That `t` is `m`-torsion holds
for every such action (`TauCeti.nsmul_torusFamilyFiberTranslationPart_eq_zero`); freeness excludes
each smaller order. -/
theorem isCancelSMul_torusFamilyAffineMulAction_rootsOfUnityBall_iff_addOrderOf_eq
    {u₀ : rootsOfUnityBall m r} (hu₀ : (u₀ : ℂ) = 0) {ζ : rootsOfUnity m ℂ}
    (hζ : IsPrimitiveRoot ζ m) (hR : ∀ v, R ζ u₀ v = v) :
    letI := periodAddAction P
    letI := torusFamilyAffineMulAction R hone hmul P ρ hP b hb hbone hbmul
    IsCancelSMul (rootsOfUnity m ℂ) (AddAction.orbitRel.Quotient Λ (rootsOfUnityBall m r × E)) ↔
      addOrderOf (torusFamilyFiberTranslationPart P b hb
        (smul_rootsOfUnityBall_of_coe_eq_zero hu₀ ζ)) = m := by
  rw [isCancelSMul_torusFamilyAffineMulAction_rootsOfUnityBall_iff R hone hmul P ρ hP b hb hbone
      hbmul hu₀ hζ, torusFamilyFiberLinearPart_eq_refl R hone hmul P ρ hP _ hR,
    addOrderOf_eq_iff (NeZero.pos m)]
  simp only [AddEquiv.coe_refl, Function.iterate_id, id, sub_self, AddEquiv.partialNorm_refl]
  -- The torsion condition `m • t = 0` always holds; the conditions on smaller orders agree.
  exact ⟨fun h ↦ ⟨nsmul_torusFamilyFiberTranslationPart_eq_zero R P ρ hP b hb hbone hbmul
    _ hR hζ.pow_eq_one, fun k hk hk₀ ↦ (h k hk₀ hk 0).symm⟩, fun h k hk₀ hk _ ↦ (h.2 k hk hk₀).symm⟩

/-- **Freeness of a translation over the rotated disc, through its lattice class.** Let `ζ` be a
primitive `m`-th root of unity whose linear part `R ζ u₀` at the centre `u₀` of the disc is the
identity, and let `P u₀` be injective. Write the value of the translation section at the centre as
`b ζ u₀ = [u₀, β]` and let `m • β = P u₀ l`; for instance, if `β` is the value at `u₀` of a lift
`β'` of `b ζ`, the orbit sum `∑ j < m, β' (ζ ^ j • u₀)` is `m • β` because the centre is fixed
(`Function.IsFixedPt.birkhoffSum_eq`). If multiplication by `m` is injective on `E`, as for a real
vector space, then the affine action on the total space is free exactly when the class of `l` in
`Λ ⧸ mΛ` has exact additive order `m`. That class does not depend on the choice of `β`
(`LinearMap.quotSMulTop_mk_eq_mk_of_smul_eq`): it is the image of the translation part on the
central torus under the connecting map `LinearMap.orbitRelQuotientTorsionByδ`. -/
theorem isCancelSMul_torusFamilyAffineMulAction_rootsOfUnityBall_iff_addOrderOf_mk_eq
    {u₀ : rootsOfUnityBall m r} (hu₀ : (u₀ : ℂ) = 0) {ζ : rootsOfUnity m ℂ}
    (hζ : IsPrimitiveRoot ζ m) (hR : ∀ v, R ζ u₀ v = v) (hinj : Function.Injective (P u₀))
    (hmE : Function.Injective fun v : E ↦ m • v) {β : E}
    (hβ : b ζ u₀ = Quotient.mk _ (u₀, β)) {l : Λ} (hl : P u₀ l = m • β) :
    letI := periodAddAction P
    letI := torusFamilyAffineMulAction R hone hmul P ρ hP b hb hbone hbmul
    IsCancelSMul (rootsOfUnity m ℂ) (AddAction.orbitRel.Quotient Λ (rootsOfUnityBall m r × E)) ↔
      addOrderOf (Submodule.Quotient.mk l : QuotSMulTop (m : ℤ) Λ) = m := by
  have hy := smul_rootsOfUnityBall_of_coe_eq_zero hu₀ ζ
  -- The translation part `t = [β]` on the central torus is `m`-torsion.
  have ht : (m : ℤ) • torusFamilyFiberTranslationPart P b hb hy = 0 := by
    rw [natCast_zsmul]
    exact nsmul_torusFamilyFiberTranslationPart_eq_zero R P ρ hP b hb hbone hbmul hy hR
      hζ.pow_eq_one
  let x : Submodule.torsionBy ℤ (AddAction.orbitRel.Quotient (LinearMap.range (P u₀)) E) m :=
    ⟨_, (Submodule.mem_torsionBy_iff _ _).2 ht⟩
  -- The connecting map sends `t` to the class of `l`, and it preserves additive orders.
  have hδ := (P u₀).orbitRelQuotientTorsionByδ_eq hinj m x
    (torusFamilyFiberTranslationPart_eq_mk P b hb hy hβ) (by rw [hl, natCast_zsmul])
  have hδx : addOrderOf ((P u₀).orbitRelQuotientTorsionByδ hinj m x) = addOrderOf x :=
    addOrderOf_injective ((P u₀).orbitRelQuotientTorsionByδ hinj m).toAddMonoidHom
      ((P u₀).injective_orbitRelQuotientTorsionByδ hinj m (by simpa only [natCast_zsmul] using hmE))
      x
  have hx : addOrderOf (torusFamilyFiberTranslationPart P b hb hy) = addOrderOf x :=
    addOrderOf_injective (Submodule.subtype _).toAddMonoidHom Subtype.val_injective x
  rw [isCancelSMul_torusFamilyAffineMulAction_rootsOfUnityBall_iff_addOrderOf_eq R hone hmul P ρ hP
      b hb hbone hbmul hu₀ hζ hR, ← hδ, hδx, hx]

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

end Freeness

section RotatedDiscLift

variable {m : ℕ} [NeZero m] {r : ℝ} {Λ : Type*} [AddCommGroup Λ] {E : Type*} [AddCommGroup E]
  (P : rootsOfUnityBall m r → Λ →ₗ[ℤ] E) (R : rootsOfUnity m ℂ → rootsOfUnityBall m r → E →+ E)
  (ρ : Representation ℤ (rootsOfUnity m ℂ) Λ)
  (hequiv : ∀ (g : rootsOfUnity m ℂ) (z : rootsOfUnityBall m r) (l : Λ),
    P (g • z) (ρ g l) = R g z (P z l))
  (b : rootsOfUnity m ℂ → rootsOfUnityBall m r →
    letI := periodAddAction P; AddAction.orbitRel.Quotient Λ (rootsOfUnityBall m r × E))
  (hb : ∀ (g : rootsOfUnity m ℂ) (z : rootsOfUnityBall m r),
    torusFamilyProjection P (b g z) = g • z)
  (hone : ∀ (z : rootsOfUnityBall m r) (v : E), R 1 z v = v)
  (hmul : ∀ (g h : rootsOfUnity m ℂ) (z : rootsOfUnityBall m r) (v : E),
    R (g * h) z v = R g (h • z) (R h z v))
  (hbone : ∀ z : rootsOfUnityBall m r, b 1 z = Quotient.mk _ (z, 0))
  (hbmul : ∀ (g h : rootsOfUnity m ℂ) (z : rootsOfUnityBall m r),
    b (g * h) z = torusFamilyAffineMap R P ρ hequiv b hb g (b h z))

/-- **The cyclic quotient lies over the quotient disc.** For a family of tori `X → D` over the
disc `D` of radius `r ≥ 0` and an affine action of the `m`-th roots of unity lifting the
rotations, the map `p_Q : X / C_m → ℂ` induced by `z ↦ z ^ m` has image the disc of radius
`r ^ m`, the quotient of `D` by the rotations (`TauCeti.rootsOfUnityBallQuotientHomeomorph`). -/
theorem range_torusFamilyAffineQuotientLift_rootsOfUnityBall (hr : 0 ≤ r) :
    letI := periodAddAction P
    letI := torusFamilyAffineMulAction R hone hmul P ρ hequiv b hb hbone hbmul
    Set.range (torusFamilyAffineQuotientLift P R ρ hequiv b hb hone hmul hbone hbmul
      (fun z : rootsOfUnityBall m r ↦ (z : ℂ) ^ m) fun g z ↦ coe_smul_rootsOfUnityBall_pow g z) =
      Metric.ball 0 (r ^ m) := by
  let _ := periodAddAction P
  let _ := torusFamilyAffineMulAction R hone hmul P ρ hequiv b hb hbone hbmul
  rw [← image_pow_ball hr]
  ext t
  constructor
  · rintro ⟨y, rfl⟩
    induction y using Quotient.inductionOn with | h x =>
    induction x using Quotient.inductionOn with | h p =>
    rw [torusFamilyAffineQuotientLift_mk, torusFamilyProjection_mk]
    exact ⟨p.1, mem_ball_zero_iff.2 (mem_rootsOfUnityBall.1 p.1.2), rfl⟩
  · rintro ⟨u, hu, rfl⟩
    refine ⟨Quotient.mk _ (Quotient.mk _
      (⟨u, mem_rootsOfUnityBall.2 (mem_ball_zero_iff.1 hu)⟩, 0)), ?_⟩
    rw [torusFamilyAffineQuotientLift_mk, torusFamilyProjection_mk]

/-- **The central fibre of the cyclic quotient.** For a family of tori `X → D` over the disc and
an affine action of the `m`-th roots of unity lifting the rotations, the fibre over `0` of the map
`p_Q : X / C_m → ℂ` induced by `z ↦ z ^ m` is the image in `X / C_m` of the fibre of `X` over the
centre `u₀` of the disc, the central torus `T₀ = E / LinearMap.range (P u₀)`. -/
theorem preimage_torusFamilyAffineQuotientLift_rootsOfUnityBall_zero {u₀ : rootsOfUnityBall m r}
    (hu₀ : (u₀ : ℂ) = 0) :
    letI := periodAddAction P
    letI := torusFamilyAffineMulAction R hone hmul P ρ hequiv b hb hbone hbmul
    torusFamilyAffineQuotientLift P R ρ hequiv b hb hone hmul hbone hbmul
      (fun z : rootsOfUnityBall m r ↦ (z : ℂ) ^ m) (fun g z ↦ coe_smul_rootsOfUnityBall_pow g z) ⁻¹'
        {0} = Set.range fun v : E ↦ Quotient.mk _ (Quotient.mk _ (u₀, v)) := by
  let _ := periodAddAction P
  let _ := torusFamilyAffineMulAction R hone hmul P ρ hequiv b hb hbone hbmul
  ext y
  induction y using Quotient.inductionOn with | h x =>
  induction x using Quotient.inductionOn with | h p =>
  rw [Set.mem_preimage, torusFamilyAffineQuotientLift_mk, torusFamilyProjection_mk,
    Set.mem_singleton_iff, pow_eq_zero_iff (NeZero.ne m)]
  constructor
  · intro hp
    exact ⟨p.2, by rw [show u₀ = p.1 from Subtype.ext (hu₀.trans hp.symm)]⟩
  · rintro ⟨v, hv⟩
    -- The map induced by `z ↦ z ^ m` takes the same value on both classes, `0` on the class of
    -- a point over the centre.
    have h := congrArg (torusFamilyAffineQuotientLift P R ρ hequiv b hb hone hmul hbone hbmul
      (fun z : rootsOfUnityBall m r ↦ (z : ℂ) ^ m) fun g z ↦ coe_smul_rootsOfUnityBall_pow g z) hv
    simp only [torusFamilyAffineQuotientLift_mk, torusFamilyProjection_mk, hu₀,
      zero_pow (NeZero.ne m)] at h
    exact (pow_eq_zero_iff (NeZero.ne m)).1 h.symm

end RotatedDiscLift

section Charts

variable {m : ℕ} [NeZero m] {r : ℝ}
  {Λ : Type*} [AddCommGroup Λ] [Module.Free ℤ Λ] [Module.Finite ℤ Λ]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  (P : rootsOfUnityBall m r → Λ →ₗ[ℤ] E) [∀ z, DiscreteTopology (LinearMap.range (P z))]
  [∀ z, IsZLattice ℝ (LinearMap.range (P z))]
  (hcont : ∀ l, Continuous fun z ↦ P z l) (hinj : ∀ z, Function.Injective (P z))
  (R : rootsOfUnity m ℂ → rootsOfUnityBall m r → E →+ E)
  (ρ : Representation ℤ (rootsOfUnity m ℂ) Λ)
  (hequiv : ∀ (g : rootsOfUnity m ℂ) (z : rootsOfUnityBall m r) (l : Λ),
    P (g • z) (ρ g l) = R g z (P z l))
  (b : rootsOfUnity m ℂ → rootsOfUnityBall m r →
    letI := periodAddAction P; AddAction.orbitRel.Quotient Λ (rootsOfUnityBall m r × E))
  (hb : ∀ (g : rootsOfUnity m ℂ) (z : rootsOfUnityBall m r),
    torusFamilyProjection P (b g z) = g • z)
  (hone : ∀ (z : rootsOfUnityBall m r) (v : E), R 1 z v = v)
  (hmul : ∀ (g h : rootsOfUnity m ℂ) (z : rootsOfUnityBall m r) (v : E),
    R (g * h) z v = R g (h • z) (R h z v))
  (hbone : ∀ z : rootsOfUnityBall m r, b 1 z = Quotient.mk _ (z, 0))
  (hbmul : ∀ (g h : rootsOfUnity m ℂ) (z : rootsOfUnityBall m r),
    b (g * h) z = torusFamilyAffineMap R P ρ hequiv b hb g (b h z))
  (hRc : ∀ g : rootsOfUnity m ℂ, Continuous fun p : rootsOfUnityBall m r × E ↦ R g p.1 p.2)
  (hbc : letI := periodAddAction P; ∀ g, Continuous (b g))
  (hfree : letI := periodAddAction P
    letI := torusFamilyAffineMulAction R hone hmul P ρ hequiv b hb hbone hbmul
    IsCancelSMul (rootsOfUnity m ℂ) (AddAction.orbitRel.Quotient Λ (rootsOfUnityBall m r × E)))
  {e : letI := periodAddAction P
    letI := torusFamilyAffineMulAction R hone hmul P ρ hequiv b hb hbone hbmul
    OpenPartialHomeomorph (MulAction.orbitRel.Quotient (rootsOfUnity m ℂ)
      (AddAction.orbitRel.Quotient Λ (rootsOfUnityBall m r × E))) (ModelProd ℂ E)}
  (he : letI := periodAddAction P
    letI := torusFamilyAffineMulAction R hone hmul P ρ hequiv b hb hbone hbmul
    letI := torusFamilyAffineQuotientChartedSpace (H := ℂ) P hinj R ρ hequiv b hb hone hmul
      hbone hbmul hcont hRc hbc hfree
    e ∈ atlas (ModelProd ℂ E) (MulAction.orbitRel.Quotient (rootsOfUnity m ℂ)
      (AddAction.orbitRel.Quotient Λ (rootsOfUnityBall m r × E))))

include he

/-- **The local equation of the cyclic quotient.** Let the `m`-th roots of unity act freely on a
family of tori `X → D` over the disc by an affine action lifting the rotations. In every chart
`e` of the quotient atlas of `Q = X / C_m`, the map `p_Q : Q → ℂ` induced by `z ↦ z ^ m` is
`(u, v) ↦ u ^ m`. -/
theorem torusFamilyAffineQuotientLift_rootsOfUnityBall_symm_eq_pow {w : ModelProd ℂ E}
    (hw : w ∈ e.target) :
    torusFamilyAffineQuotientLift P R ρ hequiv b hb hone hmul hbone hbmul
      (fun z : rootsOfUnityBall m r ↦ (z : ℂ) ^ m) (fun g z ↦ coe_smul_rootsOfUnityBall_pow g z)
      (e.symm w) = w.1 ^ m := by
  obtain ⟨z, hz⟩ := exists_torusFamilyAffineQuotientLift_symm_eq_of_mem_atlas (H := ℂ) P hcont
    hinj R ρ hequiv b hb hone hmul hbone hbmul (fun z : rootsOfUnityBall m r ↦ (z : ℂ) ^ m)
    (fun g z ↦ coe_smul_rootsOfUnityBall_pow g z) hRc hbc hfree he
  obtain ⟨hwz, hw⟩ := hz w hw
  rw [hw, rootsOfUnityBall.coe_chartAt_symm z hwz]

/-- **The local equation of the cyclic quotient, on its source.** In every chart `e` of the
quotient atlas of `Q = X / C_m`, the map `p_Q : Q → ℂ` induced by `z ↦ z ^ m` is the `m`-th power
of the first coordinate `u` of `e`: `p_Q = u ^ m`. -/
theorem torusFamilyAffineQuotientLift_rootsOfUnityBall_eq_pow
    {x : letI := periodAddAction P
      letI := torusFamilyAffineMulAction R hone hmul P ρ hequiv b hb hbone hbmul
      MulAction.orbitRel.Quotient (rootsOfUnity m ℂ)
        (AddAction.orbitRel.Quotient Λ (rootsOfUnityBall m r × E))}
    (hx : x ∈ e.source) :
    torusFamilyAffineQuotientLift P R ρ hequiv b hb hone hmul hbone hbmul
      (fun z : rootsOfUnityBall m r ↦ (z : ℂ) ^ m) (fun g z ↦ coe_smul_rootsOfUnityBall_pow g z)
      x = (e x).1 ^ m := by
  rw [← torusFamilyAffineQuotientLift_rootsOfUnityBall_symm_eq_pow P hcont hinj R ρ hequiv b hb
    hone hmul hbone hbmul hRc hbc hfree he (e.map_source hx), e.left_inv hx]

/-- **The central fibre in a chart of the cyclic quotient.** In every chart `e` of the quotient
atlas of `Q = X / C_m`, the fibre over `0` of the map `p_Q : Q → ℂ` induced by `z ↦ z ^ m`, which
is the image of the central torus
(`TauCeti.preimage_torusFamilyAffineQuotientLift_rootsOfUnityBall_zero`), is the slice of the
target of `e` on which the first coordinate vanishes. So it is an embedded hypersurface of `Q`,
cut out in each chart by the first coordinate. -/
theorem image_source_inter_preimage_torusFamilyAffineQuotientLift_rootsOfUnityBall_zero :
    e '' (e.source ∩ torusFamilyAffineQuotientLift P R ρ hequiv b hb hone hmul hbone hbmul
      (fun z : rootsOfUnityBall m r ↦ (z : ℂ) ^ m)
      (fun g z ↦ coe_smul_rootsOfUnityBall_pow g z) ⁻¹' {0}) =
      e.target ∩ {w | w.1 = 0} := by
  rw [e.image_source_inter_eq']
  ext w
  refine and_congr_right fun hw ↦ ?_
  simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_ofPred_eq]
  rw [torusFamilyAffineQuotientLift_rootsOfUnityBall_symm_eq_pow P hcont hinj R ρ hequiv b hb hone
      hmul hbone hbmul hRc hbc hfree he hw, pow_eq_zero_iff (NeZero.ne m)]

/-- **The central fibre has multiplicity `m`.** Let `x` be a point of the central fibre of the
cyclic quotient `Q = X / C_m`, the fibre over `0` of the map `p_Q : Q → ℂ` induced by
`z ↦ z ^ m`, and let `e` be a chart of the quotient atlas at `x`. Along the transverse line
`u ↦ e.symm (u, v₀)` through `x`, where `v₀` is the fibre coordinate of `x`, the function `p_Q`
vanishes at `u = 0` to order exactly `m`. -/
theorem analyticOrderAt_torusFamilyAffineQuotientLift_rootsOfUnityBall
    {x : letI := periodAddAction P
      letI := torusFamilyAffineMulAction R hone hmul P ρ hequiv b hb hbone hbmul
      MulAction.orbitRel.Quotient (rootsOfUnity m ℂ)
        (AddAction.orbitRel.Quotient Λ (rootsOfUnityBall m r × E))}
    (hx : x ∈ e.source)
    (hx0 : torusFamilyAffineQuotientLift P R ρ hequiv b hb hone hmul hbone hbmul
      (fun z : rootsOfUnityBall m r ↦ (z : ℂ) ^ m) (fun g z ↦ coe_smul_rootsOfUnityBall_pow g z)
      x = 0) :
    analyticOrderAt (fun u : ℂ ↦ torusFamilyAffineQuotientLift P R ρ hequiv b hb hone hmul hbone
      hbmul (fun z : rootsOfUnityBall m r ↦ (z : ℂ) ^ m)
      (fun g z ↦ coe_smul_rootsOfUnityBall_pow g z) (e.symm ((u, (e x).2) : ℂ × E))) 0 = m := by
  rw [torusFamilyAffineQuotientLift_rootsOfUnityBall_eq_pow P hcont hinj R ρ hequiv b hb hone hmul
    hbone hbmul hRc hbc hfree he hx, pow_eq_zero_iff (NeZero.ne m)] at hx0
  -- The transverse line stays in the target of `e` near `u = 0`, where `p_Q` reads as `u ^ m`.
  have hmem : {u : ℂ | ((u, (e x).2) : ℂ × E) ∈ e.target} ∈ nhds (0 : ℂ) := by
    refine (e.open_target.preimage (Continuous.prodMk_left (e x).2)).mem_nhds ?_
    rw [Set.mem_ofPred_eq, ← hx0]
    exact e.map_source hx
  rw [← analyticOrderAt_centeredMonomial (z₀ := (0 : ℂ)) (n := m)]
  refine analyticOrderAt_congr (Filter.eventually_of_mem hmem fun u hu ↦ ?_)
  dsimp only
  rw [torusFamilyAffineQuotientLift_rootsOfUnityBall_symm_eq_pow P hcont hinj R ρ hequiv b hb hone
    hmul hbone hbmul hRc hbc hfree he hu, Pi.pow_apply, sub_zero]

end Charts

section RotatedDisc

variable {m : ℕ} [NeZero m] {r : ℝ}
  {Λ : Type*} [AddCommGroup Λ] [Module.Free ℤ Λ] [Module.Finite ℤ Λ]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  (P : rootsOfUnityBall m r → Λ →ₗ[ℤ] E) [∀ z, DiscreteTopology (LinearMap.range (P z))]
  [∀ z, IsZLattice ℝ (LinearMap.range (P z))]
  (hinj : ∀ z, Function.Injective (P z)) (hP : ∀ l, ContMDiff 𝓘(ℂ) 𝓘(ℂ, E) ω fun z ↦ P z l)
  (R : rootsOfUnity m ℂ → rootsOfUnityBall m r → E →+ E)
  (ρ : Representation ℤ (rootsOfUnity m ℂ) Λ)
  (hequiv : ∀ (g : rootsOfUnity m ℂ) (z : rootsOfUnityBall m r) (l : Λ),
    P (g • z) (ρ g l) = R g z (P z l))
  (b : rootsOfUnity m ℂ → rootsOfUnityBall m r →
    letI := periodAddAction P; AddAction.orbitRel.Quotient Λ (rootsOfUnityBall m r × E))
  (hb : ∀ (g : rootsOfUnity m ℂ) (z : rootsOfUnityBall m r),
    torusFamilyProjection P (b g z) = g • z)
  (hone : ∀ (z : rootsOfUnityBall m r) (v : E), R 1 z v = v)
  (hmul : ∀ (g h : rootsOfUnity m ℂ) (z : rootsOfUnityBall m r) (v : E),
    R (g * h) z v = R g (h • z) (R h z v))
  (hbone : ∀ z : rootsOfUnityBall m r, b 1 z = Quotient.mk _ (z, 0))
  (hbmul : ∀ (g h : rootsOfUnity m ℂ) (z : rootsOfUnityBall m r),
    b (g * h) z = torusFamilyAffineMap R P ρ hequiv b hb g (b h z))
  (hR : ∀ g : rootsOfUnity m ℂ,
    ContMDiff (𝓘(ℂ).prod 𝓘(ℂ, E)) 𝓘(ℂ, E) ω fun p : rootsOfUnityBall m r × E ↦ R g p.1 p.2)
  (hbc : letI := periodAddAction P
    letI := torusFamilyChartedSpace (H := ℂ) P (fun l ↦ (hP l).continuous) hinj
    ∀ g, ContMDiff 𝓘(ℂ) (𝓘(ℂ).prod 𝓘(ℂ, E)) ω (b g))
  (hfree : letI := periodAddAction P
    letI := torusFamilyAffineMulAction R hone hmul P ρ hequiv b hb hbone hbmul
    IsCancelSMul (rootsOfUnity m ℂ) (AddAction.orbitRel.Quotient Λ (rootsOfUnityBall m r × E)))

/-- **The cyclic quotient is a holomorphic submersion off the central fibre.** For a holomorphic
family of tori `X → D` over the disc `D` and a free holomorphic affine action of the `m`-th roots of
unity lifting the rotations, the map `p_Q : X / C_m → ℂ` induced by `z ↦ z ^ m` is a holomorphic
submersion, with complement `E`, at every point of `X / C_m` that it does not send to `0`. Freeness
of the action is characterized by
`TauCeti.isCancelSMul_torusFamilyAffineMulAction_rootsOfUnityBall_iff`. -/
theorem isSubmersionAtOfComplement_torusFamilyAffineQuotientLift_rootsOfUnityBall
    (y : letI := periodAddAction P
      letI := torusFamilyAffineMulAction R hone hmul P ρ hequiv b hb hbone hbmul
      MulAction.orbitRel.Quotient (rootsOfUnity m ℂ)
        (AddAction.orbitRel.Quotient Λ (rootsOfUnityBall m r × E)))
    (hy : torusFamilyAffineQuotientLift P R ρ hequiv b hb hone hmul hbone hbmul
      (fun z : rootsOfUnityBall m r ↦ (z : ℂ) ^ m) (fun g z ↦ coe_smul_rootsOfUnityBall_pow g z) y ≠
        0) :
    letI := periodAddAction P
    letI := torusFamilyChartedSpace (H := ℂ) P (fun l ↦ (hP l).continuous) hinj
    letI := torusFamilyAffineMulAction R hone hmul P ρ hequiv b hb hbone hbmul
    letI := torusFamilyAffineQuotientChartedSpace (H := ℂ) P hinj R ρ hequiv b hb hone hmul
      hbone hbmul (fun l ↦ (hP l).continuous) (fun g ↦ (hR g).continuous)
      (fun g ↦ (hbc g).continuous) hfree
    IsSubmersionAtOfComplement E (𝓘(ℂ).prod 𝓘(ℂ, E)) 𝓘(ℂ) ω
      (torusFamilyAffineQuotientLift P R ρ hequiv b hb hone hmul hbone hbmul
        (fun z : rootsOfUnityBall m r ↦ (z : ℂ) ^ m) fun g z ↦ coe_smul_rootsOfUnityBall_pow g z)
      y := by
  let _ := periodAddAction P
  let _ := torusFamilyAffineMulAction R hone hmul P ρ hequiv b hb hbone hbmul
  induction y using Quotient.inductionOn with | h x =>
  rw [torusFamilyAffineQuotientLift_mk] at hy
  exact isSubmersionAtOfComplement_torusFamilyAffineQuotientLift P hinj hP R ρ hequiv b hb hone
    hmul hbone hbmul hR hbc hfree _ x
    (isLocalDiffeomorphAt_coe_pow_rootsOfUnityBall le_top fun h ↦ hy (by rw [h, zero_pow
      (NeZero.ne m)]))

end RotatedDisc

end TauCeti
