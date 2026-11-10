/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.GroupAction.OrbitRelQuotient
public import TauCeti.Algebra.Module.ZLattice.Family.Action
public import TauCeti.Analysis.Complex.RootsOfUnity.Manifold

/-!
# The coordinate `t = z ^ m` on the cyclic quotient of a family of tori

Let `D = TauCeti.rootsOfUnityBall m r` be the open disc of radius `r` about `0` in `ℂ`, on which
the group `C_m = rootsOfUnity m ℂ` of `m`-th roots of unity acts by the rotations `z ↦ ζ z`. Let
`P : D → (Λ →ₗ[ℤ] E)` be a family of full lattices in a finite-dimensional complex space `E`,
with total space `X = (D × E)/Λ` and projection `p : X → D`, and let `C_m` act on `X` by an affine
cocycle `ζ • [z, v] = R ζ z v +ᵥ b ζ z` lifting the rotations
(`TauCeti.torusFamilyAffineMulAction`).

The function `t = z ^ m` of the base is invariant under the rotations, so `[x] ↦ p(x) ^ m`
descends to the orbit space `Q = X / C_m` (`TauCeti.torusFamilyCyclicQuotientProjection`). For
`0 ≤ r`, its image is the disc of radius `r ^ m`
(`TauCeti.range_torusFamilyCyclicQuotientProjection`), and two points of `Q` have the same image
exactly when they lie over one orbit of the rotations on `D`
(`TauCeti.torusFamilyCyclicQuotientProjection_mk_eq_mk_iff`): it is the map from `Q` to the
quotient disc `D / C_m`, read in the coordinate `t` of
`TauCeti.rootsOfUnityBallQuotientHomeomorph`. Its fibre over `0` consists of the points over the
centre of `D`, the fixed point of the rotations on the base, that is, the image of the central torus
(`TauCeti.torusFamilyCyclicQuotientProjection_eq_zero_iff`).

When the action of `C_m` on `X` is free, a condition on the central torus only
(`TauCeti.isCancelSMul_torusFamilyAffineMulAction_rootsOfUnityBall_iff`), `Q` is a `C^n` manifold
whose orbit map from `X` is a `C^n` local diffeomorphism
(`TauCeti.isManifold_torusFamilyAffineQuotient`,
`TauCeti.isLocalDiffeomorph_torusFamilyAffineQuotient_mk`); `C_m` is finite, so its action on the
base is properly discontinuous. For `C^n` data the coordinate `t` is then `C^n` on `Q`
(`TauCeti.contMDiff_torusFamilyCyclicQuotientProjection`). With holomorphic periods, linear parts
and translation sections and `n = ω`, `Q` is a complex manifold and `t : Q → ℂ` is holomorphic.

## Main definitions

* `TauCeti.torusFamilyCyclicQuotientProjection`: the map `Q → ℂ` descended from `[z, v] ↦ z ^ m`.

## Main results

* `TauCeti.torusFamilyCyclicQuotientProjection_mk`: the value on the orbit of a point over `z`
  is `z ^ m`.
* `TauCeti.torusFamilyCyclicQuotientProjection_mk_eq_mk_iff`: its fibres are the preimages of the
  orbits of the rotations on the base.
* `TauCeti.torusFamilyCyclicQuotientProjection_eq_zero_iff`: its fibre over `0` lies over the
  centre of the disc.
* `TauCeti.range_torusFamilyCyclicQuotientProjection`: for `0 ≤ r`, its image is the disc of
  radius `r ^ m`.
* `TauCeti.contMDiff_torusFamilyCyclicQuotientProjection`: for a free action with `C^n` data it is
  `C^n`; for holomorphic data it is holomorphic.

## References

* W. P. Barth, K. Hulek, C. A. M. Peters, A. Van de Ven, *Compact Complex Surfaces*, second
  edition, Springer (2004), Chapter V, section *Logarithmic transformations*, for the cyclic
  quotient of a family of tori over a disc and its map to the quotient disc.
-/

public section

open MulAction Set
open scoped Manifold ContDiff

namespace TauCeti

variable {m : ℕ} [NeZero m] {r : ℝ}
  {Λ : Type*} [AddCommGroup Λ] {E : Type*} [AddCommGroup E]
  (R : rootsOfUnity m ℂ → rootsOfUnityBall m r → E →+ E)
  (hone : ∀ (z : rootsOfUnityBall m r) (v : E), R 1 z v = v)
  (hmul : ∀ (g h : rootsOfUnity m ℂ) (z : rootsOfUnityBall m r) (v : E),
    R (g * h) z v = R g (h • z) (R h z v))
  (P : rootsOfUnityBall m r → Λ →ₗ[ℤ] E) (ρ : Representation ℤ (rootsOfUnity m ℂ) Λ)
  (hequiv : ∀ (g : rootsOfUnity m ℂ) (z : rootsOfUnityBall m r) (l : Λ),
    P (g • z) (ρ g l) = R g z (P z l))
  (b : rootsOfUnity m ℂ → rootsOfUnityBall m r →
    letI := periodAddAction P; AddAction.orbitRel.Quotient Λ (rootsOfUnityBall m r × E))
  (hb : ∀ (g : rootsOfUnity m ℂ) (z : rootsOfUnityBall m r),
    torusFamilyProjection P (b g z) = g • z)
  (hbone : ∀ z : rootsOfUnityBall m r, b 1 z = Quotient.mk _ (z, 0))
  (hbmul : ∀ (g h : rootsOfUnity m ℂ) (z : rootsOfUnityBall m r),
    b (g * h) z = torusFamilyAffineMap R P ρ hequiv b hb g (b h z))

/-! ### The descended coordinate `t = z ^ m` -/

/-- **The coordinate `t = z ^ m` on the cyclic quotient.** The map `Q → ℂ` from the orbit space
`Q = X / C_m` of the cyclic affine action on the family of tori `X = (D × E)/Λ`, sending the orbit
of a point over `z` to `z ^ m`. For `0 ≤ r`, its image is the disc of radius `r ^ m`, the quotient
of `D` by the rotations. -/
noncomputable def torusFamilyCyclicQuotientProjection :
    letI := periodAddAction P
    letI := torusFamilyAffineMulAction R hone hmul P ρ hequiv b hb hbone hbmul
    orbitRel.Quotient (rootsOfUnity m ℂ) (AddAction.orbitRel.Quotient Λ (rootsOfUnityBall m r × E))
      → ℂ :=
  letI := periodAddAction P
  letI := torusFamilyAffineMulAction R hone hmul P ρ hequiv b hb hbone hbmul
  MulAction.orbitRelQuotientLift
    (fun x ↦ ((torusFamilyProjection P x : rootsOfUnityBall m r) : ℂ) ^ m) fun g x ↦ by
    rw [torusFamilyAffineMulAction_smul, torusFamilyProjection_affineMap, SubMulAction.val_smul,
      rootsOfUnity.smul_pow]

/-- The coordinate `t` of the orbit of a point over `z` is `z ^ m`. -/
@[simp] theorem torusFamilyCyclicQuotientProjection_mk
    (x : letI := periodAddAction P; AddAction.orbitRel.Quotient Λ (rootsOfUnityBall m r × E)) :
    letI := periodAddAction P
    letI := torusFamilyAffineMulAction R hone hmul P ρ hequiv b hb hbone hbmul
    torusFamilyCyclicQuotientProjection R hone hmul P ρ hequiv b hb hbone hbmul
      (Quotient.mk _ x) = ((torusFamilyProjection P x : rootsOfUnityBall m r) : ℂ) ^ m := by
  let _ := periodAddAction P
  let _ := torusFamilyAffineMulAction R hone hmul P ρ hequiv b hb hbone hbmul
  exact MulAction.orbitRelQuotientLift_mk x

/-- **The fibres of `t`.** Two points of the cyclic quotient have the same coordinate `t` exactly
when they lie over points of the disc in one orbit of the rotations. -/
theorem torusFamilyCyclicQuotientProjection_mk_eq_mk_iff
    (x y : letI := periodAddAction P; AddAction.orbitRel.Quotient Λ (rootsOfUnityBall m r × E)) :
    letI := periodAddAction P
    letI := torusFamilyAffineMulAction R hone hmul P ρ hequiv b hb hbone hbmul
    torusFamilyCyclicQuotientProjection R hone hmul P ρ hequiv b hb hbone hbmul
        (Quotient.mk _ x) =
      torusFamilyCyclicQuotientProjection R hone hmul P ρ hequiv b hb hbone hbmul
        (Quotient.mk _ y) ↔
      ∃ g : rootsOfUnity m ℂ, g • torusFamilyProjection P x = torusFamilyProjection P y := by
  simp only [torusFamilyCyclicQuotientProjection_mk]
  rw [pow_eq_pow_iff_exists_rootsOfUnity_smul (NeZero.ne m)]
  simp only [← SubMulAction.val_smul, Subtype.val_inj]

/-- **The fibre of `t` over `0`.** A point of the cyclic quotient has coordinate `t = 0` exactly
when it lies over the centre of the disc, that is, when it is the image of a point of the central
torus. -/
theorem torusFamilyCyclicQuotientProjection_eq_zero_iff
    (x : letI := periodAddAction P; AddAction.orbitRel.Quotient Λ (rootsOfUnityBall m r × E)) :
    letI := periodAddAction P
    letI := torusFamilyAffineMulAction R hone hmul P ρ hequiv b hb hbone hbmul
    torusFamilyCyclicQuotientProjection R hone hmul P ρ hequiv b hb hbone hbmul
        (Quotient.mk _ x) = 0 ↔ ((torusFamilyProjection P x : rootsOfUnityBall m r) : ℂ) = 0 := by
  rw [torusFamilyCyclicQuotientProjection_mk, pow_eq_zero_iff (NeZero.ne m)]

/-- **The image of `t`.** For `0 ≤ r`, the coordinate `t` maps the cyclic quotient onto the disc
of radius `r ^ m`, the quotient of the disc of radius `r` by the rotations. -/
theorem range_torusFamilyCyclicQuotientProjection (hr : 0 ≤ r) :
    range (torusFamilyCyclicQuotientProjection R hone hmul P ρ hequiv b hb hbone hbmul) =
      Metric.ball 0 (r ^ m) := by
  let _ := periodAddAction P
  let _ := torusFamilyAffineMulAction R hone hmul P ρ hequiv b hb hbone hbmul
  rw [← image_pow_ball (m := m) hr]
  ext t
  constructor
  · rintro ⟨q, rfl⟩
    induction q using Quotient.inductionOn with
    | h x =>
      rw [torusFamilyCyclicQuotientProjection_mk]
      exact mem_image_of_mem _
        (mem_ball_zero_iff.2 (mem_rootsOfUnityBall.1 (torusFamilyProjection P x).2))
  · rintro ⟨u, hu, rfl⟩
    obtain ⟨x, hx⟩ := torusFamilyProjection_surjective P
      ⟨u, mem_rootsOfUnityBall.2 (mem_ball_zero_iff.1 hu)⟩
    exact ⟨Quotient.mk _ x, by rw [torusFamilyCyclicQuotientProjection_mk, hx]⟩

/-! ### Holomorphy of the coordinate `t` -/

section Manifold

variable [Module.Free ℤ Λ] [Module.Finite ℤ Λ] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  (R : rootsOfUnity m ℂ → rootsOfUnityBall m r → E →+ E)
  (hone : ∀ (z : rootsOfUnityBall m r) (v : E), R 1 z v = v)
  (hmul : ∀ (g h : rootsOfUnity m ℂ) (z : rootsOfUnityBall m r) (v : E),
    R (g * h) z v = R g (h • z) (R h z v))
  (P : rootsOfUnityBall m r → Λ →ₗ[ℤ] E) [∀ z, DiscreteTopology (LinearMap.range (P z))]
  [∀ z, IsZLattice ℝ (LinearMap.range (P z))]
  (hinj : ∀ z, Function.Injective (P z)) {n : ℕ∞ω}
  (hP : ∀ l, ContMDiff 𝓘(ℂ) 𝓘(ℂ, E) n fun z ↦ P z l)
  (ρ : Representation ℤ (rootsOfUnity m ℂ) Λ)
  (hequiv : ∀ (g : rootsOfUnity m ℂ) (z : rootsOfUnityBall m r) (l : Λ),
    P (g • z) (ρ g l) = R g z (P z l))
  (b : rootsOfUnity m ℂ → rootsOfUnityBall m r →
    letI := periodAddAction P; AddAction.orbitRel.Quotient Λ (rootsOfUnityBall m r × E))
  (hb : ∀ (g : rootsOfUnity m ℂ) (z : rootsOfUnityBall m r),
    torusFamilyProjection P (b g z) = g • z)
  (hbone : ∀ z : rootsOfUnityBall m r, b 1 z = Quotient.mk _ (z, 0))
  (hbmul : ∀ (g h : rootsOfUnity m ℂ) (z : rootsOfUnityBall m r),
    b (g * h) z = torusFamilyAffineMap R P ρ hequiv b hb g (b h z))
  (hR : ∀ g : rootsOfUnity m ℂ,
    ContMDiff (𝓘(ℂ).prod 𝓘(ℂ, E)) 𝓘(ℂ, E) n fun p : rootsOfUnityBall m r × E ↦ R g p.1 p.2)
  (hbc : letI := periodAddAction P
    letI := torusFamilyChartedSpace (H := ℂ) P (fun l ↦ (hP l).continuous) hinj
    ∀ g, ContMDiff 𝓘(ℂ) (𝓘(ℂ).prod 𝓘(ℂ, E)) n (b g))
  (hfree : letI := periodAddAction P
    letI := torusFamilyAffineMulAction R hone hmul P ρ hequiv b hb hbone hbmul
    IsCancelSMul (rootsOfUnity m ℂ) (AddAction.orbitRel.Quotient Λ (rootsOfUnityBall m r × E)))

/-- **The coordinate `t` is holomorphic.** If the cyclic affine action on the `C^n` family of tori
`X` over the rotated disc is free, the map `X / C_m → ℂ` descended from `[z, v] ↦ z ^ m` is `C^n`
for the quotient manifold structure (`TauCeti.isManifold_torusFamilyAffineQuotient`); with
holomorphic data and `n = ω`, it is a holomorphic function on the complex manifold `X / C_m`. -/
theorem contMDiff_torusFamilyCyclicQuotientProjection :
    letI := periodAddAction P
    letI := torusFamilyChartedSpace (H := ℂ) P (fun l ↦ (hP l).continuous) hinj
    letI := torusFamilyAffineMulAction R hone hmul P ρ hequiv b hb hbone hbmul
    letI := torusFamilyAffineQuotientChartedSpace (H := ℂ) P hinj R ρ hequiv b hb hone hmul hbone
      hbmul (fun l ↦ (hP l).continuous) (fun g ↦ (hR g).continuous) (fun g ↦ (hbc g).continuous)
      hfree
    ContMDiff (𝓘(ℂ).prod 𝓘(ℂ, E)) 𝓘(ℂ) n
      (torusFamilyCyclicQuotientProjection R hone hmul P ρ hequiv b hb hbone hbmul) := by
  let _ := periodAddAction P
  let _ := torusFamilyChartedSpace (H := ℂ) P (fun l ↦ (hP l).continuous) hinj
  let _ := torusFamilyAffineMulAction R hone hmul P ρ hequiv b hb hbone hbmul
  let _ := torusFamilyAffineQuotientChartedSpace (H := ℂ) P hinj R ρ hequiv b hb hone hmul hbone
    hbmul (fun l ↦ (hP l).continuous) (fun g ↦ (hR g).continuous) (fun g ↦ (hbc g).continuous)
    hfree
  refine ((isLocalDiffeomorph_torusFamilyAffineQuotient_mk P hinj hP R ρ hequiv b hb hone hmul
    hbone hbmul hR hbc hfree).contMDiff_comp_iff Quotient.mk_surjective le_rfl).1 ?_
  simp only [Function.comp_def, torusFamilyCyclicQuotientProjection_mk]
  exact (contDiff_id.pow m).contMDiff.comp
    (rootsOfUnityBall.contMDiff_val.comp (contMDiff_torusFamilyProjection P hinj hP))

end Manifold

end TauCeti
