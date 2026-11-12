/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.CauchyRiemann.Weak
public import Mathlib.Topology.OpenPartialHomeomorph.Continuity
public import TauCeti.Analysis.Calculus.FDeriv.PullbackEnd
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import TauCeti.Analysis.Complex.RealDeriv
import TauCeti.Analysis.Sobolev.Local.ChainRule
import TauCeti.Analysis.Sobolev.WeakDeriv.ChainRule

/-!
# The weak Cauchy–Riemann equation under changes of the target

The weak equation `TauCeti.IsWeakCauchyRiemannOn p U J η u`, that is
`∂ₛu + J(z, u) ∂ₜu = η(z, u)` weakly on `U ⊆ ℂ`, is invariant under nonlinear `C¹` changes of
coordinates in the target, provided `J` and `η` are transported along. If `ψ` is `C¹` on an open
set containing `u '' U`, the weak chain rule gives `ψ ∘ u` the weak derivative
`dψ(u) ∘ D`, and applying `dψ(u)` to `D 1 + J D I = η` gives the equation for `ψ ∘ u` with any
field `J'` intertwined with `J` by `dψ(u)` and the term `dψ(u) η`. No invertibility of `ψ` is
needed for this direction. For a `C¹` diffeomorphism `Ψ` between open sets the transported field
is `Ψ_* J = dΨ ∘ J ∘ dΨ⁻¹` and the equation is equivalent before and after the change. The
domain-dependent form, for `z ↦ Φ(z, u z)`, picks up the partial derivative of `Φ` in `z` as an
extra inhomogeneous term; this is the form used by graph constructions and by the reduction of
elliptic bootstrapping to coordinates.

Since the predicate takes the weak derivative on `interior U` and the `Lᵖ` bounds on compact
subsets of `U`, every statement applies verbatim to half-discs.

## Main results

* `TauCeti.IsWeakCauchyRiemannOn.comp_contDiffOn_of_intertwine`: composition with a `C¹` map
  intertwining `J` with a field `J'`.
* `TauCeti.isWeakCauchyRiemannOn_iff_openPartialHomeomorph_comp`: invariance under `C¹`
  diffeomorphisms of the target. The field `Ψ_* J` is `OpenPartialHomeomorph.pullbackEnd` along
  `Ψ.symm` and the term `Ψ_* η` is Mathlib's `VectorField.pullback` along `Ψ.symm`.
* `TauCeti.IsWeakCauchyRiemannOn.comp_graph_of_intertwine`: domain-dependent changes of target
  coordinates `z ↦ Φ(z, u z)`.
* `TauCeti.IsWeakCauchyRiemannOn.conj_comp`: complex conjugation transports the standard
  structure `i` to `-i`; together with `TauCeti.not_isWeakCauchyRiemannOn_conj` this shows that
  the transport of `J` cannot be dropped.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Section 3.1 and Appendix B.4.
-/

public noncomputable section

open Complex MeasureTheory Set TopologicalSpace
open scoped ComplexConjugate Topology

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup W]
  [NormedSpace ℝ W] {p : ENNReal} {U : Set ℂ}
  {J : ℂ → V → V →L[ℝ] V} {η : ℂ → V → V} {u : ℂ → V}
  {J' : ℂ → W → W →L[ℝ] W} {η' : ℂ → W → W}

namespace TauCeti

/-! ### Composition with `C¹` maps -/

/-- **Transport along a `C¹` map of the target.** Let `u` be a weak solution on `U` and let `ψ` be
`C¹` on an open set `O` containing `u '' U`. If a field `J'` and a term `η'` on `W` satisfy, for
almost every `z` in the interior of `U`, `J'(z, ψ(u z)) ∘ dψ(u z) = dψ(u z) ∘ J(z, u z)` and
`η'(z, ψ(u z)) = dψ(u z) (η(z, u z))`, then `ψ ∘ u` is a weak solution for `J'` and `η'`. The
weak derivative of `ψ ∘ u` is `dψ(u) ∘ D` by the weak chain rule, and the equation is
`dψ(u)` applied to `D 1 + J D I = η`. No invertibility of `ψ` is needed. -/
theorem IsWeakCauchyRiemannOn.comp_contDiffOn_of_intertwine [CompleteSpace W] {ψ : V → W}
    {O : Set V} (h : IsWeakCauchyRiemannOn p U J η u) (hO : IsOpen O)
    (hψ : ContDiffOn ℝ 1 ψ O) (huO : MapsTo u U O)
    (hJ : ∀ᵐ z ∂volume.restrict (interior U),
      (J' z (ψ (u z))).comp (fderiv ℝ ψ (u z)) = (fderiv ℝ ψ (u z)).comp (J z (u z)))
    (hη : ∀ᵐ z ∂volume.restrict (interior U),
      η' z (ψ (u z)) = fderiv ℝ ψ (u z) (η z (u z))) :
    IsWeakCauchyRiemannOn p U J' η' (fun z => ψ (u z)) := by
  have hc := h.continuousOn
  obtain ⟨-, -, D, hD, -, hae⟩ := isWeakCauchyRiemannOn_iff.1 h
  have hDψ : HasWeakFDerivOn volume (Opens.interior U) (fun z => ψ (u z))
      fun z => (fderiv ℝ ψ (u z)).comp (D z) :=
    hD.contDiffOn_comp (hc.mono interior_subset) hO hψ (huO.mono_left interior_subset)
  refine isWeakCauchyRiemannOn_iff_forall_hasWeakFDerivOn.2
    ⟨hψ.continuousOn.comp hc huO,
      (h.memWkpLoc_one).contDiffOn_comp hc hO hψ huO, fun D' hD' => ?_⟩
  filter_upwards [hae, hJ, hη, hD'.ae_eq hDψ] with z hz hJz hηz hDz
  have hJz' := congrArg (fun L : V →L[ℝ] W => L (D z I)) hJz
  simp only [ContinuousLinearMap.comp_apply] at hJz'
  rw [hDz, hηz, ← hz, map_add, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    hJz']

/-! ### Diffeomorphisms of the target -/

section Diffeomorphism

variable {Ψ : OpenPartialHomeomorph V W}

/-- A `C¹` open partial homeomorphism with `C¹` inverse is differentiable at every point `x` of
its source, and its inverse is differentiable at `Ψ x`. -/
private theorem differentiableAt_and_symm (hΨ : ContDiffOn ℝ 1 Ψ Ψ.source)
    (hΨs : ContDiffOn ℝ 1 Ψ.symm Ψ.target) {x : V} (hx : x ∈ Ψ.source) :
    DifferentiableAt ℝ Ψ x ∧ DifferentiableAt ℝ Ψ.symm (Ψ x) :=
  ⟨(hΨ.differentiableOn one_ne_zero).differentiableAt (Ψ.open_source.mem_nhds hx),
    (hΨs.differentiableOn one_ne_zero).differentiableAt
      (Ψ.open_target.mem_nhds (Ψ.map_source hx))⟩

/-- **Invariance under `C¹` diffeomorphisms of the target, forward direction.** If `Ψ` is a `C¹`
open partial homeomorphism with `C¹` inverse whose source contains `u '' U`, and `u` is a weak
solution for `J` and `η`, then `Ψ ∘ u` is a weak solution for `Ψ_* J` and `Ψ_* η`. The
transported field `Ψ_* J = dΨ ∘ J ∘ dΨ⁻¹` is the pullback `Ψ.symm.pullbackEnd (J z)` along the
inverse, and the transported term `Ψ_* η = dΨ η` is Mathlib's vector field pullback
`VectorField.pullback ℝ Ψ.symm (η z)` along the inverse. Wherever `J(z, u z)` squares to `-1`,
so does `Ψ_* J` at `(z, Ψ (u z))` (`OpenPartialHomeomorph.pullbackEnd_apply_pullbackEnd_apply`). -/
theorem IsWeakCauchyRiemannOn.openPartialHomeomorph_comp [CompleteSpace W]
    (h : IsWeakCauchyRiemannOn p U J η u) (hΨ : ContDiffOn ℝ 1 Ψ Ψ.source)
    (hΨs : ContDiffOn ℝ 1 Ψ.symm Ψ.target) (huΨ : MapsTo u U Ψ.source) :
    IsWeakCauchyRiemannOn p U (fun z => Ψ.symm.pullbackEnd (J z))
      (fun z => VectorField.pullback ℝ Ψ.symm (η z)) (fun z => Ψ (u z)) := by
  refine h.comp_contDiffOn_of_intertwine Ψ.open_source hΨ huΨ ?_ ?_ <;>
    refine (ae_restrict_iff' measurableSet_interior).2 (Filter.Eventually.of_forall fun z hz => ?_)
  all_goals
    have hx := huΨ (interior_subset hz)
    obtain ⟨hd, hds⟩ := differentiableAt_and_symm hΨ hΨs hx
  · exact Ψ.symm_pullbackEnd_comp_fderiv (J z) hx hd hds
  · exact Ψ.pullback_symm_apply (η z) hx hd hds

/-- **Invariance under `C¹` diffeomorphisms of the target.** For a `C¹` open partial
homeomorphism `Ψ` with `C¹` inverse whose source contains `u '' U`, `u` is a weak solution for
`J` and `η` exactly when `Ψ ∘ u` is a weak solution for `Ψ_* J` and `Ψ_* η`. The reverse
direction is the forward one for `Ψ.symm`, since `Ψ.symm ∘ Ψ ∘ u = u` on `U`. -/
theorem isWeakCauchyRiemannOn_iff_openPartialHomeomorph_comp [CompleteSpace V] [CompleteSpace W]
    (hΨ : ContDiffOn ℝ 1 Ψ Ψ.source) (hΨs : ContDiffOn ℝ 1 Ψ.symm Ψ.target)
    (huΨ : MapsTo u U Ψ.source) :
    IsWeakCauchyRiemannOn p U J η u ↔
      IsWeakCauchyRiemannOn p U (fun z => Ψ.symm.pullbackEnd (J z))
        (fun z => VectorField.pullback ℝ Ψ.symm (η z)) (fun z => Ψ (u z)) := by
  refine ⟨fun h => h.openPartialHomeomorph_comp hΨ hΨs huΨ, fun h => ?_⟩
  have hvΨ : MapsTo (fun z => Ψ (u z)) U Ψ.target := fun z hz => Ψ.map_source (huΨ hz)
  refine (h.comp_contDiffOn_of_intertwine (J' := J) (η' := η) Ψ.open_target hΨs hvΨ ?_
    ?_).congr fun z hz => Ψ.left_inv (huΨ hz) <;>
    refine (ae_restrict_iff' measurableSet_interior).2 (Filter.Eventually.of_forall fun z hz => ?_)
  all_goals
    have hx := huΨ (interior_subset hz)
    obtain ⟨hd, hds⟩ := differentiableAt_and_symm hΨ hΨs hx
  · exact (Ψ.symm.fderiv_comp_pullbackEnd (J z) (Ψ.map_source hx) hds
      (by rwa [Ψ.symm_symm, Ψ.left_inv hx])).symm
  · exact (VectorField.fderiv_pullback Ψ.symm (η z) (Ψ (u z))
      (Ψ.isInvertible_fderiv_symm hx hd hds)).symm

end Diffeomorphism

/-! ### Domain-dependent changes of target coordinates -/

/-- **Domain-dependent change of target coordinates.** Let `u` be a weak solution on `U` and let
`Φ : ℂ × V → W` be `C¹` on an open set containing the graph of `u` over `U`. Write
`∂ₓΦ = dΦ(z, u z) ∘ inr` and `∂_zΦ = dΦ(z, u z) ∘ inl` for the partial derivatives along the
graph. If, for almost every `z` in the interior of `U`, `J'(z, Φ(z, u z)) ∘ ∂ₓΦ = ∂ₓΦ ∘ J(z, u z)`
and `η'(z, Φ(z, u z)) = ∂ₓΦ (η(z, u z)) + ∂_zΦ 1 + J'(z, Φ(z, u z)) (∂_zΦ I)`, then
`z ↦ Φ(z, u z)` is a weak solution for `J'` and `η'`. The extra terms come from the derivative of
`Φ` in the domain variable. -/
theorem IsWeakCauchyRiemannOn.comp_graph_of_intertwine [CompleteSpace W] {Φ : ℂ × V → W}
    {O : Set (ℂ × V)} (h : IsWeakCauchyRiemannOn p U J η u) (hO : IsOpen O)
    (hΦ : ContDiffOn ℝ 1 Φ O) (huO : ∀ z ∈ U, (z, u z) ∈ O)
    (hJ : ∀ᵐ z ∂volume.restrict (interior U),
      (J' z (Φ (z, u z))).comp ((fderiv ℝ Φ (z, u z)).comp (ContinuousLinearMap.inr ℝ ℂ V)) =
        ((fderiv ℝ Φ (z, u z)).comp (ContinuousLinearMap.inr ℝ ℂ V)).comp (J z (u z)))
    (hη : ∀ᵐ z ∂volume.restrict (interior U),
      η' z (Φ (z, u z)) = fderiv ℝ Φ (z, u z) (0, η z (u z)) + fderiv ℝ Φ (z, u z) (1, 0) +
        J' z (Φ (z, u z)) (fderiv ℝ Φ (z, u z) (I, 0))) :
    IsWeakCauchyRiemannOn p U J' η' (fun z => Φ (z, u z)) := by
  have hc := h.continuousOn
  obtain ⟨-, -, D, hD, -, hae⟩ := isWeakCauchyRiemannOn_iff.1 h
  have hDΦ := hD.contDiffOn_comp_graph (hc.mono interior_subset) hO hΦ
    fun z hz => huO z (interior_subset hz)
  refine isWeakCauchyRiemannOn_iff_forall_hasWeakFDerivOn.2
    ⟨hΦ.continuousOn.comp (continuousOn_id.prodMk hc) huO,
      (h.memWkpLoc_one).contDiffOn_comp_graph hc hO hΦ huO, fun D' hD' => ?_⟩
  filter_upwards [hae, hJ, hη, hD'.ae_eq hDΦ] with z hz hJz hηz hDz
  have hJz' := congrArg (fun L : V →L[ℝ] W => L (D z I)) hJz
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply] at hJz'
  have hsplit : ∀ w : ℂ, fderiv ℝ Φ (z, u z) (w, D z w) =
      fderiv ℝ Φ (z, u z) (w, 0) + fderiv ℝ Φ (z, u z) (0, D z w) := fun w => by
    rw [← map_add, Prod.mk_add_mk, add_zero, zero_add]
  have hpair : ((0 : ℂ), D z 1 + J z (u z) (D z I)) =
      ((0 : ℂ), D z 1) + (0, J z (u z) (D z I)) := by
    rw [Prod.mk_add_mk, add_zero]
  rw [hDz, hηz, ← hz]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.id_apply]
  rw [hsplit, hsplit, map_add, hJz', hpair, map_add]
  abel

/-! ### Checks -/

section Checks

/-- **Conjugation reverses the standard structure.** If `u : ℂ → ℂ` solves the homogeneous
equation for `J = i`, then `conj ∘ u` solves the homogeneous equation for `J = -i`: the
derivative of conjugation intertwines `i` with `-i`. Since conjugation itself does not solve the
equation for `i` (`TauCeti.not_isWeakCauchyRiemannOn_conj`), the transport of `J` in
`TauCeti.IsWeakCauchyRiemannOn.comp_contDiffOn_of_intertwine` cannot be dropped. -/
theorem IsWeakCauchyRiemannOn.conj_comp {u : ℂ → ℂ}
    (h : IsWeakCauchyRiemannOn p U (fun _ _ => I • ContinuousLinearMap.id ℝ ℂ) (fun _ _ => 0) u) :
    IsWeakCauchyRiemannOn p U (fun _ _ => (-I) • ContinuousLinearMap.id ℝ ℂ) (fun _ _ => 0)
      (fun z => conj (u z)) :=
  h.comp_contDiffOn_of_intertwine isOpen_univ conjCLE.contDiff.contDiffOn (mapsTo_univ _ _)
    (Filter.Eventually.of_forall fun z => ContinuousLinearMap.ext fun v => by
      simp)
    (Filter.Eventually.of_forall fun z => by simp)

-- Conjugation solves the homogeneous equation for `-i` but not for `i`, on any nonempty open set.
example {Ω : Opens ℂ} (hΩ : (Ω : Set ℂ).Nonempty) :
    IsWeakCauchyRiemannOn p Ω (fun _ _ => (-I) • ContinuousLinearMap.id ℝ ℂ) (fun _ _ => 0)
        (fun z => conj z) ∧
      ¬IsWeakCauchyRiemannOn p Ω (fun _ _ => I • ContinuousLinearMap.id ℝ ℂ) (fun _ _ => 0)
        conj :=
  ⟨(isWeakCauchyRiemannOn_id (p := p) (Ω := Ω)).conj_comp, not_isWeakCauchyRiemannOn_conj hΩ⟩

-- A holomorphic change of target, here `exp`, keeps the homogeneous equation for `i`: its
-- derivative is multiplication by `exp (u z)`, which commutes with `i`.
example {u : ℂ → ℂ}
    (h : IsWeakCauchyRiemannOn p U (fun _ _ => I • ContinuousLinearMap.id ℝ ℂ) (fun _ _ => 0) u) :
    IsWeakCauchyRiemannOn p U (fun _ _ => I • ContinuousLinearMap.id ℝ ℂ) (fun _ _ => 0)
      (fun z => exp (u z)) := by
  have hd (x : ℂ) : fderiv ℝ exp x = exp x • (1 : ℂ →L[ℝ] ℂ) :=
    (hasDerivAt_exp x).complexToReal_fderiv.fderiv
  refine h.comp_contDiffOn_of_intertwine isOpen_univ
    (Complex.contDiff_exp (𝕜 := ℝ)).contDiffOn (mapsTo_univ _ _)
    (Filter.Eventually.of_forall fun z => ContinuousLinearMap.ext fun v => ?_)
    (Filter.Eventually.of_forall fun z => by simp [hd])
  simp [hd, mul_left_comm]

-- A linear change of target `A` transports `J` to `A ∘ J ∘ A⁻¹` and `η` to `A ∘ η ∘ A⁻¹`.
example [CompleteSpace V] [CompleteSpace W] (A : V ≃L[ℝ] W) :
    IsWeakCauchyRiemannOn p U J η u ↔ IsWeakCauchyRiemannOn p U
      (fun z y => (A : V →L[ℝ] W).comp ((J z (A.symm y)).comp (A.symm : W →L[ℝ] V)))
      (fun z y => A (η z (A.symm y))) (fun z => A (u z)) := by
  have h := isWeakCauchyRiemannOn_iff_openPartialHomeomorph_comp (p := p) (J := J) (η := η)
    (U := U) (u := u) (Ψ := A.toHomeomorph.toOpenPartialHomeomorph)
    (by simpa using A.contDiff.contDiffOn)
    (by simpa using A.symm.contDiff.contDiffOn) (mapsTo_univ _ _)
  have e1 : ⇑A.toHomeomorph.toOpenPartialHomeomorph = ⇑A := by ext; simp
  have e2 : ⇑A.toHomeomorph.toOpenPartialHomeomorph.symm = ⇑A.symm := by ext; simp
  have hS : (fun z => A.toHomeomorph.toOpenPartialHomeomorph.symm.pullbackEnd (J z)) =
      fun z y => (A : V →L[ℝ] W).comp ((J z (A.symm y)).comp (A.symm : W →L[ℝ] V)) := by
    funext z y
    ext v
    rw [OpenPartialHomeomorph.pullbackEnd_apply, OpenPartialHomeomorph.symm_symm, e1, e2,
      A.fderiv, A.symm.fderiv, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply]
  have hT : (fun z => VectorField.pullback ℝ A.toHomeomorph.toOpenPartialHomeomorph.symm (η z)) =
      fun z y => A (η z (A.symm y)) := by
    funext z y
    rw [VectorField.pullback_eq_of_fderiv_eq (M := A.symm) (by rw [e2, A.symm.fderiv]), e2,
      ContinuousLinearEquiv.symm_symm]
  rwa [hS, hT, e1] at h

end Checks

end TauCeti
