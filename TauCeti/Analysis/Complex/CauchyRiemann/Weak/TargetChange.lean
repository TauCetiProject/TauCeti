/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.CauchyRiemann.Weak
public import Mathlib.Topology.OpenPartialHomeomorph.Continuity
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
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
* `TauCeti.transportCauchyRiemannStructure`, `TauCeti.transportCauchyRiemannTerm`: the fields
  `Ψ_* J` and `Ψ_* η` transported by an open partial homeomorphism.
* `TauCeti.isWeakCauchyRiemannOn_iff_openPartialHomeomorph_comp`: invariance under `C¹`
  diffeomorphisms of the target.
* `TauCeti.transportCauchyRiemannStructure_mul_self`: the transport of an almost complex
  structure is an almost complex structure.
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

namespace TauCeti

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup W]
  [NormedSpace ℝ W] {p : ENNReal} {U : Set ℂ}
  {J : ℂ → V → V →L[ℝ] V} {η : ℂ → V → V} {u : ℂ → V}
  {J' : ℂ → W → W →L[ℝ] W} {η' : ℂ → W → W}

/-- A weak solution stays a weak solution when it is replaced by a map agreeing with it on `U`.
The predicate only sees values on `U`. -/
private theorem IsWeakCauchyRiemannOn.congr_eqOn (h : IsWeakCauchyRiemannOn p U J η u)
    {v : ℂ → V} (huv : EqOn u v U) : IsWeakCauchyRiemannOn p U J η v := by
  obtain ⟨hc, hu, D, hD, hDp, hae⟩ := isWeakCauchyRiemannOn_iff.1 h
  have hint : u =ᵐ[volume.restrict (interior U)] v :=
    (ae_restrict_iff' measurableSet_interior).2
      (Filter.Eventually.of_forall fun z hz => huv (interior_subset hz))
  refine isWeakCauchyRiemannOn_iff.2 ⟨hc.congr fun z hz => (huv hz).symm,
    memLpLoc_iff.2 fun K hK hKc => (memLpLoc_iff.1 hu K hK hKc).ae_eq
    ((ae_restrict_iff' hKc.measurableSet).2 (Filter.Eventually.of_forall fun z hz => huv (hK hz))),
    D, hD.congr_ae hint, hDp, ?_⟩
  filter_upwards [hae, hint] with z hz hzv
  rwa [← hzv]

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

/-- The derivative of the inverse of a `C¹` open partial homeomorphism with `C¹` inverse is a
left inverse of its derivative on the source. This is the chain rule for `Ψ.symm ∘ Ψ = id` near
a point of the source. -/
private theorem fderiv_symm_comp_fderiv (Ψ : OpenPartialHomeomorph V W)
    (hΨ : ContDiffOn ℝ 1 Ψ Ψ.source) (hΨs : ContDiffOn ℝ 1 Ψ.symm Ψ.target) {x : V}
    (hx : x ∈ Ψ.source) :
    (fderiv ℝ Ψ.symm (Ψ x)).comp (fderiv ℝ Ψ x) = ContinuousLinearMap.id ℝ V := by
  have h1 : HasFDerivAt Ψ (fderiv ℝ Ψ x) x :=
    ((hΨ.differentiableOn one_ne_zero).differentiableAt (Ψ.open_source.mem_nhds hx)).hasFDerivAt
  have h2 : HasFDerivAt Ψ.symm (fderiv ℝ Ψ.symm (Ψ x)) (Ψ x) :=
    ((hΨs.differentiableOn one_ne_zero).differentiableAt
      (Ψ.open_target.mem_nhds (Ψ.map_source hx))).hasFDerivAt
  have hid : (id : V → V) =ᶠ[𝓝 x] Ψ.symm ∘ Ψ :=
    (Ψ.eventually_left_inverse hx).mono fun y hy => hy.symm
  exact ((h2.comp x h1).congr_of_eventuallyEq hid).unique (hasFDerivAt_id x)

/-- The derivative of a `C¹` open partial homeomorphism with `C¹` inverse is a left inverse of
the derivative of the inverse on the target. -/
private theorem fderiv_comp_fderiv_symm (Ψ : OpenPartialHomeomorph V W)
    (hΨ : ContDiffOn ℝ 1 Ψ Ψ.source) (hΨs : ContDiffOn ℝ 1 Ψ.symm Ψ.target) {y : W}
    (hy : y ∈ Ψ.target) :
    (fderiv ℝ Ψ (Ψ.symm y)).comp (fderiv ℝ Ψ.symm y) = ContinuousLinearMap.id ℝ W := by
  have := fderiv_symm_comp_fderiv Ψ.symm hΨs (by rwa [Ψ.symm_symm]) (x := y) hy
  rwa [Ψ.symm_symm] at this

/-- The field of endomorphisms `Ψ_* J` transported by an open partial homeomorphism `Ψ`:
`(Ψ_* J)(z, y) = dΨ(Ψ⁻¹ y) ∘ J(z, Ψ⁻¹ y) ∘ dΨ⁻¹(y)`, with `dΨ⁻¹(y)` the derivative of `Ψ.symm`
at `y`. It is meaningful on the target of `Ψ`. -/
@[expose] def transportCauchyRiemannStructure (Ψ : OpenPartialHomeomorph V W)
    (J : ℂ → V → V →L[ℝ] V) : ℂ → W → W →L[ℝ] W :=
  fun z y => (fderiv ℝ Ψ (Ψ.symm y)).comp ((J z (Ψ.symm y)).comp (fderiv ℝ Ψ.symm y))

/-- The inhomogeneous term `Ψ_* η` transported by an open partial homeomorphism `Ψ`:
`(Ψ_* η)(z, y) = dΨ(Ψ⁻¹ y) (η(z, Ψ⁻¹ y))`. It is meaningful on the target of `Ψ`. -/
@[expose] def transportCauchyRiemannTerm (Ψ : OpenPartialHomeomorph V W) (η : ℂ → V → V) :
    ℂ → W → W :=
  fun z y => fderiv ℝ Ψ (Ψ.symm y) (η z (Ψ.symm y))

theorem transportCauchyRiemannStructure_apply (Ψ : OpenPartialHomeomorph V W)
    (J : ℂ → V → V →L[ℝ] V) (z : ℂ) (y : W) :
    transportCauchyRiemannStructure Ψ J z y =
      (fderiv ℝ Ψ (Ψ.symm y)).comp ((J z (Ψ.symm y)).comp (fderiv ℝ Ψ.symm y)) :=
  rfl

theorem transportCauchyRiemannTerm_apply (Ψ : OpenPartialHomeomorph V W) (η : ℂ → V → V)
    (z : ℂ) (y : W) :
    transportCauchyRiemannTerm Ψ η z y = fderiv ℝ Ψ (Ψ.symm y) (η z (Ψ.symm y)) :=
  rfl

variable {Ψ : OpenPartialHomeomorph V W}

/-- **Transport of almost complex structures.** If `J(z, Ψ⁻¹ y)` squares to `-1` at a point `y`
of the target, so does `(Ψ_* J)(z, y)`. -/
theorem transportCauchyRiemannStructure_mul_self (hΨ : ContDiffOn ℝ 1 Ψ Ψ.source)
    (hΨs : ContDiffOn ℝ 1 Ψ.symm Ψ.target) {z : ℂ} {y : W} (hy : y ∈ Ψ.target)
    (hJ : J z (Ψ.symm y) * J z (Ψ.symm y) = -1) :
    transportCauchyRiemannStructure Ψ J z y * transportCauchyRiemannStructure Ψ J z y = -1 := by
  have hl := fderiv_symm_comp_fderiv Ψ hΨ hΨs (Ψ.map_target hy)
  rw [Ψ.right_inv hy] at hl
  have hr := fderiv_comp_fderiv_symm Ψ hΨ hΨs hy
  ext v
  have hl' := congrArg (fun L : V →L[ℝ] V => L (J z (Ψ.symm y) (fderiv ℝ Ψ.symm y v))) hl
  have hJ' : J z (Ψ.symm y) (J z (Ψ.symm y) (fderiv ℝ Ψ.symm y v)) = -fderiv ℝ Ψ.symm y v :=
    congrArg (fun L : V →L[ℝ] V => L (fderiv ℝ Ψ.symm y v)) hJ
  have hr' := congrArg (fun L : W →L[ℝ] W => L v) hr
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] at hl' hr'
  change fderiv ℝ Ψ (Ψ.symm y) (J z (Ψ.symm y) (fderiv ℝ Ψ.symm y
    (fderiv ℝ Ψ (Ψ.symm y) (J z (Ψ.symm y) (fderiv ℝ Ψ.symm y v))))) = -v
  rw [hl', hJ', map_neg, hr']

/-- **Invariance under `C¹` diffeomorphisms of the target, forward direction.** If `Ψ` is a `C¹`
open partial homeomorphism with `C¹` inverse whose source contains `u '' U`, and `u` is a weak
solution for `J` and `η`, then `Ψ ∘ u` is a weak solution for `Ψ_* J` and `Ψ_* η`. -/
theorem IsWeakCauchyRiemannOn.openPartialHomeomorph_comp [CompleteSpace W]
    (h : IsWeakCauchyRiemannOn p U J η u) (hΨ : ContDiffOn ℝ 1 Ψ Ψ.source)
    (hΨs : ContDiffOn ℝ 1 Ψ.symm Ψ.target) (huΨ : MapsTo u U Ψ.source) :
    IsWeakCauchyRiemannOn p U (transportCauchyRiemannStructure Ψ J)
      (transportCauchyRiemannTerm Ψ η) (fun z => Ψ (u z)) := by
  refine h.comp_contDiffOn_of_intertwine Ψ.open_source hΨ huΨ ?_ ?_ <;>
    refine (ae_restrict_iff' measurableSet_interior).2 (Filter.Eventually.of_forall fun z hz => ?_)
  · have hx := huΨ (interior_subset hz)
    rw [transportCauchyRiemannStructure_apply, Ψ.left_inv hx, ContinuousLinearMap.comp_assoc,
      ContinuousLinearMap.comp_assoc, fderiv_symm_comp_fderiv Ψ hΨ hΨs hx,
      ContinuousLinearMap.comp_id]
  · rw [transportCauchyRiemannTerm_apply, Ψ.left_inv (huΨ (interior_subset hz))]

/-- **Invariance under `C¹` diffeomorphisms of the target.** For a `C¹` open partial
homeomorphism `Ψ` with `C¹` inverse whose source contains `u '' U`, `u` is a weak solution for
`J` and `η` exactly when `Ψ ∘ u` is a weak solution for `Ψ_* J` and `Ψ_* η`. The reverse
direction is the forward one for `Ψ.symm`, since `Ψ.symm ∘ Ψ ∘ u = u` on `U`. -/
theorem isWeakCauchyRiemannOn_iff_openPartialHomeomorph_comp [CompleteSpace V] [CompleteSpace W]
    (hΨ : ContDiffOn ℝ 1 Ψ Ψ.source) (hΨs : ContDiffOn ℝ 1 Ψ.symm Ψ.target)
    (huΨ : MapsTo u U Ψ.source) :
    IsWeakCauchyRiemannOn p U J η u ↔
      IsWeakCauchyRiemannOn p U (transportCauchyRiemannStructure Ψ J)
        (transportCauchyRiemannTerm Ψ η) (fun z => Ψ (u z)) := by
  refine ⟨fun h => h.openPartialHomeomorph_comp hΨ hΨs huΨ, fun h => ?_⟩
  have hvΨ : MapsTo (fun z => Ψ (u z)) U Ψ.target := fun z hz => Ψ.map_source (huΨ hz)
  refine (h.comp_contDiffOn_of_intertwine (J' := J) (η' := η) Ψ.open_target hΨs hvΨ ?_
    ?_).congr_eqOn fun z hz => Ψ.left_inv (huΨ hz) <;>
    refine (ae_restrict_iff' measurableSet_interior).2 (Filter.Eventually.of_forall fun z hz => ?_)
  · have hx := huΨ (interior_subset hz)
    simp only [transportCauchyRiemannStructure_apply, Ψ.left_inv hx]
    rw [← ContinuousLinearMap.comp_assoc, fderiv_symm_comp_fderiv Ψ hΨ hΨs hx,
      ContinuousLinearMap.id_comp]
  · have hx := huΨ (interior_subset hz)
    have := congrArg (fun L : V →L[ℝ] V => L (η z (u z))) (fderiv_symm_comp_fderiv Ψ hΨ hΨs hx)
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] at this
    simp only [transportCauchyRiemannTerm_apply, Ψ.left_inv hx, this]

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
  rw [hDz, hηz, ← hz]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.id_apply]
  rw [hsplit, hsplit, map_add, hJz', show ((0 : ℂ), D z 1 + J z (u z) (D z I)) =
    ((0 : ℂ), D z 1) + (0, J z (u z) (D z I)) by simp, map_add]
  abel

/-! ### Checks -/

section Checks

/-- The derivative of complex conjugation, as a real-linear map, applies conjugation. -/
private theorem fderiv_conj_apply' (z w : ℂ) : fderiv ℝ conj z w = conj w := by
  have hconj : (conj : ℂ → ℂ) = conjCLE := funext fun x => (conjCLE_apply x).symm
  rw [hconj, conjCLE.fderiv, ContinuousLinearEquiv.coe_coe, conjCLE_apply]

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
      simp [fderiv_conj_apply'])
    (Filter.Eventually.of_forall fun z => by simp [fderiv_conj_apply'])

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
  have hS : transportCauchyRiemannStructure A.toHomeomorph.toOpenPartialHomeomorph J =
      fun z y => (A : V →L[ℝ] W).comp ((J z (A.symm y)).comp (A.symm : W →L[ℝ] V)) := by
    funext z y
    rw [transportCauchyRiemannStructure_apply, e1, e2, A.fderiv, A.symm.fderiv]
  have hT : transportCauchyRiemannTerm A.toHomeomorph.toOpenPartialHomeomorph η =
      fun z y => A (η z (A.symm y)) := by
    funext z y
    rw [transportCauchyRiemannTerm_apply, e1, e2, A.fderiv, ContinuousLinearEquiv.coe_coe]
  rwa [hS, hT, e1] at h

end Checks

end TauCeti
