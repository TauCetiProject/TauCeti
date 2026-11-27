/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Cotangent.Bundle.EulerField
public import TauCeti.Geometry.Symplectic.Cotangent.Bundle.GeodesicSpray
public import TauCeti.Geometry.Symplectic.Liouville.ClosedCharacteristic

/-!
# Almost existence near the unit cosphere bundle and contractible closed geodesics

Let `M` be a Riemannian manifold without boundary, with cotangent bundle `T*M`, canonical
symplectic form `ω = -dλ` and kinetic energy `K(q, p) = ‖p‖² / 2`
(`TauCeti.CotangentBundle.kineticEnergy`). The unit cosphere bundle `S*M` is the level `K = 1/2`
(`TauCeti.CotangentBundle.kineticEnergy_eq_half_iff_mem_cosphereBundle`), and the Hamiltonian flow
of `K` is the cogeodesic flow. Below, names without a namespace are in `TauCeti.CotangentBundle`.

The radial field `Z = p ∂_p` is a complete Liouville field of `ω`, with flow `ψ_t(z) = e^t z`
(`TauCeti.flowOf_vectorBundleEulerField`), and `K` is homogeneous of degree two in the fibres:
`K ∘ ψ_t = e^(2t) K` (`kineticEnergy_flowOf_vectorBundleEulerField`). Since `ψ_t^* ω = e^t ω`,
the flow carries the characteristic foliation of each level onto that of the level it is mapped
to, so all positive levels of `K`, the cosphere bundles of all radii, carry closed characteristics
contractible in `T*M` together (`hasContractibleClosedCharacteristic_kineticEnergy_mul_iff`).
Every positive value of `K` is regular (`isRegularValue_kineticEnergy`), so if some positive level
has the contractible almost existence property in `T*M`, some nearby level carries a contractible
closed characteristic, and hence so does every positive level, `S*M` included
(`hasContractibleClosedCharacteristic_kineticEnergy_of_hasContractibleAlmostExistence`). This is
the contact-type step of Hofer and Zehnder, from almost existence to existence, for the model
hypersurface `S*M`.

A closed characteristic of a level of `K` is a periodic orbit of the cogeodesic flow, and its
projection to `M` is a geodesic
(`TauCeti.isGeodesicCurveOn_proj_of_isMIntegralCurveOn_kineticEnergy`). The orbit is the Legendre
transform of the velocity of its projection
(`TauCeti.eq_legendreMap_curveVelocityLiftWithin_of_isMIntegralCurveOn_kineticEnergy`), so the
projection is not constant, and a null-homotopy of the orbit in `T*M` projects to one of the
geodesic in `M`. Hence a contractible closed characteristic on a level of `K` gives a
nonconstant closed geodesic of `M` contractible in `M`
(`exists_isGeodesicCurve_of_hasContractibleClosedCharacteristic_kineticEnergy`), and almost
existence near `S*M` gives one
(`exists_isGeodesicCurve_of_hasContractibleAlmostExistence_kineticEnergy`).

## Main results

In the namespace `TauCeti.CotangentBundle`:

* `hasContractibleClosedCharacteristic_kineticEnergy_mul_iff`: the positive levels of `K` carry
  contractible closed characteristics together.
* `hasContractibleClosedCharacteristic_kineticEnergy_of_hasContractibleAlmostExistence`: almost
  existence at a positive level gives contractible closed characteristics on every positive level,
  in particular on `S*M`.
* `exists_isGeodesicCurve_of_hasContractibleClosedCharacteristic_kineticEnergy`: a contractible
  closed characteristic of a level of `K` projects to a nonconstant closed geodesic contractible
  in `M`.
* `exists_isGeodesicCurve_of_hasContractibleAlmostExistence_kineticEnergy`: almost existence near
  the cosphere bundle gives a contractible closed geodesic.

## References

* H. Hofer, E. Zehnder, *Symplectic Invariants and Hamiltonian Dynamics*, Birkhäuser, 1994,
  Section 4.2 (closed characteristics on hypersurfaces of contact type from almost existence).
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, §1.2 and the remark before Corollary E.
* G. P. Paternain, *Geodesic Flows*, Progress in Mathematics 180, Birkhäuser, 1999, Chapter 1
  (the geodesic flow as the Hamiltonian flow of the kinetic energy).
-/

public section

noncomputable section

open Bundle Function Set
open scoped Manifold ContDiff

namespace TauCeti

namespace CotangentBundle

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]

/-! ### Closed characteristics of the levels of the kinetic energy -/

/-- Flowing along the radial field for time `t` carries the closed characteristics of the level
`K = c` to those of the level `K = e^(2t) c`. -/
private theorem hasContractibleClosedCharacteristic_kineticEnergy_exp_mul (t : ℝ) {c : ℝ}
    (h : (symplecticForm I M).HasContractibleClosedCharacteristic univ (kineticEnergy I M) c) :
    (symplecticForm I M).HasContractibleClosedCharacteristic univ (kineticEnergy I M)
      (Real.exp (2 * t) * c) := by
  have hZ := contMDiff_vectorBundleEulerField (I := I) (V := fun x : M ↦ TangentSpace I x →L[ℝ] ℝ)
    (F := E →L[ℝ] ℝ) (m := ∞)
  have hc := isCompleteVectorField_vectorBundleEulerField (I := I)
    (V := fun x : M ↦ TangentSpace I x →L[ℝ] ℝ) (F := E →L[ℝ] ℝ)
  have hK : MDifferentiable (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) 𝓘(ℝ) (kineticEnergy I M) :=
    contMDiff_kineticEnergy.mdifferentiable one_ne_zero
  -- The level `e^(2t) c` of `K` is the level `e^(2t) c` of `e^(2t) K = K ∘ ψ_t`.
  have hcomp : (fun s ↦ Real.exp (2 * t) * s) ∘ kineticEnergy I M =
      kineticEnergy I M ∘ flowOf (vectorBundleEulerField I) (-(-t)) := by
    funext z
    simp only [comp_apply, neg_neg, kineticEnergy_flowOf_vectorBundleEulerField]
  have h' := h.comp (φ := fun s ↦ Real.exp (2 * t) * s) (by simp [(Real.exp_pos _).ne'])
    fun z _ ↦ hK z
  rw [hcomp] at h'
  rw [← IsLiouvilleVectorField.hasContractibleClosedCharacteristic_image_flowOf_iff
      isLiouvilleVectorField_vectorBundleEulerField isSymplectic_symplecticForm.isNondegenerate hc
      hZ (-t) fun z _ ↦ hK z,
    image_univ_of_surjective (flowOf_surjective (hZ.of_le (by simp)) hc (-t))]
  exact h'

/-- **The positive levels of the kinetic energy carry closed characteristics together.** For
`a > 0`, the level `K = a c` carries a closed characteristic contractible in `T*M` exactly when
the level `K = c` does: the radial flow, which rescales `ω` by a constant, carries one level onto
the other. -/
theorem hasContractibleClosedCharacteristic_kineticEnergy_mul_iff {a : ℝ} (ha : 0 < a) {c : ℝ} :
    (symplecticForm I M).HasContractibleClosedCharacteristic univ (kineticEnergy I M) (a * c) ↔
      (symplecticForm I M).HasContractibleClosedCharacteristic univ (kineticEnergy I M) c := by
  have hexp : Real.exp (2 * (Real.log a / 2)) = a := by
    rw [mul_div_cancel₀ _ two_ne_zero, Real.exp_log ha]
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · have h' := hasContractibleClosedCharacteristic_kineticEnergy_exp_mul (-(Real.log a / 2)) h
    rwa [← mul_assoc, mul_neg, Real.exp_neg, hexp, inv_mul_cancel₀ ha.ne', one_mul] at h'
  · have h' := hasContractibleClosedCharacteristic_kineticEnergy_exp_mul (Real.log a / 2) h
    rwa [hexp] at h'

/-- **Almost existence near a cosphere bundle gives closed characteristics on every cosphere
bundle.** If a positive level of the kinetic energy has the contractible almost existence property
in `T*M`, then every positive level carries a closed characteristic contractible in `T*M`; for the
level `K = 1/2` this is a closed characteristic of the unit cosphere bundle `S*M`. -/
theorem hasContractibleClosedCharacteristic_kineticEnergy_of_hasContractibleAlmostExistence
    {c : ℝ} (hc : 0 < c)
    (h : (symplecticForm I M).HasContractibleAlmostExistence univ (kineticEnergy I M) c)
    {c' : ℝ} (hc' : 0 < c') :
    (symplecticForm I M).HasContractibleClosedCharacteristic univ (kineticEnergy I M) c' := by
  -- Every value in `(0, 2c)` is regular, so some level in that band carries one.
  obtain ⟨c'', hc'', h''⟩ := h.exists_hasContractibleClosedCharacteristic hc
    fun b hb ↦ isRegularValue_kineticEnergy (by linarith [hb.1])
  have hc''0 : 0 < c'' := by linarith [hc''.1]
  rw [← div_mul_cancel₀ c' hc''0.ne']
  exact (hasContractibleClosedCharacteristic_kineticEnergy_mul_iff (div_pos hc' hc''0)).2 h''

/-! ### Contractible closed geodesics -/

omit [T2Space M] in
/-- **A contractible closed characteristic of a level of the kinetic energy gives a contractible
closed geodesic.** If a level of `K` carries a closed characteristic contractible in `T*M`, then
`M` carries a nonconstant geodesic `γ`, periodic of some period `T > 0`, whose loop `ℝ/Tℤ → M` is
null-homotopic. The geodesic is the projection of the closed characteristic, a periodic orbit of
the cogeodesic flow. -/
theorem exists_isGeodesicCurve_of_hasContractibleClosedCharacteristic_kineticEnergy {c : ℝ}
    (h : (symplecticForm I M).HasContractibleClosedCharacteristic univ (kineticEnergy I M) c) :
    ∃ (T : ℝ) (γ : ℝ → M), 0 < T ∧ Manifold.IsGeodesicCurve I γ ∧ Periodic γ T ∧
      (∃ t, γ t ≠ γ 0) ∧ ∃ g : C(AddCircle T, M), g.Nullhomotopic ∧ ∀ t : ℝ, g t = γ t := by
  obtain ⟨T, δ, hT, hδ, hper, hne, -, g, hg, hgδ⟩ :=
    SmoothTwoForm.hasContractibleClosedCharacteristic_iff.1 h
  have hδu := hδ.isMIntegralCurveOn univ
  refine ⟨T, fun t ↦ (δ t).proj, hT,
    Manifold.isGeodesicCurveOn_univ.1
      (isGeodesicCurveOn_proj_of_isMIntegralCurveOn_kineticEnergy uniqueDiffOn_univ hδu),
    hper.comp _, ?_, ?_⟩
  · -- The orbit is the Legendre transform of the velocity of its projection, so a constant
    -- projection would make the orbit constant.
    by_contra! hconst
    obtain ⟨t, ht⟩ := hne
    have hγ : (fun r ↦ (δ r).proj) = fun _ ↦ (δ 0).proj := funext hconst
    have hleg (r : ℝ) := eq_legendreMap_curveVelocityLiftWithin_of_isMIntegralCurveOn_kineticEnergy
      uniqueDiffWithinAt_univ hδu (mem_univ r)
    refine ht ?_
    rw [hleg t, hleg 0, hγ]
    simp only [Manifold.curveVelocityLiftWithin_apply, Manifold.curveVelocityWithin_const]
  · -- A null-homotopy of the orbit in `T*M` projects to one of the geodesic in `M`.
    let p : C(CotangentBundle I M, M) := ⟨TotalSpace.proj, FiberBundle.continuous_proj _ _⟩
    refine ⟨(p.comp ⟨Subtype.val, continuous_subtypeVal⟩).comp g, hg.comp_right _, fun t ↦ ?_⟩
    simp [p, hgδ t]

/-- **Almost existence near the unit cosphere bundle gives a contractible closed geodesic.** If a
positive level of the kinetic energy, for instance the unit cosphere bundle `S*M = {K = 1/2}`, has
the contractible almost existence property in `T*M`, then `M` carries a nonconstant closed
geodesic whose loop is null-homotopic in `M`. -/
theorem exists_isGeodesicCurve_of_hasContractibleAlmostExistence_kineticEnergy {c : ℝ}
    (hc : 0 < c)
    (h : (symplecticForm I M).HasContractibleAlmostExistence univ (kineticEnergy I M) c) :
    ∃ (T : ℝ) (γ : ℝ → M), 0 < T ∧ Manifold.IsGeodesicCurve I γ ∧ Periodic γ T ∧
      (∃ t, γ t ≠ γ 0) ∧ ∃ g : C(AddCircle T, M), g.Nullhomotopic ∧ ∀ t : ℝ, g t = γ t :=
  exists_isGeodesicCurve_of_hasContractibleClosedCharacteristic_kineticEnergy
    (hasContractibleClosedCharacteristic_kineticEnergy_of_hasContractibleAlmostExistence hc h hc)

end CotangentBundle

end TauCeti
