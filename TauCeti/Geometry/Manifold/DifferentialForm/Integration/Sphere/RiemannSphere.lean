/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DeRham.Integration.Bijective
public import TauCeti.Geometry.Manifold.DifferentialForm.Integration.FubiniStudySphere
public import TauCeti.Geometry.Manifold.DifferentialForm.Integration.RiemannSphere
public import TauCeti.Geometry.Manifold.DifferentialForm.Integration.Sphere.Hurewicz

/-!
# The area of a map of the Riemann sphere is a homological period

Let `M` be a compact boundaryless manifold, `φ` a smooth closed real two-form on `M`, and
`u : OnePoint ℂ → M` a smooth map of the Riemann sphere. This file proves that the area
`∫_{S²} u^*φ`, the integral over the Riemann sphere with the orientation of its complex structure,
is the integral of `φ` over the class `u_*[S²]` of `u` in the second homotopy group
`π₂(M, u ∞)` (`TauCeti.integralTopForm_mpullback_eq_sphereIntegral`), where `[S²]` is the class
of the standard sphere `TauCeti.riemannSphereSquare`. Read through the Hurewicz map, it is the value
`P(A)` on the homology class `A = u_*[S²] ∈ H₂(M; ℤ)` of any homomorphism `P : H₂(M; ℤ) → ℝ`
that extends the integrals of `φ` over spheres
(`TauCeti.integralTopForm_mpullback_eq_apply_singularHomologyFunctor_map`), and such a period `P`
exists (`TauCeti.exists_addMonoidHom_hurewiczIntHom_eq_sphereIntegralHom`); for a simply connected
`M` it is the integral of `φ` on `H₂(M; ℤ)`
(`TauCeti.integralTopForm_mpullback_eq_homologySphereIntegralHom`). For the symplectic
form of a closed symplectic manifold this is the identity `∫ u^*ω = ω(A)`: the symplectic area of
a sphere depends only on its homology class. With the energy identity it gives the energy of
pseudoholomorphic spheres (`TauCeti.SmoothTwoForm.energy_eq_sphereIntegral`).

The proof is a top-degree de Rham argument on the sphere. The Fubini–Study form `ω_FS` integrates
to `1` both over the Riemann sphere (`OnePoint.integralTopForm_fubiniStudyForm`) and over the class
of the standard sphere (`OnePoint.sphereIntegral_fubiniStudyForm_riemannSphereSquare`). With
`c = ∫_{S²} u^*φ`, the top form `u^*φ - c ω_FS` therefore has integral `0`, so it is exact
(`TauCeti.mem_exactCompactlySupportedForms_iff_integralTopForm_eq_zero`), and exact forms have
zero integral over every class of `π₂` (`TauCeti.sphereIntegral_mextDeriv`). Hence the integral of
`u^*φ` over `[S²]` is `c`, and by naturality (`TauCeti.sphereIntegral_mpullback`) it is the
integral of `φ` over `u_*[S²]`.

## Main results

* `TauCeti.integralTopForm_mpullback_eq_sphereIntegral`: `∫_{S²} u^*φ` is the integral of `φ`
  over the class `u_*[S²]` in `π₂(M, u ∞)`.
* `TauCeti.integralTopForm_mpullback_eq_apply_singularHomologyFunctor_map`: it is `P(u_*[S²])` for
  every homomorphism `P : H₂(M; ℤ) → ℝ` extending the integrals of `φ` over spheres.
* `TauCeti.integralTopForm_mpullback_eq_homologySphereIntegralHom`: for a simply connected `M`,
  `P` can be taken to be the integral of `φ` on `H₂(M; ℤ)`, `TauCeti.homologySphereIntegralHom`.

## References

* John M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., GTM 218, Springer, 2013, Chapter 17,
  section Cohomology with Compact Support (a top form on a compact connected oriented manifold is
  exact exactly when its integral vanishes).
* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., AMS
  Colloquium Publications 52, 2012, Section 2.2 (the energy of a pseudoholomorphic sphere is the
  symplectic area `ω(A)` of its homology class).
-/

public section

noncomputable section

open Module CategoryTheory
open scoped Manifold ContDiff TauCeti.ComplexManifold

namespace TauCeti

attribute [local instance] Complex.finrank_real_complex_fact

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]

section Sphere

variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [CompactSpace M]
  [T2Space M] {φ : SmoothForm I M ℝ 2}

/-- **The area of a map of the Riemann sphere is the integral over its class in `π₂`.** For a
smooth closed real two-form `φ` on a compact boundaryless manifold `M` and a smooth map
`u : OnePoint ℂ → M`, the integral of `u^*φ` over the Riemann sphere, with the orientation of its
complex structure, is the integral of `φ` over the class `u_*[S²] ∈ π₂(M, u ∞)` of the image of
the standard sphere `TauCeti.riemannSphereSquare`. -/
theorem integralTopForm_mpullback_eq_sphereIntegral (hφ : φ.IsClosed) {u : OnePoint ℂ → M}
    (hu : ContMDiff 𝓘(ℝ, ℂ) I ∞ u) :
    integralTopForm ((complexManifoldOrientation ℂ (OnePoint ℂ)).reindex
        (finCongr ((finrank_real_of_complex ℂ).symm.trans Complex.finrank_real_complex)))
      (mpullback 𝓘(ℝ, ℂ) I u φ.val) =
      sphereIntegral φ.val (u OnePoint.infty)
        (HomotopyGroup.map ⟨u, hu.continuous⟩ rfl ⟦riemannSphereSquare⟧) := by
  -- Name the class of the standard sphere, so that it is rewritten at the type `π₂`.
  set a : HomotopyGroup (Fin 2) (OnePoint ℂ) OnePoint.infty := ⟦riemannSphereSquare⟧ with ha
  set o := (complexManifoldOrientation ℂ (OnePoint ℂ)).reindex
    (finCongr ((finrank_real_of_complex ℂ).symm.trans Complex.finrank_real_complex))
  set ψ := SmoothForm.mpullback u hu φ
  have hψ : ψ.val = mpullback 𝓘(ℝ, ℂ) I u φ.val := SmoothForm.coe_mpullback u hu φ
  set c := integralTopForm o ψ.val
  -- The top form `u^*φ - c ω_FS` has integral `0`, so it is exact: `u^*φ = dα + c ω_FS`.
  set θ := ψ + (-c) • OnePoint.fubiniStudyForm
  have hθ : θ.val = ψ.val + (-c) • OnePoint.fubiniStudyForm.val := by
    rw [SmoothForm.add_toRoughForm, SmoothForm.smul_toRoughForm]
  have hint : integralTopForm o θ.val = 0 := by
    rw [hθ, integralTopForm_add_of_compactSpace o (ψ.isSmoothForm.of_le (by simp))
        ((OnePoint.fubiniStudyForm.isSmoothForm.smul (-c)).of_le (by simp)),
      integralTopForm_smul, OnePoint.integralTopForm_fubiniStudyForm, mul_one, add_neg_cancel]
  obtain ⟨α, -, hα⟩ := Submodule.mem_map.1 <|
    (exactCompactlySupportedForms_succ (I := 𝓘(ℝ, ℂ)) (M := OnePoint ℂ) 1).le <|
      (mem_exactCompactlySupportedForms_iff_integralTopForm_eq_zero o
        ((mem_compactlySupportedForms _).2 (isClosed_tsupport _).isCompact)).2 hint
  have hdα : ψ.val = mextDeriv α.val + c • OnePoint.fubiniStudyForm.val := by
    rw [← mextDerivₗ_apply, hα, hθ, neg_smul, neg_add_cancel_right]
  -- The integral of `u^*φ` over the standard sphere is therefore `c`; by naturality it is the
  -- integral of `φ` over `u_*[S²]`.
  have key : sphereIntegral ψ.val OnePoint.infty a = c := by
    rw [hdα, sphereIntegral_add (isSmoothForm_mextDeriv α.isSmoothForm (by simp))
        ((OnePoint.fubiniStudyForm.isSmoothForm.smul c).of_le (by simp)),
      sphereIntegral_mextDeriv (α.isSmoothForm.of_le (by simp)), sphereIntegral_smul, ha,
      OnePoint.sphereIntegral_fubiniStudyForm_riemannSphereSquare, zero_add, smul_eq_mul, mul_one]
  have hnat := sphereIntegral_mpullback hu (φ.isSmoothForm.of_le (by simp))
    ((SmoothForm.isClosed_def φ).1 hφ) a
  rw [← hψ] at hnat ⊢
  exact key.symm.trans hnat

end Sphere

section Homology

open AlgebraicTopology HomotopyGroup
open scoped Topology

variable {M : Type} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [CompactSpace M]
  [T2Space M] {φ : SmoothForm I M ℝ 2}

/-- **The area of a map of the Riemann sphere is a homological period.** Let `φ` be a smooth closed
real two-form on a compact boundaryless manifold `M`, and `P : H₂(M; ℤ) → ℝ` a homomorphism that
takes the Hurewicz class of every sphere to the integral of `φ` over it. Then the area
`∫_{S²} u^*φ` of a smooth map `u : OnePoint ℂ → M` is `P(u_*[S²])`, where `[S²]` is the Hurewicz
class of the standard sphere `TauCeti.riemannSphereSquare`, which generates `H₂(OnePoint ℂ; ℤ)`
(`TauCeti.zmultiples_hurewiczIntHom_riemannSphereSquare`). -/
theorem integralTopForm_mpullback_eq_apply_singularHomologyFunctor_map (hφ : φ.IsClosed)
    {P : ((singularHomologyFunctor (ModuleCat.{0} ℤ) 2).obj (ModuleCat.of ℤ ℤ)).obj
      (TopCat.of M) →+ ℝ}
    (hP : ∀ (x : M) (a : Additive (π_ 2 M x)),
      P (hurewiczIntHom M x 1 a) = sphereIntegral φ.val x a.toMul)
    {u : OnePoint ℂ → M} (hu : ContMDiff 𝓘(ℝ, ℂ) I ∞ u) :
    integralTopForm ((complexManifoldOrientation ℂ (OnePoint ℂ)).reindex
        (finCongr ((finrank_real_of_complex ℂ).symm.trans Complex.finrank_real_complex)))
      (mpullback 𝓘(ℝ, ℂ) I u φ.val) =
      P ((((singularHomologyFunctor (ModuleCat.{0} ℤ) 2).obj (ModuleCat.of ℤ ℤ)).map
        (TopCat.ofHom ⟨u, hu.continuous⟩)).hom
          (hurewiczIntHom (OnePoint ℂ) OnePoint.infty 1
            (Additive.ofMul (⟦riemannSphereSquare⟧ : π_ 2 (OnePoint ℂ) OnePoint.infty)))) :=
  (integralTopForm_mpullback_eq_sphereIntegral hφ hu).trans <|
    (hP (u OnePoint.infty)
      (Additive.ofMul (map ⟨u, hu.continuous⟩ rfl ⟦riemannSphereSquare⟧))).symm.trans
        (congrArg P (hurewiczIntHom_map (n := 1) ⟨u, hu.continuous⟩ rfl ⟦riemannSphereSquare⟧))

/-- **The area of a map of the Riemann sphere into a simply connected manifold.** For a smooth
closed real two-form `φ` on a compact boundaryless simply connected manifold `M`, the area
`∫_{S²} u^*φ` of a smooth map `u : OnePoint ℂ → M` is the integral of `φ` on second homology
(`TauCeti.homologySphereIntegralHom`) evaluated at the class `u_*[S²] ∈ H₂(M; ℤ)`. -/
theorem integralTopForm_mpullback_eq_homologySphereIntegralHom [SimplyConnectedSpace M]
    (hφ : φ.IsClosed) {u : OnePoint ℂ → M} (hu : ContMDiff 𝓘(ℝ, ℂ) I ∞ u) :
    integralTopForm ((complexManifoldOrientation ℂ (OnePoint ℂ)).reindex
        (finCongr ((finrank_real_of_complex ℂ).symm.trans Complex.finrank_real_complex)))
      (mpullback 𝓘(ℝ, ℂ) I u φ.val) =
      homologySphereIntegralHom (φ.isSmoothForm.of_le (by simp))
        ((SmoothForm.isClosed_def φ).1 hφ)
        ((((singularHomologyFunctor (ModuleCat.{0} ℤ) 2).obj (ModuleCat.of ℤ ℤ)).map
          (TopCat.ofHom ⟨u, hu.continuous⟩)).hom
            (hurewiczIntHom (OnePoint ℂ) OnePoint.infty 1
              (Additive.ofMul (⟦riemannSphereSquare⟧ : π_ 2 (OnePoint ℂ) OnePoint.infty)))) :=
  integralTopForm_mpullback_eq_apply_singularHomologyFunctor_map hφ
    (fun x a ↦ (homologySphereIntegralHom_hurewiczIntHom _ _ x a).trans
      (sphereIntegralHom_apply _ _ a)) hu

end Homology

end TauCeti
