/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DeRham.DegreeZero
public import TauCeti.Geometry.Manifold.DeRham.ExtendByZero
public import TauCeti.Geometry.Manifold.DeRham.Wedge
public import TauCeti.Geometry.Manifold.DifferentialForm.Integration.TopForm
public import TauCeti.Geometry.Manifold.Orientation.OpenSubset
import Mathlib.LinearAlgebra.Isomorphisms
import TauCeti.Geometry.Manifold.DifferentialForm.Integration.BoundarylessStokes
import TauCeti.Geometry.Manifold.DifferentialForm.Integration.OpenSubset
import TauCeti.Geometry.Manifold.DifferentialForm.Integration.Regularity
import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.Smooth

/-!
# Integration on compactly supported cohomology and the Poincaré pairing

On an oriented boundaryless manifold, Stokes' theorem says that the exterior derivative of a
compactly supported form integrates to zero. Hence integration of compactly supported closed
top forms descends to a linear map `∫_M : H^n_c(M) → ℝ` on compactly supported de Rham
cohomology, computed on classes by integrating a representative.

Composing it with the wedge product `H^k_dR(M) → H^l_c(M) → H^(k+l)_c(M)` gives the Poincaré
pairing `⟨[φ], [ψ]⟩ = ∫_M φ ∧ ψ` between de Rham cohomology and compactly supported de Rham
cohomology in complementary degrees `k + l = n`. Poincaré duality, proved in
`TauCeti.Geometry.Manifold.DeRham.PoincareDuality`, asserts that this pairing identifies
`H^k_dR(M)` with the dual of `H^l_c(M)`.

Both maps need the manifold to be boundaryless. On `M = [0, 1]` the form `dx` is exact, yet the
representative formula pairs it with the class of the constant function `1` to give
`∫₀¹ dx = 1`; integration does not descend to cohomology there.

## Main definitions and results

* `TauCeti.integralTopForm_eq_zero_of_mem_exactCompactlySupportedForms`: on a boundaryless
  manifold, the exterior derivative of a compactly supported form integrates to zero.
* `TauCeti.compactlySupportedDeRhamCohomology.integral`: integration `H^n_c(M) → ℝ`, computed on
  classes by `TauCeti.compactlySupportedDeRhamCohomology.integral_mk`.
* `TauCeti.compactlySupportedDeRhamCohomology.integral_extendByZero` and
  `TauCeti.compactlySupportedDeRhamCohomology.integral_extendByZeroTop`: integration commutes with
  extension by zero `H^n_c(U) → H^n_c(W)` along open subsets `U ≤ W`, and with extension by zero
  `H^n_c(U) → H^n_c(M)` into the whole manifold.
* `TauCeti.compactlySupportedDeRhamCohomology.integral_map_diffeomorph`: integration is
  preserved by orientation-preserving diffeomorphisms.
* `TauCeti.compactlySupportedDeRhamCohomology.wedge_map` and
  `TauCeti.compactlySupportedDeRhamCohomology.wedge_extendByZero`: compatibility of the wedge
  product with smooth proper maps and extension by zero.
* `TauCeti.poincarePairing`: the pairing `H^k_dR(M) → H^l_c(M) → ℝ`, the wedge product followed
  by integration (`TauCeti.poincarePairing_apply`), computed on classes by
  `TauCeti.poincarePairing_mk`, compatible with orientation-preserving diffeomorphisms
  (`TauCeti.poincarePairing_map_diffeomorph`), extension by zero
  (`TauCeti.poincarePairing_extendByZero`, `TauCeti.poincarePairing_extendByZeroTop`), constant
  classes (`TauCeti.poincarePairing_const_left`), and graded factor swap
  (`TauCeti.poincarePairing_comm_toDeRhamCohomology`).
* `TauCeti.integralTopForm_wedge_self_eq_of_sub_mem_exactForms`: in even middle degree, the
  integral `∫_M φ ∧ φ` of a compactly supported closed form depends only on its de Rham class.

## References

* John M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Chapter 17, the integration map on
  compactly supported top-degree cohomology, and Problems 18-6 to 18-8 (Poincaré duality).
* R. Bott and L. W. Tu, *Differential Forms in Algebraic Topology*, GTM 82, §5.
-/

public section

noncomputable section

open TopologicalSpace
open scoped ContDiff Manifold

namespace TauCeti

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M] [IsManifold I ∞ M] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M] {k l n : ℕ}

/-- On an oriented boundaryless manifold, the exterior derivative of a compactly supported smooth
form integrates to zero. This is Stokes' theorem for compactly supported exact top forms. -/
theorem integralTopForm_eq_zero_of_mem_exactCompactlySupportedForms
    (o : Manifold.Orientation I M (Fin n)) {φ : SmoothForm I M ℝ n}
    (hφ : φ ∈ exactCompactlySupportedForms I M n) : integralTopForm o φ.1 = 0 := by
  cases n with
  | zero =>
    rw [exactCompactlySupportedForms_zero, Submodule.mem_bot] at hφ
    rw [hφ]
    exact integralTopForm_zero o
  | succ n =>
    rw [exactCompactlySupportedForms_succ, Submodule.mem_map] at hφ
    obtain ⟨β, hβ, rfl⟩ := hφ
    rw [mextDerivₗ_apply]
    exact integralTopForm_mextDeriv_eq_zero o (β.isSmoothForm.of_le (by simp))
      ((mem_compactlySupportedForms I).mp hβ)

namespace compactlySupportedDeRhamCohomology

/-- Integration of compactly supported closed top forms, as a linear map. -/
private def integralClosedForms (o : Manifold.Orientation I M (Fin n)) :
    compactlySupportedClosedForms I M n →ₗ[ℝ] ℝ where
  toFun φ := integralTopForm o φ.1.1
  map_add' φ ψ := integralTopForm_add o (φ.1.isSmoothForm.of_le (by simp))
    (ψ.1.isSmoothForm.of_le (by simp))
    ((mem_compactlySupportedForms I).mp ((mem_compactlySupportedClosedForms I).mp φ.2).1)
    ((mem_compactlySupportedForms I).mp ((mem_compactlySupportedClosedForms I).mp ψ.2).1)
  map_smul' c φ := integralTopForm_smul o c φ.1.1

/-- Compactly supported exact top forms are killed by integration. -/
private theorem ker_mk_le_ker_integralClosedForms (o : Manifold.Orientation I M (Fin n)) :
    LinearMap.ker (mk I (M := M) n) ≤ LinearMap.ker (integralClosedForms o) := by
  intro φ hφ
  rw [LinearMap.mem_ker, mk_eq_zero_iff] at hφ
  exact integralTopForm_eq_zero_of_mem_exactCompactlySupportedForms o hφ

/-- Integration `H^n_c(M) → ℝ` over an oriented boundaryless manifold, induced by integrating
compactly supported closed top forms. -/
def integral (o : Manifold.Orientation I M (Fin n)) :
    compactlySupportedDeRhamCohomology I M n →ₗ[ℝ] ℝ :=
  LinearMap.liftOfSurjective (R := ℝ) (M := compactlySupportedClosedForms I M n)
    (M₂ := compactlySupportedDeRhamCohomology I M n) (M₃ := ℝ) (f := mk I (M := M) n)
    (mk_surjective I n) ⟨integralClosedForms o, ker_mk_le_ker_integralClosedForms o⟩

/-- The integral of the class of a compactly supported closed top form is the integral of the
form. -/
@[simp]
theorem integral_mk (o : Manifold.Orientation I M (Fin n))
    (φ : compactlySupportedClosedForms I M n) :
    integral o (mk I n φ) = integralTopForm o φ.1.1 :=
  LinearMap.equivOfSurjective_apply _ _

/-- Reversing the orientation negates integration on compactly supported cohomology. -/
@[simp]
theorem integral_neg (o : Manifold.Orientation I M (Fin n)) : integral (-o) = -integral o := by
  refine LinearMap.ext fun x ↦ ?_
  obtain ⟨φ, rfl⟩ := mk_surjective I n x
  rw [LinearMap.neg_apply, integral_mk, integral_mk, integralTopForm_neg]

omit [SigmaCompactSpace M] in
/-- Integration on compactly supported cohomology commutes with extension by zero: for open
subsets `U ≤ W`, `∫_W ext x = ∫_U x` for the orientations restricted from `M`. -/
@[simp]
theorem integral_extendByZero (o : Manifold.Orientation I M (Fin n)) {U W : Opens M}
    [SigmaCompactSpace U] [SigmaCompactSpace W] (h : U ≤ W)
    (x : compactlySupportedDeRhamCohomology I U n) :
    integral (o.restrict W) (extendByZero h n x) = integral (o.restrict U) x := by
  obtain ⟨φ, rfl⟩ := mk_surjective I n x
  rw [extendByZero_mk, integral_mk, integral_mk, compactlySupportedClosedForms.coe_extendByZero]
  exact integralTopForm_extendByZero o h ((mem_compactlySupportedForms I).mp
    ((mem_compactlySupportedClosedForms I).mp φ.2).1)

/-- Identifying the top open subset with the ambient manifold preserves integration on
compactly supported cohomology, with the restricted orientation. -/
theorem integral_equivOfDiffeomorph_ofTop (o : Manifold.Orientation I M (Fin n))
    (c : compactlySupportedDeRhamCohomology I M n) :
    integral (o.restrict ⊤) (equivOfDiffeomorph (Diffeomorph.ofTop ⊤ rfl) n c) =
      integral o c := by
  let Φ : (⊤ : Opens M) ≃ₘ⟮I, I⟯ M := Diffeomorph.ofTop ⊤ rfl
  obtain ⟨φ, rfl⟩ := mk_surjective I n c
  have h : integralTopForm (o.restrict ⊤) (mpullback I I Φ φ.1.1) = integralTopForm o φ.1.1 := by
    rw [Diffeomorph.coe_ofTop]
    exact integralTopForm_mpullback_subtypeVal o ⊤ (by simp)
  rw [equivOfDiffeomorph_mk, integral_mk, integral_mk, ← h]
  exact congrArg _ (compactlySupportedClosedForms.coe_coe_mpullback _ _ _ n φ)

/-- Integration on compactly supported cohomology commutes with extension by zero from an open
subset `U` into `M`: `∫_M ext x = ∫_U x` for the orientation restricted to `U`. -/
@[simp]
theorem integral_extendByZeroTop (o : Manifold.Orientation I M (Fin n)) (U : Opens M)
    [SigmaCompactSpace U] (x : compactlySupportedDeRhamCohomology I U n) :
    integral o (extendByZeroTop U n x) = integral (o.restrict U) x := by
  rw [← integral_extendByZero o (le_top : U ≤ ⊤), ← equivOfDiffeomorph_extendByZeroTop,
    integral_equivOfDiffeomorph_ofTop]

end compactlySupportedDeRhamCohomology

omit [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
/-- Reindexing the tangent tuple along `h : m = n` transports `integralTopForm` to the reindexed
orientation `o.reindex (finCongr h)`. -/
theorem integralTopForm_congr_cast {m n : ℕ} (h : m = n) (o : Manifold.Orientation I M (Fin m))
    (φ : RoughForm I M ℝ m) (ψ : RoughForm I M ℝ n)
    (hφψ : ∀ x (v : Fin m → TangentSpace I x), φ x v = ψ x (v ∘ Fin.cast h.symm)) :
    integralTopForm o φ = integralTopForm (o.reindex (finCongr h)) ψ := by
  subst h
  have ho : o.reindex (finCongr rfl) = o := by
    apply Manifold.Orientation.ext
    intro x
    rw [Manifold.Orientation.orientationAt_reindex, finCongr_refl, _root_.Orientation.reindex_refl,
      Equiv.refl_apply]
  have hφ : φ = ψ := funext fun x ↦ ContinuousAlternatingMap.ext (hφψ x)
  rw [ho, hφ]

namespace compactlySupportedDeRhamCohomology

/-- An orientation-preserving diffeomorphism preserves integration on compactly supported
cohomology. No integrability hypothesis is needed: representatives are smooth and compactly
supported. The target orientation must be specified explicitly, so this is not a simp lemma. -/
theorem integral_map_diffeomorph
    {E' H' N : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
    [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'}
    [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J ∞ N]
    [BoundarylessManifold J N] [T2Space N] [SigmaCompactSpace N]
    (o : Manifold.Orientation I M (Fin n)) (o' : Manifold.Orientation J N (Fin n))
    (Φ : M ≃ₘ⟮I, J⟯ N) (hΦ : ∀ x, o.IsOrientationPreservingAt o' Φ x)
    (c : compactlySupportedDeRhamCohomology J N n) :
    integral o (map Φ Φ.contMDiff
      (by simpa only [Diffeomorph.coe_toHomeomorph] using Φ.toHomeomorph.isProperMap) n c) =
      integral o' c := by
  obtain ⟨φ, rfl⟩ := mk_surjective J n c
  rw [map_mk, integral_mk, integral_mk, compactlySupportedClosedForms.coe_mpullback,
    SmoothForm.coe_mpullback]
  simpa only [Diffeomorph.coe_toHomeomorph] using
    Φ.toHomeomorph.isOpenEmbedding.integralTopForm_mpullback_of_isOrientationPreservingAt
      hΦ (fun y _ ↦ ⟨Φ.symm y, Φ.apply_symm_apply y⟩)

omit [FiniteDimensional ℝ E] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
/-- Pullback along a smooth proper map commutes with the wedge product of de Rham classes with
compactly supported classes. -/
theorem wedge_map {E' H' N : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'} [TopologicalSpace N] [ChartedSpace H' N]
    [IsManifold J ∞ N] (f : M → N) (hf : ContMDiff I J ∞ f) (hp : IsProperMap f)
    (x : deRhamCohomology J N k) (y : compactlySupportedDeRhamCohomology J N l) :
    map f hf hp (k + l) (wedge J N k l x y) =
      wedge I M k l (deRhamCohomology.map f hf k x) (map f hf hp l y) := by
  obtain ⟨φ, rfl⟩ := deRhamCohomology.mk_surjective J k x
  obtain ⟨ψ, rfl⟩ := mk_surjective J l y
  rw [wedge_mk, map_mk, deRhamCohomology.map_mk, map_mk, wedge_mk]
  congr 1
  apply Subtype.ext
  simp only [compactlySupportedClosedForms.coe_mpullback, closedForms.coe_mpullback,
    SmoothForm.mpullback_wedge]

omit [FiniteDimensional ℝ E] [BoundarylessManifold I M] [SigmaCompactSpace M] in
/-- Extension by zero along `h : U ≤ W` intertwines the wedge product with restriction on de Rham
cohomology: `ext (x|_U ∧ y) = x ∧ ext y`. -/
theorem wedge_extendByZero {U W : Opens M} (h : U ≤ W) (x : deRhamCohomology I W k)
    (y : compactlySupportedDeRhamCohomology I U l) :
    extendByZero h (k + l)
        (wedge I U k l (deRhamCohomology.map (Opens.inclusion h) (contMDiff_inclusion h) k x) y) =
      wedge I W k l x (extendByZero h l y) := by
  obtain ⟨φ, rfl⟩ := deRhamCohomology.mk_surjective I k x
  obtain ⟨ψ, rfl⟩ := mk_surjective I l y
  rw [deRhamCohomology.map_mk, wedge_mk, extendByZero_mk, extendByZero_mk, wedge_mk]
  congr 1
  apply Subtype.ext
  apply Subtype.ext
  rw [compactlySupportedClosedForms.coe_extendByZero, SmoothForm.coe_wedge, SmoothForm.coe_wedge,
    closedForms.coe_mpullback, SmoothForm.coe_mpullback,
    compactlySupportedClosedForms.coe_extendByZero]
  funext z
  by_cases hz : (z : M) ∈ U
  · obtain ⟨z, rfl⟩ : ∃ z' : U, Opens.inclusion h z' = z := ⟨⟨z, hz⟩, rfl⟩
    rw [RoughForm.extendByZero_inclusion, ← mpullback_inclusion_apply h (RoughForm.wedge φ.1.1 _),
      mpullback_wedge, RoughForm.mpullback_inclusion_extendByZero]
  · rw [RoughForm.extendByZero_apply_of_notMem _ hz, RoughForm.wedge_def,
      RoughForm.wedgeWith_apply', RoughForm.extendByZero_apply_of_notMem _ hz,
      ContinuousAlternatingMap.pairedWedge_zero_right]

end compactlySupportedDeRhamCohomology

variable (I M) in
/-- The Poincaré pairing `H^k_dR(M) → H^l_c(M) → ℝ` on an oriented boundaryless manifold of
dimension `k + l`, sending classes `[φ]` and `[ψ]` to `∫_M φ ∧ ψ`. It is the wedge product
`H^k_dR(M) → H^l_c(M) → H^(k+l)_c(M)` followed by integration. -/
def poincarePairing (o : Manifold.Orientation I M (Fin (k + l))) :
    deRhamCohomology I M k →ₗ[ℝ] compactlySupportedDeRhamCohomology I M l →ₗ[ℝ] ℝ :=
  (compactlySupportedDeRhamCohomology.wedge I M k l).compr₂
    (compactlySupportedDeRhamCohomology.integral o)

/-- The Poincaré pairing of two classes is the integral of their wedge product. -/
theorem poincarePairing_apply (o : Manifold.Orientation I M (Fin (k + l)))
    (x : deRhamCohomology I M k) (y : compactlySupportedDeRhamCohomology I M l) :
    poincarePairing I M o x y =
      compactlySupportedDeRhamCohomology.integral o
        (compactlySupportedDeRhamCohomology.wedge I M k l x y) :=
  (rfl)

/-- The Poincaré pairing of the classes of a closed form `φ` and a compactly supported closed
form `ψ` is `∫_M φ ∧ ψ`. -/
@[simp]
theorem poincarePairing_mk (o : Manifold.Orientation I M (Fin (k + l)))
    (φ : closedForms I M k) (ψ : compactlySupportedClosedForms I M l) :
    poincarePairing I M o (deRhamCohomology.mk I k φ)
        (compactlySupportedDeRhamCohomology.mk I l ψ) =
      integralTopForm o (RoughForm.wedge (φ.1 : RoughForm I M ℝ k) ψ.1.1) := by
  rw [poincarePairing_apply, compactlySupportedDeRhamCohomology.wedge_mk,
    compactlySupportedDeRhamCohomology.integral_mk, SmoothForm.coe_wedge]

/-- Reversing the orientation negates the Poincaré pairing. -/
@[simp]
theorem poincarePairing_neg (o : Manifold.Orientation I M (Fin (k + l))) :
    poincarePairing I M (-o) = -poincarePairing I M o := by
  ext x y
  rw [poincarePairing_apply, compactlySupportedDeRhamCohomology.integral_neg,
    LinearMap.neg_apply, LinearMap.neg_apply, LinearMap.neg_apply, poincarePairing_apply]

/-- An orientation-preserving diffeomorphism preserves the Poincaré pairing. -/
theorem poincarePairing_map_diffeomorph
    {E' H' N : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
    [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'}
    [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J ∞ N]
    [BoundarylessManifold J N] [T2Space N] [SigmaCompactSpace N]
    (o : Manifold.Orientation I M (Fin (k + l))) (o' : Manifold.Orientation J N (Fin (k + l)))
    (Φ : M ≃ₘ⟮I, J⟯ N) (hΦ : ∀ x, o.IsOrientationPreservingAt o' Φ x)
    (x : deRhamCohomology J N k) (y : compactlySupportedDeRhamCohomology J N l) :
    poincarePairing I M o (deRhamCohomology.map Φ Φ.contMDiff k x)
        (compactlySupportedDeRhamCohomology.map Φ Φ.contMDiff
          (by simpa only [Diffeomorph.coe_toHomeomorph] using Φ.toHomeomorph.isProperMap) l y) =
      poincarePairing J N o' x y := by
  rw [poincarePairing_apply, ← compactlySupportedDeRhamCohomology.wedge_map,
    compactlySupportedDeRhamCohomology.integral_map_diffeomorph o o' Φ hΦ, poincarePairing_apply]

omit [SigmaCompactSpace M] in
/-- The Poincaré pairing is adjoint to restriction and extension by zero along `h : U ≤ W`:
`⟨x, ext y⟩_W = ⟨x|_U, y⟩_U`. -/
@[simp]
theorem poincarePairing_extendByZero (o : Manifold.Orientation I M (Fin (k + l))) {U W : Opens M}
    [SigmaCompactSpace U] [SigmaCompactSpace W] (h : U ≤ W)
    (x : deRhamCohomology I W k) (y : compactlySupportedDeRhamCohomology I U l) :
    poincarePairing I W (o.restrict W) x
        (compactlySupportedDeRhamCohomology.extendByZero h l y) =
      poincarePairing I U (o.restrict U)
        (deRhamCohomology.map (Opens.inclusion h) (contMDiff_inclusion h) k x) y := by
  rw [poincarePairing_apply, ← compactlySupportedDeRhamCohomology.wedge_extendByZero h,
    compactlySupportedDeRhamCohomology.integral_extendByZero, poincarePairing_apply]

/-- The Poincaré pairing commutes with extension by zero from an open subset `U` into `M`:
`⟨x, ext y⟩_M = ⟨x|_U, y⟩_U`. -/
@[simp]
theorem poincarePairing_extendByZeroTop (o : Manifold.Orientation I M (Fin (k + l))) (U : Opens M)
    [SigmaCompactSpace U] (x : deRhamCohomology I M k)
    (y : compactlySupportedDeRhamCohomology I U l) :
    poincarePairing I M o x (compactlySupportedDeRhamCohomology.extendByZeroTop U l y) =
      poincarePairing I U (o.restrict U)
        (deRhamCohomology.map Subtype.val contMDiff_subtype_val k x) y := by
  let Φ : (⊤ : Opens M) ≃ₘ⟮I, I⟯ M := Diffeomorph.ofTop ⊤ rfl
  have hΦ : ∀ z : (⊤ : Opens M), (o.restrict ⊤).IsOrientationPreservingAt o Φ z := by
    intro z
    rw [Diffeomorph.coe_ofTop]
    exact o.isOrientationPreservingAt_restrict ⊤ z
  have hext : compactlySupportedDeRhamCohomology.map Φ Φ.contMDiff
      (by simpa only [Diffeomorph.coe_toHomeomorph] using Φ.toHomeomorph.isProperMap) l
      (compactlySupportedDeRhamCohomology.extendByZeroTop U l y) =
      compactlySupportedDeRhamCohomology.extendByZero (le_top : U ≤ ⊤) l y :=
    (compactlySupportedDeRhamCohomology.equivOfDiffeomorph_apply Φ l _).symm.trans
      (compactlySupportedDeRhamCohomology.equivOfDiffeomorph_extendByZeroTop U l y)
  have hcomp : ⇑Φ ∘ Opens.inclusion (le_top : U ≤ ⊤) = (Subtype.val : U → M) := by
    funext z
    rw [Function.comp_apply, Diffeomorph.coe_ofTop]
  rw [← poincarePairing_map_diffeomorph (o.restrict ⊤) o Φ hΦ x
      (compactlySupportedDeRhamCohomology.extendByZeroTop U l y),
    hext, poincarePairing_extendByZero o (le_top : U ≤ ⊤),
    ← LinearMap.comp_apply (deRhamCohomology.map (Opens.inclusion (le_top : U ≤ ⊤)) _ k),
    ← deRhamCohomology.map_comp]
  simp only [hcomp]

/-- Pairing the degree-zero class of a constant `r` with `y ∈ H^l_c(M)` multiplies the integral of
`y` by `r`. -/
@[simp]
theorem poincarePairing_const_left (o : Manifold.Orientation I M (Fin (0 + l))) (r : ℝ)
    (y : compactlySupportedDeRhamCohomology I M l) :
    poincarePairing I M o (deRhamCohomology.const I M r) y =
      r * compactlySupportedDeRhamCohomology.integral (o.reindex (finCongr (zero_add l))) y := by
  obtain ⟨ψ, rfl⟩ := compactlySupportedDeRhamCohomology.mk_surjective I l y
  rw [deRhamCohomology.const_eq_mk, poincarePairing_mk,
    compactlySupportedDeRhamCohomology.integral_mk, ← integralTopForm_smul]
  refine integralTopForm_congr_cast (zero_add l) o _ _ fun x v ↦ ?_
  rw [coe_closedFormsZeroEquiv_symm_apply, RoughForm.ofFunction_wedge_apply]
  rfl

/-- Pairing the unit constant class `[1] ∈ H⁰_dR(M)` with `y ∈ H^l_c(M)` evaluates the oriented
integral `∫_M y`. -/
theorem poincarePairing_const_one_left (o : Manifold.Orientation I M (Fin (0 + l)))
    (y : compactlySupportedDeRhamCohomology I M l) :
    poincarePairing I M o (deRhamCohomology.const I M 1) y =
      compactlySupportedDeRhamCohomology.integral (o.reindex (finCongr (zero_add l))) y := by
  rw [poincarePairing_const_left, one_mul]

/-- **Graded symmetry of the Poincaré pairing on compactly supported classes.** Swapping two
compactly supported classes `x ∈ H^k_c(M)` and `y ∈ H^l_c(M)` reindexes the orientation along
`k + l = l + k` and multiplies the pairing by `(-1) ^ (k * l)`. -/
theorem poincarePairing_comm_toDeRhamCohomology (o : Manifold.Orientation I M (Fin (k + l)))
    (x : compactlySupportedDeRhamCohomology I M k)
    (y : compactlySupportedDeRhamCohomology I M l) :
    poincarePairing I M o (compactlySupportedDeRhamCohomology.toDeRhamCohomology I M k x) y =
      (-1 : ℝ) ^ (k * l) *
        poincarePairing I M (o.reindex (finCongr (Nat.add_comm k l)))
          (compactlySupportedDeRhamCohomology.toDeRhamCohomology I M l y) x := by
  obtain ⟨φ, rfl⟩ := compactlySupportedDeRhamCohomology.mk_surjective I k x
  obtain ⟨ψ, rfl⟩ := compactlySupportedDeRhamCohomology.mk_surjective I l y
  rw [compactlySupportedDeRhamCohomology.toDeRhamCohomology_mk,
    compactlySupportedDeRhamCohomology.toDeRhamCohomology_mk, poincarePairing_mk,
    poincarePairing_mk, ← integralTopForm_smul]
  refine integralTopForm_congr_cast (Nat.add_comm k l) o _ _ fun x v ↦ ?_
  simpa only [SmoothForm.coe_wedge, Pi.smul_apply, ContinuousAlternatingMap.smul_apply] using
    SmoothForm.wedge_comm φ.1 ψ.1 x v

/-- **The integral of a wedge square depends only on the de Rham class**: on an oriented
boundaryless manifold of dimension `k + k` with `k` even, compactly supported closed `k`-forms
`φ` and `ψ` whose difference is exact satisfy `∫_M ψ ∧ ψ = ∫_M φ ∧ φ`. The primitive of `ψ - φ`
need not be compactly supported. For the curvature forms of two connections on a line bundle
over a closed four-manifold, this is the independence of `∫_M F ∧ F` from the connection. -/
theorem integralTopForm_wedge_self_eq_of_sub_mem_exactForms
    (o : Manifold.Orientation I M (Fin (k + k))) (hk : Even k) {φ ψ : SmoothForm I M ℝ k}
    (hφ : φ ∈ compactlySupportedClosedForms I M k)
    (hψ : ψ ∈ compactlySupportedClosedForms I M k) (hψφ : ψ - φ ∈ exactForms I M k) :
    integralTopForm o (RoughForm.wedge ψ.1 ψ.1) = integralTopForm o (RoughForm.wedge φ.1 φ.1) := by
  -- Forms of even degree commute, so `ψ ∧ ψ - φ ∧ φ = (ψ - φ) ∧ ψ + (ψ - φ) ∧ φ`, which is
  -- compactly supported exact.
  have hsub : SmoothForm.wedge ψ ψ - SmoothForm.wedge φ φ =
      SmoothForm.wedge (ψ - φ) ψ + SmoothForm.wedge (ψ - φ) φ := by
    simp only [map_sub, LinearMap.sub_apply, SmoothForm.wedge_comm_of_even hk φ ψ]
    abel
  have hmk := (compactlySupportedDeRhamCohomology.mk_eq_mk_iff I (k + k)
    ⟨_, SmoothForm.wedge_mem_compactlySupportedClosedForms
      ((mem_compactlySupportedClosedForms I).mp hψ).2 hψ⟩
    ⟨_, SmoothForm.wedge_mem_compactlySupportedClosedForms
      ((mem_compactlySupportedClosedForms I).mp hφ).2 hφ⟩).mpr <| by
      rw [hsub]
      exact add_mem (SmoothForm.wedge_mem_exactCompactlySupportedForms_of_left_mem hψφ hψ)
        (SmoothForm.wedge_mem_exactCompactlySupportedForms_of_left_mem hψφ hφ)
  simpa [SmoothForm.coe_wedge] using
    congrArg (compactlySupportedDeRhamCohomology.integral o) hmk

end TauCeti
