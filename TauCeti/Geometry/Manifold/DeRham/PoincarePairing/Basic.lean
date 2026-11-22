/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DeRham.Wedge
public import TauCeti.Geometry.Manifold.DifferentialForm.Integration.TopForm
public import TauCeti.Geometry.Manifold.DeRham.ExtendByZero
public import TauCeti.Geometry.Manifold.Orientation.OpenSubset
import TauCeti.Geometry.Manifold.DifferentialForm.Integration.OpenSubset
import TauCeti.Geometry.Manifold.DifferentialForm.Opens.Wedge
import TauCeti.Geometry.Manifold.DifferentialForm.Integration.BoundarylessStokes
import TauCeti.Geometry.Manifold.DifferentialForm.Integration.Regularity
import TauCeti.Geometry.Manifold.DifferentialForm.Wedge.Leibniz
import Mathlib.LinearAlgebra.Isomorphisms

/-!
# Integration on compactly supported cohomology and the Poincaré pairing

On an oriented boundaryless manifold, Stokes' theorem says that the exterior derivative of a
compactly supported form integrates to zero. Hence integration of compactly supported closed
top forms descends to a linear map `∫_M : H^n_c(M) → ℝ` on compactly supported de Rham
cohomology, computed on classes by integrating a representative.

Composing it with the wedge product `H^k_dR(M) → H^l_c(M) → H^(k+l)_c(M)` gives the Poincaré
pairing `⟨[φ], [ψ]⟩ = ∫_M φ ∧ ψ` between de Rham cohomology and compactly supported de Rham
cohomology in complementary degrees `k + l = n`. Poincaré duality, which is not proved here,
asserts that this pairing identifies `H^k_dR(M)` with the dual of `H^l_c(M)`.

Both maps need the manifold to be boundaryless. On `M = [0, 1]` the form `dx` is exact, yet the
representative formula pairs it with the class of the constant function `1` to give
`∫₀¹ dx = 1`; integration does not descend to cohomology there.

## Main definitions and results

* `TauCeti.integralTopForm_eq_zero_of_mem_exactCompactlySupportedForms`: on a boundaryless
  manifold, the exterior derivative of a compactly supported form integrates to zero.
* `TauCeti.integralTopForm_add_of_mem_compactlySupportedForms` and
  `TauCeti.integralTopForm_sub_of_mem_compactlySupportedForms`: the integral is additive on
  compactly supported smooth top forms.
* `TauCeti.integralTopForm_wedge_sub_left`: wedging with a fixed compactly supported form and
  integrating is additive in the other form, `∫ (A - B) ∧ θ = ∫ A ∧ θ - ∫ B ∧ θ`.
* `TauCeti.integralTopForm_cast_mextDerivₗ_wedge`: integration by parts,
  `∫ dα ∧ a = -(-1)^k ∫ α ∧ da` for a compactly supported form `a`.
* `TauCeti.integralTopForm_wedge_extendByZero`: for open subsets `U ≤ W`,
  `∫_W φ ∧ ext ψ = ∫_U φ|_U ∧ ψ`, from `φ ∧ ext ψ = ext (φ|_U ∧ ψ)`
  (`TauCeti.RoughForm.extendByZero_mpullback_inclusion_wedge`).
* `TauCeti.compactlySupportedDeRhamCohomology.integral`: integration `H^n_c(M) → ℝ`, computed on
  classes by `TauCeti.compactlySupportedDeRhamCohomology.integral_mk`.
* `TauCeti.compactlySupportedDeRhamCohomology.integral_extendByZero` and
  `TauCeti.compactlySupportedDeRhamCohomology.integral_extendByZeroTop`: integration commutes with
  extension by zero `H^n_c(U) → H^n_c(W)` along open subsets `U ≤ W`, and with extension by zero
  `H^n_c(U) → H^n_c(M)` into the whole manifold.
* `TauCeti.compactlySupportedDeRhamCohomology.integral_map_diffeomorph`: integration is
  preserved by orientation-preserving diffeomorphisms.
* `TauCeti.deRhamCohomology.integral`: integration `H^n_dR(M) → ℝ` on a compact manifold, where
  the comparison map `H^n_c(M) → H^n_dR(M)` is bijective, computed on classes by
  `TauCeti.deRhamCohomology.integral_mk`.
* `TauCeti.poincarePairing`: the pairing `H^k_dR(M) → H^l_c(M) → ℝ`, the wedge product followed
  by integration (`TauCeti.poincarePairing_apply`), computed on classes by
  `TauCeti.poincarePairing_mk`.
* `TauCeti.poincarePairing_extendByZero`: for open subsets `U ≤ W`, the pairing intertwines
  restriction `H^k_dR(W) → H^k_dR(U)` and extension by zero `H^l_c(U) → H^l_c(W)`.
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
    (hφ : φ ∈ exactCompactlySupportedForms I M n) : integralTopForm o φ.val = 0 := by
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

omit [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
/-- The integral is additive on compactly supported smooth top forms. -/
theorem integralTopForm_add_of_mem_compactlySupportedForms (o : Manifold.Orientation I M (Fin n))
    {A B : SmoothForm I M ℝ n} (hA : A ∈ compactlySupportedForms I M n)
    (hB : B ∈ compactlySupportedForms I M n) :
    integralTopForm o (A + B).val = integralTopForm o A.val + integralTopForm o B.val := by
  rw [Submodule.coe_add]
  exact integralTopForm_add o (A.isSmoothForm.of_le bot_le) (B.isSmoothForm.of_le bot_le)
    ((mem_compactlySupportedForms I).mp hA) ((mem_compactlySupportedForms I).mp hB)

omit [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
/-- The integral is additive on compactly supported smooth top forms: the form of subtraction. -/
theorem integralTopForm_sub_of_mem_compactlySupportedForms (o : Manifold.Orientation I M (Fin n))
    {A B : SmoothForm I M ℝ n} (hA : A ∈ compactlySupportedForms I M n)
    (hB : B ∈ compactlySupportedForms I M n) :
    integralTopForm o (A - B).val = integralTopForm o A.val - integralTopForm o B.val := by
  rw [eq_sub_iff_add_eq,
    ← integralTopForm_add_of_mem_compactlySupportedForms o (sub_mem hA hB) hB, sub_add_cancel]

omit [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
/-- Wedging with a fixed compactly supported form and integrating is additive in the other form:
the form of subtraction. -/
theorem integralTopForm_wedge_sub_left (o : Manifold.Orientation I M (Fin (k + l)))
    (A B : SmoothForm I M ℝ k) {θ : SmoothForm I M ℝ l} (hθ : θ ∈ compactlySupportedForms I M l) :
    integralTopForm o (RoughForm.wedge (A - B).val θ.val) =
      integralTopForm o (RoughForm.wedge A.val θ.val) -
        integralTopForm o (RoughForm.wedge B.val θ.val) := by
  simp only [← SmoothForm.coe_wedge, map_sub, LinearMap.sub_apply]
  exact integralTopForm_sub_of_mem_compactlySupportedForms o
    (SmoothForm.wedge_mem_compactlySupportedForms _ hθ)
    (SmoothForm.wedge_mem_compactlySupportedForms _ hθ)

/-- **Integration by parts against a compactly supported form.** On an oriented boundaryless
manifold of dimension `k + l + 1`, a smooth `k`-form `α` and a compactly supported smooth `l`-form
`a` satisfy `∫ dα ∧ a = -(-1)^k ∫ α ∧ da`, the first integrand being transported to degree
`k + l + 1`. This is Stokes' theorem for the compactly supported form `α ∧ a`. -/
theorem integralTopForm_cast_mextDerivₗ_wedge (o : Manifold.Orientation I M (Fin (k + l + 1)))
    (α : SmoothForm I M ℝ k) {a : SmoothForm I M ℝ l} (ha : a ∈ compactlySupportedForms I M l) :
    integralTopForm o (LinearEquiv.cast (R := ℝ) (M := fun q : ℕ ↦ SmoothForm I M ℝ q)
        (add_right_comm k 1 l) (SmoothForm.wedge (mextDerivₗ I k α) a)).val =
      -((-1 : ℝ) ^ k * integralTopForm o (SmoothForm.wedge α (mextDerivₗ I l a)).val) := by
  have hγ := SmoothForm.wedge_mem_compactlySupportedForms α ha
  set A := LinearEquiv.cast (R := ℝ) (M := fun q : ℕ ↦ SmoothForm I M ℝ q)
    (add_right_comm k 1 l) (SmoothForm.wedge (mextDerivₗ I k α) a)
  set B := SmoothForm.wedge α (mextDerivₗ I l a)
  have hA : A ∈ compactlySupportedForms I M (k + l + 1) :=
    (cast_mem_compactlySupportedForms_iff I (add_right_comm k 1 l)).mpr
      (SmoothForm.wedge_mem_compactlySupportedForms (mextDerivₗ I k α) ha)
  have hB : (-1 : ℝ) ^ k • B ∈ compactlySupportedForms I M (k + l + 1) :=
    Submodule.smul_mem _ _ (SmoothForm.wedge_mem_compactlySupportedForms α
      (mextDerivₗ_mem_compactlySupportedForms I ha))
  -- The transport along `k + (l + 1) = k + l + 1` in the Leibniz rule is the identity.
  have hcast : LinearEquiv.cast (R := ℝ) (M := fun q : ℕ ↦ SmoothForm I M ℝ q)
      (add_assoc k l 1).symm B = B := by
    refine Subtype.ext (funext fun x ↦ ?_)
    ext v
    rw [SmoothForm.cast_apply]
    simp only [Function.comp_def, Fin.cast_eq_self]
  -- Stokes' theorem for `α ∧ a`, expanded by the Leibniz rule.
  have hstokes := integralTopForm_eq_zero_of_mem_exactCompactlySupportedForms o
    (φ := mextDerivₗ I (k + l) (SmoothForm.wedge α a)) (by
      rw [exactCompactlySupportedForms_succ]
      exact ⟨_, hγ, rfl⟩)
  rw [SmoothForm.mextDerivₗ_wedge, hcast,
    integralTopForm_add_of_mem_compactlySupportedForms o hA hB, Submodule.coe_smul,
    integralTopForm_smul] at hstokes
  linarith

omit [BoundarylessManifold I M] [SigmaCompactSpace M] in
/-- **Integration against an extension by zero.** For open subsets `U ≤ W`, a smooth form `φ` on
`W` and a compactly supported smooth form `ψ` on `U`, `∫_W φ ∧ ext ψ = ∫_U φ|_U ∧ ψ`, for the
orientations restricted from `M`. -/
theorem integralTopForm_wedge_extendByZero (o : Manifold.Orientation I M (Fin (k + l)))
    {U W : Opens M} (h : U ≤ W) (φ : SmoothForm I W ℝ k) {ψ : SmoothForm I U ℝ l}
    (hψ : ψ ∈ compactlySupportedForms I U l) :
    integralTopForm (o.restrict W) (RoughForm.wedge φ.val (RoughForm.extendByZero W ψ.val)) =
      integralTopForm (o.restrict U) (RoughForm.wedge
        (SmoothForm.mpullback (Opens.inclusion h) (contMDiff_inclusion h) φ).val ψ.val) := by
  have hc := (mem_compactlySupportedForms I).mp (SmoothForm.wedge_mem_compactlySupportedForms
    (SmoothForm.mpullback (Opens.inclusion h) (contMDiff_inclusion h) φ) hψ)
  rw [SmoothForm.coe_wedge] at hc
  rw [← RoughForm.extendByZero_mpullback_inclusion_wedge h, integralTopForm_extendByZero o h
    (by rwa [SmoothForm.coe_mpullback] at hc), SmoothForm.coe_mpullback]

namespace compactlySupportedDeRhamCohomology

/-- Integration of compactly supported closed top forms, as a linear map. -/
private def integralClosedForms (o : Manifold.Orientation I M (Fin n)) :
    compactlySupportedClosedForms I M n →ₗ[ℝ] ℝ where
  toFun φ := integralTopForm o φ.val.val
  map_add' φ ψ := integralTopForm_add_of_mem_compactlySupportedForms o
    ((mem_compactlySupportedClosedForms I).mp φ.property).1
    ((mem_compactlySupportedClosedForms I).mp ψ.property).1
  map_smul' c φ := integralTopForm_smul o c φ.val.val

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
    integral o (mk I n φ) = integralTopForm o φ.val.val :=
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
    ((mem_compactlySupportedClosedForms I).mp φ.property).1)

/-- Identifying the top open subset with the ambient manifold preserves integration on
compactly supported cohomology, with the restricted orientation. -/
theorem integral_equivOfDiffeomorph_ofTop (o : Manifold.Orientation I M (Fin n))
    (c : compactlySupportedDeRhamCohomology I M n) :
    integral (o.restrict ⊤) (equivOfDiffeomorph (Diffeomorph.ofTop ⊤ rfl) n c) =
      integral o c := by
  let Φ : (⊤ : Opens M) ≃ₘ⟮I, I⟯ M := Diffeomorph.ofTop ⊤ rfl
  obtain ⟨φ, rfl⟩ := mk_surjective I n c
  have h : integralTopForm (o.restrict ⊤) (mpullback I I Φ φ.val.val) = integralTopForm o φ.val.val
      := by
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

/-- An orientation-preserving diffeomorphism preserves integration on compactly supported
cohomology. No integrability hypothesis is needed: representatives are smooth and compactly
supported. The target orientation must be specified explicitly, so this is not a simp lemma. -/
theorem integral_map_diffeomorph
    {H' N : Type*} [TopologicalSpace H'] {J : ModelWithCorners ℝ E H'}
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
      integralTopForm o (RoughForm.wedge (φ.val : RoughForm I M ℝ k) ψ.val.val) := by
  rw [poincarePairing_apply, compactlySupportedDeRhamCohomology.wedge_mk,
    compactlySupportedDeRhamCohomology.integral_mk, SmoothForm.coe_wedge]

omit [SigmaCompactSpace M] in
/-- **The Poincaré pairing intertwines restriction and extension by zero.** For open subsets
`U ≤ W` of an oriented boundaryless manifold of dimension `k + l`, a de Rham class `x` on `W` and
a compactly supported class `y` on `U`, `⟨x, ext y⟩_W = ⟨x|_U, y⟩_U` for the orientations
restricted from `M`. -/
theorem poincarePairing_extendByZero (o : Manifold.Orientation I M (Fin (k + l))) {U W : Opens M}
    [SigmaCompactSpace U] [SigmaCompactSpace W] (h : U ≤ W) (x : deRhamCohomology I W k)
    (y : compactlySupportedDeRhamCohomology I U l) :
    poincarePairing I W (o.restrict W) x (compactlySupportedDeRhamCohomology.extendByZero h l y) =
      poincarePairing I U (o.restrict U)
        (deRhamCohomology.map (Opens.inclusion h) (contMDiff_inclusion h) k x) y := by
  obtain ⟨φ, rfl⟩ := deRhamCohomology.mk_surjective I k x
  obtain ⟨ψ, rfl⟩ := compactlySupportedDeRhamCohomology.mk_surjective I l y
  rw [compactlySupportedDeRhamCohomology.extendByZero_mk, deRhamCohomology.map_mk,
    poincarePairing_mk, poincarePairing_mk, compactlySupportedClosedForms.coe_extendByZero,
    closedForms.coe_mpullback]
  exact integralTopForm_wedge_extendByZero o h φ.val
    (compactlySupportedClosedForms_le_compactlySupportedForms I l ψ.property)

/-- **The integral of a wedge square depends only on the de Rham class**: on an oriented
boundaryless manifold of dimension `k + k` with `k` even, compactly supported closed `k`-forms
`φ` and `ψ` whose difference is exact satisfy `∫_M ψ ∧ ψ = ∫_M φ ∧ φ`. The primitive of `ψ - φ`
need not be compactly supported. For the curvature forms of two connections on a line bundle
over a closed four-manifold, this is the independence of `∫_M F ∧ F` from the connection. -/
theorem integralTopForm_wedge_self_eq_of_sub_mem_exactForms
    (o : Manifold.Orientation I M (Fin (k + k))) (hk : Even k) {φ ψ : SmoothForm I M ℝ k}
    (hφ : φ ∈ compactlySupportedClosedForms I M k)
    (hψ : ψ ∈ compactlySupportedClosedForms I M k) (hψφ : ψ - φ ∈ exactForms I M k) :
    integralTopForm o (RoughForm.wedge ψ.val ψ.val) = integralTopForm o
        (RoughForm.wedge φ.val φ.val) := by
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

namespace TauCeti.deRhamCohomology

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M] [IsManifold I ∞ M] [BoundarylessManifold I M]
  [T2Space M] [CompactSpace M] {n : ℕ}

/-- Integration `H^n_dR(M) → ℝ` on a compact oriented boundaryless manifold: on a compact manifold
de Rham cohomology is compactly supported de Rham cohomology, on which integration is defined. -/
def integral (o : Manifold.Orientation I M (Fin n)) : deRhamCohomology I M n →ₗ[ℝ] ℝ :=
  compactlySupportedDeRhamCohomology.integral o ∘ₗ (LinearEquiv.ofBijective _
    (compactlySupportedDeRhamCohomology.toDeRhamCohomology_bijective I n)).symm.toLinearMap

/-- Integration on de Rham cohomology extends integration on compactly supported de Rham
cohomology along the comparison map, which is bijective on a compact manifold. -/
@[simp]
theorem integral_toDeRhamCohomology (o : Manifold.Orientation I M (Fin n))
    (c : compactlySupportedDeRhamCohomology I M n) :
    integral o (compactlySupportedDeRhamCohomology.toDeRhamCohomology I M n c) =
      compactlySupportedDeRhamCohomology.integral o c := by
  rw [integral, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
    LinearEquiv.ofBijective_symm_apply_apply]

/-- The integral of the class of a closed top form on a compact manifold is the integral of the
form. -/
@[simp]
theorem integral_mk (o : Manifold.Orientation I M (Fin n)) (φ : closedForms I M n) :
    integral o (mk I n φ) = integralTopForm o φ.val.val := by
  -- On a compact manifold the closed form `φ` is a compactly supported closed form.
  let ψ : compactlySupportedClosedForms I M n :=
    ⟨φ.val, (mem_compactlySupportedClosedForms I).mpr
      ⟨by simp [compactlySupportedForms_eq_top], φ.property⟩⟩
  have hψ : compactlySupportedDeRhamCohomology.toDeRhamCohomology I M n
      (compactlySupportedDeRhamCohomology.mk I n ψ) = mk I n φ :=
    compactlySupportedDeRhamCohomology.toDeRhamCohomology_mk I n ψ
  rw [← hψ, integral_toDeRhamCohomology, compactlySupportedDeRhamCohomology.integral_mk]

end TauCeti.deRhamCohomology
