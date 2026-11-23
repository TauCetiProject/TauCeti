/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Cotangent.Bundle.LatticeQuotient.ActionAngle
public import TauCeti.Geometry.Manifold.MFDeriv.Matrix

/-!
# Developing maps and action coordinates of the torus bundle of an exact coframe

Let `B` be a boundaryless manifold modelled on a finite-dimensional real space, let `p ≠ 0`, and
let `a : B → ℝ^ι` be a smooth map all of whose differentials are bijective. The one-forms
`α_i = p • d a_i` (`TauCeti.CotangentBundle.developingForm`) are closed and form a global frame of
the cotangent bundle (`TauCeti.CotangentBundle.isLocalFrameOn_developingForm`). They are the
period one-forms of the lattice `Λ ⊆ T*B` that they span over `ℤ`, and `T*B/Λ` is the regular
Lagrangian torus fibration `TauCeti.CotangentBundle.LatticeQuotient`. The map `a` is its
*developing map*: it gives the actions of the action–angle chart
`TauCeti.CotangentBundle.LatticeQuotient.actionAngleChart`, which is injective exactly when `a`
is.

Conversely, take any frame `α` of `T*B` with `α_i = p • d a_i` for a map `a`; then the
differentials of `a` are bijective (`TauCeti.CotangentBundle.LatticeQuotient.bijective_mfderiv`).
Functions `J : B → ℝ^ι` whose differentials, scaled by `p`, lie in the lattice `Λ` at every point
are the candidates for global action coordinates of `T*B/Λ`. On a preconnected base they are
integral affine functions of the developing map:

`J = N a + b`, with `N` an integer matrix and `b` a constant vector

(`TauCeti.CotangentBundle.LatticeQuotient.exists_eq_mulVec_add_of_mem_span`). This is the
basis-change indeterminacy of global action coordinates. In particular `J` is constant on the
fibres of `a` (`TauCeti.CotangentBundle.LatticeQuotient.apply_eq_apply_of_mem_span`), so when `a`
is not injective no such `J` is injective
(`TauCeti.CotangentBundle.LatticeQuotient.not_injective_of_mem_span`). So exactness of the period
forms does not suffice for global action coordinates onto an open subset of `ℝ^ι`: the developing
map must also be injective. An explicit example is in
`TauCeti.Geometry.Symplectic.Cotangent.Bundle.LatticeQuotient.PolarRectangle`.

## Main definitions

* `TauCeti.CotangentBundle.developingForm p a i`: the one-form `p • d a_i`.

## Main results

* `TauCeti.CotangentBundle.isLocalFrameOn_developingForm`: the forms `p • d a_i` are a global
  frame of `T*B` when the differentials of `a` are bijective.
* `TauCeti.CotangentBundle.LatticeQuotient.exists_eq_mulVec_add_of_mem_span`: functions whose
  differentials lie in the lattice are integral affine functions of the developing map.
* `TauCeti.CotangentBundle.LatticeQuotient.not_injective_of_mem_span`: when the developing map is
  not injective, neither is any such function.

## References

* J. J. Duistermaat, *On global action-angle coordinates*, Comm. Pure Appl. Math. 33 (1980),
  687–706 (the period lattice, its developing map and the obstructions to global action–angle
  coordinates).
-/

public section

noncomputable section

open Bundle Set Function Matrix
open scoped Manifold ContDiff

namespace TauCeti

namespace CotangentBundle

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {B : Type*} [TopologicalSpace B] [ChartedSpace H B]
  [IsManifold I ∞ B] {ι : Type*} [Fintype ι]

/-! ### The developing coframe -/

/-- The **developing coframe** of a smooth map `a : B → ℝ^ι`: the one-forms `p • d a_i`. When the
differentials of `a` are bijective, these forms are a global frame of `T*B`
(`TauCeti.CotangentBundle.isLocalFrameOn_developingForm`), the exact period one-forms of a lattice
whose torus bundle has developing map `a`. -/
def developingForm (p : ℝ) (a : C^∞⟮I, B; 𝓘(ℝ, ι → ℝ), ι → ℝ⟯) (i : ι) : SmoothForm I B ℝ 1 :=
  p • mextDerivₗ I 0 (SmoothForm.ofFunction
    (⟨ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι ↦ ℝ) i ∘ a,
      (ContinuousLinearMap.proj i).contMDiff.comp a.contMDiff⟩ : C^∞⟮I, B; 𝓘(ℝ, ℝ), ℝ⟯))

/-- The developing form `p • d a_i` takes the value `p * (da_x v)_i` on a tangent vector `v`. -/
theorem degreeOneEquiv_developingForm_apply (p : ℝ) (a : C^∞⟮I, B; 𝓘(ℝ, ι → ℝ), ι → ℝ⟯) (i : ι)
    (x : B) (v : TangentSpace I x) :
    SmoothForm.degreeOneEquiv (developingForm p a i) x v =
      p * mfderiv I 𝓘(ℝ, ι → ℝ) a x v i := by
  simp only [developingForm, map_smul, ContMDiffSection.coe_smul, Pi.smul_apply, smul_apply,
    SmoothForm.degreeOneEquiv_mextDerivₗ, smul_eq_mul]
  -- `erw`: the function is the coercion of an explicitly constructed `C^∞` map.
  erw [SmoothForm.ofFunction_apply_zero]
  congr 1
  -- The component `a_i` is the projection `(·) i` composed with `a`.
  exact (mvfderiv_comp_apply x
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι ↦ ℝ) i).mdifferentiableAt
    (a.contMDiff.mdifferentiableAt (by simp)) v).trans (by
      rw [mvfderiv, (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι ↦ ℝ) i).hasMFDerivAt.mfderiv]
      -- `rfl`: the tangent space of `ℝ^ι` at `a x` is `ℝ^ι` itself, and `proj i` evaluates at `i`.
      rfl)

/-- The developing form `p • d a_i` evaluates the one-element family `![v]` to `p * (da_x v)_i`;
this is the simp normal form of `degreeOneEquiv_developingForm_apply`. -/
@[simp]
theorem developingForm_apply_vec (p : ℝ) (a : C^∞⟮I, B; 𝓘(ℝ, ι → ℝ), ι → ℝ⟯) (i : ι) (x : B)
    (v : TangentSpace I x) :
    (developingForm p a i).val x ![v] = p * mfderiv I 𝓘(ℝ, ι → ℝ) a x v i := by
  rw [← SmoothForm.degreeOneEquiv_apply_apply_vec, degreeOneEquiv_developingForm_apply]

/-- The developing forms are closed, being multiples of exact forms. -/
theorem isClosed_developingForm (p : ℝ) (a : C^∞⟮I, B; 𝓘(ℝ, ι → ℝ), ι → ℝ⟯) (i : ι) :
    (developingForm p a i).IsClosed := by
  rw [SmoothForm.isClosed_iff_mextDerivₗ_eq_zero, developingForm, map_smul,
    (SmoothForm.isClosed_iff_mextDerivₗ_eq_zero _).1 (SmoothForm.isClosed_mextDerivₗ _),
    smul_zero]

/-- **The developing coframe is a frame.** If the differentials of `a` are bijective and `p ≠ 0`,
the forms `p • d a_i` are a global frame of the cotangent bundle. -/
theorem isLocalFrameOn_developingForm {p : ℝ} (hp : p ≠ 0) {a : C^∞⟮I, B; 𝓘(ℝ, ι → ℝ), ι → ℝ⟯}
    (hda : ∀ x, Bijective (mfderiv I 𝓘(ℝ, ι → ℝ) a x)) :
    IsLocalFrameOn I (E →L[ℝ] ℝ) ∞
      (fun i x ↦ SmoothForm.degreeOneEquiv (developingForm p a i) x) univ := by
  classical
  refine isLocalFrameOn_degreeOneEquiv_iff.2 fun x _ ↦ ?_
  -- Tangent vectors `e j` with `da_x (e j) = Pi.single j 1`.
  choose e he using fun j : ι ↦ (hda x).2 (Pi.single j 1)
  refine ⟨Fintype.linearIndependent_iff.2 fun g hg i ↦ ?_,
    top_le_iff.2 (Submodule.eq_top_iff'.2 fun q ↦ ?_)⟩
  · have h := congrArg (fun φ : TangentSpace I x →L[ℝ] ℝ ↦ φ (e i)) hg
    simp only [FunLike.coe_sum, Finset.sum_apply, smul_apply,
      degreeOneEquiv_developingForm_apply, he, smul_eq_mul, zero_apply] at h
    simpa [Pi.single_apply, hp] using h
  -- A covector `q` is `∑ j, (q (e j) / p) • (p • d a_j)`.
  refine (Submodule.mem_span_range_iff_exists_fun ℝ).2 ⟨fun j ↦ q (e j) / p, ?_⟩
  ext v
  have hv : ∑ j, mfderiv I 𝓘(ℝ, ι → ℝ) a x v j • e j = v := (hda x).1 (by
    rw [map_sum]
    simp_rw [map_smul, he]
    have h := (Pi.basisFun ℝ ι).sum_repr (mfderiv I 𝓘(ℝ, ι → ℝ) a x v)
    simp only [Pi.basisFun_apply] at h
    exact h)
  simp only [FunLike.coe_sum, Finset.sum_apply, smul_apply,
    degreeOneEquiv_developingForm_apply, smul_eq_mul]
  conv_rhs => rw [← hv]
  simp only [map_sum, map_smul, smul_eq_mul]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  field_simp

namespace LatticeQuotient

variable {α : ι → SmoothForm I B ℝ 1}
  (hα : IsLocalFrameOn I (E →L[ℝ] ℝ) ∞ (fun i x ↦ SmoothForm.degreeOneEquiv (α i) x) univ)
  {p : ℝ} {a J : B → ι → ℝ}

/-! ### Action coordinates -/

include hα in
/-- The developing map of a frame `α_i = p • d a_i` has bijective differentials. -/
theorem bijective_mfderiv [FiniteDimensional ℝ E]
    (hαa : ∀ i x v, SmoothForm.degreeOneEquiv (α i) x v = p * mfderiv I 𝓘(ℝ, ι → ℝ) a x v i)
    (x : B) : Bijective (mfderiv I 𝓘(ℝ, ι → ℝ) a x) := by
  have hinj := injective_mfderiv hα hαa x
  have hdim : Module.finrank ℝ E = Module.finrank ℝ (ι → ℝ) := by
    rw [Module.finrank_fintype_fun_eq_card, hα.card_eq_finrank (mem_univ x),
      ContinuousLinearMap.dual_finrank_eq]
  exact ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).1 hinj⟩

include hα in
/-- **Action coordinates are integral affine functions of the developing map.** Let `α` be a frame
of `T*B` with `α_i = p • d a_i`, for `p ≠ 0` and a `C¹` map `a`, on a preconnected boundaryless
base. If the differentials of a `C¹` map `J : B → ℝ^ι`, scaled by `p`, lie at every point in the
lattice spanned over `ℤ` by the `α_j`, then `J = N a + b` for an integer matrix `N` and a constant
vector `b`. -/
theorem exists_eq_mulVec_add_of_mem_span [FiniteDimensional ℝ E] [BoundarylessManifold I B]
    [PreconnectedSpace B] (hp : p ≠ 0) (ha : ContMDiff I 𝓘(ℝ, ι → ℝ) 1 a)
    (hαa : ∀ i x v, SmoothForm.degreeOneEquiv (α i) x v = p * mfderiv I 𝓘(ℝ, ι → ℝ) a x v i)
    (hJ : ContMDiff I 𝓘(ℝ, ι → ℝ) 1 J)
    (hJα : ∀ x i, p • (ContinuousLinearMap.proj i).comp (mfderiv I 𝓘(ℝ, ι → ℝ) J x) ∈
      Submodule.span ℤ (range fun j ↦ SmoothForm.degreeOneEquiv (α j) x)) :
    ∃ (N : Matrix ι ι ℤ) (b : ι → ℝ), ∀ x, J x = N.map (↑) *ᵥ a x + b := by
  refine exists_eq_mulVec_add_of_forall_exists_mfderiv_eq ha (bijective_mfderiv hα hαa) hJ
    fun x ↦ ?_
  -- Write each `p • dJ_i` in the lattice basis: `p • dJ_i = ∑ j, c_ij • α_j`.
  choose c hc using fun i ↦ (Submodule.mem_span_range_iff_exists_fun ℤ).1 (hJα x i)
  refine ⟨Matrix.of c, fun v ↦ funext fun i ↦ ?_⟩
  have h := congrArg (fun φ : TangentSpace I x →L[ℝ] ℝ ↦ φ v) (hc i)
  simp only [FunLike.coe_sum, Finset.sum_apply, FunLike.coe_smul, Pi.smul_apply, zsmul_eq_mul,
    Pi.mul_apply, Pi.intCast_apply, hαa, smul_eq_mul] at h
  simp only [mulVec, dotProduct, map_apply, of_apply]
  apply mul_left_cancel₀ hp
  rw [Finset.mul_sum]
  exact h.symm.trans (Finset.sum_congr rfl fun j _ ↦ by ring)

include hα in
/-- **Action coordinates are constant on the fibres of the developing map.** Under the hypotheses
of `exists_eq_mulVec_add_of_mem_span`, `J x = J y` whenever `a x = a y`. -/
theorem apply_eq_apply_of_mem_span [FiniteDimensional ℝ E] [BoundarylessManifold I B]
    [PreconnectedSpace B] (hp : p ≠ 0) (ha : ContMDiff I 𝓘(ℝ, ι → ℝ) 1 a)
    (hαa : ∀ i x v, SmoothForm.degreeOneEquiv (α i) x v = p * mfderiv I 𝓘(ℝ, ι → ℝ) a x v i)
    (hJ : ContMDiff I 𝓘(ℝ, ι → ℝ) 1 J)
    (hJα : ∀ x i, p • (ContinuousLinearMap.proj i).comp (mfderiv I 𝓘(ℝ, ι → ℝ) J x) ∈
      Submodule.span ℤ (range fun j ↦ SmoothForm.degreeOneEquiv (α j) x))
    {x y : B} (hxy : a x = a y) : J x = J y := by
  obtain ⟨N, b, hNb⟩ := exists_eq_mulVec_add_of_mem_span hα hp ha hαa hJ hJα
  rw [hNb, hNb, hxy]

include hα in
/-- **A non-injective developing map admits no injective action coordinates.** Under the
hypotheses of `exists_eq_mulVec_add_of_mem_span`, if `a` is not injective then neither is `J`. -/
theorem not_injective_of_mem_span [FiniteDimensional ℝ E] [BoundarylessManifold I B]
    [PreconnectedSpace B] (hp : p ≠ 0) (ha : ContMDiff I 𝓘(ℝ, ι → ℝ) 1 a)
    (hαa : ∀ i x v, SmoothForm.degreeOneEquiv (α i) x v = p * mfderiv I 𝓘(ℝ, ι → ℝ) a x v i)
    (hJ : ContMDiff I 𝓘(ℝ, ι → ℝ) 1 J)
    (hJα : ∀ x i, p • (ContinuousLinearMap.proj i).comp (mfderiv I 𝓘(ℝ, ι → ℝ) J x) ∈
      Submodule.span ℤ (range fun j ↦ SmoothForm.degreeOneEquiv (α j) x))
    (hna : ¬ Injective a) : ¬ Injective J := fun hJi ↦
  hna fun _ _ hxy ↦ hJi (apply_eq_apply_of_mem_span hα hp ha hαa hJ hJα hxy)

end LatticeQuotient

end CotangentBundle

end TauCeti
