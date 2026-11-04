/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Complex.AlmostComplexStructure
public import TauCeti.Geometry.Manifold.Complex.Family.Block

/-!
# Pseudoholomorphic sections in a product trivialization

Given a product trivialization `B × V` over a base `B` with constant complex structure `i`
(`i² = -1`) and a smooth almost complex structure `J` agreeing at `(b, σ b)` with
`TauCeti.ComplexStructureFamily.blockEndomorphism i α j (b, σ b)`, a section
`x ↦ (x, σ x) : B → B × V` of `Prod.fst` is `(i, J)`-pseudoholomorphic if and only if `σ` is
differentiable and satisfies Robbin–Salamon's marked-section Cauchy–Riemann equation

`dσ(b)(a) + j(b, σ b)(dσ(b)(i a)) + α(b, σ b)(i a) = 0`

for all `a : B` (`sectionTerm i α j σ b a = 0`).

This file establishes that equivalence within a set (under `UniqueDiffWithinAt`), at a point, on a
set, and globally on arbitrary real normed spaces `B` and `V` (without finite-dimensionality
assumptions), relates `sectionTerm` to `TauCeti.complexAntilinearPart`, and records two geometric
specializations:

* when the connection block vanishes along the section (`α(b, σ b) = 0`), the section equation
  reduces to `(i, j(b, σ b))`-complex-linearity of `fderiv ℝ σ b`;
* for a constant section `x ↦ (x, v₀)` (such as a marked section straightened in local
  coordinates), pseudoholomorphy at `b` is equivalent to `α(b, v₀) = 0`.

## Main declarations

* `TauCeti.ComplexStructureFamily.sectionTermWithin`,
  `TauCeti.ComplexStructureFamily.sectionTerm`: the inhomogeneous Cauchy–Riemann expression
  `dσ(a) + j(dσ(i a)) + α(i a)` of a section `σ : B → V`.
* `TauCeti.ComplexStructureFamily.isPseudoholomorphicWithinAt_graph_iff`,
  `TauCeti.ComplexStructureFamily.isPseudoholomorphicAt_graph_iff`,
  `TauCeti.ComplexStructureFamily.isPseudoholomorphicOn_graph_iff`,
  `TauCeti.ComplexStructureFamily.isPseudoholomorphic_graph_iff`: characterization of
  pseudoholomorphic sections via `sectionTerm`.
* `TauCeti.ComplexStructureFamily.sectionTerm_eq_two_smul_complexAntilinearPart_add`: decomposition
  into `2 • ∂bar σ + α ∘ i`.
* `TauCeti.ComplexStructureFamily.isPseudoholomorphicAt_graph_const_iff`: a constant section
  `x ↦ (x, v₀)` is pseudoholomorphic at `b` iff `α(b, v₀) = 0`.

## References

* J. W. Robbin and D. A. Salamon, *A construction of the Deligne–Mumford orbifold*, J. Eur. Math.
  Soc. 8 (2006), 611–699, Section 8.9, equation (15).
-/

public noncomputable section

open scoped Manifold Topology

namespace TauCeti.ComplexStructureFamily

variable {B V : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

/-! ### The marked-section Cauchy–Riemann operator -/

/-- The inhomogeneous Cauchy–Riemann expression
`dσ_s(b)(a) + j(b, σ b)(dσ_s(b)(i a)) + α(b, σ b)(i a)` within a set `s ⊆ B` for a section
`x ↦ (x, σ x)` of `B × V → B`. -/
def sectionTermWithin (i : B →L[ℝ] B) (α : B × V → B →L[ℝ] V) (j : B × V → V →L[ℝ] V)
    (σ : B → V) (s : Set B) (b a : B) : V :=
  fderivWithin ℝ σ s b a + j (b, σ b) (fderivWithin ℝ σ s b (i a)) + α (b, σ b) (i a)

/-- The inhomogeneous Cauchy–Riemann expression `dσ(b)(a) + j(b, σ b)(dσ(b)(i a)) + α(b, σ b)(i a)`
for a section `x ↦ (x, σ x)` of `B × V → B`. -/
def sectionTerm (i : B →L[ℝ] B) (α : B × V → B →L[ℝ] V) (j : B × V → V →L[ℝ] V)
    (σ : B → V) (b a : B) : V :=
  fderiv ℝ σ b a + j (b, σ b) (fderiv ℝ σ b (i a)) + α (b, σ b) (i a)

theorem sectionTermWithin_def (i : B →L[ℝ] B) (α : B × V → B →L[ℝ] V) (j : B × V → V →L[ℝ] V)
    (σ : B → V) (s : Set B) (b a : B) : sectionTermWithin i α j σ s b a =
      fderivWithin ℝ σ s b a + j (b, σ b) (fderivWithin ℝ σ s b (i a)) + α (b, σ b) (i a) := (rfl)

theorem sectionTerm_def (i : B →L[ℝ] B) (α : B × V → B →L[ℝ] V) (j : B × V → V →L[ℝ] V)
    (σ : B → V) (b a : B) : sectionTerm i α j σ b a =
      fderiv ℝ σ b a + j (b, σ b) (fderiv ℝ σ b (i a)) + α (b, σ b) (i a) := (rfl)

@[simp]
theorem sectionTermWithin_univ (i : B →L[ℝ] B) (α : B × V → B →L[ℝ] V) (j : B × V → V →L[ℝ] V)
    (σ : B → V) (b a : B) :
    sectionTermWithin i α j σ Set.univ b a = sectionTerm i α j σ b a := by
  simp [sectionTermWithin_def, sectionTerm_def]

theorem _root_.Filter.EventuallyEq.sectionTerm_eq {σ₁ σ₂ : B → V} {b : B}
    (hσ : σ₁ =ᶠ[𝓝 b] σ₂) (i : B →L[ℝ] B) (α : B × V → B →L[ℝ] V) (j : B × V → V →L[ℝ] V)
    (a : B) : sectionTerm i α j σ₁ b a = sectionTerm i α j σ₂ b a := by
  simp only [sectionTerm_def, hσ.fderiv_eq, hσ.self_of_nhds]

/-- Express `sectionTerm` via the complex-antilinear part `∂bar` of `fderiv ℝ σ b`:
`sectionTerm i α j σ b a = 2 • ∂bar(dσ_b) a + α(b, σ b)(i a)`. -/
theorem sectionTerm_eq_two_smul_complexAntilinearPart_add (i : B →L[ℝ] B)
    (α : B × V → B →L[ℝ] V) (j : B × V → V →L[ℝ] V) (σ : B → V) (b a : B) :
    sectionTerm i α j σ b a =
      (2 : ℝ) • complexAntilinearPart i.toLinearMap (j (b, σ b)).toLinearMap
          (fderiv ℝ σ b).toLinearMap a + α (b, σ b) (i a) := by
  rw [sectionTerm_def, complexAntilinearPart_apply]
  simp only [ContinuousLinearMap.coe_coe]; rw [smul_smul]; norm_num

/-! ### Equivalence with pseudoholomorphy of the section graph -/

/-- Algebraic core of the section equation: when `i² = -1`, intertwining `i` with
`blockEndomorphism i α j p` along `(id, L)` is equivalent to `L a + j p (L (i a)) + α p (i a) = 0`
for all `a`. -/
private theorem graph_intertwine_iff {i : B →L[ℝ] B} (hi : ∀ a, i (i a) = -a)
    (α : B × V → B →L[ℝ] V) (j : B × V → V →L[ℝ] V) (p : B × V) (L : B →L[ℝ] V) :
    (∀ a : B, (i a, L (i a)) = blockEndomorphism i α j p (a, L a)) ↔
      ∀ a : B, L a + j p (L (i a)) + α p (i a) = 0 := by
  simp only [blockEndomorphism_apply, Prod.mk.injEq, true_and]
  refine ⟨fun h a ↦ ?_, fun h a ↦ ?_⟩
  · have hia := h (i a); rw [hi a, map_neg] at hia
    simpa [add_assoc] using (show L a + (j p (L (i a)) + α p (i a)) = L a + (-L a) by
      rw [add_comm (j p _) (α p _), ← hia])
  · have hnia := h (-i a)
    rw [map_neg, map_neg, hi a, neg_neg] at hnia
    exact eq_of_sub_eq_zero (by
      rw [show L (i a) - (α p a + j p (L a)) = -((-L (i a)) + j p (L a) + α p a) by abel,
        hnia, neg_zero])

/-- Within a set `s` of unique differentiability at `b`, the graph `x ↦ (x, σ x)` is
`(i, J)`-pseudoholomorphic within `s` at `b` if and only if `σ` is differentiable within `s` at `b`
and `sectionTermWithin i α j σ s b a = 0` for all `a`. -/
theorem isPseudoholomorphicWithinAt_graph_iff
    (J : SmoothAlmostComplexStructure 𝓘(ℝ, B × V) (B × V))
    (i : B →L[ℝ] B) (hi : ∀ a, i (i a) = -a)
    (α : B × V → B →L[ℝ] V) (j : B × V → V →L[ℝ] V)
    {σ : B → V} {s : Set B} {b : B} (hs : UniqueDiffWithinAt ℝ s b)
    (hJ : (J.toEndomorphism (b, σ b) : (B × V) →L[ℝ] B × V) =
      blockEndomorphism i α j (b, σ b)) :
    IsPseudoholomorphicWithinAt (SmoothAlmostComplexStructure.const i hi) J
        (fun x ↦ (x, σ x)) s b ↔
      DifferentiableWithinAt ℝ σ s b ∧ ∀ a, sectionTermWithin i α j σ s b a = 0 := by
  rw [isPseudoholomorphicWithinAt_iff_isJHolomorphicWithinAt]
  constructor
  · intro h
    obtain ⟨u', hu', hlin⟩ := (isJHolomorphicWithinAt_iff _ _ _ _ _).1 h
    have hsnd : HasFDerivWithinAt σ ((ContinuousLinearMap.snd ℝ B V).comp u') s b :=
      (ContinuousLinearMap.snd ℝ B V).hasFDerivAt.comp_hasFDerivWithinAt b hu'
    have hu1 : (ContinuousLinearMap.fst ℝ B V).comp u' = ContinuousLinearMap.id ℝ B :=
      hs.eq ((ContinuousLinearMap.fst ℝ B V).hasFDerivAt.comp_hasFDerivWithinAt b hu')
        (hasFDerivWithinAt_id b s)
    have hu_eq : u' = (ContinuousLinearMap.id ℝ B).prod (fderivWithin ℝ σ s b) := by
      ext a <;> [exact congrArg (· a) hu1; exact congrArg (· a) (hsnd.fderivWithin hs).symm]
    refine ⟨hsnd.differentiableWithinAt, ?_⟩
    simp only [sectionTermWithin_def]
    refine (graph_intertwine_iff hi α j (b, σ b) (fderivWithin ℝ σ s b)).1 fun a ↦ ?_
    have ha := (isComplexLinearMap_iff_apply _ _ _).1 hlin a
    simp only [SmoothAlmostComplexStructure.almostComplexStructureAt_toLinearMap,
      ContinuousLinearMap.coe_coe] at ha
    change u' ((SmoothAlmostComplexStructure.const i hi).toEndomorphism b a) =
      (J.toEndomorphism (b, σ b) : (B × V) →L[ℝ] B × V) (u' a) at ha
    rwa [SmoothAlmostComplexStructure.const_toEndomorphism_apply, hJ, hu_eq] at ha
  · rintro ⟨hσ, hsec⟩
    refine (isJHolomorphicWithinAt_iff _ _ _ _ _).2
      ⟨(ContinuousLinearMap.id ℝ B).prod (fderivWithin ℝ σ s b),
        (hasFDerivWithinAt_id b s).prodMk hσ.hasFDerivWithinAt,
        (isComplexLinearMap_iff_apply _ _ _).2 fun a ↦ ?_⟩
    simp only [SmoothAlmostComplexStructure.almostComplexStructureAt_toLinearMap,
      ContinuousLinearMap.coe_coe]
    change ((ContinuousLinearMap.id ℝ B).prod (fderivWithin ℝ σ s b))
        ((SmoothAlmostComplexStructure.const i hi).toEndomorphism b a) =
      (J.toEndomorphism (b, σ b) : (B × V) →L[ℝ] B × V)
        (((ContinuousLinearMap.id ℝ B).prod (fderivWithin ℝ σ s b)) a)
    rw [SmoothAlmostComplexStructure.const_toEndomorphism_apply, hJ]
    exact (graph_intertwine_iff hi α j (b, σ b) (fderivWithin ℝ σ s b)).2
      (fun c ↦ by simpa only [sectionTermWithin_def] using hsec c) a

/-- Pointwise characterization: the graph `x ↦ (x, σ x)` is `(i, J)`-pseudoholomorphic at `b` if
and only if `σ` is differentiable at `b` and `sectionTerm i α j σ b a = 0` for all `a`. -/
theorem isPseudoholomorphicAt_graph_iff
    (J : SmoothAlmostComplexStructure 𝓘(ℝ, B × V) (B × V))
    (i : B →L[ℝ] B) (hi : ∀ a, i (i a) = -a)
    (α : B × V → B →L[ℝ] V) (j : B × V → V →L[ℝ] V) {σ : B → V} {b : B}
    (hJ : (J.toEndomorphism (b, σ b) : (B × V) →L[ℝ] B × V) =
      blockEndomorphism i α j (b, σ b)) :
    IsPseudoholomorphicAt (SmoothAlmostComplexStructure.const i hi) J (fun x ↦ (x, σ x)) b ↔
      DifferentiableAt ℝ σ b ∧ ∀ a, sectionTerm i α j σ b a = 0 := by
  simpa only [isPseudoholomorphicWithinAt_univ, differentiableWithinAt_univ,
    sectionTermWithin_univ] using
    isPseudoholomorphicWithinAt_graph_iff J i hi α j uniqueDiffWithinAt_univ hJ

/-- Setwise characterization on a domain `s` of unique differentiability. -/
theorem isPseudoholomorphicOn_graph_iff
    (J : SmoothAlmostComplexStructure 𝓘(ℝ, B × V) (B × V))
    (i : B →L[ℝ] B) (hi : ∀ a, i (i a) = -a)
    (α : B × V → B →L[ℝ] V) (j : B × V → V →L[ℝ] V)
    {σ : B → V} {s : Set B} (hs : UniqueDiffOn ℝ s)
    (hJ : ∀ b ∈ s, (J.toEndomorphism (b, σ b) : (B × V) →L[ℝ] B × V) =
      blockEndomorphism i α j (b, σ b)) :
    IsPseudoholomorphicOn (SmoothAlmostComplexStructure.const i hi) J (fun x ↦ (x, σ x)) s ↔
      DifferentiableOn ℝ σ s ∧ ∀ b ∈ s, ∀ a, sectionTermWithin i α j σ s b a = 0 := by
  rw [isPseudoholomorphicOn_iff, DifferentiableOn]
  exact ⟨fun h ↦ ⟨fun b hb ↦ ((isPseudoholomorphicWithinAt_graph_iff J i hi α j (hs b hb)
        (hJ b hb)).1 (h b hb)).1,
      fun b hb ↦ ((isPseudoholomorphicWithinAt_graph_iff J i hi α j (hs b hb)
        (hJ b hb)).1 (h b hb)).2⟩,
    fun ⟨hσ, hsec⟩ b hb ↦ (isPseudoholomorphicWithinAt_graph_iff J i hi α j (hs b hb)
      (hJ b hb)).2 ⟨hσ b hb, hsec b hb⟩⟩

/-- Global characterization: `x ↦ (x, σ x)` is `(i, J)`-pseudoholomorphic if and only if `σ` is
differentiable everywhere and `sectionTerm i α j σ b a = 0` for all `b, a`. -/
theorem isPseudoholomorphic_graph_iff
    (J : SmoothAlmostComplexStructure 𝓘(ℝ, B × V) (B × V))
    (i : B →L[ℝ] B) (hi : ∀ a, i (i a) = -a)
    (α : B × V → B →L[ℝ] V) (j : B × V → V →L[ℝ] V) {σ : B → V}
    (hJ : ∀ b, (J.toEndomorphism (b, σ b) : (B × V) →L[ℝ] B × V) =
      blockEndomorphism i α j (b, σ b)) :
    IsPseudoholomorphic (SmoothAlmostComplexStructure.const i hi) J (fun x ↦ (x, σ x)) ↔
      Differentiable ℝ σ ∧ ∀ b a, sectionTerm i α j σ b a = 0 := by
  rw [isPseudoholomorphic_iff, Differentiable, ← forall_and]
  exact forall_congr' fun b ↦ isPseudoholomorphicAt_graph_iff J i hi α j (hJ b)

/-- Specialization of `isPseudoholomorphicAt_graph_iff` when the base `B` is a complex normed space
equipped with `SmoothAlmostComplexStructure.ofComplexManifold B B`. -/
theorem isPseudoholomorphicAt_ofComplexManifold_graph_iff
    {C : Type*} [NormedAddCommGroup C] [NormedSpace ℂ C]
    (J : SmoothAlmostComplexStructure 𝓘(ℝ, C × V) (C × V))
    (α : C × V → C →L[ℝ] V) (j : C × V → V →L[ℝ] V) {σ : C → V} {b : C}
    (hJ : (J.toEndomorphism (b, σ b) : (C × V) →L[ℝ] C × V) =
      blockEndomorphism (Complex.I • ContinuousLinearMap.id ℝ C) α j (b, σ b)) :
    IsPseudoholomorphicAt (SmoothAlmostComplexStructure.ofComplexManifold C C) J
        (fun x ↦ (x, σ x)) b ↔
      DifferentiableAt ℝ σ b ∧
        ∀ a, sectionTerm (Complex.I • ContinuousLinearMap.id ℝ C) α j σ b a = 0 := by
  have hi (a : C) : (Complex.I • ContinuousLinearMap.id ℝ C)
      ((Complex.I • ContinuousLinearMap.id ℝ C) a) = -a := by simp [smul_smul, Complex.I_mul_I]
  have heq : SmoothAlmostComplexStructure.ofComplexManifold C C =
      SmoothAlmostComplexStructure.const (Complex.I • ContinuousLinearMap.id ℝ C) hi := by
    apply SmoothAlmostComplexStructure.toEndomorphism_injective; ext x v
    let v' : C := v
    exact (congrArg (· v')
      (SmoothAlmostComplexStructure.toEndomorphism_ofComplexManifold (E := C) x)).trans
      (congrArg (· v') (SmoothAlmostComplexStructure.const_toEndomorphism_apply _ hi x)).symm
  rw [heq]; exact isPseudoholomorphicAt_graph_iff J _ hi α j hJ

/-! ### Split families and constant sections -/

/-- When the connection block vanishes at `(b, σ b)`, the section equation reduces to
`(i, j(b, σ b))`-complex-linearity of `fderiv ℝ σ b`. -/
theorem isPseudoholomorphicAt_graph_iff_isComplexLinear_of_connection_eq_zero
    (J : SmoothAlmostComplexStructure 𝓘(ℝ, B × V) (B × V))
    (i : B →L[ℝ] B) (hi : ∀ a, i (i a) = -a)
    (α : B × V → B →L[ℝ] V) (j : B × V → V →L[ℝ] V) {σ : B → V} {b : B}
    (hJ : (J.toEndomorphism (b, σ b) : (B × V) →L[ℝ] B × V) =
      blockEndomorphism i α j (b, σ b))
    (hj : ∀ v, j (b, σ b) (j (b, σ b) v) = -v)
    (hα : α (b, σ b) = 0) :
    IsPseudoholomorphicAt (SmoothAlmostComplexStructure.const i hi) J (fun x ↦ (x, σ x)) b ↔
      DifferentiableAt ℝ σ b ∧
        IsComplexLinear i.toLinearMap (j (b, σ b)).toLinearMap (fderiv ℝ σ b).toLinearMap := by
  rw [isPseudoholomorphicAt_graph_iff J i hi α j hJ]
  refine and_congr_right fun _ ↦ ?_
  rw [isComplexLinear_iff_complexAntilinearPart_eq_zero (LinearMap.ext hj) _, LinearMap.ext_iff]
  refine forall_congr' fun a ↦ ?_
  rw [sectionTerm_eq_two_smul_complexAntilinearPart_add, hα, zero_apply,
    add_zero, LinearMap.zero_apply, smul_eq_zero, or_iff_right (two_ne_zero' ℝ)]

/-- For a constant section `x ↦ (x, v₀)`, `sectionTerm` reduces to `α(b, v₀)(i a)`. -/
@[simp]
theorem sectionTerm_const (i : B →L[ℝ] B) (α : B × V → B →L[ℝ] V) (j : B × V → V →L[ℝ] V)
    (v₀ : V) (b a : B) :
    sectionTerm i α j (fun _ ↦ v₀) b a = α (b, v₀) (i a) := by
  simp [sectionTerm_def]

/-- A constant section `x ↦ (x, v₀)` (e.g. a marked section straightened in product coordinates) is
`(i, J)`-pseudoholomorphic at `b` if and only if the connection block vanishes at `(b, v₀)`. -/
theorem isPseudoholomorphicAt_graph_const_iff
    (J : SmoothAlmostComplexStructure 𝓘(ℝ, B × V) (B × V))
    (i : B →L[ℝ] B) (hi : ∀ a, i (i a) = -a)
    (α : B × V → B →L[ℝ] V) (j : B × V → V →L[ℝ] V) (v₀ : V) {b : B}
    (hJ : (J.toEndomorphism (b, v₀) : (B × V) →L[ℝ] B × V) =
      blockEndomorphism i α j (b, v₀)) :
    IsPseudoholomorphicAt (SmoothAlmostComplexStructure.const i hi) J (fun x ↦ (x, v₀)) b ↔
      α (b, v₀) = 0 := by
  rw [isPseudoholomorphicAt_graph_iff J i hi α j hJ]
  simp only [differentiableAt_const, true_and, sectionTerm_const]
  exact ⟨fun h ↦ ContinuousLinearMap.ext fun a ↦ by simpa [hi a] using h (-i a),
    fun h a ↦ by simp [h]⟩

end TauCeti.ComplexStructureFamily
