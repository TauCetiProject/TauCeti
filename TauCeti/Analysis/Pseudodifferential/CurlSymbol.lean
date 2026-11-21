/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.HodgeStar.CrossProduct
public import TauCeti.Analysis.Pseudodifferential.DeRhamSymbol

/-!
# The principal symbol of the curl

Let `E` be an oriented three-dimensional real inner product space, the frequency (cotangent)
space of an oriented Riemannian three-manifold at a point. On one-forms the curl is `curl = ⋆ d`,
the exterior derivative `d : Ω¹ → Ω²` followed by the Hodge star `⋆ : Ω² → Ω¹`; identifying
one-forms with vector fields by the metric, it is the classical curl of a vector field. In the
Fourier convention `σ(∂ⱼ) = i ξⱼ` its principal symbol is

`σ(curl)(x, ξ) = i ⋆(ξ ∧ ·) : (⋀¹ E)_ℂ → (⋀¹ E)_ℂ`

(`TauCeti.HomogeneousSymbol.curl`), the complexification of `i` times the cross product
`v ↦ ξ × v`, characterized by `⟪⋆(ξ ∧ v), w⟫ = vol(ξ, v, w)`
(`Orientation.inner_hodgeStar_wedgeLeft_ιMulti`). It is the Hodge star applied to the de Rham
symbol `σ(d) = i ε_ξ` (`TauCeti.HomogeneousSymbol.coefficient_curl_eq_comp_extDeriv`).

The cross product is skew-adjoint, so `σ(curl)` is self-adjoint: the curl is formally self-adjoint
(`TauCeti.HomogeneousSymbol.adjoint_curl`). Write `σ(grad) = σ(d) = i ξ` on functions and
`σ(div) = σ(grad)† = -i ⟪ξ, ·⟫` for the symbol of the divergence `d*`. Then

* `curl ∘ grad = 0` and `div ∘ curl = 0` on symbols
  (`TauCeti.HomogeneousSymbol.curl_comp_extDeriv_zero`,
  `TauCeti.HomogeneousSymbol.adjoint_extDeriv_zero_comp_curl`);
* `σ(curl)² + σ(grad) σ(div) = ‖ξ‖² Id`, the symbol of the identity
  `curl curl - grad div = -Δ` on vector fields of `ℝ³`
  (`TauCeti.HomogeneousSymbol.curl_comp_curl_add_extDeriv_zero_comp_adjoint`). It is the
  Laplacian of the de Rham symbol complex on one-forms, rewritten with `⋆` and `σ(curl)† = σ(curl)`.

Consequently the symbol sequence of the complex `grad`, `curl`, `div`,

`0 → ℂ → (⋀¹ E)_ℂ → (⋀¹ E)_ℂ → ℂ → 0`,

is exact at both middle terms at every nonzero covector
(`TauCeti.HomogeneousSymbol.exact_extDeriv_zero_curl`,
`TauCeti.HomogeneousSymbol.exact_curl_adjoint_extDeriv_zero`). In particular the kernel of
`σ(curl)(x, ξ)` is the line `ℂ ξ` of gradient symbols, so **the curl is not elliptic**
(`TauCeti.HomogeneousSymbol.not_isElliptic_curl`). Reversing the orientation negates the curl
(`TauCeti.HomogeneousSymbol.curl_neg_orientation`).

## References

* M. F. Atiyah, I. M. Singer, *The index of elliptic operators: I*, Ann. of Math. 87 (1968),
  §7, pp. 520–522 (symbol sequences of elliptic complexes).
* F. W. Warner, *Foundations of Differentiable Manifolds and Lie Groups*, Graduate Texts in
  Mathematics 94, Springer (1983), §6.1 (the Hodge star).
-/

public section

noncomputable section

open Module

namespace TauCeti

namespace HomogeneousSymbol

variable (X E : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [Fact (finrank ℝ E = 3)]
  (o : Orientation ℝ E (Fin 3))

/-- **The principal symbol of the curl** `⋆ d` on one-forms of an oriented three-dimensional
space, in the Fourier convention `σ(∂ⱼ) = i ξⱼ`: at every position and every covector `ξ`, the
complexification of `i ⋆(ξ ∧ ·)`, that is of `i` times the cross product `v ↦ ξ × v`. It is
homogeneous of degree `1`. -/
def curl :
    HomogeneousSymbol X E (WithLp 2 (Complexification (⋀[ℝ]^1 E)))
      (WithLp 2 (Complexification (⋀[ℝ]^1 E))) 1 :=
  ofLinear X <| Complex.I • ((ContinuousLinearMap.complexifyL2ₗᵢ _ _).toContinuousLinearMap ∘L
    LinearMap.toContinuousLinearMap
      (LinearMap.toContinuousLinearMap.toLinearMap ∘ₗ
        LinearMap.llcomp ℝ (⋀[ℝ]^1 E) (⋀[ℝ]^(1 + 1) E) (⋀[ℝ]^1 E)
          (o.hodgeStar (k := 1 + 1) (l := 1) (Fact.out : finrank ℝ E = 3).symm).toLinearMap ∘ₗ
          ExteriorAlgebra.wedgeLeftₗ ℝ E 1))

variable {X E}

/-- The value of the curl symbol at `(x, ξ)` is the complexification of `i ⋆(ξ ∧ ·)`. -/
@[simp]
theorem coefficient_curl (p : X × E) :
    (curl X E o).coefficient p =
      Complex.I •
        ((o.hodgeStar (k := 1 + 1) (l := 1) (Fact.out : finrank ℝ E = 3).symm).toLinearMap ∘ₗ
          ExteriorAlgebra.wedgeLeft p.2 1).toContinuousLinearMap.complexifyL2 := by
  simp [curl, LinearMap.llcomp_apply']

/-- The curl symbol is the Hodge star `⋆ : (⋀² E)_ℂ → (⋀¹ E)_ℂ` applied to the de Rham symbol
`σ(d) = i ε_ξ` on one-forms. -/
theorem coefficient_curl_eq_comp_extDeriv (p : X × E) :
    (curl X E o).coefficient p =
      ContinuousLinearMap.complexifyL2 (LinearMap.toContinuousLinearMap
        (o.hodgeStar (k := 1 + 1) (l := 1) (Fact.out : finrank ℝ E = 3).symm).toLinearMap) ∘L
          (extDeriv X E 1).coefficient p := by
  rw [coefficient_curl, coefficient_extDeriv, ContinuousLinearMap.comp_smul,
    ← ContinuousLinearMap.complexifyL2_comp]
  -- what remains is `toContinuousLinearMap (⋆ ∘ₗ ε_ξ) = toContinuousLinearMap ⋆ ∘L ε_ξ`
  congr 2

/-- **The curl is formally self-adjoint**: the cross product `ξ × ·` is skew-adjoint, so
`σ(curl)† = σ(curl)`. -/
@[simp]
theorem adjoint_curl : (curl X E o).adjoint = curl X E o := by
  ext1
  funext p
  set C := (LinearMap.toContinuousLinearMap
    ((o.hodgeStar (k := 1 + 1) (l := 1) (Fact.out : finrank ℝ E = 3).symm).toLinearMap ∘ₗ
      ExteriorAlgebra.wedgeLeft p.2 1)).complexifyL2
  rw [coefficient_adjoint, coefficient_curl, ContinuousLinearMap.adjoint.map_smulₛₗ,
    ContinuousLinearMap.adjoint_complexifyL2, ← LinearMap.adjoint_toContinuousLinearMap,
    o.adjoint_hodgeStar_comp_wedgeLeft, pow_one, map_smul, ContinuousLinearMap.complexifyL2_smul,
    Complex.conj_I]
  -- The scalar actions on these operator spaces are reached through the submodule instances of
  -- `⋀¹ E`, which `rw` does not unfold, so the sign lemmas are used through typed terms.
  rw [(neg_one_smul ℝ C : (-1 : ℝ) • C = -C)]
  exact neg_smul_neg _ _

/-- **`curl ∘ grad = 0`** on symbols, since `⋆(ξ ∧ ξ ∧ ·) = 0`. -/
@[simp]
theorem curl_comp_extDeriv_zero : (curl X E o).comp (extDeriv X E 0) = 0 := by
  ext1
  funext p
  have h : (extDeriv X E 1).coefficient p ∘L (extDeriv X E 0).coefficient p = 0 :=
    coefficient_comp_coefficient_eq_zero (extDeriv_comp_extDeriv 0) p
  rw [coefficient_comp, coefficient_curl_eq_comp_extDeriv, ContinuousLinearMap.comp_assoc, h,
    ContinuousLinearMap.comp_zero, coefficient_zero, Pi.zero_apply]

/-- **`div ∘ curl = 0`** on symbols, where `σ(div) = σ(grad)†` is the symbol of the
codifferential on one-forms. -/
@[simp]
theorem adjoint_extDeriv_zero_comp_curl : (extDeriv X E 0).adjoint.comp (curl X E o) = 0 := by
  ext1
  funext p
  have h := congrArg ContinuousLinearMap.adjoint
    (coefficient_comp_coefficient_eq_zero (curl_comp_extDeriv_zero o) p)
  have hc : ContinuousLinearMap.adjoint ((curl X E o).coefficient p) = (curl X E o).coefficient p :=
    by rw [← coefficient_adjoint, adjoint_curl]
  rw [ContinuousLinearMap.adjoint_comp, map_zero, hc] at h
  rw [coefficient_comp, coefficient_adjoint, h, coefficient_zero, Pi.zero_apply]

/-- **The symbol of `curl curl - grad div = -Δ`**: `σ(curl)² + σ(grad) σ(div) = ‖ξ‖² Id` on
complex one-forms. -/
theorem coefficient_curl_comp_curl_add_extDeriv_zero_comp_adjoint (p : X × E) :
    ((curl X E o).comp (curl X E o)).coefficient p +
        ((extDeriv X E 0).comp (extDeriv X E 0).adjoint).coefficient p =
      (‖p.2‖ ^ 2 : ℝ) • ContinuousLinearMap.id ℂ _ := by
  -- With `σ(curl) = ⋆ σ(d)`, `σ(curl)† = σ(curl)` and `⋆† ⋆ = 1`, this is the Laplacian
  -- `σ(d) σ(d)† + σ(d)† σ(d)` of the de Rham symbol complex on one-forms.
  have h := coefficient_hodgeLaplacian_extDeriv (X := X) (E := E) 0 p
  rw [coefficient_hodgeLaplacian, ContinuousLinearMap.hodgeLaplacian_def] at h
  rw [coefficient_comp, coefficient_comp]
  nth_rw 1 [← adjoint_curl o]
  rw [coefficient_adjoint, coefficient_curl_eq_comp_extDeriv, ContinuousLinearMap.adjoint_comp,
    ContinuousLinearMap.comp_assoc]
  set S := ContinuousLinearMap.complexifyL2 (LinearMap.toContinuousLinearMap
    (o.hodgeStar (k := 1 + 1) (l := 1) (Fact.out : finrank ℝ E = 3).symm).toLinearMap)
  -- `⋆` is an isometry, so `⋆† ⋆ = 1`
  have hS : ContinuousLinearMap.adjoint S ∘L S = ContinuousLinearMap.id ℂ _ := by
    rw [ContinuousLinearMap.adjoint_complexifyL2, ← ContinuousLinearMap.complexifyL2_comp,
      ← ContinuousLinearMap.complexifyL2_id]
    congr 1
    refine ContinuousLinearMap.ext fun x ↦ ext_inner_right ℝ fun y ↦ ?_
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_left]
    simp
  rw [← ContinuousLinearMap.comp_assoc _ S, hS, ContinuousLinearMap.id_comp, add_comm,
    coefficient_adjoint]
  exact h

/-- **The symbol of `curl curl - grad div = -Δ`**: `σ(curl)² + σ(grad) σ(div)` is the symbol
`‖ξ‖² Id` of degree `2`. -/
theorem curl_comp_curl_add_extDeriv_zero_comp_adjoint :
    (curl X E o).comp (curl X E o) + (extDeriv X E 0).comp (extDeriv X E 0).adjoint =
      normRpow X E _ (1 + 1) :=
  ext_of_ne_zero fun x ξ hξ ↦ by
    rw [coefficient_add, Pi.add_apply,
      coefficient_curl_comp_curl_add_extDeriv_zero_comp_adjoint,
      coefficient_normRpow_of_ne_zero _ _ _ hξ, one_add_one_eq_two, Real.rpow_two]

/-- **Exactness at the first one-forms**: at a nonzero covector `ξ`, the kernel of `σ(curl)` is the
image `ℂ ξ` of `σ(grad)`. -/
theorem exact_extDeriv_zero_curl {x : X} {ξ : E} (hξ : ξ ≠ 0) :
    Function.Exact ((extDeriv X E 0).coefficient (x, ξ)) ((curl X E o).coefficient (x, ξ)) := by
  have hξ' : (‖ξ‖ ^ 2 : ℝ) ≠ 0 := by positivity
  intro v
  constructor
  · intro hv
    refine ⟨((‖ξ‖ ^ 2)⁻¹ : ℝ) • (extDeriv X E 0).adjoint.coefficient (x, ξ) v, ?_⟩
    have h := congrArg (· v)
      (coefficient_curl_comp_curl_add_extDeriv_zero_comp_adjoint o (x, ξ))
    simp only [add_apply, coefficient_comp, ContinuousLinearMap.comp_apply, hv, map_zero,
      zero_add, smul_apply, ContinuousLinearMap.id_apply] at h
    rw [ContinuousLinearMap.map_smul_of_tower, h, smul_smul, inv_mul_cancel₀ hξ', one_smul]
  · rintro ⟨w, rfl⟩
    exact congrArg (· w) (coefficient_comp_coefficient_eq_zero (curl_comp_extDeriv_zero o) (x, ξ))

/-- **Exactness at the second one-forms**: at a nonzero covector `ξ`, the kernel of
`σ(div) = σ(grad)†` is the image of `σ(curl)`. -/
theorem exact_curl_adjoint_extDeriv_zero {x : X} {ξ : E} (hξ : ξ ≠ 0) :
    Function.Exact ((curl X E o).coefficient (x, ξ))
      ((extDeriv X E 0).adjoint.coefficient (x, ξ)) := by
  have hξ' : (‖ξ‖ ^ 2 : ℝ) ≠ 0 := by positivity
  intro v
  constructor
  · intro hv
    refine ⟨((‖ξ‖ ^ 2)⁻¹ : ℝ) • (curl X E o).coefficient (x, ξ) v, ?_⟩
    have h := congrArg (· v)
      (coefficient_curl_comp_curl_add_extDeriv_zero_comp_adjoint o (x, ξ))
    simp only [add_apply, coefficient_comp, ContinuousLinearMap.comp_apply, hv, map_zero,
      add_zero, smul_apply, ContinuousLinearMap.id_apply] at h
    rw [ContinuousLinearMap.map_smul_of_tower, h, smul_smul, inv_mul_cancel₀ hξ', one_smul]
  · rintro ⟨w, rfl⟩
    exact congrArg (· w)
      (coefficient_comp_coefficient_eq_zero (adjoint_extDeriv_zero_comp_curl o) (x, ξ))

/-- **The curl is not elliptic**: at every nonzero covector `ξ`, `σ(curl)(ξ)` kills the gradient
symbol `σ(grad)(ξ) w = i ξ w`, which is nonzero for `w ≠ 0`. -/
theorem not_isElliptic_curl [Nonempty X] : ¬ (curl X E o).IsElliptic := by
  intro h
  have h3 : finrank ℝ E = 3 := Fact.out
  have : Nontrivial E := Module.nontrivial_of_finrank_pos (R := ℝ) (by omega)
  obtain ⟨ξ, hξ⟩ := exists_ne (0 : E)
  have : Nontrivial (WithLp 2 (Complexification (⋀[ℝ]^0 E))) :=
    Module.nontrivial_of_finrank_pos (R := ℂ) (by simp [WithLp.finrank_complexification])
  obtain ⟨w, hw⟩ := exists_ne (0 : WithLp 2 (Complexification (⋀[ℝ]^0 E)))
  set x := Classical.arbitrary X
  have h0 : (curl X E o).coefficient (x, ξ) ((extDeriv X E 0).coefficient (x, ξ) w) = 0 :=
    (exact_extDeriv_zero_curl o hξ _).2 ⟨w, rfl⟩
  have h1 : (extDeriv X E 0).coefficient (x, ξ) w = 0 :=
    (isElliptic_iff.1 h x ξ hξ).injective (h0.trans (map_zero _).symm)
  exact hw (injective_extDeriv_zero hξ (h1.trans (map_zero _).symm))

/-- Reversing the orientation negates the curl. -/
@[simp]
theorem curl_neg_orientation : curl X E (-o) = -curl X E o := by
  have hk : 1 + 1 + 1 = finrank ℝ E := (Fact.out : finrank ℝ E = 3).symm
  have h : ((-o).hodgeStar hk).toLinearMap = (-1 : ℝ) • (o.hodgeStar hk).toLinearMap :=
    LinearMap.ext fun x ↦ by simp
  ext1
  funext p
  set C := (LinearMap.toContinuousLinearMap
    ((o.hodgeStar hk).toLinearMap ∘ₗ ExteriorAlgebra.wedgeLeft p.2 1)).complexifyL2
  rw [coefficient_neg, Pi.neg_apply, coefficient_curl, coefficient_curl, h, LinearMap.smul_comp,
    map_smul, ContinuousLinearMap.complexifyL2_smul, smul_comm]
  -- The scalar actions on these operator spaces are reached through the submodule instances of
  -- `⋀¹ E`, which `rw` does not unfold, so the sign lemma is used through a typed term.
  exact neg_one_smul ℝ (Complex.I • C)

end HomogeneousSymbol

end TauCeti
