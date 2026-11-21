/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.Gram.PosSemidef
public import TauCeti.Analysis.PositiveDefinite.Kernel.Kolmogorov
public import TauCeti.RepresentationTheory.Continuous.Unitary.Basic
import TauCeti.Analysis.Normed.Operator.Dense

/-!
# Positive-definite functions on groups and unitary representations

A function `φ : G → 𝕜` on a group, valued in an `RCLike` field `𝕜` such as `ℝ` or `ℂ`, is
positive definite when `∑ᵢ ∑ⱼ conj (cᵢ) cⱼ φ (gᵢ⁻¹ gⱼ) ≥ 0` for all finite families, that is,
when the kernel `(g, h) ↦ φ (g⁻¹ * h)` is positive semidefinite in the sense of Mathlib's
`Matrix.PosSemidef` for matrices indexed by `G`. No topology on `G` is involved: this is the
theory for discrete groups.

The coefficients `g ↦ ⟪ξ, π g ξ⟫` of unitary representations are positive definite, and the
GNS construction shows that every positive-definite function arises this way. The GNS space of
`φ` is the Kolmogorov space of the kernel `(g, h) ↦ φ (g⁻¹ * h)`, with feature vectors
`gnsVector g` satisfying `⟪gnsVector g, gnsVector h⟫ = φ (g⁻¹ * h)`. Left translation of the
feature vectors preserves the kernel, so it extends to a unitary representation in which
`gnsVector 1` is a cyclic vector with coefficient `φ`. Any other unitary representation with a
vector whose coefficient is `φ` receives an intertwining linear isometry from the GNS space, which
is onto when that vector is cyclic. When `φ` vanishes at infinity, so does every coefficient of
its GNS representation, since the GNS vectors span a dense subspace.

## Main declarations

* `ContRepresentation.IsUnitary.posSemidef_inner_map_inv_mul`: coefficients of unitary
  representations are positive definite.
* `Matrix.PosSemidef.gnsRepresentation`: the GNS unitary representation of a positive-definite
  function, with `Matrix.PosSemidef.isUnitary_gnsRepresentation`,
  `Matrix.PosSemidef.inner_gnsVector_one_gnsRepresentation`,
  `Matrix.PosSemidef.norm_gnsVector_eq_one`, `Matrix.PosSemidef.norm_gnsVector_sub_lt` and
  `Matrix.PosSemidef.norm_gnsRepresentation_gnsVector_one_sub_lt`.
* `Matrix.PosSemidef.tendsto_inner_gnsRepresentation_of_tendsto_mul`,
  `Matrix.PosSemidef.eq_zero_of_eventually_gnsRepresentation_eq_self`,
  `Matrix.PosSemidef.invariants_restrict_gnsRepresentation_eq_bot`, and
  `Matrix.PosSemidef.tendsto_inner_gnsRepresentation_cofinite`: decay of matrix coefficients of
  the GNS representation along a filter or at infinity, and the resulting vanishing of invariant
  vectors.
* `Matrix.PosSemidef.gnsIsometry` and `Matrix.PosSemidef.gnsEquiv`: the universal property of
  the GNS representation.
* `TauCeti.posSemidef_inv_mul_iff_exists_isUnitary`: a function on a group is positive definite
  exactly when it is a coefficient of a unitary representation on a Hilbert space.

## References

* C. Anantharaman and S. Popa, *An Introduction to II₁ Factors*, §§1.6 and 16.1.
* B. Bekka, P. de la Harpe and A. Valette, *Kazhdan's Property (T)*, Appendix C.4.
-/

public section

noncomputable section

open Filter InnerProductSpace Topology
open scoped ComplexConjugate ComplexOrder

namespace ContRepresentation.IsUnitary

variable {𝕜 G V : Type*} [RCLike 𝕜] [Group G] [NormedAddCommGroup V] [InnerProductSpace 𝕜 V]
  {π : ContRepresentation 𝕜 G V}

/-- The coefficient `g ↦ ⟪ξ, π g ξ⟫` of a unitary representation is positive definite: the kernel
`(g, h) ↦ ⟪ξ, π (g⁻¹ * h) ξ⟫` is positive semidefinite. -/
theorem posSemidef_inner_map_inv_mul (hπ : π.IsUnitary) (ξ : V) :
    (Matrix.of fun g h : G ↦ ⟪ξ, π (g⁻¹ * h) ξ⟫_𝕜).PosSemidef := by
  convert TauCeti.posSemidef_gram 𝕜 fun g : G ↦ π g ξ using 1
  ext g h
  rw [Matrix.of_apply, Matrix.gram_apply, hπ.inner_map_inv_mul]

end ContRepresentation.IsUnitary

namespace Matrix.PosSemidef

universe u v

variable {𝕜 : Type u} [RCLike 𝕜] {G : Type v} [Group G] {φ : G → 𝕜}

variable (hφ : (Matrix.of fun g h : G ↦ φ (g⁻¹ * h)).PosSemidef)

/-- The GNS Hilbert space of a positive-definite function `φ` on a group: the Kolmogorov space of
the kernel `(g, h) ↦ φ (g⁻¹ * h)`. -/
abbrev gnsSpace := KolmogorovSpace hφ

/-- The vector of the GNS space corresponding to a group element. -/
def gnsVector (g : G) : hφ.gnsSpace := hφ.kolmogorovFeature g

/-- Inner products of GNS vectors recover the positive-definite function. -/
@[simp]
theorem inner_gnsVector (g h : G) : ⟪hφ.gnsVector g, hφ.gnsVector h⟫_𝕜 = φ (g⁻¹ * h) :=
  hφ.inner_kolmogorovFeature g h

/-- The GNS vectors span a dense subspace of the GNS space. -/
theorem gnsVector_dense :
    (Submodule.span 𝕜 (Set.range hφ.gnsVector)).topologicalClosure = ⊤ :=
  hφ.kolmogorovFeature_dense

private theorem dense_span_range_gnsVector :
    Dense (Submodule.span 𝕜 (Set.range hφ.gnsVector) : Set hφ.gnsSpace) :=
  Submodule.dense_iff_topologicalClosure_eq_top.mpr hφ.gnsVector_dense

private theorem gnsVector_mul_dense (g : G) :
    (Submodule.span 𝕜 (Set.range fun h ↦ hφ.gnsVector (g * h))).topologicalClosure = ⊤ := by
  have hrange : Set.range (fun h ↦ hφ.gnsVector (g * h)) = Set.range hφ.gnsVector :=
    (Equiv.mulLeft g).surjective.range_comp hφ.gnsVector
  rw [hrange]
  exact hφ.gnsVector_dense

/-- Left translation by `g` as a unitary operator on the GNS space, sending `gnsVector h` to
`gnsVector (g * h)`. It is the action of `g` in `gnsRepresentation`. -/
private def gnsTranslation (g : G) : hφ.gnsSpace ≃ₗᵢ[𝕜] hφ.gnsSpace :=
  hφ.kolmogorovEquiv (fun h ↦ hφ.gnsVector (g * h))
    (fun a b ↦ by simp [mul_assoc]) (hφ.gnsVector_mul_dense g)

@[simp]
private theorem gnsTranslation_gnsVector (g h : G) :
    hφ.gnsTranslation g (hφ.gnsVector h) = hφ.gnsVector (g * h) :=
  hφ.kolmogorovEquiv_apply _ _ _ h

/-- Two continuous linear operators on the GNS space agree when they agree on the GNS vectors. -/
private theorem continuousLinearMap_ext {S T : hφ.gnsSpace →L[𝕜] hφ.gnsSpace}
    (h : ∀ g, S (hφ.gnsVector g) = T (hφ.gnsVector g)) : S = T :=
  ContinuousLinearMap.ext_on hφ.dense_span_range_gnsVector (by rintro _ ⟨g, rfl⟩; exact h g)

/-- The GNS representation of a positive-definite function on a group: left translation of the
GNS vectors, `gnsVector h ↦ gnsVector (g * h)`. -/
def gnsRepresentation : ContRepresentation 𝕜 G hφ.gnsSpace :=
  .ofMonoidHom
    { toFun g := (hφ.gnsTranslation g).toContinuousLinearEquiv
      map_one' := hφ.continuousLinearMap_ext fun h ↦ by simp
      map_mul' g k := hφ.continuousLinearMap_ext fun h ↦ by simp [mul_assoc] }

/-- The action of `g` in the GNS representation is the unitary operator `gnsTranslation g`. -/
private theorem gnsRepresentation_apply (g : G) (x : hφ.gnsSpace) :
    hφ.gnsRepresentation g x = hφ.gnsTranslation g x :=
  rfl

/-- The GNS representation translates the GNS vectors on the left. -/
@[simp]
theorem gnsRepresentation_gnsVector (g h : G) :
    hφ.gnsRepresentation g (hφ.gnsVector h) = hφ.gnsVector (g * h) := by
  rw [gnsRepresentation_apply, gnsTranslation_gnsVector]

/-- Every GNS vector is the image of the vector at the identity under the GNS representation. -/
theorem gnsRepresentation_gnsVector_one (g : G) :
    hφ.gnsRepresentation g (hφ.gnsVector 1) = hφ.gnsVector g := by
  simp

/-- The GNS representation is unitary. -/
theorem isUnitary_gnsRepresentation : hφ.gnsRepresentation.IsUnitary :=
  (ContRepresentation.isUnitary_iff_norm_map _).mpr fun g x ↦ by
    rw [gnsRepresentation_apply, LinearIsometryEquiv.norm_map]

/-- A positive-definite function is the coefficient of the GNS vector at the identity in the GNS
representation. -/
theorem inner_gnsVector_one_gnsRepresentation (g : G) :
    ⟪hφ.gnsVector 1, hφ.gnsRepresentation g (hφ.gnsVector 1)⟫_𝕜 = φ g := by
  simp

/-- The GNS vector at the identity is cyclic for the GNS representation. -/
theorem gnsRepresentation_gnsVector_one_dense :
    (Submodule.span 𝕜
      (Set.range fun g ↦ hφ.gnsRepresentation g (hφ.gnsVector 1))).topologicalClosure = ⊤ := by
  simpa only [hφ.gnsRepresentation_gnsVector_one] using hφ.gnsVector_dense

/-- Every GNS vector of a normalized (`φ 1 = 1`) positive-definite function has unit norm. -/
theorem norm_gnsVector_eq_one (h1 : φ 1 = 1) (g : G) : ‖hφ.gnsVector g‖ = 1 := by
  have hsq : ‖hφ.gnsVector g‖ ^ 2 = 1 := by
    rw [@norm_sq_eq_re_inner 𝕜, hφ.inner_gnsVector, inv_mul_cancel, h1, RCLike.one_re]
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).mp hsq

/-- The squared distance between two GNS vectors in terms of the positive-definite function. -/
theorem norm_gnsVector_sub_sq (g h : G) :
    ‖hφ.gnsVector g - hφ.gnsVector h‖ ^ 2 =
      2 * (RCLike.re (φ 1) - RCLike.re (φ (g⁻¹ * h))) := by
  rw [@norm_sub_sq 𝕜, ← inner_self_eq_norm_sq (𝕜 := 𝕜), ← inner_self_eq_norm_sq (𝕜 := 𝕜)]
  simp only [inner_gnsVector, inv_mul_cancel]
  ring

/-- If a normalized positive-definite function `φ` satisfies `‖φ (g⁻¹ * h) - 1‖ < δ ^ 2 / 2` with
`δ > 0`, then the GNS vectors at `g` and `h` lie within distance `δ`. -/
theorem norm_gnsVector_sub_lt (h1 : φ 1 = 1) {g h : G} {δ : ℝ} (hδ : 0 < δ)
    (hgh : ‖φ (g⁻¹ * h) - 1‖ < δ ^ 2 / 2) :
    ‖hφ.gnsVector g - hφ.gnsVector h‖ < δ := by
  have hsq := hφ.norm_gnsVector_sub_sq g h
  rw [h1, RCLike.one_re] at hsq
  have hre : 1 - RCLike.re (φ (g⁻¹ * h)) < δ ^ 2 / 2 :=
    lt_of_le_of_lt (by simpa [norm_sub_rev] using RCLike.re_le_norm (1 - φ (g⁻¹ * h))) hgh
  exact (sq_lt_sq₀ (norm_nonneg _) hδ.le).mp (by linarith)

/-- If a normalized positive-definite function `φ` satisfies `‖φ g - 1‖ < δ ^ 2 / 2` with `δ > 0`,
then `g` moves the GNS vector at the identity by less than `δ`. -/
theorem norm_gnsRepresentation_gnsVector_one_sub_lt (h1 : φ 1 = 1) {g : G} {δ : ℝ} (hδ : 0 < δ)
    (hg : ‖φ g - 1‖ < δ ^ 2 / 2) :
    ‖hφ.gnsRepresentation g (hφ.gnsVector 1) - hφ.gnsVector 1‖ < δ := by
  rw [hφ.gnsRepresentation_gnsVector_one, norm_sub_rev]
  exact hφ.norm_gnsVector_sub_lt h1 hδ (by simpa using hg)

/-- If all double translates `i ↦ φ (a⁻¹ * s i * b)` converge to `0` along a filter `l`, then
every matrix coefficient `i ↦ ⟪x, π (s i) y⟫` of the GNS representation `π` converges to `0` along
`l`. -/
theorem tendsto_inner_gnsRepresentation_of_tendsto_mul {ι : Type*} {l : Filter ι} {s : ι → G}
    (hs : ∀ a b : G, Tendsto (fun i ↦ φ (a⁻¹ * s i * b)) l (𝓝 0)) (x y : hφ.gnsSpace) :
    Tendsto (fun i ↦ ⟪x, hφ.gnsRepresentation (s i) y⟫_𝕜) l (𝓝 0) := by
  set S := Submodule.span 𝕜 (Set.range hφ.gnsVector)
  -- Coefficients of GNS vectors are double translates of `φ`, so the claim holds on the span `S`.
  have hS : ∀ x ∈ S, ∀ y ∈ S,
      Tendsto (fun i ↦ ⟪x, hφ.gnsRepresentation (s i) y⟫_𝕜) l (𝓝 0) := by
    intro x hx y hy
    induction hx using Submodule.span_induction with
    | mem _ hx =>
      obtain ⟨a, rfl⟩ := hx
      induction hy using Submodule.span_induction with
      | mem _ hy =>
        obtain ⟨b, rfl⟩ := hy
        simpa [mul_assoc] using hs a b
      | zero => simpa using tendsto_const_nhds
      | add _ _ _ _ h₁ h₂ => simpa [inner_add_right] using h₁.add h₂
      | smul c _ _ h => simpa [inner_smul_right] using h.const_mul c
    | zero => simpa using tendsto_const_nhds
    | add _ _ _ _ h₁ h₂ => simpa [inner_add_left] using h₁.add h₂
    | smul c _ _ h => simpa [inner_smul_left] using h.const_mul (conj c)
  have hπ := hφ.isUnitary_gnsRepresentation
  have hD : Dense (S : Set hφ.gnsSpace) := hφ.dense_span_range_gnsVector
  have hS' : ∀ y ∈ S, Tendsto (fun i ↦ ⟪x, hφ.gnsRepresentation (s i) y⟫_𝕜) l (𝓝 0) := by
    intro y hy
    let f : ι → hφ.gnsSpace →L⋆[𝕜] 𝕜 := fun i ↦ innerSLFlip 𝕜 (hφ.gnsRepresentation (s i) y)
    have hbound : ∀ᶠ i in l, ‖f i‖ ≤ ‖y‖ := Eventually.of_forall fun i ↦
      (f i).opNorm_le_bound (norm_nonneg y) fun u ↦ by
        simpa [f, hπ.norm_map, mul_comm] using norm_inner_le_norm u (hφ.gnsRepresentation (s i) y)
    simpa [f] using ContinuousLinearMap.tendsto_apply_of_dense (g := 0) hD hbound
      (fun u hu ↦ by simpa [f] using hS u hu y hy) x
  let f : ι → hφ.gnsSpace →L[𝕜] 𝕜 := fun i ↦ (innerSL 𝕜 x).comp (hφ.gnsRepresentation (s i))
  have hbound : ∀ᶠ i in l, ‖f i‖ ≤ ‖x‖ := Eventually.of_forall fun i ↦
    (f i).opNorm_le_bound (norm_nonneg x) fun v ↦ by
      simpa [f, hπ.norm_map] using norm_inner_le_norm x (hφ.gnsRepresentation (s i) v)
  simpa [f] using ContinuousLinearMap.tendsto_apply_of_dense (g := 0) hD hbound
    (fun v hv ↦ by simpa [f] using hS' v hv) y

/-- If all double translates `i ↦ φ (a⁻¹ * s i * b)` converge to `0` along a nontrivial filter `l`,
then any vector in the GNS space fixed eventually by `gnsRepresentation (s i)` is zero. -/
theorem eq_zero_of_eventually_gnsRepresentation_eq_self {ι : Type*} {l : Filter ι} [l.NeBot]
    {s : ι → G} (hs : ∀ a b : G, Tendsto (fun i ↦ φ (a⁻¹ * s i * b)) l (𝓝 0))
    {v : hφ.gnsSpace} (hv : ∀ᶠ i in l, hφ.gnsRepresentation (s i) v = v) :
    v = 0 := by
  have hconst : Tendsto (fun i ↦ ⟪v, hφ.gnsRepresentation (s i) v⟫_𝕜) l (𝓝 ⟪v, v⟫_𝕜) :=
    tendsto_const_nhds.congr' (hv.mono fun i hi ↦ congrArg (⟪v, ·⟫_𝕜) hi.symm)
  exact inner_self_eq_zero.mp
    (tendsto_nhds_unique hconst (hφ.tendsto_inner_gnsRepresentation_of_tendsto_mul hs v v))

/-- If all double translates `i ↦ φ (a⁻¹ * f (s i) * b)` along a monoid homomorphism `f : K →* G`
converge to `0` along a nontrivial filter `l`, then the restricted GNS representation
`gnsRepresentation.restrict f` has no nonzero invariant vectors. -/
theorem invariants_restrict_gnsRepresentation_eq_bot {ι K : Type*} {l : Filter ι} [l.NeBot]
    [Monoid K] (f : K →* G) {s : ι → K}
    (hs : ∀ a b : G, Tendsto (fun i ↦ φ (a⁻¹ * f (s i) * b)) l (𝓝 0)) :
    (hφ.gnsRepresentation.restrict f).invariants = ⊥ :=
  (Submodule.eq_bot_iff _).mpr fun v hv ↦
    hφ.eq_zero_of_eventually_gnsRepresentation_eq_self hs <|
      Eventually.of_forall fun i ↦ by simpa using hv (s i)

/-- If a positive-definite function vanishes at infinity, then so does every coefficient
`g ↦ ⟪x, π g y⟫` of its GNS representation `π`. -/
theorem tendsto_inner_gnsRepresentation_cofinite (hφ0 : Tendsto φ cofinite (𝓝 0))
    (x y : hφ.gnsSpace) :
    Tendsto (fun g ↦ ⟪x, hφ.gnsRepresentation g y⟫_𝕜) cofinite (𝓝 0) :=
  hφ.tendsto_inner_gnsRepresentation_of_tendsto_mul (s := id) (fun a b ↦ by
    have hinj : Function.Injective fun g : G ↦ a⁻¹ * g * b :=
      fun g k h ↦ mul_left_cancel (mul_right_cancel h)
    exact hφ0.comp hinj.tendsto_cofinite) x y

section Universal

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace 𝕜 V] [CompleteSpace V]
  {π : ContRepresentation 𝕜 G V} (hπ : π.IsUnitary) {ξ : V} (hξ : ∀ g, ⟪ξ, π g ξ⟫_𝕜 = φ g)

omit [CompleteSpace V] in
private theorem inner_apply_apply_of_coeff {π : ContRepresentation 𝕜 G V} (hπ : π.IsUnitary)
    {ξ : V} (hξ : ∀ g, ⟪ξ, π g ξ⟫_𝕜 = φ g) (g h : G) :
    ⟪π g ξ, π h ξ⟫_𝕜 = φ (g⁻¹ * h) := by
  rw [← hπ.inner_map_inv_mul, hξ]

/-- The universal property of the GNS representation: if `ξ` is a vector of a unitary
representation `π` whose coefficient is `φ`, then `gnsVector g ↦ π g ξ` extends to a linear
isometry of the GNS space into the space of `π`. It intertwines the two representations
(`Matrix.PosSemidef.gnsIsometry_gnsRepresentation`). -/
def gnsIsometry : hφ.gnsSpace →ₗᵢ[𝕜] V :=
  hφ.kolmogorovIsometry (fun g ↦ π g ξ) (inner_apply_apply_of_coeff hπ hξ)

/-- The GNS isometry sends `gnsVector g` to `π g ξ`. -/
@[simp]
theorem gnsIsometry_gnsVector (g : G) : hφ.gnsIsometry hπ hξ (hφ.gnsVector g) = π g ξ :=
  hφ.kolmogorovIsometry_apply _ _ g

/-- The GNS isometry is the unique linear isometry sending `gnsVector g` to `π g ξ` for every
`g`. -/
theorem eq_gnsIsometry (T : hφ.gnsSpace →ₗᵢ[𝕜] V) (hT : ∀ g, T (hφ.gnsVector g) = π g ξ) :
    T = hφ.gnsIsometry hπ hξ :=
  hφ.kolmogorovIsometry_unique _ _ T hT

/-- The GNS isometry intertwines the GNS representation with `π`. -/
theorem gnsIsometry_gnsRepresentation (g : G) (x : hφ.gnsSpace) :
    hφ.gnsIsometry hπ hξ (hφ.gnsRepresentation g x) = π g (hφ.gnsIsometry hπ hξ x) := by
  let T := (hφ.gnsIsometry hπ hξ).toContinuousLinearMap
  have h : T.comp (hφ.gnsRepresentation g) = (π g).comp T :=
    ContinuousLinearMap.ext_on hφ.dense_span_range_gnsVector (by
      rintro _ ⟨h, rfl⟩
      simp [T, map_mul])
  exact congr($h x)

/-- When `ξ` is cyclic for `π`, the GNS isometry is a linear isometric equivalence: the GNS
representation is unitarily equivalent to every unitary representation with a cyclic vector
whose coefficient is `φ`. -/
def gnsEquiv (hcyc : (Submodule.span 𝕜 (Set.range fun g ↦ π g ξ)).topologicalClosure = ⊤) :
    hφ.gnsSpace ≃ₗᵢ[𝕜] V :=
  hφ.kolmogorovEquiv (fun g ↦ π g ξ) (inner_apply_apply_of_coeff hπ hξ) hcyc

/-- The GNS equivalence sends `gnsVector g` to `π g ξ`. -/
@[simp]
theorem gnsEquiv_gnsVector
    (hcyc : (Submodule.span 𝕜 (Set.range fun g ↦ π g ξ)).topologicalClosure = ⊤) (g : G) :
    hφ.gnsEquiv hπ hξ hcyc (hφ.gnsVector g) = π g ξ :=
  hφ.kolmogorovEquiv_apply _ _ _ g

/-- The GNS equivalence agrees with the GNS isometry. -/
theorem coe_gnsEquiv
    (hcyc : (Submodule.span 𝕜 (Set.range fun g ↦ π g ξ)).topologicalClosure = ⊤) :
    ⇑(hφ.gnsEquiv hπ hξ hcyc) = hφ.gnsIsometry hπ hξ := by
  have := hφ.eq_gnsIsometry hπ hξ (hφ.gnsEquiv hπ hξ hcyc).toLinearIsometry
    (hφ.gnsEquiv_gnsVector hπ hξ hcyc)
  exact congr(⇑$this)

/-- The GNS equivalence intertwines the GNS representation with `π`. -/
theorem gnsEquiv_gnsRepresentation
    (hcyc : (Submodule.span 𝕜 (Set.range fun g ↦ π g ξ)).topologicalClosure = ⊤) (g : G)
    (x : hφ.gnsSpace) :
    hφ.gnsEquiv hπ hξ hcyc (hφ.gnsRepresentation g x) = π g (hφ.gnsEquiv hπ hξ hcyc x) := by
  simpa only [coe_gnsEquiv] using hφ.gnsIsometry_gnsRepresentation hπ hξ g x

end Universal

end Matrix.PosSemidef

namespace TauCeti

universe u v

variable {𝕜 : Type u} [RCLike 𝕜] {G : Type v} [Group G] {φ : G → 𝕜}

/-- **GNS characterization of positive-definite functions.** A function `φ` on a group is positive
definite, in the sense that the kernel `(g, h) ↦ φ (g⁻¹ * h)` is positive semidefinite, exactly
when it is a coefficient `g ↦ ⟪ξ, π g ξ⟫` of a unitary representation `π` on a Hilbert space over
`𝕜`. The Hilbert space may be taken in the universe `max u v` of the scalar field and the group,
which is the universe of the group when `𝕜` is `ℝ` or `ℂ`. -/
theorem posSemidef_inv_mul_iff_exists_isUnitary :
    (Matrix.of fun g h : G ↦ φ (g⁻¹ * h)).PosSemidef ↔
      ∃ (V : Type (max u v)) (_ : NormedAddCommGroup V) (_ : InnerProductSpace 𝕜 V)
        (_ : CompleteSpace V)
        (π : ContRepresentation 𝕜 G V) (ξ : V), π.IsUnitary ∧ ∀ g, φ g = ⟪ξ, π g ξ⟫_𝕜 := by
  refine ⟨fun hφ ↦ ⟨hφ.gnsSpace, inferInstance, inferInstance, inferInstance,
    hφ.gnsRepresentation, hφ.gnsVector 1, hφ.isUnitary_gnsRepresentation,
    fun g ↦ (hφ.inner_gnsVector_one_gnsRepresentation g).symm⟩, ?_⟩
  rintro ⟨V, _, _, _, π, ξ, hπ, hξ⟩
  simpa only [hξ] using hπ.posSemidef_inner_map_inv_mul ξ

end TauCeti
