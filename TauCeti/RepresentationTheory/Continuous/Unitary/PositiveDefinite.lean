/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.Gram.PosSemidef
public import TauCeti.Analysis.PositiveDefinite.Kernel.Kolmogorov
public import TauCeti.RepresentationTheory.Continuous.Unitary.Basic

/-!
# Positive-definite functions on groups and unitary representations

A function `φ : G → ℂ` on a group is positive definite when
`∑ᵢ ∑ⱼ conj (cᵢ) cⱼ φ (gᵢ⁻¹ gⱼ) ≥ 0` for all finite families, that is, when the kernel
`(g, h) ↦ φ (g⁻¹ * h)` is positive semidefinite in the sense of Mathlib's `Matrix.PosSemidef`
for matrices indexed by `G`. No topology on `G` is involved: this is the theory for discrete
groups.

The coefficients `g ↦ ⟪ξ, π g ξ⟫` of unitary representations are positive definite, and the
GNS construction shows that every positive-definite function arises this way. The GNS space of
`φ` is the Kolmogorov space of the kernel `(g, h) ↦ φ (g⁻¹ * h)`, with feature vectors
`gnsVector g` satisfying `⟪gnsVector g, gnsVector h⟫ = φ (g⁻¹ * h)`. Left translation of the
feature vectors preserves the kernel, so it extends to a unitary representation in which
`gnsVector 1` is a cyclic vector with coefficient `φ`. Any other unitary representation with a
vector whose coefficient is `φ` receives an intertwining linear isometry from the GNS space, which
is onto when that vector is cyclic.

## Main declarations

* `ContRepresentation.IsUnitary.posSemidef_inner_apply_inv_mul`: coefficients of unitary
  representations are positive definite.
* `Matrix.PosSemidef.gnsRepresentation`: the GNS unitary representation of a positive-definite
  function, with `Matrix.PosSemidef.isUnitary_gnsRepresentation` and
  `Matrix.PosSemidef.inner_gnsVector_one_gnsRepresentation`.
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

open InnerProductSpace
open scoped ComplexConjugate ComplexOrder

namespace ContRepresentation.IsUnitary

variable {G V : Type*} [Group G] [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {π : ContRepresentation ℂ G V}

/-- The coefficient `g ↦ ⟪ξ, π g ξ⟫` of a unitary representation is positive definite: the kernel
`(g, h) ↦ ⟪ξ, π (g⁻¹ * h) ξ⟫` is positive semidefinite. -/
theorem posSemidef_inner_apply_inv_mul (hπ : π.IsUnitary) (ξ : V) :
    (Matrix.of fun g h : G ↦ ⟪ξ, π (g⁻¹ * h) ξ⟫_ℂ).PosSemidef := by
  convert TauCeti.posSemidef_gram ℂ fun g : G ↦ π g ξ using 1
  ext g h
  rw [Matrix.of_apply, Matrix.gram_apply, hπ.inner_apply_inv_mul]

end ContRepresentation.IsUnitary

namespace Matrix.PosSemidef

universe v

variable {G : Type v} [Group G] {φ : G → ℂ}

variable (hφ : (Matrix.of fun g h : G ↦ φ (g⁻¹ * h)).PosSemidef)

/-- The GNS Hilbert space of a positive-definite function `φ` on a group: the Kolmogorov space of
the kernel `(g, h) ↦ φ (g⁻¹ * h)`. -/
abbrev gnsSpace := KolmogorovSpace hφ

/-- The vector of the GNS space corresponding to a group element. -/
def gnsVector (g : G) : hφ.gnsSpace := hφ.kolmogorovFeature g

/-- Inner products of GNS vectors recover the positive-definite function. -/
@[simp]
theorem inner_gnsVector (g h : G) : ⟪hφ.gnsVector g, hφ.gnsVector h⟫_ℂ = φ (g⁻¹ * h) :=
  hφ.inner_kolmogorovFeature g h

/-- The GNS vectors span a dense subspace of the GNS space. -/
theorem gnsVector_dense :
    (Submodule.span ℂ (Set.range hφ.gnsVector)).topologicalClosure = ⊤ :=
  hφ.kolmogorovFeature_dense

private theorem dense_span_range_gnsVector :
    Dense (Submodule.span ℂ (Set.range hφ.gnsVector) : Set hφ.gnsSpace) :=
  Submodule.dense_iff_topologicalClosure_eq_top.mpr hφ.gnsVector_dense

private theorem gnsVector_mul_dense (g : G) :
    (Submodule.span ℂ (Set.range fun h ↦ hφ.gnsVector (g * h))).topologicalClosure = ⊤ := by
  rw [show Set.range (fun h ↦ hφ.gnsVector (g * h)) = Set.range hφ.gnsVector from
    (Equiv.mulLeft g).surjective.range_comp hφ.gnsVector]
  exact hφ.gnsVector_dense

/-- Left translation by `g` as a unitary operator on the GNS space, sending `gnsVector h` to
`gnsVector (g * h)`. It is the action of `g` in `gnsRepresentation`. -/
private def gnsTranslation (g : G) : hφ.gnsSpace ≃ₗᵢ[ℂ] hφ.gnsSpace :=
  hφ.kolmogorovEquiv (fun h ↦ hφ.gnsVector (g * h))
    (fun a b ↦ by simp [mul_assoc]) (hφ.gnsVector_mul_dense g)

@[simp]
private theorem gnsTranslation_gnsVector (g h : G) :
    hφ.gnsTranslation g (hφ.gnsVector h) = hφ.gnsVector (g * h) :=
  hφ.kolmogorovEquiv_apply _ _ _ h

/-- Two continuous linear operators on the GNS space agree when they agree on the GNS vectors. -/
private theorem continuousLinearMap_ext {S T : hφ.gnsSpace →L[ℂ] hφ.gnsSpace}
    (h : ∀ g, S (hφ.gnsVector g) = T (hφ.gnsVector g)) : S = T :=
  ContinuousLinearMap.ext_on hφ.dense_span_range_gnsVector (by rintro _ ⟨g, rfl⟩; exact h g)

/-- The GNS representation of a positive-definite function on a group: left translation of the
GNS vectors, `gnsVector h ↦ gnsVector (g * h)`. -/
def gnsRepresentation : ContRepresentation ℂ G hφ.gnsSpace :=
  .ofMonoidHom
    { toFun g := (hφ.gnsTranslation g).toContinuousLinearEquiv
      map_one' := hφ.continuousLinearMap_ext fun h ↦ by simp
      map_mul' g k := hφ.continuousLinearMap_ext fun h ↦ by simp [mul_assoc] }

/-- The GNS representation translates the GNS vectors on the left. -/
@[simp]
theorem gnsRepresentation_gnsVector (g h : G) :
    hφ.gnsRepresentation g (hφ.gnsVector h) = hφ.gnsVector (g * h) :=
  hφ.gnsTranslation_gnsVector g h

/-- Every GNS vector is the image of the vector at the identity under the GNS representation. -/
theorem gnsRepresentation_gnsVector_one (g : G) :
    hφ.gnsRepresentation g (hφ.gnsVector 1) = hφ.gnsVector g := by
  simp

/-- The GNS representation is unitary. -/
theorem isUnitary_gnsRepresentation : hφ.gnsRepresentation.IsUnitary :=
  -- Each action operator is, by construction, the linear isometry `gnsTranslation g`.
  (ContRepresentation.isUnitary_iff_norm_map _).mpr fun g x ↦ (hφ.gnsTranslation g).norm_map x

/-- A positive-definite function is the coefficient of the GNS vector at the identity in the GNS
representation. -/
theorem inner_gnsVector_one_gnsRepresentation (g : G) :
    ⟪hφ.gnsVector 1, hφ.gnsRepresentation g (hφ.gnsVector 1)⟫_ℂ = φ g := by
  simp

/-- The GNS vector at the identity is cyclic for the GNS representation. -/
theorem gnsRepresentation_gnsVector_one_dense :
    (Submodule.span ℂ
      (Set.range fun g ↦ hφ.gnsRepresentation g (hφ.gnsVector 1))).topologicalClosure = ⊤ := by
  simpa only [hφ.gnsRepresentation_gnsVector_one] using hφ.gnsVector_dense

/-- The squared distance between two GNS vectors in terms of the positive-definite function. -/
theorem norm_gnsVector_sub_sq (g h : G) :
    ‖hφ.gnsVector g - hφ.gnsVector h‖ ^ 2 = 2 * ((φ 1).re - (φ (g⁻¹ * h)).re) := by
  rw [@norm_sub_sq ℂ, ← inner_self_eq_norm_sq (𝕜 := ℂ), ← inner_self_eq_norm_sq (𝕜 := ℂ)]
  simp only [inner_gnsVector, inv_mul_cancel, RCLike.re_to_complex]
  ring

section Universal

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
  {π : ContRepresentation ℂ G V} (hπ : π.IsUnitary) {ξ : V} (hξ : ∀ g, ⟪ξ, π g ξ⟫_ℂ = φ g)

omit [CompleteSpace V] in
private theorem inner_apply_apply_of_coeff {π : ContRepresentation ℂ G V} (hπ : π.IsUnitary)
    {ξ : V} (hξ : ∀ g, ⟪ξ, π g ξ⟫_ℂ = φ g) (g h : G) :
    ⟪π g ξ, π h ξ⟫_ℂ = φ (g⁻¹ * h) := by
  rw [← hπ.inner_apply_inv_mul, hξ]

/-- The universal property of the GNS representation: if `ξ` is a vector of a unitary
representation `π` whose coefficient is `φ`, then `gnsVector g ↦ π g ξ` extends to a linear
isometry of the GNS space into the space of `π`. It intertwines the two representations
(`Matrix.PosSemidef.gnsIsometry_gnsRepresentation`). -/
def gnsIsometry : hφ.gnsSpace →ₗᵢ[ℂ] V :=
  hφ.kolmogorovIsometry (fun g ↦ π g ξ) (inner_apply_apply_of_coeff hπ hξ)

/-- The GNS isometry sends `gnsVector g` to `π g ξ`. -/
@[simp]
theorem gnsIsometry_gnsVector (g : G) : hφ.gnsIsometry hπ hξ (hφ.gnsVector g) = π g ξ :=
  hφ.kolmogorovIsometry_apply _ _ g

/-- The GNS isometry is the unique linear isometry sending `gnsVector g` to `π g ξ` for every
`g`. -/
theorem eq_gnsIsometry (T : hφ.gnsSpace →ₗᵢ[ℂ] V) (hT : ∀ g, T (hφ.gnsVector g) = π g ξ) :
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
def gnsEquiv (hcyc : (Submodule.span ℂ (Set.range fun g ↦ π g ξ)).topologicalClosure = ⊤) :
    hφ.gnsSpace ≃ₗᵢ[ℂ] V :=
  hφ.kolmogorovEquiv (fun g ↦ π g ξ) (inner_apply_apply_of_coeff hπ hξ) hcyc

/-- The GNS equivalence sends `gnsVector g` to `π g ξ`. -/
@[simp]
theorem gnsEquiv_gnsVector
    (hcyc : (Submodule.span ℂ (Set.range fun g ↦ π g ξ)).topologicalClosure = ⊤) (g : G) :
    hφ.gnsEquiv hπ hξ hcyc (hφ.gnsVector g) = π g ξ :=
  hφ.kolmogorovEquiv_apply _ _ _ g

/-- The GNS equivalence agrees with the GNS isometry. -/
theorem coe_gnsEquiv
    (hcyc : (Submodule.span ℂ (Set.range fun g ↦ π g ξ)).topologicalClosure = ⊤) :
    ⇑(hφ.gnsEquiv hπ hξ hcyc) = hφ.gnsIsometry hπ hξ := by
  have := hφ.eq_gnsIsometry hπ hξ (hφ.gnsEquiv hπ hξ hcyc).toLinearIsometry
    (hφ.gnsEquiv_gnsVector hπ hξ hcyc)
  exact congr(⇑$this)

/-- The GNS equivalence intertwines the GNS representation with `π`. -/
theorem gnsEquiv_gnsRepresentation
    (hcyc : (Submodule.span ℂ (Set.range fun g ↦ π g ξ)).topologicalClosure = ⊤) (g : G)
    (x : hφ.gnsSpace) :
    hφ.gnsEquiv hπ hξ hcyc (hφ.gnsRepresentation g x) = π g (hφ.gnsEquiv hπ hξ hcyc x) := by
  simpa only [coe_gnsEquiv] using hφ.gnsIsometry_gnsRepresentation hπ hξ g x

end Universal

end Matrix.PosSemidef

namespace TauCeti

universe v

variable {G : Type v} [Group G] {φ : G → ℂ}

/-- **GNS characterization of positive-definite functions.** A function `φ` on a group is positive
definite, in the sense that the kernel `(g, h) ↦ φ (g⁻¹ * h)` is positive semidefinite, exactly
when it is a coefficient `g ↦ ⟪ξ, π g ξ⟫` of a unitary representation `π` on a complex Hilbert
space. The Hilbert space may be taken in the universe of the group. -/
theorem posSemidef_inv_mul_iff_exists_isUnitary :
    (Matrix.of fun g h : G ↦ φ (g⁻¹ * h)).PosSemidef ↔
      ∃ (V : Type v) (_ : NormedAddCommGroup V) (_ : InnerProductSpace ℂ V) (_ : CompleteSpace V)
        (π : ContRepresentation ℂ G V) (ξ : V), π.IsUnitary ∧ ∀ g, φ g = ⟪ξ, π g ξ⟫_ℂ := by
  refine ⟨fun hφ ↦ ⟨hφ.gnsSpace, inferInstance, inferInstance, inferInstance,
    hφ.gnsRepresentation, hφ.gnsVector 1, hφ.isUnitary_gnsRepresentation,
    fun g ↦ (hφ.inner_gnsVector_one_gnsRepresentation g).symm⟩, ?_⟩
  rintro ⟨V, _, _, _, π, ξ, hπ, hξ⟩
  simpa only [hξ] using hπ.posSemidef_inner_apply_inv_mul ξ

end TauCeti
