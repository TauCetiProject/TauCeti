/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.SmoothEmbedding
public import TauCeti.Geometry.Contact.Distribution
public import TauCeti.Geometry.Manifold.Distribution.Horizontal
import TauCeti.Geometry.Manifold.Immersion.Basic
import TauCeti.Geometry.Manifold.IsManifold.Basic
import TauCeti.Geometry.Manifold.SmoothEmbedding.Diffeomorph
import TauCeti.LinearAlgebra.BilinearForm.Orthogonal

/-!
# Isotropic and Legendrian maps into contact manifolds

Let `ξ` be a hyperplane field on a manifold `M`. A map `f : N → M` is horizontal for `ξ`
(`TauCeti.IsHorizontalMap`) when every tangent image `df_y(T_y N)` lies in the hyperplane
`ξ_(f y)`. When `ξ` is a contact structure such maps are called **isotropic**; an isotropic smooth
immersion parametrizes an immersed isotropic submanifold. The source is an arbitrary charted space
and `f` need not be injective, so embedded and immersed submanifolds are treated alike.

The Levi form `L_ξ(u, v) = -[U, V] mod ξ` of a `C¹` hyperplane field vanishes on the tangent
images of every `C²` horizontal map (`TauCeti.IsHorizontalMap.distributionLeviForm_eq_zero`, in
`TauCeti.Geometry.Contact.Levi`). Since the Levi form of a contact structure is a nondegenerate
alternating form with values in the line `TM ⧸ ξ`, a tangent image on which it vanishes has at
most half the dimension of `ξ`. So an isotropic map with injective differential
into a contact manifold of dimension `2 n + 1` has a source of dimension at most `n`
(`TauCeti.IsHorizontalMap.two_mul_finrank_add_one_le`). None of this uses a coorientation of `ξ`.

For a global one-form `α`, a smooth map is horizontal for `ker α` exactly when it pulls `α` back
to zero (`TauCeti.SmoothForm.isHorizontalMap_kerDistribution_iff_mpullback_eq_zero`, in
`TauCeti.Geometry.Contact.Pullback`), and then it also pulls `dα` back to zero.

A **Legendrian immersion** (`TauCeti.IsLegendrianImmersion`) into a contact manifold of
dimension `2 n + 1` is a smooth isotropic immersion from a manifold of dimension `n`, the
largest dimension allowed. A **Legendrian embedding** (`TauCeti.IsLegendrianEmbedding`) is
moreover a topological embedding, so that it parametrizes an embedded Legendrian submanifold;
the image of a Legendrian immersion may have self-intersections.
The tangent image of a Legendrian immersion at every point is its own Levi orthogonal in the
contact hyperplane
(`TauCeti.IsLegendrianImmersion.mem_range_mfderiv_of_distributionLeviForm_eq_zero`), the contact
counterpart of the maximality of Lagrangian subspaces. Both notions are unchanged by
reparametrizing the source (`TauCeti.isLegendrianImmersion_comp_diffeomorph_iff`) and are
transported by contactomorphisms (`TauCeti.isLegendrianImmersion_diffeomorph_comp_iff`).

## Main declarations

* `TauCeti.IsHorizontalMap.two_mul_finrank_add_one_le`: the dimension bound `2 dim N + 1 ≤ dim M`
  for isotropic maps into a contact manifold with injective differential at some point.
* `TauCeti.IsLegendrianImmersion`, `TauCeti.IsLegendrianEmbedding`: Legendrian immersions and
  embeddings.
* `TauCeti.IsLegendrianImmersion.mem_range_mfderiv_of_distributionLeviForm_eq_zero`: the tangent
  images of a Legendrian immersion are maximal isotropic for the Levi form.
* `TauCeti.isLegendrianImmersion_comp_diffeomorph_iff`,
  `TauCeti.isLegendrianImmersion_diffeomorph_comp_iff`: invariance under reparametrization and
  transport by contactomorphisms, with their embedding counterparts.

## References

* H. Geiges, *An Introduction to Contact Topology*, Cambridge Studies in Advanced Mathematics 109
  (2008), Chapters 1 and 2 (isotropic and Legendrian submanifolds and the bound on their
  dimension).
-/

public section

noncomputable section

open Set Filter Function Module Bundle
open scoped Manifold Topology ContDiff

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  {E' H' N : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  {J : ModelWithCorners ℝ E' H'} [TopologicalSpace N] [ChartedSpace H' N]
  {D : Π x : M, Submodule ℝ (TangentSpace I x)} {f : N → M}

/-! ### The dimension bound -/

section DimensionBound

variable [CompleteSpace E] [FiniteDimensional ℝ E] [IsManifold I 2 M] [IsManifold J 2 N]
  {n : ℕ∞ω} {k : ℕ}

/-- **Isotropic maps into a contact manifold have at most half the dimension of the contact
hyperplanes.** If `D` is a `C^n` contact structure, with `1 ≤ n`, on a manifold of dimension
`2 m + 1`, and `f` is horizontal for `D`, that is isotropic, of class `C²` at `y` and with
injective differential at `y`, then `N` has dimension at most `m`: `2 dim N + 1 ≤ dim M`. -/
theorem IsHorizontalMap.two_mul_finrank_add_one_le [IsManifold I (n + 1) M]
    (hD : IsContactDistribution I n D) (hn : 1 ≤ n) (hf : IsHorizontalMap J D f) {y : N}
    (hfy : ContMDiffAt J I 2 f y) (hinj : Injective (mfderiv J I f y)) :
    2 * finrank ℝ E' + 1 ≤ finrank ℝ E := by
  have : FiniteDimensional ℝ (TangentSpace I (f y)) := inferInstanceAs (FiniteDimensional ℝ E)
  have hk : finrank ℝ E - 1 + 1 = finrank ℝ E := by
    have := hD.finrank_add_one (f y)
    omega
  -- The tangent image, as a subspace of the contact hyperplane.
  set W := (LinearMap.range (mfderiv J I f y).toLinearMap).comap (D (f y)).subtype
  have hW : ∀ u ∈ W, ∀ u' ∈ W, distributionLeviForm D (f y) u u' = 0 := by
    rintro ⟨_, hu⟩ ⟨v, rfl⟩ ⟨_, hu'⟩ ⟨w, rfl⟩
    exact hf.distributionLeviForm_eq_zero hD.isContMDiffDistribution hk hn hfy v w
  have hle := LinearMap.two_mul_finrank_le_finrank_of_apply_eq_zero_of_injective
    (hD.bijective_distributionLeviForm (f y)).injective (hD.finrank_quotient (f y)) hW
  have hWf : finrank ℝ W = finrank ℝ E' := by
    rw [LinearEquiv.finrank_eq (Submodule.comapSubtypeEquivOfLe (hf.range_mfderiv_le y)),
      LinearMap.finrank_range_of_inj hinj]
    exact finrank_tangentSpace y
  have := hD.finrank_add_one (f y)
  omega

end DimensionBound

/-! ### Legendrian immersions and embeddings -/

variable [CompleteSpace E] [FiniteDimensional ℝ E] [IsManifold I 2 M]

variable (J) in
/-- A **Legendrian immersion** for a contact structure `D` on a manifold of dimension `2 n + 1` is
a smooth immersion `f : N → M`, horizontal for `D`, from a manifold of dimension `n`. This is the
largest dimension of an isotropic immersion
(`TauCeti.IsHorizontalMap.two_mul_finrank_add_one_le`). Its image may have self-intersections. -/
structure IsLegendrianImmersion (D : Π x : M, Submodule ℝ (TangentSpace I x)) (f : N → M) :
    Prop where
  /-- The distribution of a Legendrian immersion is a contact structure. -/
  isContactDistribution : IsContactDistribution I 1 D
  /-- A Legendrian immersion is a smooth immersion. -/
  isImmersion : Manifold.IsImmersion J I ∞ f
  /-- A Legendrian immersion is tangent to the contact structure. -/
  isHorizontalMap : IsHorizontalMap J D f
  /-- A Legendrian immersion has a source of dimension `n` in a manifold of dimension
  `2 n + 1`. -/
  two_mul_finrank_add_one : 2 * finrank ℝ E' + 1 = finrank ℝ E

variable (J) in
/-- A **Legendrian embedding** for a contact structure `D` is a Legendrian immersion which is a
homeomorphism onto its image. It parametrizes an embedded Legendrian submanifold. -/
structure IsLegendrianEmbedding (D : Π x : M, Submodule ℝ (TangentSpace I x)) (f : N → M) : Prop
    extends IsLegendrianImmersion J D f where
  /-- A Legendrian embedding is a homeomorphism onto its image. -/
  isEmbedding : Topology.IsEmbedding f

/-- A Legendrian embedding is a smooth embedding. -/
theorem IsLegendrianEmbedding.isSmoothEmbedding (h : IsLegendrianEmbedding J D f) :
    Manifold.IsSmoothEmbedding J I ∞ f :=
  ⟨h.isImmersion, h.isEmbedding⟩

/-- A smooth embedding is a Legendrian embedding exactly when it is a Legendrian immersion. -/
@[simp]
theorem isLegendrianEmbedding_iff_of_isSmoothEmbedding (hf : Manifold.IsSmoothEmbedding J I ∞ f) :
    IsLegendrianEmbedding J D f ↔ IsLegendrianImmersion J D f :=
  ⟨fun h ↦ h.toIsLegendrianImmersion, fun h ↦ ⟨h, hf.isEmbedding⟩⟩

/-- A smooth isotropic immersion into a contact manifold of dimension `2 n + 1` from a nonempty
manifold is a Legendrian immersion exactly when its source has the largest possible dimension
`n`, equivalently when `2 dim N + 1 ≥ dim M`. -/
theorem isLegendrianImmersion_iff_finrank_le [IsManifold J 2 N] [Nonempty N] {n : ℕ∞ω}
    [IsManifold I (n + 1) M] (hD : IsContactDistribution I n D) (hn : 1 ≤ n)
    (hf : Manifold.IsImmersion J I ∞ f) (hfD : IsHorizontalMap J D f) :
    IsLegendrianImmersion J D f ↔ finrank ℝ E ≤ 2 * finrank ℝ E' + 1 := by
  refine ⟨fun h ↦ h.two_mul_finrank_add_one.ge, fun h ↦
    ⟨⟨hD.isContMDiffDistribution.of_le hn, hD.ne_top, hD.bijective_distributionLeviForm⟩, hf, hfD,
      le_antisymm ?_ h⟩⟩
  obtain ⟨y⟩ := ‹Nonempty N›
  exact hfD.two_mul_finrank_add_one_le hD hn ((hf.contMDiff y).of_le (by simp))
    (hf.mfderiv_injective (by simp) y)


/-- **The tangent images of a Legendrian immersion are maximal isotropic.** A vector of the contact
hyperplane at `f y` which is Levi-orthogonal to the tangent image `df_y(T_y N)` lies in it. This is
the contact counterpart of the fact that Lagrangian subspaces are maximal isotropic. -/
theorem IsLegendrianImmersion.mem_range_mfderiv_of_distributionLeviForm_eq_zero
    [IsManifold J 2 N] (h : IsLegendrianImmersion J D f) {y : N} {a : D (f y)}
    (ha : ∀ u, distributionLeviForm D (f y) a ⟨_, h.isHorizontalMap.mfderiv_mem y u⟩ = 0) :
    a.1 ∈ LinearMap.range (mfderiv J I f y).toLinearMap := by
  have : FiniteDimensional ℝ (TangentSpace I (f y)) := inferInstanceAs (FiniteDimensional ℝ E)
  have : IsManifold I (1 + 1) M := .of_le (n := 2) (by norm_num)
  have hD := h.isContactDistribution
  have hk : finrank ℝ E - 1 + 1 = finrank ℝ E := by
    have := hD.finrank_add_one (f y)
    omega
  -- The tangent image, as a subspace of the contact hyperplane.
  set W := (LinearMap.range (mfderiv J I f y).toLinearMap).comap (D (f y)).subtype
  have hW : ∀ u ∈ W, ∀ u' ∈ W, distributionLeviForm D (f y) u u' = 0 := by
    rintro ⟨_, hu⟩ ⟨v, rfl⟩ ⟨_, hu'⟩ ⟨w, rfl⟩
    exact h.isHorizontalMap.distributionLeviForm_eq_zero hD.isContMDiffDistribution hk le_rfl
      ((h.isImmersion.contMDiff y).of_le (by simp)) v w
  have hWf : finrank ℝ W = finrank ℝ E' := by
    rw [LinearEquiv.finrank_eq
        (Submodule.comapSubtypeEquivOfLe (h.isHorizontalMap.range_mfderiv_le y)),
      LinearMap.finrank_range_of_inj (h.isImmersion.mfderiv_injective (by simp) y)]
    exact finrank_tangentSpace y
  have hdim : 2 * finrank ℝ W = finrank ℝ (D (f y)) := by
    have := hD.finrank_add_one (f y)
    have := h.two_mul_finrank_add_one
    omega
  exact LinearMap.mem_of_apply_eq_zero_of_two_mul_finrank_eq
    (hD.bijective_distributionLeviForm (f y)).injective (hD.finrank_quotient (f y)) hW hdim
    fun b ⟨u, hu⟩ ↦ by
      obtain rfl : b = ⟨_, h.isHorizontalMap.mfderiv_mem y u⟩ := Subtype.ext hu.symm
      exact ha u

/-! ### Reparametrization and transport -/

section Reparametrization

variable {P : Type*} [TopologicalSpace P] [ChartedSpace H' P] [IsManifold J ∞ N] [IsManifold J ∞ P]

/-- **Independence of the parametrization.** Precomposing with a diffeomorphism of the source
does not change whether a map is a Legendrian immersion. -/
@[simp]
theorem isLegendrianImmersion_comp_diffeomorph_iff (φ : P ≃ₘ⟮J, J⟯ N) :
    IsLegendrianImmersion J D (f ∘ φ) ↔ IsLegendrianImmersion J D f :=
  ⟨fun h ↦ ⟨h.isContactDistribution, (isImmersion_comp_diffeomorph_iff φ).1 h.isImmersion,
      (isHorizontalMap_comp_diffeomorph_iff φ (by simp)).1 h.isHorizontalMap,
      h.two_mul_finrank_add_one⟩,
    fun h ↦ ⟨h.isContactDistribution, (isImmersion_comp_diffeomorph_iff φ).2 h.isImmersion,
      (isHorizontalMap_comp_diffeomorph_iff φ (by simp)).2 h.isHorizontalMap,
      h.two_mul_finrank_add_one⟩⟩

/-- **Independence of the parametrization.** Precomposing with a diffeomorphism of the source
does not change whether a map is a Legendrian embedding. -/
@[simp]
theorem isLegendrianEmbedding_comp_diffeomorph_iff (φ : P ≃ₘ⟮J, J⟯ N) :
    IsLegendrianEmbedding J D (f ∘ φ) ↔ IsLegendrianEmbedding J D f :=
  ⟨fun h ↦ (isLegendrianEmbedding_iff_of_isSmoothEmbedding
      ((isSmoothEmbedding_comp_diffeomorph_iff φ).1 h.isSmoothEmbedding)).2
      ((isLegendrianImmersion_comp_diffeomorph_iff φ).1 h.toIsLegendrianImmersion),
    fun h ↦ (isLegendrianEmbedding_iff_of_isSmoothEmbedding
      (isSmoothEmbedding_comp_diffeomorph φ h.isSmoothEmbedding)).2
      ((isLegendrianImmersion_comp_diffeomorph_iff φ).2 h.toIsLegendrianImmersion)⟩

end Reparametrization

section Transport

variable {M₂ : Type*} [TopologicalSpace M₂] [ChartedSpace H M₂] [IsManifold I ∞ M]
  [IsManifold I ∞ M₂] [IsManifold I 2 M₂] {D₂ : Π x : M₂, Submodule ℝ (TangentSpace I x)}

/-- **Transport by contactomorphisms.** If the differential of a diffeomorphism `ψ : M → M₂`
carries the contact structure `D` onto the contact structure `D₂`, then `ψ ∘ f` is a Legendrian
immersion for `D₂` exactly when `f` is a Legendrian immersion for `D`. -/
theorem isLegendrianImmersion_diffeomorph_comp_iff (ψ : M ≃ₘ⟮I, I⟯ M₂)
    (hD : IsContactDistribution I 1 D) (hD₂ : IsContactDistribution I 1 D₂)
    (hψ : ∀ x (v : TangentSpace I x), v ∈ D x ↔ mfderiv I I ψ x v ∈ D₂ (ψ x)) :
    IsLegendrianImmersion J D₂ (ψ ∘ f) ↔ IsLegendrianImmersion J D f :=
  ⟨fun h ↦ ⟨hD, (isImmersion_diffeomorph_comp_iff ψ).1 h.isImmersion,
      (isHorizontalMap_diffeomorph_comp_iff ψ (by simp) hψ).1 h.isHorizontalMap,
      h.two_mul_finrank_add_one⟩,
    fun h ↦ ⟨hD₂, (isImmersion_diffeomorph_comp_iff ψ).2 h.isImmersion,
      (isHorizontalMap_diffeomorph_comp_iff ψ (by simp) hψ).2 h.isHorizontalMap,
      h.two_mul_finrank_add_one⟩⟩

/-- **Transport by contactomorphisms.** If the differential of a diffeomorphism `ψ : M → M₂`
carries the contact structure `D` onto the contact structure `D₂`, then `ψ ∘ f` is a Legendrian
embedding for `D₂` exactly when `f` is a Legendrian embedding for `D`. -/
theorem isLegendrianEmbedding_diffeomorph_comp_iff (ψ : M ≃ₘ⟮I, I⟯ M₂)
    (hD : IsContactDistribution I 1 D) (hD₂ : IsContactDistribution I 1 D₂)
    (hψ : ∀ x (v : TangentSpace I x), v ∈ D x ↔ mfderiv I I ψ x v ∈ D₂ (ψ x)) :
    IsLegendrianEmbedding J D₂ (ψ ∘ f) ↔ IsLegendrianEmbedding J D f :=
  ⟨fun h ↦ (isLegendrianEmbedding_iff_of_isSmoothEmbedding
      ((isSmoothEmbedding_diffeomorph_comp_iff ψ).1 h.isSmoothEmbedding)).2
      ((isLegendrianImmersion_diffeomorph_comp_iff ψ hD hD₂ hψ).1 h.toIsLegendrianImmersion),
    fun h ↦ (isLegendrianEmbedding_iff_of_isSmoothEmbedding
      (isSmoothEmbedding_diffeomorph_comp h.isSmoothEmbedding ψ)).2
      ((isLegendrianImmersion_diffeomorph_comp_iff ψ hD hD₂ hψ).2 h.toIsLegendrianImmersion)⟩

end Transport

end TauCeti
