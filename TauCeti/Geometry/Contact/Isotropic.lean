/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Immersion
public import TauCeti.Geometry.Contact.Distribution
public import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.Smooth
public import TauCeti.Geometry.Manifold.Distribution.Isotropic
import TauCeti.Geometry.Manifold.Distribution.Annihilator
import TauCeti.Geometry.Manifold.IsManifold.Basic
import TauCeti.Geometry.Manifold.SmoothEmbedding.Diffeomorph
import TauCeti.LinearAlgebra.BilinearForm.Orthogonal

/-!
# Isotropic and Legendrian maps into a contact manifold

Let `ξ` be a field of hyperplanes on a manifold `M`, given as a distribution
`ξ x ⊆ T_x M`. A map `f : N → M` is **isotropic** for `ξ`
(`TauCeti.IsDistributionIsotropicMap J ξ f`, defined in
`TauCeti.Geometry.Manifold.Distribution.Isotropic`) when it is tangent to `ξ`: every tangent image
`df_y(T_y N)` lies in `ξ (f y)`. When `ξ = ker α` is the kernel of a smooth one-form, a smooth
map is isotropic exactly when it pulls `α` back to zero
(`TauCeti.SmoothForm.isDistributionIsotropicMap_kerDistribution_iff_mpullback_eq_zero`).

The tangent images of an isotropic map are isotropic for the Levi form
`L_ξ(u, v) = -[U, V] mod ξ` (`TauCeti.distributionLeviForm`) of any `C¹` hyperplane field:

`L_ξ(df u, df v) = 0` for all `u, v ∈ T_y N`

(`TauCeti.IsDistributionIsotropicMap.distributionLeviForm_eq_zero`), as soon as `f` is `C²` at
`y`. The proof pulls back a local defining one-form `α` of `ξ` near `f y`: since `f^* α` vanishes
near `y`, so does `f^* dα = d(f^* α)`
(`TauCeti.IsDistributionIsotropicMap.mextDeriv_apply_mfderiv_eq_zero`), and `α` carries the
Levi form to `dα` on `ξ`. No coorientation of `ξ` is used, so this also covers contact structures
that are not the kernel of a global one-form.

For a contact structure on a manifold of dimension `2 n + 1`, the Levi form is a nondegenerate
form on the `2 n`-dimensional hyperplanes `ξ x` with values in the line `T_x M ⧸ ξ x`. A subspace
on which it vanishes has dimension at most `n`, so an isotropic map with injective differential at
some point satisfies `2 dim N + 1 ≤ dim M`
(`TauCeti.IsDistributionIsotropicMap.two_mul_finrank_add_one_le`).

A **Legendrian immersion** (`TauCeti.IsLegendrianImmersion`) is a smooth isotropic immersion of
the maximal dimension, `2 dim N + 1 = dim M`; its image may have self-intersections. A
**Legendrian embedding** (`TauCeti.IsLegendrianEmbedding`) is one which is moreover a smooth
embedding. The tangent image of a Legendrian immersion at every point is its own orthogonal for
the Levi form: a vector of `ξ (f y)` that is Levi-orthogonal to `df_y(T_y N)` lies in it
(`TauCeti.IsLegendrianImmersion.mem_range_mfderiv_of_distributionLeviForm_eq_zero`). This is the
contact counterpart of the fact that Lagrangian subspaces are maximal isotropic. Both notions are
unchanged by reparametrizing the source
(`Diffeomorph.isLegendrianEmbedding_comp_diffeomorph_iff`) and are transported by diffeomorphisms
whose differential carries one distribution onto the other, such as contactomorphisms
(`Diffeomorph.isLegendrianEmbedding_diffeomorph_comp_iff`).

## Main declarations

* `TauCeti.SmoothForm.isDistributionIsotropicMap_kerDistribution_iff_mpullback_eq_zero`: isotropy
  for the kernel of a one-form is the vanishing of its pullback.
* `TauCeti.IsDistributionIsotropicMap.distributionLeviForm_eq_zero`: the Levi form vanishes on
  the tangent images of an isotropic map.
* `TauCeti.IsDistributionIsotropicMap.two_mul_finrank_add_one_le`: the dimension bound for
  isotropic maps into a contact manifold.
* `TauCeti.IsLegendrianImmersion`, `TauCeti.IsLegendrianEmbedding`: Legendrian immersions and
  embeddings.
* `Diffeomorph.isLegendrianImmersion_comp_diffeomorph_iff`,
  `Diffeomorph.isLegendrianImmersion_diffeomorph_comp_iff`: invariance under reparametrization and
  transport by contactomorphisms, with their embedding counterparts.

## References

* H. Geiges, *An Introduction to Contact Topology*, Cambridge Studies in Advanced Mathematics 109
  (2008), Chapters 1 and 2 (isotropic and Legendrian submanifolds and their dimension bound).
-/

public section

noncomputable section

open Set Filter Function Module Bundle Manifold
open scoped Manifold Topology ContDiff

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  {E' H' N : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  {J : ModelWithCorners ℝ E' H'} [TopologicalSpace N] [ChartedSpace H' N]
  {D : Π x : M, Submodule ℝ (TangentSpace I x)} {f : N → M}

/-! ### Kernels of one-forms -/

section Kernel

variable [IsManifold I ∞ M]

/-- A map is isotropic for the kernel of a one-form `α` exactly when `α` vanishes on all its
tangent images. -/
theorem SmoothForm.isDistributionIsotropicMap_kerDistribution_iff {α : SmoothForm I M ℝ 1} :
    IsDistributionIsotropicMap J α.kerDistribution f ↔
      ∀ y v, α.1 (f y) ![mfderiv J I f y v] = 0 := by
  simp only [isDistributionIsotropicMap_iff, SmoothForm.mem_kerDistribution]

/-- **Isotropy is the vanishing of the pullback.** A smooth map is isotropic for the kernel of a
smooth one-form `α` exactly when it pulls `α` back to zero. -/
theorem SmoothForm.isDistributionIsotropicMap_kerDistribution_iff_mpullback_eq_zero
    [IsManifold J ∞ N] {α : SmoothForm I M ℝ 1} (hf : ContMDiff J I ∞ f) :
    IsDistributionIsotropicMap J α.kerDistribution f ↔ SmoothForm.mpullback f hf α = 0 := by
  simp only [isDistributionIsotropicMap_iff, Subtype.ext_iff, funext_iff, SmoothForm.coe_mpullback,
    ZeroMemClass.coe_zero, Pi.zero_apply, mpullback_apply_eq_zero_iff_mem_ker,
    SmoothForm.mem_kerDistribution, RoughForm.mem_ker]

end Kernel

/-- The tangent image of an isotropic map, viewed inside the hyperplane at its image point, has
the same dimension as the tangent image itself. -/
private theorem IsDistributionIsotropicMap.finrank_comap_range
    (h : IsDistributionIsotropicMap J D f) (y : N) :
    finrank ℝ ((LinearMap.range (mfderiv J I f y).toLinearMap).comap (D (f y)).subtype) =
      finrank ℝ (LinearMap.range (mfderiv J I f y).toLinearMap) :=
  (Submodule.comapSubtypeEquivOfLe (h.range_le y)).finrank_eq

/-! ### Vanishing of the Levi form -/

section Levi

variable [IsManifold I 2 M] [IsManifold J 2 N]
  [CompleteSpace E] [FiniteDimensional ℝ E] {n : ℕ∞ω} {k : ℕ}

/-- **The Levi form vanishes on the tangent images of an isotropic map.** Let `D` be a `C^n`
hyperplane field, `1 ≤ n`, and let `f` be isotropic for `D` and `C²` at `y`. Then
`L_D(df u, df v) = 0` for all tangent vectors `u, v` at `y`. -/
theorem IsDistributionIsotropicMap.distributionLeviForm_eq_zero [IsManifold I (n + 1) M]
    (hD : IsContMDiffDistribution I n k D) (hk : k + 1 = finrank ℝ E) (hn : 1 ≤ n)
    (h : IsDistributionIsotropicMap J D f) {y : N} (hf : ContMDiffAt J I 2 f y)
    (u v : TangentSpace J y) :
    distributionLeviForm D (f y) ⟨_, h.mfderiv_mem y u⟩ ⟨_, h.mfderiv_mem y v⟩ = 0 := by
  obtain ⟨U, hU, hyU, α, hα, hαD⟩ := hD.exists_roughForm_ker_eq hk (f y)
  have hαy := ((hα (f y) hyU).contMDiffAt (hU.mem_nhds hyU)).of_le hn
  have hDα : ∀ᶠ x in 𝓝 (f y), D x ≤ α.ker x :=
    eventually_of_mem (hU.mem_nhds hyU) fun x hx ↦ (hαD x hx).2.ge
  obtain ⟨V, hV, hyV, X, hX⟩ := isContMDiffDistribution_iff.1 hD (f y)
  -- A representative `w` of the Levi form satisfies `α(w) = dα(df u, df v) = 0`.
  obtain ⟨w, hw⟩ := (D (f y)).mkQ_surjective
    (distributionLeviForm D (f y) ⟨_, h.mfderiv_mem y u⟩ ⟨_, h.mfderiv_mem y v⟩)
  have hαw := RoughForm.apply_eq_mextDeriv_of_mkQ_eq_distributionLeviForm (hX.of_le hn)
    (hV.mem_nhds hyV) (hαy.mdifferentiableAt one_ne_zero) hDα hw
  rw [h.mextDeriv_apply_mfderiv_eq_zero hf hαy hDα] at hαw
  rw [← hw, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, ← (hαD (f y) hyU).2,
    RoughForm.mem_ker]
  exact hαw

/-- The tangent image of an isotropic map, as a subspace of the contact hyperplane at its image
point, is isotropic for the Levi form. -/
private theorem IsDistributionIsotropicMap.distributionLeviForm_eq_zero_of_mem_comap
    [IsManifold I (n + 1) M] (hD : IsContMDiffDistribution I n k D) (hk : k + 1 = finrank ℝ E)
    (hn : 1 ≤ n) (h : IsDistributionIsotropicMap J D f) {y : N} (hf : ContMDiffAt J I 2 f y)
    {a b : D (f y)}
    (ha : a ∈ (LinearMap.range (mfderiv J I f y).toLinearMap).comap (D (f y)).subtype)
    (hb : b ∈ (LinearMap.range (mfderiv J I f y).toLinearMap).comap (D (f y)).subtype) :
    distributionLeviForm D (f y) a b = 0 := by
  obtain ⟨u, hu⟩ := ha
  obtain ⟨v, hv⟩ := hb
  obtain rfl : a = ⟨_, h.mfderiv_mem y u⟩ := Subtype.ext hu.symm
  obtain rfl : b = ⟨_, h.mfderiv_mem y v⟩ := Subtype.ext hv.symm
  exact h.distributionLeviForm_eq_zero hD hk hn hf u v

/-- **Dimension bound for isotropic maps.** An isotropic map into a `(2 m + 1)`-dimensional contact
manifold, `C²` and with injective differential at some point, comes from a manifold of dimension
at most `m`: `2 dim N + 1 ≤ dim M`. -/
theorem IsDistributionIsotropicMap.two_mul_finrank_add_one_le [IsManifold I (n + 1) M]
    (hD : IsContactDistribution I n D) (hn : 1 ≤ n) (h : IsDistributionIsotropicMap J D f) {y : N}
    (hf : ContMDiffAt J I 2 f y) (hy : Injective (mfderiv J I f y)) :
    2 * finrank ℝ E' + 1 ≤ finrank ℝ E := by
  have : FiniteDimensional ℝ (TangentSpace I (f y)) := inferInstanceAs (FiniteDimensional ℝ E)
  have hle := LinearMap.two_mul_finrank_le_finrank_of_injective
    (hD.bijective_distributionLeviForm (f y)).injective (hD.finrank_quotient (f y))
    fun a ha b hb ↦ h.distributionLeviForm_eq_zero_of_mem_comap hD.isContMDiffDistribution
      (hD.finrank_sub_one_add_one (f y)) hn hf ha hb
  rw [h.finrank_comap_range, LinearMap.finrank_range_of_inj hy, finrank_tangentSpace] at hle
  have := hD.finrank_add_one (f y)
  omega

/-! ### Legendrian immersions and embeddings -/

variable (J D) in
/-- A **Legendrian immersion** for a distribution `D` on `M` is a smooth immersion `f : N → M`
which is isotropic for `D` and satisfies `2 dim N + 1 = dim M`. The predicate is defined for any
distribution `D`; when `D` is a contact structure on a manifold of dimension `2 m + 1`, this is the
usual notion of a Legendrian immersion, from a manifold of the maximal dimension `m`. Its image
may have self-intersections. -/
structure IsLegendrianImmersion (f : N → M) : Prop where
  /-- A Legendrian immersion is a smooth immersion. -/
  isImmersion : IsImmersion J I ∞ f
  /-- A Legendrian immersion is tangent to the distribution. -/
  isDistributionIsotropicMap : IsDistributionIsotropicMap J D f
  /-- A Legendrian immersion satisfies `2 dim N + 1 = dim M`. -/
  two_mul_finrank_add_one : 2 * finrank ℝ E' + 1 = finrank ℝ E

variable (J D) in
/-- A **Legendrian embedding** is a Legendrian immersion which is a topological embedding, hence a
smooth embedding. Its image is an embedded Legendrian submanifold. -/
structure IsLegendrianEmbedding (f : N → M) : Prop extends IsLegendrianImmersion J D f where
  /-- A Legendrian embedding is a homeomorphism onto its image. -/
  isEmbedding : Topology.IsEmbedding f

omit [IsManifold I 2 M] [IsManifold J 2 N] [CompleteSpace E] [FiniteDimensional ℝ E] in
/-- A Legendrian embedding is a smooth embedding in Mathlib's sense. -/
theorem IsLegendrianEmbedding.isSmoothEmbedding (h : IsLegendrianEmbedding J D f) :
    IsSmoothEmbedding J I ∞ f :=
  ⟨h.isImmersion, h.isEmbedding⟩

omit [IsManifold I 2 M] [IsManifold J 2 N] [CompleteSpace E] [FiniteDimensional ℝ E] in
/-- Among smooth embeddings, the Legendrian embeddings are precisely the Legendrian immersions. -/
@[simp]
theorem isLegendrianEmbedding_iff_of_isSmoothEmbedding (hf : IsSmoothEmbedding J I ∞ f) :
    IsLegendrianEmbedding J D f ↔ IsLegendrianImmersion J D f :=
  ⟨fun h ↦ h.toIsLegendrianImmersion, fun h ↦ ⟨h, hf.isEmbedding⟩⟩

/-- An isotropic immersion into a contact manifold, from a nonempty manifold, is a Legendrian
immersion exactly when its source has the maximal dimension allowed by the dimension bound. -/
theorem isLegendrianImmersion_iff_finrank_le [IsManifold I (n + 1) M]
    (hD : IsContactDistribution I n D) (hn : 1 ≤ n) [Nonempty N] :
    IsLegendrianImmersion J D f ↔
      IsImmersion J I ∞ f ∧ IsDistributionIsotropicMap J D f ∧
        finrank ℝ E ≤ 2 * finrank ℝ E' + 1 := by
  refine ⟨fun h ↦ ⟨h.isImmersion, h.isDistributionIsotropicMap, h.two_mul_finrank_add_one.ge⟩,
    fun ⟨himm, hiso, hdim⟩ ↦ ⟨himm, hiso, ?_⟩⟩
  obtain ⟨y⟩ := ‹Nonempty N›
  have := hiso.two_mul_finrank_add_one_le hD hn ((himm.contMDiff y).of_le (by simp))
    (himm.mfderiv_injective (by simp) y)
  omega

/-- **The tangent images of a Legendrian immersion are maximal isotropic.** A vector of the contact
hyperplane at `f y` which is Levi-orthogonal to the tangent image `df_y(T_y N)` lies in it. -/
theorem IsLegendrianImmersion.mem_range_mfderiv_of_distributionLeviForm_eq_zero
    [IsManifold I (n + 1) M] (hD : IsContactDistribution I n D) (hn : 1 ≤ n)
    (h : IsLegendrianImmersion J D f) {y : N} {a : D (f y)}
    (ha : ∀ u,
      distributionLeviForm D (f y) a ⟨_, h.isDistributionIsotropicMap.mfderiv_mem y u⟩ = 0) :
    a.1 ∈ LinearMap.range (mfderiv J I f y).toLinearMap := by
  have : FiniteDimensional ℝ (TangentSpace I (f y)) := inferInstanceAs (FiniteDimensional ℝ E)
  set W := (LinearMap.range (mfderiv J I f y).toLinearMap).comap (D (f y)).subtype
  have hinj := (hD.bijective_distributionLeviForm (f y)).injective
  have hW : ∀ a ∈ W, ∀ b ∈ W, distributionLeviForm D (f y) a b = 0 := fun a ha b hb ↦
    h.isDistributionIsotropicMap.distributionLeviForm_eq_zero_of_mem_comap
      hD.isContMDiffDistribution (hD.finrank_sub_one_add_one (f y)) hn
      ((h.isImmersion.contMDiff y).of_le (by simp)) ha hb
  have hdim : 2 * finrank ℝ W = finrank ℝ (D (f y)) := by
    rw [h.isDistributionIsotropicMap.finrank_comap_range,
      LinearMap.finrank_range_of_inj (h.isImmersion.mfderiv_injective (by simp) y),
      finrank_tangentSpace]
    have := hD.finrank_add_one (f y)
    have := h.two_mul_finrank_add_one
    omega
  exact LinearMap.mem_of_injective_of_two_mul_finrank_eq hinj (hD.finrank_quotient (f y)) hW hdim
    fun b ⟨u, hu⟩ ↦ by
      obtain rfl : b = ⟨_, h.isDistributionIsotropicMap.mfderiv_mem y u⟩ := Subtype.ext hu.symm
      exact ha u

end Levi

section Reparametrization

variable {P : Type*} [TopologicalSpace P] [ChartedSpace H' P] [IsManifold J ∞ N] [IsManifold J ∞ P]

/-- Reparametrization by a diffeomorphism preserves and reflects Legendrian immersions. -/
@[simp]
theorem _root_.Diffeomorph.isLegendrianImmersion_comp_diffeomorph_iff (φ : P ≃ₘ⟮J, J⟯ N) :
    IsLegendrianImmersion J D (f ∘ φ) ↔ IsLegendrianImmersion J D f :=
  ⟨fun h ↦ ⟨(isImmersion_comp_diffeomorph_iff φ).1 h.isImmersion,
      (φ.isDistributionIsotropicMap_comp_diffeomorph_iff (by simp)).1
        h.isDistributionIsotropicMap, h.two_mul_finrank_add_one⟩,
    fun h ↦ ⟨(isImmersion_comp_diffeomorph_iff φ).2 h.isImmersion,
      (φ.isDistributionIsotropicMap_comp_diffeomorph_iff (by simp)).2
        h.isDistributionIsotropicMap, h.two_mul_finrank_add_one⟩⟩

/-- Reparametrization by a diffeomorphism preserves and reflects Legendrian embeddings. -/
@[simp]
theorem _root_.Diffeomorph.isLegendrianEmbedding_comp_diffeomorph_iff (φ : P ≃ₘ⟮J, J⟯ N) :
    IsLegendrianEmbedding J D (f ∘ φ) ↔ IsLegendrianEmbedding J D f :=
  ⟨fun h ↦ (isLegendrianEmbedding_iff_of_isSmoothEmbedding
      ((isSmoothEmbedding_comp_diffeomorph_iff φ).1 h.isSmoothEmbedding)).2
      (φ.isLegendrianImmersion_comp_diffeomorph_iff.1 h.toIsLegendrianImmersion),
    fun h ↦ (isLegendrianEmbedding_iff_of_isSmoothEmbedding
      (isSmoothEmbedding_comp_diffeomorph φ h.isSmoothEmbedding)).2
      (φ.isLegendrianImmersion_comp_diffeomorph_iff.2 h.toIsLegendrianImmersion)⟩

end Reparametrization

section Transport

variable {M₂ : Type*} [TopologicalSpace M₂] [ChartedSpace H M₂] [IsManifold I ∞ M]
  [IsManifold I ∞ M₂] {D₂ : Π x : M₂, Submodule ℝ (TangentSpace I x)}

/-- A diffeomorphism whose differential carries `D` onto `D₂`, such as a contactomorphism,
preserves and reflects Legendrian immersions. -/
theorem _root_.Diffeomorph.isLegendrianImmersion_diffeomorph_comp_iff (ψ : M ≃ₘ⟮I, I⟯ M₂)
    (hψ : ∀ x v, v ∈ D x ↔ mfderiv I I ψ x v ∈ D₂ (ψ x)) :
    IsLegendrianImmersion J D₂ (ψ ∘ f) ↔ IsLegendrianImmersion J D f :=
  ⟨fun h ↦ ⟨(isImmersion_diffeomorph_comp_iff ψ).1 h.isImmersion,
      (ψ.isDistributionIsotropicMap_diffeomorph_comp_iff (by simp) hψ).1
        h.isDistributionIsotropicMap, h.two_mul_finrank_add_one⟩,
    fun h ↦ ⟨(isImmersion_diffeomorph_comp_iff ψ).2 h.isImmersion,
      (ψ.isDistributionIsotropicMap_diffeomorph_comp_iff (by simp) hψ).2
        h.isDistributionIsotropicMap, h.two_mul_finrank_add_one⟩⟩

/-- A diffeomorphism whose differential carries `D` onto `D₂`, such as a contactomorphism,
preserves and reflects Legendrian embeddings. -/
theorem _root_.Diffeomorph.isLegendrianEmbedding_diffeomorph_comp_iff (ψ : M ≃ₘ⟮I, I⟯ M₂)
    (hψ : ∀ x v, v ∈ D x ↔ mfderiv I I ψ x v ∈ D₂ (ψ x)) :
    IsLegendrianEmbedding J D₂ (ψ ∘ f) ↔ IsLegendrianEmbedding J D f :=
  ⟨fun h ↦ (isLegendrianEmbedding_iff_of_isSmoothEmbedding
      ((isSmoothEmbedding_diffeomorph_comp_iff ψ).1 h.isSmoothEmbedding)).2
      ((ψ.isLegendrianImmersion_diffeomorph_comp_iff hψ).1 h.toIsLegendrianImmersion),
    fun h ↦ (isLegendrianEmbedding_iff_of_isSmoothEmbedding
      (isSmoothEmbedding_diffeomorph_comp h.isSmoothEmbedding ψ)).2
      ((ψ.isLegendrianImmersion_diffeomorph_comp_iff hψ).2 h.toIsLegendrianImmersion)⟩

end Transport

end TauCeti
