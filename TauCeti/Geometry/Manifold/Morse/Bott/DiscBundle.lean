/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.Bott.Attachment
public import TauCeti.Geometry.Manifold.Morse.Bott.Family
public import TauCeti.Geometry.Manifold.Morse.Bott.NormalSubbundle
public import TauCeti.Geometry.Manifold.Morse.Bott.Tubular
import TauCeti.Topology.Compactness.LocallyCompact
import TauCeti.Topology.FiberBundle.Separation

/-!
# Attaching the negative disc bundle of a compact Morse–Bott submanifold

Let `i : S → M` be a compact nondegenerate critical submanifold of a smooth function `f` on a
boundaryless manifold, on the level `f = c`, and let `g` be a smooth fibre metric on its normal
bundle `ν`. The metric splits each normal space into the negative normal space `ν⁻`, on which the
normal Hessian `Hessₛ` is negative definite, and the positive normal space `ν⁺`
(`TauCeti.SmoothEmbedding.IsCriticalSubmanifold.negativeNormalSpace`). The **negative disc
bundle** of size `ε` is `D_ε = {v ∈ ν⁻ | -½ Hessₛ (v, v) ≤ ε}`
(`TauCeti.SmoothEmbedding.IsCriticalSubmanifold.negativeDiscBundle`); its fibres are closed
ellipsoids of dimension the index of the submanifold.

This file proves that crossing the critical level attaches the negative disc bundle
(`IsNondegenerateCriticalSubmanifold.exists_sublevel_union_negativeDiscBundle_deformation`, in the
namespace `TauCeti.SmoothEmbedding`): there are a Morse–Bott normal form `Θ : ν → M` near the
zero section, with `f (Θ v) = c + ½ Hessₛ (v, v)`, and an `ε₀ > 0` such that for `0 < ε < ε₀`, if
the band `f⁻¹[c - ε, c + ε]` is compact and its critical points lie on the submanifold, then the
sublevel `{f ≤ c + ε}` strong deformation retracts onto `{f ≤ c - ε} ∪ Θ(D_ε)`. For an isolated
nondegenerate critical point the base is a point and this is Milnor's attachment of a cell of
dimension the index.

A level may carry several critical submanifolds, of different dimensions. For finitely many compact
ones `i a : S a → M` with pairwise disjoint images on the level `f = c`, crossing the level attaches
all their negative disc bundles at once
(`TauCeti.SmoothEmbedding.exists_sublevel_union_iUnion_negativeDiscBundle_deformation`): the
sublevel `{f ≤ c + ε}` strong deformation retracts onto `{f ≤ c - ε} ∪ ⋃ a, Θ a (D a ε)`.

For a Morse–Bott function (`TauCeti.IsMorseBottFamily`) on a manifold which need not be compact,
it is enough that some band `f⁻¹[c - δ, c + δ]` around the level is compact. The critical
submanifolds on the level then lie in this band, so they are finitely many, compact and disjoint,
and the function takes finitely many critical values in the band; so for small `ε` the band
`f⁻¹[c - ε, c + ε]` is compact and its critical points lie on the level, and crossing the level
attaches the negative disc bundles of the critical submanifolds on it
(`IsMorseBottFamily.exists_sublevel_union_iUnion_negativeDiscBundle_deformation_of_isCompact`).
This is the case of a proper function, for instance. On a compact manifold every band is compact,
so crossing any level attaches these disc bundles
(`TauCeti.IsMorseBottFamily.exists_sublevel_union_iUnion_negativeDiscBundle_deformation`).

The normal form `Θ` is the Morse–Bott lemma on the normal bundle
(`IsNondegenerateCriticalSubmanifold.exists_morseBott_partialDiffeomorph_normalBundle`).
Writing a normal vector as `v = u + w` with `u ∈ ν⁻` and `w ∈ ν⁺`, the two parts are orthogonal
for the normal Hessian, so `f ∘ Θ = c - s + t` with `s = -½ Hessₛ (u, u) ≥ 0` and
`t = ½ Hessₛ (w, w) ≥ 0`. These are smooth on the total space, since the projections onto `ν⁻`
and `ν⁺` are (`IsNondegenerateCriticalSubmanifold.contMDiff_projection_negativeNormalSpace`) and so
is the quadratic form of the normal Hessian
(`TauCeti.SmoothEmbedding.IsCriticalSubmanifold.contMDiff_normalHessian_apply_self`); rescaling
`(u, w) ↦ (a u, b w)` multiplies `s` by `a²` and `t` by `b²`. The attachment theorem for normal
forms given by partial diffeomorphisms (`TauCeti.exists_sublevel_union_iUnion_image_deformation`)
then applies, with tube the image under `Θ` of a sublevel `{s + 2t < m}`. Since `s + 2t` is positive
off the zero section and decreases along the rays `r ↦ r v`, `r ∈ [0, 1]`, which start on the zero
section, such a sublevel lies in any given compact neighbourhood of the compact zero section once
`m` is small, so its closed sublevels `{s + 2t ≤ 2ε}` are compact and lie in the source of `Θ`.

## Main definitions

* `TauCeti.SmoothEmbedding.IsCriticalSubmanifold.negativeDiscBundle`: the negative disc bundle of
  a critical submanifold relative to a fibre metric. It increases with its size
  (`IsCriticalSubmanifold.negativeDiscBundle_mono`), contains the zero section for nonnegative
  sizes (`IsCriticalSubmanifold.zeroSection_mem_negativeDiscBundle`), and consists of negative
  normal vectors
  (`IsCriticalSubmanifold.mem_negativeNormalSpace_of_mem_negativeDiscBundle`).
* `TauCeti.SmoothEmbedding.IsCriticalSubmanifold.negativeSphereBundle`: the negative sphere bundle
  `S_ε = {v ∈ ν⁻ | -½ Hessₛ (v, v) = ε}`, contained in the negative disc bundle of the same size
  (`IsCriticalSubmanifold.negativeSphereBundle_subset_negativeDiscBundle`).

## Main results

In the namespace `TauCeti.SmoothEmbedding`:

* `IsNondegenerateCriticalSubmanifold.exists_sublevel_union_negativeDiscBundle_deformation`:
  crossing the level of a compact Morse–Bott submanifold attaches its negative disc bundle, up to
  a strong deformation retraction.
* `exists_sublevel_union_iUnion_negativeDiscBundle_deformation`: the same for finitely many
  disjoint compact Morse–Bott submanifolds on one level, each with its own model.
* `IsNondegenerateCriticalSubmanifold.isCompact_negativeDiscBundle` and
  `IsNondegenerateCriticalSubmanifold.isCompact_negativeSphereBundle`: over a compact Morse–Bott
  submanifold the negative disc and sphere bundles of every size are compact.

In the namespace `TauCeti.IsMorseBottFamily`:

* `exists_sublevel_union_iUnion_negativeDiscBundle_deformation_of_isCompact`: crossing a level
  of a Morse–Bott function with a compact band around it attaches the negative disc bundles of all
  its critical submanifolds on that level.
* `exists_sublevel_union_iUnion_negativeDiscBundle_deformation`: the same for every level of a
  Morse–Bott function on a compact manifold.

## References

* J. Milnor, *Morse Theory*, Annals of Mathematics Studies 51, Princeton University Press, 1963,
  Theorem 3.2.
* R. Bott, *Nondegenerate critical manifolds*, Annals of Mathematics 60 (1954), 248–261.
* R. L. Cohen, K. Iga and P. Norbury, *Topics in Morse theory: lecture notes*, 2006,
  Theorems 15.1 and 15.4.
-/

public section

noncomputable section

open Bundle Function Set Filter Topology
open scoped ContDiff Manifold

namespace TauCeti

namespace SmoothEmbedding

section DiscBundle

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless] [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I 2 M] {E' H' S : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'} [TopologicalSpace S] [ChartedSpace H' S]
  {f : M → ℝ} {n : ℕ∞ω} {i : SmoothEmbedding J I n S M} (hn : n ≠ 0) {P : Type*}

namespace IsCriticalSubmanifold

variable (h : i.IsCriticalSubmanifold f) (P) (g : RiemannianMetric fun s ↦ i.NormalSpace s hn)

/-- The **negative disc bundle** of a critical submanifold, of size `ε`, relative to a fibre metric
`g` on the normal spaces: the normal vectors `v` in the negative normal space with
`-½ Hessₛ (v, v) ≤ ε`, where `Hessₛ` is the normal Hessian. For a Morse–Bott submanifold the normal
Hessian is negative definite on the negative normal spaces, so for `ε > 0` each fibre is a closed
ellipsoid of dimension the Morse index. -/
def negativeDiscBundle (ε : ℝ) : Set (TotalSpace P fun s ↦ i.NormalSpace s hn) :=
  {x | x.snd ∈ h.negativeNormalSpace hn g x.proj ∧ -(2⁻¹ * h.normalHessian hn x.proj x.snd x.snd) ≤
      ε}

variable {h P g} in
@[simp]
theorem mem_negativeDiscBundle {ε : ℝ} {x : TotalSpace P fun s ↦ i.NormalSpace s hn} :
    x ∈ h.negativeDiscBundle hn P g ε ↔
      x.snd ∈ h.negativeNormalSpace hn g x.proj ∧ -(2⁻¹ * h.normalHessian hn x.proj x.snd x.snd) ≤ ε
          :=
  Iff.rfl

variable {h P g} in
/-- A vector of the negative disc bundle lies in the negative normal space. -/
theorem mem_negativeNormalSpace_of_mem_negativeDiscBundle {ε : ℝ}
    {x : TotalSpace P fun s ↦ i.NormalSpace s hn} (hx : x ∈ h.negativeDiscBundle hn P g ε) :
    x.snd ∈ h.negativeNormalSpace hn g x.proj :=
  (mem_negativeDiscBundle hn).1 hx |>.1

/-- The negative disc bundle increases with its size. -/
theorem negativeDiscBundle_mono : Monotone (h.negativeDiscBundle hn P g) := fun _ _ hεε' _ hx ↦
  (mem_negativeDiscBundle hn).2
    ⟨((mem_negativeDiscBundle hn).1 hx).1, ((mem_negativeDiscBundle hn).1 hx).2.trans hεε'⟩

/-- The zero section lies in the negative disc bundle of any nonnegative size. -/
theorem zeroSection_mem_negativeDiscBundle {ε : ℝ} (hε : 0 ≤ ε) (s : S) :
    zeroSection P (fun s ↦ i.NormalSpace s hn) s ∈ h.negativeDiscBundle hn P g ε :=
  (mem_negativeDiscBundle hn).2 ⟨zero_mem _, by
    rw [zeroSection_snd, LinearMap.map_zero₂, mul_zero, neg_zero]
    exact hε⟩

/-- The **negative sphere bundle** of a critical submanifold, of size `ε`, relative to a fibre
metric `g` on the normal spaces: the normal vectors `v` in the negative normal space with
`-½ Hessₛ (v, v) = ε`, where `Hessₛ` is the normal Hessian. For a Morse–Bott submanifold and
`ε > 0` its fibres are the boundary spheres of the ellipsoids forming the negative disc bundle of
size `ε`; it is the part of that disc bundle along which it is attached to the sublevel below the
critical level. -/
def negativeSphereBundle (ε : ℝ) : Set (TotalSpace P fun s ↦ i.NormalSpace s hn) :=
  {x | x.snd ∈ h.negativeNormalSpace hn g x.proj ∧ -(2⁻¹ * h.normalHessian hn x.proj x.snd x.snd) =
      ε}

variable {h P g} in
@[simp]
theorem mem_negativeSphereBundle {ε : ℝ} {x : TotalSpace P fun s ↦ i.NormalSpace s hn} :
    x ∈ h.negativeSphereBundle hn P g ε ↔
      x.snd ∈ h.negativeNormalSpace hn g x.proj ∧ -(2⁻¹ * h.normalHessian hn x.proj x.snd x.snd) = ε
          :=
  Iff.rfl

/-- The negative sphere bundle lies in the negative disc bundle of the same size. -/
theorem negativeSphereBundle_subset_negativeDiscBundle (ε : ℝ) :
    h.negativeSphereBundle hn P g ε ⊆ h.negativeDiscBundle hn P g ε :=
  fun _ hx ↦ ⟨hx.1, hx.2.le⟩

end IsCriticalSubmanifold

namespace IsNondegenerateCriticalSubmanifold

variable [FiniteDimensional ℝ E] (h : i.IsNondegenerateCriticalSubmanifold f)
  (g : RiemannianMetric fun s ↦ i.NormalSpace s hn)

/-- The part of a normal vector in the negative normal space, along the positive one. -/
private def negPart (s : S) : i.NormalSpace s hn →ₗ[ℝ] i.NormalSpace s hn :=
  (h.negativeNormalSpace hn g s).projection (h.positiveNormalSpace hn g s)
    (h.isCompl_negativeNormalSpace_positiveNormalSpace hn g g s)

/-- The part of a normal vector in the positive normal space, along the negative one. -/
private def posPart (s : S) : i.NormalSpace s hn →ₗ[ℝ] i.NormalSpace s hn :=
  (h.positiveNormalSpace hn g s).projection (h.negativeNormalSpace hn g s)
    (h.isCompl_negativeNormalSpace_positiveNormalSpace hn g g s).symm

/-- Minus half the normal Hessian of the negative part of a normal vector. -/
private def negSq (x : TotalSpace P fun s ↦ i.NormalSpace s hn) : ℝ :=
  -(2⁻¹ * h.normalHessian hn x.proj (h.negPart hn g x.proj x.snd) (h.negPart hn g x.proj x.snd))

/-- Half the normal Hessian of the positive part of a normal vector. -/
private def posSq (x : TotalSpace P fun s ↦ i.NormalSpace s hn) : ℝ :=
  2⁻¹ * h.normalHessian hn x.proj (h.posPart hn g x.proj x.snd) (h.posPart hn g x.proj x.snd)

/-- Rescale the negative part of a normal vector by `a` and its positive part by `b`. -/
private def rescale (a b : ℝ) (x : TotalSpace P fun s ↦ i.NormalSpace s hn) :
    TotalSpace P fun s ↦ i.NormalSpace s hn :=
  ⟨x.proj, a • h.negPart hn g x.proj x.snd + b • h.posPart hn g x.proj x.snd⟩

variable {s : S} (v : i.NormalSpace s hn) (x : TotalSpace P fun s ↦ i.NormalSpace s hn)

private theorem negSq_mk : h.negSq hn g (⟨s, v⟩ : TotalSpace P fun s ↦ i.NormalSpace s hn) =
    -(2⁻¹ * h.normalHessian hn s (h.negPart hn g s v) (h.negPart hn g s v)) :=
  rfl

private theorem posSq_mk : h.posSq hn g (⟨s, v⟩ : TotalSpace P fun s ↦ i.NormalSpace s hn) =
    2⁻¹ * h.normalHessian hn s (h.posPart hn g s v) (h.posPart hn g s v) :=
  rfl

private theorem rescale_def (a b : ℝ) : h.rescale hn g a b x =
    ⟨x.proj, a • h.negPart hn g x.proj x.snd + b • h.posPart hn g x.proj x.snd⟩ :=
  rfl

private theorem negPart_mem : h.negPart hn g s v ∈ h.negativeNormalSpace hn g s :=
  Submodule.projection_apply_mem _ v

private theorem posPart_mem : h.posPart hn g s v ∈ h.positiveNormalSpace hn g s :=
  Submodule.projection_apply_mem _ v

private theorem negPart_add_posPart : h.negPart hn g s v + h.posPart hn g s v = v :=
  Submodule.projection_add_projection_eq_self _ v

private theorem posPart_eq_zero_iff : h.posPart hn g s v = 0 ↔ v ∈ h.negativeNormalSpace hn g s :=
  Submodule.projection_apply_eq_zero_iff _

/-- The normal Hessian of a normal vector is the sum of its values on the two parts, which are
orthogonal for it. -/
private theorem normalHessian_eq_add :
    h.normalHessian hn s v v = h.normalHessian hn s (h.negPart hn g s v) (h.negPart hn g s v) +
      h.normalHessian hn s (h.posPart hn g s v) (h.posPart hn g s v) := by
  have h0 := h.normalHessian_eq_zero_of_mem_negativeNormalSpace hn g (h.negPart_mem hn g v)
    (h.posPart_mem hn g v)
  have h0' : h.normalHessian hn s (h.posPart hn g s v) (h.negPart hn g s v) = 0 := by
    rw [(h.isSymm_normalHessian hn s).eq, h0]
  conv_lhs => rw [← h.negPart_add_posPart hn g v]
  simp only [map_add, LinearMap.add_apply, h0, h0']
  ring

private theorem negSq_nonneg : 0 ≤ h.negSq hn g x := by
  have := h.normalHessian_apply_self_nonpos_of_mem_negativeNormalSpace hn g
      (h.negPart_mem hn g x.snd)
  simp only [negSq]
  linarith

private theorem posSq_nonneg : 0 ≤ h.posSq hn g x := by
  have := h.normalHessian_apply_self_nonneg_of_mem_positiveNormalSpace hn g
      (h.posPart_mem hn g x.snd)
  simp only [posSq]
  linarith

private theorem negPart_eq_zero (hx : h.negSq hn g x = 0) : h.negPart hn g x.proj x.snd = 0 := by
  by_contra hne
  have := h.normalHessian_apply_self_neg_of_mem_negativeNormalSpace hn g
    (h.negPart_mem hn g x.snd) hne
  simp only [negSq] at hx
  linarith

private theorem posPart_eq_zero (hx : h.posSq hn g x = 0) : h.posPart hn g x.proj x.snd = 0 := by
  by_contra hne
  have := h.normalHessian_apply_self_pos_of_mem_positiveNormalSpace hn g
    (h.posPart_mem hn g x.snd) hne
  simp only [posSq] at hx
  linarith

/-- Half the normal Hessian is `-negSq + posSq`. -/
private theorem two_inv_mul_normalHessian :
    2⁻¹ * h.normalHessian hn x.proj x.snd x.snd = -h.negSq hn g x + h.posSq hn g x := by
  rw [negSq, posSq, h.normalHessian_eq_add hn g x.snd]
  ring

private theorem negPart_smul_add_smul (a b : ℝ) :
    h.negPart hn g s (a • h.negPart hn g s v + b • h.posPart hn g s v) =
      a • h.negPart hn g s v := by
  have h₁ : h.negPart hn g s (h.negPart hn g s v) = h.negPart hn g s v :=
    Submodule.projection_apply_of_mem_left _ (h.negPart_mem hn g v)
  have h₂ : h.negPart hn g s (h.posPart hn g s v) = 0 :=
    Submodule.projection_apply_of_mem_right _ (h.posPart_mem hn g v)
  rw [map_add, map_smul, map_smul, h₁, h₂, smul_zero, add_zero]

private theorem posPart_smul_add_smul (a b : ℝ) :
    h.posPart hn g s (a • h.negPart hn g s v + b • h.posPart hn g s v) =
      b • h.posPart hn g s v := by
  have h₁ : h.posPart hn g s (h.negPart hn g s v) = 0 :=
    Submodule.projection_apply_of_mem_right _ (h.negPart_mem hn g v)
  have h₂ : h.posPart hn g s (h.posPart hn g s v) = h.posPart hn g s v :=
    Submodule.projection_apply_of_mem_left _ (h.posPart_mem hn g v)
  rw [map_add, map_smul, map_smul, h₁, h₂, smul_zero, zero_add]

private theorem negSq_rescale (a b : ℝ) :
    h.negSq hn g (h.rescale hn g a b x) = a ^ 2 * h.negSq hn g x := by
  rw [rescale_def, negSq_mk, h.negPart_smul_add_smul, negSq]
  simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
  ring

private theorem posSq_rescale (a b : ℝ) :
    h.posSq hn g (h.rescale hn g a b x) = b ^ 2 * h.posSq hn g x := by
  rw [rescale_def, posSq_mk, h.posPart_smul_add_smul, posSq]
  simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
  ring

private theorem rescale_one_one : h.rescale hn g 1 1 x = x := by
  simp only [rescale, one_smul, h.negPart_add_posPart]

private theorem rescale_one_of_posSq_eq_zero (b : ℝ) (hx : h.posSq hn g x = 0) :
    h.rescale hn g 1 b x = x := by
  conv_rhs => rw [← h.rescale_one_one hn g x]
  simp only [rescale, h.posPart_eq_zero hn g x hx, smul_zero]

private theorem rescale_zero_zero :
    h.rescale hn g 0 0 x = zeroSection P (fun s ↦ i.NormalSpace s hn) x.proj := by
  simp [rescale, zeroSection]

private theorem eq_zeroSection_of_negSq_eq_zero (hs : h.negSq hn g x = 0)
    (ht : h.posSq hn g x = 0) : zeroSection P (fun s ↦ i.NormalSpace s hn) x.proj = x := by
  rw [← h.rescale_zero_zero hn g x]
  conv_rhs => rw [← h.rescale_one_one hn g x]
  simp only [rescale, h.negPart_eq_zero hn g x hs, h.posPart_eq_zero hn g x ht, smul_zero]

private theorem negSq_zeroSection (s : S) :
    h.negSq hn g (zeroSection P (fun s ↦ i.NormalSpace s hn) s) = 0 := by
  rw [zeroSection, negSq_mk, map_zero, map_zero, mul_zero, neg_zero]

private theorem posSq_zeroSection (s : S) :
    h.posSq hn g (zeroSection P (fun s ↦ i.NormalSpace s hn) s) = 0 := by
  rw [zeroSection, posSq_mk, map_zero, map_zero, mul_zero]

/-- The disc bundle `{t = 0, s ≤ ε}` of the normal form is the negative disc bundle. -/
private theorem setOf_posSq_eq_zero_and_negSq_le (ε : ℝ) :
    {x | h.posSq hn g x = 0 ∧ h.negSq hn g x ≤ ε} = h.negativeDiscBundle hn P g ε := by
  ext x
  rw [IsCriticalSubmanifold.mem_negativeDiscBundle, ← h.posPart_eq_zero_iff hn g]
  have hH (hp : h.posPart hn g x.proj x.snd = 0) :
      -(2⁻¹ * h.normalHessian hn x.proj x.snd x.snd) = h.negSq hn g x := by
    rw [h.two_inv_mul_normalHessian hn g x, posSq, hp]
    simp
  refine ⟨fun ⟨ht, hs⟩ ↦ ⟨h.posPart_eq_zero hn g x ht, by rwa [hH (h.posPart_eq_zero hn g x ht)]⟩,
    fun ⟨hp, hs⟩ ↦ ⟨by simp [posSq, hp], by rwa [hH hp] at hs⟩⟩

/-- The sphere bundle `{t = 0, s = ε}` of the normal form is the negative sphere bundle. -/
private theorem setOf_posSq_eq_zero_and_negSq_eq (ε : ℝ) :
    {x | h.posSq hn g x = 0 ∧ h.negSq hn g x = ε} = h.negativeSphereBundle hn P g ε := by
  ext x
  have hD := Set.ext_iff.1 (h.setOf_posSq_eq_zero_and_negSq_le hn g ε) x
  refine ⟨fun ⟨ht, hs⟩ ↦ ⟨(hD.1 ⟨ht, hs.le⟩).1, ?_⟩, fun hx ↦ ?_⟩
  · rw [← hs, h.two_inv_mul_normalHessian hn g x, ht]
    ring
  · obtain ⟨ht, -⟩ := hD.2 ((h.negativeSphereBundle_subset_negativeDiscBundle hn P g ε) hx)
    refine ⟨ht, ?_⟩
    rw [← hx.2, h.two_inv_mul_normalHessian hn g x, ht]
    ring

private theorem rescale_rescale (a b a' b' : ℝ) :
    h.rescale hn g a b (h.rescale hn g a' b' x) = h.rescale hn g (a * a') (b * b') x := by
  rw [rescale_def, rescale_def, h.negPart_smul_add_smul, h.posPart_smul_add_smul, smul_smul,
    smul_smul, rescale_def]

end IsNondegenerateCriticalSubmanifold

end DiscBundle

section Attachment

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless] [TopologicalSpace M]
  [ChartedSpace H M] [IsManifold I ∞ M] {E' H' S P : Type*} [NormedAddCommGroup E']
  [NormedSpace ℝ E'] [FiniteDimensional ℝ E'] [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'}
  [TopologicalSpace S] [ChartedSpace H' S] [IsManifold J ∞ S] [NormedAddCommGroup P]
  [NormedSpace ℝ P] [FiniteDimensional ℝ P] {f : M → ℝ} {i : SmoothEmbedding J I ∞ S M}
  (hn : (∞ : ℕ∞ω) ≠ 0)

namespace IsNondegenerateCriticalSubmanifold

/-- The functions `negSq` and `posSq` are smooth on the total space of the normal bundle, and the
rescalings are jointly smooth in the scales and the normal vector. -/
private theorem contMDiff_negSq_posSq_rescale (h : i.IsNondegenerateCriticalSubmanifold f)
    (hfs : ContMDiff I 𝓘(ℝ) ∞ f)
    (hdim : Module.finrank ℝ P = Module.finrank ℝ E - Module.finrank ℝ E')
    (g : letI := i.normalSpaceFiberBundle hn hdim
      letI := i.normalSpaceVectorBundle hn hdim
      ContMDiffRiemannianMetric J ∞ P fun s ↦ i.NormalSpace s hn) :
    letI := i.normalSpaceFiberBundle hn hdim
    letI := i.normalSpaceVectorBundle hn hdim
    ContMDiff (J.prod 𝓘(ℝ, P)) 𝓘(ℝ) ∞ (h.negSq (P := P) hn g.toRiemannianMetric) ∧
      ContMDiff (J.prod 𝓘(ℝ, P)) 𝓘(ℝ) ∞ (h.posSq (P := P) hn g.toRiemannianMetric) ∧
      ContMDiff (𝓘(ℝ, ℝ × ℝ).prod (J.prod 𝓘(ℝ, P))) (J.prod 𝓘(ℝ, P)) ∞
        fun p : (ℝ × ℝ) × TotalSpace P (fun s ↦ i.NormalSpace s hn) ↦
          h.rescale hn g.toRiemannianMetric p.1.1 p.1.2 p.2 := by
  have : IsManifold I (∞ + 2) M := .of_le (n := ∞) (by simp)
  have : IsManifold J (∞ + 1) S := by simpa using (inferInstance : IsManifold J ∞ S)
  have hk : (∞ : ℕ∞ω) + 1 ≤ ∞ := by simp
  have hf2 (s : S) : ContMDiffAt I 𝓘(ℝ) (∞ + 2) f (i s) := (hfs (i s)).of_le (by simp)
  let := i.normalSpaceFiberBundle hn hdim
  let := i.normalSpaceVectorBundle hn hdim
  set X := TotalSpace P fun s ↦ i.NormalSpace s hn
  have hneg := h.contMDiff_projection_negativeNormalSpace hn hk hf2 hdim g
  have hpos := h.contMDiff_projection_positiveNormalSpace hn hk hf2 hdim g
  have hH := h.toIsCriticalSubmanifold.contMDiff_normalHessian_apply_self hn hk hf2 hdim
  refine ⟨(contMDiff_const.mul (hH.comp hneg)).neg, contMDiff_const.mul (hH.comp hpos),
    fun p₀ ↦ ?_⟩
  have h1 : ContMDiffAt (𝓘(ℝ, ℝ × ℝ).prod (J.prod 𝓘(ℝ, P))) 𝓘(ℝ, ℝ × ℝ) ∞
      (fun p : (ℝ × ℝ) × X ↦ p.1) p₀ := contMDiffAt_fst
  have h2 : ContMDiffAt (𝓘(ℝ, ℝ × ℝ).prod (J.prod 𝓘(ℝ, P))) (J.prod 𝓘(ℝ, P)) ∞
      (fun p : (ℝ × ℝ) × X ↦ p.2) p₀ := contMDiffAt_snd
  have hA := (Bundle.contMDiffAt_totalSpace_iff.mp (hneg p₀.2)).2.comp p₀ h2
  have hB := (Bundle.contMDiffAt_totalSpace_iff.mp (hpos p₀.2)).2.comp p₀ h2
  have ha := (contDiff_fst (𝕜 := ℝ) (E := ℝ) (F := ℝ)).contMDiff.contMDiffAt.comp p₀ h1
  have hb := (contDiff_snd (𝕜 := ℝ) (E := ℝ) (F := ℝ)).contMDiff.contMDiffAt.comp p₀ h1
  have hproj : ContMDiffAt (𝓘(ℝ, ℝ × ℝ).prod (J.prod 𝓘(ℝ, P))) J ∞
      (fun p : (ℝ × ℝ) × X ↦ p.2.proj) p₀ := (Bundle.contMDiff_proj _).contMDiffAt.comp p₀ h2
  rw [Bundle.contMDiffAt_totalSpace_iff]
  refine ⟨hproj, ((ha.smul hA).add (hb.smul hB)).congr_of_eventuallyEq ?_⟩
  have he := mem_baseSet_trivializationAt P (fun s ↦ i.NormalSpace s hn) p₀.2.proj
  filter_upwards [((FiberBundle.continuous_proj P _).comp continuous_snd).continuousAt
    |>.preimage_mem_nhds ((trivializationAt P _ _).open_baseSet.mem_nhds he)] with p hp
  rw [mem_preimage, comp_apply] at hp
  -- In the trivialization, the fibre coordinate is linear on the fibre over `p.2.proj`.
  have hlin (v : i.NormalSpace p.2.proj hn) :
      (trivializationAt P (fun s ↦ i.NormalSpace s hn) p₀.2.proj ⟨p.2.proj, v⟩).2 =
        (trivializationAt P (fun s ↦ i.NormalSpace s hn) p₀.2.proj).linearMapAt ℝ p.2.proj v := by
    rw [Trivialization.coe_linearMapAt_of_mem _ hp]
  simp only [rescale, negPart, posPart, TotalSpace.mk', Pi.add_apply, Pi.smul_apply', comp_apply,
    hlin, map_add, map_smul]

end IsNondegenerateCriticalSubmanifold

end Attachment

section FamilyAttachment

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless] [TopologicalSpace M]
  [ChartedSpace H M] [IsManifold I ∞ M] {ι : Type*} {E' H' S P : ι → Type*}
  [∀ a, NormedAddCommGroup (E' a)] [∀ a, NormedSpace ℝ (E' a)] [∀ a, FiniteDimensional ℝ (E' a)]
  [∀ a, TopologicalSpace (H' a)] {J : ∀ a, ModelWithCorners ℝ (E' a) (H' a)}
  [∀ a, TopologicalSpace (S a)] [∀ a, ChartedSpace (H' a) (S a)] [∀ a, IsManifold (J a) ∞ (S a)]
  [∀ a, NormedAddCommGroup (P a)] [∀ a, NormedSpace ℝ (P a)] [∀ a, FiniteDimensional ℝ (P a)]
  {f : M → ℝ} {i : ∀ a, SmoothEmbedding (J a) I ∞ (S a) M} (hn : (∞ : ℕ∞ω) ≠ 0)

/-- **Crossing a critical level of finitely many compact Morse–Bott submanifolds attaches their
negative disc bundles.** Let `i a : S a → M`, for `a` in a finite index type, be nondegenerate
critical submanifolds of a smooth function `f` on a Hausdorff, second-countable,
finite-dimensional, boundaryless manifold, each modelled on its own space, with `S a` compact and
nonempty, pairwise disjoint images and `f = c` along each of them. Let `g a` be a smooth fibre
metric on the normal bundle of `i a`.

Then there are smooth partial diffeomorphisms `Θ a` from the total spaces of the normal bundles to
`M`, each defined on a neighbourhood of the zero section and sending it to `i a`, which put `f` in
the Morse–Bott normal form `f (Θ a v) = c + ½ Hessₛ (v, v)`, and an `ε₀ > 0` with the following
property. Let `0 < ε < ε₀` be such that the band `f⁻¹[c - ε, c + ε]` is compact and all its
critical points lie on the submanifolds. Then each negative disc bundle `D a ε` relative to `g a`
(`TauCeti.SmoothEmbedding.IsCriticalSubmanifold.negativeDiscBundle`) lies in the source of `Θ a`,
the images `Θ a (D a ε)` are pairwise disjoint, and `{f ≤ c - ε} ∪ ⋃ a, Θ a (D a ε)` is a strong
deformation retract of `{f ≤ c + ε}`: there is a retraction of `{f ≤ c + ε}` onto it, and a
homotopy in `{f ≤ c + ε}` from this retraction to the identity which fixes it pointwise.

The critical components of a Morse–Bott function on one level may have different dimensions, which
is why each submanifold has its own model. -/
theorem exists_sublevel_union_iUnion_negativeDiscBundle_deformation [T2Space M]
    [SecondCountableTopology M] [Finite ι] [∀ a, (J a).Boundaryless] [∀ a, CompactSpace (S a)]
    [∀ a, Nonempty (S a)] (h : ∀ a, (i a).IsNondegenerateCriticalSubmanifold f)
    (hfs : ContMDiff I 𝓘(ℝ) ∞ f) {c : ℝ} (hc : ∀ a s, f (i a s) = c)
    (hd : Pairwise (Disjoint on fun a ↦ range (i a)))
    (hdim : ∀ a, Module.finrank ℝ (P a) = Module.finrank ℝ E - Module.finrank ℝ (E' a))
    (g : letI : ∀ a, FiberBundle (P a) fun s ↦ (i a).NormalSpace s hn :=
        fun a ↦ (i a).normalSpaceFiberBundle hn (hdim a)
      letI : ∀ a, VectorBundle ℝ (P a) fun s ↦ (i a).NormalSpace s hn :=
        fun a ↦ (i a).normalSpaceVectorBundle hn (hdim a)
      ∀ a, ContMDiffRiemannianMetric (J a) ∞ (P a) fun s ↦ (i a).NormalSpace s hn) :
    letI : ∀ a, FiberBundle (P a) fun s ↦ (i a).NormalSpace s hn :=
      fun a ↦ (i a).normalSpaceFiberBundle hn (hdim a)
    letI : ∀ a, VectorBundle ℝ (P a) fun s ↦ (i a).NormalSpace s hn :=
      fun a ↦ (i a).normalSpaceVectorBundle hn (hdim a)
    ∃ Θ : ∀ a, PartialDiffeomorph ((J a).prod 𝓘(ℝ, P a)) I
        (TotalSpace (P a) fun s ↦ (i a).NormalSpace s hn) M ∞,
      (∀ a s, zeroSection (P a) (fun s ↦ (i a).NormalSpace s hn) s ∈ (Θ a).source) ∧
      (∀ a s, Θ a (zeroSection (P a) (fun s ↦ (i a).NormalSpace s hn) s) = i a s) ∧
      (∀ a, ∀ x ∈ (Θ a).source, f (Θ a x) = c + 2⁻¹ * (h a).normalHessian hn x.proj x.snd x.snd) ∧
      ∃ ε₀ > 0, ∀ ε ∈ Ioo 0 ε₀, IsCompact (f ⁻¹' Icc (c - ε) (c + ε)) →
        criticalPoints I f ∩ f ⁻¹' Icc (c - ε) (c + ε) ⊆ ⋃ a, range (i a) →
        (∀ a, (h a).negativeDiscBundle hn (P a) (g a).toRiemannianMetric ε ⊆ (Θ a).source) ∧
        Pairwise (Disjoint on fun a ↦
          Θ a '' (h a).negativeDiscBundle hn (P a) (g a).toRiemannianMetric ε) ∧
        ∃ r : C({y | f y ≤ c + ε}, ↥({y | f y ≤ c + ε} ∩ ({y | f y ≤ c - ε} ∪
            ⋃ a, Θ a '' (h a).negativeDiscBundle hn (P a) (g a).toRiemannianMetric ε))),
          (∀ y, r (ContinuousMap.inclusion inter_subset_left y) = y) ∧
          Nonempty (((ContinuousMap.inclusion inter_subset_left).comp r).HomotopyRel
            (ContinuousMap.id _) {y | (y : M) ∈ {y | f y ≤ c - ε} ∪
              ⋃ a, Θ a '' (h a).negativeDiscBundle hn (P a) (g a).toRiemannianMetric ε}) := by
  have (a : ι) : T2Space (S a) := (i a).isEmbedding.t2Space
  let : ∀ a, FiberBundle (P a) fun s ↦ (i a).NormalSpace s hn :=
    fun a ↦ (i a).normalSpaceFiberBundle hn (hdim a)
  let : ∀ a, VectorBundle ℝ (P a) fun s ↦ (i a).NormalSpace s hn :=
    fun a ↦ (i a).normalSpaceVectorBundle hn (hdim a)
  have (a : ι) : LocallyCompactSpace (ModelProd (H' a) (P a)) :=
    ((J a).prod 𝓘(ℝ, P a)).locallyCompactSpace
  have (a : ι) : LocallyCompactSpace (TotalSpace (P a) fun s ↦ (i a).NormalSpace s hn) :=
    ChartedSpace.locallyCompactSpace (ModelProd (H' a) (P a)) _
  -- The Morse–Bott lemma on each normal bundle.
  have hΘ := fun a ↦ (h a).exists_morseBott_partialDiffeomorph_normalBundle hn
    (k := ⊤) (by simp) (hdim a) isOpen_univ (subset_univ _) (hfs.contMDiffOn.of_le (by simp))
  choose Θ hΘz hΘi _ hΘf using hΘ
  refine ⟨Θ, hΘz, hΘi, fun a x hx ↦ by rw [hΘf a x hx, hc], ?_⟩
  choose hs ht hσ using fun a ↦ (h a).contMDiff_negSq_posSq_rescale hn hfs (hdim a) (g a)
  -- The curves `b ↦ σ 1 b x` are smooth.
  have hσd (a : ι) (x : TotalSpace (P a) fun s ↦ (i a).NormalSpace s hn) :
      MDifferentiableAt 𝓘(ℝ) ((J a).prod 𝓘(ℝ, P a))
        (fun b ↦ (h a).rescale hn (g a).toRiemannianMetric 1 b x) 1 :=
    (((hσ a).comp ((contDiff_const.prodMk contDiff_id).contMDiff.prodMk contMDiff_const)) 1)
      |>.mdifferentiableAt (by simp)
  -- The image of each zero section is the submanifold.
  have hZ (a : ι) :
      range (i a) = Θ a '' range (zeroSection (P a) fun s ↦ (i a).NormalSpace s hn) := by
    rw [← range_comp]
    exact congrArg range (funext fun s ↦ (hΘi a s).symm)
  obtain ⟨ε₀, hε₀, hmain⟩ := exists_sublevel_union_iUnion_image_deformation hfs Θ hs ht
    (fun a ↦ (h a).negSq_nonneg hn (g a).toRiemannianMetric)
    (fun a ↦ (h a).posSq_nonneg hn (g a).toRiemannianMetric)
    (fun a x hx ↦ by
      rw [hΘf a x hx, hc, (h a).two_inv_mul_normalHessian hn (g a).toRiemannianMetric x]; ring)
    (fun a ↦ isCompact_range (Bundle.contMDiff_zeroSection (n := ∞) (IB := J a) _ _).continuous)
    (fun a ↦ by rintro _ ⟨s, rfl⟩; exact hΘz a s)
    (fun a ↦ by
      rintro _ ⟨s, rfl⟩
      exact ⟨(h a).negSq_zeroSection hn _ s, (h a).posSq_zeroSection hn _ s⟩)
    (fun a x hs ht ↦ ⟨x.proj, (h a).eq_zeroSection_of_negSq_eq_zero hn _ x hs ht⟩)
    (fun a b hab ↦ by simpa only [← hZ] using hd hab)
    (fun a ↦ (h a).rescale hn (g a).toRiemannianMetric) (fun a ↦ (hσ a).continuous) hσd
    (fun a b' b x ↦ (h a).negSq_rescale hn _ x b' b)
    (fun a b' b x ↦ (h a).posSq_rescale hn _ x b' b) (fun a ↦ (h a).rescale_one_one hn _)
    (fun a b x hx ↦ (h a).rescale_one_of_posSq_eq_zero hn _ x b hx)
    (fun a x ↦ ⟨x.proj, ((h a).rescale_zero_zero hn _ x).symm⟩)
  refine ⟨ε₀, hε₀, fun ε hε hcomp hcrit ↦ ?_⟩
  have hD (a : ι) :=
    (h a).setOf_posSq_eq_zero_and_negSq_le hn (P := P a) (g a).toRiemannianMetric ε
  obtain ⟨hsrc, hdisj, hr⟩ := hmain ε hε hcomp (by simpa only [hZ] using hcrit)
  refine ⟨fun a ↦ hD a ▸ hsrc a,
    fun a b hab ↦ by simpa only [Function.onFun, hD] using hdisj hab, ?_⟩
  rwa [iUnion_congr fun a ↦ congrArg (Θ a '' ·) (hD a).symm]

end FamilyAttachment

section Attachment

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless] [TopologicalSpace M]
  [ChartedSpace H M] [IsManifold I ∞ M] {E' H' S P : Type*} [NormedAddCommGroup E']
  [NormedSpace ℝ E'] [FiniteDimensional ℝ E'] [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'}
  [TopologicalSpace S] [ChartedSpace H' S] [IsManifold J ∞ S] [NormedAddCommGroup P]
  [NormedSpace ℝ P] [FiniteDimensional ℝ P] {f : M → ℝ} {i : SmoothEmbedding J I ∞ S M}
  (hn : (∞ : ℕ∞ω) ≠ 0)

namespace IsNondegenerateCriticalSubmanifold

/-- **Crossing the level of a compact Morse–Bott submanifold attaches its negative disc bundle.**
Let `i : S → M` be a nondegenerate critical submanifold of a smooth function `f` on a Hausdorff,
second-countable, finite-dimensional, boundaryless manifold, with `S` compact and nonempty and
`f = c` along `i`, and let `g` be a smooth fibre metric on the normal bundle of `i`.

Then there is a smooth partial diffeomorphism `Θ` from the total space of the normal bundle to
`M`, defined on a neighbourhood of the zero section and sending it to `i`, which puts `f` in the
Morse–Bott normal form `f (Θ v) = c + ½ Hessₛ (v, v)`, and an `ε₀ > 0` with the following
property. Let `0 < ε < ε₀` be such that the band `f⁻¹[c - ε, c + ε]` is compact and all its
critical points lie on `i`. Then the negative disc bundle `D_ε` relative to `g`
(`TauCeti.SmoothEmbedding.IsCriticalSubmanifold.negativeDiscBundle`) lies in the source of `Θ`, and
`{f ≤ c - ε} ∪ Θ(D_ε)` is a strong deformation retract of `{f ≤ c + ε}`: there is a retraction of
`{f ≤ c + ε}` onto it, and a homotopy in `{f ≤ c + ε}` from this retraction to the identity which
fixes it pointwise. -/
theorem exists_sublevel_union_negativeDiscBundle_deformation [T2Space M]
    [SecondCountableTopology M] [J.Boundaryless] [CompactSpace S] [Nonempty S]
    (h : i.IsNondegenerateCriticalSubmanifold f) (hfs : ContMDiff I 𝓘(ℝ) ∞ f) {c : ℝ}
    (hc : ∀ s, f (i s) = c) (hdim : Module.finrank ℝ P = Module.finrank ℝ E - Module.finrank ℝ E')
    (g : letI := i.normalSpaceFiberBundle hn hdim
      letI := i.normalSpaceVectorBundle hn hdim
      ContMDiffRiemannianMetric J ∞ P fun s ↦ i.NormalSpace s hn) :
    letI := i.normalSpaceFiberBundle hn hdim
    letI := i.normalSpaceVectorBundle hn hdim
    ∃ Θ : PartialDiffeomorph (J.prod 𝓘(ℝ, P)) I (TotalSpace P fun s ↦ i.NormalSpace s hn) M ∞,
      (∀ s, zeroSection P (fun s ↦ i.NormalSpace s hn) s ∈ Θ.source) ∧
      (∀ s, Θ (zeroSection P (fun s ↦ i.NormalSpace s hn) s) = i s) ∧
      (∀ x ∈ Θ.source, f (Θ x) = c + 2⁻¹ * h.normalHessian hn x.proj x.snd x.snd) ∧
      ∃ ε₀ > 0, ∀ ε ∈ Ioo 0 ε₀, IsCompact (f ⁻¹' Icc (c - ε) (c + ε)) →
        criticalPoints I f ∩ f ⁻¹' Icc (c - ε) (c + ε) ⊆ range i →
        h.negativeDiscBundle hn P g.toRiemannianMetric ε ⊆ Θ.source ∧
        ∃ r : C({y | f y ≤ c + ε}, ↥({y | f y ≤ c + ε} ∩
            ({y | f y ≤ c - ε} ∪ Θ '' h.negativeDiscBundle hn P g.toRiemannianMetric ε))),
          (∀ y, r (ContinuousMap.inclusion inter_subset_left y) = y) ∧
          Nonempty (((ContinuousMap.inclusion inter_subset_left).comp r).HomotopyRel
            (ContinuousMap.id _) {y | (y : M) ∈
              {y | f y ≤ c - ε} ∪ Θ '' h.negativeDiscBundle hn P g.toRiemannianMetric ε}) := by
  obtain ⟨Θ, hΘz, hΘi, hΘf, ε₀, hε₀, hmain⟩ :=
    exists_sublevel_union_iUnion_negativeDiscBundle_deformation (ι := Unit) (S := fun _ ↦ S)
      (P := fun _ ↦ P) (J := fun _ ↦ J) (i := fun _ ↦ i) hn (fun _ ↦ h) hfs (fun _ ↦ hc)
      Subsingleton.pairwise (fun _ ↦ hdim) (fun _ ↦ g)
  refine ⟨Θ (), hΘz (), hΘi (), hΘf (), ε₀, hε₀, fun ε hε hcomp hcrit ↦ ?_⟩
  obtain ⟨hsrc, -, hr⟩ := hmain ε hε hcomp (by rwa [iUnion_const])
  let := i.normalSpaceFiberBundle hn hdim
  let := i.normalSpaceVectorBundle hn hdim
  rw [show (⋃ a, Θ a '' h.negativeDiscBundle hn P g.toRiemannianMetric ε) =
    Θ () '' h.negativeDiscBundle hn P g.toRiemannianMetric ε from
      Set.ext fun _ ↦ by simp only [mem_iUnion, Unique.exists_iff]] at hr
  exact ⟨hsrc (), hr⟩

/-- **The negative disc bundle of a compact Morse–Bott submanifold is compact.** Let `i : S → M`
be a nondegenerate critical submanifold of a smooth function, with `S` compact and Hausdorff, and
let `g` be a smooth fibre metric on its normal bundle. Then for every `ε` the negative disc bundle
`D_ε = {v ∈ ν⁻ | -½ Hessₛ (v, v) ≤ ε}` relative to `g` is a compact subset of the total space of the
normal bundle. -/
theorem isCompact_negativeDiscBundle [T2Space S] [CompactSpace S]
    (h : i.IsNondegenerateCriticalSubmanifold f) (hfs : ContMDiff I 𝓘(ℝ) ∞ f)
    (hdim : Module.finrank ℝ P = Module.finrank ℝ E - Module.finrank ℝ E')
    (g : letI := i.normalSpaceFiberBundle hn hdim
      letI := i.normalSpaceVectorBundle hn hdim
      ContMDiffRiemannianMetric J ∞ P fun s ↦ i.NormalSpace s hn) (ε : ℝ) :
    letI := i.normalSpaceFiberBundle hn hdim
    letI := i.normalSpaceVectorBundle hn hdim
    IsCompact (h.negativeDiscBundle hn P g.toRiemannianMetric ε) := by
  let := i.normalSpaceFiberBundle hn hdim
  let := i.normalSpaceVectorBundle hn hdim
  have : LocallyCompactSpace (ModelProd H' P) := (J.prod 𝓘(ℝ, P)).locallyCompactSpace
  have : LocallyCompactSpace (TotalSpace P fun s ↦ i.NormalSpace s hn) :=
    ChartedSpace.locallyCompactSpace (ModelProd H' P) _
  obtain ⟨hs, ht, hσ⟩ := h.contMDiff_negSq_posSq_rescale hn hfs hdim g
  set gR := g.toRiemannianMetric
  -- The rays `a ↦ (a u, a w)`, `a ∈ [0, 1]`, join each normal vector to the compact zero section.
  obtain ⟨m, hm, -, hmK⟩ := exists_pos_setOf_lt_subset_and_isCompact
    (isCompact_range (Bundle.contMDiff_zeroSection (n := ∞) (IB := J) _ _).continuous) isOpen_univ
    (subset_univ _) (hs.continuous.add (continuous_const.mul ht.continuous))
    (q := fun x ↦ h.negSq hn gR x + 2 * h.posSq hn gR x) (fun x hx ↦ ⟨x.proj,
      h.eq_zeroSection_of_negSq_eq_zero hn gR x
        (by linarith [h.negSq_nonneg hn gR x, h.posSq_nonneg hn gR x])
        (by linarith [h.negSq_nonneg hn gR x, h.posSq_nonneg hn gR x])⟩)
    (fun a ↦ h.rescale hn gR a a) (fun x ↦ (hσ.continuous.comp ((continuous_id.prodMk
      continuous_id).prodMk continuous_const)).continuousOn)
    (fun a ha x ↦ by
      have ha2 : a ^ 2 ≤ 1 := pow_le_one₀ ha.1 ha.2
      rw [h.negSq_rescale, h.posSq_rescale]
      nlinarith [h.negSq_nonneg hn gR x, h.posSq_nonneg hn gR x])
    (h.rescale_one_one hn gR) (fun x ↦ ⟨x.proj, (h.rescale_zero_zero hn gR x).symm⟩)
  have hD : IsClosed (h.negativeDiscBundle hn P gR ε) := by
    rw [← h.setOf_posSq_eq_zero_and_negSq_le hn gR ε]
    exact (isClosed_eq ht.continuous continuous_const).inter
      (isClosed_le hs.continuous continuous_const)
  set δ := m / 2
  have hK := hmK δ (half_lt_self hm)
  -- A disc bundle of size at most `δ` lies in the compact set `{s + 2t ≤ δ}`.
  have hDK (ε : ℝ) (hεδ : ε ≤ δ) :
      h.negativeDiscBundle hn P gR ε ⊆ {x | h.negSq hn gR x + 2 * h.posSq hn gR x ≤ δ} := by
    rw [← h.setOf_posSq_eq_zero_and_negSq_le hn gR ε]
    rintro x ⟨htx, hsx⟩
    rw [mem_ofPred_eq, htx, mul_zero, add_zero]
    exact hsx.trans hεδ
  rcases le_or_gt ε δ with hεδ | hεδ
  · exact hK.of_isClosed_subset hD (hDK ε hεδ)
  -- A larger one is the image of `D_δ` under the rescaling by `r = √(ε / δ)`.
  have hεδ' : 0 < ε / δ := div_pos ((half_pos hm).trans hεδ) (half_pos hm)
  set r := √(ε / δ)
  have hr : 0 < r := Real.sqrt_pos.2 hεδ'
  have hσr : Continuous (h.rescale hn gR r r) :=
    hσ.continuous.comp ((continuous_const (y := ((r, r) : ℝ × ℝ))).prodMk continuous_id)
  refine ((hK.image hσr).of_isClosed_subset hD) fun x hx ↦ ⟨h.rescale hn gR r⁻¹ r⁻¹ x,
    hDK δ le_rfl ?_, by rw [h.rescale_rescale, mul_inv_cancel₀ hr.ne', h.rescale_one_one]⟩
  rw [← h.setOf_posSq_eq_zero_and_negSq_le hn gR] at hx ⊢
  have hr2 : (r⁻¹) ^ 2 * ε = δ := by
    rw [inv_pow, Real.sq_sqrt hεδ'.le, inv_div, div_mul_cancel₀ _ ((half_pos hm).trans hεδ).ne']
  refine ⟨by rw [h.posSq_rescale, hx.1, mul_zero], ?_⟩
  rw [h.negSq_rescale, ← hr2]
  exact mul_le_mul_of_nonneg_left hx.2 (sq_nonneg _)

/-- **The negative sphere bundle of a compact Morse–Bott submanifold is compact.** Under the
hypotheses of `IsNondegenerateCriticalSubmanifold.isCompact_negativeDiscBundle`, the negative
sphere bundle `S_ε = {v ∈ ν⁻ | -½ Hessₛ (v, v) = ε}` is a compact subset of the total space of the
normal bundle, for every `ε`. -/
theorem isCompact_negativeSphereBundle [T2Space S] [CompactSpace S]
    (h : i.IsNondegenerateCriticalSubmanifold f) (hfs : ContMDiff I 𝓘(ℝ) ∞ f)
    (hdim : Module.finrank ℝ P = Module.finrank ℝ E - Module.finrank ℝ E')
    (g : letI := i.normalSpaceFiberBundle hn hdim
      letI := i.normalSpaceVectorBundle hn hdim
      ContMDiffRiemannianMetric J ∞ P fun s ↦ i.NormalSpace s hn) (ε : ℝ) :
    letI := i.normalSpaceFiberBundle hn hdim
    letI := i.normalSpaceVectorBundle hn hdim
    IsCompact (h.negativeSphereBundle hn P g.toRiemannianMetric ε) := by
  let := i.normalSpaceFiberBundle hn hdim
  let := i.normalSpaceVectorBundle hn hdim
  obtain ⟨hs, ht, -⟩ := h.contMDiff_negSq_posSq_rescale hn hfs hdim g
  refine (h.isCompact_negativeDiscBundle hn hfs hdim g ε).of_isClosed_subset ?_
    (h.negativeSphereBundle_subset_negativeDiscBundle hn P _ ε)
  rw [← h.setOf_posSq_eq_zero_and_negSq_eq hn g.toRiemannianMetric ε]
  exact (isClosed_eq ht.continuous continuous_const).inter
    (isClosed_eq hs.continuous continuous_const)

end IsNondegenerateCriticalSubmanifold

end Attachment

end SmoothEmbedding

namespace IsMorseBottFamily

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless] [TopologicalSpace M]
  [ChartedSpace H M] [IsManifold I ∞ M] {ι : Type*} {E' H' S P : ι → Type*}
  [∀ a, NormedAddCommGroup (E' a)] [∀ a, NormedSpace ℝ (E' a)] [∀ a, FiniteDimensional ℝ (E' a)]
  [∀ a, TopologicalSpace (H' a)] {J : ∀ a, ModelWithCorners ℝ (E' a) (H' a)}
  [∀ a, TopologicalSpace (S a)] [∀ a, ChartedSpace (H' a) (S a)] [∀ a, IsManifold (J a) ∞ (S a)]
  [∀ a, NormedAddCommGroup (P a)] [∀ a, NormedSpace ℝ (P a)] [∀ a, FiniteDimensional ℝ (P a)]
  {f : M → ℝ} {i : ∀ a, SmoothEmbedding (J a) I ∞ (S a) M} (hn : (∞ : ℕ∞ω) ≠ 0)

/-- **Crossing an isolated critical level of a Morse–Bott function attaches the negative disc
bundles of its critical submanifolds on that level.** Let the family `i a : S a → M` exhibit `f` as
a Morse–Bott function (`TauCeti.IsMorseBottFamily`) on a Hausdorff second-countable boundaryless
manifold, not necessarily compact, with pieces modelled on boundaryless models, and let `g a` be a
smooth fibre metric on the normal bundle of `i a`. Let `c : ℝ` and `δ > 0` be such that the band
`f⁻¹[c - δ, c + δ]` is compact, and index the pieces on the level `f = c` by
`{a // ∀ s, f (i a s) = c}`; they lie in the band, so they are finitely many and compact.

Then there are smooth partial diffeomorphisms `Θ a` from the total spaces of the normal bundles of
these pieces to `M`, each defined on a neighbourhood of the zero section and sending it to `i a`,
which put `f` in the Morse–Bott normal form `f (Θ a v) = c + ½ Hessₛ (v, v)`, and an `ε₀ > 0` such
that for `0 < ε < ε₀` each negative disc bundle `D a ε` relative to `g a` lies in the source of
`Θ a`, the images `Θ a (D a ε)` are pairwise disjoint, and `{f ≤ c - ε} ∪ ⋃ a, Θ a (D a ε)` is a
strong deformation retract of `{f ≤ c + ε}`. If
`c` is not a critical value there are no such pieces, and `{f ≤ c - ε}` is a strong deformation
retract of `{f ≤ c + ε}`. -/
theorem exists_sublevel_union_iUnion_negativeDiscBundle_deformation_of_isCompact [T2Space M]
    [SecondCountableTopology M] [∀ a, (J a).Boundaryless] (h : IsMorseBottFamily i f) {c δ : ℝ}
    (hδ : 0 < δ) (hcompact : IsCompact (f ⁻¹' Icc (c - δ) (c + δ)))
    (hdim : ∀ a, Module.finrank ℝ (P a) = Module.finrank ℝ E - Module.finrank ℝ (E' a))
    (g : letI : ∀ a, FiberBundle (P a) fun s ↦ (i a).NormalSpace s hn :=
        fun a ↦ (i a).normalSpaceFiberBundle hn (hdim a)
      letI : ∀ a, VectorBundle ℝ (P a) fun s ↦ (i a).NormalSpace s hn :=
        fun a ↦ (i a).normalSpaceVectorBundle hn (hdim a)
      ∀ a, ContMDiffRiemannianMetric (J a) ∞ (P a) fun s ↦ (i a).NormalSpace s hn) :
    letI : ∀ a, FiberBundle (P a) fun s ↦ (i a).NormalSpace s hn :=
      fun a ↦ (i a).normalSpaceFiberBundle hn (hdim a)
    letI : ∀ a, VectorBundle ℝ (P a) fun s ↦ (i a).NormalSpace s hn :=
      fun a ↦ (i a).normalSpaceVectorBundle hn (hdim a)
    ∃ Θ : ∀ a : {a // ∀ s, f (i a s) = c}, PartialDiffeomorph ((J a).prod 𝓘(ℝ, P a)) I
        (TotalSpace (P a) fun s ↦ (i a).NormalSpace s hn) M ∞,
      (∀ (a : {a // ∀ s, f (i a s) = c}) s,
        zeroSection (P a) (fun s ↦ (i a).NormalSpace s hn) s ∈ (Θ a).source) ∧
      (∀ (a : {a // ∀ s, f (i a s) = c}) s,
        Θ a (zeroSection (P a) (fun s ↦ (i a).NormalSpace s hn) s) = i a s) ∧
      (∀ a : {a // ∀ s, f (i a s) = c}, ∀ x ∈ (Θ a).source, f (Θ a x) =
        c + 2⁻¹ * (h.isNondegenerateCriticalSubmanifold a).normalHessian hn x.proj x.snd x.snd) ∧
      ∃ ε₀ > 0, ∀ ε ∈ Ioo 0 ε₀,
        (∀ a : {a // ∀ s, f (i a s) = c},
          (h.isNondegenerateCriticalSubmanifold a).negativeDiscBundle hn (P a)
            (g a).toRiemannianMetric ε ⊆ (Θ a).source) ∧
        Pairwise (Disjoint on fun a : {a // ∀ s, f (i a s) = c} ↦
          Θ a '' (h.isNondegenerateCriticalSubmanifold a).negativeDiscBundle hn (P a)
            (g a).toRiemannianMetric ε) ∧
        ∃ r : C({y | f y ≤ c + ε}, ↥({y | f y ≤ c + ε} ∩ ({y | f y ≤ c - ε} ∪
            ⋃ a, Θ a '' (h.isNondegenerateCriticalSubmanifold a).negativeDiscBundle hn (P a)
              (g a).toRiemannianMetric ε))),
          (∀ y, r (ContinuousMap.inclusion inter_subset_left y) = y) ∧
          Nonempty (((ContinuousMap.inclusion inter_subset_left).comp r).HomotopyRel
            (ContinuousMap.id _) {y | (y : M) ∈ {y | f y ≤ c - ε} ∪
              ⋃ a, Θ a '' (h.isNondegenerateCriticalSubmanifold a).negativeDiscBundle hn (P a)
                (g a).toRiemannianMetric ε}) := by
  -- The pieces on the level `c` lie in the compact band, so they are finitely many and compact.
  have hsub (a : {a // ∀ s, f (i a s) = c}) : range (i a) ⊆ f ⁻¹' Icc (c - δ) (c + δ) := by
    rintro _ ⟨s, rfl⟩
    rw [mem_preimage, a.property s]
    exact ⟨by linarith, by linarith⟩
  have (a : ι) : Nonempty (S a) := h.nonempty a
  have : Finite {a // ∀ s, f (i a s) = c} :=
    ((h.finite_setOf_range_subset hcompact).subset (t := {a | ∀ s, f (i a s) = c})
      fun a ha ↦ hsub ⟨a, ha⟩).to_subtype
  have (a : {a // ∀ s, f (i a s) = c}) : CompactSpace (S a) :=
    h.compactSpace_of_range_subset hcompact (hsub a)
  obtain ⟨Θ, hΘz, hΘi, hΘf, ε₀, hε₀, hmain⟩ :=
    SmoothEmbedding.exists_sublevel_union_iUnion_negativeDiscBundle_deformation
      (ι := {a // ∀ s, f (i a s) = c}) (S := fun a ↦ S a) (P := fun a ↦ P a) (J := fun a ↦ J a)
      (i := fun a ↦ i a) hn (fun a ↦ h.isNondegenerateCriticalSubmanifold a) h.contMDiff
      (fun a ↦ a.property) (fun a b hab ↦ h.pairwise_disjoint_range fun he ↦ hab (Subtype.ext he))
      (fun a ↦ hdim a) (fun a ↦ g a)
  refine ⟨Θ, hΘz, hΘi, hΘf, ?_⟩
  -- Some `ε₁ > 0` separates `c` from the other critical values in the band, of which there are
  -- finitely many.
  obtain ⟨ε₁, hε₁, hball⟩ := Metric.mem_nhds_iff.1 <|
    ((h.finite_image_criticalPoints_inter hn hcompact).sdiff (t := {c})).isClosed.isOpen_compl
      |>.mem_nhds fun hc ↦ hc.2 rfl
  refine ⟨min ε₀ (min δ ε₁), lt_min hε₀ (lt_min hδ hε₁), fun ε hε ↦ ?_⟩
  have hεε₀ : ε < ε₀ := hε.2.trans_le (min_le_left _ _)
  have hεδ : ε < δ := hε.2.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hεε₁ : ε < ε₁ := hε.2.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have hband : f ⁻¹' Icc (c - ε) (c + ε) ⊆ f ⁻¹' Icc (c - δ) (c + δ) :=
    preimage_mono (Icc_subset_Icc (by linarith) (by linarith))
  refine hmain ε ⟨hε.1, hεε₀⟩ (hcompact.of_isClosed_subset
    (isClosed_Icc.preimage h.contMDiff.continuous) hband) fun x ⟨hx, hxb⟩ ↦ ?_
  -- A critical point in the band has value `c`, so its piece lies on the level `c`.
  have hfx : f x = c := by
    by_contra hne
    refine hball (Metric.mem_ball.2 ?_) ⟨mem_image_of_mem f ⟨hx, hband hxb⟩, hne⟩
    rw [Real.dist_eq, abs_lt]
    constructor <;> linarith [hxb.1, hxb.2]
  exact h.mem_iUnion_range_of_apply_eq hn hx hfx

/-- **Crossing a critical level of a Morse–Bott function on a compact manifold attaches the
negative disc bundles of its critical submanifolds on that level.** Let the family `i a : S a → M`
exhibit `f` as a Morse–Bott function (`TauCeti.IsMorseBottFamily`) on a compact Hausdorff
second-countable boundaryless manifold, with pieces modelled on boundaryless models, and let `g a`
be a smooth fibre metric on the normal bundle of `i a`. Fix `c : ℝ`, and index the pieces on the
level `f = c` by `{a // ∀ s, f (i a s) = c}`.

Then there are smooth partial diffeomorphisms `Θ a` from the total spaces of the normal bundles of
these pieces to `M`, each defined on a neighbourhood of the zero section and sending it to `i a`,
which put `f` in the Morse–Bott normal form `f (Θ a v) = c + ½ Hessₛ (v, v)`, and an `ε₀ > 0` such
that for `0 < ε < ε₀` each negative disc bundle `D a ε` relative to `g a` lies in the source of
`Θ a`, the images `Θ a (D a ε)` are pairwise disjoint, and `{f ≤ c - ε} ∪ ⋃ a, Θ a (D a ε)` is a
strong deformation retract of `{f ≤ c + ε}`. If
`c` is not a critical value there are no such pieces, and `{f ≤ c - ε}` is a strong deformation
retract of `{f ≤ c + ε}`. -/
theorem exists_sublevel_union_iUnion_negativeDiscBundle_deformation [T2Space M]
    [SecondCountableTopology M] [CompactSpace M] [∀ a, (J a).Boundaryless]
    (h : IsMorseBottFamily i f) (c : ℝ)
    (hdim : ∀ a, Module.finrank ℝ (P a) = Module.finrank ℝ E - Module.finrank ℝ (E' a))
    (g : letI : ∀ a, FiberBundle (P a) fun s ↦ (i a).NormalSpace s hn :=
        fun a ↦ (i a).normalSpaceFiberBundle hn (hdim a)
      letI : ∀ a, VectorBundle ℝ (P a) fun s ↦ (i a).NormalSpace s hn :=
        fun a ↦ (i a).normalSpaceVectorBundle hn (hdim a)
      ∀ a, ContMDiffRiemannianMetric (J a) ∞ (P a) fun s ↦ (i a).NormalSpace s hn) :
    letI : ∀ a, FiberBundle (P a) fun s ↦ (i a).NormalSpace s hn :=
      fun a ↦ (i a).normalSpaceFiberBundle hn (hdim a)
    letI : ∀ a, VectorBundle ℝ (P a) fun s ↦ (i a).NormalSpace s hn :=
      fun a ↦ (i a).normalSpaceVectorBundle hn (hdim a)
    ∃ Θ : ∀ a : {a // ∀ s, f (i a s) = c}, PartialDiffeomorph ((J a).prod 𝓘(ℝ, P a)) I
        (TotalSpace (P a) fun s ↦ (i a).NormalSpace s hn) M ∞,
      (∀ (a : {a // ∀ s, f (i a s) = c}) s,
        zeroSection (P a) (fun s ↦ (i a).NormalSpace s hn) s ∈ (Θ a).source) ∧
      (∀ (a : {a // ∀ s, f (i a s) = c}) s,
        Θ a (zeroSection (P a) (fun s ↦ (i a).NormalSpace s hn) s) = i a s) ∧
      (∀ a : {a // ∀ s, f (i a s) = c}, ∀ x ∈ (Θ a).source, f (Θ a x) =
        c + 2⁻¹ * (h.isNondegenerateCriticalSubmanifold a).normalHessian hn x.proj x.snd x.snd) ∧
      ∃ ε₀ > 0, ∀ ε ∈ Ioo 0 ε₀,
        (∀ a : {a // ∀ s, f (i a s) = c},
          (h.isNondegenerateCriticalSubmanifold a).negativeDiscBundle hn (P a)
            (g a).toRiemannianMetric ε ⊆ (Θ a).source) ∧
        Pairwise (Disjoint on fun a : {a // ∀ s, f (i a s) = c} ↦
          Θ a '' (h.isNondegenerateCriticalSubmanifold a).negativeDiscBundle hn (P a)
            (g a).toRiemannianMetric ε) ∧
        ∃ r : C({y | f y ≤ c + ε}, ↥({y | f y ≤ c + ε} ∩ ({y | f y ≤ c - ε} ∪
            ⋃ a, Θ a '' (h.isNondegenerateCriticalSubmanifold a).negativeDiscBundle hn (P a)
              (g a).toRiemannianMetric ε))),
          (∀ y, r (ContinuousMap.inclusion inter_subset_left y) = y) ∧
          Nonempty (((ContinuousMap.inclusion inter_subset_left).comp r).HomotopyRel
            (ContinuousMap.id _) {y | (y : M) ∈ {y | f y ≤ c - ε} ∪
              ⋃ a, Θ a '' (h.isNondegenerateCriticalSubmanifold a).negativeDiscBundle hn (P a)
                (g a).toRiemannianMetric ε}) :=
  h.exists_sublevel_union_iUnion_negativeDiscBundle_deformation_of_isCompact hn one_pos
    (isClosed_Icc.preimage h.contMDiff.continuous).isCompact hdim g

end IsMorseBottFamily

end TauCeti
