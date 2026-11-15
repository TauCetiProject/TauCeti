/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.Bott.Attachment
public import TauCeti.Geometry.Manifold.Morse.Bott.NormalSubbundle
public import TauCeti.Geometry.Manifold.Morse.Bott.Tubular
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

The normal form `Θ` is the Morse–Bott lemma on the normal bundle
(`IsNondegenerateCriticalSubmanifold.exists_morseBott_partialDiffeomorph_normalBundle`).
Writing a normal vector as `v = u + w` with `u ∈ ν⁻` and `w ∈ ν⁺`, the two parts are orthogonal
for the normal Hessian, so `f ∘ Θ = c - s + t` with `s = -½ Hessₛ (u, u) ≥ 0` and
`t = ½ Hessₛ (w, w) ≥ 0`. These are smooth on the total space, since the projections onto `ν⁻`
and `ν⁺` are (`IsNondegenerateCriticalSubmanifold.contMDiff_projection_negativeNormalSpace`) and so
is the quadratic form of the normal Hessian
(`TauCeti.SmoothEmbedding.IsCriticalSubmanifold.contMDiff_normalHessian_apply_self`); rescaling
`(u, w) ↦ (a u, b w)` multiplies `s` by `a²` and `t` by `b²`. The attachment theorem for a normal
form given by a partial diffeomorphism (`TauCeti.exists_sublevel_union_image_deformation`) then
applies, with tube the image under `Θ` of a sublevel `{s + 2t < m}`. Since `s + 2t` is positive
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

## Main results

In the namespace `TauCeti.SmoothEmbedding`:

* `IsNondegenerateCriticalSubmanifold.exists_sublevel_union_negativeDiscBundle_deformation`:
  crossing the level of a compact Morse–Bott submanifold attaches its negative disc bundle, up to
  a strong deformation retraction.

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
  {x | x.2 ∈ h.negativeNormalSpace hn g x.proj ∧ -(2⁻¹ * h.normalHessian hn x.proj x.2 x.2) ≤ ε}

variable {h P g} in
@[simp]
theorem mem_negativeDiscBundle {ε : ℝ} {x : TotalSpace P fun s ↦ i.NormalSpace s hn} :
    x ∈ h.negativeDiscBundle hn P g ε ↔
      x.2 ∈ h.negativeNormalSpace hn g x.proj ∧ -(2⁻¹ * h.normalHessian hn x.proj x.2 x.2) ≤ ε :=
  Iff.rfl

variable {h P g} in
/-- A vector of the negative disc bundle lies in the negative normal space. -/
theorem mem_negativeNormalSpace_of_mem_negativeDiscBundle {ε : ℝ}
    {x : TotalSpace P fun s ↦ i.NormalSpace s hn} (hx : x ∈ h.negativeDiscBundle hn P g ε) :
    x.2 ∈ h.negativeNormalSpace hn g x.proj :=
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
  -(2⁻¹ * h.normalHessian hn x.proj (h.negPart hn g x.proj x.2) (h.negPart hn g x.proj x.2))

/-- Half the normal Hessian of the positive part of a normal vector. -/
private def posSq (x : TotalSpace P fun s ↦ i.NormalSpace s hn) : ℝ :=
  2⁻¹ * h.normalHessian hn x.proj (h.posPart hn g x.proj x.2) (h.posPart hn g x.proj x.2)

/-- Rescale the negative part of a normal vector by `a` and its positive part by `b`. -/
private def rescale (a b : ℝ) (x : TotalSpace P fun s ↦ i.NormalSpace s hn) :
    TotalSpace P fun s ↦ i.NormalSpace s hn :=
  ⟨x.proj, a • h.negPart hn g x.proj x.2 + b • h.posPart hn g x.proj x.2⟩

variable {s : S} (v : i.NormalSpace s hn) (x : TotalSpace P fun s ↦ i.NormalSpace s hn)

private theorem negSq_mk : h.negSq hn g (⟨s, v⟩ : TotalSpace P fun s ↦ i.NormalSpace s hn) =
    -(2⁻¹ * h.normalHessian hn s (h.negPart hn g s v) (h.negPart hn g s v)) :=
  rfl

private theorem posSq_mk : h.posSq hn g (⟨s, v⟩ : TotalSpace P fun s ↦ i.NormalSpace s hn) =
    2⁻¹ * h.normalHessian hn s (h.posPart hn g s v) (h.posPart hn g s v) :=
  rfl

private theorem rescale_def (a b : ℝ) : h.rescale hn g a b x =
    ⟨x.proj, a • h.negPart hn g x.proj x.2 + b • h.posPart hn g x.proj x.2⟩ :=
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
  by_cases hv : h.negPart hn g x.proj x.2 = 0
  · simp [negSq, hv]
  · have := h.normalHessian_apply_self_neg_of_mem_negativeNormalSpace hn g
      (h.negPart_mem hn g x.2) hv
    simp only [negSq]
    linarith

private theorem posSq_nonneg : 0 ≤ h.posSq hn g x := by
  by_cases hv : h.posPart hn g x.proj x.2 = 0
  · simp [posSq, hv]
  · have := h.normalHessian_apply_self_pos_of_mem_positiveNormalSpace hn g
      (h.posPart_mem hn g x.2) hv
    simp only [posSq]
    linarith

private theorem negPart_eq_zero (hx : h.negSq hn g x = 0) : h.negPart hn g x.proj x.2 = 0 := by
  by_contra hne
  have := h.normalHessian_apply_self_neg_of_mem_negativeNormalSpace hn g
    (h.negPart_mem hn g x.2) hne
  simp only [negSq] at hx
  linarith

private theorem posPart_eq_zero (hx : h.posSq hn g x = 0) : h.posPart hn g x.proj x.2 = 0 := by
  by_contra hne
  have := h.normalHessian_apply_self_pos_of_mem_positiveNormalSpace hn g
    (h.posPart_mem hn g x.2) hne
  simp only [posSq] at hx
  linarith

/-- Half the normal Hessian is `-negSq + posSq`. -/
private theorem two_inv_mul_normalHessian :
    2⁻¹ * h.normalHessian hn x.proj x.2 x.2 = -h.negSq hn g x + h.posSq hn g x := by
  rw [negSq, posSq, h.normalHessian_eq_add hn g x.2]
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
  have hH (hp : h.posPart hn g x.proj x.2 = 0) :
      -(2⁻¹ * h.normalHessian hn x.proj x.2 x.2) = h.negSq hn g x := by
    rw [h.two_inv_mul_normalHessian hn g x, posSq, hp]
    simp
  refine ⟨fun ⟨ht, hs⟩ ↦ ⟨h.posPart_eq_zero hn g x ht, by rwa [hH (h.posPart_eq_zero hn g x ht)]⟩,
    fun ⟨hp, hs⟩ ↦ ⟨by simp [posSq, hp], by rwa [hH hp] at hs⟩⟩

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
      (∀ x ∈ Θ.source, f (Θ x) = c + 2⁻¹ * h.normalHessian hn x.proj x.2 x.2) ∧
      ∃ ε₀ > 0, ∀ ε ∈ Ioo 0 ε₀, IsCompact (f ⁻¹' Icc (c - ε) (c + ε)) →
        criticalPoints I f ∩ f ⁻¹' Icc (c - ε) (c + ε) ⊆ range i →
        h.negativeDiscBundle hn P g.toRiemannianMetric ε ⊆ Θ.source ∧
        ∃ r : C({y | f y ≤ c + ε}, ↥({y | f y ≤ c + ε} ∩
            ({y | f y ≤ c - ε} ∪ Θ '' h.negativeDiscBundle hn P g.toRiemannianMetric ε))),
          (∀ y, r (ContinuousMap.inclusion inter_subset_left y) = y) ∧
          Nonempty (((ContinuousMap.inclusion inter_subset_left).comp r).HomotopyRel
            (ContinuousMap.id _) {y | (y : M) ∈
              {y | f y ≤ c - ε} ∪ Θ '' h.negativeDiscBundle hn P g.toRiemannianMetric ε}) := by
  have : T2Space S := i.isEmbedding.t2Space
  let := i.normalSpaceFiberBundle hn hdim
  let := i.normalSpaceVectorBundle hn hdim
  have : LocallyCompactSpace (ModelProd H' P) := (J.prod 𝓘(ℝ, P)).locallyCompactSpace
  have : LocallyCompactSpace (TotalSpace P fun s ↦ i.NormalSpace s hn) :=
    ChartedSpace.locallyCompactSpace (ModelProd H' P) _
  -- The Morse–Bott lemma on the normal bundle.
  obtain ⟨Θ, hΘz, hΘi, -, hΘf⟩ := h.exists_morseBott_partialDiffeomorph_normalBundle hn
    (k := ⊤) (by simp) hdim isOpen_univ (subset_univ _) (hfs.contMDiffOn.of_le (by simp))
  refine ⟨Θ, hΘz, hΘi, fun x hx ↦ by rw [hΘf x hx, hc], ?_⟩
  obtain ⟨hs, ht, hσ⟩ := h.contMDiff_negSq_posSq_rescale hn hfs hdim g
  set gR := g.toRiemannianMetric
  -- The curves `b ↦ σ 1 b x` are smooth.
  have hσd (x : TotalSpace P fun s ↦ i.NormalSpace s hn) :
      MDifferentiableAt 𝓘(ℝ) (J.prod 𝓘(ℝ, P)) (fun b ↦ h.rescale hn gR 1 b x) 1 :=
    ((hσ.comp ((contDiff_const.prodMk contDiff_id).contMDiff.prodMk contMDiff_const)) 1)
      |>.mdifferentiableAt (by simp)
  obtain ⟨ε₀, hε₀, hmain⟩ := exists_sublevel_union_image_deformation hfs Θ hs ht
    (h.negSq_nonneg hn gR) (h.posSq_nonneg hn gR)
    (fun x hx ↦ by rw [hΘf x hx, hc, h.two_inv_mul_normalHessian hn gR x]; ring)
    (isCompact_range (Bundle.contMDiff_zeroSection (n := ∞) (IB := J) _ _).continuous)
    (by rintro _ ⟨s, rfl⟩; exact hΘz s)
    (by rintro _ ⟨s, rfl⟩; exact ⟨h.negSq_zeroSection hn gR s, h.posSq_zeroSection hn gR s⟩)
    (fun x hs ht ↦ ⟨x.proj, h.eq_zeroSection_of_negSq_eq_zero hn gR x hs ht⟩)
    (h.rescale hn gR) hσ.continuous hσd (fun a b x ↦ h.negSq_rescale hn gR x a b)
    (fun a b x ↦ h.posSq_rescale hn gR x a b) (h.rescale_one_one hn gR)
    (fun b x hx ↦ h.rescale_one_of_posSq_eq_zero hn gR x b hx)
    (fun x ↦ ⟨x.proj, (h.rescale_zero_zero hn gR x).symm⟩)
  refine ⟨ε₀, hε₀, fun ε hε hcomp hcrit ↦ ?_⟩
  have hZ : range i = Θ '' range (zeroSection P fun s ↦ i.NormalSpace s hn) := by
    rw [← range_comp]
    exact congrArg range (funext fun s ↦ (hΘi s).symm)
  rw [← h.setOf_posSq_eq_zero_and_negSq_le hn gR ε]
  exact hmain ε hε hcomp (hZ ▸ hcrit)

end IsNondegenerateCriticalSubmanifold

end Attachment

end SmoothEmbedding

end TauCeti
