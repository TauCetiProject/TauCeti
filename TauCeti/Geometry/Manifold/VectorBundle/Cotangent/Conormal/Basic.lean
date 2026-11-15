/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.LocallyConvex.Polar
public import TauCeti.Analysis.Normed.Module.FiniteDimension
public import TauCeti.Geometry.Manifold.VectorBundle.Cotangent.Relation

/-!
# Conormal covectors of a map

For a map `i : Q → M`, the **conormal set** `TauCeti.CotangentBundle.conormal J I i` is the set of
covectors `p ∈ T*_{i q} M` annihilating the tangent image `di_q (T_q Q)`, for some `q : Q`. For an
embedded submanifold `Q ⊆ M` this is the conormal bundle `N*Q` as a subset of `T*M`. Its fibre
over `q` is the annihilator `TauCeti.CotangentBundle.conormalSpace J I i q` of the tangent image;
when `di_q` is injective and `M` is finite-dimensional it has dimension `dim M - dim Q`
(`TauCeti.CotangentBundle.finrank_add_finrank_conormalSpace`), so that `N*Q` has the dimension
of `M`.

A covector is conormal exactly when the cotangent relation of `i`
(`TauCeti.CotangentBundle.cotangentRel`) relates it to a zero covector of `T*Q`. By the chain
rule, conormal sets are independent of the parametrization
(`TauCeti.CotangentBundle.conormal_comp_diffeomorph`) and are carried to each other by cotangent
lifts of diffeomorphisms (`TauCeti.CotangentBundle.image_cotangent_conormal`).

The two extreme examples are the conormal set of the identity, which is the zero section
(`TauCeti.CotangentBundle.conormal_id`), and that of a constant map, which is the whole fibre over
its value (`TauCeti.CotangentBundle.conormal_const`).

As for `TauCeti.CotangentBundle.cotangentRel`, the differential is Mathlib's `mfderiv`, which is
`0` where `i` is not differentiable.

## References

* A. Cannas da Silva, *Lectures on Symplectic Geometry*, Lecture Notes in Mathematics 1764,
  Springer, 2001, Section 3.3.
* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Graduate Texts in Mathematics 218,
  Springer, 2013, Chapter 11.
-/

public section

noncomputable section

open Bundle Module Set
open scoped Manifold ContDiff

namespace TauCeti.CotangentBundle

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G]
  {E₂ : Type*} [NormedAddCommGroup E₂] [NormedSpace 𝕜 E₂]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners 𝕜 F H'}
  {H'' : Type*} [TopologicalSpace H''] {K : ModelWithCorners 𝕜 G H''}
  {H₂ : Type*} [TopologicalSpace H₂] {I₂ : ModelWithCorners 𝕜 E₂ H₂}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {Q : Type*} [TopologicalSpace Q] [ChartedSpace H' Q]
  {P : Type*} [TopologicalSpace P] [ChartedSpace H'' P]
  {M₂ : Type*} [TopologicalSpace M₂] [ChartedSpace H₂ M₂]

/-! ### The conormal fibre -/

/-- The **conormal space** of `i : Q → M` at `q`: the covectors at `i q` which annihilate the
tangent image `di_q (T_q Q)`, that is, the polar `StrongDual.polarSubmodule` of that image. -/
def conormalSpace (J : ModelWithCorners 𝕜 F H') (I : ModelWithCorners 𝕜 E H) (i : Q → M)
    (q : Q) : Submodule 𝕜 (TangentSpace I (i q) →L[𝕜] 𝕜) :=
  StrongDual.polarSubmodule 𝕜
    (LinearMap.range (mfderiv J I i q : TangentSpace J q →ₗ[𝕜] TangentSpace I (i q)))

/-- A covector at `i q` is conormal at `q` when it vanishes on the image of `di_q`. -/
@[simp]
theorem mem_conormalSpace_iff {i : Q → M} {q : Q} {p : TangentSpace I (i q) →L[𝕜] 𝕜} :
    p ∈ conormalSpace J I i q ↔ p ∘L mfderiv J I i q = 0 := by
  rw [conormalSpace, StrongDual.mem_polarSubmodule, ContinuousLinearMap.ext_iff]
  simp

/-- **The dimension of the conormal space.** If `M` is finite-dimensional and the differential
of `i` at `q` is injective, then `dim Q + dim (conormalSpace J I i q) = dim M`. -/
theorem finrank_add_finrank_conormalSpace [CompleteSpace 𝕜] [FiniteDimensional 𝕜 E]
    {i : Q → M} {q : Q} (hi : Function.Injective (mfderiv J I i q)) :
    finrank 𝕜 F + finrank 𝕜 (conormalSpace J I i q) = finrank 𝕜 E := by
  let L : F →L[𝕜] E := mfderiv J I i q
  have : FiniteDimensional 𝕜 F := FiniteDimensional.of_injective L.toLinearMap hi
  let pre : (E →L[𝕜] 𝕜) →L[𝕜] F →L[𝕜] 𝕜 := (ContinuousLinearMap.compL 𝕜 F E 𝕜).flip L
  have hrange : LinearMap.range (pre : (E →L[𝕜] 𝕜) →ₗ[𝕜] F →L[𝕜] 𝕜) = ⊤ :=
    LinearMap.range_eq_top.mpr (ContinuousLinearMap.surjective_compL_flip_of_injective hi)
  have hker : LinearMap.ker (pre : (E →L[𝕜] 𝕜) →ₗ[𝕜] F →L[𝕜] 𝕜) = conormalSpace J I i q := by
    ext p
    -- `TangentSpace I (i q)` is `E` by definition, and `pre p` is `p ∘L L`, so both
    -- memberships say that `p` vanishes on the image of `L`.
    exact LinearMap.mem_ker.trans mem_conormalSpace_iff.symm
  have hrn := LinearMap.finrank_range_add_finrank_ker (pre : (E →L[𝕜] 𝕜) →ₗ[𝕜] F →L[𝕜] 𝕜)
  rw [hrange, hker, finrank_top, ContinuousLinearMap.dual_finrank_eq,
    ContinuousLinearMap.dual_finrank_eq] at hrn
  exact hrn

/-! ### The conormal set -/

/-- The **conormal set** of a map `i : Q → M`: the covectors of `M` at points `i q` which
annihilate the tangent image `di_q (T_q Q)`. For an embedded submanifold this is its conormal
bundle `N*Q ⊆ T*M`. -/
def conormal (J : ModelWithCorners 𝕜 F H') (I : ModelWithCorners 𝕜 E H) (i : Q → M) :
    Set (CotangentBundle I M) :=
  {w | ∃ q, i q = w.proj ∧ w.2 ∘L mfderiv J I i q = 0}

/-- A covector is conormal to `i` when it lies over some `i q` and vanishes on the image of
`di_q`. -/
theorem mem_conormal_iff {i : Q → M} {w : CotangentBundle I M} :
    w ∈ conormal J I i ↔ ∃ q, i q = w.proj ∧ w.2 ∘L mfderiv J I i q = 0 :=
  Iff.rfl

/-- A covector is conormal to `i` exactly when the cotangent relation of `i` relates a zero
covector of `T*Q` to it. -/
theorem mem_conormal_iff_exists_cotangentRel {i : Q → M} {w : CotangentBundle I M} :
    w ∈ conormal J I i ↔
      ∃ q, cotangentRel J I i (zeroSection (F →L[𝕜] 𝕜) (fun q : Q ↦ TangentSpace J q →L[𝕜] 𝕜) q)
        w := by
  simp only [mem_conormal_iff, cotangentRel_iff, zeroSection_proj, zeroSection_snd]
  exact exists_congr fun q ↦ and_congr_right fun _ ↦ eq_comm

/-- For an injective map `i`, a covector at `i q` is conormal to `i` exactly when it lies in the
conormal space at `q`. -/
theorem mk_mem_conormal_iff {i : Q → M} (hi : Function.Injective i) (q : Q)
    (p : TangentSpace I (i q) →L[𝕜] 𝕜) :
    TotalSpace.mk' (E →L[𝕜] 𝕜) (i q) p ∈ conormal J I i ↔ p ∈ conormalSpace J I i q := by
  rw [mem_conormalSpace_iff]
  refine ⟨fun ⟨q', hq', hp⟩ ↦ ?_, fun hp ↦ ⟨q, rfl, hp⟩⟩
  obtain rfl := hi hq'
  exact hp

/-- The covectors of the conormal space at `q` are conormal to `i`. -/
theorem mk_mem_conormal {i : Q → M} {q : Q} {p : TangentSpace I (i q) →L[𝕜] 𝕜}
    (hp : p ∈ conormalSpace J I i q) : TotalSpace.mk' (E →L[𝕜] 𝕜) (i q) p ∈ conormal J I i :=
  ⟨q, rfl, mem_conormalSpace_iff.mp hp⟩

/-- The zero covector at every point `i q` is conormal to `i`. -/
@[simp]
theorem zeroSection_mem_conormal (i : Q → M) (q : Q) :
    zeroSection (E →L[𝕜] 𝕜) (fun x : M ↦ TangentSpace I x →L[𝕜] 𝕜) (i q) ∈ conormal J I i :=
  mk_mem_conormal (Submodule.zero_mem _)

/-- The conormal set of `i` lies over the image of `i`, and covers all of it. -/
@[simp]
theorem proj_image_conormal (i : Q → M) :
    π (E →L[𝕜] 𝕜) (fun x : M ↦ TangentSpace I x →L[𝕜] 𝕜) '' conormal J I i = range i := by
  refine Subset.antisymm ?_ ?_
  · rintro _ ⟨w, ⟨q, hq, -⟩, rfl⟩
    exact ⟨q, hq⟩
  · rintro _ ⟨q, rfl⟩
    exact ⟨_, zeroSection_mem_conormal i q, rfl⟩

/-! ### Examples -/

/-- **The conormal set of a submersive surjection is the zero section.** If `i` is surjective
with surjective differentials, then only zero covectors annihilate its tangent images. -/
theorem conormal_eq_range_zeroSection {i : Q → M} (hi : Function.Surjective i)
    (hdi : ∀ q, Function.Surjective (mfderiv J I i q)) :
    conormal J I i = range (zeroSection (E →L[𝕜] 𝕜) (fun x : M ↦ TangentSpace I x →L[𝕜] 𝕜)) := by
  refine Subset.antisymm ?_ ?_
  · rintro w ⟨q, _, hw⟩
    refine ⟨w.proj, CotangentBundle.ext rfl fun v ↦ ?_⟩
    obtain ⟨u, rfl⟩ := hdi q v
    exact (DFunLike.congr_fun hw u).symm
  · rintro _ ⟨x, rfl⟩
    obtain ⟨q, rfl⟩ := hi x
    exact zeroSection_mem_conormal i q

variable (I) in
/-- **The conormal set of `M` itself is the zero section.** -/
@[simp]
theorem conormal_id :
    conormal I I (id : M → M) =
      range (zeroSection (E →L[𝕜] 𝕜) (fun x : M ↦ TangentSpace I x →L[𝕜] 𝕜)) :=
  conormal_eq_range_zeroSection Function.surjective_id fun x ↦ by
    rw [mfderiv_id]
    exact Function.surjective_id

variable (J) in
/-- **The conormal set of a point is its whole cotangent fibre.** A constant map from a nonempty
source has zero differential, so every covector over its value is conormal. -/
@[simp]
theorem conormal_const [Nonempty Q] (y : M) :
    conormal J I (fun _ : Q ↦ y) =
      π (E →L[𝕜] 𝕜) (fun x : M ↦ TangentSpace I x →L[𝕜] 𝕜) ⁻¹' {y} := by
  ext w
  simp only [mem_conormal_iff_exists_cotangentRel, cotangentRel_const_iff, zeroSection_snd,
    and_true, exists_const, mem_preimage, mem_singleton_iff]
  exact eq_comm

/-! ### Reparametrization and transport -/

/-- Precomposing `i : Q → M` with a differentiable surjection `g : P → Q` whose differentials are
surjective does not change its conormal set. -/
theorem conormal_comp_of_surjective {g : P → Q} {i : Q → M}
    (hg : MDifferentiable K J g) (hi : MDifferentiable J I i)
    (hsurj : Function.Surjective g)
    (hdg : ∀ p, Function.Surjective (mfderiv K J g p)) :
    conormal K I (i ∘ g) = conormal J I i := by
  ext ⟨x, α⟩
  simp only [mem_conormal_iff]
  constructor
  · rintro ⟨p, rfl, hann⟩
    refine ⟨g p, rfl, ?_⟩
    ext u
    obtain ⟨v, rfl⟩ := hdg p u
    rw [ContinuousLinearMap.comp_apply, ← mfderiv_comp_apply p (hi (g p)) (hg p) v]
    exact DFunLike.congr_fun hann v
  · rintro ⟨q, rfl, hann⟩
    obtain ⟨p, rfl⟩ := hsurj q
    refine ⟨p, rfl, ?_⟩
    ext v
    rw [ContinuousLinearMap.comp_apply, mfderiv_comp_apply p (hi (g p)) (hg p) v]
    exact DFunLike.congr_fun hann (mfderiv K J g p v)

/-- **The conormal set does not depend on the parametrization.** Precomposing a map with a
diffeomorphism of its source does not change its conormal set. -/
theorem conormal_comp_diffeomorph (φ : P ≃ₘ⟮K, J⟯ Q) {i : Q → M} :
    conormal K I (i ∘ φ) = conormal J I i := by
  ext ⟨x, α⟩
  simp only [mem_conormal_iff]
  constructor
  · rintro ⟨p, rfl, hann⟩
    refine ⟨φ p, rfl, ?_⟩
    ext u
    obtain ⟨v, rfl⟩ : ∃ v, mfderiv K J φ p v = u :=
      ⟨mfderiv J K φ.symm (φ p) u, φ.mfderiv_apply_mfderiv_symm_apply (by simp) p u⟩
    rw [φ.mfderiv_comp_diffeomorph (by simp)] at hann
    exact DFunLike.congr_fun hann v
  · rintro ⟨q, rfl, hann⟩
    obtain ⟨p, rfl⟩ : ∃ p, φ p = q := φ.surjective q
    refine ⟨p, rfl, ?_⟩
    rw [φ.mfderiv_comp_diffeomorph (by simp), ← ContinuousLinearMap.comp_assoc, hann,
      ContinuousLinearMap.zero_comp]

/-- **Cotangent lifts carry conormal sets to conormal sets.** For a diffeomorphism `h : M → M₂`,
the cotangent lift of `h` maps the conormal set of a map `i` onto the conormal
set of `h ∘ i`. -/
theorem image_cotangent_conormal [IsManifold I 2 M] [IsManifold I₂ 2 M₂] (h : M ≃ₘ⟮I, I₂⟯ M₂)
    {i : Q → M} : h.cotangent '' conormal J I i = conormal J I₂ (h ∘ i) := by
  ext w
  simp only [mem_conormal_iff, mem_image]
  constructor
  · rintro ⟨⟨x, α⟩, ⟨q, hq, hz⟩, rfl⟩
    obtain rfl : i q = x := hq
    refine ⟨q, (h.proj_cotangent ⟨i q, α⟩).symm, ?_⟩
    ext v
    rw [h.mfderiv_diffeomorph_comp (by simp)]
    exact (h.cotangent_snd_apply_mfderiv ⟨i q, α⟩ _).trans (DFunLike.congr_fun hz v)
  · rintro ⟨q, hq, hw⟩
    obtain ⟨y, β⟩ := w
    obtain rfl : h (i q) = y := hq
    refine ⟨TotalSpace.mk' (E →L[𝕜] 𝕜) (i q) (β ∘L mfderiv I I₂ h (i q)),
      ⟨q, rfl, ?_⟩, ?_⟩
    · rw [h.mfderiv_diffeomorph_comp (by simp)] at hw
      exact hw
    · refine CotangentBundle.ext (h.proj_cotangent _) fun v ↦ ?_
      exact (h.cotangent_snd_apply _ v).trans
        (congrArg β (h.mfderiv_apply_mfderiv_symm_apply (by simp) (i q) v))

end TauCeti.CotangentBundle
