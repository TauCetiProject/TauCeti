/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Immersion
public import TauCeti.Geometry.Contact.Distribution
public import TauCeti.Geometry.Contact.Pullback
public import TauCeti.Geometry.Manifold.Diffeomorph.Basic
import TauCeti.Geometry.Manifold.IsManifold.Basic
import TauCeti.LinearAlgebra.BilinearForm.SymplecticBasis

/-!
# Isotropic and Legendrian maps into contact manifolds

Let `ξ` be a hyperplane field on a manifold `M`. A map `f : N → M` is **isotropic** for `ξ` when
every tangent image `df_y(T_y N)` lies in the hyperplane `ξ_(f y)`
(`TauCeti.IsIsotropicMap`). When `ξ` is a contact structure these maps parametrize the immersed
isotropic submanifolds; the source is an arbitrary charted space and `f` need not be injective,
so embedded and immersed submanifolds are treated alike. The differential is `mfderiv`, which is
`0` where `f` is not differentiable, so the predicate is meaningful for differentiable maps.

The Levi form `L_ξ(u, v) = -[U, V] mod ξ` of a `C¹` hyperplane field vanishes on the tangent
images of every `C²` isotropic map
(`TauCeti.IsIsotropicMap.distributionLeviForm_eq_zero`). The proof pulls back a local defining
form `α` of `ξ` near `f y`: since `f^* α` vanishes near `y`, so does `f^* dα = d(f^* α)`, and
`α` carries the Levi form to `dα` on `ξ`. Since the Levi form of a contact structure is a
nondegenerate alternating form with values in the line `TM ⧸ ξ`, a tangent image on which it
vanishes has at most half the dimension of `ξ`. So an isotropic map with injective differential
into a contact manifold of dimension `2 n + 1` has a source of dimension at most `n`
(`TauCeti.IsIsotropicMap.two_mul_finrank_add_one_le`). None of this uses a coorientation of `ξ`.

For a global one-form `α`, a smooth map is isotropic for `ker α` exactly when it pulls `α` back to
zero (`TauCeti.SmoothForm.isIsotropicMap_kerDistribution_iff_mpullback_eq_zero`), and then it
also pulls `dα` back to zero.

A **Legendrian immersion** (`TauCeti.IsLegendrianImmersion`) into a contact manifold of
dimension `2 n + 1` is a smooth isotropic immersion from a manifold of dimension `n`, the
largest dimension allowed. A **Legendrian embedding** (`TauCeti.IsLegendrianEmbedding`) is
moreover a topological embedding, so that it parametrizes an embedded Legendrian submanifold;
the image of a Legendrian immersion may have self-intersections.

## Main declarations

* `TauCeti.IsIsotropicMap`: maps whose tangent images lie in a distribution.
* `TauCeti.isIsotropicMap_comp_diffeomorph_iff`, `TauCeti.isIsotropicMap_diffeomorph_comp_iff`:
  independence of the parametrization and transport by diffeomorphisms preserving the
  distributions.
* `TauCeti.IsIsotropicMap.distributionLeviForm_eq_zero`: the Levi form vanishes on the tangent
  images of an isotropic map.
* `TauCeti.IsIsotropicMap.two_mul_finrank_add_one_le`: the dimension bound `2 dim N + 1 ≤ dim M`.
* `TauCeti.SmoothForm.isIsotropicMap_kerDistribution_iff_mpullback_eq_zero`: isotropy for the
  kernel of a one-form is the vanishing of the pulled-back form.
* `TauCeti.IsLegendrianImmersion`, `TauCeti.IsLegendrianEmbedding`: Legendrian immersions and
  embeddings.

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

/-! ### Isotropic maps -/

variable (J) in
/-- A map `f : N → M` is **isotropic** for a distribution `D` when every tangent image
`df_y(T_y N)` lies in `D (f y)`. For a contact structure `D` these are the parametrizations of
immersed isotropic submanifolds.

The tangent image is taken with `mfderiv`, which is `0` at points where `f` is not
differentiable, so there the condition holds trivially. -/
def IsIsotropicMap (D : Π x : M, Submodule ℝ (TangentSpace I x)) (f : N → M) : Prop :=
  ∀ y, LinearMap.range (mfderiv J I f y).toLinearMap ≤ D (f y)

/-- A map is isotropic exactly when its differential sends every tangent vector into the
distribution. -/
theorem isIsotropicMap_iff :
    IsIsotropicMap J D f ↔ ∀ y (v : TangentSpace J y), mfderiv J I f y v ∈ D (f y) := by
  simp only [IsIsotropicMap, LinearMap.range_le_iff_comap, Submodule.eq_top_iff',
    Submodule.mem_comap, ContinuousLinearMap.coe_coe]

/-- The differential of an isotropic map takes values in the distribution. -/
theorem IsIsotropicMap.mfderiv_mem (hf : IsIsotropicMap J D f) (y : N) (v : TangentSpace J y) :
    mfderiv J I f y v ∈ D (f y) :=
  isIsotropicMap_iff.1 hf y v

/-- A map into a smaller distribution is isotropic for a larger one. -/
theorem IsIsotropicMap.mono {D' : Π x : M, Submodule ℝ (TangentSpace I x)}
    (hf : IsIsotropicMap J D f) (hDD' : ∀ x, D x ≤ D' x) : IsIsotropicMap J D' f :=
  fun y ↦ (hf y).trans (hDD' (f y))

section Transport

variable {E'' H'' P : Type*} [NormedAddCommGroup E''] [NormedSpace ℝ E''] [TopologicalSpace H'']
  {K : ModelWithCorners ℝ E'' H''} [TopologicalSpace P] [ChartedSpace H'' P] {n : ℕ∞ω}

/-- **Independence of the parametrization.** Precomposing with a diffeomorphism of the source
does not change whether a map is isotropic. -/
theorem isIsotropicMap_comp_diffeomorph_iff (φ : P ≃ₘ^n⟮K, J⟯ N) (hn : n ≠ 0) :
    IsIsotropicMap K D (f ∘ φ) ↔ IsIsotropicMap J D f := by
  simp only [IsIsotropicMap, φ.range_mfderiv_comp_diffeomorph hn, Function.comp_apply]
  refine ⟨fun h y ↦ ?_, fun h x ↦ h (φ x)⟩
  obtain ⟨x, rfl⟩ := φ.surjective y
  exact h x

/-- **Transport by diffeomorphisms.** If the differential of a diffeomorphism `ψ : M → P` carries
the distribution `D` onto the distribution `D'`, then `ψ ∘ f` is isotropic for `D'` exactly when
`f` is isotropic for `D`. -/
theorem isIsotropicMap_diffeomorph_comp_iff {D' : Π z : P, Submodule ℝ (TangentSpace K z)}
    (ψ : M ≃ₘ^n⟮I, K⟯ P) (hn : n ≠ 0)
    (hψ : ∀ x (v : TangentSpace I x), v ∈ D x ↔ mfderiv I K ψ x v ∈ D' (ψ x)) :
    IsIsotropicMap J D' (ψ ∘ f) ↔ IsIsotropicMap J D f := by
  refine forall_congr' fun y ↦ ?_
  have hcoe (v : TangentSpace I (f y)) :
      (ψ.mfderivToContinuousLinearEquiv hn (f y)).toLinearEquiv.toLinearMap v =
        mfderiv I K ψ (f y) v :=
    congr($(ψ.mfderivToContinuousLinearEquiv_coe (x := f y) hn) v)
  rw [ψ.range_mfderiv_diffeomorph_comp hn, Function.comp_apply, Submodule.map_le_iff_le_comap]
  refine ⟨fun h v hv ↦ (hψ (f y) v).2 ?_, fun h v hv ↦ ?_⟩
  · simpa only [Submodule.mem_comap, hcoe] using h hv
  · simpa only [Submodule.mem_comap, hcoe] using (hψ (f y) v).1 (h hv)

end Transport

/-! ### The Levi form on tangent images -/

section Levi

variable [CompleteSpace E] [FiniteDimensional ℝ E] [IsManifold I 2 M] [IsManifold J 2 N]
  {n : ℕ∞ω} {k : ℕ}

/-- **The Levi form vanishes on isotropic tangent images.** Let `D` be a `C^n` hyperplane field,
with `1 ≤ n`, and let `f` be isotropic for `D` and of class `C²` at `y`. Then the Levi form
`L_D (u, v) = -[U, V] mod D` vanishes on any two vectors of the tangent image `df_y(T_y N)`. -/
theorem IsIsotropicMap.distributionLeviForm_eq_zero [IsManifold I (n + 1) M]
    (hD : IsContMDiffDistribution I n k D) (hk : k + 1 = finrank ℝ E) (hn : 1 ≤ n)
    (hf : IsIsotropicMap J D f) {y : N} (hfy : ContMDiffAt J I 2 f y) (v w : TangentSpace J y) :
    distributionLeviForm D (f y) ⟨mfderiv J I f y v, hf.mfderiv_mem y v⟩
      ⟨mfderiv J I f y w, hf.mfderiv_mem y w⟩ = 0 := by
  obtain ⟨U, hU, hyU, α, hα, hαD⟩ := hD.exists_roughForm_ker_eq hk (f y)
  have hαy : ContMDiffAt I (I.prod 𝓘(ℝ, E [⋀^Fin 1]→L[ℝ] ℝ)) 1
      (fun x ↦ TotalSpace.mk' (E [⋀^Fin 1]→L[ℝ] ℝ) x (α x)) (f y) :=
    ((hα _ hyU).contMDiffAt (hU.mem_nhds hyU)).of_le hn
  -- The pulled-back form `f^* α` vanishes near `y`, since `f` maps into `D = ker α` there.
  have hpull : ∀ᶠ y' in 𝓝 y, mpullback J I f α y' = 0 := by
    filter_upwards [hfy.continuousAt.preimage_mem_nhds (hU.mem_nhds hyU)] with y' hy'
    ext u
    rw [mpullback_apply, ContinuousAlternatingMap.coe_zero, Pi.zero_apply]
    have hu : (fun i ↦ mfderiv J I f y' (u i)) = ![mfderiv J I f y' (u 0)] := by
      ext i
      fin_cases i
      rfl
    rw [hu, ← RoughForm.mem_ker, (hαD _ hy').2]
    exact hf.mfderiv_mem y' (u 0)
  -- Hence `dα` vanishes on the tangent image at `y`.
  have hdα : mextDeriv α (f y) ![mfderiv J I f y v, mfderiv J I f y w] = 0 := by
    have h := congr($(mpullback_mextDeriv_at hfy hαy) ![v, w])
    rw [mextDeriv_congr_of_eventuallyEq (η := 0) hpull, mextDeriv_zero, Pi.zero_apply,
      ContinuousAlternatingMap.coe_zero, Pi.zero_apply, mpullback_apply] at h
    rw [← h]
    congr 1
    ext i
    fin_cases i <;> rfl
  -- The defining form carries the Levi form to `dα`, and is injective on `TM ⧸ D`.
  obtain ⟨V, hV, hyV, X, hX⟩ := isContMDiffDistribution_iff.1 hD (f y)
  obtain ⟨z, hz⟩ := (D (f y)).mkQ_surjective (distributionLeviForm D (f y)
    ⟨mfderiv J I f y v, hf.mfderiv_mem y v⟩ ⟨mfderiv J I f y w, hf.mfderiv_mem y w⟩)
  have hαz := RoughForm.apply_eq_mextDeriv_of_mkQ_eq_distributionLeviForm (hX.of_le hn)
    (hV.mem_nhds hyV) (hαy.mdifferentiableAt one_ne_zero)
    (eventually_of_mem (hU.mem_nhds hyU) fun x hx ↦ (hαD x hx).2.ge) hz
  rw [hdα, ← RoughForm.mem_ker, (hαD _ hyU).2] at hαz
  rw [← hz, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  exact hαz

/-- **Isotropic maps into a contact manifold have at most half the dimension of the contact
hyperplanes.** If `D` is a `C^n` contact structure, with `1 ≤ n`, on a manifold of dimension
`2 m + 1`, and `f` is isotropic for `D`, of class `C²` at `y` and with injective differential at
`y`, then `N` has dimension at most `m`: `2 dim N + 1 ≤ dim M`. -/
theorem IsIsotropicMap.two_mul_finrank_add_one_le [IsManifold I (n + 1) M]
    (hD : IsContactDistribution I n D) (hn : 1 ≤ n) (hf : IsIsotropicMap J D f) {y : N}
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
  have hle := LinearMap.two_mul_finrank_le_finrank_of_injective
    (hD.bijective_distributionLeviForm (f y)).injective (hD.finrank_quotient (f y)) hW
  have hWf : finrank ℝ W = finrank ℝ E' := by
    rw [LinearEquiv.finrank_eq (Submodule.comapSubtypeEquivOfLe (hf y)),
      LinearMap.finrank_range_of_inj hinj]
    exact finrank_tangentSpace y
  have := hD.finrank_add_one (f y)
  omega

end Levi

/-! ### Kernels of one-forms -/

namespace SmoothForm

variable [IsManifold I ∞ M] [IsManifold J ∞ N]

/-- **Isotropy is the vanishing of the pullback.** A smooth map is isotropic for the kernel of a
one-form `α` exactly when it pulls `α` back to zero. -/
theorem isIsotropicMap_kerDistribution_iff_mpullback_eq_zero
    (α : SmoothForm I M ℝ 1) (hf : ContMDiff J I ∞ f) :
    IsIsotropicMap J α.kerDistribution f ↔ mpullback f hf α = 0 := by
  have h (y : N) : (mpullback f hf α).1 y = 0 ↔
      LinearMap.range (mfderiv J I f y).toLinearMap ≤ α.kerDistribution (f y) := by
    have hker : (mpullback f hf α).kerDistribution y = RoughForm.ker (mpullback f hf α).1 y := by
      ext
      rw [mem_kerDistribution, RoughForm.mem_ker]
    rw [LinearMap.range_le_iff_comap, ← kerDistribution_mpullback f hf α y, hker,
      RoughForm.ker_eq_top_iff]
  simp only [IsIsotropicMap, ← h, Subtype.ext_iff, funext_iff, ZeroMemClass.coe_zero,
    Pi.zero_apply]

/-- A smooth isotropic map for the kernel of a one-form `α` also pulls back `dα` to zero. -/
theorem mpullback_mextDerivₗ_eq_zero_of_isIsotropicMap
    {α : SmoothForm I M ℝ 1} (hf : ContMDiff J I ∞ f)
    (hfα : IsIsotropicMap J α.kerDistribution f) :
    mpullback f hf (mextDerivₗ I 1 α) = 0 := by
  rw [← mextDerivₗ_mpullback, (isIsotropicMap_kerDistribution_iff_mpullback_eq_zero α hf).1 hfα,
    map_zero]

end SmoothForm

/-! ### Legendrian immersions and embeddings -/

variable [FiniteDimensional ℝ E]

variable (J) in
/-- A **Legendrian immersion** for a distribution `D` on a manifold of dimension `2 n + 1` is a
smooth immersion `f : N → M`, isotropic for `D`, from a manifold of dimension `n`. For a contact
structure `D` this is the largest dimension of an isotropic immersion
(`TauCeti.IsIsotropicMap.two_mul_finrank_add_one_le`). Its image may have self-intersections. -/
structure IsLegendrianImmersion (D : Π x : M, Submodule ℝ (TangentSpace I x)) (f : N → M) :
    Prop where
  /-- A Legendrian immersion is a smooth immersion. -/
  isImmersion : Manifold.IsImmersion J I ∞ f
  /-- A Legendrian immersion is tangent to the distribution. -/
  isIsotropicMap : IsIsotropicMap J D f
  /-- A Legendrian immersion has a source of dimension `n` in a manifold of dimension
  `2 n + 1`. -/
  two_mul_finrank_add_one : 2 * finrank ℝ E' + 1 = finrank ℝ E

variable (J) in
/-- A **Legendrian embedding** for a distribution `D` is a Legendrian immersion which is a
homeomorphism onto its image. It parametrizes an embedded Legendrian submanifold. -/
structure IsLegendrianEmbedding (D : Π x : M, Submodule ℝ (TangentSpace I x)) (f : N → M) : Prop
    extends IsLegendrianImmersion J D f where
  /-- A Legendrian embedding is a homeomorphism onto its image. -/
  isEmbedding : Topology.IsEmbedding f

omit [FiniteDimensional ℝ E] in
/-- A Legendrian embedding is a smooth embedding. -/
theorem IsLegendrianEmbedding.isSmoothEmbedding (h : IsLegendrianEmbedding J D f) :
    Manifold.IsSmoothEmbedding J I ∞ f :=
  ⟨h.isImmersion, h.isEmbedding⟩

omit [FiniteDimensional ℝ E] in
/-- A smooth embedding is a Legendrian embedding exactly when it is a Legendrian immersion. -/
theorem isLegendrianEmbedding_iff_of_isSmoothEmbedding (hf : Manifold.IsSmoothEmbedding J I ∞ f) :
    IsLegendrianEmbedding J D f ↔ IsLegendrianImmersion J D f :=
  ⟨fun h ↦ h.toIsLegendrianImmersion, fun h ↦ ⟨h, hf.isEmbedding⟩⟩

/-- A smooth isotropic immersion into a contact manifold of dimension `2 n + 1` from a nonempty
manifold is a Legendrian immersion exactly when its source has the largest possible dimension
`n`, equivalently when `2 dim N + 1 ≥ dim M`. -/
theorem isLegendrianImmersion_iff_finrank_le [CompleteSpace E] [IsManifold I 2 M]
    [IsManifold J 2 N] [Nonempty N] {n : ℕ∞ω} [IsManifold I (n + 1) M]
    (hD : IsContactDistribution I n D) (hn : 1 ≤ n) (hf : Manifold.IsImmersion J I ∞ f)
    (hfD : IsIsotropicMap J D f) :
    IsLegendrianImmersion J D f ↔ finrank ℝ E ≤ 2 * finrank ℝ E' + 1 := by
  refine ⟨fun h ↦ h.two_mul_finrank_add_one.ge, fun h ↦ ⟨hf, hfD, le_antisymm ?_ h⟩⟩
  obtain ⟨y⟩ := ‹Nonempty N›
  exact hfD.two_mul_finrank_add_one_le hD hn ((hf.contMDiff y).of_le (by simp))
    (hf.mfderiv_injective (by simp) y)

end TauCeti
