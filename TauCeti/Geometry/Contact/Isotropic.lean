/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Immersion
public import TauCeti.Geometry.Contact.Distribution
public import TauCeti.Geometry.Manifold.Diffeomorph.Basic
import TauCeti.Geometry.Manifold.DifferentialForm.DegreeOne
import TauCeti.Geometry.Manifold.DifferentialForm.Naturality
import TauCeti.Geometry.Manifold.Distribution.Annihilator
import TauCeti.Geometry.Manifold.IsManifold.Basic
import TauCeti.LinearAlgebra.BilinearForm.Orthogonal

/-!
# Isotropic and Legendrian maps into a contact manifold

Let `ξ` be a field of hyperplanes on a manifold `M`, for instance a contact structure
(`TauCeti.IsContactDistribution`). A map `f : N → M` is **isotropic**
(`TauCeti.IsIsotropicMap`) when it is tangent to `ξ`: every tangent image `df_y(T_y N)` lies in
the hyperplane `ξ_(f y)`. The source is an arbitrary charted space and `f` need not be injective,
so the predicate applies to embedded and immersed submanifolds alike, through any
parametrization. As for the symplectic tangent-image predicates of
`TauCeti.Geometry.Symplectic.Lagrangian.Manifold`, the differential is `mfderiv`, which is `0`
where `f` is not differentiable, so the predicate is only meaningful for differentiable maps.

The predicate depends only on the tangent images, hence not on the parametrization
(`TauCeti.isIsotropicMap_comp_diffeomorph_iff`), and a diffeomorphism carrying `ξ` to `ξ₂` carries
isotropic maps for `ξ` to isotropic maps for `ξ₂` (`TauCeti.isIsotropicMap_diffeomorph_comp_iff`).
When `ξ = ker α` for a one-form `α`, a map is isotropic exactly when it pulls `α` back to zero
(`TauCeti.RoughForm.isIsotropicMap_ker_iff`,
`TauCeti.SmoothForm.isIsotropicMap_kerDistribution_iff`).

**The Levi form vanishes on isotropic tangent images.** If `f` is isotropic for a `C¹`
hyperplane field `ξ` and `C²` at `y`, then the Levi form `L_ξ(u, v) = -[U, V] mod ξ` vanishes on
`df_y(T_y N)` (`TauCeti.IsIsotropicMap.distributionLeviForm_eq_zero`). The proof pulls back a local
defining form `α` of `ξ` near `f y`: since `f^*α = 0` near `y`, also `f^*dα = d(f^*α) = 0` at `y`
(`TauCeti.IsIsotropicMap.mextDeriv_mfderiv_eq_zero`), and `α` carries the Levi form to `dα`.

Since the Levi form of a contact structure is nondegenerate with values in the line `TM ⧸ ξ`, the
tangent image of an isotropic map with injective differential is an isotropic subspace of a
`2n`-dimensional space carrying a nondegenerate form. Hence an isotropic immersion into a contact
manifold of dimension `2n + 1` comes from a manifold of dimension at most `n`
(`TauCeti.IsIsotropicMap.two_mul_finrank_add_one_le`).

A **Legendrian immersion** (`TauCeti.IsLegendrianImmersion`) is a smooth isotropic immersion
attaining this bound, from a manifold of dimension `n`. It is a separate notion from an embedded
Legendrian submanifold: its image may have self-intersections. The basic examples, the one-jets of
functions in `J¹Q = T*Q × ℝ`, are in `TauCeti.Geometry.Contact.OneJet`.

## Main declarations

* `TauCeti.IsIsotropicMap`: maps tangent to a hyperplane field.
* `TauCeti.RoughForm.isIsotropicMap_ker_iff`: isotropy for the kernel of a one-form is the
  vanishing of the pulled-back form.
* `TauCeti.IsIsotropicMap.distributionLeviForm_eq_zero`: the Levi form vanishes on isotropic
  tangent images.
* `TauCeti.IsIsotropicMap.two_mul_finrank_add_one_le`: the dimension bound `2 dim N + 1 ≤ dim M`
  for isotropic immersions into contact manifolds.
* `TauCeti.IsLegendrianImmersion`: Legendrian immersions.

## References

* H. Geiges, *An Introduction to Contact Topology*, Cambridge Studies in Advanced Mathematics 109
  (2008): isotropic and Legendrian submanifolds and their dimension bound.
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

/-! ### The predicate -/

variable (J D) in
/-- A map `f : N → M` is **isotropic** for a field of hyperplanes `D` on `M`, typically a contact
structure, when it is tangent to `D`: every tangent image `df_y(T_y N)` lies in `D (f y)`.

The tangent image is taken with `mfderiv`, which is `0` at points where `f` is not
differentiable, so there the condition holds trivially. Isotropy is meaningful for differentiable
maps, and the statements about the Levi form assume `f` to be `C²`. -/
def IsIsotropicMap (f : N → M) : Prop :=
  ∀ y, LinearMap.range (mfderiv J I f y).toLinearMap ≤ D (f y)

/-- A map is isotropic exactly when its differential sends every tangent vector into the
hyperplane field. -/
theorem isIsotropicMap_iff : IsIsotropicMap J D f ↔ ∀ y v, mfderiv J I f y v ∈ D (f y) :=
  forall_congr' fun _ ↦ ⟨fun h v ↦ h ⟨v, rfl⟩, fun h _ ⟨v, hv⟩ ↦ hv ▸ h v⟩

/-- The differential of an isotropic map takes values in the hyperplane field. -/
theorem IsIsotropicMap.mfderiv_mem (h : IsIsotropicMap J D f) (y : N) (v : TangentSpace J y) :
    mfderiv J I f y v ∈ D (f y) :=
  isIsotropicMap_iff.1 h y v

/-! ### Reparametrization and transport -/

section Reparametrization

variable {E'' H'' : Type*} [NormedAddCommGroup E''] [NormedSpace ℝ E''] [TopologicalSpace H'']
  {K : ModelWithCorners ℝ E'' H''} {P : Type*} [TopologicalSpace P] [ChartedSpace H'' P]
  {n : ℕ∞ω}

/-- **Independence of the parametrization.** Precomposing with a diffeomorphism of the source
does not change whether a map is isotropic. -/
theorem isIsotropicMap_comp_diffeomorph_iff (φ : P ≃ₘ^n⟮K, J⟯ N) (hn : n ≠ 0) :
    IsIsotropicMap K D (f ∘ φ) ↔ IsIsotropicMap J D f := by
  simp only [IsIsotropicMap, φ.range_mfderiv_comp_diffeomorph hn, Function.comp_apply]
  refine ⟨fun h y ↦ ?_, fun h x ↦ h (φ x)⟩
  obtain ⟨x, rfl⟩ := φ.surjective y
  exact h x

end Reparametrization

section Transport

variable {E₂ H₂ : Type*} [NormedAddCommGroup E₂] [NormedSpace ℝ E₂] [TopologicalSpace H₂]
  {I₂ : ModelWithCorners ℝ E₂ H₂} {M₂ : Type*} [TopologicalSpace M₂] [ChartedSpace H₂ M₂]
  {D₂ : Π x : M₂, Submodule ℝ (TangentSpace I₂ x)} {n : ℕ∞ω}

/-- **Transport by contactomorphisms.** If a diffeomorphism `ψ` pulls the hyperplane field `D₂`
back to `D`, in the sense that `D x` is the inverse image of `D₂ (ψ x)` under `dψ_x`, then
`ψ ∘ f` is isotropic for `D₂` exactly when `f` is isotropic for `D`. -/
theorem isIsotropicMap_diffeomorph_comp_iff (ψ : M ≃ₘ^n⟮I, I₂⟯ M₂) (hn : n ≠ 0)
    (hψ : ∀ x, D x = (D₂ (ψ x)).comap (mfderiv I I₂ ψ x).toLinearMap) :
    IsIsotropicMap J D₂ (ψ ∘ f) ↔ IsIsotropicMap J D f := by
  refine forall_congr' fun y ↦ ?_
  have he : (ψ.mfderivToContinuousLinearEquiv hn (f y)).toLinearEquiv.toLinearMap =
      (mfderiv I I₂ ψ (f y)).toLinearMap :=
    congrArg ContinuousLinearMap.toLinearMap (ψ.mfderivToContinuousLinearEquiv_coe hn)
  rw [ψ.range_mfderiv_diffeomorph_comp hn, Submodule.map_le_iff_le_comap, he,
    Function.comp_apply, hψ]

end Transport

/-! ### Kernels of one-forms -/

/-- **Isotropy is the vanishing of the pullback.** A map is isotropic for the kernel of a one-form
`α` exactly when it pulls `α` back to zero. -/
theorem RoughForm.isIsotropicMap_ker_iff {α : RoughForm I M ℝ 1} :
    IsIsotropicMap J α.ker f ↔ mpullback J I f α = 0 := by
  rw [isIsotropicMap_iff]
  refine ⟨fun h ↦ funext fun y ↦ mpullback_eq_zero_of_mfderiv_mem_ker (h y), fun h y v ↦ ?_⟩
  have hv := congr($h y ![v])
  rw [mpullback_apply] at hv
  refine RoughForm.mem_ker.2 ?_
  convert hv using 2
  ext i
  fin_cases i
  rfl

/-- **Isotropy is the vanishing of the pullback.** A map is isotropic for the kernel of a smooth
one-form `α` exactly when it pulls `α` back to zero. -/
theorem SmoothForm.isIsotropicMap_kerDistribution_iff [IsManifold I ∞ M]
    {α : SmoothForm I M ℝ 1} :
    IsIsotropicMap J α.kerDistribution f ↔ mpullback J I f α.1 = 0 := by
  have hker : α.kerDistribution = RoughForm.ker α.1 := funext fun x ↦ by
    ext
    rw [mem_kerDistribution, RoughForm.mem_ker]
  rw [hker, RoughForm.isIsotropicMap_ker_iff]

/-! ### The Levi form on isotropic tangent images -/

section Levi

variable [IsManifold I 2 M] [IsManifold J 2 N]

/-- **Isotropic maps pull back the derivative of a defining form to zero.** Let `f` be isotropic
for `D` and `C²` at `y`, and let the one-form `α` be `C¹` at `f y` and vanish on `D` near `f y`.
Then `dα_(f y)` vanishes on the tangent image of `f` at `y`, since `f^*α = 0` near `y` and so
`f^*dα = d(f^*α) = 0` at `y`. -/
theorem IsIsotropicMap.mextDeriv_mfderiv_eq_zero (hfD : IsIsotropicMap J D f) {y : N}
    (hf : ContMDiffAt J I 2 f y) {α : RoughForm I M ℝ 1}
    (hα : ContMDiffAt I (I.prod 𝓘(ℝ, E [⋀^Fin 1]→L[ℝ] ℝ)) 1
      (fun x ↦ TotalSpace.mk' (E [⋀^Fin 1]→L[ℝ] ℝ) x (α x)) (f y))
    (hDα : ∀ᶠ x in 𝓝 (f y), D x ≤ α.ker x) (v w : TangentSpace J y) :
    mextDeriv α (f y) ![mfderiv J I f y v, mfderiv J I f y w] = 0 := by
  have : IsManifold I 1 M := IsManifold.of_le (n := 2) one_le_two
  have : IsManifold J 1 N := IsManifold.of_le (n := 2) one_le_two
  -- Near `y`, the map `f` lands where `α` vanishes on `D`, so `f^*α` vanishes there.
  have hpull : ∀ᶠ z in 𝓝 y, mpullback J I f α z = (0 : RoughForm J N ℝ 1) z := by
    filter_upwards [hf.continuousAt.preimage_mem_nhds hDα] with z hz
    exact mpullback_eq_zero_of_mfderiv_mem_ker fun v ↦ hz (hfD.mfderiv_mem z v)
  -- Hence `f^*dα = d(f^*α)` vanishes at `y`.
  have hd : mpullback J I f (mextDeriv α) y = 0 := by
    rw [mpullback_mextDeriv_at hf hα, mextDeriv_congr_of_eventuallyEq hpull, mextDeriv_zero]
    rfl
  have h := congr($hd ![v, w])
  rw [mpullback_apply] at h
  convert h using 2
  ext i
  fin_cases i <;> rfl

/-- **The Levi form vanishes on isotropic tangent images.** Let `D` be a `C¹` field of
hyperplanes, of rank `k` with `k + 1 = dim M`, and let `f` be isotropic for `D` and `C²` at `y`.
Then the Levi form `L_D(u, v) = -[U, V] mod D` vanishes on the tangent image `df_y(T_y N)`. -/
theorem IsIsotropicMap.distributionLeviForm_eq_zero [CompleteSpace E] [FiniteDimensional ℝ E]
    {k : ℕ} (hD : IsContMDiffDistribution I 1 k D) (hk : k + 1 = finrank ℝ E)
    (hfD : IsIsotropicMap J D f) {y : N} (hf : ContMDiffAt J I 2 f y) (v w : TangentSpace J y) :
    distributionLeviForm D (f y) ⟨mfderiv J I f y v, hfD.mfderiv_mem y v⟩
      ⟨mfderiv J I f y w, hfD.mfderiv_mem y w⟩ = 0 := by
  have : IsManifold I 1 M := IsManifold.of_le (n := 2) one_le_two
  have : IsManifold I (1 + 1) M := IsManifold.of_le (n := 2) le_rfl
  -- A local defining covector field `a` of `D` near `f y`, read as a one-form `α`.
  obtain ⟨U, a, hU, hyU, ha, haD⟩ := hD.exists_local_annihilator hk (f y)
  let α : RoughForm I M ℝ 1 :=
    fun x ↦ ContinuousAlternatingMap.ofSubsingleton ℝ (TangentSpace I x) ℝ (0 : Fin 1) (a x)
  have hker (x : M) (hx : x ∈ U) : α.ker x = D x := by
    ext u
    rw [← (haD x hx).2, RoughForm.mem_ker]
    simp [α]
  have hα : ContMDiffAt I (I.prod 𝓘(ℝ, E [⋀^Fin 1]→L[ℝ] ℝ)) 1
      (fun x ↦ TotalSpace.mk' (E [⋀^Fin 1]→L[ℝ] ℝ) x (α x)) (f y) :=
    (contMDiffAt_ofSubsingleton_iff (V := Bundle.Trivial M ℝ)).2
      ((ha (f y) hyU).contMDiffAt (hU.mem_nhds hyU))
  have hDα : ∀ᶠ x in 𝓝 (f y), D x ≤ α.ker x :=
    eventually_of_mem (hU.mem_nhds hyU) fun x hx ↦ (hker x hx).ge
  -- `α` carries the Levi form to `dα`, which vanishes on the tangent image.
  obtain ⟨V, hV, hyV, X, hX⟩ := isContMDiffDistribution_iff.1 hD (f y)
  obtain ⟨u, hu⟩ := (D (f y)).mkQ_surjective (distributionLeviForm D (f y)
    ⟨mfderiv J I f y v, hfD.mfderiv_mem y v⟩ ⟨mfderiv J I f y w, hfD.mfderiv_mem y w⟩)
  have h := RoughForm.apply_eq_mextDeriv_of_mkQ_eq_distributionLeviForm hX (hV.mem_nhds hyV)
    (hα.mdifferentiableAt one_ne_zero) hDα hu
  rw [← hu, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, ← hker _ hyU]
  exact RoughForm.mem_ker.2 (h.trans (hfD.mextDeriv_mfderiv_eq_zero hf hα hDα v w))

/-- **Dimension bound for isotropic immersions.** An isotropic map into a contact manifold of
dimension `2n + 1`, which is `C²` with injective differential at some point, comes from a
manifold of dimension at most `n`: `2 dim N + 1 ≤ dim M`. -/
theorem IsIsotropicMap.two_mul_finrank_add_one_le [CompleteSpace E] [FiniteDimensional ℝ E]
    {n : ℕ∞ω} (hD : IsContactDistribution I n D) (hn : 1 ≤ n) (hfD : IsIsotropicMap J D f)
    {y : N} (hf : ContMDiffAt J I 2 f y) (hinj : Injective (mfderiv J I f y)) :
    2 * finrank ℝ E' + 1 ≤ finrank ℝ E := by
  have : FiniteDimensional ℝ (TangentSpace I (f y)) := inferInstanceAs (FiniteDimensional ℝ E)
  have hrank := hD.finrank_add_one (f y)
  have hk : (finrank ℝ E - 1) + 1 = finrank ℝ E := by omega
  -- The differential at `y`, with values in the contact hyperplane.
  let g : TangentSpace J y →ₗ[ℝ] D (f y) :=
    (mfderiv J I f y).toLinearMap.codRestrict (D (f y)) (hfD.mfderiv_mem y)
  have hg : Injective g := fun v w h ↦ hinj (congrArg Subtype.val h)
  -- Its range is isotropic for the Levi form, which is nondegenerate with values in a line.
  have hW := LinearMap.two_mul_finrank_le_of_injective
    (hD.bijective_distributionLeviForm (f y)).injective (hD.finrank_quotient (f y))
    (W := LinearMap.range g) <| by
      rintro _ ⟨v, rfl⟩ _ ⟨w, rfl⟩
      exact hfD.distributionLeviForm_eq_zero (hD.isContMDiffDistribution.of_le hn) hk hf v w
  rw [LinearMap.finrank_range_of_inj hg, finrank_tangentSpace (I := J) y] at hW
  omega

end Levi

/-! ### Legendrian immersions -/

variable (J D) in
/-- A **Legendrian immersion** for a field of hyperplanes `D` on a manifold `M` of dimension
`2n + 1`, typically a contact structure, is a smooth immersion `f : N → M` tangent to `D` from a
manifold of dimension `n`. For a contact structure this is the largest dimension of an isotropic
immersion (`TauCeti.isLegendrianImmersion_iff_finrank_le`). Its image may have
self-intersections. -/
structure IsLegendrianImmersion (f : N → M) : Prop where
  /-- A Legendrian immersion is a smooth immersion. -/
  isImmersion : IsImmersion J I ∞ f
  /-- A Legendrian immersion is tangent to the hyperplane field. -/
  isIsotropicMap : IsIsotropicMap J D f
  /-- A Legendrian immersion into a manifold of dimension `2n + 1` comes from a manifold of
  dimension `n`. -/
  two_mul_finrank_add_one : 2 * finrank ℝ E' + 1 = finrank ℝ E

/-- **Legendrian immersions are the isotropic immersions of maximal dimension.** An isotropic
immersion from a nonempty manifold into a contact manifold of dimension `2n + 1` is Legendrian
exactly when its source has dimension at least `n`. -/
theorem isLegendrianImmersion_iff_finrank_le [CompleteSpace E] [FiniteDimensional ℝ E]
    [IsManifold I 2 M] [IsManifold J 2 N] [Nonempty N] {n : ℕ∞ω}
    (hD : IsContactDistribution I n D) (hn : 1 ≤ n) :
    IsLegendrianImmersion J D f ↔
      IsImmersion J I ∞ f ∧ IsIsotropicMap J D f ∧ finrank ℝ E ≤ 2 * finrank ℝ E' + 1 := by
  refine ⟨fun h ↦ ⟨h.isImmersion, h.isIsotropicMap, h.two_mul_finrank_add_one.ge⟩,
    fun ⟨himm, hfD, hle⟩ ↦ ⟨himm, hfD, le_antisymm ?_ hle⟩⟩
  obtain ⟨y⟩ := ‹Nonempty N›
  exact hfD.two_mul_finrank_add_one_le hD hn (himm.contMDiff.of_le (by simp) y)
    (himm.mfderiv_injective (by simp) y)

end TauCeti
