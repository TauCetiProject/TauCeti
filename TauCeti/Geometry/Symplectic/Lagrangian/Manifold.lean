/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Immersion
public import TauCeti.Geometry.Manifold.Diffeomorph.Basic
public import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.Smooth
public import TauCeti.Geometry.Manifold.IsManifold.Basic
public import TauCeti.Geometry.Symplectic.Lagrangian.Constructions
public import TauCeti.Geometry.Symplectic.Manifold.TwoForm

/-!
# Isotropic, coisotropic and Lagrangian maps into a symplectic manifold

Let `σ` be a fiberwise nondegenerate smooth two-form on `M`, so that every tangent space
`T_y M` carries the linear symplectic form `hσ.symplecticFormAt y`. A map `f : N → M` is
**isotropic**, **coisotropic** or **Lagrangian** when, at every point `x` of `N`, its tangent
image `df_x(T_x N)`, the range of the differential, is an isotropic, coisotropic or Lagrangian
subspace of `T_(f x) M` in the sense of `TauCeti.SymplecticForm.IsIsotropic` and its siblings.
The differential is `mfderiv`, which is `0` where `f` is not differentiable; there the tangent
image is zero, which is isotropic, so the predicates are only meaningful for differentiable maps.
The source is an arbitrary charted space and `f` need not be injective, so these predicates apply
to embedded and immersed submanifolds alike, through any parametrization.

The predicates are invariant under the natural operations:

* they depend only on the tangent images, hence not on the parametrization: precomposing `f` with
  a diffeomorphism of the source does not change them;
* a diffeomorphism `ψ : M → M₂` pulling a nondegenerate two-form `σ₂` back to `σ` carries
  isotropic, coisotropic and Lagrangian maps for `σ` to those for `σ₂`, and conversely.

A smooth map is isotropic exactly when it pulls `σ` back to zero
(`TauCeti.SmoothTwoForm.IsNondegenerate.isIsotropicMap_iff_mpullback_eq_zero`), which is the
form in which isotropy of graphs and sections is usually checked.

When `M` is finite-dimensional and the differential is injective at some point of `N` (so `N`
is nonempty), the linear dimension bounds give `2 dim N ≤ dim M` for isotropic maps and
`2 dim N = dim M` for Lagrangian ones, and an isotropic immersion from a manifold of half the
dimension is Lagrangian. Every map from a manifold of dimension at most one is isotropic
(`TauCeti.SmoothTwoForm.IsNondegenerate.isIsotropicMap_of_finrank_le_one`). When `M` and `N` are
finite-dimensional, a coisotropic map from a
nonempty `N` satisfies `dim M ≤ 2 dim N` without any injectivity. From an empty source every
map satisfies all three predicates vacuously, and no dimension constraint follows.

A **Lagrangian immersion** (`TauCeti.SmoothTwoForm.IsNondegenerate.IsLagrangianImmersion`)
into a finite-dimensional manifold is a smooth immersion with isotropic tangent images from a
manifold of half the dimension; when the source is nonempty, it is equivalently an immersion
which is a Lagrangian map (`TauCeti.SmoothTwoForm.IsNondegenerate.isLagrangianImmersion_iff`).
It is a separate notion from an embedded Lagrangian submanifold: its image may have
self-intersections. Every immersion of a curve into a surface is one
(`TauCeti.SmoothTwoForm.IsNondegenerate.isLagrangianImmersion_of_finrank_eq_one`).

The linear facts about a subspace `W` of a symplectic vector space and its symplectic complement
`W^σ` hold for tangent images `W = df_x(T_x N)`, read in `(T_(f x) M, σ_(f x))`: when `M` is
finite-dimensional, `W^σσ = W`, and `dim N + dim W^σ = dim M` if moreover `df_x` is injective; in
any dimension `W` is Lagrangian exactly when it is maximal isotropic, so that `f` is a Lagrangian
map exactly when its tangent images are maximal isotropic
(`TauCeti.SmoothTwoForm.IsNondegenerate.isLagrangianMap_iff_forall_maximal_isIsotropic`).

The basic example: in a finite-dimensional symplectic vector space with its constant symplectic
form, a continuous linear map is a Lagrangian map exactly when its range is a Lagrangian subspace
(`TauCeti.SymplecticForm.isLagrangianMap_continuousLinearMap_iff`). A linear symplectomorphism
of symplectic vector spaces pulls their constant forms back to each other
(`TauCeti.SymplecticForm.IsSymplectomorphism.mpullback_constSmooth`), so composing with it
preserves isotropic and Lagrangian maps
(`TauCeti.SymplecticForm.IsSymplectomorphism.isLagrangianMap_comp_iff`).

## Main declarations

* `TauCeti.SmoothTwoForm.IsNondegenerate.mem_of_forall_eval₂_eq_zero_of_isCoisotropic`: a vector
  `σ`-orthogonal to a coisotropic subspace `W ⊆ T_x M` lies in `W`.
* `TauCeti.SmoothTwoForm.IsNondegenerate.IsIsotropicMap`, `IsCoisotropicMap`, `IsLagrangianMap`:
  the three tangent-image predicates.
* `TauCeti.SmoothTwoForm.IsNondegenerate.isIsotropicMap_iff_mpullback_eq_zero`: isotropy is the
  vanishing of the pulled-back form.
* `TauCeti.SmoothTwoForm.IsNondegenerate.isLagrangianMap_comp_diffeomorph_iff`: independence of
  the parametrization.
* `TauCeti.SmoothTwoForm.IsNondegenerate.isLagrangianMap_diffeomorph_comp_iff`: transport by
  symplectomorphisms.
* `TauCeti.SmoothTwoForm.IsNondegenerate.IsLagrangianMap.two_mul_finrank`: the dimension count.
* `TauCeti.SmoothTwoForm.IsNondegenerate.finrank_add_finrank_orthogonal_range_mfderiv`,
  `TauCeti.SmoothTwoForm.IsNondegenerate.orthogonal_orthogonal_range_mfderiv` and
  `TauCeti.SmoothTwoForm.IsNondegenerate.isLagrangian_range_mfderiv_iff_maximal_isIsotropic`: the
  linear symplectic facts for a tangent image `W = df_x(T_x N)`: for finite-dimensional `M`,
  `dim N + dim W^σ = dim M` when `df_x` is injective and `W^σσ = W`; and `W` is Lagrangian exactly
  when it is maximal isotropic.
* `TauCeti.SmoothTwoForm.IsNondegenerate.IsLagrangianImmersion` and
  `TauCeti.SmoothTwoForm.IsNondegenerate.isLagrangianImmersion_iff`: Lagrangian immersions.
* `TauCeti.SmoothTwoForm.IsNondegenerate.isLagrangianImmersion_of_finrank_eq_one`: immersed curves
  in a surface are Lagrangian immersions.
* `TauCeti.SymplecticForm.IsSymplectomorphism.isLagrangianMap_comp_iff`: composing with a linear
  symplectomorphism of symplectic vector spaces preserves Lagrangian maps.

## References

* A. Cannas da Silva, *Lectures on Symplectic Geometry*, Lecture Notes in Mathematics 1764,
  Springer, 2001, Section 3.
* D. McDuff, D. Salamon, *Introduction to Symplectic Topology*, 3rd ed., Oxford, 2017,
  Sections 2.3 and 3.4.
-/

public section

noncomputable section

open Module Manifold
open scoped Manifold ContDiff

namespace TauCeti

namespace SmoothTwoForm

namespace IsNondegenerate

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M]
  {E' H' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  {J : ModelWithCorners ℝ E' H'} {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]
  {σ : SmoothTwoForm I M} (hσ : σ.IsNondegenerate) {f : N → M}

/-! ### Coisotropic subspaces of a tangent space -/

/-- A tangent vector `σ`-orthogonal to a coisotropic subspace `W` of `T_x M` lies in `W`. -/
theorem mem_of_forall_eval₂_eq_zero_of_isCoisotropic {x : M}
    {W : Submodule ℝ (TangentSpace I x)} (hW : (hσ.symplecticFormAt x).IsCoisotropic W)
    {v : TangentSpace I x} (hv : ∀ w ∈ W, SmoothBundleForm.eval₂ σ x v w = 0) : v ∈ W := by
  refine SymplecticForm.isCoisotropic_iff_le.1 hW ?_
  rw [SymplecticForm.mem_orthogonal_iff']
  intro w hw
  rw [symplecticFormAt_apply]
  exact hv w hw

/-! ### The three predicates -/

variable (J)

/-- A map `f : N → M` is **isotropic** for a nondegenerate two-form `σ` when every tangent image
`df_x(T_x N)` is an isotropic subspace of `(T_(f x) M, σ_(f x))`.

The tangent image is taken with `mfderiv`, which is `0` at points where `f` is not
differentiable, so there the condition holds trivially: a nowhere-differentiable map counts as
isotropic. Isotropy is meaningful for differentiable maps, and the statements relating it to the
pulled-back form assume `f` smooth. -/
def IsIsotropicMap (f : N → M) : Prop :=
  ∀ x, (hσ.symplecticFormAt (f x)).IsIsotropic (LinearMap.range (mfderiv J I f x).toLinearMap)

/-- A map `f : N → M` is **coisotropic** for a nondegenerate two-form `σ` when every tangent
image `df_x(T_x N)` is a coisotropic subspace of `(T_(f x) M, σ_(f x))`. -/
def IsCoisotropicMap (f : N → M) : Prop :=
  ∀ x, (hσ.symplecticFormAt (f x)).IsCoisotropic (LinearMap.range (mfderiv J I f x).toLinearMap)

/-- A map `f : N → M` is **Lagrangian** for a nondegenerate two-form `σ` when every tangent image
`df_x(T_x N)` is a Lagrangian subspace of `(T_(f x) M, σ_(f x))`. -/
def IsLagrangianMap (f : N → M) : Prop :=
  ∀ x, (hσ.symplecticFormAt (f x)).IsLagrangian (LinearMap.range (mfderiv J I f x).toLinearMap)

variable {J hσ}

/-- Isotropy of a map is pointwise isotropy of its tangent images. -/
theorem isIsotropicMap_iff_forall :
    hσ.IsIsotropicMap J f ↔
      ∀ x, (hσ.symplecticFormAt (f x)).IsIsotropic
        (LinearMap.range (mfderiv J I f x).toLinearMap) :=
  Iff.rfl

/-- Coisotropy of a map is pointwise coisotropy of its tangent images. -/
theorem isCoisotropicMap_iff :
    hσ.IsCoisotropicMap J f ↔
      ∀ x, (hσ.symplecticFormAt (f x)).IsCoisotropic
        (LinearMap.range (mfderiv J I f x).toLinearMap) :=
  Iff.rfl

/-- The Lagrangian condition on a map is the pointwise condition on its tangent images. -/
theorem isLagrangianMap_iff_forall :
    hσ.IsLagrangianMap J f ↔
      ∀ x, (hσ.symplecticFormAt (f x)).IsLagrangian
        (LinearMap.range (mfderiv J I f x).toLinearMap) :=
  Iff.rfl

/-- Isotropy of a map is the vanishing of `σ` on pairs of pushed-forward tangent vectors. -/
theorem isIsotropicMap_iff :
    hσ.IsIsotropicMap J f ↔
      ∀ x (v w : TangentSpace J x),
        SmoothBundleForm.eval₂ σ (f x)
            (mfderiv J I f x v) (mfderiv J I f x w) = 0 := by
  refine forall_congr' fun x ↦ ?_
  simp only [SymplecticForm.isIsotropic_iff, LinearMap.mem_range, forall_exists_index,
    forall_apply_eq_imp_iff, symplecticFormAt_apply, ContinuousLinearMap.coe_coe]

/-- A Lagrangian map is both isotropic and coisotropic, and conversely. -/
theorem isLagrangianMap_iff :
    hσ.IsLagrangianMap J f ↔ hσ.IsIsotropicMap J f ∧ hσ.IsCoisotropicMap J f := by
  simp only [IsLagrangianMap, IsIsotropicMap, IsCoisotropicMap, SymplecticForm.isLagrangian_iff,
    forall_and]

/-- A Lagrangian map is isotropic. -/
theorem IsLagrangianMap.isIsotropicMap (h : hσ.IsLagrangianMap J f) : hσ.IsIsotropicMap J f :=
  (isLagrangianMap_iff.mp h).1

/-- A Lagrangian map is coisotropic. -/
theorem IsLagrangianMap.isCoisotropicMap (h : hσ.IsLagrangianMap J f) : hσ.IsCoisotropicMap J f :=
  (isLagrangianMap_iff.mp h).2

/-- A tangent vector at `f x` which is `σ`-orthogonal to the tangent image of a coisotropic map `f`
lies in that tangent image. -/
theorem IsCoisotropicMap.exists_mfderiv_eq_of_forall_eval₂_mfderiv_eq_zero
    (h : hσ.IsCoisotropicMap J f) (x : N) {v : TangentSpace I (f x)}
    (hv : ∀ u, SmoothBundleForm.eval₂ σ (f x) v (mfderiv J I f x u) = 0) :
    ∃ u, mfderiv J I f x u = v :=
  LinearMap.mem_range.1 (hσ.mem_of_forall_eval₂_eq_zero_of_isCoisotropic (h x) fun w hw ↦ by
    obtain ⟨u, rfl⟩ := LinearMap.mem_range.1 hw
    exact hv u)

/-- **Isotropy is the vanishing of the pullback.** A smooth map is isotropic exactly when it pulls
the two-form back to zero. -/
theorem isIsotropicMap_iff_mpullback_eq_zero [IsManifold J ∞ N] (hf : ContMDiff J I ∞ f) :
    hσ.IsIsotropicMap J f ↔ SmoothForm.mpullback f hf σ = 0 := by
  rw [isIsotropicMap_iff, SmoothBundleForm.ext_eval₂_iff]
  simp only [SmoothForm.eval₂_mpullback]
  simp

/-! ### Reparametrization -/

section Reparametrization

variable {E'' H'' : Type*} [NormedAddCommGroup E''] [NormedSpace ℝ E''] [TopologicalSpace H'']
  {K : ModelWithCorners ℝ E'' H''} {P : Type*} [TopologicalSpace P] [ChartedSpace H'' P]
  {n : ℕ∞ω}

/-- Precomposing with a diffeomorphism of the source does not change isotropy. -/
theorem isIsotropicMap_comp_diffeomorph_iff (φ : P ≃ₘ^n⟮K, J⟯ N) (hn : n ≠ 0) :
    hσ.IsIsotropicMap K (f ∘ φ) ↔ hσ.IsIsotropicMap J f := by
  simp only [IsIsotropicMap, φ.range_mfderiv_comp_diffeomorph hn, Function.comp_apply]
  refine ⟨fun h y ↦ ?_, fun h x ↦ h (φ x)⟩
  obtain ⟨x, rfl⟩ := φ.surjective y
  exact h x

/-- Precomposing with a diffeomorphism of the source does not change coisotropy. -/
theorem isCoisotropicMap_comp_diffeomorph_iff (φ : P ≃ₘ^n⟮K, J⟯ N) (hn : n ≠ 0) :
    hσ.IsCoisotropicMap K (f ∘ φ) ↔ hσ.IsCoisotropicMap J f := by
  simp only [IsCoisotropicMap, φ.range_mfderiv_comp_diffeomorph hn, Function.comp_apply]
  refine ⟨fun h y ↦ ?_, fun h x ↦ h (φ x)⟩
  obtain ⟨x, rfl⟩ := φ.surjective y
  exact h x

/-- **Independence of the parametrization.** Precomposing with a diffeomorphism of the source
does not change whether a map is Lagrangian. -/
theorem isLagrangianMap_comp_diffeomorph_iff (φ : P ≃ₘ^n⟮K, J⟯ N) (hn : n ≠ 0) :
    hσ.IsLagrangianMap K (f ∘ φ) ↔ hσ.IsLagrangianMap J f := by
  simp only [IsLagrangianMap, φ.range_mfderiv_comp_diffeomorph hn, Function.comp_apply]
  refine ⟨fun h y ↦ ?_, fun h x ↦ h (φ x)⟩
  obtain ⟨x, rfl⟩ := φ.surjective y
  exact h x

end Reparametrization

/-! ### Transport by symplectomorphisms -/

section Transport

variable {E₂ H₂ : Type*} [NormedAddCommGroup E₂] [NormedSpace ℝ E₂] [TopologicalSpace H₂]
  {I₂ : ModelWithCorners ℝ E₂ H₂} {M₂ : Type*} [TopologicalSpace M₂] [ChartedSpace H₂ M₂]
  [IsManifold I₂ ∞ M₂] {σ₂ : SmoothTwoForm I₂ M₂} {hσ₂ : σ₂.IsNondegenerate}

/-- A symplectomorphism preserves isotropic maps: if `ψ` pulls `σ₂` back to `σ`, then `ψ ∘ f` is
isotropic for `σ₂` exactly when `f` is isotropic for `σ`. -/
theorem isIsotropicMap_diffeomorph_comp_iff (ψ : M ≃ₘ⟮I, I₂⟯ M₂)
    (hψ : SmoothForm.mpullback ψ ψ.contMDiff σ₂ = σ) :
    hσ₂.IsIsotropicMap J (ψ ∘ f) ↔ hσ.IsIsotropicMap J f := by
  refine forall_congr' fun x ↦ ?_
  rw [ψ.range_mfderiv_diffeomorph_comp (by simp), Function.comp_apply,
    ← hσ.symplecticFormAt_transport ψ hψ, SymplecticForm.isIsotropic_map_transport_iff]

/-- A symplectomorphism preserves coisotropic maps: if `ψ` pulls `σ₂` back to `σ`, then `ψ ∘ f`
is coisotropic for `σ₂` exactly when `f` is coisotropic for `σ`. -/
theorem isCoisotropicMap_diffeomorph_comp_iff (ψ : M ≃ₘ⟮I, I₂⟯ M₂)
    (hψ : SmoothForm.mpullback ψ ψ.contMDiff σ₂ = σ) :
    hσ₂.IsCoisotropicMap J (ψ ∘ f) ↔ hσ.IsCoisotropicMap J f := by
  refine forall_congr' fun x ↦ ?_
  rw [ψ.range_mfderiv_diffeomorph_comp (by simp), Function.comp_apply,
    ← hσ.symplecticFormAt_transport ψ hψ, SymplecticForm.isCoisotropic_map_transport_iff]

/-- **Transport by symplectomorphisms.** If `ψ` pulls `σ₂` back to `σ`, then `ψ ∘ f` is Lagrangian
for `σ₂` exactly when `f` is Lagrangian for `σ`. -/
theorem isLagrangianMap_diffeomorph_comp_iff (ψ : M ≃ₘ⟮I, I₂⟯ M₂)
    (hψ : SmoothForm.mpullback ψ ψ.contMDiff σ₂ = σ) :
    hσ₂.IsLagrangianMap J (ψ ∘ f) ↔ hσ.IsLagrangianMap J f := by
  refine forall_congr' fun x ↦ ?_
  rw [ψ.range_mfderiv_diffeomorph_comp (by simp), Function.comp_apply,
    ← hσ.symplecticFormAt_transport ψ hψ, SymplecticForm.isLagrangian_map_transport_iff]

end Transport

/-! ### Dimension counts -/

section Dimension

variable [FiniteDimensional ℝ E]

/-- An isotropic map with injective differential at some point comes from a manifold of at most
half the dimension: `2 dim N ≤ dim M`. -/
theorem IsIsotropicMap.two_mul_finrank_le (h : hσ.IsIsotropicMap J f) {x : N}
    (hx : Function.Injective (mfderiv J I f x)) : 2 * finrank ℝ E' ≤ finrank ℝ E := by
  have := (h x).two_mul_finrank_le
  rwa [LinearMap.finrank_range_of_inj hx, finrank_tangentSpace, finrank_tangentSpace] at this

/-- A Lagrangian map with injective differential at some point comes from a manifold of exactly
half the dimension: `2 dim N = dim M`. -/
theorem IsLagrangianMap.two_mul_finrank (h : hσ.IsLagrangianMap J f) {x : N}
    (hx : Function.Injective (mfderiv J I f x)) : 2 * finrank ℝ E' = finrank ℝ E := by
  have := (h x).two_mul_finrank
  rwa [LinearMap.finrank_range_of_inj hx, finrank_tangentSpace, finrank_tangentSpace] at this

omit [FiniteDimensional ℝ E] in
/-- A coisotropic map from a nonempty manifold, witnessed by a point `x`, comes from a manifold of
at least half the dimension: `dim M ≤ 2 dim N`. No injectivity of the differential is needed. -/
theorem IsCoisotropicMap.finrank_le_two_mul_finrank [FiniteDimensional ℝ E']
    (h : hσ.IsCoisotropicMap J f) (x : N) : finrank ℝ E ≤ 2 * finrank ℝ E' := by
  have := (h x).finrank_le_two_mul_finrank
  rw [finrank_tangentSpace] at this
  have hle := LinearMap.finrank_range_le (mfderiv J I f x).toLinearMap
  rw [finrank_tangentSpace] at hle
  omega

/-- An isotropic map with injective differentials from a manifold of half the dimension is
Lagrangian. -/
theorem IsIsotropicMap.isLagrangianMap_of_finrank (h : hσ.IsIsotropicMap J f)
    (hinj : ∀ x, Function.Injective (mfderiv J I f x))
    (hdim : 2 * finrank ℝ E' = finrank ℝ E) : hσ.IsLagrangianMap J f := fun x ↦
  (h x).isLagrangian_of_finrank (by
    rw [LinearMap.finrank_range_of_inj (hinj x), finrank_tangentSpace, finrank_tangentSpace, hdim])

omit [FiniteDimensional ℝ E] in
/-- **Maps from curves are isotropic.** Every map from a manifold of dimension at most one is
isotropic: its tangent images have dimension at most one. -/
theorem isIsotropicMap_of_finrank_le_one [FiniteDimensional ℝ E'] (hE' : finrank ℝ E' ≤ 1) :
    hσ.IsIsotropicMap J f := fun x ↦
  SymplecticForm.isIsotropic_of_finrank_le_one
    ((LinearMap.finrank_range_le (mfderiv J I f x).toLinearMap).trans
      (by rwa [finrank_tangentSpace]))

end Dimension

/-! ### The linear symplectic facts for tangent images -/

section TangentImage

/-- **The complement of a tangent image has the complementary dimension.** If `M` is
finite-dimensional and the differential of `f` is injective at `x`, the tangent image
`W = df_x(T_x N)` satisfies `dim N + dim W^σ = dim M`. -/
theorem finrank_add_finrank_orthogonal_range_mfderiv [FiniteDimensional ℝ E] {x : N}
    (hx : Function.Injective (mfderiv J I f x)) :
    finrank ℝ E' + finrank ℝ ((hσ.symplecticFormAt (f x)).orthogonal
      (LinearMap.range (mfderiv J I f x).toLinearMap)) = finrank ℝ E := by
  have := (hσ.symplecticFormAt (f x)).finrank_add_finrank_orthogonal
    (LinearMap.range (mfderiv J I f x).toLinearMap)
  rwa [LinearMap.finrank_range_of_inj hx, finrank_tangentSpace, finrank_tangentSpace] at this

/-- **The double complement of a tangent image is the tangent image**: if `M` is
finite-dimensional, `W^σσ = W` for `W = df_x(T_x N)`. No injectivity of the differential is
needed. -/
theorem orthogonal_orthogonal_range_mfderiv [FiniteDimensional ℝ E] (x : N) :
    (hσ.symplecticFormAt (f x)).orthogonal ((hσ.symplecticFormAt (f x)).orthogonal
        (LinearMap.range (mfderiv J I f x).toLinearMap)) =
      LinearMap.range (mfderiv J I f x).toLinearMap :=
  SymplecticForm.orthogonal_orthogonal _ _

/-- **A tangent image is Lagrangian exactly when it is maximal isotropic**, in any dimension. -/
theorem isLagrangian_range_mfderiv_iff_maximal_isIsotropic (x : N) :
    (hσ.symplecticFormAt (f x)).IsLagrangian (LinearMap.range (mfderiv J I f x).toLinearMap) ↔
      Maximal (hσ.symplecticFormAt (f x)).IsIsotropic
        (LinearMap.range (mfderiv J I f x).toLinearMap) :=
  SymplecticForm.isLagrangian_iff_maximal_isIsotropic

/-- A map is Lagrangian exactly when each of its tangent images is a maximal isotropic subspace. -/
theorem isLagrangianMap_iff_forall_maximal_isIsotropic :
    hσ.IsLagrangianMap J f ↔ ∀ x, Maximal (hσ.symplecticFormAt (f x)).IsIsotropic
      (LinearMap.range (mfderiv J I f x).toLinearMap) :=
  forall_congr' isLagrangian_range_mfderiv_iff_maximal_isIsotropic

end TangentImage

/-! ### Lagrangian immersions -/

variable (J hσ) in
/-- A **Lagrangian immersion** for a nondegenerate two-form `σ` on a finite-dimensional manifold
`M` is a smooth immersion `f : N → M` with isotropic tangent images from a manifold of half the
dimension of `M`. Its image may have self-intersections. -/
structure IsLagrangianImmersion [FiniteDimensional ℝ E] (f : N → M) : Prop where
  /-- A Lagrangian immersion is a smooth immersion. -/
  isImmersion : IsImmersion J I ∞ f
  /-- A Lagrangian immersion has isotropic tangent images. -/
  isIsotropicMap : hσ.IsIsotropicMap J f
  /-- A Lagrangian immersion comes from a manifold of half the dimension. -/
  two_mul_finrank : 2 * finrank ℝ E' = finrank ℝ E

/-- A Lagrangian immersion is a Lagrangian map. -/
theorem IsLagrangianImmersion.isLagrangianMap [FiniteDimensional ℝ E]
    (h : hσ.IsLagrangianImmersion J f) : hσ.IsLagrangianMap J f :=
  h.isIsotropicMap.isLagrangianMap_of_finrank (h.isImmersion.mfderiv_injective (by simp))
    h.two_mul_finrank

/-- An immersion from a nonempty manifold is a Lagrangian immersion exactly when it is a
Lagrangian map. -/
theorem isLagrangianImmersion_iff [FiniteDimensional ℝ E] [Nonempty N] :
    hσ.IsLagrangianImmersion J f ↔ IsImmersion J I ∞ f ∧ hσ.IsLagrangianMap J f := by
  refine ⟨fun h ↦ ⟨h.isImmersion, h.isLagrangianMap⟩, fun ⟨himm, hL⟩ ↦ ⟨himm, hL.isIsotropicMap,
    ?_⟩⟩
  exact hL.two_mul_finrank (himm.mfderiv_injective (by simp) (Classical.arbitrary N))

/-- A smooth immersion is Lagrangian exactly when its pulled-back two-form vanishes and
its source has half the ambient dimension. This includes empty sources. -/
theorem isLagrangianImmersion_iff_mpullback_eq_zero [FiniteDimensional ℝ E]
    [IsManifold J ∞ N] (hf : IsImmersion J I ∞ f) :
    hσ.IsLagrangianImmersion J f ↔
      SmoothForm.mpullback f hf.contMDiff σ = 0 ∧ 2 * finrank ℝ E' = finrank ℝ E := by
  constructor
  · intro h
    exact ⟨(isIsotropicMap_iff_mpullback_eq_zero hf.contMDiff).mp h.isIsotropicMap,
      h.two_mul_finrank⟩
  · rintro ⟨h, hdim⟩
    exact ⟨hf, (isIsotropicMap_iff_mpullback_eq_zero hf.contMDiff).mpr h, hdim⟩

/-- **Immersed curves in a surface are Lagrangian immersions.** An immersion of a one-dimensional
manifold into a two-dimensional manifold with a nondegenerate two-form is a Lagrangian immersion.
It need not be injective, so its image may have self-intersections. -/
theorem isLagrangianImmersion_of_finrank_eq_one [FiniteDimensional ℝ E]
    (hf : IsImmersion J I ∞ f) (hE' : finrank ℝ E' = 1) (hE : finrank ℝ E = 2) :
    hσ.IsLagrangianImmersion J f :=
  have : FiniteDimensional ℝ E' := Module.finite_of_finrank_eq_succ hE'
  ⟨hf, isIsotropicMap_of_finrank_le_one hE'.le, by omega⟩

end IsNondegenerate

end SmoothTwoForm

/-! ### Linear Lagrangian subspaces -/

namespace SymplecticForm

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]

/-- In a finite-dimensional symplectic vector space with its constant symplectic form, a
continuous linear map is a Lagrangian map exactly when its range is a Lagrangian subspace. -/
theorem isLagrangianMap_continuousLinearMap_iff (σ₀ : SymplecticForm W) (L : V →L[ℝ] W) :
    (isNondegenerate_constSmooth σ₀).IsLagrangianMap 𝓘(ℝ, V) L ↔
      σ₀.IsLagrangian (LinearMap.range L.toLinearMap) := by
  simp only [SmoothTwoForm.IsNondegenerate.IsLagrangianMap,
    isNondegenerate_constSmooth_symplecticFormAt, ContinuousLinearMap.mfderiv_eq]
  exact ⟨fun h ↦ h 0, fun h _ ↦ h⟩

section Symplectomorphism

variable [FiniteDimensional ℝ V] {σ₁ : SymplecticForm V} {σ₂ : SymplecticForm W} {e : V ≃L[ℝ] W}
  {E' H' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  {J : ModelWithCorners ℝ E' H'} {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]
  {f : N → V}

/-- Composing with a linear symplectomorphism preserves and reflects isotropic maps. -/
theorem IsSymplectomorphism.isIsotropicMap_comp_iff (he : IsSymplectomorphism σ₁ σ₂ e) :
    (isNondegenerate_constSmooth σ₂).IsIsotropicMap J (e ∘ f) ↔
      (isNondegenerate_constSmooth σ₁).IsIsotropicMap J f :=
  SmoothTwoForm.IsNondegenerate.isIsotropicMap_diffeomorph_comp_iff e.toDiffeomorph
    he.mpullback_constSmooth

/-- Composing with a linear symplectomorphism preserves and reflects Lagrangian maps. -/
theorem IsSymplectomorphism.isLagrangianMap_comp_iff (he : IsSymplectomorphism σ₁ σ₂ e) :
    (isNondegenerate_constSmooth σ₂).IsLagrangianMap J (e ∘ f) ↔
      (isNondegenerate_constSmooth σ₁).IsLagrangianMap J f :=
  SmoothTwoForm.IsNondegenerate.isLagrangianMap_diffeomorph_comp_iff e.toDiffeomorph
    he.mpullback_constSmooth

end Symplectomorphism

end SymplecticForm

end TauCeti
