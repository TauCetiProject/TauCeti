/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Sphere.TangentCircle
public import TauCeti.Analysis.InnerProductSpace.Orthonormal.Triple
public import TauCeti.Topology.Homotopy.Cube.Sphere
public import TauCeti.Topology.MappingSpace.Evaluation
public import TauCeti.Topology.Sphere.Suspension
public import TauCeti.Topology.VectorBundle.SphereBundle.Orthogonal
import TauCeti.Topology.Homotopy.GenLoop.Loop
import TauCeti.Topology.Homotopy.SerreFibration.FiberBundle

/-!
# The family of two-spheres of a sphere carrying two orthonormal tangent fields

Let `Sⁿ` be the unit sphere of a real inner product space `E`, and let `u`, `v` be two tangent
vector fields on it which are orthonormal at every point: `x`, `u x` and `v x` are orthonormal for
every `x ∈ Sⁿ`. On the spheres `S^{4k-1}` any two of the quaternionic fields `x <• i`, `x <• j`,
`x <• k` are such a pair (`TauCeti.orthonormal_vecCons_quaternionFrame_of_ne`).

Over each `x ∈ Sⁿ` lies the equator `Σₓ` of points `q ∈ Sⁿ` orthogonal to `u x` and to `v x`, a
sphere of dimension `n - 2` through `x`. These equators form the space
`Σ = {(x, q) | q ∈ Σₓ}` (`TauCeti.twoFieldEquators`), a closed subspace of `Sⁿ × Sⁿ`, compact
when `E` is finite-dimensional. For `(x, q) ∈ Σ`, Barraud–Damian–Humilière–Oancea (Example 6.20)
sweep a two-sphere through `x`: first the circle through `x` and `q` tangent to `v x`,

`s ↦ w(s) = tangentCircle x (v x) q (2π s)`,

which stays in the equator orthogonal to `u x` (`TauCeti.twoFieldInnerLoop`); then, through each
point `w(s)`, the circle through `x` tangent to `u x`,

`(s, t) ↦ tangentCircle x (u x) (w(s)) (2π t)`.

The boundary of the square goes to `x`, so the square descends along the collapse
`I² → S²` (`TauCeti.sphereCollapse`) to a map `S² → Sⁿ` sending the north pole to `x`. This
depends continuously on `(x, q)` and gives the family
(`TauCeti.twoFieldSphereFamily`)

`σ : Σ → Map(S², Sⁿ)`,

which lies over `Sⁿ`: evaluation at the north pole sends `σ (x, q)` to `x`
(`TauCeti.mappingSpaceEval_comp_twoFieldSphereFamily`). This is the commutative square over
`Sⁿ` required of a fibred family of two-spheres in the source's Definition 6.14, for the family
of their Example 6.20. That definition also asks `Σ → Sⁿ` to be an oriented locally trivial
bundle of closed manifolds, with nonvanishing class of a fibre. Over a finite-dimensional space,
`Σ` is the space of unit vectors orthogonal to the frames `(u x, v x)`
(`TauCeti.twoFieldEquators_eq_orthogonalSphereBundle`), so the projection `Σ → Sⁿ` is locally
trivial with fibre a sphere of dimension `n - 2` (`TauCeti.exists_trivialization_twoFieldEquators`)
and is a Serre fibration (`TauCeti.TopCat.mem_serreFibrations_twoFieldEquators`). The fibre `Σₓ`
of `Σ` over `x` is the equator orthogonal to `v x` of the unit sphere of the orthogonal complement
of `u x` (`TauCeti.twoFieldEquatorsFiberHomeomorph`), and over it `σ` restricts to a family of
based maps `(S², north) → (Sⁿ, x)` (`TauCeti.twoFieldSphereFamilyFiber`). That the class of a fibre
is nonvanishing for `n ≥ 4`, indeed a generator of `H_{n-2}(Ω²Sⁿ; ℤ)`, is proved in
`TauCeti.AlgebraicTopology.Sphere.DoubleTangentCircle`
(`TauCeti.isIso_singularHomologyFunctor_map_twoFieldSphereFamilyFiber`). The orientation and the
smooth structure are not addressed here.

The first cube coordinate `s` runs along the inner circle, as in
`TauCeti.tangentCircleDoubleLoop`, so that under `Map_*(S², Sⁿ) ≃ₜ Ω²Sⁿ` it is the loop parameter
of the loop of loops. On the square, `σ (x, q)` is therefore the generalized loop
`tangentCircleGenLoop` of the inner circle with its two cube coordinates exchanged
(`TauCeti.twoFieldSphereFamily_sphereCollapse`), so the fibre over `x` is read in the same terms
as the tangent-circle loops of `TauCeti.AlgebraicTopology.Sphere.TangentCircle`. The point `x`
itself lies on its equator, and its sphere is constant (`TauCeti.twoFieldSphereFamily_self`).

## Main declarations

* `TauCeti.twoFieldEquators u v`: the space `Σ` of pairs `(x, q)` with `q ⊥ u x, v x`.
* `TauCeti.exists_trivialization_twoFieldEquators`,
  `TauCeti.TopCat.mem_serreFibrations_twoFieldEquators`: `Σ → Sⁿ` is a locally trivial bundle
  and a Serre fibration.
* `TauCeti.twoFieldInnerLoop`: the circle through `x` and `q` tangent to `v x`, as a loop in the
  equator orthogonal to `u x`.
* `TauCeti.twoFieldSphereFamily`: the family `σ : Σ → Map(S², Sⁿ)`.
* `TauCeti.twoFieldSphereFamily_sphereCollapse`: on the square, `σ (x, q)` is
  `tangentCircleGenLoop` of the inner loop, with the cube coordinates exchanged.
* `TauCeti.mappingSpaceEval_comp_twoFieldSphereFamily`: `σ` lies over the sphere.
* `TauCeti.twoFieldEquatorsFiberHomeomorph`: the fibre `Σₓ` is an equator of the unit sphere of
  `(u x)⊥`.
* `TauCeti.twoFieldEquatorsProj`, `TauCeti.orthogonalSphereIsoTwoFieldEquatorsPreimage`,
  `TauCeti.finrank_orthogonal_span_twoField`: the projection `Σ → Sⁿ` in `TopCat`, whose fibre
  over `x` is the unit sphere of the orthogonal complement of `v x` in `(u x)⊥`, a sphere of
  dimension `n - 2`.
* `TauCeti.twoFieldSphereFamilyFiber`: the restriction `Σₓ → Map_*(S², Sⁿ)` of `σ` to a fibre.

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, §6.4.2, Definition 6.14 and
  Example 6.20.
-/

public section

noncomputable section

open Metric Real
open scoped RealInnerProductSpace Topology unitInterval Topology.Homotopy

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The space `Σ` of the equators cut out by two tangent vector fields `u`, `v` of the unit sphere:
the pairs `(x, q)` of points of the sphere with `q` orthogonal to `u x` and to `v x`. When
`x`, `u x`, `v x` are orthonormal, the fibre over `x` is a sphere of codimension two through
`x`. -/
def twoFieldEquators (u v : sphere (0 : E) 1 → E) : Set (sphere (0 : E) 1 × sphere (0 : E) 1) :=
  {xq | ⟪(xq.2 : E), u xq.1⟫ = 0 ∧ ⟪(xq.2 : E), v xq.1⟫ = 0}

variable {u v : sphere (0 : E) 1 → E}

@[simp]
theorem mem_twoFieldEquators {xq : sphere (0 : E) 1 × sphere (0 : E) 1} :
    xq ∈ twoFieldEquators u v ↔ ⟪(xq.2 : E), u xq.1⟫ = 0 ∧ ⟪(xq.2 : E), v xq.1⟫ = 0 :=
  Iff.rfl

theorem isClosed_twoFieldEquators (hu : Continuous u) (hv : Continuous v) :
    IsClosed (twoFieldEquators u v) :=
  (isClosed_eq (by fun_prop) continuous_const).inter (isClosed_eq (by fun_prop) continuous_const)

/-- Over a finite-dimensional space, the space of equators is compact. -/
theorem isCompact_twoFieldEquators [FiniteDimensional ℝ E] (hu : Continuous u)
    (hv : Continuous v) : IsCompact (twoFieldEquators u v) :=
  (isClosed_twoFieldEquators hu hv).isCompact

/-- **The space of equators is compact.** -/
theorem compactSpace_twoFieldEquators [FiniteDimensional ℝ E] (hu : Continuous u)
    (hv : Continuous v) : CompactSpace (twoFieldEquators u v) :=
  isCompact_iff_compactSpace.1 (isCompact_twoFieldEquators hu hv)

/-- The space of equators is the space of unit vectors orthogonal to the frames `(u x, v x)`. -/
theorem twoFieldEquators_eq_orthogonalSphereBundle :
    twoFieldEquators u v = orthogonalSphereBundle fun x ↦ ![u x, v x] := by
  ext
  simp [Fin.forall_fin_two]

/-- **The space of equators is a locally trivial bundle over the sphere.** For two continuous
vector fields `u`, `v` on the unit sphere `Sⁿ` of a finite-dimensional space `E`, orthonormal at
every point, every point of the sphere lies in the base set of a chart of the projection
`(x, q) ↦ x` of the space of equators, with fibre the unit sphere of any real normed space `F` of
dimension `dim E - 2`, a sphere of dimension `n - 2`. -/
theorem exists_trivialization_twoFieldEquators [FiniteDimensional ℝ E] {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] (hu : Continuous u)
    (hv : Continuous v) (huv : ∀ x, Orthonormal ℝ ![u x, v x])
    (hF : Module.finrank ℝ F + 2 = Module.finrank ℝ E) (x : sphere (0 : E) 1) :
    ∃ e : Bundle.Trivialization (sphere (0 : F) 1)
      (ContinuousMap.fst.comp (ContinuousMap.subtypeVal (twoFieldEquators u v))),
      x ∈ e.baseSet := by
  obtain ⟨e, he⟩ := exists_trivialization_orthogonalSphereBundleProj (by fun_prop) huv
    (by simpa using hF) x
  -- Transport the chart along the identification of the space of equators.
  have hproj : orthogonalSphereBundleProj (fun x ↦ ![u x, v x]) ∘
      Homeomorph.setCongr twoFieldEquators_eq_orthogonalSphereBundle =
      ContinuousMap.fst.comp (ContinuousMap.subtypeVal (twoFieldEquators u v)) := by
    ext xq
    simp only [Function.comp_apply, orthogonalSphereBundleProj_apply]
    -- `Homeomorph.setCongr` has no evaluation lemma; it is the identity on underlying points.
    rfl
  rw [← hproj]
  exact ⟨e.compHomeomorph _, he⟩

/-- **The space of equators is a Serre fibration over the sphere.** For two continuous vector
fields `u`, `v` on the unit sphere `Sⁿ` of `E`, orthonormal at every point, the projection
`(x, q) ↦ x` of the space of equators is a Serre fibration with fibre `Sⁿ⁻²`. -/
theorem TopCat.mem_serreFibrations_twoFieldEquators [FiniteDimensional ℝ E] (hu : Continuous u)
    (hv : Continuous v) (huv : ∀ x, Orthonormal ℝ ![u x, v x]) :
    TopCat.serreFibrations (_root_.TopCat.ofHom
      (ContinuousMap.fst.comp (ContinuousMap.subtypeVal (twoFieldEquators u v))) :
        _root_.TopCat.of (twoFieldEquators u v) ⟶ _root_.TopCat.of (sphere (0 : E) 1)) :=
  TopCat.mem_serreFibrations_of_exists_trivialization fun x ↦ by
    -- The dimension of the fibre is read off the orthonormal pair at `x`.
    have h := (huv x).linearIndependent.fintype_card_le_finrank
    exact exists_trivialization_twoFieldEquators
      (F := EuclideanSpace ℝ (Fin (Module.finrank ℝ E - 2))) hu hv huv (by simp at h ⊢; omega) x

section Pointwise

variable {x : sphere (0 : E) 1} (hx : Orthonormal ℝ ![(x : E), u x, v x])
include hx

/-- A point of the sphere lies on its own equator. -/
theorem mk_self_mem_twoFieldEquators : (x, x) ∈ twoFieldEquators u v :=
  ⟨hx.inner_eq_zero_vecCons_zero_one, hx.inner_eq_zero_vecCons_zero_two⟩

end Pointwise

section Fiber

variable {x : sphere (0 : E) 1} (huv : ⟪v x, u x⟫ = 0)

/-- **The fibre of the space of equators over a point.** When `v x` is orthogonal to `u x`, the
fibre `Σₓ = {(x', q) ∈ Σ | x' = x}` is homeomorphic, through `q ↦ (x, q)`, to the equator
orthogonal to `v x` of the unit sphere of the orthogonal complement of `u x`. -/
def twoFieldEquatorsFiberHomeomorph :
    sphereEquator (⟨v x, Submodule.mem_orthogonal_singleton_iff_inner_left.2 huv⟩ : (ℝ ∙ u x)ᗮ) ≃ₜ
      {xq : twoFieldEquators u v // xq.val.1 = x} where
  toFun q := ⟨⟨(x, ⟨((q : sphere (0 : (ℝ ∙ u x)ᗮ) 1) : (ℝ ∙ u x)ᗮ), by
      rw [mem_sphere_zero_iff_norm, Submodule.norm_coe]
      exact norm_eq_of_mem_sphere _⟩),
    Submodule.mem_orthogonal_singleton_iff_inner_left.1 (q : sphere (0 :
        (ℝ ∙ u x)ᗮ) 1).val.property,
    by simpa only [Submodule.coe_inner] using mem_sphereEquator.1 q.property⟩, rfl⟩
  invFun xq := ⟨⟨⟨xq.val.val.2, Submodule.mem_orthogonal_singleton_iff_inner_left.2 (by
      obtain ⟨⟨⟨x', q⟩, hq⟩, rfl⟩ := xq
      exact hq.1)⟩, by simp [norm_eq_of_mem_sphere]⟩, by
    obtain ⟨⟨⟨x', q⟩, hq⟩, rfl⟩ := xq
    exact mem_sphereEquator.2 hq.2⟩
  left_inv q := rfl
  right_inv xq := by
    obtain ⟨⟨⟨x', q⟩, hxq⟩, rfl⟩ := xq
    rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

/-- The homeomorphism `twoFieldEquatorsFiberHomeomorph` sends `q` to `(x, q)`. -/
@[simp]
theorem coe_twoFieldEquatorsFiberHomeomorph_apply
    (q : sphereEquator
      (⟨v x, Submodule.mem_orthogonal_singleton_iff_inner_left.2 huv⟩ : (ℝ ∙ u x)ᗮ)) :
    ((twoFieldEquatorsFiberHomeomorph huv q : twoFieldEquators u v) :
        sphere (0 : E) 1 × sphere (0 : E) 1) =
      (x, (orthogonalSphereToEquator (u x) q : sphere (0 : E) 1)) :=
  Prod.ext rfl (Subtype.ext (coe_orthogonalSphereToEquator _ _).symm)

/-- The inverse of `twoFieldEquatorsFiberHomeomorph` sends `(x, q)` to `q`. -/
@[simp]
theorem coe_twoFieldEquatorsFiberHomeomorph_symm_apply
    (xq : {xq : twoFieldEquators u v // xq.val.1 = x}) :
    ((((twoFieldEquatorsFiberHomeomorph huv).symm xq : sphere (0 : (ℝ ∙ u x)ᗮ) 1) :
        (ℝ ∙ u x)ᗮ) : E) = xq.val.val.2 :=
  (rfl)

variable (u v) in
/-- The projection `(x, q) ↦ x` of the space of equators, as a morphism of `TopCat`. -/
def twoFieldEquatorsProj :
    _root_.TopCat.of (twoFieldEquators u v) ⟶ _root_.TopCat.of (sphere (0 : E) 1) :=
  _root_.TopCat.ofHom (ContinuousMap.fst.comp (ContinuousMap.subtypeVal (twoFieldEquators u v)))

/-- The projection `TauCeti.twoFieldEquatorsProj` is the first projection `(x, q) ↦ x`. -/
@[simp]
theorem hom_twoFieldEquatorsProj :
    (twoFieldEquatorsProj u v).hom =
      ContinuousMap.fst.comp (ContinuousMap.subtypeVal (twoFieldEquators u v)) :=
  (rfl)

variable (x) in
/-- The fibre `{(x', q) ∈ Σ | x' = x}` of the space of equators over `x` is the preimage of `x`
under the projection `TauCeti.twoFieldEquatorsProj`: the two subspaces have the same points. -/
def twoFieldEquatorsFiberHomeomorphPreimage :
    {xq : twoFieldEquators u v // xq.val.1 = x} ≃ₜ (twoFieldEquatorsProj u v ⁻¹' {x} : Set _) where
  toFun xq := ⟨xq.val, xq.property⟩
  invFun xq := ⟨xq.val, xq.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The homeomorphism `TauCeti.twoFieldEquatorsFiberHomeomorphPreimage` keeps the point of the
space of equators. -/
@[simp]
theorem coe_twoFieldEquatorsFiberHomeomorphPreimage_apply
    (xq : {xq : twoFieldEquators u v // xq.val.1 = x}) :
    (twoFieldEquatorsFiberHomeomorphPreimage x xq : twoFieldEquators u v) = xq.val :=
  (rfl)

/-- The inverse of `TauCeti.twoFieldEquatorsFiberHomeomorphPreimage` keeps the point of the space
of equators. -/
@[simp]
theorem coe_twoFieldEquatorsFiberHomeomorphPreimage_symm_apply
    (xq : (twoFieldEquatorsProj u v ⁻¹' {x} : Set _)) :
    ((twoFieldEquatorsFiberHomeomorphPreimage x).symm xq : twoFieldEquators u v) = xq.val :=
  (rfl)

/-- **The fibre of the projection of the space of equators is a sphere.** When `v x` is
orthogonal to `u x`, the preimage of `x` under `TauCeti.twoFieldEquatorsProj` is homeomorphic to
the unit sphere of the orthogonal complement of `v x` in `(u x)⊥`. -/
def orthogonalSphereIsoTwoFieldEquatorsPreimage :
    _root_.TopCat.of (sphere (0 : (ℝ ∙ (⟨v x, Submodule.mem_orthogonal_singleton_iff_inner_left.2
      huv⟩ : (ℝ ∙ u x)ᗮ))ᗮ) 1) ≅ _root_.TopCat.of (twoFieldEquatorsProj u v ⁻¹' {x} : Set _) :=
  _root_.TopCat.isoOfHomeo ((orthogonalSphereHomeomorphEquator _).trans
    ((twoFieldEquatorsFiberHomeomorph huv).trans (twoFieldEquatorsFiberHomeomorphPreimage x)))

/-- The isomorphism `TauCeti.orthogonalSphereIsoTwoFieldEquatorsPreimage` sends `q` to `(x, q)`. -/
@[simp]
theorem coe_orthogonalSphereIsoTwoFieldEquatorsPreimage_hom_apply
    (q : sphere (0 : (ℝ ∙ (⟨v x, Submodule.mem_orthogonal_singleton_iff_inner_left.2 huv⟩ :
      (ℝ ∙ u x)ᗮ))ᗮ) 1) :
    (((orthogonalSphereIsoTwoFieldEquatorsPreimage huv).hom q : twoFieldEquators u v) :
        sphere (0 : E) 1 × sphere (0 : E) 1) =
      (x, (orthogonalSphereToEquator (u x)
        (orthogonalSphereToEquator _ q : sphere (0 : (ℝ ∙ u x)ᗮ) 1) : sphere (0 : E) 1)) :=
  (coe_twoFieldEquatorsFiberHomeomorph_apply huv (orthogonalSphereHomeomorphEquator _ q)).trans
    (by rw [orthogonalSphereHomeomorphEquator_apply])

/-- The inverse of `TauCeti.orthogonalSphereIsoTwoFieldEquatorsPreimage` sends `(x, q)` to `q`. -/
@[simp]
theorem coe_orthogonalSphereIsoTwoFieldEquatorsPreimage_inv_apply
    (xq : (twoFieldEquatorsProj u v ⁻¹' {x} : Set _)) :
    (((((orthogonalSphereIsoTwoFieldEquatorsPreimage huv).inv xq :
      sphere (0 : (ℝ ∙ (⟨v x, Submodule.mem_orthogonal_singleton_iff_inner_left.2 huv⟩ :
        (ℝ ∙ u x)ᗮ))ᗮ) 1) : (ℝ ∙ (⟨v x, Submodule.mem_orthogonal_singleton_iff_inner_left.2 huv⟩ :
          (ℝ ∙ u x)ᗮ))ᗮ) : (ℝ ∙ u x)ᗮ) : E) = (xq : twoFieldEquators u v).val.2 :=
  (congrArg Subtype.val (coe_orthogonalSphereHomeomorphEquator_symm_apply _ _)).trans
    (coe_twoFieldEquatorsFiberHomeomorph_symm_apply huv _)

/-- The fibre of the space of equators of `Sⁿ` is a sphere of dimension `n - 2`: when `u x` and
`v x` are nonzero and orthogonal in a space of dimension `n + 2`, the orthogonal complement of
`v x` in `(u x)⊥` has dimension `n`. -/
theorem finrank_orthogonal_span_twoField {n : ℕ} (hE : Module.finrank ℝ E = n + 2)
    (hu₀ : u x ≠ 0) (hv₀ : v x ≠ 0) :
    Module.finrank ℝ (ℝ ∙ (⟨v x, Submodule.mem_orthogonal_singleton_iff_inner_left.2 huv⟩ :
      (ℝ ∙ u x)ᗮ))ᗮ = n := by
  have : Fact (Module.finrank ℝ E = n + 1 + 1) := ⟨hE⟩
  have : Fact (Module.finrank ℝ (ℝ ∙ u x)ᗮ = n + 1) :=
    ⟨Submodule.finrank_orthogonal_span_singleton hu₀⟩
  exact Submodule.finrank_orthogonal_span_singleton fun h0 ↦ hv₀ (congrArg Subtype.val h0)

end Fiber

section InnerLoop

variable (xq : twoFieldEquators u v) (hx : Orthonormal ℝ ![(xq.val.1 : E), u xq.val.1, v xq.val.1])
include hx

/-- The circle through `x` and `q` tangent to `v x` lies on the unit sphere. -/
private theorem norm_tangentCircle_inner (θ : ℝ) :
    ‖tangentCircle (xq.val.1 : E) (v xq.val.1) (xq.val.2 : E) θ‖ = 1 :=
  norm_tangentCircle (norm_eq_of_mem_sphere xq.val.1) hx.norm_eq_one_vecCons_two
    hx.inner_eq_zero_vecCons_zero_two (norm_eq_of_mem_sphere xq.val.2) xq.property.2 θ

/-- The circle through `x` and `q` tangent to `v x` is orthogonal to `u x`. -/
private theorem inner_tangentCircle_inner (θ : ℝ) :
    ⟪tangentCircle (xq.val.1 : E) (v xq.val.1) (xq.val.2 : E) θ, u xq.val.1⟫ = 0 :=
  inner_tangentCircle_eq_zero hx.inner_eq_zero_vecCons_zero_one
    (inner_eq_zero_symm.1 hx.inner_eq_zero_vecCons_one_two) xq.property.1 θ

/-- The **inner circle** of the two-sphere of `(x, q)`: the circle through `x` and `q` tangent to
`v x`, `s ↦ tangentCircle x (v x) q (2π s)`, as a loop at `x` in the equator of the sphere
orthogonal to `u x`. -/
def twoFieldInnerLoop :
    Ω^ (Fin 1) (sphereEquator (u xq.val.1))
      ⟨xq.val.1, mem_sphereEquator.2 hx.inner_eq_zero_vecCons_zero_one⟩
    where
  val :=
    { toFun z := ⟨⟨tangentCircle (xq.val.1 : E) (v xq.val.1) (xq.val.2 : E) (2 * π * z 0),
          mem_sphere_zero_iff_norm.2 (norm_tangentCircle_inner xq hx _)⟩,
        mem_sphereEquator.2 (inner_tangentCircle_inner xq hx _)⟩
      continuous_toFun := by fun_prop }
  property z hz := by
    refine Subtype.ext (Subtype.ext ?_)
    rcases Cube.boundary_fin_one_iff.1 hz with hz | hz <;> simp [hz]

@[simp]
theorem coe_twoFieldInnerLoop_apply (z : I^(Fin 1)) :
    ((twoFieldInnerLoop xq hx z : sphere (0 : E) 1) : E) =
      tangentCircle (xq.val.1 : E) (v xq.val.1) (xq.val.2 : E) (2 * π * z 0) :=
  (rfl)

end InnerLoop

variable (h : ∀ x : sphere (0 : E) 1, Orthonormal ℝ ![(x : E), u x, v x])
  (hu : Continuous u) (hv : Continuous v)
include h hu hv

/-- The two-spheres on the square: `((x, q), y) ↦ tangentCircle x (u x) (w y₀) (2π y₁)`, where
`w` is the inner circle of `(x, q)`; this is `tangentCircleGenLoop` of `w` with the two cube
coordinates exchanged. -/
private def twoFieldSquare : C(twoFieldEquators u v × I^(Fin 2), sphere (0 : E) 1) where
  toFun a := GenLoop.congr _ (Equiv.swap 0 1)
    (tangentCircleGenLoop (h a.1.val.1).norm_eq_one_vecCons_one
      (twoFieldInnerLoop a.1 (h a.1.val.1))) a.2
  continuous_toFun := by
    refine continuous_induced_rng.2 (Continuous.congr (f := fun a ↦
      tangentCircle (a.1.val.1 : E) (u a.1.val.1)
        (tangentCircle (a.1.val.1 : E) (v a.1.val.1) (a.1.val.2 : E) (2 * π * a.2 0))
            (2 * π * a.2 1))
      ?_ fun a ↦ ?_)
    · fun_prop
    · rw [Function.comp_apply, GenLoop.congr_apply, coe_tangentCircleGenLoop_apply,
        coe_twoFieldInnerLoop_apply]
      simp [Fin.tail]

private theorem factorsThrough_twoFieldSquare :
    Function.FactorsThrough (twoFieldSquare h hu hv)
      ((ContinuousMap.id (twoFieldEquators u v)).prodMap (sphereCollapse 2 Sphere2.north)) := by
  rintro ⟨xq, y⟩ ⟨xq', y'⟩ hyy
  simp only [ContinuousMap.prodMap_apply, ContinuousMap.id_apply, Prod.map, Prod.mk.injEq] at hyy
  obtain ⟨rfl, hyy⟩ := hyy
  rcases eq_or_mem_boundary_of_sphereCollapse_eq 2 Sphere2.north hyy with rfl | ⟨hy, hy'⟩
  · rfl
  · -- both boundary points go to the base point of the generalized loop defining the square
    have hb := GenLoop.boundary (GenLoop.congr _ (Equiv.swap 0 1)
      (tangentCircleGenLoop (h xq.val.1).norm_eq_one_vecCons_one (twoFieldInnerLoop xq
          (h xq.val.1))))
    exact (hb y hy).trans (hb y' hy').symm

/-- **The family of two-spheres of two orthonormal tangent fields** (Barraud–Damian–Humilière–
Oancea, Example 6.20). For `(x, q)` in the space of equators, `σ (x, q) : S² → Sⁿ` sweeps, through
each point `w` of the circle through `x` and `q` tangent to `v x`, the circle through `x` and `w`
tangent to `u x`; it sends the north pole to `x`. -/
def twoFieldSphereFamily : C(twoFieldEquators u v, C(Sphere2, sphere (0 : E) 1)) :=
  ((isQuotientMap_prodMap_id_sphereCollapse 2 Sphere2.north _).lift _
    (factorsThrough_twoFieldSquare h hu hv)).curry

/-- On the square, the two-sphere of `(x, q)` is the generalized loop of the circles through `x`
tangent to `u x` and through the points of the inner circle `twoFieldInnerLoop`, with the two cube
coordinates exchanged so that the first one runs along the inner circle. -/
theorem twoFieldSphereFamily_sphereCollapse (xq : twoFieldEquators u v) (y : I^(Fin 2)) :
    twoFieldSphereFamily h hu hv xq (sphereCollapse 2 Sphere2.north y) =
      GenLoop.congr _ (Equiv.swap 0 1) (tangentCircleGenLoop
        (h xq.val.1).norm_eq_one_vecCons_one (twoFieldInnerLoop xq (h xq.val.1))) y :=
  DFunLike.congr_fun ((isQuotientMap_prodMap_id_sphereCollapse 2
    Sphere2.north _).lift_comp _ (factorsThrough_twoFieldSquare h hu hv)) (xq, y)

/-- On the square, the two-sphere of `(x, q)` is
`y ↦ tangentCircle x (u x) (tangentCircle x (v x) q (2π y₀)) (2π y₁)`. -/
@[simp]
theorem coe_twoFieldSphereFamily_sphereCollapse (xq : twoFieldEquators u v) (y : I^(Fin 2)) :
    (twoFieldSphereFamily h hu hv xq (sphereCollapse 2 Sphere2.north y) : E) =
      tangentCircle (xq.val.1 : E) (u xq.val.1)
        (tangentCircle (xq.val.1 : E) (v xq.val.1) (xq.val.2 : E) (2 * π * y 0)) (2 * π * y 1) := by
  rw [twoFieldSphereFamily_sphereCollapse, GenLoop.congr_apply, coe_tangentCircleGenLoop_apply,
    coe_twoFieldInnerLoop_apply]
  simp [Fin.tail]

/-- The two-sphere of `(x, q)` sends the north pole to `x`. -/
@[simp]
theorem twoFieldSphereFamily_north (xq : twoFieldEquators u v) :
    twoFieldSphereFamily h hu hv xq Sphere2.north = xq.val.1 := by
  rw [← (sphereCollapse_eq_basepoint_iff 2 Sphere2.north 0).2 zero_mem_cubeBoundary,
    twoFieldSphereFamily_sphereCollapse]
  exact GenLoop.boundary _ _ zero_mem_cubeBoundary

/-- **The family of two-spheres lies over the sphere**: evaluation at the north pole sends the
two-sphere of `(x, q)` to `x`. -/
@[simp]
theorem mappingSpaceEval_comp_twoFieldSphereFamily :
    (mappingSpaceEval Sphere2.north).comp (twoFieldSphereFamily h hu hv) =
      ContinuousMap.fst.comp (ContinuousMap.subtypeVal (twoFieldEquators u v)) := by
  ext xq
  simp

/-- The two-sphere of the point `(x, x)` of the space of equators is constant at `x`. -/
@[simp]
theorem twoFieldSphereFamily_self (x : sphere (0 : E) 1) :
    twoFieldSphereFamily h hu hv ⟨(x, x), mk_self_mem_twoFieldEquators (h x)⟩ =
      ContinuousMap.const Sphere2 x := by
  ext z : 1
  obtain ⟨y, rfl⟩ := sphereCollapse_surjective 2 Sphere2.north z
  exact Subtype.ext (by simp)

/-- **The two-spheres over a point.** Over `x`, the family `σ` restricts to the fibre
`Σₓ = {(x', q) ∈ Σ | x' = x}` as a family of based maps `(S², north) → (Sⁿ, x)`: the map that
Definition 6.14 of Barraud–Damian–Humilière–Oancea reads in the double loop space `Ω²Sⁿ`. -/
def twoFieldSphereFamilyFiber (x : sphere (0 : E) 1) :
    C({xq : twoFieldEquators u v // xq.val.1 = x},
      BasedMap Sphere2 (sphere (0 : E) 1) Sphere2.north x) :=
  BasedMap.lift ((twoFieldSphereFamily h hu hv).comp ⟨Subtype.val, continuous_subtypeVal⟩)
    fun xq ↦ by simpa using xq.property

/-- The based two-sphere of a point `(x, q)` of the fibre over `x` is the two-sphere of `(x, q)`. -/
@[simp]
theorem coe_twoFieldSphereFamilyFiber_apply (x : sphere (0 : E) 1)
    (xq : {xq : twoFieldEquators u v // xq.val.1 = x}) :
    (twoFieldSphereFamilyFiber h hu hv x xq).val = twoFieldSphereFamily h hu hv xq.val :=
  BasedMap.lift_apply_val _ _ _

end TauCeti
