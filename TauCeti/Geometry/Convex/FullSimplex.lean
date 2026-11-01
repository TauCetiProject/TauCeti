/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.SimplicialComplex.Simplex.Ball
import Mathlib.Logic.Equiv.Fin.Rotate
public import TauCeti.Geometry.Convex.ConvexSpace.Topology
public import Mathlib.Analysis.Calculus.AddTorsor.AffineMap
public import Mathlib.Analysis.Calculus.TangentCone.Real
import Mathlib.LinearAlgebra.Finsupp.Pi
import TauCeti.Geometry.Convex.ConvexSpace.Defs

/-!
# The full-dimensional standard simplex

The simplex with nonnegative coordinates whose sum is at most one is an integration domain in
Euclidean space. Its homeomorphism with Mathlib's barycentric `Convexity.StdSimplex` adds the
zeroth weight, equal to one minus the sum of the coordinates. The face inclusions are transported
from Mathlib's maps of barycentric simplices. The bridge reuses
`AbstractSimplicialComplex.realizationTopHomeomorphCoordinateSimplex` and
`AbstractSimplicialComplex.realizationTopHomeomorphStdSimplex`; `finRotate` moves the omitted
last coordinate to the zeroth position. Every map of barycentric simplices induced by a map of
vertices, read on full-dimensional simplices, is the restriction of the continuous affine map
`simplexMapAmbient` of the ambient Euclidean spaces; the face inclusions are the case of the
coface vertex maps `Fin.succAbove`. In coordinates, the face `δᵢ₊₁` opposite `eᵢ` inserts a zero
`i`-th coordinate and the face `δ₀` opposite the origin prepends `1 - ∑ yⱼ`; the derivative of
`δᵢ₊₁` sends `eₖ` to `e_{i.succAbove k}` and that of `δ₀` sends `eₖ` to the edge `eₖ₊₁ - e₀`.
The ambient extension of a permutation of the vertices maps the simplex onto itself. The simplex
is a compact convex set with nonempty interior, so derivatives within it are unique at every point
(`TauCeti.uniqueDiffOn_fullSimplex`); this is what makes it a domain for derivatives and
integrals of forms.

This is the full-dimensional simplex convention used in Lee, *Introduction to Smooth Manifolds*,
Chapter 18. The barycentric simplex, its topology, and its maps are those of Mathlib.
-/

public section

open scoped BigOperators
open Convexity

namespace TauCeti

/-- The full-dimensional standard simplex in Euclidean `p`-space. -/
noncomputable def fullSimplex (p : ℕ) : Set (EuclideanSpace ℝ (Fin p)) :=
  (EuclideanSpace.equiv (Fin p) ℝ) ⁻¹' coordinateSimplex (Fin p)

/-- Membership in the full-dimensional simplex is coordinate nonnegativity and a sum bound. -/
@[simp]
theorem mem_fullSimplex_iff {p : ℕ} {x : EuclideanSpace ℝ (Fin p)} :
    x ∈ fullSimplex p ↔ (∀ i, 0 ≤ x i) ∧ ∑ i, x i ≤ 1 := by
  exact mem_coordinateSimplex _ _

/-- The origin is the zeroth vertex of the full-dimensional simplex. -/
theorem zero_mem_fullSimplex (p : ℕ) : 0 ∈ fullSimplex p := by
  simp

/-- The full-dimensional simplex is convex. -/
theorem convex_fullSimplex (p : ℕ) : Convex ℝ (fullSimplex p) :=
  (convex_coordinateSimplex (Fin p)).linear_preimage (EuclideanSpace.equiv (Fin p) ℝ).toLinearMap

/-- The full-dimensional simplex is closed. -/
theorem isClosed_fullSimplex (p : ℕ) : IsClosed (fullSimplex p) :=
  (isClosed_coordinateSimplex (Fin p)).preimage (EuclideanSpace.equiv (Fin p) ℝ).continuous

/-- The full-dimensional simplex is compact. -/
theorem isCompact_fullSimplex (p : ℕ) : IsCompact (fullSimplex p) :=
  (EuclideanSpace.equiv (Fin p) ℝ).toHomeomorph.isCompact_preimage.2
    (isCompact_coordinateSimplex (Fin p))

/-- The full-dimensional simplex has nonempty interior in its Euclidean space. -/
theorem nonempty_interior_fullSimplex (p : ℕ) : (interior (fullSimplex p)).Nonempty := by
  have h :=
    (EuclideanSpace.equiv (Fin p) ℝ).toHomeomorph.preimage_interior (coordinateSimplex (Fin p))
  rw [ContinuousLinearEquiv.coe_toHomeomorph] at h
  rw [fullSimplex, ← h]
  exact (nonempty_interior_coordinateSimplex (Fin p)).preimage
    (EuclideanSpace.equiv (Fin p) ℝ).surjective

/-- Derivatives within the full-dimensional simplex are unique at each of its points, including
the points of its faces and corners. -/
theorem uniqueDiffOn_fullSimplex (p : ℕ) : UniqueDiffOn ℝ (fullSimplex p) :=
  uniqueDiffOn_convex (convex_fullSimplex p) (nonempty_interior_fullSimplex p)

/-- Adding the missing zeroth weight identifies the full-dimensional and barycentric simplices. -/
noncomputable def fullSimplexEquivStdSimplex (p : ℕ) :
    fullSimplex p ≃ₜ StdSimplex ℝ (Fin (p + 1)) := by
  exact ((EuclideanSpace.equiv (Fin p) ℝ).toHomeomorph.subtype
    (p := fun x ↦ x ∈ fullSimplex p) (q := fun x ↦ x ∈ coordinateSimplex (Fin p))
    (fun _ ↦ Iff.rfl)).trans
    ((AbstractSimplicialComplex.realizationTopHomeomorphCoordinateSimplex p).symm.trans
      (AbstractSimplicialComplex.realizationTopHomeomorphStdSimplex.trans
        ((finRotate (p + 1)).stdSimplexHomeomorph (R := ℝ))))

/-- The positive-index weights are precisely the original Euclidean coordinates. -/
@[simp]
theorem fullSimplexEquivStdSimplex_weights_succ {p : ℕ} (x : fullSimplex p) (i : Fin p) :
    (fullSimplexEquivStdSimplex p x).weights i.succ = x.val i := by
  have hrot : finRotate (p + 1) i.castSucc = i.succ := finRotate_of_lt i.isLt
  rw [fullSimplexEquivStdSimplex, Homeomorph.trans_apply, Homeomorph.trans_apply,
    Homeomorph.trans_apply, ← hrot]
  simp only [Equiv.coe_stdSimplexHomeomorph, StdSimplex.weights_map,
    Finsupp.mapDomain_apply_of_injective (finRotate (p + 1)).injective,
    AbstractSimplicialComplex.realizationTopHomeomorphStdSimplex_apply,
    AbstractSimplicialComplex.realizationTopHomeomorphCoordinateSimplex_symm_castSucc]
  rfl

/-- The zeroth weight is the unused part of the coordinate sum. -/
@[simp]
theorem fullSimplexEquivStdSimplex_weights_zero {p : ℕ} (x : fullSimplex p) :
    (fullSimplexEquivStdSimplex p x).weights 0 = 1 - ∑ i, x.val i := by
  rw [fullSimplexEquivStdSimplex, Homeomorph.trans_apply, Homeomorph.trans_apply,
    Homeomorph.trans_apply, ← finRotate_last (n := p)]
  simp only [Equiv.coe_stdSimplexHomeomorph, StdSimplex.weights_map,
    Finsupp.mapDomain_apply_of_injective (finRotate (p + 1)).injective,
    AbstractSimplicialComplex.realizationTopHomeomorphStdSimplex_apply,
    AbstractSimplicialComplex.realizationTopHomeomorphCoordinateSimplex_symm_last]
  rfl

/-- The inverse bridge forgets the zeroth barycentric coordinate. -/
@[simp]
theorem fullSimplexEquivStdSimplex_symm_apply {p : ℕ}
    (w : StdSimplex ℝ (Fin (p + 1))) (i : Fin p) :
    ((fullSimplexEquivStdSimplex p).symm w).val i = w.weights i.succ := by
  rw [← fullSimplexEquivStdSimplex_weights_succ]
  simp

/-- The `i`-th face inclusion, obtained by inserting a zero barycentric weight at `i`. -/
noncomputable def simplexFace (p : ℕ) (i : Fin (p + 2)) :
    fullSimplex p → fullSimplex (p + 1) :=
  (fullSimplexEquivStdSimplex (p + 1)).symm ∘ StdSimplex.map i.succAbove ∘
    fullSimplexEquivStdSimplex p

/-- The bridge intertwines a face inclusion with the barycentric coface map. -/
theorem fullSimplexEquivStdSimplex_simplexFace {p : ℕ} (i : Fin (p + 2))
    (x : fullSimplex p) :
    fullSimplexEquivStdSimplex (p + 1) (simplexFace p i x) =
      (fullSimplexEquivStdSimplex p x).map i.succAbove := by
  exact (fullSimplexEquivStdSimplex (p + 1)).apply_symm_apply _

/-- The face inclusion preserves the weights away from its missing vertex. -/
@[simp]
theorem fullSimplexEquivStdSimplex_simplexFace_succAbove {p : ℕ} (i : Fin (p + 2))
    (x : fullSimplex p) (j : Fin (p + 1)) :
    (fullSimplexEquivStdSimplex (p + 1) (simplexFace p i x)).weights (i.succAbove j) =
      (fullSimplexEquivStdSimplex p x).weights j := by
  rw [fullSimplexEquivStdSimplex_simplexFace, StdSimplex.weights_map]
  exact Finsupp.mapDomain_apply_of_injective i.succAbove_right_injective _ _

/-- The weight at the missing vertex of a face is zero. -/
@[simp]
theorem fullSimplexEquivStdSimplex_simplexFace_self {p : ℕ} (i : Fin (p + 2))
    (x : fullSimplex p) :
    (fullSimplexEquivStdSimplex (p + 1) (simplexFace p i x)).weights i = 0 := by
  rw [fullSimplexEquivStdSimplex_simplexFace, StdSimplex.weights_map]
  exact Finsupp.mapDomain_of_notMem_range _ _ (by simp)

/-- Every face inclusion is continuous in the full-dimensional topology. -/
@[fun_prop]
theorem continuous_simplexFace (p : ℕ) (i : Fin (p + 2)) : Continuous (simplexFace p i) :=
  (fullSimplexEquivStdSimplex (p + 1)).symm.continuous.comp
    ((StdSimplex.continuous_map ℝ i.succAbove).comp
      (fullSimplexEquivStdSimplex p).continuous)

/-- The affine extension to the whole Euclidean ambient space of the map of full-dimensional
simplices induced by a map of vertices `f`. It extends the barycentric weights affinely, pushes them
forward along `f` with `FunOnFinite.linearMap`, and then drops the zeroth coordinate. -/
noncomputable def simplexMapAmbient {m n : ℕ} (f : Fin (m + 1) → Fin (n + 1)) :
    EuclideanSpace ℝ (Fin m) →ᴬ[ℝ] EuclideanSpace ℝ (Fin n) := by
  let weights : Fin (m + 1) → EuclideanSpace ℝ (Fin m) →ᴬ[ℝ] ℝ :=
    Fin.cons (ContinuousAffineMap.const ℝ _ 1 -
      (∑ k, (EuclideanSpace.proj k :
        EuclideanSpace ℝ (Fin m) →L[ℝ] ℝ)).toContinuousAffineMap)
      fun k ↦ (EuclideanSpace.proj k).toContinuousAffineMap
  let barycentric : EuclideanSpace ℝ (Fin m) →ᴬ[ℝ] (Fin (m + 1) → ℝ) := {
    toAffineMap := AffineMap.pi fun i ↦ (weights i).toAffineMap
    cont := continuous_pi fun i ↦ (weights i).continuous }
  let push : (Fin (m + 1) → ℝ) →L[ℝ] (Fin (n + 1) → ℝ) :=
    LinearMap.toContinuousLinearMap (FunOnFinite.linearMap ℝ ℝ f)
  let drop : (Fin (n + 1) → ℝ) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
    (EuclideanSpace.equiv (Fin n) ℝ).symm.toContinuousLinearMap.comp
      (ContinuousLinearMap.pi fun j ↦ ContinuousLinearMap.proj j.succ)
  exact (drop.comp push).toContinuousAffineMap.comp barycentric

/-- Each coordinate of the ambient extension is the sum of the affinely extended barycentric
weights over the vertices sent to the corresponding vertex. -/
theorem simplexMapAmbient_apply {m n : ℕ} (f : Fin (m + 1) → Fin (n + 1))
    (x : EuclideanSpace ℝ (Fin m)) (j : Fin n) :
    simplexMapAmbient f x j =
      ∑ i with f i = j.succ, Fin.cons (α := fun _ ↦ ℝ) (1 - ∑ k, x k) (fun k ↦ x k) i := by
  -- The ambient construction conjugates this coordinate map by the Euclidean/Pi equivalence.
  change FunOnFinite.linearMap ℝ ℝ f _ j.succ = _
  rw [FunOnFinite.linearMap_apply_apply]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  cases i using Fin.cases <;> simp

/-- The affine ambient extension restricts to the map of full-dimensional simplices induced by
`f`. -/
theorem simplexMapAmbient_coe {m n : ℕ} (f : Fin (m + 1) → Fin (n + 1)) (x : fullSimplex m) :
    simplexMapAmbient f x.val =
      ((fullSimplexEquivStdSimplex n).symm ((fullSimplexEquivStdSimplex m x).map f)).val := by
  ext j
  rw [simplexMapAmbient_apply, fullSimplexEquivStdSimplex_symm_apply,
    StdSimplex.weights_map_apply]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  cases i using Fin.cases <;> simp

/-- The ambient extension of the `i`-th coface vertex map restricts to the face inclusion. -/
theorem simplexMapAmbient_succAbove_coe {p : ℕ} (i : Fin (p + 2)) (x : fullSimplex p) :
    simplexMapAmbient i.succAbove x.val = (simplexFace p i x).val :=
  simplexMapAmbient_coe _ x

/-- For an injective vertex map `f`, the coordinate of the ambient extension at a vertex `f k` is
the affinely extended barycentric weight of `k`. -/
theorem simplexMapAmbient_apply_of_injective {m n : ℕ} {f : Fin (m + 1) → Fin (n + 1)}
    (hf : Function.Injective f) (x : EuclideanSpace ℝ (Fin m)) {j : Fin n} {k : Fin (m + 1)}
    (hk : f k = j.succ) :
    simplexMapAmbient f x j = Fin.cons (α := fun _ ↦ ℝ) (1 - ∑ i, x i) (fun i ↦ x i) k := by
  rw [simplexMapAmbient_apply, Finset.sum_eq_single_of_mem k (by simp [hk])]
  intro i hi hik
  exact absurd (hf ((Finset.mem_filter.1 hi).2.trans hk.symm)) hik

/-- The coordinate of the ambient extension at a vertex outside the range of the vertex map
vanishes. -/
theorem simplexMapAmbient_apply_of_forall_ne {m n : ℕ} {f : Fin (m + 1) → Fin (n + 1)}
    (x : EuclideanSpace ℝ (Fin m)) {j : Fin n} (hj : ∀ k, f k ≠ j.succ) :
    simplexMapAmbient f x j = 0 := by
  rw [simplexMapAmbient_apply]
  exact Finset.sum_eq_zero fun i hi ↦ absurd (Finset.mem_filter.1 hi).2 (hj i)

/-- The ambient extension of a map of vertices maps the full-dimensional simplex into the
full-dimensional simplex. -/
theorem mapsTo_simplexMapAmbient {m n : ℕ} (f : Fin (m + 1) → Fin (n + 1)) :
    Set.MapsTo (simplexMapAmbient f) (fullSimplex m) (fullSimplex n) := fun x hx ↦ by
  rw [show x = (⟨x, hx⟩ : fullSimplex m).val from rfl, simplexMapAmbient_coe]
  exact Subtype.prop _

/-- The ambient extension of a permutation of the vertices maps the full-dimensional simplex onto
itself. -/
theorem simplexMapAmbient_image_fullSimplex {m : ℕ} (π : Fin (m + 1) ≃ Fin (m + 1)) :
    simplexMapAmbient π '' fullSimplex m = fullSimplex m := by
  refine (mapsTo_simplexMapAmbient π).image_subset.antisymm fun z hz ↦ ?_
  set w := (fullSimplexEquivStdSimplex m).symm
    ((fullSimplexEquivStdSimplex m ⟨z, hz⟩).map π.symm)
  refine ⟨w.val, w.prop, ?_⟩
  rw [simplexMapAmbient_coe, Homeomorph.apply_symm_apply, StdSimplex.map_map]
  simp only [Equiv.apply_symm_apply]
  rw [← Function.id_def, StdSimplex.map_id, Homeomorph.symm_apply_apply]

/-- The face `δᵢ₊₁` of the simplex, opposite the vertex `eᵢ`, is the coordinate hyperplane
`xᵢ = 0`: its ambient extension inserts a zero `i`-th coordinate. -/
theorem simplexMapAmbient_succ_succAbove_eq {n : ℕ} (i : Fin (n + 1))
    (y : EuclideanSpace ℝ (Fin n)) :
    simplexMapAmbient i.succ.succAbove y = WithLp.toLp 2 (i.insertNth 0 y.ofLp) := by
  ext j
  cases j using i.succAboveCases with
  | x => simp [simplexMapAmbient_apply_of_forall_ne _ fun k ↦ Fin.succAbove_ne i.succ k]
  | p j =>
    rw [simplexMapAmbient_apply_of_injective Fin.succAbove_right_injective _
      (Fin.succ_succAbove_succ i j)]
    simp

/-- The face `δ₀` of the simplex, opposite the origin, is the slanted face `∑ xⱼ = 1`: its
ambient extension prepends the coordinate `1 - ∑ yⱼ`. -/
theorem simplexMapAmbient_succ_eq {n : ℕ} (y : EuclideanSpace ℝ (Fin n)) :
    simplexMapAmbient Fin.succ y = WithLp.toLp 2 (Fin.cons (1 - ∑ j, y j) y.ofLp) := by
  ext j
  cases j using Fin.cases with
  | zero => simp [simplexMapAmbient_apply_of_injective (Fin.succ_injective _) _ (k := 0) rfl]
  | succ j =>
    simp [simplexMapAmbient_apply_of_injective (Fin.succ_injective _) _ (k := j.succ) rfl]

/-- The derivative of the face `δᵢ₊₁` sends the basis vector `eₖ` to `e_{i.succAbove k}`. -/
@[simp]
theorem simplexMapAmbient_succ_succAbove_contLinear_single {n : ℕ} (i : Fin (n + 1))
    (k : Fin n) :
    (simplexMapAmbient i.succ.succAbove).contLinear (EuclideanSpace.single k 1) =
      EuclideanSpace.single (i.succAbove k) 1 := by
  have h := (simplexMapAmbient i.succ.succAbove).contLinear_apply_vsub
    (EuclideanSpace.single k (1 : ℝ)) 0
  rw [vsub_eq_sub, sub_zero, vsub_eq_sub] at h
  rw [h, simplexMapAmbient_succ_succAbove_eq, simplexMapAmbient_succ_succAbove_eq]
  ext j
  cases j using i.succAboveCases with
  | x => simp
  | p j => simp [PiLp.single_apply, Pi.single_apply]

/-- The derivative of the face `δ₀` sends the basis vector `eₖ` to the edge `eₖ₊₁ - e₀`. -/
@[simp]
theorem simplexMapAmbient_succ_contLinear_single {n : ℕ} (k : Fin n) :
    (simplexMapAmbient Fin.succ).contLinear (EuclideanSpace.single k 1) =
      EuclideanSpace.single k.succ 1 - EuclideanSpace.single 0 1 := by
  have h := (simplexMapAmbient Fin.succ).contLinear_apply_vsub
    (EuclideanSpace.single k (1 : ℝ)) 0
  rw [vsub_eq_sub, sub_zero, vsub_eq_sub] at h
  rw [h, simplexMapAmbient_succ_eq, simplexMapAmbient_succ_eq]
  ext j
  cases j using Fin.cases with
  | zero => simp
  | succ j => simp [PiLp.single_apply, Pi.single_apply]

end TauCeti
