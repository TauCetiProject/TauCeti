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
public import Mathlib.GroupTheory.Perm.Fin
import Mathlib.LinearAlgebra.Finsupp.Pi
import TauCeti.Geometry.Convex.ConvexSpace.Defs
import TauCeti.Topology.Algebra.Module.FiniteDimension

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
coface vertex maps `Fin.succAbove`. In coordinates, the face map omitting the vertex `e_j` inserts a
zero `j`-th coordinate, and the face map omitting the origin puts the missing barycentric weight in
front; a permutation of the vertices induces an affine symmetry of the simplex. Cycling the
vertices relates the two readings of the face opposite the origin: through the coordinates other
than the `j`-th one, and through the last coordinates as the face map does. The simplex is a
compact convex set with nonempty interior, so derivatives within it are unique at every point
(`TauCeti.uniqueDiffOn_fullSimplex`); this is what makes it a domain for derivatives and integrals
of forms. The face maps are injective, hence closed embeddings of the ambient Euclidean spaces
(`TauCeti.isClosedEmbedding_simplexMapAmbient_succAbove`), so pulling back along them preserves
compact supports.

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

/-- The point of `ℝᵖ⁺¹` obtained by inserting `t` as the `j`-th coordinate of `y` lies in the
full-dimensional simplex exactly when `y` lies in the coordinate simplex and `t` lies between `0`
and the unused part `1 - ∑ k, y k` of the coordinate sum. -/
theorem toLp_insertNth_mem_fullSimplex_iff {p : ℕ} (j : Fin (p + 1)) (t : ℝ) (y : Fin p → ℝ) :
    WithLp.toLp 2 (j.insertNth t y) ∈ fullSimplex (p + 1) ↔
      y ∈ coordinateSimplex (Fin p) ∧ t ∈ Set.Icc 0 (1 - ∑ k, y k) := by
  simp only [mem_fullSimplex_iff, mem_coordinateSimplex, Set.mem_Icc, j.forall_iff_succAbove,
    Fin.sum_univ_succAbove _ j, Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove]
  constructor
  · rintro ⟨⟨ht, hy⟩, hs⟩; exact ⟨⟨hy, by linarith⟩, ht, by linarith⟩
  · rintro ⟨⟨hy, -⟩, ht, hs⟩; exact ⟨⟨ht, hy⟩, by linarith⟩

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

/-- The ambient extension of a vertex map carries the full-dimensional simplex into the
full-dimensional simplex. -/
theorem mapsTo_simplexMapAmbient {m n : ℕ} (f : Fin (m + 1) → Fin (n + 1)) :
    Set.MapsTo (simplexMapAmbient f) (fullSimplex m) (fullSimplex n) := fun x hx ↦
  simplexMapAmbient_coe f ⟨x, hx⟩ ▸ Subtype.prop _

/-- For an injective vertex map `f`, a coordinate of the ambient extension is the affinely extended
barycentric weight of the unique vertex sent to the corresponding vertex. -/
theorem simplexMapAmbient_apply_of_injective {m n : ℕ} {f : Fin (m + 1) → Fin (n + 1)}
    (hf : Function.Injective f) (x : EuclideanSpace ℝ (Fin m)) {i : Fin (m + 1)} {j : Fin n}
    (h : f i = j.succ) :
    simplexMapAmbient f x j = Fin.cons (α := fun _ ↦ ℝ) (1 - ∑ k, x k) (fun k ↦ x k) i := by
  rw [simplexMapAmbient_apply, ← h]
  simp [hf.eq_iff, Finset.filter_eq']

/-- A coordinate of the ambient extension whose vertex is not in the range of the vertex map
vanishes. -/
theorem simplexMapAmbient_apply_of_forall_ne {m n : ℕ} {f : Fin (m + 1) → Fin (n + 1)}
    (x : EuclideanSpace ℝ (Fin m)) {j : Fin n} (h : ∀ i, f i ≠ j.succ) :
    simplexMapAmbient f x j = 0 := by
  rw [simplexMapAmbient_apply]
  simp [h]

/-- The ambient extension of a permutation of the vertices maps the full-dimensional simplex onto
itself. -/
theorem image_simplexMapAmbient_perm {m : ℕ} (σ : Equiv.Perm (Fin (m + 1))) :
    simplexMapAmbient σ '' fullSimplex m = fullSimplex m := by
  refine Set.Subset.antisymm (mapsTo_simplexMapAmbient σ).image_subset fun z hz ↦ ?_
  let w := (fullSimplexEquivStdSimplex m ⟨z, hz⟩).map σ.symm
  refine ⟨((fullSimplexEquivStdSimplex m).symm w).val, Subtype.prop _, ?_⟩
  simp only [w, simplexMapAmbient_coe, Homeomorph.apply_symm_apply, StdSimplex.map_map,
    Equiv.apply_symm_apply]
  exact congrArg Subtype.val ((congrArg _ (StdSimplex.map_id _)).trans
    ((fullSimplexEquivStdSimplex m).symm_apply_apply _))

/-! ### The faces in coordinates -/

section Faces

variable {p : ℕ}

/-- The face map of `Δᵖ⁺¹` omitting the vertex `e_j` inserts a zero `j`-th coordinate. -/
theorem simplexMapAmbient_succAbove_succ (j : Fin (p + 1))
    (y : EuclideanSpace ℝ (Fin p)) :
    simplexMapAmbient j.succ.succAbove y = WithLp.toLp 2 (j.insertNth 0 y.ofLp) := by
  ext m
  refine j.succAboveCases ?_ (fun k ↦ ?_) m
  · rw [simplexMapAmbient_apply_of_forall_ne _ fun i ↦ Fin.succAbove_ne j.succ i]
    simp
  · rw [simplexMapAmbient_apply_of_injective (Fin.succAbove_right_injective) _
      (Fin.succ_succAbove_succ j k)]
    simp

/-- The face map of `Δᵖ⁺¹` omitting the origin keeps the coordinates of `y` as the last `p`
coordinates and puts the missing barycentric weight `1 - ∑ k, y k` in front. -/
theorem simplexMapAmbient_succAbove_zero (y : EuclideanSpace ℝ (Fin p)) :
    simplexMapAmbient (Fin.succAbove 0) y =
      WithLp.toLp 2 (Fin.cons (α := fun _ ↦ ℝ) (1 - ∑ k, y k) y.ofLp) := by
  ext m
  rw [simplexMapAmbient_apply_of_injective (Fin.succAbove_right_injective) _
    (Fin.succAbove_zero_apply m)]

/-- The affine symmetry of `Δᵖ` cycling the vertices `0, …, j` reads the face of `Δᵖ⁺¹` opposite
the origin in the coordinates obtained by deleting the `j`-th one. -/
theorem simplexMapAmbient_cycleRange_symm (j : Fin (p + 1)) (y : EuclideanSpace ℝ (Fin p)) :
    simplexMapAmbient j.cycleRange.symm y =
      WithLp.toLp 2 fun k ↦ (j.insertNth (1 - ∑ k, y k) y.ofLp : Fin (p + 1) → ℝ) k.succ := by
  ext m
  rw [simplexMapAmbient_apply_of_injective j.cycleRange.symm.injective _
    (j.cycleRange.symm_apply_apply m.succ)]
  simp

/-- The point of the face of `Δᵖ⁺¹` opposite the origin whose coordinates other than the `j`-th are
those of `y` is the image under the face map of the cycled point of `Δᵖ`. -/
theorem toLp_insertNth_eq_simplexMapAmbient (j : Fin (p + 1)) (y : EuclideanSpace ℝ (Fin p)) :
    WithLp.toLp 2 (j.insertNth (1 - ∑ k, y k) y.ofLp) =
      simplexMapAmbient (Fin.succAbove 0) (simplexMapAmbient j.cycleRange.symm y) := by
  rw [simplexMapAmbient_succAbove_zero, simplexMapAmbient_cycleRange_symm]
  set x : Fin (p + 1) → ℝ := j.insertNth (1 - ∑ k, y k) y.ofLp
  have hx : ∑ i, x i = 1 := by
    simp [x, Fin.sum_univ_succAbove _ j]
  rw [Fin.sum_univ_succ] at hx
  ext m
  cases m using Fin.cases <;> simp [← hx]

/-- The linear part of the face map omitting the vertex `e_j` sends `e_k` to `e_{j.succAbove k}`.
-/
theorem contLinear_simplexMapAmbient_succAbove_succ (j : Fin (p + 1)) (k : Fin p) :
    (simplexMapAmbient j.succ.succAbove).contLinear (EuclideanSpace.single k 1) =
      EuclideanSpace.single (j.succAbove k) 1 := by
  have h := (simplexMapAmbient j.succ.succAbove).contLinear_apply_vsub
    (EuclideanSpace.single k (1 : ℝ)) 0
  rw [vsub_eq_sub, vsub_eq_sub, sub_zero] at h
  rw [h, simplexMapAmbient_succAbove_succ, simplexMapAmbient_succAbove_succ]
  ext m
  refine j.succAboveCases ?_ (fun l ↦ ?_) m
  · simp
  · simp [Pi.single_apply]

/-- The linear part of the face map omitting the origin sends `e_k` to the edge vector
`e_{k+1} - e_0`. -/
theorem contLinear_simplexMapAmbient_succAbove_zero (k : Fin p) :
    (simplexMapAmbient (Fin.succAbove 0)).contLinear (EuclideanSpace.single k 1) =
      EuclideanSpace.single k.succ 1 - EuclideanSpace.single 0 1 := by
  have h := (simplexMapAmbient (Fin.succAbove (0 : Fin (p + 2)))).contLinear_apply_vsub
    (EuclideanSpace.single k (1 : ℝ)) 0
  rw [vsub_eq_sub, vsub_eq_sub, sub_zero] at h
  rw [h, simplexMapAmbient_succAbove_zero, simplexMapAmbient_succAbove_zero]
  ext m
  cases m using Fin.cases <;> simp [Pi.single_apply]

/-- The face maps of `Δᵖ⁺¹` are injective. -/
theorem simplexMapAmbient_succAbove_injective (i : Fin (p + 2)) :
    Function.Injective (simplexMapAmbient (m := p) i.succAbove) := by
  intro y z h
  cases i using Fin.cases with
  | zero =>
    rw [simplexMapAmbient_succAbove_zero, simplexMapAmbient_succAbove_zero] at h
    ext k
    simpa using congrArg (· k.succ) h
  | succ j =>
    rw [simplexMapAmbient_succAbove_succ, simplexMapAmbient_succAbove_succ] at h
    ext k
    simpa using congrArg (· (j.succAbove k)) h

/-- The face maps of `Δᵖ⁺¹` are closed embeddings, so preimages of compact sets under them are
compact. -/
theorem isClosedEmbedding_simplexMapAmbient_succAbove (i : Fin (p + 2)) :
    Topology.IsClosedEmbedding (simplexMapAmbient (m := p) i.succAbove) :=
  ContinuousAffineMap.isClosedEmbedding_of_injective (simplexMapAmbient_succAbove_injective i)

end Faces

end TauCeti
