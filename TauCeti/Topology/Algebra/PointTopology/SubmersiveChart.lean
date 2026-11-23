/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.Implicit
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.RingTheory.Smooth.StandardSmoothOfFree
public import Mathlib.Topology.IsLocalHomeomorph
public import TauCeti.Analysis.MvPolynomial.Jacobian
public import TauCeti.RingTheory.Extension.Presentation.Submersive
public import TauCeti.Topology.Algebra.PointTopology.Basic
public import TauCeti.Topology.Algebra.PointTopology.Localization
public import TauCeti.Topology.OpenPartialHomeomorph.Constructions
import Mathlib.Analysis.Calculus.FDeriv.Analytic

/-!
# Local charts on the points of smooth algebras

Let `K` be a complete nontrivially normed field and `P` a submersive presentation of a
`K`-algebra `S`, with finitely many variables `ι`, relations `σ`, and the injective map
`P.map : σ → ι` singling out the variables in which the Jacobian minor is taken. The values of a
point `x : S →ₐ[K] K` at the remaining variables, those outside `Set.range P.map`, are local
coordinates on the space of points with its evaluation topology: the map
`x ↦ (x (P.val i))_{i ∉ range P.map}` is a local homeomorphism into `K` to the power
`ι ∖ range P.map`. These are the smooth local parameters of `S`: by Mathlib's
`Algebra.SubmersivePresentation.basisKaehler`, the differentials of the same generators form a
basis of the Kähler differentials of `S` over `K`.

The proof applies Mathlib's implicit function theorem, `ImplicitFunctionData`, to the relations
as left function and to the coordinate projection as right function, at the coordinate vector of
the point. The two kernels are complementary because the Jacobian minor is invertible at every
point of a submersive presentation
(`Algebra.SubmersivePresentation.isUnit_det_jacobiMatrix_solution`). No hypothesis on the
characteristic of `K` is needed, and the theorem applies over `ℝ`, `ℂ` and every nonarchimedean
local field.

## Main results

* `TauCeti.exists_openPartialHomeomorph_levelSet`: on a level set of the left function of
  implicit-function data, the right function is a local homeomorphism at the base point.
* `TauCeti.isCompl_ker_mulVecLin_ker_restrict`: if a square minor of a matrix is invertible, the
  kernel of the matrix and the vectors supported on the minor's columns are complementary.
* `Algebra.SubmersivePresentation.isLocalHomeomorph_pointCoords`: the coordinates outside
  `Set.range P.map` are a local homeomorphism on the points of a submersive presentation.
* `Algebra.IsStandardSmooth.exists_openPartialHomeomorph_points` and
  `Algebra.Smooth.exists_openPartialHomeomorph_points`: every point of a standard smooth, or
  more generally smooth, `K`-algebra lies in the source of a chart, a homeomorphism from an open
  set of points onto an open subset of some `Kⁿ`. For a smooth algebra the chart comes from a
  standard smooth localization `A[1/g]` with `x g ≠ 0`, whose points form an open subset.

## References

* B. Conrad, *Weil and Grothendieck approaches to adelic points*, Enseign. Math. (2) 58 (2012),
  §4, p. 11.
* V. Platonov, A. Rapinchuk and I. Rapinchuk, *Algebraic Groups and Number Theory*, vol. 1,
  second edition, §3.1.
-/

public section

open MvPolynomial Topology

namespace TauCeti

section LevelSet

variable {𝕜 E F G : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]
  [NormedAddCommGroup G] [NormedSpace 𝕜 G] [CompleteSpace G]

/-- **Implicit function theorem on a level set.** On the level set of the left function of
implicit-function data through the base point, the right function agrees with an open partial
homeomorphism onto an open subset of `G` whose source contains the base point. -/
theorem exists_openPartialHomeomorph_levelSet (φ : ImplicitFunctionData 𝕜 E F G) {c : F}
    (hc : φ.leftFun φ.pt = c) :
    ∃ e : OpenPartialHomeomorph {x | φ.leftFun x = c} G,
      ⟨φ.pt, hc⟩ ∈ e.source ∧ ∀ x, e x = φ.rightFun x.val := by
  let Φ := φ.toOpenPartialHomeomorph
  have hΦ (x : E) : Φ x = (φ.leftFun x, φ.rightFun x) := φ.toOpenPartialHomeomorph_apply x
  have hinv : Set.LeftInvOn Prod.snd (fun g : G ↦ (c, g)) ((fun g ↦ (c, g)) ⁻¹' Φ.target) :=
    fun _ _ ↦ rfl
  refine ⟨Φ.subtypeCoord {x | φ.leftFun x = c} ⟨⟨φ.pt, hc⟩⟩ (fun g ↦ (c, g)) Prod.snd
    (fun {g} hg ↦ ?_) (fun {x} _ hx ↦ ?_) hinv
    (continuous_const.prodMk continuous_id) continuous_snd.continuousOn,
    ?_, fun x ↦ ?_⟩
  · have h := congrArg Prod.fst (Φ.right_inv hg)
    rwa [hΦ] at h
  · rw [hΦ, hx.out]
  · rw [OpenPartialHomeomorph.subtypeCoord_source]
    exact φ.pt_mem_toOpenPartialHomeomorph_source
  · rw [OpenPartialHomeomorph.subtypeCoord_apply, hΦ]

end LevelSet

section Minor

open Matrix

variable {K σ ι : Type*} [CommRing K] [Fintype σ] [Fintype ι] [DecidableEq σ]

omit [DecidableEq σ] in
/-- A matrix applied to a vector supported on the image of an injective `s` is its minor on the
columns `s` applied to the restriction of the vector. -/
private theorem mulVec_eq_submatrix_mulVec (A : Matrix σ ι K) {s : σ → ι}
    (hs : Function.Injective s) {v : ι → K} (hv : ∀ i ∉ Set.range s, v i = 0) :
    A *ᵥ v = A.submatrix id s *ᵥ (v ∘ s) := by
  ext j
  simp only [Matrix.mulVec, dotProduct, Matrix.submatrix_apply, id_eq, Function.comp_apply]
  exact (Fintype.sum_of_injective s hs _ _ (fun i hi ↦ by simp [hv i hi]) fun _ ↦ rfl).symm

/-- Extending by zero the image of `u` under the inverse of an invertible minor gives a preimage
of `u`. -/
private theorem mulVec_extend_inv_mulVec (A : Matrix σ ι K) {s : σ → ι}
    (hs : Function.Injective s) (hA : IsUnit (A.submatrix id s).det) (u : σ → K) :
    A *ᵥ Function.extend s ((A.submatrix id s)⁻¹ *ᵥ u) 0 = u := by
  have hv : ∀ i ∉ Set.range s, Function.extend s ((A.submatrix id s)⁻¹ *ᵥ u) 0 i = 0 :=
    fun i hi ↦ Function.extend_apply' _ _ _ fun ⟨j, hj⟩ ↦ hi ⟨j, hj⟩
  rw [mulVec_eq_submatrix_mulVec A hs hv, Function.extend_comp hs, Matrix.mulVec_mulVec,
    Matrix.mul_nonsing_inv _ hA, Matrix.one_mulVec]

/-- **Complementary kernels from an invertible minor.** If the minor of `A` on the columns `s` is
invertible, then the kernel of `A` and the vectors vanishing at the columns outside `range s` are
complementary subspaces. -/
theorem isCompl_ker_mulVecLin_ker_restrict (A : Matrix σ ι K) {s : σ → ι}
    (hs : Function.Injective s) (hA : IsUnit (A.submatrix id s).det) :
    IsCompl (LinearMap.ker A.mulVecLin)
      (LinearMap.ker (LinearMap.funLeft K K (Subtype.val : ↥(Set.range s)ᶜ → ι))) := by
  have hmem {v : ι → K} :
      v ∈ LinearMap.ker (LinearMap.funLeft K K (Subtype.val : ↥(Set.range s)ᶜ → ι)) ↔
        ∀ i ∉ Set.range s, v i = 0 := by
    simp only [LinearMap.mem_ker, funext_iff, LinearMap.funLeft_apply,
      Pi.zero_apply, Subtype.forall, Set.mem_compl_iff]
  constructor
  · rw [Submodule.disjoint_def]
    intro v hv hv'
    rw [hmem] at hv'
    rw [LinearMap.mem_ker, Matrix.mulVecLin_apply, mulVec_eq_submatrix_mulVec A hs hv'] at hv
    have h0 : v ∘ s = 0 := by
      simpa [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hA] using
        congrArg ((A.submatrix _root_.id s)⁻¹ *ᵥ ·) hv
    ext i
    by_cases hi : i ∈ Set.range s
    · obtain ⟨j, rfl⟩ := hi
      exact congrFun h0 j
    · exact hv' i hi
  · rw [codisjoint_iff, eq_top_iff]
    intro v _
    let w := Function.extend s ((A.submatrix id s)⁻¹ *ᵥ (A *ᵥ v)) 0
    have hw : w ∈ LinearMap.ker (LinearMap.funLeft K K (Subtype.val : ↥(Set.range s)ᶜ → ι)) :=
      hmem.2 fun i hi ↦ Function.extend_apply' _ _ _ fun ⟨j, hj⟩ ↦ hi ⟨j, hj⟩
    refine Submodule.mem_sup.2 ⟨v - w, ?_, w, hw, sub_add_cancel v w⟩
    rw [LinearMap.mem_ker, map_sub, Matrix.mulVecLin_apply, Matrix.mulVecLin_apply,
      mulVec_extend_inv_mulVec A hs hA, sub_self]

/-- A matrix with an invertible square minor is surjective. -/
theorem surjective_mulVec_of_isUnit_det_submatrix (A : Matrix σ ι K) {s : σ → ι}
    (hs : Function.Injective s) (hA : IsUnit (A.submatrix id s).det) :
    Function.Surjective A.mulVec :=
  fun u ↦ ⟨_, mulVec_extend_inv_mulVec A hs hA u⟩

end Minor

end TauCeti

namespace Algebra.SubmersivePresentation

open TauCeti TauCeti.PointTopology

section Algebra

variable {K S ι σ : Type*} [CommRing K] [CommRing S] [Algebra K S] [Finite σ]
  (P : SubmersivePresentation K S ι σ)

/-- Over the base ring itself, the coefficient restriction of a point is the identity, so the
tower evaluation at a point is plain evaluation of polynomials. -/
private theorem aevalTower_comp_eq_eval (x : S →ₐ[K] K) (p : MvPolynomial ι K) :
    aevalTower (x.comp (IsScalarTower.toAlgHom K K S)) (fun i ↦ x (P.val i)) p =
      eval (fun i ↦ x (P.val i)) p := by
  rw [Subsingleton.elim (x.comp (IsScalarTower.toAlgHom K K S)) (Algebra.ofId K K),
    MvPolynomial.aevalTower_ofId]
  rfl

/-- The coordinate vector of a point lies on the zero set of the relations. -/
private theorem eval_relation_eq_zero (x : S →ₐ[K] K) (j : σ) :
    eval (fun i ↦ x (P.val i)) (P.relation j) = 0 := by
  rw [← P.aevalTower_comp_eq_eval, P.toPresentation.aevalTower_comp_toAlgHom_val,
    P.aeval_val_relation, map_zero]

/-- At every point of a submersive presentation over the base ring, the minor of the Jacobian
matrix of the relations on the columns `P.map` is invertible. -/
private theorem isUnit_det_jacobiMatrixAt_submatrix [Fintype σ] [DecidableEq σ]
    (x : S →ₐ[K] K) :
    IsUnit ((jacobiMatrixAt P.relation fun i ↦ x (P.val i)).submatrix _root_.id P.map).det := by
  have h := P.jacobian_isUnit.map x
  rw [← P.det_jacobiMatrix_points_coordinates x] at h
  convert h using 1
  rw [← Matrix.det_transpose]
  congr 1
  ext i j
  simp [PreSubmersivePresentation.jacobiMatrix_apply, P.aevalTower_comp_eq_eval]

/-- The coordinates of a point of a submersive presentation at the variables outside the range
of `P.map`. These are the smooth local parameters, and they are local coordinates on the points
(`Algebra.SubmersivePresentation.isLocalHomeomorph_pointCoords`). -/
@[expose]
def pointCoords (x : S →ₐ[K] K) : ↥(Set.range P.map)ᶜ → K :=
  fun i ↦ x (P.val i)

variable [TopologicalSpace K] [IsTopologicalRing K]

/-- The coordinate vectors of points identify the points, with their evaluation topology, with
the zero set of the relations in `ι → K`. -/
private noncomputable def zeroSetHomeomorph :
    (S →ₐ[K] K) ≃ₜ {y : ι → K | (fun j ↦ eval y (P.relation j)) = 0} :=
  have hg : IsEmbedding fun (x : S →ₐ[K] K) (i : ι) ↦ x (P.val i) :=
    isEmbedding_eval_generators <| by
      rw [Algebra.adjoin_range_eq_range_aeval, AlgHom.range_eq_top]
      exact P.aeval_val_surjective
  hg.toHomeomorph.trans <| Homeomorph.setCongr <| by
    ext y
    have h := Set.ext_iff.mp (P.toPresentation.range_points_coordinates (k := K) (E := K))
      (Algebra.ofId K K, y)
    simp only [Set.mem_range, Prod.ext_iff, Subsingleton.elim _ (Algebra.ofId K K), true_and,
      Set.mem_ofPred_eq, MvPolynomial.aevalTower_ofId] at h
    simp only [Set.mem_ofPred_eq, funext_iff, Pi.zero_apply]
    exact h

end Algebra

variable {K S ι σ : Type*} [NontriviallyNormedField K] [CompleteSpace K] [CommRing S]
  [Algebra K S] [Finite ι] [Finite σ] (P : SubmersivePresentation K S ι σ)

section Fintype

variable [Fintype ι] [Fintype σ] [DecidableEq σ] [Fintype ↥(Set.range P.map)ᶜ]

/-- The coordinate projection onto the variables outside the range of `P.map`. -/
private noncomputable def coordProj : (ι → K) →L[K] ↥(Set.range P.map)ᶜ → K :=
  ContinuousLinearMap.pi fun i ↦ ContinuousLinearMap.proj i.val

/-- The implicit-function data at the coordinate vector of a point: the relations as left
function and the coordinate projection onto the variables outside `range P.map` as right
function. -/
private noncomputable abbrev implicitData (x : S →ₐ[K] K) :
    ImplicitFunctionData K (ι → K) (σ → K) (↥(Set.range P.map)ᶜ → K) :=
  have hπ : (P.coordProj : (ι → K) →ₗ[K] ↥(Set.range P.map)ᶜ → K) =
      LinearMap.funLeft K K Subtype.val := rfl
  have hJ := fderiv_eval_family P.relation fun i ↦ x (P.val i)
  have hA := P.isUnit_det_jacobiMatrixAt_submatrix x
  { leftFun := fun y j ↦ eval y (P.relation j)
    leftDeriv := fderiv K (fun y j ↦ eval y (P.relation j)) fun i ↦ x (P.val i)
    rightFun := P.coordProj
    rightDeriv := P.coordProj
    pt := fun i ↦ x (P.val i)
    hasStrictFDerivAt_leftFun := (analyticOnNhd_eval_family P.relation _ trivial).hasStrictFDerivAt
    hasStrictFDerivAt_rightFun := P.coordProj.hasStrictFDerivAt
    range_leftDeriv := by
      change LinearMap.range (fderiv K (fun y j ↦ eval y (P.relation j))
        (fun i ↦ x (P.val i)) : (ι → K) →ₗ[K] σ → K) = ⊤
      rw [hJ, LinearMap.range_eq_top, Matrix.coe_mulVecLin]
      exact surjective_mulVec_of_isUnit_det_submatrix _ P.map_inj hA
    range_rightDeriv := by
      change LinearMap.range (P.coordProj : (ι → K) →ₗ[K] ↥(Set.range P.map)ᶜ → K) = ⊤
      rw [hπ, LinearMap.range_eq_top]
      exact fun w ↦ ⟨Function.extend Subtype.val w 0, funext fun i ↦
        Subtype.val_injective.extend_apply w 0 i⟩
    isCompl_ker := by
      change IsCompl (LinearMap.ker (fderiv K (fun y j ↦ eval y (P.relation j))
          (fun i ↦ x (P.val i)) : (ι → K) →ₗ[K] σ → K))
        (LinearMap.ker (P.coordProj : (ι → K) →ₗ[K] ↥(Set.range P.map)ᶜ → K))
      rw [hJ, hπ]
      exact isCompl_ker_mulVecLin_ker_restrict _ P.map_inj hA }

end Fintype

/-- The implicit function theorem gives a chart at each point, computed by `pointCoords`. -/
private theorem exists_openPartialHomeomorph_pointCoords (x : S →ₐ[K] K) :
    ∃ e : OpenPartialHomeomorph (S →ₐ[K] K) (↥(Set.range P.map)ᶜ → K),
      x ∈ e.source ∧ ∀ y, e y = P.pointCoords y := by
  classical
  let := Fintype.ofFinite ι
  let := Fintype.ofFinite σ
  obtain ⟨e, he, hee⟩ : ∃ e : OpenPartialHomeomorph
      {y : ι → K | (fun j ↦ eval y (P.relation j)) = 0} (↥(Set.range P.map)ᶜ → K),
      ⟨fun i ↦ x (P.val i), funext (P.eval_relation_eq_zero x)⟩ ∈ e.source ∧
        ∀ y, e y = P.coordProj y.val :=
    exists_openPartialHomeomorph_levelSet (P.implicitData x) (c := 0)
      (funext (P.eval_relation_eq_zero x))
  refine ⟨P.zeroSetHomeomorph.toOpenPartialHomeomorph.trans e, ?_, fun y ↦ ?_⟩
  · rw [OpenPartialHomeomorph.trans_source, Homeomorph.toOpenPartialHomeomorph_source,
      Set.univ_inter, Set.mem_preimage]
    exact he
  · rw [OpenPartialHomeomorph.coe_trans, Function.comp_apply,
      Homeomorph.toOpenPartialHomeomorph_apply, hee]
    rfl

/-- **Local charts on the points of a submersive presentation.** The values of a point at the
variables outside the range of `P.map` form a local homeomorphism from the points, with their
evaluation topology, to `K` to the power `ι ∖ range P.map`. -/
theorem isLocalHomeomorph_pointCoords : IsLocalHomeomorph P.pointCoords := by
  refine IsLocalHomeomorph.mk _ fun x ↦ ?_
  obtain ⟨e, hx, he⟩ := P.exists_openPartialHomeomorph_pointCoords x
  exact ⟨e, hx, fun y _ ↦ (he y).symm⟩

end Algebra.SubmersivePresentation

namespace Algebra

open TauCeti.PointTopology

variable {K A : Type*} [NontriviallyNormedField K] [CompleteSpace K] [CommRing A] [Algebra K A]

/-- Every point of a standard smooth `K`-algebra has a chart: an open partial homeomorphism from
the points, with their evaluation topology, to some `Kⁿ`, whose source contains the point. -/
theorem IsStandardSmooth.exists_openPartialHomeomorph_points [IsStandardSmooth K A]
    (x : A →ₐ[K] K) :
    ∃ (n : ℕ) (e : OpenPartialHomeomorph (A →ₐ[K] K) (Fin n → K)), x ∈ e.source := by
  obtain ⟨ι, σ, _, _, ⟨P⟩⟩ := ‹IsStandardSmooth K A›.out
  obtain ⟨e, hx, -⟩ := P.isLocalHomeomorph_pointCoords x
  let := Fintype.ofFinite ↥(Set.range P.map)ᶜ
  exact ⟨_, e.transHomeomorph (Homeomorph.piCongrLeft (Y := fun _ ↦ K)
    (Fintype.equivFin ↥(Set.range P.map)ᶜ)), hx⟩

/-- **Local charts on the points of a smooth algebra.** Every point of a smooth `K`-algebra has
a chart: an open partial homeomorphism from the points, with their evaluation topology, to some
`Kⁿ`, whose source contains the point. The chart is a chart of a standard smooth localization
`A[1/g]` with `x g ≠ 0`, transported along the open embedding of its points. -/
theorem Smooth.exists_openPartialHomeomorph_points [Smooth K A] (x : A →ₐ[K] K) :
    ∃ (n : ℕ) (e : OpenPartialHomeomorph (A →ₐ[K] K) (Fin n → K)), x ∈ e.source := by
  obtain ⟨s, hs, hst⟩ := Smooth.exists_span_eq_top_isStandardSmooth K A
  obtain ⟨g, hg, hxg⟩ : ∃ g ∈ s, x g ≠ 0 := by
    by_contra! h
    have hle : Ideal.span s ≤ RingHom.ker x := Ideal.span_le.2 h
    have h1 : (1 : A) ∈ RingHom.ker x := hle (hs ▸ Submodule.mem_top)
    simp at h1
  have := hst g hg
  let j : (Localization.Away g →ₐ[K] K) → A →ₐ[K] K :=
    fun y ↦ y.comp (IsScalarTower.toAlgHom K A (Localization.Away g))
  have hj : IsOpenEmbedding j := isOpenEmbedding_localization g Units.isEmbedding_val₀ <| by
    simpa only [isUnit_iff_ne_zero] using isOpen_ne
  obtain ⟨y, rfl⟩ : x ∈ Set.range j := by
    rw [IsLocalization.Away.range_comp_toAlgHom g]
    exact isUnit_iff_ne_zero.2 hxg
  obtain ⟨n, e, he⟩ := IsStandardSmooth.exists_openPartialHomeomorph_points y
  have : Nonempty (Localization.Away g →ₐ[K] K) := ⟨y⟩
  refine ⟨n, (hj.toOpenPartialHomeomorph j).symm.trans e, ?_⟩
  rw [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source,
    IsOpenEmbedding.toOpenPartialHomeomorph_target, Set.mem_inter_iff, Set.mem_preimage,
    hj.toOpenPartialHomeomorph_left_inv]
  exact ⟨Set.mem_range_self y, he⟩

end Algebra
