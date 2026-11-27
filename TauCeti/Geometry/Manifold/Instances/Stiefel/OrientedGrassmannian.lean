/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Module
public import TauCeti.Geometry.Manifold.GroupAction.Quotient
public import TauCeti.Geometry.Manifold.Instances.Stiefel.Homogeneous
public import TauCeti.Geometry.Manifold.Instances.Stiefel.LinearIsometry
public import TauCeti.Geometry.Manifold.Instances.Unitary.Special
public import TauCeti.Topology.Grassmannian.Oriented
import Mathlib.Analysis.InnerProductSpace.Orientation
import TauCeti.Data.Nat.Choose.Basic
import TauCeti.Geometry.Lie.Subgroup.Unitary.SpecialOrthogonal
import TauCeti.LinearAlgebra.ExteriorPower.Basis
import TauCeti.Topology.Homeomorph.Quotient

/-!
# The oriented Grassmannian as a Stiefel quotient

The special orthogonal group changes the orthonormal basis of a plane by a rotation.
With frame vectors written as rows, this is a left action by matrix multiplication.
With the vectors written as columns, it is the right action by the transpose.

The action is free, smooth and proper, so the space of orbits is a smooth manifold and
the Stiefel projection onto it is a submersion. The charts use
`ProperSMul.orbitRelQuotientChartedSpace` and the native Lie group structure on
`Matrix.specialUnitaryGroup` over the reals.

The orbits are exactly the fibres of the map taking a frame to its span with the
orientation of its ordered basis. An isometric choice of coordinates identifies the
quotient with the existing `TauCeti.finiteOrientedGrassmannian`, so the projection
that forgets orientation in those coordinates is a two-sheeted covering.
In rank zero the oriented subspace carrier has two signs, and only the positive
sign is the span of an orthonormal frame.

## References

* A. Hatcher, *Vector Bundles and K-Theory*, §1.2, for the Stiefel description of the
  oriented Grassmannian.
-/

public section

noncomputable section

open Manifold Matrix Module Topology
open scoped ContDiff InnerProductSpace Manifold

namespace TauCeti

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] {k N : ℕ}

namespace stiefel

/-- Special orthogonal matrices act on orthonormal frames by multiplying their matrix of
row vectors on the left. -/
instance instMulActionSpecialOrthogonalGroup :
    MulAction (specialOrthogonalGroup (Fin k) ℝ) (stiefel E k) := by
  letI : Module (Matrix (Fin k) (Fin k) ℝ) (Fin k → E) := Matrix.Module.matrixModule
  letI : MulAction (specialOrthogonalGroup (Fin k) ℝ) (Fin k → E) :=
    MulAction.compHom _ (specialOrthogonalGroup (Fin k) ℝ).subtype
  letI : SMul (specialOrthogonalGroup (Fin k) ℝ) (stiefel E k) :=
    ⟨fun A v ↦ ⟨A • v.val, mem_stiefel_iff.2 <|
      ((mem_stiefel_iff.1 v.property).orthonormal_sum_smul_iff_mem_unitaryGroup _).2
        (mem_specialUnitaryGroup_iff.1 A.property).1⟩⟩
  exact Subtype.val_injective.mulAction Subtype.val fun _ _ ↦ rfl

/-- The vectors after a change of orthonormal basis have the corresponding matrix coefficients. -/
@[simp]
theorem coe_specialOrthogonalGroup_smul (A : specialOrthogonalGroup (Fin k) ℝ)
    (v : stiefel E k) (j : Fin k) :
    (A • v).val j = ∑ i, A.val j i • v.val i :=
  (rfl)

/-- The action on the indices of an orthonormal frame is free. -/
instance instIsCancelSMulSpecialOrthogonalGroup :
    IsCancelSMul (specialOrthogonalGroup (Fin k) ℝ) (stiefel E k) :=
  isCancelSMul_iff_eq_one_of_smul_eq.2 fun {A v} h ↦ by
    have hv := mem_stiefel_iff.1 v.property
    apply Subtype.ext
    ext j i
    have hi := congrArg (fun w : stiefel E k ↦ ⟪v.val i, w.val j⟫_ℝ) h
    simpa [hv.inner_right_fintype, orthonormal_iff_ite.1 hv, Matrix.one_apply, eq_comm] using hi

/-- Applying a linear isometric equivalence to each vector commutes with rotating the frame. -/
@[simp]
theorem _root_.LinearIsometryEquiv.stiefelHomeomorph_specialOrthogonalGroup_smul (e : E ≃ₗᵢ[ℝ] F)
    (A : specialOrthogonalGroup (Fin k) ℝ) (v : stiefel E k) :
    e.stiefelHomeomorph k (A • v) = A • e.stiefelHomeomorph k v :=
  Subtype.ext <| funext fun j ↦ by
    simp [map_smul, map_sum]

/-- Reading the vectors in Euclidean coordinates commutes with rotating the frame. -/
@[simp]
theorem finiteOrthonormalFrameHomeomorph_specialOrthogonalGroup_smul
    (A : specialOrthogonalGroup (Fin k) ℝ) (v : stiefel (EuclideanSpace ℝ (Fin N)) k) :
    finiteOrthonormalFrameHomeomorph k N (A • v) =
      A • finiteOrthonormalFrameHomeomorph k N v := by
  refine Subtype.ext (funext fun j ↦ ?_)
  rw [finiteOrthonormalFrame.specialUnitaryGroup_smul_def]
  simp [WithLp.ofLp_sum, WithLp.ofLp_smul]

section Smooth

open scoped Matrix.Norms.L2Operator
attribute [local instance] Matrix.l2OpNormedAlgebraReal

variable [FiniteDimensional ℝ E]

local notation "SO(" k ")" => specialOrthogonalGroup (Fin k) ℝ
local notation "𝓢𝓞(" k ")" => specialUnitaryGroup.model (Fin k) ℝ
local notation "𝓥(" E ", " k ")" => 𝓘(ℝ, Fin (k * finrank ℝ E - Nat.choose (k + 1) 2) → ℝ)

/-- Changing the orthonormal basis is jointly smooth in the matrix and the frame. -/
instance instContMDiffSMulSpecialOrthogonalGroup :
    ContMDiffSMul 𝓢𝓞(k) 𝓥(E, k) ∞ (SO(k)) (stiefel E k) where
  contMDiff_smul := by
    refine ContMDiff.codRestrict_stiefel (g := fun p : SO(k) × stiefel E k ↦
      fun j ↦ ∑ i, p.1.val j i • p.2.val i) ?_ (fun p ↦ (p.1 • p.2).property)
    have hA := (specialUnitaryGroup.contMDiff_val (n := Fin k) (𝕜 := ℝ)).comp
      (contMDiff_fst (I := 𝓢𝓞(k)) (J := 𝓥(E, k)) (M := SO(k)) (N := stiefel E k))
    have hv := (contMDiff_coe_stiefel E k (r := ∞)).comp
      (contMDiff_snd (I := 𝓢𝓞(k)) (J := 𝓥(E, k)) (M := SO(k)) (N := stiefel E k))
    refine contMDiff_pi_module_iff.2 fun j ↦ ContMDiff.sum fun i _ ↦ ?_
    exact (((Matrix.entryLinearMap ℝ ℝ j i).toContinuousLinearMap).contMDiff.comp hA).smul
      (contMDiff_pi_module_iff.1 hv i)

end Smooth

/-- The change-of-basis action on the Stiefel manifold is proper since the special orthogonal
group is compact and its action is continuous. -/
instance instProperSMulSpecialOrthogonalGroup :
    ProperSMul (specialOrthogonalGroup (Fin k) ℝ) (stiefel E k) := by
  let : ContinuousSMul (specialOrthogonalGroup (Fin k) ℝ) (stiefel E k) := ⟨by
    refine continuous_induced_rng.2 (continuous_pi fun j ↦ ?_)
    simp only [Function.comp_def, coe_specialOrthogonalGroup_smul]
    exact continuous_finsetSum _ fun i _ ↦
      ((continuous_subtypeVal.comp continuous_fst).matrix_elem j i).smul
        ((continuous_apply i).comp (continuous_subtypeVal.comp continuous_snd))⟩
  exact properSMul_of_compactSpace _ _

end stiefel

/-- The oriented Grassmannian of positive rank as the space of orthonormal frames modulo
positive orthogonal changes of basis. -/
abbrev orientedGrassmannian (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (r : ℕ+) :=
  MulAction.orbitRel.Quotient (specialOrthogonalGroup (Fin r) ℝ) (stiefel E r)

/-- An oriented subspace of a finite-dimensional space is a subspace of the specified
dimension together with an orientation on that subspace. -/
abbrev OrientedSubspace (E : Type*) [AddCommGroup E] [Module ℝ E] (k : ℕ) :=
  (P : {P : Submodule ℝ E // finrank ℝ P = k}) × Orientation ℝ P.val (Fin k)

/-- In rank zero the oriented planes are the two orientations of the zero subspace. -/
theorem encard_univ_orientedSubspace_zero [FiniteDimensional ℝ E] :
    (Set.univ : Set (OrientedSubspace E 0)).encard = 2 := by
  let P : {P : Submodule ℝ E // finrank ℝ P = 0} := ⟨⊥, by simp⟩
  let o : Orientation ℝ P.val (Fin 0) := positiveOrientation
  let p : OrientedSubspace E 0 := ⟨P, o⟩
  let q : OrientedSubspace E 0 := ⟨P, -o⟩
  have hpq : p ≠ q := fun h ↦ Module.Ray.ne_neg_self o (eq_of_heq (Sigma.mk.inj h).2)
  have h : (Set.univ : Set (OrientedSubspace E 0)) = {p, q} := by
    refine Set.Subset.antisymm (fun x _ ↦ ?_) (Set.subset_univ _)
    obtain ⟨⟨Q, hQ⟩, o'⟩ := x
    have hQ' : Q = ⊥ := Submodule.finrank_eq_zero.1 hQ
    subst Q
    rcases o'.eq_or_eq_neg_of_isEmpty with ho | ho
    · exact Set.mem_insert_iff.2 (Or.inl (Sigma.ext rfl (heq_of_eq ho)))
    · exact Set.mem_insert_of_mem _ (Set.mem_singleton_iff.2 (Sigma.ext rfl (heq_of_eq ho)))
  rw [h, Set.encard_pair hpq]

namespace stiefel

open Set Submodule

/-- An orthonormal frame gives an orthonormal basis of its span. A specified equality of spans
lets two such bases be compared in the same subspace. -/
def orthonormalBasisOfSpanEq (v : stiefel E k) {P : Submodule ℝ E}
    (hP : span ℝ (range v.val) = P) : OrthonormalBasis (Fin k) ℝ P := by
  subst P
  let hv := mem_stiefel_iff.1 v.property
  exact (Module.Basis.span hv.linearIndependent).toOrthonormalBasis <|
    (span ℝ (range v.val)).subtypeₗᵢ.orthonormal_comp_iff.1 <| by
      simpa [Function.comp_def] using hv

/-- The basis of the span has the vectors of the original frame. -/
@[simp]
theorem coe_orthonormalBasisOfSpanEq_apply (v : stiefel E k) {P : Submodule ℝ E}
    (hP : span ℝ (range v.val) = P) (j : Fin k) :
    (orthonormalBasisOfSpanEq v hP j : E) = v.val j := by
  subst P
  simp [orthonormalBasisOfSpanEq]

/-- The span of an orthonormal frame has dimension equal to the number of its vectors. -/
@[simp]
theorem finrank_span_range (v : stiefel E k) :
    finrank ℝ (span ℝ (range v.val)) = k := by
  simpa using finrank_span_eq_card (mem_stiefel_iff.1 v.property).linearIndependent

/-- The span of a frame with the orientation given by its ordered basis. -/
def orientedSpan (v : stiefel E k) : OrientedSubspace E k :=
  ⟨⟨span ℝ (range v.val), finrank_span_range v⟩,
    (orthonormalBasisOfSpanEq v rfl).toBasis.orientation⟩

/-- The underlying plane of the oriented span is the span of the frame vectors. -/
@[simp]
theorem coe_fst_orientedSpan (v : stiefel E k) :
    (orientedSpan v).1.val = span ℝ (range v.val) :=
  (rfl)

/-- The empty frame induces the positive orientation of its zero-dimensional span. -/
@[simp]
theorem orientation_orientedSpan_zero (v : stiefel E 0) :
    (orientedSpan v).2 = positiveOrientation :=
  (orthonormalBasisOfSpanEq v rfl).toBasis.orientation_isEmpty

/-- Write the oriented span using a specified subspace spanned by the frame. -/
theorem orientedSpan_eq_mk (v : stiefel E k) (P : {P : Submodule ℝ E // finrank ℝ P = k})
    (hP : span ℝ (range v.val) = P.val) :
    orientedSpan v = ⟨P, (orthonormalBasisOfSpanEq v hP).toBasis.orientation⟩ := by
  obtain ⟨P, hdim⟩ := P
  simp only at hP
  subst P
  rfl

/-- At positive rank every orientation of a plane is realized by an orthonormal basis. -/
theorem surjective_orientedSpan [NeZero k] :
    Function.Surjective (orientedSpan : stiefel E k → OrientedSubspace E k) := by
  rintro ⟨⟨P, hdim⟩, o⟩
  let : FiniteDimensional ℝ P := Module.finite_of_finrank_pos (hdim ▸ Nat.pos_of_ne_zero
    (NeZero.ne k))
  let b := ((stdOrthonormalBasis ℝ P).reindex (finCongr hdim)).adjustToOrientation o
  let v : stiefel E k := ⟨fun i ↦ (b i : E), mem_stiefel_iff.2
    (b.orthonormal.comp_linearIsometry P.subtypeₗᵢ)⟩
  have hP : span ℝ (range v.val) = P := by
    rw [← Submodule.range_subtype P, ← Submodule.map_top, ← b.toBasis.span_eq,
      ← Submodule.span_image, ← Set.range_comp]
    rfl
  have hb : (orthonormalBasisOfSpanEq v hP).toBasis = b.toBasis := by
    ext i : 1
    exact Subtype.ext (coe_orthonormalBasisOfSpanEq_apply _ _ _)
  refine ⟨v, ?_⟩
  rw [orientedSpan_eq_mk v ⟨P, hdim⟩ hP, hb,
    OrthonormalBasis.orientation_adjustToOrientation]

/-- A rotation of the frame preserves the underlying subspace. -/
theorem span_range_specialOrthogonalGroup_smul (A : specialOrthogonalGroup (Fin k) ℝ)
    (v : stiefel E k) : span ℝ (range (A • v).val) = span ℝ (range v.val) := by
  let : FiniteDimensional ℝ (span ℝ (range v.val)) :=
    FiniteDimensional.span_of_finite ℝ (finite_range _)
  refine Submodule.eq_of_le_of_finrank_le (span_le.2 ?_) (by simp)
  rintro _ ⟨i, rfl⟩
  rw [coe_specialOrthogonalGroup_smul]
  exact Submodule.sum_mem _ fun j _ ↦ smul_mem _ _ (subset_span (mem_range_self j))

/-- A rotation of the frame preserves the induced orientation. -/
@[simp]
theorem orientedSpan_specialOrthogonalGroup_smul (A : specialOrthogonalGroup (Fin k) ℝ)
    (v : stiefel E k) : orientedSpan (A • v) = orientedSpan v := by
  let P : {P : Submodule ℝ E // finrank ℝ P = k} := ⟨_, finrank_span_range v⟩
  let b := orthonormalBasisOfSpanEq v rfl
  let c := orthonormalBasisOfSpanEq (A • v) (span_range_specialOrthogonalGroup_smul A v)
  have hc : (c.toBasis : Fin k → P.val) = fun j ↦ ∑ i, A.val j i • b.toBasis i := by
    funext j
    exact Subtype.ext (by simp [b, c])
  have hdet : b.toBasis.det c.toBasis = 1 := by
    rw [hc, AlternatingMap.map_sum_smul, Module.Basis.det_self, smul_eq_mul, mul_one]
    exact (mem_specialUnitaryGroup_iff.1 A.property).2
  have hor : b.toBasis.orientation = c.toBasis.orientation :=
    (b.toBasis.orientation_eq_iff_det_pos c.toBasis).2 (hdet ▸ zero_lt_one)
  rw [orientedSpan_eq_mk v P rfl,
    orientedSpan_eq_mk (A • v) P (span_range_specialOrthogonalGroup_smul A v), ← hor]

/-- Two orthonormal frames have equal oriented spans exactly when they are related by a
special orthogonal change of basis. -/
theorem orientedSpan_eq_iff {v w : stiefel E k} :
    orientedSpan v = orientedSpan w ↔ w ∈ MulAction.orbit (specialOrthogonalGroup (Fin k) ℝ) v := by
  refine ⟨fun h ↦ ?_, ?_⟩
  · let P : {P : Submodule ℝ E // finrank ℝ P = k} := ⟨_, finrank_span_range v⟩
    have hw : span ℝ (range w.val) = P.val :=
      congrArg (fun p : OrientedSubspace E k ↦ p.1.val) h.symm
    let b := orthonormalBasisOfSpanEq v (P := P.val) rfl
    let c := orthonormalBasisOfSpanEq w hw
    have hor : b.toBasis.orientation = c.toBasis.orientation := by
      rw [orientedSpan_eq_mk v P rfl, orientedSpan_eq_mk w P hw] at h
      exact eq_of_heq (Sigma.mk.inj h).2
    let A := (b.toBasis.toMatrix c.toBasis)ᵀ
    have hAv (j : Fin k) : ∑ i, A j i • v.val i = w.val j := by
      have hj := congrArg P.val.subtype (b.toBasis.sum_repr (c.toBasis j))
      simpa only [A, Matrix.transpose_apply, Module.Basis.toMatrix_apply, map_sum, map_smul,
        Submodule.subtype_apply, OrthonormalBasis.coe_toBasis, b, c,
        coe_orthonormalBasisOfSpanEq_apply] using hj
    have hu : A ∈ unitaryGroup (Fin k) ℝ :=
      ((mem_stiefel_iff.1 v.property).orthonormal_sum_smul_iff_mem_unitaryGroup A).1
        ((funext hAv).symm ▸ mem_stiefel_iff.1 w.property)
    have hd : A.det = 1 := by
      rw [Matrix.det_transpose, ← Module.Basis.det_apply]
      exact b.det_to_matrix_orthonormalBasis_of_same_orientation c hor
    exact ⟨⟨A, mem_specialUnitaryGroup_iff.2 ⟨hu, hd⟩⟩,
      Subtype.ext (funext fun j ↦ (coe_specialOrthogonalGroup_smul _ _ _).trans (hAv j))⟩
  · rintro ⟨A, rfl⟩
    exact (orientedSpan_specialOrthogonalGroup_smul A v).symm

end stiefel

namespace orientedGrassmannian

variable {r : ℕ+}

/-- Send a frame to the oriented plane it spans. -/
def ofFrame (v : stiefel E r) : orientedGrassmannian E r :=
  Quotient.mk _ v

/-- Two frames determine the same oriented plane exactly when a rotation carries one to the
other. -/
theorem ofFrame_eq_iff {v w : stiefel E r} :
    ofFrame v = ofFrame w ↔ w ∈ MulAction.orbit (specialOrthogonalGroup (Fin r) ℝ) v :=
  Quotient.eq''.trans (MulAction.orbitRel_apply.trans MulAction.mem_orbit_symm)

/-- The projection from frames is an open quotient map for the rotation action. -/
theorem isOpenQuotientMap_ofFrame :
    IsOpenQuotientMap (ofFrame : stiefel E r → orientedGrassmannian E r) :=
  MulAction.isOpenQuotientMap_quotientMk

theorem surjective_ofFrame :
    Function.Surjective (ofFrame : stiefel E r → orientedGrassmannian E r) :=
  isOpenQuotientMap_ofFrame.surjective

@[fun_prop]
theorem continuous_ofFrame : Continuous (ofFrame : stiefel E r → orientedGrassmannian E r) :=
  isOpenQuotientMap_ofFrame.continuous

/-- The Stiefel quotient identifies intrinsically with the rank-`r` subspaces equipped with
an orientation. -/
def orientedSubspaceEquiv : orientedGrassmannian E r ≃ OrientedSubspace E r := by
  let f : orientedGrassmannian E r → OrientedSubspace E r :=
    Quotient.lift stiefel.orientedSpan fun v w h ↦
      stiefel.orientedSpan_eq_iff.2 (MulAction.mem_orbit_symm.1 (MulAction.orbitRel_apply.1 h))
  refine Equiv.ofBijective f ⟨?_, ?_⟩
  · intro p q
    induction p using Quotient.inductionOn with
    | _ v =>
      induction q using Quotient.inductionOn with
      | _ w => exact fun h ↦ ofFrame_eq_iff.2 (stiefel.orientedSpan_eq_iff.1 h)
  · intro p
    have : NeZero (r : ℕ) := ⟨r.ne_zero⟩
    obtain ⟨v, hv⟩ := stiefel.surjective_orientedSpan p
    exact ⟨ofFrame v, hv⟩

/-- The oriented subspace represented by a frame is its span with the frame's orientation. -/
@[simp]
theorem orientedSubspaceEquiv_ofFrame (v : stiefel E r) :
    orientedSubspaceEquiv (ofFrame v) = stiefel.orientedSpan v :=
  (rfl)

private def coordinateFrameHomeomorph (e : E ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin N)) :
    stiefel E r ≃ₜ finiteOrthonormalFrame ℝ r N :=
  (e.stiefelHomeomorph r).trans (stiefel.finiteOrthonormalFrameHomeomorph r N)

private theorem coordinateFrameHomeomorph_smul (e : E ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin N))
    (A : specialOrthogonalGroup (Fin r) ℝ) (v : stiefel E r) :
    coordinateFrameHomeomorph e (A • v) = A • coordinateFrameHomeomorph e v := by
  simp [coordinateFrameHomeomorph]

private theorem coordinateFrameHomeomorph_mem_orbit (e : E ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin N))
    {v w : stiefel E r} :
    coordinateFrameHomeomorph e w ∈ MulAction.orbit (specialOrthogonalGroup (Fin r) ℝ)
      (coordinateFrameHomeomorph e v) ↔
        w ∈ MulAction.orbit (specialOrthogonalGroup (Fin r) ℝ) v := by
  constructor
  · rintro ⟨A, hA⟩
    exact ⟨A, (coordinateFrameHomeomorph e).injective
      ((coordinateFrameHomeomorph_smul e A v).trans hA)⟩
  · rintro ⟨A, rfl⟩
    exact ⟨A, (coordinateFrameHomeomorph_smul e A v).symm⟩

/-- An isometric choice of coordinates identifies the Stiefel quotient with the orientation
double cover of the finite coordinate Grassmannian. -/
def finiteOrientedGrassmannianHomeomorph (e : E ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin N)) :
    orientedGrassmannian E r ≃ₜ finiteOrientedGrassmannian r N :=
  (Homeomorph.Quotient.congr (coordinateFrameHomeomorph e) fun _ _ ↦
    MulAction.orbitRel_apply.trans <| (coordinateFrameHomeomorph_mem_orbit e).symm.trans
      MulAction.orbitRel_apply.symm).trans
    (finiteOrientedGrassmannian.specialOrthogonalOrbitHomeomorph r N)

/-- In isometric coordinates the image of a frame is its oriented coordinate span. -/
@[simp]
theorem finiteOrientedGrassmannianHomeomorph_ofFrame (e : E ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin N))
    (v : stiefel E r) :
    finiteOrientedGrassmannianHomeomorph e (ofFrame v) =
      finiteOrientedGrassmannian.orientedFrameSpan
        (stiefel.finiteOrthonormalFrameHomeomorph r N
          (e.stiefelHomeomorph r v)).toFullRankFrame := by
  simp [finiteOrientedGrassmannianHomeomorph, ofFrame, coordinateFrameHomeomorph]

/-- In any choice of isometric coordinates, forgetting orientation is a covering map. -/
theorem isCoveringMap_forget_comp (e : E ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin N)) :
    IsCoveringMap ((finiteOrientedGrassmannian.forget :
      finiteOrientedGrassmannian r N → finiteGrassmannian ℝ r N) ∘
        finiteOrientedGrassmannianHomeomorph e) :=
  (VectorBundleOrientationCover.isCoveringMap_proj (by simp)).comp_homeomorph
    (finiteOrientedGrassmannianHomeomorph e)

/-- The orientation-forgetting covering has exactly two points over every plane. -/
theorem encard_preimage_forget_comp (e : E ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin N))
    (P : finiteGrassmannian ℝ r N) :
    (((finiteOrientedGrassmannian.forget :
      finiteOrientedGrassmannian r N → finiteGrassmannian ℝ r N) ∘
        finiteOrientedGrassmannianHomeomorph e) ⁻¹' {P}).encard = 2 := by
  let h := finiteOrientedGrassmannianHomeomorph (r := r) e
  rw [Set.preimage_comp, Set.encard_preimage_of_injective_subset_range h.injective
    (by rw [h.surjective.range_eq]; exact Set.subset_univ _)]
  exact VectorBundleOrientationCover.encard_preimage_proj_singleton (by simp) P

section Smooth

open scoped Matrix.Norms.L2Operator
attribute [local instance] Matrix.l2OpNormedAlgebraReal
attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField
attribute [local instance] ContMDiffMul.boundarylessManifold

variable (E) (r : ℕ+)

local notation "SO(" r ")" => specialOrthogonalGroup (Fin r) ℝ
local notation "𝓢𝓞(" r ")" => specialUnitaryGroup.model (Fin r) ℝ
local notation "𝔰𝔬(" r ")" =>
  LieSubalgebra.toSubmodule
    (Lie.lieSubalgebraOfSubgroup (I := 𝓘(ℝ, Matrix (Fin r) (Fin r) ℝ)) (GLSpecialUnitary (Fin r) ℝ))
local notation "StiefelModel(" E ", " r ")" => Fin (r * finrank ℝ E - Nat.choose (r + 1) 2) → ℝ

/-- The Euclidean model of the oriented Grassmannian, obtained by subtracting the dimension of
the rotation group from the dimension of the Stiefel manifold. -/
abbrev Model :=
  ProperSMul.QuotientModelSpace (𝔰𝔬(r)) (StiefelModel(E, (r : ℕ)))

/-- The quotient model has dimension `r (dim E - r)`. -/
theorem finrank_model : finrank ℝ (Model E r) = (r : ℕ) * (finrank ℝ E - r) := by
  have hSO : finrank ℝ (𝔰𝔬(r)) = (Fintype.card (Fin r)).choose 2 :=
    finrank_specialOrthogonalLieAlgebra
  have h (k : ℕ) : (k + 1).choose 2 + k.choose 2 = k * k := by
    simpa [Nat.add_comm 1 k] using Nat.add_choose_two_add_choose_two 1 k
  rw [ProperSMul.finrank_quotientModelSpace, hSO,
    Fintype.card_fin, Module.finrank_fin_fun, Nat.sub_sub, h, Nat.mul_sub_left_distrib]

variable [FiniteDimensional ℝ E]

/-- The oriented Grassmannian has the slice charts for the change-of-basis action. -/
instance instChartedSpace : ChartedSpace (Model E r) (orientedGrassmannian E r) :=
  ProperSMul.orbitRelQuotientChartedSpace 𝓢𝓞(r) (SO(r)) 𝓘(ℝ, StiefelModel(E, (r : ℕ)))
    (stiefel E r)

/-- The slice atlas makes the oriented Grassmannian a smooth manifold. -/
instance instIsManifold : IsManifold 𝓘(ℝ, Model E r) ∞ (orientedGrassmannian E r) :=
  ProperSMul.instIsManifoldOrbitRelQuotient
    (I := 𝓢𝓞(r)) (I' := 𝓘(ℝ, StiefelModel(E, (r : ℕ))))

/-- The projection from the Stiefel manifold to the oriented Grassmannian is a smooth submersion. -/
theorem isSubmersion_ofFrame :
    Manifold.IsSubmersion 𝓘(ℝ, StiefelModel(E, (r : ℕ))) 𝓘(ℝ, Model E r) ∞
      (ofFrame : stiefel E r → orientedGrassmannian E r) :=
  ProperSMul.isSubmersion_quotientMk (I := 𝓢𝓞(r)) (I' := 𝓘(ℝ, StiefelModel(E, (r : ℕ))))

end Smooth

end orientedGrassmannian

end TauCeti
