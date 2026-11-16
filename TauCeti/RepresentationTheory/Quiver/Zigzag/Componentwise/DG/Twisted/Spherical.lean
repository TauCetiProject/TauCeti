/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Hasse
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.Notation
public import TauCeti.CategoryTheory.DG.Spherical
public import TauCeti.RepresentationTheory.Quiver.Zigzag.Componentwise.DG.Twisted.Duality

/-!
# `2`-sphericality, `A_m`-configurations, and numerical Euler twists of zigzag projectives

Every pair of objects in `TauCeti.ZigzagProjectiveTwistedClosure` has finite total graded `Hom`
over a Noetherian commutative coefficient ring. Embedding the zero-DG vertex projectives into the
formal twisted closure via `vertexEmbedding` produces the canonical vertex objects `vertexObject`.
Over a field `k`:

1. Cohomology between `vertexObject k G i` and `vertexObject k G j` in degree `d` identifies
   linearly with the signed corner
   `cornerSubmodule k (e i) (e j) ⊓ zigzagAlgebraIntegerGrade k G d`, so its dimension is `1` in
   degrees `0` and `2` when `i = j`, `1` in degree `1` when `G.Adj i j`, and `0` otherwise.
2. Total graded `Hom` dimension between vertex objects equals `2` on the diagonal, `1` on edges of
   `G`, and `0` on non-edges, while the graded Euler pairing `dgEulerPairing` equals the symmetric
   generalized Cartan pairing (`2` on the diagonal, `-1` on edges, `0` on non-edges).
3. Every `vertexObject k G i` (and every shift `(shiftFunctor k m).obj (vertexObject k G i)`) is
   unconditionally a Seidel–Thomas `2`-spherical object for **every** finite simple graph `G`
   (without requiring `G` to be bipartite, since a single vertex has no self-loops in `G`, making
   the local sign condition in `TauCeti.ZigzagProjectiveTwistedClosure.isPerfPair_homologyPairing`
   vacuous).
4. Along any graph isomorphism `SimpleGraph.pathGraph m ≃g G` (and in particular on
   `SimpleGraph.pathGraph m` directly), the vertex objects form a Seidel–Thomas
   `A_m`-configuration of `2`-spherical objects (`TauCeti.IsAmSphericalConfiguration`).
5. The numerical Seidel–Thomas twist reflection matrices `eulerTwistMatrix k G r` (`[F] ↦ [F] -
   χ(E_r, F)[E_r]`) satisfy the Artin–Tits / Coxeter reflection relations on **every** finite simple
   graph `G`: involutivity `R_r * R_r = 1`, commutation `R_r * R_s = R_s * R_r` for non-adjacent
   vertices, and the braid relation `R_r * R_s * R_r = R_s * R_r * R_s` for adjacent vertices. On
   `A₂ = SimpleGraph.pathGraph 2`, `R_0 = !![-1, 1; 0, 1]` and `R_1 = !![1, 0; 1, -1]` have
   determinant `-1` and common braid product `!![0, -1; -1, 0]`.

## Main definitions

* `TauCeti.ZigzagProjectiveTwistedClosure.vertexEmbedding`: the quasi-fully-faithful DG embedding
  of the vertex subcategory into `ZigzagProjectiveTwistedClosure k G`.
* `TauCeti.ZigzagProjectiveTwistedClosure.vertexObject`: the formal twisted object corresponding to
  vertex `i : V`.
* `TauCeti.ZigzagProjectiveTwistedClosure.vertexObjectHomologyEquivCorner`: linear equivalence
  between `Hom^d(vertexObject i, vertexObject j)` and the degree-`d` vertex corner of the zigzag
  algebra.
* `TauCeti.ZigzagProjectiveTwistedClosure.eulerMatrix` and
  `TauCeti.ZigzagProjectiveTwistedClosure.eulerTwistMatrix`: the vertex Euler matrix and numerical
  twist reflection matrices `[F] ↦ [F] - χ(E_r, F)[E_r]`.

## Main results

* `TauCeti.ZigzagProjectiveTwistedClosure.hasFiniteTotalGradedHom`: total graded `Hom` finiteness
  for all pairs of objects over a Noetherian commutative ring.
* `TauCeti.ZigzagProjectiveTwistedClosure.dgTotalHomFinrank_vertexObject` and
  `TauCeti.ZigzagProjectiveTwistedClosure.dgEulerPairing_vertexObject`: total `Hom` dimension and
  Euler pairing between vertex objects.
* `TauCeti.ZigzagProjectiveTwistedClosure.isSphericalObject_vertexObject` and
  `TauCeti.ZigzagProjectiveTwistedClosure.isSphericalObject_shiftFunctor_vertexObject`: every
  vertex object and every integer shift thereof is `2`-spherical for any finite simple graph `G`.
* `TauCeti.ZigzagProjectiveTwistedClosure.isAmSphericalConfiguration_of_pathGraphIso` and
  `TauCeti.ZigzagProjectiveTwistedClosure.isAmSphericalConfiguration_vertexObject`: vertex objects
  of `A_m` form a Seidel–Thomas `A_m`-configuration of `2`-spherical objects.
* `TauCeti.ZigzagProjectiveTwistedClosure.eulerTwistMatrix_mul_self`,
  `TauCeti.ZigzagProjectiveTwistedClosure.eulerTwistMatrix_mul_comm_of_not_adj`,
  `TauCeti.ZigzagProjectiveTwistedClosure.eulerTwistMatrix_braid_of_adj`, and
  `TauCeti.ZigzagProjectiveTwistedClosure.eulerTwistMatrix_pathGraph_two_braid`: reflection and
  braid relations for the numerical Euler twists, specialized to `A₂`.

## References

* P. Seidel and R. Thomas, *Braid group actions on derived categories of coherent sheaves*,
  Definitions 2.5, 2.9, 2.15 and Section 4.
* R. Rouquier and A. Zimmermann, *Picard groups for derived module categories*, Section 4.
-/

public section
noncomputable section

open CategoryTheory

namespace TauCeti.ZigzagProjectiveTwistedClosure

universe u

variable (k : Type u) {V : Type u} (G : SimpleGraph V)

attribute [local instance] zigzagAlgebraIntegerGradedAlgebra

local notation "D" => zigzagAlgebraProjectiveDGRightModule k G
local notation "e" => fun i : V ↦ zigzagAlgebraBasis k G (Sum.inl i)
local notation "A" => zigzagAlgebraIntegerGrade k G
local notation "𝒱" => DGFullSubcategory (fun M ↦ ∃ i : V, M = D i)
local notation "𝒮" => DGShiftClosure 𝒱
local notation "𝒜" => DGAdditiveClosure 𝒮

section CommRing

variable [Finite V] [CommRing k]

/-- The canonical DG functor embedding the zero-DG vertex subcategory `𝒱` into
`ZigzagProjectiveTwistedClosure k G` as unshifted one-summand objects with zero twist. -/
def vertexEmbedding :
    EnrichedFunctor (CochainComplex (ModuleCat.{u} k) ℤ) 𝒱
      (ZigzagProjectiveTwistedClosure k G) :=
  ((DGShiftClosure.ι k).comp (CochainComplex (ModuleCat.{u} k) ℤ)
    (DGAdditiveClosure.embedding k)).comp (CochainComplex (ModuleCat.{u} k) ℤ)
    (DGTwistedObject.embedding k)

/-- `vertexEmbedding` is quasi-fully faithful: each of its three constituent embeddings is an
isomorphism on Hom complexes. -/
theorem isQuasiFullyFaithful_vertexEmbedding :
    (vertexEmbedding k G).IsQuasiFullyFaithful :=
  ((EnrichedFunctor.isQuasiFullyFaithful_of_isIso_map
      (F := DGShiftClosure.ι k (C := 𝒱)) fun _ _ ↦ inferInstance).comp
    (EnrichedFunctor.isQuasiFullyFaithful_of_isIso_map
      (F := DGAdditiveClosure.embedding k (C := 𝒮)) fun _ _ ↦ inferInstance)).comp
    (EnrichedFunctor.isQuasiFullyFaithful_of_isIso_map
      (F := DGTwistedObject.embedding k (C := 𝒜)) fun _ _ ↦ inferInstance)

/-- The canonical object of `ZigzagProjectiveTwistedClosure k G` associated to vertex `i : V`. -/
def vertexObject (i : V) : ZigzagProjectiveTwistedClosure k G :=
  (vertexEmbedding k G).obj ⟨D i, i, rfl⟩

/-- `vertexObject k G i` unfolds to the one-summand unshifted object `⟨D i, i, rfl⟩` with zero
twist. -/
theorem vertexObject_eq (i : V) :
    vertexObject k G i =
      DGTwistedObject.ofObj k ⟨PUnit, fun _ ↦ ⟨⟨D i, i, rfl⟩, 0⟩⟩ := by
  simp [vertexObject, vertexEmbedding]

/-- Canonical cohomology between `vertexObject k G i` and `vertexObject k G j` in degree `d`
identifies linearly with the signed graded corner `e_i Z e_j ∩ Z_d` of the zigzag algebra. -/
def vertexObjectHomologyEquivCorner (i j : V) (d : ℤ) :
    (dgHomComplex k (vertexObject k G i) (vertexObject k G j)).homology d ≃ₗ[k]
      ↥(cornerSubmodule k (e i) (e j) ⊓ A d) :=
  (((isQuasiFullyFaithful_vertexEmbedding k G).homologyLinearEquiv
      ⟨D i, i, rfl⟩ ⟨D j, j, rfl⟩ d).symm.trans
    (eqToIso (congrArg (fun K ↦ K.homology d)
      (DGFullSubcategory.dgHomComplex_eq (R := k)
        (⟨D i, i, rfl⟩ : 𝒱) ⟨D j, j, rfl⟩))).toLinearEquiv).trans
    (((eqToIso (congrArg (fun m ↦ (dgHomComplex k (D i) (D j)).homology m)
        (neg_neg d).symm)).toLinearEquiv.trans
      (zigzagAlgebraProjectiveHomologyEquivCorner k G i j (-d))).trans
      (LinearEquiv.ofEq _ _ (by rw [neg_neg])))

/-- Cohomology between two vertex objects vanishes outside degrees `{0, 1, 2}`. -/
theorem subsingleton_homology_vertexObject_of_not_mem (i j : V) {d : ℤ}
    (hd : d ∉ ({0, 1, 2} : Finset ℤ)) :
    Subsingleton ((dgHomComplex k (vertexObject k G i) (vertexObject k G j)).homology d) := by
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hd
  rcases hd with ⟨hd0, hd1, hd2⟩
  have hbot : cornerSubmodule k (e i) (e j) ⊓ A d = ⊥ := by
    by_cases hij : i = j
    · subst j
      rw [cornerSubmodule_zigzagAlgebra_self_inf_integerGrade]
      simp [hd0, hd2]
    · by_cases hadj : G.Adj j i
      · rw [cornerSubmodule_zigzagAlgebra_inf_integerGrade_of_adj k G hadj]
        simp [hd1]
      · rw [cornerSubmodule_zigzagAlgebra_eq_bot_of_ne_of_not_adj k G hij
          (fun h ↦ hadj h.symm), bot_inf_eq]
  have : Subsingleton ↥(cornerSubmodule k (e i) (e j) ⊓ A d) := by
    rw [hbot]
    infer_instance
  exact (vertexObjectHomologyEquivCorner k G i j d).toEquiv.subsingleton_congr.mpr inferInstance

/-- Self-cohomology of `vertexObject k G i` vanishes in every degree `d ∉ {0, 2}`. -/
theorem subsingleton_homology_vertexObject_self_of_ne (i : V) {d : ℤ}
    (hd0 : d ≠ 0) (hd2 : d ≠ 2) :
    Subsingleton ((dgHomComplex k (vertexObject k G i) (vertexObject k G i)).homology d) := by
  have hbot : cornerSubmodule k (e i) (e i) ⊓ A d = ⊥ := by
    rw [cornerSubmodule_zigzagAlgebra_self_inf_integerGrade]
    simp [hd0, hd2]
  have : Subsingleton ↥(cornerSubmodule k (e i) (e i) ⊓ A d) := by
    rw [hbot]
    infer_instance
  exact (vertexObjectHomologyEquivCorner k G i i d).toEquiv.subsingleton_congr.mpr inferInstance

end CommRing

section Noetherian

variable [Finite V] [CommRing k] [IsNoetherianRing k]

/-- Every pair of formal twisted objects in `ZigzagProjectiveTwistedClosure k G` satisfies
Seidel–Thomas's total graded `Hom` finiteness condition `TauCeti.HasFiniteTotalGradedHom` over a
Noetherian commutative coefficient ring. -/
theorem hasFiniteTotalGradedHom (X Y : ZigzagProjectiveTwistedClosure k G) :
    HasFiniteTotalGradedHom k X Y :=
  HasFiniteTotalGradedHom.of_finset k (homSupport k G X Y)
    (subsingleton_homology_of_not_mem_homSupport k G X Y)

end Noetherian

section Field

variable [Finite V] [Field k]

open scoped Classical in
/-- Over a field `k`, the dimension of `Hom^d(vertexObject i, vertexObject j)` is `1` in degrees
`0` and `2` when `i = j`, `1` in degree `1` when `G.Adj i j`, and `0` otherwise. -/
@[simp]
theorem finrank_homology_vertexObject (i j : V) (d : ℤ) :
    Module.finrank k ((dgHomComplex k (vertexObject k G i) (vertexObject k G j)).homology d) =
      if i = j then if d = 0 ∨ d = 2 then 1 else 0
      else if G.Adj i j ∧ d = 1 then 1 else 0 :=
  (vertexObjectHomologyEquivCorner k G i j d).finrank_eq.trans
    (finrank_cornerSubmodule_zigzagAlgebra_inf_integerGrade k G i j d)

open scoped Classical in
/-- Total graded `Hom` dimension between vertex objects is `2` on the diagonal, `1` on edges of
`G`, and `0` on non-edges. -/
@[simp]
theorem dgTotalHomFinrank_vertexObject (i j : V) :
    dgTotalHomFinrank k (vertexObject k G i) (vertexObject k G j) =
      if i = j then 2 else if G.Adj i j then 1 else 0 := by
  classical
  rw [dgTotalHomFinrank_eq_sum k ({0, 1, 2} : Finset ℤ) fun d hd ↦
    subsingleton_homology_vertexObject_of_not_mem k G i j hd]
  have h01 : (0 : ℤ) ∉ ({1, 2} : Finset ℤ) := by decide
  have h12 : (1 : ℤ) ∉ ({2} : Finset ℤ) := by decide
  rw [Finset.sum_insert h01, Finset.sum_insert h12, Finset.sum_singleton]
  simp only [finrank_homology_vertexObject]
  by_cases hij : i = j
  · simp [hij]
  · by_cases hadj : G.Adj i j <;> simp [hij, hadj]

open scoped Classical in
/-- The graded Euler pairing `χ(vertexObject i, vertexObject j)` equals the symmetric generalized
Cartan pairing of `G`: `2` on the diagonal, `-1` on edges of `G`, and `0` on non-edges. -/
@[simp]
theorem dgEulerPairing_vertexObject (i j : V) :
    dgEulerPairing k (vertexObject k G i) (vertexObject k G j) =
      if i = j then 2 else if G.Adj i j then -1 else 0 := by
  classical
  rw [dgEulerPairing_eq_sum k ({0, 1, 2} : Finset ℤ) fun d hd ↦
    subsingleton_homology_vertexObject_of_not_mem k G i j hd]
  have h01 : (0 : ℤ) ∉ ({1, 2} : Finset ℤ) := by decide
  have h12 : (1 : ℤ) ∉ ({2} : Finset ℤ) := by decide
  rw [Finset.sum_insert h01, Finset.sum_insert h12, Finset.sum_singleton]
  have hp0 : (0 : ℤ).negOnePow = 1 := rfl
  have hp1 : (1 : ℤ).negOnePow = -1 := by decide
  have hp2 : (2 : ℤ).negOnePow = 1 := by decide
  rw [hp0, hp1, hp2]
  simp only [finrank_homology_vertexObject]
  by_cases hij : i = j
  · simp [hij]
  · by_cases hadj : G.Adj i j <;> simp [hij, hadj]

/-- Every vertex object `vertexObject k G i` in `ZigzagProjectiveTwistedClosure k G` is
unconditionally a Seidel–Thomas `2`-spherical object over a field `k`, for **every** finite simple
graph `G` (not only bipartite graphs). -/
theorem isSphericalObject_vertexObject (i : V) :
    IsSphericalObject k 2 (vertexObject k G i) where
  pos := by decide
  hasFiniteTotalGradedHom_from F := hasFiniteTotalGradedHom k G (vertexObject k G i) F
  finrank_homology_zero := by simp
  finrank_homology_top := by simp
  subsingleton_homology_of_ne := subsingleton_homology_vertexObject_self_of_ne k G i
  exists_trace_isPerfPair := by
    let v : (vertexObject k G i).obj.ι → V := fun _ ↦ i
    have hv : ∀ u : (vertexObject k G i).obj.ι,
        ((vertexObject k G i).obj.X u).obj.obj = D (v u) := by
      dsimp only [v]
      -- Rewrite `vertexObject k G i` to `ofObj` before introducing the dependent summand index `u`.
      rw [vertexObject_eq]
      intro _
      rfl
    let c : V → kˣ := fun _ ↦ 1
    have hc : ∀ u₁ u₂ : (vertexObject k G i).obj.ι,
        G.Adj (v u₁) (v u₂) → (c (v u₂) : k) = -(c (v u₁) : k) :=
      fun _ _ hadj ↦ False.elim (G.ne_of_adj hadj rfl)
    refine ⟨homologyTrace k G (fun u ↦ (c u : k)) (vertexObject k G i) v hv hc, fun F d ↦ ?_⟩
    rw [← homologyPairing_eq_compr₂_homologyTrace]
    exact isPerfPair_homologyPairing k G c (vertexObject k G i) F v hv hc d

/-- Every integer shift `(shiftFunctor k m).obj (vertexObject k G i)` of a vertex object is
`2`-spherical. -/
theorem isSphericalObject_shiftFunctor_vertexObject (m : ℤ) (i : V) :
    IsSphericalObject k 2 ((DGTwistedObject.shiftFunctor k m).obj (vertexObject k G i)) :=
  (DGTwistedObject.isSphericalObject_shiftFunctor_iff 2 m (vertexObject k G i)).mpr
    (isSphericalObject_vertexObject k G i)

/-- Along any graph isomorphism `φ : SimpleGraph.pathGraph m ≃g G`, the vertex objects
`fun i ↦ vertexObject k G (φ i)` form a Seidel–Thomas `A_m`-configuration of `2`-spherical objects
in `ZigzagProjectiveTwistedClosure k G`. -/
theorem isAmSphericalConfiguration_of_pathGraphIso {m : ℕ} (φ : SimpleGraph.pathGraph m ≃g G) :
    IsAmSphericalConfiguration k m 2 (fun i ↦ vertexObject k G (φ i)) where
  isSphericalObject i := isSphericalObject_vertexObject k G (φ i)
  dgTotalHomFinrank_of_adj {i j} hadj := by
    have hadjG : G.Adj (φ i) (φ j) := φ.map_adj_iff.mpr (SimpleGraph.pathGraph_adj.mpr hadj)
    have hne : φ i ≠ φ j := G.ne_of_adj hadjG
    simp [dgTotalHomFinrank_vertexObject, hne, hadjG]
  dgTotalHomFinrank_of_nonadj {i j} hne hnadj := by
    have hneG : φ i ≠ φ j := fun h ↦ hne (φ.injective h)
    have hnadjG : ¬ G.Adj (φ i) (φ j) := by
      rw [φ.map_adj_iff, SimpleGraph.pathGraph_adj]
      exact hnadj
    simp [dgTotalHomFinrank_vertexObject, hneG, hnadjG]

/-- The `V × V` integer matrix of the graded Euler pairing `χ(vertexObject i, vertexObject j)`. -/
def eulerMatrix : Matrix V V ℤ :=
  Matrix.of fun i j ↦ dgEulerPairing k (vertexObject k G i) (vertexObject k G j)

/-- Entry `(i, j)` of `eulerMatrix k G` is `dgEulerPairing k (vertexObject i) (vertexObject j)`. -/
@[simp]
theorem eulerMatrix_apply (i j : V) :
    eulerMatrix k G i j = dgEulerPairing k (vertexObject k G i) (vertexObject k G j) := by
  rw [eulerMatrix, Matrix.of_apply]

open scoped Classical Matrix in
/-- `eulerMatrix k G` is symmetric (`(eulerMatrix k G)ᵀ = eulerMatrix k G`). -/
@[simp]
theorem transpose_eulerMatrix : (eulerMatrix k G)ᵀ = eulerMatrix k G := by
  ext i j
  simp only [Matrix.transpose_apply, eulerMatrix_apply, dgEulerPairing_vertexObject]
  by_cases hij : j = i
  · subst j; simp
  · have hji : i ≠ j := Ne.symm hij
    simp only [hij, hji, ↓reduceIte]
    by_cases hadj : G.Adj j i
    · simp [hadj, hadj.symm]
    · have hnadj : ¬ G.Adj i j := fun h ↦ hadj h.symm
      simp [hadj, hnadj]

end Field

/-! ### Numerical Seidel–Thomas Euler twist reflections -/

section EulerReflection

variable [Fintype V] [DecidableEq V] [Field k]

private def eulerRankOne (r : V) : Matrix V V ℤ :=
  Matrix.of fun i j ↦ if i = r then eulerMatrix k G r j else 0

private theorem eulerRankOne_mul (r s : V) :
    eulerRankOne k G r * eulerRankOne k G s =
      eulerMatrix k G r s • Matrix.of fun i j ↦ if i = r then eulerMatrix k G s j else 0 := by
  ext i j
  simp only [eulerRankOne, Matrix.mul_apply, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul]
  by_cases hir : i = r
  · subst i
    simp
  · simp [hir]

private theorem eulerRankOne_mul_self (r : V) :
    eulerRankOne k G r * eulerRankOne k G r = (2 : ℤ) • eulerRankOne k G r := by
  rw [eulerRankOne_mul]
  have hrr : eulerMatrix k G r r = 2 := by simp
  rw [hrr]
  rfl

/-- The numerical Seidel–Thomas twist matrix `R_r` on `ℤ^V`, representing the action
`[F] ↦ [F] - χ(E_r, F)[E_r]` in the vertex basis `[E_i]` (`i : V`) under `Matrix.mulVec`. -/
def eulerTwistMatrix (r : V) : Matrix V V ℤ :=
  1 - eulerRankOne k G r

/-- Entry `(i, j)` of `eulerTwistMatrix k G r`. -/
theorem eulerTwistMatrix_apply (r i j : V) :
    eulerTwistMatrix k G r i j =
      (if i = j then 1 else 0) - if i = r then eulerMatrix k G r j else 0 := by
  simp [eulerTwistMatrix, eulerRankOne, Matrix.one_apply]

/-- On the `j`-th standard basis vector `Pi.single j 1`, `eulerTwistMatrix k G r` acts by the
numerical twist formula `e_j ↦ e_j - χ(E_r, E_j) e_r`. -/
theorem eulerTwistMatrix_mulVec_single (r j : V) :
    (eulerTwistMatrix k G r).mulVec (Pi.single j 1) =
      Pi.single j 1 - eulerMatrix k G r j • Pi.single r 1 := by
  ext i
  rw [Matrix.mulVec_single_one, Matrix.col_apply, eulerTwistMatrix_apply]
  simp only [Pi.sub_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul,
    mul_ite, mul_one, mul_zero, eq_comm]

/-- For a `2`-spherical vertex object `E_r`, the numerical twist `eulerTwistMatrix k G r` is an
involution (`R_r * R_r = 1`). -/
@[simp]
theorem eulerTwistMatrix_mul_self (r : V) :
    eulerTwistMatrix k G r * eulerTwistMatrix k G r = 1 := by
  simp only [eulerTwistMatrix, sub_mul, mul_sub, one_mul, mul_one,
    eulerRankOne_mul_self, two_zsmul]
  abel

/-- Numerical twists at non-adjacent vertices commute (`R_r * R_s = R_s * R_r`). -/
theorem eulerTwistMatrix_mul_comm_of_not_adj {r s : V} (hnadj : ¬ G.Adj r s) :
    eulerTwistMatrix k G r * eulerTwistMatrix k G s =
      eulerTwistMatrix k G s * eulerTwistMatrix k G r := by
  by_cases hrs : r = s
  · subst s; rfl
  · have hnadj' : ¬ G.Adj s r := fun h ↦ hnadj h.symm
    have h0rs : eulerMatrix k G r s = 0 := by simp [hrs, hnadj]
    have h0sr : eulerMatrix k G s r = 0 := by simp [Ne.symm hrs, hnadj']
    have hmul1 : eulerRankOne k G r * eulerRankOne k G s = 0 := by
      rw [eulerRankOne_mul, h0rs, zero_smul]
    have hmul2 : eulerRankOne k G s * eulerRankOne k G r = 0 := by
      rw [eulerRankOne_mul, h0sr, zero_smul]
    simp only [eulerTwistMatrix, sub_mul, mul_sub, one_mul, mul_one, hmul1, hmul2, sub_zero]
    abel

/-- Numerical twists at adjacent vertices satisfy the Artin–Tits braid relation
`R_r * R_s * R_r = R_s * R_r * R_s`. -/
theorem eulerTwistMatrix_braid_of_adj {r s : V} (hadj : G.Adj r s) :
    eulerTwistMatrix k G r * eulerTwistMatrix k G s * eulerTwistMatrix k G r =
      eulerTwistMatrix k G s * eulerTwistMatrix k G r * eulerTwistMatrix k G s := by
  have hrs : r ≠ s := G.ne_of_adj hadj
  have hrs' : s ≠ r := hrs.symm
  have hcrs : eulerMatrix k G r s = -1 := by simp [hrs, hadj]
  have hcsr : eulerMatrix k G s r = -1 := by simp [hrs', hadj.symm]
  have htriple_r :
      eulerRankOne k G r * eulerRankOne k G s * eulerRankOne k G r = eulerRankOne k G r := by
    rw [eulerRankOne_mul, hcrs, neg_one_smul, neg_mul]
    ext i j
    simp only [eulerRankOne, Matrix.neg_apply, Matrix.mul_apply, Matrix.of_apply]
    by_cases hir : i = r
    · subst i
      simp only [↓reduceIte, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ]
      rw [hcsr, neg_one_mul, neg_neg]
    · simp only [hir, ↓reduceIte, zero_mul, Finset.sum_const_zero, neg_zero]
  have htriple_s :
      eulerRankOne k G s * eulerRankOne k G r * eulerRankOne k G s = eulerRankOne k G s := by
    rw [eulerRankOne_mul, hcsr, neg_one_smul, neg_mul]
    ext i j
    simp only [eulerRankOne, Matrix.neg_apply, Matrix.mul_apply, Matrix.of_apply]
    by_cases his : i = s
    · subst i
      simp only [↓reduceIte, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ]
      rw [hcrs, neg_one_mul, neg_neg]
    · simp only [his, ↓reduceIte, zero_mul, Finset.sum_const_zero, neg_zero]
  have expand (u w : V)
      (hsq : eulerRankOne k G u * eulerRankOne k G u = (2 : ℤ) • eulerRankOne k G u)
      (htri : eulerRankOne k G u * eulerRankOne k G w * eulerRankOne k G u = eulerRankOne k G u) :
      eulerTwistMatrix k G u * eulerTwistMatrix k G w * eulerTwistMatrix k G u =
        1 - eulerRankOne k G u - eulerRankOne k G w +
          eulerRankOne k G u * eulerRankOne k G w +
          eulerRankOne k G w * eulerRankOne k G u := by
    simp only [eulerTwistMatrix, sub_mul, mul_sub, one_mul, mul_one, hsq, htri, two_zsmul]
    abel
  rw [expand r s (eulerRankOne_mul_self k G r) htriple_r,
    expand s r (eulerRankOne_mul_self k G s) htriple_s]
  abel

end EulerReflection

/-! ### Specialization to `SimpleGraph.pathGraph` and the `A₂` reflection check -/

section PathGraph

/-- For `SimpleGraph.pathGraph m` over a `Type`-level field `k`, the vertex objects form a
Seidel–Thomas `A_m`-configuration of `2`-spherical objects. -/
theorem isAmSphericalConfiguration_vertexObject (k : Type) [Field k] (m : ℕ) :
    IsAmSphericalConfiguration k m 2 (vertexObject k (SimpleGraph.pathGraph m)) :=
  isAmSphericalConfiguration_of_pathGraphIso k (SimpleGraph.pathGraph m) SimpleGraph.Iso.refl

/-- On `A₂ = SimpleGraph.pathGraph 2`, the numerical twist at vertex `0` is `!![-1, 1; 0, 1]`. -/
theorem eulerTwistMatrix_pathGraph_two_zero (k : Type) [Field k] :
    eulerTwistMatrix k (SimpleGraph.pathGraph 2) 0 = !![(-1 : ℤ), 1; 0, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [eulerTwistMatrix_apply, eulerMatrix_apply, dgEulerPairing_vertexObject,
      SimpleGraph.pathGraph_adj]

/-- On `A₂ = SimpleGraph.pathGraph 2`, the numerical twist at vertex `1` is `!![1, 0; 1, -1]`. -/
theorem eulerTwistMatrix_pathGraph_two_one (k : Type) [Field k] :
    eulerTwistMatrix k (SimpleGraph.pathGraph 2) 1 = !![(1 : ℤ), 0; 1, -1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [eulerTwistMatrix_apply, eulerMatrix_apply, dgEulerPairing_vertexObject,
      SimpleGraph.pathGraph_adj]

/-- Both `A₂` numerical twist reflections have determinant `-1`. -/
theorem det_eulerTwistMatrix_pathGraph_two (k : Type) [Field k] (r : Fin 2) :
    (eulerTwistMatrix k (SimpleGraph.pathGraph 2) r).det = -1 := by
  fin_cases r <;>
    simp [Matrix.det_fin_two, eulerTwistMatrix_apply, eulerMatrix_apply,
      dgEulerPairing_vertexObject, SimpleGraph.pathGraph_adj]

/-- Seidel–Thomas Check (`A₂`): both three-fold products `A * B * A` and `B * A * B` of the `A₂`
numerical twist matrices equal `!![0, -1; -1, 0]`. -/
theorem eulerTwistMatrix_pathGraph_two_braid (k : Type) [Field k] :
    eulerTwistMatrix k (SimpleGraph.pathGraph 2) 0 *
        eulerTwistMatrix k (SimpleGraph.pathGraph 2) 1 *
        eulerTwistMatrix k (SimpleGraph.pathGraph 2) 0 = !![(0 : ℤ), -1; -1, 0] ∧
      eulerTwistMatrix k (SimpleGraph.pathGraph 2) 1 *
        eulerTwistMatrix k (SimpleGraph.pathGraph 2) 0 *
        eulerTwistMatrix k (SimpleGraph.pathGraph 2) 1 = !![(0 : ℤ), -1; -1, 0] := by
  have hadj : (SimpleGraph.pathGraph 2).Adj 0 1 := by simp [SimpleGraph.pathGraph_adj]
  have hbraid := eulerTwistMatrix_braid_of_adj k (SimpleGraph.pathGraph 2) hadj
  have hABA :
      eulerTwistMatrix k (SimpleGraph.pathGraph 2) 0 *
        eulerTwistMatrix k (SimpleGraph.pathGraph 2) 1 *
        eulerTwistMatrix k (SimpleGraph.pathGraph 2) 0 = !![(0 : ℤ), -1; -1, 0] := by
    rw [eulerTwistMatrix_pathGraph_two_zero, eulerTwistMatrix_pathGraph_two_one]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  exact ⟨hABA, hbraid.symm.trans hABA⟩

end PathGraph

end TauCeti.ZigzagProjectiveTwistedClosure
