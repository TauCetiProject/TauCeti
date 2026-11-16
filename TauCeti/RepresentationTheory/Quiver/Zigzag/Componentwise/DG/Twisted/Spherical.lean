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

Over a Noetherian commutative ring, all pairs in `TauCeti.ZigzagProjectiveTwistedClosure` satisfy
`TauCeti.HasFiniteTotalGradedHom` (`hasFiniteTotalGradedHom`), and `vertexObject` identifies vertex
cohomology with zigzag algebra corners (`vertexObjectHomologyEquivCorner`). Over any field `k` and
finite simple graph `G`, every `vertexObject k G i` and its shifts are `2`-spherical, any
`SimpleGraph.pathGraph m ≃g G` gives an `A_m`-configuration, and `eulerTwistMatrix` satisfies the
Artin–Tits reflection and braid relations, checked explicitly on `A₂ = SimpleGraph.pathGraph 2`.

## References

* P. Seidel and R. Thomas, *Braid group actions on derived categories of coherent sheaves*, §2, §4.
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
    EnrichedFunctor (CochainComplex (ModuleCat.{u} k) ℤ) 𝒱 (ZigzagProjectiveTwistedClosure k G) :=
  ((DGShiftClosure.ι k).comp (CochainComplex (ModuleCat.{u} k) ℤ)
    (DGAdditiveClosure.embedding k)).comp (CochainComplex (ModuleCat.{u} k) ℤ)
    (DGTwistedObject.embedding k)

/-- `vertexEmbedding` is quasi-fully faithful. -/
theorem isQuasiFullyFaithful_vertexEmbedding : (vertexEmbedding k G).IsQuasiFullyFaithful :=
  ((EnrichedFunctor.isQuasiFullyFaithful_of_isIso_map
      (F := DGShiftClosure.ι k (C := 𝒱)) fun _ _ ↦ inferInstance).comp
    (EnrichedFunctor.isQuasiFullyFaithful_of_isIso_map
      (F := DGAdditiveClosure.embedding k (C := 𝒮)) fun _ _ ↦ inferInstance)).comp
    (EnrichedFunctor.isQuasiFullyFaithful_of_isIso_map
      (F := DGTwistedObject.embedding k (C := 𝒜)) fun _ _ ↦ inferInstance)

/-- The canonical object of `ZigzagProjectiveTwistedClosure k G` associated to vertex `i : V`. -/
def vertexObject (i : V) : ZigzagProjectiveTwistedClosure k G :=
  (vertexEmbedding k G).obj ⟨D i, i, rfl⟩

/-- `vertexObject k G i` unfolds to the one-summand unshifted object with zero twist. -/
theorem vertexObject_eq (i : V) :
    vertexObject k G i = DGTwistedObject.ofObj k ⟨PUnit, fun _ ↦ ⟨⟨D i, i, rfl⟩, 0⟩⟩ := by
  simp [vertexObject, vertexEmbedding]

/-- Canonical cohomology between `vertexObject k G i` and `vertexObject k G j` in degree `d`
identifies linearly with the signed graded corner `e_i Z e_j ∩ Z_d` of the zigzag algebra. -/
def vertexObjectHomologyEquivCorner (i j : V) (d : ℤ) :
    (dgHomComplex k (vertexObject k G i) (vertexObject k G j)).homology d ≃ₗ[k]
      ↥(cornerSubmodule k (e i) (e j) ⊓ A d) :=
  (((isQuasiFullyFaithful_vertexEmbedding k G).homologyLinearEquiv
      ⟨D i, i, rfl⟩ ⟨D j, j, rfl⟩ d).symm.trans
    (eqToIso (congrArg (fun K ↦ K.homology d)
      (DGFullSubcategory.dgHomComplex_eq (R := k) (⟨D i, i, rfl⟩ : 𝒱)
        ⟨D j, j, rfl⟩))).toLinearEquiv).trans
    (((eqToIso (congrArg (fun m ↦ (dgHomComplex k (D i) (D j)).homology m)
        (neg_neg d).symm)).toLinearEquiv.trans
      (zigzagAlgebraProjectiveHomologyEquivCorner k G i j (-d))).trans
      (LinearEquiv.ofEq _ _ (by rw [neg_neg])))

/-- Self-cohomology of `vertexObject k G i` vanishes in every degree `d ∉ {0, 2}`. -/
theorem subsingleton_homology_vertexObject_self_of_ne (i : V) {d : ℤ}
    (hd0 : d ≠ 0) (hd2 : d ≠ 2) :
    Subsingleton ((dgHomComplex k (vertexObject k G i) (vertexObject k G i)).homology d) := by
  refine (vertexObjectHomologyEquivCorner k G i i d).toEquiv.subsingleton_congr.mpr ?_
  rw [cornerSubmodule_zigzagAlgebra_self_inf_integerGrade]
  simp only [hd0, hd2, ↓reduceIte]
  infer_instance

/-- Cohomology between two vertex objects vanishes outside degrees `{0, 1, 2}`. -/
theorem subsingleton_homology_vertexObject_of_not_mem (i j : V) {d : ℤ}
    (hd : d ∉ ({0, 1, 2} : Finset ℤ)) :
    Subsingleton ((dgHomComplex k (vertexObject k G i) (vertexObject k G j)).homology d) := by
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hd
  rcases hd with ⟨hd0, hd1, hd2⟩
  by_cases hij : i = j
  · exact hij ▸ subsingleton_homology_vertexObject_self_of_ne k G i hd0 hd2
  · refine (vertexObjectHomologyEquivCorner k G i j d).toEquiv.subsingleton_congr.mpr ?_
    have hbot : cornerSubmodule k (e i) (e j) ⊓ A d = ⊥ := by
      by_cases hadj : G.Adj j i
      · rw [cornerSubmodule_zigzagAlgebra_inf_integerGrade_of_adj k G hadj]; simp [hd1]
      · rw [cornerSubmodule_zigzagAlgebra_eq_bot_of_ne_of_not_adj k G hij (fun h ↦ hadj h.symm),
          bot_inf_eq]
    rw [hbot]; infer_instance

/-- Every pair of formal twisted objects in `ZigzagProjectiveTwistedClosure k G` satisfies
`TauCeti.HasFiniteTotalGradedHom` over a Noetherian commutative coefficient ring. -/
theorem hasFiniteTotalGradedHom [IsNoetherianRing k]
    (X Y : ZigzagProjectiveTwistedClosure k G) : HasFiniteTotalGradedHom k X Y :=
  HasFiniteTotalGradedHom.of_finset k (homSupport k G X Y)
    (subsingleton_homology_of_not_mem_homSupport k G X Y)

end CommRing

section Field

variable [Finite V] [Field k]

open scoped Classical in
/-- Over a field `k`, `finrank Hom^d(vertexObject i, vertexObject j)` is `1` in degrees `0, 2`
when `i = j`, `1` in degree `1` when `G.Adj i j`, and `0` otherwise. -/
@[simp]
theorem finrank_homology_vertexObject (i j : V) (d : ℤ) :
    Module.finrank k ((dgHomComplex k (vertexObject k G i) (vertexObject k G j)).homology d) =
      if i = j then if d = 0 ∨ d = 2 then 1 else 0
      else if G.Adj i j ∧ d = 1 then 1 else 0 :=
  (vertexObjectHomologyEquivCorner k G i j d).finrank_eq.trans
    (finrank_cornerSubmodule_zigzagAlgebra_inf_integerGrade k G i j d)

open scoped Classical in
/-- Total graded `Hom` dimension between vertex objects is `2` on the diagonal, `1` on edges, and
`0` on non-edges. -/
@[simp]
theorem dgTotalHomFinrank_vertexObject (i j : V) :
    dgTotalHomFinrank k (vertexObject k G i) (vertexObject k G j) =
      if i = j then 2 else if G.Adj i j then 1 else 0 := by
  classical
  rw [dgTotalHomFinrank_eq_sum k ({0, 1, 2} : Finset ℤ)
      (fun _ ↦ subsingleton_homology_vertexObject_of_not_mem k G i j),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  by_cases hij : i = j <;> by_cases hadj : G.Adj i j <;> simp [hij, hadj]

open scoped Classical in
/-- The graded Euler pairing `χ(vertexObject i, vertexObject j)` equals the symmetric generalized
Cartan pairing of `G`: `2` on the diagonal, `-1` on edges, and `0` on non-edges. -/
@[simp]
theorem dgEulerPairing_vertexObject (i j : V) :
    dgEulerPairing k (vertexObject k G i) (vertexObject k G j) =
      if i = j then 2 else if G.Adj i j then -1 else 0 := by
  classical
  rw [dgEulerPairing_eq_sum k ({0, 1, 2} : Finset ℤ)
      (fun _ ↦ subsingleton_homology_vertexObject_of_not_mem k G i j),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  have hp : (0 : ℤ).negOnePow = 1 ∧ (1 : ℤ).negOnePow = -1 ∧ (2 : ℤ).negOnePow = 1 := by decide
  rw [hp.1, hp.2.1, hp.2.2]
  by_cases hij : i = j <;> by_cases hadj : G.Adj i j <;> simp [hij, hadj]

/-- Every `vertexObject k G i` is unconditionally a Seidel–Thomas `2`-spherical object over a field
`k`, for **every** finite simple graph `G`. -/
theorem isSphericalObject_vertexObject (i : V) :
    IsSphericalObject k 2 (vertexObject k G i) where
  pos := by decide
  hasFiniteTotalGradedHom_from := hasFiniteTotalGradedHom k G (vertexObject k G i)
  finrank_homology_zero := by simp
  finrank_homology_top := by simp
  subsingleton_homology_of_ne := subsingleton_homology_vertexObject_self_of_ne k G i
  exists_trace_isPerfPair := by
    let v : (vertexObject k G i).obj.ι → V := fun _ ↦ i
    have hv : ∀ u, ((vertexObject k G i).obj.X u).obj.obj = D (v u) := by
      dsimp only [v]; rw [vertexObject_eq]; intro _; rfl
    have hc : ∀ u₁ u₂ : (vertexObject k G i).obj.ι,
        G.Adj (v u₁) (v u₂) → ((1 : kˣ) : k) = -((1 : kˣ) : k) :=
      fun _ _ hadj ↦ False.elim (G.ne_of_adj hadj rfl)
    refine ⟨homologyTrace k G (fun _ ↦ ((1 : kˣ) : k)) (vertexObject k G i) v hv hc, fun F d ↦ ?_⟩
    rw [← homologyPairing_eq_compr₂_homologyTrace]
    exact isPerfPair_homologyPairing k G (fun _ ↦ 1) (vertexObject k G i) F v hv hc d

/-- Every integer shift `(shiftFunctor k m).obj (vertexObject k G i)` is `2`-spherical. -/
theorem isSphericalObject_shiftFunctor_vertexObject (m : ℤ) (i : V) :
    IsSphericalObject k 2 ((DGTwistedObject.shiftFunctor k m).obj (vertexObject k G i)) :=
  (DGTwistedObject.isSphericalObject_shiftFunctor_iff 2 m (vertexObject k G i)).mpr
    (isSphericalObject_vertexObject k G i)

/-- Along any graph isomorphism `φ : SimpleGraph.pathGraph m ≃g G`, `fun i ↦ vertexObject k G (φ i)`
forms a Seidel–Thomas `A_m`-configuration of `2`-spherical objects. -/
theorem isAmSphericalConfiguration_of_pathGraphIso {m : ℕ} (φ : SimpleGraph.pathGraph m ≃g G) :
    IsAmSphericalConfiguration k m 2 (fun i ↦ vertexObject k G (φ i)) where
  isSphericalObject i := isSphericalObject_vertexObject k G (φ i)
  dgTotalHomFinrank_of_adj {i j} hadj := by
    have hadjG : G.Adj (φ i) (φ j) := φ.map_adj_iff.mpr (SimpleGraph.pathGraph_adj.mpr hadj)
    simp [dgTotalHomFinrank_vertexObject, G.ne_of_adj hadjG, hadjG]
  dgTotalHomFinrank_of_nonadj {i j} hne hnadj := by
    have hnadjG : ¬ G.Adj (φ i) (φ j) := by rwa [φ.map_adj_iff, SimpleGraph.pathGraph_adj]
    simp [dgTotalHomFinrank_vertexObject, hne, hnadjG]

/-- The `V × V` integer matrix of the graded Euler pairing `χ(vertexObject i, vertexObject j)`. -/
def eulerMatrix : Matrix V V ℤ :=
  Matrix.of fun i j ↦ dgEulerPairing k (vertexObject k G i) (vertexObject k G j)

/-- Entry `(i, j)` of `eulerMatrix k G` is `dgEulerPairing k (vertexObject i) (vertexObject j)`. -/
@[simp]
theorem eulerMatrix_apply (i j : V) :
    eulerMatrix k G i j = dgEulerPairing k (vertexObject k G i) (vertexObject k G j) := (rfl)

open scoped Classical Matrix in
/-- `eulerMatrix k G` is symmetric (`(eulerMatrix k G)ᵀ = eulerMatrix k G`). -/
@[simp]
theorem transpose_eulerMatrix : (eulerMatrix k G)ᵀ = eulerMatrix k G := by
  ext i j; simp [eq_comm, SimpleGraph.adj_comm]

end Field

section EulerReflection

variable [Fintype V] [DecidableEq V] [Field k]

private def eulerRankOne (r : V) : Matrix V V ℤ :=
  Matrix.of fun i j ↦ if i = r then eulerMatrix k G r j else 0

private theorem eulerRankOne_mul (r s : V) :
    eulerRankOne k G r * eulerRankOne k G s =
      eulerMatrix k G r s • Matrix.of fun i j ↦ if i = r then eulerMatrix k G s j else 0 := by
  ext i j
  simp only [eulerRankOne, Matrix.mul_apply, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul]
  by_cases hir : i = r <;> simp [hir]

private theorem eulerRankOne_mul_self (r : V) :
    eulerRankOne k G r * eulerRankOne k G r = (2 : ℤ) • eulerRankOne k G r := by
  rw [eulerRankOne_mul, show eulerMatrix k G r r = 2 by simp]; rfl

private theorem eulerRankOne_triple_of_adj {r s : V} (hadj : G.Adj r s) :
    eulerRankOne k G r * eulerRankOne k G s * eulerRankOne k G r = eulerRankOne k G r := by
  have hcrs : eulerMatrix k G r s = -1 := by simp [G.ne_of_adj hadj, hadj]
  have hcsr : eulerMatrix k G s r = -1 := by simp [(G.ne_of_adj hadj).symm, hadj.symm]
  rw [eulerRankOne_mul, hcrs, neg_one_smul, neg_mul]
  ext i j
  simp only [eulerRankOne, Matrix.neg_apply, Matrix.mul_apply, Matrix.of_apply, mul_ite, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  by_cases hir : i = r
  · subst i; simp only [↓reduceIte, hcsr, neg_mul, one_mul, neg_neg]
  · simp only [hir, ↓reduceIte, zero_mul, neg_zero]

/-- The numerical Seidel–Thomas twist matrix `R_r` on `ℤ^V`, representing the action
`[F] ↦ [F] - χ(E_r, F)[E_r]` in the vertex basis `[E_i]` (`i : V`) under `Matrix.mulVec`. -/
def eulerTwistMatrix (r : V) : Matrix V V ℤ :=
  1 - eulerRankOne k G r

/-- Entry `(i, j)` of `eulerTwistMatrix k G r`. -/
theorem eulerTwistMatrix_apply (r i j : V) :
    eulerTwistMatrix k G r i j =
      (if i = j then 1 else 0) - if i = r then eulerMatrix k G r j else 0 := by
  simp [eulerTwistMatrix, eulerRankOne, Matrix.one_apply]

/-- On `Pi.single j 1`, `eulerTwistMatrix k G r` acts by `e_j ↦ e_j - χ(E_r, E_j) e_r`. -/
theorem eulerTwistMatrix_mulVec_single (r j : V) :
    (eulerTwistMatrix k G r).mulVec (Pi.single j 1) =
      Pi.single j 1 - eulerMatrix k G r j • Pi.single r 1 := by
  ext i
  rw [Matrix.mulVec_single_one, Matrix.col_apply, eulerTwistMatrix_apply]
  simp only [Pi.sub_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul,
    mul_ite, mul_one, mul_zero, eq_comm]

/-- For a `2`-spherical vertex object `E_r`, `eulerTwistMatrix k G r` is an involution. -/
@[simp]
theorem eulerTwistMatrix_mul_self (r : V) :
    eulerTwistMatrix k G r * eulerTwistMatrix k G r = 1 := by
  simp only [eulerTwistMatrix, sub_mul, mul_sub, one_mul, mul_one, eulerRankOne_mul_self, two_zsmul]
  abel

/-- Numerical twists at non-adjacent vertices commute (`R_r * R_s = R_s * R_r`). -/
theorem eulerTwistMatrix_mul_comm_of_not_adj {r s : V} (hnadj : ¬ G.Adj r s) :
    eulerTwistMatrix k G r * eulerTwistMatrix k G s =
      eulerTwistMatrix k G s * eulerTwistMatrix k G r := by
  by_cases hrs : r = s
  · subst s; rfl
  · have hmul (u w : V) (hne : u ≠ w) (hn : ¬ G.Adj u w) :
        eulerRankOne k G u * eulerRankOne k G w = 0 := by
      rw [eulerRankOne_mul, show eulerMatrix k G u w = 0 by simp [hne, hn], zero_smul]
    simp only [eulerTwistMatrix, sub_mul, mul_sub, one_mul, mul_one,
      hmul r s hrs hnadj, hmul s r (Ne.symm hrs) (fun h ↦ hnadj h.symm), sub_zero]
    abel

/-- Numerical twists at adjacent vertices satisfy `R_r * R_s * R_r = R_s * R_r * R_s`. -/
theorem eulerTwistMatrix_braid_of_adj {r s : V} (hadj : G.Adj r s) :
    eulerTwistMatrix k G r * eulerTwistMatrix k G s * eulerTwistMatrix k G r =
      eulerTwistMatrix k G s * eulerTwistMatrix k G r * eulerTwistMatrix k G s := by
  have expand {u w : V} (h : G.Adj u w) :
      eulerTwistMatrix k G u * eulerTwistMatrix k G w * eulerTwistMatrix k G u =
        1 - eulerRankOne k G u - eulerRankOne k G w +
          eulerRankOne k G u * eulerRankOne k G w + eulerRankOne k G w * eulerRankOne k G u := by
    simp only [eulerTwistMatrix, sub_mul, mul_sub, one_mul, mul_one,
      eulerRankOne_mul_self, eulerRankOne_triple_of_adj k G h, two_zsmul]
    abel
  rw [expand hadj, expand hadj.symm]; abel

end EulerReflection

/-- For `SimpleGraph.pathGraph m` over a `Type`-level field `k`, the vertex objects form a
Seidel–Thomas `A_m`-configuration of `2`-spherical objects. -/
theorem isAmSphericalConfiguration_vertexObject (k : Type) [Field k] (m : ℕ) :
    IsAmSphericalConfiguration k m 2 (vertexObject k (SimpleGraph.pathGraph m)) :=
  isAmSphericalConfiguration_of_pathGraphIso k (SimpleGraph.pathGraph m) SimpleGraph.Iso.refl

/-- On `A₂ = SimpleGraph.pathGraph 2`, the numerical twist at vertex `0` is `!![-1, 1; 0, 1]`. -/
theorem eulerTwistMatrix_pathGraph_two_zero (k : Type) [Field k] :
    eulerTwistMatrix k (SimpleGraph.pathGraph 2) 0 = !![(-1 : ℤ), 1; 0, 1] := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [eulerTwistMatrix_apply, SimpleGraph.pathGraph_adj]

/-- On `A₂ = SimpleGraph.pathGraph 2`, the numerical twist at vertex `1` is `!![1, 0; 1, -1]`. -/
theorem eulerTwistMatrix_pathGraph_two_one (k : Type) [Field k] :
    eulerTwistMatrix k (SimpleGraph.pathGraph 2) 1 = !![(1 : ℤ), 0; 1, -1] := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [eulerTwistMatrix_apply, SimpleGraph.pathGraph_adj]

/-- Both `A₂` numerical twist reflections have determinant `-1`. -/
theorem det_eulerTwistMatrix_pathGraph_two (k : Type) [Field k] (r : Fin 2) :
    (eulerTwistMatrix k (SimpleGraph.pathGraph 2) r).det = -1 := by
  fin_cases r <;> simp [Matrix.det_fin_two, eulerTwistMatrix_apply, SimpleGraph.pathGraph_adj]

/-- Seidel–Thomas Check (`A₂`): both three-fold products `A * B * A` and `B * A * B` of the `A₂`
numerical twist matrices equal `!![0, -1; -1, 0]`. -/
theorem eulerTwistMatrix_pathGraph_two_braid (k : Type) [Field k] :
    eulerTwistMatrix k (SimpleGraph.pathGraph 2) 0 *
        eulerTwistMatrix k (SimpleGraph.pathGraph 2) 1 *
        eulerTwistMatrix k (SimpleGraph.pathGraph 2) 0 = !![(0 : ℤ), -1; -1, 0] ∧
      eulerTwistMatrix k (SimpleGraph.pathGraph 2) 1 *
        eulerTwistMatrix k (SimpleGraph.pathGraph 2) 0 *
        eulerTwistMatrix k (SimpleGraph.pathGraph 2) 1 = !![(0 : ℤ), -1; -1, 0] := by
  have hbraid := eulerTwistMatrix_braid_of_adj k (SimpleGraph.pathGraph 2)
    (by simp [SimpleGraph.pathGraph_adj] : (SimpleGraph.pathGraph 2).Adj 0 1)
  have hABA : eulerTwistMatrix k (SimpleGraph.pathGraph 2) 0 *
      eulerTwistMatrix k (SimpleGraph.pathGraph 2) 1 *
      eulerTwistMatrix k (SimpleGraph.pathGraph 2) 0 = !![(0 : ℤ), -1; -1, 0] := by
    rw [eulerTwistMatrix_pathGraph_two_zero, eulerTwistMatrix_pathGraph_two_one]
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  exact ⟨hABA, hbraid.symm.trans hABA⟩

end TauCeti.ZigzagProjectiveTwistedClosure
