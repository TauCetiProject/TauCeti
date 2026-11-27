/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.TensorProduct.Finite
public import TauCeti.LinearAlgebra.QuadraticForm.BaseChange
public import TauCeti.LinearAlgebra.QuadraticForm.RelevantPair.Stabilizer
import TauCeti.LinearAlgebra.TensorProduct.Submodule

/-!
# Scalar extension for orthogonal relevant pairs

Extension of scalars to a field extension `L / K` preserves `hyperbolicSum`, orthogonal
complements of nondegenerate finite-dimensional subspaces, framed orthogonal relevant pairs, and
the stabilizer embedding `SO(Q_W) →* SO(Q_V)`.

## Main definitions

* `TauCeti.baseChangeHyperbolicSum`: base change identification for `hyperbolicSum R j`.
* `TauCeti.baseChangeLine`: base change identification for rank-one diagonal forms `c • sq`.
* `TauCeti.OrthogonalRelevantPair.baseChange`,
  `TauCeti.FramedOrthogonalRelevantPair.baseChange`: scalar extension of relevant pairs.

## Main results

* `TauCeti.OrthogonalRelevantPair.orthogonal_baseChange_eq`: scalar extension commutes with taking
  the orthogonal complement of `range embed`.
* `TauCeti.OrthogonalRelevantPair.stabilizerHom_baseChange`: `stabilizerHom` commutes with
  `TauCeti.QuadraticMap.specialOrthogonalGroupBaseChange`.
-/

public section

open Module QuadraticMap QuadraticForm TauCeti.QuadraticMap

open scoped TensorProduct

namespace TauCeti

/-! ### Base change for split hyperbolic sums and rank-one forms -/

section HyperbolicSumBaseChange

variable {R : Type*} [CommRing R] [Invertible (2 : R)]

/-- Identifying `hyperbolicSum R j` with a diagonal weighted sum of squares on `Fin j × Fin 2`. -/
def hyperbolicSumEquivWeightedSumSquares (j : ℕ) :
    (hyperbolicSum R j).IsometryEquiv
      (weightedSumSquares R fun p : Fin j × Fin 2 ↦ if p.2 = 0 then (1 : R) else -1) where
  toLinearEquiv :=
    { toFun x p := x p.1 p.2
      invFun y i k := y (i, k)
      left_inv _ := rfl
      right_inv _ := rfl
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }
  map_app' x := by
    rw [weightedSumSquares_apply, hyperbolicSum_apply, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    simp [Fin.sum_univ_two, pow_two, sub_eq_add_neg]

@[simp]
theorem hyperbolicSumEquivWeightedSumSquares_apply (j : ℕ)
    (x : Fin j → Fin 2 → R) (p : Fin j × Fin 2) :
    hyperbolicSumEquivWeightedSumSquares (R := R) j x p = x p.1 p.2 :=
  (rfl)

@[simp]
theorem hyperbolicSumEquivWeightedSumSquares_symm_apply (j : ℕ)
    (y : Fin j × Fin 2 → R) (i : Fin j) (k : Fin 2) :
    (hyperbolicSumEquivWeightedSumSquares (R := R) j).symm y i k = y (i, k) :=
  (rfl)

private def weightedSumSquaresIndicatorEquiv (R : Type*) [CommRing R] (A : Type*)
    [CommRing A] [Algebra R A] (j : ℕ) :
    (weightedSumSquares A fun p : Fin j × Fin 2 ↦
        algebraMap R A (if p.2 = 0 then (1 : R) else -1)).IsometryEquiv
      (weightedSumSquares A fun p : Fin j × Fin 2 ↦ if p.2 = 0 then (1 : A) else -1) where
  toLinearEquiv := LinearEquiv.refl A (Fin j × Fin 2 → A)
  map_app' x := by
    simp only [weightedSumSquares_apply]
    refine Finset.sum_congr rfl fun p _ ↦ ?_
    split_ifs <;> simp

/-- Base change carries `hyperbolicSum R j` to `hyperbolicSum A j`. -/
noncomputable def baseChangeHyperbolicSum (j : ℕ) (A : Type*) [CommRing A] [Algebra R A]
    [Invertible (2 : A)] :
    ((hyperbolicSum R j).baseChange A).IsometryEquiv (hyperbolicSum A j) :=
  ((hyperbolicSumEquivWeightedSumSquares (R := R) j).baseChange A).trans
    ((QuadraticForm.baseChangeWeightedSumSquares (A := A)
        (fun p : Fin j × Fin 2 ↦ if p.2 = 0 then (1 : R) else -1)).trans
      ((weightedSumSquaresIndicatorEquiv R A j).trans
        (hyperbolicSumEquivWeightedSumSquares (R := A) j).symm))

@[simp]
theorem baseChangeHyperbolicSum_tmul (j : ℕ) (A : Type*) [CommRing A] [Algebra R A]
    [Invertible (2 : A)] (a : A) (x : Fin j → Fin 2 → R) (i : Fin j) (k : Fin 2) :
    baseChangeHyperbolicSum (R := R) j A (a ⊗ₜ x) i k = x i k • a := by
  have h1 :
      baseChangeHyperbolicSum (R := R) j A (a ⊗ₜ x) i k =
        (hyperbolicSumEquivWeightedSumSquares (R := A) j).symm
          (QuadraticForm.baseChangeWeightedSumSquares (A := A)
            (fun p : Fin j × Fin 2 ↦ if p.2 = 0 then (1 : R) else -1)
            ((hyperbolicSumEquivWeightedSumSquares (R := R) j).baseChange A
              (a ⊗ₜ x))) i k :=
    rfl
  rw [h1, QuadraticMap.IsometryEquiv.baseChange_tmul,
    QuadraticForm.baseChangeWeightedSumSquares_apply, TensorProduct.piScalarRightHom_tmul]
  rfl

/-- Base change carries a rank-one diagonal form `c • sq` to `algebraMap R A c • sq`. -/
def baseChangeLine (c : R) (A : Type*) [CommRing A] [Algebra R A] :
    (QuadraticForm.baseChange A (c • (QuadraticMap.sq : QuadraticForm R R))).IsometryEquiv
      (algebraMap R A c • (QuadraticMap.sq : QuadraticForm A A)) where
  toLinearEquiv := TensorProduct.AlgebraTensorModule.rid R A A
  map_app' x := by
    have h : (algebraMap R A c • (QuadraticMap.sq : QuadraticForm A A)).comp
          (TensorProduct.AlgebraTensorModule.rid R A A).toLinearMap =
        QuadraticForm.baseChange A (c • (QuadraticMap.sq : QuadraticForm R R)) := by
      apply baseChange_ext
      intro r
      simp [TensorProduct.AlgebraTensorModule.rid_tmul, Algebra.smul_def]
    exact DFunLike.congr_fun h x

@[simp]
theorem baseChangeLine_tmul (c : R) (A : Type*) [CommRing A] [Algebra R A] (a : A) (r : R) :
    baseChangeLine c A (a ⊗ₜ r) = r • a :=
  TensorProduct.AlgebraTensorModule.rid_tmul A r a

end HyperbolicSumBaseChange

/-! ### Scalar extension of relevant pairs -/

section BaseChange

variable {K : Type*} [Field K] [Invertible (2 : K)]
  {W V : Type*} [AddCommGroup W] [Module K W] [FiniteDimensional K W]
  [AddCommGroup V] [Module K V]
  {Q_W : QuadraticForm K W} {Q_V : QuadraticForm K V} {j : ℕ}

namespace OrthogonalRelevantPair

/-- Scalar extension of `W^⊥` equals the orthogonal complement of `range (embed.baseChange L)`
in `L ⊗[K] V`. -/
theorem orthogonal_baseChange_eq (P : OrthogonalRelevantPair Q_W Q_V j)
    (L : Type*) [Field L] [Algebra K L] [Invertible (2 : L)] :
    P.orthogonal.baseChange L =
      LinearMap.BilinForm.orthogonal (Q_V.baseChange L).polarBilin
        (LinearMap.range (P.embed.baseChange L).toLinearMap) := by
  set S := LinearMap.range P.embed.toLinearMap
  set S_L := LinearMap.range (P.embed.baseChange L).toLinearMap
  set U_L := LinearMap.BilinForm.orthogonal (Q_V.baseChange L).polarBilin S_L
  have hS_L : S.baseChange L = S_L := by
    rw [LinearMap.baseChange_range, ← Isometry.baseChange_toLinearMap]
  have hle : P.orthogonal.baseChange L ≤ U_L := by
    rw [Submodule.baseChange_le_iff_le_comap]
    intro v hv
    rw [Submodule.mem_comap]
    -- Expose `Submodule.toBaseChange` as the pure tensor `(1 : L) ⊗ₜ[K] v`.
    change (1 : L) ⊗ₜ[K] v ∈ U_L
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro x hx
    have hx' : x ∈ S.baseChange L := hS_L.symm ▸ hx
    have hker :
        S.baseChange L ≤ LinearMap.ker ((Q_V.baseChange L).polarBilin.flip (1 ⊗ₜ v)) := by
      rw [Submodule.baseChange_le_iff_le_comap]
      rintro _ ⟨w, rfl⟩
      rw [Submodule.mem_comap]
      -- Expose `Submodule.toBaseChange` as `(1 : L) ⊗ₜ[K] P.embed w`.
      change (1 : L) ⊗ₜ[K] (P.embed w) ∈
        LinearMap.ker ((Q_V.baseChange L).polarBilin.flip (1 ⊗ₜ v))
      simp only [LinearMap.mem_ker, LinearMap.flip_apply, QuadraticMap.polarBilin_apply_apply,
        QuadraticForm.polar_baseChange_tmul]
      rw [P.mem_orthogonal_iff.mp hv w, zero_smul]
    exact hker hx'
  refine le_antisymm hle fun x hx ↦ ?_
  have hsup : S_L ⊔ P.orthogonal.baseChange L = ⊤ := by
    rw [← hS_L, ← Submodule.baseChange_sup, P.isCompl_orthogonal.sup_eq_top,
      Submodule.baseChange_top]
  have hndW : (Q_W.baseChange L).Nondegenerate :=
    QuadraticForm.Nondegenerate.baseChange P.nondegenerate_domain
  have hinj : Function.Injective (P.embed.baseChange L) :=
    (P.embed.baseChange L).injective_of_radical_eq_bot hndW.radical_eq_bot
  let eRange : (Q_W.baseChange L).IsometryEquiv ((Q_V.baseChange L).restrict S_L) :=
    { toLinearEquiv := LinearEquiv.ofInjective (P.embed.baseChange L).toLinearMap hinj
      map_app' w := (P.embed.baseChange L).map_app w }
  have : FiniteDimensional L S_L := Module.Finite.equiv eRange.toLinearEquiv
  have hcomp : IsCompl S_L U_L :=
    (eRange.nondegenerate_iff.mp hndW).isCompl_orthogonal
  obtain ⟨s, hs, u, hu, rfl⟩ := Submodule.mem_sup.mp (hsup ▸ Submodule.mem_top (x := x))
  have hsU : s ∈ U_L := by
    have : s = (s + u) - u := (add_sub_cancel_right s u).symm
    rw [this]
    exact U_L.sub_mem hx (hle hu)
  have hs0 : s = 0 := Submodule.disjoint_def.mp hcomp.disjoint s hs hsU
  simpa [hs0] using hu

/-- The canonical isometric equivalence identifying `(Q_V|_{W^⊥}).baseChange L` with
`(Q_V.baseChange L)|_{(range (embed.baseChange L))^⊥}`. -/
noncomputable def orthogonalBaseChangeIsometryEquiv (P : OrthogonalRelevantPair Q_W Q_V j)
    (L : Type*) [Field L] [Algebra K L] [Invertible (2 : L)] :
    (QuadraticForm.baseChange L (Q_V.restrict P.orthogonal)).IsometryEquiv
      ((Q_V.baseChange L).restrict
        (LinearMap.BilinForm.orthogonal (Q_V.baseChange L).polarBilin
          (LinearMap.range (P.embed.baseChange L).toLinearMap))) where
  toLinearEquiv :=
    (Submodule.toBaseChange.toLinearEquiv L P.orthogonal).trans
      (LinearEquiv.ofEq _ _ (P.orthogonal_baseChange_eq L))
  map_app' x := by
    set φ := (Submodule.toBaseChange.toLinearEquiv L P.orthogonal).trans
      (LinearEquiv.ofEq _ _ (P.orthogonal_baseChange_eq L))
    have h : ((Q_V.baseChange L).restrict _).comp φ.toLinearMap =
        QuadraticForm.baseChange L (Q_V.restrict P.orthogonal) := by
      apply baseChange_ext
      intro u
      simp [φ]
    exact DFunLike.congr_fun h x

@[simp]
theorem coe_orthogonalBaseChangeIsometryEquiv_tmul (P : OrthogonalRelevantPair Q_W Q_V j)
    (L : Type*) [Field L] [Algebra K L] [Invertible (2 : L)]
    (a : L) (u : P.orthogonal) :
    ((P.orthogonalBaseChangeIsometryEquiv L (a ⊗ₜ u) : _) : L ⊗[K] V) = a ⊗ₜ (u : V) :=
  (rfl)

/-- Extend scalars of an unframed orthogonal relevant pair to a field extension `L / K`. -/
noncomputable def baseChange (P : OrthogonalRelevantPair Q_W Q_V j)
    (L : Type*) [Field L] [Algebra K L] [Invertible (2 : L)] :
    OrthogonalRelevantPair (Q_W.baseChange L) (Q_V.baseChange L) j where
  embed := P.embed.baseChange L
  nondegenerate_domain := QuadraticForm.Nondegenerate.baseChange P.nondegenerate_domain
  exists_complement := by
    obtain ⟨c, ⟨e⟩⟩ := P.exists_complement
    refine ⟨Units.map (algebraMap K L : K →* L) c, ⟨?_⟩⟩
    exact (P.orthogonalBaseChangeIsometryEquiv L).symm.trans
      ((e.baseChangeProd L).trans ((baseChangeHyperbolicSum (R := K) j L).prod
        (baseChangeLine (c : K) L)))

@[simp]
theorem baseChange_embed (P : OrthogonalRelevantPair Q_W Q_V j)
    (L : Type*) [Field L] [Algebra K L] [Invertible (2 : L)] :
    (P.baseChange L).embed = P.embed.baseChange L :=
  (rfl)

theorem baseChange_embed_tmul (P : OrthogonalRelevantPair Q_W Q_V j)
    (L : Type*) [Field L] [Algebra K L] [Invertible (2 : L)] (a : L) (w : W) :
    (P.baseChange L).embed (a ⊗ₜ w) = a ⊗ₜ P.embed w :=
  QuadraticMap.Isometry.baseChange_tmul P.embed a w

/-- Scalar extension commutes with the stabilizer embedding `SO(Q_W) →* SO(Q_V)`. -/
theorem stabilizerHom_baseChange [FiniteDimensional K V]
    (P : OrthogonalRelevantPair Q_W Q_V j)
    (L : Type*) [Field L] [Algebra K L] [Invertible (2 : L)]
    (g : specialOrthogonalGroup Q_W) :
    specialOrthogonalGroupBaseChange (A := L) Q_V (P.stabilizerHom g) =
      (P.baseChange L).stabilizerHom (specialOrthogonalGroupBaseChange (A := L) Q_W g) := by
  apply Subtype.ext
  apply LinearEquiv.toLinearMap_injective
  apply TensorProduct.AlgebraTensorModule.ext
  intro a v
  obtain ⟨⟨w, u⟩, rfl⟩ := P.ambientIsometryEquiv.toLinearEquiv.surjective v
  rw [← mul_one a, ← smul_eq_mul, ← TensorProduct.smul_tmul',
    QuadraticMap.IsometryEquiv.coe_toLinearEquiv, P.ambientIsometryEquiv_apply,
    TensorProduct.tmul_add]
  simp only [LinearEquiv.coe_coe, map_smul, map_add,
    specialOrthogonalGroupBaseChange_apply_tmul]
  rw [P.stabilizerHom_apply_embed, P.stabilizerHom_apply_of_mem_orthogonal g u.property]
  congr 2
  · rw [← P.baseChange_embed_tmul L 1 w,
      (P.baseChange L).stabilizerHom_apply_embed,
      specialOrthogonalGroupBaseChange_apply_tmul, baseChange_embed_tmul]
  · have hu : (1 : L) ⊗ₜ[K] (u : V) ∈ (P.baseChange L).orthogonal := by
      rw [orthogonal, baseChange_embed, ← P.orthogonal_baseChange_eq L]
      exact Submodule.tmul_mem_baseChange_of_mem 1 u.property
    exact ((P.baseChange L).stabilizerHom_apply_of_mem_orthogonal _ hu).symm

end OrthogonalRelevantPair

namespace FramedOrthogonalRelevantPair

/-- Extend scalars of a framed orthogonal relevant pair to a field extension `L / K`. -/
noncomputable def baseChange (F : FramedOrthogonalRelevantPair Q_W Q_V j)
    (L : Type*) [Field L] [Algebra K L] [Invertible (2 : L)] :
    FramedOrthogonalRelevantPair (Q_W.baseChange L) (Q_V.baseChange L) j where
  embed := F.embed.baseChange L
  nondegenerate_domain := QuadraticForm.Nondegenerate.baseChange F.nondegenerate_domain
  lineCoeff := Units.map (algebraMap K L : K →* L) F.lineCoeff
  complementEquiv :=
    (F.toOrthogonalRelevantPair.orthogonalBaseChangeIsometryEquiv L).symm.trans
      ((F.complementEquiv.baseChangeProd L).trans ((baseChangeHyperbolicSum (R := K) j L).prod
        (baseChangeLine (F.lineCoeff : K) L)))

@[simp]
theorem baseChange_toOrthogonalRelevantPair (F : FramedOrthogonalRelevantPair Q_W Q_V j)
    (L : Type*) [Field L] [Algebra K L] [Invertible (2 : L)] :
    (F.baseChange L).toOrthogonalRelevantPair =
      F.toOrthogonalRelevantPair.baseChange L := by
  ext x
  simp
  rfl

@[simp]
theorem baseChange_embed (F : FramedOrthogonalRelevantPair Q_W Q_V j)
    (L : Type*) [Field L] [Algebra K L] [Invertible (2 : L)] :
    (F.baseChange L).embed = F.embed.baseChange L :=
  (rfl)

@[simp]
theorem baseChange_lineCoeff (F : FramedOrthogonalRelevantPair Q_W Q_V j)
    (L : Type*) [Field L] [Algebra K L] [Invertible (2 : L)] :
    (F.baseChange L).lineCoeff = Units.map (algebraMap K L : K →* L) F.lineCoeff :=
  (rfl)

@[simp]
theorem baseChange_lineVector (F : FramedOrthogonalRelevantPair Q_W Q_V j)
    (L : Type*) [Field L] [Algebra K L] [Invertible (2 : L)] :
    (F.baseChange L).lineVector = (1 : L) ⊗ₜ[K] F.lineVector := by
  have hmem : (1 : L) ⊗ₜ[K] F.lineVector ∈ (F.baseChange L).orthogonal := by
    rw [orthogonal, baseChange_toOrthogonalRelevantPair, OrthogonalRelevantPair.orthogonal,
      OrthogonalRelevantPair.baseChange_embed,
      ← F.toOrthogonalRelevantPair.orthogonal_baseChange_eq L]
    exact Submodule.tmul_mem_baseChange_of_mem 1 F.lineVector_mem_orthogonal
  have h :
      (F.baseChange L).complementEquiv ⟨(1 : L) ⊗ₜ[K] F.lineVector, hmem⟩ =
        (0, (1 : L)) := by
    let u0 : LinearMap.BilinForm.orthogonal Q_V.polarBilin (LinearMap.range F.embed.toLinearMap) :=
      ⟨F.lineVector, F.lineVector_mem_orthogonal⟩
    have hline : F.complementEquiv u0 = (0, (1 : K)) := by
      rw [← F.complementEquiv.apply_symm_apply (0, (1 : K))]
      congr 1
      ext
      exact F.lineVector_eq
    have hinv :
        (F.toOrthogonalRelevantPair.orthogonalBaseChangeIsometryEquiv L).symm
            ⟨(1 : L) ⊗ₜ[K] F.lineVector, hmem⟩ =
          (1 : L) ⊗ₜ[K] u0 :=
      (F.toOrthogonalRelevantPair.orthogonalBaseChangeIsometryEquiv L).symm_apply_eq.mpr
        (Subtype.ext rfl)
    have hcomp :
        (F.baseChange L).complementEquiv ⟨(1 : L) ⊗ₜ[K] F.lineVector, hmem⟩ =
          ((baseChangeHyperbolicSum (R := K) j L).prod (baseChangeLine (F.lineCoeff : K) L))
            ((F.complementEquiv.baseChangeProd L)
              ((F.toOrthogonalRelevantPair.orthogonalBaseChangeIsometryEquiv L).symm
                ⟨(1 : L) ⊗ₜ[K] F.lineVector, hmem⟩)) :=
      rfl
    rw [hcomp, hinv, IsometryEquiv.baseChangeProd_tmul, hline, IsometryEquiv.prod_apply]
    refine Prod.ext ?_ (by simp)
    ext i k
    simp
  have hsymm := congrArg (fun x : (F.baseChange L).orthogonal ↦ (x : L ⊗[K] V))
    ((F.baseChange L).complementEquiv.symm_apply_eq.mpr h.symm)
  rw [(F.baseChange L).lineVector_eq]
  exact hsymm

end FramedOrthogonalRelevantPair

end BaseChange

end TauCeti
