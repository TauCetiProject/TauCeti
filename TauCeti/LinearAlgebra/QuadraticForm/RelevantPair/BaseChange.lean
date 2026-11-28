/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.TensorProduct.Finite
public import TauCeti.LinearAlgebra.QuadraticForm.BaseChange
public import TauCeti.LinearAlgebra.QuadraticForm.Hyperbolic.BaseChange
public import TauCeti.LinearAlgebra.QuadraticForm.RelevantPair.Stabilizer

/-!
# Scalar extension for orthogonal relevant pairs

Extension of scalars to a field extension `L / K` preserves orthogonal complements of
subspaces, orthogonal relevant pairs, framed orthogonal relevant pairs, and the stabilizer
embedding `SO(Q_W) →* SO(Q_V)`.

## Main definitions

* `TauCeti.OrthogonalRelevantPair.baseChange`,
  `TauCeti.FramedOrthogonalRelevantPair.baseChange`: scalar extension of relevant pairs.

## Main results

* `TauCeti.OrthogonalRelevantPair.orthogonal_baseChange_eq`: scalar extension commutes with taking
  the orthogonal complement of `range embed`.
* `TauCeti.OrthogonalRelevantPair.stabilizerHom_baseChange`: `stabilizerHom` commutes with
  `TauCeti.QuadraticMap.specialOrthogonalGroupBaseChange`.
* `TauCeti.FramedOrthogonalRelevantPair.baseChange_complementEquiv_symm_tmul`: the base-changed
  inverse framing sends base-changed vectors to pure tensors.
* `TauCeti.FramedOrthogonalRelevantPair.baseChange_lineVector`: the distinguished line vector of
  the scalar-extended frame is `1 ⊗ₜ F.lineVector`.
-/

public section

open Module QuadraticMap QuadraticForm TauCeti.QuadraticMap

open scoped TensorProduct

namespace TauCeti

/-! ### Scalar extension of relevant pairs -/

section BaseChange

variable {K : Type*} [Field K] [Invertible (2 : K)]
  {W V : Type*} [AddCommGroup W] [Module K W]
  [AddCommGroup V] [Module K V]
  {Q_W : QuadraticForm K W} {Q_V : QuadraticForm K V} {j : ℕ}

namespace OrthogonalRelevantPair

/-- Scalar extension of `W^⊥` equals the orthogonal complement of `range (embed.baseChange L)`
in `L ⊗[K] V`. -/
theorem orthogonal_baseChange_eq (P : OrthogonalRelevantPair Q_W Q_V j)
    (L : Type*) [Field L] [Algebra K L] :
    P.orthogonal.baseChange L =
      LinearMap.BilinForm.orthogonal (Q_V.baseChange L).polarBilin
        (LinearMap.range (P.embed.baseChange L).toLinearMap) :=
  P.embed.orthogonal_range_baseChange L

/-- The canonical isometric equivalence identifying `(Q_V|_{W^⊥}).baseChange L` with
`(Q_V.baseChange L)|_{(range (embed.baseChange L))^⊥}`. -/
noncomputable def orthogonalBaseChangeIsometryEquiv (P : OrthogonalRelevantPair Q_W Q_V j)
    (L : Type*) [Field L] [Algebra K L] :
    (QuadraticForm.baseChange L (Q_V.restrict P.orthogonal)).IsometryEquiv
      ((Q_V.baseChange L).restrict
        (LinearMap.BilinForm.orthogonal (Q_V.baseChange L).polarBilin
          (LinearMap.range (P.embed.baseChange L).toLinearMap))) :=
  (Q_V.baseChangeRestrict L P.orthogonal).trans
    ((IsometryEquiv.refl (Q_V.baseChange L)).ofSubmodules _ _ (by
      rw [show (IsometryEquiv.refl (Q_V.baseChange L)).toLinearMap = LinearMap.id from rfl,
        Submodule.map_id]
      exact P.orthogonal_baseChange_eq L))

/-- On pure tensors, `orthogonalBaseChangeIsometryEquiv` sends `a ⊗ₜ u` to the vector with
ambient coordinate `a ⊗ₜ (u : V)`. -/
@[simp]
theorem coe_orthogonalBaseChangeIsometryEquiv_tmul (P : OrthogonalRelevantPair Q_W Q_V j)
    (L : Type*) [Field L] [Algebra K L]
    (a : L) (u : P.orthogonal) :
    ((P.orthogonalBaseChangeIsometryEquiv L (a ⊗ₜ u) : _) : L ⊗[K] V) = a ⊗ₜ (u : V) := by
  simp [orthogonalBaseChangeIsometryEquiv]

/-- Extend a complement framing `W^⊥ ≃qᵢ H^j ⊥ ⟨c⟩` along a field extension `L / K`. -/
noncomputable def baseChangeComplementEquiv (P : OrthogonalRelevantPair Q_W Q_V j)
    (L : Type*) [Field L] [Algebra K L] [Invertible (2 : L)] (c : Kˣ)
    (e : (Q_V.restrict P.orthogonal).IsometryEquiv
      ((hyperbolicSum K j).prod ((c : K) • QuadraticMap.sq))) :
    ((Q_V.baseChange L).restrict
        (LinearMap.BilinForm.orthogonal (Q_V.baseChange L).polarBilin
          (LinearMap.range (P.embed.baseChange L).toLinearMap))).IsometryEquiv
      ((hyperbolicSum L j).prod
        (((Units.map (algebraMap K L : K →* L) c : Lˣ) : L) • QuadraticMap.sq)) :=
  (P.orthogonalBaseChangeIsometryEquiv L).symm.trans
    ((e.baseChangeProd L).trans
      ((baseChangeHyperbolicSum (R := K) j L).prod
        ((baseChangeLine (c : K) L).trans
          (IsometryEquiv.ofEq
            (congrArg (· • (QuadraticMap.sq : QuadraticForm L L))
              (Units.coe_map (algebraMap K L : K →* L) c).symm)))))

/-- The inverse of the base-changed complement framing maps base-changed coordinate tuples to
pure tensors. -/
@[simp]
theorem baseChangeComplementEquiv_symm_tmul (P : OrthogonalRelevantPair Q_W Q_V j)
    (L : Type*) [Field L] [Algebra K L] [Invertible (2 : L)] (c : Kˣ)
    (e : (Q_V.restrict P.orthogonal).IsometryEquiv
      ((hyperbolicSum K j).prod ((c : K) • QuadraticMap.sq)))
    (a : L) (y : (Fin j → Fin 2 → K) × K) :
    ((P.baseChangeComplementEquiv L c e).symm (fun i k ↦ y.1 i k • a, y.2 • a) : L ⊗[K] V) =
      a ⊗ₜ[K] (e.symm y : V) := by
  have hmem : a ⊗ₜ[K] (e.symm y : V) ∈
      LinearMap.BilinForm.orthogonal (Q_V.baseChange L).polarBilin
        (LinearMap.range (P.embed.baseChange L).toLinearMap) := by
    rw [← P.orthogonal_baseChange_eq L]
    exact Submodule.tmul_mem_baseChange_of_mem a (e.symm y).property
  have hinv :
      (P.orthogonalBaseChangeIsometryEquiv L).symm ⟨a ⊗ₜ[K] (e.symm y : V), hmem⟩ =
        a ⊗ₜ[K] e.symm y :=
    (P.orthogonalBaseChangeIsometryEquiv L).symm_apply_eq.mpr
      (Subtype.ext (P.coe_orthogonalBaseChangeIsometryEquiv_tmul L a (e.symm y)).symm)
  have hf :
      P.baseChangeComplementEquiv L c e ⟨a ⊗ₜ[K] (e.symm y : V), hmem⟩ =
        (fun i k ↦ y.1 i k • a, y.2 • a) := by
    dsimp only [baseChangeComplementEquiv]
    rw [IsometryEquiv.trans_apply, IsometryEquiv.trans_apply, hinv,
      IsometryEquiv.baseChangeProd_tmul, e.apply_symm_apply y, IsometryEquiv.prod_apply]
    refine Prod.ext (funext fun i ↦ funext fun k ↦ ?_) ?_
    · exact baseChangeHyperbolicSum_tmul (R := K) j L a y.1 i k
    · rw [IsometryEquiv.trans_apply, IsometryEquiv.ofEq_apply]
      exact baseChangeLine_tmul (c : K) L a y.2
  exact congrArg Subtype.val
    ((P.baseChangeComplementEquiv L c e).symm_apply_eq.mpr hf.symm)

/-- Extend scalars of an unframed orthogonal relevant pair to a field extension `L / K`. -/
noncomputable def baseChange (P : OrthogonalRelevantPair Q_W Q_V j)
    (L : Type*) [Field L] [Algebra K L] [Invertible (2 : L)] :
    OrthogonalRelevantPair (Q_W.baseChange L) (Q_V.baseChange L) j where
  embed := P.embed.baseChange L
  nondegenerate_domain := QuadraticForm.Nondegenerate.baseChange P.nondegenerate_domain
  exists_complement := by
    obtain ⟨c, ⟨e⟩⟩ := P.exists_complement
    exact ⟨Units.map (algebraMap K L : K →* L) c, ⟨P.baseChangeComplementEquiv L c e⟩⟩

/-- Scalar extension of `P` extends its underlying isometric embedding `P.embed`. -/
@[simp]
theorem baseChange_embed (P : OrthogonalRelevantPair Q_W Q_V j)
    (L : Type*) [Field L] [Algebra K L] [Invertible (2 : L)] :
    (P.baseChange L).embed = P.embed.baseChange L :=
  (rfl)

/-- On pure tensors, `(P.baseChange L).embed` applies `P.embed` to the vector factor. -/
theorem baseChange_embed_tmul (P : OrthogonalRelevantPair Q_W Q_V j)
    (L : Type*) [Field L] [Algebra K L] [Invertible (2 : L)] (a : L) (w : W) :
    (P.baseChange L).embed (a ⊗ₜ w) = a ⊗ₜ P.embed w :=
  QuadraticMap.Isometry.baseChange_tmul P.embed a w

/-- Scalar extension commutes with the stabilizer embedding `SO(Q_W) →* SO(Q_V)`. -/
theorem stabilizerHom_baseChange [FiniteDimensional K W] [FiniteDimensional K V]
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
  rw [TensorProduct.tmul_eq_smul_one_tmul, QuadraticMap.IsometryEquiv.coe_toLinearEquiv,
    P.ambientIsometryEquiv_apply, TensorProduct.tmul_add]
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
    F.toOrthogonalRelevantPair.baseChangeComplementEquiv L F.lineCoeff F.complementEquiv

/-- Scalar extension of a framed pair extends its underlying isometric embedding `F.embed`. -/
@[simp]
theorem baseChange_embed (F : FramedOrthogonalRelevantPair Q_W Q_V j)
    (L : Type*) [Field L] [Algebra K L] [Invertible (2 : L)] :
    (F.baseChange L).embed = F.embed.baseChange L :=
  (rfl)

/-- Forgetting the framing commutes with scalar extension. -/
@[simp]
theorem baseChange_toOrthogonalRelevantPair (F : FramedOrthogonalRelevantPair Q_W Q_V j)
    (L : Type*) [Field L] [Algebra K L] [Invertible (2 : L)] :
    (F.baseChange L).toOrthogonalRelevantPair =
      F.toOrthogonalRelevantPair.baseChange L := by
  ext x
  simp

/-- Scalar extension maps the distinguished line coefficient by `algebraMap K L`. -/
@[simp]
theorem baseChange_lineCoeff (F : FramedOrthogonalRelevantPair Q_W Q_V j)
    (L : Type*) [Field L] [Algebra K L] [Invertible (2 : L)] :
    (F.baseChange L).lineCoeff = Units.map (algebraMap K L : K →* L) F.lineCoeff :=
  (rfl)

/-- The inverse framing of the scalar-extended pair maps base-changed coordinate tuples to pure
tensors. -/
@[simp]
theorem baseChange_complementEquiv_symm_tmul (F : FramedOrthogonalRelevantPair Q_W Q_V j)
    (L : Type*) [Field L] [Algebra K L] [Invertible (2 : L)]
    (a : L) (y : (Fin j → Fin 2 → K) × K) :
    (((F.baseChange L).complementEquiv.symm (fun i k ↦ y.1 i k • a, y.2 • a) :
        LinearMap.BilinForm.orthogonal (Q_V.baseChange L).polarBilin
          (LinearMap.range (F.baseChange L).embed.toLinearMap)) : L ⊗[K] V) =
      a ⊗ₜ[K] (F.complementEquiv.symm y : V) :=
  F.toOrthogonalRelevantPair.baseChangeComplementEquiv_symm_tmul L F.lineCoeff F.complementEquiv a y

/-- The distinguished line vector of the scalar-extended frame is the pure tensor
`1 ⊗ₜ F.lineVector`. -/
@[simp]
theorem baseChange_lineVector (F : FramedOrthogonalRelevantPair Q_W Q_V j)
    (L : Type*) [Field L] [Algebra K L] [Invertible (2 : L)] :
    (F.baseChange L).lineVector = (1 : L) ⊗ₜ[K] F.lineVector := by
  have h : (fun i k ↦ ((0 : Fin j → Fin 2 → K) i k) • (1 : L), (1 : K) • (1 : L)) =
      ((0 : Fin j → Fin 2 → L), (1 : L)) := by
    ext <;> simp
  rw [lineVector_eq, lineVector_eq, ← h]
  exact F.baseChange_complementEquiv_symm_tmul L 1 (0, 1)

end FramedOrthogonalRelevantPair

end BaseChange

end TauCeti
