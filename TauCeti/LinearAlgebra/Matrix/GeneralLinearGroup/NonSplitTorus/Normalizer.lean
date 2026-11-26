/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.Galois.Basic
public import TauCeti.LinearAlgebra.GeneralLinearGroup.FieldExtension
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.NonSplitTorus.Basic
import Mathlib.FieldTheory.Finite.GaloisField
import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Card

/-!
# The normalizer of the non-split torus of `GL₂`

Let `E/F` be a field extension of degree `2`. The normalizer of the non-split torus
`TauCeti.GL2NonSplitTorus F E ≅ Eˣ` of `GL₂(F)` consists of the `F`-linear automorphisms of `E` of
the form `v ↦ c τ(v)` with `c ∈ Eˣ` and `τ` an `F`-algebra automorphism of `E`, read in the basis
`TauCeti.nonSplitTorusBasis`. The pair `(c, τ)` is unique, so the normalizer is in bijection with
`Eˣ × Gal(E/F)` (`TauCeti.GL2NonSplitTorus.normalizerEquiv`). Over a finite field with `q`
elements it therefore has `2(q² - 1)` elements, the torus has index `2` in it, and its index in
`GL₂(F)` is `q(q - 1) / 2` (`TauCeti.GL2NonSplitTorus.natCard_normalizer`,
`TauCeti.GL2NonSplitTorus.relIndex_normalizer`,
`TauCeti.GL2NonSplitTorus.two_mul_index_normalizer`). This is the subgroup `C_ns⁺(ℓ)` of the
standard levels of modular curves.

The computation is made for the general linear group of `E` as an `F`-vector space, in
`TauCeti/LinearAlgebra/GeneralLinearGroup/FieldExtension.lean`: the basis isomorphism carries the
torus to the image `TauCeti.lmulUnitsRange F E` of `Eˣ` under left multiplication
(`TauCeti.GL2NonSplitTorus.map_toLin'`), whose normalizer is described there.

## Main declarations

* `TauCeti.GL2NonSplitTorus.mem_normalizer_iff`: the normalizer consists of the matrices of the
  maps `v ↦ c τ(v)`.
* `TauCeti.GL2NonSplitTorus.normalizerEquiv`, `TauCeti.GL2NonSplitTorus.natCard_normalizer`,
  `TauCeti.GL2NonSplitTorus.relIndex_normalizer`,
  `TauCeti.GL2NonSplitTorus.two_mul_index_normalizer`,
  `TauCeti.GL2NonSplitTorus.neg_one_mem_normalizer`.

## References

* D. Zywina, *On the possible images of the mod `ℓ` representations associated to elliptic curves
  over `ℚ`*, arXiv:1508.07660, §1 (Notation).
-/

public section

open Matrix

namespace TauCeti

variable {F : Type*} [Field F] {E : Type*} [Field E] [Algebra F E]

namespace GL2NonSplitTorus

variable [Algebra.IsQuadraticExtension F E]

/-- The basis isomorphism `GL₂(F) ≃* GL_F(E)` carries the non-split torus to the units of `E`
acting by multiplication. -/
theorem map_toLin' :
    (GL2NonSplitTorus F E).map
        (Matrix.GeneralLinearGroup.toLin' (nonSplitTorusBasis F E)).toMonoidHom =
      lmulUnitsRange F E := by
  have h (x : Eˣ) : Matrix.GeneralLinearGroup.toLin' (nonSplitTorusBasis F E)
      (GL2NonSplitTorusHom F E x) = Units.map (Algebra.lmul F E : E →* Module.End F E) x := by
    refine Units.ext (LinearMap.ext fun v ↦ ?_)
    have := Matrix.GeneralLinearGroup.toLin'_apply (nonSplitTorusBasis F E)
      (GL2NonSplitTorusHom F E x) v
    rw [coe_gl2NonSplitTorusHom, Algebra.leftMulMatrix_mulVec_repr,
      Fintype.linearCombination_apply, Module.Basis.sum_repr] at this
    simpa [Algebra.coe_lmul_eq_mul, LinearMap.mul_apply'] using this
  ext u
  simp only [Subgroup.mem_map, MulEquiv.coe_toMonoidHom, mem_lmulUnitsRange_iff]
  constructor
  · rintro ⟨g, hg, rfl⟩
    obtain ⟨x, rfl⟩ := mem_iff.1 hg
    exact ⟨x, (h x).symm⟩
  · rintro ⟨x, rfl⟩
    exact ⟨_, mem_iff.2 ⟨x, rfl⟩, h x⟩

/-- **The normalizer of the non-split torus** consists of the matrices, in the basis
`TauCeti.nonSplitTorusBasis`, of the maps `v ↦ c τ(v)` with `c ∈ Eˣ` and `τ ∈ Gal(E/F)`. -/
theorem mem_normalizer_iff {g : GL (Fin 2) F} :
    g ∈ Subgroup.normalizer (GL2NonSplitTorus F E : Set (GL (Fin 2) F)) ↔
      ∃ c : Eˣ, ∃ τ : E ≃ₐ[F] E,
        Matrix.GeneralLinearGroup.toLin' (nonSplitTorusBasis F E) g = mulGalois c τ := by
  rw [← mem_normalizer_lmulUnitsRange_iff, ← map_toLin', ← Subgroup.map_equiv_normalizer_eq,
    Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply]

/-- **The normalizer of the non-split torus is in bijection with `Eˣ × Gal(E/F)`**, by sending
`(c, τ)` to the matrix of `v ↦ c τ(v)` in the basis `TauCeti.nonSplitTorusBasis`. -/
noncomputable def normalizerEquiv :
    Eˣ × (E ≃ₐ[F] E) ≃ Subgroup.normalizer (GL2NonSplitTorus F E : Set (GL (Fin 2) F)) :=
  normalizerLmulUnitsRangeEquiv.trans
    ((MulEquiv.subgroupMap (Matrix.GeneralLinearGroup.toLin' (nonSplitTorusBasis F E)) _).trans
      (MulEquiv.subgroupCongr (by
        rw [← MulEquiv.toMonoidHom_eq_coe, Subgroup.map_equiv_normalizer_eq, map_toLin']))).symm

/-- `TauCeti.GL2NonSplitTorus.normalizerEquiv` sends `(c, τ)` to the matrix of `v ↦ c τ(v)` in the
basis `TauCeti.nonSplitTorusBasis`. -/
@[simp]
theorem toLin'_normalizerEquiv_apply (p : Eˣ × (E ≃ₐ[F] E)) :
    Matrix.GeneralLinearGroup.toLin' (nonSplitTorusBasis F E) (normalizerEquiv p) =
      mulGalois p.1 p.2 := by
  simp [normalizerEquiv]

/-- `TauCeti.GL2NonSplitTorus.normalizerEquiv` sends `(c, τ)` into the non-split torus exactly when
`τ` is the identity. -/
@[simp]
theorem normalizerEquiv_mem_iff (p : Eˣ × (E ≃ₐ[F] E)) :
    (normalizerEquiv p : GL (Fin 2) F) ∈ GL2NonSplitTorus F E ↔ p.2 = 1 := by
  rw [← mulGalois_mem_lmulUnitsRange_iff (c := p.1), ← toLin'_normalizerEquiv_apply, ← map_toLin',
    Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply]

/-- **The order of the normalizer of the non-split torus**: over a field with `q` elements it has
`2(q² - 1)` elements. -/
theorem natCard_normalizer [Finite F] :
    Nat.card (Subgroup.normalizer (GL2NonSplitTorus F E : Set (GL (Fin 2) F))) =
      2 * (Nat.card F ^ 2 - 1) := by
  have := Module.finite_of_finite F (M := E)
  rw [← Nat.card_congr normalizerEquiv, Nat.card_prod, ← natCard_eq (F := F) (E := E),
    ← Nat.card_congr (unitsEquiv (F := F) (E := E)).toEquiv, IsGalois.card_aut_eq_finrank,
    Algebra.IsQuadraticExtension.finrank_eq_two, mul_comm]

/-- **The index of the normalizer of the non-split torus**: over a field with `q` elements it is
`q(q - 1) / 2`. -/
theorem two_mul_index_normalizer [Finite F] :
    2 * (Subgroup.normalizer (GL2NonSplitTorus F E : Set (GL (Fin 2) F))).index =
      Nat.card F * (Nat.card F - 1) := by
  have hq : 0 < Nat.card F ^ 2 - 1 := by
    have : 1 < Nat.card F := Finite.one_lt_card
    have : 1 < Nat.card F ^ 2 := Nat.one_lt_pow two_ne_zero this
    omega
  have h := (Subgroup.normalizer (GL2NonSplitTorus F E : Set (GL (Fin 2) F))).card_mul_index
  rw [natCard_normalizer, natCard_GL_fin_two_eq_sq_sub_one_mul] at h
  refine Nat.eq_of_mul_eq_mul_left hq ?_
  rw [← h]
  ring

/-- The non-split torus has index `2` in its normalizer, over a finite field. -/
theorem relIndex_normalizer [Finite F] :
    (GL2NonSplitTorus F E).relIndex
      (Subgroup.normalizer (GL2NonSplitTorus F E : Set (GL (Fin 2) F))) = 2 := by
  have hpos : 0 < (Subgroup.normalizer (GL2NonSplitTorus F E : Set (GL (Fin 2) F))).index :=
    Subgroup.index_pos
  have h := Subgroup.relIndex_mul_index (Subgroup.le_normalizer (H := GL2NonSplitTorus F E))
  rw [index_eq, ← two_mul_index_normalizer (E := E)] at h
  exact Nat.eq_of_mul_eq_mul_right hpos h

/-- `-1` lies in the normalizer of the non-split torus. -/
theorem neg_one_mem_normalizer :
    (-1 : GL (Fin 2) F) ∈ Subgroup.normalizer (GL2NonSplitTorus F E : Set (GL (Fin 2) F)) :=
  Subgroup.le_normalizer neg_one_mem

end GL2NonSplitTorus

end TauCeti
