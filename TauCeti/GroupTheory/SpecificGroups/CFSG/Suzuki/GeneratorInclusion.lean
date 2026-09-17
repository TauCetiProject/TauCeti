/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.SpecificGroups.CFSG.Suzuki.Generated
public import TauCeti.GroupTheory.SpecificGroups.CFSG.Suzuki.MatrixEquations

/-!
# Standard generators inside the Suzuki fixed points

The generator presentation of `Sz(2^(2m+1))` and its Steinberg fixed-point construction use
different coefficient fields. This file chooses an embedding of the generator field into the
algebraic closure of a valid Suzuki index and proves that the standard generators belong to the
Steinberg fixed subgroup. Consequently scalar extension maps the generated Suzuki group into that
fixed subgroup.

This is the inclusion half of the comparison. It does not assert that the standard generators
exhaust the fixed points, nor identify the derived central quotient with the generated group.

## References

* M. Suzuki, *On a class of doubly transitive groups*, Annals of Mathematics **75** (1962),
  105--145.
-/

public section

noncomputable section

open Matrix

namespace TauCeti.Suzuki

variable (m : ℕ)

/-- The coordinate change from the standard generator model to the standard symplectic carrier.
It exchanges the final two basis vectors. -/
def coordinateSwap : Fin 4 ≃ Fin 4 := Equiv.swap 2 3

/-- Simultaneous row and column reindexing from the standard generator coordinates to the
coordinates used by `SpStd`. -/
def coordinateEquiv (R : Type*) [CommRing R] : GL (Fin 4) R ≃* GL (Fin 4) R :=
  Units.mapEquiv (Matrix.reindexAlgEquiv R R coordinateSwap).toRingEquiv.toMulEquiv

/-- The underlying matrix of `coordinateEquiv` is obtained by swapping its final two rows and
columns. -/
@[simp]
theorem coe_coordinateEquiv (R : Type*) [CommRing R] (g : GL (Fin 4) R) :
    ((coordinateEquiv R g : GL (Fin 4) R) : Matrix (Fin 4) (Fin 4) R) =
      Matrix.reindex coordinateSwap coordinateSwap (g : Matrix (Fin 4) (Fin 4) R) := by
  simp [coordinateEquiv]

private theorem reindex_coordinateSwap_apply {R : Type*}
    (A : Matrix (Fin 4) (Fin 4) R) (i j : Fin 4) :
    Matrix.reindex coordinateSwap coordinateSwap A i j =
      A (coordinateSwap i) (coordinateSwap j) := by
  rw [Matrix.reindex_apply]
  simp [coordinateSwap]

/-- After the standard coordinate change, every unipotent Suzuki generator preserves the
alternating form used by `SpStd`. -/
theorem coordinateEquiv_unipotent_mul_jFin_mul_transpose
    (a b : GaloisField 2 (2 * m + 1)) :
    ((coordinateEquiv (GaloisField 2 (2 * m + 1)) (unipotent m a b) :
          GL (Fin 4) (GaloisField 2 (2 * m + 1))) :
        Matrix (Fin 4) (Fin 4) (GaloisField 2 (2 * m + 1))) *
        JFin 2 (GaloisField 2 (2 * m + 1)) *
        ((coordinateEquiv (GaloisField 2 (2 * m + 1)) (unipotent m a b) :
            GL (Fin 4) (GaloisField 2 (2 * m + 1))) :
          Matrix (Fin 4) (Fin 4) (GaloisField 2 (2 * m + 1)))ᵀ =
      JFin 2 (GaloisField 2 (2 * m + 1)) := by
  have htwo : (2 : GaloisField 2 (2 * m + 1)) = 0 := CharTwo.two_eq_zero
  have hfour : (4 : GaloisField 2 (2 * m + 1)) = 0 := by
    calc
      (4 : GaloisField 2 (2 * m + 1)) = 2 + 2 := by norm_num
      _ = 0 := by rw [htwo]; simp
  rw [coe_coordinateEquiv, coe_unipotent]
  rw [JFin_two_eq]
  ext i j
  rw [Matrix.mul_apply]
  simp only [Matrix.transpose_apply]
  simp_rw [reindex_coordinateSwap_apply]
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_four, CharTwo.neg_eq, unipotentMatrix_apply,
      coordinateSwap, Equiv.swap_apply_def] <;> ring_nf
  all_goals simp [htwo, hfour]

/-- After the standard coordinate change, the Weyl generator preserves the alternating form
used by `SpStd`. -/
theorem coordinateEquiv_weyl_mul_jFin_mul_transpose :
    ((coordinateEquiv (GaloisField 2 (2 * m + 1)) (weyl m) :
          GL (Fin 4) (GaloisField 2 (2 * m + 1))) :
        Matrix (Fin 4) (Fin 4) (GaloisField 2 (2 * m + 1))) *
        JFin 2 (GaloisField 2 (2 * m + 1)) *
        ((coordinateEquiv (GaloisField 2 (2 * m + 1)) (weyl m) :
            GL (Fin 4) (GaloisField 2 (2 * m + 1))) :
          Matrix (Fin 4) (Fin 4) (GaloisField 2 (2 * m + 1)))ᵀ =
      JFin 2 (GaloisField 2 (2 * m + 1)) := by
  rw [coe_coordinateEquiv, coe_weyl]
  rw [JFin_two_eq]
  ext i j
  rw [Matrix.mul_apply]
  simp only [Matrix.transpose_apply]
  simp_rw [reindex_coordinateSwap_apply]
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_four, CharTwo.neg_eq, weylMatrix_apply,
      coordinateSwap, Equiv.swap_apply_def]

/-- After the standard coordinate change, the special isogeny sends a unipotent generator to
its entrywise `2^(m+1)`-st power. -/
theorem symplecticSpecialIsogeny_coordinateEquiv_unipotent
    (a b : GaloisField 2 (2 * m + 1)) :
    Matrix.symplecticSpecialIsogeny
        ((coordinateEquiv (GaloisField 2 (2 * m + 1)) (unipotent m a b) :
            GL (Fin 4) (GaloisField 2 (2 * m + 1))) :
          Matrix (Fin 4) (Fin 4) (GaloisField 2 (2 * m + 1))) =
      (((coordinateEquiv (GaloisField 2 (2 * m + 1)) (unipotent m a b) :
            GL (Fin 4) (GaloisField 2 (2 * m + 1))) :
          Matrix (Fin 4) (Fin 4) (GaloisField 2 (2 * m + 1))).map
            (fun x ↦ x ^ 2 ^ (m + 1))) := by
  have ha := pow_two_pow_succ_pow_two_pow_succ m a
  have hb := pow_two_pow_succ_pow_two_pow_succ m b
  have htwo : (2 : GaloisField 2 (2 * m + 1)) = 0 := CharTwo.two_eq_zero
  rw [coe_coordinateEquiv, coe_unipotent]
  ext i j
  simp only [Matrix.symplecticSpecialIsogeny_apply, Matrix.map_apply]
  simp_rw [reindex_coordinateSwap_apply]
  fin_cases i <;> fin_cases j <;>
    simp [pairMinor_eq, unipotentMatrix_apply, coordinateSwap, Equiv.swap_apply_def,
      CharTwo.sub_eq_add, add_pow_char_pow, mul_pow, ha, hb] <;> ring_nf
  all_goals simp [htwo]

/-- After the standard coordinate change, the special isogeny fixes the Weyl generator. -/
theorem symplecticSpecialIsogeny_coordinateEquiv_weyl :
    Matrix.symplecticSpecialIsogeny
        ((coordinateEquiv (GaloisField 2 (2 * m + 1)) (weyl m) :
            GL (Fin 4) (GaloisField 2 (2 * m + 1))) :
          Matrix (Fin 4) (Fin 4) (GaloisField 2 (2 * m + 1))) =
      (((coordinateEquiv (GaloisField 2 (2 * m + 1)) (weyl m) :
            GL (Fin 4) (GaloisField 2 (2 * m + 1))) :
          Matrix (Fin 4) (Fin 4) (GaloisField 2 (2 * m + 1))).map
            (fun x ↦ x ^ 2 ^ (m + 1))) := by
  rw [coe_coordinateEquiv, coe_weyl]
  ext i j
  simp only [Matrix.symplecticSpecialIsogeny_apply, Matrix.map_apply]
  simp_rw [reindex_coordinateSwap_apply]
  fin_cases i <;> fin_cases j <;>
    simp [pairMinor_eq, weylMatrix_apply, coordinateSwap, Equiv.swap_apply_def,
      CharTwo.sub_eq_add]

end TauCeti.Suzuki

namespace TauCeti.SuzukiLieIndex

/-- A finite-field embedding from the coefficient field of the standard generators into the
algebraic closure used by a valid Suzuki index. -/
noncomputable def generatorFieldEmbedding (m : ℕ)
    (hvalid : (LieTypeIndex.suzuki m).Valid) :
    GaloisField 2 (2 * m + 1) →+* (of m hvalid).1.Closure := by
  letI : CharP (of m hvalid).1.Closure 2 := charP_closure_two (of m hvalid)
  letI : Algebra (ZMod 2) (of m hvalid).1.Closure := ZMod.algebra _ _
  exact (IsAlgClosed.lift :
    GaloisField 2 (2 * m + 1) →ₐ[ZMod 2] (of m hvalid).1.Closure).toRingHom

/-- Scalar extension of the coordinate-changed generator model into the algebraic closure of a
valid Suzuki index. -/
noncomputable def generatorEmbedding (m : ℕ) (hvalid : (LieTypeIndex.suzuki m).Valid) :
    GL (Fin 4) (GaloisField 2 (2 * m + 1)) →*
      GL (Fin 4) (of m hvalid).1.Closure :=
  (Matrix.GeneralLinearGroup.map (generatorFieldEmbedding m hvalid)).comp
    (Suzuki.coordinateEquiv (GaloisField 2 (2 * m + 1))).toMonoidHom

/-- Scalar extension acts entrywise after the coordinate change. -/
@[simp]
theorem generatorEmbedding_apply (m : ℕ) (hvalid : (LieTypeIndex.suzuki m).Valid)
    (g : GL (Fin 4) (GaloisField 2 (2 * m + 1))) (i j : Fin 4) :
    generatorEmbedding m hvalid g i j =
      generatorFieldEmbedding m hvalid (Suzuki.coordinateEquiv _ g i j) := by
  rw [generatorEmbedding, MonoidHom.comp_apply,
    Matrix.GeneralLinearGroup.map_apply]
  rfl

/-- The scalar extension and coordinate change used for the generator model are injective. -/
theorem generatorEmbedding_injective (m : ℕ)
    (hvalid : (LieTypeIndex.suzuki m).Valid) :
    Function.Injective (generatorEmbedding m hvalid) :=
  (Units.map_injective (Matrix.map_injective (RingHom.injective _))).comp
    (Suzuki.coordinateEquiv (GaloisField 2 (2 * m + 1))).injective

private theorem coe_generatorEmbedding (m : ℕ)
    (hvalid : (LieTypeIndex.suzuki m).Valid)
    (g : GL (Fin 4) (GaloisField 2 (2 * m + 1))) :
    (generatorEmbedding m hvalid g : Matrix (Fin 4) (Fin 4) (of m hvalid).1.Closure) =
      ((Suzuki.coordinateEquiv _ g : GL (Fin 4) _) : Matrix (Fin 4) (Fin 4) _).map
        (generatorFieldEmbedding m hvalid) := by
  ext i j
  rw [generatorEmbedding_apply, Matrix.map_apply]

/-- A generator whose coordinate change preserves the alternating form and satisfies the
special-isogeny equation over the generator field is, after scalar extension, a Steinberg fixed
point. -/
theorem generatorEmbedding_mem_map_fixedSubgroup (m : ℕ)
    (hvalid : (LieTypeIndex.suzuki m).Valid) (g : GL (Fin 4) (GaloisField 2 (2 * m + 1)))
    (hsymp : ((Suzuki.coordinateEquiv (GaloisField 2 (2 * m + 1)) g :
          GL (Fin 4) (GaloisField 2 (2 * m + 1))) :
        Matrix (Fin 4) (Fin 4) (GaloisField 2 (2 * m + 1))) *
        JFin 2 (GaloisField 2 (2 * m + 1)) *
        ((Suzuki.coordinateEquiv (GaloisField 2 (2 * m + 1)) g :
            GL (Fin 4) (GaloisField 2 (2 * m + 1))) :
          Matrix (Fin 4) (Fin 4) (GaloisField 2 (2 * m + 1)))ᵀ =
      JFin 2 (GaloisField 2 (2 * m + 1)))
    (hiso : Matrix.symplecticSpecialIsogeny
        ((Suzuki.coordinateEquiv (GaloisField 2 (2 * m + 1)) g :
            GL (Fin 4) (GaloisField 2 (2 * m + 1))) :
          Matrix (Fin 4) (Fin 4) (GaloisField 2 (2 * m + 1))) =
      (((Suzuki.coordinateEquiv (GaloisField 2 (2 * m + 1)) g :
            GL (Fin 4) (GaloisField 2 (2 * m + 1))) :
          Matrix (Fin 4) (Fin 4) (GaloisField 2 (2 * m + 1))).map
            (fun x ↦ x ^ 2 ^ (m + 1)))) :
    generatorEmbedding m hvalid g ∈
      (fixedSubgroup (of m hvalid).steinberg).map
        (SpStd.points 1 (of m hvalid).1.Closure).subtype := by
  rw [(of m hvalid).mem_map_fixedSubgroup_steinberg_iff, coe_generatorEmbedding,
    SuzukiReeIndex.halfExponent_suzuki, Matrix.symplecticSpecialIsogeny_map, hiso]
  refine ⟨?_, fun i j ↦ ?_⟩
  · rw [← Matrix.transpose_map, ← JFin_map 2 (generatorFieldEmbedding m hvalid),
      ← Matrix.map_mul, ← Matrix.map_mul, hsymp]
  · simp only [Matrix.map_apply, map_pow]

/-- Every coordinate-changed unipotent generator, extended to the algebraic closure, is a
Steinberg fixed point. -/
theorem generatorEmbedding_unipotent_mem_map_fixedSubgroup (m : ℕ)
    (hvalid : (LieTypeIndex.suzuki m).Valid)
    (a b : GaloisField 2 (2 * m + 1)) :
    generatorEmbedding m hvalid (Suzuki.unipotent m a b) ∈
      (fixedSubgroup (of m hvalid).steinberg).map
        (SpStd.points 1 (of m hvalid).1.Closure).subtype :=
  generatorEmbedding_mem_map_fixedSubgroup m hvalid _
    (Suzuki.coordinateEquiv_unipotent_mul_jFin_mul_transpose m a b)
    (Suzuki.symplecticSpecialIsogeny_coordinateEquiv_unipotent m a b)

/-- The coordinate-changed Weyl generator, extended to the algebraic closure, is a Steinberg
fixed point. -/
theorem generatorEmbedding_weyl_mem_map_fixedSubgroup (m : ℕ)
    (hvalid : (LieTypeIndex.suzuki m).Valid) :
    generatorEmbedding m hvalid (Suzuki.weyl m) ∈
      (fixedSubgroup (of m hvalid).steinberg).map
        (SpStd.points 1 (of m hvalid).1.Closure).subtype :=
  generatorEmbedding_mem_map_fixedSubgroup m hvalid _
    (Suzuki.coordinateEquiv_weyl_mul_jFin_mul_transpose m)
    (Suzuki.symplecticSpecialIsogeny_coordinateEquiv_weyl m)

/-- The coordinate-changed standard generator model embeds into the image in `GL₄` of the
Suzuki Steinberg fixed subgroup. -/
theorem map_suzukiGroup_le_map_fixedSubgroup (m : ℕ)
    (hvalid : (LieTypeIndex.suzuki m).Valid) :
    (suzukiGroup m).map (generatorEmbedding m hvalid) ≤
      (fixedSubgroup (of m hvalid).steinberg).map
        (SpStd.points 1 (of m hvalid).1.Closure).subtype := by
  rw [Subgroup.map_le_iff_le_comap, Suzuki.suzukiGroup_le_iff]
  exact ⟨fun a b ↦ generatorEmbedding_unipotent_mem_map_fixedSubgroup m hvalid a b,
    generatorEmbedding_weyl_mem_map_fixedSubgroup m hvalid⟩

end TauCeti.SuzukiLieIndex
