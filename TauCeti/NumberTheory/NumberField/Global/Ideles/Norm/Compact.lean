/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.Global.Ideles.Norm.One
public import TauCeti.NumberTheory.NumberField.Global.Ideles.FiniteIdeal

import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.NormLeOne
import Mathlib.NumberTheory.NumberField.ClassNumber
import TauCeti.NumberTheory.NumberField.CanonicalEmbedding.UnitAction
import TauCeti.RingTheory.DedekindDomain.AdicValuation.ValuativeRel

/-!
# Compactness of the norm-one idele class group

For a number field `K`, the norm-one idele class group `C_K¹ = 𝕀_K¹ / Kˣ` is compact.  This is the
adelic form of the two finiteness theorems of algebraic number theory: the finiteness of the ideal
class group and Dirichlet's unit theorem.  The full idele class group is not compact, since the
idele class norm maps it onto `ℝ>0`; `C_K¹` is the kernel of that map.

## Main results

* `TauCeti.GlobalNumberFields.IdeleClassGroup.isCompact_normOne`: the norm-one idele class group
  is a compact subset of the idele class group.
* `TauCeti.GlobalNumberFields.IdeleClassGroup.compactSpace_normOne`: the norm-one idele class
  group is a compact space.

## References

* J. W. S. Cassels and A. Fröhlich, eds., *Algebraic Number Theory*, Chapter II, §16.
* J. Neukirch, *Algebraic Number Theory*, Chapter VI, §1, Theorem 1.6.
* A. Weil, *Basic Number Theory*, Chapter IV, §4.
-/

public section

open IsDedekindDomain NumberField NumberField.InfinitePlace NumberField.mixedEmbedding

namespace TauCeti.GlobalNumberFields

variable (K : Type*) [Field K] [NumberField K]

/-- Multiplying an idele by a principal unit acts on its infinite component by the corresponding
unit action on the mixed space. -/
private lemma ringEquiv_mixedSpace_mul_unitEmbedding (z : IdeleGroup (𝓞 K) K)
    (u : (𝓞 K)ˣ) :
    InfiniteAdeleRing.ringEquiv_mixedSpace K
      ((z * IdeleGroup.unitEmbedding (𝓞 K) K
        (Units.map (algebraMap (𝓞 K) K) u) : AdeleRing (𝓞 K) K).1) =
      u • InfiniteAdeleRing.ringEquiv_mixedSpace K (z : AdeleRing (𝓞 K) K).1 := by
  rw [unitSMul_smul, InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp, ← map_mul,
    IdeleGroup.coe_unitEmbedding, AdeleRing.fst_mul, mul_comm]
  refine congrArg _ (congrArg (· * _) (funext fun w ↦ ?_))
  rw [AdeleRing.algebraMap_fst_apply, InfiniteAdeleRing.algebraMap_apply, Units.coe_map,
    MonoidHom.coe_coe]

/-- There is a compact set of ideles meeting the orbit under the global units of every idele of
norm one whose finite part is an everywhere-integral unit. -/
private lemma exists_isCompact_forall_exists_mul_unitEmbedding_mem :
    ∃ W : Set (IdeleGroup (𝓞 K) K), IsCompact W ∧
      ∀ z : IdeleGroup (𝓞 K) K, ideleNorm z = 1 →
        IdeleGroup.toFiniteIdele (𝓞 K) K z ∈ FiniteAdeleRing.integralUnits (𝓞 K) K →
        ∃ u : (𝓞 K)ˣ,
          z * IdeleGroup.unitEmbedding (𝓞 K) K (Units.map (algebraMap (𝓞 K) K) u) ∈ W := by
  classical
  let e := InfiniteAdeleRing.ringEquiv_mixedSpace K
  -- The infinite parts: the norm-one points of the closure of `normLeOne`, and their inverses.
  let F : Set (mixedSpace K) :=
    closure (fundamentalCone.normLeOne K) ∩ {x | mixedEmbedding.norm x = 1}
  have hF : IsCompact F := (fundamentalCone.isBounded_normLeOne K).isCompact_closure.inter_right
    (isClosed_eq (mixedEmbedding.continuous_norm K) continuous_const)
  have hFunit (x : mixedSpace K) (hx : x ∈ F) : IsUnit x :=
    TauCeti.NumberField.mixedEmbedding.isUnit_iff_norm_ne_zero.mpr (hx.2 ▸ one_ne_zero)
  let G : Set (mixedSpace K) := Ring.inverse '' F
  have hG : IsCompact G := hF.image_of_continuousOn fun x hx ↦
    (NormedRing.inverse_continuousAt (hFunit x hx).unit).continuousWithinAt
  -- The finite parts: the integral finite adeles.
  let O : Set (FiniteAdeleRing (𝓞 K) K) := {a | ∀ v, a v ∈ v.adicCompletionIntegers K}
  have hO : IsCompact O := FiniteAdeleRing.isCompact_integralFiniteAdeles
  let C : Set (AdeleRing (𝓞 K) K) := (e.symm '' F) ×ˢ O
  let D : Set (AdeleRing (𝓞 K) K) := (e.symm '' G) ×ˢ O
  have hC : IsCompact C :=
    (hF.image (InfiniteAdeleRing.continuous_ringEquiv_mixedSpace_symm K)).prod hO
  have hD : IsCompact D :=
    (hG.image (InfiniteAdeleRing.continuous_ringEquiv_mixedSpace_symm K)).prod hO
  -- An idele lies in `W` when it lies in `C` and its inverse lies in `D`; this is compact since
  -- the idele group is embedded as a closed subset of `𝔸_K × 𝔸_Kᵐᵒᵖ` by `x ↦ (x, x⁻¹)`.
  refine ⟨{z | (z : AdeleRing (𝓞 K) K) ∈ C ∧ ((z⁻¹ : IdeleGroup (𝓞 K) K) : AdeleRing (𝓞 K) K) ∈ D},
    Units.isClosedEmbedding_embedProduct.isCompact_preimage
      (hC.prod (MulOpposite.opHomeomorph.symm.isCompact_preimage.mpr hD)), ?_⟩
  intro z hz hzf
  have hnorm : mixedEmbedding.norm (e (z : AdeleRing (𝓞 K) K).1) = 1 := by
    rw [mixedEmbedding_norm_eq_ideleNorm (K := K) hzf, hz, Units.val_one, NNReal.coe_one]
  -- Dirichlet's unit theorem moves the infinite part into the fundamental cone.
  obtain ⟨u, hu⟩ := fundamentalCone.exists_unit_smul_mem (hnorm ▸ one_ne_zero)
  refine ⟨u, ?_⟩
  set z' := z * IdeleGroup.unitEmbedding (𝓞 K) K (Units.map (algebraMap (𝓞 K) K) u)
  have he : e (z' : AdeleRing (𝓞 K) K).1 = u • e (z : AdeleRing (𝓞 K) K).1 := by
    simpa only [z', e, Units.val_mul] using ringEquiv_mixedSpace_mul_unitEmbedding K z u
  have hF' : e (z' : AdeleRing (𝓞 K) K).1 ∈ F := by
    rw [he]
    exact ⟨subset_closure ⟨hu, by simp [hnorm]⟩, by simp [hnorm]⟩
  have hf' : IdeleGroup.toFiniteIdele (𝓞 K) K z' ∈ FiniteAdeleRing.integralUnits (𝓞 K) K := by
    rw [map_mul, IdeleGroup.toFiniteIdele_unitEmbedding]
    exact mul_mem hzf (FiniteAdeleRing.unitEmbedding_map_algebraMap_mem_integralUnits u)
  have hint := FiniteAdeleRing.mem_integralUnits_iff_forall_mem_adicCompletionIntegers.mp hf'
  refine ⟨⟨⟨e (z' : AdeleRing (𝓞 K) K).1, hF', e.symm_apply_apply _⟩, fun v ↦ ?_⟩,
    ⟨⟨Ring.inverse (e (z' : AdeleRing (𝓞 K) K).1), ⟨_, hF', rfl⟩, ?_⟩, fun v ↦ ?_⟩⟩
  · simpa using (hint v).1
  · -- The infinite part of `z'⁻¹` is the inverse of the infinite part of `z'`: the unit of the
    -- mixed space below has, by `Units.coe_map`, value `e (z' : 𝔸_K).1` and inverse
    -- `e (z'⁻¹ : 𝔸_K).1`.
    rw [e.symm_apply_eq]
    exact Ring.inverse_unit (Units.map ((e : InfiniteAdeleRing K →* mixedSpace K).comp
      (MonoidHom.fst _ (FiniteAdeleRing (𝓞 K) K))) z')
  · simpa [← map_inv] using (hint v).2

namespace IdeleClassGroup

/-- **The norm-one idele class group is compact.**  This is the adelic form of the finiteness of
the class group together with Dirichlet's unit theorem. -/
theorem isCompact_normOne : IsCompact (normOne K : Set (IdeleClassGroup (𝓞 K) K)) := by
  classical
  obtain ⟨W, hW, hWmem⟩ := exists_isCompact_forall_exists_mul_unitEmbedding_mem K
  choose b hb1 hbc using exists_ideleNorm_eq_one_and_toClassGroup_eq (K := K)
  have hq : Continuous (QuotientGroup.mk : IdeleGroup (𝓞 K) K → IdeleClassGroup (𝓞 K) K) :=
    continuous_quot_mk
  -- `C_K¹` is a closed subset of the union over the finitely many ideal classes `c` of the
  -- images of the compact sets `b_c • W`.
  refine (isCompact_iUnion fun c ↦ hW.image (hq.comp (continuous_const.mul continuous_id)
    (f := fun z ↦ b c * z))).of_isClosed_subset (isClosed_normOne K) ?_
  intro x hx
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective x
  have ha : ideleNorm a = 1 := mk_mem_normOne_iff.mp hx
  set c := FiniteAdeleRing.toClassGroup (𝓞 K) K (IdeleGroup.toFiniteIdele (𝓞 K) K a)
  -- The finite part of `a / b_c` has trivial class, so it is an everywhere-integral unit times a
  -- principal finite idele.
  have hker : IdeleGroup.toFiniteIdele (𝓞 K) K (a * (b c)⁻¹) ∈
      FiniteAdeleRing.integralUnits (𝓞 K) K ⊔ (FiniteAdeleRing.unitEmbedding (𝓞 K) K).range := by
    rw [← FiniteAdeleRing.ker_toClassGroup, MonoidHom.mem_ker, map_mul, map_mul, map_inv, map_inv,
      hbc, mul_inv_cancel]
  obtain ⟨f, hf, _, ⟨y, rfl⟩, hfy⟩ := Subgroup.mem_sup.mp hker
  set z := a * (b c)⁻¹ * (IdeleGroup.unitEmbedding (𝓞 K) K y)⁻¹
  have hz1 : ideleNorm z = 1 := by simp [z, ha, hb1]
  have hzf : IdeleGroup.toFiniteIdele (𝓞 K) K z ∈ FiniteAdeleRing.integralUnits (𝓞 K) K := by
    rw [map_mul, map_inv, IdeleGroup.toFiniteIdele_unitEmbedding, ← hfy, mul_inv_cancel_right]
    exact hf
  obtain ⟨u, hu⟩ := hWmem z hz1 hzf
  refine Set.mem_iUnion.mpr ⟨c, _, hu, ?_⟩
  -- `b_c * z * u` differs from `a` by the principal idele of `y * u⁻¹`.
  rw [Function.comp_apply, QuotientGroup.eq]
  have h : (b c * (z * IdeleGroup.unitEmbedding (𝓞 K) K (Units.map (algebraMap (𝓞 K) K) u)))⁻¹ *
      a = IdeleGroup.unitEmbedding (𝓞 K) K (y * (Units.map (algebraMap (𝓞 K) K) u)⁻¹) := by
    simp only [z, map_mul, map_inv]
    simp [mul_comm, mul_left_comm]
  rw [h]
  exact ⟨_, rfl⟩

/-- **The norm-one idele class group is a compact space.** -/
instance compactSpace_normOne : CompactSpace (normOne K) :=
  isCompact_iff_compactSpace.mp (isCompact_normOne K)

end IdeleClassGroup

end TauCeti.GlobalNumberFields
