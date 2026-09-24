/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.Global.Ideles.Norm.One

import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.NormLeOne
import Mathlib.NumberTheory.NumberField.ClassNumber
import TauCeti.NumberTheory.NumberField.CanonicalEmbedding.UnitAction
import TauCeti.NumberTheory.NumberField.Global.Adeles.Basic
import TauCeti.RingTheory.DedekindDomain.AdicValuation.ValuativeRel
import TauCeti.RingTheory.DedekindDomain.FiniteAdeleRing.ClassGroup

/-!
# Compactness of the norm-one idele class group

For a number field `K`, the norm-one idele class group `C_K¹ = 𝕀_K¹ / Kˣ` is compact.  This is the
adelic form of the two finiteness theorems of algebraic number theory: the finiteness of the ideal
class group and Dirichlet's unit theorem.  The full idele class group is not compact, since the
idele class norm maps it onto `ℝ>0`; `C_K¹` is the kernel of that map.

The proof exhibits `C_K¹` as a closed subset of a compact set, namely the image of finitely many
translates of one compact set of ideles.

* The class group is finite.  Choose, for each ideal class `c`, an idele `b_c` of norm one whose
  finite part has class `c`.  Given an idele `a` of norm one, dividing by `b_c` for the class of
  `a` and then by a principal idele leaves an idele `z` of norm one whose finite part is a unit
  of the local integers at every place.
* The finite coordinates of such a `z` have norm one, so its infinite part has mixed norm one.
  By Dirichlet's unit theorem, in Mathlib's form `fundamentalCone.exists_unit_smul_mem`, a
  global unit moves that infinite part into the fundamental cone, and hence into the compact set
  of norm-one points of the closure of `normLeOne`.  Multiplying by a global unit keeps the
  finite part everywhere integral.
* The ideles whose infinite part lies in that compact set and whose finite part is an
  everywhere-integral unit form a compact subset of the idele group.  In the units topology this
  needs both the idele and its inverse to be bounded: inversion is continuous on the units of the
  mixed space, so the inverses of the compact set of infinite parts again form a compact set.

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

/-- For an idele whose finite part is an everywhere-integral unit, the idele norm is the mixed norm
of its infinite part. -/
private lemma mixedEmbedding_norm_eq_ideleNorm {z : IdeleGroup (𝓞 K) K}
    (hz : IdeleGroup.toFiniteIdele (𝓞 K) K z ∈ FiniteAdeleRing.integralUnits (𝓞 K) K) :
    mixedEmbedding.norm (InfiniteAdeleRing.ringEquiv_mixedSpace K (z : AdeleRing (𝓞 K) K).1) =
      ((ideleNorm z : NNReal) : ℝ) := by
  have hfin (v : HeightOneSpectrum (𝓞 K)) :
      ‖(v.ideleFiniteCoord z : v.adicCompletion K)‖ = 1 := by
    have hv := FiniteAdeleRing.mem_integralUnits_iff.mp hz v
    rw [IdeleGroup.coe_toFiniteIdele] at hv
    rw [HeightOneSpectrum.coe_ideleFiniteCoord, FinitePlace.norm_def, hv, map_one, NNReal.coe_one]
  simp only [coe_ideleNorm, finprod_congr hfin, finprod_one, mul_one,
    infiniteCompletionNormalizedAbsValue_apply, InfinitePlace.coe_ideleInfiniteCoord,
    InfiniteAdeleRing.mixedEmbedding_norm_ringEquiv_mixedSpace, InfiniteAdeleRing.norm_def]

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
    rw [mixedEmbedding_norm_eq_ideleNorm K hzf, hz, Units.val_one, NNReal.coe_one]
  -- Dirichlet's unit theorem moves the infinite part into the fundamental cone.
  obtain ⟨u, hu⟩ := fundamentalCone.exists_unit_smul_mem (hnorm ▸ one_ne_zero)
  refine ⟨u, ?_⟩
  set z' := z * IdeleGroup.unitEmbedding (𝓞 K) K (Units.map (algebraMap (𝓞 K) K) u)
  have he : e (z' : AdeleRing (𝓞 K) K).1 = u • e (z : AdeleRing (𝓞 K) K).1 := by
    rw [unitSMul_smul, InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp, ← map_mul, mul_comm]
    -- `AdeleRing` is a type synonym for `K∞ × 𝔸_K^f`, so the infinite part of the product with a
    -- principal idele is the product with the diagonal image in `K∞`; no lemma states this.
    rfl
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

/-- Every ideal class is the class of the finite part of an idele of norm one. -/
private lemma exists_ideleNorm_eq_one_and_toClassGroup_eq (c : ClassGroup (𝓞 K)) :
    ∃ b : IdeleGroup (𝓞 K) K, ideleNorm b = 1 ∧
      FiniteAdeleRing.toClassGroup (𝓞 K) K (IdeleGroup.toFiniteIdele (𝓞 K) K b) = c := by
  obtain ⟨f, hf⟩ := FiniteAdeleRing.toClassGroup_surjective (R := 𝓞 K) (K := K) c
  -- Correct the norm at one infinite place, which does not change the finite part.
  obtain ⟨w⟩ := (inferInstance : Nonempty (InfinitePlace K))
  obtain ⟨x, hx⟩ := exists_infiniteCompletionNormalizedAbsValue_eq w
    ((ideleNorm (IdeleGroup.ofFiniteIdele (𝓞 K) K f))⁻¹ : NNReal).coe_nonneg
  have hx0 : x ≠ 0 := by
    rintro rfl
    rw [map_zero] at hx
    exact Units.ne_zero _ (by exact_mod_cast hx.symm)
  refine ⟨IdeleGroup.ofFiniteIdele (𝓞 K) K f * IdeleGroup.ofCompletion (𝓞 K) K w (Units.mk0 x hx0),
    ?_, ?_⟩
  · ext
    rw [map_mul, Units.val_mul, NNReal.coe_mul, coe_ideleNorm_ofCompletion, Units.val_mk0, hx]
    simp
  · rw [map_mul, map_mul, IdeleGroup.toFiniteIdele_ofFiniteIdele,
      IdeleGroup.toFiniteIdele_ofCompletion, map_one, mul_one, hf]

namespace IdeleClassGroup

/-- **The norm-one idele class group is compact.**  This is the adelic form of the finiteness of
the class group together with Dirichlet's unit theorem. -/
theorem isCompact_normOne : IsCompact (normOne K : Set (IdeleClassGroup (𝓞 K) K)) := by
  classical
  obtain ⟨W, hW, hWmem⟩ := exists_isCompact_forall_exists_mul_unitEmbedding_mem K
  choose b hb1 hbc using exists_ideleNorm_eq_one_and_toClassGroup_eq K
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
