/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Germ.Idempotent
public import TauCeti.Analysis.Normed.Algebra.HolomorphicFunctionalCalculus.Spectrum
public import Mathlib.Algebra.Module.Submodule.Invariant
public import Mathlib.Topology.Algebra.Module.Complement

/-!
# Riesz idempotents

Let `a` be an element of a complex Banach algebra `A`, and let `K` be a clopen part of its
spectrum `σ(a)`. The *Riesz idempotent* `rieszIdempotent a K` is the value of the holomorphic
calculus at the indicator germ of `K`, a function equal to `1` near `K` and to `0` near
`σ(a) \ K`. Equivalently (`TauCeti.holomorphicCalculus_ofFun_eq_integral`), it is
`(2πi)⁻¹ ∫_Γ χ(z) (z1 - a)⁻¹ dz` for such a function `χ` and any admissible cycle `Γ` around
`σ(a)`.

Since the calculus is a unital algebra homomorphism, the Riesz idempotents inherit the Boolean
algebra of clopen parts of `σ(a)`: for a finite partition of `σ(a)` into clopen parts they are
pairwise orthogonal idempotents summing to `1`. They commute with every element commuting with
`a`. The spectral mapping theorem shows that `rieszIdempotent a K` vanishes exactly when `K` is
empty.

The idempotent `p = rieszIdempotent a K` cuts out the part `K` of the spectrum: in the corner
algebra `p A p`, whose unit is `p`, the element `μ - a` is invertible exactly when `μ ∉ K`
(`TauCeti.exists_rieszIdempotent_corner_inverse_iff`). Equivalently, `(μ - a) p + (1 - p)` is a
unit of `A` exactly when `μ ∉ K`.

For a bounded operator `T` on a complex Banach space, the ranges of the Riesz idempotents of `K`
and of its complement are closed topological complements, each invariant under every operator
commuting with `T`. Hence an operator with disconnected spectrum has a nonzero proper closed
hyperinvariant subspace.

## Main results

* `TauCeti.rieszIdempotent`: the Riesz idempotent of a clopen part of the spectrum.
* `TauCeti.rieszIdempotent_inf`, `TauCeti.rieszIdempotent_compl`,
  `TauCeti.rieszIdempotent_mul_rieszIdempotent_of_disjoint` and
  `TauCeti.sum_rieszIdempotent_eq_one`: products, complements, orthogonality and sum one.
* `Commute.rieszIdempotent_right`: commutation with the commutant of `a`.
* `TauCeti.rieszIdempotent_eq_zero_iff` and `TauCeti.rieszIdempotent_eq_one_iff`.
* `TauCeti.isUnit_sub_mul_rieszIdempotent_add_iff` and
  `TauCeti.exists_rieszIdempotent_corner_inverse_iff`: the corner spectrum of `a` cut out by
  `rieszIdempotent a K` is `K`.
* `ContinuousLinearMap.isTopCompl_range_rieszIdempotent_range_rieszIdempotent_compl` and
  `ContinuousLinearMap.range_rieszIdempotent_mem_invtSubmodule`: the spectral decomposition of a
  bounded operator into closed hyperinvariant subspaces.
* `exists_isClosed_ne_bot_ne_top_forall_commute_mem_invtSubmodule_of_not_isPreconnected`
  (in the `ContinuousLinearMap` namespace): an operator with disconnected spectrum has a
  nonzero proper closed hyperinvariant subspace.

## References

* H. G. Dales, *Banach Algebras and Automatic Continuity*, §2.4.
* J. B. Conway, *A Course in Functional Analysis*, second edition, VII.4.
-/

public noncomputable section

open Function Set TopologicalSpace

namespace TauCeti

open holomorphicGerms

variable {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A]

/-- The **Riesz idempotent** of a clopen part `K` of the spectrum of `a`: the value of the
holomorphic calculus at a function equal to `1` near `K` and to `0` near the rest of the
spectrum. -/
def rieszIdempotent (a : A) (K : Clopens (spectrum ℂ a)) : A :=
  holomorphicCalculus a (indicator K)

theorem rieszIdempotent_def (a : A) (K : Clopens (spectrum ℂ a)) :
    rieszIdempotent a K = holomorphicCalculus a (indicator K) := (rfl)

theorem isIdempotentElem_rieszIdempotent (a : A) (K : Clopens (spectrum ℂ a)) :
    IsIdempotentElem (rieszIdempotent a K) :=
  (isIdempotentElem_indicator K).map _

@[simp]
theorem rieszIdempotent_bot (a : A) : rieszIdempotent a ⊥ = 0 := by
  simp [rieszIdempotent_def]

@[simp]
theorem rieszIdempotent_top (a : A) : rieszIdempotent a ⊤ = 1 := by
  simp [rieszIdempotent_def]

@[simp]
theorem rieszIdempotent_inf (a : A) (K L : Clopens (spectrum ℂ a)) :
    rieszIdempotent a (K ⊓ L) = rieszIdempotent a K * rieszIdempotent a L := by
  simp [rieszIdempotent_def]

@[simp]
theorem rieszIdempotent_compl (a : A) (K : Clopens (spectrum ℂ a)) :
    rieszIdempotent a Kᶜ = 1 - rieszIdempotent a K := by
  simp [rieszIdempotent_def]

theorem rieszIdempotent_sup (a : A) (K L : Clopens (spectrum ℂ a)) :
    rieszIdempotent a (K ⊔ L) =
      rieszIdempotent a K + rieszIdempotent a L - rieszIdempotent a K * rieszIdempotent a L := by
  simp [rieszIdempotent_def, indicator_sup]

/-- Riesz idempotents of disjoint clopen parts of the spectrum are orthogonal. -/
theorem rieszIdempotent_mul_rieszIdempotent_of_disjoint (a : A) {K L : Clopens (spectrum ℂ a)}
    (h : Disjoint K L) : rieszIdempotent a K * rieszIdempotent a L = 0 := by
  rw [← rieszIdempotent_inf, h.eq_bot, rieszIdempotent_bot]

theorem rieszIdempotent_sup_of_disjoint (a : A) {K L : Clopens (spectrum ℂ a)}
    (h : Disjoint K L) :
    rieszIdempotent a (K ⊔ L) = rieszIdempotent a K + rieszIdempotent a L := by
  simp [rieszIdempotent_def, indicator_sup_of_disjoint h]

/-- The Riesz idempotent of a finite pairwise disjoint union of clopen parts of the spectrum is
the sum of their Riesz idempotents. -/
theorem rieszIdempotent_finsetSup (a : A) {ι : Type*} {t : Finset ι}
    {K : ι → Clopens (spectrum ℂ a)} (hK : (t : Set ι).PairwiseDisjoint K) :
    rieszIdempotent a (t.sup K) = ∑ i ∈ t, rieszIdempotent a (K i) := by
  simp [rieszIdempotent_def, indicator_finsetSup hK]

/-- The Riesz idempotents of a finite partition of the spectrum into clopen parts sum to `1`. -/
theorem sum_rieszIdempotent_eq_one (a : A) {ι : Type*} [Fintype ι]
    {K : ι → Clopens (spectrum ℂ a)} (hK : Pairwise (Disjoint on K))
    (hcover : ∀ x : spectrum ℂ a, ∃ i, x ∈ K i) :
    ∑ i, rieszIdempotent a (K i) = 1 := by
  simp [rieszIdempotent_def, ← map_sum, sum_indicator_eq_one hK hcover]

theorem commute_rieszIdempotent_rieszIdempotent (a : A) (K L : Clopens (spectrum ℂ a)) :
    Commute (rieszIdempotent a K) (rieszIdempotent a L) :=
  (Commute.all _ _).map _

end TauCeti

open TauCeti

/-- Every element commuting with `a` commutes with the Riesz idempotents of `a`. -/
theorem Commute.rieszIdempotent_right {A : Type*} [NormedRing A] [NormedAlgebra ℂ A]
    [CompleteSpace A] {a b : A} (hb : Commute b a) (K : Clopens (spectrum ℂ a)) :
    Commute b (rieszIdempotent a K) :=
  hb.holomorphicCalculus_right _

namespace TauCeti

open holomorphicGerms

variable {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A]

theorem commute_rieszIdempotent (a : A) (K : Clopens (spectrum ℂ a)) :
    Commute a (rieszIdempotent a K) :=
  (Commute.refl a).rieszIdempotent_right K

/-- `1` lies in the spectrum of the Riesz idempotent of `K` exactly when `K` is nonempty. -/
theorem one_mem_spectrum_rieszIdempotent_iff (a : A) (K : Clopens (spectrum ℂ a)) :
    1 ∈ spectrum ℂ (rieszIdempotent a K) ↔ K ≠ ⊥ := by
  rw [rieszIdempotent_def, spectrum_holomorphicCalculus, spectrum_eq]
  simp only [mem_ofPred_eq, eval_indicator_eq_one_iff]
  refine ⟨fun ⟨x, hx, hxK⟩ hK ↦ ?_, fun hK ↦ not_forall_not.mp fun h ↦ hK (Clopens.ext ?_)⟩
  · exact (hK ▸ hxK : (⟨x, hx⟩ : spectrum ℂ a) ∈ (⊥ : Clopens (spectrum ℂ a)))
  · exact eq_empty_of_forall_notMem fun y hy ↦ h y ⟨y.2, hy⟩

/-- `0` lies in the spectrum of the Riesz idempotent of `K` exactly when `K` is not the whole
spectrum. -/
theorem zero_mem_spectrum_rieszIdempotent_iff (a : A) (K : Clopens (spectrum ℂ a)) :
    0 ∈ spectrum ℂ (rieszIdempotent a K) ↔ K ≠ ⊤ := by
  rw [rieszIdempotent_def, spectrum_holomorphicCalculus, spectrum_eq]
  simp only [mem_ofPred_eq, eval_indicator_eq_zero_iff]
  refine ⟨fun ⟨x, hx, hxK⟩ hK ↦ hxK (hK ▸ mem_univ _), fun hK ↦
    not_forall_not.mp fun h ↦ hK (Clopens.ext ?_)⟩
  exact eq_univ_of_forall fun y ↦ not_not.mp (h y ∘ fun hy ↦ ⟨y.2, hy⟩)

/-- A Riesz idempotent vanishes exactly when its part of the spectrum is empty. -/
@[simp]
theorem rieszIdempotent_eq_zero_iff (a : A) (K : Clopens (spectrum ℂ a)) :
    rieszIdempotent a K = 0 ↔ K = ⊥ := by
  refine ⟨fun h ↦ not_not.mp fun hK ↦ ?_, fun h ↦ by simp [h]⟩
  have h1 := (one_mem_spectrum_rieszIdempotent_iff a K).mpr hK
  rw [h, spectrum.mem_iff] at h1
  simp at h1

/-- A Riesz idempotent is `1` exactly when its part of the spectrum is the whole spectrum. -/
@[simp]
theorem rieszIdempotent_eq_one_iff (a : A) (K : Clopens (spectrum ℂ a)) :
    rieszIdempotent a K = 1 ↔ K = ⊤ := by
  rw [← compl_eq_bot, ← rieszIdempotent_eq_zero_iff, rieszIdempotent_compl, sub_eq_zero, eq_comm]

/-- **Corner spectrum**, unit form: for `p = rieszIdempotent a K`, the element
`(μ - a) p + (1 - p)` is a unit exactly when `μ` lies outside `K`. -/
theorem isUnit_sub_mul_rieszIdempotent_add_iff (a : A) (K : Clopens (spectrum ℂ a)) (μ : ℂ) :
    IsUnit ((algebraMap ℂ A μ - a) * rieszIdempotent a K + (1 - rieszIdempotent a K)) ↔
      μ ∉ ((↑) '' (K : Set (spectrum ℂ a)) : Set ℂ) := by
  have h : (algebraMap ℂ A μ - a) * rieszIdempotent a K + (1 - rieszIdempotent a K) =
      holomorphicCalculus a ((algebraMap ℂ _ μ - ofFun id analyticOnNhd_id) *
        holomorphicGerms.indicator K + (1 - holomorphicGerms.indicator K)) := by
    simp [rieszIdempotent_def]
  rw [h, isUnit_holomorphicCalculus_iff]
  simp only [mem_image, SetLike.mem_coe, not_exists, not_and]
  refine ⟨fun h ⟨x, hx⟩ hxK hxμ ↦ h x hx ?_, fun h x hx ↦ ?_⟩
  · simp [eval_indicator_of_mem hxK, ← hxμ]
  · by_cases hxK : (⟨x, hx⟩ : spectrum ℂ a) ∈ K
    · simpa [eval_indicator_of_mem hxK, sub_eq_zero] using fun h' ↦ h _ hxK h'.symm
    · simp [eval_indicator_of_notMem hxK]

/-- **Corner spectrum**: for `p = rieszIdempotent a K`, the element `μ - a` is invertible in the
corner algebra `p A p`, whose unit is `p`, exactly when `μ` lies outside `K`. Thus the spectrum
of `a` in this corner is `K`. -/
theorem exists_rieszIdempotent_corner_inverse_iff (a : A) (K : Clopens (spectrum ℂ a)) (μ : ℂ) :
    (∃ b, rieszIdempotent a K * b * rieszIdempotent a K = b ∧
        b * (algebraMap ℂ A μ - a) = rieszIdempotent a K ∧
        (algebraMap ℂ A μ - a) * b = rieszIdempotent a K) ↔
      μ ∉ ((↑) '' (K : Set (spectrum ℂ a)) : Set ℂ) := by
  rw [← isUnit_sub_mul_rieszIdempotent_add_iff]
  set p := rieszIdempotent a K
  set c := algebraMap ℂ A μ - a
  have hp : p * p = p := isIdempotentElem_rieszIdempotent a K
  have hpc : Commute p c :=
    ((Algebra.commute_algebraMap_left μ p).sub_left (commute_rieszIdempotent a K)).symm
  clear_value p c
  constructor
  · rintro ⟨b, hb, hbc, hcb⟩
    have hpb : p * b = b := by rw [← hb, ← mul_assoc, ← mul_assoc, hp]
    have hbp : b * p = b := by rw [← hb, mul_assoc, hp]
    -- `b + (1 - p)` is a two-sided inverse of `c p + (1 - p)`.
    refine ⟨⟨c * p + (1 - p), b + (1 - p), ?_, ?_⟩, rfl⟩
    · calc (c * p + (1 - p)) * (b + (1 - p))
          = c * (p * b) + c * (p - p * p) + (b - p * b) + (1 - p - p + p * p) := by noncomm_ring
        _ = 1 := by rw [hpb, hp, hcb]; noncomm_ring
    · calc (b + (1 - p)) * (c * p + (1 - p))
          = b * c * p + (b - b * p) + (c * p - p * c * p) + (1 - p - p + p * p) := by
            noncomm_ring
        _ = 1 := by rw [hbc, hbp, hpc.eq, mul_assoc c, hp]; abel
  · rintro ⟨u, hu⟩
    -- `p` commutes with `u = c p + (1 - p)`, hence with its inverse; take `b = p u⁻¹`.
    have hpu : Commute p u := by
      rw [hu]
      exact (hpc.mul_right (.refl p)).add_right ((Commute.one_right p).sub_right (.refl p))
    have hpu' : Commute p ↑u⁻¹ := hpu.units_inv_right
    have hup : c * p = u * p := by
      rw [hu, add_mul, sub_mul, one_mul, hp, sub_self, add_zero, mul_assoc, hp]
    refine ⟨p * ↑u⁻¹, ?_, ?_, ?_⟩
    · rw [← mul_assoc p p, hp, mul_assoc, ← hpu'.eq, ← mul_assoc, hp]
    · rw [hpu'.eq, mul_assoc, hpc.eq, hup, ← mul_assoc, Units.inv_mul, one_mul]
    · rw [← mul_assoc, hup, mul_assoc, hpu'.eq, ← mul_assoc, Units.mul_inv, one_mul]

end TauCeti

namespace ContinuousLinearMap

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

open Module.End

/-- The range of the Riesz idempotent of `K` is invariant under every operator commuting with
`T`: it is a hyperinvariant subspace of `T`. -/
theorem range_rieszIdempotent_mem_invtSubmodule {T S : E →L[ℂ] E} (hS : Commute S T)
    (K : Clopens (spectrum ℂ T)) :
    (rieszIdempotent T K).range ∈ invtSubmodule S.toLinearMap := by
  rw [mem_invtSubmodule_iff_mapsTo]
  rintro _ ⟨x, rfl⟩
  exact ⟨S x, by simpa using congrArg (· x) (hS.rieszIdempotent_right K).eq.symm⟩

/-- **Spectral decomposition** of a bounded operator: for a clopen part `K` of the spectrum of
`T`, the ranges of the Riesz idempotents of `K` and of its complement are topological
complements. Both are closed and hyperinvariant (`range_rieszIdempotent_mem_invtSubmodule`). -/
theorem isTopCompl_range_rieszIdempotent_range_rieszIdempotent_compl (T : E →L[ℂ] E)
    (K : Clopens (spectrum ℂ T)) :
    Submodule.IsTopCompl (rieszIdempotent T K).range (rieszIdempotent T Kᶜ).range := by
  have hP := isIdempotentElem_rieszIdempotent T K
  have hker : (rieszIdempotent T K).ker = (rieszIdempotent T Kᶜ).range := by
    have hP' : IsIdempotentElem ((rieszIdempotent T K : E →L[ℂ] E) : E →ₗ[ℂ] E) :=
      hP.map toLinearMapRingHom
    rw [rieszIdempotent_compl, LinearMap.IsIdempotentElem.ker_eq_range_one_sub hP']
    rfl
  exact hker ▸ IsIdempotentElem.isTopCompl hP

theorem isClosed_range_rieszIdempotent (T : E →L[ℂ] E) (K : Clopens (spectrum ℂ T)) :
    IsClosed ((rieszIdempotent T K).range : Set E) :=
  (isTopCompl_range_rieszIdempotent_range_rieszIdempotent_compl T K).isClosed

/-- The range of a Riesz idempotent is zero exactly when its part of the spectrum is empty. -/
theorem range_rieszIdempotent_eq_bot_iff (T : E →L[ℂ] E) (K : Clopens (spectrum ℂ T)) :
    (rieszIdempotent T K).range = ⊥ ↔ K = ⊥ := by
  rw [LinearMap.range_eq_bot, ← rieszIdempotent_eq_zero_iff T K, ← toLinearMap_zero, coe_inj]

/-- The range of a Riesz idempotent is the whole space exactly when its part of the spectrum is
the whole spectrum. -/
theorem range_rieszIdempotent_eq_top_iff (T : E →L[ℂ] E) (K : Clopens (spectrum ℂ T)) :
    (rieszIdempotent T K).range = ⊤ ↔ K = ⊤ := by
  rw [← compl_eq_bot, ← range_rieszIdempotent_eq_bot_iff T Kᶜ]
  have h := (isTopCompl_range_rieszIdempotent_range_rieszIdempotent_compl T K).isCompl
  exact ⟨fun h' ↦ by rw [← h.inf_eq_bot, h', top_inf_eq],
    fun h' ↦ by rw [← h.sup_eq_top, h', sup_bot_eq]⟩

/-- A bounded operator on a complex Banach space whose spectrum is not preconnected has a nonzero
proper closed hyperinvariant subspace, namely the range of a nontrivial Riesz idempotent. -/
theorem exists_isClosed_ne_bot_ne_top_forall_commute_mem_invtSubmodule_of_not_isPreconnected
    {T : E →L[ℂ] E} (hT : ¬IsPreconnected (spectrum ℂ T)) :
    ∃ M : Submodule ℂ E, IsClosed (M : Set E) ∧ M ≠ ⊥ ∧ M ≠ ⊤ ∧
      ∀ S : E →L[ℂ] E, Commute S T → M ∈ invtSubmodule S.toLinearMap := by
  rw [isPreconnected_iff_preconnectedSpace, preconnectedSpace_iff_clopen] at hT
  push Not at hT
  obtain ⟨K, hK, hK0, hK1⟩ := hT
  refine ⟨(rieszIdempotent T ⟨K, hK⟩).range, isClosed_range_rieszIdempotent T _, ?_, ?_,
    fun S hS ↦ range_rieszIdempotent_mem_invtSubmodule hS _⟩
  · rw [Ne, range_rieszIdempotent_eq_bot_iff, ← SetLike.coe_set_eq]
    exact hK0.ne_empty
  · rw [Ne, range_rieszIdempotent_eq_top_iff, ← SetLike.coe_set_eq]
    exact hK1

end ContinuousLinearMap
