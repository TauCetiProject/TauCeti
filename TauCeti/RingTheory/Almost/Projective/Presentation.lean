/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Almost.Projective.Basic

import TauCeti.RingTheory.Almost.Finiteness.Presentation
import TauCeti.Algebra.Module.Projective.Schanuel
import TauCeti.RingTheory.Ideal.IdempotentFG
import TauCeti.RingTheory.Ideal.Operations

/-!
# Almost finite presentation of almost finite projective modules

An almost finite projective module is almost finitely presented. More precisely, if a map
from a finitely generated module has cokernel killed by a finitely generated ideal `J`, its kernel
is finitely generated up to multiplication by `J * K` for every finitely generated `K ≤ m`.
This gives finite relations for the finite free approximations of an almost finite projective
module, without any assumption that the basic ideal is a filtered union of principal ideals.

## References

* O. Gabber, L. Ramero, *Almost ring theory*, Lecture Notes in Mathematics 1800, §2.4,
  Lemma 2.4.15 and Proposition 2.4.18(i).
-/

public section

open LinearMap Submodule
open scoped Pointwise

namespace TauCeti.Almost.BasicSetup

variable {V : Type*} [CommRing V] {S : BasicSetup V}
  {M : Type*} [AddCommGroup M] [Module V M]

/-- If `M` is almost finite projective and the cokernel of a map `φ` from a finitely generated
module is killed by a finitely generated ideal `J`, then its kernel is finitely generated up to
multiplication by `J * K`, for every finitely generated `K ≤ m`. -/
theorem IsAlmostFiniteProjective.exists_fg_smul_ker_le (h : S.IsAlmostFiniteProjective M)
    {J K : Ideal V} (hJ : J.FG) (hK : K ≤ S.ideal) (hKfg : K.FG)
    {P : Type*} [AddCommGroup P] [Module V P] [Module.Finite V P] (φ : P →ₗ[V] M)
    (hφ : J • (⊤ : Submodule V M) ≤ range φ) :
    ∃ L ≤ ker φ, L.FG ∧ (J * K) • ker φ ≤ L := by
  classical
  have hf (b : V) (hb : b ∈ K) := isAlmostFiniteProjective_iff.mp h b (hK hb)
  choose! r u v hv using hf
  have hα (a b : V) (ha : a ∈ J) :
      ∃ α : (Fin (r b) → V) →ₗ[V] P, φ ∘ₗ α = a • v b :=
    exists_comp_eq_of_range_le <| by
      rintro _ ⟨x, rfl⟩
      exact hφ (smul_mem_smul ha mem_top)
  choose! α hα using hα
  obtain ⟨s, rfl⟩ := hJ
  obtain ⟨t, rfl⟩ := hKfg
  -- These finite-rank defects land in the relations and act there as multiplication by `a * b`.
  let δ (a b : V) : P →ₗ[V] P :=
    (a * b) • LinearMap.id - α a b ∘ₗ u b ∘ₗ φ
  let L : Submodule V P := ⨆ a ∈ s, ⨆ b ∈ t, range (δ a b)
  have hδL (a : V) (ha : a ∈ s) (b : V) (hb : b ∈ t) : range (δ a b) ≤ L :=
    le_iSup₂_of_le a ha (le_iSup₂_of_le b hb le_rfl)
  refine ⟨L, iSup₂_le fun a ha ↦ iSup₂_le fun b hb ↦ ?_,
    fg_biSup s _ fun a _ ↦ fg_biSup t _ fun b _ ↦ fg_range _, ?_⟩
  · refine range_le_ker_iff.mpr (LinearMap.ext fun x ↦ ?_)
    have h₁ := LinearMap.congr_fun (hα a b (subset_span ha)) (u b (φ x))
    have h₂ := LinearMap.congr_fun (hv b (subset_span hb)) (φ x)
    simp only [LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.id_apply] at h₁ h₂
    simp [δ, h₁, h₂, mul_smul]
  · rw [Ideal.span_mul_span, span_smul_le_iff]
    rintro _ ⟨a, ha, b, hb, rfl⟩ x hx
    have hδ : δ a b x = (a * b) • x := by simp [δ, mem_ker.mp hx]
    exact hδ ▸ hδL a ha b hb (mem_range_self _ x)

/-- An almost finite projective module is almost finitely presented
(Gabber–Ramero Proposition 2.4.18(i)). -/
theorem IsAlmostFiniteProjective.almostFP (h : S.IsAlmostFiniteProjective M) : S.AlmostFP M := by
  rw [almostFP_iff_exists_fg_ker]
  intro J hJ hJfg
  obtain ⟨K, hKfg, hK, hJK⟩ :=
    Ideal.exists_fg_le_mul_of_isIdempotentElem S.isIdempotentElem hJfg hJ
  obtain ⟨n, φ, hφ⟩ := almostFG_iff.mp h.almostFG K hK hKfg
  obtain ⟨L, hL, hLfg, hKL⟩ := h.exists_fg_smul_ker_le hKfg hK hKfg φ hφ
  exact ⟨n, φ, (smul_mono_left (hJK.trans Ideal.mul_le_left)).trans hφ,
    L, hL, hLfg, (smul_mono_left hJK).trans hKL⟩

end TauCeti.Almost.BasicSetup
