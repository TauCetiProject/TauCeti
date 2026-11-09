/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Almost.Finiteness.Basic

import Mathlib.RingTheory.Finiteness.Cardinality
import Mathlib.RingTheory.Finiteness.Ideal
import TauCeti.Algebra.Module.Projective.Schanuel
import TauCeti.RingTheory.Ideal.IdempotentFG

/-!
# Almost finite presentation: Schanuel's lemma, invariance and exact sequences

Let `(V, m)` be a basic setup. This file develops almost finitely presented modules
(`TauCeti.Almost.BasicSetup.AlmostFP`) along the lines of the classical theory of finitely
presented modules.

The basic tool is an almost form of Schanuel's lemma: if `N` is almost finitely presented and
`φ : Vⁿ → N` is any map whose cokernel is killed by a finitely generated ideal `J`, then for every
finitely generated `K ≤ m` the kernel of `φ` is finitely generated up to multiplication by
`J * K ^ 2`. Classically (`J = K = V`) this says that a surjection from a finite free module onto a
finitely presented module has finitely generated kernel.

From it we deduce:

* almost finite presentation is invariant under almost isomorphisms, so it is a property of the
  almost module `N^a`;
* for a surjection `M → N` with `N` almost finitely presented and `M` almost finitely generated,
  the kernel is almost finitely generated; if `M` is almost finitely presented, `N` is almost
  finitely presented if and only if the kernel is almost finitely generated;
* in a short exact sequence, almost finitely generated (respectively presented) end terms make the
  middle term almost finitely generated (respectively presented).

These are the almost analogues of `Module.FinitePresentation.fg_ker`,
`Module.FinitePresentation.fg_ker_iff` and `Module.finitePresentation_of_ker`.

## Main results

* `TauCeti.Almost.BasicSetup.almostFP_iff_exists_fg_ker`: almost finite presentation in terms of a
  finitely generated submodule of relations.
* `TauCeti.Almost.BasicSetup.AlmostFP.exists_fg_smul_ker_le`: the almost Schanuel lemma.
* `TauCeti.Almost.BasicSetup.IsAlmostIso.almostFP_iff`: invariance under almost isomorphisms.
* `TauCeti.Almost.BasicSetup.AlmostFP.almostFG_ker`,
  `TauCeti.Almost.BasicSetup.AlmostFP.of_surjective`,
  `TauCeti.Almost.BasicSetup.AlmostFP.almostFG_ker_iff`: kernels and quotients
  (Gabber–Ramero Lemma 2.3.17(ii)).
* `TauCeti.Almost.BasicSetup.AlmostFG.extension`, `TauCeti.Almost.BasicSetup.AlmostFP.extension`:
  extensions (Gabber–Ramero Lemma 2.3.17(i)).

## References

* O. Gabber, L. Ramero, *Almost ring theory*, Lecture Notes in Mathematics 1800, §2.3:
  Proposition 2.3.10 and Lemma 2.3.17.
-/

public section

open LinearMap Submodule
open scoped Pointwise

namespace TauCeti.Almost.BasicSetup

universe u

variable {V : Type u} [CommRing V] {S : BasicSetup V}
  {M N P : Type*} [AddCommGroup M] [Module V M] [AddCommGroup N] [Module V N]
  [AddCommGroup P] [Module V P]

/-! ### Auxiliary submodule estimates -/

/-- The ideal spanned by `s` multiplies `p` into `q` as soon as every element of `s` does. -/
private theorem span_smul_le {s : Set V} {p q : Submodule V M}
    (h : ∀ r ∈ s, ∀ x ∈ p, r • x ∈ q) : Ideal.span s • p ≤ q := by
  rw [← p.span_eq, span_smul_span, span_le]
  rintro _ ⟨r, hr, x, hx, rfl⟩
  exact h r hr x hx

/-- A triple product `span s * span t * K` multiplies `p` into `q` as soon as `j • k • k' • x ∈ q`
for all generators `j ∈ s`, `k ∈ t` and all `k' ∈ K`, `x ∈ p`. -/
private theorem span_mul_span_mul_smul_le {s t : Set V} {K : Ideal V} {p q : Submodule V M}
    (h : ∀ j ∈ s, ∀ k ∈ t, ∀ k' ∈ K, ∀ x ∈ p, j • k • k' • x ∈ q) :
    (Ideal.span s * (Ideal.span t * K)) • p ≤ q := by
  rw [Submodule.mul_smul, Submodule.mul_smul]
  refine span_smul_le fun j hj y hy ↦ ?_
  suffices h' : Ideal.span t • K • p ≤ q.comap (j • LinearMap.id) from mem_comap.mp (h' hy)
  refine span_smul_le fun k hk y hy ↦ ?_
  suffices h' : K • p ≤ q.comap ((j * k) • LinearMap.id) by
    simpa only [mem_comap, LinearMap.smul_apply, LinearMap.id_apply, mul_smul] using h' hy
  exact smul_le.mpr fun k' hk' x hx ↦ by
    simpa only [mem_comap, LinearMap.smul_apply, LinearMap.id_apply, mul_smul] using
      h j hj k hk k' hk' x hx

/-- If the cokernel of `φ` is killed by `K`, then `K` multiplies `ker l` into the image of
`ker (l ∘ φ)`. -/
private theorem smul_ker_le_map_ker_comp {φ : P →ₗ[V] M} {K : Ideal V}
    (hφ : K • (⊤ : Submodule V M) ≤ range φ) (l : M →ₗ[V] N) :
    K • ker l ≤ (ker (l ∘ₗ φ)).map φ := by
  rw [ker_comp, map_comap_eq]
  exact le_inf ((smul_mono_right K le_top).trans hφ) smul_le_right

/-- Composing with a surjection keeps the cokernel killed by `K`. -/
private theorem smul_top_le_range_comp {φ : P →ₗ[V] M} {K : Ideal V}
    (hφ : K • (⊤ : Submodule V M) ≤ range φ) {l : M →ₗ[V] N} (hl : Function.Surjective l) :
    K • (⊤ : Submodule V N) ≤ range (l ∘ₗ φ) := by
  rw [range_comp, ← range_eq_top.mpr hl, range_eq_map l, ← map_smul'']
  exact map_mono hφ

/-- If `f` has almost zero kernel and `K ≤ m`, then `K` multiplies `ker (f ∘ φ)` into `ker φ`. -/
private theorem smul_ker_comp_le_ker {f : M →ₗ[V] N} (hf : S.IsAlmostZero (ker f))
    {K : Ideal V} (hK : K ≤ S.ideal) (φ : P →ₗ[V] M) : K • ker (f ∘ₗ φ) ≤ ker φ := by
  refine smul_le.mpr fun k hk x hx ↦ ?_
  rw [ker_comp] at hx
  have h := smul_mem_smul hk (mem_comap.mp hx)
  rw [hf.smul_eq_bot hK, mem_bot] at h
  rw [mem_ker, map_smul, h]

/-! ### The almost Schanuel lemma -/

/-- Almost finite presentation in terms of a finitely generated module of relations: for every
finitely generated `m₀ ≤ m` there are a map `φ : Vⁿ → N` whose cokernel is killed by `m₀` and a
finitely generated submodule of `ker φ` containing `m₀ • ker φ`. -/
theorem almostFP_iff_exists_fg_ker : S.AlmostFP N ↔ ∀ m₀ : Ideal V, m₀ ≤ S.ideal → m₀.FG →
    ∃ (n : ℕ) (φ : (Fin n → V) →ₗ[V] N), m₀ • (⊤ : Submodule V N) ≤ range φ ∧
      ∃ L ≤ ker φ, L.FG ∧ m₀ • ker φ ≤ L := by
  rw [almostFP_iff]
  refine forall₃_congr fun m₀ _ _ ↦ ⟨fun ⟨r, n, ψ, φ, hφψ, hφ, hψ⟩ ↦
    ⟨n, φ, hφ, range ψ, range_le_ker_iff.mpr hφψ, fg_range ψ, hψ⟩,
    fun ⟨n, φ, hφ, L, hL, hLfg, h⟩ ↦ ?_⟩
  obtain ⟨r, ψ, rfl⟩ := (fg_iff_exists_fin_linearMap _ _).mp hLfg
  exact ⟨r, n, ψ, φ, range_le_ker_iff.mp hL, hφ, h⟩

/-- **Almost Schanuel lemma.** Let `N` be almost finitely presented and let `φ : Vⁿ → N` have
cokernel killed by a finitely generated ideal `J`. Then for every finitely generated `K ≤ m`, some
finitely generated submodule of `ker φ` contains `(J * K ^ 2) • ker φ`.

For the classical setup and `J = K = V` this says that a surjection from a finite free module onto
a finitely presented module has finitely generated kernel. -/
theorem AlmostFP.exists_fg_smul_ker_le (hN : S.AlmostFP N) {J K : Ideal V} (hJ : J.FG)
    (hK : K ≤ S.ideal) (hKfg : K.FG) {n : ℕ} (φ : (Fin n → V) →ₗ[V] N)
    (hφ : J • (⊤ : Submodule V N) ≤ range φ) :
    ∃ L ≤ ker φ, L.FG ∧ (J * K ^ 2) • ker φ ≤ L := by
  classical
  obtain ⟨r, n', ψ, φ', hφψ, hφ', hψ⟩ := almostFP_iff.mp hN K hK hKfg
  -- `α j` lifts `j • φ'` along `φ`, and `β k` lifts `k • φ` along `φ'`.
  have hα (j : V) (hj : j ∈ J) :
      ∃ α : (Fin n' → V) →ₗ[V] (Fin n → V), φ ∘ₗ α = j • φ' :=
    exists_comp_eq_of_range_le <| by
      rintro _ ⟨x, rfl⟩
      exact hφ (smul_mem_smul hj mem_top)
  have hβ (k : V) (hk : k ∈ K) :
      ∃ β : (Fin n → V) →ₗ[V] (Fin n' → V), φ' ∘ₗ β = k • φ :=
    exists_comp_eq_of_range_le <| by
      rintro _ ⟨x, rfl⟩
      exact hφ' (smul_mem_smul hk mem_top)
  choose! α hα using hα
  choose! β hβ using hβ
  obtain ⟨sJ, rfl⟩ := hJ
  obtain ⟨sK, rfl⟩ := hKfg
  -- The relations are generated by the ranges of `α j ∘ ψ` and of `δ j k = j * k - α j ∘ β k`,
  -- for generators `j` of `J` and `k` of `K`.
  let δ (j k : V) : (Fin n → V) →ₗ[V] (Fin n → V) := (j * k) • LinearMap.id - α j ∘ₗ β k
  let L : Submodule V (Fin n → V) := ⨆ j ∈ sJ, (range (α j ∘ₗ ψ) ⊔ ⨆ k ∈ sK, range (δ j k))
  have hαψL (j : V) (hj : j ∈ sJ) : range (α j ∘ₗ ψ) ≤ L :=
    le_iSup₂_of_le j hj le_sup_left
  have hδL (j : V) (hj : j ∈ sJ) (k : V) (hk : k ∈ sK) : range (δ j k) ≤ L :=
    le_iSup₂_of_le j hj (le_sup_of_le_right (le_iSup₂_of_le k hk le_rfl))
  have key (j : V) (hj : j ∈ sJ) (k : V) (hk : k ∈ sK) (k' : V) (hk' : k' ∈ span V (sK : Set V))
      (x : Fin n → V) (hx : x ∈ ker φ) : j • k • k' • x ∈ L := by
    have h₁ : β k x ∈ ker φ' := by
      rw [mem_ker, ← LinearMap.comp_apply, hβ k (subset_span hk), LinearMap.smul_apply,
        mem_ker.mp hx, smul_zero]
    obtain ⟨z, hz⟩ := hψ (smul_mem_smul hk' h₁)
    have h₂ : j • k • k' • x = k' • δ j k x + (α j ∘ₗ ψ) z := by
      simp only [δ, LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.smul_apply,
        LinearMap.id_apply, hz, map_smul, smul_sub]
      rw [sub_add_cancel, smul_comm k' (j * k), mul_smul]
    rw [h₂]
    exact add_mem (smul_mem _ _ (hδL j hj k hk (mem_range_self _ x)))
      (hαψL j hj (mem_range_self _ z))
  refine ⟨L, iSup₂_le fun j hj ↦ sup_le ?_ (iSup₂_le fun k hk ↦ ?_),
    fg_biSup sJ _ fun j _ ↦ (fg_range _).sup (fg_biSup sK _ fun k _ ↦ fg_range _), ?_⟩
  · rw [range_le_ker_iff, ← comp_assoc, hα j (subset_span hj), smul_comp, hφψ, smul_zero]
  · refine range_le_ker_iff.mpr (LinearMap.ext fun x ↦ ?_)
    have h₁ := LinearMap.congr_fun (hα j (subset_span hj)) (β k x)
    have h₂ := LinearMap.congr_fun (hβ k (subset_span hk)) x
    simp only [LinearMap.comp_apply, LinearMap.smul_apply] at h₁ h₂
    simp [δ, h₁, h₂, mul_smul]
  · rw [sq]
    exact span_mul_span_mul_smul_le key

/-! ### Invariance under almost isomorphisms -/

section Invariance

variable {f : M →ₗ[V] N}

/-- Almost finite presentation descends along a linear map with almost zero kernel and cokernel. -/
theorem AlmostFP.of_isAlmostIso (h : S.AlmostFP N) (hf : S.IsAlmostIso f) : S.AlmostFP M := by
  obtain ⟨hker, hcoker⟩ := isAlmostIso_iff.mp hf
  have hM : S.AlmostFG M := h.almostFG.of_isAlmostIso hf
  rw [almostFP_iff_exists_fg_ker]
  intro m₀ hm hfg
  obtain ⟨K, hKfg, hK, hm₀⟩ :=
    Ideal.exists_fg_le_pow_of_isIdempotentElem S.isIdempotentElem hfg hm 5
  obtain ⟨n, φ, hφ⟩ := almostFG_iff.mp hM K hK hKfg
  -- `f ∘ φ` has cokernel killed by `K ^ 2`, so its relations are almost finitely generated, and
  -- multiplying them by `K` lands in the relations of `φ`.
  have hfφ : (K * K) • (⊤ : Submodule V N) ≤ range (f ∘ₗ φ) := by
    rw [range_comp, ← sq]
    exact pow_two_smul_top_le_map hcoker hK hφ
  obtain ⟨L, hL, hLfg, hKL⟩ := h.exists_fg_smul_ker_le (hKfg.mul hKfg) hK hKfg (f ∘ₗ φ) hfφ
  refine ⟨n, φ, (smul_mono_left (hm₀.trans (Ideal.pow_le_self (by norm_num)))).trans hφ, K • L,
    (smul_mono_right K hL).trans (smul_ker_comp_le_ker hker hK φ), Submodule.FG.smul hKfg hLfg,
    (smul_mono_left hm₀).trans ?_⟩
  calc K ^ 5 • ker φ = K • (K * K * K ^ 2) • ker φ := by rw [← Submodule.mul_smul]; ring_nf
    _ ≤ K • L := smul_mono_right K ((smul_mono_right _ (ker_le_ker_comp φ f)).trans hKL)

/-- Almost finite presentation is invariant under almost isomorphisms. -/
theorem IsAlmostIso.almostFP_iff (hf : S.IsAlmostIso f) : S.AlmostFP M ↔ S.AlmostFP N := by
  refine ⟨fun h ↦ ?_, fun h ↦ h.of_isAlmostIso hf⟩
  obtain ⟨hker, hcoker⟩ := isAlmostIso_iff.mp hf
  rw [almostFP_iff_exists_fg_ker] at h ⊢
  intro m₀ hm hfg
  obtain ⟨K, hKfg, hK, hm₀⟩ :=
    Ideal.exists_fg_le_pow_of_isIdempotentElem S.isIdempotentElem hfg hm 2
  obtain ⟨n, φ, hφ, L, hL, hLfg, hKL⟩ := h K hK hKfg
  refine ⟨n, f ∘ₗ φ, (smul_mono_left hm₀).trans ?_, L, hL.trans (ker_le_ker_comp φ f), hLfg,
    (smul_mono_left hm₀).trans ?_⟩
  · rw [range_comp]
    exact pow_two_smul_top_le_map hcoker hK hφ
  · rw [sq, Submodule.mul_smul]
    exact (smul_mono_right K (smul_ker_comp_le_ker hker hK φ)).trans hKL

end Invariance

/-! ### Kernels and quotients -/

/-- The kernel of a surjection from an almost finitely generated module onto an almost finitely
presented module is almost finitely generated (Gabber–Ramero Lemma 2.3.17(ii)). This is the almost
analogue of `Module.FinitePresentation.fg_ker`. -/
theorem AlmostFP.almostFG_ker (hN : S.AlmostFP N) (hM : S.AlmostFG M) (l : M →ₗ[V] N)
    (hl : Function.Surjective l) : S.AlmostFG (ker l) := by
  rw [almostFG_iff_exists_fg]
  intro m₀ hm hfg
  obtain ⟨K, hKfg, hK, hm₀⟩ :=
    Ideal.exists_fg_le_pow_of_isIdempotentElem S.isIdempotentElem hfg hm 4
  obtain ⟨n, φ, hφ⟩ := almostFG_iff.mp hM K hK hKfg
  obtain ⟨L, hL, hLfg, hKL⟩ :=
    hN.exists_fg_smul_ker_le hKfg hK hKfg (l ∘ₗ φ) (smul_top_le_range_comp hφ hl)
  have hLl : L.map φ ≤ ker l := by
    rw [map_le_iff_le_comap, ← ker_comp]
    exact hL
  refine ⟨(L.map φ).comap (ker l).subtype,
    fg_of_fg_map_injective _ (ker l).injective_subtype ?_, ?_⟩
  · rw [map_comap_subtype, inf_of_le_right hLl]
    exact hLfg.map φ
  · rw [← map_le_map_iff_of_injective (ker l).injective_subtype, map_comap_subtype,
      inf_of_le_right hLl, map_smul'', map_subtype_top]
    calc m₀ • ker l ≤ (K * K ^ 2 * K) • ker l := smul_mono_left (hm₀.trans_eq (by ring))
      _ = (K * K ^ 2) • K • ker l := Submodule.mul_smul ..
      _ ≤ (K * K ^ 2) • (ker (l ∘ₗ φ)).map φ :=
        smul_mono_right _ (smul_ker_le_map_ker_comp hφ l)
      _ = ((K * K ^ 2) • ker (l ∘ₗ φ)).map φ := (map_smul'' ..).symm
      _ ≤ L.map φ := map_mono hKL

/-- A quotient of an almost finitely presented module by an almost finitely generated submodule is
almost finitely presented (Gabber–Ramero Lemma 2.3.17(ii)). This is the almost analogue of
`Module.finitePresentation_of_surjective`. -/
theorem AlmostFP.of_surjective (hM : S.AlmostFP M) (l : M →ₗ[V] N) (hl : Function.Surjective l)
    (hker : S.AlmostFG (ker l)) : S.AlmostFP N := by
  rw [almostFP_iff_exists_fg_ker] at hM ⊢
  rw [almostFG_iff_exists_fg] at hker
  intro m₀ hm hfg
  obtain ⟨K, hKfg, hK, hm₀⟩ :=
    Ideal.exists_fg_le_pow_of_isIdempotentElem S.isIdempotentElem hfg hm 3
  obtain ⟨n, φ, hφ, L, hL, hLfg, hKL⟩ := hM K hK hKfg
  obtain ⟨Q, hQfg, hKQ⟩ := hker K hK hKfg
  -- `K • Q` is a finitely generated submodule of `ker l ∩ range φ`; lift its generators to `Vⁿ`.
  obtain ⟨t, ρ, hρ⟩ :=
    (fg_iff_exists_fin_linearMap _ _).mp (Submodule.FG.smul hKfg (hQfg.map (ker l).subtype))
  obtain ⟨ρ', hρ'⟩ := exists_comp_eq_of_range_le (b := φ) (a := ρ) <| by
    rw [hρ]
    exact (smul_mono_right K le_top).trans hφ
  have hρl : range ρ ≤ ker l := by
    rw [hρ]
    exact smul_le_right.trans (map_subtype_le _ _)
  have hKker : K • K • ker l ≤ range ρ := by
    have h := map_mono (f := (ker l).subtype) hKQ
    rw [map_smul'', map_subtype_top] at h
    rw [hρ]
    exact smul_mono_right K h
  refine ⟨n, l ∘ₗ φ,
    (smul_mono_left (hm₀.trans (Ideal.pow_le_self (by norm_num)))).trans
      (smul_top_le_range_comp hφ hl),
    range ρ' ⊔ L, sup_le ?_ (hL.trans (ker_le_ker_comp φ l)), (fg_range ρ').sup hLfg,
    (smul_mono_left hm₀).trans ?_⟩
  · rw [range_le_ker_iff, comp_assoc, hρ', ← range_le_ker_iff]
    exact hρl
  · -- `K ^ 2` multiplies the relations of `l ∘ φ` into `range ρ' + ker φ`.
    have h₂ : (K * K) • ker (l ∘ₗ φ) ≤ range ρ' ⊔ ker φ := by
      rw [← comap_map_eq, ← map_le_iff_le_comap, map_smul'', ← range_comp, hρ',
        Submodule.mul_smul]
      refine (smul_mono_right K (smul_mono_right K ?_)).trans hKker
      rw [map_le_iff_le_comap, ← ker_comp]
    calc (K ^ 3) • ker (l ∘ₗ φ) = K • (K * K) • ker (l ∘ₗ φ) := by
          rw [← Submodule.mul_smul]; ring_nf
      _ ≤ K • (range ρ' ⊔ ker φ) := smul_mono_right K h₂
      _ = K • range ρ' ⊔ K • ker φ := smul_sup ..
      _ ≤ range ρ' ⊔ L := sup_le_sup smul_le_right hKL

/-- For a surjection from an almost finitely presented module, the target is almost finitely
presented if and only if the kernel is almost finitely generated (Gabber–Ramero
Lemma 2.3.17(ii)). This is the almost analogue of `Module.FinitePresentation.fg_ker_iff`. -/
theorem AlmostFP.almostFG_ker_iff (hM : S.AlmostFP M) (l : M →ₗ[V] N)
    (hl : Function.Surjective l) : S.AlmostFG (ker l) ↔ S.AlmostFP N :=
  ⟨hM.of_surjective l hl, fun hN ↦ hN.almostFG_ker hM.almostFG l hl⟩

/-! ### Extensions -/

section Extension

variable {f : M →ₗ[V] N} {g : N →ₗ[V] P}

/-- If `M → N → P → 0` is exact with `M` and `P` almost finitely generated, then `N` is almost
finitely generated (Gabber–Ramero Lemma 2.3.17(i)). -/
theorem AlmostFG.extension (h₁ : S.AlmostFG M) (h₃ : S.AlmostFG P) (hfg : Function.Exact f g)
    (hg : Function.Surjective g) : S.AlmostFG N := by
  rw [almostFG_iff_exists_fg] at h₁ h₃ ⊢
  intro m₀ hm hfg₀
  obtain ⟨K, hKfg, hK, hm₀⟩ :=
    Ideal.exists_fg_le_pow_of_isIdempotentElem S.isIdempotentElem hfg₀ hm 2
  obtain ⟨Q₁, hQ₁fg, hKQ₁⟩ := h₁ K hK hKfg
  obtain ⟨Q₃, hQ₃fg, hKQ₃⟩ := h₃ K hK hKfg
  -- Lift the generators of `Q₃` along `g`.
  obtain ⟨t, ρ, rfl⟩ := (fg_iff_exists_fin_linearMap _ _).mp hQ₃fg
  obtain ⟨ρ', hρ'⟩ := exists_comp_eq_of_range_le (b := g) (a := ρ)
    (by rw [range_eq_top.mpr hg]; exact le_top)
  refine ⟨range ρ' ⊔ Q₁.map f, (fg_range ρ').sup (hQ₁fg.map f), (smul_mono_left hm₀).trans ?_⟩
  have h : K • (⊤ : Submodule V N) ≤ range ρ' ⊔ range f := by
    rw [← hfg.linearMap_ker_eq, ← comap_map_eq, ← map_le_iff_le_comap, map_smul'',
      Submodule.map_top, range_eq_top.mpr hg, ← range_comp, hρ']
    exact hKQ₃
  rw [sq, Submodule.mul_smul]
  calc K • K • (⊤ : Submodule V N) ≤ K • (range ρ' ⊔ range f) := smul_mono_right K h
    _ = K • range ρ' ⊔ (K • (⊤ : Submodule V M)).map f := by
      rw [smul_sup, range_eq_map f, map_smul'']
    _ ≤ range ρ' ⊔ Q₁.map f := sup_le_sup smul_le_right (map_mono hKQ₁)

/-- If `0 → M → N → P → 0` is exact with `M` and `P` almost finitely presented, then `N` is almost
finitely presented (Gabber–Ramero Lemma 2.3.17(i)). This is the almost analogue of
`Module.finitePresentation_of_ker`. -/
theorem AlmostFP.extension (h₁ : S.AlmostFP M) (h₃ : S.AlmostFP P) (hf : Function.Injective f)
    (hfg : Function.Exact f g) (hg : Function.Surjective g) : S.AlmostFP N := by
  have hN : S.AlmostFG N := h₁.almostFG.extension h₃.almostFG hfg hg
  rw [almostFP_iff_exists_fg_ker]
  intro m₀ hm hfg₀
  obtain ⟨K, hKfg, hK, hm₀⟩ :=
    Ideal.exists_fg_le_pow_of_isIdempotentElem S.isIdempotentElem hfg₀ hm 9
  obtain ⟨n, φ, hφ⟩ := almostFG_iff.mp hN K hK hKfg
  -- The relations of `g ∘ φ` are almost generated by the range of some `χ : Vᵗ → Vⁿ`.
  obtain ⟨L₁, hL₁, hL₁fg, hKL₁⟩ :=
    h₃.exists_fg_smul_ker_le hKfg hK hKfg (g ∘ₗ φ) (smul_top_le_range_comp hφ hg)
  obtain ⟨t, χ, rfl⟩ := (fg_iff_exists_fin_linearMap _ _).mp hL₁fg
  -- `φ ∘ χ` lands in `ker g = range f`, so it factors as `f ∘ θ`.
  obtain ⟨θ, hθ⟩ := exists_comp_eq_of_range_le (b := f) (a := φ ∘ₗ χ) <| by
    rw [← hfg.linearMap_ker_eq, range_le_ker_iff, ← comp_assoc, ← range_le_ker_iff]
    exact hL₁
  have hχθ : (ker θ).map χ = range χ ⊓ ker φ := by
    rw [← map_comap_eq, ← ker_comp, ← hθ, ker_comp_of_ker_eq_bot _ (ker_eq_bot.mpr hf)]
  have hK₃ : (K * K ^ 2) • ker φ ≤ (ker θ).map χ :=
    hχθ ▸ le_inf ((smul_mono_right _ (ker_le_ker_comp φ g)).trans hKL₁) smul_le_right
  -- The cokernel of `θ` is killed by `K ^ 4`.
  have hθ₄ : (K * K ^ 2 * K) • (⊤ : Submodule V M) ≤ range θ := by
    rw [← map_le_map_iff_of_injective hf, map_smul'', Submodule.map_top, ← hfg.linearMap_ker_eq,
      ← range_comp, hθ, range_comp, Submodule.mul_smul]
    calc (K * K ^ 2) • K • ker g ≤ (K * K ^ 2) • (ker (g ∘ₗ φ)).map φ :=
          smul_mono_right _ (smul_ker_le_map_ker_comp hφ g)
      _ = ((K * K ^ 2) • ker (g ∘ₗ φ)).map φ := (map_smul'' ..).symm
      _ ≤ (range χ).map φ := map_mono hKL₁
  -- The relations of `θ` are almost finitely generated; their image under `χ` does the job.
  obtain ⟨L₂, hL₂, hL₂fg, hKL₂⟩ :=
    h₁.exists_fg_smul_ker_le ((hKfg.mul hKfg.pow).mul hKfg) hK hKfg θ hθ₄
  refine ⟨n, φ, (smul_mono_left (hm₀.trans (Ideal.pow_le_self (by norm_num)))).trans hφ,
    L₂.map χ, (map_mono hL₂).trans (hχθ.trans_le inf_le_right), hL₂fg.map χ,
    (smul_mono_left hm₀).trans ?_⟩
  calc K ^ 9 • ker φ = (K * K ^ 2 * K * K ^ 2) • (K * K ^ 2) • ker φ := by
        rw [← Submodule.mul_smul]; ring_nf
    _ ≤ (K * K ^ 2 * K * K ^ 2) • (ker θ).map χ := smul_mono_right _ hK₃
    _ = ((K * K ^ 2 * K * K ^ 2) • ker θ).map χ := (map_smul'' ..).symm
    _ ≤ L₂.map χ := map_mono hKL₂

end Extension

end TauCeti.Almost.BasicSetup
