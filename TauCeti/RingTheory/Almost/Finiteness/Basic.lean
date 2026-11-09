/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.FinitePresentation
public import TauCeti.RingTheory.Almost.BasicSetup

import Mathlib.RingTheory.Finiteness.Cardinality
import Mathlib.RingTheory.Finiteness.Ideal
import TauCeti.Algebra.Module.Projective.Schanuel
import TauCeti.RingTheory.Ideal.IdempotentFG

/-!
# Almost finitely generated and almost finitely presented modules

Let `(V, m)` be a basic setup. A `V`-module `N` is *almost finitely generated* if for every
finitely generated ideal `m₀ ≤ m` there is a linear map `φ : Vⁿ → N` whose cokernel is killed by
`m₀`, and *almost finitely presented* if moreover `φ` can be completed to a complex
`Vʳ → Vⁿ → N` whose homology at `Vⁿ` is killed by `m₀`; the integers and maps may depend on `m₀`.
These are Gabber–Ramero's honest-module descriptions of the corresponding notions for almost
modules (Proposition 2.3.10). The *uniform* variant fixes the number `n` of generators for all
`m₀` at once.

Finite generation, finite presentation and `n` generators give the corresponding almost notions
for every setup, and for the classical setup `(V, V)` the almost notions are the ordinary ones.
An almost zero module is almost finitely presented, and the uniform bound `0` characterises almost
zero modules. Almost finite generation is invariant under almost isomorphisms. The uniform bound
is preserved along a map with almost zero cokernel for every setup, and under Gabber–Ramero's
condition (A), `BasicSetup.IsFilteredPrincipal`, it is invariant under almost isomorphisms with
the same bound. So almost finite generation, and under condition (A) the uniform bound, are
properties of the almost module `N^a` rather than of the representative `N`.

## Main definitions

* `TauCeti.Almost.BasicSetup.AlmostFG`: almost finitely generated modules.
* `TauCeti.Almost.BasicSetup.UniformlyAlmostFG`: almost finitely generated with a uniform bound
  on the number of generators.
* `TauCeti.Almost.BasicSetup.AlmostFP`: almost finitely presented modules.

## Main results

* `TauCeti.Almost.BasicSetup.almostFG_iff_exists_fg`: almost finite generation in terms of
  finitely generated submodules containing `m₀ • N`.
* `TauCeti.Almost.BasicSetup.almostFG_of_finite`,
  `TauCeti.Almost.BasicSetup.almostFP_of_finitePresentation`: finite generation and finite
  presentation imply their almost counterparts.
* `TauCeti.Almost.BasicSetup.almostFG_classical_iff`,
  `TauCeti.Almost.BasicSetup.almostFP_classical_iff`,
  `TauCeti.Almost.BasicSetup.uniformlyAlmostFG_classical_iff`: the classical setup recovers
  `Module.Finite`, `Module.FinitePresentation` and surjections from `Vⁿ`.
* `TauCeti.Almost.BasicSetup.uniformlyAlmostFG_bound_zero_iff`: the uniform bound `0` means
  almost zero; `TauCeti.Almost.BasicSetup.IsAlmostZero.almostFP`: almost zero modules are almost
  finitely presented.
* `TauCeti.Almost.BasicSetup.IsAlmostIso.almostFG_iff`: almost finite generation is invariant
  under almost isomorphisms.
* `TauCeti.Almost.BasicSetup.UniformlyAlmostFG.of_isAlmostZero_quotient_range` and
  `TauCeti.Almost.BasicSetup.UniformlyAlmostFG.iff_of_isAlmostIso`: the uniform bound passes
  along maps with almost zero cokernel, and under condition (A) it is invariant under almost
  isomorphisms (Gabber–Ramero Remark 2.3.9).

## References

* O. Gabber, L. Ramero, *Almost ring theory*, Lecture Notes in Mathematics 1800, §2.3:
  Definition 2.3.8, Remark 2.3.9 and Proposition 2.3.10.
* P. Scholze, *Perfectoid spaces*, Publ. Math. IHÉS 116 (2012), §4, Definition/Proposition 4.7.
-/

public section

open LinearMap Submodule TauCeti
open scoped Pointwise

namespace TauCeti.Almost.BasicSetup

universe u

variable {V : Type u} [CommRing V] (S : BasicSetup V)

/-! ### Definitions -/

/-- A `V`-module `N` is *almost finitely generated* for the basic setup `(V, m)` if for every
finitely generated ideal `m₀ ≤ m` there is a linear map `Vⁿ → N` whose cokernel is killed by `m₀`
(Gabber–Ramero Proposition 2.3.10(i)). -/
def AlmostFG (N : Type*) [AddCommGroup N] [Module V N] : Prop :=
  ∀ m₀ : Ideal V, m₀ ≤ S.ideal → m₀.FG → ∃ (n : ℕ) (φ : (Fin n → V) →ₗ[V] N),
    m₀ • (⊤ : Submodule V N) ≤ range φ

/-- A `V`-module `N` is *uniformly almost finitely generated with bound `n`* if for every finitely
generated ideal `m₀ ≤ m` there is a linear map `Vⁿ → N`, with this fixed `n`, whose cokernel is
killed by `m₀`. Under condition (A) this is Gabber–Ramero's uniform bound of the almost module
`N^a` (Definition 2.3.8(iii) and Remark 2.3.9). -/
def UniformlyAlmostFG (N : Type*) [AddCommGroup N] [Module V N] (n : ℕ) : Prop :=
  ∀ m₀ : Ideal V, m₀ ≤ S.ideal → m₀.FG → ∃ φ : (Fin n → V) →ₗ[V] N,
    m₀ • (⊤ : Submodule V N) ≤ range φ

/-- A `V`-module `N` is *almost finitely presented* for the basic setup `(V, m)` if for every
finitely generated ideal `m₀ ≤ m` there is a complex `Vʳ → Vⁿ → N` whose cokernel and whose
homology at `Vⁿ` are killed by `m₀` (Gabber–Ramero Proposition 2.3.10(ii)(c)). The integers and
the maps may depend on `m₀`. -/
def AlmostFP (N : Type*) [AddCommGroup N] [Module V N] : Prop :=
  ∀ m₀ : Ideal V, m₀ ≤ S.ideal → m₀.FG → ∃ (r n : ℕ) (ψ : (Fin r → V) →ₗ[V] (Fin n → V))
    (φ : (Fin n → V) →ₗ[V] N), φ ∘ₗ ψ = 0 ∧ m₀ • (⊤ : Submodule V N) ≤ range φ ∧
      m₀ • ker φ ≤ range ψ

variable {S} {M N : Type*} [AddCommGroup M] [Module V M] [AddCommGroup N] [Module V N]

theorem almostFG_iff : S.AlmostFG N ↔ ∀ m₀ : Ideal V, m₀ ≤ S.ideal → m₀.FG →
    ∃ (n : ℕ) (φ : (Fin n → V) →ₗ[V] N), m₀ • (⊤ : Submodule V N) ≤ range φ :=
  Iff.rfl

theorem uniformlyAlmostFG_iff {n : ℕ} : S.UniformlyAlmostFG N n ↔
    ∀ m₀ : Ideal V, m₀ ≤ S.ideal → m₀.FG → ∃ φ : (Fin n → V) →ₗ[V] N,
      m₀ • (⊤ : Submodule V N) ≤ range φ :=
  Iff.rfl

theorem almostFP_iff : S.AlmostFP N ↔ ∀ m₀ : Ideal V, m₀ ≤ S.ideal → m₀.FG →
    ∃ (r n : ℕ) (ψ : (Fin r → V) →ₗ[V] (Fin n → V)) (φ : (Fin n → V) →ₗ[V] N),
      φ ∘ₗ ψ = 0 ∧ m₀ • (⊤ : Submodule V N) ≤ range φ ∧ m₀ • ker φ ≤ range ψ :=
  Iff.rfl

/-- Almost finite generation in terms of submodules: for every finitely generated `m₀ ≤ m`,
some finitely generated submodule of `N` contains `m₀ • N`. -/
theorem almostFG_iff_exists_fg : S.AlmostFG N ↔ ∀ m₀ : Ideal V, m₀ ≤ S.ideal → m₀.FG →
    ∃ P : Submodule V N, P.FG ∧ m₀ • (⊤ : Submodule V N) ≤ P := by
  refine forall₃_congr fun m₀ _ _ ↦ ⟨fun ⟨n, φ, h⟩ ↦
    ⟨_, (fg_iff_exists_fin_linearMap _ _).mpr ⟨n, φ, rfl⟩, h⟩, fun ⟨P, hP, h⟩ ↦ ?_⟩
  obtain ⟨n, φ, rfl⟩ := (fg_iff_exists_fin_linearMap _ _).mp hP
  exact ⟨n, φ, h⟩

/-! ### First properties -/

/-- A uniformly almost finitely generated module is almost finitely generated. -/
theorem UniformlyAlmostFG.almostFG {n : ℕ} (h : S.UniformlyAlmostFG N n) : S.AlmostFG N :=
  fun m₀ hm hfg ↦ ⟨n, h m₀ hm hfg⟩

/-- A uniform bound on the number of generators can be enlarged. -/
theorem UniformlyAlmostFG.mono {n n' : ℕ} (h : S.UniformlyAlmostFG N n) (hn : n ≤ n') :
    S.UniformlyAlmostFG N n' := fun m₀ hm hfg ↦ by
  obtain ⟨φ, hφ⟩ := h m₀ hm hfg
  refine ⟨φ ∘ₗ funLeft V V (Fin.castLE hn), ?_⟩
  rwa [range_comp_of_range_eq_top _
    (range_eq_top.mpr (funLeft_surjective_of_injective _ _ _ (Fin.castLE_injective hn)))]

/-- An almost finitely presented module is almost finitely generated. -/
theorem AlmostFP.almostFG (h : S.AlmostFP N) : S.AlmostFG N := fun m₀ hm hfg ↦
  let ⟨_, n, _, φ, _, hφ, _⟩ := h m₀ hm hfg
  ⟨n, φ, hφ⟩

variable (S) in
/-- A module generated by `n` elements is uniformly almost finitely generated with bound `n`. -/
theorem uniformlyAlmostFG_of_surjective {n : ℕ} (φ : (Fin n → V) →ₗ[V] N)
    (hφ : Function.Surjective φ) : S.UniformlyAlmostFG N n :=
  fun _ _ _ ↦ ⟨φ, by simp [range_eq_top.mpr hφ]⟩

variable (S) in
/-- A finitely generated module is almost finitely generated. -/
theorem almostFG_of_finite [Module.Finite V N] : S.AlmostFG N :=
  let ⟨_, φ, hφ⟩ := Module.Finite.exists_fin' V N
  (uniformlyAlmostFG_of_surjective S φ hφ).almostFG

variable (S) in
/-- A finitely presented module is almost finitely presented. -/
theorem almostFP_of_finitePresentation [Module.FinitePresentation V N] : S.AlmostFP N := by
  obtain ⟨n, r, φ, ψ, hφ, hψφ⟩ := Module.FinitePresentation.exists_fin' V N
  refine fun m₀ _ _ ↦ ⟨r, n, ψ, φ, hψφ.linearMap_comp_eq_zero, by simp [range_eq_top.mpr hφ], ?_⟩
  rw [hψφ.linearMap_ker_eq]
  exact smul_le_right

/-! ### Almost zero modules -/

/-- The uniform bound `0` characterises the almost zero modules. -/
@[simp]
theorem uniformlyAlmostFG_bound_zero_iff : S.UniformlyAlmostFG N 0 ↔ S.IsAlmostZero N := by
  refine ⟨fun h ↦ isAlmostZero_iff.mpr fun ε hε x ↦ ?_, fun h m₀ hm _ ↦
    ⟨0, by rw [h.smul_top_eq_bot hm]; exact bot_le⟩⟩
  obtain ⟨φ, hφ⟩ := h (Ideal.span {ε}) (by simpa [Ideal.span_le]) (Submodule.fg_span_singleton ε)
  obtain ⟨y, hy⟩ := hφ (smul_mem_smul (Ideal.mem_span_singleton_self ε) mem_top)
  rw [← hy, Subsingleton.elim y 0, map_zero]

/-- An almost zero module is almost finitely presented. -/
theorem IsAlmostZero.almostFP (h : S.IsAlmostZero N) : S.AlmostFP N := fun m₀ hm _ ↦
  ⟨0, 0, 0, 0, by simp, by rw [h.smul_top_eq_bot hm]; exact bot_le,
    fun y _ ↦ Subsingleton.elim (0 : Fin 0 → V) y ▸ zero_mem _⟩

/-- For the zero setup every module is almost finitely presented. -/
@[simp]
theorem almostFP_zero : (zero V).AlmostFP N :=
  isAlmostZero_zero.almostFP

/-! ### The classical setup -/

/-- For the classical setup, the uniform bound `n` means generation by `n` elements. -/
@[simp]
theorem uniformlyAlmostFG_classical_iff {n : ℕ} :
    (classical V).UniformlyAlmostFG N n ↔
      ∃ φ : (Fin n → V) →ₗ[V] N, Function.Surjective φ := by
  refine ⟨fun h ↦ ?_, fun ⟨φ, hφ⟩ ↦ uniformlyAlmostFG_of_surjective _ φ hφ⟩
  obtain ⟨φ, hφ⟩ := h ⊤ (by simp) (Module.Finite.fg_top (R := V) (M := V))
  exact ⟨φ, range_eq_top.mp (top_le_iff.mp (by simpa using hφ))⟩

/-- For the classical setup, almost finite generation is finite generation. -/
@[simp]
theorem almostFG_classical_iff : (classical V).AlmostFG N ↔ Module.Finite V N := by
  refine ⟨fun h ↦ ?_, fun _ ↦ almostFG_of_finite _⟩
  obtain ⟨n, φ, hφ⟩ := h ⊤ (by simp) (Module.Finite.fg_top (R := V) (M := V))
  exact Module.Finite.of_surjective φ (range_eq_top.mp (top_le_iff.mp (by simpa using hφ)))

/-- For the classical setup, almost finite presentation is finite presentation. -/
@[simp]
theorem almostFP_classical_iff :
    (classical V).AlmostFP N ↔ Module.FinitePresentation V N := by
  refine ⟨fun h ↦ ?_, fun _ ↦ almostFP_of_finitePresentation _⟩
  obtain ⟨r, n, ψ, φ, hφψ, hφ, hψ⟩ := h ⊤ (by simp) (Module.Finite.fg_top (R := V) (M := V))
  refine Module.finitePresentation_of_surjective φ
    (range_eq_top.mp (top_le_iff.mp (by simpa using hφ))) ?_
  rw [le_antisymm (by simpa using hψ) (range_le_ker_iff.mpr hφψ)]
  exact (fg_iff_exists_fin_linearMap _ _).mpr ⟨r, ψ, rfl⟩

/-! ### Invariance under almost isomorphisms -/

section Invariance

variable {f : M →ₗ[V] N} {K : Ideal V}

/-- If `f : M → N` has almost zero cokernel, `K ≤ m` and `K • M ≤ P`, then
`K ^ 2 • N ≤ f(P)`. -/
theorem pow_two_smul_top_le_map (hf : S.IsAlmostZero (N ⧸ range f)) (hK : K ≤ S.ideal)
    {P : Submodule V M} (hP : K • (⊤ : Submodule V M) ≤ P) :
    (K ^ 2) • (⊤ : Submodule V N) ≤ P.map f := by
  rw [sq, Submodule.mul_smul]
  refine (smul_mono_right K (hf.smul_top_le hK)).trans ?_
  rw [range_eq_map, ← map_smul'']
  exact map_mono hP

/-- Backward transfer: if `K • N ≤ P`, `K • P ≤ f(Q)` and `f` has almost zero kernel, then
`K ^ 3 • M ≤ Q`. -/
private theorem pow_three_smul_top_le (hf : S.IsAlmostZero (ker f)) (hK : K ≤ S.ideal)
    {P : Submodule V N} {Q : Submodule V M} (hP : K • (⊤ : Submodule V N) ≤ P)
    (hQ : K • P ≤ Q.map f) : (K ^ 3) • (⊤ : Submodule V M) ≤ Q := by
  have h₁ : K • K • (⊤ : Submodule V M) ≤ Q ⊔ ker f := by
    rw [← comap_map_eq, ← map_le_iff_le_comap, map_smul'', map_smul'']
    exact (smul_mono_right K (smul_mono_right K le_top |>.trans hP)).trans hQ
  rw [pow_succ', sq, Submodule.mul_smul, Submodule.mul_smul]
  refine (smul_mono_right K h₁).trans ?_
  rw [smul_sup, hf.smul_eq_bot hK, sup_bot_eq]
  exact smul_le_right

/-- Almost finite generation passes along a linear map with almost zero cokernel; in particular
quotients of almost finitely generated modules are almost finitely generated. -/
theorem AlmostFG.of_isAlmostZero_quotient_range (h : S.AlmostFG M)
    (hf : S.IsAlmostZero (N ⧸ range f)) : S.AlmostFG N := by
  rw [almostFG_iff_exists_fg] at h ⊢
  intro m₀ hm hfg
  obtain ⟨K, hKfg, hK, hm₀⟩ :=
    Ideal.exists_fg_le_pow_of_isIdempotentElem S.isIdempotentElem hfg hm 2
  obtain ⟨P, hPfg, hP⟩ := h K hK hKfg
  exact ⟨P.map f, hPfg.map f,
    (smul_mono_left hm₀).trans (pow_two_smul_top_le_map hf hK hP)⟩

/-- Almost finite generation descends along a linear map with almost zero kernel and cokernel. -/
theorem AlmostFG.of_isAlmostIso (h : S.AlmostFG N) (hf : S.IsAlmostIso f) : S.AlmostFG M := by
  obtain ⟨hker, hcoker⟩ := isAlmostIso_iff.mp hf
  rw [almostFG_iff_exists_fg] at h ⊢
  intro m₀ hm hfg
  obtain ⟨K, hKfg, hK, hm₀⟩ :=
    Ideal.exists_fg_le_pow_of_isIdempotentElem S.isIdempotentElem hfg hm 3
  obtain ⟨P, hPfg, hP⟩ := h K hK hKfg
  have hKP := Submodule.FG.smul hKfg hPfg
  -- Lift a finite family generating `K • P ≤ range f` along `f`.
  obtain ⟨r, ψ, hψ⟩ := (fg_iff_exists_fin_linearMap _ _).mp hKP
  obtain ⟨χ, hχ⟩ := exists_comp_eq_of_range_le (b := f)
    (hψ ▸ (smul_mono_right K le_top).trans (hcoker.smul_top_le hK))
  refine ⟨range χ, (fg_iff_exists_fin_linearMap _ _).mpr ⟨r, χ, rfl⟩,
    (smul_mono_left hm₀).trans (pow_three_smul_top_le hker hK hP ?_)⟩
  rw [← range_comp, hχ, hψ]

/-- Almost finite generation is invariant under almost isomorphisms. -/
theorem IsAlmostIso.almostFG_iff (hf : S.IsAlmostIso f) : S.AlmostFG M ↔ S.AlmostFG N :=
  ⟨fun h ↦ h.of_isAlmostZero_quotient_range (isAlmostIso_iff.mp hf).2,
    fun h ↦ h.of_isAlmostIso hf⟩

/-- The uniform bound passes along a linear map with almost zero cokernel, for every setup. -/
theorem UniformlyAlmostFG.of_isAlmostZero_quotient_range {n : ℕ} (h : S.UniformlyAlmostFG M n)
    (hf : S.IsAlmostZero (N ⧸ range f)) : S.UniformlyAlmostFG N n := by
  intro m₀ hm hfg
  obtain ⟨K, hKfg, hK, hm₀⟩ :=
    Ideal.exists_fg_le_pow_of_isIdempotentElem S.isIdempotentElem hfg hm 2
  obtain ⟨φ, hφ⟩ := h K hK hKfg
  refine ⟨f ∘ₗ φ, (smul_mono_left hm₀).trans ?_⟩
  rw [range_comp]
  exact pow_two_smul_top_le_map hf hK hφ

/-- Under condition (A), the uniform bound of an almost isomorphism's source and target agree
(Gabber–Ramero Remark 2.3.9). -/
theorem UniformlyAlmostFG.iff_of_isAlmostIso (hS : S.IsFilteredPrincipal) (hf : S.IsAlmostIso f)
    (n : ℕ) : S.UniformlyAlmostFG M n ↔ S.UniformlyAlmostFG N n := by
  obtain ⟨hker, hcoker⟩ := isAlmostIso_iff.mp hf
  refine ⟨fun h ↦ h.of_isAlmostZero_quotient_range hcoker, fun h m₀ hm hfg ↦ ?_⟩
  obtain ⟨K, hKfg, hK, hm₀⟩ :=
    Ideal.exists_fg_le_pow_of_isIdempotentElem S.isIdempotentElem hfg hm 3
  obtain ⟨z, hz, hKz⟩ := hS.exists_le_span_singleton hKfg hK
  have hzm : Ideal.span {z} ≤ S.ideal := by simpa [Ideal.span_le]
  obtain ⟨φ, hφ⟩ := h _ hzm (Submodule.fg_span_singleton z)
  have hzφ : Ideal.span {z} • range φ ≤ range (z • φ) := smul_le.mpr fun a ha y hy ↦ by
    obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.mp ha
    obtain ⟨v, rfl⟩ := hy
    exact ⟨b • v, by simp [mul_smul, smul_comm b z]⟩
  have hrange : range (z • φ) ≤ range f := by
    rintro _ ⟨v, rfl⟩
    exact hcoker.smul_top_le hzm (smul_mem_smul (Ideal.mem_span_singleton_self z) mem_top)
  obtain ⟨χ, hχ⟩ := exists_comp_eq_of_range_le hrange
  refine ⟨χ, (smul_mono_left (hm₀.trans (Ideal.pow_right_mono hKz 3))).trans
    (pow_three_smul_top_le hker hzm hφ ?_)⟩
  rw [← range_comp, hχ]
  exact hzφ

end Invariance

end TauCeti.Almost.BasicSetup
