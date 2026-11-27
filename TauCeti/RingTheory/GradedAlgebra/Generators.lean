/-
Copyright (c) 2026 Mei contributors and The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex, The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.GradedAlgebra.AlgHom
public import Mathlib.Algebra.Algebra.Subalgebra.Lattice
public import TauCeti.RingTheory.GradedAlgebra.DirectSum

/-!
# Homogeneous words in algebra generators

For an arbitrary map of generators `e : S → A` equipped with degrees `deg : S → Γ` in an
additive monoid `Γ`, `TauCeti.GradedAlgebra.wordSpan R e deg n` is the `R`-submodule spanned by
products of generators whose degrees sum to `n`. These spans form a `SetLike.GradedMonoid`
whose supremum over all degrees is `(Algebra.adjoin R (Set.range e)).toSubmodule`. Given any
target family `ℬ : Γ' → S'` whose pieces are closed under addition, `R`-scalar multiplication,
and graded multiplication (`AddSubmonoidClass`, `SMulMemClass`, `SetLike.GradedMonoid`), an
`R`-algebra homomorphism carrying each generator of degree `d` into degree `σ d` for an additive
degree map `σ : Γ →+ Γ'` carries `wordSpan R e deg c` into `ℬ (σ c)`.

If a family of homogeneous elements generates a graded algebra, each graded piece is spanned by
the words in that family whose total degree is exactly the degree of the piece. No basis,
commutativity of the algebra, or positivity of the grading is required.

This reduces questions about a graded piece to words of a prescribed total degree; in
particular, when an additive numerical degree on `Γ` is bounded below by a positive constant on
the generators, fixed total degree bounds word length. Moreover, an algebra map out of such an
algebra is graded as soon as it sends each generator into the piece of the generator's degree.

## Main definitions and results

* `TauCeti.GradedAlgebra.wordSpan`: the `R`-submodule spanned by generator words of a given total
  degree, with `wordSpan_gradedMonoid`, `iSup_wordSpan`, `map_mem_of_mem_wordSpan`, and
  `algHom_apply_of_mem_wordSpan`.
* `TauCeti.GradedAlgebra.grade_eq_wordSpan`: a homogeneous generating family spans each graded piece
  by `wordSpan`, i.e., words of that total degree.
* `TauCeti.GradedAlgebra.grade_le_of_adjoin_eq_top` and
  `TauCeti.GradedAlgebra.grade_le_of_adjoin_range_eq_top`: graded induction from algebra generators
  for any family of submodules `ℬ : Γ → Submodule R A` closed under `1` and graded multiplication.
* `AlgHom.map_mem_of_adjoin_range_eq_top`: an algebra map preserving the degrees of a homogeneous
  generating family preserves the degree of every homogeneous element.
* `GradedAlgHom.ofAdjoinRangeEqTop`: such an algebra map, as a graded algebra map.

## Attribution

`TauCeti.GradedAlgebra.grade_eq_wordSpan` is adapted from
`Mei/RingTheory/GradedAlgebra/Generators.lean` in
[yuma-mizuno-lean/Mei](https://github.com/yuma-mizuno-lean/Mei), commit
`9cf969cdee9748087aae45dbf4888a130890655c` (Apache 2.0). Original copyright and author credit
are retained. The generic `wordSpan` construction and lemmas are generalized from
`TauCeti.UniversalEnvelopingAlgebra.homogeneousSubmodule` (itself adapted from
`Mei/Algebra/Lie/UniversalEnveloping/Grading.lean`, commit
`68536122a97fed8e87bc6870b9427151971b9ab2`).
-/

public section

open scoped DirectSum

namespace TauCeti.GradedAlgebra

open _root_.GradedAlgebra

section WordSpan

variable (R : Type*) {A S Γ : Type*} [AddMonoid Γ]
  [CommSemiring R] [Semiring A] [Algebra R A]

/-- The `R`-submodule spanned by products of generators `e : S → A` whose degrees under
`deg : S → Γ` sum to `n`. -/
def wordSpan (e : S → A) (deg : S → Γ) (n : Γ) : Submodule R A :=
  Submodule.span R {a | ∃ l : List S, (l.map deg).sum = n ∧ (l.map e).prod = a}

/-- The defining word-span formula for `wordSpan R e deg n`. -/
theorem wordSpan_def (e : S → A) (deg : S → Γ) (n : Γ) :
    wordSpan R e deg n =
      Submodule.span R {a | ∃ l : List S, (l.map deg).sum = n ∧ (l.map e).prod = a} :=
  (rfl)

variable {R}

/-- A submodule contains `wordSpan R e deg n` exactly when it contains every word of degree `n`. -/
theorem wordSpan_le_iff {e : S → A} {deg : S → Γ} (n : Γ) (p : Submodule R A) :
    wordSpan R e deg n ≤ p ↔
      ∀ l : List S, (l.map deg).sum = n → (l.map e).prod ∈ p := by
  rw [wordSpan_def, Submodule.span_le]
  exact ⟨fun h l hl => h ⟨l, hl, rfl⟩, by rintro h _ ⟨l, hl, rfl⟩; exact h l hl⟩

/-- A word in `e` lies in the `wordSpan` piece indexed by its total `deg`-degree. -/
theorem prod_mem_wordSpan (e : S → A) (deg : S → Γ) (l : List S) :
    (l.map e).prod ∈ wordSpan R e deg (l.map deg).sum :=
  Submodule.subset_span ⟨l, rfl, rfl⟩

/-- A word in `e` whose `deg`-degrees sum to `n` lies in `wordSpan R e deg n`. -/
theorem prod_mem_wordSpan_of_eq {e : S → A} {deg : S → Γ} {n : Γ} {l : List S}
    (hl : (l.map deg).sum = n) : (l.map e).prod ∈ wordSpan R e deg n :=
  hl ▸ prod_mem_wordSpan e deg l

/-- Structural induction on `wordSpan R e deg n` from generator words of degree `n` under zero,
addition, and `R`-scalar multiplication. -/
@[elab_as_elim]
theorem wordSpan_induction {e : S → A} {deg : S → Γ} {n : Γ} {x : A}
    {P : (x : A) → x ∈ wordSpan R e deg n → Prop} (hx : x ∈ wordSpan R e deg n)
    (word : ∀ l : List S, (hl : (l.map deg).sum = n) →
      P (l.map e).prod (prod_mem_wordSpan_of_eq hl))
    (zero : P 0 (Submodule.zero_mem _))
    (add : ∀ x y hx hy, P x hx → P y hy → P (x + y) (Submodule.add_mem _ hx hy))
    (smul : ∀ (r : R) x hx, P x hx → P (r • x) (Submodule.smul_mem _ r hx)) : P x hx :=
  Submodule.span_induction (by rintro _ ⟨l, hl, rfl⟩; exact word l hl) zero add smul hx

/-- Each generator `e s` lies in `wordSpan R e deg (deg s)`. -/
theorem mem_wordSpan_self (e : S → A) (deg : S → Γ) (s : S) :
    e s ∈ wordSpan R e deg (deg s) := by
  simpa using prod_mem_wordSpan e deg [s]

/-- The supremum of `wordSpan R e deg` over all degrees is the `R`-subalgebra generated by `e`. -/
theorem iSup_wordSpan (e : S → A) (deg : S → Γ) :
    ⨆ n, wordSpan R e deg n = (Algebra.adjoin R (Set.range e)).toSubmodule := by
  have hclosure : (Submonoid.closure (Set.range e) : Set A) =
      Set.range (fun l : List S => (l.map e).prod) := by
    rw [Submonoid.closure_eq_image_prod, ← Set.range_list_map, ← Set.range_comp']
  simp_rw [wordSpan_def, Submodule.iSup_span, Algebra.adjoin_eq_span, hclosure]
  congr 1
  ext a
  simp only [Set.mem_iUnion, Set.mem_ofPred_eq, Set.mem_range]
  exact ⟨fun ⟨_, l, _, hl⟩ => ⟨l, hl⟩, fun ⟨l, hl⟩ => ⟨(l.map deg).sum, l, rfl, hl⟩⟩

/-- Multiplication maps `wordSpan` pieces into the piece of the sum of their degrees. -/
instance wordSpan_gradedMonoid (e : S → A) (deg : S → Γ) :
    SetLike.GradedMonoid (wordSpan R e deg) where
  one_mem := Submodule.subset_span ⟨[], by simp, rfl⟩
  mul_mem := by
    intro m n a b ha hb
    have hmul : wordSpan R e deg m * wordSpan R e deg n ≤ wordSpan R e deg (m + n) := by
      rw [wordSpan_def, wordSpan_def, Submodule.span_mul_span, Submodule.span_le]
      rintro _ ⟨_, ⟨l, hl, rfl⟩, _, ⟨t, ht, rfl⟩, rfl⟩
      simpa [hl, ht] using prod_mem_wordSpan e deg (l ++ t)
    exact hmul (Submodule.mul_mem_mul ha hb)

/-- An `R`-algebra homomorphism carrying each generator `e s` into `ℬ (σ (deg s))` carries
`wordSpan R e deg c` into `ℬ (σ c)`. -/
theorem map_mem_of_mem_wordSpan {B S' Γ' F : Type*} [Semiring B] [Algebra R B]
    [AddMonoid Γ'] [SetLike S' B] [AddSubmonoidClass S' B] [SMulMemClass S' R B]
    {ℬ : Γ' → S'} [SetLike.GradedMonoid ℬ] [FunLike F A B] [AlgHomClass F R A B]
    (f : F) (σ : Γ →+ Γ') {e : S → A} {deg : S → Γ}
    (hf : ∀ s, f (e s) ∈ ℬ (σ (deg s))) {c : Γ} {x : A} (hx : x ∈ wordSpan R e deg c) :
    f x ∈ ℬ (σ c) := by
  induction hx using Submodule.span_induction with
  | mem _ h =>
    obtain ⟨l, hl, rfl⟩ := h
    have hprod := SetLike.list_prod_map_mem_graded l (fun s => σ (deg s)) (fun s => f (e s))
      fun s _ => hf s
    have hsum : (l.map fun s => σ (deg s)).sum = σ c := by
      simpa only [List.map_map, Function.comp_def, map_list_sum] using congrArg σ hl
    simpa only [map_list_prod, List.map_map, Function.comp_def, hsum] using hprod
  | zero => simp [zero_mem]
  | add _ _ _ _ ha hb => simpa only [map_add] using add_mem ha hb
  | smul r _ _ ha => simpa only [map_smul] using SMulMemClass.smul_mem r ha

/-- An `R`-algebra homomorphism to `⨁ n, wordSpan R e deg n` with `DirectSum.coeAlgHom` as a left
inverse that places each generator `e s` in its `(deg s)`-th summand sends every element of
`wordSpan R e deg c` to its canonical summand injection. -/
theorem algHom_apply_of_mem_wordSpan {F : Type*} [DecidableEq Γ]
    {e : S → A} {deg : S → Γ}
    [FunLike F A (⨁ n, wordSpan R e deg n)] [AlgHomClass F R A (⨁ n, wordSpan R e deg n)]
    (f : F) (hcoe : ∀ x, DirectSum.coeAlgHom (wordSpan R e deg) (f x) = x)
    (hf : ∀ s, f (e s) ∈ DirectSum.summand R (fun n => ↥(wordSpan R e deg n)) (deg s))
    {c : Γ} {x : A} (hx : x ∈ wordSpan R e deg c) :
    f x = DirectSum.of (fun n => ↥(wordSpan R e deg n)) c ⟨x, hx⟩ :=
  DirectSum.eq_of_mem_summand_of_coeLinearMap_eq (wordSpan R e deg)
    (map_mem_of_mem_wordSpan (ℬ := DirectSum.summand R fun n => ↥(wordSpan R e deg n))
      f (AddMonoidHom.id Γ) hf hx)
    ((DirectSum.coeLinearMap_eq_coeAlgHom (wordSpan R e deg) (f x)).trans (hcoe x))

end WordSpan

section Words

variable {Γ R A S : Type*} [AddMonoid Γ] [DecidableEq Γ]
  [CommSemiring R] [Semiring A] [Algebra R A]
  (𝒜 : Γ → Submodule R A) [_root_.GradedAlgebra 𝒜]

/-- A homogeneous generating family spans each graded piece by its words of exactly that total
degree (`wordSpan R e deg n`). -/
theorem grade_eq_wordSpan (e : S → A) (deg : S → Γ)
    (he : Algebra.adjoin R (Set.range e) = ⊤) (hhom : ∀ s, e s ∈ 𝒜 (deg s)) (n : Γ) :
    𝒜 n = wordSpan R e deg n := by
  have hle (m : Γ) : wordSpan R e deg m ≤ 𝒜 m := fun _ hx =>
    map_mem_of_mem_wordSpan (AlgHom.id R A) (AddMonoidHom.id Γ)
      (fun s => by simpa only [AlgHom.id_apply, AddMonoidHom.id_apply] using hhom s) hx
  refine le_antisymm ?_ (hle n)
  intro x hx
  have hsup : x ∈ ⨆ m, wordSpan R e deg m := by
    rw [iSup_wordSpan, he, Algebra.top_toSubmodule]
    trivial
  have hproj : proj 𝒜 n x ∈ wordSpan R e deg n := by
    refine Submodule.iSup_induction (wordSpan R e deg)
      (motive := fun y => proj 𝒜 n y ∈ wordSpan R e deg n) hsup
      (fun m y hy => ?_) (by simp) (fun y z hy hz => by simpa only [map_add] using add_mem hy hz)
    by_cases hm : m = n
    · subst hm
      simpa only [proj_apply, DirectSum.decompose_of_mem_same 𝒜 (hle m hy)] using hy
    · simp only [proj_apply, DirectSum.decompose_of_mem_ne 𝒜 (hle m hy) hm, Submodule.zero_mem]
  simpa only [proj_apply, DirectSum.decompose_of_mem_same 𝒜 hx] using hproj

end Words

section Induction

variable {Γ R A : Type*} [AddMonoid Γ] [DecidableEq Γ]
  [CommSemiring R] [Semiring A] [Algebra R A]
  (𝒜 : Γ → Submodule R A) [_root_.GradedAlgebra 𝒜]

/-- **Graded induction from algebra generators.** If a family of submodules `ℬ : Γ → Submodule R A`
contains `1` in degree `0`, is closed under products of homogeneous elements, and an
algebra-generating set `S` lies in `⨆ i, 𝒜 i ⊓ ℬ i`, then `𝒜 n ≤ ℬ n` for every `n`. -/
theorem grade_le_of_adjoin_eq_top {ℬ : Γ → Submodule R A}
    (h1 : (1 : A) ∈ ℬ 0)
    (hmul : ∀ {i j : Γ} {a b : A},
      a ∈ 𝒜 i → a ∈ ℬ i → b ∈ 𝒜 j → b ∈ ℬ j → a * b ∈ ℬ (i + j))
    {S : Set A} (hadj : Algebra.adjoin R S = ⊤)
    (hS : S ⊆ (⨆ i : Γ, 𝒜 i ⊓ ℬ i : Submodule R A)) (n : Γ) :
    𝒜 n ≤ ℬ n := by
  let F : Γ → Submodule R A := fun i ↦ 𝒜 i ⊓ ℬ i
  let P : Submodule R A := ⨆ i, F i
  have h1P : (1 : A) ∈ P := le_iSup F 0 ⟨SetLike.GradedOne.one_mem, h1⟩
  have hmulP : ∀ a b, a ∈ P → b ∈ P → a * b ∈ P := fun a b ha hb ↦ by
    refine Submodule.iSup_induction F (motive := fun a ↦ a * b ∈ P) ha
      (fun i a ha ↦ ?_) (by simp) fun a₁ a₂ h₁ h₂ ↦ by rw [add_mul]; exact add_mem h₁ h₂
    refine Submodule.iSup_induction F (motive := fun b ↦ a * b ∈ P) hb
      (fun j b hb ↦ ?_) (by simp) fun b₁ b₂ h₁ h₂ ↦ by rw [mul_add]; exact add_mem h₁ h₂
    exact le_iSup F (i + j) ⟨SetLike.GradedMul.mul_mem ha.1 hb.1, hmul ha.1 ha.2 hb.1 hb.2⟩
  have htop : (⊤ : Subalgebra R A) ≤ P.toSubalgebra h1P hmulP :=
    hadj ▸ Algebra.adjoin_le fun x hx ↦ Submodule.mem_toSubalgebra.2 (hS hx)
  have hproj : P ≤ (ℬ n).comap (proj 𝒜 n) := iSup_le fun i x hx ↦ by
    rw [Submodule.mem_comap, proj_apply]
    by_cases hin : i = n
    · subst hin
      simpa [DirectSum.decompose_of_mem_same 𝒜 hx.1] using hx.2
    · simp [DirectSum.decompose_of_mem_ne 𝒜 hx.1 hin]
  intro a ha
  have haP : a ∈ P := Submodule.mem_toSubalgebra.1 (htop Algebra.mem_top)
  simpa only [Submodule.mem_comap, proj_apply, DirectSum.decompose_of_mem_same 𝒜 ha] using hproj haP

/-- If a linear map `g : V →ₗ[R] A` has algebra-generating image, `𝒱` spans `V`, and `g` maps
each `𝒱 i` into `𝒜 i ⊓ ℬ i`, then under the closure hypotheses of
`TauCeti.GradedAlgebra.grade_le_of_adjoin_eq_top`, `𝒜 n ≤ ℬ n` for every `n`. -/
theorem grade_le_of_adjoin_range_eq_top {V : Type*} [AddCommMonoid V] [Module R V]
    {𝒱 : Γ → Submodule R V} {ℬ : Γ → Submodule R A}
    (h1 : (1 : A) ∈ ℬ 0)
    (hmul : ∀ {i j : Γ} {a b : A},
      a ∈ 𝒜 i → a ∈ ℬ i → b ∈ 𝒜 j → b ∈ ℬ j → a * b ∈ ℬ (i + j))
    {g : V →ₗ[R] A} (hadj : Algebra.adjoin R (Set.range g) = ⊤) (h𝒱 : ⨆ i, 𝒱 i = ⊤)
    (hg : ∀ {i : Γ} {x : V}, x ∈ 𝒱 i → g x ∈ 𝒜 i)
    (hℬ : ∀ {i : Γ} {x : V}, x ∈ 𝒱 i → g x ∈ ℬ i) (n : Γ) :
    𝒜 n ≤ ℬ n := by
  refine grade_le_of_adjoin_eq_top 𝒜 h1 hmul hadj ?_ n
  rintro _ ⟨v, rfl⟩
  have hle : (⊤ : Submodule R V) ≤ (⨆ i : Γ, 𝒜 i ⊓ ℬ i).comap g := by
    rw [← h𝒱]
    exact iSup_le fun i x hx ↦
      le_iSup (fun k ↦ 𝒜 k ⊓ ℬ k) i ⟨hg hx, hℬ hx⟩
  exact hle Submodule.mem_top

end Induction

end TauCeti.GradedAlgebra

section AlgHom

variable {Γ R A B S : Type*} [AddMonoid Γ] [DecidableEq Γ]
  [CommSemiring R] [Semiring A] [Algebra R A] [Semiring B] [Algebra R B]
  {𝒜 : Γ → Submodule R A} [GradedAlgebra 𝒜] {e : S → A} {deg : S → Γ}

/-- An algebra map out of a graded algebra generated by homogeneous elements `e s` of degrees
`deg s` sends every element of degree `n` to an element of degree `n`, provided it sends each
`e s` to an element of degree `deg s`. -/
theorem AlgHom.map_mem_of_adjoin_range_eq_top {ℬ : Γ → Submodule R B}
    [SetLike.GradedMonoid ℬ] (φ : A →ₐ[R] B) (he : Algebra.adjoin R (Set.range e) = ⊤)
    (hhom : ∀ s, e s ∈ 𝒜 (deg s)) (hφ : ∀ s, φ (e s) ∈ ℬ (deg s)) {n : Γ} {a : A}
    (ha : a ∈ 𝒜 n) : φ a ∈ ℬ n := by
  rw [TauCeti.GradedAlgebra.grade_eq_wordSpan 𝒜 e deg he hhom n] at ha
  exact TauCeti.GradedAlgebra.map_mem_of_mem_wordSpan φ (AddMonoidHom.id Γ) hφ ha

/-- An algebra map out of a graded algebra generated by homogeneous elements `e s` of degrees
`deg s`, sending each `e s` to an element of degree `deg s`, as a graded algebra map. -/
def GradedAlgHom.ofAdjoinRangeEqTop {ℬ : Γ → Submodule R B} [GradedAlgebra ℬ]
    (φ : A →ₐ[R] B) (he : Algebra.adjoin R (Set.range e) = ⊤) (hhom : ∀ s, e s ∈ 𝒜 (deg s))
    (hφ : ∀ s, φ (e s) ∈ ℬ (deg s)) : 𝒜 →ₐᵍ[R] ℬ where
  toAlgHom := φ
  map_mem := φ.map_mem_of_adjoin_range_eq_top he hhom hφ

@[simp]
theorem GradedAlgHom.coe_ofAdjoinRangeEqTop {ℬ : Γ → Submodule R B} [GradedAlgebra ℬ]
    (φ : A →ₐ[R] B) (he : Algebra.adjoin R (Set.range e) = ⊤) (hhom : ∀ s, e s ∈ 𝒜 (deg s))
    (hφ : ∀ s, φ (e s) ∈ ℬ (deg s)) : ⇑(ofAdjoinRangeEqTop φ he hhom hφ) = φ := (rfl)

end AlgHom
