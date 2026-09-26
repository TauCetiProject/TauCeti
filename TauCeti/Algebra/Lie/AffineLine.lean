/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Nilradical

/-!
# The two-dimensional nonabelian Lie algebra

`TauCeti.LieAlgebra.AffineLine K` is the Lie algebra of the group of affine transformations
`t ↦ a * t + b` of the line: the free `K`-module on a dilation `x` and a translation `y`, with
`⁅x, y⁆ = y`.  Over a field it is, up to isomorphism, the only nonabelian two-dimensional Lie
algebra (a classification not carried out here), and it is the standard witness that the nilradical
is strictly larger than Mathlib's `LieAlgebra.maxNilpotentIdeal`: its ideal of translations is
abelian, so it is the whole nilradical, while `⁅x, y⁆ = y` says the ambient algebra acts on it by an
invertible, hence non-nilpotent, operator, so `maxNilpotentIdeal` is `⊥`.

The adjoint action of an element `u` is computed here too: it sends the dilation direction into
the translation line and scales that line by the dilation coordinate `u.1`, so all of its positive
powers are scalar multiples of it.  Over a field of positive characteristic that monic relation is
what produces the explicit central `p`-polynomials of
`TauCeti.Algebra.Lie.UniversalEnveloping.AffineLine`.

## Main definitions

* `TauCeti.LieAlgebra.AffineLine`: the two-dimensional nonabelian Lie algebra, with its `dilation`
  `x`, its `translation` `y`, and its ideal `translationIdeal` of translations.

## Main statements

* `TauCeti.LieAlgebra.AffineLine.ad_pow`: every positive power of the adjoint action of an
  element is a scalar multiple of it, the scalar being a power of the dilation coordinate.
* `TauCeti.LieAlgebra.AffineLine.nilradical_eq_translationIdeal`: the nilradical is the ideal of
  translations, the span of `y`.
* `TauCeti.LieAlgebra.AffineLine.maxNilpotentIdeal_eq_bot`: Mathlib's `maxNilpotentIdeal` is `⊥`.
* `TauCeti.LieAlgebra.AffineLine.maxNilpotentIdeal_lt_nilradical`: hence the containment
  `TauCeti.LieAlgebra.maxNilpotentIdeal_le_nilradical` is strict in general.

## References

* [N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 1-3*][bourbaki1975], Chapter I, §4.
-/

public section

namespace TauCeti

namespace LieAlgebra

/-- **The two-dimensional nonabelian Lie algebra** over `K`, the Lie algebra of the group of
affine transformations `t ↦ a * t + b` of the line: the `K`-module `K × K`, whose first coordinate
is the dilation coordinate and whose second is the translation coordinate, with the bracket
determined by `⁅x, y⁆ = y` for the basis `x = (1, 0)`, `y = (0, 1)`. -/
@[expose, reducible] def AffineLine (K : Type*) : Type _ := K × K

namespace AffineLine

variable {K : Type*} [CommRing K]

instance instAddCommGroup : AddCommGroup (AffineLine K) := inferInstanceAs (AddCommGroup (K × K))

instance instModule : Module K (AffineLine K) := inferInstanceAs (Module K (K × K))

instance instIsNoetherian [IsNoetherian K K] : IsNoetherian K (AffineLine K) :=
  inferInstanceAs (IsNoetherian K (K × K))

instance instBracket : Bracket (AffineLine K) (AffineLine K) :=
  ⟨fun u v ↦ ((0 : K), u.1 * v.2 - u.2 * v.1)⟩

omit [CommRing K] in
@[ext] theorem ext {u v : AffineLine K} (h₁ : u.1 = v.1) (h₂ : u.2 = v.2) : u = v := Prod.ext h₁ h₂

@[simp] theorem fst_lie (u v : AffineLine K) : (⁅u, v⁆ : AffineLine K).1 = 0 := rfl

@[simp] theorem snd_lie (u v : AffineLine K) :
    (⁅u, v⁆ : AffineLine K).2 = u.1 * v.2 - u.2 * v.1 := rfl

instance instLieRing : LieRing (AffineLine K) where
  add_lie u v w := by ext <;> simp; ring
  lie_add u v w := by ext <;> simp; ring
  lie_self u := by ext <;> simp; ring
  leibniz_lie u v w := by ext <;> simp; ring

instance instLieAlgebra : LieAlgebra K (AffineLine K) where
  lie_smul c u v := by ext <;> simp; ring

/-- The dilation `x = (1, 0)` of `AffineLine K`. -/
def dilation (K : Type*) [CommRing K] : AffineLine K := (1, 0)

/-- The translation `y = (0, 1)` of `AffineLine K`. -/
def translation (K : Type*) [CommRing K] : AffineLine K := (0, 1)

@[simp] theorem fst_dilation : (dilation K).1 = 1 := (rfl)

@[simp] theorem snd_dilation : (dilation K).2 = 0 := (rfl)

@[simp] theorem fst_translation : (translation K).1 = 0 := (rfl)

@[simp] theorem snd_translation : (translation K).2 = 1 := (rfl)

/-- The defining relation `⁅x, y⁆ = y`. -/
@[simp] theorem lie_dilation_translation : ⁅dilation K, translation K⁆ = translation K := by
  ext <;> simp

/-- The ideal of translations, the span of `y`: the elements whose dilation coordinate vanishes. -/
def translationIdeal (K : Type*) [CommRing K] : LieIdeal K (AffineLine K) where
  carrier := {u | u.1 = 0}
  add_mem' {u v} hu hv := by
    simp only [Set.mem_ofPred_eq] at hu hv ⊢
    rw [Prod.fst_add, hu, hv, add_zero]
  zero_mem' := by
    simp only [Set.mem_ofPred_eq]
    exact Prod.fst_zero
  smul_mem' c u hu := by
    simp only [Set.mem_ofPred_eq] at hu ⊢
    rw [Prod.smul_fst, smul_eq_mul, hu, mul_zero]
  lie_mem {u v} _ := fst_lie u v

@[simp] theorem mem_translationIdeal {u : AffineLine K} :
    u ∈ translationIdeal K ↔ u.1 = 0 := (Iff.rfl)

/-- The ideal of translations is the span of the translation `y`. -/
theorem translationIdeal_toSubmodule :
    (translationIdeal K).toSubmodule = Submodule.span K {translation K} := by
  refine le_antisymm (fun u hu ↦ ?_) ?_
  · rw [LieSubmodule.mem_toSubmodule, mem_translationIdeal] at hu
    rw [Submodule.mem_span_singleton]
    exact ⟨u.2, by ext <;> simp [hu]⟩
  · rw [Submodule.span_le, Set.singleton_subset_iff]
    exact fst_translation

/-- The translation `y` is nonzero. -/
theorem translation_ne_zero (K : Type*) [CommRing K] [Nontrivial K] : translation K ≠ 0 := by
  intro h
  have h2 := congrArg (fun u : AffineLine K ↦ u.2) h
  simp at h2

/-- The ideal of translations is nonzero. -/
theorem translationIdeal_ne_bot (K : Type*) [CommRing K] [Nontrivial K] :
    translationIdeal K ≠ ⊥ := by
  intro h
  have hmem : translation K ∈ translationIdeal K := mem_translationIdeal.2 fst_translation
  rw [h, LieSubmodule.mem_bot] at hmem
  exact translation_ne_zero K hmem

/-- The ideal of translations is abelian. -/
theorem lie_translationIdeal_translationIdeal :
    ⁅translationIdeal K, (translationIdeal K : LieIdeal K (AffineLine K))⁆ = ⊥ := by
  rw [LieSubmodule.lie_eq_bot_iff]
  intro u hu v hv
  rw [mem_translationIdeal] at hu hv
  ext <;> simp [hu, hv]

/-- The ideal of translations is abelian, hence nilpotent as a Lie algebra, so it is contained in
the nilradical. -/
instance isNilpotentTranslationIdeal : LieRing.IsNilpotent (translationIdeal K) := by
  refine (LieIdeal.isNilpotent_iff_exists_lcs_eq_bot _).2 ⟨2, le_bot_iff.1 ?_⟩
  rw [LieIdeal.lcs_succ]
  refine (LieSubmodule.mono_lie_right _ ?_).trans lie_translationIdeal_translationIdeal.le
  rw [LieIdeal.lcs_succ, LieIdeal.lcs_zero]
  exact LieSubmodule.lie_le_left _ _

/-- **The adjoint action of any element squares to its dilation coordinate times itself.**  The
operator `LieAlgebra.ad K (AffineLine K) u` sends the dilation direction into the translation
line and scales that line by `u.1`, so composing it with itself only multiplies it by `u.1`.  In
particular it is idempotent at the dilation `x`, where `u.1 = 1`, and squares to zero at the
translation `y`, where `u.1 = 0`. -/
theorem ad_mul_ad_self (u : AffineLine K) :
    LieAlgebra.ad K (AffineLine K) u * LieAlgebra.ad K (AffineLine K) u =
      u.1 • LieAlgebra.ad K (AffineLine K) u := by
  refine LinearMap.ext fun v => ?_
  rw [Module.End.mul_apply]
  ext <;> simp

/-- **The monic relation satisfied by the adjoint action**: `T ^ n = u.1 ^ (n - 1) • T` for every
`n ≠ 0`, where `T = LieAlgebra.ad K (AffineLine K) u`.  Every positive power of `T` is therefore a
scalar multiple of it, the scalar being a power of the dilation coordinate.  Taking `n` to be a
power of the characteristic turns this into a linearized relation, which is what produces a
central `p`-polynomial in the universal enveloping algebra. -/
theorem ad_pow (u : AffineLine K) {n : ℕ} (hn : n ≠ 0) :
    LieAlgebra.ad K (AffineLine K) u ^ n = u.1 ^ (n - 1) • LieAlgebra.ad K (AffineLine K) u := by
  have key : ∀ m : ℕ, LieAlgebra.ad K (AffineLine K) u ^ (m + 1) =
      u.1 ^ m • LieAlgebra.ad K (AffineLine K) u := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [pow_succ, ih, smul_mul_assoc, ad_mul_ad_self, smul_smul, pow_succ]
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  simpa using key m

variable (K)

/-- The adjoint action of the translation `y` is nonzero: it sends the dilation `x` to `-y`. -/
theorem ad_translation_ne_zero [Nontrivial K] :
    LieAlgebra.ad K (AffineLine K) (translation K) ≠ 0 := by
  intro h
  have hx : LieAlgebra.ad K (AffineLine K) (translation K) (dilation K) = -translation K := by
    ext <;> simp
  rw [h, LinearMap.zero_apply, eq_comm, neg_eq_zero] at hx
  exact translation_ne_zero K hx

section Field

variable (K : Type*) [Field K]

/-- Every nonzero ideal contains the translation `y`. -/
theorem translation_mem_of_ne_bot {N : LieIdeal K (AffineLine K)} (h : N ≠ ⊥) :
    translation K ∈ N := by
  obtain ⟨u, hu, hu0⟩ : ∃ u ∈ N, u ≠ 0 := by
    by_contra hcon
    refine h ((LieSubmodule.eq_bot_iff N).2 fun m hm ↦ ?_)
    by_contra hm0
    exact hcon ⟨m, hm, hm0⟩
  by_cases h1 : u.1 = 0
  · -- `u` is already a nonzero multiple of `y`.
    have h2 : u.2 ≠ 0 := fun h2 ↦ hu0 (by ext <;> simp [h1, h2])
    have heq : (u.2)⁻¹ • u = translation K := by
      ext
      · simp [h1]
      · simp [inv_mul_cancel₀ h2]
    have hmem : (u.2)⁻¹ • u ∈ N := N.smul_mem _ hu
    rwa [heq] at hmem
  · -- Bracketing `u` with `y` kills its translation part and rescales `y` invertibly.
    have hlie : ⁅translation K, u⁆ = (-u.1) • translation K := by ext <;> simp
    have hmem : (-u.1)⁻¹ • ⁅translation K, u⁆ ∈ N := N.smul_mem _ (N.lie_mem hu)
    rwa [hlie, smul_smul, inv_mul_cancel₀ (neg_ne_zero.2 h1), one_smul] at hmem

/-- The translation `y` survives in every term of the lower central series of a nonzero ideal for
the adjoint action of the whole algebra, because `⁅x, y⁆ = y`. -/
theorem translation_mem_lcs {N : LieIdeal K (AffineLine K)} (h : N ≠ ⊥) (k : ℕ) :
    translation K ∈ LieSubmodule.lcs k N := by
  induction k with
  | zero => rw [LieSubmodule.lcs_zero]; exact translation_mem_of_ne_bot K h
  | succ k ih =>
    rw [LieSubmodule.lcs_succ]
    have hmem := LieSubmodule.lie_mem_lie (LieSubmodule.mem_top (dilation K)) ih
    rwa [lie_dilation_translation] at hmem

/-- The translation `y` survives in every term of the series `⁅N, ⁅N, … ⁆⁆` attached to an ideal
`N` containing an element of dilation coordinate `1`, because `⁅x, y⁆ = y`. -/
theorem translation_mem_lcs_self {N : LieIdeal K (AffineLine K)} {u : AffineLine K} (hu : u ∈ N)
    (hu1 : u.1 = 1) (k : ℕ) : translation K ∈ LieIdeal.lcs N (AffineLine K) k := by
  induction k with
  | zero => rw [LieIdeal.lcs_zero]; exact LieSubmodule.mem_top _
  | succ k ih =>
    rw [LieIdeal.lcs_succ]
    have hmem : ⁅u, translation K⁆ ∈ ⁅N, LieIdeal.lcs N (AffineLine K) k⁆ :=
      LieSubmodule.lie_mem_lie hu ih
    have hbracket : ⁅u, translation K⁆ = translation K := by ext <;> simp [hu1]
    rwa [hbracket] at hmem

/-- No nonzero ideal is acted on nilpotently by the whole algebra. -/
theorem not_isNilpotent_of_ne_bot {N : LieIdeal K (AffineLine K)} (h : N ≠ ⊥) :
    ¬ LieModule.IsNilpotent (AffineLine K) N := by
  intro hnil
  obtain ⟨k, hk⟩ := (LieModule.isNilpotent_iff K (AffineLine K) N).1 hnil
  rw [LieSubmodule.lowerCentralSeries_eq_bot_iff_lcs_eq_bot] at hk
  have hmem := translation_mem_lcs K h k
  rw [hk, LieSubmodule.mem_bot] at hmem
  exact translation_ne_zero K hmem

/-- An ideal that is nilpotent as a Lie algebra consists of translations. -/
theorem le_translationIdeal_of_isNilpotent {N : LieIdeal K (AffineLine K)}
    (h : LieRing.IsNilpotent N) : N ≤ translationIdeal K := by
  intro u hu
  rw [mem_translationIdeal]
  by_contra hu1
  obtain ⟨k, hk⟩ := (LieIdeal.isNilpotent_iff_exists_lcs_eq_bot N).1 h
  -- Rescale `u` to dilation coordinate `1`; it still lies in `N`.
  have hmem := translation_mem_lcs_self K (N.smul_mem (u.1)⁻¹ hu)
    (by simp [inv_mul_cancel₀ hu1]) k
  rw [hk, LieSubmodule.mem_bot] at hmem
  exact translation_ne_zero K hmem

/-- **The nilradical of the two-dimensional nonabelian Lie algebra is its ideal of translations**,
the span of `y` (`translationIdeal_toSubmodule`). -/
@[simp] theorem nilradical_eq_translationIdeal :
    nilradical K (AffineLine K) = translationIdeal K :=
  le_antisymm (le_translationIdeal_of_isNilpotent K inferInstance)
    (LieIdeal.le_nilradical K (AffineLine K) (translationIdeal K) inferInstance)

/-- **Mathlib's `LieAlgebra.maxNilpotentIdeal` of the two-dimensional nonabelian Lie algebra is
`⊥`**: the algebra acts on every nonzero ideal through an invertible operator. -/
@[simp] theorem maxNilpotentIdeal_eq_bot : LieAlgebra.maxNilpotentIdeal K (AffineLine K) = ⊥ := by
  by_contra h
  exact not_isNilpotent_of_ne_bot K h inferInstance

/-- **The containment `TauCeti.LieAlgebra.maxNilpotentIdeal_le_nilradical` is strict in general**:
for the two-dimensional nonabelian Lie algebra the nilradical is the ideal of translations, while
Mathlib's `LieAlgebra.maxNilpotentIdeal` is `⊥`. -/
theorem maxNilpotentIdeal_lt_nilradical :
    LieAlgebra.maxNilpotentIdeal K (AffineLine K) < nilradical K (AffineLine K) := by
  rw [maxNilpotentIdeal_eq_bot, nilradical_eq_translationIdeal, bot_lt_iff_ne_bot]
  exact translationIdeal_ne_bot K

end Field

end AffineLine

end LieAlgebra

end TauCeti
