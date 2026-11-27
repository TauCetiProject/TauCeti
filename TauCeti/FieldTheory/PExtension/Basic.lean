/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.Relrank
public import Mathlib.Order.Minimal
public import TauCeti.FieldTheory.IntermediateField.Adjoin.Finrank
public import TauCeti.FieldTheory.IntermediateField.ScalarTower
public import TauCeti.NumberTheory.PNumber
import Mathlib.Order.Zorn

/-!
# `P`-extensions

For a set `P` of natural numbers, an algebraic field extension `L / K` is a `P`-extension when
every finite subextension of `L / K` has a `P`-number as its degree (Temkin, *Tame distillation
and desingularization by `p`-alterations*, Annals of Mathematics 186 (2017), §2.1.1). The
extension need be neither normal nor separable, and the condition is not tested on a normal
closure: `ℚ(2^{1/3}) / ℚ` is a `{3}`-extension whose normal closure has degree `6`. Purely
inseparable extensions are allowed.

A field without nontrivial `P`-extensions is called `P`-closed; Temkin's tameness theorem for
valued fields is stated for such fields.

## Main definitions and results

* `TauCeti.IsPExtension P K L`: `L / K` is algebraic and every finite subextension of `L / K` has
  `P`-number degree;
* `TauCeti.isPExtension_iff_isPNumber_finrank`: a finite extension is a `P`-extension exactly when
  its degree is a `P`-number;
* `TauCeti.IsPExtension.mono`: enlarging `P` preserves `P`-extensions;
* `TauCeti.IsPExtension.of_algHom`, `TauCeti.isPExtension_congr`: subextensions of `P`-extensions
  are `P`-extensions, and the notion is invariant under `K`-algebra isomorphism;
* `TauCeti.isPExtension_tower_iff`: for a tower `M / L / K`, `M / K` is a `P`-extension exactly
  when `M / L` and `L / K` are;
* `TauCeti.isPExtension_iSup`: a directed union of `P`-subextensions is a `P`-extension;
* `TauCeti.exists_le_maximal_isPExtension`, `TauCeti.exists_maximal_isPExtension`: by Zorn's
  lemma, every `P`-subextension lies in a maximal one, so maximal `P`-subextensions exist;
* `TauCeti.eq_bot_of_maximal_isPExtension`: a maximal `P`-subextension `E` of `M / K` has no
  proper `P`-extension inside `M`.

The tower law rests on the descent of degrees of composita,
`IntermediateField.exists_finiteDimensional_finrank_adjoin_eq`: a finite subextension `L(F)` of
`M / L` has the same degree over `L` as `L₀(F)` over some finite subextension `L₀` of `L / K`.
-/

public section

open Module IntermediateField

namespace TauCeti

variable (P : Set ℕ) (K L : Type*) [Field K] [Field L] [Algebra K L]

/-- An extension `L / K` is a `P`-extension, for a set `P` of natural numbers, when it is algebraic
and every finite subextension of `L / K` has a `P`-number as its degree. The extension `L / K` need
be neither normal nor separable. -/
structure IsPExtension : Prop where
  /-- A `P`-extension is algebraic. -/
  isAlgebraic : Algebra.IsAlgebraic K L
  /-- Every finite subextension of a `P`-extension has a `P`-number as its degree. -/
  isPNumber_finrank (E : IntermediateField K L) [FiniteDimensional K E] :
    IsPNumber P (finrank K E)

variable {P K L} {M : Type*} [Field M]

/-- Enlarging `P` preserves `P`-extensions. -/
theorem IsPExtension.mono {Q : Set ℕ} (hPQ : P ⊆ Q) (h : IsPExtension P K L) :
    IsPExtension Q K L :=
  ⟨h.isAlgebraic, fun E _ ↦ (h.isPNumber_finrank E).mono hPQ⟩

/-- A finite extension is a `P`-extension exactly when its degree is a `P`-number. -/
theorem isPExtension_iff_isPNumber_finrank [FiniteDimensional K L] :
    IsPExtension P K L ↔ IsPNumber P (finrank K L) := by
  refine ⟨fun h ↦ finrank_top' (F := K) (E := L) ▸ h.isPNumber_finrank ⊤, fun h ↦
    ⟨inferInstance, fun E _ ↦ h.of_dvd (Dvd.intro _ (finrank_mul_finrank K E L))⟩⟩

variable (P K) in
/-- The trivial extension `K / K` is a `P`-extension for every `P`, even `P = ∅`. -/
@[simp]
theorem isPExtension_self : IsPExtension P K K :=
  isPExtension_iff_isPNumber_finrank.2 (by simp)

section AlgHom

variable [Algebra K M]

/-- A finite extension `E / K` has `P`-number degree if it is `K`-isomorphic to an extension `E'`
whose degree is a `P`-number once `E' / K` is known to be finite. -/
private theorem isPNumber_finrank_of_algEquiv {E E' : Type*} [Field E] [Field E'] [Algebra K E]
    [Algebra K E'] (e : E ≃ₐ[K] E') [FiniteDimensional K E]
    (h : ∀ [FiniteDimensional K E'], IsPNumber P (finrank K E')) : IsPNumber P (finrank K E) := by
  have := e.toLinearEquiv.finiteDimensional
  rw [e.toLinearEquiv.finrank_eq]
  exact h

/-- If `L` embeds into a `P`-extension `M` of `K`, then `L / K` is a `P`-extension. In particular,
every subextension of a `P`-extension is a `P`-extension. -/
theorem IsPExtension.of_algHom (h : IsPExtension P K M) (f : L →ₐ[K] M) : IsPExtension P K L where
  isAlgebraic := have := h.isAlgebraic; .of_injective f f.injective
  isPNumber_finrank E _ := isPNumber_finrank_of_algEquiv (E.equivMap f) (h.isPNumber_finrank _)

/-- Being a `P`-extension is invariant under `K`-algebra isomorphism. -/
theorem isPExtension_congr (e : L ≃ₐ[K] M) : IsPExtension P K L ↔ IsPExtension P K M :=
  ⟨fun h ↦ h.of_algHom e.symm.toAlgHom, fun h ↦ h.of_algHom e.toAlgHom⟩

/-- An intermediate field below a `P`-subextension is a `P`-extension. -/
theorem IsPExtension.of_le {E E' : IntermediateField K M} (h : IsPExtension P K E') (hle : E ≤ E') :
    IsPExtension P K E :=
  h.of_algHom (inclusion hle)

/-- An intermediate field `E` of `M / K` is a `P`-extension exactly when it is algebraic and every
finite subextension `F ≤ E` of `M / K` has `P`-number degree. -/
theorem isPExtension_intermediateField_iff {E : IntermediateField K M} :
    IsPExtension P K E ↔ Algebra.IsAlgebraic K E ∧
      ∀ F : IntermediateField K M, F ≤ E → FiniteDimensional K F → IsPNumber P (finrank K F) := by
  refine ⟨fun h ↦ ⟨h.isAlgebraic, fun F hF _ ↦ ?_⟩, fun ⟨halg, h⟩ ↦ ⟨halg, fun F _ ↦ ?_⟩⟩
  · exact isPNumber_finrank_of_algEquiv (restrictAlgEquiv hF) (h.isPNumber_finrank _)
  · exact isPNumber_finrank_of_algEquiv (liftAlgEquiv F) (h (lift F) (lift_le F) ‹_›)

end AlgHom

section Tower

variable [Algebra K M] [Algebra L M] [IsScalarTower K L M]

/-- If `M / K` is a `P`-extension, then so is `L / K` for every intermediate field `L`. -/
theorem IsPExtension.tower_bot (h : IsPExtension P K M) : IsPExtension P K L :=
  h.of_algHom (IsScalarTower.toAlgHom K L M)

/-- If `M / K` is a `P`-extension, then so is `M / L` for every intermediate field `L`. -/
theorem IsPExtension.tower_top (h : IsPExtension P K M) : IsPExtension P L M := by
  have := h.isAlgebraic
  have := h.tower_bot (L := L).isAlgebraic
  refine ⟨.tower_top (K := K) L, fun E _ ↦ ?_⟩
  -- `E = L(F)` for a finite subextension `F` of `M / K`, and `[E : L] = [L₀(F) : L₀]` for a
  -- finite subextension `L₀` of `L / K`; then `[E : L]` divides `[L₀(F) : K]`.
  obtain ⟨t, ht⟩ := essFiniteType_iff.1 (inferInstance : Algebra.EssFiniteType L E)
  let F := adjoin K (t : Set M)
  have : FiniteDimensional K F := finiteDimensional_adjoin fun x _ ↦ Algebra.IsIntegral.isIntegral x
  obtain ⟨L₀, _, heq⟩ := exists_finiteDimensional_finrank_adjoin_eq (L := L) F
  have hE : adjoin L (F : Set M) = E := by rw [adjoin_adjoin_right, ht]
  rw [hE] at heq
  let G := adjoin L₀ (F : Set M)
  have : FiniteDimensional L₀ G := Module.finite_of_finrank_pos (heq ▸ finrank_pos)
  have : FiniteDimensional K G := .trans K L₀ G
  have hG : IsPNumber P (finrank K G) :=
    isPNumber_finrank_of_algEquiv (restrictScalarsAlgEquiv K G).symm (h.isPNumber_finrank _)
  exact heq ▸ hG.of_dvd (Dvd.intro_left _ (finrank_mul_finrank K L₀ G))

/-- If `L / K` and `M / L` are `P`-extensions, then so is `M / K`. -/
theorem IsPExtension.trans (h₁ : IsPExtension P K L) (h₂ : IsPExtension P L M) :
    IsPExtension P K M := by
  have := h₁.isAlgebraic
  have := h₂.isAlgebraic
  refine ⟨.trans K L M, fun F _ ↦ ?_⟩
  -- `[F : K]` divides `[L₀(F) : K] = [L₀ : K]·[L(F) : L]` for a finite subextension `L₀`
  -- of `L / K`.
  obtain ⟨L₀, _, heq⟩ := exists_finiteDimensional_finrank_adjoin_eq (L := L) F
  have : FiniteDimensional L (adjoin L (F : Set M)) :=
    Module.rank_lt_aleph0_iff.1 ((adjoin_rank_le_of_isAlgebraic_right L F).trans_lt
      (Module.rank_lt_aleph0 K F))
  let G := adjoin L₀ (F : Set M)
  have hG : IsPNumber P (finrank K G) := by
    rw [← finrank_mul_finrank K L₀ G, heq]
    exact (h₁.isPNumber_finrank L₀).mul (h₂.isPNumber_finrank (adjoin L (F : Set M)))
  have hle : F ≤ G.restrictScalars K := fun x hx ↦ subset_adjoin L₀ _ hx
  exact hG.of_dvd (Dvd.intro _ ((finrank_bot_mul_relfinrank hle).trans
    (restrictScalarsAlgEquiv K G).toLinearEquiv.finrank_eq))

/-- **Tower law for `P`-extensions.** For a tower `M / L / K`, `M / K` is a `P`-extension exactly
when `M / L` and `L / K` are. -/
theorem isPExtension_tower_iff :
    IsPExtension P K M ↔ IsPExtension P L M ∧ IsPExtension P K L :=
  ⟨fun h ↦ ⟨h.tower_top, h.tower_bot⟩, fun h ↦ h.2.trans h.1⟩

end Tower

/-- A directed union of `P`-subextensions of `M / K` is a `P`-extension: a finite subextension of
the union lies in one member. -/
theorem isPExtension_iSup [Algebra K M] {ι : Type*} {E : ι → IntermediateField K M}
    (hE : Directed (· ≤ ·) E) (h : ∀ i, IsPExtension P K (E i)) :
    IsPExtension P K ↥(⨆ i, E i) := by
  refine isPExtension_intermediateField_iff.2 ⟨isAlgebraic_iSup fun i ↦ (h i).isAlgebraic,
    fun F hF _ ↦ ?_⟩
  obtain ⟨t, rfl⟩ := essFiniteType_iff.1 (inferInstance : Algebra.EssFiniteType K F)
  obtain ⟨s, hs⟩ := (adjoin_finset_isCompactElement t).exists_finset_of_le_iSup E hF
  cases isEmpty_or_nonempty ι with
  | inl _ =>
    rw [le_bot_iff.1 (hF.trans (iSup_le isEmptyElim)), IntermediateField.finrank_bot]
    exact isPNumber_one
  | inr _ =>
    obtain ⟨j, hj⟩ := hE.finset_le s
    exact isPExtension_intermediateField_iff.1 (h j) |>.2 _ ((hs.trans (iSup₂_le hj))) ‹_›

section Maximal

variable [Algebra K M] {E : IntermediateField K M}

/-- Every `P`-subextension of `M / K` is contained in a maximal one. -/
theorem exists_le_maximal_isPExtension (hE : IsPExtension P K E) :
    ∃ E' : IntermediateField K M, E ≤ E' ∧
      Maximal (fun E' : IntermediateField K M ↦ IsPExtension P K E') E' := by
  refine zorn_le_nonempty₀ {E' : IntermediateField K M | IsPExtension P K E'}
    (fun c hcs hc _ _ ↦ ?_) E hE
  exact ⟨⨆ E' : c, E'.val, isPExtension_iSup hc.directed fun E' ↦ hcs E'.property,
    fun E' hE' ↦ le_iSup_of_le ⟨E', hE'⟩ le_rfl⟩

variable (P K M) in
/-- Every field extension `M / K` contains a maximal `P`-subextension. -/
theorem exists_maximal_isPExtension :
    ∃ E : IntermediateField K M, Maximal (fun E : IntermediateField K M ↦ IsPExtension P K E) E :=
  (exists_le_maximal_isPExtension ((isPExtension_congr (botEquiv K M)).2
    (isPExtension_self P K))).imp fun _ h ↦ h.2

/-- A maximal `P`-subextension `E` of `M / K` has no proper `P`-extension inside `M`. -/
theorem eq_bot_of_maximal_isPExtension
    (hE : Maximal (fun E : IntermediateField K M ↦ IsPExtension P K E) E)
    {N : IntermediateField E M} (hN : IsPExtension P E N) : N = ⊥ := by
  have hNK : IsPExtension P K (N.restrictScalars K) :=
    (isPExtension_congr (restrictScalarsAlgEquiv K N)).2 (hE.prop.trans hN)
  have hle : E ≤ N.restrictScalars K := fun y hy ↦
    (mem_restrictScalars K).2 (N.algebraMap_mem ⟨y, hy⟩)
  refine eq_bot_iff.2 fun x hx ↦ mem_bot.2 ⟨⟨x, ?_⟩, rfl⟩
  exact (hE.eq_of_le hNK hle).ge ((mem_restrictScalars K).2 hx)

end Maximal

end TauCeti
