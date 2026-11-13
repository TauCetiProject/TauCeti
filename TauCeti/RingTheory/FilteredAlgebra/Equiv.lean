/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.RingTheory.FilteredAlgebra.AlgHom

/-!
# Completion of filtered algebra equivalences

An algebra equivalence filtered in both directions along independent monotone
cutoff moduli induces an algebra equivalence of completions. Its finite
projections use the corresponding quotient maps at the chosen source cutoffs.
The result is independent of both moduli. Exact identification of filtration
ideals is a specialization. Thus cofinal presentations of coefficient algebras
can be completed without requiring separatedness.

The construction uses `AlgFiltration.mapCompletionₐ` in both directions, its
composition law, and independence of the cutoff modulus.

Adapted from `Mei/RingTheory/FilteredAlgebra/Equiv.lean` in
[yuma-mizuno-lean/Mei](https://github.com/yuma-mizuno-lean/Mei), commit
`a79c57178cc83666fc244ca6e6eeaa722e9b8bc7` (Apache 2.0).
-/

public section

namespace TauCeti.AlgFiltration

variable {R A B : Type*} [CommRing R] [Ring A] [Algebra R A]
  [Ring B] [Algebra R B] (F : AlgFiltration A) (G : AlgFiltration B)
  (e : A ≃ₐ[R] B) (he : ∀ k, (G.ideal k).comap e.toAlgHom = F.ideal k)

section Moduli

variable (ρ σ : ℕ → ℕ) (hρ : Monotone ρ) (hσ : Monotone σ)
  (hf : ∀ k, F.ideal (ρ k + 1) ≤ (G.ideal (k + 1)).comap e.toAlgHom)
  (hi : ∀ k, G.ideal (σ k + 1) ≤ (F.ideal (k + 1)).comap e.symm.toAlgHom)

/-- Completing the two directions of an algebra equivalence gives a left inverse,
by composition and independence of the composite cutoff modulus. -/
private theorem mapCompletionₐ_equiv_leftInverse :
    Function.LeftInverse (G.mapCompletionₐ F e.symm.toAlgHom σ hσ hi)
      (F.mapCompletionₐ G e.toAlgHom ρ hρ hf) := by
  have hbound : ∀ k, F.ideal ((ρ ∘ σ) k + 1) ≤
      (F.ideal (k + 1)).comap (AlgHom.id R A) := by
    intro k a ha
    have hb := hi k (hf (σ k) ha)
    simp only [Ideal.mem_comap, AlgEquiv.toAlgHom_apply, AlgEquiv.symm_apply_apply] at hb
    simp only [Ideal.mem_comap, AlgHom.id_apply]
    exact hb
  have h := F.mapCompletionₐ_comp G e.toAlgHom ρ hρ hf F e.symm.toAlgHom σ hσ hi
  simp only [AlgEquiv.symm_comp] at h
  have hid := F.mapCompletionₐ_eq F (AlgHom.id R A) (ρ ∘ σ) (hρ.comp hσ)
    hbound id monotone_id (fun _ => by simp)
  rw [mapCompletionₐ_id] at hid
  exact fun x => (AlgHom.congr_fun (hid.symm.trans h) x).symm

/-- An algebra equivalence filtered in both directions extends to completions.
The forward component at order `k` uses source order `ρ k`, and the inverse
component uses `σ k`. The moduli may differ, so the filtrations need not agree
at equal orders; monotonicity ensures compatibility with the quotient towers. -/
def completionEquivOfModuli : F.completion ≃ₐ[R] G.completion where
  __ := F.mapCompletionₐ G e.toAlgHom ρ hρ hf
  invFun := G.mapCompletionₐ F e.symm.toAlgHom σ hσ hi
  left_inv := F.mapCompletionₐ_equiv_leftInverse G e ρ σ hρ hσ hf hi
  right_inv := G.mapCompletionₐ_equiv_leftInverse F e.symm σ ρ hσ hρ hi hf

/-- The underlying algebra homomorphism is the completion map with forward cutoff `ρ`. -/
theorem toAlgHom_completionEquivOfModuli :
    (F.completionEquivOfModuli G e ρ σ hρ hσ hf hi).toAlgHom =
      F.mapCompletionₐ G e.toAlgHom ρ hρ hf := (rfl)

/-- Finite projections use the forward quotient map at the prescribed source cutoff. -/
@[simp]
theorem projection_completionEquivOfModuli (k : ℕ) (x : F.completion) :
    G.projection k (F.completionEquivOfModuli G e ρ σ hρ hσ hf hi x) =
      Ideal.quotientMapₐ (G.ideal (k + 1)) e.toAlgHom (hf k) (F.projection (ρ k) x) :=
  F.projection_mapCompletionₐ G e.toAlgHom ρ hρ hf k x

/-- The completed equivalence extends the original map on canonical elements. -/
@[simp]
theorem completionEquivOfModuli_toCompletion (a : A) :
    F.completionEquivOfModuli G e ρ σ hρ hσ hf hi (F.toCompletion a) =
      G.toCompletion (e a) :=
  F.mapCompletionₐ_toCompletion G e.toAlgHom ρ hρ hf a

/-- Inversion swaps the two cutoff moduli and the two filtration bounds. -/
theorem completionEquivOfModuli_symm :
    (F.completionEquivOfModuli G e ρ σ hρ hσ hf hi).symm =
      G.completionEquivOfModuli F e.symm σ ρ hσ hρ hi hf := by
  apply AlgEquiv.ext
  intro y
  -- The specified invFun on the left and forward map on the right are both
  -- exactly G.mapCompletionₐ F e.symm.toAlgHom σ hσ hi by construction.
  rfl

/-- Finite projections of the inverse use the inverse modulus `σ`. -/
@[simp]
theorem projection_completionEquivOfModuli_symm (k : ℕ) (y : G.completion) :
    F.projection k ((F.completionEquivOfModuli G e ρ σ hρ hσ hf hi).symm y) =
      Ideal.quotientMapₐ (F.ideal (k + 1)) e.symm.toAlgHom (hi k)
        (G.projection (σ k) y) :=
  G.projection_mapCompletionₐ F e.symm.toAlgHom σ hσ hi k y

/-- The inverse extension agrees with the original inverse on canonical elements. -/
@[simp]
theorem completionEquivOfModuli_symm_toCompletion (b : B) :
    (F.completionEquivOfModuli G e ρ σ hρ hσ hf hi).symm (G.toCompletion b) =
      F.toCompletion (e.symm b) :=
  G.mapCompletionₐ_toCompletion F e.symm.toAlgHom σ hσ hi b

/-- The completed equivalence is independent of both valid cutoff moduli. -/
theorem completionEquivOfModuli_eq (ρ' σ' : ℕ → ℕ) (hρ' : Monotone ρ')
    (hσ' : Monotone σ')
    (hf' : ∀ k, F.ideal (ρ' k + 1) ≤ (G.ideal (k + 1)).comap e.toAlgHom)
    (hi' : ∀ k, G.ideal (σ' k + 1) ≤ (F.ideal (k + 1)).comap e.symm.toAlgHom) :
    F.completionEquivOfModuli G e ρ σ hρ hσ hf hi =
      F.completionEquivOfModuli G e ρ' σ' hρ' hσ' hf' hi' := by
  apply AlgEquiv.ext
  intro x
  exact AlgHom.congr_fun (F.mapCompletionₐ_eq G e.toAlgHom ρ hρ hf ρ' hρ' hf') x

/-- Completing an identity equivalence gives the identity, for any valid cutoff moduli. -/
@[simp]
theorem completionEquivOfModuli_refl
    (hf₀ : ∀ k, F.ideal (ρ k + 1) ≤ (F.ideal (k + 1)).comap
      (AlgEquiv.refl : A ≃ₐ[R] A).toAlgHom)
    (hi₀ : ∀ k, F.ideal (σ k + 1) ≤ (F.ideal (k + 1)).comap
      (AlgEquiv.refl : A ≃ₐ[R] A).symm.toAlgHom) :
    F.completionEquivOfModuli F (AlgEquiv.refl : A ≃ₐ[R] A) ρ σ hρ hσ hf₀ hi₀ =
      AlgEquiv.refl := by
  apply AlgEquiv.ext
  intro x
  exact AlgHom.congr_fun ((F.mapCompletionₐ_eq F (AlgHom.id R A) ρ hρ hf₀
    id monotone_id (fun _ => by simp)).trans F.mapCompletionₐ_id) x

/-- Completing successive equivalences composes the forward cutoffs as `ρ ∘ ρ'`
and the inverse cutoffs in the reverse order `σ' ∘ σ`. -/
theorem completionEquivOfModuli_trans {C : Type*} [Ring C] [Algebra R C]
    (H : AlgFiltration C) (e' : B ≃ₐ[R] C) (ρ' σ' : ℕ → ℕ)
    (hρ' : Monotone ρ') (hσ' : Monotone σ')
    (hf' : ∀ k, G.ideal (ρ' k + 1) ≤ (H.ideal (k + 1)).comap e'.toAlgHom)
    (hi' : ∀ k, H.ideal (σ' k + 1) ≤ (G.ideal (k + 1)).comap e'.symm.toAlgHom) :
    F.completionEquivOfModuli H (e.trans e') (ρ ∘ ρ') (σ' ∘ σ)
      (hρ.comp hρ') (hσ'.comp hσ)
      (fun k _ ha => hf' k (hf (ρ' k) ha))
      (fun k _ ha => hi k (hi' (σ k) ha)) =
      (F.completionEquivOfModuli G e ρ σ hρ hσ hf hi).trans
        (G.completionEquivOfModuli H e' ρ' σ' hρ' hσ' hf' hi') := by
  apply AlgEquiv.ext
  intro x
  exact AlgHom.congr_fun (F.mapCompletionₐ_comp G e.toAlgHom ρ hρ hf
    H e'.toAlgHom ρ' hρ' hf') x

end Moduli

include he

/-- Exact identification of filtration ideals also holds for the inverse map. -/
theorem ideal_comap_symm (k : ℕ) :
    (F.ideal k).comap e.symm.toAlgHom = G.ideal k := by
  ext y
  rw [Ideal.mem_comap, ← he k]
  simp

/-- A filtration-preserving algebra equivalence extends to completed algebras. -/
def completionEquiv : F.completion ≃ₐ[R] G.completion :=
  F.completionEquivOfModuli G e id id monotone_id monotone_id
    (fun k => (he (k + 1)).ge)
    (fun k => (F.ideal_comap_symm G e he (k + 1)).ge)

/-- The underlying algebra homomorphism uses the identity cutoff modulus. -/
theorem toAlgHom_completionEquiv :
    (F.completionEquiv G e he).toAlgHom =
      F.mapCompletionₐ G e.toAlgHom id monotone_id (fun k => (he (k + 1)).ge) :=
  F.toAlgHom_completionEquivOfModuli G e id id monotone_id monotone_id
    (fun k => (he (k + 1)).ge) (fun k => (F.ideal_comap_symm G e he (k + 1)).ge)

/-- Finite projections of the completed equivalence are induced quotient maps. -/
@[simp]
theorem projection_completionEquiv (k : ℕ) (x : F.completion) :
    G.projection k (F.completionEquiv G e he x) =
      Ideal.quotientMapₐ (G.ideal (k + 1)) e.toAlgHom (by simp only [he, le_refl])
        (F.projection k x) :=
  F.projection_mapCompletionₐ G e.toAlgHom id monotone_id (fun k => (he (k + 1)).ge) k x

/-- The extension agrees with the original equivalence on canonical elements. -/
@[simp]
theorem completionEquiv_toCompletion (a : A) :
    F.completionEquiv G e he (F.toCompletion a) = G.toCompletion (e a) :=
  F.mapCompletionₐ_toCompletion G e.toAlgHom id monotone_id (fun k => (he (k + 1)).ge) a

/-- Inverting the completed equivalence completes the inverse equivalence. -/
theorem completionEquiv_symm :
    (F.completionEquiv G e he).symm =
      G.completionEquiv F e.symm (F.ideal_comap_symm G e he) := by
  unfold completionEquiv
  exact F.completionEquivOfModuli_symm G e id id monotone_id monotone_id
    (fun k => (he (k + 1)).ge) (fun k => (F.ideal_comap_symm G e he (k + 1)).ge)

/-- Finite projections of the inverse use the inverse quotient map. -/
@[simp]
theorem projection_completionEquiv_symm (k : ℕ) (y : G.completion) :
    F.projection k ((F.completionEquiv G e he).symm y) =
      Ideal.quotientMapₐ (F.ideal (k + 1)) e.symm.toAlgHom
        (by simp only [F.ideal_comap_symm G e he, le_refl]) (G.projection k y) := by
  rw [completionEquiv_symm, projection_completionEquiv]

/-- The inverse extension agrees with the inverse on canonical elements. -/
@[simp]
theorem completionEquiv_symm_toCompletion (b : B) :
    (F.completionEquiv G e he).symm (G.toCompletion b) = F.toCompletion (e.symm b) := by
  rw [completionEquiv_symm, completionEquiv_toCompletion]

/-- A completed algebra equivalence preserves and reflects every induced filtration ideal. -/
@[simp]
theorem completionEquiv_mem_completionIdeal_iff (k : ℕ) (x : F.completion) :
    F.completionEquiv G e he x ∈ G.completionIdeal k ↔ x ∈ F.completionIdeal k := by
  cases k with
  | zero => simp
  | succ k =>
    simp only [completionIdeal_succ, RingHom.mem_ker, projection_completionEquiv]
    exact map_eq_zero_iff
      (Ideal.quotientMapₐ (G.ideal (k + 1)) e.toAlgHom (by rw [he]))
      (Ideal.quotientMap_injective' (H := (he (k + 1)).ge) (he (k + 1)).le)

/-- The inverse completed equivalence also preserves and reflects filtration order. -/
@[simp]
theorem completionEquiv_symm_mem_completionIdeal_iff (k : ℕ) (y : G.completion) :
    (F.completionEquiv G e he).symm y ∈ F.completionIdeal k ↔
      y ∈ G.completionIdeal k := by
  rw [completionEquiv_symm, completionEquiv_mem_completionIdeal_iff]

/-- The completed equivalence identifies the completed filtration ideals by comap. -/
@[simp]
theorem completionIdeal_comap_completionEquiv (k : ℕ) :
    (G.completionIdeal k).comap (F.completionEquiv G e he).toAlgHom =
      F.completionIdeal k := by
  ext x
  simp only [Ideal.mem_comap, AlgEquiv.coe_toAlgHom, completionEquiv_mem_completionIdeal_iff]

end TauCeti.AlgFiltration
