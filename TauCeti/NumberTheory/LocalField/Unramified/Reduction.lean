/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.Finite.Extension
public import TauCeti.NumberTheory.LocalField.Unramified.Existence
public import TauCeti.NumberTheory.LocalField.Unramified.Rigidity

/-!
# Finite unramified extensions and residue fields

Reduction identifies finite unramified extensions of a nonarchimedean local field `K` with
finite extensions of its residue field. The fully faithful part is
`TauCeti.IsUnramified.residueFieldHomEquiv`: reduction gives an equivalence between embeddings of
an unramified extension and embeddings of residue fields.

This file proves essential surjectivity. Given a finite extension `k/𝓀[K]`, the canonical
unramified extension of `K` whose degree is `[k : 𝓀[K]]` has residue field isomorphic to `k` over
`𝓀[K]`. Thus every finite residue-field extension occurs, while the chosen residue isomorphism
records the noncanonical data needed to compare abstract extensions.

## Main results

* `TauCeti.nonempty_residueFieldAlgEquiv_unramifiedExtension`: every finite extension of the
  residue field is the residue field of the canonical unramified extension of the same degree.
* `TauCeti.IsUnramified.nonempty_algEquiv_of_finrank_eq` and
  `TauCeti.IsUnramified.nonempty_algEquiv_iff_finrank_eq`: two unramified extensions of `K` are
  `K`-isomorphic if and only if they have the same degree over `K`.

## References

* [J.-P. Serre, *Corps Locaux*][serre1968], Chapter III, §5.
* J. Neukirch, *Algebraic Number Theory*, Chapter II, §7.
-/

public section
noncomputable section

open ValuativeRel

namespace TauCeti

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
variable (Ω : Type*) [Field Ω] [Algebra K Ω] [IsSepClosed Ω]

/-- **Every finite residue-field extension has an unramified lift.** Let `k/𝓀[K]` be finite and
put `f = [k : 𝓀[K]]`. With the canonical local-field structure on
`unramifiedExtension K Ω f`, its residue field is isomorphic to `k` over `𝓀[K]`.

Together with `IsUnramified.residueFieldHomEquiv`, this is the object-existence half of the
equivalence between finite unramified extensions of `K` and finite extensions of `𝓀[K]`. -/
theorem nonempty_residueFieldAlgEquiv_unramifiedExtension
    (k : Type*) [Field k] [Algebra 𝓀[K] k] [Module.Finite 𝓀[K] k] :
    let f := Module.finrank 𝓀[K] k
    let L := unramifiedExtension K Ω f
    letI := finiteIntermediateFieldValuativeRel K Ω L
    letI := finiteIntermediateFieldTopology K Ω L
    letI := finiteIntermediateField_isNonarchimedeanLocalField K Ω L
    letI := finiteIntermediateField_valuativeExtension K Ω L
    Nonempty (𝓀[L] ≃ₐ[𝓀[K]] k) := by
  dsimp only
  let f := Module.finrank 𝓀[K] k
  have hf : f ≠ 0 := Module.finrank_pos.ne'
  let _ : NeZero f := ⟨hf⟩
  let L := unramifiedExtension K Ω f
  let _ := finiteIntermediateFieldValuativeRel K Ω L
  let _ := finiteIntermediateFieldTopology K Ω L
  have _ := finiteIntermediateField_isNonarchimedeanLocalField K Ω L
  have _ := finiteIntermediateField_valuativeExtension K Ω L
  have _ : IsUnramified K L := isUnramified_unramifiedExtension
  have hL : Module.finrank 𝓀[K] 𝓀[L] = f := by
    rw [← inertiaDegree_def, IsUnramified.inertiaDegree_eq_finrank,
      finrank_unramifiedExtension hf]
  let ⟨p, hp⟩ := CharP.exists 𝓀[K]
  let _ : Fact p.Prime := ⟨CharP.char_is_prime 𝓀[K] p⟩
  let _ : CharP k p := charP_of_injective_algebraMap (algebraMap 𝓀[K] k).injective p
  let eL := FiniteField.algEquivExtension 𝓀[K] p f 𝓀[L] hL
  let ek := FiniteField.algEquivExtension 𝓀[K] p f k rfl
  exact ⟨eL.trans ek.symm⟩

section EquivOfFinrankEq

variable {K} {L M : Type*} [Field L] [ValuativeRel L] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L] [Algebra K L] [ValuativeExtension K L] [IsUnramified K L]
  [Field M] [ValuativeRel M] [TopologicalSpace M] [IsNonarchimedeanLocalField M] [Algebra K M]
  [ValuativeExtension K M] [IsUnramified K M]

/-- **Uniqueness of unramified extensions up to `K`-isomorphism.** Two unramified extensions of a
nonarchimedean local field `K` of the same degree are isomorphic as `K`-algebras. -/
theorem IsUnramified.nonempty_algEquiv_of_finrank_eq
    (h : Module.finrank K L = Module.finrank K M) : Nonempty (L ≃ₐ[K] M) := by
  have := finite_of_valuativeExtension K L
  have := finite_of_valuativeExtension K M
  let f := Module.finrank K L
  have : NeZero f := ⟨Module.finrank_pos.ne'⟩
  have hL : Module.finrank 𝓀[K] 𝓀[L] = f := by
    rw [← inertiaDegree_def, IsUnramified.inertiaDegree_eq_finrank]
  have hM : Module.finrank 𝓀[K] 𝓀[M] = f := by
    rw [← inertiaDegree_def, IsUnramified.inertiaDegree_eq_finrank, ← h]
  let ⟨p, _⟩ := CharP.exists 𝓀[K]
  let _ : Fact p.Prime := ⟨CharP.char_is_prime 𝓀[K] p⟩
  let eL := FiniteField.algEquivExtension 𝓀[K] p f 𝓀[L] hL
  let eM := FiniteField.algEquivExtension 𝓀[K] p f 𝓀[M] hM
  obtain ⟨e, -, -⟩ := IsUnramified.existsUnique_algEquiv_residueFieldHom_eq (eL.trans eM.symm)
  exact ⟨e⟩

variable (K L M) in
/-- **Classification of unramified extensions by degree.** Two unramified extensions of a
nonarchimedean local field `K` are `K`-isomorphic if and only if they have the same degree. -/
theorem IsUnramified.nonempty_algEquiv_iff_finrank_eq :
    Nonempty (L ≃ₐ[K] M) ↔ Module.finrank K L = Module.finrank K M :=
  ⟨fun ⟨e⟩ ↦ e.toLinearEquiv.finrank_eq, IsUnramified.nonempty_algEquiv_of_finrank_eq⟩

end EquivOfFinrankEq

end TauCeti
