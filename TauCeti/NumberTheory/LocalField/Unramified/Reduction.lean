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

## Main result

* `TauCeti.nonempty_residueFieldAlgEquiv_unramifiedExtension`: every finite extension of the
  residue field is the residue field of the canonical unramified extension of the same degree.

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
  have _ : IsUnramified K L := isUnramified_unramifiedExtension hf
  have hL : Module.finrank 𝓀[K] 𝓀[L] = f := by
    rw [← inertiaDegree_def, IsUnramified.inertiaDegree_eq_finrank,
      finrank_unramifiedExtension hf]
  let ⟨p, hp⟩ := CharP.exists 𝓀[K]
  let _ : Fact p.Prime := ⟨CharP.char_is_prime 𝓀[K] p⟩
  let _ : CharP k p := charP_of_injective_algebraMap (algebraMap 𝓀[K] k).injective p
  let eL := FiniteField.algEquivExtension 𝓀[K] p f 𝓀[L] hL
  let ek := FiniteField.algEquivExtension 𝓀[K] p f k rfl
  exact ⟨eL.trans ek.symm⟩

end TauCeti
