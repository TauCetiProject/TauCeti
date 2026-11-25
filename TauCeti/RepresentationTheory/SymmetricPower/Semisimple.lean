/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.RepresentationTheory.Irreducible
public import Mathlib.RepresentationTheory.Semisimple
public import TauCeti.LinearAlgebra.SymmetricPower.Basis
public import TauCeti.RepresentationTheory.Irreducible
public import TauCeti.RepresentationTheory.Subrepresentation
public import TauCeti.RepresentationTheory.SymmetricPower

/-!
# Symmetric powers of semisimple representations of commutative monoids

A representation spanned by common eigenvectors of all the operators `ρ g` is semisimple: it is
the sum of the lines through those eigenvectors, which are irreducible subrepresentations
(`Representation.isSemisimpleRepresentation_of_span_eq_top`). Conversely, a finite-dimensional
semisimple representation of a commutative monoid over an algebraically closed field has a basis
of common eigenvectors (`Representation.exists_basis_forall_apply_eq_smul`), because its
irreducible subrepresentations are lines
(`Representation.IsIrreducible.finrank_eq_one_of_isMulCommutative`).

A basis of common eigenvectors of `V` induces a basis of the symmetric power `Sym^m V` whose
vectors are again common eigenvectors (`Module.Basis.map_symmetricPower_of_apply`). Hence the
symmetric powers of a finite-dimensional semisimple representation of a commutative monoid over
an algebraically closed field are semisimple
(`Representation.isSemisimpleRepresentation_symmetricPower`), of dimension
`binom(n + m - 1, m)` for `n = dim V`. This applies to the Weil group `W_ℂ = ℂˣ`
(`Representation.isSemisimpleRepresentation_symmetricPower_units_complex`).

## Main results

* `Representation.isSemisimpleRepresentation_of_span_eq_top`: a representation spanned by common
  eigenvectors is semisimple.
* `Representation.exists_basis_forall_apply_eq_smul`: a finite-dimensional semisimple
  representation of a commutative monoid over an algebraically closed field has a basis of
  common eigenvectors.
* `Representation.isSemisimpleRepresentation_symmetricPower`: its symmetric powers are
  semisimple.
* `Representation.isSemisimpleRepresentation_symmetricPower_units_complex`: for a
  finite-dimensional semisimple complex representation of `ℂˣ`, `Sym^m` is semisimple of dimension
  `binom(n + m - 1, m)`.
-/

public section

open scoped MonoidAlgebra TensorProduct

namespace Representation

open Module

variable {k : Type} {G V : Type*} [Field k] [Monoid G] [AddCommGroup V] [Module k V]
  (ρ : Representation k G V)

/-! ### Lines through common eigenvectors -/

/-- The line through a common eigenvector `v` of the operators `ρ g`, as a subrepresentation. -/
def lineSubrepresentation (v : V) (hv : ∀ g, ∃ c : k, ρ g v = c • v) : Subrepresentation ρ where
  toSubmodule := k ∙ v
  apply_mem_toSubmodule g w hw := by
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hw
    obtain ⟨c, hc⟩ := hv g
    rw [map_smul, hc, smul_smul]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self v)

theorem mem_lineSubrepresentation {v : V} {hv : ∀ g, ∃ c : k, ρ g v = c • v} {w : V} :
    w ∈ lineSubrepresentation ρ v hv ↔ w ∈ k ∙ v :=
  Iff.rfl

/-- The line through a nonzero common eigenvector is a minimal nonzero subrepresentation. -/
theorem isAtom_lineSubrepresentation {v : V} (hv : ∀ g, ∃ c : k, ρ g v = c • v) (hv0 : v ≠ 0) :
    IsAtom (lineSubrepresentation ρ v hv) := by
  have hline : IsAtom (k ∙ v) :=
    Submodule.isAtom_iff_finrank_eq_one.2 (finrank_span_singleton hv0)
  refine ⟨fun h ↦ hline.1 ?_, fun τ hτ ↦ ?_⟩
  · refine eq_bot_iff.2 fun w hw ↦ ?_
    have : w ∈ (⊥ : Subrepresentation ρ) := h ▸ (mem_lineSubrepresentation ρ).2 hw
    exact this
  · have hlt : τ.toSubmodule < k ∙ v := SetLike.coe_ssubset_coe.1 (SetLike.coe_ssubset_coe.2 hτ)
    exact Subrepresentation.toSubmodule_injective (hline.2 _ hlt)

/-- **A representation spanned by common eigenvectors is semisimple**: it is the sum of the lines
through them, which are irreducible subrepresentations. -/
theorem isSemisimpleRepresentation_of_span_eq_top {S : Set V}
    (hS : ∀ v ∈ S, ∀ g, ∃ c : k, ρ g v = c • v) (hspan : Submodule.span k S = ⊤) :
    ρ.IsSemisimpleRepresentation := by
  rw [isSemisimpleRepresentation_iff_isSemisimpleModule_asModule]
  refine IsSemisimpleModule.of_sSup_simples_eq_top ?_
  set M := sSup {m : Submodule k[G] ρ.asModule | IsSimpleModule k[G] m}
  have hle : Submodule.span k S ≤ (Subrepresentation.ofSubmodule' M).toSubmodule := by
    rw [Submodule.span_le]
    intro v hv
    by_cases hv0 : v = 0
    · rw [hv0]
      exact zero_mem _
    have hsimple : IsSimpleModule k[G] (lineSubrepresentation ρ v (hS v hv)).asSubmodule :=
      Subrepresentation.isSimpleModule_asSubmodule_iff.2
        (isAtom_lineSubrepresentation ρ (hS v hv) hv0)
    have h1 : v ∈ lineSubrepresentation ρ v (hS v hv) :=
      (mem_lineSubrepresentation ρ).2 (Submodule.mem_span_singleton_self v)
    have h2 : lineSubrepresentation ρ v (hS v hv) ≤ Subrepresentation.ofSubmodule' M :=
      Subrepresentation.subrepresentationSubmoduleOrderIso.le_iff_le.1
        (le_sSup (s := {m : Submodule k[G] ρ.asModule | IsSimpleModule k[G] m}) hsimple)
    exact h2 h1
  have htop : Subrepresentation.ofSubmodule' M = ⊤ := by
    refine Subrepresentation.toSubmodule_injective (eq_top_iff.2 ?_)
    rw [← hspan]
    exact hle
  exact (map_eq_top_iff Subrepresentation.subrepresentationSubmoduleOrderIso).2 htop

/-! ### Eigenbases of semisimple representations of commutative monoids -/

/-- Every vector of a one-dimensional subrepresentation is a common eigenvector. -/
theorem exists_apply_eq_smul_of_finrank_eq_one {σ : Subrepresentation ρ}
    (hσ : finrank k σ.toSubmodule = 1) {w : V} (hw : w ∈ σ) (g : G) :
    ∃ c : k, ρ g w = c • w := by
  obtain ⟨u, -, hu⟩ := finrank_eq_one_iff'.1 hσ
  obtain ⟨c, hc⟩ := hu ⟨ρ g w, σ.apply_mem_toSubmodule g hw⟩
  obtain ⟨a, ha⟩ := hu ⟨w, hw⟩
  have hw' : w = a • (u : V) := (congrArg Subtype.val ha).symm
  have hgw : ρ g w = c • (u : V) := (congrArg Subtype.val hc).symm
  by_cases ha0 : a = 0
  · exact ⟨0, by rw [zero_smul, hw', ha0, zero_smul, map_zero]⟩
  · exact ⟨c / a, by rw [hgw, hw', smul_smul, div_mul_cancel₀ c ha0]⟩

variable [IsMulCommutative G] [IsAlgClosed k] [FiniteDimensional k V]

/-- **A semisimple representation of a commutative monoid is spanned by common eigenvectors**,
over an algebraically closed field and in finite dimension: its irreducible subrepresentations are
lines. -/
theorem span_setOf_forall_apply_eq_smul [ρ.IsSemisimpleRepresentation] :
    Submodule.span k {v : V | ∀ g, ∃ c : k, ρ g v = c • v} = ⊤ := by
  set T := Submodule.span k {v : V | ∀ g, ∃ c : k, ρ g v = c • v}
  -- The span of the common eigenvectors is stable: `ρ g` maps eigenvectors to eigenvectors.
  have hstable : ∀ (g : G) ⦃w : V⦄, w ∈ T → ρ g w ∈ T := by
    intro g w hw
    induction hw using Submodule.span_induction with
    | mem v hv =>
      refine Submodule.subset_span fun h ↦ ?_
      obtain ⟨c, hc⟩ := hv h
      refine ⟨c, ?_⟩
      rw [← mul_apply_eq_comp, ← map_mul, IsMulCommutative.is_comm.comm h g, map_mul,
        mul_apply_eq_comp, hc, map_smul]
    | zero => rw [map_zero]; exact zero_mem _
    | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
    | smul c a _ ha => rw [map_smul]; exact Submodule.smul_mem _ c ha
  let τ : Subrepresentation ρ := ⟨T, hstable⟩
  -- Every irreducible subrepresentation is a line, so it lies in `τ`.
  have hatoms : ∀ σ : Subrepresentation ρ, IsAtom σ → σ ≤ τ := by
    intro σ hσ w hw
    have := isIrreducible_toRepresentation_of_isAtom hσ
    have hfin : finrank k σ.toSubmodule = 1 :=
      IsIrreducible.finrank_eq_one_of_isMulCommutative σ.toRepresentation
    exact Submodule.subset_span fun g ↦ exists_apply_eq_smul_of_finrank_eq_one ρ hfin hw g
  have : IsSemisimpleModule k[G] ρ.asModule :=
    (isSemisimpleRepresentation_iff_isSemisimpleModule_asModule ρ).1 ‹_›
  have hτ : τ.asSubmodule = ⊤ := by
    rw [eq_top_iff, ← IsSemisimpleModule.sSup_simples_eq_top k[G] ρ.asModule]
    refine sSup_le fun m hm ↦ ?_
    have hatom : IsAtom (Subrepresentation.ofSubmodule' m) := by
      rw [← Subrepresentation.isSimpleModule_asSubmodule_iff]
      exact hm
    exact Subrepresentation.subrepresentationSubmoduleOrderIso.le_iff_le.2 (hatoms _ hatom)
  have : τ = ⊤ :=
    (map_eq_top_iff Subrepresentation.subrepresentationSubmoduleOrderIso).1 hτ
  exact congrArg Subrepresentation.toSubmodule this

/-- **An eigenbasis of a semisimple representation of a commutative monoid**, over an
algebraically closed field and in finite dimension: a basis of common eigenvectors of the
operators `ρ g`. -/
theorem exists_basis_forall_apply_eq_smul [ρ.IsSemisimpleRepresentation] :
    ∃ (s : Set V) (b : Basis s k V), ∀ i g, ∃ c : k, ρ g (b i) = c • b i := by
  obtain ⟨s, hs, hspan, hli⟩ := exists_linearIndependent k {v : V | ∀ g, ∃ c : k, ρ g v = c • v}
  refine ⟨s, Basis.mk hli ?_, fun i g ↦ ?_⟩
  · rw [Subtype.range_coe, hspan, span_setOf_forall_apply_eq_smul]
  · rw [Basis.mk_apply]
    exact hs i.property g

/-- **Symmetric powers of semisimple representations of commutative monoids are semisimple**,
over an algebraically closed field and in finite dimension: an eigenbasis of `V` induces an
eigenbasis of `Sym^m V`. -/
theorem isSemisimpleRepresentation_symmetricPower [ρ.IsSemisimpleRepresentation] (m : ℕ) :
    IsSemisimpleRepresentation (k := k) (G := G) (V := Sym[k]^m V) (ρ.symmetricPower m) := by
  obtain ⟨s, b, hb⟩ := exists_basis_forall_apply_eq_smul ρ
  refine isSemisimpleRepresentation_of_span_eq_top (ρ.symmetricPower m)
    (S := Set.range (b.symmetricPower m)) ?_ (b.symmetricPower m).span_eq
  rintro _ ⟨t, rfl⟩ g
  choose c hc using fun i ↦ hb i g
  exact ⟨_, (symmetricPower_apply ρ m g).symm ▸
    Basis.map_symmetricPower_of_apply b (ρ g) c hc t⟩

end Representation

namespace Representation

/-- **Symmetric powers of semisimple representations of `W_ℂ = ℂˣ`**: for a finite-dimensional
semisimple complex representation `ρ` of `ℂˣ` of dimension `n`, the symmetric power `Sym^m ρ` is
semisimple of dimension `binom(n + m - 1, m)`. -/
theorem isSemisimpleRepresentation_symmetricPower_units_complex {V : Type*} [AddCommGroup V]
    [Module ℂ V] [FiniteDimensional ℂ V] (ρ : Representation ℂ ℂˣ V)
    [ρ.IsSemisimpleRepresentation] (m : ℕ) :
    IsSemisimpleRepresentation (k := ℂ) (G := ℂˣ) (V := Sym[ℂ]^m V) (ρ.symmetricPower m) ∧
      Module.finrank ℂ (Sym[ℂ]^m V) = (Module.finrank ℂ V + m - 1).choose m := by
  refine ⟨isSemisimpleRepresentation_symmetricPower ρ m, ?_⟩
  rw [SymmetricPower.finrank_eq, Nat.multichoose_eq]

end Representation
