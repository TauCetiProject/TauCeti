/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.QuantumGroups.UqSl2.CompleteReducibility
public import TauCeti.QuantumGroups.UqSl2.SimpleClassification
public import TauCeti.RingTheory.Finiteness.LocallyFinite

/-!
# Locally finite `U_q(sl₂)`-modules

A `UqSl2 q`-module is locally finite when each vector generates a finite-dimensional submodule;
no finiteness of the whole module is assumed. At a generic parameter `q` (nonzero and not a root
of unity), the locally finite modules are exactly the algebraic direct sums of signed ladder
modules `L_m^ε`, with arbitrary, possibly infinite, index sets.

Each cyclic submodule of a locally finite module is finite-dimensional, hence semisimple by
complete reducibility of finite-dimensional modules, and a module spanned by semisimple
submodules is semisimple. A semisimple module is a direct sum of simple submodules; in a locally
finite module these are cyclic, hence finite-dimensional, hence each isomorphic to one `L_m^ε` by
the classification of finite-dimensional simple modules. Conversely, a direct sum of
finite-dimensional modules is locally finite.

## Main results

* `TauCeti.UqSl2.isSemisimpleModule_of_isLocallyFiniteModule`: at a generic parameter, every
  locally finite `UqSl2 q`-module is semisimple.
* `TauCeti.UqSl2.isLocallyFiniteModule_iff_exists_linearEquiv_dfinsupp_ladderModule`: at a
  generic parameter, a `UqSl2 q`-module is locally finite exactly when it is isomorphic to a
  direct sum `⨁ᵢ L_(mᵢ)^(εᵢ)` of signed ladder modules.

## References

* A. Virelizier, *Quantum groups*, Sections 2.3--2.4, for the rank-one conventions.
-/

public section

namespace TauCeti.UqSl2

universe u

variable {q : ℂ} {V : Type u} [AddCommGroup V] [Module ℂ V]
  [Module (UqSl2 q) V] [IsScalarTower ℂ (UqSl2 q) V]

/-- At a generic parameter, every locally finite `UqSl2 q`-module is semisimple. -/
theorem isSemisimpleModule_of_isLocallyFiniteModule (hq : IsGenericQuantumParameter q)
    [IsLocallyFiniteModule ℂ (UqSl2 q) V] : IsSemisimpleModule (UqSl2 q) V :=
  IsLocallyFiniteModule.isSemisimpleModule (k := ℂ) fun _ _ =>
    isSemisimpleModule_of_finiteDimensional hq

/-- At a generic parameter, `E` acts locally nilpotently on a locally finite module. -/
theorem exists_e_pow_smul_eq_zero_of_isLocallyFiniteModule (hq : IsGenericQuantumParameter q)
    [IsLocallyFiniteModule ℂ (UqSl2 q) V] (v : V) : ∃ n : ℕ, e q ^ n • v = 0 := by
  have := IsLocallyFiniteModule.finite_span_singleton (k := ℂ) (A := UqSl2 q) v
  obtain ⟨n, hn⟩ := exists_e_pow_smul_eq_zero hq
    (⟨v, Submodule.mem_span_singleton_self v⟩ : Submodule.span (UqSl2 q) {v})
  exact ⟨n, congrArg Subtype.val hn⟩

/-- At a generic parameter, `F` acts locally nilpotently on a locally finite module. -/
theorem exists_f_pow_smul_eq_zero_of_isLocallyFiniteModule (hq : IsGenericQuantumParameter q)
    [IsLocallyFiniteModule ℂ (UqSl2 q) V] (v : V) : ∃ n : ℕ, f q ^ n • v = 0 := by
  have := IsLocallyFiniteModule.finite_span_singleton (k := ℂ) (A := UqSl2 q) v
  obtain ⟨n, hn⟩ := exists_f_pow_smul_eq_zero hq
    (⟨v, Submodule.mem_span_singleton_self v⟩ : Submodule.span (UqSl2 q) {v})
  exact ⟨n, congrArg Subtype.val hn⟩

variable [Fact (q ≠ 0)]

/-- At a generic parameter, every locally finite `UqSl2 q`-module is isomorphic to a direct sum of
signed ladder modules `L_m^ε`. -/
theorem exists_linearEquiv_dfinsupp_ladderModule (hq : IsGenericQuantumParameter q)
    [IsLocallyFiniteModule ℂ (UqSl2 q) V] :
    ∃ (ι : Type u) (m : ι → ℕ) (ε : ι → ℤˣ),
      Nonempty (V ≃ₗ[UqSl2 q] Π₀ i, LadderModule q (m i) (ε i)) := by
  have := isSemisimpleModule_of_isLocallyFiniteModule hq (V := V)
  obtain ⟨s, e, -, hs⟩ := IsSemisimpleModule.exists_linearEquiv_dfinsupp (UqSl2 q) V
  -- Each simple summand is finite-dimensional, hence isomorphic to a signed ladder module.
  have h (N : s) : ∃ (m : ℕ) (ε : ℤˣ), Nonempty (LadderModule q m ε ≃ₗ[UqSl2 q] N.1) := by
    have := hs N
    have := IsLocallyFiniteModule.finite_of_isSimpleModule (k := ℂ) N.1
    exact exists_linearEquiv_ladderModule hq
  choose m ε e' using h
  exact ⟨s, m, ε, ⟨e.trans (DFinsupp.mapRange.linearEquiv fun N => (e' N).some.symm)⟩⟩

/-- At a generic parameter, a `UqSl2 q`-module is locally finite exactly when it is isomorphic to a
direct sum of signed ladder modules `L_m^ε`. -/
theorem isLocallyFiniteModule_iff_exists_linearEquiv_dfinsupp_ladderModule
    (hq : IsGenericQuantumParameter q) :
    IsLocallyFiniteModule ℂ (UqSl2 q) V ↔ ∃ (ι : Type u) (m : ι → ℕ) (ε : ι → ℤˣ),
      Nonempty (V ≃ₗ[UqSl2 q] Π₀ i, LadderModule q (m i) (ε i)) :=
  ⟨fun _ => exists_linearEquiv_dfinsupp_ladderModule hq,
    fun ⟨_, _, _, ⟨e⟩⟩ => .of_linearEquiv e⟩

end TauCeti.UqSl2
