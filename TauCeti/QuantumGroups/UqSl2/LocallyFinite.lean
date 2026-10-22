/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.QuantumGroups.UqSl2.CompleteReducibility
public import TauCeti.QuantumGroups.UqSl2.SimpleClassification
public import TauCeti.RingTheory.Finiteness.LocallyFinite
public import TauCeti.RingTheory.Semisimple.IsotypicTensor

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

The decomposition can be made canonical. Since the `L_m^ε` are pairwise non-isomorphic
finite-dimensional simple modules over `ℂ`, evaluation `v ⊗ φ ↦ φ v` identifies a locally finite
module `V` with `⨁_(m,ε) L_m^ε ⊗ Hom_U(L_m^ε, V)`, compatibly with the action of `UqSl2 q` on the
left tensor factors. The multiplicity of `L_m^ε` in `V` is thus the space `Hom_U(L_m^ε, V)`, with
no choice of decomposition.

## Main results

* `TauCeti.UqSl2.isSemisimpleModule_of_isLocallyFiniteModule`: at a generic parameter, every
  locally finite `UqSl2 q`-module is semisimple.
* `TauCeti.UqSl2.isLocallyFiniteModule_iff_exists_linearEquiv_dfinsupp_ladderModule`: at a
  generic parameter, a `UqSl2 q`-module is locally finite exactly when it is isomorphic to a
  direct sum `⨁ᵢ L_(mᵢ)^(εᵢ)` of signed ladder modules.
* `TauCeti.UqSl2.ladderModuleTensorHomEquiv`: at a generic parameter, the evaluation isomorphism
  `⨁_(m,ε) L_m^ε ⊗ Hom_U(L_m^ε, V) ≃ V` for a locally finite module `V`, natural in `V`
  (`TauCeti.UqSl2.ladderModuleTensorHomEquiv_map`), so that `End_U(V)` acts on the multiplicity
  spaces alone (`TauCeti.UqSl2.ladderModuleTensorHomEquiv_symm_apply_map`).

## References

* A. Virelizier, *Quantum groups*, Sections 2.3--2.4, for the rank-one conventions.
-/

public section

open TensorProduct

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

/-- **The evaluation isomorphism.** At a generic parameter, a locally finite `UqSl2 q`-module `V`
is the direct sum over `(m, ε)` of `L_m^ε ⊗ Hom_U(L_m^ε, V)`, by `v ⊗ φ ↦ φ v`. Here `UqSl2 q`
acts on the left tensor factors, and the multiplicity spaces `Hom_U(L_m^ε, V)` may be
infinite-dimensional. -/
noncomputable def ladderModuleTensorHomEquiv (hq : IsGenericQuantumParameter q)
    [IsLocallyFiniteModule ℂ (UqSl2 q) V] :
    (Π₀ p : ℕ × ℤˣ, LadderModule q p.1 p.2 ⊗[ℂ] (LadderModule q p.1 p.2 →ₗ[UqSl2 q] V)) ≃ₗ[UqSl2 q]
      V :=
  have := isSemisimpleModule_of_isLocallyFiniteModule hq (V := V)
  have (p : ℕ × ℤˣ) := LadderModule.isSimpleModule (m := p.1) (ε := p.2) hq
  directSumIsotypicTensorEquiv ℂ (fun p : ℕ × ℤˣ => LadderModule q p.1 p.2)
    (fun _ _ h => Prod.ext_iff.mpr ((LadderModule.nonempty_linearEquiv_iff hq).mp h))
    (fun N _ => by
      have := IsLocallyFiniteModule.finite_of_isSimpleModule (k := ℂ) N
      obtain ⟨m, ε, e⟩ := exists_linearEquiv_ladderModule hq (V := N)
      exact ⟨(m, ε), e⟩)

/-- The evaluation isomorphism sends `v ⊗ φ` in the `(m, ε)` summand to `φ v`. -/
@[simp]
theorem ladderModuleTensorHomEquiv_single_tmul (hq : IsGenericQuantumParameter q)
    [IsLocallyFiniteModule ℂ (UqSl2 q) V] (p : ℕ × ℤˣ) (v : LadderModule q p.1 p.2)
    (φ : LadderModule q p.1 p.2 →ₗ[UqSl2 q] V) :
    ladderModuleTensorHomEquiv hq (DFinsupp.single p (v ⊗ₜ φ)) = φ v := by
  simp [ladderModuleTensorHomEquiv]

section Naturality

variable {W : Type*} [AddCommGroup W] [Module ℂ W] [Module (UqSl2 q) W]
  [IsScalarTower ℂ (UqSl2 q) W]

-- Not `@[simp]`: the `simps` lemma `DFinsupp.mapRange.linearMap_apply` already rewrites the
-- left-hand side.
/-- **The evaluation isomorphism is natural.** A `UqSl2 q`-linear map `g : V → W` of locally
finite modules acts on each multiplicity space `Hom_U(L_m^ε, V)` by postcomposition, and trivially
on the `L_m^ε`. -/
theorem ladderModuleTensorHomEquiv_map (hq : IsGenericQuantumParameter q)
    [IsLocallyFiniteModule ℂ (UqSl2 q) V] [IsLocallyFiniteModule ℂ (UqSl2 q) W]
    (g : V →ₗ[UqSl2 q] W)
    (x : Π₀ p : ℕ × ℤˣ, LadderModule q p.1 p.2 ⊗[ℂ] (LadderModule q p.1 p.2 →ₗ[UqSl2 q] V)) :
    ladderModuleTensorHomEquiv hq
        (DFinsupp.mapRange.linearMap (fun p =>
          AlgebraTensorModule.map (LinearMap.id (R := UqSl2 q) (M := LadderModule q p.1 p.2))
            (LinearMap.compRight (M := LadderModule q p.1 p.2) ℂ g)) x) =
      g (ladderModuleTensorHomEquiv hq x) := by
  simp only [ladderModuleTensorHomEquiv, directSumIsotypicTensorEquiv_apply]
  exact directSumIsotypicEval_map_apply ℂ _ g x

/-- **The commutant acts on the multiplicity spaces.** Through the inverse evaluation
isomorphisms, a `UqSl2 q`-linear map `g : V → W` of locally finite modules is `1 ⊗ (g ∘ ·)` on
every summand; for `W = V` this is the action of `End_U(V)` on the `Hom_U(L_m^ε, V)`. -/
@[simp]
theorem ladderModuleTensorHomEquiv_symm_apply_map (hq : IsGenericQuantumParameter q)
    [IsLocallyFiniteModule ℂ (UqSl2 q) V] [IsLocallyFiniteModule ℂ (UqSl2 q) W]
    (g : V →ₗ[UqSl2 q] W) (v : V) :
    (ladderModuleTensorHomEquiv hq).symm (g v) =
      DFinsupp.mapRange.linearMap (fun p =>
        AlgebraTensorModule.map (LinearMap.id (R := UqSl2 q) (M := LadderModule q p.1 p.2))
          (LinearMap.compRight (M := LadderModule q p.1 p.2) ℂ g))
        ((ladderModuleTensorHomEquiv hq).symm v) := by
  apply (ladderModuleTensorHomEquiv hq).injective
  rw [LinearEquiv.apply_symm_apply, ladderModuleTensorHomEquiv_map hq g,
    LinearEquiv.apply_symm_apply]

end Naturality

end TauCeti.UqSl2
