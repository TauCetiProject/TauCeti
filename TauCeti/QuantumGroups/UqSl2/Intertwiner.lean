/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.QuantumGroups.UqSl2.LocallyFinite

/-!
# Intertwiners of `U_q(sl₂)`-modules

At a generic parameter `q` (nonzero and not a root of unity) a locally finite `UqSl2 q`-module `V`
is the direct sum `⨁_(m,ε) L_m^ε ⊗ Hom_U(L_m^ε, V)` of signed ladder modules tensored with their
multiplicity spaces (`TauCeti.UqSl2.ladderModuleTensorHomEquiv`). This file computes the
intertwiners out of such a module from that decomposition.

A `UqSl2 q`-linear map `g : V → W` into an arbitrary module `W` is the same thing as a family of
linear maps `Hom_U(L_m^ε, V) → Hom_U(L_m^ε, W)` of multiplicity spaces, by `g ↦ (φ ↦ g ∘ φ)`. Taking
`W = V`, the commutant `End_U(V)` is the product over `(m, ε)` of the full endomorphism algebras of
the multiplicity spaces. With multiplicities `a_(m,ε)(V) = dim Hom_U(L_m^ε, V)`, this gives the
two classical formulas, for finite-dimensional `V` and `W` and more generally whenever the
multiplicities involved are finite,

`dim Hom_U(V, W) = ∑_(m,ε) a_(m,ε)(V) · a_(m,ε)(W)` and `End_U(V) ≃ ∏_(m,ε) M_(a_(m,ε)(V))(ℂ)`.

Only finitely many `L_m^ε` occur in a finite-dimensional module, so for finite-dimensional `V` the
sum is finite and all but finitely many matrix factors are the zero ring of `0 × 0` matrices. All of
this specializes the corresponding statements for semisimple modules in
`TauCeti.RingTheory.Semisimple.IsotypicTensor`.

## Main definitions

* `TauCeti.UqSl2.ladderModuleHomEquiv`: at a generic parameter, the isomorphism
  `Hom_U(V, W) ≃ ∏_(m,ε) Hom_ℂ(Hom_U(L_m^ε, V), Hom_U(L_m^ε, W))` for locally finite `V`.
* `TauCeti.UqSl2.ladderModuleEndAlgEquiv`: at a generic parameter, the algebra isomorphism
  `End_U(V) ≃ ∏_(m,ε) End_ℂ(Hom_U(L_m^ε, V))` for locally finite `V`.

## Main results

* `TauCeti.UqSl2.finite_support_finrank_linearMap_ladderModule`: at a generic parameter, only
  finitely many `L_m^ε` occur in a finite-dimensional module.
* `TauCeti.UqSl2.finrank_linearMap_eq_finsum`: at a generic parameter,
  `dim Hom_U(V, W) = ∑_(m,ε) dim Hom_U(L_m^ε, V) · dim Hom_U(L_m^ε, W)` for finite-dimensional
  `V` and any `W` with finite multiplicities, such as a finite-dimensional one.
* `TauCeti.UqSl2.nonempty_end_algEquiv_pi_matrix`: at a generic parameter, `End_U(V)` is a
  product of full matrix algebras `M_(a_(m,ε))(ℂ)` of the sizes of the multiplicities of a
  locally finite module `V` with finite multiplicities.

## References

* J. C. Jantzen, *Lectures on Quantum Groups*, Chapter 2, for the finite-dimensional
  representations of `U_q(sl₂)`.
* J.-P. Serre, *Linear Representations of Finite Groups*, §2.6, for the canonical decomposition
  and its multiplicity spaces.
-/

public section

open Module

namespace TauCeti.UqSl2

variable {q : ℂ} [Fact (q ≠ 0)] {V W : Type*} [AddCommGroup V] [Module ℂ V] [Module (UqSl2 q) V]
  [IsScalarTower ℂ (UqSl2 q) V] [AddCommGroup W] [Module ℂ W] [Module (UqSl2 q) W]
  [IsScalarTower ℂ (UqSl2 q) W]

/-- At a generic parameter, the signed ladder modules `L_m^ε` are pairwise non-isomorphic. -/
private theorem ladderModule_eq_of_nonempty_linearEquiv (hq : IsGenericQuantumParameter q)
    (p p' : ℕ × ℤˣ) (h : Nonempty (LadderModule q p.1 p.2 ≃ₗ[UqSl2 q] LadderModule q p'.1 p'.2)) :
    p = p' :=
  Prod.ext_iff.mpr ((LadderModule.nonempty_linearEquiv_iff hq).mp h)

/-! ### Intertwiners out of a locally finite module -/

section LocallyFinite

variable [IsLocallyFiniteModule ℂ (UqSl2 q) V]

/-- **Intertwiners are maps of multiplicity spaces.** At a generic parameter, for a locally finite
`UqSl2 q`-module `V` and an arbitrary module `W`, postcomposition `g ↦ (φ ↦ g ∘ φ)` identifies
`Hom_U(V, W)` with `∏_(m,ε) Hom_ℂ(Hom_U(L_m^ε, V), Hom_U(L_m^ε, W))`. -/
noncomputable def ladderModuleHomEquiv (hq : IsGenericQuantumParameter q) :
    (V →ₗ[UqSl2 q] W) ≃ₗ[ℂ] Π p : ℕ × ℤˣ,
      (LadderModule q p.1 p.2 →ₗ[UqSl2 q] V) →ₗ[ℂ] (LadderModule q p.1 p.2 →ₗ[UqSl2 q] W) :=
  have := isSemisimpleModule_of_isLocallyFiniteModule hq (V := V)
  have (p : ℕ × ℤˣ) := LadderModule.isSimpleModule (m := p.1) (ε := p.2) hq
  isotypicHomEquiv ℂ (fun p : ℕ × ℤˣ => LadderModule q p.1 p.2)
    (ladderModule_eq_of_nonempty_linearEquiv hq)
    (fun _ _ => exists_linearEquiv_ladderModule_of_isLocallyFiniteModule hq)

@[simp]
theorem ladderModuleHomEquiv_apply (hq : IsGenericQuantumParameter q) (g : V →ₗ[UqSl2 q] W)
    (p : ℕ × ℤˣ) (φ : LadderModule q p.1 p.2 →ₗ[UqSl2 q] V) :
    ladderModuleHomEquiv hq g p φ = g ∘ₗ φ := by
  simp [ladderModuleHomEquiv]

/-- The intertwiner that the inverse of `TauCeti.UqSl2.ladderModuleHomEquiv` assigns to a family
`T` of maps of multiplicity spaces composes with `φ : L_m^ε → V` to `T (m, ε) φ`. -/
@[simp]
theorem ladderModuleHomEquiv_symm_apply_comp (hq : IsGenericQuantumParameter q)
    (T : Π p : ℕ × ℤˣ,
      (LadderModule q p.1 p.2 →ₗ[UqSl2 q] V) →ₗ[ℂ] (LadderModule q p.1 p.2 →ₗ[UqSl2 q] W))
    (m : ℕ) (ε : ℤˣ) (φ : LadderModule q m ε →ₗ[UqSl2 q] V) :
    (ladderModuleHomEquiv hq).symm T ∘ₗ φ = T (m, ε) φ := by
  rw [← ladderModuleHomEquiv_apply hq _ (m, ε) φ, LinearEquiv.apply_symm_apply]

/-- The intertwiner that the inverse of `TauCeti.UqSl2.ladderModuleHomEquiv` assigns to a family
`T` of maps of multiplicity spaces sends `φ v` to `T (m, ε) φ v`, for `φ : L_m^ε → V`. -/
@[simp]
theorem ladderModuleHomEquiv_symm_apply_apply (hq : IsGenericQuantumParameter q)
    (T : Π p : ℕ × ℤˣ,
      (LadderModule q p.1 p.2 →ₗ[UqSl2 q] V) →ₗ[ℂ] (LadderModule q p.1 p.2 →ₗ[UqSl2 q] W))
    (m : ℕ) (ε : ℤˣ) (φ : LadderModule q m ε →ₗ[UqSl2 q] V) (v : LadderModule q m ε) :
    (ladderModuleHomEquiv hq).symm T (φ v) = T (m, ε) φ v :=
  LinearMap.congr_fun (ladderModuleHomEquiv_symm_apply_comp hq T m ε φ) v

/-- **The commutant of a locally finite module.** At a generic parameter, postcomposition is an
algebra isomorphism from `End_U(V)` onto the product over `(m, ε)` of the full endomorphism
algebras `End_ℂ(Hom_U(L_m^ε, V))` of the multiplicity spaces. -/
noncomputable def ladderModuleEndAlgEquiv (hq : IsGenericQuantumParameter q) :
    Module.End (UqSl2 q) V ≃ₐ[ℂ]
      Π p : ℕ × ℤˣ, Module.End ℂ (LadderModule q p.1 p.2 →ₗ[UqSl2 q] V) :=
  have := isSemisimpleModule_of_isLocallyFiniteModule hq (V := V)
  have (p : ℕ × ℤˣ) := LadderModule.isSimpleModule (m := p.1) (ε := p.2) hq
  isotypicEndAlgEquiv ℂ (fun p : ℕ × ℤˣ => LadderModule q p.1 p.2)
    (ladderModule_eq_of_nonempty_linearEquiv hq)
    (fun _ _ => exists_linearEquiv_ladderModule_of_isLocallyFiniteModule hq)

@[simp]
theorem ladderModuleEndAlgEquiv_apply (hq : IsGenericQuantumParameter q)
    (g : Module.End (UqSl2 q) V) (p : ℕ × ℤˣ) (φ : LadderModule q p.1 p.2 →ₗ[UqSl2 q] V) :
    ladderModuleEndAlgEquiv hq g p φ = g ∘ₗ φ := by
  simp [ladderModuleEndAlgEquiv]

@[simp]
theorem ladderModuleEndAlgEquiv_toLinearEquiv (hq : IsGenericQuantumParameter q) :
    (ladderModuleEndAlgEquiv hq (V := V)).toLinearEquiv = ladderModuleHomEquiv hq :=
  LinearEquiv.ext fun _ ↦ by ext; simp

/-- The endomorphism that the inverse of `TauCeti.UqSl2.ladderModuleEndAlgEquiv` assigns to a
family `T` of endomorphisms of multiplicity spaces composes with `φ : L_m^ε → V` to
`T (m, ε) φ`. -/
@[simp]
theorem ladderModuleEndAlgEquiv_symm_apply_comp (hq : IsGenericQuantumParameter q)
    (T : Π p : ℕ × ℤˣ, Module.End ℂ (LadderModule q p.1 p.2 →ₗ[UqSl2 q] V))
    (m : ℕ) (ε : ℤˣ) (φ : LadderModule q m ε →ₗ[UqSl2 q] V) :
    (ladderModuleEndAlgEquiv hq).symm T ∘ₗ φ = T (m, ε) φ := by
  rw [← ladderModuleEndAlgEquiv_apply hq _ (m, ε) φ, AlgEquiv.apply_symm_apply]

/-- The endomorphism that the inverse of `TauCeti.UqSl2.ladderModuleEndAlgEquiv` assigns to a
family `T` of endomorphisms of multiplicity spaces sends `φ v` to `T (m, ε) φ v`, for
`φ : L_m^ε → V`. -/
@[simp]
theorem ladderModuleEndAlgEquiv_symm_apply_apply (hq : IsGenericQuantumParameter q)
    (T : Π p : ℕ × ℤˣ, Module.End ℂ (LadderModule q p.1 p.2 →ₗ[UqSl2 q] V))
    (m : ℕ) (ε : ℤˣ) (φ : LadderModule q m ε →ₗ[UqSl2 q] V) (v : LadderModule q m ε) :
    (ladderModuleEndAlgEquiv hq).symm T (φ v) = T (m, ε) φ v :=
  LinearMap.congr_fun (ladderModuleEndAlgEquiv_symm_apply_comp hq T m ε φ) v

/-- **The commutant of a locally finite module with finite multiplicities is a product of matrix
algebras.** At a generic parameter, if every multiplicity space `Hom_U(L_m^ε, V)` is
finite-dimensional, `End_U(V)` is isomorphic to the product over `(m, ε)` of the full matrix
algebras `M_a(ℂ)` with `a = dim Hom_U(L_m^ε, V)` the multiplicity of `L_m^ε` in `V`. This applies
to every finite-dimensional `V`. -/
theorem nonempty_end_algEquiv_pi_matrix (hq : IsGenericQuantumParameter q)
    [∀ p : ℕ × ℤˣ, FiniteDimensional ℂ (LadderModule q p.1 p.2 →ₗ[UqSl2 q] V)] :
    Nonempty (Module.End (UqSl2 q) V ≃ₐ[ℂ] Π p : ℕ × ℤˣ,
      Matrix (Fin (finrank ℂ (LadderModule q p.1 p.2 →ₗ[UqSl2 q] V)))
        (Fin (finrank ℂ (LadderModule q p.1 p.2 →ₗ[UqSl2 q] V))) ℂ) :=
  have := isSemisimpleModule_of_isLocallyFiniteModule hq (V := V)
  have (p : ℕ × ℤˣ) := LadderModule.isSimpleModule (m := p.1) (ε := p.2) hq
  TauCeti.nonempty_end_algEquiv_pi_matrix ℂ (fun p : ℕ × ℤˣ => LadderModule q p.1 p.2)
    (ladderModule_eq_of_nonempty_linearEquiv hq)
    (fun _ _ => exists_linearEquiv_ladderModule_of_isLocallyFiniteModule hq)

end LocallyFinite

/-! ### Finite-dimensional modules -/

section FiniteDimensional

variable [FiniteDimensional ℂ V]

/-- At a generic parameter, only finitely many signed ladder modules `L_m^ε` occur in a
finite-dimensional `UqSl2 q`-module. -/
theorem finite_support_finrank_linearMap_ladderModule (hq : IsGenericQuantumParameter q) :
    (Function.support fun p : ℕ × ℤˣ ↦
      finrank ℂ (LadderModule q p.1 p.2 →ₗ[UqSl2 q] V)).Finite :=
  have (p : ℕ × ℤˣ) := LadderModule.isSimpleModule (m := p.1) (ε := p.2) hq
  TauCeti.finite_support_finrank_linearMap ℂ (fun p : ℕ × ℤˣ => LadderModule q p.1 p.2)
    (ladderModule_eq_of_nonempty_linearEquiv hq)

/-- **The dimension of a space of intertwiners.** At a generic parameter, for a finite-dimensional
`UqSl2 q`-module `V` and a module `W` with finite multiplicities, for instance a
finite-dimensional one,
`dim Hom_U(V, W) = ∑_(m,ε) dim Hom_U(L_m^ε, V) · dim Hom_U(L_m^ε, W)`, a sum with finitely many
nonzero terms. -/
theorem finrank_linearMap_eq_finsum (hq : IsGenericQuantumParameter q)
    [∀ p : ℕ × ℤˣ, FiniteDimensional ℂ (LadderModule q p.1 p.2 →ₗ[UqSl2 q] W)] :
    finrank ℂ (V →ₗ[UqSl2 q] W) = ∑ᶠ p : ℕ × ℤˣ,
      finrank ℂ (LadderModule q p.1 p.2 →ₗ[UqSl2 q] V) *
        finrank ℂ (LadderModule q p.1 p.2 →ₗ[UqSl2 q] W) :=
  have := isSemisimpleModule_of_finiteDimensional hq (V := V)
  have (p : ℕ × ℤˣ) := LadderModule.isSimpleModule (m := p.1) (ε := p.2) hq
  TauCeti.finrank_linearMap_eq_finsum ℂ (fun p : ℕ × ℤˣ => LadderModule q p.1 p.2)
    (ladderModule_eq_of_nonempty_linearEquiv hq)
    (fun _ _ => exists_linearEquiv_ladderModule_of_isLocallyFiniteModule hq)

end FiniteDimensional

end TauCeti.UqSl2
