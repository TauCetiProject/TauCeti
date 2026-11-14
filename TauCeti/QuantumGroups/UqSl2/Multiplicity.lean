/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.QuantumGroups.UqSl2.LocallyFinite

/-!
# Hom spaces and endomorphism algebras of `U_q(sl₂)`-modules

At a generic parameter `q` (nonzero and not a root of unity), a locally finite `UqSl2 q`-module
`V` is canonically `⨁_(m,ε) L_m^ε ⊗ Hom_U(L_m^ε, V)`, by evaluation
(`TauCeti.UqSl2.ladderModuleTensorHomEquiv`). The multiplicity space `Hom_U(L_m^ε, V)` of the
signed ladder module `L_m^ε` carries all the information about maps out of `V`: a
`UqSl2 q`-linear map `g : V → W` is determined by, and can be prescribed through, the linear maps
`φ ↦ g ∘ φ` it induces between multiplicity spaces. This file records the two classical
consequences.

* The commutant of `UqSl2 q` on `V` is a product of full endomorphism algebras,
  `End_U(V) ≃ ∏_(m,ε) End_ℂ(Hom_U(L_m^ε, V))`, for any locally finite `V`, with no
  finite-dimensionality assumption on `V` or its multiplicity spaces. For
  finite-dimensional `V` this reads `End_U(V) ≃ ∏_(m,ε) M_a(ℂ)`, where
  `a = dim Hom_U(L_m^ε, V)` is the multiplicity of `L_m^ε` in `V`; only finitely many factors are
  nonzero.
* For finite-dimensional `V` and `W`,
  `dim Hom_U(V, W) = ∑_(m,ε) dim Hom_U(L_m^ε, V) · dim Hom_U(L_m^ε, W)`.

Both are the specializations of the general statements for a semisimple module over an
algebraically closed field, `TauCeti.endAlgEquivPiEnd`,
`TauCeti.nonempty_end_algEquiv_pi_matrix` and `TauCeti.finrank_linearMap_eq_finsum`, to the
complete list of finite-dimensional simple `UqSl2 q`-modules supplied by the classification.

## Main results

* `TauCeti.UqSl2.linearMapEquivPiLadderModule`: maps out of a locally finite module are
  families of linear maps between signed ladder multiplicity spaces.
* `TauCeti.UqSl2.endAlgEquivPiLadderModule`: at a generic parameter, the endomorphism algebra of
  a locally finite module is the product of the endomorphism algebras of its multiplicity spaces.
* `TauCeti.UqSl2.nonempty_end_algEquiv_pi_matrix_ladderModule`: at a generic parameter, the
  endomorphism algebra of a finite-dimensional module is a product of full matrix algebras whose
  sizes are the multiplicities.
* `TauCeti.UqSl2.finrank_linearMap_eq_finsum_ladderModule`: at a generic parameter, the dimension
  of the space of maps between finite-dimensional modules is the sum over `(m, ε)` of the products
  of the multiplicities of `L_m^ε`.

## References

* A. Virelizier, *Quantum groups*, Section 3, for the finite-dimensional representation theory of
  `U_q(sl₂)` at a generic parameter.
* C. W. Curtis and I. Reiner, *Representation Theory of Finite Groups and Associative Algebras*,
  §25, for the endomorphism algebra of a semisimple module.
-/

public section

namespace TauCeti.UqSl2

variable {q : ℂ} [Fact (q ≠ 0)]
  {V : Type*} [AddCommGroup V] [Module ℂ V] [Module (UqSl2 q) V] [IsScalarTower ℂ (UqSl2 q) V]
  {W : Type*} [AddCommGroup W] [Module ℂ W] [Module (UqSl2 q) W] [IsScalarTower ℂ (UqSl2 q) W]

/-- At a generic parameter, postcomposition identifies maps out of a locally finite module
with families of linear maps between its signed ladder multiplicity spaces. The target `W` is
arbitrary, and the multiplicity spaces may be infinite-dimensional. -/
noncomputable def linearMapEquivPiLadderModule (hq : IsGenericQuantumParameter q)
    [IsLocallyFiniteModule ℂ (UqSl2 q) V] :
    (V →ₗ[UqSl2 q] W) ≃ₗ[ℂ] Π p : ℕ × ℤˣ,
      (LadderModule q p.1 p.2 →ₗ[UqSl2 q] V) →ₗ[ℂ]
        (LadderModule q p.1 p.2 →ₗ[UqSl2 q] W) :=
  have := isSemisimpleModule_of_isLocallyFiniteModule hq (V := V)
  have (p : ℕ × ℤˣ) := LadderModule.isSimpleModule (m := p.1) (ε := p.2) hq
  linearMapEquivPiLinearMap ℂ (fun p : ℕ × ℤˣ => LadderModule q p.1 p.2)
    (fun _ _ => LadderModule.eq_of_nonempty_linearEquiv hq)
    (fun N _ => exists_linearEquiv_ladderModule_submodule hq N)

/-- `linearMapEquivPiLadderModule` acts by postcomposition on each multiplicity space. -/
@[simp]
theorem linearMapEquivPiLadderModule_apply (hq : IsGenericQuantumParameter q)
    [IsLocallyFiniteModule ℂ (UqSl2 q) V] (g : V →ₗ[UqSl2 q] W) (p : ℕ × ℤˣ)
    (φ : LadderModule q p.1 p.2 →ₗ[UqSl2 q] V) :
    linearMapEquivPiLadderModule hq g p φ = g ∘ₗ φ := by
  simp [linearMapEquivPiLadderModule]

/-- The map prescribed by `T` on multiplicity spaces sends `φ v` to `T (m, ε) φ v`. -/
@[simp]
theorem linearMapEquivPiLadderModule_symm_apply_apply (hq : IsGenericQuantumParameter q)
    [IsLocallyFiniteModule ℂ (UqSl2 q) V]
    (T : Π p : ℕ × ℤˣ, (LadderModule q p.1 p.2 →ₗ[UqSl2 q] V) →ₗ[ℂ]
      (LadderModule q p.1 p.2 →ₗ[UqSl2 q] W)) {m : ℕ} {ε : ℤˣ}
    (φ : LadderModule q m ε →ₗ[UqSl2 q] V) (v : LadderModule q m ε) :
    (linearMapEquivPiLadderModule hq).symm T (φ v) = T (m, ε) φ v := by
  have := isSemisimpleModule_of_isLocallyFiniteModule hq (V := V)
  have (p : ℕ × ℤˣ) := LadderModule.isSimpleModule (m := p.1) (ε := p.2) hq
  exact linearMapEquivPiLinearMap_symm_apply_apply ℂ
    (fun p : ℕ × ℤˣ => LadderModule q p.1 p.2)
    (fun _ _ => LadderModule.eq_of_nonempty_linearEquiv hq)
    (fun N _ => exists_linearEquiv_ladderModule_submodule hq N) T (j := (m, ε)) φ v

/-- **The commutant of a locally finite module.** At a generic parameter, postcomposition
identifies the endomorphism algebra of a locally finite `UqSl2 q`-module `V` with the product over
`(m, ε)` of the full endomorphism algebras of the multiplicity spaces `Hom_U(L_m^ε, V)`. These may
be infinite-dimensional. -/
noncomputable def endAlgEquivPiLadderModule (hq : IsGenericQuantumParameter q)
    [IsLocallyFiniteModule ℂ (UqSl2 q) V] :
    Module.End (UqSl2 q) V ≃ₐ[ℂ]
      Π p : ℕ × ℤˣ, Module.End ℂ (LadderModule q p.1 p.2 →ₗ[UqSl2 q] V) :=
  .ofLinearEquiv (linearMapEquivPiLadderModule (V := V) (W := V) hq) (by ext; simp)
    fun _ _ => by ext; simp

/-- `endAlgEquivPiLadderModule` sends an endomorphism `g` to postcomposition by `g` on every
multiplicity space. -/
@[simp]
theorem endAlgEquivPiLadderModule_apply (hq : IsGenericQuantumParameter q)
    [IsLocallyFiniteModule ℂ (UqSl2 q) V] (g : Module.End (UqSl2 q) V) (p : ℕ × ℤˣ)
    (φ : LadderModule q p.1 p.2 →ₗ[UqSl2 q] V) :
    endAlgEquivPiLadderModule hq g p φ = g ∘ₗ φ := by
  simpa only [endAlgEquivPiLadderModule, AlgEquiv.ofLinearEquiv_apply] using
    linearMapEquivPiLadderModule_apply hq g p φ

/-- The endomorphism with prescribed action `T` on the multiplicity spaces sends the value `φ v`
of `φ : L_m^ε → V` to `T (m, ε) φ v`. -/
@[simp]
theorem endAlgEquivPiLadderModule_symm_apply_apply (hq : IsGenericQuantumParameter q)
    [IsLocallyFiniteModule ℂ (UqSl2 q) V]
    (T : Π p : ℕ × ℤˣ, Module.End ℂ (LadderModule q p.1 p.2 →ₗ[UqSl2 q] V)) {m : ℕ} {ε : ℤˣ}
    (φ : LadderModule q m ε →ₗ[UqSl2 q] V) (v : LadderModule q m ε) :
    (endAlgEquivPiLadderModule hq).symm T (φ v) = T (m, ε) φ v :=
  linearMapEquivPiLadderModule_symm_apply_apply hq T φ v

/-- **The endomorphism algebra of a finite-dimensional module.** At a generic parameter, the
endomorphism algebra of a finite-dimensional `UqSl2 q`-module `V` is the product over `(m, ε)` of
the full matrix algebras `M_a(ℂ)`, where `a = dim Hom_U(L_m^ε, V)` is the multiplicity of `L_m^ε`
in `V`. All but finitely many factors are the zero ring. -/
theorem nonempty_end_algEquiv_pi_matrix_ladderModule (hq : IsGenericQuantumParameter q)
    [FiniteDimensional ℂ V] :
    Nonempty (Module.End (UqSl2 q) V ≃ₐ[ℂ] Π p : ℕ × ℤˣ,
      Matrix (Fin (Module.finrank ℂ (LadderModule q p.1 p.2 →ₗ[UqSl2 q] V)))
        (Fin (Module.finrank ℂ (LadderModule q p.1 p.2 →ₗ[UqSl2 q] V))) ℂ) := by
  have := isSemisimpleModule_of_finiteDimensional hq (V := V)
  have (p : ℕ × ℤˣ) := LadderModule.isSimpleModule (m := p.1) (ε := p.2) hq
  exact nonempty_end_algEquiv_pi_matrix ℂ (fun p : ℕ × ℤˣ => LadderModule q p.1 p.2)
    (fun _ _ => LadderModule.eq_of_nonempty_linearEquiv hq)
    (fun N _ => exists_linearEquiv_ladderModule_submodule hq N)

/-- **The dimension of a hom space.** At a generic parameter, for finite-dimensional
`UqSl2 q`-modules `V` and `W`,
`dim Hom_U(V, W) = ∑_(m,ε) dim Hom_U(L_m^ε, V) · dim Hom_U(L_m^ε, W)`: the multiplicities of
each signed ladder module `L_m^ε` in `V` and in `W` multiply, and only finitely many terms are
nonzero. -/
theorem finrank_linearMap_eq_finsum_ladderModule (hq : IsGenericQuantumParameter q)
    [FiniteDimensional ℂ V] [FiniteDimensional ℂ W] :
    Module.finrank ℂ (V →ₗ[UqSl2 q] W) =
      ∑ᶠ p : ℕ × ℤˣ, Module.finrank ℂ (LadderModule q p.1 p.2 →ₗ[UqSl2 q] V) *
        Module.finrank ℂ (LadderModule q p.1 p.2 →ₗ[UqSl2 q] W) := by
  have := isSemisimpleModule_of_finiteDimensional hq (V := V)
  have (p : ℕ × ℤˣ) := LadderModule.isSimpleModule (m := p.1) (ε := p.2) hq
  exact finrank_linearMap_eq_finsum ℂ (fun p : ℕ × ℤˣ => LadderModule q p.1 p.2)
    (fun _ _ => LadderModule.eq_of_nonempty_linearEquiv hq)
    (fun N _ => exists_linearEquiv_ladderModule_submodule hq N)

end TauCeti.UqSl2
