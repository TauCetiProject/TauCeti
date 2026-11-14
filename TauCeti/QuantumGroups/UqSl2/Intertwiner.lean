/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.ToLin
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
the multiplicity spaces. For finite-dimensional `V` and `W`, with multiplicities
`a_(m,ε)(V) = dim Hom_U(L_m^ε, V)`, this gives the two classical formulas

`dim Hom_U(V, W) = ∑_(m,ε) a_(m,ε)(V) · a_(m,ε)(W)` and `End_U(V) ≃ ∏_(m,ε) M_(a_(m,ε)(V))(ℂ)`.

Only finitely many `L_m^ε` occur in a finite-dimensional module, so the sum is finite and all but
finitely many matrix factors are the zero ring of `0 × 0` matrices.

## Main definitions

* `TauCeti.UqSl2.ladderModuleHomEquiv`: at a generic parameter, the isomorphism
  `Hom_U(V, W) ≃ ∏_(m,ε) Hom_ℂ(Hom_U(L_m^ε, V), Hom_U(L_m^ε, W))` for locally finite `V`.
* `TauCeti.UqSl2.ladderModuleEndAlgEquiv`: at a generic parameter, the algebra isomorphism
  `End_U(V) ≃ ∏_(m,ε) End_ℂ(Hom_U(L_m^ε, V))` for locally finite `V`.

## Main results

* `TauCeti.UqSl2.finite_support_finrank_linearMap_ladderModule`: only finitely many `L_m^ε` occur
  in a finite-dimensional module.
* `TauCeti.UqSl2.finrank_linearMap_eq_finsum`: at a generic parameter,
  `dim Hom_U(V, W) = ∑_(m,ε) dim Hom_U(L_m^ε, V) · dim Hom_U(L_m^ε, W)` for finite-dimensional
  `V` and `W`.
* `TauCeti.UqSl2.nonempty_end_algEquiv_pi_matrix`: at a generic parameter, `End_U(V)` is a
  product of full matrix algebras `M_(a_(m,ε))(ℂ)` of the sizes of the multiplicities of the
  finite-dimensional module `V`.

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
    (fun _ _ h => Prod.ext_iff.mpr ((LadderModule.nonempty_linearEquiv_iff hq).mp h))
    (fun N _ => exists_linearEquiv_ladderModule_submodule hq N)

@[simp]
theorem ladderModuleHomEquiv_apply (hq : IsGenericQuantumParameter q) (g : V →ₗ[UqSl2 q] W)
    (p : ℕ × ℤˣ) (φ : LadderModule q p.1 p.2 →ₗ[UqSl2 q] V) :
    ladderModuleHomEquiv hq g p φ = g ∘ₗ φ := by
  simp [ladderModuleHomEquiv]

/-- The intertwiner that `TauCeti.UqSl2.ladderModuleHomEquiv` assigns to a family `T` of maps of
multiplicity spaces composes with `φ : L_m^ε → V` to `T (m, ε) φ`. -/
@[simp]
theorem ladderModuleHomEquiv_symm_apply_comp (hq : IsGenericQuantumParameter q)
    (T : Π p : ℕ × ℤˣ,
      (LadderModule q p.1 p.2 →ₗ[UqSl2 q] V) →ₗ[ℂ] (LadderModule q p.1 p.2 →ₗ[UqSl2 q] W))
    (p : ℕ × ℤˣ) (φ : LadderModule q p.1 p.2 →ₗ[UqSl2 q] V) :
    (ladderModuleHomEquiv hq).symm T ∘ₗ φ = T p φ := by
  rw [← ladderModuleHomEquiv_apply hq, LinearEquiv.apply_symm_apply]

/-- **The commutant of a locally finite module.** At a generic parameter, postcomposition is an
algebra isomorphism from `End_U(V)` onto the product over `(m, ε)` of the full endomorphism
algebras `End_ℂ(Hom_U(L_m^ε, V))` of the multiplicity spaces. -/
noncomputable def ladderModuleEndAlgEquiv (hq : IsGenericQuantumParameter q) :
    Module.End (UqSl2 q) V ≃ₐ[ℂ]
      Π p : ℕ × ℤˣ, Module.End ℂ (LadderModule q p.1 p.2 →ₗ[UqSl2 q] V) :=
  .ofLinearEquiv (ladderModuleHomEquiv hq) (by ext; simp) fun _ _ ↦ by ext; simp

@[simp]
theorem ladderModuleEndAlgEquiv_apply (hq : IsGenericQuantumParameter q)
    (g : Module.End (UqSl2 q) V) (p : ℕ × ℤˣ) (φ : LadderModule q p.1 p.2 →ₗ[UqSl2 q] V) :
    ladderModuleEndAlgEquiv hq g p φ = g ∘ₗ φ := by
  simp [ladderModuleEndAlgEquiv]

end LocallyFinite

/-! ### Finite-dimensional modules -/

section FiniteDimensional

variable [FiniteDimensional ℂ V]

/-- At a generic parameter, only finitely many signed ladder modules `L_m^ε` occur in a
finite-dimensional `UqSl2 q`-module. -/
theorem finite_support_finrank_linearMap_ladderModule (hq : IsGenericQuantumParameter q) :
    (Function.support fun p : ℕ × ℤˣ ↦
      finrank ℂ (LadderModule q p.1 p.2 →ₗ[UqSl2 q] V)).Finite := by
  obtain ⟨n, m, ε, ⟨e⟩⟩ := exists_linearEquiv_pi_ladderModule hq (V := V)
  have (i : Fin n) := LadderModule.isSimpleModule (m := m i) (ε := ε i) hq
  refine (Set.finite_range fun i ↦ (m i, ε i)).subset fun p hp ↦ ?_
  have := LadderModule.isSimpleModule (m := p.1) (ε := p.2) hq
  rw [Function.mem_support, finrank_linearMap_eq_natCard_of_linearEquiv_pi (k := ℂ) e,
    Nat.card_ne_zero] at hp
  obtain ⟨i, he⟩ := hp.1.some
  obtain ⟨h1, h2⟩ := (LadderModule.nonempty_linearEquiv_iff hq).mp he
  exact ⟨i, Prod.ext h1.symm h2.symm⟩

variable [FiniteDimensional ℂ W]

/-- **The dimension of a space of intertwiners.** At a generic parameter, for finite-dimensional
`UqSl2 q`-modules `V` and `W`,
`dim Hom_U(V, W) = ∑_(m,ε) dim Hom_U(L_m^ε, V) · dim Hom_U(L_m^ε, W)`, a sum with finitely many
nonzero terms. -/
theorem finrank_linearMap_eq_finsum (hq : IsGenericQuantumParameter q) :
    finrank ℂ (V →ₗ[UqSl2 q] W) = ∑ᶠ p : ℕ × ℤˣ,
      finrank ℂ (LadderModule q p.1 p.2 →ₗ[UqSl2 q] V) *
        finrank ℂ (LadderModule q p.1 p.2 →ₗ[UqSl2 q] W) := by
  classical
  set s := (finite_support_finrank_linearMap_ladderModule hq (V := V)).toFinset
  let X (p : ℕ × ℤˣ) :=
    (LadderModule q p.1 p.2 →ₗ[UqSl2 q] V) →ₗ[ℂ] (LadderModule q p.1 p.2 →ₗ[UqSl2 q] W)
  -- Off the support the multiplicity space of `V`, hence the factor `X p`, is zero, so the
  -- product over all `(m, ε)` is the product over the finite support.
  have hX (p : ℕ × ℤˣ) (hp : p ∉ s) : Subsingleton (X p) := by
    rw [← Module.finrank_zero_iff (R := ℂ), Module.finrank_linearMap, mul_eq_zero]
    exact Or.inl (by simpa [s] using hp)
  let r : (Π p, X p) →ₗ[ℂ] Π p : s, X p := LinearMap.pi fun p ↦ LinearMap.proj p.1
  have hr : Function.Bijective r := by
    refine ⟨fun x y h ↦ funext fun p ↦ ?_, fun y ↦ ⟨fun p ↦ if hp : p ∈ s then y ⟨p, hp⟩ else 0,
      funext fun p ↦ by simp [r]⟩⟩
    by_cases hp : p ∈ s
    · exact congrFun h ⟨p, hp⟩
    · exact (hX p hp).elim _ _
  rw [(ladderModuleHomEquiv hq).finrank_eq, (LinearEquiv.ofBijective r hr).finrank_eq,
    Module.finrank_pi_fintype, finsum_eq_sum_of_support_subset _ (s := s) fun p hp ↦ by
      simpa [s] using left_ne_zero_of_mul hp, ← Finset.sum_coe_sort s]
  simp only [X, Module.finrank_linearMap]

/-- **The commutant of a finite-dimensional module is a product of matrix algebras.** At a
generic parameter, `End_U(V)` is isomorphic to the product over `(m, ε)` of the full matrix
algebras `M_a(ℂ)` with `a = dim Hom_U(L_m^ε, V)` the multiplicity of `L_m^ε` in `V`. -/
theorem nonempty_end_algEquiv_pi_matrix (hq : IsGenericQuantumParameter q) :
    Nonempty (Module.End (UqSl2 q) V ≃ₐ[ℂ] Π p : ℕ × ℤˣ,
      Matrix (Fin (finrank ℂ (LadderModule q p.1 p.2 →ₗ[UqSl2 q] V)))
        (Fin (finrank ℂ (LadderModule q p.1 p.2 →ₗ[UqSl2 q] V))) ℂ) :=
  ⟨(ladderModuleEndAlgEquiv hq).trans
    (AlgEquiv.piCongrRight fun _ ↦ LinearMap.toMatrixAlgEquiv (Module.finBasis ℂ _))⟩

end FiniteDimensional

end TauCeti.UqSl2
