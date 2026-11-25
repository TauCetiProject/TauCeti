/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Injective
public import Mathlib.Algebra.Module.Projective
public import Mathlib.Algebra.Module.Equiv.Basic
public import Mathlib.RingTheory.Finiteness.Cardinality
public import Mathlib.RingTheory.Finiteness.Projective

/-!
# Projective-injective modules over a ring acting on a finitely generated module

Let `M` be a finitely generated module over a ring `A`, and let a ring `Γ` act faithfully on `M` by
`A`-linear maps. The main example is the endomorphism ring `Γ = Module.End A M`, acting by
evaluation. If `m₁, …, mₖ` generate `M` over `A`, the map `γ ↦ (γ • m₁, …, γ • mₖ)` embeds `Γ` into
`Mᵏ` as a `Γ`-module (`TauCeti.exists_injective_pi_of_faithfulSMul`): an element of `Γ` killing
the generators kills `M`, since it acts `A`-linearly.

Hence a finitely generated projective `Γ`-module `P`, a direct summand of some `Γⁿ`, embeds into
`Mⁿᵏ`. If `P` is also injective, this embedding splits, so **`P` is a retract of a finite power of
`M`**: it lies in the additive closure `add M`
(`TauCeti.exists_comp_eq_id_pi_of_projective_of_injective`). Neither `A` nor `Γ` needs any
finiteness or chain condition.

This is the step of the Morita-Tachikawa correspondence that recovers the additive closure of a
generator-cogenerator `M` from its endomorphism ring: `M` is itself finitely generated, projective
and injective over `Module.End A M`, and the finitely generated projective-injective modules over
`Module.End A M` are exactly the retracts of finite powers of `M`.

## Main results

* `TauCeti.exists_injective_pi_of_faithfulSMul`: a ring acting faithfully and `A`-linearly on a
  finitely generated `A`-module `M` embeds into a finite power of `M`.
* `TauCeti.exists_comp_eq_id_pi_of_projective_of_injective`: a finitely generated projective and
  injective module over such a ring is a retract of a finite power of `M`.

## References

* B. J. Müller, *The classification of algebras by dominant dimension*, Canad. J. Math. 20 (1968),
  398–409.
* M. Auslander, I. Reiten, S. O. Smalø, *Representation Theory of Artin Algebras*, Cambridge
  Studies in Advanced Mathematics 36, CUP (1995), Section VI.5.
-/

public section

namespace TauCeti

universe v

variable {A : Type*} [Ring A] {Γ : Type*} [Ring Γ] {M : Type v} [AddCommGroup M] [Module A M]
  [Module Γ M] [SMulCommClass Γ A M] [FaithfulSMul Γ M] [Module.Finite A M]

variable (A Γ M) in
include A in
/-- **A ring acting faithfully on a finitely generated module embeds into a finite power of it.**
If `Γ` acts faithfully and `A`-linearly on a finitely generated `A`-module `M`, then `Γ` embeds
into some `Mᵏ` as a `Γ`-module, by `γ ↦ (γ • m₁, …, γ • mₖ)` for generators `mᵢ` of `M`. -/
theorem exists_injective_pi_of_faithfulSMul :
    ∃ (k : ℕ) (f : Γ →ₗ[Γ] (Fin k → M)), Function.Injective f := by
  obtain ⟨k, s, hs⟩ := Module.Finite.exists_fin (R := A) (M := M)
  refine ⟨k, LinearMap.pi fun i ↦ LinearMap.toSpanSingleton Γ M (s i), fun γ γ' h ↦ ?_⟩
  -- The `A`-linear maps `γ • ·` and `γ' • ·` agree on the generators `s i`.
  let φ (g : Γ) : M →ₗ[A] M :=
    { toFun m := g • m
      map_add' := smul_add g
      map_smul' a m := smul_comm g a m }
  have h' : φ γ = φ γ' := LinearMap.ext_on_range hs fun i ↦ by simpa [φ] using congrFun h i
  exact FaithfulSMul.eq_of_smul_eq_smul fun m ↦ LinearMap.congr_fun h' m

variable [Small.{v} Γ]

variable (A M) in
include A in
/-- **A finitely generated projective-injective module lies in the additive closure.** Let `Γ` act
faithfully and `A`-linearly on a finitely generated `A`-module `M`, for instance
`Γ = Module.End A M`. Then every finitely generated projective and injective `Γ`-module `P` is a
retract of a finite power of `M`: there are `Γ`-linear maps `s : P → Mⁿ` and `r : Mⁿ → P` with
`r ∘ s = id`. -/
theorem exists_comp_eq_id_pi_of_projective_of_injective (P : Type v) [AddCommGroup P]
    [Module Γ P] [Module.Finite Γ P] [Module.Projective Γ P] [Module.Injective Γ P] :
    ∃ (n : ℕ) (s : P →ₗ[Γ] (Fin n → M)) (r : (Fin n → M) →ₗ[Γ] P), r ∘ₗ s = .id := by
  obtain ⟨k, f, hf⟩ := exists_injective_pi_of_faithfulSMul A Γ M
  obtain ⟨n, π, σ, -, -, hπσ⟩ := Module.Finite.exists_comp_eq_id_of_projective Γ P
  -- `P` embeds into `Γⁿ`, hence into `(Mᵏ)ⁿ ≅ Mⁿᵏ`.
  let c : (Fin n → Fin k → M) ≃ₗ[Γ] (Fin (n * k) → M) :=
    (LinearEquiv.curry (R := Γ) (M := M) (V := Fin n) (V₂ := Fin k)).symm ≪≫ₗ
      LinearEquiv.funCongrLeft Γ M finProdFinEquiv.symm
  let s := c.toLinearMap ∘ₗ f.compLeft (Fin n) ∘ₗ σ
  have hσ : Function.Injective σ :=
    Function.LeftInverse.injective (g := π) fun x ↦ LinearMap.congr_fun hπσ x
  have hs : Function.Injective s :=
    c.injective.comp (Function.Injective.comp (f := σ)
      (fun x y h ↦ funext fun i ↦ hf (congrFun h i)) hσ)
  -- The embedding splits, since `P` is injective.
  obtain ⟨r, hr⟩ := (Module.Baer.of_injective ‹_›).extension_property s hs .id
  exact ⟨n * k, s, r, hr⟩

end TauCeti
