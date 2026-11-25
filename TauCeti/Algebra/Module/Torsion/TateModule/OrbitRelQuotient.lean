/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.Torsion.TateModule.Snake

/-!
# The Tate module of a torus

Let `f : Λ → E` be an injective additive map and `T = E / f(Λ)` the orbit space of translation by
its range, for instance a lattice `Λ` in a real vector space `E` and its torus. This file
specializes `TauCeti.Algebra.Module.Torsion.TateModule.Snake` to the short exact sequence
`0 → Λ → E → T → 0`.
If multiplication by `p` is bijective on `E`, the connecting isomorphisms `T[pⁿ] ≃ Λ ⧸ pⁿΛ` are
compatible with the transition maps: multiplication by `p` on `T[pⁿ⁺¹] → T[pⁿ]` corresponds to
reduction `Λ ⧸ pⁿ⁺¹Λ → Λ ⧸ pⁿΛ` (`LinearMap.orbitRelQuotientTateModuleLevelδ_transition`).
Passing to the inverse limit identifies the `p`-adic Tate module `TauCeti.TateModule p T` with
the `p`-adic completion of `Λ` (`LinearMap.orbitRelQuotientTateModuleδEquiv`), and for finitely
generated `Λ` with `ℤ^_p ⊗ Λ`, `ℤ^_p` the `p`-adic completion of `ℤ`
(`LinearMap.orbitRelQuotientTateModuleδEquivTensor`).

Both identifications are additive equivalences. Their targets are Mathlib's `AdicCompletion` for
the ideal `(p)` of `ℤ`, not modules over the `p`-adic integers `ℤ_[p]`.

## Main definitions

* `LinearMap.orbitRelQuotientTateModuleLevelδ`: the connecting map `T[pⁿ] → Λ ⧸ (p)ⁿΛ`.
* `LinearMap.orbitRelQuotientTateModuleδEquiv`: `T_p T ≃ lim Λ ⧸ pⁿΛ`, the `p`-adic completion,
  when multiplication by `p` is bijective on `E`.
* `LinearMap.orbitRelQuotientTateModuleδEquivTensor`: `T_p T ≃ ℤ^_p ⊗ Λ` for finitely generated
  `Λ`, when multiplication by `p` is bijective on `E`.

## Main statements

* `LinearMap.orbitRelQuotientTateModuleLevelδ_eq`: the class of `β` with `pⁿ β = f l` goes to the
  class of `l`.
* `LinearMap.orbitRelQuotientTateModuleLevelδ_transition`: multiplication by `p` on torsion
  corresponds to reduction of lattice classes.
* `LinearMap.bijective_orbitRelQuotientTateModuleLevelδ`: each level map is bijective when
  multiplication by `p` is bijective on `E`.
-/

public noncomputable section

open Function Submodule TauCeti

open scoped TensorProduct

namespace LinearMap

section Level

variable {Λ E : Type*} [AddCommGroup Λ] [AddCommGroup E] (f : Λ →ₗ[ℤ] E) (hf : Injective f)
  (p : ℕ)

/-- The connecting map `T[pⁿ] → Λ ⧸ (p)ⁿΛ` of the orbit space `T = E / f(Λ)`, with the target
written as the `n`-th level of the `p`-adic completion of `Λ`: the level map
`TauCeti.tateModuleLevelδ` of the exact sequence `0 → Λ → E → T → 0`. -/
def orbitRelQuotientTateModuleLevelδ (n : ℕ) :
    TateModuleLevel p (AddAction.orbitRel.Quotient (range f) E) n →+
      Λ ⧸ (Ideal.span {(p : ℤ)} ^ n • ⊤ : Submodule ℤ Λ) :=
  tateModuleLevelδ p (g := (range f).orbitRelQuotientMkHom.toIntLinearMap)
    (exact_orbitRelQuotientMkHom_range f) hf
    (range f).orbitRelQuotientMkHom_surjective n

/-- The level map sends the class of `β` with `pⁿ β = f l` to the class of `l`. -/
theorem orbitRelQuotientTateModuleLevelδ_eq {n : ℕ}
    (x : TateModuleLevel p (AddAction.orbitRel.Quotient (range f) E) n)
    {β : E} (hx : (x : AddAction.orbitRel.Quotient (range f) E) = Quotient.mk _ β) {l : Λ}
    (hl : f l = ((p ^ n : ℕ) : ℤ) • β) :
    f.orbitRelQuotientTateModuleLevelδ hf p n x = Submodule.Quotient.mk l :=
  tateModuleLevelδ_eq p _ hf _ x (by simpa using hx.symm) hl

/-- Every point of `T[pⁿ]` is the class of some `β` with `pⁿ β = f l`. -/
theorem exists_orbitRelQuotient_mk_eq_and_eq_smul {n : ℕ}
    (x : TateModuleLevel p (AddAction.orbitRel.Quotient (range f) E) n) :
    ∃ β : E, ∃ l : Λ, (x : AddAction.orbitRel.Quotient (range f) E) = Quotient.mk _ β ∧
      f l = ((p ^ n : ℕ) : ℤ) • β := by
  obtain ⟨β, hβ⟩ := Quotient.exists_rep (x : AddAction.orbitRel.Quotient (range f) E)
  obtain ⟨l, hl⟩ := (f.mk_mem_torsionBy_orbitRelQuotient_iff _).1 (hβ ▸ x.property)
  exact ⟨β, l, hβ.symm, hl⟩

/-- **Compatibility with the transition maps.** Multiplication by `p` on `T[pⁿ⁺¹] → T[pⁿ]`
corresponds to reduction `Λ ⧸ (p)ⁿ⁺¹Λ → Λ ⧸ (p)ⁿΛ`. -/
theorem orbitRelQuotientTateModuleLevelδ_transition (n : ℕ)
    (x : TateModuleLevel p (AddAction.orbitRel.Quotient (range f) E) (n + 1)) :
    f.orbitRelQuotientTateModuleLevelδ hf p n
        (tateModuleTransition p (AddAction.orbitRel.Quotient (range f) E) n x) =
      factorPow (Ideal.span {(p : ℤ)}) Λ n.le_succ
        (f.orbitRelQuotientTateModuleLevelδ hf p (n + 1) x) :=
  tateModuleLevelδ_transition p _ hf _ n x

/-- When multiplication by `p` is bijective on `E`, each level map `T[pⁿ] → Λ ⧸ (p)ⁿΛ` is
bijective. -/
theorem bijective_orbitRelQuotientTateModuleLevelδ (hp : Bijective fun v : E ↦ (p : ℤ) • v)
    (n : ℕ) :
    Bijective (f.orbitRelQuotientTateModuleLevelδ hf p n) :=
  bijective_tateModuleLevelδ p _ hf _ hp n

/-- **The Tate module of a torus.** When multiplication by `p` is bijective on `E`, the `p`-adic
Tate module of `T = E / f(Λ)` is the `p`-adic completion `lim Λ ⧸ pⁿΛ` of `Λ`: a compatible family
of torsion points `[βₙ]` with `pⁿ βₙ = f lₙ` goes to the family of classes of the `lₙ`. It is
`TauCeti.tateModuleδEquiv` for the exact sequence `0 → Λ → E → T → 0`. -/
def orbitRelQuotientTateModuleδEquiv (hp : Bijective fun v : E ↦ (p : ℤ) • v) :
    TateModule p (AddAction.orbitRel.Quotient (range f) E) ≃+
      AdicCompletion (Ideal.span {(p : ℤ)}) Λ :=
  tateModuleδEquiv p (g := (range f).orbitRelQuotientMkHom.toIntLinearMap)
    (exact_orbitRelQuotientMkHom_range f) hf
    (range f).orbitRelQuotientMkHom_surjective hp

/-- The `n`-th component of the image of a Tate-module point is the image of its `n`-th level. -/
@[simp]
theorem orbitRelQuotientTateModuleδEquiv_apply_val (hp : Bijective fun v : E ↦ (p : ℤ) • v)
    (x : TateModule p (AddAction.orbitRel.Quotient (range f) E)) (n : ℕ) :
    (f.orbitRelQuotientTateModuleδEquiv hf p hp x).val n =
      f.orbitRelQuotientTateModuleLevelδ hf p n (TateModule.proj n x) :=
  (congrArg (·.val n) (tateModuleδEquiv_apply p _ hf _ hp x)).trans
    (tateModuleδ_apply_val p _ hf _ x n)

/-- The inverse equivalence sends a compatible family of lattice classes to the Tate-module point
whose `n`-th level is sent to the `n`-th class. -/
@[simp]
theorem orbitRelQuotientTateModuleLevelδ_proj_orbitRelQuotientTateModuleδEquiv_symm
    (hp : Bijective fun v : E ↦ (p : ℤ) • v) (c : AdicCompletion (Ideal.span {(p : ℤ)}) Λ)
    (n : ℕ) :
    f.orbitRelQuotientTateModuleLevelδ hf p n
        (TateModule.proj n ((f.orbitRelQuotientTateModuleδEquiv hf p hp).symm c)) = c.val n :=
  tateModuleLevelδ_proj_tateModuleδEquiv_symm p _ hf _ hp c n

end Level

section Finite

variable {Λ : Type} {E : Type*} [AddCommGroup Λ] [Module.Finite ℤ Λ] [AddCommGroup E]
  (f : Λ →ₗ[ℤ] E) (hf : Injective f) (p : ℕ)

/-- **The Tate module of a torus as `ℤ^_p ⊗ Λ`.** For finitely generated `Λ` and injective `f`,
when multiplication by `p` is bijective on `E`, the `p`-adic Tate module of `T = E / f(Λ)` is
`ℤ^_p ⊗ Λ`, with `ℤ^_p` the `p`-adic completion of `ℤ`: `TauCeti.tateModuleδEquivTensor` for the
exact sequence `0 → Λ → E → T → 0`. -/
def orbitRelQuotientTateModuleδEquivTensor (hp : Bijective fun v : E ↦ (p : ℤ) • v) :
    TateModule p (AddAction.orbitRel.Quotient (range f) E) ≃+
      AdicCompletion (Ideal.span {(p : ℤ)}) ℤ ⊗[ℤ] Λ :=
  tateModuleδEquivTensor p (g := (range f).orbitRelQuotientMkHom.toIntLinearMap)
    (exact_orbitRelQuotientMkHom_range f) hf
    (range f).orbitRelQuotientMkHom_surjective hp

/-- Mathlib's `AdicCompletion.ofTensorProduct` turns the tensor form back into the `p`-adic
completion form of the equivalence. -/
@[simp]
theorem ofTensorProduct_orbitRelQuotientTateModuleδEquivTensor
    (hp : Bijective fun v : E ↦ (p : ℤ) • v)
    (x : TateModule p (AddAction.orbitRel.Quotient (range f) E)) :
    AdicCompletion.ofTensorProduct (Ideal.span {(p : ℤ)}) Λ
        (f.orbitRelQuotientTateModuleδEquivTensor hf p hp x) =
      f.orbitRelQuotientTateModuleδEquiv hf p hp x :=
  ofTensorProduct_tateModuleδEquivTensor p _ hf _ hp x

end Finite

end LinearMap
