/-
Copyright (c) 2026 The Formal Conjectures Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors, Codex
-/
module

public import TauCeti.LinearAlgebra.Basis.Exact
public import TauCeti.LinearAlgebra.ExteriorPower.Basis

/-!
# Determinants of exact sequences of finite free modules

For a short exact sequence `0 → M → N → P → 0` over a commutative ring, finite bases
of `M` and `P` give a canonical comparison of their determinant lines. Its value is the
wedge of the submodule vectors followed by arbitrary lifts of the quotient vectors.
The comparison is independent of both finite bases and of the quotient lifts.
No field or nontriviality hypothesis is required.

This is the affine free-module input for the determinant of an extension of vector bundles.
It does not construct or glue the sheaf isomorphism.

## Provenance

Adapted from the family 033 formalization in `openai/math`, extraction revision
`4eaee87548250b2682affda7d05d947c05554bae`, and its cLEAN refactoring supplied by an
original formalization author. The source declaration is
`OAI.ReverseLogKodaira.CanonicalAdjunction.exact_canonical_adjunction`.
This file has been modified from that formalization.

## References

* The Stacks Project, Tag 0FJB: determinants of finite projective modules.
-/

public section

noncomputable section

open scoped TensorProduct

namespace TauCeti.exteriorPower

section Comparison

variable {R M N P : Type*} [CommRing R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  [AddCommGroup P] [Module R P]
  {f : M →ₗ[R] N} {q : N →ₗ[R] P}
  (hf : Function.Injective f) (he : Function.Exact f q)
  {n r : ℕ} (b : Module.Basis (Fin n) R M) (c : Module.Basis (Fin r) R P)
  (lifts : Fin r → N) (hlifts : ∀ j, q (lifts j) = c j)

private def equivOfLifts :
    (⋀[R]^n M) ⊗[R] (⋀[R]^r P) ≃ₗ[R] ⋀[R]^(n + r) N :=
  ((TensorProduct.congr b.exteriorPowerTopEquiv c.exteriorPowerTopEquiv).trans
    (TensorProduct.lid R R)).trans
      ((Module.Basis.ofExactLift hf he b c lifts hlifts).reindex
        finSumFinEquiv).exteriorPowerTopEquiv.symm

private lemma equivOfLifts_wedge (v : Fin n → M) (z : Fin r → N) :
    equivOfLifts hf he b c lifts hlifts
      (exteriorPower.ιMulti R n v ⊗ₜ[R] exteriorPower.ιMulti R r (q ∘ z)) =
      exteriorPower.ιMulti R (n + r) (Fin.append (f ∘ v) z) := by
  apply ((Module.Basis.ofExactLift hf he b c lifts hlifts).reindex
    finSumFinEquiv).exteriorPowerTopEquiv.injective
  have happend : Fin.append (f ∘ v) z ∘ finSumFinEquiv = Sum.elim (f ∘ v) z := by
    funext i
    cases i <;> simp
  simp only [equivOfLifts, LinearEquiv.trans_apply, TensorProduct.congr_tmul,
    Module.Basis.exteriorPowerTopEquiv_apply_ιMulti, TensorProduct.lid_tmul,
    smul_eq_mul, LinearEquiv.apply_symm_apply, Module.Basis.det_reindex, happend]
  exact (Module.Basis.ofExactLift_det_eq_mul hf he b c lifts hlifts v (q ∘ z)
    (Sum.elim (f ∘ v) z) (fun _ ↦ rfl) (fun _ ↦ rfl)).symm

end Comparison

private theorem exact_canonical_adjunction
    {R M N P : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [AddCommGroup P] [Module R P]
    (f : M →ₗ[R] N) (q : N →ₗ[R] P)
    (hf : Function.Injective f) (he : Function.Exact f q) (hq : Function.Surjective q)
    {n r : ℕ} (b : Module.Basis (Fin n) R M) (c : Module.Basis (Fin r) R P) :
    ∃ e : (⋀[R]^n M) ⊗[R] (⋀[R]^r P) ≃ₗ[R] ⋀[R]^(n + r) N,
      ∀ (v : Fin n → M) (z : Fin r → N),
        e (exteriorPower.ιMulti R n v ⊗ₜ[R] exteriorPower.ιMulti R r (q ∘ z)) =
          exteriorPower.ιMulti R (n + r) (Fin.append (f ∘ v) z) := by
  let lifts : Fin r → N := fun j ↦ Classical.choose (hq (c j))
  have hlifts (j : Fin r) : q (lifts j) = c j := Classical.choose_spec (hq (c j))
  exact ⟨equivOfLifts hf he b c lifts hlifts, equivOfLifts_wedge hf he b c lifts hlifts⟩

/-- The determinant comparison of a short exact sequence of modules with finite bases.
The submodule factor comes first. Its value on wedges characterizes the map independently
of either finite basis. -/
def shortExactEquivOfBasis
    {R M N P : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [AddCommGroup P] [Module R P]
    {f : M →ₗ[R] N} {q : N →ₗ[R] P}
    (hf : Function.Injective f) (he : Function.Exact f q) (hq : Function.Surjective q)
    {n r : ℕ} (b : Module.Basis (Fin n) R M) (c : Module.Basis (Fin r) R P) :
    (⋀[R]^n M) ⊗[R] (⋀[R]^r P) ≃ₗ[R] ⋀[R]^(n + r) N :=
  (exact_canonical_adjunction f q hf he hq b c).choose

/-- The determinant comparison sends a wedge tensored with the wedge of quotient images
to the wedge of the submodule images followed by the arbitrary supplied lifts. -/
@[simp]
theorem shortExactEquivOfBasis_tmul_ιMulti
    {R M N P : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [AddCommGroup P] [Module R P]
    {f : M →ₗ[R] N} {q : N →ₗ[R] P}
    (hf : Function.Injective f) (he : Function.Exact f q) (hq : Function.Surjective q)
    {n r : ℕ} (b : Module.Basis (Fin n) R M) (c : Module.Basis (Fin r) R P)
    (v : Fin n → M) (z : Fin r → N) :
    shortExactEquivOfBasis hf he hq b c
      (exteriorPower.ιMulti R n v ⊗ₜ[R] exteriorPower.ιMulti R r (q ∘ z)) =
        exteriorPower.ιMulti R (n + r) (Fin.append (f ∘ v) z) :=
  (exact_canonical_adjunction f q hf he hq b c).choose_spec v z

section Uniqueness

variable {R M N P : Type*} [CommRing R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  [AddCommGroup P] [Module R P]
  {f : M →ₗ[R] N} {q : N →ₗ[R] P}
  (hf : Function.Injective f) (he : Function.Exact f q) (hq : Function.Surjective q)
  {n r : ℕ} (b : Module.Basis (Fin n) R M) (c : Module.Basis (Fin r) R P)

/-- The inverse determinant comparison separates the submodule wedge from the quotient wedge. -/
@[simp]
theorem shortExactEquivOfBasis_symm_ιMulti (v : Fin n → M) (z : Fin r → N) :
    (shortExactEquivOfBasis hf he hq b c).symm
        (exteriorPower.ιMulti R (n + r) (Fin.append (f ∘ v) z)) =
      exteriorPower.ιMulti R n v ⊗ₜ[R] exteriorPower.ιMulti R r (q ∘ z) :=
  (LinearEquiv.symm_apply_eq _).2
    (shortExactEquivOfBasis_tmul_ιMulti hf he hq b c v z).symm

/-- The wedge formula uniquely determines the determinant comparison. -/
theorem shortExactEquivOfBasis_unique
    (e : (⋀[R]^n M) ⊗[R] (⋀[R]^r P) ≃ₗ[R] ⋀[R]^(n + r) N)
    (h : ∀ (v : Fin n → M) (z : Fin r → N),
      e (exteriorPower.ιMulti R n v ⊗ₜ[R] exteriorPower.ιMulti R r (q ∘ z)) =
        exteriorPower.ιMulti R (n + r) (Fin.append (f ∘ v) z)) :
    e = shortExactEquivOfBasis hf he hq b c := by
  apply LinearEquiv.toLinearMap_injective
  apply TensorProduct.ext'
  intro x y
  obtain ⟨a, rfl⟩ := b.exists_smul_ιMulti_eq x
  obtain ⟨d, rfl⟩ := c.exists_smul_ιMulti_eq y
  let z : Fin r → N := fun i ↦ Classical.choose (hq (c i))
  have hz : q ∘ z = c := funext fun i ↦ Classical.choose_spec (hq (c i))
  have hbase :
      e (exteriorPower.ιMulti R n b ⊗ₜ[R] exteriorPower.ιMulti R r c) =
        shortExactEquivOfBasis hf he hq b c
          (exteriorPower.ιMulti R n b ⊗ₜ[R] exteriorPower.ιMulti R r c) := by
    rw [← hz, h, shortExactEquivOfBasis_tmul_ιMulti]
  simpa only [TensorProduct.smul_tmul_smul, map_smul, LinearEquiv.coe_coe]
    using congrArg (fun t ↦ (a * d) • t) hbase

/-- Changing either finite basis leaves the determinant comparison unchanged. -/
theorem shortExactEquivOfBasis_eq (b' : Module.Basis (Fin n) R M)
    (c' : Module.Basis (Fin r) R P) :
    shortExactEquivOfBasis hf he hq b' c' =
      shortExactEquivOfBasis hf he hq b c :=
  shortExactEquivOfBasis_unique hf he hq b c _
    (shortExactEquivOfBasis_tmul_ιMulti hf he hq b' c')

end Uniqueness

end TauCeti.exteriorPower
