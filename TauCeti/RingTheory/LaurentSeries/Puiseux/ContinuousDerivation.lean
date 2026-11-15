/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.LaurentSeries.ContinuousDerivation
public import TauCeti.RingTheory.LaurentSeries.Puiseux.Derivative

/-!
# Continuous derivations of Puiseux series

Let `K` be a field of characteristic zero and `P = puiseuxField K`, with its valuation topology
and the derivative `d/dt` of `TauCeti.puiseuxField.derivation K`. This file shows that every
continuous `K`-derivation `δ` of `P` into a Hausdorff `P`-module with continuous scalar
multiplication is `δ x = (dx/dt) • δ t`.

On level `n`, written in the variable `u = t ^ (1 / n)`, the derivation `δ` restricts to a
continuous derivation of `K⸨u⸩`, to which the classification
`Derivation.apply_eq_laurentSeriesDerivation_smul` of continuous derivations of Laurent series
applies. Comparing `δ` with `d/dt` at `t = u ^ n` then expresses `δ u` through `δ t`.

Applied to `x ↦ d/dt (ρ x)` for a continuous `K`-algebra endomorphism `ρ` of `P`, with `P` viewed
as a module over itself through `ρ`, the classification gives the chain rule
`d/dt (ρ x) = ρ (dx/dt) * d/dt (ρ t)`.

## Main results

* `Derivation.apply_eq_puiseuxFieldDerivation_smul`: continuous derivations of `P` are multiples
  of `d/dt`.
* `Derivation.continuous_iff_exists_apply_eq_puiseuxFieldDerivation_smul`: a derivation of `P` is
  continuous if and only if it is `x ↦ (dx/dt) • m` for some `m`.
* `TauCeti.puiseuxField.derivation_algHom_apply`: the chain rule for continuous `K`-algebra
  endomorphisms of `P`.
-/

public section

open HahnSeries
open scoped LaurentSeries

namespace TauCeti

namespace puiseuxField

variable {K : Type*} [Field K] [CharZero K]

section Module

variable {M : Type*} [AddCommGroup M] [Module (puiseuxField K) M] [Module K M]
  [IsScalarTower K (puiseuxField K) M] [TopologicalSpace M] [ContinuousSMul (puiseuxField K) M]
  [T2Space M]

omit [CharZero K] in
/-- On level `n`, a continuous derivation `δ` satisfies `δ (f (u)) = (D f) (u) • δ u`, where
`u = t ^ (1 / n)`. -/
private theorem apply_levelEmbedding_eq_smul (δ : Derivation K (puiseuxField K) M)
    (hδ : Continuous δ) (n : ℕ+) (f : K⸨X⸩) :
    δ (levelEmbedding K n f) =
      levelEmbedding K n (LaurentSeries.derivative K f) •
        δ (levelEmbedding K n (HahnSeries.single 1 1)) := by
  -- View `M` as a `K⸨X⸩`-module through the level-`n` embedding, and restrict `δ` to it.
  let : Module K⸨X⸩ M := Module.compHom M (levelEmbedding K n : K⸨X⸩ →+* puiseuxField K)
  have : IsScalarTower K K⸨X⸩ M := ⟨fun c f m ↦ by
    -- The scalar action of `K` on `K⸨X⸩` is multiplication by the image of `K`.
    have h : levelEmbedding K n (c • f) = c • levelEmbedding K n f := by
      rw [← C_mul_eq_smul, ← LaurentSeries.algebraMap_apply, map_mul, AlgHom.commutes,
        Algebra.smul_def]
    exact (congrArg (· • m) h).trans (smul_assoc _ _ _)⟩
  have : ContinuousSMul K⸨X⸩ M :=
    ⟨((continuous_levelEmbedding n).comp continuous_fst).smul continuous_snd⟩
  -- By construction of `Module.compHom`, `g • m` is `levelEmbedding K n g • m`; this closes the
  -- Leibniz rule for `δ'` and identifies the classification of `δ'` with the claim.
  let δ' : Derivation K K⸨X⸩ M :=
    { toLinearMap := δ.toLinearMap ∘ₗ (levelEmbedding K n).toLinearMap
      map_one_eq_zero' := by simp
      leibniz' f g := by simp [Derivation.leibniz]; rfl }
  have h := δ'.apply_eq_laurentSeriesDerivation_smul (hδ.comp (continuous_levelEmbedding n)) f
  rw [laurentSeriesDerivation_apply] at h
  exact h

/-- **Continuous derivations of Puiseux series.** A `K`-derivation `δ` of the Puiseux field into
a Hausdorff module with continuous scalar multiplication that is continuous for the valuation
topology satisfies `δ x = (dx/dt) • δ t`. -/
theorem _root_.Derivation.apply_eq_puiseuxFieldDerivation_smul
    (δ : Derivation K (puiseuxField K) M) (hδ : Continuous δ) (x : puiseuxField K) :
    δ x = derivation K x • δ (single K 1 1) := by
  obtain ⟨n, hn⟩ := exists_mem_range_levelEmbedding x
  obtain ⟨f, rfl⟩ := (AlgHom.mem_range _).mp hn
  -- Both `δ` and `d/dt` follow the chain rule on level `n`; comparing them at `t = u ^ n`
  -- expresses `δ u` through `δ t`.
  have hD := apply_levelEmbedding_eq_smul (derivation K) continuous_derivation n
  have ht := apply_levelEmbedding_eq_smul δ hδ n (HahnSeries.single (n : ℤ) 1)
  have ht' := hD (HahnSeries.single (n : ℤ) 1)
  rw [levelEmbedding_single_self] at ht ht'
  rw [derivation_single_one, smul_eq_mul] at ht'
  rw [apply_levelEmbedding_eq_smul δ hδ n f, hD f, ht, smul_eq_mul, mul_smul, smul_smul _ _ (δ _),
    mul_comm, ← ht', one_smul]

/-- A `K`-derivation of the Puiseux field into a Hausdorff module with continuous scalar
multiplication is continuous if and only if it is `x ↦ (dx/dt) • m` for some `m`. -/
theorem _root_.Derivation.continuous_iff_exists_apply_eq_puiseuxFieldDerivation_smul
    {δ : Derivation K (puiseuxField K) M} :
    Continuous δ ↔ ∃ m : M, ∀ x, δ x = derivation K x • m := by
  refine ⟨fun hδ ↦ ⟨_, δ.apply_eq_puiseuxFieldDerivation_smul hδ⟩, ?_⟩
  rintro ⟨m, hm⟩
  have h : (δ : puiseuxField K → M) = fun x ↦ derivation K x • m := funext hm
  rw [h]
  exact continuous_derivation.smul continuous_const

end Module

section ChainRule

/-- The Puiseux field as a module over itself through a `K`-algebra endomorphism `ρ`, with
`a • m = ρ a * m`. It is the target of the derivation `x ↦ d/dt (ρ x)`; a separate type avoids the
action of the Puiseux field on itself by multiplication. -/
private def Pullback (_ρ : puiseuxField K →ₐ[K] puiseuxField K) : Type _ := puiseuxField K

variable (ρ : puiseuxField K →ₐ[K] puiseuxField K)

private noncomputable instance : AddCommGroup (Pullback ρ) :=
  inferInstanceAs (AddCommGroup (puiseuxField K))

private noncomputable instance : Module K (Pullback ρ) :=
  inferInstanceAs (Module K (puiseuxField K))

private instance : TopologicalSpace (Pullback ρ) :=
  inferInstanceAs (TopologicalSpace (puiseuxField K))

private instance : T2Space (Pullback ρ) := inferInstanceAs (T2Space (puiseuxField K))

private noncomputable instance : Module (puiseuxField K) (Pullback ρ) :=
  Module.compHom (puiseuxField K) (ρ : puiseuxField K →+* puiseuxField K)

/-- The identification of the Puiseux field with `Pullback ρ`, as `K`-vector spaces. -/
private noncomputable def Pullback.equiv : puiseuxField K ≃ₗ[K] Pullback ρ := LinearEquiv.refl K _

omit [CharZero K] in
private theorem Pullback.equiv_symm_smul (a : puiseuxField K) (m : Pullback ρ) :
    (Pullback.equiv ρ).symm (a • m) = ρ a * (Pullback.equiv ρ).symm m :=
  (rfl)

omit [CharZero K] in
private theorem Pullback.continuous_equiv : Continuous (Pullback.equiv ρ) :=
  -- `Pullback ρ` carries the topology of the Puiseux field, and the identification is the identity.
  continuous_id

private instance : IsScalarTower K (puiseuxField K) (Pullback ρ) :=
  ⟨fun c a m ↦ (Pullback.equiv ρ).symm.injective <| by
    rw [Pullback.equiv_symm_smul, LinearEquiv.map_smul, Pullback.equiv_symm_smul,
      Algebra.smul_def c a, map_mul, AlgHom.commutes, mul_assoc, ← Algebra.smul_def]⟩

omit [CharZero K] in
private theorem continuousSMul_pullback (hρ : Continuous ρ) :
    ContinuousSMul (puiseuxField K) (Pullback ρ) :=
  ⟨(hρ.comp continuous_fst).mul (continuous_snd (X := puiseuxField K) (Y := puiseuxField K))⟩

/-- The derivation `x ↦ d/dt (ρ x)` into the Puiseux field viewed as a module through `ρ`. -/
private noncomputable def pullbackDerivation : Derivation K (puiseuxField K) (Pullback ρ) where
  toLinearMap := (Pullback.equiv ρ).toLinearMap ∘ₗ (derivation K).toLinearMap ∘ₗ ρ.toLinearMap
  map_one_eq_zero' := by simp
  leibniz' a b := (Pullback.equiv ρ).symm.injective <| by
    simp [Pullback.equiv_symm_smul, Derivation.leibniz]

/-- **The chain rule for continuous endomorphisms.** A continuous `K`-algebra endomorphism `ρ`
of the Puiseux field satisfies `d/dt (ρ x) = ρ (dx/dt) * d/dt (ρ t)`. -/
theorem derivation_algHom_apply (hρ : Continuous ρ) (x : puiseuxField K) :
    derivation K (ρ x) = ρ (derivation K x) * derivation K (ρ (single K 1 1)) := by
  have := continuousSMul_pullback ρ hρ
  -- Classify the continuous derivation `x ↦ d/dt (ρ x)`, whose scalar action is `ρ a * m`.
  have h := congrArg (Pullback.equiv ρ).symm <|
    (pullbackDerivation ρ).apply_eq_puiseuxFieldDerivation_smul
      ((Pullback.continuous_equiv ρ).comp (continuous_derivation.comp hρ)) x
  simpa [Pullback.equiv_symm_smul, pullbackDerivation] using h

end ChainRule

end puiseuxField

end TauCeti
