/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.FDRep.Basic
public import TauCeti.RepresentationTheory.Invariants
import Mathlib.LinearAlgebra.PID

/-!
# Invariants of finite-dimensional representations

For a representation `W : FDRep R G` of a group `G` over a commutative ring `R`, equivariant
morphisms out of the monoidal unit `𝟙_ (FDRep R G)` identify `R`-linearly with the submodule
`Representation.invariants W.ρ` of `G`-invariant vectors by evaluation at `1 : R`
(`FDRep.tensorUnitHomEquivInvariants`). Under this equivalence, postcomposition with an
endomorphism `φ : W ⟶ W` corresponds to the restriction of `φ` to `Representation.invariants W.ρ`
(`FDRep.conj_tensorUnitHomEquivInvariants_rightComp`).

When `R = k` is a field, `G` is finite, and `|G|` is invertible in `k`, composing `φ` with the
averaging projection `Representation.averageMap W.ρ` extends that restriction by zero on a
complement, so the trace of postcomposition with `φ` on `𝟙_ (FDRep k G) ⟶ W` equals the group
average `|G|⁻¹ ∑ g : G, tr_W(φ ∘ ρ(g))` (`FDRep.trace_rightComp_tensorUnit`).

## Main definitions

* `FDRep.tensorUnitHomEquivInvariants`: the `R`-linear equivalence
  `(𝟙_ (FDRep R G) ⟶ W) ≃ₗ[R] Representation.invariants W.ρ`, built from
  `FDRep.forget₂HomLinearEquiv` and `Rep.trivialHomEquivInvariants`.

## Main results

* `FDRep.map_mem_invariants`: a morphism in `FDRep R G` carries `G`-invariant vectors to
  `G`-invariant vectors.
* `FDRep.conj_tensorUnitHomEquivInvariants_rightComp`: postcomposition on `𝟙_ (FDRep R G) ⟶ W`
  conjugates across `FDRep.tensorUnitHomEquivInvariants` to the restriction to invariants.
* `FDRep.trace_rightComp_tensorUnit`: when `|G|` is invertible in `k`, the trace of postcomposition
  with `φ : W ⟶ W` on `𝟙_ (FDRep k G) ⟶ W` equals `|G|⁻¹ ∑ g : G, tr_W(φ ∘ ρ(g))`.
-/

public section

open CategoryTheory MonoidalCategory

universe u v

namespace FDRep

section CommRing

variable {R : Type u} {G : Type v} [CommRing R] [Group G]

/-- An equivariant morphism in `FDRep R G` carries `G`-invariant vectors to `G`-invariant
vectors. -/
theorem map_mem_invariants {W W' : FDRep R G} (φ : W ⟶ W') {v : W}
    (hv : v ∈ Representation.invariants W.ρ) :
    φ.hom.hom.hom v ∈ Representation.invariants W'.ρ := fun g ↦ by
  rw [← LinearMap.comp_apply, ← hom_hom_hom_comm φ g, LinearMap.comp_apply, hv g]

/-- Morphisms out of the trivial representation `𝟙_ (FDRep R G)` identify `R`-linearly with the
submodule `Representation.invariants W.ρ` of `G`-invariant vectors by evaluation at `1 : R`. -/
noncomputable def tensorUnitHomEquivInvariants (W : FDRep R G) :
    (𝟙_ (FDRep R G) ⟶ W) ≃ₗ[R] Representation.invariants W.ρ :=
  (FDRep.forget₂HomLinearEquiv (𝟙_ (FDRep R G)) W).symm ≪≫ₗ
    Rep.trivialHomEquivInvariants ((forget₂ (FDRep R G) (Rep R G)).obj W)

/-- `tensorUnitHomEquivInvariants` evaluates a morphism out of `𝟙_ (FDRep R G)` at `1 : R`. -/
@[simp]
theorem coe_tensorUnitHomEquivInvariants_apply (W : FDRep R G) (f : 𝟙_ (FDRep R G) ⟶ W) :
    (tensorUnitHomEquivInvariants W f : W) = f.hom.hom.hom 1 :=
  -- `forget₂ (FDRep R G) (Rep R G)` sends `𝟙_ (FDRep R G)` definitionally to `Rep.trivial R G R`
  -- and keeps underlying linear maps.
  Rep.coe_trivialHomEquivInvariants_apply ((forget₂ (FDRep R G) (Rep R G)).obj W)
    ((forget₂ (FDRep R G) (Rep R G)).map f)

/-- The inverse of `tensorUnitHomEquivInvariants` sends an invariant vector `x` to
`LinearMap.toSpanSingleton R W x` on underlying modules. -/
@[simp]
theorem tensorUnitHomEquivInvariants_symm_apply_hom_hom_hom (W : FDRep R G)
    (x : Representation.invariants W.ρ) :
    ((tensorUnitHomEquivInvariants W).symm x).hom.hom.hom = LinearMap.toSpanSingleton R W x :=
  let W' : Rep R G := (forget₂ (FDRep R G) (Rep R G)).obj W
  have hg : ((forget₂ (FDRep R G) (Rep R G)).map ((tensorUnitHomEquivInvariants W).symm x) :
      Rep.trivial R G R ⟶ W') = (Rep.trivialHomEquivInvariants W').symm x :=
    -- `forget₂ (FDRep R G) (Rep R G)` sends `𝟙_ (FDRep R G)` definitionally to `Rep.trivial R G R`.
    FDRep.forget₂_map_forget₂HomLinearEquiv (𝟙_ (FDRep R G)) W
      ((Rep.trivialHomEquivInvariants W').symm x)
  LinearMap.ext fun r ↦
    (congrArg (fun φ : Rep.trivial R G R ⟶ W' ↦ (φ.hom r : W)) hg).trans
      ((Rep.trivialHomEquivInvariants_symm_apply_hom W' x r).trans
        (LinearMap.toSpanSingleton_apply R W x r).symm)

/-- Postcomposition with `φ : W ⟶ W` on `𝟙_ (FDRep R G) ⟶ W` corresponds under
`tensorUnitHomEquivInvariants` to the restriction of `φ` to `Representation.invariants W.ρ`. -/
theorem conj_tensorUnitHomEquivInvariants_rightComp {W : FDRep R G} (φ : W ⟶ W) :
    (tensorUnitHomEquivInvariants W).conj (Linear.rightComp R (𝟙_ (FDRep R G)) φ) =
      φ.hom.hom.hom.restrict (fun _ hv ↦ map_mem_invariants φ hv) := by
  ext ⟨v, hv⟩
  simp only [LinearMap.restrict_apply, LinearEquiv.conj_apply_apply, Linear.rightComp_apply,
    coe_tensorUnitHomEquivInvariants_apply, Action.comp_hom, FGModuleCat.hom_hom_comp,
    LinearMap.comp_apply, tensorUnitHomEquivInvariants_symm_apply_hom_hom_hom]
  exact congrArg φ.hom.hom.hom (LinearMap.toSpanSingleton_apply_one R W v)

end CommRing

section Trace

variable {k : Type u} {G : Type v} [Field k] [Group G] [Fintype G] [Invertible (Nat.card G : k)]

/-- When `|G|` is invertible in `k`, the trace of postcomposition with `φ : W ⟶ W` on
`𝟙_ (FDRep k G) ⟶ W` equals the group average `|G|⁻¹ ∑ g : G, tr_W(φ ∘ ρ(g))`. -/
theorem trace_rightComp_tensorUnit {W : FDRep k G} (φ : W ⟶ W) :
    LinearMap.trace k (𝟙_ (FDRep k G) ⟶ W) (Linear.rightComp k (𝟙_ (FDRep k G)) φ) =
      (Nat.card G : k)⁻¹ * ∑ g : G, LinearMap.trace k W (φ.hom.hom.hom ∘ₗ W.ρ g) := by
  have : Invertible (Fintype.card G : k) :=
    invertibleOfNonzero (Fintype.card_eq_nat_card (α := G) ▸ Invertible.ne_zero (Nat.card G : k))
  have hmem : ∀ w : W,
      (φ.hom.hom.hom ∘ₗ Representation.averageMap W.ρ) w ∈ Representation.invariants W.ρ :=
    fun w ↦ map_mem_invariants φ (Representation.averageMap_invariant W.ρ w)
  have hres : φ.hom.hom.hom.restrict (fun _ hv ↦ map_mem_invariants φ hv) =
      (φ.hom.hom.hom ∘ₗ Representation.averageMap W.ρ).restrict (fun w _ ↦ hmem w) := by
    ext ⟨v, hv⟩
    simp only [LinearMap.restrict_apply, LinearMap.comp_apply,
      Representation.averageMap_id W.ρ v hv]
  have havg : φ.hom.hom.hom ∘ₗ Representation.averageMap W.ρ =
      (Nat.card G : k)⁻¹ • ∑ g : G, (φ.hom.hom.hom ∘ₗ W.ρ g) := by
    rw [Representation.averageMap_eq_invOf_card_smul_norm, Representation.norm,
      LinearMap.comp_smul, invOf_eq_inv, Fintype.card_eq_nat_card]
    ext w
    simp [LinearMap.sum_apply]
  rw [← LinearMap.trace_conj' _ (tensorUnitHomEquivInvariants W),
    conj_tensorUnitHomEquivInvariants_rightComp, hres,
    LinearMap.trace_restrict_eq_of_forall_mem (Representation.invariants W.ρ) _ hmem, havg,
    map_smul, map_sum, smul_eq_mul]

end Trace

end FDRep
