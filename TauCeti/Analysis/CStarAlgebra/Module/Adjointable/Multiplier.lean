/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Module.Spaces.PointwiseConvergenceCLM
public import TauCeti.Analysis.CStarAlgebra.Ideal
public import TauCeti.Analysis.CStarAlgebra.Module.Adjointable.Self
public import TauCeti.Analysis.CStarAlgebra.Multiplier.Strict.Topology
import TauCeti.Analysis.CStarAlgebra.Module.Factorization

/-!
# Adjointable operators as multipliers of the module-compact operators

For a complete Hilbert C⋆-module `E` over a possibly nonunital C⋆-algebra `A`, this file
identifies the adjointable endomorphisms `L_A(E) = TauCeti.AdjointableMap A E E` with the
multiplier algebra `𝓜(ℂ, K_A(E))` of the module-compact ideal
`K_A(E) = (compactOperatorIdeal A E).toNonUnitalStarSubalgebra`, and identifies the induced strict
topology on norm-bounded sets with strong-* convergence on `E`.

## Overview

1. **Nondegeneracy and approximate units of `K_A(E)`.** By the separation lemmas in
   `TauCeti.Analysis.CStarAlgebra.Module.Adjointable.Compact`
   (`eq_of_forall_compactOperator_apply_eq`, `eq_of_forall_comp_compactOperator_eq`,
   `eq_of_forall_compactOperator_comp_eq`), `K_A(E)` acts nondegenerately without completeness.
   When `E` is complete, the special factorization `x = ⟪y, y⟫_A • y`
   (`CStarModule.existsUnique_inner_self_smul_eq`) exhibits every vector `x : E` as `θ_{y, y} y`
   (`exists_rankOne_self_apply_eq`), hence as `k y` for some `k : K_A(E)`
   (`exists_compactOperatorIdeal_apply_eq`). Consequently, along any approximate unit `e` of
   `K_A(E)` (with no norm bound assumed), `e x → x` for every `x : E`
   (`tendsto_compactOperatorIdeal_apply_of_isApproximateUnit`).
2. **The multiplier isomorphism `L_A(E) ≃⋆ₐ[ℂ] 𝓜(ℂ, K_A(E))`.** Left and right
   multiplication inside `L_A(E)` embed `L_A(E)` into `𝓜(ℂ, K_A(E))` via
   `NonUnitalStarSubalgebra.multiplierHom`. Conversely, for `m : 𝓜(ℂ, K_A(E))`, the map
   `x ↦ m.fst k_x y_x` (where `k_x y_x = x`) is well-defined independently of the factorization
   and has adjoint `x ↦ (star m).fst k_x y_x`, yielding an isometric unital `⋆`-isomorphism
   `TauCeti.AdjointableMap.multiplierStarAlgEquiv A E : L_A(E) ≃⋆ₐ[ℂ] 𝓜(ℂ, K_A(E))`.
   On the right self-module `A = Bᵐᵒᵖ` (`E = B`), this agrees with
   `multiplierMulOppositeStarAlgEquiv` transported along `compactOperatorMulOppositeStarAlgEquiv`
   (`multiplierMulOppositeStarAlgEquiv_trans_congr`).
3. **Strict and strong-* topologies.** Transporting the strict topology from `𝓜ₛ(ℂ, K_A(E))`
   via `multiplierStrictStarAlgEquiv A E`, strict convergence globally implies pointwise norm
   convergence of both `T` and `T.adjoint` on `E`
   (`continuous_toPointwiseConvergenceCLM_multiplierStrictStarAlgEquiv_symm`,
   `continuous_toPointwiseConvergenceCLM_adjoint_multiplierStrictStarAlgEquiv_symm`). On
   norm-bounded filters and bounded sets, the two notions coincide
   (`tendsto_multiplierStrictStarAlgEquiv_iff_of_eventually_norm_le`,
   `induced_multiplierStrictStarAlgEquiv_eq_induced_pointwiseConvergenceCLM_of_isBounded`).

## References

* Iain Raeburn and Dana P. Williams, *Morita Equivalence and Continuous-Trace C⋆-Algebras*,
  Proposition 2.31 and Corollary 2.54.
* E. Christopher Lance, *Hilbert C⋆-Modules: A Toolkit for Operator Algebraists*, Chapter 2,
  Proposition 2.2.
-/

public section

open CStarModule Filter Topology
open scoped MultiplierAlgebra

namespace TauCeti

namespace AdjointableMap

/-! ### Nondegeneracy and approximate-unit action of `K_A(E)` -/

section Nondegenerate

variable {A E : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul A E] [CStarModule A E] [CompleteSpace E]

/-- In a complete Hilbert C⋆-module `E`, every vector `x` has the form `θ_{y, y} y` for some
`y : E`, by the special factorization `x = ⟪y, y⟫_A • y`. -/
theorem exists_rankOne_self_apply_eq (x : E) : ∃ y : E, rankOne A y y y = x := by
  obtain ⟨y, hy, -⟩ := CStarModule.existsUnique_inner_self_smul_eq (A := A) x
  exact ⟨y, by simpa [rankOne_apply] using hy⟩

/-- Every vector `x : E` in a complete Hilbert C⋆-module lies in the range of some element of
`K_A(E)`: `x = k y` with `k : compactOperatorIdeal A E` and `y : E`. -/
theorem exists_compactOperatorIdeal_apply_eq (x : E) :
    ∃ (k : compactOperatorIdeal A E) (y : E), (k : AdjointableMap A E E) y = x := by
  obtain ⟨y, hy⟩ := exists_rankOne_self_apply_eq (A := A) x
  exact ⟨⟨rankOne A y y,
    mem_compactOperatorIdeal.mpr (rankOne_mem_compactOperator y y)⟩, y, hy⟩

/-- The union of the ranges of all module-compact operators on a complete Hilbert C⋆-module `E` is
all of `E`. -/
@[simp]
theorem iUnion_range_compactOperatorIdeal_eq_univ :
    (⋃ k : compactOperatorIdeal A E, Set.range ((k : AdjointableMap A E E) : E → E)) =
      Set.univ :=
  Set.eq_univ_iff_forall.mpr fun x ↦
    let ⟨k, y, hy⟩ := exists_compactOperatorIdeal_apply_eq (A := A) x
    Set.mem_iUnion.mpr ⟨k, y, hy⟩

end Nondegenerate

/-! ### The multiplier algebra isomorphism `L_A(E) ≃⋆ₐ[ℂ] 𝓜(ℂ, K_A(E))` -/

section MultiplierIso

variable {A E : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul A E] [CStarModule A E] [CompleteSpace E]

private theorem mem_compactOperatorIdeal_toNonUnitalStarSubalgebra {T : AdjointableMap A E E} :
    T ∈ (compactOperatorIdeal A E).toNonUnitalStarSubalgebra ↔ T ∈ compactOperator A E E :=
  (TwoSidedIdeal.mem_toNonUnitalStarSubalgebra _).trans mem_compactOperatorIdeal

private theorem exists_compactOperatorIdeal_toNonUnitalStarSubalgebra_apply_eq (x : E) :
    ∃ (k : (compactOperatorIdeal A E).toNonUnitalStarSubalgebra) (y : E),
      (k : AdjointableMap A E E) y = x := by
  obtain ⟨k', y, hk'⟩ := exists_compactOperatorIdeal_apply_eq (A := A) x
  exact ⟨(compactOperatorIdeal A E).toNonUnitalStarSubalgebraEquiv k', y, by
    rw [TwoSidedIdeal.coe_toNonUnitalStarSubalgebraEquiv_apply, hk']⟩

/-- Centralizer evaluation identity: `u ((m.fst k) y) = (m.snd u) (k y)`. -/
private theorem coe_apply_fst_apply
    (m : 𝓜(ℂ, (compactOperatorIdeal A E).toNonUnitalStarSubalgebra))
    (u k : (compactOperatorIdeal A E).toNonUnitalStarSubalgebra) (y : E) :
    (u : AdjointableMap A E E) ((m.fst k : AdjointableMap A E E) y) =
      (m.snd u : AdjointableMap A E E) ((k : AdjointableMap A E E) y) := by
  calc (u : AdjointableMap A E E) ((m.fst k : AdjointableMap A E E) y)
      = (((u * m.fst k : (compactOperatorIdeal A E).toNonUnitalStarSubalgebra) :
          AdjointableMap A E E)) y := by simp [mul_apply_eq_comp]
    _ = (((m.snd u * k : (compactOperatorIdeal A E).toNonUnitalStarSubalgebra) :
          AdjointableMap A E E)) y := by rw [m.central u k]
    _ = (m.snd u : AdjointableMap A E E) ((k : AdjointableMap A E E) y) := by
        simp [mul_apply_eq_comp]

/-- Action of a multiplier `m : 𝓜(ℂ, K_A(E))` on `x : E`, defined by choosing a factorization
`x = k y` with `k : K_A(E)` and setting `m x := (m.fst k) y`. -/
private noncomputable def multiplierApply
    (m : 𝓜(ℂ, (compactOperatorIdeal A E).toNonUnitalStarSubalgebra)) (x : E) : E :=
  let h := exists_compactOperatorIdeal_toNonUnitalStarSubalgebra_apply_eq (A := A) x
  ((m.fst h.choose : AdjointableMap A E E) h.choose_spec.choose)

private theorem multiplierApply_eq_of_apply_eq
    (m : 𝓜(ℂ, (compactOperatorIdeal A E).toNonUnitalStarSubalgebra))
    {k₁ k₂ : (compactOperatorIdeal A E).toNonUnitalStarSubalgebra} {y₁ y₂ : E}
    (h : (k₁ : AdjointableMap A E E) y₁ = (k₂ : AdjointableMap A E E) y₂) :
    ((m.fst k₁ : AdjointableMap A E E) y₁) = ((m.fst k₂ : AdjointableMap A E E) y₂) := by
  refine eq_of_forall_compactOperator_apply_eq (A := A) fun u hu ↦ ?_
  let u' : (compactOperatorIdeal A E).toNonUnitalStarSubalgebra :=
    ⟨u, mem_compactOperatorIdeal_toNonUnitalStarSubalgebra.mpr hu⟩
  simpa only [u'] using
    (coe_apply_fst_apply m u' k₁ y₁).trans
      ((congrArg (m.snd u' : AdjointableMap A E E) h).trans (coe_apply_fst_apply m u' k₂ y₂).symm)

private theorem multiplierApply_apply_compactOperator
    (m : 𝓜(ℂ, (compactOperatorIdeal A E).toNonUnitalStarSubalgebra))
    (k : (compactOperatorIdeal A E).toNonUnitalStarSubalgebra) (y : E) :
    multiplierApply m ((k : AdjointableMap A E E) y) = (m.fst k : AdjointableMap A E E) y :=
  let h := exists_compactOperatorIdeal_toNonUnitalStarSubalgebra_apply_eq (A := A)
    ((k : AdjointableMap A E E) y)
  multiplierApply_eq_of_apply_eq m h.choose_spec.choose_spec

private theorem isAdjointPair_multiplierApply
    (m : 𝓜(ℂ, (compactOperatorIdeal A E).toNonUnitalStarSubalgebra)) (x₁ x₂ : E) :
    inner A (multiplierApply m x₁) x₂ = inner A x₁ (multiplierApply (star m) x₂) := by
  obtain ⟨k₁, y₁, hk₁⟩ :=
    exists_compactOperatorIdeal_toNonUnitalStarSubalgebra_apply_eq (A := A) x₁
  obtain ⟨k₂, y₂, hk₂⟩ :=
    exists_compactOperatorIdeal_toNonUnitalStarSubalgebra_apply_eq (A := A) x₂
  rw [← hk₁, ← hk₂,
    multiplierApply_apply_compactOperator m k₁ y₁,
    multiplierApply_apply_compactOperator (star m) k₂ y₂]
  have hcent : star k₂ * m.fst k₁ = star ((star m).fst k₂) * k₁ := by
    simpa [DoubleCentralizer.star_fst] using (m.central (star k₂) k₁).symm
  have hcoe : (star (k₂ : AdjointableMap A E E) * (m.fst k₁ : AdjointableMap A E E)) =
      (star ((star m).fst k₂ : AdjointableMap A E E) * (k₁ : AdjointableMap A E E)) :=
    congrArg Subtype.val hcent
  calc inner A ((m.fst k₁ : AdjointableMap A E E) y₁) ((k₂ : AdjointableMap A E E) y₂)
      = inner A ((star (k₂ : AdjointableMap A E E) *
          (m.fst k₁ : AdjointableMap A E E)) y₁) y₂ := by
        rw [mul_apply_eq_comp, star_eq_adjoint, adjoint_inner_left]
    _ = inner A ((star ((star m).fst k₂ : AdjointableMap A E E) *
          (k₁ : AdjointableMap A E E)) y₁) y₂ := by
        rw [hcoe]
    _ = inner A ((k₁ : AdjointableMap A E E) y₁)
          (((star m).fst k₂ : AdjointableMap A E E) y₂) := by
        rw [mul_apply_eq_comp, star_eq_adjoint, adjoint_inner_left]

private noncomputable def ofMultiplier
    (m : 𝓜(ℂ, (compactOperatorIdeal A E).toNonUnitalStarSubalgebra)) :
    AdjointableMap A E E :=
  AdjointableMap.ofAdjointPair (multiplierApply m) (multiplierApply (star m))
    (isAdjointPair_multiplierApply m)

private theorem ofMultiplier_apply_compactOperator
    (m : 𝓜(ℂ, (compactOperatorIdeal A E).toNonUnitalStarSubalgebra))
    (k : (compactOperatorIdeal A E).toNonUnitalStarSubalgebra) (y : E) :
    ofMultiplier m ((k : AdjointableMap A E E) y) = (m.fst k : AdjointableMap A E E) y := by
  rw [ofMultiplier, ofAdjointPair_apply, multiplierApply_apply_compactOperator]

variable (A E) in
/-- **Multiplier representation of adjointable operators** (Raeburn–Williams, Corollary 2.54):
for any complete Hilbert C⋆-module `E` over `A`, `L_A(E) = AdjointableMap A E E` is unital
`⋆`-isomorphic to the multiplier algebra `𝓜(ℂ, K_A(E))` of the module-compact ideal
`K_A(E) = (compactOperatorIdeal A E).toNonUnitalStarSubalgebra`. Under this isomorphism,
`T : L_A(E)` corresponds to the double centralizer `(k ↦ T * k, k ↦ k * T)`, and the canonical
inclusion `K_A(E) → 𝓜(ℂ, K_A(E))` corresponds to `K_A(E) ↪ L_A(E)`.
It is isometric (`norm_multiplierStarAlgEquiv`). -/
noncomputable def multiplierStarAlgEquiv :
    AdjointableMap A E E ≃⋆ₐ[ℂ]
      𝓜(ℂ, (compactOperatorIdeal A E).toNonUnitalStarSubalgebra) :=
  let I := (compactOperatorIdeal A E).toNonUnitalStarSubalgebra
  let ψ := I.multiplierHom (compactOperatorIdeal A E).mul_mem_toNonUnitalStarSubalgebra
  { toFun := ψ
    invFun := ofMultiplier
    left_inv T := ext fun x ↦ by
      obtain ⟨k, y, hk⟩ :=
        exists_compactOperatorIdeal_toNonUnitalStarSubalgebra_apply_eq (A := A) x
      rw [← hk, ofMultiplier_apply_compactOperator]
      dsimp only [ψ]
      rw [I.coe_multiplierHom_fst_apply, mul_apply_eq_comp]
    right_inv m := DoubleCentralizer.ext_fst fun k ↦ Subtype.ext <| ext fun y ↦ by
      rw [I.coe_multiplierHom_fst_apply, mul_apply_eq_comp, ofMultiplier_apply_compactOperator]
    map_mul' := map_mul ψ
    map_add' := map_add ψ
    map_smul' := map_smul ψ
    map_star' := map_star ψ }

/-- The left centralizer of `multiplierStarAlgEquiv A E T` acts on `K_A(E)` by left
multiplication by `T`. -/
@[simp]
theorem coe_multiplierStarAlgEquiv_fst (T : AdjointableMap A E E)
    (k : (compactOperatorIdeal A E).toNonUnitalStarSubalgebra) :
    ((multiplierStarAlgEquiv A E T).fst k : AdjointableMap A E E) =
      T * (k : AdjointableMap A E E) :=
  (compactOperatorIdeal A E).toNonUnitalStarSubalgebra.coe_multiplierHom_fst_apply _ T k

/-- The right centralizer of `multiplierStarAlgEquiv A E T` acts on `K_A(E)` by right
multiplication by `T`. -/
@[simp]
theorem coe_multiplierStarAlgEquiv_snd (T : AdjointableMap A E E)
    (k : (compactOperatorIdeal A E).toNonUnitalStarSubalgebra) :
    ((multiplierStarAlgEquiv A E T).snd k : AdjointableMap A E E) =
      (k : AdjointableMap A E E) * T :=
  (compactOperatorIdeal A E).toNonUnitalStarSubalgebra.coe_multiplierHom_snd_apply _ T k

/-- On `K_A(E)`, `multiplierStarAlgEquiv A E` agrees with the canonical inclusion
`K_A(E) → 𝓜(ℂ, K_A(E))`. -/
@[simp]
theorem multiplierStarAlgEquiv_coe (k : (compactOperatorIdeal A E).toNonUnitalStarSubalgebra) :
    multiplierStarAlgEquiv A E (k : AdjointableMap A E E) =
      (k : 𝓜(ℂ, (compactOperatorIdeal A E).toNonUnitalStarSubalgebra)) :=
  (compactOperatorIdeal A E).toNonUnitalStarSubalgebra.multiplierHom_coe
    (compactOperatorIdeal A E).mul_mem_toNonUnitalStarSubalgebra k

/-- The inverse of `multiplierStarAlgEquiv A E` sends the canonical image of `k : K_A(E)` in
`𝓜(ℂ, K_A(E))` back to `(k : L_A(E))`. -/
@[simp]
theorem multiplierStarAlgEquiv_symm_coe
    (k : (compactOperatorIdeal A E).toNonUnitalStarSubalgebra) :
    (multiplierStarAlgEquiv A E).symm
        (k : 𝓜(ℂ, (compactOperatorIdeal A E).toNonUnitalStarSubalgebra)) =
      (k : AdjointableMap A E E) := by
  rw [← multiplierStarAlgEquiv_coe, StarAlgEquiv.symm_apply_apply]

/-- Multiplying `(multiplierStarAlgEquiv A E).symm m` on the right by `k : K_A(E)` yields
`(m.fst k : L_A(E))`. -/
@[simp]
theorem multiplierStarAlgEquiv_symm_mul_coe
    (m : 𝓜(ℂ, (compactOperatorIdeal A E).toNonUnitalStarSubalgebra))
    (k : (compactOperatorIdeal A E).toNonUnitalStarSubalgebra) :
    (multiplierStarAlgEquiv A E).symm m * (k : AdjointableMap A E E) =
      (m.fst k : AdjointableMap A E E) := by
  rw [← coe_multiplierStarAlgEquiv_fst, StarAlgEquiv.apply_symm_apply]

/-- Multiplying `(multiplierStarAlgEquiv A E).symm m` on the left by `k : K_A(E)` yields
`(m.snd k : L_A(E))`. -/
@[simp]
theorem coe_mul_multiplierStarAlgEquiv_symm
    (k : (compactOperatorIdeal A E).toNonUnitalStarSubalgebra)
    (m : 𝓜(ℂ, (compactOperatorIdeal A E).toNonUnitalStarSubalgebra)) :
    (k : AdjointableMap A E E) * (multiplierStarAlgEquiv A E).symm m =
      (m.snd k : AdjointableMap A E E) := by
  rw [← coe_multiplierStarAlgEquiv_snd, StarAlgEquiv.apply_symm_apply]

/-- Evaluating `(multiplierStarAlgEquiv A E).symm m` on a factored vector `k y` gives
`(m.fst k : L_A(E)) y`. -/
@[simp]
theorem multiplierStarAlgEquiv_symm_apply_coe_apply
    (m : 𝓜(ℂ, (compactOperatorIdeal A E).toNonUnitalStarSubalgebra))
    (k : (compactOperatorIdeal A E).toNonUnitalStarSubalgebra) (y : E) :
    (multiplierStarAlgEquiv A E).symm m ((k : AdjointableMap A E E) y) =
      (m.fst k : AdjointableMap A E E) y := by
  rw [← mul_apply_eq_comp, multiplierStarAlgEquiv_symm_mul_coe]

/-- The adjoint of `(multiplierStarAlgEquiv A E).symm m` is
`(multiplierStarAlgEquiv A E).symm (star m)`. -/
@[simp]
theorem adjoint_multiplierStarAlgEquiv_symm
    (m : 𝓜(ℂ, (compactOperatorIdeal A E).toNonUnitalStarSubalgebra)) :
    ((multiplierStarAlgEquiv A E).symm m).adjoint = (multiplierStarAlgEquiv A E).symm (star m) := by
  rw [← star_eq_adjoint, ← map_star]

/-- Along any right-multiplication approximate unit `l` of
`(compactOperatorIdeal A E).toNonUnitalStarSubalgebra`, the compact operators `m.fst e` converge
pointwise on `E` to `(multiplierStarAlgEquiv A E).symm m`. -/
theorem tendsto_fst_apply_multiplierStarAlgEquiv_symm_apply_of_tendsto_mul_right
    {l : Filter (compactOperatorIdeal A E).toNonUnitalStarSubalgebra}
    (hl : ∀ k : (compactOperatorIdeal A E).toNonUnitalStarSubalgebra, Tendsto (· * k) l (𝓝 k))
    (m : 𝓜(ℂ, (compactOperatorIdeal A E).toNonUnitalStarSubalgebra)) (x : E) :
    Tendsto (fun e : (compactOperatorIdeal A E).toNonUnitalStarSubalgebra ↦
        ((m.fst e : AdjointableMap A E E) x)) l
      (𝓝 ((multiplierStarAlgEquiv A E).symm m x)) := by
  obtain ⟨k, y, hk⟩ := exists_compactOperatorIdeal_toNonUnitalStarSubalgebra_apply_eq (A := A) x
  rw [← hk]
  have heval : Continuous fun e : (compactOperatorIdeal A E).toNonUnitalStarSubalgebra ↦
      ((m.fst e : AdjointableMap A E E) y) :=
    ((continuous_apply y).comp continuous_subtypeVal).comp m.fst.continuous
  rw [multiplierStarAlgEquiv_symm_apply_coe_apply]
  refine ((heval.tendsto k).comp (hl k)).congr fun e ↦ ?_
  rw [Function.comp_apply, DoubleCentralizer.fst_mul]
  simp [mul_apply_eq_comp]

private theorem continuous_toNonUnitalStarSubalgebraEquiv :
    Continuous (compactOperatorIdeal A E).toNonUnitalStarSubalgebraEquiv :=
  continuous_induced_rng.mpr <| continuous_subtypeVal.congr fun u ↦
    ((compactOperatorIdeal A E).coe_toNonUnitalStarSubalgebraEquiv_apply u).symm

/-- Along any approximate unit `l` of `K_A(E)`, `e x → x` in `E` for every `x : E`
(Lance, Proposition 2.2). -/
theorem tendsto_compactOperatorIdeal_apply_of_isApproximateUnit
    {l : Filter (compactOperatorIdeal A E)} (hl : l.IsApproximateUnit) (x : E) :
    Tendsto (fun e : compactOperatorIdeal A E ↦ (e : AdjointableMap A E E) x) l (𝓝 x) := by
  let eqv := (compactOperatorIdeal A E).toNonUnitalStarSubalgebraEquiv
  have hlim := (tendsto_fst_apply_multiplierStarAlgEquiv_symm_apply_of_tendsto_mul_right
    (hl.map eqv.toNonUnitalStarAlgHom continuous_toNonUnitalStarSubalgebraEquiv
      eqv.surjective).tendsto_mul_right 1 x).comp tendsto_map
  rw [map_one, one_def, id_apply] at hlim
  exact hlim.congr fun u ↦ by
    simp only [Function.comp_apply, StarAlgEquiv.toNonUnitalStarAlgHom_apply,
      DoubleCentralizer.one_fst, one_apply_eq_self, eqv,
      TwoSidedIdeal.coe_toNonUnitalStarSubalgebraEquiv_apply]

/-- Along the canonical increasing approximate unit of `K_A(E)`, `e x → x` for every `x : E`. -/
theorem tendsto_approximateUnit_compactOperatorIdeal_apply (x : E) :
    Tendsto (fun e : compactOperatorIdeal A E ↦ (e : AdjointableMap A E E) x)
      (CStarAlgebra.approximateUnit (compactOperatorIdeal A E)) (𝓝 x) :=
  tendsto_compactOperatorIdeal_apply_of_isApproximateUnit
    (CStarAlgebra.increasingApproximateUnit (compactOperatorIdeal A E)).toIsApproximateUnit x

/-- Along any approximate unit `l` of `K_A(E)` and for any `T : L_A(E, F)`, `(T ∘ e) x → T x`
in `F` for every `x : E`. -/
theorem tendsto_comp_compactOperatorIdeal_apply_of_isApproximateUnit
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul A F] [CStarModule A F]
    {l : Filter (compactOperatorIdeal A E)} (hl : l.IsApproximateUnit)
    (T : AdjointableMap A E F) (x : E) :
    Tendsto (fun e : compactOperatorIdeal A E ↦ (T.comp (e : AdjointableMap A E E)) x) l
      (𝓝 (T x)) := by
  refine ((T.continuous.tendsto x).comp
    (tendsto_compactOperatorIdeal_apply_of_isApproximateUnit hl x)).congr fun e ↦ ?_
  simp [comp_apply]

/-- Along any approximate unit `l` of `K_A(E)` and for any `T : L_A(E)`, `(e * T) x → T x`
in `E` for every `x : E`. -/
theorem tendsto_compactOperatorIdeal_mul_apply_of_isApproximateUnit
    {l : Filter (compactOperatorIdeal A E)} (hl : l.IsApproximateUnit)
    (T : AdjointableMap A E E) (x : E) :
    Tendsto (fun e : compactOperatorIdeal A E ↦ ((e : AdjointableMap A E E) * T) x) l
      (𝓝 (T x)) := by
  refine (tendsto_compactOperatorIdeal_apply_of_isApproximateUnit hl (T x)).congr fun e ↦ ?_
  simp [mul_apply_eq_comp]

/-- `L_A(E) ≃⋆ₐ[ℂ] 𝓜(ℂ, K_A(E))` is isometric. -/
@[simp]
theorem norm_multiplierStarAlgEquiv (T : AdjointableMap A E E) :
    ‖multiplierStarAlgEquiv A E T‖ = ‖T‖ :=
  StarAlgEquiv.norm_map (multiplierStarAlgEquiv A E) T

/-- Under `L_A(E) ≃⋆ₐ[ℂ] 𝓜(ℂ, K_A(E))`, the module-compact operators `K_A(E)`
correspond to the canonical image of `K_A(E)` in its multiplier algebra. -/
theorem mem_compactOperator_iff_exists_coe_eq_multiplierStarAlgEquiv
    {T : AdjointableMap A E E} :
    T ∈ compactOperator A E E ↔
      ∃ k : (compactOperatorIdeal A E).toNonUnitalStarSubalgebra,
        (k : 𝓜(ℂ, (compactOperatorIdeal A E).toNonUnitalStarSubalgebra)) =
          multiplierStarAlgEquiv A E T := by
  refine ⟨fun hT ↦ ⟨⟨T, mem_compactOperatorIdeal_toNonUnitalStarSubalgebra.mpr hT⟩, ?_⟩, ?_⟩
  · exact (multiplierStarAlgEquiv_coe _).symm
  · rintro ⟨k, hk⟩
    have hT : T = (k : AdjointableMap A E E) :=
      (multiplierStarAlgEquiv A E).injective (hk.symm.trans (multiplierStarAlgEquiv_coe k).symm)
    rw [hT]
    exact mem_compactOperatorIdeal_toNonUnitalStarSubalgebra.mp k.property

/-- Compatibility with the right self-module (`Adjointable.Self`): on `E = A` as a right module
`Aᵐᵒᵖ`, `L_A(A) ≃⋆ₐ[ℂ] 𝓜(ℂ, A)` followed by `DoubleCentralizer.congr` along
`A ≃⋆ₐ[ℂ] K_A(A)` equals `multiplierStarAlgEquiv Aᵐᵒᵖ A`. -/
theorem multiplierMulOppositeStarAlgEquiv_trans_congr (A : Type*) [NonUnitalCStarAlgebra A]
    [PartialOrder A] [StarOrderedRing A] :
    (multiplierMulOppositeStarAlgEquiv A).trans
        (DoubleCentralizer.congr
          ((compactOperatorMulOppositeStarAlgEquiv A).trans
            (compactOperatorIdeal Aᵐᵒᵖ A).toNonUnitalStarSubalgebraEquiv)) =
      multiplierStarAlgEquiv Aᵐᵒᵖ A := by
  let e : A ≃⋆ₐ[ℂ] (compactOperatorIdeal Aᵐᵒᵖ A).toNonUnitalStarSubalgebra :=
    (compactOperatorMulOppositeStarAlgEquiv A).trans
      (compactOperatorIdeal Aᵐᵒᵖ A).toNonUnitalStarSubalgebraEquiv
  have he_apply (a : A) : (e a : AdjointableMap Aᵐᵒᵖ A A) = mulLeft A a := by
    dsimp only [e]
    rw [StarAlgEquiv.trans_apply, TwoSidedIdeal.coe_toNonUnitalStarSubalgebraEquiv_apply,
      coe_compactOperatorMulOppositeStarAlgEquiv_apply]
  ext T : 1
  refine DoubleCentralizer.ext_fst fun k ↦ Subtype.ext ?_
  have ha : mulLeft A (e.symm k) = (k : AdjointableMap Aᵐᵒᵖ A A) := by simp [← he_apply]
  calc (((multiplierMulOppositeStarAlgEquiv A).trans (DoubleCentralizer.congr e) T).fst k :
          AdjointableMap Aᵐᵒᵖ A A)
      = mulLeft A (T (e.symm k)) := by
        rw [StarAlgEquiv.trans_apply, DoubleCentralizer.congr_apply_fst, he_apply,
          multiplierMulOppositeStarAlgEquiv_fst, toContinuousLinearMap_apply]
    _ = T * (k : AdjointableMap Aᵐᵒᵖ A A) := by
        rw [← ha]; ext x
        simpa [mul_apply_eq_comp, MulOpposite.smul_eq_mul_unop] using
          (T.map_smul_coeff (MulOpposite.op x) (e.symm k)).symm
    _ = ((multiplierStarAlgEquiv Aᵐᵒᵖ A T).fst k : AdjointableMap Aᵐᵒᵖ A A) := by
        rw [coe_multiplierStarAlgEquiv_fst]

end MultiplierIso

/-! ### Strict topology on `L_A(E)` and strong-* convergence -/

section StrictTopology

section Complete

/-- The `⋆`-isomorphism `L_A(E) ≃⋆ₐ[ℂ] 𝓜ₛ(ℂ, K_A(E))` equipping `L_A(E)` with the
strict topology of `𝓜ₛ(ℂ, K_A(E))`. -/
noncomputable def multiplierStrictStarAlgEquiv (A E : Type*) [NonUnitalCStarAlgebra A]
    [PartialOrder A] [StarOrderedRing A] [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul A E]
    [CStarModule A E] [CompleteSpace E] :
    AdjointableMap A E E ≃⋆ₐ[ℂ]
      𝓜ₛ(ℂ, (compactOperatorIdeal A E).toNonUnitalStarSubalgebra) :=
  (multiplierStarAlgEquiv A E).trans DoubleCentralizerStrict.starAlgEquiv.symm

variable {A E : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul A E] [CStarModule A E] [CompleteSpace E]

@[simp]
theorem toDoubleCentralizer_multiplierStrictStarAlgEquiv (T : AdjointableMap A E E) :
    (multiplierStrictStarAlgEquiv A E T).toDoubleCentralizer = multiplierStarAlgEquiv A E T :=
  (rfl)

theorem multiplierStrictStarAlgEquiv_symm_apply
    (m : 𝓜ₛ(ℂ, (compactOperatorIdeal A E).toNonUnitalStarSubalgebra)) :
    (multiplierStrictStarAlgEquiv A E).symm m =
      (multiplierStarAlgEquiv A E).symm m.toDoubleCentralizer :=
  (rfl)

@[simp]
theorem multiplierStrictStarAlgEquiv_coe
    (k : (compactOperatorIdeal A E).toNonUnitalStarSubalgebra) :
    multiplierStrictStarAlgEquiv A E (k : AdjointableMap A E E) =
      (k : 𝓜ₛ(ℂ, (compactOperatorIdeal A E).toNonUnitalStarSubalgebra)) :=
  DoubleCentralizerStrict.toDoubleCentralizer_injective (multiplierStarAlgEquiv_coe k)

@[simp]
theorem multiplierStrictStarAlgEquiv_symm_coe
    (k : (compactOperatorIdeal A E).toNonUnitalStarSubalgebra) :
    (multiplierStrictStarAlgEquiv A E).symm
        (k : 𝓜ₛ(ℂ, (compactOperatorIdeal A E).toNonUnitalStarSubalgebra)) =
      (k : AdjointableMap A E E) := by
  rw [← multiplierStrictStarAlgEquiv_coe, StarAlgEquiv.symm_apply_apply]

/-- **Global strict-to-strong continuity on `L_A(E)`:** for every `x : E`, evaluation at `x` is
globally strictly continuous on `𝓜ₛ(ℂ, K_A(E))` (without norm-boundedness). -/
@[fun_prop]
theorem continuous_apply_multiplierStrictStarAlgEquiv_symm (x : E) :
    Continuous fun m : 𝓜ₛ(ℂ, (compactOperatorIdeal A E).toNonUnitalStarSubalgebra) ↦
      (multiplierStrictStarAlgEquiv A E).symm m x := by
  obtain ⟨k, y, hk⟩ := exists_compactOperatorIdeal_toNonUnitalStarSubalgebra_apply_eq (A := A) x
  rw [← hk]
  have heval :
      Continuous fun m : 𝓜ₛ(ℂ, (compactOperatorIdeal A E).toNonUnitalStarSubalgebra) ↦
        ((m.toDoubleCentralizer.fst k : AdjointableMap A E E) y) :=
    ((continuous_apply y).comp continuous_subtypeVal).comp
      (DoubleCentralizerStrict.continuous_fst_apply k)
  exact heval.congr fun m ↦ (multiplierStarAlgEquiv_symm_apply_coe_apply
    m.toDoubleCentralizer k y).symm

/-- **Global strict-to-strong-* continuity on `L_A(E)`:** for every `x : E`, evaluation of the
adjoint at `x` is globally strictly continuous on `𝓜ₛ(ℂ, K_A(E))`. -/
@[fun_prop]
theorem continuous_adjoint_apply_multiplierStrictStarAlgEquiv_symm (x : E) :
    Continuous fun m : 𝓜ₛ(ℂ, (compactOperatorIdeal A E).toNonUnitalStarSubalgebra) ↦
      ((multiplierStrictStarAlgEquiv A E).symm m).adjoint x :=
  ((continuous_apply_multiplierStrictStarAlgEquiv_symm (A := A) x).comp
    continuous_star).congr fun m ↦ by
      rw [Function.comp_apply, ← star_eq_adjoint, map_star]

/-- Global strict-to-strong continuity of `(multiplierStrictStarAlgEquiv A E).symm` into the
pointwise-convergence operator space `E →Lₚₜ[ℂ] E`. -/
theorem continuous_toPointwiseConvergenceCLM_multiplierStrictStarAlgEquiv_symm :
    Continuous fun m : 𝓜ₛ(ℂ, (compactOperatorIdeal A E).toNonUnitalStarSubalgebra) ↦
      ContinuousLinearMap.toPointwiseConvergenceCLM ℂ (RingHom.id ℂ) E E
        ((multiplierStrictStarAlgEquiv A E).symm m).toContinuousLinearMap :=
  PointwiseConvergenceCLM.continuous_of_continuous_eval
    continuous_apply_multiplierStrictStarAlgEquiv_symm

/-- Global strict-to-strong continuity of the adjoint of `(multiplierStrictStarAlgEquiv A E).symm`
into `E →Lₚₜ[ℂ] E`. -/
theorem continuous_toPointwiseConvergenceCLM_adjoint_multiplierStrictStarAlgEquiv_symm :
    Continuous fun m : 𝓜ₛ(ℂ, (compactOperatorIdeal A E).toNonUnitalStarSubalgebra) ↦
      ContinuousLinearMap.toPointwiseConvergenceCLM ℂ (RingHom.id ℂ) E E
        ((multiplierStrictStarAlgEquiv A E).symm m).adjoint.toContinuousLinearMap :=
  PointwiseConvergenceCLM.continuous_of_continuous_eval
    continuous_adjoint_apply_multiplierStrictStarAlgEquiv_symm

/-- Strict convergence in `𝓜ₛ(ℂ, K_A(E))` implies pointwise norm convergence on `E`. -/
theorem tendsto_apply_of_tendsto_multiplierStrictStarAlgEquiv {ι : Type*} {l : Filter ι}
    {f : ι → AdjointableMap A E E} {T : AdjointableMap A E E}
    (hf : Tendsto (fun i ↦ multiplierStrictStarAlgEquiv A E (f i)) l
      (𝓝 (multiplierStrictStarAlgEquiv A E T))) (x : E) :
    Tendsto (fun i ↦ f i x) l (𝓝 (T x)) := by
  have h := ((continuous_apply_multiplierStrictStarAlgEquiv_symm (A := A) x).tendsto
    (multiplierStrictStarAlgEquiv A E T)).comp hf
  rw [StarAlgEquiv.symm_apply_apply] at h
  exact h.congr fun i ↦ by rw [Function.comp_apply, StarAlgEquiv.symm_apply_apply]

/-- Strict convergence in `𝓜ₛ(ℂ, K_A(E))` implies pointwise norm convergence of adjoints on
`E`. -/
theorem tendsto_adjoint_apply_of_tendsto_multiplierStrictStarAlgEquiv {ι : Type*} {l : Filter ι}
    {f : ι → AdjointableMap A E E} {T : AdjointableMap A E E}
    (hf : Tendsto (fun i ↦ multiplierStrictStarAlgEquiv A E (f i)) l
      (𝓝 (multiplierStrictStarAlgEquiv A E T))) (x : E) :
    Tendsto (fun i ↦ (f i).adjoint x) l (𝓝 (T.adjoint x)) := by
  have h := ((continuous_adjoint_apply_multiplierStrictStarAlgEquiv_symm (A := A) x).tendsto
    (multiplierStrictStarAlgEquiv A E T)).comp hf
  rw [StarAlgEquiv.symm_apply_apply] at h
  exact h.congr fun i ↦ by rw [Function.comp_apply, StarAlgEquiv.symm_apply_apply]

/-- On norm-bounded filters, pointwise norm convergence of `f i` and `(f i).adjoint` on `E`
implies strict convergence in `𝓜ₛ(ℂ, K_A(E))`. -/
theorem tendsto_multiplierStrictStarAlgEquiv_of_eventually_norm_le {ι : Type*} {l : Filter ι}
    {f : ι → AdjointableMap A E E} {T : AdjointableMap A E E} {C : ℝ}
    (hC : ∀ᶠ i in l, ‖f i‖ ≤ C)
    (hf : ∀ x : E, Tendsto (fun i ↦ f i x) l (𝓝 (T x)))
    (hf_adj : ∀ x : E, Tendsto (fun i ↦ (f i).adjoint x) l (𝓝 (T.adjoint x))) :
    Tendsto (fun i ↦ multiplierStrictStarAlgEquiv A E (f i)) l
      (𝓝 (multiplierStrictStarAlgEquiv A E T)) := by
  rw [DoubleCentralizerStrict.tendsto_iff_forall_tendsto]
  refine ⟨fun k ↦ ?_, fun k ↦ ?_⟩
  · rw [isometry_subtypeVal.tendsto_nhds_iff]
    simpa [Function.comp_def, mul_def] using
      tendsto_comp_compactOperator_of_eventually_norm_le hC hf
        (mem_compactOperatorIdeal_toNonUnitalStarSubalgebra.mp k.property)
  · rw [isometry_subtypeVal.tendsto_nhds_iff]
    simpa [Function.comp_def, mul_def] using
      tendsto_compactOperator_comp_of_eventually_norm_le hC hf_adj
        (mem_compactOperatorIdeal_toNonUnitalStarSubalgebra.mp k.property)

/-- **Strict convergence on norm-bounded filters (Raeburn–Williams, Corollary 2.54).** Along any
norm-bounded filter `l` of adjointable operators `f i : L_A(E)`, `f i → T` strictly in
`𝓜ₛ(ℂ, K_A(E))` if and only if `f i x → T x` and `(f i).adjoint x → T.adjoint x` for all
`x : E`. -/
theorem tendsto_multiplierStrictStarAlgEquiv_iff_of_eventually_norm_le {ι : Type*} {l : Filter ι}
    {f : ι → AdjointableMap A E E} {T : AdjointableMap A E E} {C : ℝ}
    (hC : ∀ᶠ i in l, ‖f i‖ ≤ C) :
    Tendsto (fun i ↦ multiplierStrictStarAlgEquiv A E (f i)) l
        (𝓝 (multiplierStrictStarAlgEquiv A E T)) ↔
      (∀ x : E, Tendsto (fun i ↦ f i x) l (𝓝 (T x))) ∧
      (∀ x : E, Tendsto (fun i ↦ (f i).adjoint x) l (𝓝 (T.adjoint x))) :=
  ⟨fun h ↦ ⟨tendsto_apply_of_tendsto_multiplierStrictStarAlgEquiv h,
      tendsto_adjoint_apply_of_tendsto_multiplierStrictStarAlgEquiv h⟩,
    fun ⟨h₁, h₂⟩ ↦
      tendsto_multiplierStrictStarAlgEquiv_of_eventually_norm_le hC h₁ h₂⟩

private theorem induced_eq_induced_of_tendsto_iff {s α β : Type*}
    [TopologicalSpace α] [TopologicalSpace β] (σ : s → α) (τ : s → β)
    (hiff : ∀ {l : Filter s} {x : s}, Tendsto σ l (𝓝 (σ x)) ↔ Tendsto τ l (𝓝 (τ x))) :
    TopologicalSpace.induced σ inferInstance = TopologicalSpace.induced τ inferInstance := by
  refine TopologicalSpace.ext_nhds fun x ↦ ?_
  rw [nhds_induced, nhds_induced]
  exact le_antisymm
    (tendsto_iff_comap.mp (hiff.mp tendsto_comap))
    (tendsto_iff_comap.mp (hiff.mpr tendsto_comap))

/-- **Strict topology on norm-bounded sets.** On every bounded subset `s` of `L_A(E)`, the
topology induced from `𝓜ₛ(ℂ, K_A(E))` coincides with the strong-* topology induced by
`T ↦ (T, T.adjoint)` into `(E →Lₚₜ[ℂ] E) × (E →Lₚₜ[ℂ] E)`. -/
theorem induced_multiplierStrictStarAlgEquiv_eq_induced_pointwiseConvergenceCLM_of_isBounded
    {s : Set (AdjointableMap A E E)} (hs : Bornology.IsBounded s) :
    TopologicalSpace.induced (fun T : s ↦ multiplierStrictStarAlgEquiv A E T) inferInstance =
      TopologicalSpace.induced (fun T : s ↦
        (ContinuousLinearMap.toPointwiseConvergenceCLM ℂ (RingHom.id ℂ) E E
            (T : AdjointableMap A E E).toContinuousLinearMap,
          ContinuousLinearMap.toPointwiseConvergenceCLM ℂ (RingHom.id ℂ) E E
            (T : AdjointableMap A E E).adjoint.toContinuousLinearMap))
        inferInstance := by
  obtain ⟨C, hC⟩ := hs.subset_closedBall 0
  have hC' : ∀ T : s, ‖(T : AdjointableMap A E E)‖ ≤ C := fun T ↦ by
    simpa [Metric.mem_closedBall, dist_zero_right] using hC T.property
  refine induced_eq_induced_of_tendsto_iff _ _ fun {l T₀} ↦ ?_
  rw [Prod.tendsto_iff, PointwiseConvergenceCLM.tendsto_iff_forall_tendsto,
    PointwiseConvergenceCLM.tendsto_iff_forall_tendsto]
  exact tendsto_multiplierStrictStarAlgEquiv_iff_of_eventually_norm_le
    (Eventually.of_forall fun T ↦ hC' T)

/-- The module-compact operators `K_A(E)` are strictly dense in `L_A(E)` (via
`multiplierStrictStarAlgEquiv A E`). -/
theorem denseRange_multiplierStrictStarAlgEquiv_coe :
    DenseRange (fun k : (compactOperatorIdeal A E).toNonUnitalStarSubalgebra ↦
      multiplierStrictStarAlgEquiv A E (k : AdjointableMap A E E)) := by
  simpa only [multiplierStrictStarAlgEquiv_coe] using
    DoubleCentralizerStrict.denseRange_coe
      (A := (compactOperatorIdeal A E).toNonUnitalStarSubalgebra)

/-- Every closed operator-norm ball of radius `R` in `L_A(E)` is the strict closure of the closed
norm ball of radius `R` in `K_A(E)`. -/
theorem closure_multiplierStrictStarAlgEquiv_image_closedBall (R : ℝ) :
    closure ((fun k : (compactOperatorIdeal A E).toNonUnitalStarSubalgebra ↦
        multiplierStrictStarAlgEquiv A E (k : AdjointableMap A E E)) '' Metric.closedBall 0 R) =
      {m : 𝓜ₛ(ℂ, (compactOperatorIdeal A E).toNonUnitalStarSubalgebra) |
        ‖(multiplierStrictStarAlgEquiv A E).symm m‖ ≤ R} := by
  have himg : (fun k : (compactOperatorIdeal A E).toNonUnitalStarSubalgebra ↦
        multiplierStrictStarAlgEquiv A E (k : AdjointableMap A E E)) '' Metric.closedBall 0 R =
      (DoubleCentralizerStrict.coe ℂ :
          (compactOperatorIdeal A E).toNonUnitalStarSubalgebra →
            𝓜ₛ(ℂ, (compactOperatorIdeal A E).toNonUnitalStarSubalgebra)) ''
        Metric.closedBall 0 R := by
    ext m
    simp only [Set.mem_image, multiplierStrictStarAlgEquiv_coe]
  have hset :
      {m : 𝓜ₛ(ℂ, (compactOperatorIdeal A E).toNonUnitalStarSubalgebra) |
        ‖m.toDoubleCentralizer‖ ≤ R} =
      {m : 𝓜ₛ(ℂ, (compactOperatorIdeal A E).toNonUnitalStarSubalgebra) |
        ‖(multiplierStrictStarAlgEquiv A E).symm m‖ ≤ R} := by
    ext m
    simp only [Set.mem_ofPred_eq]
    rw [← norm_multiplierStarAlgEquiv, ← toDoubleCentralizer_multiplierStrictStarAlgEquiv,
      StarAlgEquiv.apply_symm_apply]
  rw [himg, ← hset]
  exact DoubleCentralizerStrict.closure_image_closedBall R

/-- Along any approximate unit `l` of `K_A(E)`, `T * e → T` strictly for every `T : L_A(E)`. -/
theorem tendsto_multiplierStrictStarAlgEquiv_mul_coe_of_isApproximateUnit
    {l : Filter (compactOperatorIdeal A E)} (hl : l.IsApproximateUnit)
    (T : AdjointableMap A E E) :
    Tendsto (fun e : compactOperatorIdeal A E ↦
        multiplierStrictStarAlgEquiv A E (T * (e : AdjointableMap A E E))) l
      (𝓝 (multiplierStrictStarAlgEquiv A E T)) := by
  let eqv := (compactOperatorIdeal A E).toNonUnitalStarSubalgebraEquiv
  refine ((DoubleCentralizerStrict.tendsto_coe_fst_of_isApproximateUnit
    (hl.map eqv.toNonUnitalStarAlgHom continuous_toNonUnitalStarSubalgebraEquiv eqv.surjective)
    (multiplierStrictStarAlgEquiv A E T)).comp tendsto_map).congr fun e ↦ ?_
  rw [Function.comp_apply, StarAlgEquiv.toNonUnitalStarAlgHom_apply,
    toDoubleCentralizer_multiplierStrictStarAlgEquiv, ← multiplierStrictStarAlgEquiv_coe,
    coe_multiplierStarAlgEquiv_fst, TwoSidedIdeal.coe_toNonUnitalStarSubalgebraEquiv_apply]

/-- Along any approximate unit `l` of `K_A(E)`, `e * T → T` strictly for every `T : L_A(E)`. -/
theorem tendsto_multiplierStrictStarAlgEquiv_coe_mul_of_isApproximateUnit
    {l : Filter (compactOperatorIdeal A E)} (hl : l.IsApproximateUnit)
    (T : AdjointableMap A E E) :
    Tendsto (fun e : compactOperatorIdeal A E ↦
        multiplierStrictStarAlgEquiv A E ((e : AdjointableMap A E E) * T)) l
      (𝓝 (multiplierStrictStarAlgEquiv A E T)) := by
  let eqv := (compactOperatorIdeal A E).toNonUnitalStarSubalgebraEquiv
  refine ((DoubleCentralizerStrict.tendsto_coe_snd_of_isApproximateUnit
    (hl.map eqv.toNonUnitalStarAlgHom continuous_toNonUnitalStarSubalgebraEquiv eqv.surjective)
    (multiplierStrictStarAlgEquiv A E T)).comp tendsto_map).congr fun e ↦ ?_
  rw [Function.comp_apply, StarAlgEquiv.toNonUnitalStarAlgHom_apply,
    toDoubleCentralizer_multiplierStrictStarAlgEquiv, ← multiplierStrictStarAlgEquiv_coe,
    coe_multiplierStarAlgEquiv_snd, TwoSidedIdeal.coe_toNonUnitalStarSubalgebraEquiv_apply]

end Complete

end StrictTopology

end AdjointableMap

end TauCeti
