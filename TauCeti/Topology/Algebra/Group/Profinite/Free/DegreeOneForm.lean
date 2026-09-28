/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.BilinearForm
public import TauCeti.Topology.Algebra.Group.Profinite.Free.Graded
public import TauCeti.Topology.Algebra.Group.Profinite.Free.Rank
import Mathlib.Data.Nat.Choose.Dvd

/-!
# The degree-one form of a free pro-`p` group and changes of basis

Let `F = freeProP p X` be the free pro-`p` group on a finite type `X`, with canonical generators
`x_i = freeProP.of i`, and let `gr_1(F) = λ_1(F) ⧸ λ_2(F)` be the degree-one graded piece of its
lower `p`-series. Two continuous characters `χ, ψ : F → 𝔽_p` lift to a continuous homomorphism
`F → H(𝔽_p)` into the Heisenberg group over `𝔽_p`, `x_i ↦ (χ x_i, ψ x_i, 0)`; on `λ_1(F)` its
`(1, 3)`-entry is a homomorphism killing `λ_2(F)`, the **Heisenberg functional**
`TauCeti.freeProP.heisenbergFunctional χ ψ : gr_1(F) →ₗ[𝔽_p] 𝔽_p`. It is the unique linear
functional with

  `[⟦u⟧, ⟦v⟧] ↦ χ u · ψ v - χ v · ψ u`   and   `π ⟦u⟧ ↦ (p choose 2) · χ u · ψ u`

on the brackets and `p`-power classes of degree-zero classes. Assembling these functionals gives
the **degree-one form** `TauCeti.freeProP.degreeOneForm ρ`, an `𝔽_p`-bilinear form on the
continuous `𝔽_p`-dual `H¹(F, 𝔽_p) = Hom_cont(F, 𝔽_p)` attached linearly to each class
`ρ ∈ gr_1(F)`. The form is skew-symmetric, and alternating for odd `p`. In the basis of the dual
which is dual to the generators (`TauCeti.freeProP.dualBasis`), its matrix has the commutator
coordinates of `ρ` in the standard basis of `gr_1(F)` above the diagonal, their negatives below
it, and `(p choose 2)` times the `p`-power coordinates on the diagonal. These are the coordinates
Labute reads off the class `⟦r⟧` of a relator `r ∈ λ_1(F)` to describe the cup product on
`H¹(F ⧸ ⟪r⟫, 𝔽_p)` (Labute, Proposition 3); the identification of the degree-one form of `⟦r⟧`
with that cup product is not proved in this file.

Its transformation law is the change-of-basis law of that matrix: a continuous homomorphism
`φ : F → F'` between free pro-`p` groups carries the form of `ρ` to the form of `φ_* ρ` pulled back
along the transpose of `φ` on the duals, `B_{φ_* ρ}(χ, ψ) = B_ρ(χ ∘ φ, ψ ∘ φ)`, which in matrices is
`B ↦ Pᵀ B P`. Every linear automorphism of the dual is the transpose of a continuous automorphism
of `F` (`TauCeti.freeProP.exists_continuousMulEquiv_continuousZModDualMap_eq`). Hence a change of
basis of `F` brings the matrix of the form of `ρ` into any shape a basis of the dual provides, in
particular into the normal forms of the bilinear-form theory. This normalizes the form of `ρ`
only: for odd `p` the diagonal factor `(p choose 2)` vanishes in `𝔽_p`, so the form does not see
the `p`-power coordinates of `ρ`, and bringing a relator of a Demushkin group into normal form
modulo `λ_2(F)` (Labute, Proposition 4) needs, beyond this normalization, a separate normalization
of the `p`-power component invisible to the form and the cup-product identification above.

## Main definitions

* `TauCeti.freeProP.heisenbergFunctional`: the Heisenberg functional `gr_1(F) → 𝔽_p` of two
  continuous `𝔽_p`-characters of `F`.
* `TauCeti.freeProP.degreeOneForm`: the degree-one form, the bilinear form on the continuous
  `𝔽_p`-dual of `F` attached linearly to a class in `gr_1(F)`.

## Main results

* `TauCeti.freeProP.heisenbergFunctional_gradedBracket_gradedMkZero`,
  `TauCeti.freeProP.heisenbergFunctional_gradedPow_gradedMkZero`,
  `TauCeti.freeProP.heisenbergFunctional_unique`: the values of the Heisenberg functional on
  brackets and `p`-power classes characterize it.
* `TauCeti.freeProP.degreeOneForm_swap`, `TauCeti.freeProP.isAlt_degreeOneForm_of_ne_two`: the
  degree-one form is skew-symmetric, and alternating for odd `p`.
* `TauCeti.freeProP.heisenbergFunctional_gradedMap`, `TauCeti.freeProP.degreeOneForm_gradedMap`:
  the transformation law under a continuous homomorphism between free pro-`p` groups.
* `TauCeti.freeProP.degreeOneForm_dualBasis_of_lt`,
  `TauCeti.freeProP.degreeOneForm_dualBasis_of_gt`, `TauCeti.freeProP.degreeOneForm_dualBasis_self`:
  the matrix of the degree-one form in the dual basis of the generators is read off the
  coordinates of the class in the standard basis of `gr_1(F)`.
* `TauCeti.freeProP.exists_continuousMulEquiv_toMatrix_degreeOneForm_gradedMap`: the matrix of
  the degree-one form of a class in any basis of the dual is the matrix, in the dual basis of the
  generators, of the form of the image of the class under some continuous automorphism of `F`.

## References

* J. Labute, *Classification of Demushkin groups*, Canadian J. Math. 19 (1967), §3,
  Propositions 3 and 4.
-/

public section

namespace TauCeti

open Subgroup Submodule
open scoped commutatorElement

universe u

-- Preferring the ring path keeps a single additive structure on `ZMod p`, so that the linear maps
-- into `ZMod p` below are stated over the module structure of `ZMod p` on itself.
attribute [local instance 2000] Ring.toAddCommGroup

namespace freeProP

variable {p : ℕ} [Fact p.Prime] {X : Type u}

/-! ### The Heisenberg functional

The Heisenberg group over `𝔽_p`, lifted to the universe of `X` and given the discrete topology, is
a finite `p`-group, so a pair of characters defines a continuous homomorphism from `F` into it by
the universal property. Its `(1, 3)`-entry on `λ_1(F)` is the functional. -/

section Heisenberg

/-- The Heisenberg group over `𝔽_p` in the universe of the generating type. -/
private abbrev HeisenbergLift (p : ℕ) : Type u := ULift.{u} (HeisenbergGroup (ZMod p))

private instance : TopologicalSpace (HeisenbergLift.{u} p) := ⊥

private instance : DiscreteTopology (HeisenbergLift.{u} p) := ⟨rfl⟩

private theorem isProP_heisenbergLift : IsProP p (HeisenbergLift.{u} p) :=
  ((HeisenbergGroup.isPGroup_zmod p).of_equiv MulEquiv.ulift.symm).isProP

variable (χ ψ : freeProP p X →ₜ* Multiplicative (ZMod p))

/-- The continuous homomorphism `F → H(𝔽_p)` with `x_i ↦ (χ x_i, ψ x_i, 0)`. -/
private noncomputable def heisenbergHom : freeProP p X →ₜ* HeisenbergLift.{u} p :=
  lift isProP_heisenbergLift fun i ↦ ULift.up ⟨(χ (of i)).toAdd, (ψ (of i)).toAdd, 0⟩

/-- The `(1, 2)`-entry of the lifted Heisenberg group, a continuous character. -/
private def heisenbergX : HeisenbergLift.{u} p →ₜ* Multiplicative (ZMod p) where
  toFun a := Multiplicative.ofAdd a.down.x
  map_one' := by simp
  map_mul' a b := by simp [ULift.mul_down, ofAdd_add]
  continuous_toFun := continuous_of_discreteTopology

/-- The `(2, 3)`-entry of the lifted Heisenberg group, a continuous character. -/
private def heisenbergY : HeisenbergLift.{u} p →ₜ* Multiplicative (ZMod p) where
  toFun a := Multiplicative.ofAdd a.down.y
  map_one' := by simp
  map_mul' a b := by simp [ULift.mul_down, ofAdd_add]
  continuous_toFun := continuous_of_discreteTopology

private theorem heisenbergHom_x (g : freeProP p X) :
    (heisenbergHom χ ψ g).down.x = (χ g).toAdd := by
  have h : heisenbergX.comp (heisenbergHom χ ψ) = χ :=
    hom_ext fun i ↦ by simp [heisenbergX, heisenbergHom]
  rw [← DFunLike.congr_fun h g]
  rfl

private theorem heisenbergHom_y (g : freeProP p X) :
    (heisenbergHom χ ψ g).down.y = (ψ g).toAdd := by
  have h : heisenbergY.comp (heisenbergHom χ ψ) = ψ :=
    hom_ext fun i ↦ by simp [heisenbergY, heisenbergHom]
  rw [← DFunLike.congr_fun h g]
  rfl

/-- On the lifted Heisenberg group, `λ_1` lies on the `z`-axis. -/
private theorem down_x_eq_zero_of_mem_pLowerCentralSeries_one {a : HeisenbergLift.{u} p}
    (ha : a ∈ pLowerCentralSeries p (HeisenbergLift.{u} p) 1) : a.down.x = 0 ∧ a.down.y = 0 := by
  let : TopologicalSpace (HeisenbergGroup (ZMod p)) := ⊥
  have : DiscreteTopology (HeisenbergGroup (ZMod p)) := ⟨rfl⟩
  let e : HeisenbergLift.{u} p ≃* HeisenbergGroup (ZMod p) := MulEquiv.ulift
  have h : e a ∈ (⊤ : Subgroup (HeisenbergGroup (ZMod p))).pLowerCentralSeries p 1 := by
    rw [← pLowerCentralSeries_eq_of_discreteTopology,
      ← e.map_pLowerCentralSeries_eq_of_discreteTopology]
    exact mem_map_of_mem e.toMonoidHom ha
  exact HeisenbergGroup.mem_zAxis_iff.mp (HeisenbergGroup.pLowerCentralSeries_top_one_le_zAxis p h)

private theorem heisenbergHom_mem_pLowerCentralSeries {y : freeProP p X} {k : ℕ}
    (hy : y ∈ pLowerCentralSeries p (freeProP p X) k) :
    heisenbergHom χ ψ y ∈ pLowerCentralSeries p (HeisenbergLift.{u} p) k :=
  (heisenbergHom χ ψ).toMonoidHom.map_pLowerCentralSeries_le (heisenbergHom χ ψ).continuous k
    (mem_map_of_mem _ hy)

/-- The `(1, 3)`-entry of the Heisenberg homomorphism on `λ_1(F)`, a homomorphism because the
`(1, 2)`-entry vanishes there. -/
private noncomputable def heisenbergZ :
    pLowerCentralSeries p (freeProP p X) 1 →* Multiplicative (ZMod p) where
  toFun y := Multiplicative.ofAdd (heisenbergHom χ ψ y).down.z
  map_one' := by simp
  map_mul' y _ := by
    rw [Subgroup.coe_mul, map_mul, ULift.mul_down, HeisenbergGroup.mul_z,
      (down_x_eq_zero_of_mem_pLowerCentralSeries_one
        (heisenbergHom_mem_pLowerCentralSeries χ ψ y.2)).1,
      zero_mul, add_zero, ofAdd_add]

private theorem heisenbergZ_eq_one_of_mem {y : pLowerCentralSeries p (freeProP p X) 1}
    (hy : (y : freeProP p X) ∈ pLowerCentralSeries p (freeProP p X) 2) :
    heisenbergZ χ ψ y = 1 := by
  have h := heisenbergHom_mem_pLowerCentralSeries χ ψ hy
  rw [(MulEquiv.ulift (α := HeisenbergGroup (ZMod p)))
    |>.pLowerCentralSeries_two_eq_bot_heisenbergGroup, Subgroup.mem_bot] at h
  simp [heisenbergZ, h]

/-- **The Heisenberg functional** of two continuous `𝔽_p`-characters `χ, ψ` of the free pro-`p`
group `F`: the `𝔽_p`-linear functional on `gr_1(F)` induced on `λ_1(F)` by the `(1, 3)`-entry of
the continuous homomorphism `F → H(𝔽_p)`, `x_i ↦ (χ x_i, ψ x_i, 0)`, into the Heisenberg group over
`𝔽_p`. It is characterized by its values `[⟦u⟧, ⟦v⟧] ↦ χ u · ψ v - χ v · ψ u` and
`π ⟦u⟧ ↦ (p choose 2) · χ u · ψ u` (`TauCeti.freeProP.heisenbergFunctional_unique`). -/
noncomputable def heisenbergFunctional : gradedPiece p (freeProP p X) 1 →ₗ[ZMod p] ZMod p :=
  (QuotientGroup.lift ((pLowerCentralSeries p (freeProP p X) 2).subgroupOf
      (pLowerCentralSeries p (freeProP p X) 1)) (heisenbergZ χ ψ) fun _ hy ↦
        MonoidHom.mem_ker.mpr (heisenbergZ_eq_one_of_mem χ ψ (mem_subgroupOf.mp hy))
    ).toAdditiveLeft.toZModLinearMap p

private theorem heisenbergFunctional_gradedMk (y : pLowerCentralSeries p (freeProP p X) 1) :
    heisenbergFunctional χ ψ (gradedMk p (freeProP p X) 1 y) = (heisenbergHom χ ψ y).down.z := by
  rw [gradedMk_def]
  rfl

/-- **The Heisenberg functional on a bracket**: `[⟦u⟧, ⟦v⟧] ↦ χ u · ψ v - χ v · ψ u`. -/
theorem heisenbergFunctional_gradedBracket_gradedMkZero (u v : freeProP p X) :
    heisenbergFunctional χ ψ (gradedBracket p (freeProP p X) 0 0
        (gradedMkZero p (freeProP p X) u) (gradedMkZero p (freeProP p X) v)) =
      (χ u).toAdd * (ψ v).toAdd - (χ v).toAdd * (ψ u).toAdd := by
  rw [gradedBracket_gradedMkZero, heisenbergFunctional_gradedMk, Subgroup.coe_mk,
    map_commutatorElement]
  have h : (⁅heisenbergHom χ ψ u, heisenbergHom χ ψ v⁆).down =
      ⁅(heisenbergHom χ ψ u).down, (heisenbergHom χ ψ v).down⁆ :=
    map_commutatorElement (MulEquiv.ulift (α := HeisenbergGroup (ZMod p))).toMonoidHom _ _
  rw [h, HeisenbergGroup.commutatorElement_eq, heisenbergHom_x, heisenbergHom_y, heisenbergHom_x,
    heisenbergHom_y]

/-- **The Heisenberg functional on a `p`-power class**: `π ⟦u⟧ ↦ (p choose 2) · χ u · ψ u`. -/
theorem heisenbergFunctional_gradedPow_gradedMkZero (u : freeProP p X) :
    heisenbergFunctional χ ψ (gradedPow p (freeProP p X) 0 (gradedMkZero p (freeProP p X) u)) =
      p.choose 2 • ((χ u).toAdd * (ψ u).toAdd) := by
  rw [gradedPow_gradedMkZero, heisenbergFunctional_gradedMk, Subgroup.coe_mk, map_pow]
  have h : ((heisenbergHom χ ψ u) ^ p).down = (heisenbergHom χ ψ u).down ^ p :=
    map_pow (MulEquiv.ulift (α := HeisenbergGroup (ZMod p))).toMonoidHom _ _
  rw [h, HeisenbergGroup.pow_eq, heisenbergHom_x, heisenbergHom_y]
  simp [nsmul_eq_mul]

variable [Finite X]

private theorem isOpen_pLowerCentralSeries_two :
    IsOpen (pLowerCentralSeries p (freeProP p X) 2 : Set (freeProP p X)) :=
  (isTopologicallyFinitelyGenerated_freeProP p X).isOpen_pLowerCentralSeries Fact.out 2

/-- Linear maps out of `gr_1(F)` agreeing on all brackets and `p`-power classes of degree-zero
classes are equal, for `F` of finite rank. -/
private theorem linearMap_ext {M : Type*} [AddCommMonoid M] [Module (ZMod p) M]
    {f g : gradedPiece p (freeProP p X) 1 →ₗ[ZMod p] M}
    (hpow : ∀ u : freeProP p X, f (gradedPow p _ 0 (gradedMkZero p _ u)) =
      g (gradedPow p _ 0 (gradedMkZero p _ u)))
    (hbr : ∀ u v : freeProP p X,
      f (gradedBracket p _ 0 0 (gradedMkZero p _ u) (gradedMkZero p _ v)) =
        g (gradedBracket p _ 0 0 (gradedMkZero p _ u) (gradedMkZero p _ v))) : f = g :=
  TauCeti.linearMap_ext_gradedPiece_one isOpen_pLowerCentralSeries_two (s := Set.univ)
    (by rw [Subgroup.closure_univ]; exact eq_top_iff.mpr (Subgroup.le_topologicalClosure _))
    (fun u _ ↦ hpow u) fun u _ v _ ↦ hbr u v

/-- **Uniqueness of the Heisenberg functional**: a linear functional on `gr_1(F)` with the values
`[⟦u⟧, ⟦v⟧] ↦ χ u · ψ v - χ v · ψ u` and `π ⟦u⟧ ↦ (p choose 2) · χ u · ψ u` is the Heisenberg
functional of `χ` and `ψ`. -/
theorem heisenbergFunctional_unique {f : gradedPiece p (freeProP p X) 1 →ₗ[ZMod p] ZMod p}
    (hbr : ∀ u v : freeProP p X,
      f (gradedBracket p _ 0 0 (gradedMkZero p _ u) (gradedMkZero p _ v)) =
        (χ u).toAdd * (ψ v).toAdd - (χ v).toAdd * (ψ u).toAdd)
    (hpow : ∀ u : freeProP p X,
      f (gradedPow p _ 0 (gradedMkZero p _ u)) = p.choose 2 • ((χ u).toAdd * (ψ u).toAdd)) :
    f = heisenbergFunctional χ ψ :=
  linearMap_ext (fun u ↦ (hpow u).trans (heisenbergFunctional_gradedPow_gradedMkZero χ ψ u).symm)
    fun u v ↦ (hbr u v).trans (heisenbergFunctional_gradedBracket_gradedMkZero χ ψ u v).symm

/-- The Heisenberg functional is additive in its first character. -/
@[simp]
theorem heisenbergFunctional_mul_left (χ' : freeProP p X →ₜ* Multiplicative (ZMod p)) :
    heisenbergFunctional (χ * χ') ψ = heisenbergFunctional χ ψ + heisenbergFunctional χ' ψ :=
  linearMap_ext
    (fun u ↦ by
      simp only [LinearMap.add_apply, heisenbergFunctional_gradedPow_gradedMkZero,
        ContinuousMonoidHom.mul_apply, toAdd_mul]
      rw [add_mul, nsmul_add])
    fun u v ↦ by
      simp only [LinearMap.add_apply, heisenbergFunctional_gradedBracket_gradedMkZero,
        ContinuousMonoidHom.mul_apply, toAdd_mul]
      ring

/-- The Heisenberg functional is additive in its second character. -/
@[simp]
theorem heisenbergFunctional_mul_right (ψ' : freeProP p X →ₜ* Multiplicative (ZMod p)) :
    heisenbergFunctional χ (ψ * ψ') = heisenbergFunctional χ ψ + heisenbergFunctional χ ψ' :=
  linearMap_ext
    (fun u ↦ by
      simp only [LinearMap.add_apply, heisenbergFunctional_gradedPow_gradedMkZero,
        ContinuousMonoidHom.mul_apply, toAdd_mul]
      rw [mul_add, nsmul_add])
    fun u v ↦ by
      simp only [LinearMap.add_apply, heisenbergFunctional_gradedBracket_gradedMkZero,
        ContinuousMonoidHom.mul_apply, toAdd_mul]
      ring

/-- The Heisenberg functional of the trivial character and any character vanishes. -/
@[simp]
theorem heisenbergFunctional_one_left : heisenbergFunctional 1 ψ = 0 :=
  linearMap_ext (fun u ↦ by rw [heisenbergFunctional_gradedPow_gradedMkZero]; simp)
    fun u v ↦ by rw [heisenbergFunctional_gradedBracket_gradedMkZero]; simp

/-- The Heisenberg functional of any character and the trivial character vanishes. -/
@[simp]
theorem heisenbergFunctional_one_right : heisenbergFunctional χ 1 = 0 :=
  linearMap_ext (fun u ↦ by rw [heisenbergFunctional_gradedPow_gradedMkZero]; simp)
    fun u v ↦ by rw [heisenbergFunctional_gradedBracket_gradedMkZero]; simp

variable {Y : Type u}

/-- **Naturality of the Heisenberg functional.** A continuous homomorphism `φ : F → F'` between
free pro-`p` groups, with `F` of finite rank, carries the Heisenberg functional of `χ, ψ` on
`gr_1(F')` back to the Heisenberg functional of `χ ∘ φ, ψ ∘ φ` on `gr_1(F)`. -/
theorem heisenbergFunctional_comp_gradedMap (χ ψ : freeProP p Y →ₜ* Multiplicative (ZMod p))
    (φ : freeProP p X →ₜ* freeProP p Y) :
    (heisenbergFunctional χ ψ).comp ((gradedMap p φ.toMonoidHom φ.continuous 1).toZModLinearMap p) =
      heisenbergFunctional (χ.comp φ) (ψ.comp φ) :=
  linearMap_ext
    (fun u ↦ by
      rw [LinearMap.comp_apply, AddMonoidHom.coe_toZModLinearMap, gradedMap_gradedPow,
        gradedMap_gradedMkZero, heisenbergFunctional_gradedPow_gradedMkZero,
        heisenbergFunctional_gradedPow_gradedMkZero]
      rfl)
    fun u v ↦ by
      rw [LinearMap.comp_apply, AddMonoidHom.coe_toZModLinearMap]
      -- The bracket lands in degree `0 + 0 + 1`, which is `1` by evaluation, not syntactically.
      refine (congrArg (heisenbergFunctional χ ψ) (gradedMap_gradedBracket φ.toMonoidHom
        φ.continuous (j := 0) (k := 0) _ _)).trans ?_
      rw [gradedMap_gradedMkZero, gradedMap_gradedMkZero,
        heisenbergFunctional_gradedBracket_gradedMkZero,
        heisenbergFunctional_gradedBracket_gradedMkZero]
      rfl

/-- **Naturality of the Heisenberg functional, on a class.** -/
theorem heisenbergFunctional_gradedMap (χ ψ : freeProP p Y →ₜ* Multiplicative (ZMod p))
    (φ : freeProP p X →ₜ* freeProP p Y) (ρ : gradedPiece p (freeProP p X) 1) :
    heisenbergFunctional χ ψ (gradedMap p φ.toMonoidHom φ.continuous 1 ρ) =
      heisenbergFunctional (χ.comp φ) (ψ.comp φ) ρ :=
  LinearMap.congr_fun (heisenbergFunctional_comp_gradedMap χ ψ φ) ρ

end Heisenberg

/-! ### The degree-one form -/

section Form

variable [Finite X]

/-- The Heisenberg functional at a fixed class and first character, as a linear functional of the
second character. -/
private noncomputable def degreeOneFormRight (χ : freeProP p X →ₜ* Multiplicative (ZMod p))
    (ρ : gradedPiece p (freeProP p X) 1) :
    continuousZModDual p (freeProP p X) →ₗ[ZMod p] ZMod p :=
  AddMonoidHom.toZModLinearMap p
    { toFun ψ := heisenbergFunctional χ ψ.toMul ρ
      map_zero' := by rw [toMul_zero, heisenbergFunctional_one_right, LinearMap.zero_apply]
      map_add' := fun ψ ψ' ↦ by
        rw [toMul_add, heisenbergFunctional_mul_right, LinearMap.add_apply] }

private theorem degreeOneFormRight_apply (χ : freeProP p X →ₜ* Multiplicative (ZMod p))
    (ρ : gradedPiece p (freeProP p X) 1) (ψ : continuousZModDual p (freeProP p X)) :
    degreeOneFormRight χ ρ ψ = heisenbergFunctional χ ψ.toMul ρ := by
  rw [degreeOneFormRight, AddMonoidHom.coe_toZModLinearMap, AddMonoidHom.coe_mk, ZeroHom.coe_mk]

/-- The Heisenberg functional at a fixed class, as a bilinear form on the continuous dual. -/
private noncomputable def degreeOneFormAux (ρ : gradedPiece p (freeProP p X) 1) :
    LinearMap.BilinForm (ZMod p) (continuousZModDual p (freeProP p X)) :=
  AddMonoidHom.toZModLinearMap p
    { toFun χ := degreeOneFormRight χ.toMul ρ
      map_zero' := LinearMap.ext fun ψ ↦ by
        rw [degreeOneFormRight_apply, toMul_zero, heisenbergFunctional_one_left,
          LinearMap.zero_apply, LinearMap.zero_apply]
      map_add' := fun χ χ' ↦ LinearMap.ext fun ψ ↦ by
        rw [degreeOneFormRight_apply, toMul_add, heisenbergFunctional_mul_left,
          LinearMap.add_apply, LinearMap.add_apply, degreeOneFormRight_apply,
          degreeOneFormRight_apply] }

private theorem degreeOneFormAux_apply (ρ : gradedPiece p (freeProP p X) 1)
    (χ ψ : continuousZModDual p (freeProP p X)) :
    degreeOneFormAux ρ χ ψ = heisenbergFunctional χ.toMul ψ.toMul ρ := by
  rw [degreeOneFormAux, AddMonoidHom.coe_toZModLinearMap, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
    degreeOneFormRight_apply]

/-- **The degree-one form** of a free pro-`p` group `F` of finite rank: the `𝔽_p`-bilinear form
`(χ, ψ) ↦ heisenbergFunctional χ ψ ρ` on the continuous `𝔽_p`-dual of `F`, attached
`𝔽_p`-linearly to a class `ρ ∈ gr_1(F)`. Its matrix in the dual basis of the generators has the
commutator coordinates of `ρ` above the diagonal and `(p choose 2)` times the `p`-power
coordinates on it (`TauCeti.freeProP.degreeOneForm_dualBasis_of_lt`,
`TauCeti.freeProP.degreeOneForm_dualBasis_self`); for the class of a relator `r ∈ λ_1(F)` these
are the coordinates Labute attaches to the one-relator group `F ⧸ ⟪r⟫`. -/
noncomputable def degreeOneForm : gradedPiece p (freeProP p X) 1 →ₗ[ZMod p]
    LinearMap.BilinForm (ZMod p) (continuousZModDual p (freeProP p X)) :=
  AddMonoidHom.toZModLinearMap p
    { toFun := degreeOneFormAux (p := p) (X := X)
      map_zero' := LinearMap.ext₂ fun χ ψ ↦ by
        rw [degreeOneFormAux_apply, LinearMap.zero_apply, LinearMap.zero_apply, map_zero]
      map_add' := fun ρ ρ' ↦ LinearMap.ext₂ fun χ ψ ↦ by
        rw [degreeOneFormAux_apply, LinearMap.add_apply, LinearMap.add_apply,
          degreeOneFormAux_apply, degreeOneFormAux_apply, map_add] }

/-- The degree-one form evaluates to the Heisenberg functional. -/
@[simp]
theorem degreeOneForm_apply (ρ : gradedPiece p (freeProP p X) 1)
    (χ ψ : continuousZModDual p (freeProP p X)) :
    degreeOneForm ρ χ ψ = heisenbergFunctional χ.toMul ψ.toMul ρ := by
  rw [degreeOneForm, AddMonoidHom.coe_toZModLinearMap, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
    degreeOneFormAux_apply]

/-- **The degree-one form on a bracket**: `[⟦u⟧, ⟦v⟧] ↦ χ u · ψ v - χ v · ψ u`. -/
theorem degreeOneForm_gradedBracket_gradedMkZero (u v : freeProP p X)
    (χ ψ : continuousZModDual p (freeProP p X)) :
    degreeOneForm (gradedBracket p (freeProP p X) 0 0
        (gradedMkZero p (freeProP p X) u) (gradedMkZero p (freeProP p X) v)) χ ψ =
      (χ.toMul u).toAdd * (ψ.toMul v).toAdd - (χ.toMul v).toAdd * (ψ.toMul u).toAdd :=
  heisenbergFunctional_gradedBracket_gradedMkZero _ _ u v

/-- **The degree-one form on a `p`-power class**: `π ⟦u⟧ ↦ (p choose 2) · χ u · ψ u`. -/
theorem degreeOneForm_gradedPow_gradedMkZero (u : freeProP p X)
    (χ ψ : continuousZModDual p (freeProP p X)) :
    degreeOneForm (gradedPow p (freeProP p X) 0 (gradedMkZero p (freeProP p X) u)) χ ψ =
      p.choose 2 • ((χ.toMul u).toAdd * (ψ.toMul u).toAdd) :=
  heisenbergFunctional_gradedPow_gradedMkZero _ _ u

/-- **The degree-one form is skew-symmetric**: `B_ρ(ψ, χ) = -B_ρ(χ, ψ)`. On the `p`-power classes
both sides are `(p choose 2) · χ u · ψ u`, and `2 · (p choose 2) = p (p - 1)` vanishes in `𝔽_p`. -/
theorem degreeOneForm_swap (ρ : gradedPiece p (freeProP p X) 1)
    (χ ψ : continuousZModDual p (freeProP p X)) :
    degreeOneForm ρ ψ χ = -degreeOneForm ρ χ ψ := by
  rw [degreeOneForm_apply, degreeOneForm_apply, ← LinearMap.neg_apply]
  refine LinearMap.congr_fun (linearMap_ext (fun u ↦ ?_) fun u v ↦ ?_) ρ
  · rw [LinearMap.neg_apply, heisenbergFunctional_gradedPow_gradedMkZero,
      heisenbergFunctional_gradedPow_gradedMkZero, mul_comm, eq_neg_iff_add_eq_zero, ← add_nsmul,
      ← two_mul, Nat.choose_two_right, Nat.two_mul_div_two_of_even (Nat.even_mul_pred_self p),
      nsmul_eq_mul, Nat.cast_mul, ZMod.natCast_self, zero_mul, zero_mul]
  · rw [LinearMap.neg_apply, heisenbergFunctional_gradedBracket_gradedMkZero,
      heisenbergFunctional_gradedBracket_gradedMkZero]
    ring

/-- **The degree-one form is alternating for odd `p`**: the diagonal factor `(p choose 2)` is
divisible by `p`. -/
theorem isAlt_degreeOneForm_of_ne_two (hp : p ≠ 2) (ρ : gradedPiece p (freeProP p X) 1) :
    (degreeOneForm ρ).IsAlt := by
  intro χ
  rw [degreeOneForm_apply]
  refine (LinearMap.congr_fun (linearMap_ext (g := 0) (fun u ↦ ?_) fun u v ↦ ?_) ρ).trans
    (LinearMap.zero_apply ρ)
  · rw [heisenbergFunctional_gradedPow_gradedMkZero, LinearMap.zero_apply, nsmul_eq_mul,
      (ZMod.natCast_eq_zero_iff _ _).mpr (Nat.Prime.dvd_choose_self Fact.out two_ne_zero
        (lt_of_le_of_ne (Nat.Prime.two_le Fact.out) hp.symm)), zero_mul]
  · rw [heisenbergFunctional_gradedBracket_gradedMkZero, LinearMap.zero_apply, mul_comm, sub_self]

variable {Y : Type u} [Finite Y]

/-- **The transformation law of the degree-one form.** A continuous homomorphism `φ : F → F'`
between free pro-`p` groups of finite rank carries the degree-one form of `ρ ∈ gr_1(F)` to the
degree-one form of `φ_* ρ` pulled back along the transpose of `φ` on the continuous duals:
`B_{φ_* ρ}(χ, ψ) = B_ρ(χ ∘ φ, ψ ∘ φ)`. In matrices, a change of generators by `P` acts on the
matrix of the form by `B ↦ Pᵀ B P`. -/
theorem degreeOneForm_gradedMap (φ : freeProP p X →ₜ* freeProP p Y)
    (ρ : gradedPiece p (freeProP p X) 1) :
    degreeOneForm (gradedMap p φ.toMonoidHom φ.continuous 1 ρ) =
      (degreeOneForm ρ).compl₁₂ φ.continuousZModDualMap φ.continuousZModDualMap :=
  LinearMap.ext₂ fun χ ψ ↦ by
    rw [degreeOneForm_apply, LinearMap.compl₁₂_apply, degreeOneForm_apply,
      ContinuousMonoidHom.toMul_continuousZModDualMap,
      ContinuousMonoidHom.toMul_continuousZModDualMap, heisenbergFunctional_gradedMap]

end Form

/-! ### Coordinates of the degree-one form -/

section Coordinates

variable [Finite X]

/-- Evaluation of the degree-one form at two fixed characters, as a linear functional on
`gr_1(F)`. -/
private noncomputable def evalDegreeOneForm (χ ψ : continuousZModDual p (freeProP p X)) :
    gradedPiece p (freeProP p X) 1 →ₗ[ZMod p] ZMod p :=
  AddMonoidHom.toZModLinearMap p
    { toFun ρ := degreeOneForm ρ χ ψ
      map_zero' := by rw [map_zero, LinearMap.zero_apply, LinearMap.zero_apply]
      map_add' := fun ρ ρ' ↦ by rw [map_add, LinearMap.add_apply, LinearMap.add_apply] }

private theorem evalDegreeOneForm_apply (χ ψ : continuousZModDual p (freeProP p X))
    (ρ : gradedPiece p (freeProP p X) 1) : evalDegreeOneForm χ ψ ρ = degreeOneForm ρ χ ψ := by
  rw [evalDegreeOneForm, AddMonoidHom.coe_toZModLinearMap, AddMonoidHom.coe_mk, ZeroHom.coe_mk]

variable [LinearOrder X]

/-- **The degree-one form reads off the commutator coordinates**: for `i < j`, the value of the
form of `ρ` on the `i`-th and `j`-th coordinate characters is the coefficient of `[⟦x_i⟧, ⟦x_j⟧]` in
the expansion of `ρ` in the standard basis of `gr_1(F)`. -/
theorem degreeOneForm_dualBasis_of_lt (ρ : gradedPiece p (freeProP p X) 1) {i j : X}
    (hij : i < j) :
    degreeOneForm ρ (dualBasis p X i) (dualBasis p X j) =
      (degreeOneBasis p X).repr ρ (Sum.inr ⟨(i, j), hij⟩) := by
  -- Both sides are linear in `ρ`; compare them on the standard basis of `gr_1(F)`.
  have h : evalDegreeOneForm (dualBasis p X i) (dualBasis p X j) =
      (degreeOneBasis p X).coord (Sum.inr ⟨(i, j), hij⟩) := by
    refine (degreeOneBasis p X).ext fun k ↦ ?_
    rw [evalDegreeOneForm_apply, Module.Basis.coord_apply, Module.Basis.repr_self,
      degreeOneBasis_apply]
    rcases k with m | ⟨⟨m, n⟩, hmn⟩
    · rw [degreeOneFamily_inl, degreeOneForm_gradedPow_gradedMkZero, toMul_dualBasis_of,
        toMul_dualBasis_of, toAdd_ofAdd, toAdd_ofAdd, Finsupp.single_eq_of_ne (by simp)]
      -- The two coordinate characters cannot both be `1` at `x_m`, since `i ≠ j`.
      by_cases hmi : m = i
      · subst hmi
        simp [hij.ne]
      · simp [Pi.single_apply, hmi]
    · dsimp only at hmn
      rw [degreeOneFamily_inr, degreeOneForm_gradedBracket_gradedMkZero, toMul_dualBasis_of,
        toMul_dualBasis_of, toMul_dualBasis_of, toMul_dualBasis_of, toAdd_ofAdd, toAdd_ofAdd,
        toAdd_ofAdd, toAdd_ofAdd, Finsupp.single_apply]
      simp only [Pi.single_apply, Sum.inr.injEq, Subtype.mk.injEq, Prod.mk.injEq]
      -- The crossed term vanishes: `n = i` and `m = j` would give `m < n = i < j = m`.
      have h2 : (if n = i then (1 : ZMod p) else 0) * (if m = j then 1 else 0) = 0 := by
        split_ifs with hn hm
        · exact absurd ((hmn.trans_eq hn).trans (hij.trans_eq hm.symm)) (lt_irrefl m)
        all_goals simp
      rw [h2, sub_zero]
      by_cases hmi : m = i
      · subst hmi
        by_cases hnj : n = j
        · subst hnj
          simp
        · simp [hnj]
      · simp [hmi]
  exact (evalDegreeOneForm_apply _ _ ρ).symm.trans (LinearMap.congr_fun h ρ)

/-- **The degree-one form reads off the commutator coordinates, below the diagonal**: for
`j < i`, the value of the form of `ρ` on the `i`-th and `j`-th coordinate characters is the
negative of the coefficient of `[⟦x_j⟧, ⟦x_i⟧]` in the expansion of `ρ` in the standard basis of
`gr_1(F)`. -/
theorem degreeOneForm_dualBasis_of_gt (ρ : gradedPiece p (freeProP p X) 1) {i j : X}
    (hji : j < i) :
    degreeOneForm ρ (dualBasis p X i) (dualBasis p X j) =
      -(degreeOneBasis p X).repr ρ (Sum.inr ⟨(j, i), hji⟩) := by
  rw [degreeOneForm_swap, degreeOneForm_dualBasis_of_lt ρ hji]

/-- **The degree-one form reads off the `p`-power coordinates**: the value of the form of `ρ` on
the `i`-th coordinate character twice is `(p choose 2)` times the coefficient of `π ⟦x_i⟧` in the
expansion of `ρ` in the standard basis of `gr_1(F)`. -/
theorem degreeOneForm_dualBasis_self (ρ : gradedPiece p (freeProP p X) 1) (i : X) :
    degreeOneForm ρ (dualBasis p X i) (dualBasis p X i) =
      p.choose 2 • (degreeOneBasis p X).repr ρ (Sum.inl i) := by
  have h : evalDegreeOneForm (dualBasis p X i) (dualBasis p X i) =
      p.choose 2 • (degreeOneBasis p X).coord (Sum.inl i) := by
    refine (degreeOneBasis p X).ext fun k ↦ ?_
    rw [evalDegreeOneForm_apply, LinearMap.smul_apply, Module.Basis.coord_apply,
      Module.Basis.repr_self, degreeOneBasis_apply]
    rcases k with m | ⟨⟨m, n⟩, hmn⟩
    · rw [degreeOneFamily_inl, degreeOneForm_gradedPow_gradedMkZero, toMul_dualBasis_of,
        toAdd_ofAdd, Finsupp.single_apply]
      by_cases hmi : m = i
      · subst hmi
        simp
      · simp [hmi]
    · rw [degreeOneFamily_inr, degreeOneForm_gradedBracket_gradedMkZero, toMul_dualBasis_of,
        toMul_dualBasis_of, toAdd_ofAdd, toAdd_ofAdd, Finsupp.single_eq_of_ne (by simp)]
      simp [Pi.single_apply, mul_comm]
  exact (evalDegreeOneForm_apply _ _ ρ).symm.trans (LinearMap.congr_fun h ρ)

end Coordinates

/-! ### Normal forms after an automorphism -/

section Automorphism

variable [Finite X]

/-- **A basis of the dual is the dual basis of the generators after an automorphism.** For every
class `ρ ∈ gr_1(F)` and every basis `η` of the continuous `𝔽_p`-dual of `F`, there is a continuous
automorphism `e` of `F` such that the degree-one form of `e_* ρ` on the dual basis of the
generators is the degree-one form of `ρ` on `η`. -/
theorem exists_continuousMulEquiv_degreeOneForm_gradedMap_dualBasis
    (ρ : gradedPiece p (freeProP p X) 1)
    (η : Module.Basis X (ZMod p) (continuousZModDual p (freeProP p X))) :
    ∃ e : freeProP p X ≃ₜ* freeProP p X, ∀ i j,
      degreeOneForm (gradedMap p (e : freeProP p X →ₜ* freeProP p X).toMonoidHom
          (e : freeProP p X →ₜ* freeProP p X).continuous 1 ρ) (dualBasis p X i) (dualBasis p X j) =
        degreeOneForm ρ (η i) (η j) := by
  obtain ⟨e, he⟩ :=
    exists_continuousMulEquiv_continuousZModDualMap_eq ((dualBasis p X).equiv η (Equiv.refl X))
  refine ⟨e, fun i j ↦ ?_⟩
  rw [degreeOneForm_gradedMap, LinearMap.compl₁₂_apply, he, he, Module.Basis.equiv_apply,
    Module.Basis.equiv_apply, Equiv.refl_apply, Equiv.refl_apply]

/-- **Any matrix of the degree-one form is attained in the dual basis of the generators after an
automorphism.** For every class `ρ ∈ gr_1(F)` and every basis `η` of the continuous `𝔽_p`-dual of
`F`, there is a continuous automorphism `e` of `F` such that the matrix of the degree-one form of
`e_* ρ` in the dual basis of the generators is the matrix of the degree-one form of `ρ` in `η`. So
a normal form for the matrix of the form, such as a symplectic basis, is realized by a change of
generators of `F`. -/
theorem exists_continuousMulEquiv_toMatrix_degreeOneForm_gradedMap [Fintype X] [DecidableEq X]
    (ρ : gradedPiece p (freeProP p X) 1)
    (η : Module.Basis X (ZMod p) (continuousZModDual p (freeProP p X))) :
    ∃ e : freeProP p X ≃ₜ* freeProP p X,
      LinearMap.BilinForm.toMatrix (dualBasis p X)
          (degreeOneForm (gradedMap p (e : freeProP p X →ₜ* freeProP p X).toMonoidHom
            (e : freeProP p X →ₜ* freeProP p X).continuous 1 ρ)) =
        LinearMap.BilinForm.toMatrix η (degreeOneForm ρ) := by
  obtain ⟨e, he⟩ := exists_continuousMulEquiv_degreeOneForm_gradedMap_dualBasis ρ η
  exact ⟨e, Matrix.ext fun i j ↦ by
    rw [LinearMap.BilinForm.toMatrix_apply, LinearMap.BilinForm.toMatrix_apply, he]⟩

end Automorphism

end freeProP

end TauCeti
