/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.GroupTheory.Subgroup.Center
public import Mathlib.Topology.Algebra.ContinuousMonoidHom
public import Mathlib.Topology.Algebra.Group.Basic

/-!
# Continuous automorphisms and continuous outer automorphisms

For a topological magma `G`, the continuous multiplicative self-isomorphisms `G ≃ₜ* G` form a
group under composition, `ContinuousAut G`. Its multiplication is `(φ * ψ) x = φ (ψ x)`, matching
Mathlib's `MulAut`, and forgetting continuity is an injective homomorphism
`ContinuousAut.toMulAut : ContinuousAut G →* MulAut G`.

The group `ContinuousAut G` acts faithfully on `G` by evaluation. This is a
`MulDistribMulAction`, and each individual automorphism acts continuously.

When `G` is a group whose multiplication is separately continuous, every inner automorphism
`x ↦ g * x * g⁻¹` is continuous, which gives the homomorphism
`ContinuousAut.conj : G →* ContinuousAut G`, lifting `MulAut.conj`. Its kernel is the centre of `G`
and its range is normal, so the quotient `ContinuousOut G` is the group of continuous outer
automorphisms. An automorphism that is inner as an abstract automorphism is the continuous inner
automorphism by the same element, so its class in `ContinuousOut G` is trivial.

For a profinite group an abstract automorphism need not be continuous, so `ContinuousAut G` can be
a proper subgroup of `MulAut G`. It is the group on which the congruence topology of a
profinite group is placed, and `ContinuousOut G` is the target of outer actions such as the
outer Galois action on a profinite fundamental group.

## Main definitions

* `TauCeti.ContinuousAut G`: the group `G ≃ₜ* G` of continuous automorphisms.
* `TauCeti.ContinuousAut.toMulAut`: the forgetful homomorphism `ContinuousAut G →* MulAut G`.
* `TauCeti.ContinuousAut.smul_def`: the action of a continuous automorphism is evaluation.
* `TauCeti.ContinuousAut.conj`: the inner automorphisms, `conj g x = g * x * g⁻¹`.
* `TauCeti.ContinuousOut G`: the quotient of `ContinuousAut G` by the inner automorphisms, with
  quotient map `TauCeti.ContinuousOut.mk`.
* `TauCeti.ContinuousOut.mulEquivOfIsMulCommutative`: for commutative `G`, the outer automorphism
  group is the automorphism group.

## Main results

* `TauCeti.ContinuousAut.toMulAut_injective`: a continuous automorphism is determined by its
  underlying abstract automorphism.
* `TauCeti.ContinuousAut.ker_conj`: the kernel of `conj` is the centre of `G`, so `conj` is
  injective exactly when the centre is trivial (`conj_injective_iff`) and trivial exactly when `G`
  is commutative (`range_conj_eq_bot_iff`).
* `TauCeti.ContinuousAut.mul_conj_mul_inv`: `φ * conj g * φ⁻¹ = conj (φ g)`, so the range of
  `conj` is normal.
* `TauCeti.ContinuousAut.eq_conj_of_toMulAut_eq_conj`: an automorphism that is inner as an abstract
  automorphism is the continuous inner automorphism.
* `TauCeti.ContinuousOut.mk_eq_one_iff`: the class of `φ` in `ContinuousOut G` is trivial exactly
  when the underlying abstract automorphism is inner.

## References

* L. Ribes, P. Zalesskii, *Profinite Groups*, 2nd ed., §4.4.
-/

public section

namespace TauCeti

/-- The group of continuous automorphisms of a topological magma `G`: the continuous
multiplicative isomorphisms `G ≃ₜ* G`, under composition. -/
abbrev ContinuousAut (G : Type*) [Mul G] [TopologicalSpace G] :=
  G ≃ₜ* G

namespace ContinuousAut

section Mul

variable (G : Type*) [Mul G] [TopologicalSpace G]

/-- Continuous automorphisms form a group under composition: `φ * ψ = ψ.trans φ`, so that
`(φ * ψ) x = φ (ψ x)` as for `MulAut`. -/
instance : Group (ContinuousAut G) where
  mul φ ψ := ψ.trans φ
  one := ContinuousMulEquiv.refl G
  inv := ContinuousMulEquiv.symm
  mul_assoc _ _ _ := rfl
  one_mul _ := rfl
  mul_one _ := rfl
  inv_mul_cancel := ContinuousMulEquiv.self_trans_symm

variable {G}

@[simp]
theorem coe_mul (φ ψ : ContinuousAut G) : ⇑(φ * ψ) = φ ∘ ψ :=
  (rfl)

@[simp]
theorem coe_one : ⇑(1 : ContinuousAut G) = id :=
  (rfl)

@[simp]
theorem coe_inv (φ : ContinuousAut G) : ⇑φ⁻¹ = φ.symm :=
  (rfl)

theorem mul_def (φ ψ : ContinuousAut G) : φ * ψ = ψ.trans φ :=
  (rfl)

theorem one_def : (1 : ContinuousAut G) = ContinuousMulEquiv.refl G :=
  (rfl)

theorem inv_def (φ : ContinuousAut G) : φ⁻¹ = φ.symm :=
  (rfl)

@[simp]
theorem mul_apply (φ ψ : ContinuousAut G) (x : G) : (φ * ψ) x = φ (ψ x) :=
  (rfl)

@[simp]
theorem one_apply (x : G) : (1 : ContinuousAut G) x = x :=
  (rfl)

@[simp]
theorem inv_apply (φ : ContinuousAut G) (x : G) : φ⁻¹ x = φ.symm x :=
  (rfl)

/-- The forgetful homomorphism from continuous automorphisms to abstract automorphisms. -/
def toMulAut : ContinuousAut G →* MulAut G where
  toFun φ := φ.toMulEquiv
  map_one' := rfl
  map_mul' _ _ := rfl

@[simp]
theorem coe_toMulAut (φ : ContinuousAut G) : ⇑(toMulAut φ) = φ :=
  (rfl)

/-- A continuous automorphism is determined by its underlying abstract automorphism. -/
theorem toMulAut_injective : Function.Injective (toMulAut : ContinuousAut G →* MulAut G) :=
  fun _ _ h ↦ ContinuousMulEquiv.ext fun x ↦ by simpa using DFunLike.congr_fun h x

end Mul

section Monoid

variable (G : Type*) [Monoid G] [TopologicalSpace G]

/-- Continuous automorphisms act on their underlying monoid by evaluation. -/
instance : MulDistribMulAction (ContinuousAut G) G :=
  MulDistribMulAction.compHom G toMulAut

/-- The action of a continuous automorphism is its evaluation. -/
@[simp]
theorem smul_def (φ : ContinuousAut G) (x : G) : φ • x = φ x :=
  (rfl)

/-- The evaluation action of continuous automorphisms is faithful. -/
instance : FaithfulSMul (ContinuousAut G) G where
  eq_of_smul_eq_smul h := ContinuousMulEquiv.ext h

/-- Each continuous automorphism acts continuously on its underlying monoid. -/
instance : ContinuousConstSMul (ContinuousAut G) G where
  continuous_const_smul φ := φ.continuous

end Monoid

section Group

variable {G : Type*} [Group G] [TopologicalSpace G] [SeparatelyContinuousMul G]

/-- The inner automorphisms of a group with separately continuous multiplication:
`conj g x = g * x * g⁻¹`. This lifts `MulAut.conj` along `toMulAut` (`toMulAut_conj`). -/
def conj : G →* ContinuousAut G where
  toFun g :=
    { MulAut.conj g with
      continuous_toFun := IsTopologicalGroup.continuous_conj g
      continuous_invFun := (IsTopologicalGroup.continuous_conj g⁻¹).congr fun x ↦ by simp }
  map_one' := toMulAut_injective (map_one MulAut.conj)
  map_mul' a b := toMulAut_injective (map_mul MulAut.conj a b)

@[simp]
theorem conj_apply (g x : G) : conj g x = g * x * g⁻¹ :=
  (rfl)

@[simp]
theorem conj_symm_apply (g x : G) : (conj g).symm x = g⁻¹ * x * g :=
  (rfl)

theorem conj_inv_apply (g x : G) : (conj g)⁻¹ x = g⁻¹ * x * g :=
  (rfl)

@[simp]
theorem toMulAut_conj (g : G) : toMulAut (conj g) = MulAut.conj g :=
  (rfl)

/-- The kernel of the inner-automorphism homomorphism is the centre. -/
theorem ker_conj : (conj : G →* ContinuousAut G).ker = Subgroup.center G := by
  ext g
  simp only [MonoidHom.mem_ker, ContinuousMulEquiv.ext_iff, conj_apply, one_apply,
    Subgroup.mem_center_iff, mul_inv_eq_iff_eq_mul]
  exact forall_congr' fun _ ↦ eq_comm

/-- Conjugation is injective exactly when the centre is trivial. -/
theorem conj_injective_iff :
    Function.Injective (conj : G →* ContinuousAut G) ↔ Subgroup.center G = ⊥ := by
  rw [← MonoidHom.ker_eq_bot_iff, ker_conj]

/-- Every inner automorphism is trivial exactly when `G` is commutative. -/
theorem range_conj_eq_bot_iff :
    (conj : G →* ContinuousAut G).range = ⊥ ↔ IsMulCommutative G := by
  rw [MonoidHom.range_eq_bot_iff, ← MonoidHom.ker_eq_top_iff, ker_conj,
    Subgroup.center_eq_top_iff]

/-- Conjugating an inner automorphism by a continuous automorphism `φ` gives the inner
automorphism by the image under `φ`. -/
theorem mul_conj_mul_inv (φ : ContinuousAut G) (g : G) : φ * conj g * φ⁻¹ = conj (φ g) := by
  ext x
  simp

/-- The inner automorphisms form a normal subgroup of the continuous automorphisms. -/
instance normal_range_conj : (conj : G →* ContinuousAut G).range.Normal where
  conj_mem := by
    rintro _ ⟨g, rfl⟩ φ
    exact ⟨φ g, (mul_conj_mul_inv φ g).symm⟩

/-- A continuous automorphism that is inner as an abstract automorphism is the continuous inner
automorphism by the same element. -/
theorem eq_conj_of_toMulAut_eq_conj {φ : ContinuousAut G} {g : G}
    (h : toMulAut φ = MulAut.conj g) : φ = conj g :=
  toMulAut_injective (h.trans (toMulAut_conj g).symm)

/-- A continuous automorphism is inner exactly when its underlying abstract automorphism is. -/
theorem toMulAut_mem_range_conj_iff {φ : ContinuousAut G} :
    toMulAut φ ∈ (MulAut.conj : G →* MulAut G).range ↔ φ ∈ (conj : G →* ContinuousAut G).range :=
  ⟨fun ⟨g, hg⟩ ↦ ⟨g, (eq_conj_of_toMulAut_eq_conj hg.symm).symm⟩,
    fun ⟨g, hg⟩ ↦ ⟨g, hg ▸ (toMulAut_conj g).symm⟩⟩

end Group

end ContinuousAut

/-- The group of continuous outer automorphisms of `G`: continuous automorphisms modulo the inner
ones. -/
abbrev ContinuousOut (G : Type*) [Group G] [TopologicalSpace G] [SeparatelyContinuousMul G] :=
  ContinuousAut G ⧸ (ContinuousAut.conj : G →* ContinuousAut G).range

namespace ContinuousOut

variable {G : Type*} [Group G] [TopologicalSpace G] [SeparatelyContinuousMul G]

/-- The quotient map from continuous automorphisms to continuous outer automorphisms. -/
abbrev mk : ContinuousAut G →* ContinuousOut G :=
  QuotientGroup.mk' _

/-- Inner automorphisms have trivial outer class. -/
@[simp]
theorem mk_conj (g : G) : ((ContinuousAut.conj g : ContinuousAut G) : ContinuousOut G) = 1 :=
  (QuotientGroup.eq_one_iff _).mpr ⟨g, rfl⟩

/-- The class of a continuous automorphism in `ContinuousOut G` is trivial exactly when its
underlying abstract automorphism is inner. -/
theorem mk_eq_one_iff {φ : ContinuousAut G} :
    mk φ = 1 ↔ ContinuousAut.toMulAut φ ∈ (MulAut.conj : G →* MulAut G).range := by
  rw [ContinuousAut.toMulAut_mem_range_conj_iff]
  exact QuotientGroup.eq_one_iff φ

/-- For commutative `G` every inner automorphism is trivial, so the continuous outer automorphism
group is the continuous automorphism group. -/
def mulEquivOfIsMulCommutative [IsMulCommutative G] : ContinuousOut G ≃* ContinuousAut G :=
  (QuotientGroup.quotientMulEquivOfEq
    (ContinuousAut.range_conj_eq_bot_iff.mpr inferInstance)).trans QuotientGroup.quotientBot

@[simp]
theorem mulEquivOfIsMulCommutative_mk [IsMulCommutative G] (φ : ContinuousAut G) :
    mulEquivOfIsMulCommutative (φ : ContinuousOut G) = φ := by
  rw [mulEquivOfIsMulCommutative, MulEquiv.trans_apply, QuotientGroup.quotientMulEquivOfEq_mk,
    ← MulEquiv.eq_symm_apply, QuotientGroup.quotientBot_symm_apply]

@[simp]
theorem mulEquivOfIsMulCommutative_symm_apply [IsMulCommutative G] (φ : ContinuousAut G) :
    mulEquivOfIsMulCommutative.symm φ = (φ : ContinuousOut G) := by
  apply mulEquivOfIsMulCommutative.injective
  rw [MulEquiv.apply_symm_apply, mulEquivOfIsMulCommutative_mk]

end ContinuousOut

end TauCeti
