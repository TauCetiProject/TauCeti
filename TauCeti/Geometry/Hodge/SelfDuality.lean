/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.PerfectPairing.Basic
public import TauCeti.Geometry.Hodge.Dual
public import TauCeti.Geometry.Hodge.HodgeForm
public import TauCeti.Geometry.Hodge.Tate.Twist
import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
import TauCeti.Geometry.Hodge.Substructure
import TauCeti.LinearAlgebra.FreeModule.Int

/-!
# Self-duality from a polarization

A polarization of a pure Hodge structure of weight `n` identifies its complex vector space with
its complex dual. The weight of the dual is `-n`, so the comparison is a Hodge morphism only after
twisting the dual by `-n`; this restores weight `n`. On the lattice the same map need not be an
equivalence: its cokernel records the discriminant of the integral polarizing form. It is always
injective, and it is an equivalence exactly when the form is a perfect pairing.

This is the self-duality supplied by the Hodge--Riemann bilinear relations, and it makes duals of
polarizable structures polarizable. The inverse form on the dual is in general only rational, since
the inverse of an integral form is integral only when the form is a perfect pairing. Instead, the
image of the integral self-duality has finite index `c`, so there is a Hodge morphism
`V^*(-n) → V` inverting self-duality up to the factor `c`. That morphism is injective, so the
polarizing form of `V` pulls back along it to a polarizing form of `V^*(-n)`, and a Tate twist
turns this into a polarizing form of `V^*`.

## Main declarations

* `TauCeti.Hodge.HodgeStructure.dualTateTwist`: the same-weight target `V^*(-n)`.
* `TauCeti.Hodge.Polarization.toDualHom`: the Hodge morphism from a polarized structure to the
  appropriately twisted dual.
* `TauCeti.Hodge.Polarization.toDualHom_toLinearMap`: its complex action is the polarizing form.
* `TauCeti.Hodge.Polarization.toDualHom_toLinearMap_bijective`: the complex self-duality is an
  isomorphism.
* `TauCeti.Hodge.Polarization.toDualHom_toIntLinearMap_bijective_iff_isPerfPair`: the integral
  self-duality is an isomorphism exactly for a perfect integral polarizing form.
* `TauCeti.Hodge.Polarization.exists_comp_toDualHom_eq_nsmul_id`: the integral self-duality is
  invertible up to a nonzero integer.
* `TauCeti.Hodge.IsPolarizable.dual`: the dual of a polarizable pure Hodge structure is
  polarizable.

## References

Deligne, *Théorie de Hodge II*, §2.1; Peters--Steenbrink, *Mixed Hodge Structures*, §2.1.
-/

public section

namespace TauCeti.Hodge

universe u v

variable {V : Type u} {Vℂ : Type v}
variable [AddCommGroup V] [Module.Free ℤ V] [Module.Finite ℤ V]
variable [AddCommGroup Vℂ] [Module ℂ Vℂ]
variable {ιℂ : V →ₗ[ℤ] Vℂ} {hℂ : IsBaseChange ℂ ιℂ} {n : ℤ}
variable {hs : HodgeStructure hℂ n}

namespace HodgeStructure

/-- The Tate twist of the dual that has the same weight as the original Hodge structure. -/
noncomputable def dualTateTwist (hs : HodgeStructure hℂ n) :
    HodgeStructure (isBaseChange_dualLatticeMap hℂ) n where
  F p := hs.dual.F (p - n)
  F_antitone _ _ hpq := hs.dual.F_antitone (by omega)
  F_top := by
    obtain ⟨p, hp⟩ := hs.dual.F_top
    exact ⟨p + n, by simpa only [add_sub_cancel_right] using hp⟩
  opposed p := by
    have hindex : n + 1 - p - n = -n + 1 - (p - n) := by ring
    simpa only [hindex] using hs.dual.opposed (p - n)

/-- The filtration of the same-weight dual target is the translated dual filtration. -/
@[simp]
theorem dualTateTwist_F (hs : HodgeStructure hℂ n) (p : ℤ) :
    hs.dualTateTwist.F p = hs.dual.F (p - n) := by
  rfl

/-- The conjugate filtration of the same-weight dual target is translated in the same way. -/
@[simp]
theorem dualTateTwist_conjF (hs : HodgeStructure hℂ n) (p : ℤ) :
    hs.dualTateTwist.conjF p = hs.dual.conjF (p - n) := by
  rw [HodgeStructureOn.conjF_def, HodgeStructureOn.conjF_def, dualTateTwist_F]

/-- The `p`-th Hodge component of `V^*(-n)` is the `(p-n)`-th component of `V^*`. -/
@[simp]
theorem dualTateTwist_piece (hs : HodgeStructure hℂ n) (p : ℤ) :
    hs.dualTateTwist.piece p = hs.dual.piece (p - n) := by
  rw [HodgeStructureOn.piece_def, HodgeStructureOn.piece_def, dualTateTwist_F,
    dualTateTwist_conjF]
  congr 2
  ring

/-- The Hodge numbers of `V^*(-n)` are the translated Hodge numbers of `V^*`. -/
@[simp]
theorem dualTateTwist_hodgeNumber (hs : HodgeStructure hℂ n) (p : ℤ) :
    hs.dualTateTwist.hodgeNumber p = hs.dual.hodgeNumber (p - n) := by
  rw [HodgeStructureOn.hodgeNumber_def, HodgeStructureOn.hodgeNumber_def,
    dualTateTwist_piece]

end HodgeStructure

namespace Polarization

/-- A polarization gives an integral Hodge morphism to the `(-n)`-th Tate twist of the dual.

The twist is forced by weights: the dual has weight `-n`, and twisting it by `-n` changes its
weight to `-n - 2(-n) = n`. -/
noncomputable def toDualHom (P : Polarization hℂ hs) :
    HodgeStructure.Hom hs hs.dualTateTwist where
  toIntLinearMap := P.Qint
  map_mem_F p x hx := by
    rw [integralMapToComplex_bilinForm, HodgeStructure.dualTateTwist_F,
      HodgeStructure.dual_F, HodgeStructureOn.dual_F, Submodule.mem_dualAnnihilator]
    intro y hy
    have hindex : 1 - (p - n) = n + 1 - p := by ring
    rw [hindex] at hy
    rw [← P.Q_def]
    exact P.Q_orthogonal p hx hy

/-- The integral linear map underlying self-duality is the integral polarizing form. -/
@[simp]
theorem toDualHom_toIntLinearMap (P : Polarization hℂ hs) :
    P.toDualHom.toIntLinearMap = P.Qint :=
  (rfl)

/-- The complex action of polarization self-duality is the complex polarizing form viewed as a
linear map to the dual. -/
@[simp]
theorem toDualHom_toLinearMap (P : Polarization hℂ hs) :
    P.toDualHom.toLinearMap = P.Q := by
  rw [HodgeStructure.Hom.toLinearMap_def, toDualHom_toIntLinearMap,
    integralMapToComplex_bilinForm, Q_def]

/-- The integral self-duality map induced by a polarization is injective. -/
theorem toDualHom_toIntLinearMap_injective (P : Polarization hℂ hs) :
    Function.Injective P.toDualHom.toIntLinearMap := by
  rw [toDualHom_toIntLinearMap]
  exact LinearMap.ker_eq_bot.mp P.isPolarization.nondegenerate.ker_eq_bot

/-- The complex self-duality map induced by a polarization is injective. -/
theorem toDualHom_toLinearMap_injective (P : Polarization hℂ hs) :
    Function.Injective P.toDualHom.toLinearMap := by
  rw [toDualHom_toLinearMap]
  exact LinearMap.ker_eq_bot.mp P.Q_nondegenerate.ker_eq_bot

/-- The complex self-duality map induced by a polarization is bijective. -/
theorem toDualHom_toLinearMap_bijective (P : Polarization hℂ hs) :
    Function.Bijective P.toDualHom.toLinearMap := by
  let _ : Module.Finite ℂ Vℂ := hℂ.finite
  rw [toDualHom_toLinearMap]
  exact (P.Q.toDual P.Q_nondegenerate).bijective

/-- The integral self-duality map is bijective exactly when the integral polarizing form is a
perfect pairing. This is the unimodularity condition on the polarized lattice. -/
theorem toDualHom_toIntLinearMap_bijective_iff_isPerfPair (P : Polarization hℂ hs) :
    Function.Bijective P.toDualHom.toIntLinearMap ↔ P.Qint.IsPerfPair := by
  rw [toDualHom_toIntLinearMap]
  constructor
  · intro h
    exact LinearMap.IsPerfPair.of_bijective P.Qint h
  · intro h
    exact h.bijective_left

/-- **Self-duality is invertible up to a nonzero integer.** For a polarization of `V`, there is a
Hodge morphism `g : V^*(-n) → V` such that composing it with self-duality, in either order, is
multiplication by a nonzero natural number `c`. Over `ℚ`, `c⁻¹ • g` is the inverse of
self-duality. -/
theorem exists_comp_toDualHom_eq_nsmul_id (P : Polarization hℂ hs) :
    ∃ c : ℕ, c ≠ 0 ∧ ∃ g : HodgeStructure.Hom hs.dualTateTwist hs,
      P.toDualHom.comp g = c • HodgeStructure.Hom.id _ ∧
        g.comp P.toDualHom = c • HodgeStructure.Hom.id _ := by
  obtain ⟨c, hc, g, hfg, hgf⟩ := LinearMap.exists_comp_eq_nsmul_id_of_injective
    P.toDualHom_toIntLinearMap_injective (Module.finrank_linearMap_self ℤ ℤ V).symm
  have hcomplex : P.toDualHom.toLinearMap ∘ₗ
      integralMapToComplex (isBaseChange_dualLatticeMap hℂ) ιℂ g = c • LinearMap.id := by
    rw [HodgeStructure.Hom.toLinearMap_def, ← integralMapToComplex_comp, hfg,
      integralMapToComplex_nsmul, integralMapToComplex_id]
  let g' : HodgeStructure.Hom hs.dualTateTwist hs :=
    { toIntLinearMap := g
      map_mem_F p y hy := by
        -- `c • y` lies in the image of self-duality, which by strictness meets `F^p` of the
        -- target in the image of `F^p` of the source.
        have hmem : c • y ∈ LinearMap.range P.toDualHom.toLinearMap ⊓ hs.dualTateTwist.F p :=
          ⟨⟨_, by simpa using congr($hcomplex y)⟩, nsmul_mem hy c⟩
        rw [P.toDualHom.range_inf_F] at hmem
        obtain ⟨x, hx, hxy⟩ := hmem
        have hgy : integralMapToComplex (isBaseChange_dualLatticeMap hℂ) ιℂ g y = x := by
          refine P.toDualHom_toLinearMap_injective ?_
          rw [hxy]
          simpa using congr($hcomplex y)
        exact hgy ▸ hx }
  refine ⟨c, hc, g', HodgeStructure.Hom.ext fun x ↦ ?_, HodgeStructure.Hom.ext fun x ↦ ?_⟩
  · simpa [g'] using congr($hfg x)
  · simpa [g'] using congr($hgf x)

end Polarization

/-- The same-weight twist `V^*(-n)` of the dual of a polarizable pure Hodge structure is
polarizable: a polarizing form of `V` pulls back along an inverse of self-duality up to a nonzero
integer. -/
theorem IsPolarizable.dualTateTwist (h : IsPolarizable hℂ hs) :
    IsPolarizable (isBaseChange_dualLatticeMap hℂ) hs.dualTateTwist := by
  obtain ⟨P⟩ := isPolarizable_iff_nonempty.mp h
  obtain ⟨c, hc, g, hfg, -⟩ := P.exists_comp_toDualHom_eq_nsmul_id
  refine h.of_injective g fun y y' hyy' ↦ smul_right_injective (Module.Dual ℤ V) hc ?_
  have hcomp (z : Module.Dual ℤ V) : P.Qint (g.toIntLinearMap z) = c • z := by
    simpa using congr(HodgeStructure.Hom.toIntLinearMap $hfg z)
  simp only [← hcomp, hyy']

/-- **The dual of a polarizable pure Hodge structure is polarizable.** -/
theorem IsPolarizable.dual (h : IsPolarizable hℂ hs) :
    IsPolarizable (isBaseChange_dualLatticeMap hℂ) hs.dual := by
  obtain ⟨P⟩ := isPolarizable_iff_nonempty.mp h.dualTateTwist
  refine (⟨_, P.isPolarization.of_F_eq_F_add n (by ring) fun p ↦ ?_⟩ :
    Polarization _ hs.dual).isPolarizable
  rw [HodgeStructure.dualTateTwist_F, add_sub_cancel_right]

end TauCeti.Hodge
