/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.AInfinity.Algebra.Hom.Inverse.Vogt
public import TauCeti.Algebra.Homology.AInfinity.Algebra.Transfer.Cohomology
import Mathlib.Tactic.Abel

/-!
# Homotopy inverses of A-infinity quasi-isomorphisms over a field

Over a field `K`, every `A∞` algebra admits a homogeneous deformation retract onto its cohomology
(`AInfinityAlgebra.cohomologyContraction`). Composing these contractions with the inverse induced
map on cohomology produces `LinearHomotopyInverse f` for any `A∞` quasi-isomorphism `f`, which
lifts via the ring-level theorem to a two-sided `A∞` homotopy equivalence.

## Main definitions

* `TauCeti.AInfinityHom.IsQuasiIso.linearHomotopyInverse`: linear inverse data over a field.
* `TauCeti.AInfinityHom.IsQuasiIso.homotopyInverse`: `A∞` homotopy inverse of a quasi-isomorphism.
* `TauCeti.AInfinityHom.IsQuasiIso.homotopyEquiv`: bundled `HomotopyEquiv` over a field.

## Main results

* `TauCeti.AInfinityHom.IsQuasiIso.isHomotopyEquiv`: quasi-isomorphisms are homotopy equivalences.
* `TauCeti.AInfinityHom.isHomotopyEquiv_iff_isQuasiIso`: homotopy equivalence iff quasi-isomorphism.

## References

* B. Keller, *Introduction to A-infinity algebras and modules*, Section 3.7.
* K. Lefèvre-Hasegawa, *Sur les A-infini catégories*, Chapter 1, Theorem 1.3.1.2.
-/

public section
namespace TauCeti
universe uK uA uB
namespace AInfinityHom
variable {K : Type uK} {A : Type uA} {B : Type uB} [Field K] [AddCommGroup A] [Module K A]
  [AddCommGroup B] [Module K B] {AA : AInfinityAlgebra K A} {BB : AInfinityAlgebra K B}
namespace IsQuasiIso
variable {f : AInfinityHom AA BB} (hf : f.IsQuasiIso)

private noncomputable def cohomologyInvLinear : B →ₗ[K] A :=
  AA.cohomologyContraction.incl ∘ₗ hf.cohomologyLinearEquiv.symm.toLinearMap ∘ₗ
    BB.cohomologyContraction.proj
private theorem isHomogeneous_cohomologyInvLinear :
    LinearMap.IsHomogeneous hf.cohomologyInvLinear BB.grading.piece AA.grading.piece 0 :=
  LinearMap.isHomogeneous_def.2 fun _ _ hb ↦ by
    simp only [add_zero, cohomologyInvLinear, LinearMap.comp_apply, LinearEquiv.coe_coe,
      ← hf.cohomologyMapInv_apply]
    simpa only [add_zero] using AA.isHomogeneous_cohomologyContraction_incl.map_mem
      (hf.cohomologyMapInv_mem_cohomologyGrading_piece
        (by simpa only [add_zero] using BB.isHomogeneous_cohomologyContraction_proj.map_mem hb))
private theorem differential_comp_cohomologyInvLinear :
    AA.differential ∘ₗ hf.cohomologyInvLinear = 0 := by
  simp only [cohomologyInvLinear, ← LinearMap.comp_assoc, AA.cohomologyContraction.dM_comp_incl,
    LinearMap.comp_zero, LinearMap.zero_comp]
private theorem cohomologyInvLinear_comp_differential :
    hf.cohomologyInvLinear ∘ₗ BB.differential = 0 := by
  simp only [cohomologyInvLinear, LinearMap.comp_assoc, BB.cohomologyContraction.proj_comp_dM,
    LinearMap.zero_comp, LinearMap.comp_zero]

/-- Over a field, the linear part of an `A∞` quasi-isomorphism admits homogeneous chain-homotopy
inverse data. -/
noncomputable def linearHomotopyInverse : LinearHomotopyInverse f where
  inv := hf.cohomologyInvLinear
  homotopyLeft := hf.cohomologyInvLinear ∘ₗ f.linearPart ∘ₗ AA.cohomologyContraction.homotopy -
    AA.cohomologyContraction.homotopy
  homotopyRight := BB.cohomologyContraction.homotopy ∘ₗ f.linearPart ∘ₗ hf.cohomologyInvLinear -
    BB.cohomologyContraction.homotopy
  isHomogeneous_inv := hf.isHomogeneous_cohomologyInvLinear
  differential_comp_inv :=
    hf.differential_comp_cohomologyInvLinear.trans hf.cohomologyInvLinear_comp_differential.symm
  isHomogeneous_homotopyLeft :=
    (add_zero (-1 : ℤ) ▸ hf.isHomogeneous_cohomologyInvLinear.comp
      (add_zero (-1 : ℤ) ▸ f.isHomogeneous_linearPart.comp
        AA.isHomogeneous_cohomologyContraction_homotopy)).sub
      AA.isHomogeneous_cohomologyContraction_homotopy
  inv_comp_linearPart_sub_id := LinearMap.ext fun a ↦ by
    set cA := AA.cohomologyContraction; let u := f.linearPart (cA.homotopy a)
    have hinclA (c : AA.Cohomology) : hf.cohomologyInvLinear (f.linearPart (cA.incl c)) =
        cA.incl c := by
      have hcA := AA.cohomologyContraction_incl_mem_cycles c
      rw [cohomologyInvLinear, LinearMap.comp_apply, LinearMap.comp_apply,
        BB.cohomologyContraction_proj_of_mem_cycles (f.linearPart_mem_cycles hcA),
        ← f.cohomologyMap_cohomologyClass hcA, AA.cohomologyClass_cohomologyContraction_incl,
        ← hf.cohomologyLinearEquiv_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
    have ha : a = cA.incl (cA.proj a) + AA.differential (cA.homotopy a) +
        cA.homotopy (AA.differential a) := by
      have hc := LinearMap.congr_fun cA.dM_comp_homotopy_add_homotopy_comp_dM a
      simp only [LinearMap.add_apply, LinearMap.sub_apply, LinearMap.comp_apply,
        LinearMap.id_apply] at hc; exact (eq_add_of_sub_eq hc.symm).trans (by abel)
    have hfd := LinearMap.congr_fun f.differential_comp_linearPart (cA.homotopy a)
    have hgd := LinearMap.congr_fun hf.cohomologyInvLinear_comp_differential u
    have hdg := LinearMap.congr_fun hf.differential_comp_cohomologyInvLinear u
    simp only [u, LinearMap.comp_apply, LinearMap.zero_apply] at hfd hgd hdg
    conv_lhs => rw [LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.id_apply, ha]
    simp only [map_add, hinclA, ← hfd, hgd, add_zero, LinearMap.add_apply, LinearMap.sub_apply,
      LinearMap.comp_apply, map_sub, hdg]; abel
  isHomogeneous_homotopyRight :=
    (zero_add (-1 : ℤ) ▸ BB.isHomogeneous_cohomologyContraction_homotopy.comp
      (add_zero (0 : ℤ) ▸ f.isHomogeneous_linearPart.comp
        hf.isHomogeneous_cohomologyInvLinear)).sub
      BB.isHomogeneous_cohomologyContraction_homotopy
  linearPart_comp_inv_sub_id := LinearMap.ext fun b ↦ by
    set cA := AA.cohomologyContraction; set cB := BB.cohomologyContraction
    set eInv := hf.cohomologyLinearEquiv.symm.toLinearMap
    have hin : BB.differential (cB.homotopy (f.linearPart (cA.incl (eInv (cB.proj b))))) =
        f.linearPart (cA.incl (eInv (cB.proj b))) - cB.incl (cB.proj b) := by
      have hw₀ := AA.cohomologyContraction_incl_mem_cycles (eInv (cB.proj b))
      have hw := BB.cycles.sub_mem (f.linearPart_mem_cycles hw₀)
        (BB.cohomologyContraction_incl_mem_cycles (cB.proj b))
      have hcl : BB.cohomologyClass hw = 0 := by
        rw [← BB.cohomologyContraction_proj_of_mem_cycles hw, map_sub,
          BB.cohomologyContraction_proj_of_mem_cycles (f.linearPart_mem_cycles hw₀),
          ← f.cohomologyMap_cohomologyClass hw₀, AA.cohomologyClass_cohomologyContraction_incl,
          cB.proj_incl_apply, ← hf.cohomologyLinearEquiv_apply]
        simp only [eInv, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply, sub_self]
      have hhi : cB.homotopy (cB.incl (cB.proj b)) = 0 :=
        LinearMap.congr_fun cB.homotopy_comp_incl (cB.proj b)
      simpa only [cA, cB, AInfinityAlgebra.differential_apply, map_sub, hhi, sub_zero] using
        BB.m_one_cohomologyContraction_homotopy hw hcl
    have hc := LinearMap.congr_fun cB.dM_comp_homotopy_add_homotopy_comp_dM b
    have hgd := LinearMap.congr_fun hf.cohomologyInvLinear_comp_differential b
    simp only [LinearMap.add_apply, LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.id_apply,
      LinearMap.zero_apply, map_sub] at hc hgd ⊢
    rw [hgd, map_zero, map_zero, zero_sub]
    simp only [cohomologyInvLinear, cA, cB, eInv, LinearMap.comp_apply] at hin ⊢
    rw [hin]; exact sub_eq_zero.1 (Eq.trans (by abel) (sub_eq_zero.2 hc))

/-- The underlying linear inverse map of `hf.linearHomotopyInverse`. -/
@[simp] theorem linearHomotopyInverse_inv :
    hf.linearHomotopyInverse.inv = AA.cohomologyContraction.incl ∘ₗ
      hf.cohomologyLinearEquiv.symm.toLinearMap ∘ₗ BB.cohomologyContraction.proj := (rfl)

/-- **Over a field, every `A∞` quasi-isomorphism has an `A∞` homotopy inverse.** -/
noncomputable def homotopyInverse : AInfinityHom BB AA := hf.linearHomotopyInverse.homotopyInverse

/-- The linear part of `hf.homotopyInverse` is the contraction-induced chain inverse. -/
@[simp] theorem linearPart_homotopyInverse :
    hf.homotopyInverse.linearPart = AA.cohomologyContraction.incl ∘ₗ
      hf.cohomologyLinearEquiv.symm.toLinearMap ∘ₗ BB.cohomologyContraction.proj :=
  hf.linearHomotopyInverse.linearPart_homotopyInverse

/-- Over a field, every `A∞` quasi-isomorphism upgrades to a bundled two-sided `A∞` homotopy
equivalence with forward morphism `f`. -/
noncomputable def homotopyEquiv : HomotopyEquiv AA BB := hf.linearHomotopyInverse.homotopyEquiv

@[simp] theorem homotopyEquiv_hom : hf.homotopyEquiv.hom = f :=
  hf.linearHomotopyInverse.homotopyEquiv_hom
@[simp] theorem homotopyEquiv_inv : hf.homotopyEquiv.inv = hf.homotopyInverse :=
  hf.linearHomotopyInverse.homotopyEquiv_inv

include hf in
/-- Over a field, every `A∞` quasi-isomorphism is an `A∞` homotopy equivalence. -/
theorem isHomotopyEquiv : f.IsHomotopyEquiv :=
  hf.homotopyEquiv_hom ▸ hf.homotopyEquiv.isHomotopyEquiv_hom
end IsQuasiIso

/-- **Over a field, an `A∞` morphism is a homotopy equivalence if and only if it is a
quasi-isomorphism.** -/
theorem isHomotopyEquiv_iff_isQuasiIso (f : AInfinityHom AA BB) :
    f.IsHomotopyEquiv ↔ f.IsQuasiIso :=
  ⟨IsHomotopyEquiv.isQuasiIso, IsQuasiIso.isHomotopyEquiv⟩
end AInfinityHom
end TauCeti
