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

Over a field `K`, constructs `IsQuasiIso.linearHomotopyInverse`, `IsQuasiIso.homotopyEquiv`, and
`TauCeti.AInfinityHom.isHomotopyEquiv_iff_isQuasiIso` via `AInfinityAlgebra.cohomologyContraction`.

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

private noncomputable def cohomologyInvLinear {f : AInfinityHom AA BB} (hf : f.IsQuasiIso) :
    B →ₗ[K] A :=
  AA.cohomologyContraction.incl ∘ₗ hf.cohomologyLinearEquiv.symm.toLinearMap ∘ₗ
    BB.cohomologyContraction.proj
private theorem isHomogeneous_cohomologyInvLinear {f : AInfinityHom AA BB} (hf : f.IsQuasiIso) :
    LinearMap.IsHomogeneous hf.cohomologyInvLinear BB.grading.piece AA.grading.piece 0 :=
  LinearMap.isHomogeneous_def.2 fun _ _ hb ↦ by
    rw [add_zero, cohomologyInvLinear, LinearMap.comp_apply, LinearMap.comp_apply,
      LinearEquiv.coe_coe, ← hf.cohomologyMapInv_apply]
    have h₁ := BB.isHomogeneous_cohomologyContraction_proj.map_mem hb; rw [add_zero] at h₁
    simpa only [add_zero] using AA.isHomogeneous_cohomologyContraction_incl.map_mem
      (hf.cohomologyMapInv_mem_cohomologyGrading_piece h₁)
private theorem differential_comp_cohomologyInvLinear {f : AInfinityHom AA BB}
    (hf : f.IsQuasiIso) : AA.differential ∘ₗ hf.cohomologyInvLinear = 0 := by
  rw [cohomologyInvLinear, ← LinearMap.comp_assoc, AA.cohomologyContraction.dM_comp_incl,
    LinearMap.comp_zero, LinearMap.zero_comp]
private theorem cohomologyInvLinear_comp_differential {f : AInfinityHom AA BB}
    (hf : f.IsQuasiIso) : hf.cohomologyInvLinear ∘ₗ BB.differential = 0 := by
  rw [cohomologyInvLinear, LinearMap.comp_assoc, LinearMap.comp_assoc,
    BB.cohomologyContraction.proj_comp_dM, LinearMap.zero_comp, LinearMap.comp_zero,
    LinearMap.comp_zero]
private theorem cohomologyInvLinear_inv_comp_sub_id {f : AInfinityHom AA BB} (hf : f.IsQuasiIso) :
    hf.cohomologyInvLinear ∘ₗ f.linearPart - LinearMap.id =
      AA.differential ∘ₗ (hf.cohomologyInvLinear ∘ₗ f.linearPart ∘ₗ
          AA.cohomologyContraction.homotopy - AA.cohomologyContraction.homotopy) +
        (hf.cohomologyInvLinear ∘ₗ f.linearPart ∘ₗ AA.cohomologyContraction.homotopy -
          AA.cohomologyContraction.homotopy) ∘ₗ AA.differential := by
  have hinclA (c : AA.Cohomology) :
      hf.cohomologyInvLinear (f.linearPart (AA.cohomologyContraction.incl c)) =
        AA.cohomologyContraction.incl c := by
    have hcA := AA.cohomologyContraction_incl_mem_cycles c
    rw [cohomologyInvLinear, LinearMap.comp_apply, LinearMap.comp_apply,
      BB.cohomologyContraction_proj_of_mem_cycles (f.linearPart_mem_cycles hcA),
      ← f.cohomologyMap_cohomologyClass hcA, AA.cohomologyClass_cohomologyContraction_incl,
      ← hf.cohomologyLinearEquiv_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
  set cA := AA.cohomologyContraction; refine LinearMap.ext fun a ↦ ?_
  have hc := LinearMap.congr_fun cA.dM_comp_homotopy_add_homotopy_comp_dM a
  have ha : a = cA.incl (cA.proj a) + AA.differential (cA.homotopy a) +
      cA.homotopy (AA.differential a) := by
    simp only [LinearMap.add_apply, LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.id_apply]
      at hc
    exact (eq_add_of_sub_eq hc.symm).trans (by abel)
  have hfd := LinearMap.congr_fun f.differential_comp_linearPart (cA.homotopy a)
  have hgd := LinearMap.congr_fun hf.cohomologyInvLinear_comp_differential
    (f.linearPart (cA.homotopy a))
  have hdg := LinearMap.congr_fun hf.differential_comp_cohomologyInvLinear
    (f.linearPart (cA.homotopy a))
  simp only [LinearMap.comp_apply, LinearMap.zero_apply] at hfd hgd hdg
  conv_lhs => rw [LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.id_apply, ha]
  simp only [map_add, cA, hinclA, ← hfd, hgd, add_zero, LinearMap.add_apply, LinearMap.sub_apply,
    LinearMap.comp_apply, map_sub, hdg]; abel
private theorem cohomologyInvLinear_comp_inv_sub_id {f : AInfinityHom AA BB} (hf : f.IsQuasiIso) :
    f.linearPart ∘ₗ hf.cohomologyInvLinear - LinearMap.id =
      BB.differential ∘ₗ (BB.cohomologyContraction.homotopy ∘ₗ f.linearPart ∘ₗ
          hf.cohomologyInvLinear - BB.cohomologyContraction.homotopy) +
        (BB.cohomologyContraction.homotopy ∘ₗ f.linearPart ∘ₗ hf.cohomologyInvLinear -
          BB.cohomologyContraction.homotopy) ∘ₗ BB.differential := by
  set cA := AA.cohomologyContraction; set cB := BB.cohomologyContraction
  set eInv := hf.cohomologyLinearEquiv.symm.toLinearMap
  have hinclB (c : BB.Cohomology) :
      BB.differential (cB.homotopy (f.linearPart (cA.incl (eInv c)))) =
        f.linearPart (cA.incl (eInv c)) - cB.incl c := by
    have hw₀ := AA.cohomologyContraction_incl_mem_cycles (eInv c)
    have hw₁ := f.linearPart_mem_cycles hw₀
    have hw := BB.cycles.sub_mem hw₁ (BB.cohomologyContraction_incl_mem_cycles c)
    have hcl : BB.cohomologyClass hw = 0 := by
      rw [← BB.cohomologyContraction_proj_of_mem_cycles hw, map_sub,
        BB.cohomologyContraction_proj_of_mem_cycles hw₁, ← f.cohomologyMap_cohomologyClass hw₀,
        AA.cohomologyClass_cohomologyContraction_incl, cB.proj_incl_apply,
        ← hf.cohomologyLinearEquiv_apply]
      simp only [eInv, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply, sub_self]
    have hm := BB.m_one_cohomologyContraction_homotopy hw hcl
    have hhi := LinearMap.congr_fun cB.homotopy_comp_incl c
    simp only [LinearMap.comp_apply, LinearMap.zero_apply] at hhi
    simpa only [cA, cB, AInfinityAlgebra.differential_apply, map_sub, hhi, sub_zero] using hm
  refine LinearMap.ext fun b ↦ ?_
  have hc := LinearMap.congr_fun cB.dM_comp_homotopy_add_homotopy_comp_dM b
  have hgd := LinearMap.congr_fun hf.cohomologyInvLinear_comp_differential b
  have hin := hinclB (cB.proj b)
  simp only [LinearMap.add_apply, LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.id_apply,
    LinearMap.zero_apply, map_sub] at hc hgd ⊢
  rw [hgd, map_zero, map_zero, zero_sub]
  simp only [cohomologyInvLinear, cA, cB, eInv, LinearMap.comp_apply] at hin ⊢
  rw [hin]; exact sub_eq_zero.1 (Eq.trans (by abel) (sub_eq_zero.2 hc))

/-- Over a field, the linear part of an `A∞` quasi-isomorphism admits homogeneous chain-homotopy
inverse data. -/
noncomputable def linearHomotopyInverse {f : AInfinityHom AA BB} (hf : f.IsQuasiIso) :
    LinearHomotopyInverse f where
  inv := hf.cohomologyInvLinear
  homotopyLeft := hf.cohomologyInvLinear ∘ₗ f.linearPart ∘ₗ AA.cohomologyContraction.homotopy -
    AA.cohomologyContraction.homotopy
  homotopyRight := BB.cohomologyContraction.homotopy ∘ₗ f.linearPart ∘ₗ hf.cohomologyInvLinear -
    BB.cohomologyContraction.homotopy
  isHomogeneous_inv := hf.isHomogeneous_cohomologyInvLinear
  differential_comp_inv :=
    hf.differential_comp_cohomologyInvLinear.trans hf.cohomologyInvLinear_comp_differential.symm
  isHomogeneous_homotopyLeft := (hf.isHomogeneous_cohomologyInvLinear.compOfEq
    (f.isHomogeneous_linearPart.compOfEq AA.isHomogeneous_cohomologyContraction_homotopy (-1))
    (-1)).sub AA.isHomogeneous_cohomologyContraction_homotopy
  inv_comp_linearPart_sub_id := hf.cohomologyInvLinear_inv_comp_sub_id
  isHomogeneous_homotopyRight := (BB.isHomogeneous_cohomologyContraction_homotopy.compOfEq
    (f.isHomogeneous_linearPart.compOfEq hf.isHomogeneous_cohomologyInvLinear 0) (-1)).sub
    BB.isHomogeneous_cohomologyContraction_homotopy
  linearPart_comp_inv_sub_id := hf.cohomologyInvLinear_comp_inv_sub_id

/-- **Over a field, every `A∞` quasi-isomorphism has an `A∞` homotopy inverse.** -/
noncomputable def homotopyInverse {f : AInfinityHom AA BB} (hf : f.IsQuasiIso) :
    AInfinityHom BB AA := hf.linearHomotopyInverse.homotopyInverse

@[simp] theorem linearPart_homotopyInverse {f : AInfinityHom AA BB} (hf : f.IsQuasiIso) :
    hf.homotopyInverse.linearPart = AA.cohomologyContraction.incl ∘ₗ
      hf.cohomologyLinearEquiv.symm.toLinearMap ∘ₗ BB.cohomologyContraction.proj :=
  hf.linearHomotopyInverse.linearPart_homotopyInverse

/-- Over a field, every `A∞` quasi-isomorphism upgrades to a bundled two-sided `A∞` homotopy
equivalence with forward morphism `f`. -/
noncomputable def homotopyEquiv {f : AInfinityHom AA BB} (hf : f.IsQuasiIso) :
    HomotopyEquiv AA BB := hf.linearHomotopyInverse.homotopyEquiv

@[simp] theorem homotopyEquiv_hom {f : AInfinityHom AA BB} (hf : f.IsQuasiIso) :
    hf.homotopyEquiv.hom = f := hf.linearHomotopyInverse.homotopyEquiv_hom
@[simp] theorem homotopyEquiv_inv {f : AInfinityHom AA BB} (hf : f.IsQuasiIso) :
    hf.homotopyEquiv.inv = hf.homotopyInverse := hf.linearHomotopyInverse.homotopyEquiv_inv
theorem isHomotopyEquiv {f : AInfinityHom AA BB} (hf : f.IsQuasiIso) : f.IsHomotopyEquiv :=
  hf.homotopyEquiv_hom ▸ hf.homotopyEquiv.isHomotopyEquiv_hom
end IsQuasiIso

/-- **Over a field, an `A∞` morphism is a homotopy equivalence if and only if it is a
quasi-isomorphism.** -/
theorem isHomotopyEquiv_iff_isQuasiIso (f : AInfinityHom AA BB) :
    f.IsHomotopyEquiv ↔ f.IsQuasiIso :=
  ⟨IsHomotopyEquiv.isQuasiIso, IsQuasiIso.isHomotopyEquiv⟩
end AInfinityHom
end TauCeti
