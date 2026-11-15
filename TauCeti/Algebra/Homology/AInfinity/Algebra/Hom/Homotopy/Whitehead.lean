/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.AInfinity.Algebra.Hom.Homotopy.Inverse
import Mathlib.Tactic.Abel
import TauCeti.Algebra.Homology.AInfinity.Algebra.Transfer.Cohomology

/-!
# The Whitehead theorem for A-infinity algebras over a field

Over a field `K`, conjugating `hf.cohomologyLinearEquiv : H(A) ≃ₗ[K] H(B)` by the homogeneous
contractions `AInfinityAlgebra.cohomologyContraction` and transporting along
`-(h_B ∘ f₁ ∘ i_A ∘ p_A + f₁ ∘ h_A)` extends `f.linearPart` of any `A∞` quasi-isomorphism `f` to a
homogeneous degree-`(-1)` linear chain-homotopy equivalence (`IsQuasiIso.linearHomotopyEquiv`).
Lifting via `HomotopyEquiv.ofLinear` gives the Whitehead theorem (`HomotopyEquiv.ofQuasiIso`,
`isHomotopyEquiv_iff_isQuasiIso`).

## Main definitions

* `TauCeti.AInfinityHom.IsQuasiIso.linearHomotopyEquiv`,
  `TauCeti.AInfinityHom.HomotopyEquiv.ofQuasiIso`.

## Main results

* `TauCeti.AInfinityHom.IsQuasiIso.isHomotopyEquiv`,
  `TauCeti.AInfinityHom.isHomotopyEquiv_iff_isQuasiIso`.

## References

* B. Keller, *Introduction to A-infinity algebras and modules*, Section 3.7.
* K. Lefèvre-Hasegawa, *Sur les A-infini catégories*, Université Paris 7 (2003), Théorème 1.3.3.1.
* J.-L. Loday and B. Vallette, *Algebraic Operads*, Theorem 10.4.4.
-/

public section

namespace TauCeti

universe uK uA uB

namespace AInfinityHom

variable {K : Type uK} {A : Type uA} {B : Type uB}
  [Field K] [AddCommGroup A] [Module K A] [AddCommGroup B] [Module K B]
  {AA : AInfinityAlgebra K A} {BB : AInfinityAlgebra K B}

private theorem cohomologyContraction_proj_comp_linearPart_comp_incl
    {f : AInfinityHom AA BB} (hf : f.IsQuasiIso) :
    BB.cohomologyContraction.proj ∘ₗ f.linearPart ∘ₗ AA.cohomologyContraction.incl =
      hf.cohomologyLinearEquiv.toLinearMap :=
  LinearMap.ext fun c ↦ by
    rw [LinearMap.comp_apply, LinearMap.comp_apply, BB.cohomologyContraction_proj_of_mem_cycles
        (f.linearPart_mem_cycles (AA.cohomologyContraction_incl_mem_cycles c)),
      ← f.cohomologyMap_cohomologyClass (AA.cohomologyContraction_incl_mem_cycles c),
      AA.cohomologyClass_cohomologyContraction_incl, LinearEquiv.coe_coe,
      hf.cohomologyLinearEquiv_apply]
private noncomputable def cohomologyConjLinearHomotopyEquiv {f : AInfinityHom AA BB}
    (hf : f.IsQuasiIso) : LinearHomotopyEquiv AA.differential BB.differential :=
  let eH : LinearHomotopyEquiv (0 : Module.End K AA.Cohomology) (0 : Module.End K BB.Cohomology) :=
    LinearHomotopyEquiv.ofLinearEquiv hf.cohomologyLinearEquiv (by simp)
  (AA.cohomologyContraction.toLinearContraction.toLinearHomotopyEquiv.trans eH).trans
    BB.cohomologyContraction.toLinearContraction.toLinearHomotopyEquiv.symm
private noncomputable def cohomologyConjHomotopy (f : AInfinityHom AA BB) : A →ₗ[K] B :=
  -(BB.cohomologyContraction.homotopy ∘ₗ f.linearPart ∘ₗ
      AA.cohomologyContraction.incl ∘ₗ AA.cohomologyContraction.proj +
    f.linearPart ∘ₗ AA.cohomologyContraction.homotopy)
private theorem isHomogeneous_cohomologyConjHomotopy (f : AInfinityHom AA BB) :
    LinearMap.IsHomogeneous (cohomologyConjHomotopy f) AA.grading.piece BB.grading.piece (-1) :=
  LinearMap.IsHomogeneous.neg <| LinearMap.IsHomogeneous.add
    (by
      simpa only [zero_add, add_zero] using BB.isHomogeneous_cohomologyContraction_homotopy.comp
        (f.isHomogeneous_linearPart.comp (AA.isHomogeneous_cohomologyContraction_incl.comp
          AA.isHomogeneous_cohomologyContraction_proj)))
    (add_zero (-1 : ℤ) ▸
      f.isHomogeneous_linearPart.comp AA.isHomogeneous_cohomologyContraction_homotopy)
private theorem cohomologyContraction_conj_sub_linearPart
    {f : AInfinityHom AA BB} (hf : f.IsQuasiIso) :
    (cohomologyConjLinearHomotopyEquiv hf).hom - f.linearPart =
      BB.differential ∘ₗ cohomologyConjHomotopy f +
        cohomologyConjHomotopy f ∘ₗ AA.differential := by
  set cA := AA.cohomologyContraction; set cB := BB.cohomologyContraction
  refine LinearMap.ext fun a ↦ ?_
  have hmid := congrArg cB.incl (LinearMap.congr_fun
    (cohomologyContraction_proj_comp_linearPart_comp_incl hf) (cA.proj a)).symm
  have hf_diff := LinearMap.congr_fun f.differential_comp_linearPart
  simp only [cohomologyConjLinearHomotopyEquiv, cohomologyConjHomotopy,
    LinearHomotopyEquiv.trans_hom, LinearHomotopyEquiv.symm_hom,
    LinearHomotopyEquiv.ofLinearEquiv_hom, LinearContraction.toLinearHomotopyEquiv_hom,
    LinearContraction.toLinearHomotopyEquiv_inv, LinearMap.sub_apply, LinearMap.add_apply,
    LinearMap.neg_apply, LinearMap.comp_apply] at hmid hf_diff ⊢
  rw [hmid, cB.incl_proj_apply, hf_diff (cA.incl (cA.proj a)), cA.dM_incl_apply, cA.proj_dM_apply]
  simp only [LinearMap.zero_apply, map_zero, map_neg, map_add, zero_add, sub_zero]
  rw [cA.incl_proj_apply a, map_sub, map_sub, ← hf_diff (cA.homotopy a)]; abel

section Whitehead
variable {f : AInfinityHom AA BB} (hf : f.IsQuasiIso)

/-- Over a field, `f.linearPart` of an `A∞` quasi-isomorphism extends to a homogeneous
degree-`(-1)` linear chain-homotopy equivalence between the unary complexes. -/
noncomputable def IsQuasiIso.linearHomotopyEquiv :
    LinearHomotopyEquiv AA.differential BB.differential :=
  (cohomologyConjLinearHomotopyEquiv hf).ofHomotopy f.differential_comp_linearPart
    (cohomologyConjHomotopy f) (cohomologyContraction_conj_sub_linearPart hf)
@[simp] theorem IsQuasiIso.hom_linearHomotopyEquiv : hf.linearHomotopyEquiv.hom = f.linearPart :=
  LinearHomotopyEquiv.ofHomotopy_hom _ _ _ _

/-- The linear chain-homotopy equivalence associated to a quasi-isomorphism over a field is
homogeneous with homotopy degree `-1`. -/
theorem IsQuasiIso.isHomogeneous_linearHomotopyEquiv :
    hf.linearHomotopyEquiv.IsHomogeneous AA.grading.piece BB.grading.piece (-1) :=
  have hcA := AA.cohomologyContraction.toLinearContraction.isHomogeneous_toLinearHomotopyEquiv
    AA.isHomogeneous_cohomologyContraction_incl AA.isHomogeneous_cohomologyContraction_proj
    AA.isHomogeneous_cohomologyContraction_homotopy
  have hcB := (BB.cohomologyContraction.toLinearContraction.isHomogeneous_toLinearHomotopyEquiv
    BB.isHomogeneous_cohomologyContraction_incl BB.isHomogeneous_cohomologyContraction_proj
    BB.isHomogeneous_cohomologyContraction_homotopy).symm
  have heH_hom : LinearMap.IsHomogeneous hf.cohomologyLinearEquiv.toLinearMap
      AA.cohomologyGrading.piece BB.cohomologyGrading.piece 0 :=
    LinearMap.isHomogeneous_def.2 fun _ _ hc ↦ by
      rw [add_zero, LinearEquiv.coe_coe, hf.cohomologyLinearEquiv_apply]
      exact f.cohomologyMap_mem_cohomologyGrading_piece hc
  ((hcA.trans (LinearHomotopyEquiv.isHomogeneous_ofLinearEquiv
    (dM := (0 : Module.End K AA.Cohomology)) (dN := (0 : Module.End K BB.Cohomology))
    (by simp) heH_hom heH_hom.linearEquiv_symm (-1))).trans hcB).ofHomotopy
    f.differential_comp_linearPart f.isHomogeneous_linearPart
    (isHomogeneous_cohomologyConjHomotopy f) (cohomologyContraction_conj_sub_linearPart hf)

/-- Over a field, promote an `A∞` quasi-isomorphism to a bundled `A∞` homotopy equivalence. -/
noncomputable def HomotopyEquiv.ofQuasiIso : HomotopyEquiv AA BB :=
  HomotopyEquiv.ofLinear f hf.linearHomotopyEquiv hf.hom_linearHomotopyEquiv
    hf.isHomogeneous_linearHomotopyEquiv
@[simp] theorem HomotopyEquiv.hom_ofQuasiIso : (HomotopyEquiv.ofQuasiIso hf).hom = f :=
  HomotopyEquiv.hom_ofLinear _ _ _ _
@[simp] theorem HomotopyEquiv.linearPart_inv_ofQuasiIso :
    (HomotopyEquiv.ofQuasiIso hf).inv.linearPart = hf.linearHomotopyEquiv.inv :=
  HomotopyEquiv.linearPart_inv_ofLinear _ _ _ _
end Whitehead

/-- Over a field, every `A∞` quasi-isomorphism is an `A∞` homotopy equivalence. -/
theorem IsQuasiIso.isHomotopyEquiv {f : AInfinityHom AA BB} (hf : f.IsQuasiIso) :
    f.IsHomotopyEquiv :=
  HomotopyEquiv.hom_ofQuasiIso hf ▸ (HomotopyEquiv.ofQuasiIso hf).isHomotopyEquiv_hom

/-- **Whitehead theorem for `A∞` algebras over a field.**  An `A∞` morphism over a field is a
two-sided `A∞` homotopy equivalence if and only if it is a quasi-isomorphism. -/
theorem isHomotopyEquiv_iff_isQuasiIso (f : AInfinityHom AA BB) :
    f.IsHomotopyEquiv ↔ f.IsQuasiIso := ⟨IsHomotopyEquiv.isQuasiIso, IsQuasiIso.isHomotopyEquiv⟩
end AInfinityHom

end TauCeti
