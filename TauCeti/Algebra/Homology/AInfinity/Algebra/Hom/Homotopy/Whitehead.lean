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

Over a commutative ring, `TauCeti.AInfinityHom.isHomotopyEquiv_iff_exists_linearHomotopyEquiv`
reduces two-sided `A∞` homotopy invertibility of a morphism `f : A ⟶ B` to graded linear
chain-homotopy invertibility of `f.linearPart`.  Every `A∞` homotopy equivalence is a
quasi-isomorphism (`IsHomotopyEquiv.isQuasiIso`), whereas over a general commutative ring a
quasi-isomorphism need not admit a chain-homotopy inverse (for instance, when the unary complexes
have non-split torsion in cohomology).

Over a field `K`, the unary complexes `(A, m₁)` and `(B, m₁)` contract homogeneously onto their
cohomologies via `AInfinityAlgebra.cohomologyContraction`.  If `f` is a quasi-isomorphism,
conjugating the induced linear equivalence `hf.cohomologyLinearEquiv : H(A) ≃ₗ[K] H(B)` by these
cohomology contractions produces a homogeneous degree-`(-1)` linear chain-homotopy equivalence
`i_B ∘ H(f) ∘ p_A` whose forward map is chain-homotopic to `f.linearPart` via the explicit degree
`-1` map `-(h_B ∘ f₁ ∘ i_A ∘ p_A + f₁ ∘ h_A)`.  Transporting along this chain homotopy gives a
homogeneous linear chain-homotopy equivalence with forward map `f.linearPart`
(`IsQuasiIso.linearHomotopyEquiv`), and lifting via `HomotopyEquiv.ofLinear` yields the Whitehead
theorem for `A∞` algebras over a field (`HomotopyEquiv.ofQuasiIso`,
`isHomotopyEquiv_iff_isQuasiIso`).

## Main definitions

* `TauCeti.AInfinityHom.IsQuasiIso.linearHomotopyEquiv`: over a field, extend `f.linearPart` of an
  `A∞` quasi-isomorphism `f` to a homogeneous degree-`(-1)` linear chain-homotopy equivalence.
* `TauCeti.AInfinityHom.HomotopyEquiv.ofQuasiIso`: over a field, promote an `A∞` quasi-isomorphism
  to a bundled two-sided `A∞` homotopy equivalence with the same forward morphism.

## Main results

* `TauCeti.AInfinityHom.IsQuasiIso.isHomotopyEquiv`: over a field, every `A∞` quasi-isomorphism is
  an `A∞` homotopy equivalence.
* `TauCeti.AInfinityHom.isHomotopyEquiv_iff_isQuasiIso`: over a field, an `A∞` morphism is a
  two-sided `A∞` homotopy equivalence if and only if it is a quasi-isomorphism.

## References

* B. Keller, *Introduction to A-infinity algebras and modules*, Section 3.7.
* K. Lefèvre-Hasegawa, *Sur les A-infini catégories*, thèse de doctorat, Université Paris 7
  (2003), Théorème 1.3.3.1.
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
      hf.cohomologyLinearEquiv.toLinearMap := by
  refine LinearMap.ext fun c ↦ ?_
  rw [LinearMap.comp_apply, LinearMap.comp_apply,
    BB.cohomologyContraction_proj_of_mem_cycles
      (f.linearPart_mem_cycles (AA.cohomologyContraction_incl_mem_cycles c)),
    ← f.cohomologyMap_cohomologyClass (AA.cohomologyContraction_incl_mem_cycles c),
    AA.cohomologyClass_cohomologyContraction_incl,
    LinearEquiv.coe_coe, hf.cohomologyLinearEquiv_apply]

private noncomputable def cohomologyConjLinearHomotopyEquiv {f : AInfinityHom AA BB}
    (hf : f.IsQuasiIso) : LinearHomotopyEquiv AA.differential BB.differential :=
  let eH : LinearHomotopyEquiv (0 : Module.End K AA.Cohomology) (0 : Module.End K BB.Cohomology) :=
    LinearHomotopyEquiv.ofLinearEquiv hf.cohomologyLinearEquiv
      (by rw [LinearMap.zero_comp, LinearMap.comp_zero])
  (AA.cohomologyContraction.toLinearContraction.toLinearHomotopyEquiv.trans eH).trans
    BB.cohomologyContraction.toLinearContraction.toLinearHomotopyEquiv.symm

private noncomputable def cohomologyConjHomotopy (f : AInfinityHom AA BB) : A →ₗ[K] B :=
  -(BB.cohomologyContraction.homotopy ∘ₗ f.linearPart ∘ₗ
      AA.cohomologyContraction.incl ∘ₗ AA.cohomologyContraction.proj +
    f.linearPart ∘ₗ AA.cohomologyContraction.homotopy)

private theorem isHomogeneous_cohomologyConjHomotopy (f : AInfinityHom AA BB) :
    LinearMap.IsHomogeneous (cohomologyConjHomotopy f)
      AA.grading.piece BB.grading.piece (-1) := by
  rw [cohomologyConjHomotopy]
  have hip : LinearMap.IsHomogeneous
      (AA.cohomologyContraction.incl ∘ₗ AA.cohomologyContraction.proj)
      AA.grading.piece AA.grading.piece 0 := by
    simpa only [add_zero] using AA.isHomogeneous_cohomologyContraction_incl.comp
      AA.isHomogeneous_cohomologyContraction_proj
  have hq : LinearMap.IsHomogeneous
      (f.linearPart ∘ₗ AA.cohomologyContraction.incl ∘ₗ AA.cohomologyContraction.proj)
      AA.grading.piece BB.grading.piece 0 := by
    simpa only [add_zero] using f.isHomogeneous_linearPart.comp hip
  have hs₁ : LinearMap.IsHomogeneous
      (BB.cohomologyContraction.homotopy ∘ₗ f.linearPart ∘ₗ
        AA.cohomologyContraction.incl ∘ₗ AA.cohomologyContraction.proj)
      AA.grading.piece BB.grading.piece (-1) := by
    simpa only [zero_add] using BB.isHomogeneous_cohomologyContraction_homotopy.comp hq
  have hs₂ : LinearMap.IsHomogeneous (f.linearPart ∘ₗ AA.cohomologyContraction.homotopy)
      AA.grading.piece BB.grading.piece (-1) := by
    simpa only [add_zero] using
      f.isHomogeneous_linearPart.comp AA.isHomogeneous_cohomologyContraction_homotopy
  exact (hs₁.add hs₂).neg

private theorem cohomologyContraction_conj_sub_linearPart
    {f : AInfinityHom AA BB} (hf : f.IsQuasiIso) :
    (cohomologyConjLinearHomotopyEquiv hf).hom - f.linearPart =
      BB.differential ∘ₗ cohomologyConjHomotopy f +
        cohomologyConjHomotopy f ∘ₗ AA.differential := by
  set cA := AA.cohomologyContraction
  set cB := BB.cohomologyContraction
  refine LinearMap.ext fun a ↦ ?_
  have hmid := congrArg cB.incl (LinearMap.congr_fun
    (cohomologyContraction_proj_comp_linearPart_comp_incl hf) (cA.proj a)).symm
  have hf_diff : ∀ x, BB.differential (f.linearPart x) = f.linearPart (AA.differential x) :=
    LinearMap.congr_fun f.differential_comp_linearPart
  simp only [cohomologyConjLinearHomotopyEquiv, cohomologyConjHomotopy,
    LinearHomotopyEquiv.hom_trans, LinearHomotopyEquiv.hom_symm,
    LinearHomotopyEquiv.hom_ofLinearEquiv, LinearContraction.hom_toLinearHomotopyEquiv,
    LinearContraction.inv_toLinearHomotopyEquiv, LinearMap.sub_apply, LinearMap.add_apply,
    LinearMap.neg_apply, LinearMap.comp_apply] at hmid ⊢
  rw [hmid, cB.incl_proj_apply, hf_diff (cA.incl (cA.proj a)), cA.dM_incl_apply,
    cA.proj_dM_apply]
  simp only [LinearMap.zero_apply, map_zero, map_neg, map_add, zero_add, sub_zero]
  rw [cA.incl_proj_apply a, map_sub, map_sub, ← hf_diff (cA.homotopy a)]
  abel

/-- Over a field, the linear part of an `A∞` quasi-isomorphism extends to a homogeneous
degree-`(-1)` linear chain-homotopy equivalence between the unary complexes, constructed by
conjugating `hf.cohomologyLinearEquiv` by `cohomologyContraction` and adjusting the forward map
along an explicit chain homotopy. -/
noncomputable def IsQuasiIso.linearHomotopyEquiv {f : AInfinityHom AA BB} (hf : f.IsQuasiIso) :
    LinearHomotopyEquiv AA.differential BB.differential :=
  (cohomologyConjLinearHomotopyEquiv hf).ofHomotopy f.differential_comp_linearPart
    (cohomologyConjHomotopy f) (cohomologyContraction_conj_sub_linearPart hf)

@[simp]
theorem IsQuasiIso.hom_linearHomotopyEquiv {f : AInfinityHom AA BB} (hf : f.IsQuasiIso) :
    hf.linearHomotopyEquiv.hom = f.linearPart := by
  rw [linearHomotopyEquiv, LinearHomotopyEquiv.hom_ofHomotopy]

/-- The linear chain-homotopy equivalence associated to a quasi-isomorphism over a field is
homogeneous with homotopy degree `-1`. -/
theorem IsQuasiIso.isHomogeneous_linearHomotopyEquiv {f : AInfinityHom AA BB} (hf : f.IsQuasiIso) :
    hf.linearHomotopyEquiv.IsHomogeneous AA.grading.piece BB.grading.piece (-1) := by
  rw [linearHomotopyEquiv]
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
  have heH := LinearHomotopyEquiv.isHomogeneous_ofLinearEquiv
    (dM := (0 : Module.End K AA.Cohomology)) (dN := (0 : Module.End K BB.Cohomology))
    (by rw [LinearMap.zero_comp, LinearMap.comp_zero]) heH_hom heH_hom.linearEquiv_symm (-1)
  have he₀ : (cohomologyConjLinearHomotopyEquiv hf).IsHomogeneous
      AA.grading.piece BB.grading.piece (-1) := by
    rw [cohomologyConjLinearHomotopyEquiv]
    exact (hcA.trans heH).trans hcB
  exact he₀.ofHomotopy f.differential_comp_linearPart f.isHomogeneous_linearPart
    (isHomogeneous_cohomologyConjHomotopy f) (cohomologyContraction_conj_sub_linearPart hf)

/-- Over a field, promote an `A∞` quasi-isomorphism to a bundled `A∞` homotopy equivalence with the
same forward morphism. -/
noncomputable def HomotopyEquiv.ofQuasiIso {f : AInfinityHom AA BB} (hf : f.IsQuasiIso) :
    HomotopyEquiv AA BB :=
  HomotopyEquiv.ofLinear f hf.linearHomotopyEquiv hf.hom_linearHomotopyEquiv
    hf.isHomogeneous_linearHomotopyEquiv

@[simp]
theorem HomotopyEquiv.hom_ofQuasiIso {f : AInfinityHom AA BB} (hf : f.IsQuasiIso) :
    (HomotopyEquiv.ofQuasiIso hf).hom = f :=
  HomotopyEquiv.hom_ofLinear _ _ _ _

@[simp]
theorem HomotopyEquiv.linearPart_inv_ofQuasiIso {f : AInfinityHom AA BB} (hf : f.IsQuasiIso) :
    (HomotopyEquiv.ofQuasiIso hf).inv.linearPart = hf.linearHomotopyEquiv.inv :=
  HomotopyEquiv.linearPart_inv_ofLinear _ _ _ _

/-- Over a field, every `A∞` quasi-isomorphism is an `A∞` homotopy equivalence. -/
theorem IsQuasiIso.isHomotopyEquiv {f : AInfinityHom AA BB} (hf : f.IsQuasiIso) :
    f.IsHomotopyEquiv :=
  HomotopyEquiv.hom_ofQuasiIso hf ▸ (HomotopyEquiv.ofQuasiIso hf).isHomotopyEquiv_hom

/-- **Whitehead theorem for `A∞` algebras over a field.**  An `A∞` morphism over a field is a
two-sided `A∞` homotopy equivalence if and only if it is a quasi-isomorphism. -/
theorem isHomotopyEquiv_iff_isQuasiIso (f : AInfinityHom AA BB) :
    f.IsHomotopyEquiv ↔ f.IsQuasiIso :=
  ⟨IsHomotopyEquiv.isQuasiIso, IsQuasiIso.isHomotopyEquiv⟩

end AInfinityHom

end TauCeti
