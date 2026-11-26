/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.MonoidAlgebra.CosetBasis
public import TauCeti.AlgebraicTopology.DGLocalSystem.Aspherical
public import TauCeti.AlgebraicTopology.UniversalCover.Circle.FundamentalGroup
public import TauCeti.AlgebraicTopology.UniversalCover.Circle.HigherHomotopy

/-!
# Pulling the regular local system of the circle back along `z ↦ z²`

The chain algebra `C_*(Ω S¹; R)` of the Moore loops of the circle at `1` is a DG local system on
`S¹`, the regular one, a right module over itself. Its pullback along the squaring map
`f : S¹ → S¹`, `z ↦ z²`, which fixes `1`, is the same complex with the loop chains acting through
`C_*(Ωf)` (`TauCeti.DGLocalSystem.pullback`). So its homology is `H(Ω S¹; R)`, a module over
`H(Ω S¹; R)` through the algebra map `H(Ωf)` that `C_*(Ωf)` induces on cohomology. This file
shows that this module is free of rank two, with basis `1` and the class `[γ]` of the
counterclockwise loop `γ`
(`TauCeti.Circle.bijective_cohomologyMap_loopChainMap_sq_add_mul`): every class is uniquely
`H(Ωf)(a) + H(Ωf)(b) [γ]`.

The circle is aspherical, so its loop space is homotopy discrete and `H(Ω S¹; R)` is the group
ring `R[π₁(S¹)] = R[t, t⁻¹]` in degree zero
(`TauCeti.groupAlgebraLoopChainCohomologyAlgEquiv`). Under this identification `H(Ωf)` is the map
of group rings induced by `f` on fundamental groups
(`TauCeti.cohomologyMap_loopChainMap_groupAlgebraToLoopChainCohomology`), which is `t ↦ t²`
(`Circle.mapOfEq_pow`). Its image `R[t², t⁻²]` is the span of the squares, the classes of even
degree (`Circle.mem_range_mapOfEq_pow_iff`), and the classes of odd degree form the other coset,
so `R[t, t⁻¹] = R[t², t⁻²] ⊕ R[t², t⁻²] t`
(`TauCeti.MonoidAlgebra.bijective_mapDomain_add_mapDomain_mul_single`). The same holds with `[γ]`
replaced by the class of any loop of odd degree.

This is not the regular module of `R[t, t⁻¹]`, which is free of rank one: the pullback along a map
of degree two doubles the rank. On homology the pullback is restriction of scalars along `H(Ωf)`,
here along the inclusion of `R[t², t⁻²]`, which is defined because `f` fixes the chosen basepoint
`1`.

## Main results

* `TauCeti.Circle.bijective_mapDomain_mapOfEq_sq_add_mul_single`: `R[π₁(S¹)]` is free over
  itself through `t ↦ t²`, with basis `1` and any class `g` of odd degree.
* `TauCeti.Circle.bijective_cohomologyMap_loopChainMap_sq_add_mul`: the homology of the pullback of
  the regular local system of the circle along `z ↦ z²` is free of rank two over `H(Ω S¹; R)`,
  with basis `1, [γ]`.

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, §§1.4 and 2.3.
-/

public section

noncomputable section

open MonoidAlgebra

namespace TauCeti

namespace Circle

/-- **The group ring of `π₁(S¹)` over itself through `t ↦ t²`.** Let `σ` be the endomorphism of
`π₁(S¹, 1)` induced by `z ↦ z²`, which squares loop classes, and let `g` be a loop class of odd
degree. Then every element of `R[π₁(S¹, 1)]` is uniquely `σ(a) + σ(b) g`: through `σ`, the group
ring is a free module of rank two over itself, with basis `1, g`. -/
theorem bijective_mapDomain_mapOfEq_sq_add_mul_single {R : Type*} [Semiring R]
    {g : FundamentalGroup Circle 1}
    (hg : Odd (Circle.fundamentalGroupMulEquiv 1 g).toAdd) :
    Function.Bijective fun ab :
        R[FundamentalGroup Circle 1] × R[FundamentalGroup Circle 1] ↦
      mapDomain (FundamentalGroup.mapOfEq ⟨(· ^ 2), continuous_pow 2⟩ (one_pow 2)) ab.1 +
        mapDomain (FundamentalGroup.mapOfEq ⟨(· ^ 2), continuous_pow 2⟩ (one_pow 2)) ab.2 *
          single g 1 := by
  set e := Circle.fundamentalGroupMulEquiv 1
  -- The squares are the classes of even degree.
  have hmem (x : FundamentalGroup Circle 1) :
      x ∈ (FundamentalGroup.mapOfEq ⟨(· ^ 2), continuous_pow 2⟩ (one_pow 2)).range ↔
        Even (e x).toAdd := by
    rw [Circle.mem_range_mapOfEq_pow_iff, Nat.cast_ofNat, even_iff_two_dvd]
  refine TauCeti.MonoidAlgebra.bijective_mapDomain_add_mapDomain_mul_single _
    (fun x y hxy ↦ ?_) (by rw [hmem]; exact Int.not_even_iff_odd.2 hg) fun x ↦ ?_
  · -- Squaring is injective on `π₁(S¹) ≅ ℤ`.
    rw [Circle.mapOfEq_pow, Circle.mapOfEq_pow] at hxy
    apply e.injective
    have h := congrArg (fun z ↦ (e z).toAdd) hxy
    simp only [map_pow, toAdd_pow, nsmul_eq_mul, Nat.cast_ofNat] at h
    exact Multiplicative.toAdd.injective (by simpa using h)
  · rw [hmem, hmem, map_mul, map_inv, toAdd_mul, toAdd_inv, ← sub_eq_add_neg]
    rcases Int.even_or_odd (e x).toAdd with hx | hx
    · exact Or.inl hx
    · exact Or.inr (hx.sub_odd hg)

/-- **The pullback of the regular local system of the circle along `z ↦ z²`.** Let `f` be the
squaring map of the circle, which fixes `1`, and `H(Ωf)` the map that `C_*(Ωf)` induces on the
cohomology `H(Ω S¹; R)` of the chain algebra of the Moore loops at `1`. Then every class of
`H(Ω S¹; R)` is uniquely `H(Ωf)(a) + H(Ωf)(b) [γ]`, where `[γ]` is the class of the point chain of
the counterclockwise loop `γ`. So the homology of the pullback of the regular DG local system along
`f`, which is `H(Ω S¹; R)` as a module through `H(Ωf)`, is free of rank two with basis `1, [γ]`. -/
theorem bijective_cohomologyMap_loopChainMap_sq_add_mul {R : Type} [CommRing R] :
    Function.Bijective fun ab : (loopChain_isDGAlgebra Circle 1 R).Cohomology ×
        (loopChain_isDGAlgebra Circle 1 R).Cohomology ↦
      (loopChainMap R ⟨(· ^ 2), continuous_pow 2⟩ (one_pow 2)).cohomologyMap ab.1 +
        (loopChainMap R ⟨(· ^ 2), continuous_pow 2⟩ (one_pow 2)).cohomologyMap ab.2 *
          Ideal.Quotient.mk _
            ⟨cubicalChainPoint (MooreLoopSpace Circle 1) R Circle.expLoop.toMooreLoop,
              (loopChain_isDGAlgebra Circle 1 R).mem_cycles.mpr
                (cubicalChainDifferential_cubicalChainPoint _)⟩ := by
  set E := groupAlgebraLoopChainCohomologyAlgEquiv R (B := Circle) (b := 1)
    (fun _ ↦ inferInstance)
  -- The class of the counterclockwise loop has degree `-1`, which is odd.
  have hg : Odd (Circle.fundamentalGroupMulEquiv 1
      (MooreLoopSpace.fundamentalGroupHom 1 Circle.expLoop.toMooreLoop)).toAdd := by
    rw [MooreLoopSpace.fundamentalGroupHom_toMooreLoop, map_inv,
      Circle.fundamentalGroupMulEquiv_expLoop]
    simp
  -- Through the identification of `H(Ω S¹; R)` with the group ring, the map is the one of
  -- `bijective_mapDomain_mapOfEq_sq_add_mul_single`.
  convert E.bijective.comp ((bijective_mapDomain_mapOfEq_sq_add_mul_single (R := R) hg).comp
    (E.symm.bijective.prodMap E.symm.bijective)) using 1
  funext ⟨a, b⟩
  obtain ⟨a, rfl⟩ := E.surjective a
  obtain ⟨b, rfl⟩ := E.surjective b
  simp only [Function.comp_apply, Prod.map_apply, AlgEquiv.symm_apply_apply, map_add, map_mul]
  simp only [E, groupAlgebraLoopChainCohomologyAlgEquiv_apply,
    cohomologyMap_loopChainMap_groupAlgebraToLoopChainCohomology, mapDomainAlgHom_apply]
  -- The basis element `single [γ] 1` is the class of the point chain of `γ`.
  rw [← of_apply, groupAlgebraToLoopChainCohomology_of_fundamentalGroupHom]

end Circle

end TauCeti
