/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Homotopy.LoopSpace.TorusClass
public import TauCeti.Geometry.Symplectic.Floer.SphericalPeriodGroup

/-!
# The period homomorphism of the cap cover

Let `X` be a space with homomorphisms `ω : H₂(X; ℤ) → ℝ` and `c : H₂(X; ℤ) → ℤ`, for a symplectic
manifold the symplectic area and the first Chern number, and let
`Γ = TauCeti.Floer.SphericalPeriodGroup ω c` be the quotient of the spherical classes by the joint
kernel of `ω` and `c`. Capped Hamiltonian Floer theory works on the covering space of the
contractible free loops `𝓛₀X` whose fibre over a loop is its set of caps modulo spheres of zero area
and zero first Chern number. Transporting a cap around a loop `Λ` of free loops glues to it the
torus swept out by `Λ`, so the cover is governed by the areas and first Chern numbers of these
tori.

This file shows that the period/Chern transgression of loops of contractible free loops factors
through `Γ`. A loop `Λ` of contractible free loops at the constant loop at `x` sweeps out a torus
whose class (`TauCeti.freeLoopTorusClassHom`) is spherical. Its class in `Γ` defines a homomorphism

`π₁(𝓛₀X, x) → Γ`

(`TauCeti.Floer.SphericalPeriodGroup.ofContractibleLoopsHomotopyGroup`), whose area and first
Chern number are those of the torus. Its kernel consists of the loops sweeping out tori of zero area
and zero first Chern number
(`TauCeti.Floer.SphericalPeriodGroup.ofContractibleLoopsHomotopyGroup_eq_zero_iff`), and the cap
cover is the connected covering space of `𝓛₀X` associated with this subgroup. The homomorphism is
onto when `X` is path connected
(`TauCeti.Floer.SphericalPeriodGroup.ofContractibleLoopsHomotopyGroup_surjective`), so the
quotient of `π₁(𝓛₀X, x)` by the kernel is `Γ`, the group acting simply transitively on the cap
classes of a contractible loop (`TauCeti.Floer.SphericalCapClass`). The covering space itself and
the identification of its fibres with cap classes are not constructed here.

## Main definitions

* `TauCeti.Floer.SphericalPeriodGroup.ofContractibleLoopsHomotopyGroup`: the period homomorphism
  `π₁(𝓛₀X, x) → Γ`.

## Main results

* `TauCeti.Floer.SphericalPeriodGroup.area_ofContractibleLoopsHomotopyGroup`,
  `TauCeti.Floer.SphericalPeriodGroup.chern_ofContractibleLoopsHomotopyGroup`: its area and first
  Chern number are those of the torus swept out by the loop.
* `TauCeti.Floer.SphericalPeriodGroup.ofContractibleLoopsHomotopyGroup_eq_zero_iff`: its kernel
  consists of the loops sweeping out tori of zero area and zero first Chern number.
* `TauCeti.Floer.SphericalPeriodGroup.ofContractibleLoopsHomotopyGroup_surjective`: it is onto for a
  path-connected `X`.

## References

* H. Hofer and D. A. Salamon, *Floer homology and Novikov rings*, in *The Floer memorial
  volume*, Progr. Math. 133 (1995), 483–524, on the covering space of capped loops.
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, §3.
-/

public section

noncomputable section

open CategoryTheory AlgebraicTopology HomotopyGroup

namespace TauCeti.Floer.SphericalPeriodGroup

variable {X : Type} [TopologicalSpace X]
  {ω : ((singularHomologyFunctor (ModuleCat.{0} ℤ) 2).obj (ModuleCat.of ℤ ℤ)).obj
    (TopCat.of X) →+ ℝ}
  {c : ((singularHomologyFunctor (ModuleCat.{0} ℤ) 2).obj (ModuleCat.of ℤ ℤ)).obj
    (TopCat.of X) →+ ℤ}

/-- The torus class of a loop of contractible free loops at the constant loop at `x`: the class in
`H₂(X; ℤ)` of the torus it sweeps out, through the inclusion of the contractible free loops. -/
private def contractibleTorusClassHom (x : X) :
    Additive (HomotopyGroup (Fin 1) (contractibleLoops X) (constContractibleLoop x)) →+
      ((singularHomologyFunctor (ModuleCat.{0} ℤ) 2).obj (ModuleCat.of ℤ ℤ)).obj (TopCat.of X) :=
  (freeLoopTorusClassHom X (ContinuousMap.const Circle x)).comp
    (contractibleLoopsHomotopyGroupMulEquiv x).toMonoidHom.toAdditive

variable (ω c) in
/-- **The period homomorphism of the cap cover** `π₁(𝓛₀X, x) → Γ`: a loop of contractible free loops
at the constant loop at `x` goes to the class in the period group of the torus it sweeps out, which
is spherical (`TauCeti.freeLoopTorusClassHom_const_mem_sphericalClasses`). -/
def ofContractibleLoopsHomotopyGroup (x : X) :
    Additive (HomotopyGroup (Fin 1) (contractibleLoops X) (constContractibleLoop x)) →+
      SphericalPeriodGroup ω c :=
  (QuotientAddGroup.mk' _).comp ((contractibleTorusClassHom x).codRestrict _
    fun _ ↦ freeLoopTorusClassHom_const_mem_sphericalClasses x _)

/-- The area of the period class of a loop of contractible free loops is the area of the torus it
sweeps out. -/
@[simp]
theorem area_ofContractibleLoopsHomotopyGroup (x : X)
    (a : Additive (HomotopyGroup (Fin 1) (contractibleLoops X) (constContractibleLoop x))) :
    PeriodGroup.area _ _ (ofContractibleLoopsHomotopyGroup ω c x a) =
      ω (freeLoopTorusClassHom X (ContinuousMap.const Circle x)
        (Additive.ofMul (contractibleLoopsHomotopyGroupMulEquiv x a.toMul))) := by
  simp [ofContractibleLoopsHomotopyGroup, contractibleTorusClassHom]

/-- The first Chern number of the period class of a loop of contractible free loops is the first
Chern number of the torus it sweeps out. -/
@[simp]
theorem chern_ofContractibleLoopsHomotopyGroup (x : X)
    (a : Additive (HomotopyGroup (Fin 1) (contractibleLoops X) (constContractibleLoop x))) :
    PeriodGroup.chern _ _ (ofContractibleLoopsHomotopyGroup ω c x a) =
      c (freeLoopTorusClassHom X (ContinuousMap.const Circle x)
        (Additive.ofMul (contractibleLoopsHomotopyGroupMulEquiv x a.toMul))) := by
  simp [ofContractibleLoopsHomotopyGroup, contractibleTorusClassHom]

/-- **The kernel of the period homomorphism**, the subgroup of the cap cover: a loop of
contractible free loops has trivial period class exactly when the torus it sweeps out has zero area
and zero first Chern number. -/
theorem ofContractibleLoopsHomotopyGroup_eq_zero_iff (x : X)
    (a : Additive (HomotopyGroup (Fin 1) (contractibleLoops X) (constContractibleLoop x))) :
    ofContractibleLoopsHomotopyGroup ω c x a = 0 ↔
      ω (freeLoopTorusClassHom X (ContinuousMap.const Circle x)
          (Additive.ofMul (contractibleLoopsHomotopyGroupMulEquiv x a.toMul))) = 0 ∧
        c (freeLoopTorusClassHom X (ContinuousMap.const Circle x)
          (Additive.ofMul (contractibleLoopsHomotopyGroupMulEquiv x a.toMul))) = 0 := by
  rw [PeriodGroup.ext_iff]
  simp

/-- **The period homomorphism is onto** for a path-connected space: every class of the period group
is the class of the torus swept out by a loop of contractible free loops at the constant loop at
`x`. -/
theorem ofContractibleLoopsHomotopyGroup_surjective [PathConnectedSpace X] (x : X) :
    Function.Surjective (ofContractibleLoopsHomotopyGroup ω c x) := by
  intro γ
  obtain ⟨b, rfl⟩ := ofHomotopyGroup_surjective (ω := ω) (c := c) x γ
  obtain ⟨g, hg⟩ : hurewiczIntHom X x 1 b ∈
      (freeLoopTorusClassHom X (ContinuousMap.const Circle x)).range :=
    (range_freeLoopTorusClassHom_const x).symm ▸ ⟨b, rfl⟩
  refine ⟨Additive.ofMul ((contractibleLoopsHomotopyGroupMulEquiv x).symm g.toMul),
    PeriodGroup.ext ?_ ?_⟩ <;>
    simp only [area_ofContractibleLoopsHomotopyGroup, chern_ofContractibleLoopsHomotopyGroup,
      area_ofHomotopyGroup, chern_ofHomotopyGroup, toMul_ofMul, MulEquiv.apply_symm_apply,
      ofMul_toMul, hg]

end TauCeti.Floer.SphericalPeriodGroup
