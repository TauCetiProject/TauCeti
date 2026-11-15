/-
Copyright (c) 2026 Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import TauCeti.RepresentationTheory.Homological.TateCohomology.HerbrandQuotient
public import Mathlib.RingTheory.TensorProduct.IsBaseChangeFree
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.RingTheory.TensorProduct.IsBaseChangeHom
import Mathlib.RingTheory.TensorProduct.Free
import TauCeti.LinearAlgebra.Matrix.DetDescent
import TauCeti.RepresentationTheory.Lattice

/-!
# The Herbrand quotient of a lattice in a representation

**Tate's lattice lemma.** Let `G` be a finite cyclic group and `V` a representation of `G` over a
nontrivial commutative `ℚ`-algebra `K`, classically `K = ℝ`. If two integral representations `M`
and `N`, free of finite rank over `ℤ`, are both `G`-stable lattices in `V`, that is, if
`G`-equivariant maps `M → V` and `N → V` exhibit `V` as the base change of `M` and of `N` to `K`,
then `M` and `N` have the same Herbrand quotient.

The Herbrand quotient of a lattice therefore depends only on the representation it spans. This is
how the Herbrand quotient of a unit lattice is computed: Dirichlet's logarithmic embedding makes
the `S`-units, together with a copy of `ℤ`, a lattice in the same real representation as the
permutation lattice on the places in `S`, whose Herbrand quotient is computed in
`TauCeti.RepresentationTheory.Homological.TateCohomology.Permutation.Basic`.

The identity of `V`, written in the two bases coming from `M` and from `N`, is a nonsingular
matrix over `K` intertwining the integer matrices of the actions on `M` and on `N`. By
`Matrix.exists_det_ne_zero_forall_mul_eq_mul_of_algebraMap` it may be replaced by a nonsingular
rational matrix with the same property, that is, by an equivalence between the rationalizations
`ℚ ⊗[ℤ] M` and `ℚ ⊗[ℤ] N`. Clearing denominators then gives an injective `G`-equivariant map
`M → N` with finite cokernel (`Representation.Equiv.exists_injective_finite_quotient_range`), which
preserves the Herbrand quotient by
`TauCeti.TateCohomology.herbrandQuotient_eq_of_mono_of_finite_cokernel`.

## Main results

* `TauCeti.TateCohomology.herbrandQuotient_eq_of_isBaseChange`: two `G`-stable lattices in one
  representation over a `ℚ`-algebra have the same Herbrand quotient.

## References

* J. S. Milne, *Class Field Theory*, Chapter VII, the Herbrand quotient of the unit group.
-/

public noncomputable section

open CategoryTheory Limits TensorProduct

namespace TauCeti.TateCohomology

variable {G : Type} [Group G] [Fintype G]

/-- **Tate's lattice lemma.** Let `G` be a finite cyclic group, `K` a nontrivial commutative
`ℚ`-algebra (classically `ℝ`) and `ρ` a representation of `G` on a `K`-module `V`. If `M` and `N`
are integral representations of `G`, free over `ℤ` with `M` of finite rank, and `G`-equivariant
maps `i : M → V` and `j : N → V` exhibit `V` as the base change of `M` and of `N` to `K`, then `M`
and `N` have the same Herbrand quotient. The rank of `N` is then finite as well, being that of
`V`. -/
theorem herbrandQuotient_eq_of_isBaseChange [IsCyclic G] {K V : Type*} [CommRing K] [Nontrivial K]
    [Algebra ℚ K] [AddCommGroup V] [Module K V] (ρ : Representation K G V) {M N : Rep ℤ G}
    [Module.Free ℤ M] [Module.Finite ℤ M] [Module.Free ℤ N] {i : M →ₗ[ℤ] V} {j : N →ₗ[ℤ] V}
    (hi : IsBaseChange K i) (hj : IsBaseChange K j) (hiG : ∀ g x, i (M.ρ g x) = ρ g (i x))
    (hjG : ∀ g y, j (N.ρ g y) = ρ g (j y)) :
    herbrandQuotient M = herbrandQuotient N := by
  classical
  let bM := Module.Free.chooseBasis ℤ M
  let bN₀ := Module.Free.chooseBasis ℤ N
  -- a basis of `N` indexed like that of `M`, the two base changes being bases of `V`
  let bN := bN₀.reindex ((hj.basis bN₀).indexEquiv (hi.basis bM))
  let A g := LinearMap.toMatrix bM bM (M.ρ g)
  let B g := LinearMap.toMatrix bN bN (N.ρ g)
  -- the identity of `V`, from the basis coming from `M` to the one coming from `N`
  set X := (hj.basis bN).toMatrix (hi.basis bM) with hX_def
  have hX : X.det ≠ 0 :=
    Matrix.det_ne_zero_of_right_inverse (Module.Basis.toMatrix_mul_toMatrix_flip _ _)
  -- `ρ g` is the base change of the action of `g` on `M`, and on `N`
  have hρM (g : G) : ρ g = hi.endHom (M.ρ g) :=
    hi.algHom_ext _ _ fun x ↦ by rw [IsBaseChange.endHom_comp_apply, hiG]
  have hρN (g : G) : ρ g = hj.endHom (N.ρ g) :=
    hj.algHom_ext _ _ fun y ↦ by rw [IsBaseChange.endHom_comp_apply, hjG]
  have hXG (g : G) : (B g).map (algebraMap ℤ K) * X = X * (A g).map (algebraMap ℤ K) := by
    rw [← IsBaseChange.endHom_toMatrix (ibcM := hj) (b := bN) (f := N.ρ g),
      ← IsBaseChange.endHom_toMatrix (ibcM := hi) (b := bM) (f := M.ρ g), ← hρM, ← hρN, hX_def,
      linearMap_toMatrix_mul_basis_toMatrix, basis_toMatrix_mul_linearMap_toMatrix]
  -- descend `X` to a nonsingular rational intertwiner `Y`
  obtain ⟨Y, hY, hYG⟩ := Matrix.exists_det_ne_zero_forall_mul_eq_mul_of_algebraMap (F := ℚ)
    (fun g ↦ (A g).map (algebraMap ℤ ℚ)) (fun g ↦ (B g).map (algebraMap ℤ ℚ)) hX
    fun g ↦ by
      simpa only [Matrix.map_map, Function.comp_def, algebraMap_int_eq, Int.coe_castRingHom,
        map_intCast] using hXG g
  -- read `Y` as an equivalence of the rationalizations of `M` and `N`
  let cM := Algebra.TensorProduct.basis ℚ bM
  let cN := Algebra.TensorProduct.basis ℚ bN
  have hYu : IsUnit Y.det := isUnit_iff_ne_zero.2 hY
  let e : ℚ ⊗[ℤ] M ≃ₗ[ℚ] ℚ ⊗[ℤ] N := LinearEquiv.ofLinearMap (Matrix.toLin cM cN Y)
    (Matrix.toLin cN cM Y⁻¹) (by rw [← Matrix.toLin_mul, Y.mul_nonsing_inv hYu, Matrix.toLin_one])
    (by rw [← Matrix.toLin_mul, Y.nonsing_inv_mul hYu, Matrix.toLin_one])
  have he (g : G) : e.toLinearMap ∘ₗ Representation.baseChange ℚ M.ρ g =
      Representation.baseChange ℚ N.ρ g ∘ₗ e.toLinearMap :=
    (LinearMap.toMatrix cM cN).injective <| by
      rw [LinearMap.toMatrix_comp cM cM cN, LinearMap.toMatrix_comp cM cN cN,
        Representation.baseChange_apply, Representation.baseChange_apply,
        LinearMap.toMatrix_baseChange, LinearMap.toMatrix_baseChange,
        LinearEquiv.toLinearMap_ofLinearMap, LinearMap.toMatrix_toLin, hYG]
  have : Module.Finite ℤ N := Module.Finite.of_basis bN
  obtain ⟨φ, hφ, hφfin⟩ := (Representation.Equiv.mk e he).exists_injective_finite_quotient_range
  let f : M ⟶ N := ConcreteCategory.ofHom φ
  have : Mono f := (Rep.mono_iff_injective f).2 hφ
  -- the cokernel is computed in `ModuleCat ℤ`, as the quotient by the range of `φ`
  have : Finite (((forget₂ (Rep ℤ G) (ModuleCat ℤ)).obj N) ⧸
      LinearMap.range ((forget₂ (Rep ℤ G) (ModuleCat ℤ)).map f).hom) := hφfin
  have : Finite ↑(cokernel f) :=
    Finite.of_equiv _ (PreservesCokernel.iso (forget₂ _ (ModuleCat ℤ)) f ≪≫
      ModuleCat.cokernelIsoRangeQuotient _).toLinearEquiv.toEquiv.symm
  exact herbrandQuotient_eq_of_mono_of_finite_cokernel f

end TauCeti.TateCohomology
