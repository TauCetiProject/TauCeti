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
import TauCeti.LinearAlgebra.Matrix.DetDescent

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
`TauCeti.RepresentationTheory.Homological.TateCohomology.Permutation`.

The identity of `V`, written in the two bases coming from `M` and from `N`, is a nonsingular
matrix over `K` intertwining the integer matrices of the actions on `M` and on `N`. By
`Matrix.exists_det_ne_zero_forall_mul_eq_mul_of_intCast` it may be replaced by a nonsingular
integer matrix with the same property, that is, by a `G`-equivariant map `M → N`. Such a map is
injective with finite cokernel (`Matrix.injective_toLin_of_det_ne_zero`,
`Matrix.finite_quotient_range_toLin_of_det_ne_zero`), so it preserves the Herbrand quotient by
`TauCeti.TateCohomology.herbrandQuotient_eq_of_mono_of_finite_cokernel`.

## Main results

* `TauCeti.TateCohomology.herbrandQuotient_eq_of_isBaseChange`: two `G`-stable lattices in one
  representation over a `ℚ`-algebra have the same Herbrand quotient.

## References

* J. S. Milne, *Class Field Theory*, Chapter VII, the Herbrand quotient of the unit group.
-/

public noncomputable section

open CategoryTheory Limits

namespace TauCeti.TateCohomology

variable {G : Type} [Group G] [Fintype G]

/-- An integer matrix with nonzero determinant intertwining the actions on two integral
representations, in two bases indexed by the same type, gives them the same Herbrand quotient: it
is an injective intertwining map with finite cokernel. -/
private theorem herbrandQuotient_eq_of_det_ne_zero [IsCyclic G] {M N : Rep ℤ G} {ι : Type}
    [Fintype ι] [DecidableEq ι] (bM : Module.Basis ι ℤ M) (bN : Module.Basis ι ℤ N)
    (Z : Matrix ι ι ℤ) (hZ : Z.det ≠ 0)
    (hZG : ∀ g, LinearMap.toMatrix bN bN (N.ρ g) * Z = Z * LinearMap.toMatrix bM bM (M.ρ g)) :
    herbrandQuotient M = herbrandQuotient N := by
  let φ := Matrix.toLin bM bN Z
  have hφG (g : G) (x : M) : φ (M.ρ g x) = N.ρ g (φ x) := by
    have : φ ∘ₗ M.ρ g = N.ρ g ∘ₗ φ := (LinearMap.toMatrix bM bN).injective <| by
      rw [LinearMap.toMatrix_comp bM bM bN, LinearMap.toMatrix_comp bM bN bN,
        LinearMap.toMatrix_toLin, hZG]
    exact LinearMap.congr_fun this x
  let f : M ⟶ N :=
    ConcreteCategory.ofHom (LinearMap.intertwiningMap_of_isIntertwiningMap M.ρ N.ρ φ hφG)
  have : Mono f := (Rep.mono_iff_injective f).2 (Matrix.injective_toLin_of_det_ne_zero bM bN hZ)
  -- the cokernel is computed in `ModuleCat ℤ`, as the quotient by the range of `φ`
  have : Finite (((forget₂ (Rep ℤ G) (ModuleCat ℤ)).obj N) ⧸
      LinearMap.range ((forget₂ (Rep ℤ G) (ModuleCat ℤ)).map f).hom) :=
    Matrix.finite_quotient_range_toLin_of_det_ne_zero bM bN hZ
  have : Finite ↑(cokernel f) :=
    Finite.of_equiv _ (PreservesCokernel.iso (forget₂ _ (ModuleCat ℤ)) f ≪≫
      ModuleCat.cokernelIsoRangeQuotient _).toLinearEquiv.toEquiv.symm
  exact herbrandQuotient_eq_of_mono_of_finite_cokernel f

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
  obtain ⟨Z, hZ, hZG⟩ := Matrix.exists_det_ne_zero_forall_mul_eq_mul_of_intCast A B hX
    fun g ↦ by simpa only [algebraMap_int_eq, Int.coe_castRingHom] using hXG g
  exact herbrandQuotient_eq_of_det_ne_zero bM bN Z hZ hZG

end TauCeti.TateCohomology
