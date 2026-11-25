/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Unipotent.Embedding
public import TauCeti.Algebra.Coalgebra.Comodule.GroupLike
import TauCeti.Algebra.Coalgebra.Comodule.Corestrict
import TauCeti.Algebra.Coalgebra.Comodule.MatrixCoefficient.PointAction
import TauCeti.Algebra.Coalgebra.Comodule.Transport

/-!
# Unipotent affine groups: the comodule definition

An affine group `G` over a field `k`, with coordinate Hopf algebra `H`, is unipotent when every
nonzero representation of `G` has a nonzero fixed vector, that is, every nonzero `H`-comodule `M`
contains some `v ≠ 0` with coaction `v ↦ v ⊗ 1` (Milne, *Algebraic Groups*, 6.45, p. 135). The
object property `TauCeti.unipotentCommHopfAlgProperty` asks this of the finite-dimensional
comodules in the universe of `k`; this is equivalent to the condition on all comodules in all
universes (`unipotentCommHopfAlgProperty.hasNonzeroFixedVector`), since a nonzero vector lies in a
finite-dimensional subcomodule. Unlike the geometric-point criterion
`TauCeti.geometricallyUnipotentPointsCommHopfAlgProperty`, this definition sees the infinitesimal
structure of nonreduced groups. The property is closed under isomorphisms of commutative Hopf
algebras, by corestricting comodules along the inverse isomorphism.

Equivalently, every finite-dimensional representation has a basis in which its coefficient matrix
is upper unitriangular (`unipotentCommHopfAlgProperty_iff_forall_exists_basis`; the forward
direction, for comodules in every universe, is
`unipotentCommHopfAlgProperty.exists_basis_coefficientMatrix_isUpperUnitriangular`). So every
point of `G`, with values in any commutative `k`-algebra, is a unipotent element
(`unipotentCommHopfAlgProperty.isUnipotentPoint`). Over an algebraically closed field, for a reduced
finite-type `H`, the converse holds by Kolchin's theorem, so there the comodule and geometric-point
definitions agree (`unipotentCommHopfAlgProperty_iff_geometricallyUnipotentPoints`).

A group-like element `c ≠ 1` of `H`, that is, a nontrivial character of `G`, rules out
unipotence: the one-dimensional comodule `k_c` has no nonzero fixed vector
(`not_unipotentCommHopfAlgProperty_of_isGroupLikeElem`).

## Main declarations

* `TauCeti.unipotentCommHopfAlgProperty`: unipotence of an affine group, by fixed vectors.
* `TauCeti.unipotentCommHopfAlgProperty.hasNonzeroFixedVector`: every nonzero comodule, in any
  universe and of any dimension, has a nonzero fixed vector.
* `TauCeti.unipotentCommHopfAlgProperty.exists_basis_coefficientMatrix_isUpperUnitriangular`:
  upper-unitriangular bases of finite-dimensional comodules.
* `TauCeti.unipotentCommHopfAlgProperty_iff_forall_exists_basis`: unipotence is equivalent to
  every finite-dimensional representation being upper unitriangular in some basis.
* `TauCeti.unipotentCommHopfAlgProperty.isUnipotentPoint`: every point of a unipotent group is
  unipotent.
* `TauCeti.unipotentCommHopfAlgProperty_iff_geometricallyUnipotentPoints`: over an algebraically
  closed field, for reduced finite-type groups, the two definitions agree.
* `TauCeti.not_unipotentCommHopfAlgProperty_of_isGroupLikeElem`: a nontrivial character excludes
  unipotence.

## References

* J. S. Milne, *Algebraic Groups* (2017), 6.45, p. 135, and Proposition 14.3, p. 280.
-/

public section

open scoped TensorProduct

namespace TauCeti

open Comodule

universe u v w

noncomputable section

/-- **Unipotent affine groups.** A commutative Hopf algebra `H` over a field `k` is unipotent when
every nonzero finite-dimensional `H`-comodule has a nonzero fixed vector `v`, with coaction
`v ↦ v ⊗ 1`. The comodules range over the universe of `k`;
`unipotentCommHopfAlgProperty.hasNonzeroFixedVector` gives every nonzero comodule in every
universe. -/
def unipotentCommHopfAlgProperty (k : Type u) [Field k] :
    CategoryTheory.ObjectProperty (CommHopfAlgCat.{v} k) :=
  fun H ↦ ∀ (M : Type u) [AddCommGroup M] [Module k M] [Comodule k H M] [FiniteDimensional k M]
    [Nontrivial M], HasNonzeroFixedVector k H M

/-- Membership in `unipotentCommHopfAlgProperty`. -/
@[simp]
theorem unipotentCommHopfAlgProperty_iff (k : Type u) [Field k] (H : CommHopfAlgCat.{v} k) :
    unipotentCommHopfAlgProperty k H ↔
      ∀ (M : Type u) [AddCommGroup M] [Module k M] [Comodule k H M] [FiniteDimensional k M]
        [Nontrivial M], HasNonzeroFixedVector k H M :=
  Iff.rfl

/-- Unipotence is invariant under isomorphisms of commutative Hopf algebras: corestrict a comodule
along the inverse isomorphism. -/
instance (k : Type u) [Field k] :
    (unipotentCommHopfAlgProperty k :
      CategoryTheory.ObjectProperty (CommHopfAlgCat.{v} k)).IsClosedUnderIsomorphisms where
  of_iso {H K} e hH M _ _ _ _ _ := by
    let e' : H ≃ₐc[k] K := CommHopfAlgCat.ofIso e
    let _ : Comodule k H M := Corestrict (e'.symm : K →ₗc[k] H)
    obtain ⟨v, hv, hvc⟩ := hasNonzeroFixedVector_iff.mp (hH M)
    refine hasNonzeroFixedVector_iff.mpr ⟨v, hv, ?_⟩
    have hid : (e' : H →ₗc[k] K).comp (e'.symm : K →ₗc[k] H) = CoalgHom.id k K := by ext; simp
    have h := congrArg (TensorProduct.map LinearMap.id (e' : H →ₗc[k] K).toLinearMap) hvc
    rw [← LinearMap.congr_fun (corestrictCoact_id (R := k) (M := M)) v, ← hid,
      corestrictCoact_comp]
    simpa using h

variable {k : Type u} {H : Type v} [Field k] [CommRing H] [HopfAlgebra k H]

namespace unipotentCommHopfAlgProperty

variable (hH : unipotentCommHopfAlgProperty k (CommHopfAlgCat.of k H))
include hH

/-- A nonzero finite-dimensional comodule over a unipotent group, in any universe, has a nonzero
fixed vector: transport it to coordinates `Fin n → k`. -/
private theorem hasNonzeroFixedVector_of_finiteDimensional {M : Type w} [AddCommGroup M]
    [Module k M] [Comodule k H M] [FiniteDimensional k M] [Nontrivial M] :
    HasNonzeroFixedVector k H M := by
  let e : M ≃ₗ[k] (Fin (Module.finrank k M) → k) := (Module.finBasis k M).equivFun
  let _ : Comodule k H (Fin (Module.finrank k M) → k) := Comodule.Transport e
  have : Nontrivial (Fin (Module.finrank k M) → k) := e.injective.nontrivial
  exact hasNonzeroFixedVector_of_injective (transportInvHom e) (transportInvHom_injective e)
    (hH (Fin (Module.finrank k M) → k))

/-- **Every nonzero representation of a unipotent group has a nonzero fixed vector**, in any
universe and of any dimension: a nonzero vector lies in a finite-dimensional subcomodule. -/
theorem hasNonzeroFixedVector {M : Type w} [AddCommGroup M] [Module k M] [Comodule k H M]
    [Nontrivial M] : HasNonzeroFixedVector k H M :=
  hasNonzeroFixedVector_of_forall_subcomodule fun _ _ _ ↦
    hasNonzeroFixedVector_of_finiteDimensional hH

/-- **Every finite-dimensional representation of a unipotent group is unipotent**: it has a basis
in which its coefficient matrix is upper unitriangular. -/
theorem exists_basis_coefficientMatrix_isUpperUnitriangular {M : Type w} [AddCommGroup M]
    [Module k M] [Comodule k H M] [FiniteDimensional k M] :
    ∃ (n : ℕ) (b : Module.Basis (Fin n) k M),
      (coefficientMatrix (C := H) b).IsUpperUnitriangular :=
  exists_basis_coefficientMatrix_isUpperUnitriangular_of_fixed_vectors fun _ _ _ _ _ _ ↦
    hasNonzeroFixedVector_of_finiteDimensional hH

/-- **Every point of a unipotent group is unipotent**, with values in any commutative
`k`-algebra: in an upper-unitriangular basis of a finite-dimensional comodule the point acts by
an upper-unitriangular matrix. -/
theorem isUnipotentPoint {K : Type w} [CommRing K] [Algebra k K] (g : WithConv (H →ₐ[k] K)) :
    HopfAlgebra.IsUnipotentPoint g := by
  rw [HopfAlgebra.isUnipotentPoint_iff_forall_isNilpotent_endOfPoint_sub_one]
  intro M
  obtain ⟨n, b, hb⟩ := exists_basis_coefficientMatrix_isUpperUnitriangular hH (M := M)
  exact isNilpotent_endOfPoint_sub_one_of_isUpperUnitriangular b g.ofConv (hb.map g.ofConv)

/-- A unipotent group has only unipotent geometric points. -/
theorem geometricallyUnipotentPoints :
    geometricallyUnipotentPointsCommHopfAlgProperty k (CommHopfAlgCat.of k H) :=
  (geometricallyUnipotentPointsCommHopfAlgProperty_iff k _).mpr fun g ↦ isUnipotentPoint hH g

end unipotentCommHopfAlgProperty

/-- **Unitriangular representations make a group unipotent**: if every finite-dimensional
comodule in the universe of `k` has a basis in which its coefficient matrix is upper
unitriangular, then `H` is unipotent. The first basis vector of a nonzero comodule is fixed, since
the first column of an upper-unitriangular matrix is `(1, 0, …, 0)`. -/
theorem unipotentCommHopfAlgProperty_of_forall_exists_basis
    (h : ∀ (M : Type u) [AddCommGroup M] [Module k M] [Comodule k H M] [FiniteDimensional k M],
      ∃ (n : ℕ) (b : Module.Basis (Fin n) k M),
        (coefficientMatrix (C := H) b).IsUpperUnitriangular) :
    unipotentCommHopfAlgProperty k (CommHopfAlgCat.of k H) := fun M _ _ _ _ _ ↦ by
  obtain ⟨n, b, hb⟩ := h M
  obtain ⟨i₀⟩ := b.index_nonempty
  let z : Fin n := ⟨0, i₀.pos⟩
  refine (hasNonzeroFixedVector_iff (k := k)).mpr ⟨b z, b.ne_zero z, ?_⟩
  rw [coact_basis_eq_sum_coefficientMatrix, Finset.sum_eq_single z, hb.apply_diag]
  · intro i _ hi
    have hzi : z < i := Fin.lt_def.mpr (Nat.pos_of_ne_zero fun h0 ↦ hi (Fin.ext h0))
    rw [((Matrix.isUpperUnitriangular_iff _).mp hb).1 hzi, TensorProduct.tmul_zero]
  · simp

/-- **Unipotence by unitriangular representations**: `H` is unipotent exactly when every
finite-dimensional comodule in the universe of `k` has a basis in which its coefficient matrix is
upper unitriangular. -/
theorem unipotentCommHopfAlgProperty_iff_forall_exists_basis :
    unipotentCommHopfAlgProperty k (CommHopfAlgCat.of k H) ↔
      ∀ (M : Type u) [AddCommGroup M] [Module k M] [Comodule k H M] [FiniteDimensional k M],
        ∃ (n : ℕ) (b : Module.Basis (Fin n) k M),
          (coefficientMatrix (C := H) b).IsUpperUnitriangular :=
  ⟨fun hH _ _ _ _ _ ↦ hH.exists_basis_coefficientMatrix_isUpperUnitriangular,
    unipotentCommHopfAlgProperty_of_forall_exists_basis⟩

/-- **Kolchin's criterion**: over an algebraically closed field, a reduced finite-type affine group
whose rational points are all unipotent is unipotent. -/
theorem unipotentCommHopfAlgProperty_of_forall_isUnipotentPoint [IsAlgClosed k]
    [Algebra.FiniteType k H] [IsReduced H]
    (hH : ∀ g : WithConv (H →ₐ[k] k), HopfAlgebra.IsUnipotentPoint g) :
    unipotentCommHopfAlgProperty k (CommHopfAlgCat.of k H) :=
  fun _ _ _ _ _ _ ↦ hasNonzeroFixedVector_of_forall_isUnipotentPoint hH

/-- Over an algebraically closed field, for reduced finite-type affine groups, the comodule
definition of unipotence agrees with the geometric-point criterion. -/
theorem unipotentCommHopfAlgProperty_iff_geometricallyUnipotentPoints [IsAlgClosed k]
    [Algebra.FiniteType k H] [IsReduced H] :
    unipotentCommHopfAlgProperty k (CommHopfAlgCat.of k H) ↔
      geometricallyUnipotentPointsCommHopfAlgProperty k (CommHopfAlgCat.of k H) :=
  ⟨unipotentCommHopfAlgProperty.geometricallyUnipotentPoints, fun h ↦
    unipotentCommHopfAlgProperty_of_forall_isUnipotentPoint
      (geometricallyUnipotentPointsCommHopfAlgProperty.forall_isUnipotentPoint h)⟩

/-- **A nontrivial character excludes unipotence.** If `H` has a group-like element `c ≠ 1`, then
the one-dimensional comodule `k` with coaction `1 ↦ 1 ⊗ c` has no nonzero fixed vector, so `H` is
not unipotent. -/
theorem not_unipotentCommHopfAlgProperty_of_isGroupLikeElem {c : H} (hc : IsGroupLikeElem k c)
    (hc1 : c ≠ 1) : ¬ unipotentCommHopfAlgProperty k (CommHopfAlgCat.of k H) := by
  intro hH
  let b : Module.Basis (Fin 1) k k := Module.Basis.singleton (Fin 1) k
  let _ : Comodule k H k := ofGroupLike b (fun _ ↦ c) fun _ ↦ hc
  obtain ⟨v, hv, hvc⟩ := (hasNonzeroFixedVector_iff (k := k) (H := H) (M := k)).mp
    hH.hasNonzeroFixedVector
  have hcoact : coact (R := k) (C := H) (M := k) v = v ⊗ₜ[k] c :=
    coact_eq_tmul_of_mem_span (ofGroupLike_coact_basis b _ _ 0)
      (Submodule.mem_span_singleton.mpr ⟨v, by simp [b]⟩)
  rw [hcoact] at hvc
  have h := congrArg (TensorProduct.lid k H) hvc
  rw [TensorProduct.lid_tmul, TensorProduct.lid_tmul] at h
  exact hc1 (smul_right_injective H hv h)

end

end TauCeti
