/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Solvable
public import Mathlib.LinearAlgebra.Basis.Flag
public import TauCeti.Algebra.AlgebraicGroup.Representation.Stabilizer
public import TauCeti.Algebra.Coalgebra.Comodule.ExteriorAlgebra.Power
public import TauCeti.Algebra.Coalgebra.Comodule.TensorProduct
public import TauCeti.Algebra.Coalgebra.Comodule.Transport
public import TauCeti.LinearAlgebra.ExteriorPower.FlagCone
import Mathlib.RingTheory.HopfAlgebra.Quotient
import TauCeti.Algebra.AlgebraicGroup.Representation.ExteriorStabilizer.Basic
import TauCeti.Algebra.AlgebraicGroup.Representation.PointsAction.ExteriorPower
import TauCeti.Algebra.AlgebraicGroup.Representation.PointsAction.Transport
import TauCeti.Algebra.AlgebraicGroup.Representation.TensorProduct
import TauCeti.Algebra.Coalgebra.Comodule.Flag.Basic
import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.UpperTriangular.Solvable

/-!
# Flag comodules and scheme-theoretic stabilizers of exterior flag lines

For a comodule `M` over a commutative bialgebra `H`, each exterior power `⋀ᵈ M` is an `H`-comodule
(`TauCeti.Comodule.exteriorPower`), and transporting tensor products along `flagSpaceZeroEquiv` and
`flagSpaceSuccEquiv` equips `exteriorPower.FlagSpace R M d` with an `H`-comodule structure
(`TauCeti.Comodule.exteriorFlag`) whose rational point action is `exteriorFlagMap d`.

Over a field `k` and a commutative Hopf algebra `H`:
* the line stabilizer of `exteriorFlagVector k d b` for a basis `b : Module.Basis (Fin d) k M` is
  `Finset.univ.sup fun r ↦ (b.flag r).stabilizerHopfIdeal H`, and lies below `J : HopfIdeal k H`
  precisely when the corestricted coefficient matrix of `b` over `H ⧸ J` is upper triangular;
* if `M` contains any subspace `W₀` whose stabilizer `J` has solvable `k`-points, then for *every*
  basis `b` of `M`, the `k`-points of the quotient by
  `(k ∙ exteriorFlagVector k d b).stabilizerHopfIdeal H` form a solvable group
  (`isSolvable_points_quotient_stabilizerHopfIdeal_exteriorFlagVector`), since acting on `M` maps
  it into `upperTriangularGroup (Fin d) k` with kernel fixing `W₀`.

## Main definitions

* `TauCeti.Comodule.exteriorFlag`: the `H`-comodule structure on `exteriorPower.FlagSpace R M d`.

## Main results

* `TauCeti.Comodule.exteriorFlag_zero` and `TauCeti.Comodule.exteriorFlag_succ`: recursive
  unfolding equations for `TauCeti.Comodule.exteriorFlag`.
* `TauCeti.Comodule.basePointsRepresentation_exteriorFlag`: base-valued points act on `FlagSpace`
  by `exteriorPower.exteriorFlagMap`.
* `TauCeti.Comodule.stabilizerHopfIdeal_span_exteriorFlagVector_of_linearIndependent`: the line
  stabilizer of `exteriorFlagVector k d v` for a linearly independent tuple `v` is the supremum of
  the stabilizers of its prefix spans.
* `TauCeti.Comodule.stabilizerHopfIdeal_span_exteriorFlagVector`: the line stabilizer of
  `exteriorFlagVector k d b` is `Finset.univ.sup fun r ↦ (b.flag r).stabilizerHopfIdeal H`.
* `TauCeti.Comodule.stabilizerHopfIdeal_span_exteriorFlagVector_le_iff`: the line stabilizer lies
  below `J` iff `coefficientMatrix (C := H ⧸ J.toIdeal) b` is upper triangular.
* `TauCeti.Comodule.stabilizerHopfIdeal_span_exteriorFlagVector_eq`: when `b` is upper triangular
  over `H ⧸ J.toIdeal` and `(k ∙ b 0).stabilizerHopfIdeal H = J`, the flag line stabilizer equals
  `J`.
* `TauCeti.Comodule.isSolvable_points_quotient_stabilizerHopfIdeal_exteriorFlagVector`: solvability
  of `k`-points for the stabilizer of any basis flag vector in `M`.

## References

* J. S. Milne, *Algebraic Groups*, Cambridge University Press (2017), Theorem 17.9(a), p. 354.
* J. E. Humphreys, *Linear Algebraic Groups*, GTM 21, Springer (1975), §21.3.
-/

public section

open scoped TensorProduct
open WithConv

namespace TauCeti.Comodule

section Bialgebra

variable (R H M : Type*) [CommRing R] [CommSemiring H] [Bialgebra R H]
  [AddCommGroup M] [Module R M] [Comodule R H M]

/-- The right `H`-comodule structure on `exteriorPower.FlagSpace R M d`, built recursively from
`Comodule.exteriorPower` and `Comodule.tensor` via `Comodule.Transport`. Select it explicitly as a
local instance. -/
@[implicit_reducible]
noncomputable def exteriorFlag : (d : ℕ) → Comodule R H (exteriorPower.FlagSpace R M d)
  | 0 =>
      let _ : Comodule R H (⋀[R]^0 M) := exteriorPower R H M 0
      Transport (exteriorPower.flagSpaceZeroEquiv R M).symm
  | r + 1 =>
      let _ : Comodule R H (exteriorPower.FlagSpace R M r) := exteriorFlag r
      let _ : Comodule R H (⋀[R]^(r + 1) M) := exteriorPower R H M (r + 1)
      let _ : Comodule R H (exteriorPower.FlagSpace R M r ⊗[R] ⋀[R]^(r + 1) M) :=
        tensor R H (exteriorPower.FlagSpace R M r) (⋀[R]^(r + 1) M)
      Transport (exteriorPower.flagSpaceSuccEquiv R M r).symm

/-- Base-case unfolding of `exteriorFlag` in degree `0`. -/
theorem exteriorFlag_zero :
    exteriorFlag R H M 0 =
      (letI : Comodule R H (⋀[R]^0 M) := exteriorPower R H M 0
       Transport (exteriorPower.flagSpaceZeroEquiv R M).symm) :=
  (rfl)

/-- Recursive unfolding of `exteriorFlag` in degree `r + 1`. -/
theorem exteriorFlag_succ (r : ℕ) :
    exteriorFlag R H M (r + 1) =
      (letI : Comodule R H (exteriorPower.FlagSpace R M r) := exteriorFlag R H M r
       letI : Comodule R H (⋀[R]^(r + 1) M) := exteriorPower R H M (r + 1)
       letI : Comodule R H (exteriorPower.FlagSpace R M r ⊗[R] ⋀[R]^(r + 1) M) :=
         tensor R H (exteriorPower.FlagSpace R M r) (⋀[R]^(r + 1) M)
       Transport (exteriorPower.flagSpaceSuccEquiv R M r).symm) :=
  (rfl)

end Bialgebra

section Points

variable {R H M : Type*} [CommRing R] [CommSemiring H] [HopfAlgebra R H]
  [AddCommGroup M] [Module R M] [Comodule R H M]

/-- Base-valued points act on `exteriorPower.FlagSpace R M d` by
`exteriorPower.exteriorFlagMap d`. -/
theorem basePointsRepresentation_exteriorFlag (d : ℕ) (g : WithConv (H →ₐ[R] R)) :
    (letI : Comodule R H (exteriorPower.FlagSpace R M d) := exteriorFlag R H M d
     basePointsRepresentation (R := R) (H := H) (exteriorPower.FlagSpace R M d) g) =
      exteriorPower.exteriorFlagMap d (basePointsRepresentation (R := R) (H := H) M g) := by
  induction d with
  | zero =>
    let _ : Comodule R H (⋀[R]^0 M) := exteriorPower R H M 0
    rw [exteriorFlag_zero, basePointsRepresentation_transport,
      basePointsRepresentation_exteriorPower, exteriorPower.exteriorFlagMap_zero,
      LinearEquiv.symm_symm]
  | succ r ih =>
    let _ : Comodule R H (exteriorPower.FlagSpace R M r) := exteriorFlag R H M r
    let _ : Comodule R H (⋀[R]^(r + 1) M) := exteriorPower R H M (r + 1)
    let _ : Comodule R H (exteriorPower.FlagSpace R M r ⊗[R] ⋀[R]^(r + 1) M) :=
      tensor R H (exteriorPower.FlagSpace R M r) (⋀[R]^(r + 1) M)
    rw [exteriorFlag_succ, basePointsRepresentation_transport, exteriorPower.exteriorFlagMap_succ,
      LinearEquiv.symm_symm]
    congr 2
    exact TensorProduct.ext' fun x y ↦ by
      rw [basePointsRepresentation_tensor_tmul, ih, basePointsRepresentation_exteriorPower,
        TensorProduct.map_tmul]

end Points

end TauCeti.Comodule

namespace TauCeti.Comodule

section FlagStabilizer

universe u v w

variable {k : Type u} {H : Type v} {M : Type w}
  [Field k] [CommRing H] [HopfAlgebra k H] [AddCommGroup M] [Module k M] [Comodule k H M]

/-- For a linearly independent tuple `v : Fin d → M` in a finite-dimensional comodule, the line
stabilizer of `exteriorFlagVector k d v` is the supremum of the stabilizers of its prefix spans. -/
theorem stabilizerHopfIdeal_span_exteriorFlagVector_of_linearIndependent [Module.Finite k M]
    {d : ℕ} {v : Fin d → M} (hv : LinearIndependent k v) :
    (letI : Comodule k H (exteriorPower.FlagSpace k M d) := exteriorFlag k H M d
     (k ∙ exteriorPower.exteriorFlagVector k d v).stabilizerHopfIdeal H) =
      Finset.univ.sup fun r : Fin (d + 1) ↦
        (Submodule.span k
          (Set.range (v ∘ Fin.castLE (Nat.le_of_lt_succ r.isLt)))).stabilizerHopfIdeal H := by
  induction d with
  | zero =>
    let _ : Comodule k H (⋀[k]^0 M) := exteriorPower k H M 0
    rw [exteriorFlag_zero]
    have hmap : (k ∙ _root_.exteriorPower.ιMulti k 0 v).map
        (exteriorPower.flagSpaceZeroEquiv k M).symm.toLinearMap =
        k ∙ exteriorPower.exteriorFlagVector k 0 v := by
      rw [Submodule.map_span, Set.image_singleton, LinearEquiv.coe_coe,
        ← exteriorPower.exteriorFlagVector_zero]
    rw [← hmap, Submodule.stabilizerHopfIdeal_map_transport,
      Submodule.stabilizerHopfIdeal_span_ιMulti hv]
    simp [Set.range_eq_empty]
  | succ r ih =>
    let _ : Comodule k H (exteriorPower.FlagSpace k M r) := exteriorFlag k H M r
    let _ : Comodule k H (⋀[k]^(r + 1) M) := exteriorPower k H M (r + 1)
    let _ : Comodule k H (exteriorPower.FlagSpace k M r ⊗[k] ⋀[k]^(r + 1) M) :=
      tensor k H (exteriorPower.FlagSpace k M r) (⋀[k]^(r + 1) M)
    rw [exteriorFlag_succ]
    have hv' : LinearIndependent k (v ∘ Fin.castSucc) := hv.comp _ (Fin.castSucc_injective r)
    have hx : exteriorPower.exteriorFlagVector k r (v ∘ Fin.castSucc) ≠ 0 :=
      (exteriorPower.exteriorFlagVector_ne_zero_iff (v := v ∘ Fin.castSucc)).mpr hv'
    have hy : _root_.exteriorPower.ιMulti k (r + 1) v ≠ 0 :=
      (_root_.exteriorPower.ιMulti_ne_zero_iff v).mpr hv
    have hmap : (k ∙ (exteriorPower.exteriorFlagVector k r (v ∘ Fin.castSucc) ⊗ₜ[k]
          _root_.exteriorPower.ιMulti k (r + 1) v)).map
        (exteriorPower.flagSpaceSuccEquiv k M r).symm.toLinearMap =
        k ∙ exteriorPower.exteriorFlagVector k (r + 1) v := by
      rw [Submodule.map_span, Set.image_singleton, LinearEquiv.coe_coe,
        ← exteriorPower.exteriorFlagVector_succ]
    rw [← hmap, Submodule.stabilizerHopfIdeal_map_transport,
      Submodule.stabilizerHopfIdeal_span_singleton_tmul hx hy, ih hv',
      Submodule.stabilizerHopfIdeal_span_ιMulti hv, sup_comm]
    conv_rhs =>
      rw [Fin.univ_castSuccEmb, Finset.cons_eq_insert, Finset.sup_insert, Finset.sup_map]
    rfl

/-- For a basis `b : Module.Basis (Fin d) k M`, the line stabilizer of `exteriorFlagVector k d b` is
the supremum of the stabilizers of all steps `b.flag r` of the basis flag. -/
theorem stabilizerHopfIdeal_span_exteriorFlagVector {d : ℕ} (b : Module.Basis (Fin d) k M) :
    (letI : Comodule k H (exteriorPower.FlagSpace k M d) := exteriorFlag k H M d
     (k ∙ exteriorPower.exteriorFlagVector k d b).stabilizerHopfIdeal H) =
      Finset.univ.sup fun r : Fin (d + 1) ↦ (b.flag r).stabilizerHopfIdeal H := by
  have : Module.Finite k M := Module.Finite.of_basis b
  rw [stabilizerHopfIdeal_span_exteriorFlagVector_of_linearIndependent b.linearIndependent]
  refine Finset.sup_congr rfl fun r _ ↦ ?_
  rw [Module.Basis.flag, Set.range_comp, Fin.range_castLE]
  rfl

/-- The line stabilizer of `exteriorFlagVector k d b` lies below `J` if and only if the corestricted
coefficient matrix of `b` over `H ⧸ J.toIdeal` is upper triangular. -/
theorem stabilizerHopfIdeal_span_exteriorFlagVector_le_iff {d : ℕ} (b : Module.Basis (Fin d) k M)
    (J : HopfIdeal k H) :
    (letI : Comodule k H (exteriorPower.FlagSpace k M d) := exteriorFlag k H M d
     (k ∙ exteriorPower.exteriorFlagVector k d b).stabilizerHopfIdeal H) ≤ J ↔
      (letI : Comodule k (H ⧸ J.toIdeal) M :=
        Corestrict (CommHopfAlgCat.mkQuotient (_root_.CommHopfAlgCat.of k H) J).hom.toCoalgHom
       (coefficientMatrix (C := H ⧸ J.toIdeal) b).IsUpperTriangular) := by
  let _ : Comodule k (H ⧸ J.toIdeal) M :=
    Corestrict (CommHopfAlgCat.mkQuotient (_root_.CommHopfAlgCat.of k H) J).hom.toCoalgHom
  rw [stabilizerHopfIdeal_span_exteriorFlagVector, Finset.sup_le_iff,
    coefficientMatrix_isUpperTriangular_iff (C := H ⧸ J.toIdeal) b]
  exact ⟨fun h r ↦ ((b.flag r).stabilizerHopfIdeal_le_iff_exists_subcomodule_corestrict J).mp
      (h r (Finset.mem_univ r)),
    fun h r _ ↦
      ((b.flag r).stabilizerHopfIdeal_le_iff_exists_subcomodule_corestrict J).mpr (h r)⟩

/-- If `b : Module.Basis (Fin (1 + n)) k M` has upper-triangular coefficient matrix over
`H ⧸ J.toIdeal` and its first line `k ∙ b 0` has stabilizer `J`, then the exterior flag vector of
`b` also has line stabilizer `J`. -/
theorem stabilizerHopfIdeal_span_exteriorFlagVector_eq {n : ℕ}
    (b : Module.Basis (Fin (1 + n)) k M) (J : HopfIdeal k H)
    (h0 : (k ∙ b 0).stabilizerHopfIdeal H = J)
    (htri : letI : Comodule k (H ⧸ J.toIdeal) M :=
        Corestrict (CommHopfAlgCat.mkQuotient (_root_.CommHopfAlgCat.of k H) J).hom.toCoalgHom
      (coefficientMatrix (C := H ⧸ J.toIdeal) b).IsUpperTriangular) :
    (letI : Comodule k H (exteriorPower.FlagSpace k M (1 + n)) := exteriorFlag k H M (1 + n)
     (k ∙ exteriorPower.exteriorFlagVector k (1 + n) b).stabilizerHopfIdeal H) = J := by
  refine le_antisymm ((stabilizerHopfIdeal_span_exteriorFlagVector_le_iff b J).mpr htri) ?_
  rw [stabilizerHopfIdeal_span_exteriorFlagVector, ← h0]
  have hflag1 : b.flag (Fin.succ (0 : Fin (1 + n))) = k ∙ b 0 := by
    rw [b.flag_succ, Fin.castSucc_zero, b.flag_zero, sup_bot_eq]
  rw [← hflag1]
  exact Finset.le_sup (f := fun r : Fin (1 + n + 1) ↦ (b.flag r).stabilizerHopfIdeal H)
    (Finset.mem_univ (Fin.succ 0))

/-- If `M` contains a subspace `W₀` whose stabilizer `J` has solvable `k`-points, then for *every*
basis `b : Module.Basis (Fin d) k M` the `k`-points of the quotient by the line stabilizer of
`exteriorFlagVector k d b` form a solvable group. -/
theorem isSolvable_points_quotient_stabilizerHopfIdeal_exteriorFlagVector
    {d : ℕ} (b : Module.Basis (Fin d) k M) {W₀ : Submodule k M} {J : HopfIdeal k H}
    (hW₀ : W₀.stabilizerHopfIdeal H = J)
    [Group.IsSolvable (WithConv ((H ⧸ J.toIdeal) →ₐ[k] k))] :
    letI : Comodule k H (exteriorPower.FlagSpace k M d) := exteriorFlag k H M d
    let D := (k ∙ exteriorPower.exteriorFlagVector k d b).stabilizerHopfIdeal H
    Group.IsSolvable (WithConv ((H ⧸ D.toIdeal) →ₐ[k] k)) := by
  let _ : Comodule k H (exteriorPower.FlagSpace k M d) := exteriorFlag k H M d
  set D := (k ∙ exteriorPower.exteriorFlagVector k d b).stabilizerHopfIdeal H
  let Hcat := _root_.CommHopfAlgCat.of k H
  let ιD := (CommHopfAlgCat.quotientPointsHom Hcat D (CommAlgCat.of k k)).hom
  let ιJ := (CommHopfAlgCat.quotientPointsHom Hcat J (CommAlgCat.of k k)).hom
  let eMat : (Module.End k M)ˣ ≃* Matrix.GeneralLinearGroup (Fin d) k :=
    Units.mapEquiv (LinearMap.toMatrixAlgEquiv b).toMulEquiv
  let ρ : WithConv (H →ₐ[k] k) →* Matrix.GeneralLinearGroup (Fin d) k :=
    eMat.toMonoidHom.comp (Representation.asGroupHom (basePointsRepresentation (R := k) (H := H) M))
  let f := ρ.comp ιD
  let _ : Comodule k (H ⧸ D.toIdeal) M :=
    Corestrict (CommHopfAlgCat.mkQuotient Hcat D).hom.toCoalgHom
  have htri : (coefficientMatrix (C := H ⧸ D.toIdeal) b).IsUpperTriangular :=
    (stabilizerHopfIdeal_span_exteriorFlagVector_le_iff b D).mp le_rfl
  have hf_mem (g : WithConv ((H ⧸ D.toIdeal) →ₐ[k] k)) :
      f g ∈ upperTriangularGroup (Fin d) k := by
    refine UpperTriangularGroup.mem_iff.mpr fun i j hij ↦ ?_
    have hval := congrArg (fun x ↦ g.ofConv x) (htri hij)
    rw [coefficientMatrix_apply, apply_matrixCoefficient, map_zero,
      basePointsRepresentation_corestrict] at hval
    have hιD : ιD g = toConv (g.ofConv.comp
        ((CommHopfAlgCat.mkQuotient Hcat D).hom : H →ₐ[k] _)) :=
      CommHopfAlgCat.quotientPointsHom_apply Hcat D (CommAlgCat.of k k) g
    simpa [f, ρ, eMat, hιD, LinearMap.toMatrixAlgEquiv_apply, LinearMap.toMatrix_apply,
      Representation.asGroupHom_apply] using hval
  have hker_mem (g : f.ker) :
      ιD g.val ∈ CommHopfAlgCat.quotientPointsSubgroup Hcat J (CommAlgCat.of k k) := by
    have hid : basePointsRepresentation (R := k) (H := H) M (ιD g.val) = LinearMap.id :=
      congrArg Units.val (eMat.injective (g.property.trans (map_one eMat).symm))
    rw [← hW₀, Submodule.mem_quotientPointsSubgroup_stabilizerHopfIdeal_iff, hid, Submodule.map_id]
  let k_to_J : f.ker →* ιJ.range := (ιD.comp f.ker.subtype).codRestrict ιJ.range hker_mem
  have hk_inj : Function.Injective k_to_J := fun x y hxy ↦
    Subtype.ext ((CommHopfAlgCat.quotientPointsHom_injective Hcat D (CommAlgCat.of k k))
      (congrArg Subtype.val hxy))
  have : Group.IsSolvable ιJ.range := Group.isSolvable_of_surjective ιJ.rangeRestrict_surjective
  have : Group.IsSolvable f.ker := Group.isSolvable_of_isSolvable_injective hk_inj
  refine Group.isSolvable_of_ker_le_range f.ker.subtype
    (f.codRestrict (upperTriangularGroup (Fin d) k) hf_mem) ?_
  rw [Subgroup.subtype_range, MonoidHom.ker_codRestrict]

end FlagStabilizer

end TauCeti.Comodule
