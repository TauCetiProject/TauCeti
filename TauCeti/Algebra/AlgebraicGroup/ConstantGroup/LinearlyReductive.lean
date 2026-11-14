/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.ConstantGroup.Basic
public import TauCeti.Algebra.AlgebraicGroup.Hopf.Translation
public import TauCeti.Algebra.AlgebraicGroup.LinearlyReductive
import TauCeti.Algebra.AlgebraicGroup.ConstantGroup.Points
import TauCeti.Algebra.AlgebraicGroup.LinearlyReductive.FiniteSubgroup
import TauCeti.Algebra.AlgebraicGroup.Representation.PointsAction.Hom
import TauCeti.Algebra.Coalgebra.Comodule.LinearlyReductive.Exact
import TauCeti.LinearAlgebra.TensorProduct.Basic

/-!
# Linear reductivity of finite constant groups

Over a commutative ring `R`, summing all right translates of a coordinate function on a finite
constant group `G` produces a constant function, and in any comodule over
`TauCeti.ConstantGroup.coordinateRing R G`, the invariant vectors are characterized as the vectors
fixed by the rational point of every element of `G` (with no projectivity or finiteness assumption
on the comodule).

Over a field `k`, it follows that the constant affine group attached to a finite group `G` is
linearly reductive if and only if `(Nat.card G : k) ≠ 0`. This is the affine-group form of
Maschke's theorem, and supplies the component-group input for characterizing linear reductivity of
disconnected affine groups.

## Main declarations

* `TauCeti.ConstantGroup.sum_rightTranslationAlgHom_toPoints_mem_range`: summing all right
  translates of a coordinate function on a finite constant group yields a scalar.
* `TauCeti.ConstantGroup.mem_fixedSubcomodule_iff_forall_basePointsRepresentation_toPoints`:
  pointwise characterization of fixed vectors in comodules over a finite constant group.
* `TauCeti.ConstantGroup.natCast_card_ne_zero_of_isLinearlyReductive_coordinateRing`: linear
  reductivity of `coordinateRing k G` implies `(Nat.card G : k) ≠ 0`.
* `TauCeti.ConstantGroup.isLinearlyReductive_coordinateRing_of_natCast_card_ne_zero`: conversely,
  invertibility of `Nat.card G` in `k` implies linear reductivity of `coordinateRing k G`.
* `TauCeti.ConstantGroup.isLinearlyReductive_coordinateRing_iff` and
  `TauCeti.ConstantGroup.linearlyReductiveCommHopfAlgProperty_coordinateRing_iff`: the resulting
  equivalences.

## References

* M. Nagata, *Complete reducibility of rational representations of a matric group*,
  J. Math. Kyoto Univ. **1** (1961), 87–99.
* W. C. Waterhouse, *Introduction to Affine Group Schemes*, Section 3.3.
* J. S. Milne, *Algebraic Groups* (2017), Section 12.g.
-/

public section

open scoped TensorProduct
open WithConv

namespace TauCeti.ConstantGroup

universe u v w

section CommRing

variable {R : Type u} [CommRing R]

/-- Summing all right translates of a coordinate function on a finite constant group yields a
constant function in the image of `algebraMap`. -/
theorem sum_rightTranslationAlgHom_toPoints_mem_range {G : Type v} [Group G] [Fintype G]
    (a : coordinateRing R G) :
    (∑ g : G, HopfAlgebra.rightTranslationAlgHom (toPoints R G g) a) ∈
      Set.range (algebraMap R (coordinateRing R G)) := by
  refine ⟨∑ g : G, functionAlgEquiv R G a g, ?_⟩
  apply (functionAlgEquiv R G).injective
  ext h
  rw [AlgEquiv.commutes, Pi.algebraMap_apply, Algebra.algebraMap_self_apply, map_sum,
    Fintype.sum_apply]
  have hterm (g : G) :
      functionAlgEquiv R G (HopfAlgebra.rightTranslationAlgHom (toPoints R G g) a) h =
        functionAlgEquiv R G a (h * g) := by
    rw [← eval_apply, ← toPoints_apply, HopfAlgebra.ofConv_rightTranslationAlgHom, ← map_mul,
      toPoints_apply, eval_apply]
  simp_rw [hterm]
  exact (Equiv.sum_comp (Equiv.mulLeft h) (functionAlgEquiv R G a)).symm

/-- In any comodule over the coordinate Hopf algebra of a finite constant group, a vector is fixed
by the coaction if and only if it is fixed by the rational point of every element of `G`. -/
theorem mem_fixedSubcomodule_iff_forall_basePointsRepresentation_toPoints
    {G : Type v} [Group G] [Finite G] {M : Type w} [AddCommMonoid M] [Module R M]
    [Comodule R (coordinateRing R G) M] {m : M} :
    m ∈ Comodule.fixedSubcomodule R (coordinateRing R G) M ↔
      ∀ g : G, Comodule.basePointsRepresentation (H := coordinateRing R G) M (toPoints R G g) m =
        m := by
  classical
  let _ : Fintype G := Fintype.ofFinite G
  constructor
  · intro hm g
    exact Comodule.basePointsRepresentation_eq_of_coact_eq_tmul_one m
      (Comodule.mem_fixedSubcomodule.mp hm) (toPoints R G g)
  · intro hm
    let b : G → coordinateRing R G := delta R G
    let φ : G → (coordinateRing R G →ₗ[R] R) := fun g ↦ (toPoints R G g).ofConv.toLinearMap
    have hb (x : coordinateRing R G) : ∑ g : G, φ g x • b g = x := by
      apply (functionAlgEquiv R G).injective
      ext h
      simp [φ, b, toPoints_apply]
    rw [Comodule.mem_fixedSubcomodule,
      ← LinearMap.sum_tensorComponent_tmul b φ hb (Comodule.coact m),
      ← LinearMap.sum_tensorComponent_tmul b φ hb (m ⊗ₜ[R] 1)]
    refine Finset.sum_congr rfl fun g _ ↦ ?_
    have hcomp : LinearMap.tensorComponent (φ g)
        (Comodule.coact (R := R) (C := coordinateRing R G) m) = m := by
      have hg := congrArg (TensorProduct.lid R M)
        (Comodule.endOfPoint_one_tmul_eq_one_tmul_basePointsRepresentation (toPoints R G g) m)
      simpa only [φ, LinearMap.tensorComponent_def, LinearMap.comp_apply, LinearEquiv.coe_coe,
        TensorProduct.lid_comm, TensorProduct.lid_tmul, one_smul, hm g] using hg
    rw [hcomp, LinearMap.tensorComponent_tmul]
    simp [φ]

end CommRing

section Field

variable {k : Type u} [Field k] {G : Type v} [Group G] [Finite G]

/-- If the constant group attached to a finite group `G` is linearly reductive over `k`, then the
order of `G` is nonzero in `k`. -/
theorem natCast_card_ne_zero_of_isLinearlyReductive_coordinateRing
    (h : Coalgebra.IsLinearlyReductive.{u, max u v, u} k (coordinateRing k G)) :
    (Nat.card G : k) ≠ 0 := by
  let e := (pointsMulEquiv k G).toEquiv
  let _ : Finite (WithConv (coordinateRing k G →ₐ[k] k)) := Finite.of_equiv G e
  have heq : Nat.card (⊤ : Subgroup (WithConv (coordinateRing k G →ₐ[k] k))) = Nat.card G :=
    Nat.card_congr (Subgroup.topEquiv.toEquiv.trans e.symm)
  simpa only [heq] using HopfAlgebra.natCast_card_ne_zero_of_isLinearlyReductive h ⊤

/-- **Maschke's theorem for finite constant groups.** If the order of a finite group `G` is
nonzero in the field `k`, then the coordinate Hopf algebra of the constant group attached to `G`
is linearly reductive over `k`. -/
theorem isLinearlyReductive_coordinateRing_of_natCast_card_ne_zero
    (hcard : (Nat.card G : k) ≠ 0) :
    Coalgebra.IsLinearlyReductive.{u, max u v, u} k (coordinateRing k G) := by
  let _ : Fintype G := Fintype.ofFinite G
  let _ : AddCommGroup (coordinateRing k G) := inferInstance
  rw [Coalgebra.isLinearlyReductive_iff_forall_fixedMap_surjective_of_surjective]
  intro M N f hf n
  let _ : AddCommGroup M := Module.addCommMonoidToAddCommGroup k
  let _ : AddCommGroup N := Module.addCommMonoidToAddCommGroup k
  let φ : Comodule.Hom k (coordinateRing k G) M N := CategoryTheory.ConcreteCategory.hom f.hom
  obtain ⟨m₀, hm₀⟩ := hf n.1
  let ρM := Comodule.basePointsRepresentation (R := k) (H := coordinateRing k G) M
  let m : M := (Nat.card G : k)⁻¹ • ∑ g : G, ρM (toPoints k G g) m₀
  have hm : m ∈ Comodule.fixedSubcomodule k (coordinateRing k G) M := by
    refine mem_fixedSubcomodule_iff_forall_basePointsRepresentation_toPoints.mpr fun g ↦ ?_
    simp only [ρM, m, map_smul, map_sum]
    congr 1
    have hmul (x : G) :
        Comodule.basePointsRepresentation (H := coordinateRing k G) M (toPoints k G g)
          (Comodule.basePointsRepresentation (H := coordinateRing k G) M (toPoints k G x) m₀) =
        Comodule.basePointsRepresentation (H := coordinateRing k G) M
          (toPoints k G (g * x)) m₀ := by
      rw [map_mul, map_mul, mul_apply_eq_comp]
    simp_rw [hmul]
    exact Equiv.sum_comp (Equiv.mulLeft g) fun x ↦
      Comodule.basePointsRepresentation (H := coordinateRing k G) M (toPoints k G x) m₀
  have hfm : φ m = n.1 := by
    have hn (g : G) : φ (ρM (toPoints k G g) m₀) = n.1 := by
      rw [φ.map_basePointsRepresentation, hm₀]
      exact Comodule.basePointsRepresentation_eq_of_coact_eq_tmul_one n.1
        (Comodule.mem_fixedSubcomodule.mp n.2) (toPoints k G g)
    calc
      φ m = (Nat.card G : k)⁻¹ • ∑ g : G, φ (ρM (toPoints k G g) m₀) := by
        rw [← φ.coe_toLinearMap, map_smul, map_sum]
      _ = n.1 := by
        simp only [hn, Finset.sum_const, Finset.card_univ, Fintype.card_eq_nat_card,
          ← Nat.cast_smul_eq_nsmul k, inv_smul_smul₀ hcard]
  exact ⟨⟨m, hm⟩, Subtype.ext ((φ.fixedMap_apply ⟨m, hm⟩).trans hfm)⟩

end Field

/-- Over a field `k`, the coordinate Hopf algebra of a finite constant group `G` is linearly
reductive if and only if `(Nat.card G : k) ≠ 0`. -/
@[simp]
theorem isLinearlyReductive_coordinateRing_iff (k : Type u) [Field k]
    (G : Type v) [Group G] [Finite G] :
    Coalgebra.IsLinearlyReductive.{u, max u v, u} k (coordinateRing k G) ↔
      (Nat.card G : k) ≠ 0 :=
  ⟨natCast_card_ne_zero_of_isLinearlyReductive_coordinateRing,
    isLinearlyReductive_coordinateRing_of_natCast_card_ne_zero⟩

/-- A finite constant group over a field `k` satisfies `linearlyReductiveCommHopfAlgProperty` if
and only if `(Nat.card G : k) ≠ 0`. -/
theorem linearlyReductiveCommHopfAlgProperty_coordinateRing_iff (k : Type u) [Field k]
    (G : Type v) [Group G] [Finite G] :
    linearlyReductiveCommHopfAlgProperty k (CommHopfAlgCat.of k (coordinateRing k G)) ↔
      (Nat.card G : k) ≠ 0 :=
  (linearlyReductiveCommHopfAlgProperty_iff k _).trans (isLinearlyReductive_coordinateRing_iff k G)

end TauCeti.ConstantGroup
