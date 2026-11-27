/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Star.Unitary
public import Mathlib.GroupTheory.Index
public import Mathlib.RingTheory.Ideal.Quotient.HasFiniteQuotients.Basic
public import TauCeti.RingTheory.IntegralOrder.Star
import Mathlib.RingTheory.Ideal.Quotient.Index
import TauCeti.Algebra.Module.LocalizedModule.Submodule
import TauCeti.RingTheory.Ideal.Extended

/-!
# Unitary subgroups of star-orders

The unitary elements in a star-order form a subgroup of the ambient unitary group. Over a ring
with finite quotients, the unitary subgroups of any two star-orders have finite relative index.
The proof adapts the argument for quaternion orders in Voight, *Quaternion algebras*, §38.3.1.
-/

public section

open scoped Pointwise nonZeroDivisors

namespace TauCeti.IntegralOrder.StarOrder

variable {R F E : Type*} [CommRing R] [CommRing F] [Ring E] [StarRing E]
  [Algebra R E] [Algebra F E] {O P : StarOrder R F E}

/-- The subgroup of ambient unitary elements belonging to a star-order. -/
def unitarySubgroup (O : StarOrder R F E) : Subgroup (unitary E) where
  carrier := {x | (x : E) ∈ O}
  one_mem' := one_mem O
  mul_mem' := mul_mem
  inv_mem' := O.star_mem'

/-- An ambient unitary element belongs to the subgroup exactly when it belongs to the order. -/
@[simp]
theorem mem_unitarySubgroup (O : StarOrder R F E) {x : unitary E} :
    x ∈ O.unitarySubgroup ↔ (x : E) ∈ O :=
  Iff.rfl

/-- Inclusion of star-orders induces inclusion of their unitary subgroups. -/
theorem unitarySubgroup_mono (h : O ≤ P) : O.unitarySubgroup ≤ P.unitarySubgroup :=
  fun _ hx => h hx

omit [StarRing E] in
private theorem mem_of_sub_one_mem_map {Λ Γ : Subalgebra R E} {r : R}
    (hrΓ : ∀ v ∈ Γ, r • v ∈ Λ) (z : Γ)
    (hz : z - 1 ∈ (Ideal.span {r}).map (algebraMap R Γ)) : (z : E) ∈ Λ := by
  rw [Ideal.mem_map_algebraMap_iff, Submodule.ideal_span_singleton_smul] at hz
  obtain ⟨y, _, hy⟩ := (Submodule.mem_smul_pointwise_iff_exists _ r ⊤).mp hz
  have hdiff : r • (y : E) = (z : E) - 1 := by
    simpa only [Subalgebra.coe_smul, Subalgebra.coe_sub, Subalgebra.coe_one] using
      congrArg ((↑) : Γ → E) hy
  have hsub : (z : E) - 1 ∈ Λ := hdiff ▸ hrΓ y y.property
  simpa only [sub_add_cancel] using Λ.add_mem hsub Λ.one_mem

/-- Over a ring with finite quotients, the unitary subgroups of any two star-orders have finite
relative index. For nested star-orders the smaller unitary subgroup thus has finite index in
the larger one. -/
theorem unitarySubgroup_isFiniteRelIndex {K : Type*} [Field K] [Algebra R K]
    [IsFractionRing R K] [Ring.HasFiniteQuotients R] [Algebra K E] [IsScalarTower R K E]
    (O P : StarOrder R K E) : O.unitarySubgroup.IsFiniteRelIndex P.unitarySubgroup := by
  have : IsDomain R := (IsFractionRing.isDomain_iff_isField (K := K)).2 (Field.toIsField K)
  let Λ := O.toSubalgebra
  let Γ := P.toSubalgebra
  -- Clear denominators uniformly so that a nonzero scalar carries Γ into Λ.
  have hfg : Γ.toSubmodule.FG := Module.Finite.iff_fg.1 P.isOrder.finite
  obtain ⟨r, hr, hrΓ⟩ := hfg.exists_smul_mem_of_le_span (F := K) (M := Λ.toSubmodule) R⁰ (by
    intro v _
    -- The subalgebra and its underlying submodule have the same carrier.
    change v ∈ Submodule.span K (Λ : Set E)
    rw [O.isOrder.span_eq_top]
    trivial)
  have hr0 : r ≠ 0 := nonZeroDivisors.ne_zero hr
  -- Reduce the unitary subgroup of Γ into the units of the finite quotient Γ / rΓ.
  have : Finite (R ⧸ Ideal.span {r}) :=
    Ring.HasFiniteQuotients.finiteQuotient (by simpa using hr0)
  have := P.isOrder.finite
  have : Finite (Γ ⧸ (Ideal.span {r} • (⊤ : Submodule R Γ))) :=
    Submodule.finite_quotient_smul (Ideal.span {r}) (Module.Finite.fg_top (R := R) (M := Γ))
  let J : Ideal Γ := (Ideal.span {r}).map (algebraMap R Γ)
  let inclusion : P.unitarySubgroup →* Γ :=
    { toFun := fun x => ⟨(x.val : E), (mem_unitarySubgroup P).mp x.property⟩
      map_one' := rfl
      map_mul' _ _ := rfl }
  have inclusion_coe (x : P.unitarySubgroup) : ((inclusion x : Γ) : E) = (x.val : E) :=
    rfl
  let reduction : P.unitarySubgroup →* (Γ ⧸ J)ˣ :=
    ((Ideal.Quotient.mk J).toMonoidHom.comp inclusion).toHomUnits
  have reduction_val (x : P.unitarySubgroup) :
      (reduction x : Γ ⧸ J) = Ideal.Quotient.mk J (inclusion x) :=
    MonoidHom.coe_toHomUnits _ _
  have : reduction.ker.FiniteIndex := inferInstance
  -- A kernel element is congruent to one modulo rΓ, so it belongs to Λ.
  have hker : reduction.ker ≤ O.unitarySubgroup.subgroupOf P.unitarySubgroup := by
    intro x hx
    have hxval : (reduction x : Γ ⧸ J) = 1 :=
      Units.ext_iff.mp (MonoidHom.mem_ker.mp hx)
    have hxquot : Ideal.Quotient.mk J (inclusion x) = Ideal.Quotient.mk J 1 := by
      rw [← reduction_val, map_one]
      exact hxval
    have hx' : inclusion x - 1 ∈ J := Ideal.Quotient.eq.mp hxquot
    have hmem := mem_of_sub_one_mem_map hrΓ (inclusion x) hx'
    rw [inclusion_coe] at hmem
    exact (mem_unitarySubgroup O).2 (mem_toSubalgebra.mp hmem)
  rw [Subgroup.isFiniteRelIndex_iff_finiteIndex]
  exact Subgroup.finiteIndex_of_le hker

end TauCeti.IntegralOrder.StarOrder
