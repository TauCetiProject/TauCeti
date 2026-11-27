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

/-- Over a ring with finite quotients, the unitary subgroups of any two star-orders have finite
relative index. For nested star-orders the smaller unitary subgroup thus has finite index in
the larger one. -/
theorem unitarySubgroup_isFiniteRelIndex {K : Type*} [Field K] [Algebra R K]
    [IsFractionRing R K] [Ring.HasFiniteQuotients R] [Algebra K E] [IsScalarTower R K E]
    (O P : StarOrder R K E) : O.unitarySubgroup.IsFiniteRelIndex P.unitarySubgroup := by
  have : IsDomain R := (IsFractionRing.isDomain_iff_isField (K := K)).2 (Field.toIsField K)
  let Λ := O.toSubalgebra
  let Γ := P.toSubalgebra
  have hfg : Γ.toSubmodule.FG := Module.Finite.iff_fg.1 P.isOrder.finite
  obtain ⟨r, hr, hrΓ⟩ := hfg.exists_smul_mem_of_le_span (F := K) (M := Λ.toSubmodule) R⁰ (by
    intro v _
    -- The subalgebra and its underlying submodule have the same carrier.
    change v ∈ Submodule.span K (Λ : Set E)
    rw [O.isOrder.span_eq_top]
    trivial)
  have hr0 : r ≠ 0 := nonZeroDivisors.ne_zero hr
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
  let reduction : P.unitarySubgroup →* (Γ ⧸ J)ˣ :=
    ((Ideal.Quotient.mk J).toMonoidHom.comp inclusion).toHomUnits
  have : reduction.ker.FiniteIndex := inferInstance
  rw [Subgroup.isFiniteRelIndex_iff_finiteIndex]
  refine Subgroup.finiteIndex_of_le (H := reduction.ker) fun x hx => ?_
  have hxred : reduction x = 1 := MonoidHom.mem_ker.mp hx
  have hxquot : Ideal.Quotient.mk J (inclusion x) = Ideal.Quotient.mk J 1 := by
    have hxval := congrArg Units.val hxred
    simpa only [reduction, MonoidHom.coe_toHomUnits, MonoidHom.comp_apply,
      RingHom.toMonoidHom_eq_coe, MonoidHom.coe_ofClass, Units.val_one, map_one] using hxval
  have hx' : inclusion x - 1 ∈ J := Ideal.Quotient.eq.mp hxquot
  rw [Ideal.mem_map_algebraMap_iff, Submodule.ideal_span_singleton_smul] at hx'
  obtain ⟨y, _, hy⟩ := (Submodule.mem_smul_pointwise_iff_exists _ r ⊤).mp hx'
  have hsub : ((inclusion x : Γ) : E) - 1 ∈ Λ := by
    rw [← Subalgebra.coe_one Γ, ← Subalgebra.coe_sub, ← hy]
    exact hrΓ y y.property
  refine (mem_unitarySubgroup O).2 (mem_toSubalgebra.mp ?_)
  simpa [inclusion, Λ] using Λ.add_mem hsub Λ.one_mem

end TauCeti.IntegralOrder.StarOrder
