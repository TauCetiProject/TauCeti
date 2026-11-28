/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.Group.Profinite.ProP.PadicInt.Basic

/-!
# Kernels of finite characters of the additive group of the p-adic integers

For a continuous character of `ℤ_p` with finite image, the order and the kernel
determine the same level. If the order is `p ^ r`, the kernel is precisely
`p ^ r ℤ_p`. This identifies the subgroup on which the character is trivial in a
choice of coordinate on a procyclic tower.
-/

public section

open TauCeti Multiplicative

namespace ContinuousMonoidHom

/-- A continuous character of the additive group of `ℤ_p` with finite image has order
`p ^ r` and kernel `p ^ r ℤ_p` for the same `r`. -/
theorem exists_orderOf_eq_pow_and_ker_eq_padicIntLevel
    {p : ℕ} [hp : Fact p.Prime] {A : Type*} [CommGroup A] [TopologicalSpace A]
    [ContinuousMul A] [T2Space A] (χ : Multiplicative ℤ_[p] →ₜ* A)
    [Finite χ.toMonoidHom.range] :
    ∃ r : ℕ, orderOf χ = p ^ r ∧ χ.toMonoidHom.ker = (padicIntLevel p r).toSubgroup := by
  let g := ofAdd (1 : ℤ_[p])
  have hg := topologicallyGenerates_ofAdd_one_padicInt p
  have himage := (isProP_multiplicative_padicInt p).isPGroup_range χ.toMonoidHom
    (χ.toMonoidHom.ker.isOpen_of_isClosed_of_finiteIndex χ.isClosed_ker)
  obtain ⟨r, hr⟩ := himage.exists_orderOf_eq_pow (χ.toMonoidHom.rangeRestrict g)
  have hχ : orderOf (χ g) = p ^ r := by
    simpa [← Subgroup.orderOf_coe] using hr
  refine ⟨r, (χ.orderOf_apply_eq_of_topologicalGenerator hg).symm.trans hχ, ?_⟩
  let q := (PadicInt.toZModPow (p := p) r).toAddMonoidHom.toMultiplicative
  have hq : orderOf (q g) = p ^ r := by
    simp [q, g, orderOf_ofAdd_eq_addOrderOf, ZMod.addOrderOf_one]
  have hqclosed : IsClosed (q.ker : Set (Multiplicative ℤ_[p])) := by
    rw [← padicIntLevel_toSubgroup p r]
    exact (padicIntLevel p r).isClosed
  -- Both kernels are generated topologically by the same power of the generator.
  have hgen : (Subgroup.closure (insert g ∅)).topologicalClosure = ⊤ := by simp [g]
  have hpos : 0 < p ^ r := pow_pos hp.out.pos r
  rw [padicIntLevel_toSubgroup]
  exact (χ.toMonoidHom.ker_eq_topologicalClosure_normalClosure_insert_pow_of_orderOf_eq
    (a := g) (S := ∅) χ.isClosed_ker hgen (by simp) hpos hχ).trans
    (q.ker_eq_topologicalClosure_normalClosure_insert_pow_of_orderOf_eq
      (a := g) (S := ∅) hqclosed hgen (by simp) hpos hq).symm

end ContinuousMonoidHom
