/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.Perm.Cycle.Enumeration
public import TauCeti.LinearAlgebra.WeightedCycle.Family.Signed
public import TauCeti.Logic.Equiv.Fin.Rotate

/-!
# Fixed vectors of a linear map permuting a basis up to sign

Let `b` be a finite basis of a `ℤ`-module `V`, let `π` be a permutation of its index type and let
`w` assign a sign `±1` to every index. A linear map `f` with `f (b i) = w i • b (π i)` permutes the
basis vectors along the cycles of `π`, up to the signs `w`. The *monodromy* of a cycle is the
product of the signs `w x` over its points. The fixed vectors of `f` are classified by the cycles:

* a cycle of monodromy `1` with chosen point `x` carries a fixed vector `∑ cᵣ • b (π^[r] x)`, with
  `c₀ = 1` and `cᵣ₊₁ = cᵣ * w (π^[r] x)`;
* a cycle of monodromy `-1` carries no nonzero fixed vector over `ℤ`.

So the fixed submodule `f.fixedSubmodule` is free, with a basis indexed by the cycles of
monodromy `1` (`Module.Basis.fixedBasisOfPerm`). The coordinate of a fixed vector on a cycle is
its coefficient at the chosen point of that cycle. This is the weighted-cycle classification
`Module.Basis.fixedBasisSignedFamily` with the cycles of `π` enumerated by
`Equiv.Perm.sigmaCycleEquiv`, so that only the permutation and the signs have to be supplied.

## Main definitions

* `Module.Basis.fixedBasisOfPerm`: the basis of `f.fixedSubmodule` indexed by the cycles of `π`
  of monodromy `1`.

## Main results

* `Module.Basis.repr_apply_perm_of_mem_fixedSubmodule`: the coefficients of a fixed vector satisfy
  `b.repr v (π i) = w i * b.repr v i`, over any commutative semiring.
* `Module.Basis.repr_eq_zero_of_mem_fixedSubmodule_of_finprod_ne_one`: a fixed vector has no
  component on a cycle of monodromy `-1`.
* `Module.Basis.fixedBasisOfPerm_repr`: the coordinates of a fixed vector are its coefficients at
  the chosen points of the cycles.
* `Module.Basis.repr_fixedBasisOfPerm_iterate`: the coefficients of a basis vector along its
  cycle are the products of the signs met so far.
* `Module.Basis.repr_fixedBasisOfPerm_of_not_sameCycle`: each basis vector is supported on its
  cycle.
* `Module.Basis.fixedBasisOfPerm_apply_of_forall_eq_one`: on a cycle with all signs `1` the basis
  vector is the sum of the basis vectors of the cycle.
-/

public section

open Function Equiv.Perm

namespace Module.Basis

section CommSemiring

variable {A V ι : Type*} [CommSemiring A] [AddCommMonoid V] [Module A V]

/-- **Coefficients of a fixed vector.** If `f (b i) = w i • b (π i)` and `f v = v`, then the
coefficient of `v` at `π i` is `w i` times its coefficient at `i`. -/
theorem repr_apply_perm_of_mem_fixedSubmodule (b : Basis ι A V) (π : Equiv.Perm ι) (w : ι → A)
    {f : V →ₗ[A] V} (h : ∀ i, f (b i) = w i • b (π i)) {v : V} (hv : v ∈ f.fixedSubmodule)
    (i : ι) : b.repr v (π i) = w i * b.repr v i := by
  have key : (Finsupp.lapply (π i) ∘ₗ b.repr.toLinearMap) ∘ₗ f =
      w i • (Finsupp.lapply i ∘ₗ b.repr.toLinearMap) :=
    b.ext fun j ↦ by
      by_cases hj : j = i
      · subst hj
        simp [h]
      · simp [h, π.injective.eq_iff, Ne.symm hj]
  have hfv : f v = v := LinearMap.mem_fixedSubmodule_iff.mp hv
  simpa [hfv] using congr($key v)

end CommSemiring

variable {V ι : Type*} [AddCommGroup V] [Finite ι]
  (b : Basis ι ℤ V) (π : Equiv.Perm ι) (w : ι → ℤˣ) {f : V →ₗ[ℤ] V}

private theorem minimalPeriod_sub_one_add_one (x : ι) :
    minimalPeriod π x - 1 + 1 = minimalPeriod π x :=
  Nat.sub_add_cancel (minimalPeriod_pos_of_mem_periodicPts (π.injective.mem_periodicPts x))

/-- The enumeration `Equiv.Perm.sigmaCycleEquiv`, with every cycle length written as a successor,
the shape taken by the weighted-cycle classification. -/
private noncomputable def cycleEnum :
    (Σ c : Quotient (SameCycle.setoid π), Fin (minimalPeriod π c.out - 1 + 1)) ≃ ι :=
  (Equiv.sigmaCongrRight fun c : Quotient (SameCycle.setoid π) ↦
    finCongr (minimalPeriod_sub_one_add_one π c.out)).trans
    π.sigmaCycleEquiv

private theorem apply_cycleEnum (c : Quotient (SameCycle.setoid π))
    (i : Fin (minimalPeriod π c.out - 1 + 1)) :
    π (cycleEnum π ⟨c, i⟩) = cycleEnum π ⟨c, finRotate _ i⟩ := by
  simp only [cycleEnum, Equiv.trans_apply, Equiv.sigmaCongrRight_apply, apply_sigmaCycleEquiv,
    TauCeti.finCongr_finRotate]

private theorem cycleEnum_zero (c : Quotient (SameCycle.setoid π)) :
    cycleEnum π ⟨c, 0⟩ = c.out := by
  simp [cycleEnum]

private theorem mk_cycleEnum
    (p : Σ c : Quotient (SameCycle.setoid π), Fin (minimalPeriod π c.out - 1 + 1)) :
    Quotient.mk (SameCycle.setoid π) (cycleEnum π p) = p.1 := by
  obtain ⟨c, i⟩ := p
  exact π.mk_sigmaCycleEquiv ⟨c, finCongr _ i⟩

@[to_additive]
private theorem prod_cycleEnum {M : Type*} [CommMonoid M] (c : Quotient (SameCycle.setoid π))
    (g : ι → M) : ∏ i, g (cycleEnum π ⟨c, i⟩) = ∏ᶠ (x) (_ : π.SameCycle c.out x), g x := by
  classical
  have := Fintype.ofFinite ι
  rw [finprod_cond_eq_prod_of_cond_iff g (t := Finset.univ.filter (π.SameCycle c.out)) (by simp),
    ← prod_sigmaCycleEquiv]
  exact Fintype.prod_equiv (finCongr (minimalPeriod_sub_one_add_one π c.out)) _ _
    fun _ ↦ rfl

private theorem cycleEnum_sign (c : Quotient (SameCycle.setoid π))
    (i : Fin (minimalPeriod π c.out - 1 + 1)) :
    (w (cycleEnum π ⟨c, i⟩) : ℤ) = 1 ∨ (w (cycleEnum π ⟨c, i⟩) : ℤ) = -1 :=
  Int.isUnit_iff.mp (Units.isUnit _)

private theorem apply_basis_cycleEnum (h : ∀ i, f (b i) = w i • b (π i))
    (c : Quotient (SameCycle.setoid π)) (i : Fin (minimalPeriod π c.out - 1 + 1)) :
    f (b (cycleEnum π ⟨c, i⟩)) =
      (w (cycleEnum π ⟨c, i⟩) : ℤ) • b (cycleEnum π ⟨c, finRotate _ i⟩) := by
  rw [h, apply_cycleEnum, Units.smul_def]

/-- A cycle has monodromy `1` in the sense of the enumeration exactly when the product of the
signs over its points is `1`. -/
private noncomputable def positiveCycleEquiv :
    {c : Quotient (SameCycle.setoid π) // ∏ i, (w (cycleEnum π ⟨c, i⟩) : ℤ) = 1} ≃
      {c : Quotient (SameCycle.setoid π) // ∏ᶠ (x) (_ : π.SameCycle c.out x), w x = 1} :=
  Equiv.subtypeEquivRight fun c ↦ by
    rw [← Units.coe_prod, prod_cycleEnum, Units.val_eq_one]

private theorem positiveCycleEquiv_symm_apply
    (c : {c : Quotient (SameCycle.setoid π) // ∏ᶠ (x) (_ : π.SameCycle c.out x), w x = 1}) :
    (positiveCycleEquiv π w).symm c = ⟨c.1, ((positiveCycleEquiv π w).symm c).2⟩ :=
  (rfl)

/-- **Fixed vectors vanish on cycles of monodromy `-1`.** If `f (b i) = w i • b (π i)` and the
product of the signs `w` over the cycle of `π` through `y` is not `1`, then every fixed vector of
`f` has coefficient `0` at `y`. -/
theorem repr_eq_zero_of_mem_fixedSubmodule_of_finprod_ne_one (h : ∀ i, f (b i) = w i • b (π i))
    {v : V} (hv : v ∈ f.fixedSubmodule) {y : ι} (hy : ∏ᶠ (x) (_ : π.SameCycle y x), w x ≠ 1) :
    b.repr v y = 0 := by
  obtain ⟨⟨c, i⟩, rfl⟩ := (cycleEnum π).surjective y
  have hout : ∀ x, π.SameCycle (cycleEnum π ⟨c, i⟩) x ↔ π.SameCycle c.out x := fun x ↦ by
    have hc : π.SameCycle c.out (cycleEnum π ⟨c, i⟩) := by
      have := mk_cycleEnum π ⟨c, i⟩
      exact (Quotient.mk_eq_iff_out.1 this).symm
    exact ⟨hc.trans, hc.symm.trans⟩
  simp_rw [hout] at hy
  have hneg : ∏ k, (w (cycleEnum π ⟨c, k⟩) : ℤ) = -1 := by
    rw [← Units.coe_prod, prod_cycleEnum]
    rcases Int.units_eq_one_or (∏ᶠ (x) (_ : π.SameCycle c.out x), w x) with h1 | h1
    · exact absurd h1 hy
    · rw [h1, Units.val_neg, Units.val_one]
  have : Subsingleton (Submodule.torsionBy ℤ ℤ 2) := TauCeti.subsingleton_torsionBy_int 2 ℤ
  let e := b.fixedEquivSignedFamily (cycleEnum π) (fun c k ↦ (w (cycleEnum π ⟨c, k⟩) : ℤ))
    (cycleEnum_sign π w) f (b.apply_basis_cycleEnum π w h)
  have hrepr := b.fixedEquivSignedFamily_symm_repr_neg (cycleEnum π)
    (fun c k ↦ (w (cycleEnum π ⟨c, k⟩) : ℤ)) (cycleEnum_sign π w) f
    (b.apply_basis_cycleEnum π w h) (e ⟨v, hv⟩) ⟨c, hneg⟩ i
  rw [LinearEquiv.symm_apply_apply] at hrepr
  rw [show (e ⟨v, hv⟩).2 ⟨c, hneg⟩ = 0 from Subsingleton.elim _ _] at hrepr
  simpa using hrepr

/-- **Integral basis of the fixed vectors of a signed permutation of a basis.** If
`f (b i) = w i • b (π i)` with signs `w i = ±1`, the fixed submodule of `f` has a basis indexed by
the cycles `c` of `π` whose monodromy `∏ x ∈ c, w x` is `1`. The coordinate of a fixed vector on
`c` is its coefficient at the chosen point `c.out` (`Module.Basis.fixedBasisOfPerm_repr`). -/
noncomputable def fixedBasisOfPerm (h : ∀ i, f (b i) = w i • b (π i)) :
    Basis {c : Quotient (SameCycle.setoid π) // ∏ᶠ (x) (_ : π.SameCycle c.out x), w x = 1} ℤ
      f.fixedSubmodule :=
  (b.fixedBasisSignedFamily (cycleEnum π) (fun c k ↦ (w (cycleEnum π ⟨c, k⟩) : ℤ))
    (cycleEnum_sign π w) f (b.apply_basis_cycleEnum π w h)).reindex (positiveCycleEquiv π w)

/-- The coordinate of a fixed vector on the cycle `c` is its coefficient at the chosen point
`c.out` of that cycle. -/
@[simp]
theorem fixedBasisOfPerm_repr (h : ∀ i, f (b i) = w i • b (π i)) (v : f.fixedSubmodule)
    (c : {c : Quotient (SameCycle.setoid π) // ∏ᶠ (x) (_ : π.SameCycle c.out x), w x = 1}) :
    (b.fixedBasisOfPerm π w h).repr v c = b.repr v c.1.out := by
  simp [fixedBasisOfPerm, positiveCycleEquiv, cycleEnum_zero]

/-- The basis vector of the cycle `c` has coefficient `1` at the chosen point of `c`. -/
@[simp]
theorem repr_fixedBasisOfPerm_out (h : ∀ i, f (b i) = w i • b (π i))
    (c : {c : Quotient (SameCycle.setoid π) // ∏ᶠ (x) (_ : π.SameCycle c.out x), w x = 1}) :
    b.repr (b.fixedBasisOfPerm π w h c) c.1.out = 1 := by
  rw [← b.fixedBasisOfPerm_repr π w h, repr_self, Finsupp.single_eq_same]

/-- **The coefficients of a basis vector along its cycle.** The basis vector of the cycle `c` has
coefficient `∏_{k < r} w (π^[k] c.out)` at the point `π^[r] c.out`. -/
theorem repr_fixedBasisOfPerm_iterate (h : ∀ i, f (b i) = w i • b (π i))
    (c : {c : Quotient (SameCycle.setoid π) // ∏ᶠ (x) (_ : π.SameCycle c.out x), w x = 1})
    (r : ℕ) :
    b.repr (b.fixedBasisOfPerm π w h c) (π^[r] c.1.out) =
      ∏ k ∈ Finset.range r, (w (π^[k] c.1.out) : ℤ) := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [iterate_succ_apply', repr_apply_perm_of_mem_fixedSubmodule b π (fun i ↦ (w i : ℤ))
      (fun i ↦ by rw [h, Units.smul_def]) (b.fixedBasisOfPerm π w h c).2, ih,
      Finset.prod_range_succ, mul_comm]

/-- **Each basis vector is supported on its cycle.** The basis vector of the cycle `c` has
coefficient `0` at every point outside `c`. -/
theorem repr_fixedBasisOfPerm_of_not_sameCycle (h : ∀ i, f (b i) = w i • b (π i))
    (c : {c : Quotient (SameCycle.setoid π) // ∏ᶠ (x) (_ : π.SameCycle c.out x), w x = 1}) {y : ι}
    (hy : ¬π.SameCycle c.1.out y) : b.repr (b.fixedBasisOfPerm π w h c) y = 0 := by
  classical
  obtain ⟨⟨d, i⟩, rfl⟩ := (cycleEnum π).surjective y
  have hcd : c.1 ≠ d := by
    rintro rfl
    exact hy (Quotient.mk_eq_iff_out.1 (mk_cycleEnum π ⟨c.1, i⟩)).symm
  by_cases hd : ∏ k, (w (cycleEnum π ⟨d, k⟩) : ℤ) = 1
  · have := b.fixedBasisSignedFamily_repr_pos (cycleEnum π)
      (fun c k ↦ (w (cycleEnum π ⟨c, k⟩) : ℤ)) (cycleEnum_sign π w) f
      (b.apply_basis_cycleEnum π w h) ((positiveCycleEquiv π w).symm c) ⟨d, hd⟩ i
    have hne : (positiveCycleEquiv π w).symm c ≠ ⟨d, hd⟩ := fun h ↦
      hcd (by simpa [positiveCycleEquiv] using congrArg Subtype.val h)
    rw [fixedBasisOfPerm, reindex_apply, this]
    simp [hne]
  · refine b.repr_eq_zero_of_mem_fixedSubmodule_of_finprod_ne_one π w h
      (b.fixedBasisOfPerm π w h c).2 ?_
    have hout : ∀ x, π.SameCycle (cycleEnum π ⟨d, i⟩) x ↔ π.SameCycle d.out x := fun x ↦ by
      have hc : π.SameCycle d.out (cycleEnum π ⟨d, i⟩) :=
        (Quotient.mk_eq_iff_out.1 (mk_cycleEnum π ⟨d, i⟩)).symm
      exact ⟨hc.trans, hc.symm.trans⟩
    simp_rw [hout]
    rwa [← prod_cycleEnum, ne_eq, ← Units.val_eq_one, Units.coe_prod]

/-- **Cycles with trivial signs.** If every sign on the cycle `c` is `1`, the basis vector of `c`
is the sum of the basis vectors `b x` over the points `x` of `c`. -/
theorem fixedBasisOfPerm_apply_of_forall_eq_one (h : ∀ i, f (b i) = w i • b (π i))
    (c : {c : Quotient (SameCycle.setoid π) // ∏ᶠ (x) (_ : π.SameCycle c.out x), w x = 1})
    (hc : ∀ x, π.SameCycle c.1.out x → w x = 1) :
    (b.fixedBasisOfPerm π w h c : V) = ∑ᶠ (x) (_ : π.SameCycle c.1.out x), b x := by
  have hone : ∀ k, (w (cycleEnum π ⟨c.1, k⟩) : ℤ) = 1 := fun k ↦ by
    rw [hc _ (Quotient.mk_eq_iff_out.1 (mk_cycleEnum π ⟨c.1, k⟩)).symm, Units.val_one]
  rw [fixedBasisOfPerm, reindex_apply, positiveCycleEquiv_symm_apply,
    fixedBasisSignedFamily_apply, ← sum_cycleEnum]
  have : Fin.init (fun k ↦ (w (cycleEnum π ⟨c.1, k⟩) : ℤ)) = 1 := funext fun k ↦ hone _
  simp [this, Fin.partialProd, Pi.one_def, List.ofFn_const]

end Module.Basis
