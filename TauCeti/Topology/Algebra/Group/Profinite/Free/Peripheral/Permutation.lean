/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.Group.Profinite.Free.Automorphism
public import TauCeti.Topology.Algebra.Group.Profinite.Free.Peripheral.Basic

/-!
# Peripheral automorphisms up to a permutation of the peripheral classes

Let `F` be a pro-`p` group and `x : Fin r → F` a family, with peripheral tuple
`t = (x_0, …, x_{r-1}, z)`, where `z = (x_0 ⋯ x_{r-1})⁻¹` is the cusp. A continuous automorphism
`φ` of `F` is *peripheral for the permutation `σ` of `Fin (r + 1)` with exponent `u ∈ ℤ_pˣ`* when
it carries every `t_i` to a conjugate of the `p`-adic power `t_{σ i} ^ u`. For `σ = 1` this is
`TauCeti.Peripheral.IsPeripheralAut`. The automorphisms admitting such data form a subgroup
`peripheralPermAut`: if `φ` has data `(σ, u)` and `ψ` has data `(τ, v)`, then `φ * ψ` has data
`(σ * τ, u * v)` and `φ⁻¹` has data `(σ⁻¹, u⁻¹)`.

For the basis of a free pro-`p` group of rank `r ≥ 2` the data are determined by the
automorphism. In the abelianization `ℤ_p ^ r` the classes of the peripheral tuple are the
coordinate vectors `e_0, …, e_{r-1}` and `-(e_0 + ⋯ + e_{r-1})`, and when `r ≥ 2` no unit multiple
of one of them is a unit multiple of another. So the data define a homomorphism `permData` from
`peripheralPermAut` to `Equiv.Perm (Fin (r + 1)) × ℤ_pˣ`, whose kernel consists of the
automorphisms that are peripheral of exponent one. In rank one the data are not determined: the
peripheral tuple is `(x, x⁻¹)`, and the automorphism `x ↦ x ^ u` has both data `(1, u)` and
`(swap 0 1, -u)`.

Two automorphisms realise nontrivial permutations. In every rank the *rotation* `x_i ↦ t_{i+1}`
sends the cusp to `x_0`, so it permutes the peripheral tuple cyclically, on the nose. In rank two
the *swap* `x_0 ↦ x_1`, `x_1 ↦ x_0` sends the cusp `(x_0 x_1)⁻¹` to `(x_1 x_0)⁻¹ = x_0⁻¹ z x_0`,
so it is peripheral for the transposition of the first two classes, with exponent one.

## Main definitions

* `TauCeti.Peripheral.IsPeripheralPermAut`: a continuous automorphism carries each `t_i` to a
  conjugate of `t_{σ i} ^ u`.
* `TauCeti.Peripheral.peripheralPermAut`: the subgroup of continuous automorphisms that are
  peripheral for some permutation and some unit exponent.
* `TauCeti.Peripheral.permData`: for the basis of a free pro-`p` group of rank at least two, the
  homomorphism recording the permutation and the exponent.

## Main results

* `TauCeti.Peripheral.isPeripheralPermAut_iff`: the predicate on the basis elements and the cusp.
* `TauCeti.Peripheral.IsPeripheralPermAut.mul`, `TauCeti.Peripheral.IsPeripheralPermAut.inv`: the
  data of a composite and of an inverse.
* `TauCeti.Peripheral.IsPeripheralPermAut.unique`: in rank at least two the permutation and the
  exponent are determined by the automorphism.
* `TauCeti.Peripheral.permData_eq_iff`, `TauCeti.Peripheral.mem_ker_permData_iff`: `permData` is
  characterized by the predicate, and its kernel is the exponent-one peripheral part.
* `TauCeti.Peripheral.exists_isPeripheralPermAut_swap_rank_one`: the data are not determined in
  rank one.
* `TauCeti.Peripheral.exists_rotation`, `TauCeti.Peripheral.exists_rotation_two`: the rotation of
  the peripheral tuple, and its rank-two case `x_0 ↦ x_1 ↦ z ↦ x_0`.
* `TauCeti.Peripheral.exists_swap_two`: the rank-two swap.

## References

* Y. Ihara, "Braids, Galois groups, and some arithmetic functions", Proc. ICM Kyoto 1990,
  99–120, for automorphisms of free pro-`p` groups of rank two permuting the three peripheral
  conjugacy classes.
-/

public section

namespace TauCeti

namespace Peripheral

open Multiplicative

variable {p r : ℕ} [Fact p.Prime] {F : Type*} [Group F] [TopologicalSpace F]
  [IsTopologicalGroup F] [CompactSpace F] [TotallyDisconnectedSpace F]

section Predicate

/-- A continuous automorphism `φ` of a pro-`p` group is **peripheral for the permutation `σ` with
exponent `u`** for a family `x` when it carries every element `t_i` of the peripheral tuple
`x_0, …, x_{r-1}, cusp x` to a conjugate of the `p`-adic power `t_{σ i} ^ u`. -/
def IsPeripheralPermAut (hF : IsProP p F) (x : Fin r → F) (σ : Equiv.Perm (Fin (r + 1)))
    (u : ℤ_[p]ˣ) (φ : ContinuousAut F) : Prop :=
  ∀ i : Fin (r + 1), IsConj (hF.padicPow (peripheralTuple x (σ i)) u) (φ (peripheralTuple x i))

/-- An automorphism is peripheral for `σ` with exponent `u` exactly when it carries each `x_i`
to a conjugate of `t_{σ i} ^ u` and the cusp to a conjugate of `t_{σ r} ^ u`. -/
theorem isPeripheralPermAut_iff (hF : IsProP p F) (x : Fin r → F) (σ : Equiv.Perm (Fin (r + 1)))
    (u : ℤ_[p]ˣ) (φ : ContinuousAut F) :
    IsPeripheralPermAut hF x σ u φ ↔
      (∀ i, IsConj (hF.padicPow (peripheralTuple x (σ i.castSucc)) u) (φ (x i))) ∧
        IsConj (hF.padicPow (peripheralTuple x (σ (Fin.last r))) u) (φ (cusp x)) := by
  rw [IsPeripheralPermAut, Fin.forall_fin_succ']
  simp only [peripheralTuple_castSucc, peripheralTuple_last]

/-- For the trivial permutation, the predicate is peripherality of exponent `u`. -/
@[simp]
theorem isPeripheralPermAut_one_iff (hF : IsProP p F) (x : Fin r → F) (u : ℤ_[p]ˣ)
    (φ : ContinuousAut F) : IsPeripheralPermAut hF x 1 u φ ↔ IsPeripheralAut hF x u φ := by
  rw [isPeripheralAut_iff, isPeripheralPermAut_iff]
  simp only [Equiv.Perm.one_apply, peripheralTuple_castSucc, peripheralTuple_last]

/-- An automorphism permuting the peripheral tuple exactly, `t_i ↦ t_{σ i}`, is peripheral for
`σ` with exponent one. -/
theorem isPeripheralPermAut_of_apply_eq (hF : IsProP p F) {x : Fin r → F}
    {σ : Equiv.Perm (Fin (r + 1))} {φ : ContinuousAut F}
    (h : ∀ i, φ (peripheralTuple x i) = peripheralTuple x (σ i)) :
    IsPeripheralPermAut hF x σ 1 φ := fun i ↦ by
  rw [h, Units.val_one, hF.padicPow_one]

variable {hF : IsProP p F} {x : Fin r → F} {σ τ : Equiv.Perm (Fin (r + 1))} {u v : ℤ_[p]ˣ}
  {φ ψ : ContinuousAut F}

/-- Composition of permutation-peripheral automorphisms composes the permutations and multiplies
the exponents. -/
theorem IsPeripheralPermAut.mul (hφ : IsPeripheralPermAut hF x σ u φ)
    (hψ : IsPeripheralPermAut hF x τ v ψ) :
    IsPeripheralPermAut hF x (σ * τ) (u * v) (φ * ψ) := by
  intro i
  -- `ψ` carries `t_i` to a conjugate of `t_{τ i} ^ v`, and `φ` carries `t_{τ i} ^ v` to a
  -- conjugate of `(t_{σ (τ i)} ^ u) ^ v`.
  obtain ⟨g, hg⟩ := isConj_iff.mp (hφ (τ i))
  have hpow : IsConj (hF.padicPow (peripheralTuple x ((σ * τ) i)) ↑(u * v))
      (hF.padicPow (φ (peripheralTuple x (τ i))) v) := by
    refine isConj_iff.mpr ⟨g, ?_⟩
    rw [← hg, hF.conj_padicPow, ← hF.padicPow_mul, Units.val_mul, Equiv.Perm.mul_apply]
  have hmap := (φ : F →* F).map_isConj (hψ i)
  rw [hF.map_padicPow hF (φ : F →* F) φ.continuous] at hmap
  exact hpow.trans hmap

/-- The inverse of a permutation-peripheral automorphism has the inverse permutation and the
inverse exponent. -/
theorem IsPeripheralPermAut.inv (hφ : IsPeripheralPermAut hF x σ u φ) :
    IsPeripheralPermAut hF x σ⁻¹ u⁻¹ φ⁻¹ := by
  intro i
  -- `φ` carries `t_{σ⁻¹ i}` to a conjugate of `t_i ^ u`; apply `φ⁻¹` and take `u⁻¹`-th powers.
  have h := hφ (σ⁻¹ i)
  rw [← Equiv.Perm.mul_apply, mul_inv_cancel, Equiv.Perm.one_apply] at h
  have hmap := (φ.symm : F →* F).map_isConj h
  simp only [MonoidHom.coe_ofClass, ContinuousMulEquiv.symm_apply_apply] at hmap
  obtain ⟨g, hg⟩ := isConj_iff.mp hmap.symm
  refine isConj_iff.mpr ⟨g, ?_⟩
  rw [← hF.conj_padicPow, hg, ContinuousAut.inv_apply]
  simpa only [MonoidHom.coe_ofClass, hF.padicPow_padicPow_inv] using
    (hF.map_padicPow hF (φ.symm : F →* F) φ.symm.continuous
      (hF.padicPow (peripheralTuple x i) u) ↑u⁻¹).symm

end Predicate

section Subgroup

/-- The continuous automorphisms peripheral for `x` up to some permutation of the peripheral tuple,
with some common unit exponent. -/
def peripheralPermAut (hF : IsProP p F) (x : Fin r → F) : Subgroup (ContinuousAut F) where
  carrier := {φ | ∃ (σ : Equiv.Perm (Fin (r + 1))) (u : ℤ_[p]ˣ), IsPeripheralPermAut hF x σ u φ}
  one_mem' := ⟨1, 1, (isPeripheralPermAut_one_iff hF x 1 1).mpr (isPeripheralAut_one hF x)⟩
  mul_mem' := by
    rintro φ ψ ⟨σ, u, hφ⟩ ⟨τ, v, hψ⟩
    exact ⟨σ * τ, u * v, hφ.mul hψ⟩
  inv_mem' := by
    rintro φ ⟨σ, u, hφ⟩
    exact ⟨σ⁻¹, u⁻¹, hφ.inv⟩

/-- Membership in `peripheralPermAut` means admitting a permutation and a unit exponent. -/
@[simp]
theorem mem_peripheralPermAut_iff (hF : IsProP p F) (x : Fin r → F) (φ : ContinuousAut F) :
    φ ∈ peripheralPermAut hF x ↔
      ∃ (σ : Equiv.Perm (Fin (r + 1))) (u : ℤ_[p]ˣ), IsPeripheralPermAut hF x σ u φ :=
  Iff.rfl

end Subgroup

section Unique

variable {hF : IsProP p F} {e : F ≃ₜ* freeProP p (Fin r)}

/-- **Unit multiples of distinct peripheral classes differ in rank at least two.** If a unit
multiple of the exponent vector of `t_a` is a unit multiple of that of `t_b`, then `a = b` and
the units agree. -/
private theorem eq_and_eq_of_smul_eq_smul (hr : 2 ≤ r) {a b : Fin (r + 1)} {u u' : ℤ_[p]ˣ}
    (h : (u : ℤ_[p]) • Fin.lastCases (motive := fun _ ↦ Fin r → ℤ_[p]) (-1)
        (fun j ↦ Pi.single j 1) a =
      (u' : ℤ_[p]) • Fin.lastCases (motive := fun _ ↦ Fin r → ℤ_[p]) (-1)
        (fun j ↦ Pi.single j 1) b) :
    a = b ∧ u = u' := by
  obtain ⟨n, rfl⟩ : ∃ n, r = n + 2 := ⟨r - 2, by omega⟩
  induction a using Fin.lastCases with
  | last =>
    induction b using Fin.lastCases with
    | last =>
      have h0 := congr_fun h 0
      simp only [Fin.lastCases_last, Pi.smul_apply, Pi.neg_apply, Pi.one_apply, smul_eq_mul,
        mul_neg, mul_one, neg_inj] at h0
      exact ⟨rfl, Units.ext h0⟩
    | cast k =>
      obtain ⟨j, hj⟩ := exists_ne k
      have h0 := congr_fun h j
      simp [hj] at h0
  | cast j =>
    induction b using Fin.lastCases with
    | last =>
      obtain ⟨k, hk⟩ := exists_ne j
      have h0 := congr_fun h k
      simp [hk] at h0
    | cast k =>
      have h0 := congr_fun h j
      by_cases hjk : j = k
      · subst hjk
        simp only [Fin.lastCases_castSucc, Pi.smul_apply, Pi.single_eq_same, smul_eq_mul,
          mul_one] at h0
        exact ⟨rfl, Units.ext h0⟩
      · simp [hjk] at h0

/-- **The permutation and the exponent are determined in rank at least two.** For the basis of a
free pro-`p` group of rank `r ≥ 2`, an automorphism peripheral for `(σ, u)` and for `(σ', u')`
has `σ = σ'` and `u = u'`. -/
theorem IsPeripheralPermAut.unique (hr : 2 ≤ r) {σ σ' : Equiv.Perm (Fin (r + 1))}
    {u u' : ℤ_[p]ˣ} {φ : ContinuousAut F} (h : IsPeripheralPermAut hF (basis e) σ u φ)
    (h' : IsPeripheralPermAut hF (basis e) σ' u' φ) : σ = σ' ∧ u = u' := by
  have key (i : Fin (r + 1)) : σ i = σ' i ∧ u = u' := by
    -- `t_{σ i} ^ u` and `t_{σ' i} ^ u'` are conjugate, both being conjugate to `φ t_i`, so their
    -- exponent vectors in the abelianization `ℤ_p ^ r` agree.
    have hc := (h i).trans (h' i).symm
    let f : F →ₜ* Multiplicative (Fin r → ℤ_[p]) :=
      (freeProP.exponentSum p (Fin r)).comp (e : F →ₜ* freeProP p (Fin r))
    have hf := isConj_iff_eq.mp ((f : F →* Multiplicative (Fin r → ℤ_[p])).map_isConj hc)
    -- in `ℤ_p ^ r` the `p`-adic power by `l` is the scalar action of `l`
    rw [MonoidHom.coe_ofClass, hF.map_padicPow_pi, hF.map_padicPow_pi,
      ofAdd.injective.eq_iff] at hf
    simp only [f, ContinuousMonoidHom.comp_toFun, ContinuousMonoidHom.coe_coe,
      toAdd_exponentSum_peripheralTuple] at hf
    exact eq_and_eq_of_smul_eq_smul hr hf
  exact ⟨Equiv.ext fun i ↦ (key i).1, (key 0).2⟩

end Unique

section PermData

variable (hF : IsProP p F) (e : F ≃ₜ* freeProP p (Fin r)) (hr : 2 ≤ r)

/-- **The permutation and the exponent of a permutation-peripheral automorphism**, for the basis
of a free pro-`p` group of rank at least two, as a homomorphism. -/
noncomputable def permData :
    peripheralPermAut hF (basis e) →* Equiv.Perm (Fin (r + 1)) × ℤ_[p]ˣ where
  toFun φ := (φ.property.choose, φ.property.choose_spec.choose)
  map_one' := by
    have h := (1 : peripheralPermAut hF (basis e)).property.choose_spec.choose_spec
    exact Prod.ext_iff.mpr <| h.unique hr <|
      (isPeripheralPermAut_one_iff hF (basis e) 1 1).mpr (isPeripheralAut_one hF (basis e))
  map_mul' φ ψ := by
    have h := (φ * ψ).property.choose_spec.choose_spec
    exact Prod.ext_iff.mpr <| h.unique hr <|
      φ.property.choose_spec.choose_spec.mul ψ.property.choose_spec.choose_spec

/-- `permData` supplies a permutation and an exponent for its argument. -/
theorem isPeripheralPermAut_permData (φ : peripheralPermAut hF (basis e)) :
    IsPeripheralPermAut hF (basis e) (permData hF e hr φ).1 (permData hF e hr φ).2 φ :=
  φ.property.choose_spec.choose_spec

/-- `permData` of an automorphism is `(σ, u)` exactly when the automorphism is peripheral for
`σ` with exponent `u`. -/
@[simp]
theorem permData_eq_iff (φ : peripheralPermAut hF (basis e)) (σ : Equiv.Perm (Fin (r + 1)))
    (u : ℤ_[p]ˣ) : permData hF e hr φ = (σ, u) ↔ IsPeripheralPermAut hF (basis e) σ u φ := by
  refine ⟨fun h ↦ ?_, fun h ↦ Prod.ext_iff.mpr ((isPeripheralPermAut_permData hF e hr φ).unique
    hr h)⟩
  have hφ := isPeripheralPermAut_permData hF e hr φ
  rwa [h] at hφ

/-- The kernel of `permData` consists of the automorphisms that are peripheral of exponent one. -/
theorem mem_ker_permData_iff (φ : peripheralPermAut hF (basis e)) :
    φ ∈ (permData hF e hr).ker ↔ IsPeripheralAut hF (basis e) 1 φ := by
  rw [MonoidHom.mem_ker, Prod.one_eq_mk, permData_eq_iff, isPeripheralPermAut_one_iff]

end PermData

section Examples

/-- **The data are not determined in rank one.** In rank one the peripheral tuple is `(x, x⁻¹)`,
and an automorphism with `x ↦ x ^ u` is peripheral both for the trivial permutation with
exponent `u` and for the transposition with exponent `-u`. -/
theorem exists_isPeripheralPermAut_swap_rank_one (hF : IsProP p F)
    (e : F ≃ₜ* freeProP p (Fin 1)) (u : ℤ_[p]ˣ) :
    ∃ φ : ContinuousAut F, IsPeripheralPermAut hF (basis e) 1 u φ ∧
      IsPeripheralPermAut hF (basis e) (Equiv.swap 0 1) (-u) φ := by
  obtain ⟨φ, hφ⟩ := hF.exists_continuousAut_apply_eq_conj_padicPow_const e u 1
  have hx : φ (basis e 0) = hF.padicPow (basis e 0) u := by
    rw [basis_apply, hφ]
    simp
  have ht0 : peripheralTuple (basis e) 0 = basis e 0 := peripheralTuple_castSucc _ 0
  have hlast : peripheralTuple (basis e) 1 = cusp (basis e) := peripheralTuple_last _
  have ht1 : peripheralTuple (basis e) 1 = (basis e 0)⁻¹ := by
    rw [hlast, cusp_def]
    simp
  refine ⟨φ, fun i ↦ ?_, fun i ↦ ?_⟩
  all_goals
    match i with
    | 0 | 1 =>
      simp only [Equiv.Perm.one_apply, Equiv.swap_apply_left, Equiv.swap_apply_right, ht0, ht1,
        map_inv, hx, hF.inv_padicPow, hF.padicPow_neg, Units.val_neg, inv_inv]
      exact IsConj.refl _

/-- **The rotation.** In every rank some continuous automorphism sends `x_i` to `t_{i+1}`, the
next element of the peripheral tuple; it then sends the cusp to `x_0`, so it permutes the
peripheral tuple cyclically, `t_i ↦ t_{i+1}` with indices modulo `r + 1`, and it is peripheral for
this cyclic permutation with exponent one. -/
theorem exists_rotation (hF : IsProP p F) (e : F ≃ₜ* freeProP p (Fin r)) :
    ∃ φ : ContinuousAut F,
      (∀ i, φ (peripheralTuple (basis e) i) = peripheralTuple (basis e) (finRotate (r + 1) i)) ∧
      IsPeripheralPermAut hF (basis e) (finRotate (r + 1)) 1 φ := by
  obtain ⟨φ, hφ⟩ := freeProP.exists_continuousAut_of_topologicallyGenerates e
    (topologicalClosure_closure_range_peripheralTuple_comp_succ e)
  have hx : ⇑φ ∘ basis e = fun j ↦ peripheralTuple (basis e) j.succ :=
    funext fun j ↦ by rw [Function.comp_apply, basis_apply, hφ, Function.comp_apply]
  suffices h : ∀ i, φ (peripheralTuple (basis e) i) =
      peripheralTuple (basis e) (finRotate (r + 1) i) from
    ⟨φ, h, isPeripheralPermAut_of_apply_eq hF h⟩
  intro i
  induction i using Fin.lastCases with
  | last =>
    -- `x_1 ⋯ x_{r-1} · z = x_0⁻¹`, so `φ` carries `x_0 ⋯ x_{r-1}` to `x_0⁻¹`.
    have hprod := prod_ofFn_peripheralTuple (basis e)
    rw [List.ofFn_succ, List.prod_cons] at hprod
    rw [peripheralTuple_last, map_cusp, finRotate_last, cusp_def, hx]
    exact inv_eq_of_mul_eq_one_left hprod
  | cast j =>
    rw [peripheralTuple_castSucc, ← Function.comp_apply (f := φ), hx, finRotate_apply,
      Fin.coeSucc_eq_succ]

/-- **The rank-two rotation.** In rank two some continuous automorphism cycles the peripheral
tuple `x_0 ↦ x_1 ↦ z ↦ x_0`, where `z = (x_0 x_1)⁻¹` is the cusp, so it is peripheral for the
three-cycle `finRotate 3` with exponent one. -/
theorem exists_rotation_two (hF : IsProP p F) (e : F ≃ₜ* freeProP p (Fin 2)) :
    ∃ φ : ContinuousAut F, φ (basis e 0) = basis e 1 ∧ φ (basis e 1) = cusp (basis e) ∧
      φ (cusp (basis e)) = basis e 0 ∧ IsPeripheralPermAut hF (basis e) (finRotate 3) 1 φ := by
  obtain ⟨φ, h, hφ⟩ := exists_rotation hF e
  have ht0 : peripheralTuple (basis e) 0 = basis e 0 := peripheralTuple_castSucc _ 0
  have ht1 : peripheralTuple (basis e) 1 = basis e 1 := peripheralTuple_castSucc _ 1
  have ht2 : peripheralTuple (basis e) 2 = cusp (basis e) := peripheralTuple_last _
  refine ⟨φ, ?_, ?_, ?_, hφ⟩
  · simpa only [ht0, ht1, finRotate_apply, Fin.reduceAdd] using h 0
  · simpa only [ht1, ht2, finRotate_apply, Fin.reduceAdd] using h 1
  · simpa only [ht0, ht2, finRotate_apply, Fin.reduceAdd] using h 2

/-- **The rank-two swap.** In rank two some continuous automorphism exchanges the two basis
elements. It sends the cusp `z = (x_0 x_1)⁻¹` to `(x_1 x_0)⁻¹ = x_0⁻¹ * z * x_0`, so it is
peripheral for the transposition of the first two peripheral classes, with exponent one. -/
theorem exists_swap_two (hF : IsProP p F) (e : F ≃ₜ* freeProP p (Fin 2)) :
    ∃ φ : ContinuousAut F, φ (basis e 0) = basis e 1 ∧ φ (basis e 1) = basis e 0 ∧
      φ (cusp (basis e)) = (basis e 0)⁻¹ * cusp (basis e) * basis e 0 ∧
      IsPeripheralPermAut hF (basis e) (Equiv.swap 0 1) 1 φ := by
  let φ : ContinuousAut F := e.trans ((freeProP.congr (Equiv.swap 0 1)).trans e.symm)
  have h0 : φ (basis e 0) = basis e 1 := by
    simp [φ, basis_apply, freeProP.congr_of]
  have h1 : φ (basis e 1) = basis e 0 := by
    simp [φ, basis_apply, freeProP.congr_of]
  have hz : φ (cusp (basis e)) = (basis e 0)⁻¹ * cusp (basis e) * basis e 0 := by
    rw [map_cusp, cusp_def, cusp_def]
    simp only [List.ofFn_succ, List.ofFn_zero, Function.comp_apply, h0, h1, List.prod_cons,
      List.prod_nil, mul_one, Fin.succ_zero_eq_one]
    group
  have ht0 : peripheralTuple (basis e) 0 = basis e 0 := peripheralTuple_castSucc _ 0
  have ht1 : peripheralTuple (basis e) 1 = basis e 1 := peripheralTuple_castSucc _ 1
  have ht2 : peripheralTuple (basis e) 2 = cusp (basis e) := peripheralTuple_last _
  refine ⟨φ, h0, h1, hz, fun i ↦ ?_⟩
  rw [Units.val_one, hF.padicPow_one]
  match i with
  | 0 => rw [Equiv.swap_apply_left, ht0, ht1, h0]
  | 1 => rw [Equiv.swap_apply_right, ht0, ht1, h1]
  | 2 =>
    rw [Equiv.swap_apply_of_ne_of_ne (by decide) (by decide), ht2, hz]
    exact isConj_iff.mpr ⟨(basis e 0)⁻¹, by group⟩

end Examples

end Peripheral

end TauCeti
