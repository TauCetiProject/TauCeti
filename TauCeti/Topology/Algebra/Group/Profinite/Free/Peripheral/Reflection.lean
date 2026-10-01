/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Instances.ZMod
public import TauCeti.Topology.Algebra.Group.Heisenberg
public import TauCeti.Topology.Algebra.Group.Profinite.Free.Automorphism
public import TauCeti.Topology.Algebra.Group.Profinite.Free.Peripheral.Basic

/-!
# Peripheral automorphisms of exponent `-1`

Let `F` be a free pro-`p` group of rank `r` with basis `x_0, …, x_{r-1}` and cusp
`z = (x_0 ⋯ x_{r-1})⁻¹`, and write `P_i := x_0 ⋯ x_{i-1}` for the initial products of the basis
(Mathlib's `Fin.partialProd`). This file constructs explicit peripheral automorphisms of exponent
`-1`.

* **The reflection.** The continuous automorphism `reflect` with
  `x_i ↦ P_i * x_i⁻¹ * P_i⁻¹` inverts every initial product `P_i`, in particular the full product
  `x_0 ⋯ x_{r-1}`, so it sends the cusp to its inverse on the nose. It is therefore peripheral of
  exponent `-1` in every rank, with conjugator `P_i⁻¹` on `x_i` and `1` on the cusp, and it is an
  involution.
* **The rank-two inversion.** In rank two, every automorphism inverting both basis elements is
  also peripheral of exponent `-1`: it sends `z = (x_0 x_1)⁻¹` to
  `x_1 x_0 = x_0⁻¹ * z⁻¹ * x_0`, with conjugator `x_0` on the cusp.
* **Inversion fails in rank at least three.** For `r ≥ 3`, no automorphism inverting every basis
  element is peripheral, for any exponent. It sends `z` to `(x_0⁻¹ ⋯ x_{r-1}⁻¹)⁻¹`, and the
  continuous homomorphism to the Heisenberg group over `𝔽_p` with `x_0 ↦ a`, `x_1 ↦ b`,
  `x_2 ↦ (a b)⁻¹` and `x_i ↦ 1` for `i ≥ 3`, where `a` and `b` do not commute, kills `z` but
  not its image: the latter maps to `(a b)⁻¹ b a ≠ 1`.

Automorphisms with prescribed values on the basis exist by the automorphism criterion for
conjugated unit powers (`TauCeti.IsProP.exists_continuousAut_apply_eq_conj_padicPow_const`), and
they are unique since the basis generates `F` topologically.

## Main definitions

* `TauCeti.Peripheral.reflect`: the reflection `x_i ↦ P_i * x_i⁻¹ * P_i⁻¹`.

## Main results

* `TauCeti.Peripheral.reflect_basis`, `TauCeti.Peripheral.eq_reflect_iff`: the values of the
  reflection on the basis, which characterize it.
* `TauCeti.Peripheral.reflect_partialProd`, `TauCeti.Peripheral.reflect_cusp`: the reflection
  inverts every initial product of the basis and the cusp. Its simp normal form, after
  `TauCeti.Peripheral.map_cusp`, is `TauCeti.Peripheral.cusp_reflect_comp_basis`.
* `TauCeti.Peripheral.reflect_mul_reflect`: the reflection is an involution.
* `TauCeti.Peripheral.isPeripheralAut_reflect`: the reflection is peripheral of exponent `-1`.
* `TauCeti.Peripheral.isPeripheralAut_of_apply_basis_eq_inv_two`: in rank two such an
  automorphism is peripheral of exponent `-1`, with cusp conjugator `x_0`
  (`TauCeti.Peripheral.apply_cusp_of_apply_basis_eq_inv_two`).
* `TauCeti.Peripheral.exists_inversion_two`: the rank-two inversion exists, with these properties.
* `TauCeti.Peripheral.not_isPeripheralAut_of_apply_basis_eq_inv`: in rank at least three it is
  peripheral of no exponent.

## References

* Y. Ihara, "Braids, Galois groups, and some arithmetic functions", Proc. ICM Kyoto 1990,
  99–120, for peripheral automorphisms of free pro-`p` groups of rank two, among them the one
  attached to complex conjugation.
-/

public section

namespace TauCeti

namespace Peripheral

open Fin (partialProd)

variable {p r : ℕ} [Fact p.Prime] {F : Type*} [Group F] [TopologicalSpace F]
  [IsTopologicalGroup F] [CompactSpace F] [TotallyDisconnectedSpace F]

section Reflection

/-- **The reflection.** The continuous automorphism of `F` sending each basis element `x_i` to
`P_i * x_i⁻¹ * P_i⁻¹`, where `P_i = x_0 ⋯ x_{i-1}` is the initial product of the basis. It is
characterized by its values on the basis (`TauCeti.Peripheral.eq_reflect_iff`). -/
noncomputable def reflect (hF : IsProP p F) (e : F ≃ₜ* freeProP p (Fin r)) : ContinuousAut F :=
  (hF.exists_continuousAut_apply_eq_conj_padicPow_const e (-1)
    fun i ↦ (partialProd (basis e) i.castSucc)⁻¹).choose

/-- The reflection sends `x_i` to `P_i * x_i⁻¹ * P_i⁻¹`. -/
@[simp]
theorem reflect_basis (hF : IsProP p F) (e : F ≃ₜ* freeProP p (Fin r)) (i : Fin r) :
    reflect hF e (basis e i) =
      partialProd (basis e) i.castSucc * (basis e i)⁻¹ *
        (partialProd (basis e) i.castSucc)⁻¹ := by
  have h := (hF.exists_continuousAut_apply_eq_conj_padicPow_const e (-1)
    fun i ↦ (partialProd (basis e) i.castSucc)⁻¹).choose_spec i
  rw [← basis_apply] at h
  rw [reflect, h]
  simp

/-- A continuous automorphism of `F` is the reflection exactly when it sends every basis element
`x_i` to `P_i * x_i⁻¹ * P_i⁻¹`. -/
theorem eq_reflect_iff (hF : IsProP p F) (e : F ≃ₜ* freeProP p (Fin r)) (φ : ContinuousAut F) :
    φ = reflect hF e ↔ ∀ i, φ (basis e i) =
      partialProd (basis e) i.castSucc * (basis e i)⁻¹ * (partialProd (basis e) i.castSucc)⁻¹ :=
  ⟨fun h i ↦ h ▸ reflect_basis hF e i,
    fun h ↦ ContinuousMulEquiv.ext fun y ↦ congrArg (fun f : F →ₜ* F ↦ f y)
      (hom_ext_basis (f := (φ : F →ₜ* F)) (g := (reflect hF e : F →ₜ* F)) e fun i ↦
        (h i).trans (reflect_basis hF e i).symm)⟩

/-- The reflection inverts every initial product `P_j = x_0 ⋯ x_{j-1}` of the basis. -/
@[simp]
theorem reflect_partialProd (hF : IsProP p F) (e : F ≃ₜ* freeProP p (Fin r)) (j : Fin (r + 1)) :
    reflect hF e (partialProd (basis e) j) = (partialProd (basis e) j)⁻¹ := by
  -- The reflection carries `P_j` to the initial product of the reflected basis, whose entries
  -- `P_i * x_i⁻¹ * P_i⁻¹ = P_i * P_{i+1}⁻¹` telescope to `P_j⁻¹`.
  have hmap : reflect hF e (partialProd (basis e) j) =
      partialProd (fun i ↦ reflect hF e (basis e i)) j := by
    simp only [Fin.partialProd, map_list_prod, List.map_take, List.map_ofFn, Function.comp_def]
  have hval : (fun i ↦ reflect hF e (basis e i)) = fun i : Fin r ↦
      ((partialProd (basis e) i.castSucc)⁻¹)⁻¹ * (partialProd (basis e) i.succ)⁻¹ := by
    funext i
    rw [reflect_basis, Fin.partialProd_succ, inv_inv, mul_inv_rev, mul_assoc]
  have h := congr_fun (Fin.partialProd_left_inv fun j ↦ (partialProd (basis e) j)⁻¹) j
  rw [Fin.partialProd_zero, inv_one, one_smul] at h
  rw [hmap, hval, h]

/-- The reflection sends the cusp to its inverse. -/
theorem reflect_cusp (hF : IsProP p F) (e : F ≃ₜ* freeProP p (Fin r)) :
    reflect hF e (cusp (basis e)) = (cusp (basis e))⁻¹ := by
  have hlast : partialProd (basis e) (Fin.last r) = (List.ofFn (basis e)).prod := by
    rw [Fin.partialProd, Fin.val_last, List.take_of_length_le (by simp)]
  rw [cusp_def, map_inv, ← hlast, reflect_partialProd]

/-- The cusp of the reflected basis is the inverse of the cusp. This is the simp normal form of
`TauCeti.Peripheral.reflect_cusp`, whose left-hand side `TauCeti.Peripheral.map_cusp` rewrites. -/
@[simp]
theorem cusp_reflect_comp_basis (hF : IsProP p F) (e : F ≃ₜ* freeProP p (Fin r)) :
    cusp (reflect hF e ∘ basis e) = (cusp (basis e))⁻¹ := by
  rw [← map_cusp, reflect_cusp]

/-- **The reflection is an involution.** -/
@[simp]
theorem reflect_mul_reflect (hF : IsProP p F) (e : F ≃ₜ* freeProP p (Fin r)) :
    reflect hF e * reflect hF e = 1 :=
  ContinuousMulEquiv.ext fun y ↦ congrArg (fun f : F →ₜ* F ↦ f y)
    (hom_ext_basis (f := ((reflect hF e * reflect hF e : ContinuousAut F) : F →ₜ* F))
      (g := ((1 : ContinuousAut F) : F →ₜ* F)) e fun i ↦ by simp [mul_assoc])

/-- The reflection is its own inverse. -/
@[simp]
theorem inv_reflect (hF : IsProP p F) (e : F ≃ₜ* freeProP p (Fin r)) :
    (reflect hF e)⁻¹ = reflect hF e :=
  inv_eq_of_mul_eq_one_right (reflect_mul_reflect hF e)

/-- **The reflection is peripheral of exponent `-1`**, with conjugator `P_i⁻¹` on `x_i` and `1`
on the cusp. -/
theorem isPeripheralAut_reflect (hF : IsProP p F) (e : F ≃ₜ* freeProP p (Fin r)) :
    IsPeripheralAut hF (basis e) (-1) (reflect hF e) :=
  isPeripheralAut_of_apply_eq_conj hF (c := fun i ↦ (partialProd (basis e) i.castSucc)⁻¹)
    (d := 1) (fun i ↦ by simp) (by rw [reflect_cusp]; simp)

end Reflection

section Inversion

omit [Fact p.Prime] [IsTopologicalGroup F] [CompactSpace F] [TotallyDisconnectedSpace F] in
/-- In rank two, an automorphism inverting both basis elements sends the cusp
`z = (x_0 x_1)⁻¹` to `x_1 x_0 = x_0⁻¹ * z⁻¹ * x_0`. -/
theorem apply_cusp_of_apply_basis_eq_inv_two (e : F ≃ₜ* freeProP p (Fin 2))
    {φ : ContinuousAut F} (hφ : ∀ i, φ (basis e i) = (basis e i)⁻¹) :
    φ (cusp (basis e)) = (basis e 0)⁻¹ * (cusp (basis e))⁻¹ * basis e 0 := by
  rw [cusp_def, map_inv]
  simp [List.ofFn_succ, hφ]

/-- **The rank-two inversion is peripheral.** In rank two, an automorphism inverting both basis
elements is peripheral of exponent `-1`, with conjugator `1` on the basis and `x_0` on the
cusp. -/
theorem isPeripheralAut_of_apply_basis_eq_inv_two (hF : IsProP p F)
    (e : F ≃ₜ* freeProP p (Fin 2)) {φ : ContinuousAut F}
    (hφ : ∀ i, φ (basis e i) = (basis e i)⁻¹) :
    IsPeripheralAut hF (basis e) (-1) φ :=
  isPeripheralAut_of_apply_eq_conj hF (c := 1) (d := basis e 0) (fun i ↦ by simp [hφ])
    (by simp [apply_cusp_of_apply_basis_eq_inv_two e hφ])

/-- **The rank-two inversion.** In rank two, some continuous automorphism inverts both basis
elements. It sends the cusp `z = (x_0 x_1)⁻¹` to `x_0⁻¹ * z⁻¹ * x_0` and is peripheral of
exponent `-1`. -/
theorem exists_inversion_two (hF : IsProP p F) (e : F ≃ₜ* freeProP p (Fin 2)) :
    ∃ φ : ContinuousAut F, (∀ i, φ (basis e i) = (basis e i)⁻¹) ∧
      φ (cusp (basis e)) = (basis e 0)⁻¹ * (cusp (basis e))⁻¹ * basis e 0 ∧
      IsPeripheralAut hF (basis e) (-1) φ := by
  obtain ⟨φ, hφ⟩ := hF.exists_continuousAut_apply_eq_conj_padicPow_const e (-1) 1
  have hφ' : ∀ i, φ (basis e i) = (basis e i)⁻¹ := fun i ↦ by simpa [← basis_apply] using hφ i
  exact ⟨φ, hφ', apply_cusp_of_apply_basis_eq_inv_two e hφ',
    isPeripheralAut_of_apply_basis_eq_inv_two hF e hφ'⟩

/-- **Inversion is not peripheral in rank at least three.** For `r ≥ 3`, an automorphism
inverting every basis element is peripheral of no exponent: it sends the cusp to
`(x_0⁻¹ ⋯ x_{r-1}⁻¹)⁻¹`, which is not conjugate to any `p`-adic power of the cusp. -/
theorem not_isPeripheralAut_of_apply_basis_eq_inv {n : ℕ} (hF : IsProP p F)
    (e : F ≃ₜ* freeProP p (Fin (n + 3))) {φ : ContinuousAut F}
    (hφ : ∀ i, φ (basis e i) = (basis e i)⁻¹) (u : ℤ_[p]ˣ) :
    ¬ IsPeripheralAut hF (basis e) u φ := by
  intro hper
  -- Map `F` to the Heisenberg group over `𝔽_p`, sending `x_0, x_1, x_2` to `a`, `b`, `(a b)⁻¹`,
  -- where `a` and `b` do not commute, and the remaining basis elements to `1`.
  have hH : IsProP p (HeisenbergGroup (ZMod p)) := (HeisenbergGroup.isPGroup_zmod p).isProP
  let a : HeisenbergGroup (ZMod p) := ⟨1, 0, 0⟩
  let b : HeisenbergGroup (ZMod p) := ⟨0, 1, 0⟩
  let v : Fin (n + 3) → HeisenbergGroup (ZMod p) :=
    Fin.cons a (Fin.cons b (Fin.cons (a * b)⁻¹ 1))
  let f : F →ₜ* HeisenbergGroup (ZMod p) :=
    (freeProP.lift hH v).comp (e : F →ₜ* freeProP p (Fin (n + 3)))
  have hf : ∀ i, f (basis e i) = v i := fun i ↦ by
    simp [f, ContinuousMonoidHom.comp_toFun]
  have hfx : ⇑f ∘ basis e = v := funext hf
  have hfφx : ⇑f ∘ ⇑φ ∘ basis e = fun i ↦ (v i)⁻¹ := funext fun i ↦ by
    simp [hφ, hf]
  -- The cusp maps to `1`, so its `p`-adic powers do too, but its image under `φ` does not.
  have hcusp : f (cusp (basis e)) = 1 := by
    rw [map_cusp, hfx, cusp_def]
    simp [v, List.ofFn_succ]
  have hφcusp : f (φ (cusp (basis e))) ≠ 1 := by
    rw [map_cusp, map_cusp, hfφx, cusp_def, inv_ne_one]
    simp only [v, List.ofFn_succ, Fin.cons_zero, Fin.cons_succ, Pi.one_apply, inv_one,
      List.ofFn_const, List.prod_cons, List.prod_replicate, one_pow, mul_one]
    intro h
    have hz := congr_arg HeisenbergGroup.z h
    -- the `z`-coordinate of `a⁻¹ b⁻¹ (a b)` is `1`
    simp only [a, b, HeisenbergGroup.mul_x, HeisenbergGroup.mul_y, HeisenbergGroup.mul_z,
      HeisenbergGroup.inv_x, HeisenbergGroup.inv_y, HeisenbergGroup.inv_z,
      HeisenbergGroup.one_z] at hz
    ring_nf at hz
    exact one_ne_zero hz
  have hconj := (isPeripheralAut_iff hF (basis e) u φ).mp hper |>.2
  have hmap : IsConj (f (hF.padicPow (cusp (basis e)) u)) (f (φ (cusp (basis e)))) :=
    (f : F →* HeisenbergGroup (ZMod p)).map_isConj hconj
  have hpow : f (hF.padicPow (cusp (basis e)) u) = hH.padicPow (f (cusp (basis e))) u :=
    hF.map_padicPow hH (f : F →* HeisenbergGroup (ZMod p)) f.continuous _ _
  rw [hpow, hcusp, hH.one_padicPow, isConj_one_right] at hmap
  exact hφcusp hmap

end Inversion

end Peripheral

end TauCeti
