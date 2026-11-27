/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Multilinear.Polarization
public import TauCeti.Topology.Algebra.Module.Alternating.Wedge.Pow.Basic

/-!
# Wedge products of families of real alternating forms

For a family `α : Fin m → E [⋀^Fin k]→L[ℝ] ℝ` of real alternating forms of degree `k`, the wedge
product `ContinuousAlternatingMap.wedgeProd α = α₀ ∧ α₁ ∧ ⋯ ∧ α_{m-1}` is a form of degree
`k * m`, for the real wedge `ContinuousAlternatingMap.pairedWedge` along multiplication. On a
constant family it is the wedge power `ContinuousAlternatingMap.wedgePow`.

The product is multilinear in the family (`ContinuousAlternatingMap.wedgeProdMultilinear`), and,
when `k` is even, symmetric: forms of even degree commute, so permuting the family does not change
the product (`ContinuousAlternatingMap.wedgeProd_comp_perm`). Polarization then writes the product
as an alternating sum of wedge powers of partial sums of the family:

`m! (α₀ ∧ ⋯ ∧ α_{m-1}) = ∑_{S ⊆ Fin m} (-1)^{#S} (∑_{i ∉ S} αᵢ) ^ m`

(`ContinuousAlternatingMap.factorial_smul_wedgeProd`). For two-forms this reduces mixed wedge
products, such as `α₁ ∧ ⋯ ∧ α_k ∧ ω ^ (n - k)` in complex Hessian equations, to wedge powers.

## Main definitions

* `ContinuousAlternatingMap.wedgeProd α`: the wedge product of a family of real alternating forms.
* `ContinuousAlternatingMap.wedgeProdMultilinear`: the wedge product as a multilinear map of the
  family.

## Main results

* `ContinuousAlternatingMap.wedgeProd_const`: on a constant family the product is a wedge power.
* `ContinuousAlternatingMap.wedgeProd_comp_perm`: for forms of even degree the product is
  invariant under permutations of the family.
* `ContinuousAlternatingMap.factorial_smul_wedgeProd`: the polarization formula above.
-/

public section

noncomputable section

open Equiv Finset

open scoped Finset

namespace ContinuousAlternatingMap

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] {k : ℕ}

/-- The wedge product `α₀ ∧ α₁ ∧ ⋯ ∧ α_{m-1}` of a family of `m` real alternating forms of degree
`k`, a form of degree `k * m`. The empty product is the constant `0`-form `1`, and the product of
a family of `m + 1` forms is the product of the first `m` wedged with the last. -/
def wedgeProd : {m : ℕ} → (Fin m → E [⋀^Fin k]→L[ℝ] ℝ) → E [⋀^Fin (k * m)]→L[ℝ] ℝ
  | 0, _ => constOfIsEmpty ℝ E (Fin 0) 1
  | _ + 1, α => pairedWedge (ContinuousLinearMap.mul ℝ ℝ) (ContinuousLinearMap.mul ℝ ℝ).continuous₂
      (wedgeProd fun i => α i.castSucc) (α (Fin.last _))

/-- The empty wedge product is the constant `0`-form `1`. -/
@[simp]
theorem wedgeProd_zero_apply (α : Fin 0 → E [⋀^Fin k]→L[ℝ] ℝ) (v : Fin 0 → E) :
    DFunLike.coe (F := E [⋀^Fin 0]→L[ℝ] ℝ) (wedgeProd α) v = 1 := (rfl)

/-- The wedge product of `m + 1` forms is the product of the first `m` wedged with the last. -/
theorem wedgeProd_succ {m : ℕ} (α : Fin (m + 1) → E [⋀^Fin k]→L[ℝ] ℝ) :
    wedgeProd α = pairedWedge (ContinuousLinearMap.mul ℝ ℝ)
      (ContinuousLinearMap.mul ℝ ℝ).continuous₂ (wedgeProd fun i => α i.castSucc)
        (α (Fin.last m)) := (rfl)

/-- On a constant family the wedge product is the wedge power. -/
@[simp]
theorem wedgeProd_const (φ : E [⋀^Fin k]→L[ℝ] ℝ) (m : ℕ) :
    wedgeProd (fun _ : Fin m => φ) = wedgePow φ m := by
  induction m with
  | zero => ext v; exact (wedgeProd_zero_apply _ v).trans (wedgePow_zero_apply φ v).symm
  | succ m ih => rw [wedgeProd_succ, wedgePow_succ, ih]

/-- Updating a family at `j.castSucc` and restricting it along `Fin.castSucc` updates the
restriction at `j`. -/
private theorem update_castSucc_comp_castSucc {m : ℕ} (α : Fin (m + 1) → E [⋀^Fin k]→L[ℝ] ℝ)
    (j : Fin m) (z : E [⋀^Fin k]→L[ℝ] ℝ) :
    (fun i : Fin m => Function.update α j.castSucc z i.castSucc) =
      Function.update (fun i => α i.castSucc) j z :=
  Function.update_comp_eq_of_injective α (Fin.castSucc_injective m) j z

/-- The wedge product is additive in each factor. -/
theorem wedgeProd_update_add {m : ℕ} (α : Fin m → E [⋀^Fin k]→L[ℝ] ℝ) (i : Fin m)
    (x y : E [⋀^Fin k]→L[ℝ] ℝ) :
    wedgeProd (Function.update α i (x + y)) =
      wedgeProd (Function.update α i x) + wedgeProd (Function.update α i y) := by
  induction m with
  | zero => exact i.elim0
  | succ m ih =>
    induction i using Fin.lastCases with
    | last =>
      simp only [wedgeProd_succ, Function.update_self,
        Function.update_of_ne (Fin.castSucc_ne_last _), pairedWedge_add_right]
    | cast j =>
      simp only [wedgeProd_succ, update_castSucc_comp_castSucc, ih,
        Function.update_of_ne (Fin.castSucc_ne_last j).symm, pairedWedge_add_left]

/-- The wedge product is homogeneous in each factor. -/
theorem wedgeProd_update_smul {m : ℕ} (α : Fin m → E [⋀^Fin k]→L[ℝ] ℝ) (i : Fin m) (c : ℝ)
    (x : E [⋀^Fin k]→L[ℝ] ℝ) :
    wedgeProd (Function.update α i (c • x)) = c • wedgeProd (Function.update α i x) := by
  induction m with
  | zero => exact i.elim0
  | succ m ih =>
    induction i using Fin.lastCases with
    | last =>
      simp only [wedgeProd_succ, Function.update_self,
        Function.update_of_ne (Fin.castSucc_ne_last _), pairedWedge_smul_right]
    | cast j =>
      simp only [wedgeProd_succ, update_castSucc_comp_castSucc, ih,
        Function.update_of_ne (Fin.castSucc_ne_last j).symm, pairedWedge_smul_left]

/-- The wedge product of a family of `m` real alternating forms of degree `k`, as a multilinear map
of the family. -/
def wedgeProdMultilinear (E : Type*) [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
    (k m : ℕ) :
    MultilinearMap (RingHom.id ℝ) (fun _ : Fin m => E [⋀^Fin k]→L[ℝ] ℝ)
      (E [⋀^Fin (k * m)]→L[ℝ] ℝ) where
  toFun := wedgeProd
  map_update_add' α i x y := by
    convert wedgeProd_update_add α i x y
  map_update_smul' α i c x := by
    convert wedgeProd_update_smul α i c x

@[simp]
theorem wedgeProdMultilinear_apply {m : ℕ} (α : Fin m → E [⋀^Fin k]→L[ℝ] ℝ) :
    wedgeProdMultilinear E k m α = wedgeProd α := (rfl)

/-! ### Symmetry for forms of even degree -/

/-- For forms of even degree, the wedge product of a family of `m + 2` forms is unchanged by
exchanging the last two. -/
private theorem wedgeProd_comp_swap_last (hk : Even k) {m : ℕ}
    (α : Fin (m + 2) → E [⋀^Fin k]→L[ℝ] ℝ) :
    wedgeProd (α ∘ swap (Fin.last m).castSucc (Fin.last (m + 1))) = wedgeProd α := by
  set s := swap (Fin.last m).castSucc (Fin.last (m + 1))
  have hs (i : Fin m) : s i.castSucc.castSucc = i.castSucc.castSucc :=
    swap_apply_of_ne_of_ne (fun h => (Fin.castSucc_ne_last i) (Fin.castSucc_injective _ h))
      (Fin.castSucc_ne_last _)
  have hcomm : pairedWedge (ContinuousLinearMap.mul ℝ ℝ) (ContinuousLinearMap.mul ℝ ℝ).continuous₂
      (α (Fin.last (m + 1))) (α (Fin.last m).castSucc) =
      pairedWedge (ContinuousLinearMap.mul ℝ ℝ) (ContinuousLinearMap.mul ℝ ℝ).continuous₂
        (α (Fin.last m).castSucc) (α (Fin.last (m + 1))) := by
    ext v
    rw [pairedWedge_comm_of_even _ (fun a b => mul_comm a b) (hk.mul_right k), Fin.cast_refl,
      Function.comp_id]
  ext v
  simp only [wedgeProd_succ, Function.comp_apply, hs]
  rw [pairedWedge_mul_assoc, pairedWedge_mul_assoc]
  simp only [s, swap_apply_left, swap_apply_right]
  rw [hcomm]

/-- For forms of even degree, the wedge product is unchanged by exchanging two adjacent factors. -/
private theorem wedgeProd_comp_swap_castSucc_succ (hk : Even k) :
    ∀ {m : ℕ} (i : Fin m) (α : Fin (m + 1) → E [⋀^Fin k]→L[ℝ] ℝ),
      wedgeProd (α ∘ swap i.castSucc i.succ) = wedgeProd α
  | 0, i, _ => i.elim0
  | m + 1, i, α => by
    induction i using Fin.lastCases with
    | last => exact wedgeProd_comp_swap_last hk α
    | cast j =>
      set s := swap j.castSucc.castSucc j.castSucc.succ
      have hlast : s (Fin.last (m + 1)) = Fin.last (m + 1) :=
        swap_apply_of_ne_of_ne (Fin.castSucc_ne_last _).symm
          (by rw [Fin.succ_castSucc]; exact (Fin.castSucc_ne_last _).symm)
      have hcs (i : Fin (m + 1)) : s i.castSucc = (swap j.castSucc j.succ i).castSucc := by
        simp only [s]
        rw [Fin.succ_castSucc]
        exact (Fin.castSucc_injective _).swap_apply j.castSucc j.succ i
      rw [wedgeProd_succ, wedgeProd_succ]
      simp only [Function.comp_apply, hlast, hcs]
      congr 1
      exact wedgeProd_comp_swap_castSucc_succ hk j (fun i => α i.castSucc)

/-- **Symmetry of the wedge product of forms of even degree.** Permuting a family of forms of even
degree does not change their wedge product. -/
theorem wedgeProd_comp_perm (hk : Even k) {m : ℕ} (α : Fin m → E [⋀^Fin k]→L[ℝ] ℝ)
    (σ : Perm (Fin m)) : wedgeProd (α ∘ σ) = wedgeProd α := by
  cases m with
  | zero => rfl
  | succ m =>
    have hσ : σ ∈ Submonoid.closure (Set.range fun i : Fin m => swap i.castSucc i.succ) := by
      rw [Perm.mclosure_swap_castSucc_succ]; exact Submonoid.mem_top σ
    induction hσ using Submonoid.closure_induction generalizing α with
    | mem τ hτ =>
      obtain ⟨i, rfl⟩ := hτ
      exact wedgeProd_comp_swap_castSucc_succ hk i α
    | one => rfl
    | mul τ ρ _ _ hτ hρ =>
      rw [Perm.coe_mul, ← Function.comp_assoc, hρ, hτ]

/-- **Polarization of the wedge product.** For a family of `m` forms of even degree,
`m! (α₀ ∧ ⋯ ∧ α_{m-1}) = ∑_{S ⊆ Fin m} (-1)^{#S} (∑_{i ∉ S} αᵢ) ^ m`. -/
theorem factorial_smul_wedgeProd (hk : Even k) {m : ℕ} (α : Fin m → E [⋀^Fin k]→L[ℝ] ℝ) :
    (m.factorial : ℝ) • wedgeProd α =
      ∑ S : Finset (Fin m), (-1 : ℝ) ^ #S • wedgePow (∑ i ∈ Sᶜ, α i) m := by
  have h := (wedgeProdMultilinear E k m).sum_neg_one_pow_card_smul_apply_sum_compl α
  simp only [wedgeProdMultilinear_apply, wedgeProd_const] at h
  rw [h]
  simp only [show ∀ σ : Perm (Fin m), wedgeProd (fun i => α (σ i)) = wedgeProd α from
    fun σ => wedgeProd_comp_perm hk α σ, Finset.sum_const, Finset.card_univ, Fintype.card_perm,
    Fintype.card_fin, Nat.cast_smul_eq_nsmul]

end ContinuousAlternatingMap
