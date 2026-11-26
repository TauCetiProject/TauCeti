/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.SesquilinearForm.SignedHermitianSpace.Split
public import TauCeti.LinearAlgebra.SesquilinearForm.SignedHermitianSpace.WittDecomposition

/-!
# The Witt decomposition over the split quadratic algebra `F × F`

Let `F` be a field and `E = F × F` with the involution `σ (a, b) = (b, a)`. A finite free
`ε`-hermitian space `(V, h)` over `E` is isometric to `Eⁿ` with the form
`h a b = ∑ σ (a i) * (ε, 1) * b i`
(`TauCeti.SignedHermitianSpace.exists_linearEquiv_form_eq_sum_split`).
Writing `a = (a₁, a₂)` with `a₁, a₂ ∈ Fⁿ`, this form is `(ε a₂ ⬝ b₁, a₁ ⬝ b₂)`: the two halves
`Fⁿ × 0` and `0 × Fⁿ` are totally isotropic and put in duality by the dot product. This file
proves the **Witt decomposition over `F × F`**: the Witt index of a space of rank `n` is
`⌊n / 2⌋`, the space is `H^⌊n/2⌋ ⊥ A` for every space `A` of rank `n % 2`, and a space is
anisotropic exactly when its rank is at most one. The anisotropic part is thus `0` or the line
`⟨(ε, 1)⟩`, which for `ε = 1` is the standard line `⟨1⟩`.

## Main statements

* `TauCeti.SignedHermitianSpace.wittIndex_split`: the Witt index is `⌊n / 2⌋`.
* `TauCeti.SignedHermitianSpace.equivalent_hyperbolic_prod_split`: the Witt decomposition.
* `TauCeti.SignedHermitianSpace.anisotropic_split_iff`: anisotropic spaces have rank at most one.

## References

* W. Scharlau, *Quadratic and Hermitian Forms*, Grundlehren der mathematischen Wissenschaften
  270, Springer (1985), Chapter 7.
-/

public section

open Module

namespace TauCeti

namespace SignedHermitianSpace

variable {F : Type*} [Field F] {σ : F × F →+* F × F} {ε : ℤˣ}

/-! ### The model space `(F × F)ⁿ` -/

section Model

variable {n : ℕ}

/-- The first components `a₁` of `a : (F × F)ⁿ`. -/
private def fst₁ : (Fin n → F × F) →ₗ[F] Fin n → F :=
  LinearMap.pi fun i ↦ LinearMap.fst F F F ∘ₗ LinearMap.proj i

/-- The second components `a₂` of `a : (F × F)ⁿ`. -/
private def snd₁ : (Fin n → F × F) →ₗ[F] Fin n → F :=
  LinearMap.pi fun i ↦ LinearMap.snd F F F ∘ₗ LinearMap.proj i

/-- The vector `(u, 0)` of `(F × F)ⁿ`. -/
private def inl₁ : (Fin n → F) →ₗ[F] Fin n → F × F :=
  LinearMap.pi fun i ↦ LinearMap.inl F F F ∘ₗ LinearMap.proj i

/-- The vector `(0, u)` of `(F × F)ⁿ`. -/
private def inr₁ : (Fin n → F) →ₗ[F] Fin n → F × F :=
  LinearMap.pi fun i ↦ LinearMap.inr F F F ∘ₗ LinearMap.proj i

private theorem inl₁_apply (u : Fin n → F) (i : Fin n) : inl₁ u i = (u i, 0) := rfl
private theorem inr₁_apply (u : Fin n → F) (i : Fin n) : inr₁ u i = (0, u i) := rfl
private theorem fst₁_apply (a : Fin n → F × F) (i : Fin n) : fst₁ a i = (a i).1 := rfl
private theorem snd₁_apply (a : Fin n → F × F) (i : Fin n) : snd₁ a i = (a i).2 := rfl

private theorem smul_eq_inl₁ (a : Fin n → F × F) : ((1, 0) : F × F) • a = inl₁ (fst₁ a) :=
  funext fun i ↦ Prod.ext (by simp [inl₁_apply, fst₁_apply]) (by simp [inl₁_apply])

private theorem smul_eq_inr₁ (a : Fin n → F × F) : ((0, 1) : F × F) • a = inr₁ (snd₁ a) :=
  funext fun i ↦ Prod.ext (by simp [inr₁_apply]) (by simp [inr₁_apply, snd₁_apply])

/-- The form of the model: `∑ σ (a i) * (ε, 1) * b i = (ε a₂ ⬝ b₁, a₁ ⬝ b₂)`. -/
private theorem sum_split_eq (hσ : ∀ x, σ x = x.swap) (a b : Fin n → F × F) :
    ∑ i, σ (a i) * (((ε : ℤ) : F), 1) * b i =
      (((ε : ℤ) : F) * (snd₁ a ⬝ᵥ fst₁ b), fst₁ a ⬝ᵥ snd₁ b) := by
  ext <;> simp only [hσ, Prod.fst_sum, Prod.snd_sum, Prod.fst_mul, Prod.snd_mul, Prod.fst_swap,
    Prod.snd_swap, dotProduct, fst₁_apply, snd₁_apply, Finset.mul_sum] <;>
    exact Finset.sum_congr rfl fun _ _ ↦ by ring

end Model

/-! ### Witt decomposition -/

variable {V : Type*} [AddCommGroup V] [Module (F × F) V] [Module.Free (F × F) V]
  [Module.Finite (F × F) V] (H : SignedHermitianSpace (F × F) V σ ε)

/-- The Gram-diagonal line `⟨(ε, 1)⟩` has `σ (ε, 1) = ε • (ε, 1)` for the swap `σ`. -/
private theorem apply_split_unit (hσ : ∀ x, σ x = x.swap) :
    σ (((ε : ℤ) : F), 1) = ε • (((ε : ℤ) : F), (1 : F)) := by
  rcases Int.units_eq_one_or ε with rfl | rfl <;> ext <;> simp [hσ]

/-- A space over `F × F` of rank at most one is anisotropic. -/
private theorem anisotropic_of_finrank_le_one (hσ : ∀ x, σ x = x.swap)
    (h : finrank (F × F) V ≤ 1) : H.Anisotropic := by
  obtain ⟨T, hT⟩ := H.exists_linearEquiv_form_eq_sum_split hσ rfl
  rw [anisotropic_iff]
  intro x hiso
  obtain ⟨hxx, hx⟩ : _ ∧ _ := hiso
  obtain ⟨a, rfl⟩ := T.surjective x
  have hsub : Subsingleton (Fin (finrank (F × F) V)) := Fin.subsingleton_iff_le_one.2 h
  rw [hT, sum_split_eq hσ] at hxx
  have h₂ : fst₁ a ⬝ᵥ snd₁ a = 0 := congrArg Prod.snd hxx
  -- Either every first component vanishes, or the (single) second component does.
  by_cases h₁ : ∀ i, (a i).1 = 0
  · refine one_ne_zero (congrArg Prod.fst (hx ((1, 0) : F × F) ?_))
    rw [← map_smul, smul_eq_inl₁]
    simp [show fst₁ a = 0 from funext h₁]
  · push Not at h₁
    obtain ⟨i₀, hi₀⟩ := h₁
    have hb : snd₁ a = 0 := funext fun i ↦ by
      obtain rfl := Subsingleton.elim i i₀
      have : (a i).1 * (a i).2 = 0 := by
        simpa [dotProduct, Fintype.sum_subsingleton _ i, fst₁_apply, snd₁_apply] using h₂
      simpa [snd₁_apply, hi₀] using this
    refine one_ne_zero (congrArg Prod.snd (hx ((0, 1) : F × F) ?_))
    rw [← map_smul, smul_eq_inr₁, hb]
    simp

omit [Module.Free (F × F) V] [Module.Finite (F × F) V] in
/-- The swap is an involution. -/
private theorem ringHomInvPair_split (hσ : ∀ x, σ x = x.swap) : RingHomInvPair σ σ :=
  ⟨RingHom.ext fun x ↦ by simp [hσ], RingHom.ext fun x ↦ by simp [hσ]⟩

/-- **Witt decomposition over `F × F`.** Let `σ` be the involution `(a, b) ↦ (b, a)` of
`F × F`. A finite free `ε`-hermitian space `V` of rank `n` over `F × F` is isometric to
`H^⌊n/2⌋ ⊥ A` for every space `A` of rank `n % 2`. -/
theorem equivalent_hyperbolic_prod_split [RingHomInvPair σ σ] (hσ : ∀ x, σ x = x.swap)
    {V' : Type*} [AddCommGroup V'] [Module (F × F) V'] [Module.Free (F × F) V']
    [Module.Finite (F × F) V'] (H' : SignedHermitianSpace (F × F) V' σ ε)
    (h : finrank (F × F) V' = finrank (F × F) V % 2) :
    Equivalent H ((hyperbolic (F × F) σ ε (Fin (finrank (F × F) V / 2))).prod H') :=
  H.equivalent_of_finrank_eq_split hσ _ (by simp [finrank_prod, h]; lia)

/-- **The Witt index over `F × F`.** Let `σ` be the involution `(a, b) ↦ (b, a)` of `F × F`. A
finite free `ε`-hermitian space of rank `n` over `F × F` has Witt index `⌊n / 2⌋`. -/
theorem wittIndex_split (hσ : ∀ x, σ x = x.swap) :
    H.wittIndex = finrank (F × F) V / 2 := by
  have := ringHomInvPair_split hσ
  refine le_antisymm (by have := H.two_mul_wittIndex_le_finrank; lia) ?_
  -- Compare with `H^⌊n/2⌋ ⊥ ⟨(ε, 1)⟩^(n % 2)`.
  let A := diagonal σ ε (fun _ : Fin (finrank (F × F) V % 2) ↦ (((ε : ℤ) : F), (1 : F)))
    (fun _ ↦ apply_split_unit hσ) fun _ ↦ IsUnit.mem_nonZeroDivisors
      (Prod.isUnit_iff.2 ⟨ε.isUnit.map (Int.castRingHom F), isUnit_one⟩)
  rw [(H.equivalent_hyperbolic_prod_split hσ A (by simp)).wittIndex_eq]
  simpa using card_le_wittIndex_hyperbolic_prod (K := F × F) (σ := σ) (ε := ε)
    (Fin (finrank (F × F) V / 2)) A

/-- **Anisotropic spaces over `F × F`.** Let `σ` be the involution `(a, b) ↦ (b, a)` of
`F × F`. A finite free `ε`-hermitian space over `F × F` is anisotropic exactly when its rank is at
most one. -/
theorem anisotropic_split_iff (hσ : ∀ x, σ x = x.swap) :
    H.Anisotropic ↔ finrank (F × F) V ≤ 1 := by
  have := ringHomInvPair_split hσ
  refine ⟨fun h ↦ ?_, H.anisotropic_of_finrank_le_one hσ⟩
  by_contra hV
  obtain ⟨x, y, hxy⟩ := H.exists_isHyperbolicFrame_wittIndex
  have := H.wittIndex_split hσ
  exact (anisotropic_iff.1 h) _ (hxy.isIsotropic_left ⟨0, by lia⟩)

end SignedHermitianSpace

end TauCeti
