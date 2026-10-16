/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.SpectralObject.Abutment
public import TauCeti.Algebra.Homology.SpectralObject.SpectralSequenceMap
public import TauCeti.Algebra.Homology.SpectralSequence.Comparison

/-!
# The comparison theorem for spectral objects indexed by `EInt`

A morphism `φ : X ⟶ Y` of spectral objects induces maps on the objects `opZ^n(f, g)`
(`CategoryTheory.Abelian.SpectralObject.opcyclesMapOfHom`), compatible with Mathlib's short exact
sequences `0 ⟶ opZ^n(f₁, f₂ ≫ f₃) ⟶ opZ^n(f₁ ≫ f₂, f₃) ⟶ E^n(f₁, f₂, f₃) ⟶ 0`
(`isIso_opcyclesMapOfHom_of_isIso`). For `EInt`, these are the extensions
`0 ⟶ F_q H^n ⟶ F_{q+1} H^n ⟶ E∞ ⟶ 0` of the filtration of the abutment `H^n(⊥ ≤ ⊤)`; by induction on
`q` and the three-lemma, an isomorphism on `E∞` gives one on the abutment for finite filtrations; by
stabilization, so does an isomorphism on some page.

## Main results

* `CategoryTheory.Abelian.SpectralObject.isIso_hom_app_abutment`: the comparison theorem on `E∞`.
* `CategoryTheory.Abelian.SpectralObject.isIso_hom_app_abutment_of_isIso_page`: on a page.
-/

public section

namespace CategoryTheory.Abelian.SpectralObject

open ComposableArrows Limits

variable {C : Type*} [Category* C] [Abelian C] {X Y : SpectralObject C EInt} (φ : X ⟶ Y)

/-- **The comparison theorem on `E∞`.** Let `φ : X ⟶ Y` be a morphism of spectral objects
indexed by `EInt` and `a ≤ b` such that `H^n(⊥ ≤ a)` and `H^n(b ≤ ⊤)` vanish for `X` and `Y`
(the filtrations of the abutments in degree `n` start at `a` and end at `b`). If `φ` is an
isomorphism on `EInfty q n` for `a ≤ q < b`, then it is an isomorphism on the abutment
`H^n(⊥ ≤ ⊤)`. -/
theorem isIso_hom_app_abutment {a b n : ℤ} (hab : a ≤ b)
    (hXa : IsZero ((X.H n).obj (mk₁ (homOfLE (bot_le : (⊥ : EInt) ≤ a)))))
    (hYa : IsZero ((Y.H n).obj (mk₁ (homOfLE (bot_le : (⊥ : EInt) ≤ a)))))
    (hXb : IsZero ((X.H n).obj (mk₁ (homOfLE (le_top : (b : EInt) ≤ ⊤)))))
    (hYb : IsZero ((Y.H n).obj (mk₁ (homOfLE (le_top : (b : EInt) ≤ ⊤)))))
    (hE : ∀ q : ℤ, a ≤ q → q < b → IsIso (EMap φ (homOfLE (bot_le : (⊥ : EInt) ≤ q))
      (homOfLE (coe_le_coe_add_one q)) (homOfLE (le_top : ((q + 1 : ℤ) : EInt) ≤ ⊤))
      (n - 1) n (n + 1) (sub_add_cancel n 1) rfl)) :
    IsIso ((φ.hom n).app (mk₁ (homOfLE (bot_le : (⊥ : EInt) ≤ ⊤)))) := by
  have key : ∀ q, a ≤ q → q ≤ b → IsIso (opcyclesMapOfHom φ
      (homOfLE (bot_le : (⊥ : EInt) ≤ q)) (homOfLE (le_top : (q : EInt) ≤ ⊤)) n) := by
    intro q hq
    induction q, hq using Int.leInduction with
    | base =>
      intro _
      exact ⟨0, (X.isZero_abutmentFiltration hXa).eq_of_src _ _,
        (Y.isZero_abutmentFiltration hYa).eq_of_src _ _⟩
    | succ q hq ih =>
      intro hqb
      have := ih (by lia)
      have := hE q hq (by lia)
      exact isIso_opcyclesMapOfHom_of_isIso φ (homOfLE (bot_le : (⊥ : EInt) ≤ q))
        (homOfLE (coe_le_coe_add_one q)) (homOfLE (le_top : ((q + 1 : ℤ) : EInt) ≤ ⊤))
        (homOfLE bot_le) (Subsingleton.elim _ _) (n - 1) n (n + 1) (sub_add_cancel n 1) rfl
        (homOfLE le_top) (Subsingleton.elim _ _)
  have := key b hab le_rfl
  have hX := X.isIso_abutmentFiltrationι hXb
  have hY := Y.isIso_abutmentFiltrationι hYb
  rw [abutmentFiltrationι_eq] at hX hY
  rw [(IsIso.eq_inv_comp _).mpr
    (opcyclesMapOfHom_fromOpcycles φ (homOfLE (bot_le : (⊥ : EInt) ≤ b))
      (homOfLE (le_top : (b : EInt) ≤ ⊤)) n (homOfLE bot_le) (Subsingleton.elim _ _)).symm]
  infer_instance

/-- The morphisms of pages `spectralSequencePageXMap` correspond to the maps `EMap` on the limit
objects `EInfty` through the isomorphisms `spectralSequencePageXIsoEInfty`. -/
lemma spectralSequencePageXMap_comp_pageXIsoEInfty_hom (r : ℤ) (hr : 2 ≤ r) (pq : ℤ × ℤ)
    (n : ℤ) (hn : n = pq.1 + pq.2)
    (hX₀ : IsZero ((X.H (n + 1)).obj
      (mk₁ (homOfLE (bot_le : (⊥ : EInt) ≤ ((pq.2 - r + 2 : ℤ) : EInt))))))
    (hX₃ : IsZero ((X.H (n - 1)).obj
      (mk₁ (homOfLE (le_top : ((pq.2 + r - 1 : ℤ) : EInt) ≤ ⊤)))))
    (hY₀ : IsZero ((Y.H (n + 1)).obj
      (mk₁ (homOfLE (bot_le : (⊥ : EInt) ≤ ((pq.2 - r + 2 : ℤ) : EInt))))))
    (hY₃ : IsZero ((Y.H (n - 1)).obj
      (mk₁ (homOfLE (le_top : ((pq.2 + r - 1 : ℤ) : EInt) ≤ ⊤))))) :
    spectralSequencePageXMap coreE₂Cohomological φ r hr pq ≫
        (Y.spectralSequencePageXIsoEInfty r hr pq n hn hY₀ hY₃).hom =
      (X.spectralSequencePageXIsoEInfty r hr pq n hn hX₀ hX₃).hom ≫
        EMap φ (homOfLE (bot_le : (⊥ : EInt) ≤ pq.2)) (homOfLE (coe_le_coe_add_one pq.2))
          (homOfLE (le_top : ((pq.2 + 1 : ℤ) : EInt) ≤ ⊤)) (n - 1) n (n + 1)
          (sub_add_cancel n 1) rfl := by
  have h₀₁ : ((pq.2 - r + 2 : ℤ) : EInt) ≤ pq.2 := by simp; lia
  have h₂₃ : ((pq.2 + 1 : ℤ) : EInt) ≤ ((pq.2 + r - 1 : ℤ) : EInt) := by simp; lia
  have := X.isIso_mapFourδ₁Toδ₀' ⊥ _ _ _ _ bot_le h₀₁ (coe_le_coe_add_one pq.2) h₂₃ (n - 1) n
    (n + 1) hX₀ (sub_add_cancel n 1) rfl
  -- the indices of the recipe `coreE₂Cohomological`, as hypotheses with their syntactic types
  have e₀ : ((pq.2 - r + 2 : ℤ) : EInt) = coreE₂Cohomological.i₀ r pq hr := rfl
  have e₁ : ((pq.2 : ℤ) : EInt) = coreE₂Cohomological.i₁ pq := rfl
  have e₂ : ((pq.2 + 1 : ℤ) : EInt) = coreE₂Cohomological.i₂ pq := rfl
  have e₃ : ((pq.2 + r - 1 : ℤ) : EInt) = coreE₂Cohomological.i₃ r pq hr := rfl
  rw [← cancel_epi (X.mapFourδ₁Toδ₀' ⊥ _ _ _ _ bot_le h₀₁ (coe_le_coe_add_one pq.2) h₂₃ (n - 1) n
      (n + 1) (sub_add_cancel n 1) rfl ≫
    (X.spectralSequencePageXIso coreE₂Cohomological r hr pq _ _ _ _ e₀ e₁ e₂ e₃ (n - 1) n (n + 1)
      hn (sub_add_cancel n 1) rfl).inv),
    spectralSequencePageXMap_eq coreE₂Cohomological φ r hr pq _ _ _ _ e₀ e₁ e₂ e₃ (n - 1) n
      (n + 1) hn (sub_add_cancel n 1) rfl]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [map_EMap_assoc, Y.mapFourδ₁Toδ₀'_comp_spectralSequencePageXIsoEInfty_hom r hr pq n hn hY₀ hY₃
      h₀₁ h₂₃, X.mapFourδ₁Toδ₀'_comp_spectralSequencePageXIsoEInfty_hom_assoc r hr pq n hn hX₀ hX₃
      h₀₁ h₂₃]
  exact (map_EMap ..).symm

/-- **The comparison theorem.** Let `φ : X ⟶ Y` be a morphism of spectral objects indexed by
`EInt` and `a ≤ b` such that `H^m(⊥ ≤ i)` vanishes for `i ≤ a` and `m ∈ {n, n + 1}`, and
`H^m(i ≤ ⊤)` vanishes for `i ≥ b` and `m ∈ {n - 1, n}`, for `X` and `Y`. If the induced morphism of
spectral sequences is an isomorphism on every object of some page `r ≥ 2`, then `φ` is an
isomorphism on the abutments
`H^n(⊥ ≤ ⊤)`. -/
theorem isIso_hom_app_abutment_of_isIso_page {a b : ℤ} (hab : a ≤ b) (n : ℤ)
    (hXa : ∀ m i : ℤ, n ≤ m → m ≤ n + 1 → i ≤ a →
      IsZero ((X.H m).obj (mk₁ (homOfLE (bot_le : (⊥ : EInt) ≤ i)))))
    (hYa : ∀ m i : ℤ, n ≤ m → m ≤ n + 1 → i ≤ a →
      IsZero ((Y.H m).obj (mk₁ (homOfLE (bot_le : (⊥ : EInt) ≤ i)))))
    (hXb : ∀ m i : ℤ, n - 1 ≤ m → m ≤ n → b ≤ i →
      IsZero ((X.H m).obj (mk₁ (homOfLE (le_top : (i : EInt) ≤ ⊤)))))
    (hYb : ∀ m i : ℤ, n - 1 ≤ m → m ≤ n → b ≤ i →
      IsZero ((Y.H m).obj (mk₁ (homOfLE (le_top : (i : EInt) ≤ ⊤)))))
    (r : ℤ) (hr : 2 ≤ r)
    (h : ∀ pq, IsIso (((spectralSequenceMap coreE₂Cohomological φ).hom r hr).f pq)) :
    IsIso ((φ.hom n).app (mk₁ (homOfLE (bot_le : (⊥ : EInt) ≤ ⊤)))) := by
  refine isIso_hom_app_abutment φ hab (hXa n a le_rfl (by lia) le_rfl)
    (hYa n a le_rfl (by lia) le_rfl) (hXb n b (by lia) le_rfl le_rfl)
    (hYb n b (by lia) le_rfl le_rfl) (fun q haq hqb => ?_)
  have hr' : r ≤ max r (b - a + 1) := le_max_left _ _
  have h' := SpectralSequence.Hom.isIso_hom_f_of_le _ r hr h _ hr' (n - q, q)
  simp only [spectralSequenceMap_hom, spectralSequencePageMap_f] at h'
  have hn : n = (n - q, q).1 + (n - q, q).2 := by simp
  have e := spectralSequencePageXMap_comp_pageXIsoEInfty_hom φ _ (hr.trans hr') (n - q, q) n hn
    (hXa _ _ (by lia) le_rfl (by simp only; lia)) (hXb _ _ le_rfl (by lia) (by simp only; lia))
    (hYa _ _ (by lia) le_rfl (by simp only; lia)) (hYb _ _ le_rfl (by lia) (by simp only; lia))
  rw [← Iso.inv_comp_eq] at e
  rw [← e]
  infer_instance

end CategoryTheory.Abelian.SpectralObject
