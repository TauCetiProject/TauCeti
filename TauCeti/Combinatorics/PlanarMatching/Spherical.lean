/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Monoidal.Pivotal.Spherical
public import TauCeti.Combinatorics.PlanarMatching.Pivotal
import all TauCeti.Combinatorics.PlanarMatching.Glue
import all TauCeti.Combinatorics.PlanarMatching.Associativity
import all TauCeti.Combinatorics.PlanarMatching.Duality
import TauCeti.Data.Fin.Basic
import TauCeti.GroupTheory.Perm.OrbitCount.Basic
import TauCeti.CategoryTheory.Monoidal.Free.SelfDuality

/-!
# Spherical structure and quantum dimensions of the Temperley–Lieb diagram category

Closing an endomorphism diagram `f : n → n` on the left (bending its bottom up and top down to the
left) and on the right (bending to the right) produce the same empty diagram with the same number
of closed circles (`TauCeti.TLDiagram.leftClosure_eq_rightClosure`). On the underlying `2n`-point
planar matching, the two closures differ by a half-turn rotation (`PlanarMatching.rotate (n + n) ^
n`), and the circle count is invariant under this half-turn because twice the middle-gluing circle
count equals `orbitCount (x.1.val * Fin.revPerm)` while the half-turn commutes with `Fin.revPerm`.

This makes `TauCeti.TLDiagCat` a spherical pivotal category (`SphericalCategory TLDiagCat`) in
which the quantum dimension of `TLDiagCat.of n` is the `n`-th power of the closed circle
(`TauCeti.TLDiagCat.quantumDim_eq_circle_pow`).

## Main definitions

* `SphericalCategory TauCeti.TLDiagCat`: the spherical structure on `TLDiagCat`.

## Main results

* `TauCeti.TLDiagram.leftClosure_eq_rightClosure`: left and right diagrammatic closures of any
  endomorphism `f : TLDiagram n n` coincide.
* `TauCeti.TLDiagCat.quantumDim_eq_circle_pow`: `quantumDim (TLDiagCat.of n) =
  ((End.of TLDiagCat.circle) ^ n).asHom`.

## References

* J. Chen, *The Temperley–Lieb categories and skein modules*, arXiv:1502.06845, §2.
-/

public section

open CategoryTheory MonoidalCategory Equiv

namespace TauCeti

/-! ### Orbit count of `x * Fin.revPerm` and half-turn invariance -/

namespace PlanarMatching

section SphericalHelpers

private theorem orbitCount_mul_revPerm_eq_two_mul :
    ∀ (n : ℕ) (x : PlanarMatching (n + n)),
      orbitCount (x.val.val * Fin.revPerm) = 2 * glueCircles 0 n (pv x)
  | 0, x => by
    have h1 : x.val.val * Fin.revPerm = (1 : Perm (Fin 0)) := Subsingleton.elim _ _
    rw [h1, orbitCount_one, Nat.card_eq_fintype_card, Fintype.card_fin]
    rfl
  | n + 1, x => by
    let hdim : (n + 1) + (n + 1) = n + n + 2 := by omega
    let x' : PlanarMatching (n + n + 2) := cast hdim x
    let a : Fin (n + n + 1) := ⟨n, by omega⟩
    let y : PlanarMatching (n + n) := x'.contract a
    have ih := orbitCount_mul_revPerm_eq_two_mul n y
    have hcast : orbitCount (x.val.val * Fin.revPerm) = orbitCount (x'.val.val * Fin.revPerm) := by
      have hconj :
          (finCongr hdim).permCongr (x.val.val * Fin.revPerm) = x'.val.val * Fin.revPerm := by
        ext i
        simp only [Equiv.permCongr_apply, Perm.mul_apply, x', coe_cast_apply,
          PerfectMatching.congr_val, Fin.revPerm_apply]
        have hrev : ((finCongr hdim).symm i).rev = (finCongr hdim).symm i.rev := by
          apply Fin.ext
          simp only [Fin.val_rev, finCongr_symm, finCongr_apply, Fin.val_cast, hdim]
        rw [hrev]
      rw [← hconj, Equiv.orbitCount_permCongr]
    rw [hcast]
    -- Peel off the innermost contraction at `(A, B) = (n, n + 1)` and apply IH to `y`.
    have hgc : glueCircles 0 (n + 1) (pv x) = glueCircles 0 n (pv y) + circleInd n (pv x') := by
      simp only [glueCircles, Nat.zero_add]
      rw [← pv_cast_eq hdim x]
      -- Match the recursive call on `n = (a : ℕ)` with `pv_contract_eq`.
      change glueCircles 0 n (contractFn a (pv x')) + circleInd n (pv x') = _
      rw [pv_contract_eq]
    rw [hgc, Nat.mul_add, ← ih]
    set σ : Perm (Fin (n + n + 2)) := x'.val.val
    set τ : Perm (Fin (n + n + 2)) := Fin.revPerm
    set σ' : Perm (Fin (n + n)) := y.val.val
    set τ' : Perm (Fin (n + n)) := Fin.revPerm
    set A : Fin (n + n + 2) := a.castSucc
    set B : Fin (n + n + 2) := a.succ
    have hττ : ∀ z, τ (τ z) = z := fun z => Fin.rev_rev z
    have hτA : τ A = B := Fin.ext (by simp only [τ, A, B, a, Fin.revPerm_apply, Fin.val_rev,
      Fin.val_castSucc, Fin.val_succ]; omega)
    have hτB : τ B = A := Fin.ext (by simp only [τ, A, B, a, Fin.revPerm_apply, Fin.val_rev,
      Fin.val_castSucc, Fin.val_succ]; omega)
    have hskip_τ : ∀ i : Fin (n + n), skip a (τ' i) = τ (skip a i) := fun i => by
      apply Fin.ext
      have hi : (i : ℕ) < n + n := i.isLt
      simp only [coe_skip, τ, τ', a, Fin.revPerm_apply, Fin.val_rev]
      split_ifs <;> omega
    -- Lift `σ' * τ'` on `Fin (2n)` to `π` on `Fin (2n + 2)` fixing `A` and `B`, adding 2 orbits.
    let e₁ := (finSuccEquiv' a).symm
    let π₁ : Perm (Fin (n + n + 1)) := e₁.permCongr (Equiv.optionCongr (σ' * τ'))
    let e₂ := (finSuccEquiv' a.castSucc).symm
    let π : Perm (Fin (n + n + 2)) := e₂.permCongr (Equiv.optionCongr π₁)
    have hπ₁_succ : ∀ i, π₁ (a.succAbove i) = a.succAbove ((σ' * τ') i) := fun i => by
      simp [π₁, e₁, finSuccEquiv'_succAbove]
    have hπ₁_a : π₁ a = a := by
      simp [π₁, e₁]
    have hπ_succ : ∀ j, π (a.castSucc.succAbove j) = a.castSucc.succAbove (π₁ j) := fun j => by
      simp [π, e₂, finSuccEquiv'_succAbove]
    have hπ_skip : ∀ i, π (skip a i) = skip a ((σ' * τ') i) := fun i => by
      -- Unfold `skip a` into the two `succAbove` embeddings.
      change π (a.castSucc.succAbove (a.succAbove i)) = _
      rw [hπ_succ, hπ₁_succ]; rfl
    have hπ_A : π A = A := by
      simp [π, e₂, A]
    have hB : B = a.castSucc.succAbove a := by
      apply Fin.ext; simp [B, Fin.succAbove]
    have hπ_B : π B = B := by rw [hB, hπ_succ, hπ₁_a]
    have horb₁ : orbitCount (σ' * τ') + 1 = orbitCount π₁ :=
      orbitCount_add_one_eq_of_semiconj (f := a.succAbove) (p := a)
        (Fin.succAbove_right_injective) (Fin.succAbove_ne a)
        (fun z hz => Fin.exists_succAbove_eq hz) (fun i => (hπ₁_succ i).symm)
    have horb₂ : orbitCount π₁ + 1 = orbitCount π :=
      orbitCount_add_one_eq_of_semiconj (f := a.castSucc.succAbove) (p := A)
        (Fin.succAbove_right_injective) (Fin.succAbove_ne a.castSucc)
        (fun z hz => Fin.exists_succAbove_eq hz) (fun j => (hπ_succ j).symm)
    have hsurj_skip : ∀ z : Fin (n + n + 2), z ≠ A → z ≠ B → ∃ i, skip a i = z :=
      fun z hzA hzB => by
      obtain ⟨j, rfl⟩ := Fin.exists_succAbove_eq hzA
      have hja : j ≠ a := fun h => hzB (by subst h; exact hB.symm)
      obtain ⟨i, rfl⟩ := Fin.exists_succAbove_eq hja
      exact ⟨i, rfl⟩
    have hπ_val : ∀ i, π (skip a i) =
        if σ (τ (skip a i)) = A then σ B
        else if σ (τ (skip a i)) = B then σ A
        else σ (τ (skip a i)) := fun i => by
      rw [hπ_skip, Perm.mul_apply, ← hskip_τ]
      exact succAbove_succAbove_contract_val x' a (τ' i)
    have hci : circleInd n (pv x') = if σ A = B then 1 else 0 := by
      unfold circleInd
      rw [pv_of_lt x' (by omega : n < n + n + 2)]
      have hiff : ((x'.val.val ⟨n, by omega⟩ : Fin (n + n + 2)) : ℕ) = n + 1 ↔ σ A = B := by
        rw [Fin.ext_iff]; rfl
      simp only [hiff]
    rw [hci]
    -- Case 1: `(A, B)` is an arc of `σ`, so `σ * τ = π` and both sides increase by 2.
    -- Case 2: `σ A ≠ B`, so `σ * τ = (π * swap p A) * swap q B` merges two fixed points.
    by_cases hAB : σ A = B
    · rw [ite_eq_left hAB]
      have hBA : σ B = A := by rw [← hAB, x'.val.apply_apply]
      have heq : σ * τ = π := by
        ext z
        by_cases hzA : z = A
        · rw [hzA, Perm.mul_apply, hτA, hBA, hπ_A]
        by_cases hzB : z = B
        · rw [hzB, Perm.mul_apply, hτB, hAB, hπ_B]
        obtain ⟨i, rfl⟩ := hsurj_skip z hzA hzB
        rw [hπ_val, Perm.mul_apply]
        have h1 : σ (τ (skip a i)) ≠ A := fun h => by
          have h' : τ (skip a i) = B := x'.val.val.injective (h.trans hBA.symm)
          exact skip_ne_castSucc a i (Fin.revPerm.injective (h'.trans hτA.symm))
        have h2 : σ (τ (skip a i)) ≠ B := fun h => by
          have h' : τ (skip a i) = A := x'.val.val.injective (h.trans hAB.symm)
          exact skip_ne_succ a i (Fin.revPerm.injective (h'.trans hτB.symm))
        rw [ite_eq_right h1, ite_eq_right h2]
      rw [heq]; omega
    · rw [ite_eq_right hAB]
      have hBA : σ B ≠ A := fun h => hAB (by rw [← h, x'.val.apply_apply])
      have huA : σ A ≠ A := x'.val.apply_ne A
      have hvB : σ B ≠ B := x'.val.apply_ne B
      have hAB_ne : A ≠ B := by simp [A, B, Fin.ext_iff]
      have huv : σ A ≠ σ B := fun h => hAB_ne (σ.injective h)
      set p := τ (σ A)
      set q := τ (σ B)
      have hpA : p ≠ A := fun h => hAB (by have h' := congrArg τ h; rwa [hττ, hτA] at h')
      have hpB : p ≠ B := fun h => huA (by have h' := congrArg τ h; rwa [hττ, hτB] at h')
      have hqA : q ≠ A := fun h => hvB (by have h' := congrArg τ h; rwa [hττ, hτA] at h')
      have hqB : q ≠ B := fun h => hBA (by have h' := congrArg τ h; rwa [hττ, hτB] at h')
      have hpq : p ≠ q := fun h => huv (τ.injective h)
      have hπp : π p = σ B := by
        obtain ⟨i, hi⟩ := hsurj_skip p hpA hpB
        rw [← hi, hπ_val, hi, show τ p = σ A from hττ (σ A), x'.val.apply_apply,
          ite_eq_left rfl]
      have hπq : π q = σ A := by
        obtain ⟨i, hi⟩ := hsurj_skip q hqA hqB
        rw [← hi, hπ_val, hi, show τ q = σ B from hττ (σ B), x'.val.apply_apply,
          ite_eq_right hAB_ne.symm, ite_eq_left rfl]
      have hprod : σ * τ = (π * swap p A) * swap q B := by
        ext z
        simp only [Perm.mul_apply]
        by_cases hzA : z = A
        · rw [hzA, hτA, swap_apply_of_ne_of_ne hqA.symm hAB_ne, swap_apply_right, hπp]
        by_cases hzB : z = B
        · rw [hzB, hτB, swap_apply_right, swap_apply_of_ne_of_ne hpq.symm hqA, hπq]
        by_cases hzp : z = p
        · rw [hzp, show τ p = σ A from hττ (σ A), x'.val.apply_apply,
            swap_apply_of_ne_of_ne hpq hpB, swap_apply_left, hπ_A]
        by_cases hzq : z = q
        · rw [hzq, show τ q = σ B from hττ (σ B), x'.val.apply_apply,
            swap_apply_left, swap_apply_of_ne_of_ne hpB.symm hAB_ne.symm, hπ_B]
        obtain ⟨i, rfl⟩ := hsurj_skip z hzA hzB
        rw [swap_apply_of_ne_of_ne hzq hzB, swap_apply_of_ne_of_ne hzp hzA, hπ_val]
        have h1 : σ (τ (skip a i)) ≠ A := fun h => hzp (by
          rw [show p = τ (σ A) from rfl, ← h, x'.val.apply_apply, hττ])
        have h2 : σ (τ (skip a i)) ≠ B := fun h => hzq (by
          rw [show q = τ (σ B) from rfl, ← h, x'.val.apply_apply, hττ])
        rw [ite_eq_right h1, ite_eq_right h2]
      have h1 := orbitCount_mul_swap_add_one (τ := π) hπ_A hpA
      have hπ1_B : (π * swap p A) B = B := by
        rw [Perm.mul_apply, swap_apply_of_ne_of_ne hpB.symm hAB_ne.symm, hπ_B]
      have h2 := orbitCount_mul_swap_add_one (τ := π * swap p A) hπ1_B hqB
      rw [hprod]
      omega

/-- Rotating a `2n`-point planar matching by half a turn (`n` steps) does not change the number
of circles closed when gluing its two halves together. -/
private theorem glueCircles_rotate_pow_half (n : ℕ) (x : PlanarMatching (n + n)) :
    glueCircles 0 n (pv ((rotate (n + n) ^ n) x)) = glueCircles 0 n (pv x) := by
  have hcomm : (finRotate (n + n) ^ n : Perm (Fin (n + n))) * Fin.revPerm =
      Fin.revPerm * (finRotate (n + n) ^ n : Perm (Fin (n + n))) := by
    ext i
    simp only [Perm.mul_apply, Fin.revPerm_apply, Fin.coe_finRotate_pow, Fin.val_rev]
    by_cases h0 : n = 0
    · subst h0; exact i.elim0
    · have hi : (i : ℕ) < n + n := i.isLt
      have h1 : (n + n - (i + 1) + n) % (n + n) =
          if (i : ℕ) < n then n - 1 - i else 3 * n - 1 - i := by
        split_ifs with h
        · rw [show n + n - (i + 1) + n = (n - 1 - i) + (n + n) by omega, Nat.add_mod_right,
            Nat.mod_eq_of_lt (by omega)]
        · rw [Nat.mod_eq_of_lt (by omega)]; omega
      have h2 : (i + n) % (n + n) = if (i : ℕ) < n then i + n else i - n := by
        split_ifs with h
        · exact Nat.mod_eq_of_lt (by omega)
        · rw [show (i : ℕ) + n = (i - n) + (n + n) by omega, Nat.add_mod_right,
            Nat.mod_eq_of_lt (by omega)]
      rw [h1, h2]
      split_ifs <;> omega
  have h1 := orbitCount_mul_revPerm_eq_two_mul n ((rotate (n + n) ^ n) x)
  have h2 := orbitCount_mul_revPerm_eq_two_mul n x
  set r : Perm (Fin (n + n)) := finRotate (n + n) ^ n
  have hconj : ((rotate (n + n) ^ n) x).val.val * Fin.revPerm =
      r * (x.val.val * Fin.revPerm) * r⁻¹ := by
    rw [coe_rotate_pow_apply, PerfectMatching.congr_val]
    have hconj_val : r.permCongr x.val.val = r * x.val.val * r⁻¹ := rfl
    rw [hconj_val]
    have hcomm' : r⁻¹ * Fin.revPerm = Fin.revPerm * r⁻¹ := by
      calc r⁻¹ * Fin.revPerm = r⁻¹ * (Fin.revPerm * r) * r⁻¹ := by group
        _ = r⁻¹ * (r * Fin.revPerm) * r⁻¹ := by rw [← hcomm]
        _ = Fin.revPerm * r⁻¹ := by group
    calc r * x.val.val * r⁻¹ * Fin.revPerm
        = r * x.val.val * (r⁻¹ * Fin.revPerm) := by group
      _ = r * x.val.val * (Fin.revPerm * r⁻¹) := by rw [hcomm']
      _ = r * (x.val.val * Fin.revPerm) * r⁻¹ := by group
  rw [hconj, orbitCount_conj] at h1
  omega

end SphericalHelpers

end PlanarMatching

namespace TLDiagram

section Closure

variable {n : ℕ}

open PlanarMatching in
/-- **Sphericality at the diagram level**: closing an endomorphism diagram `f : n → n` on the left
and on the right produce the same empty diagram with the same number of circles. -/
theorem leftClosure_eq_rightClosure (f : TLDiagram n n) :
    (nestedCup n).comp (((id n).tensor f).comp (nestedCap n)) =
      (nestedCup n).comp ((f.tensor (id n)).comp (nestedCap n)) := by
  rw [← comp_assoc, ← comp_assoc, nestedCup_comp_id_tensor, nestedCup_comp_tensor_id]
  ext : 1
  · exact PlanarMatching.ext fun i => Fin.elim0 i
  · have hL := glueFn_append_nested (n := n) (p := n)
      ((PlanarMatching.rotate (n + n) ^ n) f.matching)
    have hR := glueFn_append_nested (n := n) (p := n) f.matching
    have hcastL : pv ((PlanarMatching.cast (Nat.zero_add (n + n)).symm
        ((PlanarMatching.rotate (n + n) ^ n) f.matching)).append (nested n)) =
        pv (((PlanarMatching.rotate (n + n) ^ n) f.matching).append (nested n)) := by
      rw [pv_append_eq, pv_append_eq, pv_cast_eq, Nat.zero_add]
    have hcastR : pv ((PlanarMatching.cast (Nat.zero_add (n + n)).symm
        f.matching).append (nested n)) =
        pv (f.matching.append (nested n)) := by
      rw [pv_append_eq, pv_append_eq, pv_cast_eq, Nat.zero_add]
    have haddL := glueFn_add 0 n n (pv (((PlanarMatching.rotate (n + n) ^ n) f.matching).append
      (nested n)))
    have haddR := glueFn_add 0 n n (pv (f.matching.append (nested n)))
    simp only [circles_comp, circles_nestedCap, matching_nestedCap, glueMiddleCircles_eq,
      Nat.zero_add, hcastL, hcastR, haddL.2, haddR.2, hL.1, hL.2, hR.1, hR.2,
      glueCircles_rotate_pow_half]


end Closure

end TLDiagram

namespace TLDiagCat

/-- `TLDiagCat` is a **spherical category**: the left and right traces of every endomorphism agree,
by `TauCeti.TLDiagram.leftClosure_eq_rightClosure`. -/
instance : SphericalCategory TLDiagCat where
  leftTrace_eq_rightTrace {X} f := by
    rw [leftTrace_eq_pivotalIsoApp, rightTrace_eq_pivotalIsoApp, pivotalIsoApp_eq_refl]
    -- `Xᘁ = X` definitionally.
    change η_ X X ≫ X ◁ 𝟙 X ≫ X ◁ f ≫ ε_ X X =
      η_ X X ≫ f ▷ X ≫ 𝟙 X ▷ X ≫ ε_ X X
    rw [coevaluation_eq_nestedCup, evaluation_eq_nestedCap,
      MonoidalCategory.whiskerLeft_id, MonoidalCategory.id_whiskerRight,
      Category.id_comp, Category.id_comp]
    refine hom_ext ?_
    rw [diagram_comp, diagram_comp, diagram_comp, diagram_comp, diagram_whiskerLeft,
      diagram_whiskerRight, diagram_nestedCup, diagram_nestedCap]
    exact TLDiagram.leftClosure_eq_rightClosure f.diagram

/-- The quantum dimension of `of n` in `TLDiagCat` is the `n`-th power of the closed circle. -/
@[simp]
theorem quantumDim_eq_circle_pow (n : ℕ) :
    quantumDim (of n) = ((End.of circle) ^ n).asHom := by
  rw [← trace_id, trace_eq_leftTrace, leftTrace_eq_pivotalIsoApp, pivotalIsoApp_eq_refl]
  -- `(of n)ᘁ = of n` definitionally.
  change η_ (of n) (of n) ≫ of n ◁ 𝟙 (of n) ≫ of n ◁ 𝟙 (of n) ≫ ε_ (of n) (of n) =
    ((End.of circle) ^ n).asHom
  rw [coevaluation_eq_nestedCup, evaluation_eq_nestedCap,
    MonoidalCategory.whiskerLeft_id, Category.id_comp, Category.id_comp,
    nestedCup_comp_nestedCap]

end TLDiagCat

/-- The universal lift out of `FreeSelfDualityCat` sends the generating self-duality to
`(TLDiagCat.of 1, TLDiagCat.cup, TLDiagCat.cap)`, and its quantum dimension on two strands is the
square of the closed circle. -/
example :
    SendsSelfDuality (FreeSelfDualityCat.lift (TLDiagCat.of 1)) (TLDiagCat.of 1)
      (FreeSelfDualityCat.liftObjIso (TLDiagCat.of 1)) ∧
    quantumDim (TLDiagCat.of 2) = ((End.of TLDiagCat.circle) ^ 2).asHom :=
  ⟨FreeSelfDualityCat.lift_sendsSelfDuality (TLDiagCat.of 1),
    TLDiagCat.quantumDim_eq_circle_pow 2⟩

end TauCeti
