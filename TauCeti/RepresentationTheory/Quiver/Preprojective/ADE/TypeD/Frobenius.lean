/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Algebra.Frobenius.Basic
public import TauCeti.RepresentationTheory.Quiver.Preprojective.ADE.TypeD.ForkTopPower
-- Reuse the detecting representation of the fork basis, without exporting its implementation.
import all TauCeti.RepresentationTheory.Quiver.Preprojective.ADE.TypeD.Basis

/-!
# The type-`D` fork corner is Frobenius

At the fork vertex `c = n - 3` of the signless preprojective algebra of `Dₙ`, the two
leaf backtracks have nilpotent linear span. An element annihilated on the left by
both backtracks vanishes if its terminal alternating-word coordinate vanishes.
The functional selecting that coordinate is
Frobenius, over every field, including characteristic two. Consequently this corner
is left and right self-injective.

This corner pairing controls the branch-vertex contribution to Frobenius pairings
on type-`D` preprojective algebras.

The basis and detecting representation are those of
`TauCeti.RepresentationTheory.Quiver.Preprojective.ADE.TypeD.Basis`.
See C. M. Ringel, *The preprojective algebra of a quiver*, for the finite-Dynkin
Frobenius property, and T. Y. Lam, *Lectures on modules and rings*, Section 16,
for Frobenius functionals and self-injectivity.
-/

public section

namespace TauCeti

open PathAlgebra DoubledQuiver

attribute [local instance] forkNeighborSetFintype

variable (k : Type*) [Field k] {n : ℕ}

local notation "DG" => diagramGraph (DynkinType.cartanMatrix (DynkinType.D n))
local notation "Π" => signlessPreprojectiveAlgebra k (DoubledQuiver DG)
local notation "c" => n - 3
local notation "π" => signlessPreprojectiveMk k (DoubledQuiver DG)
local notation "e" => fun hn => π (vertexIdempotent k (vertex DG (preprojectiveDForkVertex n hn)))

/-- The image of the fork vertex in the signless preprojective algebra is idempotent. -/
theorem isIdempotentElem_signlessPreprojectiveDForkVertex (hn : 3 ≤ n) : IsIdempotentElem (e hn) :=
  IsIdempotentElem.map
    (vertexIdempotent_mul_self (k := k) (vertex DG (preprojectiveDForkVertex n hn))) π

/-- The corner ring at the branch vertex of the type-`D` signless preprojective algebra.
Its unit is the branch vertex idempotent. -/
abbrev SignlessPreprojectiveDForkCorner (hn : 3 ≤ n) :=
  (isIdempotentElem_signlessPreprojectiveDForkVertex k hn).Corner

private theorem forkVector_detect (hn : 3 ≤ n) {z : Π}
    (hz : z ∈ cornerSubmodule k (e hn) (e hn)) :
    forkVector k (preprojectiveDForkVertex n hn) (forkDetect k hn z) =
      forkAction k hn z (forkVector k (preprojectiveDForkVertex n hn)
        (Finsupp.single (true, 0) 1)) := by
  have hez := mul_eq_self_of_mem_cornerSubmodule
    (isIdempotentElem_signlessPreprojectiveDForkVertex k hn) hz
  have h := congrArg (fun w => forkAction k hn w
    (forkVector k (preprojectiveDForkVertex n hn) (Finsupp.single (true, 0) 1))) hez
  rw [map_mul, Module.End.mul_apply] at h
  -- The vertex action is projection onto its direct-sum component; detection reads that component.
  simpa only [forkAction, signlessPreprojectiveLift_signlessPreprojectiveMk,
    QuiverRep.toEnd_vertexIdempotent, QuiverRep.pathEnd_apply, QuiverRep.mapₗ_nil,
    forkVector, forkDetect, LinearMap.comp_apply, LinearMap.coe_mk, AddHom.coe_mk,
    LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply, LinearMap.id_apply] using h

private theorem forkDetect_backtrack_mul (hn : 3 ≤ n) {z : Π}
    (hz : z ∈ cornerSubmodule k (e hn) (e hn)) (l : Bool) :
    forkDetect k hn (signlessPreprojectiveDForkBacktrack k l * z) =
      (if l then xStep k c else yStep k c) (forkDetect k hn z) := by
  apply forkDetect_of_eq
  rw [map_mul, Module.End.mul_apply, ← forkVector_detect k hn hz]
  cases l
  · rw [signlessPreprojectiveDForkBacktrack_false, forkAction_turn_right]
    rfl
  · rw [signlessPreprojectiveDForkBacktrack_true, forkAction_turn_left]
    rfl

private theorem xStep_apply_empty (f : ForkCoord k) :
    xStep k c f (true, 1) = f (true, 0) := by
  have h : Finsupp.lapply (true, 1) ∘ₗ xStep k c =
      (Finsupp.lapply (true, 0) : ForkCoord k →ₗ[k] k) := by
    apply Finsupp.lhom_ext'
    rintro ⟨l, t⟩
    apply LinearMap.ext_ring
    cases l <;> simp [xStep_single, Finsupp.single_apply] <;> split_ifs <;> simp_all
  exact LinearMap.congr_fun h f

private theorem xStep_apply_nonempty (f : ForkCoord k) {t : ℕ} (ht : 1 ≤ t) (htc : t ≤ c) :
    xStep k c f (true, t + 1) = f (false, t) := by
  have h : Finsupp.lapply (true, t + 1) ∘ₗ xStep k c =
      (Finsupp.lapply (false, t) : ForkCoord k →ₗ[k] k) := by
    apply Finsupp.lhom_ext'
    rintro ⟨l, s⟩
    apply LinearMap.ext_ring
    cases l <;> simp [xStep_single, Finsupp.single_apply]
    all_goals split_ifs <;> simp_all [Finsupp.single_apply]
    all_goals omega
  exact LinearMap.congr_fun h f

private theorem yStep_apply_nonterminal (f : ForkCoord k) {t : ℕ} (ht : t < c) :
    yStep k c f (false, t + 1) = f (true, t) := by
  have h : Finsupp.lapply (false, t + 1) ∘ₗ yStep k c =
      (Finsupp.lapply (true, t) : ForkCoord k →ₗ[k] k) := by
    apply Finsupp.lhom_ext'
    rintro ⟨l, s⟩
    apply LinearMap.ext_ring
    cases l <;> simp [yStep_single, bWord, Finsupp.single_apply]
    all_goals split_ifs <;> simp_all
    all_goals omega
  exact LinearMap.congr_fun h f

private theorem yStep_apply_terminal (f : ForkCoord k) :
    yStep k c f (true, c + 1) = -f (true, c) := by
  have h : Finsupp.lapply (true, c + 1) ∘ₗ yStep k c =
      -(Finsupp.lapply (true, c) : ForkCoord k →ₗ[k] k) := by
    apply Finsupp.lhom_ext'
    rintro ⟨l, s⟩
    apply LinearMap.ext_ring
    cases l <;> simp [yStep_single, bWord, Finsupp.single_apply]
    all_goals split_ifs <;> simp_all
  exact LinearMap.congr_fun h f

private theorem forkDetect_basis_coord (hn : 3 ≤ n)
    (z : cornerSubmodule k (e hn) (e hn)) (i : Option (Bool × Fin c) ⊕ Unit) :
    forkDetect k hn z (forkWordIndex n i) = (signlessPreprojectiveDForkBasis k hn).repr z i := by
  classical
  have h : Finsupp.lapply (forkWordIndex n i) ∘ₗ forkDetect k hn ∘ₗ
      (cornerSubmodule k (e hn) (e hn)).subtype =
      Finsupp.lapply i ∘ₗ (signlessPreprojectiveDForkBasis k hn).repr.toLinearMap := by
    apply (signlessPreprojectiveDForkBasis k hn).ext
    intro j
    simp only [LinearMap.comp_apply, Submodule.subtype_apply,
      coe_signlessPreprojectiveDForkBasis_apply, forkDetect_forkWords,
      Module.Basis.repr_self, LinearEquiv.coe_coe, Finsupp.lapply_apply,
      Finsupp.single_apply, (forkWordIndex_injective n).eq_iff]
  exact LinearMap.congr_fun h z

/-- The functional on the type-`D` fork corner selecting the coefficient of its terminal
alternating word `x (x + y)^(n - 3)`. -/
noncomputable def signlessPreprojectiveDForkFrobeniusFunctional (hn : 3 ≤ n) :
    SignlessPreprojectiveDForkCorner k hn →ₗ[k] k :=
  Finsupp.lapply (.inr ()) ∘ₗ (signlessPreprojectiveDForkBasis k hn).repr.toLinearMap ∘ₗ
    (IsIdempotentElem.cornerLinearEquivCornerSubmodule
      (isIdempotentElem_signlessPreprojectiveDForkVertex k hn)).toLinearMap

/-- The fork functional is the terminal coordinate in the reduced fork basis. -/
theorem signlessPreprojectiveDForkFrobeniusFunctional_apply (hn : 3 ≤ n)
    (z : SignlessPreprojectiveDForkCorner k hn) :
    signlessPreprojectiveDForkFrobeniusFunctional k hn z =
      (signlessPreprojectiveDForkBasis k hn).repr
        (IsIdempotentElem.cornerLinearEquivCornerSubmodule
          (isIdempotentElem_signlessPreprojectiveDForkVertex k hn) z) (.inr ()) :=
  (rfl)

/-- The fork functional is one on the terminal basis word and zero on all other basis words. -/
-- Read the basis word before simplification changes the diagram rank in its index type.
@[simp↓] theorem signlessPreprojectiveDForkFrobeniusFunctional_basis (hn : 3 ≤ n)
    (i : Option (Bool × Fin c) ⊕ Unit) :
    signlessPreprojectiveDForkFrobeniusFunctional k hn
      ((IsIdempotentElem.cornerLinearEquivCornerSubmodule
        (isIdempotentElem_signlessPreprojectiveDForkVertex k hn)).symm
        (signlessPreprojectiveDForkBasis k hn i)) = if i = .inr () then 1 else 0 := by
  classical
  rw [signlessPreprojectiveDForkFrobeniusFunctional_apply, LinearEquiv.apply_symm_apply,
    Module.Basis.repr_self, Finsupp.single_apply]

private theorem fork_eq_zero_of_backtrack_mul (hn : 3 ≤ n)
    (z : SignlessPreprojectiveDForkCorner k hn)
    (hx : signlessPreprojectiveDForkBacktrack k true * z.val = 0)
    (hy : signlessPreprojectiveDForkBacktrack k false * z.val = 0)
    (hφ : signlessPreprojectiveDForkFrobeniusFunctional k hn z = 0) : z = 0 := by
  let E := IsIdempotentElem.cornerLinearEquivCornerSubmodule (R := k)
    (isIdempotentElem_signlessPreprojectiveDForkVertex k hn)
  let B := signlessPreprojectiveDForkBasis k hn
  have hz : z.val ∈ cornerSubmodule k (e hn) (e hn) := by
    simpa only [E, IsIdempotentElem.coe_cornerLinearEquivCornerSubmodule_apply] using (E z).property
  have hx' : xStep k c (forkDetect k hn z.val) = 0 := by
    simpa only [ite_true, hx, map_zero] using (forkDetect_backtrack_mul k hn hz true).symm
  have hy' : yStep k c (forkDetect k hn z.val) = 0 := by
    simpa only [Bool.false_eq_true, ite_false, hy, map_zero] using
      (forkDetect_backtrack_mul k hn hz false).symm
  have hrepr : B.repr (E z) = 0 := by
    ext i
    rw [Finsupp.zero_apply, ← forkDetect_basis_coord k hn (E z) i]
    simp only [E, IsIdempotentElem.coe_cornerLinearEquivCornerSubmodule_apply]
    rcases i with (_ | ⟨l, t⟩) | u
    · exact (xStep_apply_empty (n := n) k _).symm.trans (DFunLike.congr_fun hx' (true, 1))
    · cases l
      · exact (xStep_apply_nonempty k _ (by omega : 1 ≤ t.val + 1)
          (by omega : t.val + 1 ≤ c)).symm.trans (DFunLike.congr_fun hx' (true, t.val + 2))
      · by_cases ht : t.val + 1 < c
        · exact (yStep_apply_nonterminal k _ ht).symm.trans
            (DFunLike.congr_fun hy' (false, t.val + 2))
        · have ht' : t.val + 1 = c := by omega
          have h := yStep_apply_terminal (n := n) k (forkDetect k hn z.val)
          rw [hy', Finsupp.zero_apply, zero_eq_neg] at h
          simpa only [forkWordIndex, ht'] using h
    · cases u
      simpa only [E, IsIdempotentElem.coe_cornerLinearEquivCornerSubmodule_apply] using
        (forkDetect_basis_coord k hn (E z) (.inr ())).trans hφ
  have hz0 : E z = 0 := B.repr.injective (hrepr.trans (B.repr.map_zero).symm)
  exact E.injective (hz0.trans E.map_zero.symm)

private theorem forkBacktrack_mem (hn : 3 ≤ n) (l : Bool) :
    signlessPreprojectiveDForkBacktrack k l ∈ cornerSubmodule k (e hn) (e hn) := by
  rw [mem_cornerSubmodule_iff k (isIdempotentElem_signlessPreprojectiveDForkVertex k hn)
    (isIdempotentElem_signlessPreprojectiveDForkVertex k hn)]
  cases l <;> first | rw [signlessPreprojectiveDForkBacktrack_false] |
    rw [signlessPreprojectiveDForkBacktrack_true]
  all_goals
    simp only [mul_assoc, signlessArrow_mul_vertexIdempotent,
      preprojectiveDForkVertex_val, ite_true]
    rw [← mul_assoc, vertexIdempotent_mul_signlessArrow]
    simp only [preprojectiveDForkVertex_val, ite_true]

private noncomputable def forkBacktrack (hn : 3 ≤ n) (l : Bool) :
    SignlessPreprojectiveDForkCorner k hn :=
  (isIdempotentElem_signlessPreprojectiveDForkVertex k hn).cornerLinearEquivCornerSubmodule.symm
    ⟨signlessPreprojectiveDForkBacktrack k l, forkBacktrack_mem k hn l⟩

private theorem forkBacktrack_val (hn : 3 ≤ n) (l : Bool) :
    (forkBacktrack k hn l).val = signlessPreprojectiveDForkBacktrack k l := by
  simp only [forkBacktrack, IsIdempotentElem.val_cornerLinearEquivCornerSubmodule_symm_apply]

private theorem forkBacktrack_sq (hn : 3 ≤ n) (l : Bool) :
    forkBacktrack k hn l * forkBacktrack k hn l = 0 := by
  apply Subtype.ext
  simpa only [IsIdempotentElem.Corner.val_mul, IsIdempotentElem.Corner.val_zero,
    forkBacktrack_val] using signlessPreprojectiveDForkBacktrack_mul_self k hn l

private theorem forkBacktrack_add_pow (hn : 3 ≤ n) :
    (forkBacktrack k hn true + forkBacktrack k hn false) ^ (c + 1) = 0 := by
  let s := forkBacktrack k hn true + forkBacktrack k hn false
  have hp (t : ℕ) : (s ^ (t + 1)).val = s.val ^ (t + 1) := by
    induction t with
    | zero => simp only [Nat.zero_add, pow_one]
    | succ t ih => rw [pow_succ, IsIdempotentElem.Corner.val_mul, ih, ← pow_succ]
  apply Subtype.ext
  rw [hp, IsIdempotentElem.Corner.val_zero]
  simpa only [s, IsIdempotentElem.Corner.val_add, forkBacktrack_val] using
    signlessPreprojectiveDForkBacktrack_add_pow_eq_zero k hn

/-- The terminal-word functional on the type-`D` fork corner is Frobenius over every field. -/
theorem isFrobeniusFunctional_signlessPreprojectiveDForkFrobeniusFunctional (hn : 3 ≤ n) :
    (signlessPreprojectiveDForkFrobeniusFunctional k hn).IsFrobeniusFunctional := by
  classical
  let x := forkBacktrack k hn true
  let y := forkBacktrack k hn false
  let P := Submodule.span k {x, y}
  let φ := signlessPreprojectiveDForkFrobeniusFunctional k hn
  let : IsScalarTower k (SignlessPreprojectiveDForkCorner k hn)
      (SignlessPreprojectiveDForkCorner k hn) :=
    ⟨fun r a b => Subtype.ext (smul_mul_assoc r a.val b.val)⟩
  have hnil : P ^ (c + 2) = ⊥ :=
    span_pair_pow_succ_eq_bot (forkBacktrack_sq k hn true) (forkBacktrack_sq k hn false)
      (forkBacktrack_add_pow k hn)
  -- Descend through the nilpotent backtrack-span powers. At the last step, the
  -- common annihilator is detected by the terminal-word functional.
  have hsep (m : ℕ) (z : SignlessPreprojectiveDForkCorner k hn)
      (hz : ∀ a, φ (a * z) = 0) (hm : ∀ w ∈ P ^ m, w * z = 0) : z = 0 := by
    induction m generalizing z with
    | zero =>
      apply (one_mul z).symm.trans
      apply hm
      rw [Submodule.pow_zero, Submodule.one_eq_span]
      exact Submodule.subset_span rfl
    | succ m ih =>
      have hgen (w : SignlessPreprojectiveDForkCorner k hn) (hw : w ∈ P) : w * z = 0 := by
        apply ih (w * z) (fun a => by simpa only [← mul_assoc] using hz (a * w))
        intro a ha
        rw [← mul_assoc]
        exact hm (a * w) (by rw [Submodule.pow_succ]; exact Submodule.mul_mem_mul ha hw)
      have hx := congrArg Subtype.val (hgen x (Submodule.subset_span (Or.inl rfl)))
      have hy := congrArg Subtype.val (hgen y (Submodule.subset_span (Or.inr rfl)))
      simp only [x, y, IsIdempotentElem.Corner.val_mul, IsIdempotentElem.Corner.val_zero,
        forkBacktrack_val] at hx hy
      exact fork_eq_zero_of_backtrack_mul k hn z hx hy (by simpa only [one_mul] using hz 1)
  apply LinearMap.IsFrobeniusFunctional.of_right
  intro z hz
  apply hsep (c + 2) z hz
  intro w hw
  rw [hnil, Submodule.mem_bot] at hw
  rw [hw, zero_mul]

/-- The type-`D` branch-vertex corner is left self-injective. -/
theorem moduleInjective_signlessPreprojectiveDForkCorner (hn : 3 ≤ n) :
    Module.Injective (SignlessPreprojectiveDForkCorner k hn)
      (SignlessPreprojectiveDForkCorner k hn) :=
  (isFrobeniusFunctional_signlessPreprojectiveDForkFrobeniusFunctional k hn).moduleInjective_self

/-- The type-`D` branch-vertex corner is right self-injective. -/
theorem moduleInjective_op_signlessPreprojectiveDForkCorner (hn : 3 ≤ n) :
    Module.Injective (SignlessPreprojectiveDForkCorner k hn)ᵐᵒᵖ
      (SignlessPreprojectiveDForkCorner k hn) :=
  (isFrobeniusFunctional_signlessPreprojectiveDForkFrobeniusFunctional k hn).moduleInjective_op_self

end TauCeti
