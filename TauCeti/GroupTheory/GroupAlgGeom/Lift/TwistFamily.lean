/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.GroupAlgGeom.Lift.BasicSeq
import TauCeti.GroupTheory.GroupAlgGeom.ChangeOfCoordinates

/-!
# Twist families of solutions of a standard orientable quadratic equation

Let `S = 1` be a standard orientable quadratic equation over `G` with basic sequence
`Γ = (γ₁, …, γ_K)`, and let `φ_{j,p} = γ_j^{p_j} ⋯ γ₁^{p₁}` be the automorphisms of `G[X]` built
from it, the sequence being continued periodically. For a point `v` of `H` (over a coefficient
homomorphism `ι : G →* H`), the point `twistPoint ι S hS v p` is the composite `ψ_{j,p} = φ_{j,p} v`
of [IFT], §7.4: its value at a variable `x` is the value at `v` of the word `φ_{j,p}(x)`. When `v`
is a solution of `S`, so are all the points `ψ_{j,p}`, because the automorphisms `φ_{j,p}` fix the
coefficients and the left side of `S` ([IFT], §7.1); these are the *twist families* of solutions
from which the discriminating families of solutions of a regular quadratic equation are drawn
([IFT], §7.2, Theorem 10).

Since `φ_{j,p}` is a coefficient-preserving automorphism of `G[X]` fixing `S`, the twist is a
change of coordinates that preserves the system `{S}`. Consequently `φ_{j,p}` also preserves the
radical of `S`: an element vanishes on all solutions of `S` exactly when its image under
`φ_{j,p}` does.

## Main definitions

* `TauCeti.GroupAlgGeom.Lift.twistPoint ι S hS v p`: the point `φ_{j,p} v`.

## Main results

* `TauCeti.GroupAlgGeom.Lift.eval_twistPoint`: evaluating at `φ_{j,p} v` is evaluating at `v`
  after applying `φ_{j,p}`.
* `TauCeti.GroupAlgGeom.Lift.twistPoint_concat`: the twist family is built one automorphism at a
  time, `φ_{j+1,p} v = γ_{j+1}^{p_{j+1}} (φ_{j,p} v)`.
* `TauCeti.GroupAlgGeom.Lift.twistPoint_mem_V`, `TauCeti.GroupAlgGeom.Lift.twistPoint_mem_V_iff`:
  the members of the twist family of a solution are solutions, and conversely.
* `TauCeti.GroupAlgGeom.Lift.phi_basicSeq_mem_Rad_iff`: the automorphisms `φ_{j,p}` preserve the
  radical of `S`.

## References

* [IFT] O. Kharlampovich, A. Myasnikov, *Implicit function theorem over free groups*, J. Algebra
  290 (2005), §7.1, §7.2 (Theorem 10) and §7.4.
-/

public section

open Monoid.Coprod

namespace TauCeti.GroupAlgGeom.Lift

open Quadratic

variable {G H X : Type*} [Group G] [Group H]

section TwistPoint

variable (ι : G →* H) (S : Standard G X) (hS : S.IsOrientable)

/-- The point `φ_{j,p} v` of [IFT], §7.4: the composite of a point `v` with the automorphism
`φ_{j,p}` of the basic sequence of a standard orientable quadratic equation `S`, `j` being the
length of `p`. Its value at a variable `x` is the value at `v` of the word `φ_{j,p}(x)`. -/
noncomputable def twistPoint (v : X → H) (p : List ℕ) : X → H :=
  wordMap ι (fun x => phi (basicSeq S hS) p (inr (FreeGroup.of x))) v

theorem twistPoint_def (v : X → H) (p : List ℕ) : twistPoint ι S hS v p =
    wordMap ι (fun x => phi (basicSeq S hS) p (inr (FreeGroup.of x))) v := (rfl)

/-- The twist family of `v` starts at `v`: with no exponents, `φ_{0,()}` is the identity. -/
@[simp]
theorem twistPoint_nil (v : X → H) : twistPoint ι S hS v [] = v := by
  simp [twistPoint_def]

/-- With all exponents zero, the point `φ_{j,p} v` is `v`. -/
@[simp]
theorem twistPoint_replicate_zero (v : X → H) (j : ℕ) :
    twistPoint ι S hS v (List.replicate j 0) = v := by
  simp [twistPoint_def]

/-- Evaluating at the point `φ_{j,p} v` is evaluating at `v` after applying `φ_{j,p}`. -/
@[simp]
theorem eval_twistPoint (v : X → H) (p : List ℕ) (w : GX G X) : eval ι (twistPoint ι S hS v p) w =
    eval ι v (phi (basicSeq S hS) p w) := by
  have h := DFunLike.congr_fun
    (eval_wordMap (ι := ι) (.ofMulEquiv (phi (basicSeq S hS) p) (phi_basicSeq_inl hS p)) v) w
  simpa [twistPoint_def] using h

/-- The twist family is built one automorphism at a time: `φ_{j+1,p} v` is the point
`φ_{j,p} v` composed with `γ_{j+1} ^ p_{j+1}`, the indices of the basic sequence being read
modulo its length. -/
theorem twistPoint_concat (v : X → H) (p : List ℕ) (e : ℕ) : twistPoint ι S hS v (p ++ [e]) =
    wordMap ι (fun x => ((basicSeq S hS).getD (p.length % (basicSeq S hS).length) 1 ^ e)
      (inr (FreeGroup.of x))) (twistPoint ι S hS v p) := by
  funext x
  simp [twistPoint_def ι S hS v (p ++ [e]), phi_concat]

variable {ι S}

/-- The point `φ_{j,p} v` is a solution of `S` exactly when `v` is. -/
theorem twistPoint_mem_V_iff {v : X → H} (p : List ℕ) : twistPoint ι S hS v p ∈ V ι {S.toWord} ↔
    v ∈ V ι {S.toWord} :=
  wordMap_phi_basicSeq_mem_V_iff hS ι p v

/-- The members `φ_{j,p} v` of the twist family of a solution `v` of `S` are solutions of `S`. -/
theorem twistPoint_mem_V {v : X → H} (hv : v ∈ V ι {S.toWord}) (p : List ℕ) :
    twistPoint ι S hS v p ∈ V ι {S.toWord} :=
  (twistPoint_mem_V_iff hS p).2 hv

/-- The automorphisms `φ_{j,p}` preserve the radical of `S`: an element vanishes on every
solution of `S` exactly when its image under `φ_{j,p}` does. -/
theorem phi_basicSeq_mem_Rad_iff (p : List ℕ) {w : GX G X} :
    phi (basicSeq S hS) p w ∈ Rad ι {S.toWord} ↔ w ∈ Rad ι {S.toWord} := by
  have h := Rad_preimage ι (.ofMulEquiv (phi (basicSeq S hS) p) (phi_basicSeq_inl hS p))
    (GHom.ofMulEquiv_bijective _ _) {S.toWord}
  simpa [← MulEquiv.eq_symm_apply] using (SetLike.ext_iff.1 h w).symm

end TwistPoint

/-! ### Examples -/

section Examples

open Quadratic.Standard

/-- For the equation `∏ᵢ₌₁ⁿ [xᵢ, yᵢ] = 1`, the first member of the twist family of a point `v` with
exponent `e` takes the value `v(x₁) ^ e v(y₁)` at `y₁`: the first basic automorphism is
`y₁ ↦ x₁ y₁`. -/
theorem twistPoint_orientable_singleton_apply_y (ι : G →* H) {n : ℕ} (hn : 0 < n) {x y : Fin n → X}
    (inj : (Sum.elim x y).Injective) (v : X → H) (e : ℕ) :
    twistPoint ι (orientable n hn x y inj) (isOrientable_orientable hn inj) v [e] (y ⟨0, hn⟩) =
      v (x ⟨0, hn⟩) ^ e * v (y ⟨0, hn⟩) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero hn.ne'
  have hseq : (basicWordSeq (inj.sumElim_of_isEmpty Fin.elim0) (Fin.elim0 : Fin 0 → G)).getD 0 1 =
      basicY (inj.sumElim_of_isEmpty Fin.elim0) ⟨0, hn⟩ := by
    simp [basicWordSeq_def, List.ofFn_succ]
  rw [twistPoint_def, wordMap_apply, phi_singleton, basicSeq_orientable hn inj, hseq,
    ← zpow_natCast, basicY_zpow_inr_of]
  simp

end Examples

end TauCeti.GroupAlgGeom.Lift
