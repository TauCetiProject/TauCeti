/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.DoubleDual
public import Mathlib.Topology.Algebra.Module.Spaces.WeakDual
public import TauCeti.Analysis.Normed.Operator.Restrict
import TauCeti.Analysis.Normed.Module.Dual.Adjoint
import TauCeti.Analysis.Normed.Module.Dual.Functoriality

/-!
# The dual of a Banach bimodule

Let `A` be a normed algebra over `𝕜` and `E` a normed space. A bounded bimodule structure on `E`
is given by two bounded bilinear maps `L R : A →L[𝕜] E →L[𝕜] E`, with `a · x = L a x` and
`x · a = R a x`, satisfying `L (a * b) x = L a (L b x)`, `R (a * b) x = R b (R a x)` and
`L a (R b x) = R b (L a x)`. The actions need not be contractive or unital.

The continuous dual `E*` is again a bounded bimodule, with the *dual actions*

`(a · φ) x = φ (x · a)` and `(φ · a) x = φ (a · x)`.

Both are instances of one construction: for a bounded bilinear action
`M : A →L[𝕜] E →L[𝕜] E`, the bounded bilinear map `ContinuousLinearMap.dualAction M` sends `a` to
the adjoint `φ ↦ φ ∘ M a` of `M a`. The left action of `A` on `E*` is `dualAction R` and the
right action is `dualAction L`. Dual bimodules are the coefficient modules in the definition of
amenability, where derivations into duals of Banach bimodules are required to be inner, and in
the bounded Hochschild cohomology `Hⁿ(A, E*)`.

This file proves the bimodule laws of the dual actions, the weak-star continuity of each dual
action in the dual variable, and that adjoints of bounded module maps are module maps for the dual
actions. Since `dualAction M a` is the adjoint `precomp 𝕜 (M a)` of `M a`
(`ContinuousLinearMap.dualAction_apply`), the adjoint API applies directly after rewriting:
`ContinuousLinearMap.norm_precomp_le` gives the bound `‖dualAction M a‖ ≤ ‖M a‖`,
`ContinuousLinearMap.norm_precomp` gives equality over `ℝ` or `ℂ`, and
`ContinuousLinearMap.precomp_precomp_inclusionInDoubleDual` shows that the canonical map of `E` into
its bidual `E**` is a bimodule map when `E**` carries the dual actions of `E*`. Likewise, the
correspondence between invariant subspaces and their annihilators in
`TauCeti.Analysis.Normed.Module.Dual.Invariant` identifies the closed submodules of `E` with the
weak-star closed submodules of `E*`. Over fields satisfying `IsRCLikeNormedField`, a bounded
derivation `D₀ : A →L[𝕜] E**` whose values lie in the bidual image of a bi-invariant submodule `p`
(in particular, in `ker T**` for a closed-range bounded operator `T` between Banach spaces) pulls
back to a bounded derivation into `p**` (respectively `(ker T)**`).

## Main definitions

* `ContinuousLinearMap.dualAction`: the dual action `a ↦ (φ ↦ φ ∘ M a)` of a bounded bilinear
  action `M`.

## Main results

* `ContinuousLinearMap.dualAction_apply`: the dual action of `a` is the adjoint of the action of
  `a`.
* `ContinuousLinearMap.dualAction_mul_apply_of_right`,
  `ContinuousLinearMap.dualAction_mul_apply_of_left`,
  `ContinuousLinearMap.dualAction_apply_dualAction_apply_comm`: the dual actions of a bounded
  bimodule satisfy the bimodule laws.
* `ContinuousLinearMap.continuous_toWeakDual_dualAction`: each dual action is weak-star
  continuous in the dual variable.
* `ContinuousLinearMap.precomp_dualAction_apply` and
  `ContinuousLinearMap.dualAction_restrictAction_comp_subtypeL`: the adjoint of a module map
  intertwines the dual actions, in particular when restricting to an invariant submodule.
* `ContinuousLinearMap.dualAction_dualAction_inclusionInDoubleDual` and
  `ContinuousLinearMap.precomp_precomp_dualAction_dualAction_apply`: the iterated dual action on
  the bidual `E**` extends `M` along the canonical embedding and is intertwined by bidual adjoints
  of module maps.
* `ContinuousLinearMap.exists_derivation_bidual_of_mem_range_precomp_precomp_subtypeL` and
  `ContinuousLinearMap.exists_derivation_bidual_ker`: pulling a bounded derivation `A →L[𝕜] E**`
  landing in the bidual image of a bi-invariant submodule (or in `ker T**` for closed-range `T`)
  back to a bounded derivation into `p**` (respectively `(ker T)**`).

## References

* H. G. Dales, *Banach Algebras and Automatic Continuity*, §2.6, dual modules.
* V. Runde, *Lectures on Amenability*, §2.1, dual Banach bimodules.
-/

public section

noncomputable section

namespace ContinuousLinearMap

variable {𝕜 A E F : Type*} [NontriviallyNormedField 𝕜]
  [SeminormedAddCommGroup A] [NormedSpace 𝕜 A]
  [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
  [SeminormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- The dual action of a bounded bilinear action `M : A →L[𝕜] E →L[𝕜] E` on the continuous dual
of `E`: `dualAction M a φ = φ ∘ M a`. For a bounded bimodule with left action `L` and right action
`R`, the dual bimodule has left action `dualAction R`, `(a · φ) x = φ (x · a)`, and right action
`dualAction L`, `(φ · a) x = φ (a · x)`. -/
def dualAction (M : A →L[𝕜] E →L[𝕜] E) :
    A →L[𝕜] StrongDual 𝕜 E →L[𝕜] StrongDual 𝕜 E :=
  (compL 𝕜 E E 𝕜).flip ∘L M

/-- The dual action evaluates as `(dualAction M a φ) x = φ (M a x)`. -/
@[simp]
theorem dualAction_apply_apply (M : A →L[𝕜] E →L[𝕜] E) (a : A) (φ : StrongDual 𝕜 E) (x : E) :
    dualAction M a φ x = φ (M a x) := (rfl)

/-- The dual action of `a` is the adjoint of the action of `a`. -/
theorem dualAction_apply (M : A →L[𝕜] E →L[𝕜] E) (a : A) :
    dualAction M a = precomp 𝕜 (M a) := by
  ext φ x
  simp

section Laws

variable [Mul A]

/-- The dual of a right action is a left action: if `R (a * b) x = R b (R a x)`, then
`a * b` acts on functionals as `a` after `b`. -/
theorem dualAction_mul_apply_of_right {R : A →L[𝕜] E →L[𝕜] E}
    (hR : ∀ a b x, R (a * b) x = R b (R a x)) (a b : A) (φ : StrongDual 𝕜 E) :
    dualAction R (a * b) φ = dualAction R a (dualAction R b φ) := by
  ext x
  simp [hR]

/-- The dual of a left action is a right action: if `L (a * b) x = L a (L b x)`, then
`a * b` acts on functionals as `b` after `a`. -/
theorem dualAction_mul_apply_of_left {L : A →L[𝕜] E →L[𝕜] E}
    (hL : ∀ a b x, L (a * b) x = L a (L b x)) (a b : A) (φ : StrongDual 𝕜 E) :
    dualAction L (a * b) φ = dualAction L b (dualAction L a φ) := by
  ext x
  simp [hL]

end Laws

/-- The dual actions of commuting actions commute: if `L a (R b x) = R b (L a x)`, then the dual
left action `dualAction R` commutes with the dual right action `dualAction L`. -/
theorem dualAction_apply_dualAction_apply_comm {L R : A →L[𝕜] E →L[𝕜] E}
    (hLR : ∀ a b x, L a (R b x) = R b (L a x)) (a b : A) (φ : StrongDual 𝕜 E) :
    dualAction R a (dualAction L b φ) = dualAction L b (dualAction R a φ) := by
  ext x
  simp [hLR]

/-- Each dual action is continuous for the weak-star topology in the dual variable. -/
theorem continuous_toWeakDual_dualAction (M : A →L[𝕜] E →L[𝕜] E) (a : A) :
    Continuous fun φ : WeakDual 𝕜 E ↦
      StrongDual.toWeakDual (dualAction M a (WeakDual.toStrongDual φ)) :=
  WeakDual.continuous_of_continuous_eval fun x ↦ WeakDual.eval_continuous (M a x)

/-- The adjoint of a bounded module map intertwines the dual actions: if `T (M a x) = N a (T x)`,
then `T* (dualAction N a ψ) = dualAction M a (T* ψ)`. -/
theorem precomp_dualAction_apply {M : A →L[𝕜] E →L[𝕜] E} {N : A →L[𝕜] F →L[𝕜] F}
    {T : E →L[𝕜] F} (hT : ∀ a x, T (M a x) = N a (T x)) (a : A) (ψ : StrongDual 𝕜 F) :
    precomp 𝕜 T (dualAction N a ψ) = dualAction M a (precomp 𝕜 T ψ) := by
  ext x
  simp [hT]

/-- Restricting a functional to an invariant submodule intertwines the dual action with the dual of
the restricted action. -/
@[simp]
theorem dualAction_restrictAction_comp_subtypeL (M : A →L[𝕜] E →L[𝕜] E) (p : Submodule 𝕜 E)
    (hM : ∀ a x, x ∈ p → M a x ∈ p) (a : A) (φ : StrongDual 𝕜 E) :
    dualAction (M.restrictAction p hM) a (φ.comp p.subtypeL) =
      (dualAction M a φ).comp p.subtypeL := by
  ext x
  simp

/-- The iterated dual action on the bidual extends the original action along the canonical
embedding `NormedSpace.inclusionInDoubleDual`. -/
@[simp]
theorem dualAction_dualAction_inclusionInDoubleDual (M : A →L[𝕜] E →L[𝕜] E) (a : A) (x : E) :
    dualAction (dualAction M) a (NormedSpace.inclusionInDoubleDual 𝕜 E x) =
      NormedSpace.inclusionInDoubleDual 𝕜 E (M a x) := by
  ext φ
  simp [NormedSpace.dual_def]

/-- The bidual adjoint `T**` of a bounded module map intertwines the iterated dual actions on the
biduals. -/
theorem precomp_precomp_dualAction_dualAction_apply {M : A →L[𝕜] E →L[𝕜] E}
    {N : A →L[𝕜] F →L[𝕜] F} {T : E →L[𝕜] F} (hT : ∀ a x, T (M a x) = N a (T x)) (a : A)
    (Φ : StrongDual 𝕜 (StrongDual 𝕜 E)) :
    precomp 𝕜 (precomp 𝕜 T : StrongDual 𝕜 F →L[𝕜] StrongDual 𝕜 E)
        (dualAction (dualAction M) a Φ) =
      dualAction (dualAction N) a
        (precomp 𝕜 (precomp 𝕜 T : StrongDual 𝕜 F →L[𝕜] StrongDual 𝕜 E) Φ) :=
  precomp_dualAction_apply (precomp_dualAction_apply hT) a Φ

section BidualDerivation

variable [IsRCLikeNormedField 𝕜] [Mul A]

/-- If a bounded derivation `D₀ : A →L[𝕜] E**` takes values in the range of the bidual adjoint of
`p.subtypeL` for a bi-invariant submodule `p ≤ E`, then it pulls back along `(p.subtypeL)**` to a
bounded derivation `A →L[𝕜] p**` for the restricted bidual actions. -/
theorem exists_derivation_bidual_of_mem_range_precomp_precomp_subtypeL
    (D₀ : A →L[𝕜] StrongDual 𝕜 (StrongDual 𝕜 E))
    {L R : A →L[𝕜] E →L[𝕜] E} {p : Submodule 𝕜 E}
    (hpL : ∀ a x, x ∈ p → L a x ∈ p)
    (hpR : ∀ a x, x ∈ p → R a x ∈ p)
    (hD₀ : ∀ a b : A,
      D₀ (a * b) = dualAction (dualAction L) a (D₀ b) + dualAction (dualAction R) b (D₀ a))
    (hmem : ∀ a : A,
      D₀ a ∈ (precomp 𝕜 (precomp 𝕜 p.subtypeL : StrongDual 𝕜 E →L[𝕜] StrongDual 𝕜 p) :
        StrongDual 𝕜 (StrongDual 𝕜 p) →L[𝕜] StrongDual 𝕜 (StrongDual 𝕜 E)).range) :
    ∃ D : A →L[𝕜] StrongDual 𝕜 (StrongDual 𝕜 p),
      (∀ a : A,
        precomp 𝕜 (precomp 𝕜 p.subtypeL : StrongDual 𝕜 E →L[𝕜] StrongDual 𝕜 p) (D a) = D₀ a) ∧
      ∀ a b : A, D (a * b) =
        dualAction (dualAction (L.restrictAction p hpL)) a (D b) +
          dualAction (dualAction (R.restrictAction p hpR)) b (D a) := by
  let : SeminormedAddCommGroup (StrongDual 𝕜 E) := inferInstance
  let : NormedSpace 𝕜 (StrongDual 𝕜 E) := inferInstance
  let : SeminormedAddCommGroup (StrongDual 𝕜 (StrongDual 𝕜 E)) := inferInstance
  let : NormedSpace 𝕜 (StrongDual 𝕜 (StrongDual 𝕜 E)) := inferInstance
  let : SeminormedAddCommGroup (StrongDual 𝕜 p) := inferInstance
  let : NormedSpace 𝕜 (StrongDual 𝕜 p) := inferInstance
  let : SeminormedAddCommGroup (StrongDual 𝕜 (StrongDual 𝕜 p)) := inferInstance
  let : NormedSpace 𝕜 (StrongDual 𝕜 (StrongDual 𝕜 p)) := inferInstance
  have hmem' (a : A) : D₀ a ∈
      (p.orthogonalBilin (topDualPairing 𝕜 E).flip).orthogonalBilin
        (topDualPairing 𝕜 (StrongDual 𝕜 E)).flip :=
    p.range_precomp_precomp_subtypeL ▸ hmem a
  let D : A →L[𝕜] StrongDual 𝕜 (StrongDual 𝕜 p) :=
    p.bidualEquivDoubleAnnihilator.symm.toLinearIsometry.toContinuousLinearMap.comp
      (D₀.codRestrict _ hmem')
  have hD_precomp (a : A) :
      precomp 𝕜 (precomp 𝕜 p.subtypeL : StrongDual 𝕜 E →L[𝕜] StrongDual 𝕜 p) (D a) = D₀ a := by
    rw [← p.coe_bidualEquivDoubleAnnihilator_apply]
    exact congrArg Subtype.val (p.bidualEquivDoubleAnnihilator.apply_symm_apply _)
  refine ⟨D, hD_precomp, fun a b ↦ p.bidualEquivDoubleAnnihilator.injective <| Subtype.ext ?_⟩
  rw [p.coe_bidualEquivDoubleAnnihilator_apply, p.coe_bidualEquivDoubleAnnihilator_apply,
    map_add, hD_precomp, hD₀,
    precomp_precomp_dualAction_dualAction_apply (M := L.restrictAction p hpL) (N := L)
      (T := p.subtypeL) (coe_restrictAction_apply L p hpL),
    precomp_precomp_dualAction_dualAction_apply (M := R.restrictAction p hpR) (N := R)
      (T := p.subtypeL) (coe_restrictAction_apply R p hpR),
    hD_precomp, hD_precomp]

/-- If `T : E →L[𝕜] F` is a closed-range bounded operator between Banach spaces whose kernel is
bi-invariant and `D₀ : A →L[𝕜] E**` is a bounded derivation taking values in `ker T**`, then `D₀`
pulls back along `(T.ker.subtypeL)**` to a bounded derivation `A →L[𝕜] (ker T)**` for the
restricted bidual actions. -/
theorem exists_derivation_bidual_ker {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]
    (T : E →L[𝕜] F) {L R : A →L[𝕜] E →L[𝕜] E}
    (hTL : ∀ a x, x ∈ T.ker → L a x ∈ T.ker)
    (hTR : ∀ a x, x ∈ T.ker → R a x ∈ T.ker)
    (hT : IsClosed (T.range : Set F))
    (D₀ : A →L[𝕜] StrongDual 𝕜 (StrongDual 𝕜 E))
    (hD₀ : ∀ a b : A,
      D₀ (a * b) = dualAction (dualAction L) a (D₀ b) + dualAction (dualAction R) b (D₀ a))
    (hker : ∀ a : A,
      D₀ a ∈ (precomp 𝕜 (precomp 𝕜 T : StrongDual 𝕜 F →L[𝕜] StrongDual 𝕜 E) :
        StrongDual 𝕜 (StrongDual 𝕜 E) →L[𝕜] StrongDual 𝕜 (StrongDual 𝕜 F)).ker) :
    ∃ D : A →L[𝕜] StrongDual 𝕜 (StrongDual 𝕜 T.ker),
      (∀ a : A,
        precomp 𝕜 (precomp 𝕜 T.ker.subtypeL : StrongDual 𝕜 E →L[𝕜] StrongDual 𝕜 T.ker) (D a) =
          D₀ a) ∧
      ∀ a b : A, D (a * b) =
        dualAction (dualAction (L.restrictAction T.ker hTL)) a (D b) +
          dualAction (dualAction (R.restrictAction T.ker hTR)) b (D a) :=
  D₀.exists_derivation_bidual_of_mem_range_precomp_precomp_subtypeL hTL hTR hD₀ fun a ↦ by
    rw [← T.ker_precomp_precomp_eq_range_precomp_precomp_subtypeL hT]
    exact hker a

end BidualDerivation

end ContinuousLinearMap
