/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.PathSpace.Moore.Replacement.Append
public import TauCeti.Topology.PathSpace.Moore.Replacement.Equiv

/-!
# The Moore-path replacement of the inclusion of a point

Let `a` be a point of `B`, included in `B` by `ContinuousMap.subtypeVal ({a} : Set B)`. The total
space `E'` of its Moore-path replacement is the space `P_a B` of Moore paths from `a`, by
`TauCeti.MooreReplacement.homeomorphPathsFrom {a}`; this file identifies its fibre `F'_b` over `b`
with the space of Moore paths from `a` to `b`
(`TauCeti.MooreReplacement.Fiber.homeomorphPathsBetween`). Read through these identifications, the
loops at `b` act on the fibre by concatenation behind
(`TauCeti.MooreReplacement.Fiber.homeomorphPathsBetween_op_smul`), and appending a Moore path from
`b` to a point of the fibre is concatenation of paths
(`TauCeti.MooreReplacement.Fiber.homeomorphPathsFrom_appendFrom`).

The codomain `{γ // γ.source ∈ {a}}` of `homeomorphPathsFrom {a}` is by definition the space
`MoorePathFrom B a = {γ // γ.source = a}`, and this file uses it as such.

## Main definitions

* `TauCeti.MooreReplacement.Fiber.homeomorphPathsBetween a b`: the homeomorphism of the fibre over
  `b` with the space of Moore paths from `a` to `b`.

## Main results

* `TauCeti.MooreReplacement.Fiber.homeomorphPathsBetween_op_smul`: the identification of the fibre
  is equivariant for the loops at `b`.
* `TauCeti.MooreReplacement.Fiber.homeomorphPathsFrom_appendFrom`: appending a path from `b` is
  concatenation.
-/

public noncomputable section

open MulOpposite

namespace TauCeti.MooreReplacement

variable {B : Type*} [TopologicalSpace B] {a b : B}

/-- The Moore path from `a` of a point of the replacement of the inclusion of `a`. -/
@[simp]
theorem toMoorePath_homeomorphPathsFrom (x : MooreReplacement (ContinuousMap.subtypeVal {a})) :
    MoorePathFrom.toMoorePath (homeomorphPathsFrom {a} x : MoorePathFrom B a) = x.path :=
  (MoorePathFrom.toMoorePath_mk _ _).trans (coe_homeomorphPathsFrom _ x)

/-- The point of the replacement of the inclusion of `a` with Moore path `γ` from `a`. -/
@[simp]
theorem path_homeomorphPathsFrom_symm_singleton (γ : MoorePathFrom B a) :
    ((homeomorphPathsFrom {a}).symm γ).path = γ.toMoorePath :=
  (path_homeomorphPathsFrom_symm {a} γ).trans (MoorePathFrom.toMoorePath_mk γ.val γ.property).symm

namespace Fiber

variable (a b) in
/-- **The fibre of the replacement of the inclusion of a point**: a point `(a, γ)` of the fibre over
`b` of the Moore-path replacement of the inclusion of `a` is the Moore path `γ` from `a` to `b`. -/
def homeomorphPathsBetween :
    Fiber (ContinuousMap.subtypeVal ({a} : Set B)) b ≃ₜ MoorePathBetween B a b where
  toFun x := ⟨x.val.path, source_path_mem x.val, x.target_path_val⟩
  invFun γ := mk' ((homeomorphPathsFrom {a}).symm (MoorePathBetween.toMoorePathFrom a b γ)) <|
    (congrArg MoorePath.target ((path_homeomorphPathsFrom_symm_singleton _).trans
      (MoorePathBetween.toMoorePath_toMoorePathFrom γ))).trans γ.target
  left_inv x := ext (MooreReplacement.ext (Subsingleton.elim _ _) (by simp))
  right_inv γ := MoorePathBetween.ext (by simp)
  continuous_toFun := (continuous_path.comp continuous_val).subtype_mk _
  continuous_invFun := continuous_mk' ((homeomorphPathsFrom {a}).symm.continuous.comp
    (MoorePathBetween.toMoorePathFrom a b).continuous) _

@[simp]
theorem toMoorePath_homeomorphPathsBetween (x : Fiber (ContinuousMap.subtypeVal {a}) b) :
    (homeomorphPathsBetween a b x).toMoorePath = x.val.path :=
  MoorePathBetween.toMoorePath_mk _ _

@[simp]
theorem path_val_homeomorphPathsBetween_symm (γ : MoorePathBetween B a b) :
    ((homeomorphPathsBetween a b).symm γ).val.path = γ.toMoorePath := by
  simp [homeomorphPathsBetween]

/-- The identification of the fibre with the Moore paths from `a` to `b` is equivariant for the
loops at `b`, acting on both from behind. -/
theorem homeomorphPathsBetween_op_smul (ω : MooreLoopSpace B b)
    (x : Fiber (ContinuousMap.subtypeVal {a}) b) :
    homeomorphPathsBetween a b (op ω • x) = op ω • homeomorphPathsBetween a b x :=
  MoorePathBetween.ext (by simp [op_smul_eq_act])

/-- The inverse identification is equivariant for the loops at `b`. -/
theorem homeomorphPathsBetween_symm_op_smul (ω : MooreLoopSpace B b) (γ : MoorePathBetween B a b) :
    (homeomorphPathsBetween a b).symm (op ω • γ) = op ω • (homeomorphPathsBetween a b).symm γ :=
  (homeomorphPathsBetween a b).symm_apply_eq.2 <| by
    rw [homeomorphPathsBetween_op_smul, Homeomorph.apply_symm_apply]

/-- Read through the identifications with Moore paths, appending a path from `b` to a point of the
fibre over `b` is concatenation of paths. -/
theorem homeomorphPathsFrom_appendFrom (x : Fiber (ContinuousMap.subtypeVal {a}) b)
    (δ : MoorePathFrom B b) :
    (homeomorphPathsFrom {a} (x.appendFrom δ) : MoorePathFrom B a) =
      MoorePathBetween.transFrom a b (homeomorphPathsBetween a b x, δ) :=
  MoorePathFrom.ext (by simp)

end Fiber

end TauCeti.MooreReplacement
