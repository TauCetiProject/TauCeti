/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.PathSpace.Moore.Replacement.Append

/-!
# The Moore-path replacement of the inclusion of a point

Let `a` be a point of `B`, included in `B` by the constant map `E → B` on a one-point space `E`.
A point `(e, γ)` of the total space `E'` of its Moore-path replacement is determined by the Moore
path `γ` from `a`, so `E'` is the space `P_a B` of Moore paths from `a`
(`TauCeti.MooreReplacement.constHomeomorph`), and its fibre `F'_b` over `b` is the space of Moore
paths from `a` to `b` (`TauCeti.MooreReplacement.Fiber.constHomeomorph`). Read through these
identifications, the loops at `b` act on the fibre by concatenation behind
(`TauCeti.MooreReplacement.Fiber.constHomeomorph_op_smul`), and appending a Moore path from `b` to
a point of the fibre is concatenation of paths
(`TauCeti.MooreReplacement.Fiber.constHomeomorph_appendFrom`).

## Main definitions

* `TauCeti.MooreReplacement.constHomeomorph E a`: the homeomorphism `E' ≃ₜ P_a B`.
* `TauCeti.MooreReplacement.Fiber.constHomeomorph E a b`: the homeomorphism of the fibre over
  `b` with the space of Moore paths from `a` to `b`.

## Main results

* `TauCeti.MooreReplacement.Fiber.constHomeomorph_op_smul`: the identification of the fibre is
  equivariant for the loops at `b`.
* `TauCeti.MooreReplacement.Fiber.constHomeomorph_appendFrom`: appending a path from `b` is
  concatenation.
-/

public noncomputable section

open MulOpposite

namespace TauCeti.MooreReplacement

variable (E : Type*) {B : Type*} [TopologicalSpace E] [Unique E] [TopologicalSpace B] (a : B)
  {b : B}

/-- **The replacement of the inclusion of a point is the space of Moore paths from it**: for a
one-point space `E`, a point `(e, γ)` of the total space of the Moore-path replacement of the
constant map `E → B` at `a` is the Moore path `γ` from `a`. -/
def constHomeomorph : MooreReplacement (.const E a) ≃ₜ MoorePathFrom B a where
  toFun x := ⟨x.path, x.source_path.trans (ContinuousMap.const_apply a _)⟩
  invFun γ := mk default γ.toMoorePath (γ.source.trans (ContinuousMap.const_apply a _).symm)
  left_inv x := MooreReplacement.ext (Subsingleton.elim _ _) (by simp)
  right_inv γ := MoorePathFrom.ext (by simp)
  continuous_toFun := continuous_path.subtype_mk _
  continuous_invFun := continuous_mk continuous_const MoorePathFrom.continuous_toMoorePath _

variable {E a}

@[simp]
theorem toMoorePath_constHomeomorph (x : MooreReplacement (.const E a)) :
    (constHomeomorph E a x).toMoorePath = x.path :=
  MoorePathFrom.toMoorePath_mk _ _

@[simp]
theorem path_constHomeomorph_symm (γ : MoorePathFrom B a) :
    ((constHomeomorph E a).symm γ).path = γ.toMoorePath := by
  simp [constHomeomorph]

namespace Fiber

variable (E a b) in
/-- **The fibre of the replacement of the inclusion of a point**: for a one-point space `E`, a point
`(e, γ)` of the fibre over `b` of the Moore-path replacement of the constant map `E → B` at `a` is
the Moore path `γ` from `a` to `b`. -/
def constHomeomorph : Fiber (.const E a) b ≃ₜ MoorePathBetween B a b where
  toFun x := ⟨x.val.path, x.val.source_path.trans (ContinuousMap.const_apply a _),
    x.target_path_val⟩
  invFun γ := mk' ((MooreReplacement.constHomeomorph E a).symm
    (MoorePathBetween.toMoorePathFrom a b γ)) <| (congrArg MoorePath.target
      ((path_constHomeomorph_symm _).trans (MoorePathBetween.toMoorePath_toMoorePathFrom γ))).trans
        γ.target
  left_inv x := ext (MooreReplacement.ext (Subsingleton.elim _ _) (by simp))
  right_inv γ := MoorePathBetween.ext (by simp)
  continuous_toFun := (continuous_path.comp continuous_val).subtype_mk _
  continuous_invFun := continuous_mk' ((MooreReplacement.constHomeomorph E a).symm.continuous.comp
    (MoorePathBetween.toMoorePathFrom a b).continuous) _

@[simp]
theorem toMoorePath_constHomeomorph (x : Fiber (.const E a) b) :
    (constHomeomorph E a b x).toMoorePath = x.val.path :=
  MoorePathBetween.toMoorePath_mk _ _

@[simp]
theorem path_val_constHomeomorph_symm (γ : MoorePathBetween B a b) :
    ((constHomeomorph E a b).symm γ).val.path = γ.toMoorePath := by
  simp [constHomeomorph]

/-- The identification of the fibre with the Moore paths from `a` to `b` is equivariant for the
loops at `b`, acting on both from behind. -/
theorem constHomeomorph_op_smul (ω : MooreLoopSpace B b) (x : Fiber (.const E a) b) :
    constHomeomorph E a b (op ω • x) = op ω • constHomeomorph E a b x :=
  MoorePathBetween.ext (by simp [op_smul_eq_act])

/-- The inverse identification is equivariant for the loops at `b`. -/
theorem constHomeomorph_symm_op_smul (ω : MooreLoopSpace B b) (γ : MoorePathBetween B a b) :
    (constHomeomorph E a b).symm (op ω • γ) = op ω • (constHomeomorph E a b).symm γ :=
  (constHomeomorph E a b).symm_apply_eq.2 <| by
    rw [constHomeomorph_op_smul, Homeomorph.apply_symm_apply]

/-- Read through the identifications with Moore paths, appending a path from `b` to a point of the
fibre over `b` is concatenation of paths. -/
theorem constHomeomorph_appendFrom (x : Fiber (.const E a) b) (δ : MoorePathFrom B b) :
    MooreReplacement.constHomeomorph E a (x.appendFrom δ) =
      MoorePathBetween.transFrom a b (constHomeomorph E a b x, δ) :=
  MoorePathFrom.ext (by simp)

end Fiber

end TauCeti.MooreReplacement
