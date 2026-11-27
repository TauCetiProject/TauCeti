/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Geometry.ScatteringDiagram.Path.Product
public import Mathlib.Algebra.Group.Subgroup.Ker
import Mathlib.Algebra.Group.Equiv.Opposite
import TauCeti.Combinatorics.Quiver.PathWeight

/-!
# Lift defects for wall transport

Suppose chosen vertex lifts project to transports from a common basepoint. A segment
then has a corrected transport in the projection kernel. Corrected transports multiply
along paths by cancellation of all interior lifts. A homomorphism from the kernel to an
additive coefficient group turns the corrected path product into the sum of the local
defects. At a vertex with identity lift the formula evaluates the original loop product.
-/

public section

noncomputable section

namespace TauCeti.WallComplement

variable {V ι G K : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [Finite ι]
  [Group G] [Group K] {W : ι → Set V}
  (ν : ι → V →ₗ[ℝ] ℝ) (labels : ι → G)
  (hc : ∀ i j, affineSpan ℝ (W i) = affineSpan ℝ (W j) → Commute (labels i) (labels j))
  (f : G →* K) (t : WallComplement W → G)

/-- Corrected transport for a segment whose projection carries one vertex lift to the
other, as an element of the kernel of the projection. -/
def segmentDefect
    {x y : WallComplement W} (e : x ⟶ y)
    (ht : f (segmentPathProduct ν labels hc e) * f (t x) = f (t y)) : f.ker :=
  ⟨(t y)⁻¹ * segmentPathProduct ν labels hc e * t x, by
    rw [MonoidHom.mem_ker, map_mul, map_mul, map_inv, mul_assoc, ht, inv_mul_cancel]⟩

/-- The underlying corrected transport is obtained by inserting the two endpoint lifts. -/
@[simp]
theorem coe_segmentDefect
    {x y : WallComplement W} (e : x ⟶ y)
    (ht : f (segmentPathProduct ν labels hc e) * f (t x) = f (t y)) :
    (segmentDefect ν labels hc f t e ht : G) = (t y)⁻¹ * segmentPathProduct ν labels hc e * t x :=
  (rfl)

end TauCeti.WallComplement

namespace Quiver.Path

open TauCeti WallComplement

variable {V ι G K : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [Finite ι]
  [Group G] [Group K] {W : ι → Set V}
  (ν : ι → V →ₗ[ℝ] ℝ) (labels : ι → G)
  (hc : ∀ i j, affineSpan ℝ (W i) = affineSpan ℝ (W j) → Commute (labels i) (labels j))
  (f : G →* K) (t : WallComplement W → G)
  (ht : ∀ {x y : WallComplement W} (e : x ⟶ y),
    f (segmentPathProduct ν labels hc e) * f (t x) = f (t y))
  {x y z : WallComplement W}

/-- The product of the kernel-valued segment defects along a path. Later segment
defects act on the left. -/
def wallPathDefect (p : AdmissiblePLPath x y) : f.ker :=
  MulOpposite.unop <| p.weight fun e => MulOpposite.op (segmentDefect ν labels hc f t e (ht e))

/-- The kernel path defect is the path weight of opposite-group segment defects. -/
theorem wallPathDefect_eq_unop_weight (p : AdmissiblePLPath x y) :
    p.wallPathDefect ν labels hc f t ht =
      MulOpposite.unop (p.weight fun e =>
        MulOpposite.op (segmentDefect ν labels hc f t e (ht e))) :=
  (rfl)

/-- The empty path has identity defect. -/
@[simp]
theorem wallPathDefect_nil :
    (Quiver.Path.nil : AdmissiblePLPath x x).wallPathDefect ν labels hc f t ht = 1 := by
  simp only [wallPathDefect_eq_unop_weight, weight_nil, MulOpposite.unop_one]

/-- The last segment defect multiplies the preceding path defect on the left. -/
@[simp]
theorem wallPathDefect_cons (p : AdmissiblePLPath x y) (e : y ⟶ z) :
    (p.cons e).wallPathDefect ν labels hc f t ht =
      segmentDefect ν labels hc f t e (ht e) * p.wallPathDefect ν labels hc f t ht := by
  simp only [wallPathDefect_eq_unop_weight, weight_cons, MulOpposite.unop_mul, MulOpposite.unop_op]

/-- A one-segment path has the defect of that segment. -/
@[simp]
theorem wallPathDefect_toPath (e : x ⟶ y) :
    e.toPath.wallPathDefect ν labels hc f t ht = segmentDefect ν labels hc f t e (ht e) := by
  simp [Quiver.Hom.toPath]

/-- In a composed path, the second path's defect multiplies the first on the left. -/
@[simp]
theorem wallPathDefect_comp (p : AdmissiblePLPath x y) (q : AdmissiblePLPath y z) :
    (p.comp q).wallPathDefect ν labels hc f t ht =
      q.wallPathDefect ν labels hc f t ht * p.wallPathDefect ν labels hc f t ht := by
  simp only [wallPathDefect_eq_unop_weight, weight_comp, MulOpposite.unop_mul]

/-- Multiplying the segment defects cancels the lifts of all interior vertices. -/
@[simp]
theorem coe_wallPathDefect (p : AdmissiblePLPath x y) :
    (p.wallPathDefect ν labels hc f t ht : G) =
      (t y)⁻¹ * p.wallPathProduct ν labels hc * t x := by
  -- The opposite subtype map is the subtype coercion after returning to the ambient group.
  have hcoe (g : f.kerᵐᵒᵖ) : (g.unop : G) = (MonoidHom.op f.ker.subtype g).unop :=
    (rfl)
  rw [wallPathDefect_eq_unop_weight, hcoe, map_weight, wallPathProduct_eq_unop_weight]
  let lifts (v : WallComplement W) : Gᵐᵒᵖ := (MulOpposite.op (t v))⁻¹
  let w : ∀ {a b : WallComplement W}, (a ⟶ b) → Gᵐᵒᵖ :=
    fun e => MulOpposite.op (segmentPathProduct ν labels hc e)
  -- Reversing multiplication puts the source factor first in the arrow weight.
  have hweights : (fun {a b : WallComplement W} (e : a ⟶ b) =>
      MonoidHom.op f.ker.subtype (MulOpposite.op (segmentDefect ν labels hc f t e (ht e)))) =
      (fun {a b} e => (lifts a)⁻¹ * w e * lifts b) := by
    funext a b e
    apply MulOpposite.unop_injective
    simp [lifts, w, MonoidHom.op_apply_apply, MulOpposite.unop_mul, mul_assoc]
  rw [hweights, weight_inv_mul_mul]
  simp [lifts, w, MulOpposite.unop_mul, mul_assoc]

/-- A normalized lift identifies the path defect of a loop with its uncorrected
transport in the ambient group. -/
theorem coe_wallPathDefect_loop (p : AdmissiblePLPath x x) (hx : t x = 1) :
    (p.wallPathDefect ν labels hc f t ht : G) = p.wallPathProduct ν labels hc := by
  simp [hx]

/-- An additive evaluation of the kernel product is the sum of the evaluated
segment defects. In particular this applies to the central logarithm. -/
theorem log_wallPathDefect_eq_addWeight {A : Type*} [AddCommMonoid A]
    (log : f.ker →* Multiplicative A) (p : AdmissiblePLPath x y) :
    (log (p.wallPathDefect ν labels hc f t ht)).toAdd =
      p.addWeight fun e => (log (segmentDefect ν labels hc f t e (ht e))).toAdd := by
  let evaluate : f.kerᵐᵒᵖ →* Multiplicative A :=
    MulOpposite.opMulEquiv.symm.toMonoidHom.comp (MonoidHom.op log)
  apply congrArg Multiplicative.toAdd
  calc
    log (p.wallPathDefect ν labels hc f t ht) =
        evaluate (p.weight fun e => MulOpposite.op (segmentDefect ν labels hc f t e (ht e))) := by
      rw [wallPathDefect_eq_unop_weight]
      simp [evaluate, MonoidHom.op_apply_apply]
    _ = p.weight (fun e => evaluate (MulOpposite.op (segmentDefect ν labels hc f t e (ht e)))) :=
      p.map_weight evaluate _
    _ = Multiplicative.ofAdd (p.addWeight fun e =>
        (log (segmentDefect ν labels hc f t e (ht e))).toAdd) :=
      p.weight_ofAdd (M := A) fun e => (log (segmentDefect ν labels hc f t e (ht e))).toAdd

end Quiver.Path
