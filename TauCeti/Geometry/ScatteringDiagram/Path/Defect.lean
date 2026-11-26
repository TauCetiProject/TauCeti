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

namespace Quiver.Path

variable {V : Type*} [Quiver V] {G : Type*} [Group G]

/-- Changing each arrow weight by the vertex factors on its two ends changes the path
weight by the corresponding factors at its endpoints. -/
private theorem weight_vertex_conj (t : V → G) (w : ∀ {x y : V}, (x ⟶ y) → G)
    {x y : V} (p : Quiver.Path x y) :
    p.weight (fun {a b} e => (t a)⁻¹ * w e * t b) = (t x)⁻¹ * p.weight w * t y := by
  induction p with
  | nil => simp
  | cons p e ih =>
    rw [weight_cons, weight_cons, ih]
    simp [mul_assoc]

end Quiver.Path

namespace TauCeti.WallComplement

variable {V ι G K : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [Finite ι]
  [Group G] [Group K] {W : ι → Set V}
  (ν : ι → V →ₗ[ℝ] ℝ) (labels : ι → G)
  (hc : ∀ i j, affineSpan ℝ (W i) = affineSpan ℝ (W j) → Commute (labels i) (labels j))
  (f : G →* K) (t : WallComplement W → G)

/-- Corrected transport for a segment whose projection carries one vertex lift to the
other, as an element of the kernel of the projection. -/
def segmentDefect
    (ht : ∀ {x y : WallComplement W} (e : x ⟶ y),
      f (segmentPathProduct ν labels hc e) * f (t x) = f (t y))
    {x y : WallComplement W} (e : x ⟶ y) : f.ker :=
  ⟨(t y)⁻¹ * segmentPathProduct ν labels hc e * t x, by
    rw [MonoidHom.mem_ker, map_mul, map_mul, map_inv, mul_assoc, ht e, inv_mul_cancel]⟩

/-- The underlying corrected transport is obtained by inserting the two endpoint lifts. -/
@[simp]
theorem coe_segmentDefect
    (ht : ∀ {x y : WallComplement W} (e : x ⟶ y),
      f (segmentPathProduct ν labels hc e) * f (t x) = f (t y))
    {x y : WallComplement W} (e : x ⟶ y) :
    (segmentDefect ν labels hc f t ht e : G) = (t y)⁻¹ * segmentPathProduct ν labels hc e * t x :=
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
  {x y : WallComplement W}

/-- The product of the kernel-valued segment defects along a path. Later segment
defects act on the left. -/
def wallPathDefect (p : AdmissiblePLPath x y) : f.ker :=
  MulOpposite.unop <| p.weight fun e => MulOpposite.op (segmentDefect ν labels hc f t ht e)

/-- Multiplying the segment defects cancels the lifts of all interior vertices. -/
@[simp]
theorem coe_wallPathDefect (p : AdmissiblePLPath x y) :
    (p.wallPathDefect ν labels hc f t ht : G) =
      (t y)⁻¹ * p.wallPathProduct ν labels hc * t x := by
  change MulOpposite.unop (MonoidHom.op f.ker.subtype (p.weight
    (fun e => MulOpposite.op (segmentDefect ν labels hc f t ht e)))) = _
  rw [map_weight]
  change MulOpposite.unop (p.weight (fun {a b} e =>
    MulOpposite.op ((t b)⁻¹ * segmentPathProduct ν labels hc e * t a))) = _
  rw [p.wallPathProduct_eq_unop_weight ν labels hc]
  let lifts (v : WallComplement W) : Gᵐᵒᵖ := (MulOpposite.op (t v))⁻¹
  let w : ∀ {a b : WallComplement W}, (a ⟶ b) → Gᵐᵒᵖ :=
    fun e => MulOpposite.op (segmentPathProduct ν labels hc e)
  have he : (fun {a b : WallComplement W} (e : a ⟶ b) =>
      MulOpposite.op ((t b)⁻¹ * segmentPathProduct ν labels hc e * t a)) =
      (fun {a b} e => (lifts a)⁻¹ * w e * lifts b) := by
    funext a b e
    apply MulOpposite.unop_injective
    simp [lifts, w, MulOpposite.unop_mul, mul_assoc]
  rw [he, weight_vertex_conj]
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
      p.addWeight fun e => (log (segmentDefect ν labels hc f t ht e)).toAdd := by
  induction p with
  | nil => simp [wallPathDefect]
  | cons p e ih =>
    simp only [wallPathDefect, weight_cons, MulOpposite.unop_mul, MulOpposite.unop_op,
      map_mul, addWeight_cons]
    change (log (segmentDefect ν labels hc f t ht e)).toAdd +
      (log (p.wallPathDefect ν labels hc f t ht)).toAdd = _
    rw [ih, add_comm]

end Quiver.Path
