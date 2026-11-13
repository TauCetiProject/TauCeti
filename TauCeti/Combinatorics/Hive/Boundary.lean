/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Hive.Basic

/-!
# Ambient boundaries and additive gauge invariance

The clockwise boundary operator on arbitrary lattice labellings is unchanged by
constant translation. Normalization and translated subtriangle restriction therefore
have the same boundary as the underlying unnormalized labellings. Rotation cycles
the three sides.

The conventions follow Knutson–Tao, *The honeycomb model of GLₙ(ℂ) tensor
products I*, Appendix 2.
-/

public section

namespace TauCeti.Hive

variable {n : ℕ} {R : Type*} [AddCommGroup R]

section Ambient

variable (S : Type*) [Semiring S] [Module S R]

/-- The function underlying the ambient boundary linear map. -/
@[simp] theorem coe_boundaryLinear :
    ⇑(boundaryLinear S n R) = fun f s i =>
      f (Vertex.edgePoint n s i.succ) - f (Vertex.edgePoint n s i.castSucc) := by
  funext f s i
  exact boundaryLinear_apply S f s i

/-- Rotating a labelling cycles its clockwise boundary sides. -/
@[simp] theorem boundaryLinear_rotate (f : Vertex n → R) :
    boundaryLinear S n R (fun p => f p.rotate) = fun s => boundaryLinear S n R f (s + 1) := by
  funext s i
  simp only [boundaryLinear_apply, Vertex.rotate_edgePoint]

@[simp] theorem boundaryLinear_const (c : R) :
    boundaryLinear S n R (fun _ => c) = 0 := by ext s i; simp

/-- Boundary differences do not depend on the additive gauge. -/
@[simp] theorem boundaryLinear_add_const (f : Vertex n → R) (c : R) :
    boundaryLinear S n R (fun p => f p + c) = boundaryLinear S n R f := by ext s i; simp

@[simp] theorem boundaryLinear_const_add (c : R) (f : Vertex n → R) :
    boundaryLinear S n R (fun p => c + f p) = boundaryLinear S n R f := by ext s i; simp

@[simp] theorem boundaryLinear_sub_const (f : Vertex n → R) (c : R) :
    boundaryLinear S n R (fun p => f p - c) = boundaryLinear S n R f := by ext s i; simp

/-- The ambient boundary commutes with any distributive scalar action. -/
theorem boundaryLinear_smul {K : Type*} [Monoid K] [DistribMulAction K R]
    (c : K) (f : Vertex n → R) :
    boundaryLinear S n R (c • f) = c • boundaryLinear S n R f := by
  ext s i
  simp only [boundaryLinear_apply, Pi.smul_apply, smul_sub]

end Ambient

section Ordered

variable [Preorder R] [IsOrderedAddMonoid R]

/-- Normalization leaves the clockwise boundary unchanged. -/
@[simp] theorem boundary_ofRhombusConcave (f : Vertex n → R) (hf : IsRhombusConcave f) :
    (ofRhombusConcave f hf).boundary = boundaryLinear ℤ n R f := by
  ext s i
  simp [boundary_apply]

/-- A subtriangle has the boundary of its translated, unnormalized labelling. -/
@[simp] theorem boundary_subtriangle {m : ℕ} (h : Hive (m + n) R) (p : Vertex m) :
    (h.subtriangle p).boundary = boundaryLinear ℤ n R (fun q => h (p.add q)) := by
  ext s i
  simp [boundary_apply]

end Ordered

end TauCeti.Hive
