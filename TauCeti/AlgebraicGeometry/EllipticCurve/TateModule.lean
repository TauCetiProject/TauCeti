/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.Torsion.TateModule
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.MulByInt.KernelCard

/-!
# The profinite topology on an elliptic curve's Tate module

The torsion levels of an elliptic curve are finite.  Consequently the inverse-limit topology on
its Tate module is compact, Hausdorff, and totally disconnected.  Hausdorffness and total
disconnectedness hold for every `TauCeti.TateModule`; this file supplies the elliptic-curve input
needed for compactness.
-/

public section

noncomputable section

open TauCeti

namespace WeierstrassCurve

variable {K : Type*} [Field K] (W : WeierstrassCurve K) [W.IsElliptic]

open scoped Classical in
/-- The Tate module of an elliptic curve at a nonzero natural number is compact.  It is a closed
subgroup of the product of the finite torsion groups `E[p^n]`. -/
noncomputable instance instCompactSpaceTateModule (p : ℕ) [NeZero p] :
    CompactSpace (TateModule p W.toAffine.Point) := by
  let _ (n : ℕ) : Finite (TateModuleLevel p W.toAffine.Point n) :=
    W.finite_torsionBy (by exact_mod_cast pow_ne_zero n (NeZero.ne p))
  infer_instance

end WeierstrassCurve

end
