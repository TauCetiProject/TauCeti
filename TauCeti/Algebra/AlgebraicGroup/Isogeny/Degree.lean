/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Isogeny.Basic
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Quotient.Finrank

/-!
# Isogenies of degree one

An isogeny of affine group schemes over a field is an isomorphism exactly when its
scheme-theoretic kernel has coordinate algebra of dimension one. No smoothness or
reducedness assumption is needed: dimension measures the whole kernel scheme.
-/

public section

open CategoryTheory

namespace TauCeti.CommHopfAlgCat.IsIsogeny

universe u v

variable {k : Type u} [Field k] {H K : _root_.CommHopfAlgCat.{v} k} {f : H ⟶ K}

/-- An affine isogeny over a field is an isomorphism exactly when its kernel has degree one,
where degree is the dimension of the kernel's coordinate algebra. -/
theorem isIso_iff_finrank_kernelCoordinate_eq_one (hf : IsIsogeny f) :
    IsIso f ↔ Module.finrank k (quotient K (kernelHopfIdeal f)) = 1 := by
  rw [hf.isIso_iff_kernelHopfIdeal_eq_augmentation, HopfIdeal.finrank_quotient_eq_one_iff]

end TauCeti.CommHopfAlgCat.IsIsogeny
