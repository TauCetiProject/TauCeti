/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.FiberBundle.Principal.Equiv
public import TauCeti.Topology.FiberBundle.Pullback

/-!
# Pullbacks of principal-bundle equivalences

A fibrewise equivariant equivalence pulls back along any map of bases. Its continuity follows
from the universal property of the pullback topology. In particular this restricts equivalences
to subsets of the base, by taking the map to be `Subtype.val`.
-/

public section

open Bundle

namespace TauCeti.PrincipalBundle.Equiv

variable {B B' G : Type*} [Group G] [TopologicalSpace B']
  {P Q R : B → Type*}
  [TopologicalSpace (TotalSpace G P)] [TopologicalSpace (TotalSpace G Q)]
  [TopologicalSpace (TotalSpace G R)]
  [∀ b, MulAction Gᵐᵒᵖ (P b)] [∀ b, MulAction Gᵐᵒᵖ (Q b)]
  [∀ b, MulAction Gᵐᵒᵖ (R b)]

/-- Pull back an equivariant bundle equivalence along a map of bases. No continuity of the base
map is needed for continuity of the induced maps of pullback total spaces. -/
def pullback (ψ : PrincipalBundle.Equiv G P Q) (f : B' → B) :
    PrincipalBundle.Equiv G (f *ᵖ P) (f *ᵖ Q) where
  toEquiv x := ψ.toEquiv (f x)
  continuous_toFun := Pullback.continuous_fiberwise (Φ := fun b ↦ ψ.toEquiv b)
    ψ.continuous_toFun f
  continuous_invFun := Pullback.continuous_fiberwise (Φ := fun b ↦ (ψ.toEquiv b).symm)
    ψ.continuous_invFun f
  map_smul x p g := ψ.map_smul (f x) p g

/-- On each fibre, pullback uses the original equivalence at the image base point. -/
theorem pullback_toEquiv (ψ : PrincipalBundle.Equiv G P Q) (f : B' → B) (x : B') :
    (ψ.pullback f).toEquiv x = ψ.toEquiv (f x) :=
  (rfl)

@[simp]
theorem pullback_refl (f : B' → B) :
    (refl G P).pullback f = refl G (f *ᵖ P) :=
  ext fun _ _ ↦ rfl

@[simp]
theorem pullback_symm (ψ : PrincipalBundle.Equiv G P Q) (f : B' → B) :
    ψ.symm.pullback f = (ψ.pullback f).symm :=
  ext fun _ _ ↦ rfl

@[simp]
theorem pullback_trans (ψ : PrincipalBundle.Equiv G P Q) (φ : PrincipalBundle.Equiv G Q R)
    (f : B' → B) :
    (ψ.trans φ).pullback f = (ψ.pullback f).trans (φ.pullback f) :=
  ext fun _ _ ↦ rfl

end TauCeti.PrincipalBundle.Equiv
