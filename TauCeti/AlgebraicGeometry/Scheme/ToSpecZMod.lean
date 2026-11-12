/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.Algebra.Ring.ULift
public import Mathlib.Data.ZMod.Basic

/-!
# The structure morphism to `Spec ℤ/n`

A scheme `X` in which `n` vanishes, that is, with `(n : Γ(X, ⊤)) = 0`, is a scheme over
`Spec ℤ/n`: the ring map `ℤ/n → Γ(X, ⊤)` gives a morphism `X ⟶ Spec ℤ/n`. It is the only morphism
from `X` to `Spec ℤ/n`, since there is at most one ring map out of `ℤ/n`. For a prime `p` this is
the structure morphism `X ⟶ Spec 𝔽_p` of a scheme in characteristic `p`.

`ℤ/n` is lifted to universe `u` by `ULift`, so that its spectrum is a scheme in the universe of
`X`.

## Main definitions

* `AlgebraicGeometry.Scheme.toSpecZMod`: the morphism `X ⟶ Spec ℤ/n` of a scheme in which `n`
  vanishes.

## Main results

* `AlgebraicGeometry.Scheme.subsingleton_hom_spec_zmod`: there is at most one morphism
  `X ⟶ Spec ℤ/n`.
-/

public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme

variable (X : Scheme.{u}) {n : ℕ}

/-- The morphism `X ⟶ Spec ℤ/n` of a scheme in which `n` vanishes, induced by the ring map
`ℤ/n → Γ(X, ⊤)`. For a prime `p` it is the structure morphism `X ⟶ Spec 𝔽_p`. -/
noncomputable def toSpecZMod (hX : (n : Γ(X, ⊤)) = 0) : X ⟶ Spec (.of (ULift.{u} (ZMod n))) :=
  X.toSpecΓ ≫ Spec.map (CommRingCat.ofHom <|
    (ZMod.castHom (ringChar.dvd hX) Γ(X, ⊤)).comp ULift.ringEquiv.toRingHom)

/-- There is at most one morphism from a scheme to `Spec ℤ/n`, since there is at most one ring map
out of `ℤ/n`. In particular every such morphism is `AlgebraicGeometry.Scheme.toSpecZMod`. -/
instance subsingleton_hom_spec_zmod : Subsingleton (X ⟶ Spec (.of (ULift.{u} (ZMod n)))) := by
  refine ⟨fun f g ↦ ext_of_isAffine ?_⟩
  rw [← cancel_epi (ΓSpecIso (.of (ULift.{u} (ZMod n)))).inv]
  generalize (ΓSpecIso _).inv ≫ f.appTop = φ, (ΓSpecIso _).inv ≫ g.appTop = ψ
  ext ⟨x⟩
  exact DFunLike.congr_fun (RingHom.ext_zmod (φ.hom.comp ULift.ringEquiv.symm.toRingHom)
    (ψ.hom.comp ULift.ringEquiv.symm.toRingHom)) x

end AlgebraicGeometry.Scheme
