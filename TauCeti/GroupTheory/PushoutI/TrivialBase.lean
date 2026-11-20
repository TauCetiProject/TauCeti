/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.PushoutI
public import TauCeti.GroupTheory.CoprodI

/-!
# Amalgamated products over a trivial monoid are free products

The amalgamated product `Monoid.PushoutI φ` of a family of monoids `G i` along maps
`φ i : H →* G i` identifies the images of `H` in the factors. When `H` is trivial there is
nothing to identify, and the amalgamated product is the free product `Monoid.CoprodI G`. For a
family of two monoids indexed by `Bool` this is the binary free product
`Monoid.Coprod (G false) (G true)`: an amalgam `A ∗_C B` with `C = 1` is the free product
`A ∗ B`.

## Main definitions

* `Monoid.PushoutI.equivCoprodI`: `PushoutI φ ≃* CoprodI G` when the base monoid is trivial.
* `Monoid.PushoutI.equivCoprod`: `PushoutI φ ≃* Coprod (G false) (G true)` for a family indexed
  by `Bool` over a trivial base monoid.

## References

* J.-P. Serre, *Trees*, Chapter I, §1.1.
-/

public section

namespace Monoid.PushoutI

section CoprodI

variable {ι : Type*} {G : ι → Type*} {H : Type*} [∀ i, Monoid (G i)] [Monoid H]
  (φ : ∀ i, H →* G i) [Subsingleton H]

/-- The amalgamated product of a family of monoids over a trivial monoid is their free product:
the canonical map `Monoid.PushoutI.ofCoprodI` from the free product is an isomorphism. -/
def equivCoprodI : PushoutI φ ≃* CoprodI G :=
  MonoidHom.toMulEquiv
    (lift (fun _ => CoprodI.of) 1 fun i => by
      ext h
      simp [Subsingleton.elim h 1])
    ofCoprodI
    (hom_ext (fun i => by ext; simp) (by ext h; simp [Subsingleton.elim h 1]))
    (by ext; simp)

variable {φ}

@[simp]
theorem equivCoprodI_of (i : ι) (g : G i) : equivCoprodI φ (of i g) = CoprodI.of g := by
  simp [equivCoprodI]

@[simp]
theorem equivCoprodI_symm_of (i : ι) (g : G i) : (equivCoprodI φ).symm (CoprodI.of g) = of i g :=
  ofCoprodI_of ..

@[simp]
theorem equivCoprodI_base (h : H) : equivCoprodI φ (base φ h) = 1 := by
  simp [equivCoprodI]

variable (φ) in
theorem coe_equivCoprodI_symm : ⇑(equivCoprodI φ).symm = ofCoprodI :=
  (rfl)

end CoprodI

section Coprod

variable {G : Bool → Type*} {H : Type*} [∀ i, Monoid (G i)] [Monoid H]
  (φ : ∀ i, H →* G i) [Subsingleton H]

/-- The amalgamated product of two monoids over a trivial monoid is their free product: the
inclusions of the factors `G false` and `G true` correspond to `Monoid.Coprod.inl` and
`Monoid.Coprod.inr`. -/
def equivCoprod : PushoutI φ ≃* Coprod (G false) (G true) :=
  (equivCoprodI φ).trans (CoprodI.boolEquivCoprod G)

variable {φ}

@[simp]
theorem equivCoprod_of_false (g : G false) : equivCoprod φ (of false g) = Coprod.inl g := by
  simp [equivCoprod]

@[simp]
theorem equivCoprod_of_true (g : G true) : equivCoprod φ (of true g) = Coprod.inr g := by
  simp [equivCoprod]

@[simp]
theorem equivCoprod_base (h : H) : equivCoprod φ (base φ h) = 1 := by
  simp [equivCoprod]

@[simp]
theorem equivCoprod_symm_inl (g : G false) :
    (equivCoprod φ).symm (Coprod.inl g) = of false g := by
  simp [equivCoprod]

@[simp]
theorem equivCoprod_symm_inr (g : G true) :
    (equivCoprod φ).symm (Coprod.inr g) = of true g := by
  simp [equivCoprod]

end Coprod

end Monoid.PushoutI
