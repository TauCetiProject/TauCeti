/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.GaloisRepresentation.TateTwist
public import TauCeti.RingTheory.RootsOfUnity.PadicTateTwist
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import TauCeti.Topology.Algebra.Module.AutomaticContinuity

/-!
# `ℤ_ℓ(1)` as the Tate module of roots of unity

Let `F` be a field and `ℓ` a prime. Tau Ceti's `PadicTateTwist ℓ F^alg` is the inverse limit of the
groups `μ_{ℓ^n}(F^alg)` of roots of unity, with its inverse-limit topology, and `G_F` acts on it
componentwise (`TauCeti.PadicTateTwist.galoisRepresentation`), jointly continuously. This file
packages this action as a continuous representation
`TauCeti.ContinuousRep.padicTateTwist ℓ F` of `G_F` over `ℤ_ℓ`, and compares it with the line
`TauCeti.ContinuousRep.cyclotomicLine ℓ F = ℤ_ℓ(χ_ℓ)`.

Since `G_F` acts on `PadicTateTwist ℓ F^alg` by multiplication by the cyclotomic character, every
`ℤ_ℓ`-linear equivalence `ℤ_ℓ ≃ PadicTateTwist ℓ F^alg` is `G_F`-equivariant. It is also a
homeomorphism, as a finitely generated Hausdorff topological module over the compact ring `ℤ_ℓ`
carries the module topology (`TauCeti.isModuleTopology_of_finite_of_compactSpace`), so it is an
isomorphism of continuous representations (`TauCeti.ContinuousRep.Iso.ofEquiv`)
(`TauCeti.ContinuousRep.cyclotomicLineIsoPadicTateTwist`). Such an equivalence is the choice of a
compatible system of primitive `ℓ^n`-th roots of unity, the levels of the generator. When
`ℓ ≠ char F` such equivalences exist, so `ℤ_ℓ(1) ≅ PadicTateTwist ℓ F^alg`
(`TauCeti.ContinuousRep.nonempty_iso_cyclotomicLine_padicTateTwist`).

The hypothesis `ℓ ≠ char F` is needed: in characteristic `ℓ` there are no nontrivial `ℓ`-th roots
of unity, so `PadicTateTwist ℓ F^alg = 0` (`TauCeti.PadicTateTwist.subsingleton_of_expChar`), while
`ℤ_ℓ(1)` is a nonzero line.

## Main definitions

* `TauCeti.ContinuousRep.padicTateTwist ℓ F`: `PadicTateTwist ℓ F^alg` as a continuous
  representation of `G_F` over `ℤ_ℓ`.
* `TauCeti.ContinuousRep.cyclotomicLineIsoPadicTateTwist e`: the isomorphism
  `ℤ_ℓ(1) ≅ PadicTateTwist ℓ F^alg` given by a `ℤ_ℓ`-linear equivalence `e`.

## Main results

* `TauCeti.ContinuousRep.padicTateTwist_apply`: `G_F` acts by `χ_ℓ`.
* `TauCeti.ContinuousRep.nonempty_iso_cyclotomicLine_padicTateTwist`: for `ℓ ≠ char F`,
  `ℤ_ℓ(1) ≅ PadicTateTwist ℓ F^alg` as continuous representations.

## References

* H. Darmon, F. Diamond, R. Taylor, *Fermat's Last Theorem*, revised version (2007) of Current
  Developments in Mathematics 1995, §2.1, p. 50.
-/

public section

noncomputable section

namespace TauCeti

variable (ℓ : ℕ) [Fact ℓ.Prime] (F : Type*) [Field F]

namespace ContinuousRep

/-- **`ℤ_ℓ(1)` as roots of unity**: the `ℓ`-adic Tate module `PadicTateTwist ℓ F^alg` of the
roots of unity of `F^alg`, with the componentwise action of `G_F`, as a continuous representation
over `ℤ_ℓ`. -/
def padicTateTwist :
    ContinuousRep (Field.absoluteGaloisGroup F) ℤ_[ℓ] (PadicTateTwist ℓ (AlgebraicClosure F)) where
  toRepresentation := PadicTateTwist.galoisRepresentation (F := F)
  continuous_action := PadicTateTwist.continuous_galoisRepresentation

/-- The underlying representation of `padicTateTwist ℓ F` is the componentwise action
`PadicTateTwist.galoisRepresentation`. -/
theorem toRepresentation_padicTateTwist :
    (padicTateTwist ℓ F).toRepresentation = PadicTateTwist.galoisRepresentation (F := F) :=
  (rfl)

/-- **`G_F` acts on `PadicTateTwist ℓ F^alg` by the cyclotomic character.** -/
@[simp]
theorem padicTateTwist_apply (σ : Field.absoluteGaloisGroup F)
    (x : PadicTateTwist ℓ (AlgebraicClosure F)) :
    padicTateTwist ℓ F σ x = (localCyclotomicCharacter ℓ F σ : ℤ_[ℓ]) • x := by
  rw [← coe_toRepresentation, toRepresentation_padicTateTwist, localCyclotomicCharacter_apply]
  exact PadicTateTwist.galoisRepresentation_apply_eq_smul σ x

variable {ℓ F}

/-- **`ℤ_ℓ(1) ≅ PadicTateTwist ℓ F^alg`** through a `ℤ_ℓ`-linear equivalence `e`, that is, through
the compatible system of primitive `ℓ^n`-th roots of unity given by the levels of `e 1`. Every such
`e` is equivariant, both sides being acted on by `χ_ℓ`, and it is a homeomorphism. -/
def cyclotomicLineIsoPadicTateTwist (e : ℤ_[ℓ] ≃ₗ[ℤ_[ℓ]] PadicTateTwist ℓ (AlgebraicClosure F)) :
    Iso (cyclotomicLine ℓ F) (padicTateTwist ℓ F) :=
  have : Module.Finite ℤ_[ℓ] (PadicTateTwist ℓ (AlgebraicClosure F)) := .equiv e
  have := isModuleTopology_of_finite_of_compactSpace (R := ℤ_[ℓ])
    (M := PadicTateTwist ℓ (AlgebraicClosure F))
  Iso.ofEquiv (.mk e fun σ ↦ LinearMap.ext fun a ↦ by simp [← smul_eq_mul])

@[simp]
theorem cyclotomicLineIsoPadicTateTwist_apply
    (e : ℤ_[ℓ] ≃ₗ[ℤ_[ℓ]] PadicTateTwist ℓ (AlgebraicClosure F)) (a : ℤ_[ℓ]) :
    cyclotomicLineIsoPadicTateTwist e a = e a := by
  simp [cyclotomicLineIsoPadicTateTwist]

@[simp]
theorem cyclotomicLineIsoPadicTateTwist_symm_apply
    (e : ℤ_[ℓ] ≃ₗ[ℤ_[ℓ]] PadicTateTwist ℓ (AlgebraicClosure F))
    (x : PadicTateTwist ℓ (AlgebraicClosure F)) :
    (cyclotomicLineIsoPadicTateTwist e).symm x = e.symm x :=
  (cyclotomicLineIsoPadicTateTwist e).injective <| by simp

variable (ℓ F) in
/-- **`ℤ_ℓ(1) ≅ PadicTateTwist ℓ F^alg`** as continuous representations of `G_F` over `ℤ_ℓ`, when
`ℓ ≠ char F`. -/
theorem nonempty_iso_cyclotomicLine_padicTateTwist [NeZero (ℓ : F)] :
    Nonempty (Iso (cyclotomicLine ℓ F) (padicTateTwist ℓ F)) :=
  ⟨cyclotomicLineIsoPadicTateTwist (PadicTateTwist.nonempty_linearEquiv ℓ _).some.symm⟩

end ContinuousRep

end TauCeti
