/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Flat.Rank
public import Mathlib.RingTheory.RingHom.Flat

/-!
# Ring maps with explicit coordinates

Let `φ : A →+* B` be a ring map and `L : B ≃+ (ι →₀ A)` an additive equivalence that is linear
along `φ`, that is `L (φ a * b) = a • L b`. Then `L` is the coordinate map of a basis of `B` over
`A` for the module structure `φ.toAlgebra`, so `φ` is flat of constant rank `Nat.card ι`.

The statements are about a ring map `φ` rather than an `A`-algebra `B`. Applied to an
endomorphism `φ : A →+* A`, this keeps the module structure of `φ.toAlgebra` apart from the
multiplication of `A` on itself, which instance search would otherwise prefer; the two structures
are not defeq.

## Main results

* `RingHom.basisOfAddEquiv`: the basis of `B` over `A` along `φ` with coordinates `L`, with its
  coordinates and basis vectors computed by `RingHom.basisOfAddEquiv_repr_apply` and
  `RingHom.basisOfAddEquiv_apply`.
* `RingHom.flat_of_addEquiv`: `φ` is flat.
* `RingHom.finrank_of_addEquiv`: `φ` has rank `Nat.card ι` at every prime.
-/

public section

namespace RingHom

variable {A B ι : Type*} [CommRing A] [CommRing B] (φ : A →+* B) (L : B ≃+ (ι →₀ A))
  (hL : ∀ a b, L (φ a * b) = a • L b)

include hL

/-- The basis of `B` over `A` along `φ` whose coordinates are given by `L`. -/
noncomputable def basisOfAddEquiv : letI := φ.toAlgebra; Module.Basis ι A B :=
  letI := φ.toAlgebra
  .ofRepr { L with
    map_smul' a b := by simpa [Algebra.smul_def, RingHom.algebraMap_toAlgebra] using hL a b }

/-- The coordinates of `RingHom.basisOfAddEquiv` are given by `L`. -/
@[simp]
theorem basisOfAddEquiv_repr_apply (b : B) :
    letI := φ.toAlgebra; (basisOfAddEquiv φ L hL).repr b = L b := by
  simp [basisOfAddEquiv]

/-- The basis vectors of `RingHom.basisOfAddEquiv` are the preimages under `L` of the
standard basis vectors. -/
@[simp]
theorem basisOfAddEquiv_apply (i : ι) :
    letI := φ.toAlgebra; basisOfAddEquiv φ L hL i = L.symm (Finsupp.single i 1) := by
  simp [basisOfAddEquiv]

/-- `φ` is flat when `L` gives coordinates of `B` over `A` along `φ`. -/
theorem flat_of_addEquiv : φ.Flat :=
  letI := φ.toAlgebra
  have := Module.Free.of_basis (basisOfAddEquiv φ L hL)
  Module.Flat.of_free

/-- `φ` has rank `Nat.card ι` everywhere when `L` gives coordinates of `B` over `A` along `φ`. -/
theorem finrank_of_addEquiv : φ.finrank = fun _ ↦ Nat.card ι := by
  ext x
  let := φ.toAlgebra
  have := Module.Free.of_basis (basisOfAddEquiv φ L hL)
  have : Nontrivial A := x.nontrivial
  rw [RingHom.finrank, Module.rankAtStalk_eq_finrank_of_free,
    Module.finrank_eq_nat_card_basis (basisOfAddEquiv φ L hL), Pi.natCast_apply, Nat.cast_id]

end RingHom
