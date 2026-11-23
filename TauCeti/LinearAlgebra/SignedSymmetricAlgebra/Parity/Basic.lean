/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.SignedSymmetricAlgebra.Coarsen

/-!
# Parity reduction of the signed symmetric algebra

Because `TauCeti.SignedSym` is defined over any Koszul-signed degree semiring `ι`
(`[CommSemiring ι] [DecidableEq ι] [Module ι (Additive ℤˣ)]`), taking `ι = ZMod 2` constructs the
free supercommutative algebra directly from a parity-graded module
`H : InternalGrading R V (ZMod 2)`, complete with its universal property, native `ZMod 2`-grading
`signedSymPiece H`, Koszul supercommutativity, word-length grading, and odd derivations
`liftDerivation`, without choosing an integer lift.

For an integer grading `G : InternalGrading R V ℤ`, specializing
`TauCeti.LinearAlgebra.SignedSymmetricAlgebra.Coarsen` to `Int.castAddHom (ZMod 2) : ℤ →+ ZMod 2`
identifies the integer-graded orbit algebra `SignedSym G` with the parity-graded orbit algebra
`SignedSym G.parity` built directly from parities (`TauCeti.SignedSym.parityEquiv`). Because
`TauCeti.SignedSym.parityEquiv`, `TauCeti.SignedSym.toParity`, and `TauCeti.SignedSym.ofParity` are
`abbrev`s for `coarsenEquiv`, `toCoarsen`, and `ofCoarsen` along `Int.castAddHom (ZMod 2)`
(matching `TauCeti.InternalGrading.parity` and `TauCeti.parityGrading`), all generator, quotient,
augmentation, word-length, graded-piece, naturality, homogeneity, Leibniz, and derivation-transport
lemmas from `TauCeti.LinearAlgebra.SignedSymmetricAlgebra.Coarsen` apply directly to them.

For `IsDGAlgebra` differentials, conjugating a degree-one signed derivation `d` of `SignedSym G`
across `parityEquiv` yields a parity-odd signed derivation of `SignedSym G.parity`, and `d` defines
a differential graded algebra structure on `SignedSym G` if and only if its parity transport
squares to zero (`TauCeti.SignedSym.isDGAlgebra_iff_conj_parityEquiv_comp_self_eq_zero`). For
derivations built from a degree-one generator assignment `δ`, this reduces `IsDGAlgebra` to the
parity-reduced `liftDerivation` squaring to zero
(`TauCeti.SignedSym.isDGAlgebra_liftDerivation_iff_liftDerivation_parityEquiv_comp_self_eq_zero`).

## Main definitions

* `TauCeti.SignedSym.parityEquiv`: the canonical `R`-algebra equivalence
  `SignedSym G ≃ₐ[R] SignedSym G.parity` (an `abbrev` for `coarsenEquiv` along
  `Int.castAddHom (ZMod 2)`).
* `TauCeti.SignedSym.toParity` and `TauCeti.SignedSym.ofParity`: the mutually inverse
  `ZMod 2`-graded algebra homomorphisms identifying `parityGrading (signedSymPiece G)` with
  `signedSymPiece G.parity` (`abbrev`s for `toCoarsen` and `ofCoarsen`).

## Main results

* `TauCeti.SignedSym.isDGAlgebra_iff_conj_parityEquiv_comp_self_eq_zero`: a degree-one signed
  Leibniz endomorphism of `SignedSym G` defines an `IsDGAlgebra` structure iff its `parityEquiv`
  conjugate squares to zero.
* `TauCeti.SignedSym.isDGAlgebra_liftDerivation_iff_liftDerivation_parityEquiv_comp_self_eq_zero`:
  an integer degree-one generator assignment induces an `IsDGAlgebra` structure on `SignedSym G`
  iff the parity-reduced `liftDerivation` on `SignedSym G.parity` squares to zero.

## References

* J. Pardon, *Contact homology and virtual fundamental cycles*, equation (1.1) and Definition 2.48,
  for the parity-graded orbit algebra and its comparison with an integer Conley–Zehnder lift.
* Y. Eliashberg, A. Givental, and H. Hofer, *Introduction to symplectic field theory*,
  Geom. Funct. Anal. (2000), 560–673, for `ℤ/2ℤ`-graded SFT orbit algebras when integer gradings
  reduce modulo `2`.
-/

public section

namespace TauCeti.SignedSym

universe u v

variable {R : Type u} [CommRing R]
variable {V : Type v} [AddCommGroup V] [Module R V]
variable (G : InternalGrading R V ℤ)

/-- **The parity-graded signed symmetric algebra `SignedSym G.parity` is canonically isomorphic to
the integer-graded `SignedSym G`.** -/
noncomputable abbrev parityEquiv : SignedSym G ≃ₐ[R] SignedSym G.parity :=
  coarsenEquiv G (f := Int.castAddHom (ZMod 2))
    (fun p ↦ by rw [Int.coe_castAddHom]; exact uzpow_intCast (-1) p)

/-- `parityEquiv` as a `ZMod 2`-graded algebra homomorphism from `parityGrading (signedSymPiece G)`
to `signedSymPiece G.parity`. -/
noncomputable abbrev toParity :
    parityGrading (signedSymPiece G) →ₐᵍ[R] signedSymPiece G.parity :=
  toCoarsen G (f := Int.castAddHom (ZMod 2))
    (fun p ↦ by rw [Int.coe_castAddHom]; exact uzpow_intCast (-1) p)

/-- The inverse of `parityEquiv` as a `ZMod 2`-graded algebra homomorphism from
`signedSymPiece G.parity` to `parityGrading (signedSymPiece G)`. -/
noncomputable abbrev ofParity :
    signedSymPiece G.parity →ₐᵍ[R] parityGrading (signedSymPiece G) :=
  ofCoarsen G (f := Int.castAddHom (ZMod 2))
    (fun p ↦ by rw [Int.coe_castAddHom]; exact uzpow_intCast (-1) p)

/-- A degree-`1` signed Leibniz endomorphism of `SignedSym G` defines a differential graded algebra
structure if and only if its parity transport on `SignedSym G.parity` squares to zero. -/
theorem isDGAlgebra_iff_conj_parityEquiv_comp_self_eq_zero {d : SignedSym G →ₗ[R] SignedSym G}
    (hdeg : LinearMap.IsHomogeneous d (signedSymPiece G) (signedSymPiece G) 1)
    (hleibniz : ∀ {p : ℤ} {a : SignedSym G}, a ∈ signedSymPiece G p → ∀ b : SignedSym G,
      d (a * b) = d a * b + p.negOnePow • (a * d b)) :
    IsDGAlgebra (signedSymPiece G) d ↔
      (parityEquiv G).toLinearEquiv.conj d ∘ₗ (parityEquiv G).toLinearEquiv.conj d = 0 := by
  rw [← LinearEquiv.conj_comp, LinearEquiv.map_eq_zero_iff]
  exact ⟨fun h ↦ LinearMap.ext h.sq_zero, fun h ↦
    { map_mem := fun ha ↦ hdeg.map_mem ha
      sq_zero := fun a ↦ LinearMap.congr_fun h a
      leibniz := fun ha b ↦ hleibniz ha b }⟩

/-- Extending an integer degree-`1` generator assignment yields a differential graded algebra
structure on `SignedSym G` if and only if the parity-reduced odd derivation on `SignedSym G.parity`
squares to zero. -/
theorem isDGAlgebra_liftDerivation_iff_liftDerivation_parityEquiv_comp_self_eq_zero
    {δ : V →ₗ[R] SignedSym G}
    (hδ : LinearMap.IsHomogeneous δ G.piece (signedSymPiece G) 1)
    (hδ' : LinearMap.IsHomogeneous ((parityEquiv G).toLinearMap ∘ₗ δ)
      G.parity.piece (signedSymPiece G.parity) 1 :=
      LinearMap.isHomogeneous_def.2 fun _ _ hx ↦ by
        have h1 : Int.castAddHom (ZMod 2) 1 = 1 := Int.cast_one
        simpa only [h1] using
          (isHomogeneous_coarsenEquiv_comp G (f := Int.castAddHom (ZMod 2))
            (fun p ↦ by rw [Int.coe_castAddHom]; exact uzpow_intCast (-1) p) hδ).map_mem hx) :
    IsDGAlgebra (signedSymPiece G) (liftDerivation δ hδ (uzpow_one (-1))) ↔
      liftDerivation ((parityEquiv G).toLinearMap ∘ₗ δ) hδ' (uzpow_one (-1)) ∘ₗ
        liftDerivation ((parityEquiv G).toLinearMap ∘ₗ δ) hδ' (uzpow_one (-1)) = 0 := by
  have hconj : (parityEquiv G).toLinearEquiv.conj (liftDerivation δ hδ (uzpow_one (-1))) =
      liftDerivation ((parityEquiv G).toLinearMap ∘ₗ δ) hδ' (uzpow_one (-1)) := by
    rw [conj_coarsenEquiv_liftDerivation G (f := Int.castAddHom (ZMod 2))]
    exact eq_liftDerivation hδ' (uzpow_one (-1)) (liftDerivation_mul _ _)
      (liftDerivation_generator _ _)
  rw [isDGAlgebra_iff_conj_parityEquiv_comp_self_eq_zero G
      (isHomogeneous_liftDerivation hδ (uzpow_one (-1)))
      (liftDerivation_mul hδ (uzpow_one (-1))),
    hconj]

end TauCeti.SignedSym
