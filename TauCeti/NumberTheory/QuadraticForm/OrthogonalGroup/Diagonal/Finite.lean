/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.QuadraticForm.OrthogonalGroup.AdelicSpinorNorm
public import TauCeti.FieldTheory.SquareClassGroup.Multiplicative
public import TauCeti.Topology.Algebra.RestrictedProduct.Diagonal
import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.SpinorNorm.BaseChange

/-!
# Rational points on the diagonal of the finite adelic orthogonal groups

Let `Q` be a quadratic form on a finite-dimensional rational vector space `V`, and let `U` be
compatible compact-open reference data (`TauCeti.QuadraticMap.OrthogonalCompactOpens`). Extending
scalars to `ℚ_p` sends a rational point of `O(V)`, `SO(V)` or `Spin(V)` to a local point at every
prime, and the integrality conditions recorded in `U` put it in the reference subgroup at almost
every prime. These local images therefore assemble into diagonal homomorphisms

  `O(V)(ℚ) → O(V)(𝔸_f)`, `SO(V)(ℚ) → SO(V)(𝔸_f)`, `Spin(V)(ℚ) → Spin(V)(𝔸_f)`,

built with `TauCeti.rationalDiagonal`. For `SO` the integrality comes from that of `O`, through
`OrthogonalCompactOpens.eventually_specialOrthogonal`, rather than from a further hypothesis.

Each diagonal is injective, since already the extension of scalars to a single `ℚ_p` is. The
diagonals commute with the componentwise natural maps `Spin(V)(𝔸_f) → SO(V)(𝔸_f) → O(V)(𝔸_f)`
(the Spin-to-SO map and the SO-to-O inclusion). In particular the two routes from `Spin(V)(ℚ)`
to `SO(V)(𝔸_f)`, through `Spin(V)(𝔸_f)` or through `SO(V)(ℚ)`, agree, so the image of the
rational Spin points in adelic `SO` is unambiguous. Finally the finite adelic spinor norm of a
rational proper isometry is, at every prime, the image of its rational spinor norm in the local
square classes; so rational proper isometries with trivial spinor norm lie in the adelic spinor
kernel.

## Main definitions

* `OrthogonalCompactOpens.finiteAdelicOrthogonalDiagonal`,
  `OrthogonalCompactOpens.finiteAdelicSpecialOrthogonalDiagonal`,
  `OrthogonalCompactOpens.finiteAdelicSpinDiagonal`: the three diagonal homomorphisms.

## Main results

* `OrthogonalCompactOpens.finiteAdelicSpinToSpecialOrthogonal_comp_finiteAdelicSpinDiagonal`:
  the square from `Spin(V)(ℚ)` to `SO(V)(𝔸_f)` commutes.
* `finiteAdelicSpecialOrthogonalToOrthogonal_comp_finiteAdelicSpecialOrthogonalDiagonal`, in the
  namespace `OrthogonalCompactOpens`: the square from `SO(V)(ℚ)` to `O(V)(𝔸_f)` commutes.
* `OrthogonalCompactOpens.adelicSpinorNorm_finiteAdelicSpecialOrthogonalDiagonal_apply`: the
  adelic spinor norm of a rational point is the localization of its rational spinor norm.

## References

* O. T. O'Meara, *Introduction to Quadratic Forms* (1963), §101.
* A. Weil, *Adeles and Algebraic Groups* (1982), Chapter I.
-/

public section

namespace TauCeti
namespace QuadraticMap
namespace OrthogonalCompactOpens

open _root_.QuadraticMap
open scoped TensorProduct

noncomputable section

variable {V : Type*} [AddCommGroup V] [Module ℚ V]
  {Q : QuadraticForm ℚ V} (U : OrthogonalCompactOpens Q)

/-! ### The three diagonals -/

/-- The diagonal embedding `O(V)(ℚ) → O(V)(𝔸_f)`, extending the scalars of a rational isometry to
`ℚ_p` at every prime. -/
def finiteAdelicOrthogonalDiagonal : orthogonalGroup Q →* U.finiteAdelicOrthogonal :=
  rationalDiagonal (fun p : Nat.Primes ↦ orthogonalGroupBaseChange (A := ℚ_[p]) Q) U.orthogonal
    U.eventually_orthogonal

/-- The `p`-component of the diagonal image of a rational isometry is its extension of scalars
to `ℚ_p`. -/
@[simp]
theorem finiteAdelicOrthogonalDiagonal_apply (g : orthogonalGroup Q) (p : Nat.Primes) :
    U.finiteAdelicOrthogonalDiagonal g p = orthogonalGroupBaseChange (A := ℚ_[p]) Q g :=
  rationalDiagonal_apply _ _ _ g p

/-- The diagonal embedding of rational isometries is injective. -/
theorem finiteAdelicOrthogonalDiagonal_injective :
    Function.Injective U.finiteAdelicOrthogonalDiagonal :=
  injective_rationalDiagonal _ _ _ ⟨⟨2, Nat.prime_two⟩, orthogonalGroupBaseChange_injective Q⟩

/-- The diagonal embedding `Spin(V)(ℚ) → Spin(V)(𝔸_f)`, extending the scalars of a rational Spin
element to `ℚ_p` at every prime. -/
def finiteAdelicSpinDiagonal : spinGroup Q →* U.finiteAdelicSpin :=
  rationalDiagonal (fun p : Nat.Primes ↦ CliffordAlgebra.spinGroupBaseChange (A := ℚ_[p]) Q)
    U.spin U.eventually_spin

/-- The `p`-component of the diagonal image of a rational Spin element is its extension of
scalars to `ℚ_p`. -/
@[simp]
theorem finiteAdelicSpinDiagonal_apply (x : spinGroup Q) (p : Nat.Primes) :
    U.finiteAdelicSpinDiagonal x p = CliffordAlgebra.spinGroupBaseChange (A := ℚ_[p]) Q x :=
  rationalDiagonal_apply _ _ _ x p

/-- The diagonal embedding of rational Spin elements is injective. -/
theorem finiteAdelicSpinDiagonal_injective :
    Function.Injective U.finiteAdelicSpinDiagonal :=
  injective_rationalDiagonal _ _ _
    ⟨⟨2, Nat.prime_two⟩, CliffordAlgebra.spinGroupBaseChange_injective Q⟩

variable [FiniteDimensional ℚ V]

/-- The diagonal embedding `SO(V)(ℚ) → SO(V)(𝔸_f)`. Its integrality at almost every prime is
derived from that of the orthogonal reference subgroups. -/
def finiteAdelicSpecialOrthogonalDiagonal :
    specialOrthogonalGroup Q →* U.finiteAdelicSpecialOrthogonal :=
  rationalDiagonal (fun p : Nat.Primes ↦ specialOrthogonalGroupBaseChange (A := ℚ_[p]) Q)
    U.specialOrthogonal U.eventually_specialOrthogonal

/-- The `p`-component of the diagonal image of a rational proper isometry is its extension of
scalars to `ℚ_p`. -/
@[simp]
theorem finiteAdelicSpecialOrthogonalDiagonal_apply (g : specialOrthogonalGroup Q)
    (p : Nat.Primes) :
    U.finiteAdelicSpecialOrthogonalDiagonal g p =
      specialOrthogonalGroupBaseChange (A := ℚ_[p]) Q g :=
  rationalDiagonal_apply _ _ _ g p

/-- The diagonal embedding of rational proper isometries is injective. -/
theorem finiteAdelicSpecialOrthogonalDiagonal_injective :
    Function.Injective U.finiteAdelicSpecialOrthogonalDiagonal :=
  injective_rationalDiagonal _ _ _
    ⟨⟨2, Nat.prime_two⟩, specialOrthogonalGroupBaseChange_injective Q⟩

/-! ### Compatibility with the componentwise natural maps -/

/-- The diagonal commutes with the projections `Spin → SO`: mapping `Spin(V)(ℚ)` to
`SO(V)(𝔸_f)` through `Spin(V)(𝔸_f)` or through `SO(V)(ℚ)` gives the same homomorphism. -/
theorem finiteAdelicSpinToSpecialOrthogonal_comp_finiteAdelicSpinDiagonal :
    U.finiteAdelicSpinToSpecialOrthogonal.comp U.finiteAdelicSpinDiagonal =
      U.finiteAdelicSpecialOrthogonalDiagonal.comp (CliffordAlgebra.spinToSpecialOrthogonal Q) := by
  ext x p : 2
  have h := CliffordAlgebra.spinToSpecialOrthogonal_baseChange (A := ℚ_[p]) Q x
  -- Identify the scalar-extended inverse of two with the canonical `p`-adic instance.
  rw [Subsingleton.elim ((Invertible.map (algebraMap ℚ ℚ_[p]) 2).copy 2 (map_ofNat _ _).symm)
    (inferInstance : Invertible (2 : ℚ_[p]))] at h
  simp only [MonoidHom.comp_apply, finiteAdelicSpinToSpecialOrthogonal_apply,
    finiteAdelicSpinDiagonal_apply, finiteAdelicSpecialOrthogonalDiagonal_apply, h]

/-- Pointwise form of `finiteAdelicSpinToSpecialOrthogonal_comp_finiteAdelicSpinDiagonal`. -/
@[simp]
theorem finiteAdelicSpinToSpecialOrthogonal_finiteAdelicSpinDiagonal (x : spinGroup Q) :
    U.finiteAdelicSpinToSpecialOrthogonal (U.finiteAdelicSpinDiagonal x) =
      U.finiteAdelicSpecialOrthogonalDiagonal (CliffordAlgebra.spinToSpecialOrthogonal Q x) :=
  DFunLike.congr_fun U.finiteAdelicSpinToSpecialOrthogonal_comp_finiteAdelicSpinDiagonal x

/-- The diagonal commutes with the inclusions `SO → O`. -/
theorem finiteAdelicSpecialOrthogonalToOrthogonal_comp_finiteAdelicSpecialOrthogonalDiagonal :
    U.finiteAdelicSpecialOrthogonalToOrthogonal.comp U.finiteAdelicSpecialOrthogonalDiagonal =
      U.finiteAdelicOrthogonalDiagonal.comp (specialOrthogonalToOrthogonal Q) := by
  ext g p : 2
  simp only [MonoidHom.comp_apply, finiteAdelicSpecialOrthogonalToOrthogonal_apply,
    finiteAdelicSpecialOrthogonalDiagonal_apply, finiteAdelicOrthogonalDiagonal_apply,
    specialOrthogonalToOrthogonal_specialOrthogonalGroupBaseChange]

/-- Pointwise form of
`finiteAdelicSpecialOrthogonalToOrthogonal_comp_finiteAdelicSpecialOrthogonalDiagonal`. -/
@[simp]
theorem finiteAdelicSpecialOrthogonalToOrthogonal_finiteAdelicSpecialOrthogonalDiagonal
    (g : specialOrthogonalGroup Q) :
    U.finiteAdelicSpecialOrthogonalToOrthogonal (U.finiteAdelicSpecialOrthogonalDiagonal g) =
      U.finiteAdelicOrthogonalDiagonal (specialOrthogonalToOrthogonal Q g) :=
  DFunLike.congr_fun
    U.finiteAdelicSpecialOrthogonalToOrthogonal_comp_finiteAdelicSpecialOrthogonalDiagonal g

/-! ### The adelic spinor norm of a rational point -/

variable (hQ : Q.Nondegenerate)

/-- The `p`-component of the finite adelic spinor norm of a rational proper isometry is the image
of its rational spinor norm in the local square classes. -/
theorem adelicSpinorNorm_finiteAdelicSpecialOrthogonalDiagonal_apply
    (g : specialOrthogonalGroup Q) (p : Nat.Primes) :
    U.adelicSpinorNorm hQ (U.finiteAdelicSpecialOrthogonalDiagonal g) p =
      Multiplicative.ofAdd ((algebraMap ℚ ℚ_[p]).squareClassMap
        (CliffordAlgebra.spinorNorm Q hQ g).toAdd) := by
  have h := CliffordAlgebra.spinorNorm_specialOrthogonalGroupBaseChange (L := ℚ_[p]) Q hQ g
  -- Identify the scalar-extended inverse of two with the canonical `p`-adic instance.
  rw [Subsingleton.elim ((Invertible.map (algebraMap ℚ ℚ_[p]) 2).copy 2 (map_ofNat _ _).symm)
    (inferInstance : Invertible (2 : ℚ_[p]))] at h
  rw [adelicSpinorNorm_apply, finiteAdelicSpecialOrthogonalDiagonal_apply, h]

/-- A rational proper isometry of trivial spinor norm lies, diagonally, in the adelic spinor
kernel. -/
theorem finiteAdelicSpecialOrthogonalDiagonal_mem_adelicSpinorKernel
    {g : specialOrthogonalGroup Q} (hg : CliffordAlgebra.spinorNorm Q hQ g = 1) :
    U.finiteAdelicSpecialOrthogonalDiagonal g ∈ U.adelicSpinorKernel hQ := by
  rw [adelicSpinorKernel_def, MonoidHom.mem_ker]
  ext p : 1
  rw [adelicSpinorNorm_finiteAdelicSpecialOrthogonalDiagonal_apply, hg, toAdd_one, map_zero,
    ofAdd_zero, RestrictedProduct.one_apply]

end

end OrthogonalCompactOpens
end QuadraticMap
end TauCeti
