/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.Loop
public import TauCeti.Algebra.Lie.Extension.Basic
public import TauCeti.Algebra.Lie.InvariantForm.Basic
public import TauCeti.Algebra.Lie.Loop.Cocycle

/-!
# The Heisenberg Lie algebra of a symmetric bilinear space

Let `H` be an abelian Lie algebra over a commutative ring `R`, for instance a Cartan subalgebra of
a semisimple Lie algebra, and let `B` be a symmetric bilinear form on `H`. The **Heisenberg Lie
algebra** `Heis_B = H[t, t⁻¹] ⊕ R K` is the central extension of the abelian Lie algebra of Laurent
polynomials with coefficients in `H` by the 2-cocycle

`c(x, y) = ∑ₘ m B(xₘ, y₋ₘ)`

(`TauCeti.heisenbergCocycle`), where `xₘ` is the coefficient of `tᵐ` in `x`. Writing
`h(n) = h ⊗ tⁿ` for the **modes** (`TauCeti.HeisenbergAlgebra.mode`) and `K` for the central
element `(0, 1)`, its only brackets are

`[h(m), k(n)] = m B(h, k) δ_{m+n,0} K`

(`TauCeti.HeisenbergAlgebra.lie_mode_mode`).

Every form on an abelian Lie algebra is invariant, so `Heis_B` is the affine central extension of
the loop algebra of `H` for the invariant form `-B`: the cocycle is Mathlib's residue cocycle
`LieAlgebra.LoopAlgebra.twoCocycleOfBilinear` for `-B`, whose value `Res(f dg)` carries the
opposite sign. The form `B` may be degenerate, and is allowed to be zero, when `Heis_B` is abelian.
The ring `R` is additively torsion-free, as for Mathlib's residue cocycle.

This infinite-dimensional Lie algebra is distinct from the three-dimensional Heisenberg Lie
algebra `TauCeti.heisenberg` of `TauCeti.Algebra.Lie.Heisenberg.Basic`. Linear maps out of it are
determined by their values on the modes and on `K` (`TauCeti.HeisenbergAlgebra.linearMap_ext`).

The Heisenberg Lie algebra acts on its Fock module, `TauCeti.HeisenbergAlgebra.fockRepresentation`
in `TauCeti.Algebra.Lie.Heisenberg.Fock`.

## Main definitions

* `TauCeti.heisenbergCocycle`: the 2-cocycle `c(x, y) = ∑ₘ m B(xₘ, y₋ₘ)`.
* `TauCeti.HeisenbergAlgebra`: the Heisenberg Lie algebra `Heis_B`.
* `TauCeti.HeisenbergAlgebra.mode`: the modes `h(n)`.

## Main results

* `TauCeti.heisenbergCocycle_single_tmul`: the cocycle on modes.
* `TauCeti.HeisenbergAlgebra.lie_mode_mode`: the bracket `[h(m), k(n)] = m B(h, k) δ_{m+n,0} K`.

## References

* E. Frenkel, *Langlands Correspondence for Loop Groups*, Cambridge University Press (2007),
  §6.2.1, for the Heisenberg Lie algebra of a Cartan subalgebra.
* E. Frenkel and D. Ben-Zvi, *Vertex Algebras and Algebraic Curves*, 2nd ed., American
  Mathematical Society (2004), §2.1, for the Heisenberg Lie algebra.
-/

public section

noncomputable section

open scoped TensorProduct
open LieAlgebra LieAlgebra.LoopAlgebra LieModule.Cohomology
open LieAlgebra.ofTwoCocycle (centralElement)

namespace TauCeti

variable {R H : Type*} [CommRing R] [HasUniqueDiv R] [LieRing H] [LieAlgebra R H]
  [IsLieAbelian H] (B : LinearMap.BilinForm R H) (hB : B.IsSymm)

/-- The **Heisenberg cocycle** `c(x, y) = ∑ₘ m B(xₘ, y₋ₘ)` on Laurent polynomials with
coefficients in `H`: Mathlib's residue cocycle for the form `-B`. -/
def heisenbergCocycle :
    twoCocycle R (loopAlgebra R ℤ H) (TrivialLieModule R (loopAlgebra R ℤ H) R) :=
  twoCocycleOfBilinear R ℤ H (-B) (-B).lieInvariant_of_isTrivial hB.neg

/-- The Heisenberg cocycle is Mathlib's residue cocycle for the form `-B`. -/
theorem heisenbergCocycle_def : heisenbergCocycle B hB =
    twoCocycleOfBilinear R ℤ H (-B) (-B).lieInvariant_of_isTrivial hB.neg :=
  (rfl)

/-- The Heisenberg cocycle on modes: `c(h(m), k(n)) = m B(h, k)` when `m + n = 0`, and zero
otherwise. -/
theorem heisenbergCocycle_single_tmul (m n : ℤ) (h k : H) :
    TrivialLieModule.equiv R (loopAlgebra R ℤ H) R
        ((heisenbergCocycle B hB : loopAlgebra R ℤ H →ₗ[R] loopAlgebra R ℤ H →ₗ[R]
          TrivialLieModule R (loopAlgebra R ℤ H) R) (AddMonoidAlgebra.single m 1 ⊗ₜ h)
          (AddMonoidAlgebra.single n 1 ⊗ₜ k)) =
      if m + n = 0 then (m : R) * B h k else 0 := by
  rw [heisenbergCocycle_def, twoCocycleOfBilinear_coe, twoCochain_val_apply,
    twoCochainOfBilinear_apply_apply, LinearEquiv.apply_symm_apply,
    TauCeti.LieAlgebra.LoopAlgebra.residuePairing_single_tmul]
  split_ifs with hmn
  · rw [eq_neg_of_add_eq_zero_right hmn, LinearMap.neg_apply, LinearMap.neg_apply, zsmul_eq_mul]
    push_cast
    ring
  · rfl

/-- The **Heisenberg Lie algebra** `Heis_B = H[t, t⁻¹] ⊕ R K` of a symmetric bilinear form `B` on an
abelian Lie algebra `H`: the central extension of the loop algebra of `H` by the Heisenberg
cocycle, with brackets `[h(m), k(n)] = m B(h, k) δ_{m+n,0} K`. -/
abbrev HeisenbergAlgebra : Type _ :=
  LieAlgebra.ofTwoCocycle (heisenbergCocycle B hB)

namespace HeisenbergAlgebra

/-- The **mode** `h(n) = h ⊗ tⁿ` of the Heisenberg Lie algebra, with zero central coordinate. -/
def mode (n : ℤ) : H →ₗ[R] HeisenbergAlgebra B hB :=
  (ofProdLinearEquiv (heisenbergCocycle B hB)).toLinearMap ∘ₗ
    LinearMap.inl R (loopAlgebra R ℤ H) (TrivialLieModule R (loopAlgebra R ℤ H) R) ∘ₗ
      ((toFinsupp R ℤ H).symm.toLinearMap ∘ₗ Finsupp.lsingle n)

/-- The mode `h(n)` is the pair `(h ⊗ tⁿ, 0)`. -/
theorem mode_apply (n : ℤ) (h : H) :
    mode B hB n h = ofProd (heisenbergCocycle B hB) (AddMonoidAlgebra.single n 1 ⊗ₜ h, 0) := by
  simp [mode, coe_ofProdLinearEquiv, toFinsupp_symm_single]

/-- Two linear maps out of the Heisenberg Lie algebra agree when they agree on every mode and on
the central element `K`. -/
@[ext]
theorem linearMap_ext {M : Type*} [AddCommGroup M] [Module R M]
    {f g : HeisenbergAlgebra B hB →ₗ[R] M} (hmode : ∀ n h, f (mode B hB n h) = g (mode B hB n h))
    (hK : f (centralElement _) = g (centralElement _)) : f = g := by
  refine LinearMap.ext fun x ↦ ?_
  obtain ⟨⟨u, z⟩, rfl⟩ := (ofProd (heisenbergCocycle B hB)).surjective x
  rw [ofTwoCocycle.ofProd_eq_add_smul_centralElement, map_add, map_add, map_smul, map_smul, hK]
  congr 1
  obtain ⟨v, rfl⟩ := (toFinsupp R ℤ H).symm.surjective u
  induction v using Finsupp.induction_linear with
  | zero => simp [Prod.mk_zero_zero]
  | add v w hv hw => simpa [← map_add, ← of_add] using congr($hv + $hw)
  | single n h => simpa [mode_apply, toFinsupp_symm_single] using hmode n h

/-- **The Heisenberg bracket.** `[h(m), k(n)] = m B(h, k) δ_{m+n,0} K`. -/
@[simp]
theorem lie_mode_mode (m n : ℤ) (h k : H) :
    ⁅mode B hB m h, mode B hB n k⁆ =
      (if m + n = 0 then (m : R) * B h k else 0) • centralElement (heisenbergCocycle B hB) := by
  rw [mode_apply, mode_apply, bracket_ofTwoCocycle]
  simp only [Equiv.symm_apply_apply, ExtendScalars.bracket_tmul, trivial_lie_zero,
    TensorProduct.tmul_zero, add_zero, sub_zero]
  rw [ofTwoCocycle.ofProd_eq_add_smul_centralElement, Prod.mk_zero_zero, of_zero, zero_add,
    heisenbergCocycle_single_tmul]

end HeisenbergAlgebra

end TauCeti
