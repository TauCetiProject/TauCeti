/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.Loop
public import TauCeti.Algebra.Lie.Extension.Basic
public import TauCeti.Algebra.Lie.InvariantForm.Basic
import TauCeti.Algebra.Lie.Loop.Cocycle

/-!
# The Heisenberg Lie algebra of a symmetric bilinear space

Let `H` be an abelian Lie algebra over an additively torsion-free commutative ring `R`, for
instance a vector space over a field of characteristic zero with the zero bracket, and let `B` be
a symmetric bilinear form on `H`, possibly degenerate or zero. The **Heisenberg Lie algebra** of
`(H, B)` is the central extension

`Heis = H[t, t⁻¹] ⊕ R K`

of the loop algebra of `H` by the 2-cocycle `c(x, y) = Σ_m m B(x_m, y_{-m})`, where `x_m` is the
coefficient of `t^m`. On modes `h(m) = h ⊗ t^m` the bracket is

`⁅h(m), k(n)⁆ = m B(h, k) δ_{m + n, 0} K`,

and `K` is central. Mathlib's residue cocycle `LieAlgebra.LoopAlgebra.twoCocycleOfBilinear` uses
`+Res(f dg)`, which is the mode factor of the *second* argument, so the Heisenberg cocycle is
Mathlib's residue cocycle of `-B` (`TauCeti.heisenbergCocycle`); every form on an abelian Lie
algebra is invariant, so no invariance hypothesis is needed. The Heisenberg algebra is then
Mathlib's cocycle extension `LieAlgebra.ofTwoCocycle` (`TauCeti.loopHeisenberg`), and the
extension API of `TauCeti.Algebra.Lie.Extension.Basic` (the central element `K`, projections,
maps of extensions) applies to it directly.

The mode factor makes the cocycle alternating: `c(h(1), h(-1)) = B(h, h)` while
`c(h(-1), h(1)) = -B(h, h)`. For a Cartan subalgebra `𝔥` of a simple Lie algebra and the
restriction of a shifted level form, this is the Heisenberg algebra of the free-field (Wakimoto)
realisation of affine algebras.

## Main definitions

* `TauCeti.heisenbergCocycle`: the Heisenberg 2-cocycle on `H[t, t⁻¹]`.
* `TauCeti.loopHeisenberg`: the Heisenberg Lie algebra `H[t, t⁻¹] ⊕ R K`.
* `TauCeti.heisenbergMode`: the modes `h ↦ h(n)`, as linear maps `H → Heis`.

## Main results

* `TauCeti.heisenbergCocycle_single_tmul`: the cocycle on modes is `m B(h, k) δ_{m + n, 0}`.
* `TauCeti.lie_heisenbergMode_heisenbergMode`: **the Heisenberg relations**
  `⁅h(m), k(n)⁆ = m B(h, k) δ_{m + n, 0} K`, with the special cases
  `TauCeti.lie_heisenbergMode_heisenbergMode_neg` and
  `TauCeti.lie_heisenbergMode_heisenbergMode_of_add_ne_zero`.
* `TauCeti.loopHeisenberg.induction_on`: every element is a sum of modes and a multiple of `K`.
* `TauCeti.loopHeisenberg.lieHom_ext`: Lie algebra maps out of `Heis` agreeing on modes and on `K`
  are equal.

## References

* E. Frenkel, *Langlands Correspondence for Loop Groups*, §6.2.1, equation (6.2-1).
* V. G. Kac, *Vertex Algebras for Beginners*, 2nd ed., Example 1.3 and §3.5, for the free boson
  in characteristic zero.
-/

public section

noncomputable section

open scoped TensorProduct
open LieAlgebra LieAlgebra.LoopAlgebra LieModule.Cohomology

namespace TauCeti

variable {R H : Type*} [CommRing R] [HasUniqueDiv R] [LieRing H] [LieAlgebra R H]
  [IsLieAbelian H]

variable (B : LinearMap.BilinForm R H) (hB : B.IsSymm)

/-- The **Heisenberg 2-cocycle** `c(x, y) = Σ_m m B(x_m, y_{-m})` on the loop algebra
`H[t, t⁻¹]` of an abelian Lie algebra `H` with a symmetric form `B`. It is Mathlib's residue
cocycle, normalised by the mode of the second argument, of the form `-B`. -/
def heisenbergCocycle :
    twoCocycle R (loopAlgebra R ℤ H) (TrivialLieModule R (loopAlgebra R ℤ H) R) :=
  twoCocycleOfBilinear R ℤ H (-B) (-B).lieInvariant_of_isTrivial
    (LinearMap.BilinForm.isSymm_neg.2 hB)

/-- The **Heisenberg Lie algebra** `Heis = H[t, t⁻¹] ⊕ R K` of an abelian Lie algebra `H` with a
symmetric form `B`: the central extension of the loop algebra of `H` by the Heisenberg cocycle,
with bracket `⁅h(m), k(n)⁆ = m B(h, k) δ_{m + n, 0} K` on modes. -/
abbrev loopHeisenberg : Type _ :=
  ofTwoCocycle (heisenbergCocycle B hB)

/-- The Heisenberg cocycle on modes: `c(h(m), k(n)) = m B(h, k)` when `m + n = 0`, and zero
otherwise. -/
theorem heisenbergCocycle_single_tmul (m n : ℤ) (h k : H) :
    TrivialLieModule.equiv R (loopAlgebra R ℤ H) R
        ((heisenbergCocycle B hB : loopAlgebra R ℤ H →ₗ[R] loopAlgebra R ℤ H →ₗ[R]
          TrivialLieModule R (loopAlgebra R ℤ H) R)
          (AddMonoidAlgebra.single m 1 ⊗ₜ h) (AddMonoidAlgebra.single n 1 ⊗ₜ k)) =
      if m + n = 0 then (m : R) * B h k else 0 := by
  rw [twoCochain_val_apply, heisenbergCocycle, twoCocycleOfBilinear_coe,
    twoCochainOfBilinear_apply_apply, LinearEquiv.apply_symm_apply,
    TauCeti.LieAlgebra.LoopAlgebra.residuePairing_single_tmul]
  split_ifs with hmn
  · rw [eq_neg_of_add_eq_zero_right hmn, LinearMap.neg_apply, LinearMap.neg_apply, neg_smul,
      smul_neg, neg_neg, zsmul_eq_mul]
  · rfl

/-- The mode `h(n) = h ⊗ tⁿ` of an element `h : H` in the Heisenberg Lie algebra. -/
def heisenbergMode (n : ℤ) : H →ₗ[R] loopHeisenberg B hB :=
  (ofProdLinearEquiv (heisenbergCocycle B hB)).toLinearMap ∘ₗ LinearMap.inl R _ _ ∘ₗ
    TensorProduct.mk R (AddMonoidAlgebra R ℤ) H (AddMonoidAlgebra.single n 1)

/-- The coordinates of the mode `h(n)` are `(h ⊗ tⁿ, 0)`. -/
theorem heisenbergMode_apply (n : ℤ) (h : H) :
    heisenbergMode B hB n h =
      ofProd (heisenbergCocycle B hB) (AddMonoidAlgebra.single n 1 ⊗ₜ h, 0) := by
  simp [heisenbergMode]

/-- The **Heisenberg relations**: `⁅h(m), k(n)⁆ = m B(h, k) δ_{m + n, 0} K`, where `K` is the
central element of the extension. -/
theorem lie_heisenbergMode_heisenbergMode (m n : ℤ) (h k : H) :
    ⁅heisenbergMode B hB m h, heisenbergMode B hB n k⁆ =
      (if m + n = 0 then (m : R) * B h k else 0) •
        ofTwoCocycle.centralElement (heisenbergCocycle B hB) := by
  rw [heisenbergMode_apply, heisenbergMode_apply, bracket_ofTwoCocycle,
    ofTwoCocycle.ofProd_eq_add_smul_centralElement]
  simp only [Equiv.symm_apply_apply, trivial_lie_zero, ExtendScalars.bracket_tmul, sub_zero,
    add_zero, TensorProduct.tmul_zero]
  rw [heisenbergCocycle_single_tmul, ← Prod.zero_eq_mk, of_zero, zero_add]

/-- The bracket of opposite modes: `⁅h(m), k(-m)⁆ = m B(h, k) K`. -/
theorem lie_heisenbergMode_heisenbergMode_neg (m : ℤ) (h k : H) :
    ⁅heisenbergMode B hB m h, heisenbergMode B hB (-m) k⁆ =
      ((m : R) * B h k) • ofTwoCocycle.centralElement (heisenbergCocycle B hB) := by
  simp only [lie_heisenbergMode_heisenbergMode, add_neg_cancel, ↓reduceIte]

/-- Modes whose indices do not add up to zero commute. -/
theorem lie_heisenbergMode_heisenbergMode_of_add_ne_zero {m n : ℤ} (hmn : m + n ≠ 0) (h k : H) :
    ⁅heisenbergMode B hB m h, heisenbergMode B hB n k⁆ = 0 := by
  simp only [lie_heisenbergMode_heisenbergMode, hmn, ↓reduceIte, zero_smul]

namespace loopHeisenberg

/-- **Induction on the Heisenberg algebra**: a property of elements of `Heis` that holds for every
mode and every multiple of `K` and is closed under addition holds everywhere. -/
@[elab_as_elim]
theorem induction_on {motive : loopHeisenberg B hB → Prop} (x : loopHeisenberg B hB)
    (mode : ∀ (n : ℤ) (h : H), motive (heisenbergMode B hB n h))
    (central : ∀ r : R, motive (r • ofTwoCocycle.centralElement (heisenbergCocycle B hB)))
    (add : ∀ x y, motive x → motive y → motive (x + y)) : motive x := by
  obtain ⟨⟨p, z⟩, rfl⟩ := (ofProd (heisenbergCocycle B hB)).surjective x
  rw [ofTwoCocycle.ofProd_eq_add_smul_centralElement]
  refine add _ _ ?_ (central _)
  obtain ⟨f, rfl⟩ := (toFinsupp R ℤ H).symm.surjective p
  induction f using Finsupp.induction_linear with
  | zero =>
    simpa [heisenbergMode_apply] using mode 0 0
  | add f g hf hg =>
    rw [map_add, ← add_zero (0 : TrivialLieModule R (loopAlgebra R ℤ H) R), ← Prod.mk_add_mk,
      of_add]
    exact add _ _ hf hg
  | single n h =>
    rw [toFinsupp_symm_single, ← heisenbergMode_apply]
    exact mode n h

/-- Two linear maps out of the Heisenberg algebra agreeing on all modes and on `K` are equal. -/
theorem linearMap_ext {M : Type*} [AddCommGroup M] [Module R M]
    {f g : loopHeisenberg B hB →ₗ[R] M}
    (hmode : ∀ (n : ℤ) (h : H), f (heisenbergMode B hB n h) = g (heisenbergMode B hB n h))
    (hK : f (ofTwoCocycle.centralElement (heisenbergCocycle B hB)) =
      g (ofTwoCocycle.centralElement (heisenbergCocycle B hB))) :
    f = g :=
  LinearMap.ext fun x => induction_on B hB x hmode (fun r => by rw [map_smul, map_smul, hK])
    fun x y hx hy => by rw [map_add, map_add, hx, hy]

/-- Two Lie algebra maps out of the Heisenberg algebra agreeing on all modes and on `K` are
equal. -/
theorem lieHom_ext {L : Type*} [LieRing L] [LieAlgebra R L] {f g : loopHeisenberg B hB →ₗ⁅R⁆ L}
    (hmode : ∀ (n : ℤ) (h : H), f (heisenbergMode B hB n h) = g (heisenbergMode B hB n h))
    (hK : f (ofTwoCocycle.centralElement (heisenbergCocycle B hB)) =
      g (ofTwoCocycle.centralElement (heisenbergCocycle B hB))) :
    f = g :=
  LieHom.ext (LinearMap.congr_fun
    (linearMap_ext B hB (f := f.toLinearMap) (g := g.toLinearMap) hmode hK))

end loopHeisenberg

end TauCeti
