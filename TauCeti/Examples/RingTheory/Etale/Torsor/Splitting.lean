/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Etale.Torsor.Splitting
import Mathlib.NumberTheory.Padics.PadicNumbers

/-!
# Tests for splitting finite étale algebras by finite étale torsors

Concrete checks for `TauCeti.Algebra.FrameAlgebra.universalFrameEquiv`,
`TauCeti.Algebra.FrameAlgebra.isFiniteSplit_tensorProduct`, and
`TauCeti.Algebra.exists_isFiniteEtaleTorsor_isTotallySplit`:

* For the split algebra `Fin n → A` over any commutative ring `A`, the universal frame is an
  isomorphism over `FrameAlgebra A (Fin n → A) (Fin n) ≃ₐ[A] (Equiv.Perm (Fin n) → A)`, and at
  permutation `τ` and slot `i` it evaluates `p ⊗ f` to `(permEquiv A (Fin n) p τ) * f (τ i)`.
* The cubic algebra `S = ℚ[X] ⧸ (X ^ 3 - 2)` is finite étale of rank `3` over `ℚ`, is not split
  over `ℚ` (as `2` has `2`-adic valuation `1`, hence no rational cube root), and becomes finite
  split over its frame algebra `FrameAlgebra ℚ S (Fin 3)`, which is a finite étale
  `Equiv.Perm (Fin 3)`-torsor over `ℚ` of dimension `6`.
* Over a ring `A` with an idempotent `e`, the finite étale algebra `A × (A ⧸ (1 - e))` has
  non-constant rank (`2` on `D(e)` and `1` outside `D(e)`) and is totally split after base change
  to a finite étale torsor over `A`.
* Local-ring, universe-polymorphic, and zero-ring edge cases.
-/

public section

open Polynomial TauCeti.Algebra
open scoped TensorProduct

universe u

namespace TauCeti.Examples.TorsorSplitting

/-- For the split algebra `Fin n → A`, reading the universal frame through `FrameAlgebra.permEquiv`
sends `p ⊗ f` at slot `i` and permutation `τ` to `permEquiv A (Fin n) p τ * f (τ i)`. -/
example (A : Type*) [CommRing A] (n : ℕ) (p : FrameAlgebra A (Fin n → A) (Fin n)) (f : Fin n → A)
    (i : Fin n) (τ : Equiv.Perm (Fin n)) :
    FrameAlgebra.permEquiv A (Fin n) (FrameAlgebra.universalFramePiEquiv A (Fin n) (p ⊗ₜ f) i) τ =
      FrameAlgebra.permEquiv A (Fin n) p τ * f (τ i) := by
  rw [FrameAlgebra.universalFramePiEquiv_tmul, map_mul, Pi.mul_apply,
    FrameAlgebra.permEquiv_singleAlgHom]

section CubicOverRat

/-- The monic polynomial `X ^ 3 - 2` over `ℚ`. -/
noncomputable abbrev cubicTwo : ℚ[X] := X ^ 3 - C 2

/-- `X ^ 3 - 2` is monic over `ℚ`. -/
theorem monic_cubicTwo : cubicTwo.Monic :=
  monic_X_pow_sub_C (n := 3) (2 : ℚ) (by norm_num)

/-- `ℚ[X] ⧸ (X ^ 3 - 2)` is étale over `ℚ`. -/
local instance etale_adjoinRoot_cubicTwo : Algebra.Etale ℚ (AdjoinRoot cubicTwo) :=
  monic_cubicTwo.etale_adjoinRoot_iff.mpr
    (separable_X_pow_sub_C (2 : ℚ) (by norm_num) (by norm_num))

/-- `ℚ[X] ⧸ (X ^ 3 - 2)` is finite étale of dimension `3` over `ℚ`, is not split over `ℚ`, and
becomes finite split over `FrameAlgebra ℚ (AdjoinRoot (X ^ 3 - 2)) (Fin 3)`, which is an
`Equiv.Perm (Fin 3)`-torsor over `ℚ` of dimension `6`. -/
example :
    ¬ Algebra.IsFiniteSplit ℚ (AdjoinRoot cubicTwo) ∧
      IsFiniteEtaleTorsor (Equiv.Perm (Fin 3)) ℚ (FrameAlgebra ℚ (AdjoinRoot cubicTwo) (Fin 3)) ∧
      Module.finrank ℚ (FrameAlgebra ℚ (AdjoinRoot cubicTwo) (Fin 3)) = 6 ∧
      Algebra.IsFiniteSplit (FrameAlgebra ℚ (AdjoinRoot cubicTwo) (Fin 3))
        (FrameAlgebra ℚ (AdjoinRoot cubicTwo) (Fin 3) ⊗[ℚ] AdjoinRoot cubicTwo) := by
  have hfin : Module.finrank ℚ (AdjoinRoot cubicTwo) = Fintype.card (Fin 3) := by
    rw [PowerBasis.finrank (AdjoinRoot.powerBasis' monic_cubicTwo), AdjoinRoot.powerBasis'_dim,
      Fintype.card_fin]
    exact natDegree_X_pow_sub_C (n := 3) (2 : ℚ)
  refine ⟨?_, FrameAlgebra.isFiniteEtaleTorsor_of_finrank_eq hfin, ?_,
    FrameAlgebra.isFiniteSplit_tensorProduct_of_finrank_eq hfin⟩
  · intro hsplit
    obtain ⟨m, ⟨e⟩⟩ := Algebra.IsFiniteSplit.nonempty_algEquiv_fun ℚ (AdjoinRoot cubicTwo)
    have hm : m = 3 := by
      have := e.toLinearEquiv.finrank_eq
      simpa [hfin] using this.symm
    subst hm
    -- Evaluating at coordinate `0` gives a `ℚ`-algebra hom `AdjoinRoot cubicTwo →ₐ[ℚ] ℚ`, hence a
    -- rational cube root of `2`, contradicting `2`-adic valuation in `ℚ_[2]`.
    let φ : AdjoinRoot cubicTwo →ₐ[ℚ] ℚ := (Pi.evalAlgHom ℚ (fun _ : Fin 3 ↦ ℚ) 0).comp e.toAlgHom
    let r : ℚ := φ (AdjoinRoot.root cubicTwo)
    have hr : r ^ 3 = 2 := by
      have hsub : r ^ 3 - 2 = 0 := by
        simpa [cubicTwo, r, ← AdjoinRoot.algebraMap_eq] using
          congrArg φ (AdjoinRoot.aeval_eq cubicTwo)
      exact sub_eq_zero.mp hsub
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hr2 : (r : ℚ_[2]) ^ 3 = (2 : ℕ) := by exact_mod_cast hr
    have hv := congrArg Padic.valuation hr2
    rw [Padic.valuation_pow, Padic.valuation_p] at hv
    omega
  · rw [FrameAlgebra.finrank_eq_factorial hfin, Fintype.card_fin]
    rfl

end CubicOverRat

/-- Over any commutative ring `A` with an idempotent `e`, the finite étale algebra
`A × (A ⧸ (1 - e))` (whose stalk rank is `2` on `D(e)` and `1` outside `D(e)`) becomes totally split
after base change to a finite étale torsor over `A`. -/
example (A : Type u) [CommRing A] (e : A) (he : IsIdempotentElem e) :
    ∃ (G : Type u) (_ : Group G) (_ : Finite G) (P : Type u) (_ : CommRing P)
      (_ : Algebra A P) (_ : MulSemiringAction G P) (_ : SMulCommClass G A P),
      IsFiniteEtaleTorsor G A P ∧
        IsTotallySplit P (P ⊗[A] (A × (A ⧸ Ideal.span {1 - e}))) := by
  have : Algebra.Etale A (A ⧸ Ideal.span {1 - e}) := Etale.quotient_span_singleton he.one_sub
  exact exists_isFiniteEtaleTorsor_isTotallySplit A (A × (A ⧸ Ideal.span {1 - e}))

/-- Over a local ring `A`, every finite étale `A`-algebra becomes finite split (not merely totally
split) after base change to a finite étale torsor over `A`. -/
example (A : Type u) (S : Type*) [CommRing A] [IsLocalRing A] [CommRing S] [Algebra A S]
    [Algebra.Etale A S] [Module.Finite A S] :
    ∃ (G : Type u) (_ : Group G) (_ : Finite G) (P : Type u) (_ : CommRing P)
      (_ : Algebra A P) (_ : MulSemiringAction G P) (_ : SMulCommClass G A P),
      IsFiniteEtaleTorsor G A P ∧ Algebra.IsFiniteSplit P (P ⊗[A] S) :=
  exists_isFiniteEtaleTorsor_isFiniteSplit_of_preconnectedSpace A S

/-- Universe-polymorphic check: when `S` lives in `Type (u + 1)` over `A : Type u`, the splitting
group `G` and torsor `P` are still produced in `Type u`. -/
example (A : Type u) [CommRing A] :
    ∃ (G : Type u) (_ : Group G) (_ : Finite G) (P : Type u) (_ : CommRing P)
      (_ : Algebra A P) (_ : MulSemiringAction G P) (_ : SMulCommClass G A P),
      IsFiniteEtaleTorsor G A P ∧ IsTotallySplit P (P ⊗[A] (ULift.{u + 1} (Fin 2) → A)) :=
  exists_isFiniteEtaleTorsor_isTotallySplit A (ULift.{u + 1} (Fin 2) → A)

/-- Zero-ring edge case: `exists_isFiniteEtaleTorsor_isTotallySplit` holds over `ZMod 1`. -/
example :
    ∃ (G : Type) (_ : Group G) (_ : Finite G) (P : Type) (_ : CommRing P)
      (_ : Algebra (ZMod 1) P) (_ : MulSemiringAction G P) (_ : SMulCommClass G (ZMod 1) P),
      IsFiniteEtaleTorsor G (ZMod 1) P ∧ IsTotallySplit P (P ⊗[ZMod 1] ZMod 1) :=
  exists_isFiniteEtaleTorsor_isTotallySplit (ZMod 1) (ZMod 1)

end TauCeti.Examples.TorsorSplitting
