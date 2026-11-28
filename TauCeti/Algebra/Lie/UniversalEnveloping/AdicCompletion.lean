/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.UniversalEnveloping.PBW.Basis
public import TauCeti.RingTheory.AdicCompletion.ScalarIdeal

import TauCeti.LinearAlgebra.Basis.ExtendedIdeal
import TauCeti.RingTheory.Ideal.Operations
import TauCeti.RingTheory.AdicCompletion.Finite

/-!
# Integral adic completion of a universal enveloping algebra

For an ideal `I` of the scalar ring, `adicCompletion I L` is the integral inverse limit of
`U(L) / Iⁿ U(L)`. In particular `I = Ideal.span {π}` gives the integral scalar-adic
completed enveloping `R`-algebra of a Lie lattice. The positive-order quotient convention
of `AlgFiltration` retains
`U(L) / I^(k+1) U(L)` at order `k`.

The finite-order quotients have finitely supported PBW coordinates in `R / Iⁿ`, and reduction
between finite orders is coordinatewise reduction of scalars. These descriptions prove
that the ordinary enveloping algebra embeds whenever the scalar ring is `I`-adically
separated and the Lie algebra is free, without finite-rank or noetherian hypotheses.

## References

* K. Ardakov and S. J. Wadsley, *On irreducible representations of compact p-adic analytic
  groups*, Annals of Mathematics 178 (2013), §3.7 and §10.4.
* W. Fu, *Sharp bounds for multiplicities of Bianchi modular forms*, Annals of Mathematics
  200 (2024), §§3–4.
-/

public section

namespace TauCeti.UniversalEnvelopingAlgebra

universe u v w

variable {R : Type u} [CommRing R] (I : Ideal R) (L : Type v)
  [LieRing L] [LieAlgebra R L]

local notation "U" => _root_.UniversalEnvelopingAlgebra R L

/-- The scalar-adic filtration of the enveloping algebra, by powers of the central
extended scalar ideal. -/
abbrev scalarAdicFiltration : TauCeti.AlgFiltration U :=
  (I.map (algebraMap R U)).algFiltration

/-- The integral scalar-adic completed enveloping algebra, on the carrier of compatible
families in the finite-order quotient rings. -/
abbrev adicCompletion := (scalarAdicFiltration I L).completion

/-- Projection to the actual finite-order quotient by `I^(k+1) U(L)`. -/
abbrev adicProjection (k : ℕ) :
    adicCompletion I L →ₐ[R] U ⧸ (I.map (algebraMap R U)) ^ (k + 1) :=
  TauCeti.extendedIdealCompletionProjection I k

variable {L} {ι : Type w} [LinearOrder ι] (b : Module.Basis ι R L)

/-- Divisibility by `Iⁿ` in the enveloping algebra is scalar divisibility of every PBW
coefficient, on the actual two-sided ideal used in the finite-order quotients. -/
theorem mem_scalarAdicFiltration_iff (n : ℕ) (x : U) :
    x ∈ (scalarAdicFiltration I L).ideal n ↔
      ∀ α, b.pbwBasis.repr x α ∈ I ^ n := by
  rw [Ideal.algFiltration_ideal, ← Submodule.restrictScalars_mem R,
    ← Ideal.pow_smul_top_eq_restrictScalars_map_pow, b.pbwBasis.mem_smul_top_iff]

/-- Finite-order scalar-adic quotients of the enveloping algebra are precisely finite PBW sums
with coefficients in `R / Iⁿ`. This is a linear equivalence, since PBW coordinates need
not preserve multiplication. -/
noncomputable def adicPBWEquiv (n : ℕ) :
    (U ⧸ (I.map (algebraMap R U)) ^ n) ≃ₗ[R] ((ι →₀ ℕ) →₀ (R ⧸ I ^ n)) :=
  (Ideal.quotientEquivAlgOfEq R (Ideal.map_algebraMap_pow I n).symm).toLinearEquiv ≪≫ₗ
    b.pbwBasis.quotientEquiv (I ^ n)

/-- The finite-order quotient equivalence computes on every ordinary enveloping element. -/
@[simp]
theorem adicPBWEquiv_mk (n : ℕ) (x : U) (α : ι →₀ ℕ) :
    adicPBWEquiv I b n (Ideal.Quotient.mk ((I.map (algebraMap R U)) ^ n) x) α =
      Ideal.Quotient.mk (I ^ n) (b.pbwBasis.repr x α) := by
  simp [adicPBWEquiv]

/-- A single finite-order PBW coefficient is represented by the corresponding scalar
multiple of the ordered PBW monomial. -/
@[simp↓]
theorem adicPBWEquiv_symm_single (n : ℕ) (α : ι →₀ ℕ) (r : R) :
    (adicPBWEquiv I b n).symm (Finsupp.single α (Ideal.Quotient.mk (I ^ n) r)) =
      Ideal.Quotient.mk _ (r • b.pbwBasis α) := by
  simp [adicPBWEquiv, ← AlgEquiv.toLinearEquiv_symm]

/-- Reduction of finite-order quotients reduces each PBW coefficient by the scalar quotient map. -/
theorem adicPBWEquiv_factor {m n : ℕ} (h : m ≤ n)
    (x : U ⧸ (I.map (algebraMap R U)) ^ n) (α : ι →₀ ℕ) :
    adicPBWEquiv I b m (Ideal.Quotient.factor (Ideal.pow_le_pow_right h) x) α =
      Ideal.Quotient.factor (Ideal.pow_le_pow_right h) (adicPBWEquiv I b n x α) := by
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  simp only [Ideal.Quotient.factor_mk, adicPBWEquiv_mk]

/-- Freeness of the Lie algebra and separatedness of the base suffice for the ordinary
inclusion into the integral completion; finite rank and completeness are not needed. -/
theorem toCompletionₐ_injective [Module.Free R L] [IsHausdorff I R] :
    Function.Injective ((scalarAdicFiltration I L).toCompletionₐ (R := R)) := by
  classical
  let b := Module.Free.chooseBasis R L
  let : LinearOrder (Module.Free.ChooseBasisIndex R L) :=
    IsWellOrder.linearOrder WellOrderingRel
  let : Module.Free R U := Module.Free.of_basis b.pbwBasis
  let : IsHausdorff I U := IsHausdorff.of_free I U
  exact TauCeti.toCompletionₐ_injective_of_isHausdorff I

end TauCeti.UniversalEnvelopingAlgebra
