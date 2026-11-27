/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.UniversalEnveloping.PBW.Basis
public import TauCeti.RingTheory.AdicCompletion.ScalarIdeal

import TauCeti.RingTheory.Ideal.Operations
import TauCeti.LinearAlgebra.Submodule.Quotient
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

/-- The canonical map from the ordinary enveloping algebra to its integral completion. -/
def toAdicCompletion : U →ₐ[R] adicCompletion I L :=
  (scalarAdicFiltration I L).toCompletionₐ

/-- The canonical algebra map has the same values as the generic ring completion map. -/
theorem toAdicCompletion_apply (x : U) :
    toAdicCompletion I L x = (scalarAdicFiltration I L).toCompletion x :=
  (scalarAdicFiltration I L).toCompletionₐ_apply x

/-- Projection to the actual finite-order quotient by `I^(k+1) U(L)`. -/
abbrev adicProjection (k : ℕ) :
    adicCompletion I L →ₐ[R] U ⧸ (I.map (algebraMap R U)) ^ (k + 1) :=
  AdicCompletion.extendedIdealCompletionProjection I k

/-- The canonical map computes to the ordinary quotient map at each finite order. -/
@[simp]
theorem adicProjection_toAdicCompletion (k : ℕ) (x : U) :
    adicProjection I L k (toAdicCompletion I L x) =
      Ideal.Quotient.mk ((I.map (algebraMap R U)) ^ (k + 1)) x := by
  rw [AdicCompletion.extendedIdealCompletionProjection_apply, toAdicCompletion_apply,
    TauCeti.AlgFiltration.projection_toCompletion, Ideal.quotientEquivAlgOfEq_mk]

/-- Finite-order projections are compatible with the concrete quotient transition maps. -/
@[simp]
theorem adicProjection_factor {k l : ℕ} (h : k ≤ l) (x : adicCompletion I L) :
    Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.add_le_add_right h 1))
      (adicProjection I L l x) = adicProjection I L k x := by
  let F := scalarAdicFiltration I L
  have he (z : U ⧸ F.ideal (l + 1)) :
      Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.add_le_add_right h 1))
        (Ideal.quotientEquivAlgOfEq R
          (Ideal.algFiltration_ideal (I.map (algebraMap R U)) (l + 1)) z) =
      Ideal.quotientEquivAlgOfEq R (Ideal.algFiltration_ideal (I.map (algebraMap R U)) (k + 1))
        (Ideal.Quotient.factor (F.antitone (Nat.add_le_add_right h 1)) z) := by
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective z
    dsimp only [F]
    simp only [Ideal.quotientEquivAlgOfEq_mk, Ideal.Quotient.factor_mk]
  simp only [AdicCompletion.extendedIdealCompletionProjection_apply]
  rw [he, F.factor_projection h]

/-- All finite-order projections determine an element of the integral completion. -/
@[ext]
theorem adicCompletion_ext {x y : adicCompletion I L}
    (h : ∀ k, adicProjection I L k x = adicProjection I L k y) : x = y := by
  apply (scalarAdicFiltration I L).completion_ext
  intro k
  let e := Ideal.quotientEquivAlgOfEq R (Ideal.algFiltration_ideal (I.map (algebraMap R U)) (k + 1))
  have hk := h k
  simp only [AdicCompletion.extendedIdealCompletionProjection_apply] at hk
  exact e.injective hk

variable {L} {ι : Type w} [LinearOrder ι] (b : Module.Basis ι R L)

/-- Divisibility by `Iⁿ` in the enveloping algebra is scalar divisibility of every PBW
coefficient, on the actual two-sided ideal used in the finite-order quotients. -/
theorem mem_scalarAdicFiltration_iff (n : ℕ) (x : U) :
    x ∈ (scalarAdicFiltration I L).ideal n ↔
      ∀ α, b.pbwBasis.repr x α ∈ I ^ n := by
  rw [Ideal.algFiltration_ideal, ← Submodule.restrictScalars_mem R,
    ← Ideal.pow_smul_top_eq_restrictScalars_map_pow, b.pbwBasis.mem_smul_top_iff]

/-- The PBW coordinate map before taking the quotient, with coefficients reduced mod `Iⁿ`. -/
private noncomputable def adicPBWRepr (n : ℕ) :
    U →ₗ[R] ((ι →₀ ℕ) →₀ (R ⧸ I ^ n)) :=
  (Finsupp.mapRange.linearMap (I ^ n).mkQ).comp b.pbwBasis.repr.toLinearMap

/-- Reduced PBW coordinates are obtained by reducing each ordinary PBW coefficient. -/
@[simp]
private theorem adicPBWRepr_apply (n : ℕ) (x : U) (α : ι →₀ ℕ) :
    adicPBWRepr I b n x α = Ideal.Quotient.mk (I ^ n) (b.pbwBasis.repr x α) := (rfl)

/-- Every finitely supported family of residues lifts to a finite PBW sum. -/
private theorem adicPBWRepr_surjective (n : ℕ) : Function.Surjective (adicPBWRepr I b n) :=
  (Finsupp.mapRange_surjective (I ^ n).mkQ (map_zero _)
    (Submodule.mkQ_surjective _)).comp b.pbwBasis.repr.surjective

/-- The reduced PBW coordinates have exactly the scalar-adic ideal as kernel. -/
private theorem adicPBWRepr_ker (n : ℕ) :
    LinearMap.ker (adicPBWRepr I b n) =
      ((I.map (algebraMap R U)) ^ n).restrictScalars R := by
  ext x
  rw [LinearMap.mem_ker, Submodule.restrictScalars_mem]
  rw [← Ideal.algFiltration_ideal (I.map (algebraMap R U)) n]
  rw [mem_scalarAdicFiltration_iff I b]
  simp only [Finsupp.ext_iff, adicPBWRepr_apply, Finsupp.zero_apply,
    Ideal.Quotient.eq_zero_iff_mem]

/-- Finite-order scalar-adic quotients of the enveloping algebra are precisely finite PBW sums
with coefficients in `R / Iⁿ`. This is a linear equivalence, since PBW coordinates need
not preserve multiplication. -/
noncomputable def adicPBWEquiv (n : ℕ) :
    (U ⧸ (I.map (algebraMap R U)) ^ n) ≃ₗ[R] ((ι →₀ ℕ) →₀ (R ⧸ I ^ n)) :=
  (Ideal.Quotient.mkₐ R ((I.map (algebraMap R U)) ^ n)).toLinearMap
    |>.equivOfSurjectiveOfKerEq (adicPBWRepr I b n)
      (Ideal.Quotient.mkₐ_surjective R _) (adicPBWRepr_surjective I b n) (by
        rw [adicPBWRepr_ker]
        ext x
        simp [Ideal.Quotient.eq_zero_iff_mem])

/-- The finite-order quotient equivalence computes on every ordinary enveloping element. -/
@[simp]
theorem adicPBWEquiv_mk (n : ℕ) (x : U) (α : ι →₀ ℕ) :
    adicPBWEquiv I b n (Ideal.Quotient.mk ((I.map (algebraMap R U)) ^ n) x) α =
      Ideal.Quotient.mk (I ^ n) (b.pbwBasis.repr x α) := by
  -- Observe the private reduced-coordinate map at one exponent.
  change _ = adicPBWRepr I b n x α
  exact congrArg (fun c : ((ι →₀ ℕ) →₀ (R ⧸ I ^ n)) => c α)
    (LinearMap.equivOfSurjectiveOfKerEq_apply
      (Ideal.Quotient.mkₐ R ((I.map (algebraMap R U)) ^ n)).toLinearMap
      (adicPBWRepr I b n) _ _ _ x)

/-- Reduction of finite-order quotients reduces each PBW coefficient by the scalar quotient map. -/
theorem adicPBWEquiv_factor {m n : ℕ} (h : m ≤ n)
    (x : U ⧸ (I.map (algebraMap R U)) ^ n) (α : ι →₀ ℕ) :
    adicPBWEquiv I b m (Ideal.Quotient.factor (Ideal.pow_le_pow_right h) x) α =
      Ideal.Quotient.factor (Ideal.pow_le_pow_right h) (adicPBWEquiv I b n x α) := by
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  simp only [Ideal.Quotient.factor_mk, adicPBWEquiv_mk]

/-- Freeness of the Lie algebra and separatedness of the base suffice for the ordinary
inclusion into the integral completion; finite rank and completeness are not needed. -/
theorem toAdicCompletion_injective [Module.Free R L] [IsHausdorff I R] :
    Function.Injective (toAdicCompletion I L) := by
  classical
  let b := Module.Free.chooseBasis R L
  let : LinearOrder (Module.Free.ChooseBasisIndex R L) :=
    IsWellOrder.linearOrder WellOrderingRel
  let : Module.Free R U := Module.Free.of_basis b.pbwBasis
  let : IsHausdorff I U := IsHausdorff.of_free I U
  intro x y h
  apply AdicCompletion.of_injective I U
  apply (AdicCompletion.extendedIdealCompletionEquiv (A := U) I).injective
  simpa only [AdicCompletion.extendedIdealCompletionEquiv_of, toAdicCompletion,
    TauCeti.AlgFiltration.toCompletionₐ_apply] using h

end TauCeti.UniversalEnvelopingAlgebra
