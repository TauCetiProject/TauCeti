/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Smooth.Local
public import TauCeti.RingTheory.FittingIdeal.BaseChange
public import Mathlib.RingTheory.Smooth.Locus
import Mathlib.RingTheory.Kaehler.Polynomial
import Mathlib.RingTheory.Localization.Algebra
import Mathlib.RingTheory.TensorProduct.IsBaseChangeFree
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.TensorProduct.RightExactness

/-!
# Smoothness from the rank of the differentials

For a local quotient of a formally smooth algebra with `r` independent differentials and
`c` defining equations, the fibre of the differentials has dimension at least `r - c`.
If its dimension is at most `r - c`, the conormal map is injective and the quotient is
formally smooth. This criterion identifies the smooth part of complete intersection curves
using the first Fitting ideal of their differentials.

## References

* The Stacks Project, Tag 00T7 (standard smooth algebras and their differentials).
* The local conormal criterion is Mathlib's
  `Algebra.FormallySmooth.iff_injective_lTensor_residueField`.
-/

public section

noncomputable section

open Module TensorProduct IsLocalRing

namespace Algebra.Extension

variable {R S ι σ : Type*} [CommRing R] [CommRing S] [Algebra R S] [IsLocalRing S]
  [Fintype ι] [Fintype σ]

/-- A local quotient of a formally smooth algebra with `r` independent differentials and
`c` equations is formally smooth if the residue-field fibre of its differentials has
dimension at most `r - c`. The additive bound avoids truncated subtraction. -/
theorem formallySmooth_of_finrank_kaehlerDifferential_add_le
    (P : Extension R S) [FormallySmooth R P.Ring]
    (b : Basis ι P.Ring Ω[P.Ring⁄R]) (s : σ → P.Ring)
    (hs : Ideal.span (Set.range s) = P.ker)
    (h : finrank (ResidueField S) (ResidueField S ⊗[S] Ω[S⁄R]) +
      Fintype.card σ ≤ Fintype.card ι) : FormallySmooth R S := by
  classical
  have : Module.Free P.Ring Ω[P.Ring⁄R] := .of_basis b
  have : Module.Finite P.Ring Ω[P.Ring⁄R] := .of_basis b
  let v : σ → P.Cotangent := fun i ↦ .mk ⟨s i, hs.le (Ideal.subset_span ⟨i, rfl⟩)⟩
  have hv : Submodule.span S (Set.range v) = ⊤ :=
    Cotangent.span_eq_top_of_span_eq_ker s hs
  have : Module.Finite S P.Cotangent := ⟨hv ▸ Submodule.fg_span (Set.finite_range v)⟩
  let f := P.cotangentComplex.baseChange (ResidueField S)
  let g := P.toKaehler.baseChange (ResidueField S)
  have hfg : Function.Exact f g :=
    lTensor_exact (ResidueField S) P.exact_cotangentComplex_toKaehler P.toKaehler_surjective
  have hg : Function.Surjective g :=
    LinearMap.lTensor_surjective (ResidueField S) P.toKaehler_surjective
  have hsource : finrank (ResidueField S) (ResidueField S ⊗[S] P.Cotangent) ≤ Fintype.card σ := by
    apply finrank_le_of_span_eq_top (v := fun i ↦ (1 : ResidueField S) ⊗ₜ[S] v i)
    simpa only [Submodule.baseChange_span, ← Set.range_comp, Function.comp_def, mk_apply,
      Submodule.baseChange_top] using congrArg (Submodule.baseChange (ResidueField S)) hv
  have hmiddle : finrank (ResidueField S) (ResidueField S ⊗[S] P.CotangentSpace) =
      Fintype.card ι := by
    exact finrank_eq_card_basis
      ((Algebra.TensorProduct.basis (ResidueField S) b).map
        (AlgebraTensorModule.cancelBaseChange P.Ring S
          (ResidueField S) (ResidueField S) Ω[P.Ring⁄R]).symm)
  have hrank := g.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr hg, finrank_top,
    hfg.linearMap_ker_eq, hmiddle] at hrank
  have hnull := f.finrank_range_add_finrank_ker
  have hker : LinearMap.ker f = ⊥ := Submodule.finrank_eq_zero.mp (by omega)
  exact (FormallySmooth.iff_injective_lTensor_residueField P
    (hs ▸ Submodule.fg_span (Set.finite_range s))).mpr (by
      simpa only [LinearMap.baseChange_eq_lTensor] using
        (LinearMap.ker_eq_bot.mp hker :
          Function.Injective (P.cotangentComplex.baseChange (ResidueField S))))

end Algebra.Extension

namespace Algebra.Presentation

open KaehlerDifferential TauCeti

variable {R S ι σ : Type*} [CommRing R] [CommRing S] [Algebra R S]
  [Finite ι] [Finite σ]

/-- A finite presentation with at least `n` more variables than relations is smooth at every
prime outside the `n`-th Fitting locus of its differentials. This is the Jacobian criterion
expressed without choosing a minor of the Jacobian matrix. -/
theorem isSmoothAt_of_not_fittingIdeal_le (P : Presentation R S ι σ) {n : ℕ}
    (hcard : n + Nat.card σ ≤ Nat.card ι) (q : Ideal S) [q.IsPrime] :
    letI := P.finitePresentation_of_isFinite
    ¬ fittingIdeal S Ω[S⁄R] n ≤ q → IsSmoothAt R q := by
  classical
  let := Fintype.ofFinite ι
  let := Fintype.ofFinite σ
  have := P.finitePresentation_of_isFinite
  intro h
  -- Localize the polynomial presentation at the prime above `q`.
  let q' := q.comap (algebraMap P.Ring S)
  let Q := Localization.AtPrime q'
  let A := Localization.AtPrime q
  have : FormallyEtale P.Ring Q := .of_isLocalization q'.primeCompl
  have : FormallySmooth R Q := .comp R P.Ring Q
  have hT : q'.primeCompl.map (algebraMap P.Ring S) = q.primeCompl :=
    Ideal.map_primeCompl_comap_of_surjective _ P.algebraMap_surjective q
  have : IsLocalization (q'.primeCompl.map (algebraMap P.Ring S)) A := by
    rw [hT]
    infer_instance
  let π₀ : Q →+* A :=
    IsLocalization.map A (algebraMap P.Ring S) (hT.symm ▸ q'.primeCompl.le_comap_map)
  have hπ₀ (r : P.Ring) : π₀ (algebraMap P.Ring Q r) =
      algebraMap S A (algebraMap P.Ring S r) := IsLocalization.map_eq _ _
  let π : Q →ₐ[R] A := { π₀ with
    commutes' := fun r ↦ by
      rw [IsScalarTower.algebraMap_apply R P.Ring Q r]
      exact (hπ₀ _).trans (by rw [← IsScalarTower.algebraMap_apply,
        ← IsScalarTower.algebraMap_apply]) }
  have hπ : Function.Surjective π :=
    IsLocalization.map_surjective_of_surjective _ _ _ P.algebraMap_surjective
  let E := Extension.ofSurjective π hπ
  -- The extension retains the ambient ring `Q`; only its surjection is bundled.
  have : FormallySmooth R E.Ring := (inferInstance : FormallySmooth R Q)
  let b : Basis ι Q Ω[Q⁄R] :=
    (isBaseChange_of_formallyEtale R P.Ring Q).basis (mvPolynomialBasis R ι)
  have hker : Ideal.span (Set.range (algebraMap P.Ring Q ∘ P.relation)) = E.ker := by
    rw [Set.range_comp, ← Ideal.map_span, P.span_range_relation_eq_ker]
    exact (IsLocalization.ker_map (S := Q) A (algebraMap P.Ring S) hT).symm
  -- Localization carries the Fitting ideal to the Fitting ideal of the local differentials.
  have hlocal : finrank (ResidueField A) (ResidueField A ⊗[A] Ω[A⁄R]) ≤ n := by
    apply Nat.le_of_not_gt
    intro hlt
    apply h
    have hzero := (fittingIdeal_map_eq_bot_iff_lt_finrank (R := A) (M := Ω[A⁄R])
      (ResidueField A) n).mpr hlt
    rw [(isBaseChange_of_formallyEtale R S A).fittingIdeal_eq_map n,
      Ideal.map_map, Ideal.map_eq_bot_iff_le_ker, ← RingHom.comap_ker,
      ResidueField.algebraMap_eq, ker_residue] at hzero
    exact hzero.trans (Localization.AtPrime.under_maximalIdeal (I := q)).le
  apply E.formallySmooth_of_finrank_kaehlerDifferential_add_le b
    (algebraMap P.Ring Q ∘ P.relation) hker
  simpa only [Nat.card_eq_fintype_card] using (Nat.add_le_add_right hlocal _).trans hcard

end Algebra.Presentation
