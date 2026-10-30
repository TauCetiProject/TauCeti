/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Smooth.Local
public import Mathlib.RingTheory.Smooth.StandardSmooth

/-!
# Smoothness after inverting a Jacobian minor

A finite presentation equipped with a choice of as many variables as relations becomes
standard smooth after inverting the corresponding Jacobian determinant. Its relative
dimension is the number of variables minus the number of relations. This provides smooth
coordinate charts for hypersurfaces.

For a hypersurface, one can apply the criterion wherever a chosen partial derivative is
invertible; with several relations, use the determinant of a square Jacobian minor.

A related form of the Jacobian criterion: a local quotient of a formally smooth algebra by
elements whose differentials extend to a basis of the differentials is formally smooth
(`TauCeti.formallySmooth_quotient_of_basis_kaehlerDifferential`).

## References

* Stacks Project, Tag 00T7.
* [Stacks Project, Tag 031I](https://stacks.math.columbia.edu/tag/031I): the conormal sequence of
  a formally smooth quotient is split exact on the left.
-/

public section

namespace Algebra.PreSubmersivePresentation

variable {R S ι σ : Type*} [CommRing R] [CommRing S] [Algebra R S]
  [Finite ι] [Finite σ]

/-- Inverting the selected Jacobian minor of a finite presentation gives a standard smooth
algebra of the dimension of that presentation. -/
theorem isStandardSmoothOfRelativeDimension_localizationAway
    (P : PreSubmersivePresentation R S ι σ) (T : Type*) [CommRing T]
    [Algebra S T] [Algebra R T] [IsScalarTower R S T]
    [IsLocalization.Away P.jacobian T] :
    IsStandardSmoothOfRelativeDimension P.dimension R T := by
  let Q := PreSubmersivePresentation.localizationAway T P.jacobian
  let QP : SubmersivePresentation R T (Unit ⊕ ι) (Unit ⊕ σ) :=
    { Q.comp P with
      jacobian_isUnit := by
        rw [comp_jacobian_eq_jacobian_smul_jacobian, Algebra.smul_def,
          localizationAway_jacobian]
        exact (IsLocalization.Away.algebraMap_isUnit P.jacobian).mul
          (IsLocalization.Away.algebraMap_isUnit P.jacobian) }
  apply QP.isStandardSmoothOfRelativeDimension
  exact (Q.dimension_comp_eq_dimension_add_dimension P).trans (by
    simp [Presentation.dimension])

end Algebra.PreSubmersivePresentation

namespace TauCeti

open KaehlerDifferential TensorProduct

variable {K Q τ ι : Type*} [CommRing K] [CommRing Q] [Algebra K Q] [Algebra.FormallySmooth K Q]
  [Finite τ] [Finite ι]

/-- **Cutting out coordinate hyperplanes preserves smoothness.** Let `Q` be formally smooth over
`K`, and let the differentials of `g : τ → Q` extend to a basis of `Ω[Q⁄K]`. If `Q ⧸ (g)` is local,
then it is formally smooth over `K`. This is the Jacobian criterion: the conormal map of `Q ⧸ (g)`
sends the generators `g t` to part of a basis. -/
theorem formallySmooth_quotient_of_basis_kaehlerDifferential (b : Module.Basis (τ ⊕ ι) Q Ω[Q⁄K])
    {g : τ → Q} (hb : ∀ t, b (.inl t) = D K Q (g t))
    [IsLocalRing (Q ⧸ Ideal.span (Set.range g))] :
    Algebra.FormallySmooth K (Q ⧸ Ideal.span (Set.range g)) := by
  classical
  have : Module.Free Q Ω[Q⁄K] := .of_basis b
  have : Module.Finite Q Ω[Q⁄K] := .of_basis b
  have hN : RingHom.ker (algebraMap Q (Q ⧸ Ideal.span (Set.range g))) =
      Ideal.span (Set.range g) := by
    rw [Ideal.Quotient.algebraMap_eq, Ideal.mk_ker]
  refine (Algebra.FormallySmooth.iff_injective_cotangentComplexBaseChange Q
    (IsLocalRing.ResidueField (Q ⧸ Ideal.span (Set.range g))) Ideal.Quotient.mk_surjective
    (by rw [hN]; exact Submodule.fg_span (Set.finite_range g))
    (by rw [IsLocalRing.ResidueField.algebraMap_eq, IsLocalRing.ker_residue])).2 ?_
  set κ := IsLocalRing.ResidueField (Q ⧸ Ideal.span (Set.range g))
  set N := RingHom.ker (algebraMap Q (Q ⧸ Ideal.span (Set.range g)))
  -- `κ ⊗[Q] N` is spanned by the `1 ⊗ g t`, which map to part of a basis of `κ ⊗[Q] Ω[Q⁄K]`.
  let v : τ → N := fun t ↦ ⟨g t, hN ▸ Ideal.subset_span ⟨t, rfl⟩⟩
  have hvN : Submodule.span Q (Set.range v) = ⊤ := by
    refine Submodule.map_injective_of_injective N.injective_subtype ?_
    rw [Submodule.map_span, Submodule.map_subtype_top, ← Set.range_comp]
    exact hN.symm
  have hv : Submodule.span κ (Set.range fun t ↦ (1 : κ) ⊗ₜ[Q] v t) = ⊤ := by
    rw [← Submodule.baseChange_top, ← hvN, Submodule.baseChange_span, ← Set.range_comp]
    rfl
  let bκ := Algebra.TensorProduct.basis κ b
  have himg (t : τ) : cotangentComplexBaseChange K _ Q κ ((1 : κ) ⊗ₜ v t) = bκ (.inl t) := by
    rw [cotangentComplexBaseChange_tmul, one_smul, kerToTensor_apply,
      Algebra.TensorProduct.basis_apply, hb]
  refine LinearMap.injective_of_linearIndependent hv ?_
  rw [show _ ∘ _ = bκ ∘ Sum.inl from funext himg]
  exact bκ.linearIndependent.comp _ Sum.inl_injective

end TauCeti
