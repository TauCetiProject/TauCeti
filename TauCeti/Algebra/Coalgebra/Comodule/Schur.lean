/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Coalgebra.Comodule.Convolution.Module
public import TauCeti.Algebra.Coalgebra.Comodule.Inverse
public import TauCeti.Algebra.Coalgebra.Comodule.MatrixCoefficient.Intertwiner
public import TauCeti.Algebra.Coalgebra.Subcomodule.Convolution
import TauCeti.Algebra.Coalgebra.Subcomodule.Finite

/-!
# Schur's lemma for comodules

Let `C` be a coalgebra that is projective over a commutative ring `R`. Through the isomorphism
between right `C`-subcomodules and `WithConv (C →ₗ[R] R)`-submodules, Schur's lemma for simple
modules transfers to simple right comodules: every morphism out of a simple comodule is injective
or zero, every morphism into a simple comodule is surjective or zero, and every nonzero morphism
between simple comodules is bijective.

Over an algebraically closed field `k`, every simple comodule is automatically finite dimensional
by the fundamental theorem of comodules, and every comodule endomorphism of a simple comodule is a
scalar multiple of the identity (`TauCeti.Comodule.Hom.exists_eq_smul_id`). Consequently any scalar
matrix commuting with the coefficient matrix of a finite basis of a simple comodule is a scalar
multiple of the identity matrix (`Module.Basis.exists_eq_smul_one_of_commute_coefficientMatrix`).

## Main declarations

* `TauCeti.Comodule.finite_of_isSimpleOrder`: every simple comodule over a projective coalgebra is
  finitely generated as a module.
* `TauCeti.Comodule.Hom.injective_or_eq_zero`, `TauCeti.Comodule.Hom.surjective_or_eq_zero`, and
  `TauCeti.Comodule.Hom.bijective_of_ne_zero`: structural Schur's lemma for morphisms between
  simple comodules.
* `TauCeti.Comodule.Hom.exists_eq_smul_id`: over an algebraically closed field, every endomorphism
  of a simple comodule is multiplication by a scalar.
* `TauCeti.Comodule.Hom.exists_eq_smul_of_ne_zero`: over an algebraically closed field, the space of
  comodule morphisms between two simple comodules is at most one-dimensional.
* `Module.Basis.exists_eq_smul_one_of_commute_coefficientMatrix`: matrix form of Schur's lemma for
  the coefficient matrix of a finite basis of a simple comodule.

## References

* M. Sweedler, *Hopf Algebras*, W. A. Benjamin, 1969, Chapter 2.
* W. C. Waterhouse, *Introduction to Affine Group Schemes*, Springer, 1979, Section 3.5.
-/

public section

open Module TauCeti TauCeti.Comodule

/-- If the coefficient coalgebra is projective over `R`, every simple right comodule is finitely
generated over `R`. -/
theorem TauCeti.Comodule.finite_of_isSimpleOrder {R C M : Type*} [CommSemiring R]
    [AddCommMonoid C] [Module R C] [Coalgebra R C] [Module.Projective R C]
    [AddCommMonoid M] [Module R M] [Comodule R C M] [IsSimpleOrder (Subcomodule R C M)] :
    Module.Finite R M := by
  have hfin : Module.Finite R (⊤ : Subcomodule R C M).toSubmodule :=
    Subcomodule.finite_of_isAtom (R := R) (C := C) isAtom_top
  rw [Subcomodule.top_toSubmodule] at hfin
  exact Module.Finite.equiv (Submodule.topEquiv (R := R) (M := M))

namespace TauCeti.Comodule.Hom

section Ring

variable {R C M N : Type*} [CommRing R]
  [AddCommGroup C] [Module R C] [Coalgebra R C] [Module.Projective R C]
  [AddCommGroup M] [Module R M] [Comodule R C M]
  [AddCommGroup N] [Module R N] [Comodule R C N]

attribute [local instance] Comodule.convolutionModule

/-- Every comodule morphism out of a simple comodule is either injective or zero. -/
theorem injective_or_eq_zero [IsSimpleOrder (Subcomodule R C M)] (f : Hom R C M N) :
    Function.Injective f ∨ f = 0 := by
  have := isSimpleModule_convolution_iff.mpr ‹IsSimpleOrder (Subcomodule R C M)›
  have hcoe : (⇑f.toConvolutionLinearMap : M → N) = ⇑f := funext f.toConvolutionLinearMap_apply
  rcases f.toConvolutionLinearMap.injective_or_eq_zero with h | h
  · exact .inl (hcoe ▸ h)
  · exact .inr (ext fun m ↦ by simpa using LinearMap.congr_fun h m)

/-- Every comodule morphism into a simple comodule is either surjective or zero. -/
theorem surjective_or_eq_zero [IsSimpleOrder (Subcomodule R C N)] (f : Hom R C M N) :
    Function.Surjective f ∨ f = 0 := by
  have := isSimpleModule_convolution_iff.mpr ‹IsSimpleOrder (Subcomodule R C N)›
  have hcoe : (⇑f.toConvolutionLinearMap : M → N) = ⇑f := funext f.toConvolutionLinearMap_apply
  rcases f.toConvolutionLinearMap.surjective_or_eq_zero with h | h
  · exact .inl (hcoe ▸ h)
  · exact .inr (ext fun m ↦ by simpa using LinearMap.congr_fun h m)

/-- Every nonzero comodule morphism between simple comodules is bijective. -/
theorem bijective_of_ne_zero [IsSimpleOrder (Subcomodule R C M)]
    [IsSimpleOrder (Subcomodule R C N)] {f : Hom R C M N} (hf : f ≠ 0) :
    Function.Bijective f :=
  ⟨(f.injective_or_eq_zero).resolve_right hf, (f.surjective_or_eq_zero).resolve_right hf⟩

/-- Every comodule morphism between simple comodules is either bijective or zero. -/
theorem bijective_or_eq_zero [IsSimpleOrder (Subcomodule R C M)]
    [IsSimpleOrder (Subcomodule R C N)] (f : Hom R C M N) :
    Function.Bijective f ∨ f = 0 := by
  by_cases hf : f = 0
  · exact .inr hf
  · exact .inl (f.bijective_of_ne_zero hf)

end Ring

section AlgClosed

variable {k C M N : Type*} [Field k] [IsAlgClosed k]
  [AddCommGroup C] [Module k C] [Coalgebra k C]
  [AddCommGroup M] [Module k M] [Comodule k C M]
  [AddCommGroup N] [Module k N] [Comodule k C N]

/-- **Schur's lemma for comodules.** Over an algebraically closed field, every endomorphism of a
simple comodule is multiplication by a scalar. No finite-dimensionality hypothesis on `M` is
needed because every simple comodule over a field is finite dimensional. -/
theorem exists_eq_smul_id [IsSimpleOrder (Subcomodule k C M)] (f : Hom k C M M) :
    ∃ c : k, f = c • Hom.id k C M := by
  have : Module.Finite k M := Comodule.finite_of_isSimpleOrder (C := C)
  have hIrr : Representation.IsIrreducible
      (convolutionAction (R := k) (C := C) (M := M)).toMonoidHom :=
    isIrreducible_convolutionAction
  obtain ⟨c, hc⟩ := hIrr.exists_forall_apply_eq_smul f.toLinearMap fun φ m ↦
    f.map_convolutionAction φ m
  exact ⟨c, ext hc⟩

/-- Over an algebraically closed field, any morphism between simple comodules is a scalar multiple
of any nonzero morphism between them. -/
theorem exists_eq_smul_of_ne_zero [IsSimpleOrder (Subcomodule k C M)]
    [IsSimpleOrder (Subcomodule k C N)] {f : Hom k C M N} (hf : f ≠ 0) (g : Hom k C M N) :
    ∃ c : k, g = c • f := by
  have hbij := f.bijective_of_ne_zero hf
  obtain ⟨c, hc⟩ := exists_eq_smul_id ((f.inverse hbij).comp g)
  refine ⟨c, ?_⟩
  calc g = (Hom.id k C N).comp g := (id_comp g).symm
    _ = (f.comp (f.inverse hbij)).comp g := by rw [comp_inverse]
    _ = f.comp ((f.inverse hbij).comp g) := comp_assoc _ _ _
    _ = f.comp (c • Hom.id k C M) := by rw [hc]
    _ = c • f := toLinearMap_injective (by simp)

end AlgClosed

end TauCeti.Comodule.Hom

namespace Module.Basis

variable {k A M ι : Type*} [Field k] [IsAlgClosed k]
  [Ring A] [Algebra k A] [Coalgebra k A]
  [AddCommGroup M] [Module k M] [Comodule k A M] [IsSimpleOrder (Subcomodule k A M)]
  [Fintype ι] [DecidableEq ι]

/-- **Matrix form of Schur's lemma.** If a scalar matrix `T` commutes with the coefficient matrix
of a finite basis of a simple comodule over an algebraically closed field, then `T` is a scalar
multiple of the identity matrix. -/
theorem exists_eq_smul_one_of_commute_coefficientMatrix (b : Basis ι k M) (T : Matrix ι ι k)
    (hT : coefficientMatrix (C := A) b * T.map (algebraMap k A) =
      T.map (algebraMap k A) * coefficientMatrix (C := A) b) :
    ∃ c : k, T = c • (1 : Matrix ι ι k) := by
  let φ : Hom k A M M :=
    { toLinearMap := Matrix.toLin b b T
      map_coact := (b.map_coact_iff_coefficientMatrix b (Matrix.toLin b b T)).mpr (by
        simpa [LinearMap.toMatrix_toLin] using hT) }
  obtain ⟨c, hc⟩ := φ.exists_eq_smul_id
  refine ⟨c, ?_⟩
  calc T = LinearMap.toMatrix b b φ.toLinearMap := (LinearMap.toMatrix_toLin b b T).symm
    _ = LinearMap.toMatrix b b (c • LinearMap.id) := by
      rw [congrArg Hom.toLinearMap hc, Hom.smul_toLinearMap, Hom.id_toLinearMap]
    _ = c • (1 : Matrix ι ι k) := by rw [map_smul, LinearMap.toMatrix_id]

end Module.Basis
