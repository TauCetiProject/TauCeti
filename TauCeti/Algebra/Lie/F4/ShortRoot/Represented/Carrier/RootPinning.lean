/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.F4.ShortRoot.Represented.Carrier.PointAction
public import TauCeti.Algebra.Lie.F4.ShortRoot.Quotient.Exponential

/-!
# Root pinning of the represented F4 quotient comodule

The actual carrier action on its represented middle quotient agrees with the special-isogeny
root formulas. The comparison descends the integral conjugation identity and then uses the
structural quotient-column pinning; it does not compute a new matrix table.

## References

* R. Steinberg, *Endomorphisms of linear algebraic groups*, Memoirs AMS 80 (1968), §11.
* R. W. Carter, *Simple Groups of Lie Type*, §12.3.
-/

public section

namespace TauCeti.DynkinType

open CategoryTheory
open scoped TensorProduct

noncomputable section

local notation "𝔽₂" => ZMod 2

variable {A : Type} [CommRing A] [Algebra 𝔽₂ A]

private theorem repr_comp_of_basis
    {R M N ι : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
    [AddCommMonoid N] [Module R N]
    (b : Module.Basis ι R M) (c : Module.Basis ι R N) (f : M →ₗ[R] N)
    (hf : ∀ i, f (b i) = c i) (x : M) : c.repr (f x) = b.repr x := by
  have h : c.repr.toLinearMap ∘ₗ f = b.repr.toLinearMap := by
    apply b.ext
    intro i
    exact (congrArg c.repr (hf i)).trans
      ((c.repr_self i).trans (b.repr_self i).symm)
  exact DFunLike.congr_fun h x

/-- The prescribed quotient and ideal bases have the same coordinates under the pinned
identification after scalar extension. -/
theorem f4ShortRootLieIdealBasis_repr_quotientToIdeal
    (x : A ⊗[𝔽₂] (f4ModularChevalleyLieAlgebra ⧸ f4ShortRootSubspace)) :
    (f4ShortRootLieIdealBasis.baseChange A).repr
        (f4ShortRootQuotientToIdealBaseChange x) =
      (f4ShortRootQuotientBasis.baseChange A).repr x := by
  apply repr_comp_of_basis (f4ShortRootQuotientBasis.baseChange A)
    (f4ShortRootLieIdealBasis.baseChange A) f4ShortRootQuotientToIdealBaseChange _ x
  intro a
  simp only [Module.Basis.baseChange_apply, f4ShortRootQuotientToIdealBaseChange_tmul,
    f4ShortRootQuotientToIdealEquiv_basis]

/-- Every signed simple-root point acts on the carrier quotient by the prescribed reversed
root exponential with parameter exponent one or two. -/
theorem f4ShortRootQuotient_endOfPoint_root_pinning
    (g : f4ShortRootCarrierCoordinateHopfAlgebra →ₐ[𝔽₂] A)
    (k : Fin 4 ⊕ Fin 4) (u : Multiplicative A)
    (hg : GeneralLinear.pointsMulEquiv 26
        (WithConv.toConv (g.comp
          (CommHopfAlgCat.mkQuotient (GeneralLinear.coordinateHopfAlgebra 𝔽₂ 26)
            (CommHopfAlgCat.commonKernelHopfIdeal
              F4ShortRoot.PrimeField.generator)).hom.toAlgHom)) =
      F4ShortRoot.rootSubgroupPoints k A u)
    (a : Fin 26) :
    f4ShortRootQuotientToIdealBaseChange
        (Comodule.endOfPoint (f4ModularChevalleyLieAlgebra ⧸ f4ShortRootSubspace) g
          ((f4ShortRootQuotientBasis.baseChange A) a)) =
      f4ShortRootExponential (F4ShortRoot.isogenyReverse k)
        (Multiplicative.toAdd u ^ F4ShortRoot.isogenyExponent k)
        ((f4ShortRootLieIdealBasis.baseChange A) a) := by
  let c := TauCeti.cancelBaseChange ℤ 𝔽₂ A f4ChevalleyLieLattice
  let z := (1 : A) ⊗ₜ[ℤ] f4IntegralShortRootQuotientLift a
  have hq : f4ShortRootSubspace.mkQ.baseChange A (c.symm z) =
      (f4ShortRootQuotientBasis.baseChange A) a := by
    simp only [c, z, TauCeti.cancelBaseChange_symm_tmul,
      LinearMap.baseChange_tmul, f4IntegralShortRootQuotientLift_mkQ,
      Module.Basis.baseChange_apply]
  have h := f4ShortRootQuotient_endOfPoint_root g k u hg (c.symm z)
  have h' : Comodule.endOfPoint
      (f4ModularChevalleyLieAlgebra ⧸ f4ShortRootSubspace) g
        ((f4ShortRootQuotientBasis.baseChange A) a) =
      f4ShortRootSubspace.mkQ.baseChange A
        (c.symm (f4RootExponential k (Multiplicative.toAdd u) z)) :=
    (congrArg (Comodule.endOfPoint _ g) hq.symm).trans
      (h.trans (congrArg (fun w => f4ShortRootSubspace.mkQ.baseChange A
        (c.symm (f4RootExponential k (Multiplicative.toAdd u) w)))
          (c.apply_symm_apply z)))
  have hp := f4ShortRootQuotient_rootExponential_pinning k (Multiplicative.toAdd u) a
  have h'' := h'.trans
    (f4ShortRootBaseChangeQuotient_apply
      (f4RootExponential k (Multiplicative.toAdd u) z)).symm
  exact (congrArg f4ShortRootQuotientToIdealBaseChange h'').trans
    (hp.trans (congrArg
      (f4ShortRootExponential (F4ShortRoot.isogenyReverse k)
        (Multiplicative.toAdd u ^ F4ShortRoot.isogenyExponent k))
      (Module.Basis.baseChange_apply A f4ShortRootLieIdealBasis a).symm))

/-- Evaluating the coordinate morphism of the actual quotient comodule at a root point
produces the pinned target root matrix. -/
theorem pointsMulEquiv_f4ShortRootQuotientCoordinateBialgHom_root
    (g : f4ShortRootCarrierCoordinateHopfAlgebra →ₐ[𝔽₂] A)
    (k : Fin 4 ⊕ Fin 4) (u : Multiplicative A)
    (hg : GeneralLinear.pointsMulEquiv 26
        (WithConv.toConv (g.comp
          (CommHopfAlgCat.mkQuotient (GeneralLinear.coordinateHopfAlgebra 𝔽₂ 26)
            (CommHopfAlgCat.commonKernelHopfIdeal
              F4ShortRoot.PrimeField.generator)).hom.toAlgHom)) =
      F4ShortRoot.rootSubgroupPoints k A u) :
    GeneralLinear.pointsMulEquiv 26
        (WithConv.toConv (g.comp f4ShortRootQuotientCoordinateBialgHom.toAlgHom)) =
      F4ShortRoot.rootSubgroupPoints (F4ShortRoot.isogenyReverse k) A
        (Multiplicative.ofAdd (Multiplicative.toAdd u ^ F4ShortRoot.isogenyExponent k)) := by
  apply Units.ext
  rw [pointsMulEquiv_comp_f4ShortRootQuotientCoordinateBialgHom]
  calc
    _ = LinearMap.toMatrix (f4ShortRootLieIdealBasis.baseChange A)
        (f4ShortRootLieIdealBasis.baseChange A)
        (f4ShortRootExponential (F4ShortRoot.isogenyReverse k)
          (Multiplicative.toAdd u ^ F4ShortRoot.isogenyExponent k)) := by
      ext i j
      simp only [LinearMap.toMatrix_apply]
      exact (congrArg (fun v : Fin 26 →₀ A => v i)
        (f4ShortRootLieIdealBasis_repr_quotientToIdeal
          (Comodule.endOfPoint _ g ((f4ShortRootQuotientBasis.baseChange A) j)))).symm.trans
          (congrArg (fun x => (f4ShortRootLieIdealBasis.baseChange A).repr x i)
            (f4ShortRootQuotient_endOfPoint_root_pinning g k u hg j))
    _ = _ := f4ShortRootExponential_toMatrix_eq_rootSubgroupPoints _ _

end

end TauCeti.DynkinType
