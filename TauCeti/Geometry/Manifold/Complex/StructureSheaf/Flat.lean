/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Complex.StructureSheaf.Hyperplane
public import Mathlib.RingTheory.RingHom.Flat
import TauCeti.Geometry.Manifold.Complex.StructureSheaf.LocalRing
import TauCeti.Geometry.Manifold.Complex.StructureSheaf.Noetherian
import TauCeti.RingTheory.Flat.LocalCriterion

/-!
# Flatness of holomorphic germs over a factor

For a finite-dimensional complex vector space `E`, pulling holomorphic germs back along the
projection `E × ℂ → E` makes the holomorphic stalk `𝒪_{E × ℂ, (a, w)}` a flat algebra over
`𝒪_{E, a}` (`TauCeti.holomorphicStructureSheaf.flat_stalkPrecomp_fst`). In coordinates this is the
flatness of `ℂ{b, v}` over `ℂ{b}`, which is not a finite extension.

The proof uses the local flatness criterion along a regular element of the algebra
(`Module.Flat.of_flat_quotSMulTop_of_isSMulRegular`). The centered last coordinate `w - w₀` is a
nonzero element of the maximal ideal of the Noetherian domain `𝒪_{E × ℂ, (a, w₀)}`, so it is
regular. The quotient by it is the stalk `𝒪_{E, a}` itself (`hyperplaneQuotientEquiv`), and the
identification is linear over `𝒪_{E, a}` because restricting to the hyperplane undoes the
pullback along the projection. A free module of rank one is flat.

## References

* H. Matsumura, *Commutative Ring Theory*, Theorem 22.5, for the local flatness criterion along a
  regular element.
* R. C. Gunning and H. Rossi, *Analytic Functions of Several Complex Variables*, Chapter II, for
  the local rings of holomorphic germs.
-/

public section

open scoped ContDiff Manifold

namespace TauCeti.holomorphicStructureSheaf

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]

/-- **Holomorphic germs are flat over a factor.** Pullback along the projection `E × ℂ → E` makes
the holomorphic stalk at `(a, w)` a flat algebra over the holomorphic stalk at `a`. -/
theorem flat_stalkPrecomp_fst (a : E) (w : ℂ) :
    (stalkPrecomp 𝓘(ℂ, E × ℂ) (E × ℂ) Prod.fst contDiff_fst.contMDiff (a, w)).Flat := by
  algebraize [stalkPrecomp 𝓘(ℂ, E × ℂ) (E × ℂ) Prod.fst contDiff_fst.contMDiff (a, w)]
  set x := hyperplaneCoordinateGerm a w
  -- The quotient by the normal coordinate is the base stalk, linearly over the base stalk.
  let e : ((holomorphicStructureSheaf 𝓘(ℂ, E × ℂ) (E × ℂ)).presheaf.stalk (a, w) ⧸
      Ideal.span {x}) ≃ₐ[(holomorphicStructureSheaf 𝓘(ℂ, E) E).presheaf.stalk a]
      (holomorphicStructureSheaf 𝓘(ℂ, E) E).presheaf.stalk a :=
    AlgEquiv.ofRingEquiv (f := hyperplaneQuotientEquiv a w) fun c ↦ by
      rw [← Ideal.Quotient.mk_algebraMap, hyperplaneQuotientEquiv_mk, Algebra.algebraMap_self_apply]
      exact restrictHyperplane_stalkPrecomp_fst a w c
  have : Module.Flat ((holomorphicStructureSheaf 𝓘(ℂ, E) E).presheaf.stalk a)
      (QuotSMulTop x ((holomorphicStructureSheaf 𝓘(ℂ, E × ℂ) (E × ℂ)).presheaf.stalk (a, w))) :=
    .of_linearEquiv (((Submodule.quotEquivOfEq _ _ (by
      rw [← Submodule.ideal_span_singleton_smul, smul_eq_mul, Ideal.mul_top])).restrictScalars
        _).trans e.toLinearEquiv)
  refine Module.Flat.of_flat_quotSMulTop_of_isSMulRegular (x := x) ?_
    (.of_ne_zero (hyperplaneCoordinateGerm_ne_zero a w))
  rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top, maximalIdeal_stalk, RingHom.mem_ker]
  exact OpenPartialHomeomorph.eval_holomorphicLinearCoordinateGerm _ _ _ _ _

end TauCeti.holomorphicStructureSheaf
