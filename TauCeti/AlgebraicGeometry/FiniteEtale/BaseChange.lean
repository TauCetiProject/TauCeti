/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.FiniteEtale.Fiber
public import TauCeti.AlgebraicGeometry.Pullback.SpecMap

/-!
# Lifting finite étale schemes by lifting their coordinate algebras

Essential surjectivity of scalar extension on finite étale algebras implies essential
surjectivity of actual scheme pullback over the corresponding affine bases. This allows
algebraic lifting results to be used for geometric restriction functors.

The proof uses the affine anti-equivalence `TauCeti.FiniteEtaleScheme.spec` and the
existing comparison `TauCeti.AlgebraicGeometry.pullbackSpecIsoOfAlgEquiv`; it does not
introduce a second pullback functor or a choice of affine presentation in its statement.
-/

public section

open CategoryTheory AlgebraicGeometry Opposite
open scoped TensorProduct

universe u

namespace TauCeti.FiniteEtaleScheme

/-- If scalar extension of finite étale algebras is essentially surjective, then so is
pullback of finite étale schemes along the corresponding affine morphism. -/
theorem essSurj_pullback_of_essSurj_baseChange (R S : Type u) [CommRing R] [CommRing S]
    [Algebra R S] [(CommAlgCat.FiniteEtale.baseChange.{u} R S).EssSurj] :
    (pullback (Spec.map (CommRingCat.ofHom (algebraMap R S)))).EssSurj := by
  constructor
  intro X
  have : (spec (.of S)).IsEquivalence := by
    rw [← finiteEtaleCommAlgCatOpEquivFiniteEtaleScheme_functor]
    infer_instance
  obtain ⟨A, ⟨eA⟩⟩ := Functor.EssSurj.mem_essImage (spec (.of S)) X
  obtain ⟨B, ⟨eB⟩⟩ := Functor.EssSurj.mem_essImage
    (CommAlgCat.FiniteEtale.baseChange R S) A.unop
  refine ⟨(spec (.of R)).obj (op B), ⟨?_ ≪≫ (spec (.of S)).mapIso eB.symm.op ≪≫ eA⟩⟩
  apply ObjectProperty.isoMk
  rw [pullback_obj_obj, spec_obj_obj, spec_obj_obj]
  exact TauCeti.AlgebraicGeometry.pullbackSpecIsoOfAlgEquiv R B.obj S (S ⊗[R] B.obj)
    (AlgEquiv.refl : S ⊗[R] B.obj ≃ₐ[S] S ⊗[R] B.obj)

end TauCeti.FiniteEtaleScheme
