/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import Mathlib.Algebra.Field.ZMod
import Mathlib.FieldTheory.RatFunc.AsPolynomial
import TauCeti.AlgebraicGeometry.FiniteEtale.Galois.FundamentalGroup
import TauCeti.CategoryTheory.Aut.Torsor

/-!
# Tests for étale paths over a finite prime field

Over `Spec 𝔽_p` with the geometric point `x : Spec 𝔽_p^alg ⟶ Spec 𝔽_p`, the étale paths from `x`
to itself are the automorphisms of the geometric fibre functor, that is, the elements of
`π₁(Spec 𝔽_p, x) ≅ Gal(𝔽_p^alg/𝔽_p)`, and the actions of the fundamental group by postcomposition
and by precomposition are both simply transitive.

Paths are isomorphisms of fibre functors, not of separably closed fields. For a second
geometric point `y : Spec Ω ⟶ Spec 𝔽_p`, with `Ω` an algebraic closure of `𝔽_p(t)`, there is an
étale path from `x` to `y`, since `Spec 𝔽_p` is connected, although `𝔽_p^alg` and `Ω` are not
isomorphic fields: `Ω` contains the transcendental element `t`.
-/

open CategoryTheory AlgebraicGeometry

namespace TauCeti.FiniteEtaleScheme

variable (p : ℕ) [Fact p.Prime]

/-- *test_path_eq_galois*: the étale paths from the geometric point `Spec 𝔽_p^alg ⟶ Spec 𝔽_p` to
itself are the elements of `Gal(𝔽_p^alg/𝔽_p)`, through the identification of the étale fundamental
group with the absolute Galois group. -/
example : Function.Bijective fun σ : Gal(AlgebraicClosure (ZMod p)/ZMod p) ↦
    ((galContinuousMulEquivAutFiber (ZMod p) (AlgebraicClosure (ZMod p)) σ).asIso :
      EtalePath (Spec.map (CommRingCat.ofHom (algebraMap (ZMod p) (AlgebraicClosure (ZMod p)))))
        (Spec.map (CommRingCat.ofHom (algebraMap (ZMod p) (AlgebraicClosure (ZMod p)))))) :=
  Aut.isoEquiv.bijective.comp
    (galContinuousMulEquivAutFiber (ZMod p) (AlgebraicClosure (ZMod p))).bijective

/-- *test_postcomposition_simply_transitive*: `Gal(𝔽_p^alg/𝔽_p)` acts simply transitively on the
étale paths from `Spec 𝔽_p^alg` to itself by postcomposition. -/
example (e₁ e₂ : EtalePath
      (Spec.map (CommRingCat.ofHom (algebraMap (ZMod p) (AlgebraicClosure (ZMod p)))))
      (Spec.map (CommRingCat.ofHom (algebraMap (ZMod p) (AlgebraicClosure (ZMod p)))))) :
    ∃! σ : Gal(AlgebraicClosure (ZMod p)/ZMod p),
      galContinuousMulEquivAutFiber (ZMod p) (AlgebraicClosure (ZMod p)) σ • e₁ = e₂ :=
  (galContinuousMulEquivAutFiber (ZMod p) (AlgebraicClosure (ZMod p))).toEquiv.existsUnique_congr
    (fun _ ↦ Iff.rfl) |>.mpr (Iso.existsUnique_smul_eq e₁ e₂)

/-- *test_precomposition_simply_transitive*: `Gal(𝔽_p^alg/𝔽_p)` acts simply transitively on the
étale paths from `Spec 𝔽_p^alg` to itself by precomposition. -/
example (e₁ e₂ : EtalePath
      (Spec.map (CommRingCat.ofHom (algebraMap (ZMod p) (AlgebraicClosure (ZMod p)))))
      (Spec.map (CommRingCat.ofHom (algebraMap (ZMod p) (AlgebraicClosure (ZMod p)))))) :
    ∃! σ : Gal(AlgebraicClosure (ZMod p)/ZMod p),
      MulOpposite.op (galContinuousMulEquivAutFiber (ZMod p) (AlgebraicClosure (ZMod p)) σ) • e₁ =
        e₂ :=
  (galContinuousMulEquivAutFiber (ZMod p) (AlgebraicClosure (ZMod p))).toEquiv.existsUnique_congr
    (fun _ ↦ Iff.rfl) |>.mpr (Iso.existsUnique_op_smul_eq e₁ e₂)

/-- *test_path_between_different_fields*: every geometric point of `Spec 𝔽_p`, for instance at
an algebraic closure of `𝔽_p(t)`, is joined to `Spec 𝔽_p^alg` by an étale path. -/
example (y : Spec (.of (AlgebraicClosure (RatFunc (ZMod p)))) ⟶ Spec (.of (ZMod p))) :
    Nonempty (EtalePath
      (Spec.map (CommRingCat.ofHom (algebraMap (ZMod p) (AlgebraicClosure (ZMod p))))) y) :=
  nonempty_fiber_iso _ _

/-- *test_no_field_isomorphism*: `𝔽_p^alg` and an algebraic closure of `𝔽_p(t)` are not isomorphic
fields, so étale paths are not isomorphisms of the fields of the geometric points. -/
example : IsEmpty (AlgebraicClosure (ZMod p) ≃+* AlgebraicClosure (RatFunc (ZMod p))) := by
  refine ⟨fun e ↦ ?_⟩
  let f : AlgebraicClosure (ZMod p) ≃ₐ[ZMod p] AlgebraicClosure (RatFunc (ZMod p)) :=
    AlgEquiv.ofRingEquiv (f := e) fun a ↦
      DFunLike.congr_fun (RingHom.ext_zmod (e.toRingHom.comp (algebraMap _ _)) (algebraMap _ _)) a
  have ht : Transcendental (ZMod p)
      (algebraMap (RatFunc (ZMod p)) (AlgebraicClosure (RatFunc (ZMod p))) RatFunc.X) :=
    (transcendental_algebraMap_iff (FaithfulSMul.algebraMap_injective _ _)).mpr
      RatFunc.transcendental_X
  have := f.isAlgebraic
  exact ht (Algebra.IsAlgebraic.isAlgebraic _)

end TauCeti.FiniteEtaleScheme
