/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import TauCeti.AlgebraicGeometry.Sites.Nisnevich.DistinguishedSquare.EmptyOpen

/-!
# Examples: étale maps that are not distinguished with empty open part

An elementary distinguished square `Q` over a reduced scheme with empty open part `U` has `p` an
isomorphism (`ElementaryDistinguishedSquare.isIso_p_of_isEmpty`). Hence:

* for a field extension `K → L` of degree two, for instance `ℝ → ℂ`, no such `Q` over `Spec K` has
  `p` isomorphic over `Spec K` to `Spec L ⟶ Spec K`;
* over `X = Spec ℝ`, no such `Q` has `p` isomorphic over `X` to the morphism
  `Spec ℝ ⨿ Spec ℂ ⟶ Spec ℝ`, which has two points over the single point of `X`: the structure
  rejects it, although it has exactly one point with residue field `ℝ` over that point.
-/

public section

open CategoryTheory Limits AlgebraicGeometry

namespace TauCeti.AlgebraicGeometry.DistinguishedSquareEmptyOpenExample

open TauCeti.AlgebraicGeometry.Scheme

universe u

/-- For a field extension `K → L` of degree other than one, `Spec L ⟶ Spec K` is not an
isomorphism. -/
theorem not_isIso_spec_algebraMap (K L : Type u) [Field K] [Field L] [Algebra K L]
    (h : Module.finrank K L ≠ 1) :
    ¬ IsIso (Spec.map (CommRingCat.ofHom (algebraMap K L))) := by
  intro hi
  have : IsIso (Scheme.Spec.map (CommRingCat.ofHom (algebraMap K L)).op) := hi
  have : IsIso (CommRingCat.ofHom (algebraMap K L)).op := isIso_of_reflects_iso _ Scheme.Spec
  have : IsIso (CommRingCat.ofHom (algebraMap K L)) := isIso_of_op _
  have hb : Function.Bijective (algebraMap K L) :=
    ConcreteCategory.bijective_of_isIso (CommRingCat.ofHom (algebraMap K L))
  exact h ((AlgEquiv.ofBijective (Algebra.ofId K L) hb).toLinearEquiv.finrank_eq.symm.trans
    (Module.finrank_self K))

/-- **A degree-two extension is not distinguished with empty `U`.** For a field extension `K → L`
of degree two, no elementary distinguished square over `Spec K` with empty open part has `p`
isomorphic over `Spec K` to `Spec L ⟶ Spec K`. -/
theorem isEmpty_iso_spec_of_finrank_eq_two (K L : Type u) [Field K] [Field L] [Algebra K L]
    (h : Module.finrank K L = 2) (Q : ElementaryDistinguishedSquare (Spec (.of K)))
    [IsEmpty Q.U] :
    IsEmpty (Over.mk Q.p ≅ Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K L)))) :=
  Q.not_nonempty_iso_of_isEmpty _ (not_isIso_spec_algebraMap K L (by omega))

/-- The case `ℝ → ℂ`. -/
example (Q : ElementaryDistinguishedSquare (Spec (.of ℝ))) [IsEmpty Q.U] :
    IsEmpty (Over.mk Q.p ≅ Over.mk (Spec.map (CommRingCat.ofHom (algebraMap ℝ ℂ)))) :=
  isEmpty_iso_spec_of_finrank_eq_two ℝ ℂ Complex.finrank_real_complex Q

/-- The morphism `Spec ℝ ⨿ Spec ℂ ⟶ Spec ℝ`: the identity on `Spec ℝ` and `Spec ℂ ⟶ Spec ℝ`. -/
noncomputable abbrev realComplexToReal :
    Spec (.of ℝ) ⨿ Spec (.of ℂ) ⟶ Spec (.of ℝ) :=
  coprod.desc (𝟙 _) (Spec.map (CommRingCat.ofHom (algebraMap ℝ ℂ)))

/-- `Spec ℝ ⨿ Spec ℂ ⟶ Spec ℝ` is not an isomorphism: it identifies the points of the two
components. -/
theorem not_isIso_realComplexToReal : ¬ IsIso realComplexToReal := by
  intro _
  obtain ⟨a⟩ : Nonempty (Spec (.of ℝ)) := inferInstanceAs (Nonempty (PrimeSpectrum ℝ))
  obtain ⟨b⟩ : Nonempty (Spec (.of ℂ)) := inferInstanceAs (Nonempty (PrimeSpectrum ℂ))
  have hs : Subsingleton (Spec (.of ℝ)) := inferInstanceAs (Subsingleton (PrimeSpectrum ℝ))
  refine inl_ne_inr _ _ a b (realComplexToReal.isOpenEmbedding.injective (Subsingleton.elim _ _))

/-- **`Spec ℝ ⨿ Spec ℂ` is rejected.** No elementary distinguished square over `Spec ℝ` with empty
open part has `p` isomorphic over `Spec ℝ` to `Spec ℝ ⨿ Spec ℂ ⟶ Spec ℝ`. -/
theorem isEmpty_iso_realComplexToReal (Q : ElementaryDistinguishedSquare (Spec (.of ℝ)))
    [IsEmpty Q.U] : IsEmpty (Over.mk Q.p ≅ Over.mk realComplexToReal) :=
  Q.not_nonempty_iso_of_isEmpty _ not_isIso_realComplexToReal

end TauCeti.AlgebraicGeometry.DistinguishedSquareEmptyOpenExample
