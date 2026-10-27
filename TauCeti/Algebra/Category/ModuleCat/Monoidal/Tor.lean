/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.CategoryTheory.Monoidal.Tor
public import TauCeti.Algebra.Homology.ModuleCat.Basic
public import TauCeti.LinearAlgebra.End.TensorProduct

/-!
# Locally nilpotent endomorphisms and `Tor'` of modules

Let `A` be a commutative ring and `φ i` a family of endomorphisms of an `A`-module `Y` that is
locally nilpotent: every element of `Y` is killed by all sufficiently long composites of the maps
`φ i`, which is to say `⨆ d, Module.End.wordKer (fun i ↦ (φ i).hom) d = ⊤`. Then for every
`A`-module `N` and every `n`, the induced family of endomorphisms of Mathlib's
`Tor'ₙ^A(N, Y)`, the derived functor of the tensor product in its first variable, is again
locally nilpotent (`CategoryTheory.iSup_wordKer_Tor'_map_eq_top`).

Indeed `Tor'ₙ^A(N, Y)` is the homology of `P ⊗ Y` for a projective resolution `P` of `N`, with
the maps `φ i` acting through the second factor. Local nilpotence passes to tensor products
(`Module.End.iSup_wordKer_lTensor_eq_top`) and from a complex to its homology
(`HomologicalComplex.iSup_wordKer_homologyMap_eq_top`).

A typical family is that of operators lowering a grading of `Y` by `ℕ`, such as the
divided-difference operators on a polynomial ring. This is how the divided-difference argument
for the invariants of a reflection group reaches `Tor'` without a grading on `Tor'` itself.

## References

* C. A. Weibel, *An Introduction to Homological Algebra*, Cambridge Studies in Advanced
  Mathematics 38, Cambridge University Press (1994), Section 2.4, for left derived functors
  computed from a projective resolution.
-/

public section

namespace CategoryTheory

open MonoidalCategory

universe u

variable {A : Type u} [CommRing A]

/-- **`Tor'` preserves local nilpotence in its underived variable.** If every element of an
`A`-module `Y` is killed by all sufficiently long composites of the endomorphisms `φ i`, then every
element of `Tor'ₙ^A(N, Y)` is killed by all sufficiently long composites of the induced
endomorphisms. -/
theorem iSup_wordKer_Tor'_map_eq_top (N : ModuleCat.{u} A) {Y : ModuleCat.{u} A} {ι : Type*}
    (φ : ι → (Y ⟶ Y)) (h : ⨆ d, Module.End.wordKer (fun i ↦ (φ i).hom) d = ⊤) (n : ℕ) :
    ⨆ d, Module.End.wordKer (fun i ↦ (((Tor' (ModuleCat.{u} A) n).obj N).map (φ i)).hom) d =
      ⊤ := by
  let P := projectiveResolution N
  let F := (tensoringRight (ModuleCat.{u} A)).obj Y
  -- `Tor'ₙ(N, Y)` is the homology of `P ⊗ Y`, on which `φ i` acts by the chain map `P ◁ φ i`.
  let ψ (i : ι) := (NatTrans.mapHomologicalComplex ((tensoringRight _).map (φ i)) _).app P.complex
  have hψ (i : ι) : ((ψ i).f n).hom = (φ i).hom.lTensor (P.complex.X n) := by
    simp [ψ, ModuleCat.hom_whiskerLeft]
  have hP := HomologicalComplex.iSup_wordKer_homologyMap_eq_top ((F.mapHomologicalComplex _).obj
    P.complex) n ψ (by simpa only [hψ] using Module.End.iSup_wordKer_lTensor_eq_top _ h)
  refine Module.End.iSup_wordKer_eq_top_of_surjective (fun i ↦ ?_)
    ((ModuleCat.epi_iff_surjective (P.isoLeftDerivedObj F n).inv).1 inferInstance) hP
  -- The action of `φ i` on `Tor'ₙ(N, Y) = Lₙ(- ⊗ Y)(N)` is computed by the resolution `P`.
  have key : HomologicalComplex.homologyMap (ψ i) n ≫ (P.isoLeftDerivedObj F n).inv =
      (P.isoLeftDerivedObj F n).inv ≫
        (NatTrans.leftDerived ((tensoringRight _).map (φ i)) n).app N := by
    rw [P.leftDerived_app_eq _ n, Iso.inv_hom_id_assoc, HomologicalComplex.homologyFunctor_map]
    -- The two sides agree after unfolding the local definitions `ψ i` and `F`.
    rfl
  rw [Tor'_obj_map]
  -- `Tor'ₙ(N, Y)` is by definition (`Tor'_obj_obj`) the object `Lₙ(- ⊗ Y)(N)` of `key`, and
  -- composition in `ModuleCat` is composition of linear maps (`ModuleCat.hom_comp`).
  exact congrArg ModuleCat.Hom.hom key

end CategoryTheory
