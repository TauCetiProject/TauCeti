/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.CategoryTheory.Monoidal.Tor
public import Mathlib.RingTheory.Flat.Basic

import Mathlib.Algebra.Homology.Augment
import Mathlib.RingTheory.Flat.Tensor
public import TauCeti.Algebra.Homology.ModuleCat.Basic
public import TauCeti.LinearAlgebra.End.TensorProduct

/-!
# Flatness and locally nilpotent endomorphisms on `Tor'`

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

The vanishing of `Tor'₁^A(N, M)` for all `N` implies that `M` is flat
(`ModuleCat.flat_of_isZero_Tor'_one`). It suffices to apply this vanishing to `N = A ⧸ I`:
a projective resolution of `I`, augmented by its inclusion into `A`, computes this `Tor'₁`
and detects injectivity of `I ⊗ M → A ⊗ M`.

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

namespace ModuleCat

open CategoryTheory Limits MonoidalCategory
open scoped TensorProduct

universe u

variable {A : Type u} [CommRing A]

private noncomputable def flatnessTestResolution (I : Ideal A) :
    ProjectiveResolution (ModuleCat.of A (A ⧸ I)) := by
  -- Resolve the ideal first, then prepend the ambient ring.
  let P := projectiveResolution (ModuleCat.of A I)
  let p : P.complex.X 0 ⟶ ModuleCat.of A I :=
    P.π.f 0 ≫ (HomologicalComplex.singleObjXSelf _ 0 _).hom
  have hp : P.complex.d 1 0 ≫ p = 0 := by
    simp only [p, ← Category.assoc, P.complex_d_comp_π_f_zero, zero_comp]
  let f := p ≫ ModuleCat.ofHom I.subtype
  have hf : P.complex.d 1 0 ≫ f = 0 := by
    dsimp only [f]
    rw [← Category.assoc, hp, zero_comp]
  let K := P.complex.augment f hf
  let q : K.X 0 ⟶ ModuleCat.of A (A ⧸ I) := ModuleCat.ofHom I.mkQ
  have hq : K.d 1 0 ≫ q = 0 := by
    apply ModuleCat.hom_ext
    ext x
    exact (Submodule.Quotient.mk_eq_zero I).2 (p x).property
  refine { complex := K
           projective := ?_
           π := (ChainComplex.toSingle₀Equiv K _).symm ⟨q, hq⟩
           quasiIso := ?_ }
  · intro n
    cases n with
    | zero => exact inferInstanceAs (Projective (ModuleCat.of A A))
    | succ n => exact P.projective n
  · constructor
    intro n
    cases n with
    | zero =>
      -- The cokernel of the ideal inclusion is the required quotient.
      rw [ChainComplex.quasiIsoAt₀_iff, ShortComplex.quasiIso_iff_of_zeros']
      · dsimp
        simp only [ChainComplex.toSingle₀Equiv_symm_apply_f_zero]
        refine ⟨?_, (ModuleCat.epi_iff_surjective _).2 I.mkQ_surjective⟩
        rw [ShortComplex.moduleCat_exact_iff]
        intro x hx
        obtain ⟨y, hy⟩ := (ModuleCat.epi_iff_surjective p).1 inferInstance
          ⟨x, (Submodule.Quotient.mk_eq_zero I).1 hx⟩
        exact ⟨y, congrArg Subtype.val hy⟩
      all_goals rfl
    | succ n =>
      -- Exactness above degree one is inherited from the resolution of the ideal.
      rw [quasiIsoAt_iff_exactAt' _ _ (ChainComplex.exactAt_succ_single_obj _ _)]
      rw [HomologicalComplex.exactAt_iff' K (n + 2) (n + 1) n (by simp) (by simp)]
      cases n with
      | zero =>
        rw [ShortComplex.moduleCat_exact_iff]
        intro x hx
        have hx' : P.π.f 0 x = 0 := by
          apply (ModuleCat.mono_iff_injective
            (HomologicalComplex.singleObjXSelf _ 0 _).hom).1 inferInstance
          exact Subtype.val_injective hx
        exact (ShortComplex.moduleCat_exact_iff _).1 P.exact₀ x hx'
      | succ n => exact P.exact_succ n

/-- A module is flat if its first `Tor'` with every module vanishes. -/
theorem flat_of_isZero_Tor'_one (M : ModuleCat.{u} A)
    (h : ∀ N : ModuleCat.{u} A, IsZero (((Tor' (ModuleCat.{u} A) 1).obj N).obj M)) :
    Module.Flat A M := by
  rw [Module.Flat.iff_rTensor_injective']
  intro I
  let P := projectiveResolution (ModuleCat.of A I)
  let p : P.complex.X 0 ⟶ ModuleCat.of A I :=
    P.π.f 0 ≫ (HomologicalComplex.singleObjXSelf _ 0 _).hom
  let Q := flatnessTestResolution I
  let F := tensorRight M
  have hzero : IsZero (((F.mapHomologicalComplex _).obj Q.complex).homology 1) :=
    (h (ModuleCat.of A (A ⧸ I))).of_iso (Q.isoLeftDerivedObj F 1).symm
  have hex := (HomologicalComplex.exactAt_iff_isZero_homology _ _).2 hzero
  rw [HomologicalComplex.exactAt_iff' _ 2 1 0 (by simp) (by simp),
    ShortComplex.moduleCat_exact_iff] at hex
  -- The augmented complex starts with the chosen resolution of `I` followed by `A`.
  -- Tensoring these two differentials is `LinearMap.rTensor`.
  change ∀ y : (P.complex.X 0) ⊗[A] M,
    ((I.subtype.comp p.hom).rTensor M) y = 0 →
    ∃ z : (P.complex.X 1) ⊗[A] M,
      ((P.complex.d 1 0).hom.rTensor M) z = y at hex
  have hp : Function.Surjective (p.hom.rTensor M) :=
    LinearMap.rTensor_surjective M ((ModuleCat.epi_iff_surjective p).1 inferInstance)
  have hdp' : P.complex.d 1 0 ≫ p = 0 := by
    simp only [p, ← Category.assoc, P.complex_d_comp_π_f_zero, zero_comp]
  have hdp : p.hom.comp (P.complex.d 1 0).hom = 0 :=
    congrArg ModuleCat.Hom.hom hdp'
  apply LinearMap.ker_eq_bot.1
  apply (Submodule.eq_bot_iff _).2
  intro x hx
  obtain ⟨y, rfl⟩ := hp x
  obtain ⟨z, hz⟩ := hex y (by
    rw [LinearMap.rTensor_comp_apply]
    exact hx)
  rw [← hz, ← LinearMap.rTensor_comp_apply, hdp]
  simp

end ModuleCat
