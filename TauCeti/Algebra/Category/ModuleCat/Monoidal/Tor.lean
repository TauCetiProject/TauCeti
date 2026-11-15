/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.CategoryTheory.Monoidal.Tor
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.RingHom.Flat
public import TauCeti.Algebra.Category.ModuleCat.Projective.QuotientResolution
public import TauCeti.CategoryTheory.Abelian.Projective.Dimension
public import TauCeti.CategoryTheory.Monoidal.Tor

import Mathlib.Algebra.Category.ModuleCat.Descent
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import Mathlib.Algebra.Homology.HomologySequence
import Mathlib.Algebra.Homology.HomologySequenceLemmas
import Mathlib.RingTheory.Flat.CategoryTheory
import Mathlib.RingTheory.Flat.Tensor
import TauCeti.Algebra.Category.ModuleCat.ChangeOfRings
import TauCeti.Algebra.Category.ModuleCat.Monoidal.ChangeOfRings
import TauCeti.LinearAlgebra.TensorProduct.Basic
public import TauCeti.Algebra.Homology.ModuleCat.Basic
public import TauCeti.LinearAlgebra.End.TensorProduct

/-!
# `Tor` of modules: flatness, short exact sequences, balancing and locally nilpotent endomorphisms

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

Mathlib's `Tor`, which derives the second variable, is computed by `X ⊗ P` for a projective
resolution `P` of `M`. The terms of `P` are flat, so a short exact sequence
`0 → X₁ → X₂ → X₃ → 0` gives a short exact sequence of complexes `Xᵢ ⊗ P`, and its long exact
homology sequence relates the groups `Torₙ(Xᵢ, M)`. We record the vanishing statements it gives:
`Torₙ(X₂, M)` vanishes with `Torₙ(X₁, M)` and `Torₙ(X₃, M)`
(`CategoryTheory.ShortComplex.ShortExact.isZero_Tor_X₂`), in particular `Torₙ(X × Y, M)` vanishes
with `Torₙ(X, M)` and `Torₙ(Y, M)` (`ModuleCat.isZero_Tor_prod`), `Torₙ₊₁(X₃, M)` vanishes with
`Torₙ₊₁(X₂, M)` and `Torₙ(X₁, M)` (`CategoryTheory.ShortComplex.ShortExact.isZero_Tor_succ_X₃`),
and `Tor₁(X₃, M)` vanishes with `Tor₁(X₂, M)` when `X₁ ⊗ M → X₂ ⊗ M` is injective
(`CategoryTheory.ShortComplex.ShortExact.isZero_Tor_one_X₃`). Flat modules have vanishing higher
`Tor` (`ModuleCat.isZero_Tor_succ_of_flat`), and `Torₙ₊₁(X ⧸ N, M)` vanishes when `N` is a directed
union of submodules `Nᵢ` with `Torₙ₊₁(X ⧸ Nᵢ, M) = 0`
(`ModuleCat.isZero_Tor_succ_quotient_iSup`), since an element of `N ⊗ P` already comes from a
finitely generated submodule of `N`.

When `X₂` is flat in `0 → X₁ → X₂ → X₃ → 0`, the connecting morphism of `Xᵢ ⊗ P` identifies
`Tor₁(X₃, M)` with the kernel of `X₁ ⊗ M → X₂ ⊗ M`
(`CategoryTheory.ShortComplex.ShortExact.torOneIsoKernelRight`), naturally in both the presentation
and `M`. When `X₁` and `X₂` are projective, combining this with `tor'OneIsoKernel` balances the two
derived tensor functors in degree `1` (`CategoryTheory.ShortComplex.ShortExact.tor'OneIsoTorOne`),
naturally in arbitrary morphisms of the presented modules and of `M`, and hence globally as a
natural isomorphism of bifunctors `ModuleCat.tor'OneIsoTorOne` when every `A`-module has projective
dimension at most one (for instance over a principal ideal domain).

`Tor` vanishing is invariant under flat base change: for a flat ring homomorphism `f : A →+* B`,
a `B`-module `M` and an `A`-module `N`, `Torₙ^A(M, N)` vanishes exactly when
`Torₙ^B(M, B ⊗[A] N)` does (`ModuleCat.isZero_Tor_restrictScalars_iff`). Extension of scalars
along `f` carries a projective resolution of `N` to one of `B ⊗[A] N`, and
`M ⊗[B] (B ⊗[A] -) ≅ M ⊗[A] -` (`ModuleCat.extendScalarsCompTensorLeftIso`).

## References

* C. A. Weibel, *An Introduction to Homological Algebra*, Cambridge Studies in Advanced
  Mathematics 38, Cambridge University Press (1994), Section 2.4, Theorem 2.7.2, and Section 3.2.
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

/-- A module is flat if its first `Tor'` with every module vanishes. -/
theorem flat_of_isZero_Tor'_one (M : ModuleCat.{u} A)
    (h : ∀ N : ModuleCat.{u} A, IsZero (((Tor' (ModuleCat.{u} A) 1).obj N).obj M)) :
    Module.Flat A M := by
  rw [Module.Flat.iff_rTensor_injective']
  intro I
  let P := projectiveResolution (ModuleCat.of A I)
  let p : P.complex.X 0 ⟶ ModuleCat.of A I :=
    P.π.f 0 ≫ (HomologicalComplex.singleObjXSelf _ 0 _).hom
  let Q := I.quotientProjectiveResolution
  let F := tensorRight M
  have hzero : IsZero (((F.mapHomologicalComplex _).obj Q.complex).homology 1) :=
    (h (ModuleCat.of A (A ⧸ I))).of_iso (Q.isoLeftDerivedObj F 1).symm
  have hex := (HomologicalComplex.exactAt_iff_isZero_homology _ _).2 hzero
  rw [HomologicalComplex.exactAt_iff' _ 2 1 0 (by simp) (by simp),
    ShortComplex.moduleCat_exact_iff] at hex
  -- Identify the local resolution `Q` through its public characteristic equation.
  rw [show Q.complex = _ from I.quotientProjectiveResolution_complex] at hex
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

/-! ### `Tor` along short exact sequences in the first variable -/

namespace ModuleCat

open CategoryTheory Limits MonoidalCategory
open scoped TensorProduct

universe u

variable {A : Type u} [CommRing A] {M : ModuleCat.{u} A}

/-- The complex `X ⊗ P` for a projective resolution `P` of `M`; its homology is `Tor(X, M)`. -/
private abbrev tensorResolution (P : ProjectiveResolution M) (X : ModuleCat.{u} A) :
    ChainComplex (ModuleCat.{u} A) ℕ :=
  (((tensoringLeft _).obj X).mapHomologicalComplex _).obj P.complex

private lemma isZero_Tor_iff (P : ProjectiveResolution M) (X : ModuleCat.{u} A) (n : ℕ) :
    IsZero (((Tor (ModuleCat.{u} A) n).obj X).obj M) ↔
      IsZero ((tensorResolution P X).homology n) :=
  ⟨fun h ↦ h.of_iso (P.isoLeftDerivedObj _ n).symm, fun h ↦ h.of_iso (P.isoLeftDerivedObj _ n)⟩

/-- Tensoring a short complex with a projective resolution, term by term. -/
private abbrev tensorResolutionShortComplex (P : ProjectiveResolution M)
    (S : ShortComplex (ModuleCat.{u} A)) : ShortComplex (ChainComplex (ModuleCat.{u} A) ℕ) :=
  ShortComplex.mk ((NatTrans.mapHomologicalComplex ((tensoringLeft _).map S.f) _).app P.complex)
    ((NatTrans.mapHomologicalComplex ((tensoringLeft _).map S.g) _).app P.complex) (by
      ext n : 2
      simp [← comp_whiskerRight])

/-- The terms of a projective resolution are flat, so tensoring them with a short exact sequence
gives a short exact sequence of complexes. -/
private lemma shortExact_tensorResolutionShortComplex (P : ProjectiveResolution M)
    {S : ShortComplex (ModuleCat.{u} A)} (hS : S.ShortExact) :
    (tensorResolutionShortComplex P S).ShortExact := by
  refine HomologicalComplex.shortExact_of_degreewise_shortExact _ fun n ↦ ?_
  have : Module.Flat A (P.complex.X n) := Module.Flat.of_projective
  refine .mk' (Module.Flat.rTensor_shortComplex_exact _ S hS.exact) ?_ ?_
  · rw [ModuleCat.mono_iff_injective]
    exact Module.Flat.rTensor_preserves_injective_linearMap _
      ((ModuleCat.mono_iff_injective _).1 hS.mono_f)
  · rw [ModuleCat.epi_iff_surjective]
    exact LinearMap.rTensor_surjective _ ((ModuleCat.epi_iff_surjective _).1 hS.epi_g)

/-- `Tor_{n+1}(X, M)` vanishes exactly when `X ⊗ P` is exact in degree `n + 1`. -/
private lemma isZero_Tor_succ_iff (P : ProjectiveResolution M) (X : ModuleCat.{u} A) (n : ℕ) :
    IsZero (((Tor (ModuleCat.{u} A) (n + 1)).obj X).obj M) ↔
      ∀ y : (X ⊗ P.complex.X (n + 1) : ModuleCat.{u} A),
        (P.complex.d (n + 1) n).hom.lTensor X y = 0 →
        ∃ z : (X ⊗ P.complex.X (n + 2) : ModuleCat.{u} A),
          (P.complex.d (n + 2) (n + 1)).hom.lTensor X z = y := by
  rw [isZero_Tor_iff P, ← HomologicalComplex.exactAt_iff_isZero_homology,
    HomologicalComplex.exactAt_iff' _ (n + 2) (n + 1) n (by simp) (by simp),
    ShortComplex.moduleCat_exact_iff]
  simp only [HomologicalComplex.shortComplexFunctor'_obj_X₁,
    HomologicalComplex.shortComplexFunctor'_obj_X₂, HomologicalComplex.shortComplexFunctor'_obj_f,
    HomologicalComplex.shortComplexFunctor'_obj_g, Functor.mapHomologicalComplex_obj_X,
    Functor.mapHomologicalComplex_obj_d, curriedTensor_obj_obj, curriedTensor_obj_map,
    hom_whiskerLeft]

/-- **Flat modules are `Tor`-acyclic.** If `X` is flat, then `Tor_{n+1}(X, M) = 0` for every
module `M`. -/
theorem isZero_Tor_succ_of_flat (X M : ModuleCat.{u} A) [Module.Flat A X] (n : ℕ) :
    IsZero (((Tor (ModuleCat.{u} A) (n + 1)).obj X).obj M) :=
  Functor.isZero_leftDerived_succ ((tensoringLeft _).obj X) M n

/-- **`Tor` of a quotient by a directed union.** If `N` is a directed family of submodules of `X`
and `Tor_{n+1}(X ⧸ N i, M)` vanishes for every `i`, then `Tor_{n+1}(X ⧸ ⨆ i, N i, M)` vanishes. -/
theorem isZero_Tor_succ_quotient_iSup {X : ModuleCat.{u} A} {ι : Type*} [Nonempty ι]
    {N : ι → Submodule A X} (hN : Directed (· ≤ ·) N) (n : ℕ)
    (h : ∀ i, IsZero (((Tor (ModuleCat.{u} A) (n + 1)).obj (of A (X ⧸ N i))).obj M)) :
    IsZero (((Tor (ModuleCat.{u} A) (n + 1)).obj (of A (X ⧸ ⨆ i, N i))).obj M) := by
  let P := CategoryTheory.projectiveResolution M
  set K := ⨆ i, N i
  simp only [isZero_Tor_succ_iff P] at h ⊢
  set d₁ := (P.complex.d (n + 1) n).hom
  set d₂ := (P.complex.d (n + 2) (n + 1)).hom
  intro y hy
  -- Lift `y` to `X ⊗ P`; its boundary comes from `K ⊗ P`, hence from `N₀ ⊗ P` for a finitely
  -- generated `N₀ ≤ K`, and `N₀` lies in a single `N i`.
  obtain ⟨y, rfl⟩ := LinearMap.rTensor_surjective _ K.mkQ_surjective y
  have hy' : K.mkQ.rTensor _ (d₁.lTensor X y) = 0 := by
    rwa [← LinearMap.lTensor_rTensor_comm]
  obtain ⟨t, ht⟩ := (rTensor_exact _ (LinearMap.exact_subtype_mkQ K)
    K.mkQ_surjective _).1 hy'
  obtain ⟨N₀, hN₀, hle, t, rfl⟩ := Submodule.exists_fg_le_eq_rTensor_inclusion t
  obtain ⟨_, ⟨i, rfl⟩, hi⟩ := (isCompactElement_iff_le_of_directed_sSup_le _).1
    ((Submodule.fg_iff_compact N₀).1 hN₀) (Set.range N) (Set.range_nonempty N)
    hN.directedOn_range (by rwa [sSup_range])
  -- In `(X ⧸ N i) ⊗ P` the image of `y` is a cycle, hence a boundary.
  obtain ⟨z, hz⟩ := h i ((N i).mkQ.rTensor _ y) (by
    rw [LinearMap.lTensor_rTensor_comm, ← ht]
    have h0 : (N i).mkQ ∘ₗ K.subtype ∘ₗ Submodule.inclusion hle = 0 := by
      ext x
      exact (Submodule.Quotient.mk_eq_zero _).2 (hi x.2)
    simp only [← LinearMap.rTensor_comp_apply, h0, LinearMap.rTensor_zero, LinearMap.zero_apply])
  refine ⟨(Submodule.factor (le_iSup N i)).rTensor _ z, ?_⟩
  rw [LinearMap.lTensor_rTensor_comm, hz, ← LinearMap.rTensor_comp_apply, Submodule.factor_comp_mk]

end ModuleCat

namespace CategoryTheory.ShortComplex.ShortExact

open Limits MonoidalCategory ModuleCat

universe u

variable {A : Type u} [CommRing A] {S : ShortComplex (ModuleCat.{u} A)} (hS : S.ShortExact)
  (M : ModuleCat.{u} A)

include hS

/-- **`Tor` is half exact in the first variable**: for a short exact sequence
`0 → X₁ → X₂ → X₃ → 0`, if `Tor_n(X₁, M)` and `Tor_n(X₃, M)` vanish then so does `Tor_n(X₂, M)`. -/
theorem isZero_Tor_X₂ {n : ℕ} (h₁ : IsZero (((Tor (ModuleCat.{u} A) n).obj S.X₁).obj M))
    (h₃ : IsZero (((Tor (ModuleCat.{u} A) n).obj S.X₃).obj M)) :
    IsZero (((Tor (ModuleCat.{u} A) n).obj S.X₂).obj M) := by
  let P := CategoryTheory.projectiveResolution M
  have hT := shortExact_tensorResolutionShortComplex P hS
  rw [isZero_Tor_iff P] at h₁ h₃ ⊢
  exact (hT.homology_exact₂ n).isZero_X₂ (h₁.eq_of_src _ _) (h₃.eq_of_tgt _ _)

/-- **Dimension shifting for `Tor` in the first variable**: for a short exact sequence
`0 → X₁ → X₂ → X₃ → 0`, if `Tor_{n+1}(X₂, M)` and `Tor_n(X₁, M)` vanish then so does
`Tor_{n+1}(X₃, M)`. -/
theorem isZero_Tor_succ_X₃ {n : ℕ}
    (h₂ : IsZero (((Tor (ModuleCat.{u} A) (n + 1)).obj S.X₂).obj M))
    (h₁ : IsZero (((Tor (ModuleCat.{u} A) n).obj S.X₁).obj M)) :
    IsZero (((Tor (ModuleCat.{u} A) (n + 1)).obj S.X₃).obj M) := by
  let P := CategoryTheory.projectiveResolution M
  have hT := shortExact_tensorResolutionShortComplex P hS
  rw [isZero_Tor_iff P] at h₁ h₂ ⊢
  exact (hT.homology_exact₃ (n + 1) n rfl).isZero_X₂ (h₂.eq_of_src _ _) (h₁.eq_of_tgt _ _)

/-- **`Tor₁` of a cokernel**: for a short exact sequence `0 → X₁ → X₂ → X₃ → 0`, if
`Tor₁(X₂, M)` vanishes and `X₁ ⊗ M → X₂ ⊗ M` is injective, then `Tor₁(X₃, M)` vanishes. -/
theorem isZero_Tor_one_X₃ (h₂ : IsZero (((Tor (ModuleCat.{u} A) 1).obj S.X₂).obj M))
    (h₁ : Function.Injective (S.f.hom.rTensor M)) :
    IsZero (((Tor (ModuleCat.{u} A) 1).obj S.X₃).obj M) := by
  let P := CategoryTheory.projectiveResolution M
  have hT := shortExact_tensorResolutionShortComplex P hS
  rw [isZero_Tor_iff P] at h₂ ⊢
  -- In degree zero, the homology of `X ⊗ P` is `X ⊗ M` through `fromLeftDerivedZero'`, so
  -- `H₀(S.f ⊗ P)` is the injective map `S.f ⊗ M`; hence the connecting map `δ` vanishes.
  let e (X : ModuleCat.{u} A) : (tensorResolution P X).homology 0 ⟶ X ⊗ M :=
    (tensorResolution P X).homologyι 0 ≫ P.fromLeftDerivedZero' ((tensoringLeft _).obj X)
  have key : HomologicalComplex.homologyMap (tensorResolutionShortComplex P S).f 0 ≫ e S.X₂ =
      e S.X₁ ≫ S.f ▷ M := by
    simp only [e, HomologicalComplex.homologyι_naturality_assoc, Category.assoc]
    congr 1
    rw [← cancel_epi (HomologicalComplex.pOpcycles _ 0)]
    simp only [HomologicalComplex.p_opcyclesMap_assoc,
      ProjectiveResolution.pOpcycles_comp_fromLeftDerivedZero',
      ProjectiveResolution.pOpcycles_comp_fromLeftDerivedZero'_assoc]
    -- `(tensoringLeft _).obj X` acts on morphisms by whiskering on the left with `X`.
    exact (whisker_exchange S.f (P.π.f 0)).symm
  have hf : Mono (S.f ▷ M) :=
    (ModuleCat.mono_iff_injective _).2 (by simpa [ModuleCat.hom_whiskerRight] using h₁)
  have : Mono (HomologicalComplex.homologyMap (tensorResolutionShortComplex P S).f 0) := by
    have : Mono (HomologicalComplex.homologyMap (tensorResolutionShortComplex P S).f 0 ≫
        e S.X₂) := by
      rw [key]
      infer_instance
    exact mono_of_mono _ (e S.X₂)
  have hδ : hT.δ 1 0 rfl = 0 := (hT.homology_exact₁ 1 0 rfl).mono_g_iff.1 this
  exact (hT.homology_exact₃ 1 0 rfl).isZero_X₂ (h₂.eq_of_src _ _) hδ

end CategoryTheory.ShortComplex.ShortExact

namespace ModuleCat

open CategoryTheory Limits

universe u

variable {A : Type u} [CommRing A]

/-- **`Tor` of a product**: if `Torₙ(X, M)` and `Torₙ(Y, M)` vanish then so does
`Torₙ(X × Y, M)`, by half exactness along `0 → X → X × Y → Y → 0`. -/
theorem isZero_Tor_prod {X Y : ModuleCat.{u} A} (M : ModuleCat.{u} A) {n : ℕ}
    (hX : IsZero (((Tor (ModuleCat.{u} A) n).obj X).obj M))
    (hY : IsZero (((Tor (ModuleCat.{u} A) n).obj Y).obj M)) :
    IsZero (((Tor (ModuleCat.{u} A) n).obj (of A (X × Y))).obj M) :=
  (shortComplex_shortExact
    (shortComplexOfCompEqZero (LinearMap.inl A X Y) (LinearMap.snd A X Y)
      (LinearMap.snd_comp_inl _ _ _))
    Function.Exact.inl_snd LinearMap.inl_injective LinearMap.snd_surjective).isZero_Tor_X₂ M hX hY

end ModuleCat

/-! ### Flat base change -/

namespace ModuleCat

open CategoryTheory Limits MonoidalCategory

universe u

variable {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B)

/-- **Flat base change for the vanishing of `Tor`.** For a flat ring homomorphism `f : A →+* B`, a
`B`-module `M` and an `A`-module `N`, `Torₙ^A(M, N)` vanishes exactly when `Torₙ^B(M, B ⊗[A] N)`
vanishes. -/
theorem isZero_Tor_restrictScalars_iff (hf : f.Flat) (M : ModuleCat.{u} B) (N : ModuleCat.{u} A)
    (n : ℕ) :
    IsZero (((Tor (ModuleCat.{u} A) n).obj ((restrictScalars f).obj M)).obj N) ↔
      IsZero (((Tor (ModuleCat.{u} B) n).obj M).obj ((extendScalars f).obj N)) := by
  -- Flatness makes extension of scalars exact, and as a left adjoint of the exact restriction of
  -- scalars it preserves projectives, so it carries projective resolutions to projective
  -- resolutions.
  have := preservesFiniteLimits_extendScalars_of_flat hf
  have : PreservesColimitsOfSize.{0, 0} (extendScalars.{u, u, u} f) :=
    (extendRestrictScalarsAdj.{u, u, u} f).leftAdjoint_preservesColimits
  have : PreservesFiniteColimits (extendScalars.{u, u, u} f) :=
    PreservesColimitsOfSize.preservesFiniteColimits _
  have : (extendScalars.{u, u, u} f).PreservesProjectiveObjects :=
    Functor.preservesProjectiveObjects_of_adjunction_of_preservesEpimorphisms
      (extendRestrictScalarsAdj.{u, u, u} f)
  let Q := projectiveResolution N
  let Q' := (extendScalars.{u, u, u} f).mapProjectiveResolution Q
  rw [isZero_Tor_iff Q, isZero_Tor_iff Q', ← HomologicalComplex.exactAt_iff_isZero_homology,
    ← HomologicalComplex.exactAt_iff_isZero_homology]
  -- Restricting scalars in `M ⊗[B] (B ⊗[A] Q)` gives `M ⊗[A] Q`, and restriction of scalars is
  -- exact and faithful, so it neither creates nor destroys exactness.
  let e : ((restrictScalars.{u} f).mapHomologicalComplex _).obj (tensorResolution Q' M) ≅
      tensorResolution Q ((restrictScalars f).obj M) :=
    HomologicalComplex.Hom.isoOfComponents
      (fun k ↦ (extendScalarsCompTensorLeftIso f M).app (Q.complex.X k))
      fun i j _ ↦ ((extendScalarsCompTensorLeftIso f M).hom.naturality (Q.complex.d i j)).symm
  have hR : (((restrictScalars.{u} f).mapHomologicalComplex _).obj
      (tensorResolution Q' M)).ExactAt n ↔ (tensorResolution Q' M).ExactAt n :=
    ((tensorResolution Q' M).sc n).exact_map_iff_of_faithful (restrictScalars.{u} f)
  rw [← hR]
  exact ⟨fun h ↦ h.of_iso e.symm, fun h ↦ h.of_iso e⟩

end ModuleCat

/-! ### Balancing `Tor'` and `Tor` on length-one presentations -/

namespace ModuleCat

open CategoryTheory Limits MonoidalCategory HomologicalComplex

universe u

variable {A : Type u} [CommRing A]

/-- Right exactness of `X ⊗ -` identifies `H₀(X ⊗ P)` with `X ⊗ M` for any projective resolution
`P` of `M`. -/
private noncomputable def tensorResolutionHomologyZeroIso {M : ModuleCat.{u} A}
    (P : ProjectiveResolution M) (X : ModuleCat.{u} A) :
    (tensorResolution P X).homology 0 ≅ X ⊗ M :=
  have : PreservesFiniteColimits ((tensoringLeft (ModuleCat.{u} A)).obj X) :=
    PreservesColimitsOfSize.preservesFiniteColimits (tensorLeft X)
  ChainComplex.isoHomologyι₀ (tensorResolution P X) ≪≫
    asIso (P.fromLeftDerivedZero' ((tensoringLeft (ModuleCat.{u} A)).obj X))

@[reassoc]
private lemma tensorResolutionHomologyZeroIso_hom_naturality_left {M : ModuleCat.{u} A}
    (P : ProjectiveResolution M) {X Y : ModuleCat.{u} A} (f : X ⟶ Y) :
    homologyMap (((NatTrans.mapHomologicalComplex ((tensoringLeft _).map f) _).app P.complex)) 0 ≫
        (tensorResolutionHomologyZeroIso P Y).hom =
      (tensorResolutionHomologyZeroIso P X).hom ≫ f ▷ M := by
  simp only [tensorResolutionHomologyZeroIso, Iso.trans_hom, isoHomologyι_hom,
    asIso_hom, homologyι_naturality_assoc, Category.assoc]
  congr 1
  rw [← cancel_epi (pOpcycles _ 0), p_opcyclesMap_assoc,
    ProjectiveResolution.pOpcycles_comp_fromLeftDerivedZero',
    ProjectiveResolution.pOpcycles_comp_fromLeftDerivedZero'_assoc]
  exact (whisker_exchange f (P.π.f 0)).symm

@[reassoc]
private lemma tensorResolutionHomologyZeroIso_hom_naturality_right {M M' : ModuleCat.{u} A}
    {g : M ⟶ M'} (P : ProjectiveResolution M) (P' : ProjectiveResolution M')
    (ψ : P.complex ⟶ P'.complex) (hψ : ψ ≫ P'.π = P.π ≫ (ChainComplex.single₀ _).map g)
    (X : ModuleCat.{u} A) :
    homologyMap (((tensoringLeft _).obj X).mapHomologicalComplex _ |>.map ψ) 0 ≫
        (tensorResolutionHomologyZeroIso P' X).hom =
      (tensorResolutionHomologyZeroIso P X).hom ≫ X ◁ g := by
  simp only [tensorResolutionHomologyZeroIso, Iso.trans_hom, isoHomologyι_hom,
    asIso_hom, homologyι_naturality_assoc, Category.assoc]
  congr 1
  exact ProjectiveResolution.fromLeftDerivedZero'_naturality g P P' ψ
    (by simpa using HomologicalComplex.congr_hom hψ 0)
    ((tensoringLeft (ModuleCat.{u} A)).obj X)

/-- Morphism of resolution-tensored short complexes induced by `φ : S ⟶ S'`. -/
@[simps]
private noncomputable def tensorResolutionShortComplexMapLeft {M : ModuleCat.{u} A}
    (P : ProjectiveResolution M) {S S' : ShortComplex (ModuleCat.{u} A)} (φ : S ⟶ S') :
    tensorResolutionShortComplex P S ⟶ tensorResolutionShortComplex P S' where
  τ₁ := (NatTrans.mapHomologicalComplex ((tensoringLeft _).map φ.τ₁) _).app P.complex
  τ₂ := (NatTrans.mapHomologicalComplex ((tensoringLeft _).map φ.τ₂) _).app P.complex
  τ₃ := (NatTrans.mapHomologicalComplex ((tensoringLeft _).map φ.τ₃) _).app P.complex
  comm₁₂ := HomologicalComplex.hom_ext _ _ fun n ↦ by
    simpa [← comp_whiskerRight] using congrArg (· ▷ P.complex.X n) φ.comm₁₂
  comm₂₃ := HomologicalComplex.hom_ext _ _ fun n ↦ by
    simpa [← comp_whiskerRight] using congrArg (· ▷ P.complex.X n) φ.comm₂₃

/-- Morphism of resolution-tensored short complexes induced by a lift `ψ : P ⟶ P'`. -/
@[simps]
private noncomputable def tensorResolutionShortComplexMapRight {M M' : ModuleCat.{u} A}
    {P : ProjectiveResolution M} {P' : ProjectiveResolution M'} (ψ : P.complex ⟶ P'.complex)
    (S : ShortComplex (ModuleCat.{u} A)) :
    tensorResolutionShortComplex P S ⟶ tensorResolutionShortComplex P' S where
  τ₁ := (((tensoringLeft _).obj S.X₁).mapHomologicalComplex _).map ψ
  τ₂ := (((tensoringLeft _).obj S.X₂).mapHomologicalComplex _).map ψ
  τ₃ := (((tensoringLeft _).obj S.X₃).mapHomologicalComplex _).map ψ
  comm₁₂ := HomologicalComplex.hom_ext _ _ fun n ↦ by simp
  comm₂₃ := HomologicalComplex.hom_ext _ _ fun n ↦ by simp

/-- Every morphism `S.X₃ ⟶ S'.X₃` from a short complex with projective middle term into a short
exact sequence lifts to a morphism of short complexes. -/
private lemma exists_hom_of_projective_X₂ {C : Type*} [Category* C] [Abelian C]
    {S S' : ShortComplex C} [Projective S.X₂] (hS' : S'.ShortExact) (f : S.X₃ ⟶ S'.X₃) :
    ∃ φ : S ⟶ S', φ.τ₃ = f := by
  have := hS'.epi_g
  let τ₂ : S.X₂ ⟶ S'.X₂ := Projective.factorThru (S.g ≫ f) S'.g
  have hτ₂ : τ₂ ≫ S'.g = S.g ≫ f := Projective.factorThru_comp _ _
  obtain ⟨τ₁, hτ₁⟩ := KernelFork.IsLimit.lift' hS'.fIsKernel (S.f ≫ τ₂)
    (by rw [Category.assoc, hτ₂, S.zero_assoc, zero_comp])
  exact ⟨{ τ₁ := τ₁, τ₂ := τ₂, τ₃ := f, comm₁₂ := hτ₁, comm₂₃ := hτ₂ }, rfl⟩

end ModuleCat

namespace CategoryTheory.ShortComplex.ShortExact

open Limits MonoidalCategory ModuleCat

universe u

variable {A : Type u} [CommRing A] {S S' : ShortComplex (ModuleCat.{u} A)}

section FlatPresentation

private lemma rel_one_zero : (ComplexShape.down ℕ).Rel 1 0 := rfl

private noncomputable def isoTensorResolutionHomology {M : ModuleCat.{u} A}
    (P : ProjectiveResolution M) (X : ModuleCat.{u} A) (n : ℕ) :
    (((tensoringLeft (ModuleCat.{u} A)).obj X).leftDerived n).obj M ≅
      (tensorResolution P X).homology n :=
  P.isoLeftDerivedObj ((tensoringLeft _).obj X) n

private lemma leftDerived_tensoringLeft_app_eq {M : ModuleCat.{u} A}
    (P : ProjectiveResolution M) {X Y : ModuleCat.{u} A} (f : X ⟶ Y) (n : ℕ) :
    (NatTrans.leftDerived ((tensoringLeft (ModuleCat.{u} A)).map f) n).app M =
      (isoTensorResolutionHomology P X n).hom ≫
        HomologicalComplex.homologyMap
          ((NatTrans.mapHomologicalComplex ((tensoringLeft _).map f) _).app P.complex) n ≫
          (isoTensorResolutionHomology P Y n).inv :=
  P.leftDerived_app_eq ((tensoringLeft _).map f) n

private lemma leftDerived_tensoringLeft_map_eq {M M' : ModuleCat.{u} A}
    (P : ProjectiveResolution M) (P' : ProjectiveResolution M') (X : ModuleCat.{u} A) (n : ℕ)
    (g : M ⟶ M') (ψ : P.complex ⟶ P'.complex)
    (hψ : ψ ≫ P'.π = P.π ≫ (ChainComplex.single₀ _).map g) :
    (((tensoringLeft (ModuleCat.{u} A)).obj X).leftDerived n).map g =
      (isoTensorResolutionHomology P X n).hom ≫
        HomologicalComplex.homologyMap ((((tensoringLeft _).obj X).mapHomologicalComplex _).map ψ)
          n ≫
          (isoTensorResolutionHomology P' X n).inv :=
  ((tensoringLeft _).obj X).leftDerived_map_eq n g ψ hψ

variable (hS : S.ShortExact)

/-- The connecting map `Tor₁(S.X₃, M) ⟶ S.X₁ ⊗ M` of `0 ⟶ S.X₁ ⊗ P ⟶ S.X₂ ⊗ P ⟶ S.X₃ ⊗ P ⟶ 0`
for a projective resolution `P` of `M`. -/
private noncomputable def torOneToWhiskerRight {M : ModuleCat.{u} A} (P : ProjectiveResolution M) :
    (((tensoringLeft (ModuleCat.{u} A)).obj S.X₃).leftDerived 1).obj M ⟶ S.X₁ ⊗ M :=
  (isoTensorResolutionHomology P S.X₃ 1).hom ≫
    (shortExact_tensorResolutionShortComplex P hS).δ 1 0 rel_one_zero ≫
      (tensorResolutionHomologyZeroIso P S.X₁).hom

private lemma torOneToWhiskerRight_def {M : ModuleCat.{u} A} (P : ProjectiveResolution M) :
    hS.torOneToWhiskerRight P =
      (isoTensorResolutionHomology P S.X₃ 1).hom ≫
        (shortExact_tensorResolutionShortComplex P hS).δ 1 0 rel_one_zero ≫
          (tensorResolutionHomologyZeroIso P S.X₁).hom :=
  rfl

private lemma torOneToWhiskerRight_comp {M : ModuleCat.{u} A} (P : ProjectiveResolution M) :
    hS.torOneToWhiskerRight P ≫ (S.f ▷ M) = 0 := by
  rw [torOneToWhiskerRight_def, Category.assoc, Category.assoc,
    ← tensorResolutionHomologyZeroIso_hom_naturality_left,
    (shortExact_tensorResolutionShortComplex P hS).δ_comp_assoc, zero_comp, comp_zero]

variable [Module.Flat A S.X₂]

private noncomputable def isLimitTorOneToWhiskerRight {M : ModuleCat.{u} A}
    (P : ProjectiveResolution M) :
    IsLimit (KernelFork.ofι (hS.torOneToWhiskerRight P) (hS.torOneToWhiskerRight_comp P)) := by
  have hT := shortExact_tensorResolutionShortComplex P hS
  have : Mono (hT.δ 1 0 rel_one_zero) :=
    hT.mono_δ 1 0 rel_one_zero ((isZero_Tor_iff P S.X₂ 1).1 (isZero_Tor_succ_of_flat S.X₂ M 0))
  let S₁ : ShortComplex (ModuleCat.{u} A) :=
    ShortComplex.mk (hT.δ 1 0 rel_one_zero)
      (HomologicalComplex.homologyMap (tensorResolutionShortComplex P S).f 0)
      (hT.δ_comp 1 0 rel_one_zero)
  let S₂ : ShortComplex (ModuleCat.{u} A) :=
    ShortComplex.mk (hS.torOneToWhiskerRight P) (S.f ▷ M) (hS.torOneToWhiskerRight_comp P)
  have e : S₁ ≅ S₂ := ShortComplex.isoMk
    (isoTensorResolutionHomology P S.X₃ 1).symm
    (tensorResolutionHomologyZeroIso P S.X₁) (tensorResolutionHomologyZeroIso P S.X₂)
    (by
      dsimp only [S₁, S₂]
      rw [Iso.symm_hom, torOneToWhiskerRight_def, Iso.inv_hom_id_assoc])
    (tensorResolutionHomologyZeroIso_hom_naturality_left P S.f).symm
  have : Mono (hS.torOneToWhiskerRight P) := by
    rw [torOneToWhiskerRight_def]
    infer_instance
  exact ((ShortComplex.exact_iff_of_iso e).1 (hT.homology_exact₁ 1 0 rel_one_zero)).fIsKernel

private noncomputable def leftDerivedTensoringLeftOneIsoKernel {M : ModuleCat.{u} A}
    (P : ProjectiveResolution M) :
    (((tensoringLeft (ModuleCat.{u} A)).obj S.X₃).leftDerived 1).obj M ≅ kernel (S.f ▷ M) :=
  (hS.isLimitTorOneToWhiskerRight P).conePointUniqueUpToIso (limit.isLimit _)

@[reassoc]
private lemma leftDerivedTensoringLeftOneIsoKernel_hom_comp_ι {M : ModuleCat.{u} A}
    (P : ProjectiveResolution M) :
    (hS.leftDerivedTensoringLeftOneIsoKernel P).hom ≫ kernel.ι (S.f ▷ M) =
      hS.torOneToWhiskerRight P :=
  IsLimit.conePointUniqueUpToIso_hom_comp (hS.isLimitTorOneToWhiskerRight P) (limit.isLimit _)
    WalkingParallelPair.zero

variable {hS} in
private lemma leftDerived_app_comp_leftDerivedTensoringLeftOneIsoKernel_hom
    (hS' : S'.ShortExact) [Module.Flat A S'.X₂] {M : ModuleCat.{u} A}
    (P : ProjectiveResolution M) (φ : S ⟶ S') :
    (NatTrans.leftDerived ((tensoringLeft (ModuleCat.{u} A)).map φ.τ₃) 1).app M ≫
        (hS'.leftDerivedTensoringLeftOneIsoKernel P).hom =
      (hS.leftDerivedTensoringLeftOneIsoKernel P).hom ≫
        kernel.map (S.f ▷ M) (S'.f ▷ M) (φ.τ₁ ▷ M) (φ.τ₂ ▷ M)
          (by simp only [← comp_whiskerRight, φ.comm₁₂]) := by
  rw [← cancel_mono (kernel.ι (S'.f ▷ M)), Category.assoc, Category.assoc, kernel.lift_ι,
    leftDerivedTensoringLeftOneIsoKernel_hom_comp_ι,
    leftDerivedTensoringLeftOneIsoKernel_hom_comp_ι_assoc,
    torOneToWhiskerRight_def, torOneToWhiskerRight_def,
    leftDerived_tensoringLeft_app_eq P φ.τ₃ 1, Category.assoc, Category.assoc,
    Iso.inv_hom_id_assoc, ← tensorResolutionShortComplexMapLeft_τ₃ P φ,
    ← HomologicalComplex.HomologySequence.δ_naturality_assoc
      (tensorResolutionShortComplexMapLeft P φ)
      (shortExact_tensorResolutionShortComplex P hS)
      (shortExact_tensorResolutionShortComplex P hS') 1 0 rel_one_zero,
    tensorResolutionShortComplexMapLeft_τ₁,
    Category.assoc, tensorResolutionHomologyZeroIso_hom_naturality_left, Category.assoc]

private lemma leftDerived_map_comp_leftDerivedTensoringLeftOneIsoKernel_hom
    {M M' : ModuleCat.{u} A} (P : ProjectiveResolution M) (P' : ProjectiveResolution M')
    (g : M ⟶ M') :
    (((tensoringLeft (ModuleCat.{u} A)).obj S.X₃).leftDerived 1).map g ≫
        (hS.leftDerivedTensoringLeftOneIsoKernel P').hom =
      (hS.leftDerivedTensoringLeftOneIsoKernel P).hom ≫
        kernel.map (S.f ▷ M) (S.f ▷ M') (S.X₁ ◁ g) (S.X₂ ◁ g) (whisker_exchange S.f g).symm := by
  let ψ : P.complex ⟶ P'.complex := ProjectiveResolution.lift g P P'
  have hψ : ψ ≫ P'.π = P.π ≫ (ChainComplex.single₀ _).map g :=
    ProjectiveResolution.lift_commutes g P P'
  rw [← cancel_mono (kernel.ι (S.f ▷ M')), Category.assoc, Category.assoc, kernel.lift_ι,
    leftDerivedTensoringLeftOneIsoKernel_hom_comp_ι,
    leftDerivedTensoringLeftOneIsoKernel_hom_comp_ι_assoc,
    torOneToWhiskerRight_def, torOneToWhiskerRight_def,
    leftDerived_tensoringLeft_map_eq P P' S.X₃ 1 g ψ hψ, Category.assoc, Category.assoc,
    Iso.inv_hom_id_assoc, ← tensorResolutionShortComplexMapRight_τ₃ ψ S,
    ← HomologicalComplex.HomologySequence.δ_naturality_assoc
      (tensorResolutionShortComplexMapRight ψ S)
      (shortExact_tensorResolutionShortComplex P hS)
      (shortExact_tensorResolutionShortComplex P' hS) 1 0 rel_one_zero,
    tensorResolutionShortComplexMapRight_τ₁,
    Category.assoc, tensorResolutionHomologyZeroIso_hom_naturality_right P P' ψ hψ, Category.assoc]

/-- **Dimension-shifting computation of `Tor₁` in the first variable.** For a short exact sequence
`0 ⟶ X₁ ⟶ X₂ ⟶ X₃ ⟶ 0` of `A`-modules with `X₂` flat, `Tor₁(X₃, M)` is the kernel of
`S.f ▷ M : X₁ ⊗ M ⟶ X₂ ⊗ M`. -/
noncomputable def torOneIsoKernelRight (M : ModuleCat.{u} A) :
    ((Tor (ModuleCat.{u} A) 1).obj S.X₃).obj M ≅ kernel (S.f ▷ M) :=
  hS.leftDerivedTensoringLeftOneIsoKernel (CategoryTheory.projectiveResolution M)

variable {hS} in
/-- `torOneIsoKernelRight` is natural in morphisms of presentations with flat middle term. -/
@[reassoc]
lemma Tor_map_app_comp_torOneIsoKernelRight_hom (hS' : S'.ShortExact)
    [Module.Flat A S'.X₂] (M : ModuleCat.{u} A) (φ : S ⟶ S') :
    ((Tor (ModuleCat.{u} A) 1).map φ.τ₃).app M ≫ (hS'.torOneIsoKernelRight M).hom =
      (hS.torOneIsoKernelRight M).hom ≫
        kernel.map (S.f ▷ M) (S'.f ▷ M) (φ.τ₁ ▷ M) (φ.τ₂ ▷ M)
          (by simp only [← comp_whiskerRight, φ.comm₁₂]) :=
  leftDerived_app_comp_leftDerivedTensoringLeftOneIsoKernel_hom (hS := hS) hS'
    (CategoryTheory.projectiveResolution M) φ

/-- `torOneIsoKernelRight` is natural in the second variable `M`. -/
@[reassoc]
lemma Tor_obj_map_comp_torOneIsoKernelRight_hom {M M' : ModuleCat.{u} A} (g : M ⟶ M') :
    ((Tor (ModuleCat.{u} A) 1).obj S.X₃).map g ≫ (hS.torOneIsoKernelRight M').hom =
      (hS.torOneIsoKernelRight M).hom ≫
        kernel.map (S.f ▷ M) (S.f ▷ M') (S.X₁ ◁ g) (S.X₂ ◁ g) (whisker_exchange S.f g).symm :=
  hS.leftDerived_map_comp_leftDerivedTensoringLeftOneIsoKernel_hom
    (CategoryTheory.projectiveResolution M) (CategoryTheory.projectiveResolution M') g

end FlatPresentation

section Balancing

variable (hS : S.ShortExact) [Projective S.X₁] [Projective S.X₂]

/-- **Balancing `Tor'₁` and `Tor₁` on a length-one projective presentation.** Both derived functors
compute the kernel of `S.f ▷ M : S.X₁ ⊗ M ⟶ S.X₂ ⊗ M`, identifying `Tor'₁(S.X₃, M)` with
`Tor₁(S.X₃, M)` naturally in both variables. -/
noncomputable def tor'OneIsoTorOne (M : ModuleCat.{u} A) :
    ((Tor' (ModuleCat.{u} A) 1).obj S.X₃).obj M ≅ ((Tor (ModuleCat.{u} A) 1).obj S.X₃).obj M :=
  have : Module.Flat A S.X₂ := Module.Flat.of_projective
  hS.tor'OneIsoKernel M ≪≫ (hS.torOneIsoKernelRight M).symm

/-- `tor'OneIsoTorOne` intertwines the two kernel identifications `tor'OneIsoKernel` and
`torOneIsoKernelRight`. -/
@[reassoc (attr := simp)]
lemma tor'OneIsoTorOne_hom_comp_torOneIsoKernelRight_hom (M : ModuleCat.{u} A) :
    have : Module.Flat A S.X₂ := Module.Flat.of_projective
    (hS.tor'OneIsoTorOne M).hom ≫ (hS.torOneIsoKernelRight M).hom =
      (hS.tor'OneIsoKernel M).hom := by
  simp [tor'OneIsoTorOne]

/-- `tor'OneIsoTorOne` is natural in the second variable `M`. -/
@[reassoc]
lemma Tor'_obj_map_comp_tor'OneIsoTorOne_hom {M M' : ModuleCat.{u} A} (g : M ⟶ M') :
    ((Tor' (ModuleCat.{u} A) 1).obj S.X₃).map g ≫ (hS.tor'OneIsoTorOne M').hom =
      (hS.tor'OneIsoTorOne M).hom ≫ ((Tor (ModuleCat.{u} A) 1).obj S.X₃).map g := by
  have : Module.Flat A S.X₂ := Module.Flat.of_projective
  rw [← cancel_mono (hS.torOneIsoKernelRight M').hom, Category.assoc, Category.assoc,
    tor'OneIsoTorOne_hom_comp_torOneIsoKernelRight_hom,
    Tor_obj_map_comp_torOneIsoKernelRight_hom,
    tor'OneIsoTorOne_hom_comp_torOneIsoKernelRight_hom_assoc,
    Tor'_obj_map_comp_tor'OneIsoKernel_hom]

variable {hS} in
/-- `tor'OneIsoTorOne` is natural in arbitrary morphisms `f : S.X₃ ⟶ S'.X₃` between modules with
length-one projective presentations, and in particular independent of the chosen presentation. -/
@[reassoc]
lemma Tor'_map_app_comp_tor'OneIsoTorOne_hom (hS' : S'.ShortExact)
    [Projective S'.X₁] [Projective S'.X₂] (M : ModuleCat.{u} A) (f : S.X₃ ⟶ S'.X₃) :
    ((Tor' (ModuleCat.{u} A) 1).map f).app M ≫ (hS'.tor'OneIsoTorOne M).hom =
      (hS.tor'OneIsoTorOne M).hom ≫ ((Tor (ModuleCat.{u} A) 1).map f).app M := by
  have : Module.Flat A S.X₂ := Module.Flat.of_projective
  have : Module.Flat A S'.X₂ := Module.Flat.of_projective
  obtain ⟨φ, rfl⟩ := exists_hom_of_projective_X₂ hS' f
  rw [← cancel_mono (hS'.torOneIsoKernelRight M).hom, Category.assoc, Category.assoc,
    tor'OneIsoTorOne_hom_comp_torOneIsoKernelRight_hom,
    Tor_map_app_comp_torOneIsoKernelRight_hom (hS := hS) hS' M φ,
    tor'OneIsoTorOne_hom_comp_torOneIsoKernelRight_hom_assoc,
    Tor'_map_app_comp_tor'OneIsoKernel_hom (hS := hS) hS' M φ]

end Balancing

end CategoryTheory.ShortComplex.ShortExact

namespace ModuleCat

open CategoryTheory Limits

universe u

variable {A : Type u} [CommRing A] [∀ X : ModuleCat.{u} A, HasProjectiveDimensionLE X 1]

private instance projective_kernelShortComplex_X₁ (X : ModuleCat.{u} A) :
    Projective (Projective.kernelShortComplex X).X₁ :=
  projective_of_mono_of_hasProjectiveDimensionLE_one (kernel.ι (Projective.π X))

variable (A) in
/-- **Balancing `Tor'₁` and `Tor₁` over a ring of global dimension at most one** (such as any
principal ideal domain): natural isomorphism of bifunctors `Tor'₁^A ≅ Tor₁^A`. -/
noncomputable def tor'OneIsoTorOne : Tor' (ModuleCat.{u} A) 1 ≅ Tor (ModuleCat.{u} A) 1 :=
  NatIso.ofComponents
    (fun X ↦ NatIso.ofComponents
      (fun M ↦ (Projective.kernelShortComplex_shortExact X).tor'OneIsoTorOne M)
      fun g ↦ (Projective.kernelShortComplex_shortExact X).Tor'_obj_map_comp_tor'OneIsoTorOne_hom g)
    fun f ↦ by
      ext M : 2
      exact ShortComplex.ShortExact.Tor'_map_app_comp_tor'OneIsoTorOne_hom
        (hS := Projective.kernelShortComplex_shortExact _)
        (Projective.kernelShortComplex_shortExact _) M f

/-- On any length-one projective presentation `hS : 0 ⟶ P₁ ⟶ P₀ ⟶ X ⟶ 0`, the global balancing
isomorphism `ModuleCat.tor'OneIsoTorOne` agrees with `hS.tor'OneIsoTorOne`. -/
lemma tor'OneIsoTorOne_hom_app_app_eq {S : ShortComplex (ModuleCat.{u} A)} (hS : S.ShortExact)
    [Projective S.X₁] [Projective S.X₂] (M : ModuleCat.{u} A) :
    ((tor'OneIsoTorOne A).hom.app S.X₃).app M = (hS.tor'OneIsoTorOne M).hom := by
  have h := ShortComplex.ShortExact.Tor'_map_app_comp_tor'OneIsoTorOne_hom
    (hS := Projective.kernelShortComplex_shortExact S.X₃) hS M (𝟙 S.X₃)
  rw [(Tor' (ModuleCat.{u} A) 1).map_id, NatTrans.id_app, Category.id_comp,
    (Tor (ModuleCat.{u} A) 1).map_id, NatTrans.id_app, Category.comp_id] at h
  exact h.symm

end ModuleCat
