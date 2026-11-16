/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.LiftingProperties.ParametrizedAdjunction
public import TauCeti.AlgebraicTopology.SimplicialSet.Pointed.TrivialFibration
public import TauCeti.AlgebraicTopology.Spectra.LevelFactorization
public import TauCeti.AlgebraicTopology.Spectra.Tensor
public import TauCeti.CategoryTheory.Limits.Shapes.Pullback.PullbackObjObj

/-!
# Pushout-products and pullback-hom corners of symmetric spectra

Combining the two-variable parametrized adjunctions for symmetric spectra
(`TauCeti.AlgebraicTopology.Spectra.Tensor` and
`Mathlib.CategoryTheory.LiftingProperties.ParametrizedAdjunction`) with the level projective weak
factorization systems on `SymmetricSpectrum`
(`TauCeti.AlgebraicTopology.Spectra.LevelFactorization`) and the based pullback-hom corner theorems
on `PointedSSet` (`TauCeti.AlgebraicTopology.SimplicialSet.Pointed.TrivialFibration`) yields the
three families of corner lifting properties for symmetric spectra (both in pointed form and in
unpointed simplicial form):

1. **Cotensor corners.** For a based map `k : K ⟶ L`, a map of symmetric spectra `p : E ⟶ F`, and a
   single level `n : ℕ` (hence also across all levels), every pullback-hom corner
   `E^L ⟶ E^K ×[F^K] F^L` is a Kan fibration in level `n` when `k` is a monomorphism and level `n`
   of `p` is a Kan fibration, and lifts against all simplicial monomorphisms in level `n` when
   either `k` is anodyne and level `n` of `p` is a Kan fibration, or `k` is a monomorphism and
   level `n` of `p` lifts against all simplicial monomorphisms.
2. **Pushout-products.** For a map of symmetric spectra `i : A ⟶ B` and a based map `k : K ⟶ L`,
   every pushout-product corner `(A ∧ L) ⨿_(A ∧ K) (B ∧ K) ⟶ B ∧ L` is a projective cofibration
   when `i` is a projective cofibration and `k` is a monomorphism, and lifts against all level
   fibrations when either `i` is a projective cofibration and `k` is anodyne, or `i` lifts against
   all level fibrations and `k` is a monomorphism.
3. **Mapping-space corners.** For maps of symmetric spectra `i : A ⟶ B` and `p : E ⟶ F`, every
   pullback-hom corner `Map(B, E) ⟶ Map(A, E) ×[Map(A, F)] Map(B, F)` is a Kan fibration on
   underlying simplicial sets when `i` is a projective cofibration and `p` is a level fibration,
   and lifts against all simplicial monomorphisms when either `i` lifts against all level
   fibrations and `p` is a level fibration, or `i` is a projective cofibration and `p` is a level
   trivial fibration.

Specializing to an initial source or a terminal target gives the single-variable preservation
properties of `cotensor`, `levelSmash`, `levelSmashRight`, and `mappingSpace`, including Kan
fibrancy of `(E^K)_n` whenever `E_n` is a Kan complex and Kan fibrancy of `Map(X, E)` when `X` is
projective cofibrant and every level of `E` is a Kan complex. These statements hold for the level
projective weak factorization systems without assuming the full Kan–Quillen model structure on
simplicial sets.

## Main statements

* `SymmetricSpectrum.fibration_evaluation_cotensor_pullbackObjObjπ`,
  `SymmetricSpectrum.rlp_monomorphisms_evaluation_cotensor_pullbackObjObjπ`,
  `SymmetricSpectrum.rlp_monomorphisms_evaluation_cotensor_pullbackObjObjπ_of_rlp_monomorphisms`,
  `SymmetricSpectrum.levelFibrations_cotensor_pullbackObjObjπ`,
  `SymmetricSpectrum.levelTrivialFibrations_cotensor_pullbackObjObjπ`,
  `SymmetricSpectrum.levelTrivialFibrations_cotensor_pullbackObjObjπ_of_levelTrivialFibrations`,
  and their unpointed `simplicialCotensor` counterparts: single-level and levelwise lifting for
  cotensor pullback-hom corners.
* `SymmetricSpectrum.projectiveCofibrations_levelSmash_pushoutObjObjι`,
  `SymmetricSpectrum.llp_levelFibrations_levelSmash_pushoutObjObjι_of_anodyneExtensions`,
  `SymmetricSpectrum.llp_levelFibrations_levelSmash_pushoutObjObjι`, and their unpointed
  `simplicialTensor` counterparts: lifting for levelwise-smash pushout-products.
* `SymmetricSpectrum.fibration_mappingSpace_pullbackObjObjπ`,
  `SymmetricSpectrum.rlp_monomorphisms_mappingSpace_pullbackObjObjπ`,
  `SymmetricSpectrum.rlp_monomorphisms_mappingSpace_pullbackObjObjπ_of_levelTrivialFibrations`,
  and their unpointed `simplicialMappingSpace` counterparts: lifting for spectral mapping-space
  pullback-hom corners.

## References

* M. Hovey, B. Shipley and J. Smith, *Symmetric spectra*, J. Amer. Math. Soc. 13 (2000),
  Sections 3.1 and 5.1.
* P. G. Goerss and J. F. Jardine, *Simplicial homotopy theory*, Progress in Mathematics 174,
  Birkhäuser, 1999, Chapter II, Section 3.
-/

public section

open CategoryTheory MonoidalCategory MonoidalClosed Limits MorphismProperty HomotopicalAlgebra
  Opposite
open SSet.modelCategoryQuillen
open scoped Simplicial

namespace TauCeti.SymmetricSpectrum

open PointedSSet

/-! ### Cotensor pullback-hom corners -/

section CotensorCorners

variable {K L : PointedSSet.{0}} {U V : SSet.{0}} {E F : SymmetricSpectrum}

/-- Transport a morphism property `W` on `SSet.{0}` from the pointed internal-hom corner at level
`n` along `cotensorEvaluationNatIso n` to level `n` of a cotensor pullback-hom corner. -/
private lemma mem_evaluation_cotensor_pullbackObjObjπ (W : MorphismProperty SSet.{0})
    [W.RespectsIso] {k : K ⟶ L} {p : E ⟶ F} (n : ℕ)
    (P : cotensorBifunctor.PullbackObjObj k p)
    (hQ :
      W ((P.map (evaluation n)).ofNatIso (cotensorEvaluationNatIso n)).ofWhiskeringLeft.π.right) :
    W ((evaluation n).map P.π).right := by
  let e := ((cotensorEvaluationNatIso n).app (op L)).app E
  have heq : ((evaluation n).map P.π).right =
      forgetBasepoint.map e.hom ≫
        ((P.map (evaluation n)).ofNatIso (cotensorEvaluationNatIso n)).ofWhiskeringLeft.π.right :=
    congrArg Under.Hom.right
      (Functor.PullbackObjObj.hom_comp_ofNatIso_π (P.map (evaluation n))
        (cotensorEvaluationNatIso n)).symm
  have : IsIso (forgetBasepoint.map e.hom) := forgetBasepoint.map_isIso e.hom
  rw [heq]
  exact (W.cancel_left_of_respectsIso _ _).2 hQ

/-- At level `n`, the cotensor pullback-hom corner `E^L ⟶ E^K ×[F^K] F^L` of a based monomorphism
and a map whose level `n` is a Kan fibration is a Kan fibration. -/
theorem fibration_evaluation_cotensor_pullbackObjObjπ (k : K ⟶ L) (p : E ⟶ F) (n : ℕ)
    [Mono k.right] [Fibration ((evaluation n).map p).right]
    (P : cotensorBifunctor.PullbackObjObj k p) :
    Fibration ((evaluation n).map P.π).right := by
  rw [HomotopicalAlgebra.fibration_iff]
  exact mem_evaluation_cotensor_pullbackObjObjπ (fibrations SSet.{0}) n P
    (PointedSSet.fibration_pullbackObjObjπ k ((evaluation n).map p) _).mem

/-- At level `n`, the cotensor pullback-hom corner `E^L ⟶ E^K ×[F^K] F^L` of an anodyne based map
and a map whose level `n` is a Kan fibration lifts against all simplicial monomorphisms. -/
theorem rlp_monomorphisms_evaluation_cotensor_pullbackObjObjπ (k : K ⟶ L) (p : E ⟶ F) (n : ℕ)
    (hk : SSet.anodyneExtensions k.right) [Fibration ((evaluation n).map p).right]
    (P : cotensorBifunctor.PullbackObjObj k p) :
    (monomorphisms SSet.{0}).rlp ((evaluation n).map P.π).right :=
  mem_evaluation_cotensor_pullbackObjObjπ (monomorphisms SSet.{0}).rlp n P
    (PointedSSet.rlp_monomorphisms_pullbackObjObjπ k ((evaluation n).map p) hk _)

/-- At level `n`, the cotensor pullback-hom corner `E^L ⟶ E^K ×[F^K] F^L` of a based monomorphism
and a map whose level `n` lifts against all simplicial monomorphisms also lifts against all
simplicial monomorphisms. -/
theorem rlp_monomorphisms_evaluation_cotensor_pullbackObjObjπ_of_rlp_monomorphisms
    (k : K ⟶ L) (p : E ⟶ F) (n : ℕ) [Mono k.right]
    (hp : (monomorphisms SSet.{0}).rlp ((evaluation n).map p).right)
    (P : cotensorBifunctor.PullbackObjObj k p) :
    (monomorphisms SSet.{0}).rlp ((evaluation n).map P.π).right :=
  mem_evaluation_cotensor_pullbackObjObjπ (monomorphisms SSet.{0}).rlp n P
    (PointedSSet.rlp_monomorphisms_pullbackObjObjπ_of_rlp k ((evaluation n).map p) hp _)

/-- The cotensor pullback-hom corner `E^L ⟶ E^K ×[F^K] F^L` of a based monomorphism and a level
fibration is a level fibration. -/
theorem levelFibrations_cotensor_pullbackObjObjπ (k : K ⟶ L) (p : E ⟶ F)
    [Mono k.right] (hp : levelFibrations p) (P : cotensorBifunctor.PullbackObjObj k p) :
    levelFibrations P.π :=
  (levelFibrations_iff P.π).2 fun n ↦
    have := (levelFibrations_iff p).1 hp n
    fibration_evaluation_cotensor_pullbackObjObjπ k p n P

/-- The cotensor pullback-hom corner `E^L ⟶ E^K ×[F^K] F^L` of an anodyne based map and a level
fibration is a level trivial fibration. -/
theorem levelTrivialFibrations_cotensor_pullbackObjObjπ (k : K ⟶ L) (p : E ⟶ F)
    (hk : SSet.anodyneExtensions k.right) (hp : levelFibrations p)
    (P : cotensorBifunctor.PullbackObjObj k p) :
    levelTrivialFibrations P.π :=
  (levelTrivialFibrations_iff P.π).2 fun n ↦
    have := (levelFibrations_iff p).1 hp n
    rlp_monomorphisms_evaluation_cotensor_pullbackObjObjπ k p n hk P

/-- The cotensor pullback-hom corner `E^L ⟶ E^K ×[F^K] F^L` of a based monomorphism and a level
trivial fibration is a level trivial fibration. -/
theorem levelTrivialFibrations_cotensor_pullbackObjObjπ_of_levelTrivialFibrations
    (k : K ⟶ L) (p : E ⟶ F) [Mono k.right] (hp : levelTrivialFibrations p)
    (P : cotensorBifunctor.PullbackObjObj k p) :
    levelTrivialFibrations P.π :=
  (levelTrivialFibrations_iff P.π).2 fun n ↦
    rlp_monomorphisms_evaluation_cotensor_pullbackObjObjπ_of_rlp_monomorphisms k p n
      ((levelTrivialFibrations_iff p).1 hp n) P

/-- At level `n`, the unpointed simplicial cotensor pullback-hom corner
`E^(V₊) ⟶ E^(U₊) ×[F^(U₊)] F^(V₊)` of a simplicial monomorphism and a map whose level `n` is a Kan
fibration is a Kan fibration. -/
theorem fibration_evaluation_simplicialCotensor_pullbackObjObjπ (j : U ⟶ V) (p : E ⟶ F) (n : ℕ)
    [Mono j] [Fibration ((evaluation n).map p).right]
    (P : simplicialCotensor.PullbackObjObj j p) :
    Fibration ((evaluation n).map P.π).right :=
  fibration_evaluation_cotensor_pullbackObjObjπ (addBasepoint.map j) p n P.ofOpComp

/-- At level `n`, the unpointed simplicial cotensor pullback-hom corner
`E^(V₊) ⟶ E^(U₊) ×[F^(U₊)] F^(V₊)` of an anodyne extension and a map whose level `n` is a Kan
fibration lifts against all simplicial monomorphisms. -/
theorem rlp_monomorphisms_evaluation_simplicialCotensor_pullbackObjObjπ (j : U ⟶ V) (p : E ⟶ F)
    (n : ℕ) (hj : SSet.anodyneExtensions j) [Fibration ((evaluation n).map p).right]
    (P : simplicialCotensor.PullbackObjObj j p) :
    (monomorphisms SSet.{0}).rlp ((evaluation n).map P.π).right :=
  rlp_monomorphisms_evaluation_cotensor_pullbackObjObjπ (addBasepoint.map j) p n
    (addBasepoint_map_right_mem_of_isStableUnderCobaseChange SSet.anodyneExtensions hj) P.ofOpComp

/-- At level `n`, the unpointed simplicial cotensor pullback-hom corner
`E^(V₊) ⟶ E^(U₊) ×[F^(U₊)] F^(V₊)` of a simplicial monomorphism and a map whose level `n` lifts
against all simplicial monomorphisms also lifts against all simplicial monomorphisms. -/
theorem rlp_monomorphisms_evaluation_simplicialCotensor_pullbackObjObjπ_of_rlp_monomorphisms
    (j : U ⟶ V) (p : E ⟶ F) (n : ℕ) [Mono j]
    (hp : (monomorphisms SSet.{0}).rlp ((evaluation n).map p).right)
    (P : simplicialCotensor.PullbackObjObj j p) :
    (monomorphisms SSet.{0}).rlp ((evaluation n).map P.π).right :=
  rlp_monomorphisms_evaluation_cotensor_pullbackObjObjπ_of_rlp_monomorphisms (addBasepoint.map j) p
    n hp P.ofOpComp

/-- The unpointed simplicial cotensor pullback-hom corner `E^(V₊) ⟶ E^(U₊) ×[F^(U₊)] F^(V₊)` of a
simplicial monomorphism and a level fibration is a level fibration. -/
theorem levelFibrations_simplicialCotensor_pullbackObjObjπ (j : U ⟶ V) (p : E ⟶ F)
    [Mono j] (hp : levelFibrations p) (P : simplicialCotensor.PullbackObjObj j p) :
    levelFibrations P.π :=
  levelFibrations_cotensor_pullbackObjObjπ (addBasepoint.map j) p hp P.ofOpComp

/-- The unpointed simplicial cotensor pullback-hom corner `E^(V₊) ⟶ E^(U₊) ×[F^(U₊)] F^(V₊)` of an
anodyne extension and a level fibration is a level trivial fibration. -/
theorem levelTrivialFibrations_simplicialCotensor_pullbackObjObjπ (j : U ⟶ V) (p : E ⟶ F)
    (hj : SSet.anodyneExtensions j) (hp : levelFibrations p)
    (P : simplicialCotensor.PullbackObjObj j p) :
    levelTrivialFibrations P.π :=
  levelTrivialFibrations_cotensor_pullbackObjObjπ (addBasepoint.map j) p
    (addBasepoint_map_right_mem_of_isStableUnderCobaseChange SSet.anodyneExtensions hj) hp
    P.ofOpComp

/-- The unpointed simplicial cotensor pullback-hom corner `E^(V₊) ⟶ E^(U₊) ×[F^(U₊)] F^(V₊)` of a
simplicial monomorphism and a level trivial fibration is a level trivial fibration. -/
theorem levelTrivialFibrations_simplicialCotensor_pullbackObjObjπ_of_levelTrivialFibrations
    (j : U ⟶ V) (p : E ⟶ F) [Mono j] (hp : levelTrivialFibrations p)
    (P : simplicialCotensor.PullbackObjObj j p) :
    levelTrivialFibrations P.π :=
  levelTrivialFibrations_cotensor_pullbackObjObjπ_of_levelTrivialFibrations (addBasepoint.map j) p
    hp P.ofOpComp

/-- Point-set cotensors preserve Kan fibrations in each individual level `n`, with no hypothesis on
the pointed simplicial set `K`. -/
instance fibration_evaluation_cotensor_map (K : PointedSSet.{0}) (p : E ⟶ F) (n : ℕ)
    [Fibration ((evaluation n).map p).right] :
    Fibration ((evaluation n).map ((cotensor K).map p)).right := by
  let i : Under.mk (𝟙 (Δ[0] : SSet.{0})) ⟶ K := Under.homMk K.hom
  have : Mono i.right := SSet.stdSimplex.isTerminalObj₀.mono_from K.hom
  exact fibration_evaluation_cotensor_pullbackObjObjπ i p n
    (Functor.PullbackObjObj.ofIsInitial cotensorBifunctor i p Under.mkIdInitial)

/-- Point-set cotensors preserve maps lifting against all simplicial monomorphisms in each
individual level `n`, with no hypothesis on the pointed simplicial set `K`. -/
theorem rlp_monomorphisms_evaluation_cotensor_map (K : PointedSSet.{0}) {p : E ⟶ F} (n : ℕ)
    (hp : (monomorphisms SSet.{0}).rlp ((evaluation n).map p).right) :
    (monomorphisms SSet.{0}).rlp ((evaluation n).map ((cotensor K).map p)).right := by
  let i : Under.mk (𝟙 (Δ[0] : SSet.{0})) ⟶ K := Under.homMk K.hom
  have : Mono i.right := SSet.stdSimplex.isTerminalObj₀.mono_from K.hom
  exact rlp_monomorphisms_evaluation_cotensor_pullbackObjObjπ_of_rlp_monomorphisms i p n hp
    (Functor.PullbackObjObj.ofIsInitial cotensorBifunctor i p Under.mkIdInitial)

/-- Point-set cotensors preserve level fibrations in the spectrum variable, with no hypothesis on
the pointed simplicial set `K`. -/
theorem levelFibrations_cotensor_map (K : PointedSSet.{0}) {p : E ⟶ F} (hp : levelFibrations p) :
    levelFibrations ((cotensor K).map p) :=
  (levelFibrations_iff _).2 fun n ↦
    have := (levelFibrations_iff p).1 hp n
    inferInstance

/-- Point-set cotensors preserve level trivial fibrations in the spectrum variable, with no
hypothesis on the pointed simplicial set `K`. -/
theorem levelTrivialFibrations_cotensor_map (K : PointedSSet.{0}) {p : E ⟶ F}
    (hp : levelTrivialFibrations p) :
    levelTrivialFibrations ((cotensor K).map p) :=
  (levelTrivialFibrations_iff _).2 fun n ↦
    rlp_monomorphisms_evaluation_cotensor_map K n ((levelTrivialFibrations_iff p).1 hp n)

/-- If level `n` of `E` is a Kan complex, then level `n` of the cotensor `E^K` is a Kan complex,
with no hypothesis on the pointed simplicial set `K` or on other levels of `E`. -/
instance kanComplex_cotensor (K : PointedSSet.{0}) (E : SymmetricSpectrum) (n : ℕ)
    [SSet.KanComplex ((evaluation n).obj E).right] :
    SSet.KanComplex ((evaluation n).obj ((cotensor K).obj E)).right :=
  have : IsFibrant (forgetBasepoint.obj ((CategoryTheory.ihom K).obj ((evaluation n).obj E))) :=
    PointedSSet.kanComplex_ihom K ((evaluation n).obj E)
  isFibrant_of_fibration (forgetBasepoint.map (cotensorLevelIso K E n).hom)

/-- At level `n`, precomposition `E^L ⟶ E^K` along a based monomorphism is a Kan fibration whenever
level `n` of `E` is a Kan complex. -/
instance fibration_evaluation_pre_free_zero_map (k : K ⟶ L) [Mono k.right] (E : SymmetricSpectrum)
    (n : ℕ) [SSet.KanComplex ((evaluation n).obj E).right] :
    Fibration ((evaluation n).map ((MonoidalClosed.pre ((free 0).map k)).app E)).right :=
  have : Fibration ((evaluation n).map (terminal.from E)).right :=
    (isFibrant_iff_of_isTerminal _
      (terminalIsTerminal.isTerminalObj (evaluation n ⋙ forgetBasepoint)
        (⊤_ SymmetricSpectrum))).1 inferInstance
  fibration_evaluation_cotensor_pullbackObjObjπ k (terminal.from E) n
    (Functor.PullbackObjObj.ofIsTerminal cotensorBifunctor k (terminal.from E) terminalIsTerminal)

/-- At level `n`, precomposition `E^L ⟶ E^K` along an anodyne based map lifts against all simplicial
monomorphisms whenever level `n` of `E` is a Kan complex. -/
theorem rlp_monomorphisms_evaluation_pre_free_zero_map (k : K ⟶ L)
    (hk : SSet.anodyneExtensions k.right) (E : SymmetricSpectrum) (n : ℕ)
    [SSet.KanComplex ((evaluation n).obj E).right] :
    (monomorphisms SSet.{0}).rlp
      ((evaluation n).map ((MonoidalClosed.pre ((free 0).map k)).app E)).right :=
  have : Fibration ((evaluation n).map (terminal.from E)).right :=
    (isFibrant_iff_of_isTerminal _
      (terminalIsTerminal.isTerminalObj (evaluation n ⋙ forgetBasepoint)
        (⊤_ SymmetricSpectrum))).1 inferInstance
  rlp_monomorphisms_evaluation_cotensor_pullbackObjObjπ k (terminal.from E) n hk
    (Functor.PullbackObjObj.ofIsTerminal cotensorBifunctor k (terminal.from E) terminalIsTerminal)

/-- Precomposition `E^L ⟶ E^K` along a based monomorphism is a level fibration whenever every
level of `E` is a Kan complex. -/
theorem levelFibrations_pre_free_zero_map (k : K ⟶ L) [Mono k.right] (E : SymmetricSpectrum)
    (hE : ∀ n, SSet.KanComplex ((evaluation n).obj E).right) :
    levelFibrations ((MonoidalClosed.pre ((free 0).map k)).app E) :=
  (levelFibrations_iff _).2 fun n ↦
    have := hE n
    inferInstance

/-- Precomposition `E^L ⟶ E^K` along an anodyne based map is a level trivial fibration whenever
every level of `E` is a Kan complex. -/
theorem levelTrivialFibrations_pre_free_zero_map (k : K ⟶ L) (hk : SSet.anodyneExtensions k.right)
    (E : SymmetricSpectrum) (hE : ∀ n, SSet.KanComplex ((evaluation n).obj E).right) :
    levelTrivialFibrations ((MonoidalClosed.pre ((free 0).map k)).app E) :=
  (levelTrivialFibrations_iff _).2 fun n ↦
    have := hE n
    rlp_monomorphisms_evaluation_pre_free_zero_map k hk E n

end CotensorCorners

/-! ### Pushout-products for levelwise smash and simplicial tensors -/

section PushoutProducts

variable {A B : SymmetricSpectrum} {K L : PointedSSet.{0}} {U V : SSet.{0}}

/-- The pushout-product `(A ∧ L) ⨿_(A ∧ K) (B ∧ K) ⟶ B ∧ L` of a projective cofibration and a
based monomorphism is a projective cofibration. -/
theorem projectiveCofibrations_levelSmash_pushoutObjObjι {i : A ⟶ B} {k : K ⟶ L}
    (hi : projectiveCofibrations i) [Mono k.right] (Q : curriedLevelSmash.PushoutObjObj i k) :
    projectiveCofibrations Q.ι := by
  rw [projectiveCofibrations_iff] at hi ⊢
  intro E F p hp
  let P := Functor.PullbackObjObj.ofHasPullback cotensorBifunctor k p
  exact (levelSmashCotensorAdjunction₂.hasLiftingProperty_iff Q.flip P).2
    (hi P.π (levelTrivialFibrations_cotensor_pullbackObjObjπ_of_levelTrivialFibrations k p hp P))

/-- The pushout-product `(A ∧ L) ⨿_(A ∧ K) (B ∧ K) ⟶ B ∧ L` of a projective cofibration and an
anodyne based map lifts against every level fibration. -/
theorem llp_levelFibrations_levelSmash_pushoutObjObjι_of_anodyneExtensions {i : A ⟶ B} {k : K ⟶ L}
    (hi : projectiveCofibrations i) (hk : SSet.anodyneExtensions k.right)
    (Q : curriedLevelSmash.PushoutObjObj i k) :
    levelFibrations.llp Q.ι := by
  rw [projectiveCofibrations_iff] at hi
  intro E F p hp
  let P := Functor.PullbackObjObj.ofHasPullback cotensorBifunctor k p
  exact (levelSmashCotensorAdjunction₂.hasLiftingProperty_iff Q.flip P).2
    (hi P.π (levelTrivialFibrations_cotensor_pullbackObjObjπ k p hk hp P))

/-- The pushout-product `(A ∧ L) ⨿_(A ∧ K) (B ∧ K) ⟶ B ∧ L` of a map lifting against all level
fibrations and a based monomorphism again lifts against all level fibrations. -/
theorem llp_levelFibrations_levelSmash_pushoutObjObjι {i : A ⟶ B} {k : K ⟶ L}
    (hi : levelFibrations.llp i) [Mono k.right] (Q : curriedLevelSmash.PushoutObjObj i k) :
    levelFibrations.llp Q.ι := by
  intro E F p hp
  let P := Functor.PullbackObjObj.ofHasPullback cotensorBifunctor k p
  exact (levelSmashCotensorAdjunction₂.hasLiftingProperty_iff Q.flip P).2
    (hi P.π (levelFibrations_cotensor_pullbackObjObjπ k p hp P))

/-- The unpointed simplicial pushout-product `(A ∧ V₊) ⨿_(A ∧ U₊) (B ∧ U₊) ⟶ B ∧ V₊` of a
projective cofibration and a simplicial monomorphism is a projective cofibration. -/
theorem projectiveCofibrations_simplicialTensor_pushoutObjObjι {i : A ⟶ B} {j : U ⟶ V}
    (hi : projectiveCofibrations i) [Mono j] (Q : simplicialTensor.PushoutObjObj i j) :
    projectiveCofibrations Q.ι := by
  rw [projectiveCofibrations_iff] at hi ⊢
  intro E F p hp
  let P := Functor.PullbackObjObj.ofHasPullback simplicialCotensor j p
  exact (simplicialTensorCotensorAdjunction₂.hasLiftingProperty_iff Q.flip P).2
    (hi P.π
      (levelTrivialFibrations_simplicialCotensor_pullbackObjObjπ_of_levelTrivialFibrations j p hp
        P))

/-- The unpointed simplicial pushout-product `(A ∧ V₊) ⨿_(A ∧ U₊) (B ∧ U₊) ⟶ B ∧ V₊` of a
projective cofibration and an anodyne extension lifts against every level fibration. -/
theorem llp_levelFibrations_simplicialTensor_pushoutObjObjι_of_anodyneExtensions {i : A ⟶ B}
    {j : U ⟶ V} (hi : projectiveCofibrations i) (hj : SSet.anodyneExtensions j)
    (Q : simplicialTensor.PushoutObjObj i j) :
    levelFibrations.llp Q.ι := by
  rw [projectiveCofibrations_iff] at hi
  intro E F p hp
  let P := Functor.PullbackObjObj.ofHasPullback simplicialCotensor j p
  exact (simplicialTensorCotensorAdjunction₂.hasLiftingProperty_iff Q.flip P).2
    (hi P.π (levelTrivialFibrations_simplicialCotensor_pullbackObjObjπ j p hj hp P))

/-- The unpointed simplicial pushout-product `(A ∧ V₊) ⨿_(A ∧ U₊) (B ∧ U₊) ⟶ B ∧ V₊` of a map
lifting against all level fibrations and a simplicial monomorphism again lifts against all level
fibrations. -/
theorem llp_levelFibrations_simplicialTensor_pushoutObjObjι {i : A ⟶ B} {j : U ⟶ V}
    (hi : levelFibrations.llp i) [Mono j] (Q : simplicialTensor.PushoutObjObj i j) :
    levelFibrations.llp Q.ι := by
  intro E F p hp
  let P := Functor.PullbackObjObj.ofHasPullback simplicialCotensor j p
  exact (simplicialTensorCotensorAdjunction₂.hasLiftingProperty_iff Q.flip P).2
    (hi P.π (levelFibrations_simplicialCotensor_pullbackObjObjπ j p hp P))

/-- Levelwise smash with any pointed simplicial set `K` preserves projective cofibrations. -/
theorem projectiveCofibrations_levelSmashRight_map (K : PointedSSet.{0}) {i : A ⟶ B}
    (hi : projectiveCofibrations i) :
    projectiveCofibrations ((levelSmashRight K).map i) := by
  let k : Under.mk (𝟙 (Δ[0] : SSet.{0})) ⟶ K := Under.homMk K.hom
  have : Mono k.right := SSet.stdSimplex.isTerminalObj₀.mono_from K.hom
  exact projectiveCofibrations_levelSmash_pushoutObjObjι hi
    (Functor.PushoutObjObj.ofIsInitialRight curriedLevelSmash i k Under.mkIdInitial)

/-- Levelwise smash with any pointed simplicial set `K` preserves maps lifting against all level
fibrations. -/
theorem llp_levelFibrations_levelSmashRight_map (K : PointedSSet.{0}) {i : A ⟶ B}
    (hi : levelFibrations.llp i) :
    levelFibrations.llp ((levelSmashRight K).map i) := by
  let k : Under.mk (𝟙 (Δ[0] : SSet.{0})) ⟶ K := Under.homMk K.hom
  have : Mono k.right := SSet.stdSimplex.isTerminalObj₀.mono_from K.hom
  exact llp_levelFibrations_levelSmash_pushoutObjObjι hi
    (Functor.PushoutObjObj.ofIsInitialRight curriedLevelSmash i k Under.mkIdInitial)

/-- Smashing a projective-cofibrant spectrum with a based monomorphism gives a projective
cofibration. -/
theorem projectiveCofibrations_levelSmash_map {X : SymmetricSpectrum}
    (hX : projectiveCofibrations (initial.to X)) (k : K ⟶ L) [Mono k.right] :
    projectiveCofibrations ((levelSmash X).map k) :=
  projectiveCofibrations_levelSmash_pushoutObjObjι hX
    (Functor.PushoutObjObj.ofIsInitialLeft curriedLevelSmash (initial.to X) k initialIsInitial)

/-- Smashing a projective-cofibrant spectrum with an anodyne based map gives a map lifting against
all level fibrations. -/
theorem llp_levelFibrations_levelSmash_map {X : SymmetricSpectrum}
    (hX : projectiveCofibrations (initial.to X)) {k : K ⟶ L} (hk : SSet.anodyneExtensions k.right) :
    levelFibrations.llp ((levelSmash X).map k) :=
  llp_levelFibrations_levelSmash_pushoutObjObjι_of_anodyneExtensions hX hk
    (Functor.PushoutObjObj.ofIsInitialLeft curriedLevelSmash (initial.to X) k initialIsInitial)

end PushoutProducts

/-! ### Mapping-space pullback-hom corners -/

section MappingSpaceCorners

variable {A B E F : SymmetricSpectrum}

/-- The unpointed spectral mapping-space corner `Map(B, E) ⟶ Map(A, E) ×[Map(A, F)] Map(B, F)` of
a projective cofibration and a level fibration is a Kan fibration. -/
theorem fibration_simplicialMappingSpace_pullbackObjObjπ {i : A ⟶ B} {p : E ⟶ F}
    (hi : projectiveCofibrations i) (hp : levelFibrations p)
    (P : simplicialMappingSpace.PullbackObjObj i p) :
    Fibration P.π := by
  rw [HomotopicalAlgebra.fibration_iff,
    ← rlp_eq_of_wfs (W₁ := SSet.anodyneExtensions.{0}) (W₂ := fibrations SSet.{0})]
  intro U V j hj
  let Q := Functor.PushoutObjObj.ofHasPushout simplicialTensor i j
  rw [← simplicialTensorMappingSpaceAdjunction₂.hasLiftingProperty_iff Q P]
  exact llp_levelFibrations_simplicialTensor_pushoutObjObjι_of_anodyneExtensions hi hj Q p hp

/-- The unpointed spectral mapping-space corner `Map(B, E) ⟶ Map(A, E) ×[Map(A, F)] Map(B, F)` of
a map lifting against all level fibrations and a level fibration lifts against every simplicial
monomorphism. -/
theorem rlp_monomorphisms_simplicialMappingSpace_pullbackObjObjπ {i : A ⟶ B} {p : E ⟶ F}
    (hi : levelFibrations.llp i) (hp : levelFibrations p)
    (P : simplicialMappingSpace.PullbackObjObj i p) :
    (monomorphisms SSet.{0}).rlp P.π := by
  intro U V j (_ : Mono j)
  let Q := Functor.PushoutObjObj.ofHasPushout simplicialTensor i j
  rw [← simplicialTensorMappingSpaceAdjunction₂.hasLiftingProperty_iff Q P]
  exact llp_levelFibrations_simplicialTensor_pushoutObjObjι hi Q p hp

/-- The unpointed spectral mapping-space corner `Map(B, E) ⟶ Map(A, E) ×[Map(A, F)] Map(B, F)` of
a projective cofibration and a level trivial fibration lifts against every simplicial
monomorphism. -/
theorem rlp_monomorphisms_simplicialMappingSpace_pullbackObjObjπ_of_levelTrivialFibrations
    {i : A ⟶ B} {p : E ⟶ F} (hi : projectiveCofibrations i) (hp : levelTrivialFibrations p)
    (P : simplicialMappingSpace.PullbackObjObj i p) :
    (monomorphisms SSet.{0}).rlp P.π := by
  intro U V j (_ : Mono j)
  let Q := Functor.PushoutObjObj.ofHasPushout simplicialTensor i j
  rw [← simplicialTensorMappingSpaceAdjunction₂.hasLiftingProperty_iff Q P]
  exact ((projectiveCofibrations_iff _).1
    (projectiveCofibrations_simplicialTensor_pushoutObjObjι hi Q)) p hp

/-- The pointed spectral mapping-space corner `Map(B, E) ⟶ Map(A, E) ×[Map(A, F)] Map(B, F)` of a
projective cofibration and a level fibration is a Kan fibration on underlying simplicial sets. -/
theorem fibration_mappingSpace_pullbackObjObjπ {i : A ⟶ B} {p : E ⟶ F}
    (hi : projectiveCofibrations i) (hp : levelFibrations p)
    (P : mappingSpaceBifunctor.PullbackObjObj i p) :
    Fibration P.π.right :=
  fibration_simplicialMappingSpace_pullbackObjObjπ hi hp (P.map forgetBasepoint)

/-- The pointed spectral mapping-space corner `Map(B, E) ⟶ Map(A, E) ×[Map(A, F)] Map(B, F)` of a
map lifting against all level fibrations and a level fibration lifts against every simplicial
monomorphism on underlying simplicial sets. -/
theorem rlp_monomorphisms_mappingSpace_pullbackObjObjπ {i : A ⟶ B} {p : E ⟶ F}
    (hi : levelFibrations.llp i) (hp : levelFibrations p)
    (P : mappingSpaceBifunctor.PullbackObjObj i p) :
    (monomorphisms SSet.{0}).rlp P.π.right :=
  rlp_monomorphisms_simplicialMappingSpace_pullbackObjObjπ hi hp (P.map forgetBasepoint)

/-- The pointed spectral mapping-space corner `Map(B, E) ⟶ Map(A, E) ×[Map(A, F)] Map(B, F)` of a
projective cofibration and a level trivial fibration lifts against every simplicial monomorphism on
underlying simplicial sets. -/
theorem rlp_monomorphisms_mappingSpace_pullbackObjObjπ_of_levelTrivialFibrations
    {i : A ⟶ B} {p : E ⟶ F} (hi : projectiveCofibrations i) (hp : levelTrivialFibrations p)
    (P : mappingSpaceBifunctor.PullbackObjObj i p) :
    (monomorphisms SSet.{0}).rlp P.π.right :=
  rlp_monomorphisms_simplicialMappingSpace_pullbackObjObjπ_of_levelTrivialFibrations hi hp
    (P.map forgetBasepoint)

/-- Mapping out of a projective-cofibrant spectrum carries level fibrations to Kan fibrations. -/
theorem fibration_mappingSpace_map {X : SymmetricSpectrum}
    (hX : projectiveCofibrations (initial.to X)) {p : E ⟶ F} (hp : levelFibrations p) :
    Fibration ((mappingSpace X).map p).right :=
  fibration_mappingSpace_pullbackObjObjπ hX hp
    (Functor.PullbackObjObj.ofIsInitial mappingSpaceBifunctor (initial.to X) p initialIsInitial)

/-- Mapping out of a projective-cofibrant spectrum carries level trivial fibrations to maps lifting
against all simplicial monomorphisms. -/
theorem rlp_monomorphisms_mappingSpace_map {X : SymmetricSpectrum}
    (hX : projectiveCofibrations (initial.to X)) {p : E ⟶ F} (hp : levelTrivialFibrations p) :
    (monomorphisms SSet.{0}).rlp ((mappingSpace X).map p).right :=
  rlp_monomorphisms_mappingSpace_pullbackObjObjπ_of_levelTrivialFibrations hX hp
    (Functor.PullbackObjObj.ofIsInitial mappingSpaceBifunctor (initial.to X) p initialIsInitial)

/-- Mapping out of a projective-cofibrant spectrum carries level trivial fibrations to weak
equivalences of simplicial sets. -/
theorem weakEquivalence_mappingSpace_map_of_levelTrivialFibrations {X : SymmetricSpectrum}
    (hX : projectiveCofibrations (initial.to X)) {p : E ⟶ F} (hp : levelTrivialFibrations p) :
    WeakEquivalence ((mappingSpace X).map p).right :=
  weakEquivalence_of_rlp_monomorphisms (rlp_monomorphisms_mappingSpace_map hX hp)

/-- For a projective-cofibrant spectrum `X` and a spectrum `E` whose levels are Kan complexes, the
mapping space `Map(X, E)` is a Kan complex. -/
theorem kanComplex_mappingSpace {X : SymmetricSpectrum}
    (hX : projectiveCofibrations (initial.to X)) (E : SymmetricSpectrum)
    (hE : ∀ n, SSet.KanComplex ((evaluation n).obj E).right) :
    SSet.KanComplex ((mappingSpace X).obj E).right :=
  (isFibrant_iff_of_isTerminal ((mappingSpace X).map (terminal.from E)).right
    (terminalIsTerminal.isTerminalObj (mappingSpace X ⋙ forgetBasepoint)
      (⊤_ SymmetricSpectrum))).2
    (fibration_mappingSpace_map hX ((levelFibrations_terminal_from_iff E).2 hE))

/-- Precomposition `Map(B, E) ⟶ Map(A, E)` along a projective cofibration is a Kan fibration
whenever every level of `E` is a Kan complex. -/
theorem fibration_mappingSpaceBifunctor_map_app {i : A ⟶ B} (hi : projectiveCofibrations i)
    (E : SymmetricSpectrum) (hE : ∀ n, SSet.KanComplex ((evaluation n).obj E).right) :
    Fibration ((mappingSpaceBifunctor.map i.op).app E).right :=
  fibration_mappingSpace_pullbackObjObjπ hi ((levelFibrations_terminal_from_iff E).2 hE)
    (Functor.PullbackObjObj.ofIsTerminal mappingSpaceBifunctor i (terminal.from E)
      terminalIsTerminal)

/-- Precomposition `Map(B, E) ⟶ Map(A, E)` along a map lifting against all level fibrations lifts
against every simplicial monomorphism whenever every level of `E` is a Kan complex. -/
theorem rlp_monomorphisms_mappingSpaceBifunctor_map_app {i : A ⟶ B} (hi : levelFibrations.llp i)
    (E : SymmetricSpectrum) (hE : ∀ n, SSet.KanComplex ((evaluation n).obj E).right) :
    (monomorphisms SSet.{0}).rlp ((mappingSpaceBifunctor.map i.op).app E).right :=
  rlp_monomorphisms_mappingSpace_pullbackObjObjπ hi ((levelFibrations_terminal_from_iff E).2 hE)
    (Functor.PullbackObjObj.ofIsTerminal mappingSpaceBifunctor i (terminal.from E)
      terminalIsTerminal)

/-- Precomposition `Map(B, E) ⟶ Map(A, E)` along a map lifting against all level fibrations is a
weak equivalence of simplicial sets whenever every level of `E` is a Kan complex. -/
theorem weakEquivalence_mappingSpaceBifunctor_map_app_of_llp_levelFibrations {i : A ⟶ B}
    (hi : levelFibrations.llp i) (E : SymmetricSpectrum)
    (hE : ∀ n, SSet.KanComplex ((evaluation n).obj E).right) :
    WeakEquivalence ((mappingSpaceBifunctor.map i.op).app E).right :=
  weakEquivalence_of_rlp_monomorphisms
    (rlp_monomorphisms_mappingSpaceBifunctor_map_app hi E hE)

end MappingSpaceCorners

end TauCeti.SymmetricSpectrum
