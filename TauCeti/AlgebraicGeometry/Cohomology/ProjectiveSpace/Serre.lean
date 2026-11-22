/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Cohomology.Module.Base
public import TauCeti.AlgebraicGeometry.Modules.Tensor.Product
public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.ProjectiveOver
public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.TwistingSheaf.Basic
import Mathlib.Algebra.Module.Equiv.Basic
import TauCeti.Algebra.Homology.ShortComplex.ShortExact
import TauCeti.AlgebraicGeometry.Cohomology.Biproduct
import TauCeti.AlgebraicGeometry.Cohomology.ClosedImmersion.Linear
import TauCeti.AlgebraicGeometry.Cohomology.LongExactSequence
import TauCeti.AlgebraicGeometry.Cohomology.ProjectiveSpace.HigherCohomology
import TauCeti.AlgebraicGeometry.Cohomology.ProjectiveSpace.Vanishing
import TauCeti.AlgebraicGeometry.Modules.Biprod
import TauCeti.AlgebraicGeometry.Modules.FinitePresentation.Abelian
import TauCeti.AlgebraicGeometry.Modules.Quasicoherent.Pushforward.Finite
import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.TwistingSheaf.Ample
import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.TwistingSheaf.Pullback
import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.TwistingSheaf.TensorProduct
import TauCeti.AlgebraicGeometry.VectorBundle.Dual.Basic
import TauCeti.AlgebraicGeometry.VectorBundle.ProjectionFormula

/-!
# Serre's finiteness and vanishing theorems on projective schemes

This file proves Serre's finiteness and vanishing theorems for quasi-coherent modules of finite
type on projective schemes over a Noetherian commutative ring.

The argument proceeds in three steps:
1. On a quasi-compact, quasi-separated `Proj A` covered by degree-one standard opens, `𝒪(1)` is
   ample (`AlgebraicGeometry.Proj.isAmple_twistingSheaf`), so every quasi-coherent module of finite
   type admits a surjection from a finite direct sum `⨁_{Fin k} 𝒪(-n)` for all sufficiently large
   `n` (`AlgebraicGeometry.Proj.exists_epi_biproduct_twistingSheaf`).
2. On projective space `ℙⁿ_R = Proj (Sym_R M)` over a Noetherian ring `R` (with `M` finite free of
   rank at least `2`), descending induction on the cohomological degree from the vanishing bound
   `Hᵠ(ℙⁿ_R, F) = 0` for `q > n` combines this presentation with the long exact cohomology sequence
   and the explicit cohomology of twisting sheaves to establish both finite generation of `Hᵠ(F)`
   and vanishing of `Hᵠ(𝒪(m) ⊗ F)` for `q > 0` and `m ≫ 0`.
3. Every projective scheme `X` over `R` embeds as a closed subscheme over `R` into some
   `Proj (Sym_R (Fin (d + 2) → R))`. Pushing `F` forward along the closed immersion preserves
   coherence and cohomology, and the projection formula transfers twisting sheaves, yielding
   Serre's finiteness and vanishing theorems for arbitrary projective schemes over a Noetherian
   ring.

## Main results

* `AlgebraicGeometry.Scheme.Modules.finite_cohomology_of_isProjectiveOver`: **Serre's finiteness
  theorem** — for a projective scheme `X` over a Noetherian ring `R` and a quasi-coherent
  `𝒪_X`-module `F` of finite type, `Hᵠ(X, F)` is a finitely generated `R`-module for every `q`.
* `AlgebraicGeometry.Scheme.Modules.exists_subsingleton_cohomology_pullback_twistingSheaf_tensor`:
  **Serre's vanishing theorem** — for a closed immersion `i : X ⟶ Proj (Sym_R M)` with `R`
  Noetherian and `M` finite, and a quasi-coherent `𝒪_X`-module `F` of finite type,
  `Hᵠ(X, i^* 𝒪(n) ⊗ F) = 0` for all `q > 0` and all sufficiently large `n : ℤ`.
* `TauCeti.SymmetricAlgebra.exists_subsingleton_cohomology_twistingSheaf_tensor`: specialization of
  Serre's vanishing theorem to `Proj (Sym_R M)` itself.

## References

* R. Hartshorne, *Algebraic Geometry*, GTM 52, Springer, 1977, Theorem III.5.2 (Serre finiteness
  and vanishing).
* [The Stacks Project, Tag 01Q3](https://stacks.math.columbia.edu/tag/01Q3) (global generation
  after twisting by an ample invertible sheaf) and
  [Tag 02O6](https://stacks.math.columbia.edu/tag/02O6) (finiteness of cohomology of coherent
  sheaves on proper schemes).
-/

public section

open CategoryTheory Limits MonoidalCategory AlgebraicGeometry Scheme.Modules
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme.Modules

universe u

noncomputable section

namespace TauCeti.AlgebraicGeometry.Serre

open TauCeti.SymmetricAlgebra

/-- On `Proj (Sym_R M)` for a finite module `M` over a Noetherian ring `R`, every quasi-coherent
module `G` of finite type fits into a short exact sequence
`0 ⟶ K ⟶ ⨁_{Fin k} 𝒪(-m) ⟶ G ⟶ 0` whose kernel `K` is finitely presented. -/
private lemma exists_kernel_shortExact_biproduct_twistingSheaf
    {R M : Type u} [CommRing R] [IsNoetherianRing R] [AddCommMonoid M] [Module R M]
    [Module.Finite R M] (G : (Proj (homogeneousSubmodule R M)).Modules)
    [G.IsQuasicoherent] [G.IsFiniteType] :
    ∃ (m k : ℕ)
      (p : (⨁ fun _ : Fin k ↦ Proj.twistingSheaf (homogeneousSubmodule R M) (-(m : ℤ))) ⟶ G),
      (kernel p).IsFinitePresentation ∧
        (ShortComplex.mk (kernel.ι p) p (kernel.condition p)).ShortExact := by
  have : QuasiSeparatedSpace (Proj (homogeneousSubmodule R M)) :=
    quasiSeparatedSpace_of_quasiSeparated (projToSpec R M)
  obtain ⟨m, hm⟩ := Proj.exists_epi_biproduct_twistingSheaf (_root_.SymmetricAlgebra.ι R M)
    (ι_mem_homogeneousSubmodule R M) (iSup_basicOpen_ι_eq_top R M id (by simp)) G
  obtain ⟨k, p, hp⟩ := hm m le_rfl
  exact ⟨m, k, p, Scheme.Modules.isFinitePresentation_kernel p, TauCeti.kernelSequence_shortExact p⟩

/-- Serre's finiteness theorem on positive-dimensional projective space `Proj (Sym_R M)` over a
Noetherian ring `R`, proved by descending induction on the cohomological degree. -/
private theorem finite_cohomology_proj_of_basis {R M : Type u} [CommRing R] [IsNoetherianRing R]
    [AddCommMonoid M] [Module R M] {κ : Type*} [Finite κ] [Nontrivial κ]
    (b : Module.Basis κ R M) (F : (Proj (homogeneousSubmodule R M)).Modules)
    [F.IsQuasicoherent] [F.IsFiniteType] (q : ℕ) :
    Module.Finite R (Cohomology F q) := by
  have := Fintype.ofFinite κ
  have : Module.Finite R M := Module.Finite.of_basis b
  -- Descending induction on `d` with `card κ ≤ q + d`.
  suffices h : ∀ (d : ℕ) (G : (Proj (homogeneousSubmodule R M)).Modules)
      [G.IsQuasicoherent] [G.IsFiniteType] (r : ℕ),
      Fintype.card κ ≤ r + d → Module.Finite R (Cohomology G r) from
    h (Fintype.card κ) F q (by omega)
  intro d
  induction d with
  | zero =>
    intro G _ _ r hr
    have := b.subsingleton_cohomology_proj_of_card_le G r (by omega)
    infer_instance
  | succ d ih =>
    intro G _ _ r hr
    obtain ⟨m, k, p, _, hS⟩ := exists_kernel_shortExact_biproduct_twistingSheaf G
    let T : (Proj (homogeneousSubmodule R M)).Modules :=
      Proj.twistingSheaf (homogeneousSubmodule R M) (-(m : ℤ))
    have hE : Module.Finite R (Cohomology (⨁ fun _ : Fin k ↦ T) r) := by
      have (_ : Fin k) : Module.Finite R (Cohomology T r) :=
        b.finite_cohomology_twistingSheaf (-(m : ℤ)) r
      exact Module.Finite.equiv
        (Scheme.Modules.cohomologyBiproductLinearEquiv R (fun _ : Fin k ↦ T) r).symm
    have hK : Module.Finite R (Cohomology (kernel p) (r + 1)) :=
      ih (kernel p) (r + 1) (by omega)
    let δ := cohomologyδBaseLinear R (Proj (homogeneousSubmodule R M)) hS r (r + 1) rfl
    have hex : Function.Exact (cohomologyMapBaseLinear R (Proj (homogeneousSubmodule R M)) p r)
        δ :=
      exact_cohomologyMapBaseLinear_cohomologyδBaseLinear R (Proj (homogeneousSubmodule R M)) hS r
    have hNoeth : IsNoetherian R (Cohomology (kernel p) (r + 1)) :=
      isNoetherian_of_isNoetherianRing_of_finite R (Cohomology (kernel p) (r + 1))
    have : Module.Finite R (LinearMap.range δ) :=
      Module.Finite.iff_fg.mpr (hNoeth.noetherian (LinearMap.range δ))
    exact Module.Finite.of_exact hex.rangeRestrict (LinearMap.surjective_rangeRestrict δ)

/-- Serre's vanishing theorem on positive-dimensional projective space `Proj (Sym_R M)` over a
Noetherian ring `R`, proved by descending induction on the cohomological degree. -/
private theorem exists_subsingleton_cohomology_tensor_twistingSheaf_of_basis
    {R M : Type u} [CommRing R] [IsNoetherianRing R] [AddCommMonoid M] [Module R M]
    {κ : Type*} [Finite κ] [Nontrivial κ] (b : Module.Basis κ R M)
    (F : (Proj (homogeneousSubmodule R M)).Modules) [F.IsQuasicoherent] [F.IsFiniteType] :
    ∃ n₀ : ℤ, ∀ n ≥ n₀, ∀ q > 0,
      Subsingleton (Cohomology (Proj.twistingSheaf (homogeneousSubmodule R M) n ⊗ F) q) := by
  have := Fintype.ofFinite κ
  have : Module.Finite R M := Module.Finite.of_basis b
  have : MonoidalPreadditive (Proj (homogeneousSubmodule R M)).Modules :=
    TauCeti.SheafOfModules.monoidalPreadditive (Proj (homogeneousSubmodule R M)).sheaf
  -- Per-degree vanishing by descending induction on `d` with `card κ ≤ r + d`.
  have hdeg : ∀ (d : ℕ) (G : (Proj (homogeneousSubmodule R M)).Modules)
      [G.IsQuasicoherent] [G.IsFiniteType] (r : ℕ), 0 < r → Fintype.card κ ≤ r + d →
      ∃ n₀ : ℤ, ∀ n ≥ n₀,
        Subsingleton (Cohomology (Proj.twistingSheaf (homogeneousSubmodule R M) n ⊗ G) r) := by
    intro d
    induction d with
    | zero =>
      intro G _ _ r _ hr
      refine ⟨0, fun n _ ↦ ?_⟩
      have : (Proj.twistingSheaf (homogeneousSubmodule R M) n ⊗ G).IsQuasicoherent :=
        Scheme.Modules.isQuasicoherent_tensorObj _ _ _
      exact b.subsingleton_cohomology_proj_of_card_le _ r (by omega)
    | succ d ih =>
      intro G _ _ r hr hrcard
      obtain ⟨m, k, p, _, hS⟩ := exists_kernel_shortExact_biproduct_twistingSheaf G
      let T : (Proj (homogeneousSubmodule R M)).Modules :=
        Proj.twistingSheaf (homogeneousSubmodule R M) (-(m : ℤ))
      obtain ⟨n₁, hn₁⟩ := ih (kernel p) (r + 1) (Nat.succ_pos r) (by omega)
      refine ⟨max n₁ ((m : ℤ) + 1 - Fintype.card κ), fun n hn ↦ ?_⟩
      let L : (Proj (homogeneousSubmodule R M)).Modules :=
        Proj.twistingSheaf (homogeneousSubmodule R M) n
      have hSn : ((ShortComplex.mk (kernel.ι p) p (kernel.condition p)).map
          (tensorLeft L)).ShortExact :=
        Scheme.Modules.shortExact_map_tensorLeft L hS
      -- `L ⊗ E ≅ ⨁_{Fin k} 𝒪(n - m)` has vanishing `H^r` since `n - m > -card κ`.
      have hE : Subsingleton (Cohomology (L ⊗ (⨁ fun _ : Fin k ↦ T)) r) := by
        let eE : L ⊗ (⨁ fun _ : Fin k ↦ T) ≅ ⨁ fun _ : Fin k ↦
            Proj.twistingSheaf (homogeneousSubmodule R M) (n + -(m : ℤ)) :=
          leftDistributor L (fun _ : Fin k ↦ T) ≪≫
            biproduct.mapIso fun _ ↦
              Proj.twistingSheaf.tensorObjIso (_root_.SymmetricAlgebra.ι R M)
                (ι_mem_homogeneousSubmodule R M) (iSup_basicOpen_ι_eq_top R M id (by simp))
                n (-(m : ℤ))
        have hsum : ∀ _ : Fin k,
            Subsingleton (Cohomology
              (Proj.twistingSheaf (homogeneousSubmodule R M) (n + -(m : ℤ))) r) := fun _ ↦
          b.subsingleton_cohomology_twistingSheaf_of_neg_card_lt
            (by have := (le_max_right n₁ _).trans hn; omega) hr
        have hpi : Subsingleton
            (∀ _ : Fin k, Cohomology
              (Proj.twistingSheaf (homogeneousSubmodule R M) (n + -(m : ℤ))) r) :=
          inferInstance
        exact ((cohomologyBaseLinearEquivOfIso R eE r).trans
          (cohomologyBiproductLinearEquiv R _ r)).toEquiv.subsingleton
      have hK : Subsingleton (Cohomology (L ⊗ kernel p) (r + 1)) :=
        hn₁ n ((le_max_left n₁ _).trans hn)
      exact TauCeti.AlgebraicGeometry.Scheme.Modules.subsingleton_cohomology_X₃
        hSn r (r + 1) rfl hE hK
  -- Take a uniform bound over the finitely many degrees `1 ≤ q < card κ`; degrees `≥ card κ`
  -- vanish automatically.
  choose N hN using fun q (hq : 0 < q) ↦ hdeg (Fintype.card κ) F q hq (by omega)
  let s : Finset ℕ := Finset.Ico 1 (Fintype.card κ)
  have hs : s.attach.Nonempty :=
    ⟨⟨1, Finset.mem_Ico.mpr ⟨le_rfl, Fintype.one_lt_card⟩⟩, Finset.mem_attach _ _⟩
  refine ⟨s.attach.sup' hs (fun q ↦ N q.val (Finset.mem_Ico.mp q.property).left),
    fun n hn q hq ↦ ?_⟩
  by_cases hlt : q < Fintype.card κ
  · have hqmem : q ∈ s := Finset.mem_Ico.mpr ⟨hq, hlt⟩
    have hle : N q hq ≤ n :=
      (Finset.le_sup' (f := fun x : {x // x ∈ s} ↦ N x.val (Finset.mem_Ico.mp x.property).left)
        (Finset.mem_attach s ⟨q, hqmem⟩)).trans hn
    exact hN q hq n hle
  · have : (Proj.twistingSheaf (homogeneousSubmodule R M) n ⊗ F).IsQuasicoherent :=
      Scheme.Modules.isQuasicoherent_tensorObj _ _ _
    exact b.subsingleton_cohomology_proj_of_card_le _ q (by omega)

end TauCeti.AlgebraicGeometry.Serre

namespace AlgebraicGeometry.Scheme.Modules

open TauCeti.SymmetricAlgebra TauCeti.AlgebraicGeometry.Serre

/-- **Serre's finiteness theorem.** Let `X` be a projective scheme over a Noetherian commutative
ring `R` and `F` a quasi-coherent `𝒪_X`-module of finite type. Then `Hᵠ(X, F)` is a finitely
generated `R`-module for every `q : ℕ`. -/
theorem finite_cohomology_of_isProjectiveOver (R : Type u) [CommRing R] [IsNoetherianRing R]
    {X : Scheme.{u}} [X.Over (Spec (.of R))] [X.IsProjectiveOver R]
    (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType] (q : ℕ) :
    Module.Finite R (Cohomology F q) := by
  obtain ⟨M, _, _, _, i₀, hi₀, hi₀R⟩ :=
    Scheme.IsProjectiveOver.exists_isClosedImmersion (R := R) (X := X)
  obtain ⟨d, j, _, _, -⟩ := exists_isClosedImmersion_proj_fin_add R M 2
  let i : X ⟶ Proj (homogeneousSubmodule R (Fin (d + 2) → R)) := i₀ ≫ j
  have : ((pushforward i).obj F).IsFinitePresentation :=
    isFinitePresentation_pushforward_of_isFinite i F
  exact (i.moduleFinite_cohomology_pushforward_iff R F q).mp
    (finite_cohomology_proj_of_basis (Pi.basisFun R (Fin (d + 2))) ((pushforward i).obj F) q)

/-- **Serre's vanishing theorem.** Let `R` be a Noetherian commutative ring, `M` a finite
`R`-module, `i : X ⟶ Proj (Sym_R M)` a closed immersion, and `F` a quasi-coherent `𝒪_X`-module of
finite type. Then there exists `n₀ : ℤ` such that `Hᵠ(X, i^* 𝒪(n) ⊗ F) = 0` for every `n ≥ n₀`
and every `q > 0`. -/
theorem exists_subsingleton_cohomology_pullback_twistingSheaf_tensor
    {R M : Type u} [CommRing R] [IsNoetherianRing R] [AddCommMonoid M] [Module R M]
    [Module.Finite R M] {X : Scheme.{u}}
    (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType]
    (i : X ⟶ Proj (homogeneousSubmodule R M)) [IsClosedImmersion i] :
    ∃ n₀ : ℤ, ∀ n ≥ n₀, ∀ q > 0,
      Subsingleton (Cohomology
        ((pullback i).obj (Proj.twistingSheaf (homogeneousSubmodule R M) n) ⊗ F) q) := by
  obtain ⟨d, j, _, _, hjPull⟩ := exists_isClosedImmersion_proj_fin_add R M 2
  let ι : X ⟶ Proj (homogeneousSubmodule R (Fin (d + 2) → R)) := i ≫ j
  have : ((pushforward ι).obj F).IsFinitePresentation :=
    isFinitePresentation_pushforward_of_isFinite ι F
  obtain ⟨n₀, hn₀⟩ := exists_subsingleton_cohomology_tensor_twistingSheaf_of_basis
    (Pi.basisFun R (Fin (d + 2))) ((pushforward ι).obj F)
  refine ⟨n₀, fun n hn q hq ↦ ?_⟩
  have hvan : Subsingleton (Cohomology
      (Proj.twistingSheaf (homogeneousSubmodule R (Fin (d + 2) → R)) n ⊗
        (pushforward ι).obj F) q) :=
    hn₀ n hn q hq
  -- Identify `𝒪_{ℙ}(n) ⊗ ι_* F ≅ ι_* (i^* 𝒪_{Proj (Sym M)}(n) ⊗ F)` via the projection formula
  -- and the pullback isomorphism for twisting sheaves.
  obtain ⟨ej⟩ := hjPull n
  let E : FiniteLocallyFreeSheaf (Proj (homogeneousSubmodule R (Fin (d + 2) → R))) :=
    (InvertibleSheaf.toFiniteLocallyFree _).obj
      ⟨Proj.twistingSheaf (homogeneousSubmodule R (Fin (d + 2) → R)) n, inferInstance⟩
  let ePull : ((FiniteLocallyFreeSheaf.pullback ι).obj E).obj ≅
      (pullback i).obj (Proj.twistingSheaf (homogeneousSubmodule R M) n) :=
    eqToIso (FiniteLocallyFreeSheaf.pullback_obj_obj ι E) ≪≫
      ((Scheme.Modules.pullbackComp i j).app E.obj).symm ≪≫
      (pullback i).mapIso ej
  let eProj : Proj.twistingSheaf (homogeneousSubmodule R (Fin (d + 2) → R)) n ⊗
      (pushforward ι).obj F ≅
      (pushforward ι).obj
        ((pullback i).obj (Proj.twistingSheaf (homogeneousSubmodule R M) n) ⊗ F) :=
    (FiniteLocallyFreeSheaf.pushforwardTensorLeftIso ι E).app F ≪≫
      (pushforward ι).mapIso (whiskerRightIso ePull F)
  let eCoh : Cohomology
        (Proj.twistingSheaf (homogeneousSubmodule R (Fin (d + 2) → R)) n ⊗
          (pushforward ι).obj F) q ≃+
      Cohomology
        ((pullback i).obj (Proj.twistingSheaf (homogeneousSubmodule R M) n) ⊗ F) q :=
    (((cohomologyFunctor _ q).mapIso eProj).addCommGroupIsoToAddEquiv).trans
      (cohomologyPushforwardIso ι _ q).addCommGroupIsoToAddEquiv
  exact eCoh.symm.toEquiv.subsingleton

end AlgebraicGeometry.Scheme.Modules

namespace TauCeti.SymmetricAlgebra

/-- **Serre's vanishing theorem on `Proj (Sym_R M)`.** Let `R` be a Noetherian commutative ring,
`M` a finite `R`-module, and `F` a quasi-coherent `𝒪`-module of finite type on `Proj (Sym_R M)`.
Then there exists `n₀ : ℤ` such that `Hᵠ(Proj (Sym_R M), 𝒪(n) ⊗ F) = 0` for every `n ≥ n₀` and
every `q > 0`. -/
theorem exists_subsingleton_cohomology_twistingSheaf_tensor
    {R M : Type u} [CommRing R] [IsNoetherianRing R] [AddCommMonoid M] [Module R M]
    [Module.Finite R M] (F : (Proj (homogeneousSubmodule R M)).Modules)
    [F.IsQuasicoherent] [F.IsFiniteType] :
    ∃ n₀ : ℤ, ∀ n ≥ n₀, ∀ q > 0,
      Subsingleton (Cohomology (Proj.twistingSheaf (homogeneousSubmodule R M) n ⊗ F) q) := by
  obtain ⟨n₀, hn₀⟩ :=
    F.exists_subsingleton_cohomology_pullback_twistingSheaf_tensor
      (𝟙 (Proj (homogeneousSubmodule R M)))
  refine ⟨n₀, fun n hn q hq ↦ ?_⟩
  have hvan : Subsingleton (Cohomology
      ((Scheme.Modules.pullback (𝟙 (Proj (homogeneousSubmodule R M)))).obj
        (Proj.twistingSheaf (homogeneousSubmodule R M) n) ⊗ F) q) :=
    hn₀ n hn q hq
  let e : (Scheme.Modules.pullback (𝟙 (Proj (homogeneousSubmodule R M)))).obj
        (Proj.twistingSheaf (homogeneousSubmodule R M) n) ⊗ F ≅
      Proj.twistingSheaf (homogeneousSubmodule R M) n ⊗ F :=
    whiskerRightIso ((Scheme.Modules.pullbackId _).app _) F
  let eCoh : Cohomology
        ((Scheme.Modules.pullback (𝟙 (Proj (homogeneousSubmodule R M)))).obj
          (Proj.twistingSheaf (homogeneousSubmodule R M) n) ⊗ F) q ≃+
      Cohomology (Proj.twistingSheaf (homogeneousSubmodule R M) n ⊗ F) q :=
    ((cohomologyFunctor _ q).mapIso e).addCommGroupIsoToAddEquiv
  exact eCoh.symm.toEquiv.subsingleton

end TauCeti.SymmetricAlgebra

end
