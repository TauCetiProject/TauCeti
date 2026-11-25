/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import TauCeti.AlgebraicGeometry.Cohomology.Module.Base
public import TauCeti.AlgebraicGeometry.Modules.Tensor.Product
public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.TwistingSheaf.Basic
public import TauCeti.LinearAlgebra.SymmetricAlgebra.Grading
import TauCeti.Algebra.Homology.ShortComplex.ShortExact
import TauCeti.AlgebraicGeometry.Cohomology.Biproduct
import TauCeti.AlgebraicGeometry.Cohomology.ClosedImmersion.Linear
import TauCeti.AlgebraicGeometry.Cohomology.LongExactSequence
import TauCeti.AlgebraicGeometry.Cohomology.ProjectiveSpace.HigherCohomology
import TauCeti.AlgebraicGeometry.Cohomology.ProjectiveSpace.Vanishing
import TauCeti.AlgebraicGeometry.LineBundle.GlobalGeneration.Ample
import TauCeti.AlgebraicGeometry.Modules.Biprod
import TauCeti.AlgebraicGeometry.Modules.FinitePresentation.Abelian
import TauCeti.AlgebraicGeometry.Modules.Quasicoherent.Pushforward.Finite
import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.TwistingSheaf.Ample
import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.TwistingSheaf.Pullback
import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.TwistingSheaf.TensorProduct
import TauCeti.AlgebraicGeometry.VectorBundle.ProjectionFormula

/-!
# Serre's vanishing theorem on projective schemes

This file proves Serre's vanishing theorem for quasi-coherent modules of finite type on projective
schemes over a Noetherian commutative ring.

The argument proceeds in three steps:
1. On `Proj (Sym_R M)` for a finite `R`-module `M`, `𝒪(1)` is ample
   (`TauCeti.SymmetricAlgebra.isAmple_twistingSheaf`), so every quasi-coherent module of finite
   type receives an epimorphism from a finite direct sum `⨁_{Fin k} 𝒪(-n)` for all sufficiently
   large `n` (`AlgebraicGeometry.Scheme.Modules.exists_epi_biproduct_of_isAmple`).
2. On projective space `ℙⁿ_R = Proj (Sym_R M)` over a Noetherian ring `R` (with `M` finite free of
   rank at least `2`), descending induction on the cohomological degree from the vanishing bound
   `Hᵠ(ℙⁿ_R, F) = 0` for `q > n` combines this presentation with the long exact cohomology sequence
   and the explicit cohomology of twisting sheaves to establish vanishing of `Hᵠ(𝒪(m) ⊗ F)` for
   `q > 0` and `m ≫ 0`.
3. Every closed subscheme `i : X ⟶ Proj (Sym_R M)` embeds over `Spec R` into some
   `Proj (Sym_R (Fin (d + 2) → R))`. Pushing `F` forward along the closed immersion preserves
   coherence and cohomology, and the projection formula transfers twisting sheaves, yielding
   Serre's vanishing theorem for arbitrary closed subschemes of `Proj (Sym_R M)`.

## Main results

* `AlgebraicGeometry.Scheme.Modules.exists_subsingleton_cohomology_pullback_twistingSheaf_tensor`:
  **Serre's vanishing theorem** — for a closed immersion `i : X ⟶ Proj (Sym_R M)` with `R`
  Noetherian and `M` finite, and a quasi-coherent `𝒪_X`-module `F` of finite type,
  `Hᵠ(X, i^* 𝒪(n) ⊗ F) = 0` for all `q > 0` and all sufficiently large `n : ℤ`.
* `AlgebraicGeometry.Scheme.Modules.exists_subsingleton_cohomology_twistingSheaf_tensor`:
  specialization of Serre's vanishing theorem to `Proj (Sym_R M)` itself.

## References

* R. Hartshorne, *Algebraic Geometry*, GTM 52, Springer, 1977, Theorem III.5.2 (Serre finiteness
  and vanishing).
* [The Stacks Project, Tag 01Q3](https://stacks.math.columbia.edu/tag/01Q3) (global generation
  after twisting by an ample invertible sheaf).
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
  let L : TauCeti.AlgebraicGeometry.InvertibleSheaf (Proj (homogeneousSubmodule R M)) :=
    ⟨Proj.twistingSheaf (homogeneousSubmodule R M) (1 : ℕ), inferInstance⟩
  have hL : (TauCeti.AlgebraicGeometry.LineBundleClass.mk L).IsAmple :=
    SymmetricAlgebra.isAmple_twistingSheaf R M Nat.one_pos
  obtain ⟨m, hm⟩ := G.exists_epi_biproduct_of_isAmple L hL
  let K : TauCeti.AlgebraicGeometry.InvertibleSheaf (Proj (homogeneousSubmodule R M)) :=
    ⟨Proj.twistingSheaf (homogeneousSubmodule R M) (-(m : ℤ)), inferInstance⟩
  have hK : TauCeti.AlgebraicGeometry.LineBundleClass.mk K =
      (TauCeti.AlgebraicGeometry.LineBundleClass.mk L ^ m)⁻¹ := by
    rw [← zpow_natCast, ← zpow_neg]
    exact Proj.lineBundleClass_twistingSheaf_eq_zpow (_root_.SymmetricAlgebra.ι R M)
      (ι_mem_homogeneousSubmodule R M) (iSup_basicOpen_ι_eq_top R M id (by simp)) (-(m : ℤ))
  obtain ⟨k, p, _⟩ := hm m le_rfl K hK
  exact ⟨m, k, p, Scheme.Modules.isFinitePresentation_kernel p, TauCeti.kernelSequence_shortExact p⟩

/-- Fixed-degree Serre vanishing on positive-dimensional projective space `Proj (Sym_R M)` over a
Noetherian ring `R`, proved by descending induction on the cohomological degree. -/
private theorem exists_subsingleton_cohomology_tensor_twistingSheaf_of_basis_of_pos
    {R M : Type u} [CommRing R] [IsNoetherianRing R] [AddCommMonoid M] [Module R M]
    {κ : Type*} [Fintype κ] [Nontrivial κ] (b : Module.Basis κ R M) :
    ∀ (d : ℕ) (G : (Proj (homogeneousSubmodule R M)).Modules)
      [G.IsQuasicoherent] [G.IsFiniteType] (r : ℕ), 0 < r → Fintype.card κ ≤ r + d →
      ∃ n₀ : ℤ, ∀ n ≥ n₀,
        Subsingleton (Cohomology (Proj.twistingSheaf (homogeneousSubmodule R M) n ⊗ G) r) := by
  have : Module.Finite R M := Module.Finite.of_basis b
  have : MonoidalPreadditive (Proj (homogeneousSubmodule R M)).Modules :=
    TauCeti.SheafOfModules.monoidalPreadditive (Proj (homogeneousSubmodule R M)).sheaf
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

/-- Serre's vanishing theorem on positive-dimensional projective space `Proj (Sym_R M)` over a
Noetherian ring `R`, uniform across all positive cohomological degrees. -/
private theorem exists_subsingleton_cohomology_tensor_twistingSheaf_of_basis
    {R M : Type u} [CommRing R] [IsNoetherianRing R] [AddCommMonoid M] [Module R M]
    {κ : Type*} [Finite κ] [Nontrivial κ] (b : Module.Basis κ R M)
    (F : (Proj (homogeneousSubmodule R M)).Modules) [F.IsQuasicoherent] [F.IsFiniteType] :
    ∃ n₀ : ℤ, ∀ n ≥ n₀, ∀ q > 0,
      Subsingleton (Cohomology (Proj.twistingSheaf (homogeneousSubmodule R M) n ⊗ F) q) := by
  have := Fintype.ofFinite κ
  have : Module.Finite R M := Module.Finite.of_basis b
  -- Take a uniform bound over the finitely many degrees `1 ≤ q < card κ`; degrees `≥ card κ`
  -- vanish automatically.
  have hfin : ∀ q ∈ Finset.Ico 1 (Fintype.card κ), ∀ᶠ n : ℤ in Filter.atTop,
      Subsingleton (Cohomology (Proj.twistingSheaf (homogeneousSubmodule R M) n ⊗ F) q) :=
    fun q hq ↦ Filter.eventually_atTop.mpr
      (exists_subsingleton_cohomology_tensor_twistingSheaf_of_basis_of_pos b
        (Fintype.card κ) F q (Finset.mem_Ico.mp hq).1 (by omega))
  obtain ⟨n₀, hn₀⟩ := Filter.eventually_atTop.mp ((Filter.eventually_all_finset _).mpr hfin)
  refine ⟨n₀, fun n hn q hq ↦ ?_⟩
  by_cases hlt : q < Fintype.card κ
  · exact hn₀ n hn q (Finset.mem_Ico.mpr ⟨hq, hlt⟩)
  · have : (Proj.twistingSheaf (homogeneousSubmodule R M) n ⊗ F).IsQuasicoherent :=
      Scheme.Modules.isQuasicoherent_tensorObj _ _ _
    exact b.subsingleton_cohomology_proj_of_card_le _ q (by omega)

end TauCeti.AlgebraicGeometry.Serre

namespace AlgebraicGeometry.Scheme.Modules

open TauCeti.SymmetricAlgebra TauCeti.AlgebraicGeometry.Serre

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
  obtain ⟨d, j, _, _, hjPull⟩ :=
    exists_isClosedImmersion_proj_fin_add_with_pullbackTwistingSheafIso R M 2
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

end AlgebraicGeometry.Scheme.Modules

end
