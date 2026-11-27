/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Noetherian.Defs
public import TauCeti.AlgebraicGeometry.Cohomology.Module.Base
public import TauCeti.AlgebraicGeometry.Modules.Tensor.Product
public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.SymmetricAlgebra
public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.TwistingSheaf.Basic
import Mathlib.LinearAlgebra.StdBasis
import TauCeti.Algebra.Category.ModuleCat.Sheaf.Free.Basic
import TauCeti.Algebra.Homology.ShortComplex.ShortExact
import TauCeti.AlgebraicGeometry.Cohomology.Biproduct
import TauCeti.AlgebraicGeometry.Cohomology.ClosedImmersion.Linear
import TauCeti.AlgebraicGeometry.Cohomology.LongExactSequence
import TauCeti.AlgebraicGeometry.Cohomology.ProjectiveSpace.HigherCohomology
import TauCeti.AlgebraicGeometry.Cohomology.ProjectiveSpace.Vanishing
import TauCeti.AlgebraicGeometry.Modules.FinitePresentation.Abelian
import TauCeti.AlgebraicGeometry.Modules.Quasicoherent.Pushforward.Finite
import TauCeti.AlgebraicGeometry.Modules.Tensor.FinitePresentation
import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.ClosedImmersion
import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.LinearAction
import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.TwistingSheaf.GlobalGeneration
import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.TwistingSheaf.Pullback
import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.TwistingSheaf.Quasicoherent
import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.TwistingSheaf.TensorProduct
import TauCeti.AlgebraicGeometry.VectorBundle.Dual.Basic
import TauCeti.AlgebraicGeometry.VectorBundle.FiniteLocallyFree
import TauCeti.AlgebraicGeometry.VectorBundle.ProjectionFormula

/-!
# Serre's vanishing theorem on projective space and projective schemes

Let `R` be a Noetherian commutative ring and `M` a finitely generated `R`-module, and let
`P = Proj (Sym_R M)` be the associated projective scheme over `Spec R` (in particular
`ℙⁿ_R = Proj (Sym_R R^{n+1})`). For every quasi-coherent `𝒪_P`-module `F` of finite type:

1. **Serre's vanishing theorem**
   (`TauCeti.SymmetricAlgebra.exists_subsingleton_cohomology_tensor_twistingSheaf`): there exists
   `m₀ : ℤ` such that `H^q(P, F ⊗ 𝒪_P(m)) = 0` for all `m ≥ m₀` and all `q > 0`.
2. **Closed subschemes**
   (`AlgebraicGeometry.Scheme.Hom.exists_subsingleton_cohomology_tensor_pullback_twistingSheaf`):
   for any closed immersion `i : X ⟶ P` and any quasi-coherent `𝒪_X`-module `F` of finite type,
   `H^q(X, F ⊗ i^* 𝒪_P(m)) = 0` for all sufficiently large `m` and all `q > 0`.

## Proof overview

On `Proj (Sym_R M)` for a finite `R`-module `M`, Serre's global generation theorem
(`Proj.eventually_exists_epi_free_tensor_twistingSheaf`) presents any quasi-coherent sheaf `F` of
finite type as a quotient of `𝒪^{⊕J} ⊗ 𝒪(-r)` for a finite index type `J`.

When `M` is free on a finite nonempty basis `b` and `R` is Noetherian, the kernel `K` of
`𝒪^{⊕J} ⊗ 𝒪(-r) ⟶ F` is again coherent (`Scheme.Modules.isFinitePresentation_kernel`), giving a
short exact sequence `0 ⟶ K ⟶ 𝒪^{⊕J} ⊗ 𝒪(-r) ⟶ F ⟶ 0`. Vanishing follows by downward induction
on `q > 0` from the vanishing above the dimension
(`Module.Basis.subsingleton_cohomology_proj_of_card_le`), using the long exact cohomology sequence
(`Scheme.Modules.subsingleton_cohomology_X₃`) together with the explicit vanishing for twisting
sheaves `𝒪(m)` (`Module.Basis.subsingleton_cohomology_twistingSheaf_of_neg_card_lt`).

For an arbitrary finite `R`-module `M`, choosing a surjection `(Fin (n + 2) → R) →ₗ[R] M` embeds
`Proj (Sym_R M)` as a closed subscheme over `Spec R` of `Proj (Sym_R (Fin (n + 2) → R))`. Pushing
forward along the closed immersion preserves coherence
(`Scheme.Modules.isFinitePresentation_pushforward_of_isFinite`) and cohomology
(`Scheme.Hom.cohomologyPushforwardIso`), and commutes with twisting by `𝒪(m)` via the projection
formula (`FiniteLocallyFreeSheaf.pushforwardTensorLeftIso`) and pullback of twisting sheaves
(`Proj.isIso_pullbackTwistingSheafMap`).

## References

* R. Hartshorne, *Algebraic Geometry*, GTM 52, Springer, 1977, Theorem III.5.2(b).
* [The Stacks Project, Tag 01XT](https://stacks.math.columbia.edu/tag/01XT).
-/

public section

open CategoryTheory Limits MonoidalCategory BraidedCategory AlgebraicGeometry
  AlgebraicGeometry.Scheme.Modules TauCeti TauCeti.AlgebraicGeometry
  TauCeti.AlgebraicGeometry.Scheme.Modules

universe u

noncomputable section

namespace TauCeti.AlgebraicGeometry

variable {X : Scheme.{u}}

/-- Transfer `Subsingleton` of cohomology along an isomorphism of `𝒪_X`-modules. -/
private theorem subsingleton_cohomology_of_iso {M N : X.Modules} (e : M ≅ N) (q : ℕ)
    (h : Subsingleton (Cohomology M q)) : Subsingleton (Cohomology N q) := by
  have : Subsingleton ((cohomologyFunctor X q).obj M) := h
  exact ((cohomologyFunctor X q).mapIso e).addCommGroupIsoToAddEquiv.symm.injective.subsingleton

/-- Transport cohomology vanishing of a twist `F ⊗ K` along a closed immersion `i : X ⟶ Y`
from the pushforward `(pushforward i).obj F ⊗ L` via the projection formula, given an
identification `i^* L ≅ K`. -/
private theorem subsingleton_cohomology_tensor_of_isClosedImmersion {X Y : Scheme.{u}}
    (i : X ⟶ Y) [IsClosedImmersion i] (F : X.Modules) (L : Y.Modules)
    [SheafOfModules.isInvertible Y L] (K : X.Modules)
    (epb : (Scheme.Modules.pullback i).obj L ≅ K) (q : ℕ)
    (h : Subsingleton (Cohomology ((pushforward i).obj F ⊗ L) q)) :
    Subsingleton (Cohomology (F ⊗ K) q) := by
  let L' := (InvertibleSheaf.toFiniteLocallyFree Y).obj ⟨L, inferInstance⟩
  let epb' : ((FiniteLocallyFreeSheaf.pullback i).obj L').obj ≅ K :=
    eqToIso (FiniteLocallyFreeSheaf.pullback_obj_obj i L') ≪≫ epb
  let e : (pushforward i).obj F ⊗ L ≅ (pushforward i).obj (F ⊗ K) :=
    β_ ((pushforward i).obj F) L ≪≫
      (FiniteLocallyFreeSheaf.pushforwardTensorLeftIso i L').app F ≪≫
      (pushforward i).mapIso (whiskerRightIso epb' F ≪≫ β_ K F)
  have hpush : Subsingleton (Cohomology ((pushforward i).obj (F ⊗ K)) q) :=
    subsingleton_cohomology_of_iso e q h
  exact (cohomologyPushforwardIso i (F ⊗ K) q).addCommGroupIsoToAddEquiv
    |>.symm.injective.subsingleton

end TauCeti.AlgebraicGeometry

namespace TauCeti.SymmetricAlgebra

variable {R M : Type u} [CommRing R] [AddCommMonoid M] [Module R M]

local notation "𝒜" => homogeneousSubmodule R M

/-- Helper: on `Proj (Sym_R M)` over a Noetherian ring `R`, any finite-type quasi-coherent sheaf
`F` admits a surjection `𝒪^{⊕J} ⊗ 𝒪(-r) ⟶ F` whose kernel is again quasi-coherent of finite
type. -/
private theorem exists_epi_free_tensor_twistingSheaf_kernel [IsNoetherianRing R]
    [Module.Finite R M] (F : (Proj 𝒜).Modules) [F.IsQuasicoherent] [F.IsFiniteType] :
    ∃ (r : ℕ) (J : Type u) (_ : Finite J)
      (π : (SheafOfModules.free J : (Proj 𝒜).Modules) ⊗ Proj.twistingSheaf 𝒜 (-(r : ℤ)) ⟶ F)
      (_ : Epi π),
      (kernel π).IsQuasicoherent ∧ (kernel π).IsFiniteType := by
  obtain ⟨r, J, hJ, π, hπ⟩ := (Proj.eventually_exists_epi_free_tensor_twistingSheaf
    (_root_.SymmetricAlgebra.ι R M) (ι_mem_homogeneousSubmodule R M)
    (iSup_basicOpen_ι_eq_top R M id (by simp)) F).exists
  have : Epi π := hπ
  have : ((SheafOfModules.free J : (Proj 𝒜).Modules) ⊗
      Proj.twistingSheaf 𝒜 (-(r : ℤ))).IsFinitePresentation :=
    isFinitePresentation_tensorObj (Proj 𝒜) _ _
  have : (kernel π).IsFinitePresentation := isFinitePresentation_kernel π
  exact ⟨r, J, hJ, π, hπ, isQuasicoherent_of_isFinitePresentation _,
    isFiniteType_of_isFinitePresentation _⟩

/-! ### Serre's vanishing theorem on projective space with a basis -/

section Basis

variable [IsNoetherianRing R] {κ : Type*} [Finite κ]

/-- Downward induction step for Serre's vanishing theorem on `ℙⁿ_R`. -/
private theorem serre_vanishing_step (b : Module.Basis κ R M) (q : ℕ) (hq : 0 < q)
    (ih : ∀ (G : (Proj 𝒜).Modules) [G.IsQuasicoherent] [G.IsFiniteType],
      ∃ m₀ : ℤ, ∀ m ≥ m₀, Subsingleton (Cohomology (G ⊗ Proj.twistingSheaf 𝒜 m) (q + 1)))
    (F : (Proj 𝒜).Modules) [F.IsQuasicoherent] [F.IsFiniteType] :
    ∃ m₀ : ℤ, ∀ m ≥ m₀, Subsingleton (Cohomology (F ⊗ Proj.twistingSheaf 𝒜 m) q) := by
  cases nonempty_fintype κ
  have : Module.Finite R M := Module.Finite.of_basis b
  obtain ⟨r, J, hJ, π, hπ, hKq, hKf⟩ := exists_epi_free_tensor_twistingSheaf_kernel F
  let : Fintype J := @Fintype.ofFinite J hJ
  have : Epi π := hπ
  have hS := TauCeti.kernelSequence_shortExact π
  obtain ⟨m₁, hm₁⟩ := @ih (kernel π) hKq hKf
  refine ⟨max m₁ ((r : ℤ) + 1 - Fintype.card κ), fun m hm ↦ ?_⟩
  have hm1 : m₁ ≤ m := le_trans (le_max_left _ _) hm
  have hmr : -(Fintype.card κ : ℤ) < m + -(r : ℤ) := by
    have := le_trans (le_max_right _ _) hm
    omega
  have hSm := shortExact_map_tensorLeft (Proj.twistingSheaf 𝒜 m) hS
  let eK : Iso (C := (Proj 𝒜).Modules) (kernel π ⊗ Proj.twistingSheaf 𝒜 m)
      (Proj.twistingSheaf 𝒜 m ⊗ kernel π) := β_ _ _
  have hK : Subsingleton (Cohomology (Proj.twistingSheaf 𝒜 m ⊗ kernel π) (q + 1)) :=
    subsingleton_cohomology_of_iso eK (q + 1) (hm₁ m hm1)
  have hE : Subsingleton (Cohomology
      (Proj.twistingSheaf 𝒜 m ⊗
        ((SheafOfModules.free J : (Proj 𝒜).Modules) ⊗ Proj.twistingSheaf 𝒜 (-(r : ℤ)))) q) := by
    have : HasBiproduct (C := (Proj 𝒜).Modules) fun _ : J ↦ Proj.twistingSheaf 𝒜 (m + -(r : ℤ)) :=
      HasBiproduct.of_hasCoproduct _
    let eTwist : Proj.twistingSheaf 𝒜 m ⊗ Proj.twistingSheaf 𝒜 (-(r : ℤ)) ≅
        Proj.twistingSheaf 𝒜 (m + -(r : ℤ)) :=
      Proj.twistingSheaf.tensorObjIso (_root_.SymmetricAlgebra.ι R M)
        (ι_mem_homogeneousSubmodule R M) (iSup_basicOpen_ι_eq_top R M id (by simp)) m (-r)
    let eE : Iso (C := (Proj 𝒜).Modules)
        (Proj.twistingSheaf 𝒜 m ⊗
          ((SheafOfModules.free J : (Proj 𝒜).Modules) ⊗ Proj.twistingSheaf 𝒜 (-(r : ℤ))))
        (⨁ fun _ : J ↦ Proj.twistingSheaf 𝒜 (m + -(r : ℤ))) :=
      whiskerLeftIso _ (β_ _ _) ≪≫ (α_ _ _ _).symm ≪≫
        whiskerRightIso eTwist _ ≪≫
        (TauCeti.SheafOfModules.biproductConstIsoTensorFree (R := (Proj 𝒜).sheaf)
          (Proj.twistingSheaf 𝒜 (m + -(r : ℤ))) J).symm
    have hsub : Subsingleton (Cohomology (Proj.twistingSheaf 𝒜 (m + -(r : ℤ))) q) :=
      b.subsingleton_cohomology_twistingSheaf_of_neg_card_lt hmr hq
    have hsum : Subsingleton (Cohomology (⨁ fun _ : J ↦ Proj.twistingSheaf 𝒜 (m + -(r : ℤ))) q) :=
      (cohomologyBiproductLinearEquiv R _ q).injective.subsingleton
    exact subsingleton_cohomology_of_iso eE.symm q hsum
  have hF : Subsingleton (Cohomology (Proj.twistingSheaf 𝒜 m ⊗ F) q) :=
    subsingleton_cohomology_X₃ hSm q (q + 1) rfl hE hK
  exact subsingleton_cohomology_of_iso (β_ (Proj.twistingSheaf 𝒜 m) F) q hF

/-- Serre's vanishing theorem on `Proj (Sym_R M)` for a nonempty finite basis, in a single positive
degree `q`. -/
private theorem exists_subsingleton_cohomology_tensor_of_basis_deg [Nonempty κ]
    (b : Module.Basis κ R M) (q : ℕ) (hq : 0 < q)
    (F : (Proj 𝒜).Modules) [F.IsQuasicoherent] [F.IsFiniteType] :
    ∃ m₀ : ℤ, ∀ m ≥ m₀, Subsingleton (Cohomology (F ⊗ Proj.twistingSheaf 𝒜 m) q) := by
  cases nonempty_fintype κ
  have : Module.Finite R M := Module.Finite.of_basis b
  by_cases hq' : Fintype.card κ ≤ q
  · refine ⟨0, fun m _ ↦ ?_⟩
    exact b.subsingleton_cohomology_proj_of_card_le (F ⊗ Proj.twistingSheaf 𝒜 m) q hq'
  · refine Nat.decreasingInduction'
      (motive := fun k ↦ ∀ (G : (Proj 𝒜).Modules) [G.IsQuasicoherent] [G.IsFiniteType],
        ∃ m₀ : ℤ, ∀ m ≥ m₀, Subsingleton (Cohomology (G ⊗ Proj.twistingSheaf 𝒜 m) k))
      (n := Fintype.card κ)
      (fun k _ hqk ih G _ _ ↦ serre_vanishing_step b k (lt_of_lt_of_le hq hqk) ih G)
      (le_of_not_ge hq') ?_ F
    intro G _ _
    refine ⟨0, fun m _ ↦ ?_⟩
    exact b.subsingleton_cohomology_proj_of_card_le (G ⊗ Proj.twistingSheaf 𝒜 m)
      (Fintype.card κ) le_rfl

/-- Uniform Serre vanishing across all positive degrees for a nonempty finite basis. -/
private theorem exists_subsingleton_cohomology_tensor_of_basis [Nonempty κ]
    (b : Module.Basis κ R M) (F : (Proj 𝒜).Modules) [F.IsQuasicoherent] [F.IsFiniteType] :
    ∃ m₀ : ℤ, ∀ m ≥ m₀, ∀ q > 0, Subsingleton (Cohomology (F ⊗ Proj.twistingSheaf 𝒜 m) q) := by
  cases nonempty_fintype κ
  have : Module.Finite R M := Module.Finite.of_basis b
  have hdeg (i : Fin (Fintype.card κ)) :
      ∃ m₀ : ℤ, ∀ m ≥ m₀,
        Subsingleton (Cohomology (F ⊗ Proj.twistingSheaf 𝒜 m) (i.val + 1)) :=
    exists_subsingleton_cohomology_tensor_of_basis_deg b (i.val + 1) (Nat.succ_pos i.val) F
  choose m₀ hm₀ using hdeg
  refine ⟨Finset.univ.sup' Finset.univ_nonempty m₀, fun m hm q hq ↦ ?_⟩
  by_cases hq' : Fintype.card κ ≤ q
  · exact b.subsingleton_cohomology_proj_of_card_le (F ⊗ Proj.twistingSheaf 𝒜 m) q hq'
  · let i : Fin (Fintype.card κ) := ⟨q - 1, by omega⟩
    have hmi : m₀ i ≤ m := (Finset.le_sup' m₀ (Finset.mem_univ i)).trans hm
    have hiq : i.val + 1 = q := by dsimp [i]; omega
    simpa only [hiq] using hm₀ i m hmi

end Basis

/-! ### Serre's vanishing theorem for any finite module `M` -/

/-- **Serre's vanishing theorem** (Hartshorne, Theorem III.5.2(b)). Let `R` be a Noetherian ring
and `M` a finitely generated `R`-module. For every quasi-coherent sheaf `F` of finite type on
`Proj (Sym_R M)`, there exists `m₀ : ℤ` such that `H^q(Proj (Sym_R M), F ⊗ 𝒪(m)) = 0` for all
`m ≥ m₀` and all `q > 0`. -/
theorem exists_subsingleton_cohomology_tensor_twistingSheaf [IsNoetherianRing R] [Module.Finite R M]
    (F : (Proj 𝒜).Modules) [F.IsQuasicoherent] [F.IsFiniteType] :
    ∃ m₀ : ℤ, ∀ m ≥ m₀, ∀ q > 0,
      Subsingleton (Cohomology (F ⊗ Proj.twistingSheaf 𝒜 m) q) := by
  obtain ⟨n, g, hg⟩ := Module.Finite.exists_fin' R M
  let q : (Fin (n + 2) → R) →ₗ[R] M := g ∘ₗ LinearMap.funLeft R R (Fin.castAdd 2)
  have hq : Function.Surjective q :=
    hg.comp (LinearMap.funLeft_surjective_of_injective R R _ (Fin.castAdd_injective n 2))
  let φ := _root_.SymmetricAlgebra.gradedMap R q
  have hφ : Function.Surjective φ := fun a ↦ by
    obtain ⟨x, hx⟩ := _root_.SymmetricAlgebra.map_surjective R q hq a
    exact ⟨x, (_root_.SymmetricAlgebra.gradedMap_apply R q x).trans hx⟩
  have hirr := HomogeneousIdeal.irrelevant_le_map_of_surjective φ hφ
  let i := Proj.map φ hirr
  have : IsClosedImmersion i := Proj.isClosedImmersion_map φ hirr hφ
  have : i.IsOver (Spec (.of R)) := ⟨Proj.map_gradedMap_projToSpec R q hirr⟩
  have : ((pushforward i).obj F).IsFinitePresentation :=
    isFinitePresentation_pushforward_of_isFinite i F
  have : ((pushforward i).obj F).IsQuasicoherent := isQuasicoherent_of_isFinitePresentation _
  have : ((pushforward i).obj F).IsFiniteType := isFiniteType_of_isFinitePresentation _
  obtain ⟨m₀, hm₀⟩ :=
    exists_subsingleton_cohomology_tensor_of_basis (Pi.basisFun R (Fin (n + 2)))
      ((pushforward i).obj F)
  refine ⟨m₀, fun m hm k hk ↦ ?_⟩
  exact subsingleton_cohomology_tensor_of_isClosedImmersion i F
    (Proj.twistingSheaf (homogeneousSubmodule R (Fin (n + 2) → R)) m)
    (Proj.twistingSheaf 𝒜 m)
    (@asIso _ _ _ _ _ (isIso_pullbackTwistingSheafMap φ hirr m))
    k (hm₀ m hm k hk)

end TauCeti.SymmetricAlgebra

namespace AlgebraicGeometry.Scheme.Hom

variable {R M : Type u} [CommRing R] [AddCommMonoid M] [Module R M]

/-- **Serre's vanishing theorem for closed subschemes of projective space.** Let `R` be a
Noetherian ring, `M` a finitely generated `R`-module, and `i : X ⟶ Proj (Sym_R M)` a closed
immersion. For every quasi-coherent `𝒪_X`-module `F` of finite type, there exists `m₀ : ℤ` such
that `H^q(X, F ⊗ i^* 𝒪(m)) = 0` for all `m ≥ m₀` and all `q > 0`. -/
theorem exists_subsingleton_cohomology_tensor_pullback_twistingSheaf [IsNoetherianRing R]
    [Module.Finite R M] {X : Scheme.{u}}
    (i : X ⟶ Proj (TauCeti.SymmetricAlgebra.homogeneousSubmodule R M)) [IsClosedImmersion i]
    (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType] :
    ∃ m₀ : ℤ, ∀ m ≥ m₀, ∀ q > 0,
      Subsingleton (Cohomology
        (F ⊗ (Scheme.Modules.pullback i).obj
          (Proj.twistingSheaf (TauCeti.SymmetricAlgebra.homogeneousSubmodule R M) m)) q) := by
  let 𝒜 := TauCeti.SymmetricAlgebra.homogeneousSubmodule R M
  have : ((pushforward i).obj F).IsFinitePresentation :=
    isFinitePresentation_pushforward_of_isFinite i F
  have : ((pushforward i).obj F).IsQuasicoherent := isQuasicoherent_of_isFinitePresentation _
  have : ((pushforward i).obj F).IsFiniteType := isFiniteType_of_isFinitePresentation _
  obtain ⟨m₀, hm₀⟩ :=
    TauCeti.SymmetricAlgebra.exists_subsingleton_cohomology_tensor_twistingSheaf
      ((pushforward i).obj F)
  refine ⟨m₀, fun m hm q hq ↦ ?_⟩
  exact subsingleton_cohomology_tensor_of_isClosedImmersion i F
    (Proj.twistingSheaf 𝒜 m) _ (Iso.refl _) q (hm₀ m hm q hq)

end AlgebraicGeometry.Scheme.Hom

end
