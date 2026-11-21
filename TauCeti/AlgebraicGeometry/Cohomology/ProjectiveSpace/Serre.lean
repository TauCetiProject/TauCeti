/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Noetherian.Defs
public import TauCeti.AlgebraicGeometry.Cohomology.Module.Base
public import TauCeti.AlgebraicGeometry.Modules.Tensor.Product
public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.ProjectiveOver
public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.TwistingSheaf.Basic
import Mathlib.Algebra.Homology.ShortComplex.Exact
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import Mathlib.LinearAlgebra.StdBasis
import TauCeti.AlgebraicGeometry.Cohomology.Biproduct
import TauCeti.AlgebraicGeometry.Cohomology.ClosedImmersion.Linear
import TauCeti.AlgebraicGeometry.Cohomology.LongExactSequence
import TauCeti.AlgebraicGeometry.Cohomology.ProjectiveSpace.HigherCohomology
import TauCeti.AlgebraicGeometry.Cohomology.ProjectiveSpace.Vanishing
import TauCeti.AlgebraicGeometry.LineBundle.GlobalGeneration.Ample
import TauCeti.AlgebraicGeometry.Modules.FinitePresentation.Abelian
import TauCeti.AlgebraicGeometry.Modules.Quasicoherent.Pushforward.Finite
import TauCeti.AlgebraicGeometry.Modules.Tensor.FinitePresentation
import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.ProjectiveOver.ClosedImmersion
import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.TwistingSheaf.Ample
import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.TwistingSheaf.Pullback
import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.TwistingSheaf.TensorProduct
import TauCeti.AlgebraicGeometry.VectorBundle.Dual.Basic
import TauCeti.AlgebraicGeometry.VectorBundle.FiniteLocallyFree
import TauCeti.AlgebraicGeometry.VectorBundle.ProjectionFormula
import TauCeti.LinearAlgebra.Exact.Noetherian

/-!
# Serre's finiteness and vanishing theorems on projective space

Let `R` be a Noetherian commutative ring and `M` a finitely generated `R`-module, and let
`P = Proj (Sym_R M)` be the associated projective scheme over `Spec R` (in particular
`ℙⁿ_R = Proj (Sym_R R^{n+1})`). For every quasi-coherent `𝒪_P`-module `F` of finite type:

1. **Serre's finiteness theorem** (`TauCeti.SymmetricAlgebra.finite_cohomology_proj`): the
   cohomology `H^q(P, F)` is a finitely generated `R`-module for every `q : ℕ`.
2. **Serre's vanishing theorem**
   (`TauCeti.SymmetricAlgebra.exists_subsingleton_cohomology_tensor_twistingSheaf`): there exists
   `m₀ : ℤ` such that `H^q(P, F ⊗ 𝒪_P(m)) = 0` for all `m ≥ m₀` and all `q > 0`.
3. **Closed subschemes**
   (`AlgebraicGeometry.Scheme.Hom.exists_subsingleton_cohomology_tensor_pullback_twistingSheaf`):
   for any closed immersion `i : X ⟶ P` and any quasi-coherent `𝒪_X`-module `F` of finite type,
   `H^q(X, F ⊗ i^* 𝒪_P(m)) = 0` for all sufficiently large `m` and all `q > 0`.

## Proof overview

On any quasi-compact quasi-separated `Proj A` covered by degree-one standard opens, `𝒪(1)` is
ample (`Proj.isAmple_twistingSheaf`), so Serre's global generation theorem
(`Scheme.Modules.exists_epi_free_tensorPow_of_isAmple`) gives for any quasi-coherent sheaf `F` of
finite type a surjection `⨁_J 𝒪(-r) ⟶ F` from a finite direct sum of copies of `𝒪(-r)` for all
sufficiently large `r` (`Proj.exists_epi_biproduct_twistingSheaf`).

When `M` is free on a finite basis `b` of size at least two and `R` is Noetherian, the kernel `K`
of `⨁_J 𝒪(-r) ⟶ F` is again coherent (`Scheme.Modules.isFinitePresentation_kernel`), giving a
short exact sequence `0 ⟶ K ⟶ ⨁_J 𝒪(-r) ⟶ F ⟶ 0`. Both finiteness and vanishing follow by
downward induction on `q` from the vanishing above the dimension
(`Module.Basis.subsingleton_cohomology_proj_of_card_le`), using the long exact cohomology sequence
(`Scheme.Modules.exact_cohomologyMapBaseLinear_cohomologyδBaseLinear`, `TauCeti.finite_of_exact`,
`Scheme.Modules.subsingleton_cohomology_X₃`) together with the explicit cohomology of the twisting
sheaves `𝒪(m)` (`Module.Basis.finite_cohomology_twistingSheaf`,
`Module.Basis.subsingleton_cohomology_twistingSheaf_of_neg_card_lt`).

For an arbitrary finite `R`-module `M`, choosing a surjection `(Fin (n + 2) → R) →ₗ[R] M` embeds
`Proj (Sym_R M)` as a closed subscheme over `Spec R` of `Proj (Sym_R (Fin (n + 2) → R))`, which
has a finite basis of size `n + 2 ≥ 2`. Pushing forward along the closed immersion preserves
coherence (`Scheme.Modules.isFinitePresentation_pushforward_of_isFinite`) and cohomology
(`Scheme.Hom.cohomologyPushforwardBaseLinearEquiv`), and commutes with twisting by `𝒪(m)` via the
projection formula (`FiniteLocallyFreeSheaf.pushforwardTensorLeftIso`) and pullback of twisting
sheaves (`Proj.pullbackTwistingSheafIso`).

## References

* R. Hartshorne, *Algebraic Geometry*, GTM 52, Springer, 1977, Theorem III.5.2.
* [The Stacks Project, Tag 01XS / Tag 01XT](https://stacks.math.columbia.edu/tag/01XT).
-/

public section

open CategoryTheory Limits MonoidalCategory BraidedCategory AlgebraicGeometry
  AlgebraicGeometry.Scheme.Modules TauCeti TauCeti.AlgebraicGeometry
  TauCeti.AlgebraicGeometry.Scheme.Modules

universe u

noncomputable section

namespace TauCeti.AlgebraicGeometry

variable {X : Scheme.{u}}

/-- A finite biproduct of copies of `M` is isomorphic to `M ⊗ 𝒪_X^J`. -/
private def biproductConstIsoTensorFree (M : X.Modules) (J : Type u) [Finite J]
    [HasBiproduct fun _ : J ↦ M] :
    (⨁ fun _ : J ↦ M) ≅ M ⊗ SheafOfModules.free J := by
  letI : Fintype J := Fintype.ofFinite J
  have : HasBiproduct (C := X.Modules) fun _ : J ↦ 𝟙_ X.Modules :=
    HasBiproduct.of_hasCoproduct _
  exact biproduct.isoCoproduct (fun _ : J ↦ M) ≪≫
    Sigma.mapIso (fun _ ↦ (ρ_ M).symm) ≪≫
    (PreservesCoproduct.iso (tensorLeft M) (fun _ : J ↦ 𝟙_ X.Modules)).symm ≪≫
    whiskerLeftIso M ((biproduct.isoCoproduct (fun _ : J ↦ 𝟙_ X.Modules)).symm ≪≫
      TauCeti.SheafOfModules.biproductIsoFree (R := X.sheaf) J)

/-- A finite direct sum of copies of a finitely presented `𝒪_X`-module is finitely presented. -/
private theorem isFinitePresentation_biproduct_const (M : X.Modules) [M.IsFinitePresentation]
    (J : Type u) [Finite J] [HasBiproduct fun _ : J ↦ M] :
    (⨁ fun _ : J ↦ M).IsFinitePresentation := by
  have : (SheafOfModules.free (R := X.ringCatSheaf) J).IsFinitePresentation := inferInstance
  exact (SheafOfModules.isFinitePresentation X.ringCatSheaf).prop_of_iso
    (biproductConstIsoTensorFree M J).symm
    (isFinitePresentation_tensorObj X M (SheafOfModules.free J))

/-- The kernel of an epimorphism yields a short exact sequence in `X.Modules`. -/
private theorem shortExact_kernel_of_epi {E F : X.Modules} (π : E ⟶ F) [Epi π] :
    (ShortComplex.mk (kernel.ι π) π (kernel.condition π)).ShortExact :=
  ShortComplex.ShortExact.mk' (ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel π))
    inferInstance inferInstance

/-- Transfer `Subsingleton` of cohomology along an isomorphism of `𝒪_X`-modules. -/
private theorem subsingleton_cohomology_of_iso {M N : X.Modules} (e : M ≅ N) (q : ℕ)
    (h : Subsingleton (Cohomology M q)) : Subsingleton (Cohomology N q) := by
  have : Subsingleton ((cohomologyFunctor X q).obj M) := h
  exact ((cohomologyFunctor X q).mapIso e).addCommGroupIsoToAddEquiv.symm.injective.subsingleton

end TauCeti.AlgebraicGeometry

namespace AlgebraicGeometry.Proj

variable {A : Type u} {σ : Type*} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  {𝒜 : ℕ → σ} [GradedRing 𝒜]

/-- **Resolutions by negative twists on `Proj`.** On a quasi-compact quasi-separated `Proj A`
covered by degree-one standard opens, every quasi-coherent `𝒪`-module `F` of finite type admits
an epimorphism from a finite direct sum of copies of `𝒪(-m)` for all sufficiently large `m`. -/
theorem exists_epi_biproduct_twistingSheaf {ι : Type u} (f : ι → A) (hf : ∀ i, f i ∈ 𝒜 1)
    (hcover : ⨆ i, basicOpen 𝒜 (f i) = ⊤) [CompactSpace (Proj 𝒜)] [QuasiSeparatedSpace (Proj 𝒜)]
    (F : (Proj 𝒜).Modules) [F.IsQuasicoherent] [F.IsFiniteType] :
    ∃ m₀ : ℕ, ∀ m ≥ m₀,
      ∃ (J : Type u) (_ : Finite J)
        (_ : HasBiproduct fun _ : J ↦ twistingSheaf 𝒜 (-(m : ℤ)))
        (π : (⨁ fun _ : J ↦ twistingSheaf 𝒜 (-(m : ℤ))) ⟶ F), Epi π := by
  have hinv (n : ℤ) : SheafOfModules.isInvertible (Proj 𝒜) (twistingSheaf 𝒜 n) :=
    isInvertible_twistingSheaf_of_iSup_eq_top f hf hcover n
  let O1 : InvertibleSheaf (Proj 𝒜) := ⟨twistingSheaf 𝒜 1, hinv 1⟩
  have hamp : (LineBundleClass.mk O1).IsAmple := isAmple_twistingSheaf f hf hcover Nat.one_pos
  obtain ⟨m₀, hm₀⟩ := exists_epi_free_tensorPow_of_isAmple O1 hamp F
  refine ⟨m₀, fun m hm ↦ ?_⟩
  obtain ⟨J, hJ, π, hπ⟩ := hm₀ m hm
  cases nonempty_fintype J
  have hbip : HasBiproduct (C := (Proj 𝒜).Modules) fun _ : J ↦ twistingSheaf 𝒜 (-(m : ℤ)) :=
    HasBiproduct.of_hasCoproduct _
  -- Identify `𝒪(1)^{⊗m}` with `𝒪(m)` and `𝒪(m) ⊗ 𝒪(-m)` with `𝒪`.
  let Om : InvertibleSheaf (Proj 𝒜) := ⟨twistingSheaf 𝒜 (m : ℤ), hinv m⟩
  let Onm : InvertibleSheaf (Proj 𝒜) := ⟨twistingSheaf 𝒜 (-(m : ℤ)), hinv (-m)⟩
  have hmk1 : LineBundleClass.mk ⟨tensorPow O1.obj m, inferInstance⟩ =
      LineBundleClass.mk Om := by
    rw [LineBundleClass.mk_tensorPow_obj, lineBundleClass_twistingSheaf_eq_zpow f hf hcover m,
      zpow_natCast]
  obtain ⟨e1⟩ := LineBundleClass.mk_eq_mk_iff.mp hmk1
  have hmk2 : LineBundleClass.mk (InvertibleSheaf.tensorProduct Om Onm) =
      LineBundleClass.mk (InvertibleSheaf.trivial (Proj 𝒜)) := by
    rw [LineBundleClass.mk_tensorProduct, lineBundleClass_twistingSheaf_eq_zpow f hf hcover m,
      lineBundleClass_twistingSheaf_eq_zpow f hf hcover (-m), zpow_neg, mul_inv_cancel,
      LineBundleClass.mk_trivial]
  obtain ⟨e2'⟩ := LineBundleClass.mk_eq_mk_iff.mp hmk2
  let e2 : twistingSheaf 𝒜 (m : ℤ) ⊗ twistingSheaf 𝒜 (-(m : ℤ)) ≅ 𝟙_ (Proj 𝒜).Modules :=
    (InvertibleSheaf.tensorProductObjIso Om Onm).symm ≪≫ e2' ≪≫
      InvertibleSheaf.trivialObjIsoUnit (Proj 𝒜)
  have : Epi (π ≫ (F ◁ e1.hom)) := epi_comp π (F ◁ e1.hom)
  obtain ⟨π', hπ'⟩ := exists_epi_biproduct_of_epi_free_tensor (π ≫ (F ◁ e1.hom)) e2
  exact ⟨J, hJ, hbip, π', hπ'⟩

end AlgebraicGeometry.Proj

namespace TauCeti.SymmetricAlgebra

variable {R M : Type u} [CommRing R] [AddCommMonoid M] [Module R M]

local notation "𝒜" => homogeneousSubmodule R M

/-- On `Proj (Sym_R M)` for a finite `R`-module `M`, every quasi-coherent sheaf of finite type
admits a surjection from a finite direct sum of copies of `𝒪(-m)` for all sufficiently large `m`. -/
theorem exists_epi_biproduct_twistingSheaf [Module.Finite R M]
    (F : (Proj 𝒜).Modules) [F.IsQuasicoherent] [F.IsFiniteType] :
    ∃ m₀ : ℕ, ∀ m ≥ m₀,
      ∃ (J : Type u) (_ : Finite J)
        (_ : HasBiproduct fun _ : J ↦ Proj.twistingSheaf 𝒜 (-(m : ℤ)))
        (π : (⨁ fun _ : J ↦ Proj.twistingSheaf 𝒜 (-(m : ℤ))) ⟶ F), Epi π := by
  have : CompactSpace (Proj 𝒜) := QuasiCompact.compactSpace_of_compactSpace (projToSpec R M)
  have : QuasiSeparatedSpace (Proj 𝒜) := quasiSeparatedSpace_of_quasiSeparated (projToSpec R M)
  exact Proj.exists_epi_biproduct_twistingSheaf (_root_.SymmetricAlgebra.ι R M)
    (ι_mem_homogeneousSubmodule R M) (iSup_basicOpen_ι_eq_top R M id (by simp)) F

/-- Helper: every twisting sheaf on `Proj (Sym_R M)` is locally free and finitely presented. -/
private theorem twistingSheaf_properties (m : ℤ) :
    (Proj.twistingSheaf 𝒜 m).IsLocallyFree ∧ (Proj.twistingSheaf 𝒜 m).IsFinitePresentation :=
  ((InvertibleSheaf.toFiniteLocallyFree (Proj 𝒜)).obj
    ⟨Proj.twistingSheaf 𝒜 m, inferInstance⟩).property

/-- Helper: `𝒪(m) ⊗ 𝒪(n) ≅ 𝒪(m + n)` in the monoidal category `(Proj (Sym_R M)).Modules`. -/
private theorem exists_twistingSheaf_tensor_iso (m n : ℤ) :
    Nonempty (Proj.twistingSheaf 𝒜 m ⊗ Proj.twistingSheaf 𝒜 n ≅ Proj.twistingSheaf 𝒜 (m + n)) := by
  let Om : InvertibleSheaf (Proj 𝒜) := ⟨Proj.twistingSheaf 𝒜 m, inferInstance⟩
  let On : InvertibleSheaf (Proj 𝒜) := ⟨Proj.twistingSheaf 𝒜 n, inferInstance⟩
  have hmk : LineBundleClass.mk (InvertibleSheaf.tensorProduct Om On) =
      LineBundleClass.mk ⟨Proj.twistingSheaf 𝒜 (m + n), inferInstance⟩ := by
    rw [LineBundleClass.mk_tensorProduct,
      Proj.lineBundleClass_twistingSheaf_eq_zpow (_root_.SymmetricAlgebra.ι R M)
        (ι_mem_homogeneousSubmodule R M) (iSup_basicOpen_ι_eq_top R M id (by simp)) m,
      Proj.lineBundleClass_twistingSheaf_eq_zpow (_root_.SymmetricAlgebra.ι R M)
        (ι_mem_homogeneousSubmodule R M) (iSup_basicOpen_ι_eq_top R M id (by simp)) n,
      Proj.lineBundleClass_twistingSheaf_eq_zpow (_root_.SymmetricAlgebra.ι R M)
        (ι_mem_homogeneousSubmodule R M) (iSup_basicOpen_ι_eq_top R M id (by simp)) (m + n),
      zpow_add]
  obtain ⟨e⟩ := LineBundleClass.mk_eq_mk_iff.mp hmk
  exact ⟨(InvertibleSheaf.tensorProductObjIso Om On).symm ≪≫ e⟩

/-- Helper: on `Proj (Sym_R M)` over a Noetherian ring `R`, any finite-type quasi-coherent sheaf
`F` admits a surjection `π : ⨁_J 𝒪(-r) ⟶ F` whose kernel is again quasi-coherent of finite
type. -/
private theorem exists_epi_biproduct_twistingSheaf_kernel [IsNoetherianRing R] [Module.Finite R M]
    (F : (Proj 𝒜).Modules) [F.IsQuasicoherent] [F.IsFiniteType] :
    ∃ (r : ℕ) (J : Type u) (_ : Finite J)
      (_ : HasBiproduct fun _ : J ↦ Proj.twistingSheaf 𝒜 (-(r : ℤ)))
      (π : (⨁ fun _ : J ↦ Proj.twistingSheaf 𝒜 (-(r : ℤ))) ⟶ F) (_ : Epi π),
      (kernel π).IsQuasicoherent ∧ (kernel π).IsFiniteType := by
  have : IsLocallyNoetherian (Proj 𝒜) := LocallyOfFiniteType.isLocallyNoetherian (projToSpec R M)
  obtain ⟨r, hr⟩ := exists_epi_biproduct_twistingSheaf F
  obtain ⟨J, hJ, hbip, π, hπ⟩ := hr r le_rfl
  cases nonempty_fintype J
  have : (Proj.twistingSheaf 𝒜 (-(r : ℤ))).IsFinitePresentation := (twistingSheaf_properties (-r)).2
  have : (⨁ fun _ : J ↦ Proj.twistingSheaf 𝒜 (-(r : ℤ))).IsFinitePresentation :=
    isFinitePresentation_biproduct_const _ J
  have : (kernel π).IsFinitePresentation := isFinitePresentation_kernel π
  exact ⟨r, J, hJ, hbip, π, hπ, isQuasicoherent_of_isFinitePresentation _,
    isFiniteType_of_isFinitePresentation _⟩

/-! ### Serre's theorem on projective space with a basis -/

section Basis

variable [IsNoetherianRing R] {κ : Type*} [Finite κ]

/-- Downward induction step for Serre's finiteness theorem on `ℙⁿ_R` (`n ≥ 1`). -/
private theorem serre_finite_step [Nontrivial κ] (b : Module.Basis κ R M) (q : ℕ)
    (ih : ∀ (G : (Proj 𝒜).Modules) [G.IsQuasicoherent] [G.IsFiniteType],
      Module.Finite R (Cohomology G (q + 1)))
    (F : (Proj 𝒜).Modules) [F.IsQuasicoherent] [F.IsFiniteType] :
    Module.Finite R (Cohomology F q) := by
  cases nonempty_fintype κ
  have : Module.Finite R M := Module.Finite.of_basis b
  obtain ⟨r, J, hJ, hbip, π, hπ, hKq, hKf⟩ := exists_epi_biproduct_twistingSheaf_kernel F
  cases nonempty_fintype J
  have hS := shortExact_kernel_of_epi π
  have hE : Module.Finite R (Cohomology (⨁ fun _ : J ↦ Proj.twistingSheaf 𝒜 (-(r : ℤ))) q) := by
    have : Module.Finite R (Cohomology (Proj.twistingSheaf 𝒜 (-(r : ℤ))) q) :=
      b.finite_cohomology_twistingSheaf (-r) q
    exact Module.Finite.equiv (cohomologyBiproductLinearEquiv R _ q).symm
  have hK : Module.Finite R (Cohomology (kernel π) (q + 1)) := ih (kernel π)
  exact finite_of_exact (exact_cohomologyMapBaseLinear_cohomologyδBaseLinear R (Proj 𝒜) hS q)

/-- Downward induction step for Serre's vanishing theorem on `ℙⁿ_R`. -/
private theorem serre_vanishing_step (b : Module.Basis κ R M) (q : ℕ) (hq : 0 < q)
    (ih : ∀ (G : (Proj 𝒜).Modules) [G.IsQuasicoherent] [G.IsFiniteType],
      ∃ m₀ : ℤ, ∀ m ≥ m₀, Subsingleton (Cohomology (G ⊗ Proj.twistingSheaf 𝒜 m) (q + 1)))
    (F : (Proj 𝒜).Modules) [F.IsQuasicoherent] [F.IsFiniteType] :
    ∃ m₀ : ℤ, ∀ m ≥ m₀, Subsingleton (Cohomology (F ⊗ Proj.twistingSheaf 𝒜 m) q) := by
  cases nonempty_fintype κ
  have : Module.Finite R M := Module.Finite.of_basis b
  obtain ⟨r, J, hJ, hbip, π, hπ, hKq, hKf⟩ := exists_epi_biproduct_twistingSheaf_kernel F
  cases nonempty_fintype J
  have hS := shortExact_kernel_of_epi π
  obtain ⟨m₁, hm₁⟩ := ih (kernel π)
  refine ⟨max m₁ ((r : ℤ) + 1 - Fintype.card κ), fun m hm ↦ ?_⟩
  have hm1 : m₁ ≤ m := le_trans (le_max_left _ _) hm
  have hmr : -(Fintype.card κ : ℤ) < m + -(r : ℤ) := by
    have := le_trans (le_max_right _ _) hm
    omega
  have hOm := twistingSheaf_properties (R := R) (M := M) m
  have : (Proj.twistingSheaf 𝒜 m).IsLocallyFree := hOm.1
  have : (Proj.twistingSheaf 𝒜 m).IsFinitePresentation := hOm.2
  have : (Proj.twistingSheaf 𝒜 m).IsFiniteType := isFiniteType_of_isFinitePresentation _
  have hSm := shortExact_map_tensorLeft (Proj.twistingSheaf 𝒜 m) hS
  have hK : Subsingleton (Cohomology (Proj.twistingSheaf 𝒜 m ⊗ kernel π) (q + 1)) :=
    subsingleton_cohomology_of_iso (β_ (kernel π) (Proj.twistingSheaf 𝒜 m)) (q + 1) (hm₁ m hm1)
  have hE : Subsingleton (Cohomology
      (Proj.twistingSheaf 𝒜 m ⊗ ⨁ fun _ : J ↦ Proj.twistingSheaf 𝒜 (-(r : ℤ))) q) := by
    have : HasBiproduct (C := (Proj 𝒜).Modules) fun _ : J ↦
        Proj.twistingSheaf 𝒜 m ⊗ Proj.twistingSheaf 𝒜 (-(r : ℤ)) :=
      HasBiproduct.of_hasCoproduct _
    have : HasBiproduct (C := (Proj 𝒜).Modules) fun _ : J ↦
        Proj.twistingSheaf 𝒜 (m + -(r : ℤ)) :=
      HasBiproduct.of_hasCoproduct _
    obtain ⟨eTwist⟩ := exists_twistingSheaf_tensor_iso (R := R) (M := M) m (-r)
    have : PreservesBiproduct (fun _ : J ↦ Proj.twistingSheaf 𝒜 (-(r : ℤ)))
        (tensorLeft (Proj.twistingSheaf 𝒜 m)) :=
      preservesBiproduct_of_preservesCoproduct _
    let eE := (tensorLeft (Proj.twistingSheaf 𝒜 m)).mapBiproduct
        (fun _ : J ↦ Proj.twistingSheaf 𝒜 (-(r : ℤ))) ≪≫
      biproduct.mapIso fun _ ↦ eTwist
    have hsub : Subsingleton (Cohomology (Proj.twistingSheaf 𝒜 (m + -(r : ℤ))) q) :=
      b.subsingleton_cohomology_twistingSheaf_of_neg_card_lt hmr hq
    have hsum : Subsingleton (Cohomology (⨁ fun _ : J ↦ Proj.twistingSheaf 𝒜 (m + -(r : ℤ))) q) :=
      (cohomologyBiproductLinearEquiv R _ q).injective.subsingleton
    exact subsingleton_cohomology_of_iso eE.symm q hsum
  have hF : Subsingleton (Cohomology (Proj.twistingSheaf 𝒜 m ⊗ F) q) :=
    subsingleton_cohomology_X₃ hSm q (q + 1) rfl hE hK
  exact subsingleton_cohomology_of_iso (β_ (Proj.twistingSheaf 𝒜 m) F) q hF

/-- Serre's finiteness theorem on `Proj (Sym_R M)` for a finite basis of size at least two. -/
private theorem finite_cohomology_of_basis [Nontrivial κ] (b : Module.Basis κ R M) (q : ℕ)
    (F : (Proj 𝒜).Modules) [F.IsQuasicoherent] [F.IsFiniteType] :
    Module.Finite R (Cohomology F q) := by
  cases nonempty_fintype κ
  suffices H : ∀ d : ℕ, ∀ (G : (Proj 𝒜).Modules) [G.IsQuasicoherent] [G.IsFiniteType],
      Module.Finite R (Cohomology G (Fintype.card κ - d)) by
    by_cases hq : Fintype.card κ ≤ q
    · have := b.subsingleton_cohomology_proj_of_card_le F q hq
      infer_instance
    · have := H (Fintype.card κ - q) F
      rwa [Nat.sub_sub_self (le_of_not_ge hq)] at this
  intro d
  induction d with
  | zero =>
    intro G _ _
    have := b.subsingleton_cohomology_proj_of_card_le G (Fintype.card κ) le_rfl
    infer_instance
  | succ d ih =>
    intro G _ _
    by_cases hd : Fintype.card κ ≤ d
    · have h0 : Fintype.card κ - (d + 1) = Fintype.card κ - d := by omega
      rw [h0]
      exact ih G
    · have hstep : Fintype.card κ - (d + 1) + 1 = Fintype.card κ - d := by omega
      exact serre_finite_step b (Fintype.card κ - (d + 1)) (fun G' _ _ ↦ by
        rw [hstep]; exact ih G') G

/-- Serre's vanishing theorem on `Proj (Sym_R M)` for a nonempty finite basis, in a single positive
degree `q`. -/
private theorem exists_subsingleton_cohomology_tensor_of_basis_deg [Nonempty κ]
    (b : Module.Basis κ R M) (q : ℕ) (hq : 0 < q)
    (F : (Proj 𝒜).Modules) [F.IsQuasicoherent] [F.IsFiniteType] :
    ∃ m₀ : ℤ, ∀ m ≥ m₀, Subsingleton (Cohomology (F ⊗ Proj.twistingSheaf 𝒜 m) q) := by
  cases nonempty_fintype κ
  have : Module.Finite R M := Module.Finite.of_basis b
  suffices H : ∀ d : ℕ, 0 < Fintype.card κ - d →
      ∀ (G : (Proj 𝒜).Modules) [G.IsQuasicoherent] [G.IsFiniteType],
        ∃ m₀ : ℤ, ∀ m ≥ m₀,
          Subsingleton (Cohomology (G ⊗ Proj.twistingSheaf 𝒜 m) (Fintype.card κ - d)) by
    by_cases hq' : Fintype.card κ ≤ q
    · refine ⟨0, fun m _ ↦ ?_⟩
      have : (Proj.twistingSheaf 𝒜 m).IsFinitePresentation := (twistingSheaf_properties m).2
      have : (Proj.twistingSheaf 𝒜 m).IsQuasicoherent := isQuasicoherent_of_isFinitePresentation _
      exact b.subsingleton_cohomology_proj_of_card_le (F ⊗ Proj.twistingSheaf 𝒜 m) q hq'
    · have hsub : Fintype.card κ - (Fintype.card κ - q) = q :=
        Nat.sub_sub_self (le_of_not_ge hq')
      simpa only [hsub] using H (Fintype.card κ - q) (by omega) F
  intro d
  induction d with
  | zero =>
    intro _ G _ _
    refine ⟨0, fun m _ ↦ ?_⟩
    have : (Proj.twistingSheaf 𝒜 m).IsFinitePresentation := (twistingSheaf_properties m).2
    have : (Proj.twistingSheaf 𝒜 m).IsQuasicoherent := isQuasicoherent_of_isFinitePresentation _
    exact b.subsingleton_cohomology_proj_of_card_le (G ⊗ Proj.twistingSheaf 𝒜 m)
      (Fintype.card κ) le_rfl
  | succ d ih =>
    intro hpos G _ _
    have hstep : Fintype.card κ - (d + 1) + 1 = Fintype.card κ - d := by omega
    exact serre_vanishing_step b (Fintype.card κ - (d + 1)) hpos
      (fun G' _ _ ↦ by rw [hstep]; exact ih (by omega) G') G

/-- Uniform Serre vanishing across all positive degrees for a nonempty finite basis. -/
private theorem exists_subsingleton_cohomology_tensor_of_basis [Nonempty κ]
    (b : Module.Basis κ R M) (F : (Proj 𝒜).Modules) [F.IsQuasicoherent] [F.IsFiniteType] :
    ∃ m₀ : ℤ, ∀ m ≥ m₀, ∀ q > 0, Subsingleton (Cohomology (F ⊗ Proj.twistingSheaf 𝒜 m) q) := by
  cases nonempty_fintype κ
  have : Module.Finite R M := Module.Finite.of_basis b
  have hdeg (i : Fin (Fintype.card κ)) :
      ∃ m₀ : ℤ, ∀ m ≥ m₀,
        Subsingleton (Cohomology (F ⊗ Proj.twistingSheaf 𝒜 m) (i.1 + 1)) :=
    exists_subsingleton_cohomology_tensor_of_basis_deg b (i.1 + 1) (Nat.succ_pos i.1) F
  choose m₀ hm₀ using hdeg
  refine ⟨Finset.univ.sup' Finset.univ_nonempty m₀, fun m hm q hq ↦ ?_⟩
  by_cases hq' : Fintype.card κ ≤ q
  · have : (Proj.twistingSheaf 𝒜 m).IsFinitePresentation := (twistingSheaf_properties m).2
    have : (Proj.twistingSheaf 𝒜 m).IsQuasicoherent := isQuasicoherent_of_isFinitePresentation _
    exact b.subsingleton_cohomology_proj_of_card_le (F ⊗ Proj.twistingSheaf 𝒜 m) q hq'
  · let i : Fin (Fintype.card κ) := ⟨q - 1, by omega⟩
    have hmi : m₀ i ≤ m := (Finset.le_sup' m₀ (Finset.mem_univ i)).trans hm
    have hiq : i.1 + 1 = q := by dsimp [i]; omega
    simpa only [hiq] using hm₀ i m hmi

end Basis

/-! ### Serre's theorems for any finite module `M` -/

/-- Any finitely generated `R`-module admits a surjection from `Fin (n + 2) → R` for some `n`,
embedding `Proj (Sym_R M)` into a projective space of positive dimension. -/
private theorem exists_surjective_fin_add_two [Module.Finite R M] :
    ∃ (n : ℕ) (g : (Fin (n + 2) → R) →ₗ[R] M), Function.Surjective g := by
  obtain ⟨n, g₀, hg₀⟩ := Module.Finite.exists_fin' R M
  let proj : (Fin (n + 2) → R) →ₗ[R] (Fin n → R) :=
    { toFun := fun v i ↦ v (Fin.castAdd 2 i)
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  refine ⟨n, g₀.comp proj, hg₀.comp fun v ↦ ?_⟩
  refine ⟨fun j ↦ if h : j.1 < n then v ⟨j.1, h⟩ else 0, ?_⟩
  ext i
  simp [proj]

/-- **Serre's finiteness theorem** (Hartshorne, Theorem III.5.2(a)). Let `R` be a Noetherian ring
and `M` a finitely generated `R`-module. For every quasi-coherent sheaf `F` of finite type on
`Proj (Sym_R M)` and every `q : ℕ`, the cohomology `H^q(Proj (Sym_R M), F)` is a finitely
generated `R`-module. -/
theorem finite_cohomology_proj [IsNoetherianRing R] [Module.Finite R M]
    (F : (Proj 𝒜).Modules) [F.IsQuasicoherent] [F.IsFiniteType] (q : ℕ) :
    Module.Finite R (Cohomology F q) := by
  obtain ⟨n, g, hg⟩ := exists_surjective_fin_add_two (R := R) (M := M)
  have hsurj : Function.Surjective (_root_.SymmetricAlgebra.gradedMap R g) := fun a ↦ by
    obtain ⟨b, hb⟩ := _root_.SymmetricAlgebra.map_surjective R g hg a
    exact ⟨b, (_root_.SymmetricAlgebra.gradedMap_apply R g b).trans hb⟩
  let hirr := HomogeneousIdeal.irrelevant_le_map_of_surjective _ hsurj
  let i := Proj.map (_root_.SymmetricAlgebra.gradedMap R g) hirr
  have : IsClosedImmersion i := isClosedImmersion_projMap_of_surjective R g hg hirr
  have : i.IsOver (Spec (.of R)) := isOver_projMap R g hirr
  have : IsLocallyNoetherian (Proj (homogeneousSubmodule R (Fin (n + 2) → R))) :=
    LocallyOfFiniteType.isLocallyNoetherian (projToSpec R (Fin (n + 2) → R))
  have : ((pushforward i).obj F).IsFinitePresentation :=
    isFinitePresentation_pushforward_of_isFinite i F
  have : ((pushforward i).obj F).IsQuasicoherent := isQuasicoherent_of_isFinitePresentation _
  have : ((pushforward i).obj F).IsFiniteType := isFiniteType_of_isFinitePresentation _
  have hfin : Module.Finite R (Cohomology ((pushforward i).obj F) q) :=
    finite_cohomology_of_basis (Pi.basisFun R (Fin (n + 2))) q ((pushforward i).obj F)
  exact (i.moduleFinite_cohomology_pushforward_iff R F q).mp hfin

/-- **Serre's vanishing theorem** (Hartshorne, Theorem III.5.2(b)). Let `R` be a Noetherian ring
and `M` a finitely generated `R`-module. For every quasi-coherent sheaf `F` of finite type on
`Proj (Sym_R M)`, there exists `m₀ : ℤ` such that `H^q(Proj (Sym_R M), F ⊗ 𝒪(m)) = 0` for all
`m ≥ m₀` and all `q > 0`. -/
theorem exists_subsingleton_cohomology_tensor_twistingSheaf [IsNoetherianRing R] [Module.Finite R M]
    (F : (Proj 𝒜).Modules) [F.IsQuasicoherent] [F.IsFiniteType] :
    ∃ m₀ : ℤ, ∀ m ≥ m₀, ∀ q > 0,
      Subsingleton (Cohomology (F ⊗ Proj.twistingSheaf 𝒜 m) q) := by
  obtain ⟨n, g, hg⟩ := exists_surjective_fin_add_two (R := R) (M := M)
  have hsurj : Function.Surjective (_root_.SymmetricAlgebra.gradedMap R g) := fun a ↦ by
    obtain ⟨b, hb⟩ := _root_.SymmetricAlgebra.map_surjective R g hg a
    exact ⟨b, (_root_.SymmetricAlgebra.gradedMap_apply R g b).trans hb⟩
  let hirr := HomogeneousIdeal.irrelevant_le_map_of_surjective _ hsurj
  let i := Proj.map (_root_.SymmetricAlgebra.gradedMap R g) hirr
  have : IsClosedImmersion i := isClosedImmersion_projMap_of_surjective R g hg hirr
  have : IsLocallyNoetherian (Proj (homogeneousSubmodule R (Fin (n + 2) → R))) :=
    LocallyOfFiniteType.isLocallyNoetherian (projToSpec R (Fin (n + 2) → R))
  have : ((pushforward i).obj F).IsFinitePresentation :=
    isFinitePresentation_pushforward_of_isFinite i F
  have : ((pushforward i).obj F).IsQuasicoherent := isQuasicoherent_of_isFinitePresentation _
  have : ((pushforward i).obj F).IsFiniteType := isFiniteType_of_isFinitePresentation _
  obtain ⟨m₀, hm₀⟩ :=
    exists_subsingleton_cohomology_tensor_of_basis (Pi.basisFun R (Fin (n + 2)))
      ((pushforward i).obj F)
  refine ⟨m₀, fun m hm q hq ↦ ?_⟩
  let Om := (InvertibleSheaf.toFiniteLocallyFree _).obj
    ⟨Proj.twistingSheaf (homogeneousSubmodule R (Fin (n + 2) → R)) m, inferInstance⟩
  let epb : ((FiniteLocallyFreeSheaf.pullback i).obj Om).obj ≅ Proj.twistingSheaf 𝒜 m :=
    eqToIso (FiniteLocallyFreeSheaf.pullback_obj_obj i Om) ≪≫
      asIso (Proj.pullbackTwistingSheafMap (_root_.SymmetricAlgebra.gradedMap R g) hirr m)
  let e : (pushforward i).obj F ⊗ Om.obj ≅
      (pushforward i).obj (F ⊗ Proj.twistingSheaf 𝒜 m) :=
    β_ ((pushforward i).obj F) Om.obj ≪≫
      (FiniteLocallyFreeSheaf.pushforwardTensorLeftIso i Om).app F ≪≫
      (pushforward i).mapIso (whiskerRightIso epb F ≪≫ β_ (Proj.twistingSheaf 𝒜 m) F)
  have hpush : Subsingleton (Cohomology ((pushforward i).obj (F ⊗ Proj.twistingSheaf 𝒜 m)) q) :=
    subsingleton_cohomology_of_iso e q (hm₀ m hm q hq)
  exact (cohomologyPushforwardIso i (F ⊗ Proj.twistingSheaf 𝒜 m) q).addCommGroupIsoToAddEquiv
    |>.symm.injective.subsingleton

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
  have : IsLocallyNoetherian (Proj 𝒜) :=
    LocallyOfFiniteType.isLocallyNoetherian (TauCeti.SymmetricAlgebra.projToSpec R M)
  have : ((pushforward i).obj F).IsFinitePresentation :=
    isFinitePresentation_pushforward_of_isFinite i F
  have : ((pushforward i).obj F).IsQuasicoherent := isQuasicoherent_of_isFinitePresentation _
  have : ((pushforward i).obj F).IsFiniteType := isFiniteType_of_isFinitePresentation _
  obtain ⟨m₀, hm₀⟩ :=
    TauCeti.SymmetricAlgebra.exists_subsingleton_cohomology_tensor_twistingSheaf
      ((pushforward i).obj F)
  refine ⟨m₀, fun m hm q hq ↦ ?_⟩
  let Om := (InvertibleSheaf.toFiniteLocallyFree (Proj 𝒜)).obj
    ⟨Proj.twistingSheaf 𝒜 m, inferInstance⟩
  let epb : ((FiniteLocallyFreeSheaf.pullback i).obj Om).obj ≅
      (Scheme.Modules.pullback i).obj (Proj.twistingSheaf 𝒜 m) :=
    eqToIso (FiniteLocallyFreeSheaf.pullback_obj_obj i Om)
  let e : (pushforward i).obj F ⊗ Om.obj ≅
      (pushforward i).obj (F ⊗ (Scheme.Modules.pullback i).obj (Proj.twistingSheaf 𝒜 m)) :=
    β_ ((pushforward i).obj F) Om.obj ≪≫
      (FiniteLocallyFreeSheaf.pushforwardTensorLeftIso i Om).app F ≪≫
      (pushforward i).mapIso
        (whiskerRightIso epb F ≪≫ β_ ((Scheme.Modules.pullback i).obj (Proj.twistingSheaf 𝒜 m)) F)
  have hpush : Subsingleton (Cohomology
      ((pushforward i).obj (F ⊗ (Scheme.Modules.pullback i).obj (Proj.twistingSheaf 𝒜 m))) q) :=
    subsingleton_cohomology_of_iso e q (hm₀ m hm q hq)
  exact (cohomologyPushforwardIso i _ q).addCommGroupIsoToAddEquiv.symm.injective.subsingleton

end AlgebraicGeometry.Scheme.Hom

end
