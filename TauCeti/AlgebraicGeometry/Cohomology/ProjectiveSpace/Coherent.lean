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
import Mathlib.Algebra.Exact.Basic
import Mathlib.CategoryTheory.ObjectProperty.FiniteProducts
import Mathlib.RingTheory.Finiteness.Cardinality
import Mathlib.RingTheory.Noetherian.Basic
import TauCeti.Algebra.Category.ModuleCat.Sheaf.Invertible.FinitePresentation
import TauCeti.AlgebraicGeometry.Cohomology.Biproduct
import TauCeti.AlgebraicGeometry.Cohomology.ClosedImmersion.Linear
import TauCeti.AlgebraicGeometry.Cohomology.LongExactSequence
import TauCeti.AlgebraicGeometry.Cohomology.ProjectiveSpace.HigherCohomology
import TauCeti.AlgebraicGeometry.Cohomology.ProjectiveSpace.Vanishing
import TauCeti.AlgebraicGeometry.Modules.Biprod
import TauCeti.AlgebraicGeometry.Modules.FinitePresentation.Abelian
import TauCeti.AlgebraicGeometry.Modules.Quasicoherent.Pushforward.Finite
import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.BaseChange
import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.ClosedImmersion
import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.TwistingSheaf.Ample
import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.TwistingSheaf.Pullback
import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.TwistingSheaf.TensorProduct
import TauCeti.AlgebraicGeometry.VectorBundle.Dual.Basic
import TauCeti.AlgebraicGeometry.VectorBundle.ProjectionFormula

/-!
# Serre's theorems for coherent sheaves on projective schemes

Let `R` be a Noetherian commutative ring. This file proves Serre's finiteness and vanishing
theorems for coherent (quasi-coherent of finite type) sheaves of modules on `Proj (Sym_R M)` for
any finite `R`-module `M`, and on any projective scheme over `Spec R`
(`AlgebraicGeometry.Scheme.IsProjectiveOver`).

For a free module `M` with a finite basis of at least two elements, the proofs proceed by descending
induction on the cohomological degree `q` from the ambient vanishing bound `card κ ≤ q`
(`Module.Basis.subsingleton_cohomology_proj_of_card_le`). Every quasi-coherent sheaf `F` of finite
type is covered by a finite direct sum `E = ⨁_{Fin k} 𝒪(-n₀)`
(`TauCeti.SymmetricAlgebra.exists_epi_biproduct_twistingSheaf`). Because `Proj (Sym_R M)` is
Noetherian, the kernel `K` of `E ↠ F` is again finitely presented, hence quasi-coherent and of
finite type (`AlgebraicGeometry.Scheme.Modules.isFinitePresentation_kernel`).

* **Finiteness:** in the exact sequence `Hᵠ(E) → Hᵠ(F) → H^{q+1}(K)` from the cohomology long exact
  sequence, `Hᵠ(E)` is finite over `R` by `Module.Basis.finite_cohomology_twistingSheaf` and
  `H^{q+1}(K)` is finite by the induction hypothesis; over a Noetherian ring the middle term `Hᵠ(F)`
  is therefore finite (`isNoetherian_of_range_eq_ker`).
* **Vanishing:** twisting `0 → K → E → F → 0` by `𝒪(m)` preserves exactness
  (`AlgebraicGeometry.Scheme.Modules.shortExact_map_tensorLeft`), and for `m` sufficiently large
  both `Hᵠ(𝒪(m) ⊗ E)` (`Module.Basis.subsingleton_cohomology_twistingSheaf_of_neg_card_lt`) and
  `H^{q+1}(𝒪(m) ⊗ K)` (induction hypothesis) vanish, forcing `Hᵠ(𝒪(m) ⊗ F) = 0`. Taking the
  maximum over the finitely many degrees `0 < q < card κ` yields a uniform bound `m₀ : ℤ`.

An arbitrary finite `R`-module `M` is a quotient of a free module `R^{r+2}` of rank at least two,
producing a closed immersion `Proj (Sym_R M) ↪ Proj (Sym_R R^{r+2})` over `Spec R` along which
`𝒪(m)` pulls back to `𝒪(m)` (`TauCeti.SymmetricAlgebra.isIso_pullbackTwistingSheafMap`). Pushing
forward along a closed immersion preserves coherence and cohomology
(`AlgebraicGeometry.Scheme.Hom.moduleFinite_cohomology_pushforward_iff`), and the projection formula
(`TauCeti.AlgebraicGeometry.FiniteLocallyFreeSheaf.pushforwardTensorLeftIso`) transfers twisting by
`𝒪(m)`. This extends both finiteness and vanishing first to `Proj (Sym_R M)` for any finite `M`
(no freeness or rank hypothesis), and then to every closed subscheme of `Proj (Sym_R M)`. For the
vanishing theorem on a closed immersion `j : X ⟶ Proj (Sym_R M)`, no base-scheme structure on `X`
is required. Over a field `k`, `Module.Finite k` is `FiniteDimensional k`, so finiteness directly
yields finite-dimensionality of `Hᵠ(X, F)`.

## Main results

* `TauCeti.SymmetricAlgebra.finite_cohomology`: over a Noetherian ring `R`, `Hᵠ(Proj (Sym_R M), F)`
  is a finite `R`-module for every finite `R`-module `M`, every quasi-coherent `F` of finite type,
  and every `q : ℕ`.
* `TauCeti.SymmetricAlgebra.exists_subsingleton_cohomology_tensor_twistingSheaf`: Serre's vanishing
  theorem on `Proj (Sym_R M)` for a finite `R`-module `M`.
* `AlgebraicGeometry.Scheme.IsProjectiveOver.finite_cohomology`: for a scheme `X` projective over a
  Noetherian ring `R`, `Hᵠ(X, F)` is a finite `R`-module for every quasi-coherent `F` of finite
  type and every `q : ℕ`.
* `AlgebraicGeometry.Scheme.Hom.exists_subsingleton_cohomology_tensor_pullback_twistingSheaf`:
  Serre's vanishing theorem for a closed subscheme `j : X ⟶ Proj (Sym_R M)`.

## References

* R. Hartshorne, *Algebraic Geometry*, GTM 52, Springer, 1977, Theorem III.5.2.
* [Stacks, Lemma 30.14.1 (01XT)](https://stacks.math.columbia.edu/tag/01XT) and
  [Lemma 30.19.2 (02O6)](https://stacks.math.columbia.edu/tag/02O6).
-/

public section

open CategoryTheory Limits MonoidalCategory AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme.Modules

universe u

noncomputable section

namespace TauCeti.SymmetricAlgebra

section Helpers

/-- Tensoring a finite direct sum of twisting sheaves `⨁_{Fin k} 𝒪(n)` on the left by `𝒪(m)`
yields `⨁_{Fin k} 𝒪(m + n)`. -/
private def tensorLeftBiproductTwistingSheafIso (R M : Type u) [CommRing R] [AddCommMonoid M]
    [Module R M] (m n : ℤ) (k : ℕ)
    [HasBiproduct fun _ : Fin k ↦ Proj.twistingSheaf (homogeneousSubmodule R M) n]
    [HasBiproduct fun _ : Fin k ↦ Proj.twistingSheaf (homogeneousSubmodule R M) (m + n)] :
    Proj.twistingSheaf (homogeneousSubmodule R M) m ⊗
        (⨁ fun _ : Fin k ↦ Proj.twistingSheaf (homogeneousSubmodule R M) n) ≅
      ⨁ fun _ : Fin k ↦ Proj.twistingSheaf (homogeneousSubmodule R M) (m + n) := by
  let L := Proj.twistingSheaf (homogeneousSubmodule R M) m
  let c : IsColimit ((tensorLeft L).mapCocone
      (biproduct.bicone fun _ : Fin k ↦
        Proj.twistingSheaf (homogeneousSubmodule R M) n).toCocone) :=
    isColimitOfPreserves (tensorLeft L) (biproduct.isColimit _)
  exact IsColimit.coconePointsIsoOfNatIso c
    (biproduct.isColimit fun _ : Fin k ↦
      Proj.twistingSheaf (homogeneousSubmodule R M) (m + n))
    (Discrete.natIso fun _ ↦ twistingSheafTensorObjIso R M m n)

/-- Every quasi-coherent sheaf `F` of finite type on `Proj (Sym_R M)` (over a Noetherian ring `R`
and finite `R`-module `M`) sits in a short exact sequence `0 → K → E → F → 0` where `E` is a finite
direct sum of copies of a negative twist `𝒪(-n₀)` and `K = kernel π` is again quasi-coherent of
finite type. -/
private theorem exists_epi_biproduct_twistingSheaf_kernel (R M : Type u) [CommRing R]
    [IsNoetherianRing R] [AddCommMonoid M] [Module R M] [Module.Finite R M]
    (F : (Proj (homogeneousSubmodule R M)).Modules) [F.IsQuasicoherent] [F.IsFiniteType] :
    ∃ (n₀ k : ℕ)
      (_ : HasBiproduct fun _ : Fin k ↦
        Proj.twistingSheaf (homogeneousSubmodule R M) (-(n₀ : ℤ)))
      (π : (⨁ fun _ : Fin k ↦ Proj.twistingSheaf (homogeneousSubmodule R M) (-(n₀ : ℤ))) ⟶ F),
      Epi π ∧ (kernel π).IsQuasicoherent ∧ (kernel π).IsFiniteType := by
  obtain ⟨n₀, hn₀⟩ := exists_epi_biproduct_twistingSheaf R M F
  obtain ⟨k, hbp, π, hπ⟩ := hn₀ n₀ le_rfl
  let F_fam : Fin k → (Proj (homogeneousSubmodule R M)).Modules :=
    fun _ ↦ Proj.twistingSheaf (homogeneousSubmodule R M) (-(n₀ : ℤ))
  let E : (Proj (homogeneousSubmodule R M)).Modules := ⨁ F_fam
  have htw : (Proj.twistingSheaf (homogeneousSubmodule R M) (-(n₀ : ℤ))).IsFinitePresentation :=
    ((InvertibleSheaf.toFiniteLocallyFree _).obj
      ⟨Proj.twistingSheaf (homogeneousSubmodule R M) (-(n₀ : ℤ)), inferInstance⟩).property.2
  have : E.IsFinitePresentation :=
    (SheafOfModules.isFinitePresentation
      (Proj (homogeneousSubmodule R M)).ringCatSheaf).prop_of_isLimit (biproduct.isLimit F_fam)
      fun ⟨_⟩ ↦ htw
  have : E.IsQuasicoherent := isQuasicoherent_of_isFinitePresentation E
  have : E.IsFiniteType := isFiniteType_of_isFinitePresentation E
  have : (kernel π).IsFinitePresentation := isFinitePresentation_kernel π
  exact ⟨n₀, k, hbp, π, hπ, isQuasicoherent_of_isFinitePresentation (kernel π),
    isFiniteType_of_isFinitePresentation (kernel π)⟩

/-- Embed `Proj (Sym_R M)` for any finite `R`-module `M` as a closed subscheme of
`Proj (Sym_R (Fin (r + 2) → R))` over `Spec R` via a surjective graded ring homomorphism. -/
private theorem exists_closedImmersion_free_nontrivial (R M : Type u) [CommRing R]
    [AddCommMonoid M] [Module R M] [Module.Finite R M] :
    ∃ (r : ℕ) (φ : GradedRingHom (homogeneousSubmodule R (Fin (r + 2) → R))
        (homogeneousSubmodule R M))
      (hφ : HomogeneousIdeal.irrelevant (homogeneousSubmodule R M) ≤
        (HomogeneousIdeal.irrelevant (homogeneousSubmodule R (Fin (r + 2) → R))).map φ),
      IsClosedImmersion (Proj.map φ hφ) ∧
        (Proj.map φ hφ).IsOver (Spec (.of R)) := by
  obtain ⟨r, g₀, hg₀⟩ := Module.Finite.exists_fin' R M
  let g : (Fin (r + 2) → R) →ₗ[R] M := g₀.comp (LinearMap.funLeft R R (Fin.castAdd 2))
  have hg : Function.Surjective g :=
    hg₀.comp (LinearMap.funLeft_surjective_of_injective _ _ _ (Fin.castAdd_injective r 2))
  let φ := _root_.SymmetricAlgebra.gradedMap R g
  have hφ_surj : Function.Surjective φ := by
    dsimp only [φ]
    simpa only [Function.Surjective, _root_.SymmetricAlgebra.gradedMap_apply] using
      _root_.SymmetricAlgebra.map_surjective R g hg
  have hφ : HomogeneousIdeal.irrelevant (homogeneousSubmodule R M) ≤
      (HomogeneousIdeal.irrelevant (homogeneousSubmodule R (Fin (r + 2) → R))).map φ :=
    HomogeneousIdeal.irrelevant_le_map_of_surjective φ hφ_surj
  refine ⟨r, φ, hφ, Proj.isClosedImmersion_map φ hφ hφ_surj, ⟨?_⟩⟩
  rw [over_eq_projToSpec, over_eq_projToSpec, projToSpec_def, projToSpec_def,
    ← Proj.toSpecCoeff_def, ← Proj.toSpecCoeff_def, Proj.map_toSpecCoeff]
  intro c
  apply Subtype.ext
  rw [GradedRingHom.gradedZeroRingHom_apply_coe]
  dsimp only [φ]
  rw [_root_.SymmetricAlgebra.gradedMap_apply]
  exact (_root_.SymmetricAlgebra.map R g).commutes c

end Helpers

section Basis

variable {R M : Type u} [CommRing R] [IsNoetherianRing R] [AddCommMonoid M] [Module R M]
  {κ : Type*} [Fintype κ] [Nontrivial κ] (b : Module.Basis κ R M)

local notation "𝒜" => homogeneousSubmodule R M

include b in
/-- Auxiliary descending induction proving finiteness of `Hᵠ(Proj (Sym_R M), F)` for free `M` of
rank at least two. -/
private theorem finite_cohomology_of_basis_aux :
    ∀ (r q : ℕ), Fintype.card κ - q ≤ r →
      ∀ (F : (Proj 𝒜).Modules) [F.IsQuasicoherent] [F.IsFiniteType],
        Module.Finite R (Cohomology F q) := by
  have : Module.Finite R M := Module.Finite.of_basis b
  intro r
  induction r with
  | zero =>
    intro q hqr F _ _
    have := b.subsingleton_cohomology_proj_of_card_le F q (by omega)
    infer_instance
  | succ r ih =>
    intro q hqr F _ _
    by_cases hle : Fintype.card κ ≤ q
    · have := b.subsingleton_cohomology_proj_of_card_le F q hle
      infer_instance
    · obtain ⟨n₀, k, _, π, hπ, _, _⟩ := exists_epi_biproduct_twistingSheaf_kernel R M F
      let E : (Proj 𝒜).Modules := ⨁ fun _ : Fin k ↦ Proj.twistingSheaf 𝒜 (-(n₀ : ℤ))
      have hK : Module.Finite R (Cohomology (kernel π) (q + 1)) := ih (q + 1) (by omega) (kernel π)
      have hE : Module.Finite R (Cohomology E q) := by
        have : ∀ _ : Fin k,
            Module.Finite R (Cohomology (Proj.twistingSheaf 𝒜 (-(n₀ : ℤ))) q) :=
          fun _ ↦ b.finite_cohomology_twistingSheaf (-(n₀ : ℤ)) q
        exact Module.Finite.equiv (cohomologyBiproductLinearEquiv R _ q).symm
      let S : ShortComplex (Proj 𝒜).Modules :=
        ShortComplex.mk (kernel.ι π) π (kernel.condition π)
      have hS : S.ShortExact :=
        ShortComplex.ShortExact.mk' (ShortComplex.exact_kernel π) inferInstance hπ
      have : IsNoetherian R (Cohomology F q) := isNoetherian_of_range_eq_ker
        (cohomologyMapBaseLinear R (Proj 𝒜) S.g q)
        (cohomologyδBaseLinear R (Proj 𝒜) hS q (q + 1) rfl)
        (LinearMap.exact_iff.mp
          (exact_cohomologyMapBaseLinear_cohomologyδBaseLinear R (Proj 𝒜) hS q)).symm
      infer_instance

include b in
/-- Auxiliary descending induction proving Serre vanishing at a fixed degree `q > 0` for free `M`
of rank at least two. -/
private theorem exists_subsingleton_cohomology_tensorLeft_of_basis_at :
    ∀ (r q : ℕ), 0 < q → Fintype.card κ - q ≤ r →
      ∀ (F : (Proj 𝒜).Modules) [F.IsQuasicoherent] [F.IsFiniteType],
        ∃ m₀ : ℤ, ∀ m ≥ m₀,
          Subsingleton (Cohomology (Proj.twistingSheaf 𝒜 m ⊗ F) q) := by
  have : Module.Finite R M := Module.Finite.of_basis b
  intro r
  induction r with
  | zero =>
    intro q _ hqr F _ _
    exact ⟨0, fun m _ ↦ b.subsingleton_cohomology_proj_of_card_le _ q (by omega)⟩
  | succ r ih =>
    intro q hq hqr F _ _
    by_cases hle : Fintype.card κ ≤ q
    · exact ⟨0, fun m _ ↦ b.subsingleton_cohomology_proj_of_card_le _ q hle⟩
    · obtain ⟨n₀, k, _, π, hπ, _, _⟩ := exists_epi_biproduct_twistingSheaf_kernel R M F
      obtain ⟨m₁, hm₁⟩ := ih (q + 1) (Nat.succ_pos q) (by omega) (kernel π)
      refine ⟨max m₁ ((n₀ : ℤ) - (Fintype.card κ : ℤ) + 1), fun m hm ↦ ?_⟩
      have hmE : -(Fintype.card κ : ℤ) < m + -(n₀ : ℤ) := by
        have : (n₀ : ℤ) - (Fintype.card κ : ℤ) + 1 ≤ m := le_trans (le_max_right _ _) hm
        omega
      have hK_sub : Subsingleton (Cohomology (Proj.twistingSheaf 𝒜 m ⊗ kernel π) (q + 1)) :=
        hm₁ m (le_trans (le_max_left _ _) hm)
      let L_flf := (InvertibleSheaf.toFiniteLocallyFree (Proj 𝒜)).obj
        ⟨Proj.twistingSheaf 𝒜 m, inferInstance⟩
      have : (Proj.twistingSheaf 𝒜 m).IsLocallyFree := L_flf.property.1
      have : (Proj.twistingSheaf 𝒜 m).IsFinitePresentation := L_flf.property.2
      have : (Proj.twistingSheaf 𝒜 m).IsFiniteType :=
        isFiniteType_of_isFinitePresentation (Proj.twistingSheaf 𝒜 m)
      have hS : (ShortComplex.mk (kernel.ι π) π (kernel.condition π)).ShortExact :=
        ShortComplex.ShortExact.mk' (ShortComplex.exact_kernel π) inferInstance hπ
      have hSm : ((ShortComplex.mk (kernel.ι π) π (kernel.condition π)).map
          (tensorLeft (Proj.twistingSheaf 𝒜 m))).ShortExact :=
        shortExact_map_tensorLeft (Proj.twistingSheaf 𝒜 m) hS
      have : ∀ _ : Fin k,
          Subsingleton (Cohomology (Proj.twistingSheaf 𝒜 (m + -(n₀ : ℤ))) q) :=
        fun _ ↦ b.subsingleton_cohomology_twistingSheaf_of_neg_card_lt hmE hq
      have : HasFiniteBiproducts (Proj 𝒜).Modules := Abelian.hasFiniteBiproducts
      have hsum_sub : Subsingleton (Cohomology
          (⨁ fun _ : Fin k ↦ Proj.twistingSheaf 𝒜 (m + -(n₀ : ℤ))) q) :=
        (cohomologyBiproductLinearEquiv R _ q).injective.subsingleton
      have hE_sub : Subsingleton (Cohomology (Proj.twistingSheaf 𝒜 m ⊗
          (⨁ fun _ : Fin k ↦ Proj.twistingSheaf 𝒜 (-(n₀ : ℤ)))) q) :=
        ((cohomologyFunctor (Proj 𝒜) q).mapIso
          (tensorLeftBiproductTwistingSheafIso R M m (-(n₀ : ℤ)) k).symm).addCommGroupIsoToAddEquiv
          |>.toEquiv.subsingleton_congr.mp hsum_sub
      exact subsingleton_cohomology_X₃ hSm q (q + 1) rfl hE_sub hK_sub

end Basis

section BasisUniform

variable {R M : Type u} [CommRing R] [IsNoetherianRing R] [AddCommMonoid M] [Module R M]
  {κ : Type*} [Finite κ] [Nontrivial κ] (b : Module.Basis κ R M)

local notation "𝒜" => homogeneousSubmodule R M

include b in
/-- Uniform Serre vanishing on `Proj (Sym_R M)` for free `M` of rank at least two. -/
private theorem exists_subsingleton_cohomology_tensorLeft_of_basis
    (F : (Proj 𝒜).Modules) [F.IsQuasicoherent] [F.IsFiniteType] :
    ∃ m₀ : ℤ, ∀ m ≥ m₀, ∀ q > 0,
      Subsingleton (Cohomology (Proj.twistingSheaf 𝒜 m ⊗ F) q) := by
  classical
  have := Fintype.ofFinite κ
  have : Module.Finite R M := Module.Finite.of_basis b
  have hex : ∀ i : Fin (Fintype.card κ), 0 < i.1 →
      ∃ m₀ : ℤ, ∀ m ≥ m₀, Subsingleton (Cohomology (Proj.twistingSheaf 𝒜 m ⊗ F) i.1) :=
    fun i hi ↦ exists_subsingleton_cohomology_tensorLeft_of_basis_at b (Fintype.card κ - i.1)
      i.1 hi le_rfl F
  let bound : Fin (Fintype.card κ) → ℤ := fun i ↦
    if h : 0 < i.1 then (hex i h).choose else 0
  let m₀ : ℤ := Finset.univ.sup' ⟨⟨0, Fintype.card_pos⟩, Finset.mem_univ _⟩ bound
  refine ⟨m₀, fun m hm q hq ↦ ?_⟩
  by_cases hlt : q < Fintype.card κ
  · let i : Fin (Fintype.card κ) := ⟨q, hlt⟩
    have hle : bound i ≤ m₀ := Finset.le_sup' bound (Finset.mem_univ i)
    have hbound : bound i = (hex i hq).choose := by
      dsimp only [bound]
      split_ifs with h
      · rfl
      · exact absurd hq h
    exact (hex i hq).choose_spec m (le_trans (hbound ▸ hle) hm)
  · exact b.subsingleton_cohomology_proj_of_card_le _ q (not_lt.mp hlt)

end BasisUniform

section General

variable (R M : Type u) [CommRing R] [IsNoetherianRing R] [AddCommMonoid M] [Module R M]
  [Module.Finite R M]

local notation "𝒜" => homogeneousSubmodule R M

/-- **Serre's finiteness theorem on `Proj (Sym_R M)`.** Over a Noetherian ring `R`, for any finite
`R`-module `M` (not necessarily free) and any quasi-coherent `𝒪_{Proj (Sym_R M)}`-module `F` of
finite type, the cohomology `Hᵠ(Proj (Sym_R M), F)` is a finitely generated `R`-module in every
degree `q`. -/
theorem finite_cohomology (F : (Proj 𝒜).Modules) [F.IsQuasicoherent] [F.IsFiniteType] (q : ℕ) :
    Module.Finite R (Cohomology F q) := by
  obtain ⟨r, φ, hφ, _, _⟩ := exists_closedImmersion_free_nontrivial R M
  let j := Proj.map φ hφ
  have : ((pushforward j).obj F).IsFinitePresentation :=
    isFinitePresentation_pushforward_of_isFinite j F
  have : ((pushforward j).obj F).IsQuasicoherent :=
    isQuasicoherent_of_isFinitePresentation ((pushforward j).obj F)
  have : ((pushforward j).obj F).IsFiniteType :=
    isFiniteType_of_isFinitePresentation ((pushforward j).obj F)
  have hpush : Module.Finite R (Cohomology ((pushforward j).obj F) q) :=
    finite_cohomology_of_basis_aux (Pi.basisFun R (Fin (r + 2)))
      (Fintype.card (Fin (r + 2)) - q) q le_rfl ((pushforward j).obj F)
  exact (Scheme.Hom.moduleFinite_cohomology_pushforward_iff j R F q).mp hpush

/-- **Serre's vanishing theorem on `Proj (Sym_R M)`.** Over a Noetherian ring `R`, for any finite
`R`-module `M` (not necessarily free) and any quasi-coherent `𝒪_{Proj (Sym_R M)}`-module `F` of
finite type, there exists `m₀ : ℤ` such that `Hᵠ(Proj (Sym_R M), F ⊗ 𝒪(m)) = 0` for all `m ≥ m₀`
and all `q > 0`. -/
theorem exists_subsingleton_cohomology_tensor_twistingSheaf
    (F : (Proj 𝒜).Modules) [F.IsQuasicoherent] [F.IsFiniteType] :
    ∃ m₀ : ℤ, ∀ m ≥ m₀, ∀ q > 0,
      Subsingleton (Cohomology (F ⊗ Proj.twistingSheaf 𝒜 m) q) := by
  obtain ⟨r, φ, hφ, _, _⟩ := exists_closedImmersion_free_nontrivial R M
  let N := Fin (r + 2) → R
  let j := Proj.map φ hφ
  have : ((pushforward j).obj F).IsFinitePresentation :=
    isFinitePresentation_pushforward_of_isFinite j F
  have : ((pushforward j).obj F).IsQuasicoherent :=
    isQuasicoherent_of_isFinitePresentation ((pushforward j).obj F)
  have : ((pushforward j).obj F).IsFiniteType :=
    isFiniteType_of_isFinitePresentation ((pushforward j).obj F)
  obtain ⟨m₀, hm₀⟩ := exists_subsingleton_cohomology_tensorLeft_of_basis
    (Pi.basisFun R (Fin (r + 2))) ((pushforward j).obj F)
  refine ⟨m₀, fun m hm q hq ↦ ?_⟩
  have hsub := hm₀ m hm q hq
  -- Projection formula and `j^* 𝒪(m) ≅ 𝒪(m)` identify `𝒪(m) ⊗ j_* F` with `j_* (F ⊗ 𝒪(m))`.
  let E := (InvertibleSheaf.toFiniteLocallyFree (Proj (homogeneousSubmodule R N))).obj
    ⟨Proj.twistingSheaf (homogeneousSubmodule R N) m, inferInstance⟩
  have hpb : (Scheme.Modules.pullback j).obj
        (Proj.twistingSheaf (homogeneousSubmodule R N) m) ≅
      Proj.twistingSheaf 𝒜 m :=
    asIso (Proj.pullbackTwistingSheafMap φ hφ m)
  let e₁ : Proj.twistingSheaf (homogeneousSubmodule R N) m ⊗ (pushforward j).obj F ≅
      (pushforward j).obj (((FiniteLocallyFreeSheaf.pullback j).obj E).obj ⊗ F) :=
    (FiniteLocallyFreeSheaf.pushforwardTensorLeftIso j E).app F
  let e₂ : ((FiniteLocallyFreeSheaf.pullback j).obj E).obj ⊗ F ≅
      F ⊗ Proj.twistingSheaf 𝒜 m :=
    whiskerRightIso (eqToIso (FiniteLocallyFreeSheaf.pullback_obj_obj j E) ≪≫ hpb) F ≪≫
      β_ (Proj.twistingSheaf 𝒜 m) F
  have hsub' : Subsingleton (Cohomology
      ((pushforward j).obj (F ⊗ Proj.twistingSheaf 𝒜 m)) q) :=
    ((cohomologyFunctor _ q).mapIso (e₁ ≪≫ (pushforward j).mapIso e₂)).addCommGroupIsoToAddEquiv
      |>.toEquiv.subsingleton_congr.mp hsub
  exact (cohomologyPushforwardIso j (F ⊗ Proj.twistingSheaf 𝒜 m)
    q).addCommGroupIsoToAddEquiv.toEquiv.subsingleton_congr.mp hsub'

end General

end TauCeti.SymmetricAlgebra

namespace AlgebraicGeometry.Scheme

/-- **Serre's finiteness theorem for projective schemes.** Let `X` be a scheme projective over a
Noetherian commutative ring `R`, and let `F` be a quasi-coherent `𝒪_X`-module of finite type.
Then `Hᵠ(X, F)` is a finitely generated `R`-module for every `q : ℕ`. Over a field, this says
`Hᵠ(X, F)` is finite-dimensional (`FiniteDimensional` is an abbreviation for `Module.Finite`). -/
theorem IsProjectiveOver.finite_cohomology (R : Type u) [CommRing R] [IsNoetherianRing R]
    {X : Scheme.{u}} [X.Over (Spec (.of R))] [X.IsProjectiveOver R]
    (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType] (q : ℕ) :
    Module.Finite R (Cohomology F q) := by
  obtain ⟨M, _, _, _, j, hj, hjR⟩ := IsProjectiveOver.exists_isClosedImmersion (R := R) (X := X)
  have : ((pushforward j).obj F).IsFinitePresentation :=
    isFinitePresentation_pushforward_of_isFinite j F
  have : ((pushforward j).obj F).IsQuasicoherent :=
    isQuasicoherent_of_isFinitePresentation ((pushforward j).obj F)
  have : ((pushforward j).obj F).IsFiniteType :=
    isFiniteType_of_isFinitePresentation ((pushforward j).obj F)
  exact (Scheme.Hom.moduleFinite_cohomology_pushforward_iff j R F q).mp
    (TauCeti.SymmetricAlgebra.finite_cohomology R M ((pushforward j).obj F) q)

/-- **Serre's vanishing theorem for closed subschemes of `Proj (Sym_R M)`.** Let `R` be a
Noetherian ring, `M` a finite `R`-module, and `j : X ⟶ Proj (Sym_R M)` a closed immersion. For
every quasi-coherent `𝒪_X`-module `F` of finite type, there exists `m₀ : ℤ` such that
`Hᵠ(X, F ⊗ j^* 𝒪(m)) = 0` for all `m ≥ m₀` and all `q > 0`. No base-scheme structure on `X` is
required. -/
theorem Hom.exists_subsingleton_cohomology_tensor_pullback_twistingSheaf {R M : Type u}
    [CommRing R] [IsNoetherianRing R] [AddCommMonoid M] [Module R M] [Module.Finite R M]
    {X : Scheme.{u}} (j : X ⟶ Proj (TauCeti.SymmetricAlgebra.homogeneousSubmodule R M))
    [IsClosedImmersion j] (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType] :
    ∃ m₀ : ℤ, ∀ m ≥ m₀, ∀ q > 0,
      Subsingleton (Cohomology (F ⊗ (Scheme.Modules.pullback j).obj
        (Proj.twistingSheaf (TauCeti.SymmetricAlgebra.homogeneousSubmodule R M) m)) q) := by
  have : ((pushforward j).obj F).IsFinitePresentation :=
    isFinitePresentation_pushforward_of_isFinite j F
  have : ((pushforward j).obj F).IsQuasicoherent :=
    isQuasicoherent_of_isFinitePresentation ((pushforward j).obj F)
  have : ((pushforward j).obj F).IsFiniteType :=
    isFiniteType_of_isFinitePresentation ((pushforward j).obj F)
  obtain ⟨m₀, hm₀⟩ :=
    TauCeti.SymmetricAlgebra.exists_subsingleton_cohomology_tensor_twistingSheaf R M
      ((pushforward j).obj F)
  refine ⟨m₀, fun m hm q hq ↦ ?_⟩
  have hsub := hm₀ m hm q hq
  let E := (InvertibleSheaf.toFiniteLocallyFree
    (Proj (TauCeti.SymmetricAlgebra.homogeneousSubmodule R M))).obj
      ⟨Proj.twistingSheaf _ m, inferInstance⟩
  let e : ((pushforward j).obj F) ⊗ Proj.twistingSheaf _ m ≅
      (pushforward j).obj (F ⊗ (Scheme.Modules.pullback j).obj (Proj.twistingSheaf _ m)) :=
    β_ _ _ ≪≫
      (FiniteLocallyFreeSheaf.pushforwardTensorLeftIso j E).app F ≪≫
      (pushforward j).mapIso
        (whiskerRightIso (eqToIso (FiniteLocallyFreeSheaf.pullback_obj_obj j E)) F ≪≫ β_ _ F)
  have hsub' : Subsingleton (Cohomology
      ((pushforward j).obj (F ⊗ (Scheme.Modules.pullback j).obj (Proj.twistingSheaf _ m))) q) :=
    ((cohomologyFunctor _ q).mapIso e).addCommGroupIsoToAddEquiv.toEquiv.subsingleton_congr.mp
      hsub
  exact (cohomologyPushforwardIso j _ q).addCommGroupIsoToAddEquiv.toEquiv.subsingleton_congr.mp
    hsub'

end AlgebraicGeometry.Scheme
