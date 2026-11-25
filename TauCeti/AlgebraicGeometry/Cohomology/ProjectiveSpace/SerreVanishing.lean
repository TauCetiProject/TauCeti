/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.RingTheory.Noetherian.Defs
public import TauCeti.AlgebraicGeometry.Cohomology.Module.Base
public import TauCeti.AlgebraicGeometry.Modules.Tensor.Product
public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.SymmetricAlgebra
public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.TwistingSheaf.Basic
import Mathlib.RingTheory.Noetherian.Basic
import TauCeti.Algebra.Category.ModuleCat.Sheaf.FinitePresentation
import TauCeti.Algebra.Category.ModuleCat.Sheaf.Free.Basic
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
import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.TwistingSheaf.GlobalGeneration
import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.TwistingSheaf.Pullback
import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.TwistingSheaf.TensorProduct
import TauCeti.AlgebraicGeometry.VectorBundle.Dual.Basic
import TauCeti.AlgebraicGeometry.VectorBundle.ProjectionFormula

/-!
# Serre's vanishing theorem on projective schemes

Let `R` be a Noetherian commutative ring. This file proves Serre's vanishing theorem (Hartshorne,
Theorem III.5.2(b); Stacks, Lemma 30.14.1, Tag 01YS) for coherent (quasi-coherent of finite type)
sheaves of modules on `Proj (Sym_R M)` for any finite `R`-module `M`, and along any closed
immersion `j : X ⟶ Proj (Sym_R M)` with respect to the pulled-back twisting sheaves `j^* 𝒪(m)`.
Together with `Cohomology/ProjectiveSpace/Finite.lean` (Hartshorne, Theorem III.5.2(a)), this
completes Serre's finiteness and vanishing theorems on projective schemes.

For a free module `M` with a finite basis of at least two elements, the proof proceeds by
descending induction on the cohomological degree `q` from the ambient vanishing bound `card κ ≤ q`
(`Module.Basis.subsingleton_cohomology_proj_of_card_le`). Every quasi-coherent sheaf `F` of finite
type receives an epimorphism from `E = 𝒪^{⊕I} ⊗ 𝒪(-n₀)` for a finite `I`
(`AlgebraicGeometry.Proj.eventually_exists_epi_free_tensor_twistingSheaf`). Because
`Proj (Sym_R M)` is Noetherian, the kernel `K` of `E ↠ F` is again finitely presented, hence
quasi-coherent and of finite type (`AlgebraicGeometry.Scheme.Modules.isFinitePresentation_kernel`).
Twisting `0 → K → E → F → 0` by `𝒪(m)` preserves exactness
(`AlgebraicGeometry.Scheme.Modules.shortExact_map_tensorLeft`), and for `m` sufficiently large both
`Hᵠ(𝒪(m) ⊗ E)` (`Module.Basis.subsingleton_cohomology_twistingSheaf_of_neg_card_lt`) and
`H^{q+1}(𝒪(m) ⊗ K)` (induction hypothesis) vanish, forcing `Hᵠ(𝒪(m) ⊗ F) = 0`. Taking the maximum
over the finitely many degrees `0 < q < card κ` yields a uniform bound `m₀ : ℤ`.

Pushing forward along a closed immersion preserves coherence and cohomology, and the projection
formula (`TauCeti.AlgebraicGeometry.FiniteLocallyFreeSheaf.pushforwardTensorLeftIso`) transfers
twisting by `𝒪(m)` to closed subschemes of `Proj (Sym_R M)` when `M` is free of rank at least two.
An arbitrary finite `R`-module `M` embeds via
`TauCeti.SymmetricAlgebra.exists_isClosedImmersion_proj_map_free` as a closed subscheme
`Proj (Sym_R M) ↪ Proj (Sym_R R^{r+2})` along which `𝒪(m)` pulls back to `𝒪(m)`
(`AlgebraicGeometry.Proj.pullbackTwistingSheafMap`), extending Serre vanishing to every closed
subscheme `j : X ⟶ Proj (Sym_R M)` with no base-scheme structure on `X` required, and in particular
to `Proj (Sym_R M)` itself.

## Main results

* `AlgebraicGeometry.Scheme.Hom.exists_subsingleton_cohomology_tensor_pullback_twistingSheaf`:
  Serre's vanishing theorem for a closed subscheme `j : X ⟶ Proj (Sym_R M)` with respect to
  `j^* 𝒪(m)`.
* `TauCeti.SymmetricAlgebra.exists_subsingleton_cohomology_tensor_twistingSheaf`: Serre's vanishing
  theorem on `Proj (Sym_R M)` for a finite `R`-module `M` over a Noetherian ring `R`.

## References

* R. Hartshorne, *Algebraic Geometry*, GTM 52, Springer, 1977, Theorem III.5.2(b).
* [Stacks, Lemma 30.14.1 (01YS)](https://stacks.math.columbia.edu/tag/01YS).
-/

public section

open CategoryTheory Limits MonoidalCategory BraidedCategory AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme.Modules

universe u

noncomputable section

namespace TauCeti.SymmetricAlgebra

section Helpers

/-- Tensoring `𝒪^{⊕I} ⊗ 𝒪(n)` on the left by `𝒪(m)` yields a finite direct sum `⨁_I 𝒪(m + n)`. -/
private def tensorLeftFreeTensorTwistingSheafIso (R M : Type u) [CommRing R] [AddCommMonoid M]
    [Module R M] (m n : ℤ) (I : Type u) [Finite I] :
    (Proj.twistingSheaf (homogeneousSubmodule R M) m ⊗
        ((_root_.SheafOfModules.free I : (Proj (homogeneousSubmodule R M)).Modules) ⊗
          Proj.twistingSheaf (homogeneousSubmodule R M) n) :
        (Proj (homogeneousSubmodule R M)).Modules) ≅
      (⨁ fun _ : I ↦ Proj.twistingSheaf (homogeneousSubmodule R M) (m + n) :
        (Proj (homogeneousSubmodule R M)).Modules) :=
  (α_ _ _ _).symm ≪≫ whiskerRightIso (β_ _ _) _ ≪≫ α_ _ _ _ ≪≫
    whiskerLeftIso _
      (Proj.twistingSheaf.tensorObjIso (_root_.SymmetricAlgebra.ι R M)
        (ι_mem_homogeneousSubmodule R M) (iSup_basicOpen_ι_eq_top R M id (by simp)) m n) ≪≫
    freeTensorIsoBiproduct I (Proj.twistingSheaf (homogeneousSubmodule R M) (m + n))

end Helpers

section Basis

variable {R M : Type u} [CommRing R] [IsNoetherianRing R] [AddCommMonoid M] [Module R M]
  {κ : Type*} [Fintype κ] [Nontrivial κ] (b : Module.Basis κ R M)

local notation "𝒜" => homogeneousSubmodule R M

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
    · obtain ⟨n₀, I, _, π₀, hπ₀⟩ := (Proj.eventually_exists_epi_free_tensor_twistingSheaf
        (_root_.SymmetricAlgebra.ι R M) (ι_mem_homogeneousSubmodule R M)
        (iSup_basicOpen_ι_eq_top R M id (by simp)) F).exists
      have : Fintype I := Fintype.ofFinite I
      let freeI : (Proj 𝒜).Modules := _root_.SheafOfModules.free I
      let E : (Proj 𝒜).Modules := freeI ⊗ Proj.twistingSheaf 𝒜 (-(n₀ : ℤ))
      let π : E ⟶ F := π₀
      have hπ : Epi π := hπ₀
      have : E.IsFinitePresentation :=
        TauCeti.SheafOfModules.isFinitePresentation_tensorObj (R := (Proj 𝒜).sheaf)
      obtain ⟨m₁, hm₁⟩ := ih (q + 1) (Nat.succ_pos q) (by omega) (kernel π)
      refine ⟨max m₁ ((n₀ : ℤ) - (Fintype.card κ : ℤ) + 1), fun m hm ↦ ?_⟩
      have hmE : -(Fintype.card κ : ℤ) < m + -(n₀ : ℤ) := by
        have : (n₀ : ℤ) - (Fintype.card κ : ℤ) + 1 ≤ m := le_trans (le_max_right _ _) hm
        omega
      have hK_sub : Subsingleton (Cohomology (Proj.twistingSheaf 𝒜 m ⊗ kernel π) (q + 1)) :=
        hm₁ m (le_trans (le_max_left _ _) hm)
      let L_flf := (InvertibleSheaf.toFiniteLocallyFree (Proj 𝒜)).obj
        ⟨Proj.twistingSheaf 𝒜 m, inferInstance⟩
      have : (Proj.twistingSheaf 𝒜 m).IsLocallyFree := L_flf.property.left
      have : (Proj.twistingSheaf 𝒜 m).IsFinitePresentation := L_flf.property.right
      have : (Proj.twistingSheaf 𝒜 m).IsFiniteType :=
        isFiniteType_of_isFinitePresentation (Proj.twistingSheaf 𝒜 m)
      have hS : (ShortComplex.mk (kernel.ι π) π (kernel.condition π)).ShortExact :=
        ShortComplex.ShortExact.mk' (ShortComplex.exact_kernel π) inferInstance hπ
      have hSm : ((ShortComplex.mk (kernel.ι π) π (kernel.condition π)).map
          (tensorLeft (Proj.twistingSheaf 𝒜 m))).ShortExact :=
        shortExact_map_tensorLeft (Proj.twistingSheaf 𝒜 m) hS
      have : ∀ _ : I,
          Subsingleton (Cohomology (Proj.twistingSheaf 𝒜 (m + -(n₀ : ℤ))) q) :=
        fun _ ↦ b.subsingleton_cohomology_twistingSheaf_of_neg_card_lt hmE hq
      have hsum_sub : Subsingleton (Cohomology
          (⨁ fun _ : I ↦ Proj.twistingSheaf 𝒜 (m + -(n₀ : ℤ)) : (Proj 𝒜).Modules) q) :=
        (cohomologyBiproductLinearEquiv R _ q).injective.subsingleton
      have hE_sub : Subsingleton (Cohomology (Proj.twistingSheaf 𝒜 m ⊗ E) q) :=
        ((cohomologyFunctor (Proj 𝒜) q).mapIso
          (tensorLeftFreeTensorTwistingSheafIso R M m (-(n₀ : ℤ)) I).symm).addCommGroupIsoToAddEquiv
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
  have hex : ∀ i : Fin (Fintype.card κ), 0 < i.val →
      ∃ m₀ : ℤ, ∀ m ≥ m₀, Subsingleton (Cohomology (Proj.twistingSheaf 𝒜 m ⊗ F) i.val) :=
    fun i hi ↦ exists_subsingleton_cohomology_tensorLeft_of_basis_at b (Fintype.card κ - i.val)
      i.val hi le_rfl F
  let bound : Fin (Fintype.card κ) → ℤ := fun i ↦
    if h : 0 < i.val then (hex i h).choose else 0
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

include b in
/-- Serre vanishing along a closed immersion into `Proj (Sym_R M)` when `M` is free of rank at least
two, proved via the projection formula and cohomology preservation under closed immersions. -/
private theorem exists_subsingleton_cohomology_tensor_pullback_twistingSheaf_of_basis
    {X : Scheme.{u}} (j : X ⟶ Proj 𝒜) [IsClosedImmersion j]
    (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType] :
    ∃ m₀ : ℤ, ∀ m ≥ m₀, ∀ q > 0,
      Subsingleton (Cohomology (F ⊗ (Scheme.Modules.pullback j).obj
        (Proj.twistingSheaf 𝒜 m)) q) := by
  have : Module.Finite R M := Module.Finite.of_basis b
  have : ((pushforward j).obj F).IsFinitePresentation :=
    isFinitePresentation_pushforward_of_isFinite j F
  have : ((pushforward j).obj F).IsQuasicoherent :=
    isQuasicoherent_of_isFinitePresentation ((pushforward j).obj F)
  have : ((pushforward j).obj F).IsFiniteType :=
    isFiniteType_of_isFinitePresentation ((pushforward j).obj F)
  obtain ⟨m₀, hm₀⟩ := exists_subsingleton_cohomology_tensorLeft_of_basis b ((pushforward j).obj F)
  refine ⟨m₀, fun m hm q hq ↦ ?_⟩
  let E := (InvertibleSheaf.toFiniteLocallyFree (Proj 𝒜)).obj
    ⟨Proj.twistingSheaf 𝒜 m, inferInstance⟩
  let e : Proj.twistingSheaf 𝒜 m ⊗ (pushforward j).obj F ≅
      (pushforward j).obj (F ⊗ (Scheme.Modules.pullback j).obj (Proj.twistingSheaf 𝒜 m)) :=
    (FiniteLocallyFreeSheaf.pushforwardTensorLeftIso j E).app F ≪≫
      (pushforward j).mapIso
        (whiskerRightIso (eqToIso (FiniteLocallyFreeSheaf.pullback_obj_obj j E)) F ≪≫ β_ _ F)
  have hsub' : Subsingleton (Cohomology
      ((pushforward j).obj (F ⊗ (Scheme.Modules.pullback j).obj (Proj.twistingSheaf 𝒜 m))) q) :=
    ((cohomologyFunctor _ q).mapIso e).addCommGroupIsoToAddEquiv.toEquiv.subsingleton_congr.mp
      (hm₀ m hm q hq)
  exact (cohomologyPushforwardIso j _ q).addCommGroupIsoToAddEquiv.toEquiv.subsingleton_congr.mp
    hsub'

end BasisUniform

end TauCeti.SymmetricAlgebra

namespace AlgebraicGeometry.Scheme

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
  obtain ⟨r, g, hg, _, _⟩ :=
    TauCeti.SymmetricAlgebra.exists_isClosedImmersion_proj_map_free R M
  let φ := _root_.SymmetricAlgebra.gradedMap R g
  let k := Proj.map φ hg
  obtain ⟨m₀, hm₀⟩ :=
    TauCeti.SymmetricAlgebra.exists_subsingleton_cohomology_tensor_pullback_twistingSheaf_of_basis
      (Pi.basisFun R (Fin (r + 2))) (j ≫ k) F
  refine ⟨m₀, fun m hm q hq ↦ ?_⟩
  let e : (Scheme.Modules.pullback (j ≫ k)).obj
        (Proj.twistingSheaf (TauCeti.SymmetricAlgebra.homogeneousSubmodule R (Fin (r + 2) → R)) m) ≅
      (Scheme.Modules.pullback j).obj
        (Proj.twistingSheaf (TauCeti.SymmetricAlgebra.homogeneousSubmodule R M) m) :=
    ((Scheme.Modules.pullbackComp j k).app _).symm ≪≫
      (Scheme.Modules.pullback j).mapIso (asIso (Proj.pullbackTwistingSheafMap φ hg m))
  exact ((cohomologyFunctor X q).mapIso (whiskerLeftIso F e)).addCommGroupIsoToAddEquiv
    |>.toEquiv.subsingleton_congr.mp (hm₀ m hm q hq)

end AlgebraicGeometry.Scheme

namespace TauCeti.SymmetricAlgebra

variable (R M : Type u) [CommRing R] [IsNoetherianRing R] [AddCommMonoid M] [Module R M]
  [Module.Finite R M]

/-- **Serre's vanishing theorem on `Proj (Sym_R M)`.** Over a Noetherian ring `R`, for any finite
`R`-module `M` (not necessarily free) and any quasi-coherent `𝒪_{Proj (Sym_R M)}`-module `F` of
finite type, there exists `m₀ : ℤ` such that `Hᵠ(Proj (Sym_R M), F ⊗ 𝒪(m)) = 0` for all `m ≥ m₀`
and all `q > 0`. -/
theorem exists_subsingleton_cohomology_tensor_twistingSheaf
    (F : (Proj (homogeneousSubmodule R M)).Modules) [F.IsQuasicoherent] [F.IsFiniteType] :
    ∃ m₀ : ℤ, ∀ m ≥ m₀, ∀ q > 0,
      Subsingleton (Cohomology (F ⊗ Proj.twistingSheaf (homogeneousSubmodule R M) m) q) := by
  obtain ⟨m₀, hm₀⟩ :=
    Scheme.Hom.exists_subsingleton_cohomology_tensor_pullback_twistingSheaf (𝟙 _) F
  refine ⟨m₀, fun m hm q hq ↦ ?_⟩
  let e := whiskerLeftIso F ((Scheme.Modules.pullbackId _).app
    (Proj.twistingSheaf (homogeneousSubmodule R M) m))
  exact ((cohomologyFunctor _ q).mapIso e).addCommGroupIsoToAddEquiv
    |>.toEquiv.subsingleton_congr.mp (hm₀ m hm q hq)

end TauCeti.SymmetricAlgebra

end
