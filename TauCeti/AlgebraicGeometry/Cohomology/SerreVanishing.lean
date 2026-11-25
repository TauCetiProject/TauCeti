/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import TauCeti.AlgebraicGeometry.Cohomology.Basic
public import TauCeti.AlgebraicGeometry.Modules.Tensor.Product
public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.ClosedImmersion
public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.TwistingSheaf.Basic
import TauCeti.Algebra.Category.ModuleCat.Sheaf.FinitePresentation
import TauCeti.Algebra.Category.ModuleCat.Sheaf.Free.Basic
import TauCeti.Algebra.Category.ModuleCat.Sheaf.Quasicoherent.Monoidal
import TauCeti.AlgebraicGeometry.Cohomology.Biproduct
import TauCeti.AlgebraicGeometry.Cohomology.ClosedImmersion.ProjectionFormula
import TauCeti.AlgebraicGeometry.Cohomology.LongExactSequence
import TauCeti.AlgebraicGeometry.Cohomology.ProjectiveSpace.HigherCohomology
import TauCeti.AlgebraicGeometry.Cohomology.ProjectiveSpace.Vanishing
import TauCeti.AlgebraicGeometry.LineBundle.Dual
import TauCeti.AlgebraicGeometry.Modules.FinitePresentation.Abelian
import TauCeti.AlgebraicGeometry.Modules.FinitePresentation.Basic
import TauCeti.AlgebraicGeometry.Modules.Quasicoherent.Pushforward.Finite
import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.TwistingSheaf.GlobalGeneration
import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.TwistingSheaf.LocalTriviality
import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.TwistingSheaf.Pullback
import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.TwistingSheaf.TensorProduct

/-!
# Serre's cohomology vanishing theorem on projective schemes

Let `R` be a Noetherian commutative ring and `M` a finitely generated `R`-module. This file proves
Serre's cohomology vanishing theorem (Hartshorne, Theorem III.5.2(b); Stacks Tags 01YS, 0B5T, and
0B5U; for Serre's cohomology finiteness theorem III.5.2(a), see
`AlgebraicGeometry.Scheme.Modules.finite_cohomology_of_isProjectiveOver` in
`TauCeti.AlgebraicGeometry.Cohomology.ProjectiveSpace.Finite`):

1. **On `Proj (Sym_R M)`**
   (`TauCeti.SymmetricAlgebra.exists_forall_ge_subsingleton_cohomology_tensor_twistingSheaf`):
   for every quasi-coherent `𝒪`-module `F` of finite type on `Proj (Sym_R M)`, some `m₀ : ℤ` gives
   `H^q(Proj (Sym_R M), F ⊗ 𝒪(m)) = 0` for all `m ≥ m₀` and `q > 0`.
2. **On closed subschemes of `Proj (Sym_R M)`**
   (`Scheme.Hom.exists_forall_ge_subsingleton_cohomology_tensor_pullback_twistingSheaf`):
   for any closed immersion `i : X ⟶ Proj (Sym_R M)` and quasi-coherent `F` of finite type on `X`,
   some `m₀ : ℤ` gives `H^q(X, F ⊗ i^* 𝒪(m)) = 0` for all `m ≥ m₀` and `q > 0`.

The proof first treats standard projective space `Proj (Sym_R R^{r+2})` by descending induction on
`q` starting from Čech vanishing above the dimension, presenting `F` as a quotient of
`𝒪^{⊕I} ⊗ 𝒪(-n₀)` (`AlgebraicGeometry.Proj.eventually_exists_epi_free_tensor_twistingSheaf`) and
using the vanishing of positive cohomology of `𝒪(-n₀ + m)` for `-n₀ + m > -(r + 2)`, and then
transfers to `Proj (Sym_R M)` and its closed subschemes along closed immersions via
`AlgebraicGeometry.Scheme.Hom.subsingleton_cohomology_pushforward_tensor_iff_of_isInvertible`.

## References

* J.-P. Serre, *Faisceaux algébriques cohérents*, Ann. of Math. (2) **61** (1955), §66.
* A. Grothendieck, *EGA III₁*, Publ. Math. IHÉS **11** (1961), Theorem 2.2.1.
* R. Hartshorne, *Algebraic Geometry*, GTM 52, Springer, 1977, Theorem III.5.2(b).
* [The Stacks Project, Tag 01YS](https://stacks.math.columbia.edu/tag/01YS),
  [Tag 0B5T](https://stacks.math.columbia.edu/tag/0B5T), and
  [Tag 0B5U](https://stacks.math.columbia.edu/tag/0B5U).
-/

public section

noncomputable section

open CategoryTheory Limits MonoidalCategory AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme.Modules

universe u

namespace Module.Basis

open TauCeti.SymmetricAlgebra

variable {R P : Type u} [CommRing R] [AddCommMonoid P] [Module R P]

local notation "𝒜" => homogeneousSubmodule R P
local notation "𝒪(" m ")" => (Proj.twistingSheaf 𝒜 m : Scheme.Modules (Proj 𝒜))

private theorem subsingleton_cohomology_free_tensor (I : Type u) [Finite I]
    (L : (Proj 𝒜).Modules) (q : ℕ) [Subsingleton (Cohomology L q)] :
    Subsingleton (Cohomology ((SheafOfModules.free I : (Proj 𝒜).Modules) ⊗ L) q) := by
  have : Fintype I := .ofFinite I
  have : MonoidalPreadditive (Proj 𝒜).Modules :=
    TauCeti.SheafOfModules.monoidalPreadditive (Proj 𝒜).sheaf
  have : HasBiproduct (C := (Proj 𝒜).Modules) fun _ : I ↦ L := HasBiproduct.of_hasCoproduct _
  have : HasBiproduct (C := (Proj 𝒜).Modules) fun _ : I ↦ 𝟙_ (Proj 𝒜).Modules :=
    HasBiproduct.of_hasCoproduct _
  let e₀ : Iso (C := (Proj 𝒜).Modules) (SheafOfModules.free I)
      (⨁ fun _ : I ↦ 𝟙_ (Proj 𝒜).Modules) :=
    (TauCeti.SheafOfModules.biproductIsoFree (R := (Proj 𝒜).sheaf) I).symm
  let e : Iso (C := (Proj 𝒜).Modules)
      ((SheafOfModules.free I : (Proj 𝒜).Modules) ⊗ L) (⨁ fun _ : I ↦ L) :=
    whiskerRightIso e₀ L ≪≫ (tensorRight L).mapBiproduct _ ≪≫ biproduct.mapIso fun _ ↦ λ_ L
  have := (cohomologyBiproductLinearEquiv R (fun _ : I ↦ L) q).subsingleton
  exact subsingleton_cohomology_of_iso e q

private theorem subsingleton_cohomology_free_tensor_twistingSheaf {κ : Type*} [Fintype κ]
    (b : Module.Basis κ R P) (I : Type u) [Finite I] (n m : ℤ)
    (hm : -(Fintype.card κ : ℤ) < -n + m) {q : ℕ} (hq : 0 < q) :
    Subsingleton (Cohomology (((SheafOfModules.free I : (Proj 𝒜).Modules) ⊗ 𝒪(-n)) ⊗ 𝒪(m)) q) := by
  have : Subsingleton (Cohomology 𝒪(-n + m) q) :=
    b.subsingleton_cohomology_twistingSheaf_of_neg_card_lt hm hq
  have := subsingleton_cohomology_free_tensor (R := R) (P := P) I 𝒪(-n + m) q
  let e₁ : ((SheafOfModules.free I : (Proj 𝒜).Modules) ⊗ 𝒪(-n)) ⊗ 𝒪(m) ≅
      (SheafOfModules.free I : (Proj 𝒜).Modules) ⊗ 𝒪(-n + m) :=
    α_ _ _ _ ≪≫ whiskerLeftIso _ (Proj.twistingSheaf.tensorObjIso
      (_root_.SymmetricAlgebra.ι R P) (ι_mem_homogeneousSubmodule R P)
      (iSup_basicOpen_ι_eq_top R P id (by simp)) (-n) m)
  exact subsingleton_cohomology_of_iso e₁ q

private theorem exists_forall_ge_subsingleton_cohomology_tensor_twistingSheaf_aux
    [IsNoetherianRing R] {κ : Type*} [Fintype κ] [Nonempty κ] (b : Module.Basis κ R P) :
    ∀ (d : ℕ) (F : (Proj 𝒜).Modules) [F.IsQuasicoherent] [F.IsFiniteType],
      ∃ m₀ : ℤ, ∀ m ≥ m₀, ∀ q ≥ Fintype.card κ - d, 0 < q → Subsingleton (Cohomology (F ⊗ 𝒪(m)) q)
  | 0, F, _, _ =>
    ⟨0, fun m _ q hq _ ↦ b.subsingleton_cohomology_proj_of_card_le (F ⊗ 𝒪(m)) q (by simpa using hq)⟩
  | d + 1, F, _, _ => by
    have : Module.Finite R P := .of_basis b
    -- Present `F` as a quotient of `𝒪^{⊕I} ⊗ 𝒪(-n₀)` with finite `I` and coherent kernel.
    obtain ⟨n₀, I, _, p₀, hp₀⟩ := (Proj.eventually_exists_epi_free_tensor_twistingSheaf
      (_root_.SymmetricAlgebra.ι R P) (ι_mem_homogeneousSubmodule R P)
      (iSup_basicOpen_ι_eq_top R P id (by simp)) F).exists
    let E : (Proj 𝒜).Modules := (SheafOfModules.free I : (Proj 𝒜).Modules) ⊗ 𝒪(-(n₀ : ℤ))
    let p : E ⟶ F := p₀
    have : Epi p := hp₀
    have : E.IsFinitePresentation :=
      TauCeti.SheafOfModules.isFinitePresentation_tensorObj (R := (Proj 𝒜).sheaf)
    let S := ShortComplex.mk (kernel.ι p) p (kernel.condition p)
    have hS : S.ShortExact :=
      .mk' (ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel p)) inferInstance ‹_›
    obtain ⟨m₁, hm₁⟩ :=
      exists_forall_ge_subsingleton_cohomology_tensor_twistingSheaf_aux b d (kernel p)
    refine ⟨max m₁ ((n₀ : ℤ) - Fintype.card κ + 1), fun m hm q hqd hq ↦ ?_⟩
    have hm_card : -(Fintype.card κ : ℤ) < -(n₀ : ℤ) + m := by
      have := le_of_max_le_right hm; omega
    let Lm : InvertibleSheaf (Proj 𝒜) :=
      ⟨𝒪(m), Proj.isInvertible_twistingSheaf_of_iSup_eq_top
        (_root_.SymmetricAlgebra.ι R P) (ι_mem_homogeneousSubmodule R P)
        (iSup_basicOpen_ι_eq_top R P id (by simp)) m⟩
    have : (tensorRight Lm.obj).IsEquivalence := by
      rw [← InvertibleSheaf.tensorRightDualEquivalence_inverse Lm]
      infer_instance
    exact subsingleton_cohomology_X₃ (hS.map_of_exact (tensorRight Lm.obj)) q (q + 1) rfl
      (subsingleton_cohomology_free_tensor_twistingSheaf b I n₀ m hm_card hq)
      (hm₁ m (le_of_max_le_left hm) (q + 1) (by omega) (Nat.succ_pos q))

end Module.Basis

namespace TauCeti.SymmetricAlgebra

variable (R M : Type u) [CommRing R] [AddCommMonoid M] [Module R M]

/-- **Serre's vanishing theorem on `Proj (Sym_R M)`** (Hartshorne, Theorem III.5.2(b); Stacks Tags
01YS and 0B5T): over a Noetherian ring `R`, for any finite `R`-module `M` and quasi-coherent `F` of
finite type on `Proj (Sym_R M)`, some `m₀ : ℤ` gives `H^q(Proj (Sym_R M), F ⊗ 𝒪(m)) = 0` for all
`m ≥ m₀` and `q > 0`. -/
theorem exists_forall_ge_subsingleton_cohomology_tensor_twistingSheaf [IsNoetherianRing R]
    [Module.Finite R M] (F : (Proj (homogeneousSubmodule R M)).Modules)
    [F.IsQuasicoherent] [F.IsFiniteType] :
    ∃ m₀ : ℤ, ∀ m ≥ m₀, ∀ q > 0,
      Subsingleton (Cohomology
        (F ⊗ (Proj.twistingSheaf (homogeneousSubmodule R M) m :
          (Proj (homogeneousSubmodule R M)).Modules)) q) := by
  obtain ⟨r, φ₀, hφ₀⟩ := Module.Finite.exists_fin' R M
  let φ : (Fin (r + 2) → R) →ₗ[R] M := φ₀.comp (LinearMap.funLeft R R (Fin.castAdd 2))
  have hφ : Function.Surjective φ := hφ₀.comp (Fin.castAdd_injective r 2).surjective_comp_right
  let g := Proj.mapSymmetricAlgebraOfSurjective φ hφ
  obtain ⟨m₀, hm₀⟩ :=
    Module.Basis.exists_forall_ge_subsingleton_cohomology_tensor_twistingSheaf_aux
      (Pi.basisFun R (Fin (r + 2))) (r + 2) ((pushforward g).obj F)
  exact ⟨m₀, fun m hm q hq ↦ (subsingleton_cohomology_congr
      ((tensorLeft F).mapIso (Proj.pullbackTwistingSheafMapSymmetricAlgebraIso φ hφ m)).symm q).mpr
    ((g.subsingleton_cohomology_pushforward_tensor_iff_of_isInvertible F _ q).mp
      (hm₀ m hm q (by simp) hq))⟩

end TauCeti.SymmetricAlgebra

namespace AlgebraicGeometry.Scheme

open TauCeti.SymmetricAlgebra

/-- **Serre's vanishing theorem on closed subschemes of `Proj (Sym_R M)`** (Hartshorne, Theorem
III.5.2(b); Stacks Tag 0B5U): for a closed immersion `i : X ⟶ Proj (Sym_R M)` with `R` Noetherian
and `M` finite over `R`, and quasi-coherent `F` of finite type on `X`, some `m₀ : ℤ` gives
`H^q(X, F ⊗ i^* 𝒪(m)) = 0` for all `m ≥ m₀` and `q > 0`. -/
theorem Hom.exists_forall_ge_subsingleton_cohomology_tensor_pullback_twistingSheaf
    {R M : Type u} [CommRing R] [IsNoetherianRing R] [AddCommMonoid M] [Module R M]
    [Module.Finite R M] {X : Scheme.{u}} (i : X ⟶ Proj (homogeneousSubmodule R M))
    [IsClosedImmersion i] (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType] :
    ∃ m₀ : ℤ, ∀ m ≥ m₀, ∀ q > 0,
      Subsingleton (Cohomology (F ⊗ (Scheme.Modules.pullback i).obj
        (Proj.twistingSheaf (homogeneousSubmodule R M) m :
          (Proj (homogeneousSubmodule R M)).Modules)) q) := by
  obtain ⟨m₀, hm₀⟩ :=
    TauCeti.SymmetricAlgebra.exists_forall_ge_subsingleton_cohomology_tensor_twistingSheaf R M
      ((pushforward i).obj F)
  exact ⟨m₀, fun m hm q hq ↦
    (i.subsingleton_cohomology_pushforward_tensor_iff_of_isInvertible F _ q).mp (hm₀ m hm q hq)⟩

end AlgebraicGeometry.Scheme

end
