/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import TauCeti.AlgebraicGeometry.Cohomology.Module.Base
public import TauCeti.AlgebraicGeometry.Modules.Tensor.Product
public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.SymmetricAlgebra
public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.TwistingSheaf.Basic
import TauCeti.AlgebraicGeometry.Cohomology.Biproduct
import TauCeti.AlgebraicGeometry.Cohomology.ClosedImmersion.Linear
import TauCeti.AlgebraicGeometry.Cohomology.ClosedImmersion.ProjectionFormula
import TauCeti.AlgebraicGeometry.Cohomology.ProjectiveSpace.HigherCohomology
import TauCeti.AlgebraicGeometry.Cohomology.ProjectiveSpace.Vanishing
import TauCeti.AlgebraicGeometry.Modules.FinitePresentation.Abelian
import TauCeti.AlgebraicGeometry.Modules.Quasicoherent.Pushforward.Finite
import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.TwistingSheaf.Presentation
import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.TwistingSheaf.Pullback
import TauCeti.RingTheory.Finiteness.Finsupp

/-!
# Serre's finiteness and vanishing theorems on `Proj (Sym_R M)`

Let `R` be a Noetherian commutative ring and `M` a finitely generated `R`-module. For every
quasi-coherent `𝒪`-module `F` of finite type on `Proj (Sym_R M)`:
1. **Serre's finiteness theorem** (`TauCeti.SymmetricAlgebra.finite_cohomology_proj`):
   `H^q(Proj (Sym_R M), F)` is a finitely generated `R`-module for every `q ≥ 0` (properness is
   essential; see `TauCeti.Examples.AlgebraicGeometry.Cohomology.Finiteness`).
2. **Serre's vanishing theorem**
   (`TauCeti.SymmetricAlgebra.exists_forall_ge_subsingleton_cohomology_tensor_twistingSheaf`):
   some `m₀ : ℤ` gives `H^q(Proj (Sym_R M), F ⊗ 𝒪(m)) = 0` for all `m ≥ m₀` and `q > 0`.

For general projective schemes over `R`, see `TauCeti.AlgebraicGeometry.Cohomology.Projective`.
The proof descends on `q` from Čech vanishing on `Proj (Sym_R R^{r+2})` via a short exact sequence
`0 ⟶ K ⟶ ⨁_{Fin k} 𝒪(-n₀) ⟶ F ⟶ 0`, then transfers to `Proj (Sym_R M)` along a closed immersion
induced by a surjection `R^{r+2} ↠ M`.

## References

* J.-P. Serre, *Faisceaux algébriques cohérents*, Ann. of Math. (2) **61** (1955), §66.
* A. Grothendieck, *EGA III₁*, Publ. Math. IHÉS **11** (1961), Theorem 2.2.1.
* R. Hartshorne, *Algebraic Geometry*, GTM 52, Springer, 1977, Theorem III.5.2.
* [The Stacks Project, Tag 01YS](https://stacks.math.columbia.edu/tag/01YS),
  [Tag 0B5T](https://stacks.math.columbia.edu/tag/0B5T), and
  [Tag 02O6](https://stacks.math.columbia.edu/tag/02O6).
-/

public section

open CategoryTheory Limits MonoidalCategory AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme.Modules

universe u

namespace Module.Basis

open TauCeti.SymmetricAlgebra

variable {R P : Type u} [CommRing R] [AddCommMonoid P] [Module R P]

local notation "𝒜" => homogeneousSubmodule R P
local notation "𝒪(" m ")" => (Proj.twistingSheaf 𝒜 m : Scheme.Modules (Proj 𝒜))

private theorem exists_shortExact_biproduct_twistingSheaf [IsNoetherianRing R] [Module.Finite R P]
    (F : (Proj 𝒜).Modules) [F.IsQuasicoherent] [F.IsFiniteType] :
    ∃ (n₀ k : ℕ) (p : (⨁ fun _ : Fin k ↦ 𝒪(-(n₀ : ℤ))) ⟶ F),
      (ShortComplex.mk (kernel.ι p) p (kernel.condition p)).ShortExact ∧
      (kernel p).IsQuasicoherent ∧ (kernel p).IsFiniteType := by
  obtain ⟨n₀, hn₀⟩ := exists_forall_ge_epi_biproduct_twistingSheaf R P F
  obtain ⟨k, p, hp⟩ := hn₀ n₀ le_rfl
  exact ⟨n₀, k, p,
    ShortComplex.ShortExact.mk' (ShortComplex.exact_kernel p) inferInstance inferInstance,
    inferInstance, inferInstance⟩

private theorem finite_cohomology_proj_aux [IsNoetherianRing R] {κ : Type*} [Fintype κ]
    [Nontrivial κ] (b : Module.Basis κ R P) :
    ∀ (d : ℕ) (F : (Proj 𝒜).Modules) [F.IsQuasicoherent] [F.IsFiniteType] (q : ℕ),
      Fintype.card κ - d ≤ q → Module.Finite R (Cohomology F q)
  | 0, F, _, _, q, hq => by
    have := b.subsingleton_cohomology_proj_of_card_le F q (by simpa using hq)
    infer_instance
  | d + 1, F, _, _, q, hq => by
    have : Module.Finite R P := Module.Finite.of_basis b
    obtain ⟨n₀, k, p, hS, _, _⟩ := exists_shortExact_biproduct_twistingSheaf F
    have : ∀ _ : Fin k, Module.Finite R (Cohomology 𝒪(-(n₀ : ℤ)) q) :=
      fun _ ↦ b.finite_cohomology_twistingSheaf (-(n₀ : ℤ)) q
    have : Module.Finite R (Cohomology (kernel p) (q + 1)) :=
      finite_cohomology_proj_aux b d (kernel p) (q + 1) (by omega)
    exact Module.Finite.of_exact_of_isNoetherian
      (exact_cohomologyMapBaseLinear_cohomologyδBaseLinear R (Proj 𝒜) hS q)

private theorem subsingleton_cohomology_biproduct_twistingSheaf_tensor {κ : Type*} [Fintype κ]
    (b : Module.Basis κ R P) (k : ℕ) (n m : ℤ) (hm : -(Fintype.card κ : ℤ) < -n + m)
    {q : ℕ} (hq : 0 < q) :
    Subsingleton (Cohomology ((⨁ fun _ : Fin k ↦ 𝒪(-n)) ⊗ 𝒪(m)) q) := by
  let e : (⨁ fun _ : Fin k ↦ 𝒪(-n)) ⊗ 𝒪(m) ≅ ⨁ fun _ : Fin k ↦ 𝒪(-n + m) :=
    (tensorRight 𝒪(m)).mapBiproduct _ ≪≫ biproduct.mapIso fun _ ↦ twistingSheafTensorIso (-n) m
  have : ∀ _ : Fin k, Subsingleton (Cohomology 𝒪(-n + m) q) :=
    fun _ ↦ b.subsingleton_cohomology_twistingSheaf_of_neg_card_lt hm hq
  have := (cohomologyBiproductLinearEquiv R (fun _ : Fin k ↦ 𝒪(-n + m)) q).subsingleton
  exact subsingleton_cohomology_of_iso e q

private theorem exists_forall_ge_subsingleton_cohomology_tensor_twistingSheaf_aux
    [IsNoetherianRing R] {κ : Type*} [Fintype κ] [Nonempty κ] (b : Module.Basis κ R P) :
    ∀ (d : ℕ) (F : (Proj 𝒜).Modules) [F.IsQuasicoherent] [F.IsFiniteType],
      ∃ m₀ : ℤ, ∀ m ≥ m₀, ∀ q ≥ Fintype.card κ - d, 0 < q → Subsingleton (Cohomology (F ⊗ 𝒪(m)) q)
  | 0, F, _, _ =>
    ⟨0, fun m _ q hq _ ↦ b.subsingleton_cohomology_proj_of_card_le (F ⊗ 𝒪(m)) q (by simpa using hq)⟩
  | d + 1, F, _, _ => by
    have : Module.Finite R P := Module.Finite.of_basis b
    obtain ⟨n₀, k, p, hS, _, _⟩ := exists_shortExact_biproduct_twistingSheaf F
    obtain ⟨m₁, hm₁⟩ :=
      exists_forall_ge_subsingleton_cohomology_tensor_twistingSheaf_aux b d (kernel p)
    refine ⟨max m₁ ((n₀ : ℤ) - Fintype.card κ + 1), fun m hm q hqd hq ↦ ?_⟩
    have hm_card : -(Fintype.card κ : ℤ) < -(n₀ : ℤ) + m := by
      have := le_of_max_le_right hm; omega
    exact subsingleton_cohomology_X₃ (hS.map_of_exact (tensorRight 𝒪(m))) q (q + 1) rfl
      (subsingleton_cohomology_biproduct_twistingSheaf_tensor b k n₀ m hm_card hq)
      (hm₁ m (le_of_max_le_left hm) (q + 1) (by omega) (Nat.succ_pos q))

end Module.Basis

namespace TauCeti.SymmetricAlgebra

variable (R M : Type u) [CommRing R] [AddCommMonoid M] [Module R M]

private theorem exists_surjective_pi_fin_add_two [Module.Finite R M] :
    ∃ (r : ℕ) (φ : (Fin (r + 2) → R) →ₗ[R] M), Function.Surjective φ := by
  obtain ⟨r, φ₀, hφ₀⟩ := Module.Finite.exists_fin' R M
  exact ⟨r, φ₀.comp (LinearMap.funLeft R R (Fin.castAdd 2)),
    hφ₀.comp (Fin.castAdd_injective r 2).surjective_comp_right⟩

/-- **Serre's finiteness theorem on `Proj (Sym_R M)`.** Over a Noetherian ring `R`, for any finite
`R`-module `M` and quasi-coherent `F` of finite type on `Proj (Sym_R M)`, `H^q(Proj (Sym_R M), F)`
is a finitely generated `R`-module in every degree `q`. -/
theorem finite_cohomology_proj [IsNoetherianRing R] [Module.Finite R M]
    (F : (Proj (homogeneousSubmodule R M)).Modules) [F.IsQuasicoherent] [F.IsFiniteType]
    (q : ℕ) : Module.Finite R (Cohomology F q) := by
  obtain ⟨r, φ, hφ⟩ := exists_surjective_pi_fin_add_two R M
  let g := Proj.mapSymmetricAlgebraOfSurjective φ hφ
  exact (g.moduleFinite_cohomology_pushforward_iff R F q).mp
    (Module.Basis.finite_cohomology_proj_aux (Pi.basisFun R (Fin (r + 2))) (r + 2)
      ((pushforward g).obj F) q (by simp))

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
  obtain ⟨r, φ, hφ⟩ := exists_surjective_pi_fin_add_two R M
  let g := Proj.mapSymmetricAlgebraOfSurjective φ hφ
  obtain ⟨m₀, hm₀⟩ :=
    Module.Basis.exists_forall_ge_subsingleton_cohomology_tensor_twistingSheaf_aux
      (Pi.basisFun R (Fin (r + 2))) (r + 2) ((pushforward g).obj F)
  exact ⟨m₀, fun m hm q hq ↦ (subsingleton_cohomology_congr
      ((tensorLeft F).mapIso (Proj.pullbackTwistingSheafMapSymmetricAlgebraIso φ hφ m)).symm q).mpr
    ((g.subsingleton_cohomology_pushforward_tensor_iff_of_isInvertible F _ q).mp
      (hm₀ m hm q (by simp) hq))⟩

end TauCeti.SymmetricAlgebra
