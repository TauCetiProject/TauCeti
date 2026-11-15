/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Cohomology.Biproduct
public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.ProjectiveOver
public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.TwistingSheaf.Pullback
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import Mathlib.LinearAlgebra.StdBasis
import TauCeti.AlgebraicGeometry.Cohomology.ClosedImmersion.Linear
import TauCeti.AlgebraicGeometry.Cohomology.LongExactSequence
import TauCeti.AlgebraicGeometry.Cohomology.ProjectiveSpace.HigherCohomology
import TauCeti.AlgebraicGeometry.Cohomology.ProjectiveSpace.Vanishing
import TauCeti.AlgebraicGeometry.LineBundle.Dual
import TauCeti.AlgebraicGeometry.Modules.FinitePresentation.Abelian
import TauCeti.AlgebraicGeometry.Modules.Quasicoherent.Pushforward.Finite
import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.TwistingSheaf.Presentation
import TauCeti.AlgebraicGeometry.VectorBundle.ProjectionFormula
import TauCeti.RingTheory.Finiteness.Finsupp

/-!
# Serre's finiteness and vanishing theorems for projective schemes

Let `R` be a Noetherian commutative ring and `X` a scheme projective over `R`
(`AlgebraicGeometry.Scheme.IsProjectiveOver R X`). For every quasi-coherent `𝒪_X`-module `F` of
finite type (equivalently, coherent on the locally Noetherian scheme `X`):

1. **Serre's finiteness theorem** (`AlgebraicGeometry.Scheme.IsProjectiveOver.finite_cohomology`):
   the cohomology `H^q(X, F)` is a finitely generated `R`-module in every degree `q ≥ 0`.
2. **Serre's vanishing theorem**
   (`TauCeti.SymmetricAlgebra.exists_forall_ge_subsingleton_cohomology_tensor_twistingSheaf` and
   `Scheme.Hom.exists_forall_ge_subsingleton_cohomology_tensor_pullback_twistingSheaf`):
   for a closed immersion `i : X ⟶ Proj (Sym_R M)` with `M` finite over `R`, there exists `m₀ : ℤ`
   such that `H^q(X, F ⊗ i^* 𝒪(m)) = 0` for all `m ≥ m₀` and all `q > 0`.

Properness is essential; see `TauCeti.Examples.AlgebraicGeometry.Cohomology.Finiteness` for the
failure of `H⁰` finiteness on the affine line `Spec R[t]`.

## Proof outline

First suppose `P` is a finite free `R`-module with a basis indexed by a nontrivial finite type `κ`,
so `Proj (Sym_R P)` is projective space of positive relative dimension `n = card κ - 1`. By
Grothendieck–Čech vanishing above the cover size
(`Module.Basis.subsingleton_cohomology_proj_of_card_le`), `H^q(Proj (Sym_R P), F) = 0` for all
`q ≥ card κ` and every quasi-coherent sheaf `F`. Descending from `q = card κ` to `q = 0`, Serre's
quotient presentation (`TauCeti.SymmetricAlgebra.exists_forall_ge_epi_biproduct_twistingSheaf`)
writes `F` in a short exact sequence

`0 ⟶ K ⟶ ⨁_{Fin k} 𝒪(-d) ⟶ F ⟶ 0`.

Since `Proj (Sym_R P)` is Noetherian, the kernel `K` is finitely presented
(`AlgebraicGeometry.Scheme.Modules.isFinitePresentation_kernel`), hence quasi-coherent of finite
type. In the long exact cohomology sequence over `R`, `H^q(⨁ 𝒪(-d))` is finite by the explicit
Laurent computation (`Module.Basis.finite_cohomology_twistingSheaf`) and `H^{q+1}(K)` is finite by
the descending induction hypothesis; over the Noetherian ring `R`, any `R`-module squeezed in an
exact sequence between two finite `R`-modules is finite
(`Module.Finite.of_exact_of_isNoetherianRing`). Twisting the same short exact sequence by
`𝒪(m)` (an exact operation since `𝒪(m)` is invertible) and inducting downward from `card κ` gives
Serre's vanishing theorem
(`Module.Basis.exists_forall_ge_subsingleton_cohomology_tensor_twistingSheaf`), using
`H^q(𝒪(m - d)) = 0` for `q > 0` once `m - d > -card κ`
(`Module.Basis.subsingleton_cohomology_twistingSheaf_of_neg_card_lt`).

Finally, any finite `R`-module `M` is a quotient of `R^{r+2}`, giving a closed immersion over
`Spec R` from `Proj (Sym_R M)` into `Proj (Sym_R R^{r+2})`
(`AlgebraicGeometry.Proj.mapSymmetricAlgebraOfSurjective`) along which `𝒪(m)` pulls back to `𝒪(m)`
(`AlgebraicGeometry.Proj.pullbackTwistingSheafMapSymmetricAlgebraIso`). Pushing forward coherent
sheaves along closed immersions preserves coherence
(`AlgebraicGeometry.Scheme.Modules.isFinitePresentation_pushforward_of_isFinite`), preserves
cohomology `R`-linearly (`AlgebraicGeometry.Scheme.Hom.cohomologyPushforwardBaseLinearEquiv`), and
satisfies the projection formula
(`TauCeti.AlgebraicGeometry.FiniteLocallyFreeSheaf.pushforwardTensorRightIso`), transferring both
finiteness and vanishing to arbitrary closed subschemes of `Proj (Sym_R M)`.

## References

* J.-P. Serre, *Faisceaux algébriques cohérents*, Ann. of Math. (2) **61** (1955), §66, Theorem 1
  and Theorem 2.
* A. Grothendieck, *Éléments de géométrie algébrique. III. Première partie*, Publ. Math. IHÉS
  **11** (1961), Theorem 2.2.1.
* R. Hartshorne, *Algebraic Geometry*, GTM 52, Springer, 1977, Theorem III.5.2.
* [The Stacks Project, Tag 01XT](https://stacks.math.columbia.edu/tag/01XT) and
  [Tag 02O6](https://stacks.math.columbia.edu/tag/02O6).
-/

public section

noncomputable section

open CategoryTheory Limits MonoidalCategory AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme.Modules

universe u

/-! ### Cohomology finiteness and Serre vanishing on projective space -/

namespace Module.Basis

open TauCeti.SymmetricAlgebra

variable {R P : Type u} [CommRing R] [AddCommMonoid P] [Module R P]

local notation "𝒜" => homogeneousSubmodule R P

/-- Auxiliary descending induction for `finite_cohomology_proj`: for `d : ℕ`, every quasi-coherent
module `F` of finite type on `Proj (Sym_R P)` has finite cohomology in all degrees
`q ≥ card κ - d`. -/
private theorem finite_cohomology_proj_aux [IsNoetherianRing R] {κ : Type*} [Fintype κ]
    [Nontrivial κ] (b : Module.Basis κ R P) :
    ∀ (d : ℕ) (F : (Proj 𝒜).Modules) [F.IsQuasicoherent] [F.IsFiniteType] (q : ℕ),
      Fintype.card κ - d ≤ q → Module.Finite R (Cohomology F q)
  | 0, F, _, _, q, hq => by
    have : Nonempty κ := inferInstance
    have := b.subsingleton_cohomology_proj_of_card_le F q (by simpa using hq)
    infer_instance
  | d + 1, F, _, _, q, hq => by
    have : Module.Finite R P := Module.Finite.of_basis b
    obtain ⟨n₀, hn₀⟩ := exists_forall_ge_epi_biproduct_twistingSheaf R P F
    obtain ⟨k, p, hp⟩ := hn₀ n₀ le_rfl
    have hS : (ShortComplex.kernelSequence p).ShortExact :=
      ShortComplex.ShortExact.mk' (ShortComplex.exact_kernel p) inferInstance inferInstance
    have : ∀ _ : Fin k, Module.Finite R
        (Cohomology (Proj.twistingSheaf 𝒜 (-(n₀ : ℤ)) : (Proj 𝒜).Modules) q) :=
      fun _ ↦ b.finite_cohomology_twistingSheaf (-(n₀ : ℤ)) q
    have : Module.Finite R (Cohomology (ShortComplex.kernelSequence p).X₂ q) := by
      -- `X₂` of `kernelSequence p` is the biproduct `⨁_{Fin k} 𝒪(-n₀)`
      change Module.Finite R
        (Cohomology (⨁ fun _ : Fin k ↦ (Proj.twistingSheaf 𝒜 (-(n₀ : ℤ)) : (Proj 𝒜).Modules)) q)
      infer_instance
    -- `X₁` of `kernelSequence p` is `kernel p` by definition
    have : Module.Finite R (Cohomology (ShortComplex.kernelSequence p).X₁ (q + 1)) :=
      finite_cohomology_proj_aux b d (kernel p) (q + 1) (by omega)
    exact Module.Finite.of_exact_of_isNoetherianRing
      (exact_cohomologyMapBaseLinear_cohomologyδBaseLinear R (Proj 𝒜) hS q)

/-- **Serre's finiteness theorem on projective space.** Let `P` be a free `R`-module over a
Noetherian ring `R` with a finite basis of at least two elements. For every quasi-coherent module
`F` of finite type on `Proj (Sym_R P)` and every `q : ℕ`, the cohomology `H^q(Proj (Sym_R P), F)`
is a finitely generated `R`-module. -/
theorem finite_cohomology_proj [IsNoetherianRing R] {κ : Type*} [Finite κ] [Nontrivial κ]
    (b : Module.Basis κ R P) (F : (Proj 𝒜).Modules) [F.IsQuasicoherent] [F.IsFiniteType]
    (q : ℕ) : Module.Finite R (Cohomology F q) := by
  have := Fintype.ofFinite κ
  exact finite_cohomology_proj_aux b (Fintype.card κ) F q (by simp)

/-- On projective space `Proj (Sym_R P)`, a finite biproduct of copies of `𝒪(-n)` twisted by
`𝒪(m)` has vanishing positive cohomology once `m - n > -card κ`. -/
private theorem subsingleton_cohomology_biproduct_twistingSheaf_tensor {κ : Type*} [Fintype κ]
    (b : Module.Basis κ R P) (k : ℕ) (n m : ℤ) (hm : -(Fintype.card κ : ℤ) < -n + m)
    {q : ℕ} (hq : 0 < q) :
    Subsingleton (Cohomology
      ((⨁ fun _ : Fin k ↦ (Proj.twistingSheaf 𝒜 (-n) : (Proj 𝒜).Modules)) ⊗
        (Proj.twistingSheaf 𝒜 m : (Proj 𝒜).Modules)) q) := by
  let L : (Proj 𝒜).Modules := Proj.twistingSheaf 𝒜 m
  let G : Fin k → (Proj 𝒜).Modules := fun _ ↦ Proj.twistingSheaf 𝒜 (-n)
  let e : (⨁ G) ⊗ L ≅ ⨁ fun _ : Fin k ↦ (Proj.twistingSheaf 𝒜 (-n + m) : (Proj 𝒜).Modules) :=
    (tensorRight L).mapBiproduct G ≪≫
      biproduct.mapIso fun _ ↦ twistingSheafTensorIso (-n) m
  have : ∀ _ : Fin k, Subsingleton (Cohomology (Proj.twistingSheaf 𝒜 (-n + m)) q) :=
    fun _ ↦ b.subsingleton_cohomology_twistingSheaf_of_neg_card_lt hm hq
  have : Subsingleton (Cohomology
      (⨁ fun _ : Fin k ↦ (Proj.twistingSheaf 𝒜 (-n + m) : (Proj 𝒜).Modules)) q) :=
    (cohomologyBiproductLinearEquiv R
      (fun _ : Fin k ↦ (Proj.twistingSheaf 𝒜 (-n + m) : (Proj 𝒜).Modules)) q).subsingleton
  exact subsingleton_cohomology_of_iso e q

/-- Auxiliary descending induction for Serre vanishing on projective space: for `d : ℕ` and any
quasi-coherent `F` of finite type on `Proj (Sym_R P)`, some twist threshold `m₀` kills `H^q(F(m))`
simultaneously for all `m ≥ m₀` and all positive degrees `q ≥ card κ - d`. -/
private theorem exists_forall_ge_subsingleton_cohomology_tensor_twistingSheaf_aux
    [IsNoetherianRing R] {κ : Type*} [Fintype κ] [Nonempty κ] (b : Module.Basis κ R P) :
    ∀ (d : ℕ) (F : (Proj 𝒜).Modules) [F.IsQuasicoherent] [F.IsFiniteType],
      ∃ m₀ : ℤ, ∀ m ≥ m₀, ∀ q ≥ Fintype.card κ - d, 0 < q →
        Subsingleton (Cohomology (F ⊗ (Proj.twistingSheaf 𝒜 m : (Proj 𝒜).Modules)) q)
  | 0, F, _, _ =>
    ⟨0, fun m _ q hq _ ↦
      b.subsingleton_cohomology_proj_of_card_le
        (F ⊗ (Proj.twistingSheaf 𝒜 m : (Proj 𝒜).Modules)) q (by simpa using hq)⟩
  | d + 1, F, _, _ => by
    have : Module.Finite R P := Module.Finite.of_basis b
    obtain ⟨n₀, hn₀⟩ := exists_forall_ge_epi_biproduct_twistingSheaf R P F
    obtain ⟨k, p, hp⟩ := hn₀ n₀ le_rfl
    have hS : (ShortComplex.kernelSequence p).ShortExact :=
      ShortComplex.ShortExact.mk' (ShortComplex.exact_kernel p) inferInstance inferInstance
    obtain ⟨m₁, hm₁⟩ :=
      exists_forall_ge_subsingleton_cohomology_tensor_twistingSheaf_aux b d (kernel p)
    refine ⟨max m₁ ((n₀ : ℤ) - Fintype.card κ + 1), fun m hm q hqd hq ↦ ?_⟩
    have hm_ge₁ : m₁ ≤ m := le_of_max_le_left hm
    have hm_card : -(Fintype.card κ : ℤ) < -(n₀ : ℤ) + m := by
      have : (n₀ : ℤ) - Fintype.card κ + 1 ≤ m := le_of_max_le_right hm
      omega
    let L : (Proj 𝒜).Modules := Proj.twistingSheaf 𝒜 m
    have hSm : ((ShortComplex.kernelSequence p).map (tensorRight L)).ShortExact :=
      hS.map_of_exact (tensorRight L)
    have hX₂ : Subsingleton
        (Cohomology ((ShortComplex.kernelSequence p).map (tensorRight L)).X₂ q) :=
      subsingleton_cohomology_biproduct_twistingSheaf_tensor b k n₀ m hm_card hq
    have hX₁ : Subsingleton
        (Cohomology ((ShortComplex.kernelSequence p).map (tensorRight L)).X₁ (q + 1)) :=
      hm₁ m hm_ge₁ (q + 1) (by omega) (Nat.succ_pos q)
    exact subsingleton_cohomology_X₃ hSm q (q + 1) rfl hX₂ hX₁

/-- **Serre's vanishing theorem on projective space.** Let `P` be a free `R`-module over a
Noetherian ring `R` with a nonempty finite basis. For every quasi-coherent module `F` of finite
type on `Proj (Sym_R P)`, there exists `m₀ : ℤ` such that
`H^q(Proj (Sym_R P), F ⊗ 𝒪(m)) = 0` for all `m ≥ m₀` and all `q > 0`. -/
theorem exists_forall_ge_subsingleton_cohomology_tensor_twistingSheaf [IsNoetherianRing R]
    {κ : Type*} [Finite κ] [Nonempty κ] (b : Module.Basis κ R P)
    (F : (Proj 𝒜).Modules) [F.IsQuasicoherent] [F.IsFiniteType] :
    ∃ m₀ : ℤ, ∀ m ≥ m₀, ∀ q > 0,
      Subsingleton (Cohomology (F ⊗ (Proj.twistingSheaf 𝒜 m : (Proj 𝒜).Modules)) q) := by
  have := Fintype.ofFinite κ
  obtain ⟨m₀, hm₀⟩ :=
    exists_forall_ge_subsingleton_cohomology_tensor_twistingSheaf_aux b (Fintype.card κ) F
  exact ⟨m₀, fun m hm q hq ↦ hm₀ m hm q (by simp) hq⟩

end Module.Basis

/-! ### Reduction from `Proj (Sym_R M)` and projective schemes over `R` to projective space -/

/-- Transfer vanishing of `H^q(Proj (Sym_R P), (i_* F) ⊗ 𝒪(m))` to `H^q(X, F ⊗ i^* 𝒪(m))` along a
closed immersion `i : X ⟶ Proj (Sym_R P)` via the projection formula and closed-immersion
cohomology invariance. -/
private theorem subsingleton_cohomology_tensor_pullback_twistingSheaf
    {R P : Type u} [CommRing R] [AddCommMonoid P] [Module R P] {X : Scheme.{u}}
    (i : X ⟶ Proj (TauCeti.SymmetricAlgebra.homogeneousSubmodule R P)) [IsClosedImmersion i]
    (F : X.Modules) (m : ℤ) (q : ℕ)
    (h : Subsingleton (Cohomology ((pushforward i).obj F ⊗
      (Proj.twistingSheaf (TauCeti.SymmetricAlgebra.homogeneousSubmodule R P) m :
        (Proj (TauCeti.SymmetricAlgebra.homogeneousSubmodule R P)).Modules)) q)) :
    Subsingleton (Cohomology (F ⊗ (Scheme.Modules.pullback i).obj
      (Proj.twistingSheaf (TauCeti.SymmetricAlgebra.homogeneousSubmodule R P) m :
        (Proj (TauCeti.SymmetricAlgebra.homogeneousSubmodule R P)).Modules)) q) :=
  let E : FiniteLocallyFreeSheaf (Proj (TauCeti.SymmetricAlgebra.homogeneousSubmodule R P)) :=
    (InvertibleSheaf.toFiniteLocallyFree _).obj
      ⟨Proj.twistingSheaf (TauCeti.SymmetricAlgebra.homogeneousSubmodule R P) m, inferInstance⟩
  (i.subsingleton_cohomology_pushforward_iff _ q).mp
    ((subsingleton_cohomology_congr
      (FiniteLocallyFreeSheaf.pushforwardTensorRightIso i E F) q).mp h)

namespace TauCeti.SymmetricAlgebra

variable (R M : Type u) [CommRing R] [AddCommMonoid M] [Module R M]

/-- Every finite `R`-module is a surjective linear image of `Fin (r + 2) → R` for some `r : ℕ`,
ensuring the free cover has rank at least `2` (so its projective spectrum has positive relative
dimension even when `M` is cyclic or zero). -/
private theorem exists_surjective_pi_fin_add_two [Module.Finite R M] :
    ∃ (r : ℕ) (φ : (Fin (r + 2) → R) →ₗ[R] M), Function.Surjective φ := by
  obtain ⟨r, φ₀, hφ₀⟩ := Module.Finite.exists_fin' R M
  let π : (Fin (r + 2) → R) →ₗ[R] (Fin r → R) :=
    { toFun := fun v i ↦ v (Fin.castAdd 2 i)
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  have hπ : Function.Surjective π := fun w ↦
    ⟨fun j ↦ if hj : j.1 < r then w ⟨j.1, hj⟩ else 0,
      funext fun i ↦ by simp [π, i.isLt]⟩
  exact ⟨r, φ₀.comp π, hφ₀.comp hπ⟩

/-- **Serre's finiteness theorem on `Proj (Sym_R M)`.** Over a Noetherian ring `R`, for any finite
`R`-module `M` (not assumed free or projective) and any quasi-coherent module `F` of finite type
on `Proj (Sym_R M)`, the cohomology `H^q(Proj (Sym_R M), F)` is a finitely generated `R`-module in
every degree `q`. -/
theorem finite_cohomology_proj [IsNoetherianRing R] [Module.Finite R M]
    (F : (Proj (homogeneousSubmodule R M)).Modules) [F.IsQuasicoherent] [F.IsFiniteType]
    (q : ℕ) : Module.Finite R (Cohomology F q) := by
  obtain ⟨r, φ, hφ⟩ := exists_surjective_pi_fin_add_two R M
  let g := Proj.mapSymmetricAlgebraOfSurjective φ hφ
  have : Module.Finite R (Cohomology ((pushforward g).obj F) q) :=
    (Pi.basisFun R (Fin (r + 2))).finite_cohomology_proj ((pushforward g).obj F) q
  exact (g.moduleFinite_cohomology_pushforward_iff R F q).mp this

/-- **Serre's vanishing theorem on `Proj (Sym_R M)`** (Hartshorne, Theorem III.5.2(b); Stacks Tag
01XT): over a Noetherian ring `R`, for any finite `R`-module `M` and any quasi-coherent module `F`
of finite type on `Proj (Sym_R M)`, there exists `m₀ : ℤ` such that
`H^q(Proj (Sym_R M), F ⊗ 𝒪(m)) = 0` for all `m ≥ m₀` and all `q > 0`. -/
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
    (Pi.basisFun R (Fin (r + 2))).exists_forall_ge_subsingleton_cohomology_tensor_twistingSheaf
      ((pushforward g).obj F)
  refine ⟨m₀, fun m hm q hq ↦ ?_⟩
  exact (subsingleton_cohomology_congr
      ((tensorLeft F).mapIso (Proj.pullbackTwistingSheafMapSymmetricAlgebraIso φ hφ m)).symm q).mpr
    (subsingleton_cohomology_tensor_pullback_twistingSheaf g F m q (hm₀ m hm q hq))

end TauCeti.SymmetricAlgebra

namespace AlgebraicGeometry.Scheme

open TauCeti.SymmetricAlgebra

/-- **Serre's finiteness theorem for projective schemes** (Hartshorne, Theorem III.5.2(a); Stacks
Tag 02O6): if `X` is a projective scheme over a Noetherian ring `R`, then for every quasi-coherent
`𝒪_X`-module `F` of finite type and every `q : ℕ`, the cohomology `H^q(X, F)` is a finitely
generated `R`-module. -/
instance IsProjectiveOver.finite_cohomology (R : Type u) [CommRing R] [IsNoetherianRing R]
    {X : Scheme.{u}} [X.Over (Spec (.of R))] [X.IsProjectiveOver R]
    (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType] (q : ℕ) :
    Module.Finite R (Cohomology F q) := by
  obtain ⟨M, _, _, _, i, hi, hiR⟩ := IsProjectiveOver.exists_isClosedImmersion (R := R) (X := X)
  have : Module.Finite R (Cohomology ((pushforward i).obj F) q) :=
    TauCeti.SymmetricAlgebra.finite_cohomology_proj R M ((pushforward i).obj F) q
  exact (i.moduleFinite_cohomology_pushforward_iff R F q).mp this

/-- **Serre's vanishing theorem on closed subschemes of `Proj (Sym_R M)`** (Hartshorne, Theorem
III.5.2(b)): for a closed immersion `i : X ⟶ Proj (Sym_R M)` with `R` Noetherian and `M` finite
over `R`, and any quasi-coherent `𝒪_X`-module `F` of finite type, there exists `m₀ : ℤ` such that
`H^q(X, F ⊗ i^* 𝒪(m)) = 0` for all `m ≥ m₀` and all `q > 0`. -/
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
    subsingleton_cohomology_tensor_pullback_twistingSheaf i F m q (hm₀ m hm q hq)⟩

end AlgebraicGeometry.Scheme

end
