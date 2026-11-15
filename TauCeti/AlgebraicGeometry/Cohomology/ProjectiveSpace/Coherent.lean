/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Cohomology.Biproduct
public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.ProjectiveOver
public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.TwistingSheaf.Pullback
public import TauCeti.AlgebraicGeometry.VectorBundle.ProjectionFormula
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import Mathlib.LinearAlgebra.StdBasis
import TauCeti.AlgebraicGeometry.Cohomology.ClosedImmersion.Linear
import TauCeti.AlgebraicGeometry.Cohomology.LongExactSequence
import TauCeti.AlgebraicGeometry.Cohomology.ProjectiveSpace.HigherCohomology
import TauCeti.AlgebraicGeometry.Cohomology.ProjectiveSpace.Vanishing
import TauCeti.AlgebraicGeometry.LineBundle.Dual
import TauCeti.AlgebraicGeometry.Modules.FinitePresentation.Abelian
import TauCeti.AlgebraicGeometry.Modules.Quasicoherent.Pushforward.Finite
import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.BaseChange
import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.ClosedImmersion
import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.TwistingSheaf.Presentation

/-!
# Serre's finiteness and vanishing theorems for projective schemes

Let `R` be a Noetherian commutative ring and `X` a scheme projective over `R`
(`AlgebraicGeometry.Scheme.IsProjectiveOver R X`). For every quasi-coherent `𝒪_X`-module `F` of
finite type (equivalently, coherent on the locally Noetherian scheme `X`):

1. **Serre's finiteness theorem** (`AlgebraicGeometry.Scheme.IsProjectiveOver.finite_cohomology`):
   the cohomology `H^q(X, F)` is a finitely generated `R`-module in every degree `q ≥ 0`.
2. **Serre's vanishing theorem**
   (`TauCeti.SymmetricAlgebra.exists_forall_ge_subsingleton_cohomology_twistingSheaf` and
   `AlgebraicGeometry.Scheme.Hom.exists_forall_ge_subsingleton_cohomology_pullback_twistingSheaf`):
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
exact sequence between two finite `R`-modules is finite. Twisting the same short exact sequence by
`𝒪(m)` (an exact operation since `𝒪(m)` is invertible) and inducting downward from `card κ` gives
Serre's vanishing theorem, using `H^q(𝒪(m - d)) = 0` for `q > 0` once `m - d > -card κ`
(`Module.Basis.subsingleton_cohomology_twistingSheaf_of_neg_card_lt`).

Finally, any finite `R`-module `M` is a quotient of `R^{r+2}`, giving a closed immersion over
`Spec R` from `Proj (Sym_R M)` into `Proj (Sym_R R^{r+2})` along which `𝒪(m)` pulls back to `𝒪(m)`
(`TauCeti.SymmetricAlgebra.isIso_pullbackTwistingSheafMap`). Pushing forward coherent sheaves along
closed immersions preserves coherence
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

/-! ### Exactness, biproduct, and invertible-sheaf preliminaries -/

/-- Over a Noetherian ring, a module sitting in the middle of an exact sequence between two finite
modules is finite (without assuming the right-hand map is surjective). -/
private theorem finite_of_exact_of_isNoetherianRing {R M₁ M₂ M₃ : Type*} [CommRing R]
    [IsNoetherianRing R] [AddCommGroup M₁] [AddCommGroup M₂] [AddCommGroup M₃]
    [Module R M₁] [Module R M₂] [Module R M₃] {f : M₁ →ₗ[R] M₂} {g : M₂ →ₗ[R] M₃}
    (hfg : Function.Exact f g) [Module.Finite R M₁] [Module.Finite R M₃] :
    Module.Finite R M₂ :=
  Module.Finite.of_exact (f := f) (g := g.rangeRestrict)
    (fun y ↦ Subtype.ext_iff.trans (hfg y)) g.surjective_rangeRestrict

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

/-- An invertible `𝒪_X`-module is finitely presented. -/
instance isFinitePresentation_of_isInvertible (L : X.Modules)
    [TauCeti.SheafOfModules.IsInvertible (R := X.ringCatSheaf) L] :
    L.IsFinitePresentation :=
  ((InvertibleSheaf.toFiniteLocallyFree X).obj ⟨L, inferInstance⟩).property.2

/-- Tensoring on the right by an invertible `𝒪_X`-module is an equivalence of categories, with
quasi-inverse given by tensoring on the right with the dual line bundle. -/
instance isEquivalence_tensorRight_of_isInvertible (L : X.Modules)
    [TauCeti.SheafOfModules.IsInvertible (R := X.ringCatSheaf) L] :
    (tensorRight L).IsEquivalence :=
  let L' : InvertibleSheaf X := ⟨L, inferInstance⟩
  let e : L ⊗ (InvertibleSheaf.dual L').obj ≅ 𝟙_ X.Modules :=
    isoOfSheafIso X
      ((InvertibleSheaf.tensorProductObjIso L' (InvertibleSheaf.dual L')).symm ≪≫
        InvertibleSheaf.tensorDualIsoSheaf L' ≪≫
        InvertibleSheaf.trivialObjIsoUnit X)
  (tensorRightEquivalenceOfIso e (β_ _ _ ≪≫ e)).isEquivalence_functor

/-- A finite biproduct of finitely presented `𝒪_X`-modules is finitely presented. -/
instance isFinitePresentation_biproduct {J : Type*} [Finite J] (F : J → X.Modules)
    [HasBiproduct F] [∀ j, (F j).IsFinitePresentation] :
    (⨁ F).IsFinitePresentation := by
  have := Fintype.ofFinite J
  let e : Fin (Fintype.card J) ≃ J := (Fintype.equivFin J).symm
  let G : Fin (Fintype.card J) → X.Modules := fun i ↦ F (e i)
  exact (SheafOfModules.isFinitePresentation X.ringCatSheaf).prop_of_iso
    ((biproduct.isoProduct G).symm ≪≫
      biproduct.whiskerEquiv (f := G) (g := F) e fun _ ↦ Iso.refl _)
    ((SheafOfModules.isFinitePresentation X.ringCatSheaf).prop_pi G fun i ↦ inferInstance)

/-- A finite biproduct of quasi-coherent `𝒪_X`-modules is quasi-coherent. -/
instance isQuasicoherent_biproduct {J : Type*} [Finite J] (F : J → X.Modules)
    [HasBiproduct F] [∀ j, (F j).IsQuasicoherent] :
    (⨁ F).IsQuasicoherent := by
  classical
  have := Fintype.ofFinite J
  let e : Fin (Fintype.card J) ≃ J := (Fintype.equivFin J).symm
  suffices ∀ (k : ℕ) (G : Fin k → X.Modules) [∀ i, (G i).IsQuasicoherent],
      (⨁ G).IsQuasicoherent from
    (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
      (biproduct.whiskerEquiv (f := fun i ↦ F (e i)) (g := F) e fun _ ↦ Iso.refl _) (this _ _)
  intro k
  induction k with
  | zero =>
    intro G _
    have hZ := TauCeti.SheafOfModules.isZero_free (S := X.ringCatSheaf) PEmpty.{u + 1}
    exact (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
      (hZ.iso (TauCeti.isZero_biproduct_of_isEmpty G)) inferInstance
  | succ k ih =>
    intro G _
    let e' : Option (Fin k) ≃ Fin (k + 1) := (finSuccEquiv k).symm
    have := ih (fun j ↦ G (e' (some j)))
    exact (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
      ((TauCeti.biproductOptionIso (fun j ↦ G (e' j))).symm ≪≫
        biproduct.whiskerEquiv (f := fun j ↦ G (e' j)) (g := G) e' fun _ ↦ Iso.refl _)
      inferInstance

/-- The cohomology of a finite biproduct of `𝒪_X`-modules is finitely generated over the base ring
when the cohomology of each summand is. -/
instance finite_cohomology_biproduct (R : Type u) [CommRing R] [X.Over (Spec (.of R))]
    {J : Type*} [Finite J] (F : J → X.Modules) [HasBiproduct F] (i : ℕ)
    [∀ j, Module.Finite R (Cohomology (F j) i)] :
    Module.Finite R (Cohomology (⨁ F) i) := by
  have := Fintype.ofFinite J
  exact Module.Finite.equiv (cohomologyBiproductLinearEquiv R F i).symm

/-- Isomorphic `𝒪_X`-modules have simultaneously trivial cohomology in degree `q`. -/
private theorem subsingleton_cohomology_of_iso {M N : X.Modules} (e : M ≅ N) (q : ℕ)
    (_ : Subsingleton (Cohomology N q)) : Subsingleton (Cohomology M q) :=
  let i := (cohomologyFunctor X q).mapIso e
  let f : Cohomology M q → Cohomology N q := i.hom
  let g : Cohomology N q → Cohomology M q := i.inv
  have hfg : Function.LeftInverse g f := Iso.hom_inv_id_apply i
  hfg.injective.subsingleton

/-- If `f : X ⟶ Y` is a closed immersion and `H^q(Y, f_* M)` is subsingleton, so is `H^q(X, M)`. -/
private theorem subsingleton_cohomology_of_isClosedImmersion {Y : Scheme.{u}} (f : X ⟶ Y)
    [IsClosedImmersion f] (M : X.Modules) (q : ℕ)
    (_ : Subsingleton (Cohomology ((pushforward f).obj M) q)) :
    Subsingleton (Cohomology M q) :=
  let i := cohomologyPushforwardIso f M q
  let u : Cohomology M q → Cohomology ((pushforward f).obj M) q := i.inv
  let v : Cohomology ((pushforward f).obj M) q → Cohomology M q := i.hom
  have huv : Function.LeftInverse v u := Iso.inv_hom_id_apply i
  huv.injective.subsingleton

end AlgebraicGeometry.Scheme.Modules

namespace TauCeti.AlgebraicGeometry.FiniteLocallyFreeSheaf

open _root_.AlgebraicGeometry

/-- Right-hand form of the projection formula for a finite locally free sheaf `E` on `Y` and any
morphism `f : X ⟶ Y`: `(f_* N) ⊗ E ≅ f_* (N ⊗ f^* E)`. -/
def pushforwardTensorRightIso {X Y : Scheme.{u}} (f : X ⟶ Y) (E : FiniteLocallyFreeSheaf Y)
    (N : X.Modules) :
    (Scheme.Modules.pushforward f).obj N ⊗ E.obj ≅
      (Scheme.Modules.pushforward f).obj (N ⊗ (Scheme.Modules.pullback f).obj E.obj) :=
  β_ _ _ ≪≫ (pushforwardTensorLeftIso f E).app N ≪≫
    (Scheme.Modules.pushforward f).mapIso
      (β_ _ _ ≪≫ (tensorLeft N).mapIso (eqToIso (pullback_obj_obj f E)))

end TauCeti.AlgebraicGeometry.FiniteLocallyFreeSheaf

/-! ### Cohomology finiteness and Serre vanishing on projective space -/

namespace TauCeti.SymmetricAlgebra

section TensorTwistingSheaf

variable {R M : Type u} [CommRing R] [AddCommMonoid M] [Module R M]

/-- On `Proj (Sym_R M)`, the monoidal tensor product of twisting sheaves `𝒪(m) ⊗ 𝒪(n)` in
`(Proj (Sym_R M)).Modules` is isomorphic to `𝒪(m + n)`. -/
def twistingSheafTensorIso (m n : ℤ) :
    (Proj.twistingSheaf (homogeneousSubmodule R M) m : (Proj (homogeneousSubmodule R M)).Modules) ⊗
        (Proj.twistingSheaf (homogeneousSubmodule R M) n :
          (Proj (homogeneousSubmodule R M)).Modules) ≅
      (Proj.twistingSheaf (homogeneousSubmodule R M) (m + n) :
        (Proj (homogeneousSubmodule R M)).Modules) :=
  let Lm : InvertibleSheaf (Proj (homogeneousSubmodule R M)) :=
    ⟨Proj.twistingSheaf (homogeneousSubmodule R M) m, inferInstance⟩
  let Ln : InvertibleSheaf (Proj (homogeneousSubmodule R M)) :=
    ⟨Proj.twistingSheaf (homogeneousSubmodule R M) n, inferInstance⟩
  isoOfSheafIso (Proj (homogeneousSubmodule R M))
    ((InvertibleSheaf.tensorProductObjIso Lm Ln).symm ≪≫
      eqToIso (InvertibleSheaf.tensorProduct_obj Lm Ln) ≪≫
      Proj.twistingSheaf.tensorProductIso (_root_.SymmetricAlgebra.ι R M)
        (ι_mem_homogeneousSubmodule R M) (iSup_basicOpen_ι_eq_top R M id (by simp)) m n)

end TensorTwistingSheaf

end TauCeti.SymmetricAlgebra

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
    have : Module.Finite R (Cohomology (kernel p) (q + 1)) :=
      finite_cohomology_proj_aux b d (kernel p) (q + 1) (by omega)
    have : Module.Finite R (Cohomology (ShortComplex.kernelSequence p).X₁ (q + 1)) := this
    exact finite_of_exact_of_isNoetherianRing
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
  have hsum : Subsingleton (Cohomology
      (⨁ fun _ : Fin k ↦ (Proj.twistingSheaf 𝒜 (-n + m) : (Proj 𝒜).Modules)) q) :=
    (cohomologyBiproductLinearEquiv R
      (fun _ : Fin k ↦ (Proj.twistingSheaf 𝒜 (-n + m) : (Proj 𝒜).Modules)) q).subsingleton
  exact subsingleton_cohomology_of_iso e q hsum

/-- Auxiliary descending induction for Serre vanishing on projective space: for `d : ℕ` and any
quasi-coherent `F` of finite type on `Proj (Sym_R P)`, some twist threshold `m₀` kills `H^q(F(m))`
simultaneously for all `m ≥ m₀` and all positive degrees `q ≥ card κ - d`. -/
private theorem exists_forall_ge_subsingleton_cohomology_twistingSheaf_aux [IsNoetherianRing R]
    {κ : Type*} [Fintype κ] [Nonempty κ] (b : Module.Basis κ R P) :
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
      exists_forall_ge_subsingleton_cohomology_twistingSheaf_aux b d (kernel p)
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
theorem exists_forall_ge_subsingleton_cohomology_twistingSheaf [IsNoetherianRing R]
    {κ : Type*} [Finite κ] [Nonempty κ] (b : Module.Basis κ R P)
    (F : (Proj 𝒜).Modules) [F.IsQuasicoherent] [F.IsFiniteType] :
    ∃ m₀ : ℤ, ∀ m ≥ m₀, ∀ q > 0,
      Subsingleton (Cohomology (F ⊗ (Proj.twistingSheaf 𝒜 m : (Proj 𝒜).Modules)) q) := by
  have := Fintype.ofFinite κ
  obtain ⟨m₀, hm₀⟩ :=
    exists_forall_ge_subsingleton_cohomology_twistingSheaf_aux b (Fintype.card κ) F
  exact ⟨m₀, fun m hm q hq ↦ hm₀ m hm q (by simp) hq⟩

end Module.Basis

/-! ### Reduction from `Proj (Sym_R M)` and projective schemes over `R` to projective space -/

namespace AlgebraicGeometry.Proj

open TauCeti.SymmetricAlgebra

variable {R M P : Type u} [CommRing R] [AddCommMonoid M] [Module R M]
  [AddCommMonoid P] [Module R P]

/-- A surjective `R`-linear map `φ : P →ₗ[R] M` induces a closed immersion of projective spectra
`Proj (Sym_R M) ⟶ Proj (Sym_R P)` over `Spec R`. -/
def mapSymmetricAlgebraOfSurjective (φ : P →ₗ[R] M) (hφ : Function.Surjective φ) :
    Proj (homogeneousSubmodule R M) ⟶ Proj (homogeneousSubmodule R P) :=
  map (SymmetricAlgebra.gradedMap R φ)
    (HomogeneousIdeal.irrelevant_le_map_of_surjective _
      (by
        simpa only [Function.Surjective, SymmetricAlgebra.gradedMap_apply] using
          SymmetricAlgebra.map_surjective R φ hφ))

/-- The projective map associated to a surjective linear map is a closed immersion. -/
instance isClosedImmersion_mapSymmetricAlgebraOfSurjective (φ : P →ₗ[R] M)
    (hφ : Function.Surjective φ) :
    IsClosedImmersion (mapSymmetricAlgebraOfSurjective φ hφ) :=
  isClosedImmersion_map _ _
    (by
      simpa only [Function.Surjective, SymmetricAlgebra.gradedMap_apply] using
        SymmetricAlgebra.map_surjective R φ hφ)

/-- The projective map associated to a surjective linear map commutes with `projToSpec`. -/
@[reassoc (attr := simp)]
theorem mapSymmetricAlgebraOfSurjective_projToSpec (φ : P →ₗ[R] M)
    (hφ : Function.Surjective φ) :
    mapSymmetricAlgebraOfSurjective φ hφ ≫ projToSpec R P = projToSpec R M := by
  rw [mapSymmetricAlgebraOfSurjective, projToSpec_def, projToSpec_def, ← toSpecCoeff_def,
    ← toSpecCoeff_def, map_toSpecCoeff]
  intro r
  apply Subtype.ext
  simp [GradedRingHom.gradedZeroRingHom]

/-- The projective map associated to a surjective linear map is a morphism over `Spec R`. -/
instance isOver_mapSymmetricAlgebraOfSurjective (φ : P →ₗ[R] M)
    (hφ : Function.Surjective φ) :
    (mapSymmetricAlgebraOfSurjective φ hφ).IsOver (Spec (.of R)) where
  comp_over := mapSymmetricAlgebraOfSurjective_projToSpec φ hφ

/-- Along `mapSymmetricAlgebraOfSurjective φ hφ`, the twisting sheaf `𝒪(n)` on `Proj (Sym_R P)`
pulls back isomorphically to `𝒪(n)` on `Proj (Sym_R M)`. -/
def pullbackTwistingSheafMapSymmetricAlgebraIso (φ : P →ₗ[R] M)
    (hφ : Function.Surjective φ) (n : ℤ) :
    (Scheme.Modules.pullback (mapSymmetricAlgebraOfSurjective φ hφ)).obj
        (twistingSheaf (homogeneousSubmodule R P) n) ≅
      twistingSheaf (homogeneousSubmodule R M) n :=
  pullbackTwistingSheafIso (SymmetricAlgebra.gradedMap R φ) _
    (_root_.SymmetricAlgebra.ι R P) (ι_mem_homogeneousSubmodule R P)
    (iSup_basicOpen_ι_eq_top R P id (by simp)) n

end AlgebraicGeometry.Proj

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
theorem exists_forall_ge_subsingleton_cohomology_twistingSheaf [IsNoetherianRing R]
    [Module.Finite R M] (F : (Proj (homogeneousSubmodule R M)).Modules)
    [F.IsQuasicoherent] [F.IsFiniteType] :
    ∃ m₀ : ℤ, ∀ m ≥ m₀, ∀ q > 0,
      Subsingleton (Cohomology
        (F ⊗ (Proj.twistingSheaf (homogeneousSubmodule R M) m :
          (Proj (homogeneousSubmodule R M)).Modules)) q) := by
  obtain ⟨r, φ, hφ⟩ := exists_surjective_pi_fin_add_two R M
  let P := Fin (r + 2) → R
  let g := Proj.mapSymmetricAlgebraOfSurjective φ hφ
  obtain ⟨m₀, hm₀⟩ :=
    (Pi.basisFun R (Fin (r + 2))).exists_forall_ge_subsingleton_cohomology_twistingSheaf
      ((pushforward g).obj F)
  refine ⟨m₀, fun m hm q hq ↦ ?_⟩
  let E : FiniteLocallyFreeSheaf (Proj (homogeneousSubmodule R P)) :=
    (InvertibleSheaf.toFiniteLocallyFree _).obj
      ⟨Proj.twistingSheaf (homogeneousSubmodule R P) m, inferInstance⟩
  let e : (pushforward g).obj F ⊗ E.obj ≅
      (pushforward g).obj
        (F ⊗ (Proj.twistingSheaf (homogeneousSubmodule R M) m :
          (Proj (homogeneousSubmodule R M)).Modules)) :=
    FiniteLocallyFreeSheaf.pushforwardTensorRightIso g E F ≪≫
      (pushforward g).mapIso
        ((tensorLeft F).mapIso (Proj.pullbackTwistingSheafMapSymmetricAlgebraIso φ hφ m))
  have hsub : Subsingleton (Cohomology ((pushforward g).obj F ⊗ E.obj) q) := hm₀ m hm q hq
  have hpush : Subsingleton (Cohomology ((pushforward g).obj
      (F ⊗ (Proj.twistingSheaf (homogeneousSubmodule R M) m :
        (Proj (homogeneousSubmodule R M)).Modules))) q) :=
    subsingleton_cohomology_of_iso e.symm q hsub
  exact subsingleton_cohomology_of_isClosedImmersion g _ q hpush

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
theorem Hom.exists_forall_ge_subsingleton_cohomology_pullback_twistingSheaf
    {R M : Type u} [CommRing R] [IsNoetherianRing R] [AddCommMonoid M] [Module R M]
    [Module.Finite R M] {X : Scheme.{u}} (i : X ⟶ Proj (homogeneousSubmodule R M))
    [IsClosedImmersion i] (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType] :
    ∃ m₀ : ℤ, ∀ m ≥ m₀, ∀ q > 0,
      Subsingleton (Cohomology (F ⊗ (Scheme.Modules.pullback i).obj
        (Proj.twistingSheaf (homogeneousSubmodule R M) m :
          (Proj (homogeneousSubmodule R M)).Modules)) q) := by
  obtain ⟨m₀, hm₀⟩ :=
    TauCeti.SymmetricAlgebra.exists_forall_ge_subsingleton_cohomology_twistingSheaf R M
      ((pushforward i).obj F)
  refine ⟨m₀, fun m hm q hq ↦ ?_⟩
  let E : FiniteLocallyFreeSheaf (Proj (homogeneousSubmodule R M)) :=
    (InvertibleSheaf.toFiniteLocallyFree _).obj
      ⟨Proj.twistingSheaf (homogeneousSubmodule R M) m, inferInstance⟩
  let e : (pushforward i).obj F ⊗ E.obj ≅
      (pushforward i).obj (F ⊗ (Scheme.Modules.pullback i).obj E.obj) :=
    FiniteLocallyFreeSheaf.pushforwardTensorRightIso i E F
  have hsub : Subsingleton (Cohomology ((pushforward i).obj F ⊗ E.obj) q) := hm₀ m hm q hq
  have hpush : Subsingleton
      (Cohomology ((pushforward i).obj (F ⊗ (Scheme.Modules.pullback i).obj E.obj)) q) :=
    subsingleton_cohomology_of_iso e.symm q hsub
  exact subsingleton_cohomology_of_isClosedImmersion i _ q hpush

end AlgebraicGeometry.Scheme

end
