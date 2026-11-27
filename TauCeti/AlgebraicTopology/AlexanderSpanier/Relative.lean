/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.HomologySequence
public import TauCeti.Algebra.Homology.ModuleCat.Basic
public import TauCeti.AlgebraicTopology.AlexanderSpanier.Basic

/-!
# Relative Alexander–Spanier cohomology and the exact sequence of a pair

Let `A` be a subspace of a topological space `X`. Restriction of functions from `X^{n+1}` to
`A^{n+1}` is the cochain map `C^*(X; M) ⟶ C^*(A; M)` induced by the inclusion
(`TauCeti.AlexanderSpanier.restriction`). It is surjective in every degree, since every function on
`A^{n+1}` extends by zero to `X^{n+1}`. Its kernel is the **relative Alexander–Spanier cochain
complex** `C^*(X, A; M)` (`TauCeti.AlexanderSpanier.relativeCochainComplex`): in degree `n` it
consists of the classes of the functions `φ : X^{n+1} → M` whose restriction to `A^{n+1}` is
locally zero on `A` (`TauCeti.AlexanderSpanier.mem_range_relativeCochainComplexι_f_iff`). Its
cohomology is the **relative Alexander–Spanier cohomology** `H^n(X, A; M)`
(`TauCeti.AlexanderSpanier.relativeCohomology`).

The short exact sequence `0 ⟶ C^*(X, A; M) ⟶ C^*(X; M) ⟶ C^*(A; M) ⟶ 0`
(`TauCeti.AlexanderSpanier.shortExact_shortComplex`) gives the connecting morphism
`H^n(A; M) ⟶ H^{n+1}(X, A; M)` (`TauCeti.AlexanderSpanier.connectingHom`), computed on
cocycles by the coboundary of a lift (`TauCeti.AlexanderSpanier.connectingHom_homologyπ`), and the
**long exact sequence of the pair**

`⋯ ⟶ H^n(X, A; M) ⟶ H^n(X; M) ⟶ H^n(A; M) ⟶ H^{n+1}(X, A; M) ⟶ ⋯`,

exact at each of its three kinds of terms
(`TauCeti.AlexanderSpanier.exact_cohomologyMap_subtypeVal`,
`TauCeti.AlexanderSpanier.exact_connectingHom` and
`TauCeti.AlexanderSpanier.exact_relativeCohomologyMap`).

## References

* E. H. Spanier, *Algebraic Topology*, McGraw–Hill, 1966, Chapter 6, Section 6.4.
-/

public section

noncomputable section

open CategoryTheory Limits

universe w u v

namespace TauCeti.AlexanderSpanier

variable (R : Type w) [Ring R] {X : Type u} [TopologicalSpace X] (M : Type v) [AddCommGroup M]
  [Module R M] (A : Set X)

/-- The **restriction** `C^*(X; M) ⟶ C^*(A; M)` of Alexander–Spanier cochains to a subspace `A`:
the pullback along the inclusion `A → X`. -/
abbrev restriction : cochainComplex R X M ⟶ cochainComplex R A M :=
  cochainComplexMap R M (ContinuousMap.subtypeVal A)

variable {R M A} in
/-- Restriction sends the class of `φ` to the class of its restriction to `A^{n+1}`. -/
lemma restriction_f_cochainClass (n : ℕ) (φ : (Fin (n + 1) → X) → M) :
    ((restriction R M A).f n).hom (cochainClass R X M n φ) =
      cochainClass R A M n fun y ↦ φ (Subtype.val ∘ y) :=
  cochainComplexMap_f_cochainClass _ n φ

/-- Restriction of Alexander–Spanier cochains to a subspace is surjective in every degree: a
function on `A^{n+1}` extends by zero to `X^{n+1}`. -/
lemma restriction_f_surjective (n : ℕ) : Function.Surjective ((restriction R M A).f n).hom := by
  classical
  intro c
  obtain ⟨φ, rfl⟩ := cochainClass_surjective n c
  refine ⟨cochainClass R X M n fun y ↦ if h : ∀ i, y i ∈ A then φ fun i ↦ ⟨y i, h i⟩ else 0, ?_⟩
  rw [restriction_f_cochainClass]
  congr 1
  funext y
  simp

instance : Epi (restriction R M A) :=
  HomologicalComplex.epi_of_epi_f _ fun n ↦
    (ModuleCat.epi_iff_surjective _).2 (restriction_f_surjective R M A n)

/-- The **relative Alexander–Spanier cochain complex** `C^*(X, A; M)`: the kernel of the
restriction `C^*(X; M) ⟶ C^*(A; M)`. -/
def relativeCochainComplex : CochainComplex (ModuleCat.{max u v} R) ℕ :=
  kernel (restriction R M A)

/-- The inclusion `C^*(X, A; M) ⟶ C^*(X; M)` of the relative cochains. -/
def relativeCochainComplexι : relativeCochainComplex R M A ⟶ cochainComplex R X M :=
  kernel.ι (restriction R M A)

instance : Mono (relativeCochainComplexι R M A) :=
  inferInstanceAs (Mono (kernel.ι _))

@[reassoc (attr := simp)]
lemma relativeCochainComplexι_comp_restriction :
    relativeCochainComplexι R M A ≫ restriction R M A = 0 :=
  kernel.condition _

/-- The short complex of cochain complexes `C^*(X, A; M) ⟶ C^*(X; M) ⟶ C^*(A; M)`. -/
abbrev shortComplex : ShortComplex (CochainComplex (ModuleCat.{max u v} R) ℕ) :=
  ShortComplex.mk _ _ (relativeCochainComplexι_comp_restriction R M A)

/-- The sequence `0 ⟶ C^*(X, A; M) ⟶ C^*(X; M) ⟶ C^*(A; M) ⟶ 0` is short exact. -/
lemma shortExact_shortComplex : (shortComplex R M A).ShortExact :=
  .mk' (ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel _)) inferInstance inferInstance

/-- In each degree, the relative cochains are exactly the cochains whose restriction to `A`
vanishes. -/
lemma range_relativeCochainComplexι_f (n : ℕ) :
    LinearMap.range ((relativeCochainComplexι R M A).f n).hom =
      LinearMap.ker ((restriction R M A).f n).hom := by
  have h := (HomologicalComplex.shortExact_iff_degreewise_shortExact _).1
    (shortExact_shortComplex R M A) n
  exact ((ShortComplex.moduleCat_exact_iff_range_eq_ker _).1 h.exact)

variable {R M A} in
/-- The class of `φ : X^{n+1} → M` is a relative cochain exactly when the restriction of `φ` to
`A^{n+1}` is locally zero on `A`. -/
lemma mem_range_relativeCochainComplexι_f_iff {n : ℕ} {φ : (Fin (n + 1) → X) → M} :
    cochainClass R X M n φ ∈ LinearMap.range ((relativeCochainComplexι R M A).f n).hom ↔
      IsLocallyZero fun y : Fin (n + 1) → A ↦ φ (Subtype.val ∘ y) := by
  rw [range_relativeCochainComplexι_f, LinearMap.mem_ker, restriction_f_cochainClass,
    cochainClass_eq_zero_iff]

/-- The relative cochain inclusion is injective in every degree. -/
lemma relativeCochainComplexι_f_injective (n : ℕ) :
    Function.Injective ((relativeCochainComplexι R M A).f n).hom :=
  (ModuleCat.mono_iff_injective _).1 inferInstance

/-- **Relative Alexander–Spanier cohomology** `H^n(X, A; M)`. -/
abbrev relativeCohomology (n : ℕ) : ModuleCat.{max u v} R :=
  (relativeCochainComplex R M A).homology n

/-- The map `H^n(X, A; M) ⟶ H^n(X; M)` induced by the inclusion of relative cochains. -/
abbrev relativeCohomologyMap (n : ℕ) : relativeCohomology R M A n ⟶ cohomology R X M n :=
  HomologicalComplex.homologyMap (relativeCochainComplexι R M A) n

/-- The **connecting morphism** `H^n(A; M) ⟶ H^{n+1}(X, A; M)` of the pair `(X, A)`. -/
def connectingHom (n : ℕ) : cohomology R A M n ⟶ relativeCohomology R M A (n + 1) :=
  (shortExact_shortComplex R M A).δ n (n + 1) (by simp)

/-- Restricting to `A` and then applying the connecting morphism is zero. -/
@[reassoc (attr := simp)]
lemma cohomologyMap_subtypeVal_comp_connectingHom (n : ℕ) :
    cohomologyMap R M (ContinuousMap.subtypeVal A) n ≫ connectingHom R M A n = 0 :=
  (shortExact_shortComplex R M A).comp_δ n (n + 1) (by simp)

/-- The connecting morphism followed by the map to `H^{n+1}(X; M)` is zero. -/
@[reassoc (attr := simp)]
lemma connectingHom_comp_relativeCohomologyMap (n : ℕ) :
    connectingHom R M A n ≫ relativeCohomologyMap R M A (n + 1) = 0 :=
  (shortExact_shortComplex R M A).δ_comp n (n + 1) (by simp)

variable {R M A} in
/-- The **connecting morphism on cocycles**. Let `z` be an `n`-cocycle on `A`, `x` an `n`-cochain on
`X` restricting to `z` (for instance an extension by zero, see `restriction_f_surjective`), and `z'`
a relative `(n + 1)`-cocycle whose image in `C^{n+1}(X; M)` is the coboundary of `x`. Then the
connecting morphism sends the class of `z` to the class of `z'`. -/
lemma connectingHom_homologyπ {n : ℕ} (z : (cochainComplex R A M).cycles n)
    (x : (cochainComplex R X M).X n)
    (hx : ((restriction R M A).f n).hom x = ((cochainComplex R A M).iCycles n).hom z)
    (z' : (relativeCochainComplex R M A).cycles (n + 1))
    (hz' : ((relativeCochainComplexι R M A).f (n + 1)).hom
        (((relativeCochainComplex R M A).iCycles (n + 1)).hom z') =
      ((cochainComplex R X M).d n (n + 1)).hom x) :
    (connectingHom R M A n).hom (((cochainComplex R A M).homologyπ n).hom z) =
      ((relativeCochainComplex R M A).homologyπ (n + 1)).hom z' :=
  (shortExact_shortComplex R M A).moduleCat_δ_homologyπ n (n + 1) (by simp) z x hx z' hz'

/-- **Exactness at `H^n(X; M)`** of the long exact sequence of the pair: the kernel of restriction
to `A` is the image of the relative cohomology. -/
theorem exact_cohomologyMap_subtypeVal (n : ℕ) :
    (ShortComplex.mk (relativeCohomologyMap R M A n)
      (cohomologyMap R M (ContinuousMap.subtypeVal A) n)
      (by rw [← HomologicalComplex.homologyMap_comp, relativeCochainComplexι_comp_restriction,
        HomologicalComplex.homologyMap_zero])).Exact :=
  (shortExact_shortComplex R M A).homology_exact₂ n

/-- **Exactness at `H^n(A; M)`** of the long exact sequence of the pair: the kernel of the
connecting morphism is the image of restriction from `X`. -/
theorem exact_connectingHom (n : ℕ) :
    (ShortComplex.mk (cohomologyMap R M (ContinuousMap.subtypeVal A) n) (connectingHom R M A n)
      (cohomologyMap_subtypeVal_comp_connectingHom R M A n)).Exact :=
  (shortExact_shortComplex R M A).homology_exact₃ n (n + 1) (by simp)

/-- **Exactness at `H^{n+1}(X, A; M)`** of the long exact sequence of the pair: the kernel of the
map to `H^{n+1}(X; M)` is the image of the connecting morphism. -/
theorem exact_relativeCohomologyMap (n : ℕ) :
    (ShortComplex.mk (connectingHom R M A n) (relativeCohomologyMap R M A (n + 1))
      (connectingHom_comp_relativeCohomologyMap R M A n)).Exact :=
  (shortExact_shortComplex R M A).homology_exact₁ n (n + 1) (by simp)

end TauCeti.AlexanderSpanier
