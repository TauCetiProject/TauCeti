/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Kernels
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
public import Mathlib.Topology.Category.TopCat.Basic
public import Mathlib.Topology.LocallyConstant.Algebra
public import TauCeti.AlgebraicTopology.AlternatingCofaceMapComplex

/-!
# Alexander–Spanier cohomology

Let `X` be a topological space and `M` a module over a ring `R`. An **Alexander–Spanier
`n`-cochain** of `X` with coefficients in `M` is an arbitrary function `φ : X^{n+1} → M`, with
the coboundary

`(δφ)(x₀, …, x_{n+1}) = ∑ᵢ (-1)ⁱ φ(x₀, …, xᵢ₋₁, xᵢ₊₁, …, x_{n+1})`.

A function `φ : X^{n+1} → M` is **locally zero** (`TauCeti.AlexanderSpanier.IsLocallyZero`) when
every point has a neighbourhood `U` with `φ = 0` on `U^{n+1}`. The locally zero functions form a
subcomplex, and the **Alexander–Spanier cochain complex** `C^*(X; M)` is the quotient
(`TauCeti.AlexanderSpanier.cochainComplex`). Its cohomology is the **Alexander–Spanier cohomology**
`H^n(X; M)` (`TauCeti.AlexanderSpanier.cohomology`).

The cochains form a cosimplicial module, `⦋n⦌ ↦ (X^{n+1} → M)`, with a map `f : ⦋m⦌ ⟶ ⦋n⦌` acting by
precomposition of tuples with `f`. Locally zero functions form a cosimplicial submodule, so the
quotients form a cosimplicial module (`TauCeti.AlexanderSpanier.cosimplicialModule`), and the
cochain complex is its alternating coface map complex
`AlgebraicTopology.alternatingCofaceMapComplex`. Its differential is the displayed alternating sum
(`TauCeti.AlexanderSpanier.cochainComplex_d_cochainClass`).

A continuous map `f : Y → X` pulls cochains back by `ψ ↦ ψ ∘ f^{n+1}`, which preserves locally zero
functions. This gives cochain maps `C^*(X; M) ⟶ C^*(Y; M)`
(`TauCeti.AlexanderSpanier.cochainComplexMap`) and maps in cohomology
(`TauCeti.AlexanderSpanier.cohomologyMap`), contravariantly functorial in `f`
(`TauCeti.AlexanderSpanier.cochainComplexFunctor` on `TopCat`).

In degree zero, a cochain is a function `X → M`, locally zero only when it is zero, and its
coboundary `(x₀, x₁) ↦ ψ(x₁) - ψ(x₀)` is locally zero exactly when `ψ` is locally constant. So
`H⁰(X; M)` is the module of locally constant functions `X → M`
(`TauCeti.AlexanderSpanier.cohomologyZeroIso`), naturally in `X`
(`TauCeti.AlexanderSpanier.cohomologyMap_zero_comp_cohomologyZeroIso_hom`). Locally constant
functions are constant on connected components, whereas the degree-zero singular cohomology
consists of the functions constant on path components.

Alexander–Spanier cohomology agrees with Čech cohomology on paracompact Hausdorff spaces, and it is
the theory used for the continuity and tautness properties of cohomology on compact pairs. The
relative groups of a pair and its exact sequence are in
`TauCeti.AlgebraicTopology.AlexanderSpanier.Relative`.

## References

* E. H. Spanier, *Algebraic Topology*, McGraw–Hill, 1966, Chapter 6, Section 6.4.
-/

public section

noncomputable section

open CategoryTheory Filter Topology AlgebraicTopology
open scoped Simplicial

universe w u v

namespace TauCeti.AlexanderSpanier

section LocallyZero

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {M : Type*} {ι κ : Type*}

/-- A function `φ` on `ι`-tuples of points of `X` is **locally zero** when every point of `X`
has a neighbourhood `U` such that `φ` vanishes on all tuples of points of `U`. -/
def IsLocallyZero [Zero M] (φ : (ι → X) → M) : Prop :=
  ∀ x : X, ∃ U ∈ 𝓝 x, ∀ y : ι → X, (∀ i, y i ∈ U) → φ y = 0

/-- Restatement of the definition of `TauCeti.AlexanderSpanier.IsLocallyZero`. -/
lemma isLocallyZero_iff [Zero M] {φ : (ι → X) → M} :
    IsLocallyZero φ ↔ ∀ x : X, ∃ U ∈ 𝓝 x, ∀ y : ι → X, (∀ i, y i ∈ U) → φ y = 0 :=
  Iff.rfl

/-- The zero function is locally zero. -/
@[simp]
lemma isLocallyZero_zero [Zero M] : IsLocallyZero (0 : (ι → X) → M) :=
  fun _ ↦ ⟨Set.univ, univ_mem, fun _ _ ↦ rfl⟩

/-- A sum of locally zero functions is locally zero. -/
lemma IsLocallyZero.add [AddZeroClass M] {φ ψ : (ι → X) → M} (hφ : IsLocallyZero φ)
    (hψ : IsLocallyZero ψ) : IsLocallyZero (φ + ψ) := by
  intro x
  obtain ⟨U, hU, hφU⟩ := hφ x
  obtain ⟨V, hV, hψV⟩ := hψ x
  refine ⟨U ∩ V, inter_mem hU hV, fun y hy ↦ ?_⟩
  simp [hφU y fun i ↦ (hy i).1, hψV y fun i ↦ (hy i).2]

/-- A scalar multiple of a locally zero function is locally zero. -/
lemma IsLocallyZero.smul {R : Type*} [Zero M] [SMulZeroClass R M] (c : R)
    {φ : (ι → X) → M} (hφ : IsLocallyZero φ) : IsLocallyZero (c • φ) := by
  intro x
  obtain ⟨U, hU, hφU⟩ := hφ x
  exact ⟨U, hU, fun y hy ↦ by simp [hφU y hy]⟩

/-- Reindexing the tuples along a map of index types preserves locally zero functions. -/
lemma IsLocallyZero.reindex [Zero M] {φ : (ι → X) → M} (hφ : IsLocallyZero φ) (g : ι → κ) :
    IsLocallyZero fun y : κ → X ↦ φ (y ∘ g) := by
  intro x
  obtain ⟨U, hU, hφU⟩ := hφ x
  exact ⟨U, hU, fun y hy ↦ hφU _ fun i ↦ hy (g i)⟩

/-- Pulling back along a continuous map preserves locally zero functions. -/
lemma IsLocallyZero.comp_continuous [Zero M] {φ : (ι → X) → M} (hφ : IsLocallyZero φ)
    {f : Y → X} (hf : Continuous f) : IsLocallyZero fun y : ι → Y ↦ φ (f ∘ y) := by
  intro x
  obtain ⟨U, hU, hφU⟩ := hφ (f x)
  exact ⟨f ⁻¹' U, hf.continuousAt hU, fun y hy ↦ hφU _ hy⟩

/-- A locally zero function vanishes on every constant tuple. -/
lemma IsLocallyZero.apply_const [Zero M] {φ : (ι → X) → M} (hφ : IsLocallyZero φ)
    (x : X) : φ (fun _ ↦ x) = 0 := by
  obtain ⟨U, hU, hφU⟩ := hφ x
  exact hφU _ fun _ ↦ mem_of_mem_nhds hU

/-- On one-element tuples, a function is locally zero exactly when it is zero. -/
lemma isLocallyZero_iff_eq_zero [Zero M] [Unique ι] {φ : (ι → X) → M} :
    IsLocallyZero φ ↔ φ = 0 := by
  refine ⟨fun hφ ↦ funext fun y ↦ ?_, fun h ↦ h ▸ isLocallyZero_zero⟩
  rw [Pi.zero_apply, ← hφ.apply_const (y default)]
  exact congrArg φ (funext fun i ↦ by rw [Unique.eq_default i])

/-- The function `(x₀, x₁) ↦ ψ(x₁) - ψ(x₀)` on pairs is locally zero exactly when `ψ` is locally
constant. -/
lemma isLocallyZero_sub_iff_isLocallyConstant [AddGroup M] {ψ : X → M} :
    IsLocallyZero (fun y : Fin 2 → X ↦ ψ (y 1) - ψ (y 0)) ↔ IsLocallyConstant ψ := by
  rw [IsLocallyConstant.iff_eventually_eq]
  refine ⟨fun h x ↦ ?_, fun h x ↦ ?_⟩
  · obtain ⟨U, hU, hψU⟩ := h x
    filter_upwards [hU] with z hz
    simpa [sub_eq_zero] using hψU ![x, z] (by simp [Fin.forall_fin_two, mem_of_mem_nhds hU, hz])
  · refine ⟨_, h x, fun y hy ↦ ?_⟩
    have h₀ : ψ (y 0) = ψ x := hy 0
    have h₁ : ψ (y 1) = ψ x := hy 1
    rw [sub_eq_zero, h₀, h₁]

end LocallyZero

section Submodule

variable (R : Type*) [Semiring R] (X : Type*) [TopologicalSpace X] (M : Type*) [AddCommMonoid M]
  [Module R M] (ι : Type*) {Y κ : Type*} [TopologicalSpace Y]

/-- The submodule of locally zero functions on `ι`-tuples of points of `X`. -/
def locallyZero : Submodule R ((ι → X) → M) where
  carrier := {φ | IsLocallyZero φ}
  zero_mem' := isLocallyZero_zero
  add_mem' := IsLocallyZero.add
  smul_mem' := IsLocallyZero.smul

variable {R X M ι}

@[simp]
lemma mem_locallyZero {φ : (ι → X) → M} : φ ∈ locallyZero R X M ι ↔ IsLocallyZero φ :=
  Iff.rfl

variable (R M) in
/-- Precomposing tuples with a map of index types preserves locally zero functions. -/
lemma locallyZero_le_comap_funLeft (g : ι → κ) :
    locallyZero R X M ι ≤
      (locallyZero R X M κ).comap (LinearMap.funLeft R M fun y : κ → X ↦ y ∘ g) :=
  fun _ hφ ↦ IsLocallyZero.reindex hφ g

variable (R M ι) in
/-- Pulling back along a continuous map preserves locally zero functions. -/
lemma locallyZero_le_comap_funLeft_of_continuous {f : Y → X} (hf : Continuous f) :
    locallyZero R X M ι ≤
      (locallyZero R Y M ι).comap (LinearMap.funLeft R M fun y : ι → Y ↦ f ∘ y) :=
  fun _ hφ ↦ IsLocallyZero.comp_continuous hφ hf

end Submodule

section Complex

variable (R : Type w) [Ring R] (X : Type u) [TopologicalSpace X] (M : Type v) [AddCommGroup M]
  [Module R M]

/-- The module of Alexander–Spanier cochains in a cosimplicial degree `n`: functions on
`(n + 1)`-tuples of points modulo the locally zero functions. -/
abbrev cochains (n : SimplexCategory) : ModuleCat.{max u v} R :=
  ModuleCat.of R (((Fin (n.len + 1) → X) → M) ⧸ locallyZero R X M (Fin (n.len + 1)))

/-- The map of Alexander–Spanier cochains induced by a map `f : ⦋m⦌ ⟶ ⦋n⦌` of the simplex
category: precomposition of `(n + 1)`-tuples with `f`. -/
def cochainsMap {m n : SimplexCategory} (f : m ⟶ n) : cochains R X M m ⟶ cochains R X M n :=
  ModuleCat.ofHom (Submodule.mapQ _ _ (LinearMap.funLeft R M fun y ↦ y ∘ f.toOrderHom)
    (locallyZero_le_comap_funLeft R M _))

/-- The **Alexander–Spanier cosimplicial module** `⦋n⦌ ↦ (X^{n+1} → M) / (locally zero)`. -/
@[expose] def cosimplicialModule : CosimplicialObject (ModuleCat.{max u v} R) where
  obj := cochains R X M
  map := cochainsMap R X M
  map_id _ := by
    ext φ
    rfl
  map_comp _ _ := by
    ext φ
    rfl

/-- The **Alexander–Spanier cochain complex** `C^*(X; M)`: the alternating coface map complex of
the Alexander–Spanier cosimplicial module. In degree `n` it consists of the functions
`X^{n+1} → M` modulo the locally zero functions. -/
@[expose] def cochainComplex : CochainComplex (ModuleCat.{max u v} R) ℕ :=
  (alternatingCofaceMapComplex (ModuleCat.{max u v} R)).obj (cosimplicialModule R X M)

/-- The class of a function `X^{n+1} → M` as an Alexander–Spanier `n`-cochain. -/
def cochainClass (n : ℕ) : ((Fin (n + 1) → X) → M) →ₗ[R] (cochainComplex R X M).X n :=
  (locallyZero R X M (Fin (n + 1))).mkQ

variable {R X M}

/-- Every Alexander–Spanier cochain is the class of a function. -/
lemma cochainClass_surjective (n : ℕ) : Function.Surjective (cochainClass R X M n) :=
  Submodule.mkQ_surjective _

/-- The class of a function is zero exactly when the function is locally zero. -/
@[simp]
lemma cochainClass_eq_zero_iff {n : ℕ} {φ : (Fin (n + 1) → X) → M} :
    cochainClass R X M n φ = 0 ↔ IsLocallyZero φ :=
  Submodule.Quotient.mk_eq_zero _

/-- Two functions have the same class exactly when their difference is locally zero. -/
lemma cochainClass_eq_cochainClass_iff {n : ℕ} {φ ψ : (Fin (n + 1) → X) → M} :
    cochainClass R X M n φ = cochainClass R X M n ψ ↔ IsLocallyZero (φ - ψ) :=
  Submodule.Quotient.eq _

/-- On one-element tuples, two functions have the same class exactly when they are equal. -/
lemma cochainClass_zero_inj {φ ψ : (Fin 1 → X) → M} :
    cochainClass R X M 0 φ = cochainClass R X M 0 ψ ↔ φ = ψ := by
  -- Instance search does not reduce `0 + 1` to `1`.
  have : Unique (Fin (0 + 1)) := inferInstanceAs (Unique (Fin 1))
  rw [cochainClass_eq_cochainClass_iff, isLocallyZero_iff_eq_zero, sub_eq_zero]

/-- Two linear maps out of the Alexander–Spanier `n`-cochains agree once they agree on the
classes of all functions. -/
lemma cochainComplex_linearMap_ext {n : ℕ} {N : Type*} [AddCommGroup N] [Module R N]
    {f g : (cochainComplex R X M).X n →ₗ[R] N}
    (h : ∀ φ, f (cochainClass R X M n φ) = g (cochainClass R X M n φ)) : f = g :=
  Submodule.linearMap_qext _ (LinearMap.ext h)

/-- The coface `δⁱ` of the Alexander–Spanier cosimplicial module sends the class of `φ` to the class
of `(x₀, …, x_{n+1}) ↦ φ(x₀, …, xᵢ₋₁, xᵢ₊₁, …, x_{n+1})`. -/
@[simp]
lemma cosimplicialModule_δ_cochainClass {n : ℕ} (i : Fin (n + 2)) (φ : (Fin (n + 1) → X) → M) :
    ((cosimplicialModule R X M).δ i).hom (cochainClass R X M n φ) =
      cochainClass R X M (n + 1) fun y ↦ φ (y ∘ Fin.succAbove i) :=
  (rfl)

/-- The **differential** of the Alexander–Spanier cochain complex on the class of a function `φ`
is the class of `(x₀, …, x_{n+1}) ↦ ∑ᵢ (-1)ⁱ φ(x₀, …, xᵢ₋₁, xᵢ₊₁, …, x_{n+1})`. -/
@[simp]
theorem cochainComplex_d_cochainClass (n : ℕ) (φ : (Fin (n + 1) → X) → M) :
    ((cochainComplex R X M).d n (n + 1)).hom (cochainClass R X M n φ) =
      cochainClass R X M (n + 1) fun y ↦
        ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) • φ (y ∘ Fin.succAbove i) := by
  have hφ : (fun y : Fin (n + 2) → X ↦
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) • φ (y ∘ Fin.succAbove i)) =
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) • fun y ↦ φ (y ∘ Fin.succAbove i) := by
    ext y
    simp [Finset.sum_apply]
  have hsum (x : (cosimplicialModule R X M).obj ⦋n⦌) :
      (∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) • (cosimplicialModule R X M).δ i).hom x =
        ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) • ((cosimplicialModule R X M).δ i).hom x := by
    simp
  rw [hφ, map_sum]
  simp_rw [map_zsmul, ← cosimplicialModule_δ_cochainClass]
  -- The degree `n` cochains of the complex are by definition the cosimplicial degree `n` module.
  exact (LinearMap.congr_fun (congrArg ModuleCat.Hom.hom
    (AlternatingCofaceMapComplex.obj_d_eq (cosimplicialModule R X M) n)) _).trans (hsum _)

variable (R X M) in
/-- **Alexander–Spanier cohomology** `H^n(X; M)`. -/
abbrev cohomology (n : ℕ) : ModuleCat.{max u v} R :=
  (cochainComplex R X M).homology n

end Complex

section Functoriality

variable (R : Type w) [Ring R] {X Y Z : Type u} [TopologicalSpace X] [TopologicalSpace Y]
  [TopologicalSpace Z] (M : Type v) [AddCommGroup M] [Module R M]

/-- The pullback of Alexander–Spanier cochains along a continuous map `f : Y → X`, in a
cosimplicial degree: `ψ ↦ ψ ∘ f^{n+1}`. -/
def cochainsPullback (f : C(Y, X)) (n : SimplexCategory) :
    cochains R X M n ⟶ cochains R Y M n :=
  ModuleCat.ofHom (Submodule.mapQ _ _ (LinearMap.funLeft R M fun y ↦ f ∘ y)
    (locallyZero_le_comap_funLeft_of_continuous R M _ f.continuous))

/-- The pullback along a continuous map `f : Y → X` as a map of Alexander–Spanier cosimplicial
modules. -/
def cosimplicialModuleMap (f : C(Y, X)) : cosimplicialModule R X M ⟶ cosimplicialModule R Y M where
  app := cochainsPullback R M f
  naturality _ _ _ := ModuleCat.hom_ext (Submodule.linearMap_qext _ rfl)

/-- Pullback along the identity is the identity. -/
lemma cosimplicialModuleMap_id : cosimplicialModuleMap R M (ContinuousMap.id X) = 𝟙 _ :=
  NatTrans.ext (funext fun _ ↦ ModuleCat.hom_ext (Submodule.linearMap_qext _ rfl))

/-- Pullback along a composite is the composite of the pullbacks, in the opposite order. -/
lemma cosimplicialModuleMap_comp (f : C(Y, X)) (g : C(Z, Y)) :
    cosimplicialModuleMap R M (f.comp g) =
      cosimplicialModuleMap R M f ≫ cosimplicialModuleMap R M g :=
  NatTrans.ext (funext fun _ ↦ ModuleCat.hom_ext (Submodule.linearMap_qext _ rfl))

/-- The pullback along a continuous map `f : Y → X` as a cochain map
`C^*(X; M) ⟶ C^*(Y; M)`. -/
def cochainComplexMap (f : C(Y, X)) : cochainComplex R X M ⟶ cochainComplex R Y M :=
  (alternatingCofaceMapComplex (ModuleCat.{max u v} R)).map (cosimplicialModuleMap R M f)

variable {R M} in
/-- The pullback of the class of `φ` along `f` is the class of `y ↦ φ (f ∘ y)`. -/
@[simp]
lemma cochainComplexMap_f_cochainClass (f : C(Y, X)) (n : ℕ) (φ : (Fin (n + 1) → X) → M) :
    ((cochainComplexMap R M f).f n).hom (cochainClass R X M n φ) =
      cochainClass R Y M n fun y ↦ φ (f ∘ y) :=
  (rfl)

/-- Pullback of cochains along the identity is the identity. -/
@[simp]
lemma cochainComplexMap_id : cochainComplexMap R M (ContinuousMap.id X) = 𝟙 _ :=
  (congrArg (alternatingCofaceMapComplex _).map (cosimplicialModuleMap_id R M)).trans
    ((alternatingCofaceMapComplex _).map_id _)

/-- Pullback of cochains along a composite is the composite of the pullbacks. -/
@[simp]
lemma cochainComplexMap_comp (f : C(Y, X)) (g : C(Z, Y)) :
    cochainComplexMap R M (f.comp g) = cochainComplexMap R M f ≫ cochainComplexMap R M g :=
  (congrArg (alternatingCofaceMapComplex _).map (cosimplicialModuleMap_comp R M f g)).trans
    ((alternatingCofaceMapComplex _).map_comp _ _)

/-- The map `H^n(X; M) ⟶ H^n(Y; M)` induced by a continuous map `f : Y → X`. -/
abbrev cohomologyMap (f : C(Y, X)) (n : ℕ) : cohomology R X M n ⟶ cohomology R Y M n :=
  HomologicalComplex.homologyMap (cochainComplexMap R M f) n

/-- The identity induces the identity in Alexander–Spanier cohomology. -/
@[simp]
lemma cohomologyMap_id (n : ℕ) : cohomologyMap R M (ContinuousMap.id X) n = 𝟙 _ := by
  rw [cohomologyMap, cochainComplexMap_id, HomologicalComplex.homologyMap_id]

/-- Alexander–Spanier cohomology is contravariantly functorial. -/
@[simp]
lemma cohomologyMap_comp (f : C(Y, X)) (g : C(Z, Y)) (n : ℕ) :
    cohomologyMap R M (f.comp g) n = cohomologyMap R M f n ≫ cohomologyMap R M g n := by
  rw [cohomologyMap, cochainComplexMap_comp, HomologicalComplex.homologyMap_comp]

/-- The **Alexander–Spanier cochain complex** as a contravariant functor on topological
spaces. -/
@[expose, simps]
def cochainComplexFunctor : TopCat.{u}ᵒᵖ ⥤ CochainComplex (ModuleCat.{max u v} R) ℕ where
  obj X := cochainComplex R X.unop M
  map f := cochainComplexMap R M f.unop.hom
  map_id _ := cochainComplexMap_id R M
  map_comp f g := cochainComplexMap_comp R M f.unop.hom g.unop.hom

end Functoriality

section DegreeZero

variable (R : Type w) [Ring R] (X : Type u) [TopologicalSpace X] (M : Type v) [AddCommGroup M]
  [Module R M]

/-- A locally constant function `ψ : X → M` as an Alexander–Spanier `0`-cochain. -/
def locallyConstantToCochains : LocallyConstant X M →ₗ[R] (cochainComplex R X M).X 0 :=
  cochainClass R X M 0 ∘ₗ LinearMap.funLeft R M (fun y : Fin 1 → X ↦ y 0) ∘ₗ
    LocallyConstant.coeFnₗ R

variable {R X M}

/-- The `0`-cochain of a locally constant function `ψ` is the class of `y ↦ ψ (y 0)`. -/
@[simp]
lemma locallyConstantToCochains_apply (ψ : LocallyConstant X M) :
    locallyConstantToCochains R X M ψ = cochainClass R X M 0 fun y ↦ ψ (y 0) :=
  (rfl)

/-- The degree `0` differential of the Alexander–Spanier cochain complex sends the class of `ψ` to
the class of `(x₀, x₁) ↦ ψ(x₁) - ψ(x₀)`. -/
lemma cochainComplex_d_zero_cochainClass (ψ : X → M) :
    ((cochainComplex R X M).d 0 1).hom (cochainClass R X M 0 fun y ↦ ψ (y 0)) =
      cochainClass R X M 1 fun y ↦ ψ (y 1) - ψ (y 0) := by
  rw [cochainComplex_d_cochainClass]
  congr 1
  funext y
  simp [Fin.sum_univ_two, sub_eq_add_neg]

/-- Distinct locally constant functions give distinct `0`-cochains. -/
lemma locallyConstantToCochains_injective :
    Function.Injective (locallyConstantToCochains R X M) := by
  intro ψ ψ' h
  rw [locallyConstantToCochains_apply, locallyConstantToCochains_apply,
    cochainClass_zero_inj] at h
  ext x
  exact congrFun h fun _ ↦ x

/-- The `0`-cochains with zero coboundary are exactly those of locally constant functions. -/
lemma exact_locallyConstantToCochains :
    Function.Exact (locallyConstantToCochains R X M) ((cochainComplex R X M).d 0 1).hom := by
  intro φ
  obtain ⟨φ, rfl⟩ := cochainClass_surjective 0 φ
  set ψ : X → M := fun x ↦ φ fun _ ↦ x
  have hφ : φ = fun y ↦ ψ (y 0) := funext fun y ↦ congrArg φ (funext fun i ↦ by
    rw [Fin.fin_one_eq_zero i])
  rw [hφ, cochainComplex_d_zero_cochainClass, cochainClass_eq_zero_iff,
    isLocallyZero_sub_iff_isLocallyConstant]
  refine ⟨fun h ↦ ⟨⟨ψ, h⟩, rfl⟩, ?_⟩
  rintro ⟨ψ', hψ'⟩
  rw [locallyConstantToCochains_apply, cochainClass_zero_inj] at hψ'
  have : ψ = ψ' := funext fun x ↦ (congrFun hψ' fun _ ↦ x).symm
  exact this ▸ ψ'.isLocallyConstant

variable (R X M)

/-- The Alexander–Spanier `0`-cocycles are the locally constant functions. -/
def cyclesZeroIso :
    (cochainComplex R X M).cycles 0 ≅ ModuleCat.of R (LocallyConstant X M) :=
  Limits.IsLimit.conePointUniqueUpToIso ((cochainComplex R X M).cyclesIsKernel 0 1 (by simp))
    (ModuleCat.isLimitKernelFork (ModuleCat.ofHom (locallyConstantToCochains R X M)) _
      exact_locallyConstantToCochains locallyConstantToCochains_injective)

/-- The cocycle of a locally constant function `ψ` is the class of `y ↦ ψ (y 0)`. -/
@[reassoc (attr := simp), elementwise (attr := simp)]
lemma cyclesZeroIso_inv_iCycles :
    (cyclesZeroIso R X M).inv ≫ (cochainComplex R X M).iCycles 0 =
      ModuleCat.ofHom (locallyConstantToCochains R X M) :=
  Limits.IsLimit.conePointUniqueUpToIso_inv_comp _ _ Limits.WalkingParallelPair.zero

/-- **Degree-zero Alexander–Spanier cohomology** is the module of locally constant functions:
`H⁰(X; M) ≅ LocallyConstant X M`. -/
def cohomologyZeroIso : cohomology R X M 0 ≅ ModuleCat.of R (LocallyConstant X M) :=
  (cochainComplex R X M).isoHomologyπ₀.symm ≪≫ cyclesZeroIso R X M

/-- The class in `H⁰(X; M)` of a locally constant function is the cohomology class of its
cocycle. -/
lemma cohomologyZeroIso_inv :
    (cohomologyZeroIso R X M).inv =
      (cyclesZeroIso R X M).inv ≫ (cochainComplex R X M).homologyπ 0 :=
  (rfl)

/-- The class in `H⁰(X; M)` of a locally constant function `ψ` is the cohomology class of the
cocycle of `ψ`. -/
@[simp]
lemma cohomologyZeroIso_inv_apply (ψ : LocallyConstant X M) :
    (cohomologyZeroIso R X M).inv.hom ψ =
      ((cochainComplex R X M).homologyπ 0).hom ((cyclesZeroIso R X M).inv.hom ψ) :=
  (rfl)

/-- On a `0`-cocycle, the identification `H⁰(X; M) ≅ LocallyConstant X M` is the identification of
`0`-cocycles with locally constant functions. -/
@[reassoc (attr := simp), elementwise (attr := simp)]
lemma homologyπ_comp_cohomologyZeroIso_hom :
    (cochainComplex R X M).homologyπ 0 ≫ (cohomologyZeroIso R X M).hom =
      (cyclesZeroIso R X M).hom :=
  Iso.hom_inv_id_assoc (cochainComplex R X M).isoHomologyπ₀ _

variable {R X M} in
/-- A `0`-cocycle represented by the class of `φ : X^1 → M` corresponds to the locally constant
function `x ↦ φ(x)`. -/
lemma cyclesZeroIso_hom_apply {z : (cochainComplex R X M).cycles 0} {φ : (Fin 1 → X) → M}
    (hz : ((cochainComplex R X M).iCycles 0).hom z = cochainClass R X M 0 φ) (x : X) :
    (cyclesZeroIso R X M).hom.hom z x = φ fun _ ↦ x := by
  set ψ := (cyclesZeroIso R X M).hom.hom z
  have hz' : (cyclesZeroIso R X M).inv.hom ψ = z := Iso.hom_inv_id_apply (cyclesZeroIso R X M) z
  rw [← hz', cyclesZeroIso_inv_iCycles_apply, cochainClass_zero_inj] at hz
  exact congrFun hz fun _ ↦ x

variable {R X M} in
/-- The class in `H⁰(X; M)` of a `0`-cocycle represented by the class of `φ : X^1 → M` corresponds
to the locally constant function `x ↦ φ(x)`. -/
lemma cohomologyZeroIso_hom_homologyπ_apply {z : (cochainComplex R X M).cycles 0}
    {φ : (Fin 1 → X) → M}
    (hz : ((cochainComplex R X M).iCycles 0).hom z = cochainClass R X M 0 φ) (x : X) :
    (cohomologyZeroIso R X M).hom.hom (((cochainComplex R X M).homologyπ 0).hom z) x =
      φ fun _ ↦ x := by
  rw [homologyπ_comp_cohomologyZeroIso_hom_apply, cyclesZeroIso_hom_apply hz]

variable {R M} in
/-- The identification `H⁰(X; M) ≅ LocallyConstant X M` is natural: pulling back a class along a
continuous map `f` pulls back its locally constant function along `f`. -/
@[reassoc]
lemma cohomologyMap_zero_comp_cohomologyZeroIso_hom {Y : Type u} [TopologicalSpace Y]
    (f : C(Y, X)) :
    cohomologyMap R M f 0 ≫ (cohomologyZeroIso R Y M).hom =
      (cohomologyZeroIso R X M).hom ≫ ModuleCat.ofHom (LocallyConstant.comapₗ R f) := by
  have h : (cyclesZeroIso R X M).inv ≫ HomologicalComplex.cyclesMap (cochainComplexMap R M f) 0 =
      ModuleCat.ofHom (LocallyConstant.comapₗ R f) ≫ (cyclesZeroIso R Y M).inv := by
    rw [← cancel_mono ((cochainComplex R Y M).iCycles 0)]
    simp only [Category.assoc, HomologicalComplex.cyclesMap_i, cyclesZeroIso_inv_iCycles,
      cyclesZeroIso_inv_iCycles_assoc]
    ext ψ
    simp [cochainComplexMap_f_cochainClass, locallyConstantToCochains_apply]
  rw [← Iso.inv_comp_eq, ← Category.assoc, ← Iso.eq_comp_inv]
  simp only [cohomologyZeroIso_inv, Category.assoc, HomologicalComplex.homologyπ_naturality,
    reassoc_of% h]

end DegreeZero

end TauCeti.AlexanderSpanier
