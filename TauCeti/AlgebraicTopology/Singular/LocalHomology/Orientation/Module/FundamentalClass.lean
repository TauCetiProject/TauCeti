/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.LocalHomology.IsFundamentalClass
public import TauCeti.AlgebraicTopology.Singular.LocalHomology.Orientation.Module.Basic

/-!
# Fundamental classes of module-oriented manifolds

For a Hausdorff space `M` modelled on an `n`-dimensional real normed space `E`, ring `R` in the
universe of `M`, and `R`-module `N`, an `N`-orientation `o : ModuleOrientation N M E n` glues
uniquely along each compact `A ⊆ M` to `o.fundamentalClassOn hn hA` in `Hₙ(M, M ∖ A; N)` (Hatcher,
Lemma 3.27), and for compact `M` to `o.fundamentalClass hn` in `Hₙ(M; N)`, giving
`ModuleOrientation.equivSubtypeIsFundamentalClass` (Theorem 3.26). On a compact connected
`n`-manifold over a Dedekind-finite ring `R`, `r ↦ r • μ` gives `R ≃ₗ[R] Hₙ(M; R)`
(`ModuleOrientation.fundamentalClassLinearEquiv`, `IsFundamentalClass.linearEquiv`). Recharting
`M : Type w` onto `EuclideanSpace ℝ (ULift (Fin (finrank ℝ E)))` yields
`existsUnique_isFundamentalClass_of_subsingleton_units`,
`exists_isFundamentalClass_of_simplyConnectedSpace`, `exists_isFundamentalClass_of_two_eq_zero`, and
`nonempty_singularHomologyLinearEquiv_of_two_eq_zero`.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf), §3.3.
-/

public section
noncomputable section

open CategoryTheory Limits Module Set Topology
open scoped ChangeOfRings

universe w v u

namespace TauCeti

section General
variable {M : Type w} [TopologicalSpace M] {R : Type u} [Ring R] {N : ModuleCat.{w} R} {n : ℕ}

/-- `TauCeti.IsFundamentalClass` expressed directly via the pair quotient morphism
`Hₙ(M; N) ⟶ Hₙ(M, M ∖ {x}; N)`. -/
theorem isFundamentalClass_iff_singularHomologyπ
    (μ : ((TopCat.toSSet.obj (TopCat.of M)).homology N n : ModuleCat.{w} R)) :
    IsFundamentalClass μ ↔
      ∀ x : M, Submodule.span R
        {((TopPair.ofSubset ({x}ᶜ : Set (TopCat.of M))).singularHomologyπ
          (C := ModuleCat.{w} R) N n).hom μ} = ⊤ := by
  simp only [isFundamentalClass_iff, singularHomologyToLocalHomology_eq_singularHomologyπ]; rfl

/-- A class `μ ∈ Hₙ(M; N)` is a fundamental class if and only if its image in local homology at
every point is a local `N`-orientation. -/
theorem isFundamentalClass_iff_forall_isModuleLocalOrientation
    (μ : ((TopCat.toSSet.obj (TopCat.of M)).homology N n : ModuleCat.{w} R)) :
    IsFundamentalClass μ ↔
      ∀ x : M, IsModuleLocalOrientation N x n (singularHomologyToLocalHomology N x n μ) :=
  (isFundamentalClass_iff μ).trans
    (forall_congr' fun x ↦ (isModuleLocalOrientation_iff N x n _).symm)

/-- An isomorphism of coefficient modules `e : N ≅ N'` preserves fundamental classes. -/
theorem IsFundamentalClass.map_coefficientsIso {N' : ModuleCat.{w} R} (e : N ≅ N')
    {μ : ((TopCat.toSSet.obj (TopCat.of M)).homology N n : ModuleCat.{w} R)}
    (hμ : IsFundamentalClass μ) :
    IsFundamentalClass
      ((SSet.homologyIsoOfCoefficientsIso e (TopCat.toSSet.obj (TopCat.of M)) n).hom μ) :=
  (isFundamentalClass_iff_forall_isModuleLocalOrientation _).2 fun x ↦
    singularHomologyToLocalHomology_homologyIsoOfCoefficientsIso_hom_apply e x n μ ▸
      ((isFundamentalClass_iff_forall_isModuleLocalOrientation μ).1 hμ x).map
        (localHomologyIsoOfCoefficientsIso e ({x} : Set M) n)

/-- **Exact extension of scalars preserves fundamental classes.** -/
theorem IsFundamentalClass.extendScalars {R S : Type w} [CommRing R] [CommRing S] (f : R →+* S)
    [PreservesFiniteLimits (ModuleCat.extendScalars.{w, w, w} f)]
    {μ : ((TopCat.toSSet.obj (TopCat.of M)).homology (ModuleCat.of R R) n : ModuleCat.{w} R)}
    (hμ : IsFundamentalClass μ) :
    IsFundamentalClass ((singularHomologyExtendScalarsIso f M n).hom ((1 : S) ⊗ₜ[R, f] μ)) :=
  (isFundamentalClass_iff_forall_isModuleLocalOrientation _).2 fun x ↦
    singularHomologyToLocalHomology_singularHomologyExtendScalarsIso_hom_tmul f x n 1 μ ▸
      ((isFundamentalClass_iff_forall_isModuleLocalOrientation μ).1 hμ x).extendScalars f

end General

section ToOrientation

variable {R : Type u} [Ring R] {N : ModuleCat.{w} R}
  {M E : Type w} [TopologicalSpace M] [T2Space M]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [ChartedSpace E M]
  {d : ℕ}

/-- The local homology images of any global homology class `μ ∈ H_d(M; N)` are invariant under path
transport. -/
theorem localHomologyTransport_singularHomologyToLocalHomology
    {x y : FundamentalGroupoid M} (g : x ⟶ y)
    (μ : ((TopCat.toSSet.obj (TopCat.of M)).homology N d : ModuleCat.{w} R)) :
    localHomologyTransport N M E d g (singularHomologyToLocalHomology N x.as d μ) =
      singularHomologyToLocalHomology N y.as d μ := by
  rw [singularHomologyToLocalHomology_apply, singularHomologyToLocalHomology_apply,
    ← ConcreteCategory.comp_apply, localHomologyRestriction_univ_comp_localHomologyTransport]

/-- **A fundamental class determines an `N`-orientation**: its images in the local homology groups
generate every fibre and are invariant under path transport. -/
def IsFundamentalClass.toModuleOrientation
    {μ : ((TopCat.toSSet.obj (TopCat.of M)).homology N d : ModuleCat.{w} R)}
    (hμ : IsFundamentalClass μ) : ModuleOrientation N M E d where
  toFun x := ⟨singularHomologyToLocalHomology N x d μ,
    (isFundamentalClass_iff_forall_isModuleLocalOrientation μ).1 hμ x⟩
  moduleLocalOrientationTransport_toFun' g :=
    Subtype.ext ((coe_moduleLocalOrientationTransport N M E d g _).trans
      (localHomologyTransport_singularHomologyToLocalHomology (E := E) g μ))

@[simp] theorem IsFundamentalClass.coe_toModuleOrientation_apply
    {μ : ((TopCat.toSSet.obj (TopCat.of M)).homology N d : ModuleCat.{w} R)}
    (hμ : IsFundamentalClass μ) (x : M) :
    (hμ.toModuleOrientation (E := E) x).val = singularHomologyToLocalHomology N x d μ := (rfl)

end ToOrientation

namespace ModuleOrientation
section Gluing
variable {R : Type w} [Ring R] {N : ModuleCat.{w} R}
  {M E : Type w} [TopologicalSpace M] [T2Space M]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [ChartedSpace E M]
  {n : ℕ} (o : ModuleOrientation N M E n) (hn : finrank ℝ E = n)

section Compact
variable {A : Set M} (hA : IsCompact A)

include hn hA in
private theorem existsUnique_fundamentalClassOn :
    ∃! γ : (localHomology N A n : ModuleCat.{w} R),
      ∀ x (hx : x ∈ A), localHomologyRestriction N (singleton_subset_iff.2 hx) n γ = (o x).val :=
  existsUnique_localHomologyRestriction_eq_of_invariant N hn hA (fun x ↦ (o x).val)
    o.localHomologyTransport_coe_apply

/-- **The relative fundamental class along a compact subset** `A ⊆ M`: the unique class of
`Hₙ(M, M ∖ A; N)` restricting to `o x` at each `x ∈ A` (Hatcher, Lemma 3.27). -/
def fundamentalClassOn : (localHomology N A n : ModuleCat.{w} R) :=
  (o.existsUnique_fundamentalClassOn hn hA).exists.choose

/-- `o.fundamentalClassOn` restricts to `o x` at every point `x ∈ A`. -/
theorem localHomologyRestriction_fundamentalClassOn {x : M} (hx : x ∈ A) :
    localHomologyRestriction N (singleton_subset_iff.2 hx) n (o.fundamentalClassOn hn hA) =
      (o x).val :=
  (o.existsUnique_fundamentalClassOn hn hA).exists.choose_spec x hx

/-- **Uniqueness of the relative fundamental class along `A`.** -/
theorem eq_fundamentalClassOn {γ : (localHomology N A n : ModuleCat.{w} R)}
    (hγ : ∀ x (hx : x ∈ A),
      localHomologyRestriction N (singleton_subset_iff.2 hx) n γ = (o x).val) :
    γ = o.fundamentalClassOn hn hA :=
  (o.existsUnique_fundamentalClassOn hn hA).unique hγ fun _ hx ↦
    o.localHomologyRestriction_fundamentalClassOn hn hA hx

/-- For compact subsets `B ⊆ A`, restricting `o.fundamentalClassOn` from `A` to `B` gives
`o.fundamentalClassOn` on `B`. -/
@[simp] theorem localHomologyRestriction_fundamentalClassOn_of_subset {B : Set M}
    (hB : IsCompact B) (hBA : B ⊆ A) :
    localHomologyRestriction N hBA n (o.fundamentalClassOn hn hA) = o.fundamentalClassOn hn hB :=
  o.eq_fundamentalClassOn hn hB fun _ hx ↦ by
    rw [localHomologyRestriction_comp_apply]
    exact o.localHomologyRestriction_fundamentalClassOn hn hA (hBA hx)

/-- The fundamental class along a singleton `{x}` is the local orientation `o x`. -/
@[simp] theorem fundamentalClassOn_singleton (x : M) (hx : IsCompact ({x} : Set M)) :
    o.fundamentalClassOn hn hx = (o x).val := by
  rw [← o.localHomologyRestriction_fundamentalClassOn hn hx (mem_singleton x),
    localHomologyRestriction_refl, ModuleCat.id_apply]

/-- Scaling an orientation by `u : Rˣ` scales the relative fundamental class by `u`. -/
@[simp] theorem fundamentalClassOn_smul (u : Rˣ) :
    (u • o).fundamentalClassOn hn hA = (u : R) • o.fundamentalClassOn hn hA :=
  ((u • o).eq_fundamentalClassOn hn hA fun x hx ↦ by
    rw [map_smul, o.localHomologyRestriction_fundamentalClassOn hn hA hx, smul_apply,
      ModuleLocalOrientation.coe_smul]).symm

/-- Reversing the orientation negates the relative fundamental class along `A`. -/
@[simp] theorem fundamentalClassOn_neg :
    (-o).fundamentalClassOn hn hA = -o.fundamentalClassOn hn hA :=
  ((-o).eq_fundamentalClassOn hn hA fun x hx ↦ by
    rw [map_neg, o.localHomologyRestriction_fundamentalClassOn hn hA hx, neg_apply,
      ModuleLocalOrientation.coe_neg]).symm

end Compact

section OpenEmbedding

variable {X : Type w} [TopologicalSpace X] [T1Space X] {ι : M → X} (hι : IsOpenEmbedding ι)

/-- Along an open embedding `ι : M → X` into a `T₁` space, a class of `Hₙ(X, X ∖ T; N)` (for closed
`T ⊆ range ι` with compact `S = ι ⁻¹' T`) restricting at each `ι x ∈ T` to the excised image of
`o x` is the image under `ι` of `o.fundamentalClassOn hn hS`. -/
theorem eq_localHomologyMap_fundamentalClassOn {S : Set M} (hS : IsCompact S) {T : Set X}
    (h : ι ⁻¹' T = S) (hT : IsClosed T) (hTι : T ⊆ range ι)
    {γ : (localHomology N T n : ModuleCat.{w} R)}
    (hγ : ∀ x (hx : ι x ∈ T),
      localHomologyRestriction N (singleton_subset_iff.2 hx) n γ =
        (localHomologyIsoOfIsOpenEmbedding N hι x n).hom (o x).val) :
    γ = localHomologyMap N ⟨ι, hι.continuous⟩ h.subset n (o.fundamentalClassOn hn hS) := by
  have := isIso_localHomologyMap (A := ModuleCat.{w} R) N ⟨ι, hι.continuous⟩ hι h hT hTι n
  set a := localHomologyMap (A := ModuleCat.{w} R) N ⟨ι, hι.continuous⟩ h.subset n
  suffices hδ : inv a γ = o.fundamentalClassOn hn hS by
    rw [← hδ, ← ConcreteCategory.comp_apply, IsIso.inv_hom_id, ModuleCat.id_apply]
  refine o.eq_fundamentalClassOn hn hS fun x hx ↦
    ConcreteCategory.injective_of_mono_of_preservesPullback
      (localHomologyIsoOfIsOpenEmbedding N hι x n).hom ?_
  have hxT : ι x ∈ T := h.symm.subset hx
  rw [← ConcreteCategory.comp_apply,
    ← localHomologyMap_comp_localHomologyRestriction_singleton _ hι h.subset hxT,
    ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply (inv a), IsIso.inv_hom_id,
    ModuleCat.id_apply, hγ x hxT]

/-- **Open embeddings carry relative fundamental classes to relative fundamental classes.** -/
theorem localHomologyMap_fundamentalClassOn_comap {U : Type w} [TopologicalSpace U] [T2Space U]
    [ChartedSpace E U] {j : C(U, M)} (hj : IsOpenEmbedding j) {K : Set U} (hK : IsCompact K) :
    localHomologyMap N j (hj.injective.preimage_image K).subset n
        ((o.comap hj).fundamentalClassOn hn hK) =
      o.fundamentalClassOn hn (hK.image j.continuous) := by
  refine o.eq_fundamentalClassOn hn _ ?_
  rintro _ ⟨x, hx, rfl⟩
  have hjx : j ⁻¹' {j x} ⊆ {x} := by rw [← image_singleton, hj.injective.preimage_image]
  have hox : localHomologyMap N j hjx n (o.comap hj x).val = (o (j x)).val := by
    rw [← moduleLocalOrientationEquiv_comap_apply o hj x,
      IsOpenEmbedding.coe_moduleLocalOrientationEquiv, localHomologyIsoOfIsOpenEmbedding_hom,
      localHomologyMap_congr _ (ContinuousMap.ext fun _ ↦ rfl : ⟨j, hj.continuous⟩ = j)]
  rw [← hox, ← (o.comap hj).localHomologyRestriction_fundamentalClassOn hn hK hx,
    ← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply,
    localHomologyMap_comp_localHomologyRestriction, localHomologyRestriction_comp_localHomologyMap]

end OpenEmbedding

section CompactSpace

variable [CompactSpace M]

include hn in
private theorem existsUnique_fundamentalClass :
    ∃! γ : ((TopCat.toSSet.obj (TopCat.of M)).homology N n : ModuleCat.{w} R),
      ∀ x : M, singularHomologyToLocalHomology N x n γ = (o x).val :=
  existsUnique_singularHomology_localHomologyRestriction_eq_of_invariant N hn (fun x ↦ (o x).val)
    o.localHomologyTransport_coe_apply

/-- **The fundamental class of a compact `N`-oriented manifold**: the unique class of `Hₙ(M; N)`
mapping to `o x` in `Hₙ(M, M ∖ {x}; N)` at every `x : M` (Hatcher, Theorem 3.26). -/
def fundamentalClass : ((TopCat.toSSet.obj (TopCat.of M)).homology N n : ModuleCat.{w} R) :=
  (o.existsUnique_fundamentalClass hn).exists.choose

/-- The image of `o.fundamentalClass hn` in local homology at `x` is `(o x).val`. -/
@[simp] theorem singularHomologyToLocalHomology_fundamentalClass (x : M) :
    singularHomologyToLocalHomology N x n (o.fundamentalClass hn) = (o x).val :=
  (o.existsUnique_fundamentalClass hn).exists.choose_spec x

/-- **Uniqueness of the fundamental class.** -/
theorem eq_fundamentalClass
    {γ : ((TopCat.toSSet.obj (TopCat.of M)).homology N n : ModuleCat.{w} R)}
    (hγ : ∀ x : M, singularHomologyToLocalHomology N x n γ = (o x).val) :
    γ = o.fundamentalClass hn :=
  (o.existsUnique_fundamentalClass hn).unique hγ
    (o.singularHomologyToLocalHomology_fundamentalClass hn)

/-- The image of `o.fundamentalClass hn` in `Hₙ(M, M ∖ A; N)` is `o.fundamentalClassOn hn hA`. -/
theorem singularHomologyπ_fundamentalClass {A : Set M} (hA : IsCompact A) :
    ((TopPair.ofSubset (Aᶜ : Set (TopCat.of M))).singularHomologyπ
      (C := ModuleCat.{w} R) N n).hom (o.fundamentalClass hn) = o.fundamentalClassOn hn hA :=
  o.eq_fundamentalClassOn hn hA fun x hx ↦ by
    have h := TopPair.singularHomologyπ_comp_singularHomologyMap_ofSubsetMap_id_assoc N
      (X := TopCat.of M) (S := Aᶜ) (S' := univᶜ) (compl_subset_compl.2 (subset_univ A)) n
      (localHomologyRestriction N (singleton_subset_iff.2 hx) n)
    rw [← localHomologyRestriction_def _ (subset_univ A), localHomologyRestriction_comp] at h
    exact (ConcreteCategory.congr_hom h.symm (o.fundamentalClass hn)).trans
      ((singularHomologyToLocalHomology_apply _ x _).symm.trans
        (o.singularHomologyToLocalHomology_fundamentalClass hn x))

/-- Scaling an orientation by `u : Rˣ` scales the fundamental class by `u`. -/
@[simp] theorem fundamentalClass_smul (u : Rˣ) :
    (u • o).fundamentalClass hn = (u : R) • o.fundamentalClass hn :=
  ((u • o).eq_fundamentalClass hn fun x ↦ by
    rw [map_smul, o.singularHomologyToLocalHomology_fundamentalClass hn x, smul_apply,
      ModuleLocalOrientation.coe_smul]).symm

/-- Reversing the orientation negates the fundamental class. -/
@[simp] theorem fundamentalClass_neg : (-o).fundamentalClass hn = -o.fundamentalClass hn :=
  ((-o).eq_fundamentalClass hn fun x ↦ by
    rw [map_neg, o.singularHomologyToLocalHomology_fundamentalClass hn x, neg_apply,
      ModuleLocalOrientation.coe_neg]).symm

/-- **The fundamental class of a compact `N`-oriented manifold satisfies `IsFundamentalClass`.** -/
theorem isFundamentalClass_fundamentalClass : IsFundamentalClass (o.fundamentalClass hn) :=
  (isFundamentalClass_iff_forall_isModuleLocalOrientation _).2 fun x ↦ by
    rw [o.singularHomologyToLocalHomology_fundamentalClass hn x]; exact (o x).property

/-- Passing from `o` to its fundamental class and back recovers `o`. -/
@[simp] theorem toModuleOrientation_fundamentalClass :
    (o.isFundamentalClass_fundamentalClass hn).toModuleOrientation (E := E) = o :=
  ext fun x ↦ Subtype.ext (o.singularHomologyToLocalHomology_fundamentalClass hn x)

/-- Passing from a fundamental class `μ` to its induced orientation and back recovers `μ`. -/
@[simp] theorem _root_.TauCeti.IsFundamentalClass.fundamentalClass_toModuleOrientation
    {μ : ((TopCat.toSSet.obj (TopCat.of M)).homology N n : ModuleCat.{w} R)}
    (hμ : IsFundamentalClass μ) :
    (hμ.toModuleOrientation (E := E)).fundamentalClass hn = μ :=
  ((hμ.toModuleOrientation (E := E)).eq_fundamentalClass hn fun _ ↦ rfl).symm

/-- **Orientations and fundamental classes correspond bijectively** on a compact `n`-manifold
(Hatcher, Theorem 3.26). -/
def equivSubtypeIsFundamentalClass (hn : finrank ℝ E = n) :
    ModuleOrientation N M E n ≃
      {μ : ((TopCat.toSSet.obj (TopCat.of M)).homology N n : ModuleCat.{w} R) //
        IsFundamentalClass μ} where
  toFun o := ⟨o.fundamentalClass hn, o.isFundamentalClass_fundamentalClass hn⟩
  invFun μ := μ.2.toModuleOrientation
  left_inv o := o.toModuleOrientation_fundamentalClass hn
  right_inv μ := Subtype.ext (μ.2.fundamentalClass_toModuleOrientation hn)

@[simp] theorem coe_equivSubtypeIsFundamentalClass_apply (hn : finrank ℝ E = n) :
    (equivSubtypeIsFundamentalClass (N := N) (M := M) hn o).val = o.fundamentalClass hn := (rfl)

@[simp] theorem equivSubtypeIsFundamentalClass_symm_apply (hn : finrank ℝ E = n)
    (μ : {μ : ((TopCat.toSSet.obj (TopCat.of M)).homology N n : ModuleCat.{w} R) //
      IsFundamentalClass μ}) :
    (equivSubtypeIsFundamentalClass (N := N) (M := M) (E := E) hn).symm μ =
      μ.2.toModuleOrientation := (rfl)

section Map

open AlgebraicTopology

variable {X Y : Type w} [TopologicalSpace X] [TopologicalSpace Y]

/-- The pushforward `f_*[M] ∈ Hₙ(X; N)` of `o.fundamentalClass hn` along `f : C(M, X)`. -/
def mapFundamentalClass (f : C(M, X)) :
    ((singularHomologyFunctor (ModuleCat.{w} R) n).obj N).obj (TopCat.of X) :=
  (((singularHomologyFunctor (ModuleCat.{w} R) n).obj N).map (TopCat.ofHom f)).hom
    (o.fundamentalClass hn)

theorem mapFundamentalClass_def (f : C(M, X)) :
    o.mapFundamentalClass hn f =
      (((singularHomologyFunctor (ModuleCat.{w} R) n).obj N).map (TopCat.ofHom f)).hom
        (o.fundamentalClass hn) := (rfl)

@[simp] theorem mapFundamentalClass_id :
    o.mapFundamentalClass hn (ContinuousMap.id M) = o.fundamentalClass hn := by
  rw [mapFundamentalClass_def, TopCat.ofHom_id, CategoryTheory.Functor.map_id]; rfl

theorem mapFundamentalClass_comp (g : C(X, Y)) (f : C(M, X)) :
    o.mapFundamentalClass hn (g.comp f) =
      (((singularHomologyFunctor (ModuleCat.{w} R) n).obj N).map (TopCat.ofHom g)).hom
        (o.mapFundamentalClass hn f) := by
  rw [mapFundamentalClass_def, mapFundamentalClass_def, TopCat.ofHom_comp,
    CategoryTheory.Functor.map_comp]; rfl

/-- Homotopic maps push the fundamental class forward to the same class. -/
theorem mapFundamentalClass_eq_of_homotopic {f g : C(M, X)} (h : f.Homotopic g) :
    o.mapFundamentalClass hn f = o.mapFundamentalClass hn g := by
  rw [mapFundamentalClass_def, mapFundamentalClass_def]; congr 2
  exact TopCat.Homotopy.congr_homologyMap_singularChainComplexFunctor (C := ModuleCat.{w} R)
    (f := TopCat.ofHom f) (g := TopCat.ofHom g) h.some _ n

@[simp] theorem mapFundamentalClass_smul (u : Rˣ) (f : C(M, X)) :
    (u • o).mapFundamentalClass hn f = (u : R) • o.mapFundamentalClass hn f := by
  rw [mapFundamentalClass_def, mapFundamentalClass_def, fundamentalClass_smul]
  exact map_smul _ (u : R) _

@[simp] theorem mapFundamentalClass_neg (f : C(M, X)) :
    (-o).mapFundamentalClass hn f = -o.mapFundamentalClass hn f := by
  rw [mapFundamentalClass_def, mapFundamentalClass_def, fundamentalClass_neg]; exact map_neg _ _

theorem singularHomologyπ_mapFundamentalClass (f : C(M, X)) :
    ((TopPair.ofSubset ((univ : Set (TopCat.of X))ᶜ)).singularHomologyπ
      (C := ModuleCat.{w} R) N n).hom (o.mapFundamentalClass hn f) =
      localHomologyMap N f (subset_univ _) n (o.fundamentalClassOn hn isCompact_univ) := by
  have h := congrArg (fun φ ↦ φ.hom (o.fundamentalClass hn))
    (TopPair.singularHomologyπ_naturality (TopPair.ofSubsetMap (X := TopCat.of M)
      (Y := TopCat.of X) (B := (univ : Set M)ᶜ) (B' := (univ : Set X)ᶜ) (TopCat.ofHom f)
      fun _ hx ↦ (hx (mem_univ _)).elim) N n)
  erw [TopPair.ofSubsetMap_fst] at h
  rwa [← o.singularHomologyπ_fundamentalClass hn, localHomologyMap_def, mapFundamentalClass_def,
    TauCeti.singularHomologyFunctor_obj_map]

/-- A homeomorphism `e : M' ≃ₜ M` pushes the fundamental class of `o.comap e.isOpenEmbedding`
forward to `o.fundamentalClass hn`. -/
@[simp] theorem mapFundamentalClass_comap {M' : Type w} [TopologicalSpace M'] [T2Space M']
    [ChartedSpace E M'] [CompactSpace M'] (e : M' ≃ₜ M) :
    (o.comap e.isOpenEmbedding).mapFundamentalClass hn (e : C(M', M)) = o.fundamentalClass hn := by
  refine o.eq_fundamentalClass hn fun y ↦ ?_
  obtain ⟨x, rfl⟩ := e.surjective y
  have hx : (e : C(M', M)) ⁻¹' {e x} ⊆ {x} := fun _ hz ↦ e.injective hz
  refine (singularHomologyToLocalHomology_apply _ (e x) _).trans ?_
  rw [singularHomologyπ_mapFundamentalClass, ← ConcreteCategory.comp_apply,
    localHomologyMap_comp_localHomologyRestriction,
    ← localHomologyRestriction_comp_localHomologyMap (hS := singleton_subset_iff.2 (mem_univ x))
      (h := hx),
    ConcreteCategory.comp_apply, localHomologyRestriction_fundamentalClassOn (hx := mem_univ x),
    comap_apply]
  exact e.isOpenEmbedding.localHomologyMap_moduleLocalOrientationEquiv_symm N x (o (e x)) hx

end Map

end CompactSpace

end Gluing

section Connected

variable {R : Type w} [Ring R] [IsDedekindFiniteMonoid R]
  {M E : Type w} [TopologicalSpace M] [T2Space M]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [ChartedSpace E M]
  [CompactSpace M] [ConnectedSpace M]
  {n : ℕ} (o : ModuleOrientation (ModuleCat.of R R) M E n) (hn : finrank ℝ E = n)

include hn in
private theorem bijective_toSpanSingleton_fundamentalClass :
    Function.Bijective (LinearMap.toSpanSingleton R _ (o.fundamentalClass hn)) := by
  obtain ⟨x⟩ := ConnectedSpace.toNonempty (α := M)
  have hx (r : R) : singularHomologyToLocalHomology (ModuleCat.of R R) x n
      (LinearMap.toSpanSingleton R _ (o.fundamentalClass hn) r) = r • (o x).val := by
    rw [LinearMap.toSpanSingleton_apply, map_smul,
      o.singularHomologyToLocalHomology_fundamentalClass hn x]
  refine ⟨fun r r' h ↦ ?_, fun γ ↦ ?_⟩
  · subst hn
    let e := singularHomologyComplSingletonFinrankIso (ModuleCat.of R R) (chartAt E x)
      (mem_chart_source E x)
    apply ((isModuleLocalOrientation_iff_isUnit e _).1 (o x).property).mul_left_inj.1
    simpa only [hx, map_smul, smul_eq_mul] using
      congrArg (fun γ ↦ e.hom (singularHomologyToLocalHomology (ModuleCat.of R R) x _ γ)) h
  · obtain ⟨r, hr⟩ := (Submodule.span_singleton_eq_top_iff R (o x).val).1
      ((isModuleLocalOrientation_iff _ _ _ _).1 (o x).property)
      (singularHomologyToLocalHomology (ModuleCat.of R R) x n γ)
    exact ⟨r, singularHomologyToLocalHomology_injective (ModuleCat.of R R) hn x ((hx r).trans hr)⟩

/-- **The fundamental class freely generates top homology** (Hatcher, Theorem 3.26(a)). -/
def fundamentalClassLinearEquiv :
    R ≃ₗ[R] ((TopCat.toSSet.obj (TopCat.of M)).homology (ModuleCat.of R R) n : ModuleCat.{w} R) :=
  LinearEquiv.ofBijective _ (o.bijective_toSpanSingleton_fundamentalClass hn)

@[simp] theorem fundamentalClassLinearEquiv_apply (r : R) :
    o.fundamentalClassLinearEquiv hn r = r • o.fundamentalClass hn := (rfl)

theorem fundamentalClassLinearEquiv_one :
    o.fundamentalClassLinearEquiv hn 1 = o.fundamentalClass hn := one_smul R (o.fundamentalClass hn)

/-- On a compact connected `R`-oriented `n`-manifold, every class of `Hₙ(M; R)` is an `R`-multiple
of `o.fundamentalClass hn`. -/
theorem exists_eq_smul_fundamentalClass
    (γ : ((TopCat.toSSet.obj (TopCat.of M)).homology (ModuleCat.of R R) n : ModuleCat.{w} R)) :
    ∃ r : R, γ = r • o.fundamentalClass hn :=
  ⟨(o.fundamentalClassLinearEquiv hn).symm γ,
    ((o.fundamentalClassLinearEquiv hn).apply_symm_apply γ).symm⟩

end Connected

section Integral

variable {M E : Type} [TopologicalSpace M] [T2Space M]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [ChartedSpace E M]
  {n : ℕ} (o : ModuleOrientation (ModuleCat.of ℤ (ULift.{0} ℤ)) M E n) (hn : finrank ℝ E = n)

/-- Compatibility of `ModuleOrientation.fundamentalClassOn` with
`HomologicalOrientation.fundamentalClassOn` in `Type`. -/
@[simp] theorem equivHomologicalOrientation_fundamentalClassOn {A : Set M} (hA : IsCompact A) :
    (equivHomologicalOrientation o).fundamentalClassOn hn hA = o.fundamentalClassOn hn hA :=
  o.eq_fundamentalClassOn hn hA fun x hx ↦
    ((equivHomologicalOrientation o).localHomologyRestriction_fundamentalClassOn hn hA hx).trans
      (coe_equivHomologicalOrientation_apply o x)

/-- Compatibility of `ModuleOrientation.fundamentalClass` with
`HomologicalOrientation.fundamentalClass` in `Type`. -/
@[simp] theorem equivHomologicalOrientation_fundamentalClass [CompactSpace M] :
    (equivHomologicalOrientation o).fundamentalClass hn = o.fundamentalClass hn :=
  o.eq_fundamentalClass hn fun x ↦
    ((equivHomologicalOrientation o).singularHomologyToLocalHomology_fundamentalClass hn x).trans
      (coe_equivHomologicalOrientation_apply o x)

end Integral

section ExtendScalars

variable {R S : Type w} [CommRing R] [CommRing S] (f : R →+* S)
  [PreservesFiniteLimits (ModuleCat.extendScalars.{w, w, w} f)]
  {M E : Type w} [TopologicalSpace M] [T2Space M]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [ChartedSpace E M]
  {n : ℕ} (o : ModuleOrientation (ModuleCat.of R R) M E n) (hn : finrank ℝ E = n)

/-- **Extension of scalars commutes with relative fundamental classes.** -/
theorem fundamentalClassOn_extendScalars {A : Set M} (hA : IsCompact A) :
    (o.extendScalars f).fundamentalClassOn hn hA =
      (localHomologyExtendScalarsIso f A n).hom ((1 : S) ⊗ₜ[R, f] o.fundamentalClassOn hn hA) := by
  refine ((o.extendScalars f).eq_fundamentalClassOn hn hA fun x hx ↦ ?_).symm
  let η := (ModuleCat.extendRestrictScalarsAdj.{w, w, w} f).unit
  let rR := localHomologyRestriction (ModuleCat.of R R) (singleton_subset_iff.2 hx) n
  let rS := localHomologyRestriction (ModuleCat.of S S) (singleton_subset_iff.2 hx) n
  let tA := η.app _ (o.fundamentalClassOn hn hA)
  have htA := (ModuleCat.extendRestrictScalarsAdj_unit_app_apply.{w, w, w} f _
    (o.fundamentalClassOn hn hA)).symm
  have htx : (localHomologyExtendScalarsIso f ({x} : Set M) n).hom (η.app _ (o x).val) =
      (o.extendScalars f x).val :=
    (congrArg (localHomologyExtendScalarsIso f ({x} : Set M) n).hom
      (ModuleCat.extendRestrictScalarsAdj_unit_app_apply.{w, w, w} f _ (o x).val)).trans
      (o.coe_extendScalars_apply f x).symm
  have hcomm : rS ((localHomologyExtendScalarsIso f A n).hom tA) =
      (localHomologyExtendScalarsIso f ({x} : Set M) n).hom
        (((ModuleCat.extendScalars.{w, w, w} f).map rR) tA) :=
    (ConcreteCategory.comp_apply _ _ _).symm.trans ((ConcreteCategory.congr_hom
      (map_localHomologyRestriction_comp_localHomologyExtendScalarsIso_hom f
        (singleton_subset_iff.2 hx) n).symm tA).trans (ConcreteCategory.comp_apply _ _ _))
  have hnat : ((ModuleCat.extendScalars.{w, w, w} f).map rR) tA = η.app _ (o x).val :=
    (ConcreteCategory.congr_hom (η.naturality rR).symm (o.fundamentalClassOn hn hA)).trans
      (congrArg (η.app _) (o.localHomologyRestriction_fundamentalClassOn hn hA hx))
  exact (congrArg (fun u ↦ rS ((localHomologyExtendScalarsIso f A n).hom u)) htA).trans
    (hcomm.trans ((congrArg (localHomologyExtendScalarsIso f ({x} : Set M) n).hom hnat).trans htx))

/-- **Extension of scalars commutes with fundamental classes.** -/
theorem fundamentalClass_extendScalars [CompactSpace M] :
    (o.extendScalars f).fundamentalClass hn =
      (singularHomologyExtendScalarsIso f M n).hom ((1 : S) ⊗ₜ[R, f] o.fundamentalClass hn) := by
  refine ((o.extendScalars f).eq_fundamentalClass hn fun x ↦ ?_).symm
  let P := localHomology (A := ModuleCat.{w} R) (ModuleCat.of R R) ({x} : Set M) n
  let η := (ModuleCat.extendRestrictScalarsAdj.{w, w, w} f).unit.app P
  have h1 := congrArg (localHomologyExtendScalarsIso f ({x} : Set M) n).hom
    (ModuleCat.extendRestrictScalarsAdj_unit_app_apply.{w, w, w} f P
      (singularHomologyToLocalHomology (ModuleCat.of R R) x n (o.fundamentalClass hn))).symm
  have h2 : (localHomologyExtendScalarsIso f ({x} : Set M) n).hom (η (o x).val) =
      (o.extendScalars f x).val :=
    (congrArg (localHomologyExtendScalarsIso f ({x} : Set M) n).hom
      (ModuleCat.extendRestrictScalarsAdj_unit_app_apply.{w, w, w} f P _)).trans
      (o.coe_extendScalars_apply f x).symm
  exact (singularHomologyToLocalHomology_singularHomologyExtendScalarsIso_hom_tmul f x n 1
    (o.fundamentalClass hn)).trans (h1.trans
      ((congrArg (fun z ↦ (localHomologyExtendScalarsIso f ({x} : Set M) n).hom (η z))
        (o.singularHomologyToLocalHomology_fundamentalClass hn x)).trans h2))

end ExtendScalars

end ModuleOrientation

section OrientationFree

variable {M : Type w} {E : Type v} [TopologicalSpace M] [T2Space M] [CompactSpace M]
  [NormedAddCommGroup E] [NormedSpace ℝ E] {n : ℕ}

private abbrev ModelSpace (E : Type v) [NormedAddCommGroup E] [NormedSpace ℝ E] :=
  EuclideanSpace ℝ (ULift.{w} (Fin (finrank ℝ E)))

private theorem finrank_modelSpace (hn : finrank ℝ E = n) : finrank ℝ (ModelSpace.{w} E) = n :=
  (finrank_euclideanSpace_ulift_fin.{w} (finrank ℝ E)).trans hn

variable [FiniteDimensional ℝ E] [ChartedSpace E M]

@[instance_reducible] private def chartedSpaceEuclideanUlift :
    ChartedSpace (ModelSpace.{w} E) M :=
  let e := (ContinuousLinearEquiv.ofFinrankEq (finrank_modelSpace.{w} (E := E) rfl)).toHomeomorph
  letI : ChartedSpace (ModelSpace.{w} E) E := e.isLocalHomeomorph.chartedSpace e.surjective
  ChartedSpace.comp (ModelSpace.{w} E) E M

/-- **Existence and uniqueness of a `K`-fundamental class when `Subsingleton Kˣ`**
(Hatcher, Theorem 3.26). -/
theorem existsUnique_isFundamentalClass_of_subsingleton_units {K : Type w} [CommRing K]
    [Subsingleton Kˣ] (hn : finrank ℝ E = n) :
    ∃! μ : ((TopCat.toSSet.obj (TopCat.of M)).homology (ModuleCat.of K K) n : ModuleCat.{w} K),
      IsFundamentalClass μ := by
  let _ := chartedSpaceEuclideanUlift (M := M) (E := E)
  have hE' := finrank_modelSpace.{w} hn
  let e := ModuleOrientation.equivSubtypeIsFundamentalClass (N := ModuleCat.of K K) (M := M) hE'
  have _ := ModuleOrientation.uniqueOfSubsingletonUnits (M := M) (K := K) hE'
  exact ⟨(e default).val, (e default).property, fun μ hμ ↦
    congrArg Subtype.val
      (e.symm.injective (Subsingleton.elim (e.symm ⟨μ, hμ⟩) (e.symm (e default))))⟩

/-- **Every compact simply connected `n`-manifold admits an `R`-fundamental class** over any ring
`R`. -/
theorem exists_isFundamentalClass_of_simplyConnectedSpace [SimplyConnectedSpace M] {R : Type w}
    [Ring R] (hn : finrank ℝ E = n) :
    ∃ μ : ((TopCat.toSSet.obj (TopCat.of M)).homology (ModuleCat.of R R) n : ModuleCat.{w} R),
      IsFundamentalClass μ := by
  let _ := chartedSpaceEuclideanUlift (M := M) (E := E)
  have hE' := finrank_modelSpace.{w} hn
  obtain ⟨o⟩ := ModuleOrientation.nonempty_of_simplyConnectedSpace (M := M) (R := R) hE'
  exact ⟨o.fundamentalClass hE', o.isFundamentalClass_fundamentalClass hE'⟩

/-- **Every compact topological `n`-manifold admits an `R`-fundamental class when `(2 : R) = 0`**
(Hatcher, Section 3.3, Theorem 3.26). -/
theorem exists_isFundamentalClass_of_two_eq_zero {R : Type w} [CommRing R] (hn : finrank ℝ E = n)
    (h2 : (2 : R) = 0) :
    ∃ μ : ((TopCat.toSSet.obj (TopCat.of M)).homology (ModuleCat.of R R) n : ModuleCat.{w} R),
      IsFundamentalClass μ := by
  let _ := chartedSpaceEuclideanUlift (M := M) (E := E)
  have hE' := finrank_modelSpace.{w} hn
  let o := ModuleOrientation.ofTwoEqZero (M := M) hE' h2
  exact ⟨o.fundamentalClass hE', o.isFundamentalClass_fundamentalClass hE'⟩

section Connected

variable [ConnectedSpace M] {R : Type w} [Ring R] [IsDedekindFiniteMonoid R]
  {μ : ((TopCat.toSSet.obj (TopCat.of M)).homology (ModuleCat.of R R) n : ModuleCat.{w} R)}

/-- **A fundamental class on a compact connected `n`-manifold freely generates top homology**
(Hatcher, Theorem 3.26(a)). -/
theorem IsFundamentalClass.bijective_toSpanSingleton (hμ : IsFundamentalClass μ)
    (hn : finrank ℝ E = n) : Function.Bijective (LinearMap.toSpanSingleton R _ μ) := by
  let _ := chartedSpaceEuclideanUlift (M := M) (E := E)
  have hE' := finrank_modelSpace.{w} hn
  rw [← hμ.fundamentalClass_toModuleOrientation (E := ModelSpace.{w} E) hE']
  exact ((hμ.toModuleOrientation (E := ModelSpace.{w} E)).fundamentalClassLinearEquiv
    hE').bijective

/-- **Linear isomorphism `R ≃ₗ[R] Hₙ(M; R)` generated by an `R`-fundamental class** on a compact
connected `n`-manifold. -/
def IsFundamentalClass.linearEquiv (hμ : IsFundamentalClass μ) (hn : finrank ℝ E = n) :
    R ≃ₗ[R] ((TopCat.toSSet.obj (TopCat.of M)).homology (ModuleCat.of R R) n : ModuleCat.{w} R) :=
  LinearEquiv.ofBijective _ (hμ.bijective_toSpanSingleton hn)

@[simp] theorem IsFundamentalClass.linearEquiv_apply (hμ : IsFundamentalClass μ)
    (hn : finrank ℝ E = n) (r : R) : hμ.linearEquiv hn r = r • μ := (rfl)

theorem IsFundamentalClass.linearEquiv_one (hμ : IsFundamentalClass μ) (hn : finrank ℝ E = n) :
    hμ.linearEquiv hn 1 = μ := one_smul R μ

end Connected

/-- **Top homology of a compact connected `n`-manifold when `(2 : R) = 0`**: `Hₙ(M; R)` is linearly
isomorphic to `R` with no orientability hypothesis on `M` (Hatcher, Theorem 3.26). -/
theorem nonempty_singularHomologyLinearEquiv_of_two_eq_zero [ConnectedSpace M] {R : Type w}
    [CommRing R] (hn : finrank ℝ E = n) (h2 : (2 : R) = 0) :
    Nonempty
      (R ≃ₗ[R]
        ((TopCat.toSSet.obj (TopCat.of M)).homology (ModuleCat.of R R) n : ModuleCat.{w} R)) :=
  let ⟨_, hμ⟩ := exists_isFundamentalClass_of_two_eq_zero hn h2
  ⟨hμ.linearEquiv hn⟩

end OrientationFree

end TauCeti
