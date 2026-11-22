/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module
public import TauCeti.AlgebraicTopology.Singular.LocalHomology.IsFundamentalClass
public import TauCeti.AlgebraicTopology.Singular.LocalHomology.Orientation.Module.Basic
import TauCeti.Geometry.Manifold.ModelTransport.Finrank
/-!
# Fundamental classes of module-oriented manifolds

For Hausdorff `M` modelled on an `n`-dimensional real normed space `E`, ring `R` in `M`'s universe,
and `R`-module `N`, `o : ModuleOrientation N M E n` glues uniquely along compact `A ⊆ M` to
`o.fundamentalClassOn hn hA` in `Hₙ(M, M ∖ A; N)` (Hatcher, Lemma 3.27), and for compact `M` to
`o.fundamentalClass hn` in `Hₙ(M; N)`, giving `equivSubtypeIsFundamentalClass` (Thm 3.26). For
compact connected `M` over a Dedekind-finite ring `R`, `r ↦ r • μ` gives `R ≃ₗ[R] Hₙ(M; R)`
(`fundamentalClassEquiv`, `IsFundamentalClass.linearEquiv`). Supplies `IsFundamentalClass` witnesses
and top-degree homology isomorphisms for closed-manifold Poincaré duality over arbitrary rings. For
compact `M : Type w` modelled on `E : Type v` (universe-decoupled from `M, R : Type w`),
orientation-free results via `ChartedSpace.ofFinrankEq` establish:
* `exists_isFundamentalClass_of_simplyConnectedSpace`: existence over any ring `R`.
* `exists_isFundamentalClass_of_two_eq_zero`: existence over `[CommRing R]`, `(2 : R) = 0`.
* `IsFundamentalClass.linearEquiv`: `R ≃ₗ[R] Hₙ(M; R)` (`[ConnectedSpace M]`, Dedekind-finite `R`).
* `nonempty_linearEquiv_singularHomology_of_two_eq_zero`: `Nonempty (R ≃ₗ[R] Hₙ(M; R))` for
  `[CommRing R]`, `(2 : R) = 0`, `[ConnectedSpace M]`.
Adapts `LocalHomology.FundamentalClass` (`existsUnique_localHomologyRestriction_eq_of_invariant` and
`existsUnique_singularHomology_localHomologyRestriction_eq_of_invariant`; Hatcher, §3.3). -/
public noncomputable section
open CategoryTheory Limits Module Set Topology
open CategoryTheory.ConcreteCategory (congr_hom)
open ModuleCat (of)
open ModuleCat.ExtendScalars (apply_tmul_of_comm)
open TopCat (toSSet ofHom)
open scoped ChangeOfRings
universe w v u
namespace TauCeti
section General
variable {M : Type w} [TopologicalSpace M] {R : Type u} [Ring R] {N : ModuleCat.{w} R} {n : ℕ}
/-- `TauCeti.IsFundamentalClass` expressed via `TopPair.singularHomologyπ`. -/
theorem isFundamentalClass_iff_singularHomologyπ
    (μ : ↑((toSSet.obj (TopCat.of M)).homology N n)) : IsFundamentalClass μ ↔ ∀ x : M,
      Submodule.span R {((TopPair.ofSubset ({x}ᶜ : Set (TopCat.of M))).singularHomologyπ
        (C := ModuleCat.{w} R) N n).hom μ} = ⊤ :=
  (isFundamentalClass_iff μ).trans
    (forall_congr' fun _ ↦ by rw [singularHomologyToLocalHomology_eq_singularHomologyπ])
/-- An isomorphism of coefficient modules `e : N ≅ N'` preserves fundamental classes. -/
theorem IsFundamentalClass.map_coefficientsIso {N' : ModuleCat.{w} R} (e : N ≅ N')
    {μ : ↑((toSSet.obj (TopCat.of M)).homology N n)} (hμ : IsFundamentalClass μ) :
    IsFundamentalClass
      ((SSet.homologyIsoOfCoefficientsIso e (toSSet.obj (TopCat.of M)) n).hom μ) :=
  (isFundamentalClass_iff _).2 fun x ↦ by
    rw [singularHomologyToLocalHomology_homologyIsoOfCoefficientsIso_hom_apply]
    exact (ModuleCat.span_singleton_apply_eq_top_iff _).2 ((isFundamentalClass_iff μ).1 hμ x)
section
variable {R S : Type w} [CommRing R] [CommRing S] (f : R →+* S)
  [PreservesFiniteLimits (ModuleCat.extendScalars.{w, w, w} f)]
/-- Exact scalar extension along `f : R →+* S` preserves fundamental classes for arbitrary `N`. -/
theorem IsFundamentalClass.extendScalarsObj {N : ModuleCat.{w} R}
    {μ : ↑((toSSet.obj (TopCat.of M)).homology N n)} (hμ : IsFundamentalClass μ) :
    IsFundamentalClass ((SSet.homologyObjIso (ModuleCat.extendScalars.{w, w, w} f) N
      (toSSet.obj (TopCat.of M)) n).hom ((1 : S) ⊗ₜ[R, f] μ)) :=
  (isFundamentalClass_iff _).2 fun x ↦ by
    rw [singularHomologyToLocalHomology_homologyObjIso_hom_tmul]
    exact (ModuleCat.span_singleton_apply_eq_top_iff _).2
      (ModuleCat.ExtendScalars.span_singleton_one_tmul_eq_top f ((isFundamentalClass_iff μ).1 hμ x))
/-- **Exact extension of scalars preserves fundamental classes** for ring coefficients. -/
theorem IsFundamentalClass.extendScalars
    {μ : ↑((toSSet.obj (TopCat.of M)).homology (of R R) n)} (hμ : IsFundamentalClass μ) :
    IsFundamentalClass ((f.singularHomologyExtendScalarsIso M n).hom ((1 : S) ⊗ₜ[R, f] μ)) :=
  (isFundamentalClass_iff _).2 fun x ↦ by
    rw [singularHomologyToLocalHomology_singularHomologyExtendScalarsIso_hom_tmul]
    exact (ModuleCat.span_singleton_apply_eq_top_iff _).2
      (ModuleCat.ExtendScalars.span_singleton_one_tmul_eq_top f ((isFundamentalClass_iff μ).1 hμ x))
end
/-- `μ ∈ Hₙ(M; N)` is a fundamental class iff each local image is a local `N`-orientation. -/
theorem isFundamentalClass_iff_forall_isModuleLocalOrientation
    (μ : ↑((toSSet.obj (TopCat.of M)).homology N n)) : IsFundamentalClass μ ↔
      ∀ x : M, IsModuleLocalOrientation N x n (singularHomologyToLocalHomology N x n μ) :=
  (isFundamentalClass_iff μ).trans
    (forall_congr' fun x ↦ (isModuleLocalOrientation_iff N x n _).symm)
variable {E : Type w} [T2Space M] [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [ChartedSpace E M] {d : ℕ}
/-- **A fundamental class determines an `N`-orientation**: its local images generate every fibre and
are invariant under path transport. -/
def IsFundamentalClass.toModuleOrientation {μ : ↑((toSSet.obj (TopCat.of M)).homology N d)}
    (hμ : IsFundamentalClass μ) : ModuleOrientation N M E d :=
  ⟨fun x ↦ ⟨singularHomologyToLocalHomology N x d μ,
      (isFundamentalClass_iff_forall_isModuleLocalOrientation μ).1 hμ x⟩,
   fun g ↦ Subtype.ext <| (coe_moduleLocalOrientationTransport N M E d g _).trans
      (localHomologyTransport_singularHomologyToLocalHomology (E := E) g μ)⟩
@[simp] theorem IsFundamentalClass.coe_toModuleOrientation_apply
    {μ : ↑((toSSet.obj (TopCat.of M)).homology N d)} (hμ : IsFundamentalClass μ) (x : M) :
    (hμ.toModuleOrientation (E := E) x).val = singularHomologyToLocalHomology N x d μ := (rfl)
end General
namespace ModuleOrientation
section Gluing
variable {R : Type w} [Ring R] {N : ModuleCat.{w} R} {M E : Type w} [TopologicalSpace M]
  [T2Space M] [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [ChartedSpace E M]
  {n : ℕ} (o : ModuleOrientation N M E n) (hn : finrank ℝ E = n)
section Compact
variable {A : Set M} (hA : IsCompact A)
include hn hA in
private theorem existsUnique_fundamentalClassOn : ∃! γ : ↑(localHomology N A n),
    ∀ x (hx : x ∈ A), localHomologyRestriction N (singleton_subset_iff.2 hx) n γ = (o x).val :=
  existsUnique_localHomologyRestriction_eq_of_invariant N hn hA (fun x ↦ (o x).val)
    o.localHomologyTransport_coe_apply
/-- **Relative fundamental class along compact `A ⊆ M`**: unique class in `Hₙ(M, M ∖ A; N)`
restricting to `o x` at each `x ∈ A` (Hatcher, Lemma 3.27). -/
def fundamentalClassOn : ↑(localHomology N A n) :=
  (o.existsUnique_fundamentalClassOn hn hA).exists.choose
theorem localHomologyRestriction_fundamentalClassOn {x : M} (hx : x ∈ A) :
    localHomologyRestriction N (singleton_subset_iff.2 hx) n (o.fundamentalClassOn hn hA) =
      (o x).val := (o.existsUnique_fundamentalClassOn hn hA).exists.choose_spec x hx
/-- **Uniqueness of the relative fundamental class along `A`.** -/
theorem eq_fundamentalClassOn {γ : ↑(localHomology N A n)} (hγ : ∀ x (hx : x ∈ A),
    localHomologyRestriction N (singleton_subset_iff.2 hx) n γ = (o x).val) :
    γ = o.fundamentalClassOn hn hA := (o.existsUnique_fundamentalClassOn hn hA).unique hγ fun _ hx ↦
  o.localHomologyRestriction_fundamentalClassOn hn hA hx
@[simp] theorem localHomologyRestriction_fundamentalClassOn_of_subset {B : Set M} (hB : IsCompact B)
    (hBA : B ⊆ A) : localHomologyRestriction N hBA n (o.fundamentalClassOn hn hA) =
      o.fundamentalClassOn hn hB := o.eq_fundamentalClassOn hn hB fun _ hx ↦ by
  rw [localHomologyRestriction_comp_apply]
  exact o.localHomologyRestriction_fundamentalClassOn hn hA (hBA hx)
@[simp] theorem fundamentalClassOn_singleton (x : M) (hx : IsCompact ({x} : Set M)) :
    o.fundamentalClassOn hn hx = (o x).val := by
  rw [← o.localHomologyRestriction_fundamentalClassOn hn hx (mem_singleton x),
    localHomologyRestriction_refl, ModuleCat.id_apply]
@[simp] theorem fundamentalClassOn_smul (u : Rˣ) :
    (u • o).fundamentalClassOn hn hA = (u : R) • o.fundamentalClassOn hn hA :=
  ((u • o).eq_fundamentalClassOn hn hA fun x hx ↦ by
    rw [map_smul, o.localHomologyRestriction_fundamentalClassOn hn hA hx]; rfl).symm
@[simp] theorem fundamentalClassOn_neg :
    (-o).fundamentalClassOn hn hA = -o.fundamentalClassOn hn hA :=
  ((-o).eq_fundamentalClassOn hn hA fun x hx ↦ by
    rw [map_neg, o.localHomologyRestriction_fundamentalClassOn hn hA hx]; rfl).symm
@[simp] theorem fundamentalClassOn_equivOfCoefficientsIso {N' : ModuleCat.{w} R} (e : N ≅ N') :
    (equivOfCoefficientsIso e o).fundamentalClassOn hn hA =
      (localHomologyIsoOfCoefficientsIso e A n).hom (o.fundamentalClassOn hn hA) :=
  ((equivOfCoefficientsIso e o).eq_fundamentalClassOn hn hA fun x hx ↦ by
    have h := congr_hom (localHomologyRestriction_comp_localHomologyIsoOfCoefficientsIso_hom e
      (singleton_subset_iff.2 hx) n) (o.fundamentalClassOn hn hA); simp only [comp_apply] at h
    rw [← h, o.localHomologyRestriction_fundamentalClassOn hn hA hx]; simp).symm
end Compact
section OpenEmbedding
variable {X : Type w} [TopologicalSpace X] [T1Space X] {ι : M → X} (hι : IsOpenEmbedding ι)
/-- Along an open embedding `ι : M → X` (`T₁` target, closed `T ⊆ range ι`, compact `S = ι ⁻¹' T`),
a class of `Hₙ(X, X ∖ T; N)` restricting to excised `o x` equals `ι_* [M]_S`. -/
theorem eq_localHomologyMap_fundamentalClassOn {S : Set M} (hS : IsCompact S) {T : Set X}
    (h : ι ⁻¹' T = S) (hT : IsClosed T) (hTι : T ⊆ range ι) {γ : ↑(localHomology N T n)}
    (hγ : ∀ x (hx : ι x ∈ T), localHomologyRestriction N (singleton_subset_iff.2 hx) n γ =
      (localHomologyIsoOfIsOpenEmbedding N hι x n).hom (o x).val) :
    γ = localHomologyMap N ⟨ι, hι.continuous⟩ h.subset n (o.fundamentalClassOn hn hS) := by
  have := isIso_localHomologyMap (A := ModuleCat.{w} R) N ⟨ι, hι.continuous⟩ hι h hT hTι n
  set a := localHomologyMap (A := ModuleCat.{w} R) N ⟨ι, hι.continuous⟩ h.subset n
  suffices hδ : inv a γ = o.fundamentalClassOn hn hS by
    rw [← hδ, ← comp_apply, IsIso.inv_hom_id, ModuleCat.id_apply]
  refine o.eq_fundamentalClassOn hn hS fun x hx ↦
    ConcreteCategory.injective_of_mono_of_preservesPullback
      (localHomologyIsoOfIsOpenEmbedding N hι x n).hom ?_
  have hxT : ι x ∈ T := h.symm.subset hx
  rw [← comp_apply, ← localHomologyMap_comp_localHomologyRestriction_singleton _ hι h.subset hxT,
    comp_apply, ← comp_apply (inv a), IsIso.inv_hom_id, ModuleCat.id_apply, hγ x hxT]
/-- **Open embeddings carry relative fundamental classes to relative fundamental classes.** -/
theorem localHomologyMap_fundamentalClassOn_comap {U : Type w} [TopologicalSpace U] [T2Space U]
    [ChartedSpace E U] {j : C(U, M)} (hj : IsOpenEmbedding j) {K : Set U} (hK : IsCompact K) :
    localHomologyMap N j (hj.injective.preimage_image K).subset n
        ((o.comap hj).fundamentalClassOn hn hK) = o.fundamentalClassOn hn (hK.image j.continuous) :=
  o.eq_fundamentalClassOn hn _ fun _ ⟨x, hx, hx'⟩ ↦ by
    subst hx'; have hjx : j ⁻¹' {j x} ⊆ {x} := fun _ hz ↦ hj.injective hz
    have hox : localHomologyMap N j hjx n (o.comap hj x).val = (o (j x)).val := by
      rw [← moduleLocalOrientationEquiv_comap_apply o hj x,
        IsOpenEmbedding.coe_moduleLocalOrientationEquiv, localHomologyIsoOfIsOpenEmbedding_hom,
        localHomologyMap_congr _ (ContinuousMap.ext fun _ ↦ rfl : ⟨j, hj.continuous⟩ = j)]
    rw [← hox, ← (o.comap hj).localHomologyRestriction_fundamentalClassOn hn hK hx, ← comp_apply,
      ← comp_apply, localHomologyMap_comp_localHomologyRestriction,
      localHomologyRestriction_comp_localHomologyMap]
end OpenEmbedding
section CompactSpace
variable [CompactSpace M]
include hn in
private theorem existsUnique_fundamentalClass : ∃! γ : ↑((toSSet.obj (TopCat.of M)).homology N n),
    ∀ x : M, singularHomologyToLocalHomology N x n γ = (o x).val :=
  existsUnique_singularHomology_localHomologyRestriction_eq_of_invariant N hn (fun x ↦ (o x).val)
    o.localHomologyTransport_coe_apply
/-- **Fundamental class of a compact `N`-oriented manifold**: unique class of `Hₙ(M; N)` mapping to
`o x` in `Hₙ(M, M ∖ {x}; N)` at every `x` (Hatcher, Theorem 3.26). -/
def fundamentalClass : ↑((toSSet.obj (TopCat.of M)).homology N n) :=
  (o.existsUnique_fundamentalClass hn).exists.choose
@[simp] theorem singularHomologyToLocalHomology_fundamentalClass (x : M) :
    singularHomologyToLocalHomology N x n (o.fundamentalClass hn) = (o x).val :=
  (o.existsUnique_fundamentalClass hn).exists.choose_spec x
/-- **Uniqueness of the fundamental class.** -/
theorem eq_fundamentalClass {γ : ↑((toSSet.obj (TopCat.of M)).homology N n)}
    (hγ : ∀ x : M, singularHomologyToLocalHomology N x n γ = (o x).val) :
    γ = o.fundamentalClass hn := (o.existsUnique_fundamentalClass hn).unique hγ fun x ↦
  o.singularHomologyToLocalHomology_fundamentalClass hn x
theorem singularHomologyπ_fundamentalClass {A : Set M} (hA : IsCompact A) :
    ((TopPair.ofSubset (Aᶜ : Set (TopCat.of M))).singularHomologyπ
      (C := ModuleCat.{w} R) N n).hom (o.fundamentalClass hn) = o.fundamentalClassOn hn hA :=
  o.eq_fundamentalClassOn hn hA fun x hx ↦ by
    have h := TopPair.singularHomologyπ_comp_singularHomologyMap_ofSubsetMap_id_assoc N
      (X := TopCat.of M) (S := Aᶜ) (S' := univᶜ) (compl_subset_compl.2 (subset_univ A)) n
      (localHomologyRestriction N (singleton_subset_iff.2 hx) n)
    rw [← localHomologyRestriction_def _ (subset_univ A), localHomologyRestriction_comp] at h
    exact (comp_apply _ _ _).symm.trans ((congr_hom h.symm (o.fundamentalClass hn)).trans
      ((comp_apply _ _ _).trans ((singularHomologyToLocalHomology_apply _ x _).symm.trans
        (o.singularHomologyToLocalHomology_fundamentalClass hn x))))
@[simp] theorem fundamentalClass_smul (u : Rˣ) :
    (u • o).fundamentalClass hn = (u : R) • o.fundamentalClass hn :=
  ((u • o).eq_fundamentalClass hn fun x ↦ by
    rw [map_smul, o.singularHomologyToLocalHomology_fundamentalClass hn x]; rfl).symm
@[simp] theorem fundamentalClass_neg : (-o).fundamentalClass hn = -o.fundamentalClass hn :=
  ((-o).eq_fundamentalClass hn fun x ↦ by
    rw [map_neg, o.singularHomologyToLocalHomology_fundamentalClass hn x]; rfl).symm
@[simp] theorem fundamentalClass_equivOfCoefficientsIso {N' : ModuleCat.{w} R} (e : N ≅ N') :
    (equivOfCoefficientsIso e o).fundamentalClass hn = (SSet.homologyIsoOfCoefficientsIso e
      (toSSet.obj (TopCat.of M)) n).hom (o.fundamentalClass hn) :=
  ((equivOfCoefficientsIso e o).eq_fundamentalClass hn fun x ↦ by
    rw [singularHomologyToLocalHomology_homologyIsoOfCoefficientsIso_hom_apply,
      o.singularHomologyToLocalHomology_fundamentalClass hn x]; simp).symm
/-- **The fundamental class of a compact `N`-oriented manifold satisfies `IsFundamentalClass`.** -/
theorem isFundamentalClass_fundamentalClass : IsFundamentalClass (o.fundamentalClass hn) :=
  (isFundamentalClass_iff_forall_isModuleLocalOrientation _).2 fun x ↦ by
    rw [o.singularHomologyToLocalHomology_fundamentalClass hn x]; exact (o x).property
@[simp] theorem toModuleOrientation_fundamentalClass :
    (o.isFundamentalClass_fundamentalClass hn).toModuleOrientation (E := E) = o :=
  ext fun x ↦ Subtype.ext (o.singularHomologyToLocalHomology_fundamentalClass hn x)
@[simp] theorem _root_.TauCeti.IsFundamentalClass.fundamentalClass_toModuleOrientation
    {μ : ↑((toSSet.obj (TopCat.of M)).homology N n)} (hμ : IsFundamentalClass μ) :
    (hμ.toModuleOrientation (E := E)).fundamentalClass hn = μ :=
  ((hμ.toModuleOrientation (E := E)).eq_fundamentalClass hn fun x ↦
    (hμ.coe_toModuleOrientation_apply (E := E) x).symm).symm
/-- **Orientations and fundamental classes correspond** on compact `n`-manifolds (Thm 3.26). -/
def equivSubtypeIsFundamentalClass (hn : finrank ℝ E = n) : ModuleOrientation N M E n ≃
      {μ : ↑((toSSet.obj (TopCat.of M)).homology N n) // IsFundamentalClass μ} :=
  ⟨fun o ↦ ⟨o.fundamentalClass hn, o.isFundamentalClass_fundamentalClass hn⟩,
   fun μ ↦ μ.property.toModuleOrientation, fun o ↦ o.toModuleOrientation_fundamentalClass hn,
   fun μ ↦ Subtype.ext (μ.property.fundamentalClass_toModuleOrientation hn)⟩
@[simp] theorem coe_equivSubtypeIsFundamentalClass_apply (hn : finrank ℝ E = n) :
    (equivSubtypeIsFundamentalClass (N := N) (M := M) hn o).val = o.fundamentalClass hn := (rfl)
@[simp] theorem equivSubtypeIsFundamentalClass_symm_apply (hn : finrank ℝ E = n)
    (μ : {μ : ↑((toSSet.obj (TopCat.of M)).homology N n) // IsFundamentalClass μ}) :
    (equivSubtypeIsFundamentalClass (N := N) (M := M) (E := E) hn).symm μ =
      μ.property.toModuleOrientation := (rfl)
section Map
open AlgebraicTopology
variable {X Y : Type w} [TopologicalSpace X] [TopologicalSpace Y]
/-- The pushforward `f_*[M] ∈ Hₙ(X; N)` of `o.fundamentalClass hn` along `f : C(M, X)`. -/
def mapFundamentalClass (f : C(M, X)) :
    ((singularHomologyFunctor (ModuleCat.{w} R) n).obj N).obj (TopCat.of X) :=
  (((singularHomologyFunctor (ModuleCat.{w} R) n).obj N).map (ofHom f)).hom (o.fundamentalClass hn)
theorem mapFundamentalClass_def (f : C(M, X)) : o.mapFundamentalClass hn f =
    (((singularHomologyFunctor (ModuleCat.{w} R) n).obj N).map (ofHom f)).hom
      (o.fundamentalClass hn) := (rfl)
@[simp] theorem mapFundamentalClass_id :
    o.mapFundamentalClass hn (ContinuousMap.id M) = o.fundamentalClass hn := by
  rw [mapFundamentalClass_def, TopCat.ofHom_id, CategoryTheory.Functor.map_id]
  exact ModuleCat.id_apply _ (o.fundamentalClass hn)
theorem mapFundamentalClass_comp (g : C(X, Y)) (f : C(M, X)) : o.mapFundamentalClass hn (g.comp f) =
      (((singularHomologyFunctor (ModuleCat.{w} R) n).obj N).map (ofHom g)).hom
        (o.mapFundamentalClass hn f) := by
  rw [mapFundamentalClass_def, mapFundamentalClass_def, TopCat.ofHom_comp,
    CategoryTheory.Functor.map_comp]; exact comp_apply _ _ _
theorem mapFundamentalClass_eq_of_homotopic {f g : C(M, X)} (h : f.Homotopic g) :
    o.mapFundamentalClass hn f = o.mapFundamentalClass hn g := by
  rw [mapFundamentalClass_def, mapFundamentalClass_def]; congr 2
  exact TopCat.Homotopy.congr_homologyMap_singularChainComplexFunctor (C := ModuleCat.{w} R)
    (f := ofHom f) (g := ofHom g) h.some _ n
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
      (Y := TopCat.of X) (B := (univ : Set M)ᶜ) (B' := (univ : Set X)ᶜ) (ofHom f)
      fun _ hx ↦ (hx (mem_univ _)).elim) N n)
  -- `(TopPair.ofSubset _).fst` is `TopCat.of M` definitionally, so `erw` identifies the source
  -- of `TopPair.ofSubsetMap_fst` across the `TopPair.ofSubset` wrapper.
  erw [TopPair.ofSubsetMap_fst] at h
  rw [← o.singularHomologyπ_fundamentalClass hn, localHomologyMap_def, mapFundamentalClass_def,
    TauCeti.singularHomologyFunctor_obj_map]
  exact (comp_apply _ _ _).symm.trans (h.trans (comp_apply _ _ _))
@[simp] theorem mapFundamentalClass_comap {M' : Type w} [TopologicalSpace M'] [T2Space M']
    [ChartedSpace E M'] [CompactSpace M'] (e : M' ≃ₜ M) :
    (o.comap e.isOpenEmbedding).mapFundamentalClass hn (e : C(M', M)) = o.fundamentalClass hn := by
  refine o.eq_fundamentalClass hn fun y ↦ ?_; obtain ⟨x, rfl⟩ := e.surjective y
  have hx : (e : C(M', M)) ⁻¹' {e x} ⊆ {x} := fun _ hz ↦ e.injective hz
  refine (singularHomologyToLocalHomology_apply _ (e x) _).trans ?_
  rw [singularHomologyπ_mapFundamentalClass, ← comp_apply,
    localHomologyMap_comp_localHomologyRestriction,
    ← localHomologyRestriction_comp_localHomologyMap (hS := singleton_subset_iff.2 (mem_univ x))
      (h := hx), comp_apply, localHomologyRestriction_fundamentalClassOn (hx := mem_univ x),
    comap_apply]
  exact e.isOpenEmbedding.localHomologyMap_moduleLocalOrientationEquiv_symm N x (o (e x)) hx
@[simp] theorem mapFundamentalClass_comap_comp {M' : Type w} [TopologicalSpace M'] [T2Space M']
    [ChartedSpace E M'] [CompactSpace M'] (e : M' ≃ₜ M) (f : C(M, X)) :
    (o.comap e.isOpenEmbedding).mapFundamentalClass hn (f.comp (e : C(M', M))) =
      o.mapFundamentalClass hn f := by
  rw [mapFundamentalClass_comp, mapFundamentalClass_comap, mapFundamentalClass_def]
end Map
end CompactSpace
end Gluing
section Connected
variable {R : Type w} [Ring R] [IsDedekindFiniteMonoid R] {M E : Type w} [TopologicalSpace M]
  [T2Space M] [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [ChartedSpace E M]
  [CompactSpace M] [ConnectedSpace M] {n : ℕ} (o : ModuleOrientation (of R R) M E n)
  (hn : finrank ℝ E = n)
include hn in
private theorem bijective_toSpanSingleton_fundamentalClass :
    Function.Bijective (LinearMap.toSpanSingleton R _ (o.fundamentalClass hn)) := by
  obtain ⟨x⟩ := ConnectedSpace.toNonempty (α := M)
  have hx (r : R) : singularHomologyToLocalHomology (of R R) x n
      (LinearMap.toSpanSingleton R _ (o.fundamentalClass hn) r) = r • (o x).val := by
    rw [LinearMap.toSpanSingleton_apply, map_smul,
      o.singularHomologyToLocalHomology_fundamentalClass hn x]
  refine ⟨fun r r' h ↦ ?_, fun γ ↦ ?_⟩
  · subst hn; let e := (singularHomologyComplSingletonFinrankIso (of R R) (chartAt E x)
      (mem_chart_source E x)).toLinearEquiv
    apply ((isModuleLocalOrientation_iff_isUnit e _).1 (o x).property).mul_left_inj.1
    simpa only [hx, map_smul, smul_eq_mul] using
      congrArg (fun γ ↦ e (singularHomologyToLocalHomology (of R R) x _ γ)) h
  · obtain ⟨r, hr⟩ := (Submodule.span_singleton_eq_top_iff R (o x).val).1
      ((isModuleLocalOrientation_iff _ _ _ _).1 (o x).property)
      (singularHomologyToLocalHomology (of R R) x n γ)
    exact ⟨r, singularHomologyToLocalHomology_injective (of R R) hn x ((hx r).trans hr)⟩
/-- **`R`-linear iso `R ≃ₗ[R] Hₙ(M; R)`** sending `r ↦ r • o.fundamentalClass hn` on a compact
connected `n`-manifold over a Dedekind-finite ring `R` (Hatcher, Theorem 3.26(a)). -/
def fundamentalClassEquiv : R ≃ₗ[R] ↑((toSSet.obj (TopCat.of M)).homology (of R R) n) :=
  LinearEquiv.ofBijective _ (o.bijective_toSpanSingleton_fundamentalClass hn)
@[simp] theorem fundamentalClassEquiv_apply (r : R) :
    o.fundamentalClassEquiv hn r = r • o.fundamentalClass hn := (rfl)
/-- On a compact connected `R`-oriented `n`-manifold (`[IsDedekindFiniteMonoid R]`), every class in
`Hₙ(M; R)` is an `R`-multiple of `o.fundamentalClass hn`. -/
theorem exists_eq_smul_fundamentalClass (γ : ↑((toSSet.obj (TopCat.of M)).homology (of R R) n)) :
    ∃ r : R, γ = r • o.fundamentalClass hn :=
  ⟨(o.fundamentalClassEquiv hn).symm γ, ((o.fundamentalClassEquiv hn).apply_symm_apply γ).symm⟩
end Connected
section ExtendScalars
variable {R S : Type w} [CommRing R] [CommRing S] (f : R →+* S)
  [PreservesFiniteLimits (ModuleCat.extendScalars.{w} f)] {M E : Type w} [TopologicalSpace M]
  [T2Space M] [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [ChartedSpace E M]
  {n : ℕ} (hn : finrank ℝ E = n)
@[simp] theorem fundamentalClassOn_extendScalarsObj {N : ModuleCat.{w} R}
    (o : ModuleOrientation N M E n) {A : Set M} (hA : IsCompact A) :
    (o.extendScalarsObj f).fundamentalClassOn hn hA =
      (localHomologyObjIso (ModuleCat.extendScalars.{w} f) N A n).hom
        ((1 : S) ⊗ₜ[R, f] o.fundamentalClassOn hn hA) :=
  ((o.extendScalarsObj f).eq_fundamentalClassOn hn hA fun x hx ↦ by rw [apply_tmul_of_comm f
      (map_localHomologyRestriction_comp_localHomologyObjIso_hom _ N (singleton_subset_iff.2 hx) n),
    o.localHomologyRestriction_fundamentalClassOn hn hA hx, coe_extendScalarsObj_apply]).symm
@[simp] theorem fundamentalClassOn_extendScalars (o : ModuleOrientation (of R R) M E n)
    {A : Set M} (hA : IsCompact A) : (o.extendScalars f).fundamentalClassOn hn hA =
      (localHomologyExtendScalarsIso f A n).hom ((1 : S) ⊗ₜ[R, f] o.fundamentalClassOn hn hA) :=
  ((o.extendScalars f).eq_fundamentalClassOn hn hA fun x hx ↦ by rw [apply_tmul_of_comm f
      (map_localHomologyRestriction_comp_localHomologyExtendScalarsIso_hom f
        (singleton_subset_iff.2 hx) n),
    o.localHomologyRestriction_fundamentalClassOn hn hA hx, coe_extendScalars_apply]).symm
@[simp] theorem fundamentalClass_extendScalarsObj [CompactSpace M] {N : ModuleCat.{w} R}
    (o : ModuleOrientation N M E n) : (o.extendScalarsObj f).fundamentalClass hn =
      (SSet.homologyObjIso (ModuleCat.extendScalars.{w} f) N (toSSet.obj (TopCat.of M)) n).hom
        ((1 : S) ⊗ₜ[R, f] o.fundamentalClass hn) :=
  ((o.extendScalarsObj f).eq_fundamentalClass hn fun x ↦ by
    rw [singularHomologyToLocalHomology_homologyObjIso_hom_tmul,
      o.singularHomologyToLocalHomology_fundamentalClass hn x, coe_extendScalarsObj_apply]).symm
@[simp] theorem fundamentalClass_extendScalars [CompactSpace M]
    (o : ModuleOrientation (of R R) M E n) : (o.extendScalars f).fundamentalClass hn =
      (f.singularHomologyExtendScalarsIso M n).hom ((1 : S) ⊗ₜ[R, f] o.fundamentalClass hn) :=
  ((o.extendScalars f).eq_fundamentalClass hn fun x ↦ by
    rw [singularHomologyToLocalHomology_singularHomologyExtendScalarsIso_hom_tmul,
      o.singularHomologyToLocalHomology_fundamentalClass hn x, coe_extendScalars_apply]).symm
end ExtendScalars
end ModuleOrientation
section OrientationFree
variable {M : Type w} {E : Type v} [TopologicalSpace M] [T2Space M] [CompactSpace M]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [ChartedSpace E M] {n : ℕ}
/-- **Compact simply connected `n`-manifolds admit an `R`-fundamental class** (any ring `R`). -/
theorem exists_isFundamentalClass_of_simplyConnectedSpace [SimplyConnectedSpace M] {R : Type w}
    [Ring R] (hn : finrank ℝ E = n) :
    ∃ μ : ↑((toSSet.obj (TopCat.of M)).homology (of R R) n), IsFundamentalClass μ := by
  let E' := ULift.{w} (Fin (finrank ℝ E)) → ℝ
  let _ : ChartedSpace E' M := ChartedSpace.ofFinrankEq (𝕜 := ℝ) (E := E) M (by simp [E'])
  have hE' : finrank ℝ E' = n := by simpa [E'] using hn
  obtain ⟨o⟩ := ModuleOrientation.nonempty_of_simplyConnectedSpace (M := M) (R := R) hE'
  exact ⟨o.fundamentalClass hE', o.isFundamentalClass_fundamentalClass hE'⟩
/-- **Compact `n`-manifolds admit an `R`-fundamental class** for `[CommRing R]`, `(2 : R) = 0`. -/
theorem exists_isFundamentalClass_of_two_eq_zero {R : Type w} [CommRing R] (hn : finrank ℝ E = n)
    (h2 : (2 : R) = 0) :
    ∃ μ : ↑((toSSet.obj (TopCat.of M)).homology (of R R) n), IsFundamentalClass μ := by
  let E' := ULift.{w} (Fin (finrank ℝ E)) → ℝ
  let _ : ChartedSpace E' M := ChartedSpace.ofFinrankEq (𝕜 := ℝ) (E := E) M (by simp [E'])
  have hE' : finrank ℝ E' = n := by simpa [E'] using hn
  let o := ModuleOrientation.ofTwoEqZero (M := M) hE' h2
  exact ⟨o.fundamentalClass hE', o.isFundamentalClass_fundamentalClass hE'⟩
section
variable [ConnectedSpace M] {R : Type w} [Ring R] [IsDedekindFiniteMonoid R]
  {μ : ↑((toSSet.obj (TopCat.of M)).homology (of R R) n)} (hμ : IsFundamentalClass μ)
  (hn : finrank ℝ E = n)
include hμ hn
/-- **A fundamental class freely generates top homology** on a compact connected `n`-manifold over a
Dedekind-finite ring `R` (Hatcher, Theorem 3.26(a)). -/
theorem IsFundamentalClass.bijective_toSpanSingleton :
    Function.Bijective (LinearMap.toSpanSingleton R _ μ) := by
  let E' := ULift.{w} (Fin (finrank ℝ E)) → ℝ
  let _ : ChartedSpace E' M := ChartedSpace.ofFinrankEq (𝕜 := ℝ) (E := E) M (by simp [E'])
  have hE' : finrank ℝ E' = n := by simpa [E'] using hn
  rw [← hμ.fundamentalClass_toModuleOrientation (E := E') hE']
  exact ((hμ.toModuleOrientation (E := E')).fundamentalClassEquiv hE').bijective
/-- **`R`-linear iso `R ≃ₗ[R] Hₙ(M; R)`** on a compact connected `n`-manifold over a
Dedekind-finite ring `R`. -/
def IsFundamentalClass.linearEquiv : R ≃ₗ[R] ↑((toSSet.obj (TopCat.of M)).homology (of R R) n) :=
  LinearEquiv.ofBijective _ (hμ.bijective_toSpanSingleton hn)
@[simp] theorem IsFundamentalClass.linearEquiv_apply (r : R) : hμ.linearEquiv hn r = r • μ := (rfl)
end
/-- **Top homology over `[CommRing R]` with `(2 : R) = 0`**: on a compact connected `n`-manifold,
`Hₙ(M; R)` is isomorphic to `R` with no orientability hypothesis (Hatcher, Theorem 3.26). -/
theorem nonempty_linearEquiv_singularHomology_of_two_eq_zero [ConnectedSpace M] {R : Type w}
    [CommRing R] (hn : finrank ℝ E = n) (h2 : (2 : R) = 0) :
    Nonempty (R ≃ₗ[R] ↑((toSSet.obj (TopCat.of M)).homology (of R R) n)) :=
  let ⟨_, hμ⟩ := exists_isFundamentalClass_of_two_eq_zero hn h2; ⟨hμ.linearEquiv hn⟩
end OrientationFree
namespace ModuleOrientation
variable {M E : Type} [TopologicalSpace M] [T2Space M] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [ChartedSpace E M] {n : ℕ}
  (o : ModuleOrientation (of ℤ (ULift.{0} ℤ)) M E n) (hn : finrank ℝ E = n)
@[simp] theorem fundamentalClassOn_equivHomologicalOrientation {A : Set M} (hA : IsCompact A) :
    (equivHomologicalOrientation o).fundamentalClassOn hn hA = o.fundamentalClassOn hn hA :=
  o.eq_fundamentalClassOn hn hA fun x hx ↦
    ((equivHomologicalOrientation o).localHomologyRestriction_fundamentalClassOn hn hA hx).trans
      (coe_equivHomologicalOrientation_apply o x)
@[simp] theorem fundamentalClass_equivHomologicalOrientation [CompactSpace M] :
    (equivHomologicalOrientation o).fundamentalClass hn = o.fundamentalClass hn :=
  o.eq_fundamentalClass hn fun x ↦
    ((equivHomologicalOrientation o).singularHomologyToLocalHomology_fundamentalClass hn x).trans
      (coe_equivHomologicalOrientation_apply o x)
end ModuleOrientation
end TauCeti
