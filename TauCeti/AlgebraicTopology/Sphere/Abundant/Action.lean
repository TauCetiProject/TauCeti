/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Sphere.Abundant.Basic
public import TauCeti.Topology.MappingSpace.Action
import TauCeti.Algebra.Category.ModuleCat.Monoidal.TensorMk
import TauCeti.AlgebraicTopology.Singular.Fibration.LocalHomology
import TauCeti.AlgebraicTopology.Singular.LocalHomology.OpenEmbedding

/-!
# Abundance with 2-spheres from a group action

Let a topological group `G` act continuously on a compact oriented `d`-manifold `M`, and let
`x₀ ∈ M`. The action map

`Φ : G × Map_*(B, M) → Map(B, M)`, `(g, u) ↦ g • u`

(`TauCeti.BasedMap.actionMap`) lies over the orbit map `π : G → M`, `g ↦ g • x₀`, for evaluation
`Map(B, M) → M` at the base point of `B`. Suppose that the orbit map has continuous local sections
around every point. If a class `A ∈ H_d(G; ℤ)` satisfies `π_* A = ℓ • [M]` and a class `α` of the
based mapping space satisfies `ℓ • α ≠ 0` and is fixed by every element of the stabilizer of `x₀`,
then `Φ_*(A × α)` lives over the fundamental class of `M` at `x₀`
(`TauCeti.HomologicalOrientation.livesOverFundamentalClass_actionMap_singularHomologyCross`). For
`B = S²` and `α` of positive degree, `M` is therefore abundant with 2-spheres
(`TauCeti.HomologicalOrientation.isAbundantWithTwoSpheres_of_smul_ne_zero`).

This is the argument of Propositions 6.29 and 6.33 of Barraud–Damian–Humilière–Oancea, for
classes of diffeomorphisms coming from a group action. There the group is the identity component
of `Diff(M)`, and the source uses that its stabilizer acts trivially on the homology of `Ω²M`; the
hypothesis here asks this only of the class `α`. It holds when the stabilizer is path connected
(`IsPathConnected.homologyMap_stabilizer_smul_apply`, in
`TauCeti.AlgebraicTopology.Singular.Homotopy.BasedMapStabilizer`). It can fail for the identity
component of `Diff(M)` when `π₁(M)` acts nontrivially on `π₂(M)`: an isotopy from the identity to a
diffeomorphism fixing `x₀` moves `x₀` around a loop, and the diffeomorphism acts on
`π₀(Ω²M) = π₂(M)` through that loop.

## The computation

Localizing at the fibre over `x₀` commutes with `Φ`, a map over `M`, and localizing a cross product
`A × α` for the projection `G × Map_*(B, M) → M` gives the relative cross product of the
localization of `A` with `α` (`TauCeti.fiberLocalization_singularHomologyCross_tmul`).

* **The class of `A`.** The orbit map is a Serre fibration whose fibre over `x₀` is the stabilizer
  `H`, so the local homology `H_d(G, G ∖ H)` is the zeroth homology of `H`
  (`TauCeti.TopCat.singularHomologyComplFiberIso`), spanned by the classes of the points of `H`.
  Right translation by `h ∈ H` lies over `M` and carries the class of the point `1` to that of `h`.
  It changes `c × α` into `c × h_* α = c × α`, since `(g h) • u = g • (h • u)`. So the maps
  `c ↦ Φ_*(c × α)` and `c ↦ π_* c` are both determined by their values on the class of `1`. Let
  `s : U → G` be a section of the orbit map over an open neighbourhood `U` of `x₀`, and
  `o_U ∈ H_d(U, U ∖ {x₀})` the local orientation at `x₀`, read in `U`. Comparing `A` with `s_* o_U`,
  which the orbit map sends to the local orientation, a generator of infinite order, gives
  `Φ_*(loc(A) × α) = Φ_*(ℓ • s_* o_U × α)`.
* **The class of `Φ_*(A × α)`.** The composite `Θ = Φ ∘ (s × id) : U × Map_*(B, M) → Map(B, M)`,
  `(x, u) ↦ s(x) • u`, is an open embedding onto the maps sending the base point into `U`, the
  inverse of the local trivialization of evaluation given by `s`
  (`TauCeti.mappingSpaceEvalTrivialization`). By excision it induces an isomorphism on local
  homology along the fibre over `x₀` (`TauCeti.isIso_localHomologyMap`), and the localization of
  `Φ_*(A × α)` is its image of the relative cross product of `o_U` with `ℓ • α`. That relative
  cross product is nonzero, since its image in `M × Map_*(B, M)` is the relative cross product of
  the local orientation, a free generator, with `ℓ • α ≠ 0`.

## Main results

* `TauCeti.HomologicalOrientation.livesOverFundamentalClass_actionMap_singularHomologyCross`:
  `Φ_*(A × α)` lives over the fundamental class at `x₀`.
* `TauCeti.HomologicalOrientation.isAbundantWithTwoSpheres_of_smul_ne_zero`: a manifold with such
  an action, a class `A` with `π_* A = ℓ • [M]` and a class `α` of positive degree of
  `Map_*(S², M)` with `ℓ • α ≠ 0`, fixed by the stabilizer, is abundant with 2-spheres.

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, §6.4.3, Propositions 6.29 and 6.33.
-/

public section

noncomputable section

open CategoryTheory MonoidalCategory TensorProduct Module Set Topology

namespace TauCeti

namespace HomologicalOrientation

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] {d : ℕ}
  {M : Type} [TopologicalSpace M] [T2Space M] [CompactSpace M] [ChartedSpace V M]
  (o : HomologicalOrientation M V d) (hd : finrank ℝ V = d)
  {G : Type} [TopologicalSpace G] [Group G] [IsTopologicalGroup G] [MulAction G M]
  [ContinuousSMul G M]

omit [CompactSpace M] [ContinuousSMul G M] in
/-- **Right translation along the stabilizer, on the fibre.** The orbit map `π`, `g ↦ g • x₀`, is
a Serre fibration whose fibre over `x₀` is the stabilizer `H`. For `y ∈ H`, the identification
`H₀(H) ≅ H_d(G, G ∖ H)` (`TauCeti.TopCat.singularHomologyComplFiberIso`) carries the class of the
point `y` to the image of the class of `1` under right translation by `y`, which lies over `M`. -/
private theorem singularHomology₀Section_comp_singularHomologyComplFiberIso_inv {x₀ : M}
    (π : C(G, M)) (hπ : ∀ g, π g = g • x₀) (hp : TopCat.serreFibrations (TopCat.ofHom π))
    {ε : ℝ} (hε : Metric.ball (chartAt V x₀ x₀) ε ⊆ (chartAt V x₀).target) (hε₀ : 0 < ε)
    (h0 : 0 + finrank ℝ V = d)
    (y : TopCat.of ((TopCat.ofHom π : TopCat.of G ⟶ TopCat.of M) ⁻¹' {x₀}))
    (hy : (y : G) ∈ MulAction.stabilizer G x₀)
    (hyS : ContinuousMap.mulRight (y : G) ⁻¹' (π ⁻¹' {x₀}) ⊆ π ⁻¹' {x₀}) :
    singularHomology₀Section (ModuleCat.of ℤ (ULift.{0} ℤ)) y ≫
        (TopCat.singularHomologyComplFiberIso _ (chartAt V x₀) (mem_chart_source V x₀) hε hε₀ hp
          0 d h0).inv =
      singularHomology₀Section (ModuleCat.of ℤ (ULift.{0} ℤ))
          (X := TopCat.of ((TopCat.ofHom π : TopCat.of G ⟶ TopCat.of M) ⁻¹' {x₀}))
          ⟨1, by simp [hπ]⟩ ≫
        (TopCat.singularHomologyComplFiberIso _ (chartAt V x₀) (mem_chart_source V x₀) hε hε₀ hp
          0 d h0).inv ≫
        localHomologyMap (ModuleCat.of ℤ (ULift.{0} ℤ)) (ContinuousMap.mulRight (y : G)) hyS d := by
  let R := ModuleCat.of ℤ (ULift.{0} ℤ)
  let p : TopCat.of G ⟶ TopCat.of M := TopCat.ofHom π
  let fib := TopCat.singularHomologyComplFiberIso R (chartAt V x₀) (mem_chart_source V x₀) hε hε₀
    hp 0 d h0
  let one : p ⁻¹' {x₀} := ⟨1, by simp [p, hπ]⟩
  let f : TopCat.of G ⟶ TopCat.of G := TopCat.ofHom (ContinuousMap.mulRight (y : G))
  have hf : f ≫ p = p := TopCat.hom_ext (π.comp_mulRight_eq_of_mem_stabilizer hπ hy)
  -- Right translation by `y` on the fibre carries the point `1` to `y`.
  have hsec : singularHomology₀Section R y = singularHomology₀Section R one ≫
      ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℤ) 0).obj R).map
        (f.preimageMap hf {x₀}) := by
    rw [singularHomology₀Section_naturality]
    congr 1
    refine Subtype.ext ?_
    rw [TopCat.Hom.coe_preimageMap_apply]
    simp [f, one]
  have hnat : ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℤ) 0).obj R).map
      (f.preimageMap hf {x₀}) ≫ fib.inv =
      fib.inv ≫ localHomologyMap R (ContinuousMap.mulRight (y : G))
        hyS d := by
    rw [Iso.eq_inv_comp, ← Category.assoc, ← TopCat.singularHomologyComplFiberIso_hom_naturality
      R (chartAt V x₀) (mem_chart_source V x₀) hε hε₀ hp hp hf 0 d _, Category.assoc,
      Iso.hom_inv_id,
      Category.comp_id, localHomologyMap_def]
  rw [hsec, Category.assoc, hnat]

omit [CompactSpace M] in
include hd in
/-- **Maps out of the local homology along the stabilizer that are invariant under right
translations.** Let the orbit map `π : G → M`, `g ↦ g • x₀`, have continuous local sections
around every point. There are a function `χ` on `H_d(G, G ∖ π⁻¹(x₀); ℤ)` and a class `c₁` of it
such that every map `Q` out of this local homology that is invariant under right translation by
the elements of the stabilizer of `x₀` satisfies `Q c = χ c • Q c₁`.

The orbit map is a Serre fibration whose fibre over `x₀` is the stabilizer, so the local
homology is the zeroth homology of the stabilizer, and right translation by `h` acts on it through
the right translation of the fibre (`TauCeti.TopCat.singularHomologyComplFiberIso` and its
naturality). Right translation by `h` carries the class of the point `1` to that of `h`, so `Q`
takes the same value on the classes of all points, and is therefore the augmentation followed by
its value on the class of `1`. Here `χ` is the augmentation and `c₁` the class of `1`. -/
private theorem exists_forall_apply_eq_zsmul {x₀ : M} (π : C(G, M)) (hπ : ∀ g, π g = g • x₀)
    (hloc : ∀ y : M, ∃ U : Set M, IsOpen U ∧ y ∈ U ∧ ∃ s : M → G, ContinuousOn s U ∧
      ∀ z ∈ U, s z • x₀ = z) :
    ∃ (χ : localHomology (A := ModuleCat.{0} ℤ) (ModuleCat.of ℤ (ULift.{0} ℤ)) (π ⁻¹' {x₀}) d →
        ℤ) (c₁ : localHomology (A := ModuleCat.{0} ℤ) (ModuleCat.of ℤ (ULift.{0} ℤ))
          (π ⁻¹' {x₀}) d),
      ∀ (T : ModuleCat.{0} ℤ)
        (Q : localHomology (A := ModuleCat.{0} ℤ) (ModuleCat.of ℤ (ULift.{0} ℤ)) (π ⁻¹' {x₀}) d ⟶
          T),
        (∀ (h : MulAction.stabilizer G x₀) (hh : ContinuousMap.mulRight (h : G) ⁻¹' (π ⁻¹' {x₀}) ⊆
          π ⁻¹' {x₀}),
          localHomologyMap (ModuleCat.of ℤ (ULift.{0} ℤ)) (ContinuousMap.mulRight (h : G)) hh d ≫
            Q = Q) →
        ∀ c, Q c = χ c • Q c₁ := by
  let R := ModuleCat.of ℤ (ULift.{0} ℤ)
  let p : TopCat.of G ⟶ TopCat.of M := TopCat.ofHom π
  have hπ' : p = TopCat.ofHom ⟨fun g : G ↦ g • x₀, by fun_prop⟩ :=
    TopCat.hom_ext (ContinuousMap.ext hπ)
  have hp : TopCat.serreFibrations p := hπ' ▸ orbitMap_mem_serreFibrations (G := G) x₀ hloc
  let e := chartAt V x₀
  obtain ⟨ε, hε₀, hε⟩ := Metric.isOpen_iff.1 e.open_target (e x₀) (e.map_source
    (mem_chart_source V x₀))
  -- `H_d(G, G ∖ π⁻¹(x₀)) ≅ H₀(π⁻¹(x₀))`.
  let fib := TopCat.singularHomologyComplFiberIso R e (mem_chart_source V x₀) hε hε₀ hp 0 d
    (by rw [zero_add, hd])
  let ε₀ := (TopCat.of (p ⁻¹' {x₀})).singularHomology₀ε R
  let one : p ⁻¹' {x₀} := ⟨1, by simp [p, hπ]⟩
  let c₁ := fib.inv (singularHomology₀Section R one (ULift.up 1))
  refine ⟨fun c ↦ (ε₀ (fib.hom c)).down, c₁, fun T Q hQ c ↦ ?_⟩
  -- On zeroth homology, `Q` is the augmentation followed by multiplication by `Q c₁`.
  have key : fib.inv ≫ Q = ε₀ ≫ ModuleCat.ofHom ((LinearMap.toSpanSingleton ℤ T (Q c₁)).comp
      (ULift.moduleEquiv : ULift.{0} ℤ ≃ₗ[ℤ] ℤ).toLinearMap) := by
    refine singularHomology₀_hom_ext R fun y ↦ ?_
    have hy : (y : G) ∈ MulAction.stabilizer G x₀ := by
      have h := y.property
      rw [Set.mem_preimage, Set.mem_singleton_iff] at h
      exact MulAction.mem_stabilizer_iff.2 ((hπ _).symm.trans h)
    have hyS : ContinuousMap.mulRight (y : G) ⁻¹' (π ⁻¹' {x₀}) ⊆ π ⁻¹' {x₀} := by
      rw [← preimage_comp, ← ContinuousMap.coe_comp, π.comp_mulRight_eq_of_mem_stabilizer hπ hy]
    have hsec : singularHomology₀Section R y ≫ fib.inv = singularHomology₀Section R one ≫
        fib.inv ≫ localHomologyMap R (ContinuousMap.mulRight (y : G)) hyS d :=
      singularHomology₀Section_comp_singularHomologyComplFiberIso_inv π hπ hp hε hε₀
        (by rw [zero_add, hd]) y hy hyS
    rw [singularHomology₀Section_singularHomology₀ε_assoc, reassoc_of% hsec, hQ ⟨y, hy⟩]
    ext r
    obtain ⟨r⟩ := r
    have hr : (ULift.up r : ULift.{0} ℤ) = r • ULift.up 1 := ULift.ext (by simp)
    simp only [R, c₁, hr, map_zsmul, ModuleCat.hom_comp, ModuleCat.hom_ofHom, LinearMap.comp_apply,
      LinearEquiv.coe_coe, ULift.moduleEquiv_apply, LinearMap.toSpanSingleton_apply_one]
  have := ConcreteCategory.congr_hom key (fib.hom c)
  rw [ConcreteCategory.comp_apply, Iso.hom_inv_id_apply] at this
  rw [this, ConcreteCategory.comp_apply]
  exact int_smul_eq_zsmul _ _ _

omit [T2Space M] [CompactSpace M] [ChartedSpace V M] in
/-- **The translation chart of evaluation.** Let `s : U → G` be a section of the orbit map over an
open set `U ∋ x₀`. Then `Θ : U × Map_*(B, M) → Map(B, M)`, `(x, u) ↦ s(x) • u`, is an open
embedding onto the maps sending `b₀` into `U`, the inverse of the local trivialization of
evaluation given by `s` (`TauCeti.mappingSpaceEvalTrivialization`). By excision it induces an
isomorphism from the local homology along `{x₀} × Map_*(B, M)` to the local homology along the
fibre of evaluation over `x₀`. -/
private theorem isIso_localHomologyMap_actionMap_comp_prodMap [T1Space M] {B : Type}
    [TopologicalSpace B] (b₀ : B) {U : Set M} (hU : IsOpen U) (x₀ : U) (s : M → G)
    (hs : ContinuousOn s U) (hsec : ∀ z ∈ U, s z • (x₀ : M) = z) (R : ModuleCat.{0} ℤ) (n : ℕ) :
    ∃ h : ((BasedMap.actionMap (G := G) b₀ (x₀ : M)).comp
        ((⟨U.domRestrict s, hs.domRestrict⟩ : C(U, G)).prodMap
          (ContinuousMap.id (BasedMap B M b₀ (x₀ : M))))) ⁻¹' (mappingSpaceEval b₀ ⁻¹' {(x₀ : M)}) ⊆
        Prod.fst ⁻¹' {x₀},
      IsIso (localHomologyMap R ((BasedMap.actionMap (G := G) b₀ (x₀ : M)).comp
        ((⟨U.domRestrict s, hs.domRestrict⟩ : C(U, G)).prodMap
          (ContinuousMap.id (BasedMap B M b₀ (x₀ : M))))) h n) := by
  let sU : C(U, G) := ⟨U.domRestrict s, hs.domRestrict⟩
  have hsU : ∀ z : U, sU z • (x₀ : M) = z := fun z ↦ hsec z z.property
  let F := BasedMap B M b₀ (x₀ : M)
  let Θ : C(U × F, C(B, M)) := (BasedMap.actionMap (G := G) b₀ (x₀ : M)).comp
    (sU.prodMap (ContinuousMap.id F))
  have hΘapply : ∀ p : U × F, Θ p = sU p.1 • p.2.val := fun _ ↦ by simp [Θ]
  let τ := mappingSpaceEvalTrivialization b₀ (x₀ : M) U hU s hs hsec
  have hτ : U ⊆ τ.baseSet := by simp [τ]
  have hΘτ : (Θ : U × F → C(B, M)) = Subtype.val ∘ (τ.preimageHomeomorph hτ).symm :=
    funext fun p ↦ by simp [hΘapply, τ, sU]
  have hΘ : IsOpenEmbedding Θ := by
    rw [hΘτ]
    exact (hU.preimage (mappingSpaceEval b₀).continuous).isOpenEmbedding_subtypeVal.comp
      (τ.preimageHomeomorph hτ).symm.isOpenEmbedding
  have hΘF : Θ ⁻¹' (mappingSpaceEval b₀ ⁻¹' {(x₀ : M)}) = Prod.fst ⁻¹' {x₀} := by
    ext p
    simp [hΘapply, p.2.property, hsU, Subtype.ext_iff]
  have hFΘ : mappingSpaceEval b₀ ⁻¹' {(x₀ : M)} ⊆ range Θ := fun f hf ↦ by
    have hf' : f b₀ = x₀ := by simpa using hf
    refine ⟨(x₀, ⟨(sU x₀)⁻¹ • f, by
      rw [ContinuousMap.smul_apply, hf', inv_smul_eq_iff, hsU]⟩), ?_⟩
    simp [hΘapply]
  exact ⟨hΘF.subset, isIso_localHomologyMap R Θ hΘ hΘF
    (isClosed_singleton.preimage (mappingSpaceEval b₀).continuous) hFΘ n⟩

omit [CompactSpace M] in
include o hd in
/-- **The relative cross product with the local orientation is injective.** For `x₀` in an open set
`U ⊆ M` and a nonzero class `β` of a space `N`, the relative cross product of the local orientation
at `x₀`, read in `U`, with `β` is nonzero: its image in `M × N` is the relative cross product of
the local orientation of `M`, a free generator, with `β`. -/
private theorem singularHomologyCrossRel_localOrientation_ne_zero {U : Set M} (hU : IsOpen U)
    (x₀ : U) {N : Type} [TopologicalSpace N] {k : ℕ}
    {β : ((TopCat.toSSet.obj (TopCat.of N)).homology (ModuleCat.of ℤ (ULift.{0} ℤ)) k :
      ModuleCat.{0} ℤ)} (hβ : β ≠ 0) :
    (TopCat.singularHomologyCrossRel (TopCat.of U) (TopCat.of N) {x₀}ᶜ
      (ModuleCat.of ℤ (ULift.{0} ℤ)) (ModuleCat.of ℤ (ULift.{0} ℤ)) d k (d + k) rfl).hom
        ((localHomologyIsoOfIsOpenEmbedding (ModuleCat.of ℤ (ULift.{0} ℤ))
          hU.isOpenEmbedding_subtypeVal x₀ d).inv.hom (o x₀).val ⊗ₜ β) ≠ 0 := by
  intro hX0
  let incl : C(U, M) := ⟨Subtype.val, continuous_subtypeVal⟩
  have h₁ : incl ⁻¹' {(x₀ : M)} ⊆ {x₀} := fun _ hz ↦ Subtype.ext hz
  have hincl := singularHomologyCrossRel_localHomologyMap_tmul _ _ incl h₁ rfl
    ((localHomologyIsoOfIsOpenEmbedding (ModuleCat.of ℤ (ULift.{0} ℤ))
      hU.isOpenEmbedding_subtypeVal x₀ d).inv.hom (o x₀).val) β
  have hoU := ConcreteCategory.congr_hom
    (localHomologyIsoOfIsOpenEmbedding_inv_comp_localHomologyMap (ModuleCat.of ℤ (ULift.{0} ℤ))
      hU.isOpenEmbedding_subtypeVal x₀ h₁ d) (o x₀).val
  rw [ConcreteCategory.comp_apply, ConcreteCategory.id_apply] at hoU
  rw [hoU] at hincl
  exact (map_ne_zero_iff _ ((ModuleCat.mono_iff_injective _).1 inferInstance)).2
    (o.apply_tmul_ne_zero hd x₀ hβ) (hincl.trans ((congrArg _ hX0).trans (map_zero _)))

omit [CompactSpace M] [IsTopologicalGroup G] [ContinuousSMul G M] in
include o in
/-- **The orbit map on a section.** For a section `s : U → G` of the orbit map over an open set
`U ∋ x₀`, the orbit map sends `s_* o_U`, the image of the local orientation at `x₀` read in `U`, to
the local orientation at `x₀`. -/
private theorem localHomologyMap_orbitMap_section {U : Set M} (hU : IsOpen U) (x₀ : U)
    (π : C(G, M)) (hπ : ∀ g, π g = g • (x₀ : M)) (s : C(U, G))
    (hs : ∀ z : U, s z • (x₀ : M) = z) (hsU : s ⁻¹' (π ⁻¹' {(x₀ : M)}) ⊆ {x₀}) :
    (localHomologyMap (ModuleCat.of ℤ (ULift.{0} ℤ)) π (subset_refl (π ⁻¹' {(x₀ : M)})) d).hom
        ((localHomologyMap (ModuleCat.of ℤ (ULift.{0} ℤ)) s hsU d).hom
          ((localHomologyIsoOfIsOpenEmbedding (ModuleCat.of ℤ (ULift.{0} ℤ))
            hU.isOpenEmbedding_subtypeVal x₀ d).inv.hom (o x₀).val)) = (o x₀).val := by
  let R := ModuleCat.of ℤ (ULift.{0} ℤ)
  have hπs : π.comp s = ⟨Subtype.val, continuous_subtypeVal⟩ :=
    ContinuousMap.ext fun z ↦ by simp [hπ, hs]
  have hc : localHomologyMap R s hsU d ≫ localHomologyMap R π (subset_refl _) d =
      localHomologyMap R ⟨Subtype.val, continuous_subtypeVal⟩
        (by rw [← hπs, ContinuousMap.coe_comp, preimage_comp]; exact hsU) d := by
    rw [localHomologyMap_comp]
    exact localHomologyMap_congr R hπs _ d
  rw [← ModuleCat.comp_apply, hc]
  exact ConcreteCategory.congr_hom (localHomologyIsoOfIsOpenEmbedding_inv_comp_localHomologyMap
    R hU.isOpenEmbedding_subtypeVal x₀ _ d) (o x₀).val

omit [T2Space M] [CompactSpace M] [ChartedSpace V M] in
/-- **Right translation by the stabilizer under the action map.** For `h` in the stabilizer of
`x₀` fixing the class `α` of the based mapping space, the action map sends the relative cross
products `(c h) × α` and `c × α` to the same class: `(g h) • u = g • (h • u)`, so the first is the
image of `c × h_* α = c × α`. -/
private theorem localHomologyMap_actionMap_singularHomologyCrossRel_mulRight {B : Type}
    [TopologicalSpace B] (b₀ : B) {x₀ : M} (π : C(G, M)) (h : MulAction.stabilizer G x₀) {k : ℕ}
    {α : ((TopCat.toSSet.obj (TopCat.of (BasedMap B M b₀ x₀))).homology
      (ModuleCat.of ℤ (ULift.{0} ℤ)) k : ModuleCat.{0} ℤ)}
    (hfix : (SSet.homologyMap (TopCat.toSSet.map (TopCat.ofHom ⟨(h • · : BasedMap B M b₀ x₀ →
      BasedMap B M b₀ x₀), continuous_const_smul h⟩)) (ModuleCat.of ℤ (ULift.{0} ℤ)) k).hom α =
        α)
    (hΦS : BasedMap.actionMap (G := G) b₀ x₀ ⁻¹' (mappingSpaceEval b₀ ⁻¹' {x₀}) ⊆
      (π ∘ Prod.fst) ⁻¹' {x₀})
    (hh : ContinuousMap.mulRight (h : G) ⁻¹' (π ⁻¹' {x₀}) ⊆ π ⁻¹' {x₀})
    (c : localHomology (A := ModuleCat.{0} ℤ) (ModuleCat.of ℤ (ULift.{0} ℤ)) (π ⁻¹' {x₀}) d) :
    let R := ModuleCat.of ℤ (ULift.{0} ℤ)
    let cross := TopCat.singularHomologyCrossRel (TopCat.of G)
      (TopCat.of (BasedMap B M b₀ x₀)) (π ⁻¹' {x₀})ᶜ R R d k (d + k) rfl
    let Φloc := localHomologyMap (R ⊗ R : ModuleCat ℤ) (BasedMap.actionMap (G := G) b₀ x₀) hΦS
      (d + k)
    Φloc.hom (cross.hom ((localHomologyMap R (ContinuousMap.mulRight (h : G)) hh d).hom c ⊗ₜ α)) =
      Φloc.hom (cross.hom (c ⊗ₜ α)) := by
  intro R cross Φloc
  let F := BasedMap B M b₀ x₀
  let act : C(F, F) := ⟨(h • ·), continuous_const_smul h⟩
  have hΦ : (BasedMap.actionMap (G := G) b₀ x₀).comp
      ((ContinuousMap.mulRight (h : G)).prodMap (ContinuousMap.id F)) =
      (BasedMap.actionMap (G := G) b₀ x₀).comp ((ContinuousMap.id G).prodMap act) :=
    ContinuousMap.ext fun q ↦ BasedMap.actionMap_mul_stabilizer q.1 h q.2
  have h₁ : (ContinuousMap.mulRight (h : G)).prodMap (ContinuousMap.id F) ⁻¹'
      (Prod.fst ⁻¹' (π ⁻¹' {x₀})) ⊆ Prod.fst ⁻¹' (π ⁻¹' {x₀}) := fun _ hz ↦ hh hz
  have h₂ : (ContinuousMap.id G).prodMap act ⁻¹' (Prod.fst ⁻¹' (π ⁻¹' {x₀})) ⊆
      Prod.fst ⁻¹' (π ⁻¹' {x₀}) := fun _ hz ↦ hz
  have e := (localHomologyMap_comp (R ⊗ R : ModuleCat ℤ) _ _ h₁ hΦS (d + k)).trans
    ((localHomologyMap_congr (R ⊗ R : ModuleCat ℤ) hΦ _ (d + k)).trans
      (localHomologyMap_comp (R ⊗ R : ModuleCat ℤ) _ _ h₂ hΦS (d + k)).symm)
  exact (congrArg Φloc.hom
    (singularHomologyCrossRel_localHomologyMap_tmul R R _ hh rfl c α)).trans
    ((ConcreteCategory.congr_hom e _).trans
      ((congrArg Φloc.hom (singularHomologyCrossRel_tmul_homologyMap R R act rfl c α)).symm.trans
        (congrArg (fun a ↦ Φloc.hom (cross.hom (c ⊗ₜ a))) hfix)))

omit [CompactSpace M] in
include o hd in
/-- **The image of `c × α` for a class `c` of the stabilizer covering `ℓ • [M]`.** Let `s : U → G`
be a section of the orbit map over an open set `U ∋ x₀`, and `o_U` the local orientation at `x₀`
read in `U`. If every element of the stabilizer of `x₀` fixes the class `α` of the based mapping
space, then for a class `c` of `H_d(G, G ∖ π⁻¹(x₀))` sent by the orbit map to `ℓ` times the local
orientation, the action map sends the relative cross product `c × α` to `ℓ` times the image of
`s_* o_U × α`.

Right translation by an element `h` of the stabilizer changes `c × α` into `c × h_* α`, since
`(g h) • u = g • (h • u)`; so `c ↦ Φ_*(c × α)` is invariant under these translations, as is the
orbit map, and both are multiples of one function `χ` of `c`
(`exists_forall_apply_eq_zsmul`). Comparing the orbit map on `c` and on `s_* o_U`, whose image is
the local orientation, determines `χ c` in terms of `χ (s_* o_U)` and `ℓ`. -/
private theorem localHomologyMap_actionMap_singularHomologyCrossRel_eq_zsmul {B : Type}
    [TopologicalSpace B] (b₀ : B) {U : Set M} (hU : IsOpen U) (x₀ : U) (π : C(G, M))
    (hπ : ∀ g, π g = g • (x₀ : M))
    (hloc : ∀ y : M, ∃ U : Set M, IsOpen U ∧ y ∈ U ∧ ∃ s : M → G, ContinuousOn s U ∧
      ∀ z ∈ U, s z • (x₀ : M) = z) (s : C(U, G))
    (hs : ∀ z : U, s z • (x₀ : M) = z) (hsU : s ⁻¹' (π ⁻¹' {(x₀ : M)}) ⊆ {x₀}) {k : ℕ}
    {α : ((TopCat.toSSet.obj (TopCat.of (BasedMap B M b₀ (x₀ : M)))).homology
      (ModuleCat.of ℤ (ULift.{0} ℤ)) k : ModuleCat.{0} ℤ)}
    (hfix : ∀ h : MulAction.stabilizer G (x₀ : M),
      (SSet.homologyMap (TopCat.toSSet.map (TopCat.ofHom ⟨(h • · : BasedMap B M b₀ (x₀ : M) →
        BasedMap B M b₀ (x₀ : M)), continuous_const_smul h⟩)) (ModuleCat.of ℤ (ULift.{0} ℤ))
          k).hom α = α)
    (hΦS : BasedMap.actionMap (G := G) b₀ (x₀ : M) ⁻¹' (mappingSpaceEval b₀ ⁻¹' {(x₀ : M)}) ⊆
      (π ∘ Prod.fst) ⁻¹' {(x₀ : M)})
    {ℓ : ℤ} {c : localHomology (A := ModuleCat.{0} ℤ) (ModuleCat.of ℤ (ULift.{0} ℤ))
      (π ⁻¹' {(x₀ : M)}) d}
    (hc : (localHomologyMap (ModuleCat.of ℤ (ULift.{0} ℤ)) π (subset_refl _) d).hom c =
      ℓ • (o x₀).val) :
    let R := ModuleCat.of ℤ (ULift.{0} ℤ)
    let cross := TopCat.singularHomologyCrossRel (TopCat.of G)
      (TopCat.of (BasedMap B M b₀ (x₀ : M))) (π ⁻¹' {(x₀ : M)})ᶜ R R d k (d + k) rfl
    let Φloc := localHomologyMap (R ⊗ R : ModuleCat ℤ) (BasedMap.actionMap (G := G) b₀ (x₀ : M))
      hΦS (d + k)
    Φloc.hom (cross.hom (c ⊗ₜ α)) = Φloc.hom (cross.hom ((ℓ • (localHomologyMap R s hsU d).hom
      ((localHomologyIsoOfIsOpenEmbedding R hU.isOpenEmbedding_subtypeVal x₀ d).inv.hom
        (o x₀).val)) ⊗ₜ α)) := by
  intro R cross Φloc
  obtain ⟨χ, c₁, hχ⟩ := exists_forall_apply_eq_zsmul hd π hπ hloc
  let F := BasedMap B M b₀ (x₀ : M)
  let Lπ := localHomologyMap R π (subset_refl (π ⁻¹' {(x₀ : M)})) d
  -- `c ↦ Φ_*(c × α)` as a morphism out of the local homology along the stabilizer.
  let αmap : 𝟙_ (ModuleCat.{0} ℤ) ⟶ (TopCat.toSSet.obj (TopCat.of F)).homology R k :=
    ModuleCat.ofHom (LinearMap.toSpanSingleton ℤ _ α)
  let P : localHomology (A := ModuleCat.{0} ℤ) R (π ⁻¹' {(x₀ : M)}) d ⟶ _ :=
    ((ρ_ _).inv ≫ (_ ◁ αmap)) ≫ cross ≫ Φloc
  have hPapply : ∀ c, P c = Φloc.hom (cross.hom (c ⊗ₜ α)) := fun c ↦
    (ConcreteCategory.comp_apply _ (cross ≫ Φloc) c).trans
      ((congrArg (cross ≫ Φloc)
        (ModuleCat.rightUnitor_inv_whiskerLeft_toSpanSingleton_apply α c)).trans
          (ConcreteCategory.comp_apply cross Φloc _))
  have hLπ : ∀ (h : MulAction.stabilizer G (x₀ : M)) hh,
      localHomologyMap R (ContinuousMap.mulRight (h : G)) hh d ≫ Lπ = Lπ :=
    fun h hh ↦ (localHomologyMap_comp R _ π hh _ d).trans
      (localHomologyMap_congr R (π.comp_mulRight_eq_of_mem_stabilizer hπ h.property) _ d)
  have hP : ∀ (h : MulAction.stabilizer G (x₀ : M)) hh,
      localHomologyMap R (ContinuousMap.mulRight (h : G)) hh d ≫ P = P := by
    intro h hh
    ext c
    rw [ModuleCat.comp_apply, hPapply, hPapply]
    exact localHomologyMap_actionMap_singularHomologyCrossRel_mulRight b₀ π h (hfix h) hΦS hh c
  have hPc := hχ _ P hP c
  have hPz := hχ _ P hP ((localHomologyMap R s hsU d).hom
    ((localHomologyIsoOfIsOpenEmbedding R hU.isOpenEmbedding_subtypeVal x₀ d).inv.hom (o x₀).val))
  have hLc := hχ _ Lπ hLπ c
  have hLz := hχ _ Lπ hLπ ((localHomologyMap R s hsU d).hom
    ((localHomologyIsoOfIsOpenEmbedding R hU.isOpenEmbedding_subtypeVal x₀ d).inv.hom (o x₀).val))
  -- The orbit map sends `s_* o_U` to the local orientation.
  rw [o.localHomologyMap_orbitMap_section hU x₀ π hπ s hs hsU] at hLz
  rw [hc] at hLc
  -- The local orientation generates the local homology, so `Lπ c₁ = m • o` with
  -- `χ (s_* o_U) * m = 1` and `ℓ = χ c * m`.
  obtain ⟨m, hm⟩ := (isLocalOrientation_iff _ _ _).1 (o x₀).property (Lπ c₁)
  rw [← hm, smul_smul] at hLc hLz
  have h₁ := o.zsmul_left_injective hd x₀ ((one_smul ℤ _).trans hLz)
  have h₂ := o.zsmul_left_injective hd x₀ hLc
  -- Hence `χ c = χ c * χ (s_* o_U) * m = ℓ * χ (s_* o_U)`.
  have hχc : χ c = ℓ * χ ((localHomologyMap R s hsU d).hom
      ((localHomologyIsoOfIsOpenEmbedding R hU.isOpenEmbedding_subtypeVal x₀ d).inv.hom
        (o x₀).val)) := by grind
  rw [← hPapply, ← hPapply, map_zsmul, hPc, hPz, smul_smul, hχc]

omit [Group G] [IsTopologicalGroup G] [MulAction G M] [ContinuousSMul G M] in
include o hd in
/-- **The localization of a class covering `ℓ • [M]`.** If `π_* A = ℓ • [M]`, then `π` sends the
localization of `A` at the fibre over `x₀` to `ℓ` times the local orientation at `x₀`. -/
private theorem localHomologyMap_fiberLocalization {x₀ : M} (π : C(G, M)) {ℓ : ℤ}
    {A : ((TopCat.toSSet.obj (TopCat.of G)).homology (ModuleCat.of ℤ (ULift.{0} ℤ)) d :
      ModuleCat.{0} ℤ)}
    (hA : (SSet.homologyMap (TopCat.toSSet.map (TopCat.ofHom π)) (ModuleCat.of ℤ (ULift.{0} ℤ))
      d).hom A = ℓ • o.fundamentalClass hd) :
    (localHomologyMap (ModuleCat.of ℤ (ULift.{0} ℤ)) π (subset_refl _) d).hom
      ((fiberLocalization (ModuleCat.of ℤ (ULift.{0} ℤ)) π x₀ d).hom A) = ℓ • (o x₀).val := by
  have h := ConcreteCategory.congr_hom (homologyMap_comp_fiberLocalization
    (ModuleCat.of ℤ (ULift.{0} ℤ)) π (p := π) (p' := id) rfl x₀ d) A
  rw [ModuleCat.comp_apply, ModuleCat.comp_apply, hA, map_zsmul,
    o.fiberLocalization_id_fundamentalClass hd] at h
  exact h.symm

include o hd in
/-- **Classes of the action map living over the fundamental class** (the argument of
Barraud–Damian–Humilière–Oancea, Propositions 6.29 and 6.33, for a group action). Let a
topological group `G` act on a compact oriented `d`-manifold `M` with orbit map
`π : G → M`, `g ↦ g • x₀`, which has continuous local sections around every point. Let
`A ∈ H_d(G; ℤ)` satisfy `π_* A = ℓ • [M]`, and let `α` be a class of the based mapping space
`Map_*(B, M)` with `ℓ • α ≠ 0` which every element of the stabilizer of `x₀` fixes. Then the image
of `A × α` under the action map `G × Map_*(B, M) → Map(B, M)` lives over the fundamental class of
`M` at `x₀`, for evaluation at the base point `b₀` of `B`. -/
theorem livesOverFundamentalClass_actionMap_singularHomologyCross {B : Type}
    [TopologicalSpace B] (b₀ : B) {x₀ : M} (π : C(G, M)) (hπ : ∀ g, π g = g • x₀)
    (hloc : ∀ y : M, ∃ U : Set M, IsOpen U ∧ y ∈ U ∧ ∃ s : M → G, ContinuousOn s U ∧
      ∀ z ∈ U, s z • x₀ = z) {ℓ : ℤ}
    {A : ((TopCat.toSSet.obj (TopCat.of G)).homology (ModuleCat.of ℤ (ULift.{0} ℤ)) d :
      ModuleCat.{0} ℤ)}
    (hA : (SSet.homologyMap (TopCat.toSSet.map (TopCat.ofHom π)) (ModuleCat.of ℤ (ULift.{0} ℤ))
      d).hom A = ℓ • o.fundamentalClass hd) {k : ℕ}
    {α : ((TopCat.toSSet.obj (TopCat.of (BasedMap B M b₀ x₀))).homology
      (ModuleCat.of ℤ (ULift.{0} ℤ)) k : ModuleCat.{0} ℤ)} (hα : ℓ • α ≠ 0)
    (hfix : ∀ h : MulAction.stabilizer G x₀,
      (SSet.homologyMap (TopCat.toSSet.map (TopCat.ofHom ⟨(h • · : BasedMap B M b₀ x₀ →
        BasedMap B M b₀ x₀), continuous_const_smul h⟩)) (ModuleCat.of ℤ (ULift.{0} ℤ)) k).hom α =
          α) :
    LivesOverFundamentalClass (ModuleCat.of ℤ (ULift.{0} ℤ) ⊗ ModuleCat.of ℤ (ULift.{0} ℤ))
      (mappingSpaceEval b₀) x₀
      ((SSet.homologyMap (TopCat.toSSet.map (TopCat.ofHom (BasedMap.actionMap (G := G) b₀ x₀)))
        (ModuleCat.of ℤ (ULift.{0} ℤ) ⊗ ModuleCat.of ℤ (ULift.{0} ℤ)) (d + k)).hom
        ((TopCat.singularHomologyCross (TopCat.of G) (TopCat.of (BasedMap B M b₀ x₀))
          (ModuleCat.of ℤ (ULift.{0} ℤ)) (ModuleCat.of ℤ (ULift.{0} ℤ)) d k (d + k) rfl).hom
            (A ⊗ₜ α))) := by
  let R := ModuleCat.of ℤ (ULift.{0} ℤ)
  obtain ⟨U, hU, hx₀U, s, hs, hsec⟩ := hloc x₀
  -- Work with the base point as a point of `U`.
  obtain ⟨x₀, rfl⟩ : ∃ x₀' : U, (x₀' : M) = x₀ := ⟨⟨x₀, hx₀U⟩, rfl⟩
  let sU : C(U, G) := ⟨U.domRestrict s, hs.domRestrict⟩
  have hsU : ∀ z : U, sU z • (x₀ : M) = z := fun z ↦ hsec z z.property
  have hsU' : sU ⁻¹' (π ⁻¹' {(x₀ : M)}) ⊆ {x₀} := fun z hz ↦
    Subtype.ext ((hsU z).symm.trans ((hπ _).symm.trans hz))
  let F := BasedMap B M b₀ (x₀ : M)
  let Φ := BasedMap.actionMap (G := G) b₀ (x₀ : M)
  have hΦ : mappingSpaceEval b₀ ∘ Φ = π ∘ Prod.fst := funext fun p ↦ by simp [Φ, hπ, p.2.property]
  -- `Θ = Φ ∘ (s × id)`, `(x, u) ↦ s(x) • u`, induces an isomorphism on local homology.
  let Θ : C(U × F, C(B, M)) := Φ.comp (sU.prodMap (ContinuousMap.id F))
  obtain ⟨hΘF, hΘiso⟩ := isIso_localHomologyMap_actionMap_comp_prodMap (G := G) b₀ hU x₀ s hs hsec
    (R ⊗ R : ModuleCat ℤ) (d + k)
  -- The local orientation `o_U` at `x₀`, read in `U`, and the relative cross product `X` of
  -- `o_U` with `ℓ • α`, which is nonzero.
  let oU := (localHomologyIsoOfIsOpenEmbedding R hU.isOpenEmbedding_subtypeVal x₀ d).inv.hom
    (o x₀).val
  let X := (TopCat.singularHomologyCrossRel (TopCat.of U) (TopCat.of F) {x₀}ᶜ R R d k (d + k)
    rfl).hom (oU ⊗ₜ (ℓ • α))
  have hX : X ≠ 0 := o.singularHomologyCrossRel_localOrientation_ne_zero hd hU x₀ hα
  -- Localizing `Φ_*(A × α)` gives `Θ_* X`, and `Θ_*` is injective by excision.
  have hΦS : Φ ⁻¹' (mappingSpaceEval b₀ ⁻¹' {(x₀ : M)}) ⊆ (π ∘ Prod.fst) ⁻¹' {(x₀ : M)} := by
    rw [← preimage_comp, hΦ]
  have hsF : sU.prodMap (ContinuousMap.id F) ⁻¹' (Prod.fst ⁻¹' (π ⁻¹' {(x₀ : M)})) ⊆
      Prod.fst ⁻¹' {x₀} := fun _ hz ↦ hsU' hz
  let c := (TopCat.singularHomologyCross (TopCat.of G) (TopCat.of F) R R d k (d + k) rfl).hom
    (A ⊗ₜ α)
  have key : (fiberLocalization (R ⊗ R : ModuleCat ℤ) (mappingSpaceEval b₀) (x₀ : M) (d + k)).hom
      ((SSet.homologyMap (TopCat.toSSet.map (TopCat.ofHom Φ)) (R ⊗ R : ModuleCat ℤ)
        (d + k)).hom c) =
      (localHomologyMap (R ⊗ R : ModuleCat ℤ) Θ hΘF (d + k)).hom X := by
    calc _ = (localHomologyMap (R ⊗ R : ModuleCat ℤ) Φ hΦS (d + k)).hom
          ((TopCat.singularHomologyCrossRel (TopCat.of G) (TopCat.of F) (π ⁻¹' {(x₀ : M)})ᶜ R R d
            k (d + k) rfl).hom ((fiberLocalization R π (x₀ : M) d).hom A ⊗ₜ α)) :=
          (ConcreteCategory.congr_hom (homologyMap_comp_fiberLocalization (R ⊗ R : ModuleCat ℤ) Φ
            hΦ (x₀ : M) (d + k)) c).trans
              (congrArg _ (fiberLocalization_singularHomologyCross_tmul R R π (x₀ : M) rfl A α))
      _ = (localHomologyMap (R ⊗ R : ModuleCat ℤ) Φ hΦS (d + k)).hom
          ((TopCat.singularHomologyCrossRel (TopCat.of G) (TopCat.of F) (π ⁻¹' {(x₀ : M)})ᶜ R R d
            k (d + k) rfl).hom ((localHomologyMap R sU hsU' d).hom oU ⊗ₜ (ℓ • α))) := by
          refine (o.localHomologyMap_actionMap_singularHomologyCrossRel_eq_zsmul hd b₀ hU x₀ π hπ
            hloc sU hsU hsU' hfix hΦS (o.localHomologyMap_fiberLocalization hd π hA)).trans ?_
          -- The `ℤ`-action on these carriers is `zsmul`, so name Mathlib's instance for it.
          exact congrArg _ (congrArg _ ((CompatibleSMul.int (R := ℤ)).smul_tmul ℓ _ α))
      _ = _ :=
          (congrArg _ (singularHomologyCrossRel_localHomologyMap_tmul R R sU hsU' rfl oU
            (ℓ • α))).trans (ConcreteCategory.congr_hom (localHomologyMap_comp (R ⊗ R : ModuleCat ℤ)
              (sU.prodMap (ContinuousMap.id F)) Φ hsF hΦS (d + k)) X)
  have hΘinj : Function.Injective (localHomologyMap (R ⊗ R : ModuleCat ℤ) Θ hΘF (d + k)).hom :=
    (ModuleCat.mono_iff_injective _).1 inferInstance
  exact (livesOverFundamentalClass_iff _ _ _ _).2 fun h0 ↦
    hX (hΘinj ((key.symm.trans h0).trans (map_zero _).symm))

include o hd in
/-- **Abundance with 2-spheres from a group action** (Barraud–Damian–Humilière–Oancea,
Propositions 6.29 and 6.33, for classes coming from a group action). Let a topological group `G`
act on a compact oriented `d`-manifold `M`, with orbit map `π : G → M`, `g ↦ g • x₀`, having
continuous local sections around every point. If some `A ∈ H_d(G; ℤ)` satisfies
`π_* A = ℓ • [M]` and some class `α` of positive degree of the based mapping space `Map_*(S², M)`
satisfies `ℓ • α ≠ 0` and is fixed by every element of the stabilizer of `x₀`, then `M` is
abundant with 2-spheres at `x₀`. -/
theorem isAbundantWithTwoSpheres_of_smul_ne_zero {x₀ : M} (π : C(G, M))
    (hπ : ∀ g, π g = g • x₀)
    (hloc : ∀ y : M, ∃ U : Set M, IsOpen U ∧ y ∈ U ∧ ∃ s : M → G, ContinuousOn s U ∧
      ∀ z ∈ U, s z • x₀ = z) {ℓ : ℤ}
    {A : ((TopCat.toSSet.obj (TopCat.of G)).homology (ModuleCat.of ℤ (ULift.{0} ℤ)) d :
      ModuleCat.{0} ℤ)}
    (hA : (SSet.homologyMap (TopCat.toSSet.map (TopCat.ofHom π)) (ModuleCat.of ℤ (ULift.{0} ℤ))
      d).hom A = ℓ • o.fundamentalClass hd) {k : ℕ} (hk : 0 < k)
    {α : ((TopCat.toSSet.obj (TopCat.of (BasedMap Sphere2 M Sphere2.north x₀))).homology
      (ModuleCat.of ℤ (ULift.{0} ℤ)) k : ModuleCat.{0} ℤ)} (hα : ℓ • α ≠ 0)
    (hfix : ∀ h : MulAction.stabilizer G x₀,
      (SSet.homologyMap (TopCat.toSSet.map (TopCat.ofHom ⟨(h • · : BasedMap Sphere2 M
        Sphere2.north x₀ → BasedMap Sphere2 M Sphere2.north x₀), continuous_const_smul h⟩))
          (ModuleCat.of ℤ (ULift.{0} ℤ)) k).hom α = α) :
    IsAbundantWithTwoSpheres M d x₀ := by
  let R := ModuleCat.of ℤ (ULift.{0} ℤ)
  have hx := o.livesOverFundamentalClass_actionMap_singularHomologyCross hd Sphere2.north π hπ
    hloc hA hα hfix
  -- Identify the coefficients `ℤ ⊗ ℤ` with `ℤ`.
  let e : R ≅ 𝟙_ (ModuleCat.{0} ℤ) := (ULift.moduleEquiv : ULift.{0} ℤ ≃ₗ[ℤ] ℤ).toModuleIso
  let φ : R ⊗ R ≅ R := tensorIso e e ≪≫ λ_ (𝟙_ _) ≪≫ e.symm
  exact isAbundantWithTwoSpheres_of_lt
    ((livesOverFundamentalClass_homologyMap_coefficient_iff (R ⊗ R) φ).2 hx) (by omega)

end HomologicalOrientation

end TauCeti
