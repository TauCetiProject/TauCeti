/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Additive
public import TauCeti.RepresentationTheory.Homological.ContCohomology.ShortExact

/-!
# Short exact sequences of canonical continuous cochains

Mathlib's continuous cohomology is the homology of the homogeneous cochain complex
`TopRep.homogeneousCochains X`, whose degree-`n` term is the `G`-invariant submodule of the
iterated coinduced representation `C(G, C(G, …, C(G, X)))` with `n + 1` factors of `C(G, -)`.
This file shows that a short exact sequence `0 → A → B → C → 0` of discrete `G`-modules induces,
in **every** degree, a short exact sequence of these cochain modules. This is the input to the
snake lemma, hence to the long exact sequence of continuous cohomology in all degrees.

The three exactness statements have different hypotheses, and the statements below carry exactly
those:

* **Injectivity** (`resolutionMap_id_injective`, `cochainsMap_id_f_injective`): postcomposition
  with an injective map is injective, so this holds for any injective coefficient map.
* **Exactness in the middle** (`resolutionMap_id_exact`, `cochainsMap_id_f_exact`): a continuous
  function killed by `g` factors pointwise through `f`, and the factorization is continuous when
  `f` is inducing. For discrete `A` and `B` every injection is an embedding.
* **Surjectivity** (`cochainsMap_id_f_surjective_of_section`,
  `DiscreteShortExact.continuousCochainsShortExact_g_surjective`) is the
  substantial one, because an *invariant* cochain has to be lifted to an *invariant* cochain. A
  homogeneous cochain `F` satisfies `F(g x₀, …, g xₙ) = g • F(x₀, …, xₙ)`, and it is lifted by
  `(x₀, …, xₙ) ↦ x₀ • s (x₀⁻¹ • F(x₀, …, xₙ))` for any set-theoretic section `s` of `B → C`. The
  twisted section `(h, c) ↦ h • s (h⁻¹ • c)` is jointly continuous because `C` is discrete and the
  actions are continuous, and it is equivariant in the sense
  `k • σ(h, c) = σ(k h, k • c)`, which is what makes the lift invariant. Carrying this through the
  iterated function spaces uses continuity of evaluation `C(G, V) × G → V`, which is where local
  compactness of `G` enters; profinite groups are locally compact.

The cochain functor is defined in `Additive.lean`, and the coefficient short complex is defined
in `ShortExact.lean`.

## Main definition

* `TauCeti.ContCohomology.DiscreteShortExact.continuousCochainsShortExact`: its image under
  `continuousCochainsFunctor`, a short complex of cochain complexes.

## Main results

* `TauCeti.ContinuousCohomology.cochainsMap_id_f_surjective_of_section`: invariant cochains lift
  along any coefficient map admitting a continuous family of sections `σ : G × Z → Y` that is
  equivariant in the sense `k • σ(h, z) = σ(k h, k • z)`, over a locally compact group.
* `TauCeti.ContCohomology.DiscreteShortExact.continuousCochainsShortExact_f_injective`,
  `continuousCochainsShortExact_exact` and `continuousCochainsShortExact_g_surjective`: the
  degreewise exactness of the cochain sequence.
* `TauCeti.ContCohomology.DiscreteShortExact.continuousCochainsShortExact_map_forget₂_shortExact`:
  after forgetting topologies, the cochain sequence is a short exact sequence of cochain complexes
  of `ℤ`-modules. `TopModuleCat ℤ` is not abelian, so the snake lemma
  (`HomologicalComplex.HomologySequence`) applies only after this step.

## References

* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., Springer (2008),
  Chapter I §2 (homogeneous continuous cochains) and (1.3.2) (the long exact sequence, whose proof
  starts from the exactness of cochains proved here).
-/

public section

open CategoryTheory Topology

namespace TauCeti

namespace ContinuousCohomology

open _root_.ContinuousCohomology

universe u v

/-! ### Exactness on the coinduced resolution -/

section Resolution

variable {R : Type u} [Ring R] [TopologicalSpace R]
  {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {X Y Z : TopRep.{v} R G}

/-- The level-`(n + 1)` map of the coinduced resolution is postcomposition with the level-`n`
map. -/
@[simp]
theorem resolutionMap_id_succ_apply (f : X ⟶ Y) (n : ℕ)
    (F : C(G, (TopRep.resolutionX X n).V)) (x : G) :
    ((resolutionMap (ContinuousMonoidHom.id G) f (n + 1)).hom F :
        C(G, (TopRep.resolutionX Y n).V)) x =
      (resolutionMap (ContinuousMonoidHom.id G) f n).hom (F x) :=
  (rfl)

/-- The level maps of the coinduced resolution induced by an injective coefficient map are
injective. -/
theorem resolutionMap_id_injective {f : X ⟶ Y} (hf : Function.Injective f.hom) :
    ∀ n, Function.Injective (resolutionMap (ContinuousMonoidHom.id G) f n).hom
  | 0 => hf
  | n + 1 => ContinuousMap.postcomp_injective (X := G)
      ⟨_, (resolutionMap (ContinuousMonoidHom.id G) f n).hom.continuous⟩
      (resolutionMap_id_injective hf n)

/-- The level maps of the coinduced resolution induced by an inducing coefficient map are
inducing. -/
theorem isInducing_resolutionMap_id {f : X ⟶ Y} (hf : IsInducing f.hom) :
    ∀ n, IsInducing (resolutionMap (ContinuousMonoidHom.id G) f n).hom
  | 0 => hf
  | n + 1 => ContinuousMap.isInducing_postcomp (X := G)
      ⟨_, (resolutionMap (ContinuousMonoidHom.id G) f n).hom.continuous⟩
      (isInducing_resolutionMap_id hf n)

/-- **Exactness of the coinduced resolution in the middle.** If `X → Y → Z` is exact and the first
map is inducing, then so is every level `C(G, …, C(G, X)) → C(G, …, C(G, Y)) → C(G, …, C(G, Z))`:
a continuous function killed by the second map factors pointwise through the first, and the
factorization is continuous because the first map is inducing. -/
theorem resolutionMap_id_exact {f : X ⟶ Y} {g : Y ⟶ Z} (hf : IsInducing f.hom)
    (hfg : Function.Exact f.hom g.hom) :
    ∀ n, Function.Exact (resolutionMap (ContinuousMonoidHom.id G) f n).hom
      (resolutionMap (ContinuousMonoidHom.id G) g n).hom
  | 0 => hfg
  | n + 1 => by
    have ih := resolutionMap_id_exact hf hfg n
    intro (ψ : C(G, (TopRep.resolutionX Y n).V))
    constructor
    · intro hψ
      have hx (x : G) : ∃ a, (resolutionMap (ContinuousMonoidHom.id G) f n).hom a = ψ x :=
        (ih (ψ x)).1 <| by
          rw [← resolutionMap_id_succ_apply, hψ]
          rfl
      choose φ hφ using hx
      have hφc : Continuous φ :=
        (isInducing_resolutionMap_id hf n).continuous_iff.2 <| by
          simpa only [Function.comp_def, hφ] using ψ.continuous
      exact ⟨(⟨φ, hφc⟩ : C(G, (TopRep.resolutionX X n).V)), ContinuousMap.ext hφ⟩
    · rintro ⟨F, rfl⟩
      refine ContinuousMap.ext fun x ↦ ?_
      rw [resolutionMap_id_succ_apply, resolutionMap_id_succ_apply]
      exact (ih _).2 ⟨_, rfl⟩

end Resolution

/-! ### Exactness on homogeneous cochains -/

section Cochains

variable {R : Type u} [Ring R] [TopologicalSpace R]
  {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {X Y Z : TopRep.{v} R G}

/-- A homogeneous cochain is carried by the cochain map to its image under the level map of the
coinduced resolution.

This is deliberately not `@[simp]`, like Mathlib's `ContinuousCohomology.cochainsMap_f_hom`:
`simp` first unfolds the carrier types in the implicit arguments of the left-hand side, after
which this statement no longer matches (the `simpNF` linter rejects it). -/
theorem coe_cochainsMap_id_f_hom_apply (f : X ⟶ Y) (n : ℕ)
    (v : (TopRep.resolutionX X (n + 1)).ρ.invariants) :
    Subtype.val (((cochainsMap (ContinuousMonoidHom.id G) f).f n).hom v) =
      (resolutionMap (ContinuousMonoidHom.id G) f (n + 1)).hom v.1 :=
  (rfl)

/-- The cochain maps induced by an injective coefficient map are injective in every degree. -/
theorem cochainsMap_id_f_injective {f : X ⟶ Y} (hf : Function.Injective f.hom) (n : ℕ) :
    Function.Injective ((cochainsMap (ContinuousMonoidHom.id G) f).f n).hom := by
  intro (v : (TopRep.resolutionX X (n + 1)).ρ.invariants)
    (w : (TopRep.resolutionX X (n + 1)).ρ.invariants) h
  apply Subtype.ext
  apply resolutionMap_id_injective hf (n + 1)
  exact (coe_cochainsMap_id_f_hom_apply f n v).symm.trans
    ((congrArg Subtype.val h).trans (coe_cochainsMap_id_f_hom_apply f n w))

/-- **Exactness of homogeneous cochains in the middle.** If `X → Y → Z` is exact and the first map
is an embedding, the induced sequence of homogeneous `n`-cochains is exact. Injectivity is what
makes the preimage of an invariant cochain invariant. -/
theorem cochainsMap_id_f_exact {f : X ⟶ Y} {g : Y ⟶ Z} (hf : IsEmbedding f.hom)
    (hfg : Function.Exact f.hom g.hom) (n : ℕ) :
    Function.Exact ((cochainsMap (ContinuousMonoidHom.id G) f).f n).hom
      ((cochainsMap (ContinuousMonoidHom.id G) g).f n).hom := by
  intro (v : (TopRep.resolutionX Y (n + 1)).ρ.invariants)
  constructor
  · intro hv
    have hv' : (resolutionMap (ContinuousMonoidHom.id G) g (n + 1)).hom v.1 = 0 :=
      (coe_cochainsMap_id_f_hom_apply g n v).symm.trans (congrArg Subtype.val hv)
    obtain ⟨u, hu⟩ := (resolutionMap_id_exact hf.isInducing hfg (n + 1) _).1 hv'
    have hinv : u ∈ (TopRep.resolutionX X (n + 1)).ρ.invariants := fun k ↦ by
      apply resolutionMap_id_injective hf.injective (n + 1)
      refine ((resolutionMap (ContinuousMonoidHom.id G) f (n + 1)).hom.isIntertwining k u).trans ?_
      rw [hu]
      exact v.2 k
    exact ⟨⟨u, hinv⟩, Subtype.ext hu⟩
  · rintro ⟨u, rfl⟩
    apply Subtype.ext
    refine (coe_cochainsMap_id_f_hom_apply g n _).trans ?_
    exact (resolutionMap_id_exact hf.isInducing hfg (n + 1) _).2 ⟨u.1, rfl⟩

end Cochains

/-! ### Lifting invariant cochains along a twisted section -/

section Lift

variable {R : Type u} [Ring R] [TopologicalSpace R]
  {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {Y Z : TopRep.{v} R G}

/-- The action on the successor level of the coinduced resolution, evaluated at a point. -/
private theorem resolutionX_succ_ρ_apply_apply (X : TopRep.{v} R G) (n : ℕ)
    (k : G) (F : C(G, (TopRep.resolutionX X n).V)) (y : G) :
    ((TopRep.resolutionX X (n + 1)).ρ k F) y =
      (TopRep.resolutionX X n).ρ k (F (k⁻¹ * y)) := by
  exact ContRepresentation.coind₁_apply_apply (TopRep.resolutionX X n).ρ k F y

variable [LocallyCompactSpace G]

/-- A continuous family `σ : G × Z → Y` of maps, transported to every level of the coinduced
resolution by `σₙ₊₁ (h, φ) = (y ↦ σₙ (h, φ y))`. Continuity at each level uses continuity of
evaluation on `C(G, -)`, which is where local compactness of `G` is used. -/
private noncomputable def levelLift (σ : C(G × Z.V, Y.V)) :
    (n : ℕ) → C(G × (TopRep.resolutionX Z n).V, (TopRep.resolutionX Y n).V)
  | 0 => σ
  | n + 1 => ContinuousMap.curry
      ⟨fun p : (G × C(G, (TopRep.resolutionX Z n).V)) × G ↦ levelLift σ n (p.1.1, p.1.2 p.2),
        (levelLift σ n).continuous.comp <| continuous_fst.fst.prodMk <|
          continuous_eval.comp (continuous_fst.snd.prodMk continuous_snd)⟩

private theorem levelLift_succ_apply (σ : C(G × Z.V, Y.V)) (n : ℕ) (h : G)
    (φ : C(G, (TopRep.resolutionX Z n).V)) (y : G) :
    (levelLift σ (n + 1) (h, φ) : C(G, (TopRep.resolutionX Y n).V)) y =
      levelLift σ n (h, φ y) :=
  (rfl)

/-- Every level of the transported family is a section of the level map of `g`. -/
private theorem resolutionMap_levelLift (σ : C(G × Z.V, Y.V)) (g : Y ⟶ Z)
    (hσ : ∀ h z, g.hom (σ (h, z)) = z) :
    ∀ n h φ, (resolutionMap (ContinuousMonoidHom.id G) g n).hom (levelLift σ n (h, φ)) = φ
  | 0, h, z => hσ h z
  | n + 1, h, (φ : C(G, (TopRep.resolutionX Z n).V)) => ContinuousMap.ext fun y ↦ by
    rw [resolutionMap_id_succ_apply, levelLift_succ_apply, resolutionMap_levelLift σ g hσ n]

/-- Every level of the transported family is equivariant in the sense
`k • σₙ (h, φ) = σₙ (k h, k • φ)`. -/
private theorem ρ_levelLift (σ : C(G × Z.V, Y.V))
    (hσ : ∀ k h z, Y.ρ k (σ (h, z)) = σ (k * h, Z.ρ k z)) :
    ∀ n k h φ, (TopRep.resolutionX Y n).ρ k (levelLift σ n (h, φ)) =
      levelLift σ n (k * h, (TopRep.resolutionX Z n).ρ k φ)
  | 0, k, h, z => hσ k h z
  | n + 1, k, h, (φ : C(G, (TopRep.resolutionX Z n).V)) => ContinuousMap.ext fun y ↦ by
    calc
      ((TopRep.resolutionX Y (n + 1)).ρ k (levelLift σ (n + 1) (h, φ))) y =
          (TopRep.resolutionX Y n).ρ k
            ((levelLift σ (n + 1) (h, φ)) (k⁻¹ * y)) :=
        resolutionX_succ_ρ_apply_apply Y n k _ y
      _ = levelLift σ n (k * h, (TopRep.resolutionX Z n).ρ k (φ (k⁻¹ * y))) := by
        rw [levelLift_succ_apply]
        exact ρ_levelLift σ hσ n k h (φ (k⁻¹ * y))
      _ = (levelLift σ (n + 1)
          (k * h, (TopRep.resolutionX Z (n + 1)).ρ k φ)) y := by
        rw [levelLift_succ_apply, resolutionX_succ_ρ_apply_apply]

/-- **Invariant cochains lift along a map with an equivariant continuous family of sections.** If
`σ : G × Z → Y` is continuous, `g (σ (h, z)) = z` and `k • σ (h, z) = σ (k h, k • z)`, then every
homogeneous `n`-cochain of `Z` is the image of one of `Y`: the lift of `F` is
`x ↦ σₙ (x, F x)`. -/
theorem cochainsMap_id_f_surjective_of_section (g : Y ⟶ Z) (σ : C(G × Z.V, Y.V))
    (hσ : ∀ h z, g.hom (σ (h, z)) = z)
    (hσ' : ∀ k h z, Y.ρ k (σ (h, z)) = σ (k * h, Z.ρ k z)) (n : ℕ) :
    Function.Surjective ((cochainsMap (ContinuousMonoidHom.id G) g).f n).hom := by
  intro (F : (TopRep.resolutionX Z (n + 1)).ρ.invariants)
  let F₀ : C(G, (TopRep.resolutionX Z n).V) := F.1
  let L : C(G, (TopRep.resolutionX Y n).V) :=
    ⟨fun x ↦ levelLift σ n (x, F₀ x), (levelLift σ n).continuous.comp
      (continuous_id.prodMk F₀.continuous)⟩
  have hL : L ∈ (TopRep.resolutionX Y (n + 1)).ρ.invariants := fun k ↦ ContinuousMap.ext fun y ↦ by
    calc
      ((TopRep.resolutionX Y (n + 1)).ρ k L) y =
          (TopRep.resolutionX Y n).ρ k (L (k⁻¹ * y)) :=
        resolutionX_succ_ρ_apply_apply Y n k L y
      _ = levelLift σ n (y, F₀ y) := by
        -- The invariant condition is stated for the successor resolution; unfold its action
        -- to apply the equivariance rule for `levelLift` at level `n`.
        change (TopRep.resolutionX Y n).ρ k
          (levelLift σ n (k⁻¹ * y, F₀ (k⁻¹ * y))) = levelLift σ n (y, F₀ y)
        rw [ρ_levelLift σ hσ', mul_inv_cancel_left]
        congr 2
        exact congrArg (fun F' : C(G, (TopRep.resolutionX Z n).V) ↦ F' y) (F.2 k)
      _ = L y := rfl
  refine ⟨⟨L, hL⟩, Subtype.ext ((coe_cochainsMap_id_f_hom_apply g n ⟨L, hL⟩).trans ?_)⟩
  exact ContinuousMap.ext fun y ↦ by
    rw [resolutionMap_id_succ_apply]
    exact resolutionMap_levelLift σ g hσ n y (F₀ y)

end Lift

end ContinuousCohomology

namespace ContCohomology

namespace DiscreteShortExact

open _root_.ContinuousCohomology _root_.TauCeti.ContinuousCohomology

universe u

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {A : Type u} [AddCommGroup A] [TopologicalSpace A] [DiscreteTopology A] [DistribMulAction G A]
  {B : Type u} [AddCommGroup B] [TopologicalSpace B] [DiscreteTopology B] [DistribMulAction G B]
  {C : Type u} [AddCommGroup C] [TopologicalSpace C] [DiscreteTopology C] [DistribMulAction G C]
  (S : DiscreteShortExact G A B C)

-- Exposed because the generated `@[simps!]` field lemmas are `rfl` proofs about this body.
/-- The short complex of canonical homogeneous-cochain complexes attached to a short exact
sequence of discrete `G`-modules: in degree `n` it is
`Cⁿ(G, A) → Cⁿ(G, B) → Cⁿ(G, C)` on Mathlib's homogeneous continuous cochains. -/
@[expose, simps!]
noncomputable def continuousCochainsShortExact :
    ShortComplex (CochainComplex (TopModuleCat.{u} ℤ) ℕ) :=
  S.toShortComplex.map (continuousCochainsFunctor ℤ G)

/-- The cochain map induced by the inclusion `A → B` is injective in every degree. -/
theorem continuousCochainsShortExact_f_injective (n : ℕ) :
    Function.Injective (S.continuousCochainsShortExact.f.f n).hom :=
  cochainsMap_id_f_injective S.incl_injective n

/-- The sequence of homogeneous `n`-cochains `Cⁿ(G, A) → Cⁿ(G, B) → Cⁿ(G, C)` is exact in the
middle, in every degree. -/
theorem continuousCochainsShortExact_exact (n : ℕ) :
    Function.Exact (S.continuousCochainsShortExact.f.f n).hom
      (S.continuousCochainsShortExact.g.f n).hom :=
  cochainsMap_id_f_exact
    (IsClosedEmbedding.of_continuous_injective_isClosedMap continuous_of_discreteTopology
      S.incl_injective fun _ _ ↦ isClosed_discrete _).isEmbedding S.exact n

/-- **Continuous cochains lift along `B → C` in every degree.** For a locally compact group `G`
acting continuously on the discrete modules `B` and `C`, every homogeneous continuous `n`-cochain
with values in `C` is the image of one with values in `B`. -/
theorem continuousCochainsShortExact_g_surjective [LocallyCompactSpace G]
    [ContinuousSMul G B] [ContinuousSMul G C] (n : ℕ) :
    Function.Surjective (S.continuousCochainsShortExact.g.f n).hom := by
  let s : C → B := Function.surjInv S.proj_surjective
  let σ : C(G × C, B) :=
    ⟨fun p ↦ p.1 • s (p.1⁻¹ • p.2), continuous_fst.smul
      ((continuous_of_discreteTopology (f := s)).comp (continuous_fst.inv.smul continuous_snd))⟩
  refine cochainsMap_id_f_surjective_of_section _ σ (fun h (c : C) ↦ ?_)
    (fun k h (c : C) ↦ ?_) n
  · -- Unfold `σ` to use the public rule identifying the short-complex projection with `proj`.
    change S.toShortComplex.g.hom (h • s (h⁻¹ • c)) = c
    rw [S.toShortComplex_g_hom_apply]
    rw [S.proj_equivariant, Function.surjInv_eq S.proj_surjective, smul_inv_smul]
  · -- Unfold the bundled coefficient actions before reducing the equivariance identity.
    change (S.toShortComplex.X₂).ρ k (σ (h, c)) =
      σ (k * h, (S.toShortComplex.X₃).ρ k c)
    rw [S.toShortComplex_X₂_ρ_apply, S.toShortComplex_X₃_ρ_apply]
    -- Both sides now have the original coefficient carriers, so unfold `σ` to compare actions.
    change k • (h • s (h⁻¹ • c)) = (k * h) • s ((k * h)⁻¹ • (k • c))
    rw [mul_inv_rev, mul_smul, mul_smul, inv_smul_smul]

/-- **The cochain sequence of a short exact sequence of discrete modules is short exact.** After
forgetting topologies, `0 → C•(G, A) → C•(G, B) → C•(G, C) → 0` is a short exact sequence of
cochain complexes of `ℤ`-modules, for a locally compact group `G` acting continuously on `B` and
`C`. This is the input to the snake lemma, and hence to the long exact sequence of continuous
cohomology in every degree. -/
theorem continuousCochainsShortExact_map_forget₂_shortExact [LocallyCompactSpace G]
    [ContinuousSMul G B] [ContinuousSMul G C] :
    (S.continuousCochainsShortExact.map
      ((forget₂ (TopModuleCat.{u} ℤ) (ModuleCat.{u} ℤ)).mapHomologicalComplex _)).ShortExact :=
  HomologicalComplex.shortExact_of_degreewise_shortExact _ fun n ↦
    ModuleCat.shortComplex_shortExact _ (S.continuousCochainsShortExact_exact n)
      (S.continuousCochainsShortExact_f_injective n)
      (S.continuousCochainsShortExact_g_surjective n)

end DiscreteShortExact

end ContCohomology

end TauCeti
