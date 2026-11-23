/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Additive
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Resolution.Basic
public import TauCeti.RepresentationTheory.Homological.ContCohomology.ShortExact
import TauCeti.Topology.Algebra.Group.Profinite.Section

/-!
# Short exact sequences of canonical continuous cochains

Mathlib's continuous cohomology is the homology of the homogeneous cochain complex
`TopRep.homogeneousCochains X`, whose degree-`n` term is the `G`-invariant submodule of the
iterated coinduced representation `C(G, C(G, …, C(G, X)))` with `n + 1` factors of `C(G, -)`.
This file shows that a topologically short exact sequence `0 → X₁ → X₂ → X₃ → 0` of topological
`G`-modules (`CategoryTheory.ShortComplex.TopShortExact`: an embedding followed by a map with a
continuous set-theoretic section, with `G` acting jointly continuously on `X₂`) induces, in
**every** degree, a short exact sequence of these cochain modules; a short exact sequence of
discrete `G`-modules is an instance. This is the input to the snake lemma, hence to the long exact
sequence of continuous cohomology in all degrees.

The three exactness statements have different hypotheses, and the statements below carry exactly
those:

* **Injectivity** (`resolutionMap_injective`, `cochainsMap_f_injective`): postcomposition
  with an injective map is injective, so this holds for any injective coefficient map.
* **Exactness in the middle** (`resolutionMap_id_exact`, `cochainsMap_id_f_exact`): a continuous
  function killed by `g` factors pointwise through `f`, and the factorization is continuous when
  `f` is inducing. For discrete coefficients every injection is an embedding.
* **Surjectivity** (`cochainsMap_id_f_surjective_of_section`,
  `CategoryTheory.ShortComplex.TopShortExact.cochainsMap_g_f_surjective`) is the
  substantial one, because an *invariant* cochain has to be lifted to an *invariant* cochain. A
  homogeneous cochain `F` satisfies `F(g x₀, …, g xₙ) = g • F(x₀, …, xₙ)`, and it is lifted by
  `(x₀, …, xₙ) ↦ x₀ • s (x₀⁻¹ • F(x₀, …, xₙ))` for a continuous section `s` of `X₂ → X₃`. The
  twisted section `(h, c) ↦ h • s (h⁻¹ • c)` is jointly continuous because the actions are, and
  it is equivariant in the sense
  `k • σ(h, c) = σ(k h, k • c)`, which is what makes the lift invariant. Carrying this through the
  iterated function spaces uses continuity of evaluation `C(G, V) × G → V`, which is where local
  compactness of `G` enters; profinite groups are locally compact.

The cochain functor is defined in `Additive.lean`, and the coefficient short complex is defined
in `ShortExact.lean`.

## Main definitions

* `CategoryTheory.ShortComplex.TopShortExact`: a short complex of topological representations
  whose second map has a continuous section, with an embedding as first map and a jointly
  continuous action on the middle term.
* `TauCeti.ContCohomology.DiscreteShortExact.continuousCochainsShortExact`: the image of a short
  exact sequence of discrete modules under `continuousCochainsFunctor`, a short complex of cochain
  complexes.

## Main results

* `TauCeti.ContinuousCohomology.cochainsMap_id_f_surjective_of_section`: invariant cochains lift
  along any coefficient map admitting a continuous family of sections `σ : G × Z → Y` that is
  equivariant in the sense `k • σ(h, z) = σ(k h, k • z)`, over a locally compact group.
* `CategoryTheory.ShortComplex.TopShortExact.cochains_shortExact_moduleCat`: after forgetting
  topologies, the cochains of a topologically short exact sequence form a short exact sequence of
  cochain complexes of modules.
* `CategoryTheory.ShortComplex.TopShortExact.of_compactSpace`: a short complex with profinite
  middle term, Hausdorff last term, an embedding as first map, a surjective second map, exact in
  the middle, and a jointly continuous action on the middle term, is topologically short exact.
* `TauCeti.ContCohomology.DiscreteShortExact.topShortExact`: a short exact sequence of discrete
  modules, with a continuous action on the middle term, is topologically short exact.
* `TauCeti.ContCohomology.DiscreteShortExact.continuousCochainsShortExact_f_injective`,
  `continuousCochainsShortExact_exact` and `continuousCochainsShortExact_g_surjective`: the
  degreewise exactness of the cochain sequence.
* `TauCeti.ContCohomology.DiscreteShortExact.continuousCochainsShortExact_shortExact_moduleCat`:
  after forgetting topologies, the cochain sequence is a short exact sequence of cochain complexes
  of `ℤ`-modules. `TopModuleCat ℤ` is not abelian, so the snake lemma
  (`HomologicalComplex.HomologySequence`) applies only after this step.

## References

* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., Springer (2008),
  Chapter I §2 (homogeneous continuous cochains), (1.3.2) (the long exact sequence, whose proof
  starts from the exactness of cochains proved here), Chapter I §1, Exercise 4 (the continuous
  section for compact coefficients) and Chapter II §7, Lemma 2.7.2 (the cochain sequence and the
  long exact sequence for topological coefficients).
* K. Rubin, *Euler Systems*, Annals of Mathematics Studies 147, Princeton University Press (2000),
  Appendix B, §2, Definition 2.1.
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

-- Stated through `dsimp% only`: `simp` reduces the implicit carrier types of the level map,
-- `(TopRep.resolutionX X (n + 1)).V` restricted along the identity, to `C(G, _)` before it looks
-- a term up, so the plain form is never found.
/-- The level-`(n + 1)` map of the coinduced resolution is postcomposition with the level-`n`
map. -/
@[simp]
theorem resolutionMap_id_succ_apply (f : X ⟶ Y) (n : ℕ)
    (F : C(G, (TopRep.resolutionX X n).V)) (x : G) :
    (dsimp% only (((resolutionMap (ContinuousMonoidHom.id G) f (n + 1)).hom F :
        C(G, (TopRep.resolutionX Y n).V)) x)) =
      (resolutionMap (ContinuousMonoidHom.id G) f n).hom (F x) :=
  (rfl)

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

-- This is not `@[simp]`: simplifying the implicit carrier types makes the left side no longer
-- match, as with Mathlib's `ContinuousCohomology.cochainsMap_f_hom`.
/-- A homogeneous cochain is carried by the cochain map to its image under the level map of the
coinduced resolution. -/
theorem coe_cochainsMap_id_f_hom_apply (f : X ⟶ Y) (n : ℕ)
    (v : (TopRep.resolutionX X (n + 1)).ρ.invariants) :
    Subtype.val (((cochainsMap (ContinuousMonoidHom.id G) f).f n).hom v) =
      (resolutionMap (ContinuousMonoidHom.id G) f (n + 1)).hom v.val :=
  (rfl)

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
    have hv' : (resolutionMap (ContinuousMonoidHom.id G) g (n + 1)).hom v.val = 0 :=
      (coe_cochainsMap_id_f_hom_apply g n v).symm.trans (congrArg Subtype.val hv)
    obtain ⟨u, hu⟩ := (resolutionMap_id_exact hf.isInducing hfg (n + 1) _).1 hv'
    have hinv : u ∈ (TopRep.resolutionX X (n + 1)).ρ.invariants := fun k ↦ by
      apply resolutionMap_injective (ContinuousMonoidHom.id G) f Function.surjective_id
        hf.injective (n + 1)
      refine ((resolutionMap (ContinuousMonoidHom.id G) f (n + 1)).hom.isIntertwining k u).trans ?_
      rw [hu]
      exact v.property k
    refine ⟨⟨u, hinv⟩, Subtype.ext ?_⟩
    exact (coe_cochainsMap_id_f_hom_apply f n ⟨u, hinv⟩).trans hu
  · rintro ⟨u, rfl⟩
    apply Subtype.ext
    refine (coe_cochainsMap_id_f_hom_apply g n _).trans ?_
    exact (resolutionMap_id_exact hf.isInducing hfg (n + 1) _).2
      ⟨u.val, (coe_cochainsMap_id_f_hom_apply f n u).symm⟩

end Cochains

/-! ### Lifting invariant cochains along a twisted section -/

section Lift

variable {R : Type u} [Ring R] [TopologicalSpace R]
  {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {Y Z : TopRep.{v} R G}

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
        TopRep.resolutionX_succ_ρ_apply_apply Y n k _ y
      _ = levelLift σ n (k * h, (TopRep.resolutionX Z n).ρ k (φ (k⁻¹ * y))) := by
        rw [levelLift_succ_apply]
        exact ρ_levelLift σ hσ n k h (φ (k⁻¹ * y))
      _ = (levelLift σ (n + 1)
          (k * h, (TopRep.resolutionX Z (n + 1)).ρ k φ)) y := by
        rw [levelLift_succ_apply, TopRep.resolutionX_succ_ρ_apply_apply]

/-- **Invariant cochains lift along a map with an equivariant continuous family of sections.** If
`σ : G × Z → Y` is continuous, `g (σ (h, z)) = z` and `k • σ (h, z) = σ (k h, k • z)`, then every
homogeneous `n`-cochain of `Z` is the image of one of `Y`: the lift of `F` is
`x ↦ σₙ (x, F x)`. -/
theorem cochainsMap_id_f_surjective_of_section (g : Y ⟶ Z) (σ : C(G × Z.V, Y.V))
    (hσ : ∀ h z, g.hom (σ (h, z)) = z)
    (hσ' : ∀ k h z, Y.ρ k (σ (h, z)) = σ (k * h, Z.ρ k z)) (n : ℕ) :
    Function.Surjective ((cochainsMap (ContinuousMonoidHom.id G) g).f n).hom := by
  intro (F : (TopRep.resolutionX Z (n + 1)).ρ.invariants)
  let F₀ : C(G, (TopRep.resolutionX Z n).V) := F.val
  let L : C(G, (TopRep.resolutionX Y n).V) :=
    ⟨fun x ↦ levelLift σ n (x, F₀ x), (levelLift σ n).continuous.comp
      (continuous_id.prodMk F₀.continuous)⟩
  have hL : L ∈ (TopRep.resolutionX Y (n + 1)).ρ.invariants := fun k ↦ ContinuousMap.ext fun y ↦ by
    calc
      ((TopRep.resolutionX Y (n + 1)).ρ k L) y =
          (TopRep.resolutionX Y n).ρ k (L (k⁻¹ * y)) :=
        TopRep.resolutionX_succ_ρ_apply_apply Y n k L y
      _ = levelLift σ n (y, F₀ y) := by
        -- The invariant condition is stated for the successor resolution; unfold its action
        -- to apply the equivariance rule for `levelLift` at level `n`.
        change (TopRep.resolutionX Y n).ρ k
          (levelLift σ n (k⁻¹ * y, F₀ (k⁻¹ * y))) = levelLift σ n (y, F₀ y)
        rw [ρ_levelLift σ hσ', mul_inv_cancel_left]
        congr 2
        exact congrArg (fun F' : C(G, (TopRep.resolutionX Z n).V) ↦ F' y) (F.property k)
      _ = L y := rfl
  refine ⟨⟨L, hL⟩, Subtype.ext ((coe_cochainsMap_id_f_hom_apply g n ⟨L, hL⟩).trans ?_)⟩
  exact ContinuousMap.ext fun y ↦ by
    rw [resolutionMap_id_succ_apply]
    exact resolutionMap_levelLift σ g hσ n y (F₀ y)

end Lift

end ContinuousCohomology

end TauCeti

/-! ### Short exact sequences with a continuous section -/

namespace CategoryTheory.ShortComplex

open _root_.ContinuousCohomology TauCeti.ContinuousCohomology

universe u v

variable {R : Type u} [Ring R] [TopologicalSpace R]
  {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- A short complex `0 → X₁ → X₂ → X₃ → 0` of topological representations is *topologically
short exact* when `X₁ → X₂` is a topological embedding, the sequence is exact at `X₂`, the map
`X₂ → X₃` has a continuous set-theoretic section, and `G` acts jointly continuously on `X₂`.
These are the conditions under which the homogeneous continuous cochains form a short exact
sequence in every degree (`TopShortExact.cochains_shortExact_moduleCat`), so that continuous
cohomology has a long exact sequence. A short exact sequence of discrete modules is an instance
(`TauCeti.ContCohomology.DiscreteShortExact.topShortExact`); for compact coefficients, a
continuous section of a continuous surjection of profinite additive groups exists by
`AddMonoidHom.exists_continuous_section_of_surjective`. -/
structure TopShortExact (S : ShortComplex (TopRep.{v} R G)) : Prop where
  /-- The first map is a topological embedding. -/
  isEmbedding_f : IsEmbedding S.f.hom
  /-- The sequence is exact at the middle term. -/
  exact : Function.Exact S.f.hom S.g.hom
  /-- The second map has a continuous set-theoretic section. -/
  exists_continuous_section : ∃ s : S.X₃ → S.X₂, Continuous s ∧ ∀ z, S.g.hom (s z) = z
  /-- The group acts jointly continuously on the middle term. -/
  continuous_ρ₂ : Continuous fun p : G × S.X₂ ↦ S.X₂.ρ p.1 p.2

namespace TopShortExact

omit [IsTopologicalGroup G] in
/-- **Compact coefficients.** A short complex of topological representations whose middle term is
profinite as an additive group and whose last term is Hausdorff is topologically short exact as
soon as its first map is an embedding, it is exact at the middle term, its second map is surjective
and `G` acts jointly continuously on the middle term: the continuous section is provided by
`AddMonoidHom.exists_continuous_section_of_surjective`. -/
theorem of_compactSpace {S : ShortComplex (TopRep.{v} R G)} [CompactSpace S.X₂]
    [TotallyDisconnectedSpace S.X₂] [T2Space S.X₃] (hf : IsEmbedding S.f.hom)
    (hfg : Function.Exact S.f.hom S.g.hom) (hg : Function.Surjective S.g.hom)
    (hρ : Continuous fun p : G × S.X₂ ↦ S.X₂.ρ p.1 p.2) : S.TopShortExact where
  isEmbedding_f := hf
  exact := hfg
  exists_continuous_section := by
    obtain ⟨s, hs, hgs, -⟩ := AddMonoidHom.exists_continuous_section_of_surjective
      (S.g.hom : S.X₂ →+ S.X₃) S.g.hom.continuous hg
    exact ⟨s, hs, hgs⟩
  continuous_ρ₂ := hρ

variable {S : ShortComplex (TopRep.{v} R G)} (hS : S.TopShortExact)
include hS

section

omit [IsTopologicalGroup G]

/-- The first map of a topologically short exact sequence is injective. -/
theorem injective_f : Function.Injective S.f.hom :=
  hS.isEmbedding_f.injective

/-- The second map of a topologically short exact sequence is surjective. -/
theorem surjective_g : Function.Surjective S.g.hom := by
  obtain ⟨s, -, hgs⟩ := hS.exists_continuous_section
  exact fun z ↦ ⟨s z, hgs z⟩

/-- The group acts jointly continuously on the last term of a topologically short exact
sequence: `h • z = g (h • s z)` for the continuous section `s`. -/
theorem continuous_ρ₃ : Continuous fun p : G × S.X₃ ↦ S.X₃.ρ p.1 p.2 := by
  obtain ⟨s, hs, hgs⟩ := hS.exists_continuous_section
  have h : (fun p : G × S.X₃ ↦ S.X₃.ρ p.1 p.2) = fun p ↦ S.g.hom (S.X₂.ρ p.1 (s p.2)) := by
    funext p
    rw [S.g.hom.isIntertwining, hgs]
  rw [h]
  exact S.g.hom.continuous.comp
    (hS.continuous_ρ₂.comp (continuous_fst.prodMk (hs.comp continuous_snd)))

end

/-- **Continuous cochains lift along the second map** of a topologically short exact sequence,
in every degree, over a locally compact group. The lift uses the twisted section
`(h, z) ↦ h • s (h⁻¹ • z)`, which is continuous by joint continuity of the actions and
equivariant. -/
theorem cochainsMap_g_f_surjective [LocallyCompactSpace G] (n : ℕ) :
    Function.Surjective ((cochainsMap (ContinuousMonoidHom.id G) S.g).f n).hom := by
  obtain ⟨s, hs, hgs⟩ := hS.exists_continuous_section
  let σ : C(G × S.X₃, S.X₂) :=
    ⟨fun p ↦ S.X₂.ρ p.1 (s (S.X₃.ρ p.1⁻¹ p.2)), hS.continuous_ρ₂.comp <| continuous_fst.prodMk <|
      hs.comp <| hS.continuous_ρ₃.comp (continuous_fst.inv.prodMk continuous_snd)⟩
  have hσ (h : G) (z : S.X₃) : σ (h, z) = S.X₂.ρ h (s (S.X₃.ρ h⁻¹ z)) := rfl
  refine cochainsMap_id_f_surjective_of_section S.g σ (fun h z ↦ ?_) (fun k h z ↦ ?_) n
  · simp [hσ, S.g.hom.isIntertwining, hgs, ← mul_apply_eq_comp, ← map_mul]
  · simp [hσ, ← mul_apply_eq_comp, ← map_mul, mul_assoc]

/-- **The cochain sequence of a topologically short exact sequence is short exact.** After
forgetting topologies, `0 → C•(G, X₁) → C•(G, X₂) → C•(G, X₃) → 0` is a short exact sequence of
cochain complexes of modules, for a locally compact group `G`. This is the input to the snake
lemma, and hence to the long exact sequence of continuous cohomology in every degree. -/
theorem cochains_shortExact_moduleCat [LocallyCompactSpace G] :
    ((S.map (continuousCochainsFunctor R G)).map
      ((forget₂ (TopModuleCat.{v} R) (ModuleCat.{v} R)).mapHomologicalComplex _)).ShortExact :=
  HomologicalComplex.shortExact_of_degreewise_shortExact _ fun n ↦
    ModuleCat.shortComplex_shortExact _ (cochainsMap_id_f_exact hS.isEmbedding_f hS.exact n)
      (cochainsMap_f_injective (ContinuousMonoidHom.id G) S.f Function.surjective_id
        hS.injective_f n)
      (hS.cochainsMap_g_f_surjective n)

end TopShortExact

end CategoryTheory.ShortComplex

namespace TauCeti

namespace ContCohomology

namespace DiscreteShortExact

open _root_.ContinuousCohomology _root_.TauCeti.ContinuousCohomology

universe u

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {A : Type u} [AddCommGroup A] [TopologicalSpace A] [DiscreteTopology A] [DistribMulAction G A]
  {B : Type u} [AddCommGroup B] [TopologicalSpace B] [DiscreteTopology B] [DistribMulAction G B]
  {C : Type u} [AddCommGroup C] [TopologicalSpace C] [DiscreteTopology C] [DistribMulAction G C]
  (S : DiscreteShortExact G A B C)

-- Exposed so that the homology of its terms is `continuousCohomology` by definition: the
-- connecting map of `HomologySequence.lean` is transported along that identification.
/-- The short complex of canonical homogeneous-cochain complexes attached to a short exact
sequence of discrete `G`-modules: in degree `n` it is
`Cⁿ(G, A) → Cⁿ(G, B) → Cⁿ(G, C)` on Mathlib's homogeneous continuous cochains. -/
@[expose]
noncomputable def continuousCochainsShortExact :
    ShortComplex (CochainComplex (TopModuleCat.{u} ℤ) ℕ) :=
  S.toShortComplex.map (continuousCochainsFunctor ℤ G)

/-- The first cochain complex is the image of the first coefficient representation. -/
@[simp] theorem continuousCochainsShortExact_X₁ :
    S.continuousCochainsShortExact.X₁ =
      (continuousCochainsFunctor ℤ G).obj S.toShortComplex.X₁ := by
  unfold continuousCochainsShortExact
  rfl

/-- The middle cochain complex is the image of the middle coefficient representation. -/
@[simp] theorem continuousCochainsShortExact_X₂ :
    S.continuousCochainsShortExact.X₂ =
      (continuousCochainsFunctor ℤ G).obj S.toShortComplex.X₂ := by
  unfold continuousCochainsShortExact
  rfl

/-- The last cochain complex is the image of the last coefficient representation. -/
@[simp] theorem continuousCochainsShortExact_X₃ :
    S.continuousCochainsShortExact.X₃ =
      (continuousCochainsFunctor ℤ G).obj S.toShortComplex.X₃ := by
  unfold continuousCochainsShortExact
  rfl

/-- The first cochain map is the functorial image of the coefficient inclusion, after
transporting its source and target along the object identifications. -/
theorem continuousCochainsShortExact_f :
    S.continuousCochainsShortExact.f ≫ eqToHom S.continuousCochainsShortExact_X₂ =
      eqToHom S.continuousCochainsShortExact_X₁ ≫
        (continuousCochainsFunctor ℤ G).map S.toShortComplex.f := by
  unfold continuousCochainsShortExact
  rfl

/-- The second cochain map is the functorial image of the coefficient projection, after
transporting its source and target along the object identifications. -/
theorem continuousCochainsShortExact_g :
    S.continuousCochainsShortExact.g ≫ eqToHom S.continuousCochainsShortExact_X₃ =
      eqToHom S.continuousCochainsShortExact_X₂ ≫
        (continuousCochainsFunctor ℤ G).map S.toShortComplex.g := by
  unfold continuousCochainsShortExact
  rfl

/-- On homogeneous cochains, the short-complex inclusion is the compatible-pair cochain map
of the given coefficient inclusion. -/
theorem continuousCochainsShortExact_f_f_apply (k : ℕ)
    (x : (TopRep.homogeneousCochains (ofDiscreteModule ℤ G A)).X k) :
    (S.continuousCochainsShortExact.f.f k).hom x =
      (cochainsMap (ContinuousMonoidHom.id G)
        (ofDiscreteModulePair (ContinuousMonoidHom.id G : G →* G)
          S.incl.toIntLinearMap S.incl_equivariant)).f k x := by
  rw [cochainsMap_ofDiscreteModulePair_id]
  rfl

/-- On homogeneous cochains, the short-complex projection is the compatible-pair cochain map
of the given coefficient projection. -/
theorem continuousCochainsShortExact_g_f_apply (k : ℕ)
    (x : (TopRep.homogeneousCochains (ofDiscreteModule ℤ G B)).X k) :
    (S.continuousCochainsShortExact.g.f k).hom x =
      (cochainsMap (ContinuousMonoidHom.id G)
        (ofDiscreteModulePair (ContinuousMonoidHom.id G : G →* G)
          S.proj.toIntLinearMap S.proj_equivariant)).f k x := by
  rw [cochainsMap_ofDiscreteModulePair_id]
  rfl

/-- The cochain map induced by the inclusion `A → B` is injective in every degree. -/
theorem continuousCochainsShortExact_f_injective (n : ℕ) :
    Function.Injective (S.continuousCochainsShortExact.f.f n).hom := by
  intro x y h
  apply Subtype.ext
  apply resolutionMap_injective (ContinuousMonoidHom.id G)
    (ofDiscreteModuleMap S.incl.toIntLinearMap S.incl_equivariant)
    Function.surjective_id S.incl_injective (n + 1)
  exact congrArg Subtype.val h

/-- The sequence of homogeneous `n`-cochains `Cⁿ(G, A) → Cⁿ(G, B) → Cⁿ(G, C)` is exact in the
middle, in every degree. -/
theorem continuousCochainsShortExact_exact (n : ℕ) :
    Function.Exact (S.continuousCochainsShortExact.f.f n).hom
      (S.continuousCochainsShortExact.g.f n).hom :=
  cochainsMap_id_f_exact
    (IsClosedEmbedding.of_continuous_injective_isClosedMap continuous_of_discreteTopology
      S.incl_injective fun _ _ ↦ isClosed_discrete _).isEmbedding S.exact n

omit [IsTopologicalGroup G] in
/-- **A short exact sequence of discrete modules is topologically short exact** when `G` acts
continuously on the middle term: an injection of discrete spaces is an embedding, and every
set-theoretic section of `B → C` is continuous because `C` is discrete. -/
theorem topShortExact [ContinuousSMul G B] : S.toShortComplex.TopShortExact where
  isEmbedding_f := (IsClosedEmbedding.of_continuous_injective_isClosedMap
    continuous_of_discreteTopology S.incl_injective fun _ _ ↦ isClosed_discrete _).isEmbedding
  -- The remaining fields hold by unfolding `toShortComplex`, `ofDiscreteModuleMap` and
  -- `ofDiscreteModule`: the objects are `B` and `C`, the maps are `S.incl` and `S.proj` on
  -- elements, and `X₂.ρ` is the given action (`toShortComplex_g_hom_apply`,
  -- `toShortComplex_X₂_ρ_apply`). Those rfl lemmas are stated for elements of `B` and do not
  -- match elements of `S.toShortComplex.X₂` syntactically, so the fields are given as terms.
  exact := S.exact
  exists_continuous_section := ⟨Function.surjInv S.proj_surjective,
    continuous_of_discreteTopology (α := C), Function.surjInv_eq S.proj_surjective⟩
  continuous_ρ₂ := continuous_smul (M := G) (X := B)

/-- **Continuous cochains lift along `B → C` in every degree.** For a locally compact group `G`
acting continuously on the discrete module `B`, every homogeneous continuous `n`-cochain with
values in `C` is the image of one with values in `B`. -/
theorem continuousCochainsShortExact_g_surjective [LocallyCompactSpace G]
    [ContinuousSMul G B] (n : ℕ) :
    Function.Surjective (S.continuousCochainsShortExact.g.f n).hom :=
  S.topShortExact.cochainsMap_g_f_surjective n

/-- **The cochain sequence of a short exact sequence of discrete modules is short exact.** After
forgetting topologies, `0 → C•(G, A) → C•(G, B) → C•(G, C) → 0` is a short exact sequence of
cochain complexes of `ℤ`-modules, for a locally compact group `G` acting continuously on `B`.
This is the input to the snake lemma, and hence to the long exact sequence of continuous
cohomology in every degree. -/
theorem continuousCochainsShortExact_shortExact_moduleCat [LocallyCompactSpace G]
    [ContinuousSMul G B] :
    (S.continuousCochainsShortExact.map
      ((forget₂ (TopModuleCat.{u} ℤ) (ModuleCat.{u} ℤ)).mapHomologicalComplex _)).ShortExact :=
  S.topShortExact.cochains_shortExact_moduleCat

end DiscreteShortExact

end ContCohomology

end TauCeti
