/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cohomology.Cup.Pullback
public import TauCeti.AlgebraicTopology.Cohomology.ProdThomPair.Basic
import Mathlib.Topology.Algebra.Module.FiniteDimension
import TauCeti.Algebra.Module.Equiv.SpanSingleton
import TauCeti.AlgebraicTopology.Cohomology.Additivity.Basic
import TauCeti.AlgebraicTopology.Cohomology.Cup.Connecting
import TauCeti.AlgebraicTopology.Cohomology.DegreeZero
import TauCeti.AlgebraicTopology.Cohomology.GradedCommutativity
import TauCeti.AlgebraicTopology.Cohomology.Local.Basic
import TauCeti.AlgebraicTopology.Cohomology.ProdThomPair.Sphere
import TauCeti.AlgebraicTopology.Sphere.Zero
import TauCeti.Topology.Category.TopCat.Monoidal

/-!
# The Thom isomorphism for a product bundle

Let `B` be a topological space, `F` a finite-dimensional real normed space of rank
`r = finrank ℝ F`, `K` a commutative ring, and `M` a `K`-module. For a class
`u ∈ Hʳ(B × F, B × (F ∖ {0}); K)` of the Thom pair `TauCeti.prodThomPair B F` whose restriction
`u|_b ∈ Hʳ(F, F ∖ {0}; K)` along `TauCeti.prodThomPairFiberMap F b` generates `Hʳ(F, F ∖ {0}; K)`
for every `b ∈ B`, this file proves that the map

`Hᵖ(B; M) ⟶ Hᵐ(B × F, B × (F ∖ {0}); M)`,  `a ↦ π^* a ⌣ u`,  `p + r = m`,

(`TopPair.pullbackCup` along `TauCeti.prodThomPairProj B F`) is bijective in every degree `p`
(`TauCeti.bijective_pullbackCup_prodThomPair`), giving the `K`-linear equivalence
`TauCeti.prodThomPairPullbackCupEquiv`. This is the local model of the cohomological Thom
isomorphism, before gluing over trivializing open sets by Mayer–Vietoris.

## Proof outline

First we construct, for every finite rank `r`, one fibre class `g₀ ∈ Hʳ(F, F ∖ {0}; K)` whose
pullback `u₀ = pr₂^* g₀` along `TauCeti.prodThomPairSnd B F` has bijective `pullbackCup` for all
spaces `B`, all modules `M`, and all degrees `p`:

* **Rank `r = 0`**: `F` is a subsingleton, so `B × (F ∖ {0})` is empty, the map from relative to
  absolute cohomology is an isomorphism (`TopPair.isIso_singularCohomologyπ_of_isEmpty`), and the
  projection `B × F ⟶ B` is a homeomorphism. Taking `g₀` to lift the unit `0`-class of `F` makes
  `π^* a ⌣ u₀` correspond to `π^* a`.
* **Ranks `r ≥ 1`**: for a continuous linear equivalence `e : F ≃L[ℝ] ℝʳ`, the punctured product
  `B × (F ∖ {0})` is homotopy equivalent to `Sʳ⁻¹ × B`
  (`TauCeti.prodThomPairPuncturedHomotopyEquiv`). When `r = d + 2 ≥ 2`,
  `TauCeti.prodThomPairSingularCohomologySphereEquiv` already gives the bijection
  `c ↦ δ (σ ⌣ π₀^* c)`. When `r = 1`, `S⁰` consists of two discrete points, so additivity of
  singular cohomology (`TauCeti.isLimitFanSingularCohomology`) decomposes `Hᵖ(S⁰ × B; M)` as
  `(b, c) ↦ pr₂^* b + pr₁^* θ₀ ⌣ pr₂^* c`, and chasing the long exact sequence of the pair again
  shows `c ↦ δ (σ₀ ⌣ π₀^* c)` is bijective. In both cases, graded commutativity
  (`TopCat.singularCup_gradedComm`) and compatibility of the connecting morphism with cup products
  (`TopPair.singularCohomologyδ_singularCup`) rewrite `δ (σ ⌣ π₀^* c)` as
  `(-1)^(p r) (π^* c ⌣ δ σ)`, and naturality identifies `δ σ` with the pullback of the fibre class
  over a point.

Finally, for an arbitrary class `u` restricting to a generator on every fibre, surjectivity of
`pullbackCup` for `u₀` in degree `p = 0` with `M = K` writes `u = π^* γ ⌣ u₀` for some
`γ ∈ H⁰(B; K)`. Restricting to each fibre shows `u|_b = γ(b) • g₀`, so `γ(b)` is a unit of `K` at
every `b : B` (`LinearEquiv.span_singleton_eq_top_iff_isUnit` via
`TauCeti.singularCohomologyComplSingletonFinrankEquivSelf`), hence `γ` is a cup-product unit in
`H⁰(B; K)` (`TauCeti.exists_singularCup_eq_one`). By associativity of the relative cup product,
`π^* a ⌣ u = π^* (a ⌣ γ) ⌣ u₀`, which is a composite of two bijections.

## Main definitions and results

* `TauCeti.bijective_pullbackCup_prodThomPair`: `a ↦ π^* a ⌣ u` is bijective on `prodThomPair B F`
  whenever `u` generates on every fibre.
* `TauCeti.bijective_pullbackCup_prodThomPairSnd`: the specialization to `pr₂^* g` for a generator
  `g` of `Hʳ(F, F ∖ {0}; K)`.
* `TauCeti.prodThomPairPullbackCupEquiv`: the resulting `K`-linear equivalence
  `Hᵖ(B; M) ≃ₗ[K] Hᵐ(B × F, B × (F ∖ {0}); M)`.

## References

* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton (1974), §10, Theorem 10.4.
* A. Hatcher, *Algebraic Topology*, Section 4.D, Theorem 4D.10.
-/

public section

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory Module

universe w

namespace TauCeti

section ConnectingCup

/-- Multiplication by `(-1)^k` is an involution on any additive group, hence bijective. -/
private theorem bijective_neg_one_pow_zsmul_comp_iff {α β : Type*} [AddCommGroup β] (k : ℕ)
    (f : α → β) :
    (Function.Bijective fun a ↦ ((-1 : ℤ) ^ k) • f a) ↔ Function.Bijective f := by
  have hinv : Function.Bijective fun y : β ↦ ((-1 : ℤ) ^ k) • y :=
    Function.Involutive.bijective fun y ↦ by
      rw [smul_smul, ← mul_pow, neg_one_mul, neg_neg, one_pow, one_smul]
  exact hinv.of_comp_iff' f

/-- For a pair `P`, a map `g : P.fst ⟶ Z`, and `σ ∈ H^q(P.snd; K)`, the connecting morphism takes
`σ ⌣ (P.map ≫ g)^* c` to `(-1)^(p (q + 1))` times `P.pullbackCup` of `δ σ` at `c`. -/
private theorem singularCohomologyδ_singularCup_eq_zsmul_pullbackCup {K : Type w} [CommRing K]
    (M : ModuleCat.{w} K) (P : TopPair.{w}) {Z : TopCat.{w}} (g : P.fst ⟶ Z) {q q' p n m : ℕ}
    (h : p + q = n) (hq : q + 1 = q') (hm : n + 1 = m) (h' : p + q' = m)
    (σ : P.snd.singularCohomology (𝟙_ (ModuleCat.{w} K)) K (𝟙_ (ModuleCat.{w} K)) q)
    (c : Z.singularCohomology (𝟙_ (ModuleCat.{w} K)) K M p) :
    P.singularCohomologyδ (𝟙_ (ModuleCat.{w} K)) K M n m hm
        (P.snd.singularCup K (λ_ (𝟙_ (ModuleCat.{w} K))).inv (λ_ M).hom q p n (by omega) σ
          (TopCat.singularCohomologyMap (P.map ≫ g) p c)) =
      ((-1 : ℤ) ^ (p * q')) • P.pullbackCup M g q' p m h'
        (P.singularCohomologyδ (𝟙_ (ModuleCat.{w} K)) K (𝟙_ (ModuleCat.{w} K)) q q' hq σ) c := by
  subst hq
  have hu : (λ_ (𝟙_ (ModuleCat.{w} K))).inv ≫
      (β_ (𝟙_ (ModuleCat.{w} K)) (𝟙_ (ModuleCat.{w} K))).hom =
      (λ_ (𝟙_ (ModuleCat.{w} K))).inv := by
    rw [braiding_tensorUnit_left, Iso.inv_hom_id_assoc, unitors_inv_equal]
  have hμ : (β_ M (𝟙_ (ModuleCat.{w} K))).hom ≫ (λ_ M).hom = (ρ_ M).hom := by
    rw [braiding_tensorUnit_right, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [TopCat.singularCohomologyMap_comp, ConcreteCategory.comp_apply,
    P.snd.singularCup_gradedComm K hu hμ h, map_zsmul,
    P.singularCohomologyδ_singularCup K (λ_ (𝟙_ (ModuleCat.{w} K))).inv (ρ_ M).hom h rfl hm h',
    smul_smul, TopPair.pullbackCup_apply]
  have hexp : (-1 : ℤ) ^ (p * q) * (-1 : ℤ) ^ p = (-1 : ℤ) ^ (p * (q + 1)) := by
    rw [mul_add, mul_one, pow_add]
  rw [hexp]

/-- The constant map `B → PUnit` induces `prodThomPairSnd B F ≫ prodThomPairFiberMap F unit`. -/
private theorem prodThomPairMap_const_punit (B : Type w) [TopologicalSpace B] (F : Type w)
    [TopologicalSpace F] [Zero F] :
    prodThomPairMap F (ContinuousMap.const B (PUnit.unit : PUnit.{w + 1})) =
      prodThomPairSnd B F ≫ prodThomPairFiberMap F (PUnit.unit : PUnit.{w + 1}) :=
  TopPair.hom_ext_of_fst _ (TopCat.ext fun p ↦
    (prodThomPairMap_fst_apply F _ p).trans <|
      (prodThomPairFiberMap_fst_apply F _ (p.2)).symm.trans <|
        congrArg (TopPair.Hom.fst (prodThomPairFiberMap F _)) (prodThomPairSnd_fst_apply F p).symm)

end ConnectingCup

/-! ### Rank zero -/

section RankZero

variable {F : Type w} [TopologicalSpace F] [Zero F] [Subsingleton F]

/-- When `F` is a subsingleton, `F ∖ {0}` is empty. -/
private instance isEmpty_compl_zero_of_subsingleton :
    IsEmpty (TopPair.ofSubset ({0}ᶜ : Set (TopCat.of F))).snd :=
  ⟨fun x ↦ x.2 (Subsingleton.elim x.1 0)⟩

/-- When `F` is a subsingleton, `B × (F ∖ {0})` is empty. -/
private instance isEmpty_prodThomPair_snd (B : Type w) [TopologicalSpace B] :
    IsEmpty (prodThomPair B F).snd :=
  ⟨fun p ↦ p.2 (Subsingleton.elim p.1.2 0)⟩

variable {K : Type w} [CommRing K]

/-- In rank zero, the fibre class lifting the unit `0`-class of `F` across `H⁰(F, ∅) ≅ H⁰(F)`. -/
private def rankZeroFiberClass :
    (TopPair.ofSubset ({0}ᶜ : Set (TopCat.of F))).singularCohomology
      (ModuleCat.of K K) K (ModuleCat.of K K) 0 :=
  inv ((TopPair.ofSubset ({0}ᶜ : Set (TopCat.of F))).singularCohomologyπ
    (𝟙_ (ModuleCat.{w} K)) K (𝟙_ (ModuleCat.{w} K)) 0)
    ((TopPair.ofSubset ({0}ᶜ : Set (TopCat.of F))).fst.singularCohomologyZeroOne (k := K))

/-- In rank zero, `pullbackCup` with the pullback of `rankZeroFiberClass` is bijective. -/
private theorem bijective_pullbackCup_rankZero (B : Type w) [TopologicalSpace B]
    (M : ModuleCat.{w} K) {p m : ℕ} (h : p + 0 = m) :
    Function.Bijective ((prodThomPair B F).pullbackCup M (prodThomPairProj B F) 0 p m h
      (TopPair.singularCohomologyMap (prodThomPairSnd B F) 0 (rankZeroFiberClass (K := K)))) := by
  subst h
  let P := prodThomPair B F
  let : Unique F := ⟨⟨0⟩, fun x ↦ Subsingleton.elim x 0⟩
  -- `prodThomPairProj B F` is the first projection of `B × F ≃ₜ B`, hence an isomorphism.
  have hproj : prodThomPairProj B F = (TopCat.isoOfHomeo (Homeomorph.prodUnique B F)).hom :=
    TopCat.ext fun x ↦ prodThomPairProj_apply F x
  have : IsIso (prodThomPairProj B F) := hproj ▸ inferInstance
  let u₀ : P.singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) 0 :=
    TopPair.singularCohomologyMap (prodThomPairSnd B F) 0 (rankZeroFiberClass (K := K))
  -- The image of `u₀ = pr₂^* g₀` in `H⁰(B × F; K)` is the unit `0`-class.
  have huπ : P.singularCohomologyπ (𝟙_ (ModuleCat.{w} K)) K (𝟙_ (ModuleCat.{w} K)) 0 u₀ =
      P.fst.singularCohomologyZeroOne := by
    have hπ0 : (TopPair.ofSubset ({0}ᶜ : Set (TopCat.of F))).singularCohomologyπ
        (𝟙_ (ModuleCat.{w} K)) K (𝟙_ (ModuleCat.{w} K)) 0 (rankZeroFiberClass (K := K)) =
        (TopPair.ofSubset ({0}ᶜ : Set (TopCat.of F))).fst.singularCohomologyZeroOne := by
      rw [rankZeroFiberClass, ← ConcreteCategory.comp_apply, IsIso.inv_hom_id,
        ConcreteCategory.id_apply]
    have hnat := ConcreteCategory.congr_hom (TopPair.singularCohomologyπ_naturality
      (R := 𝟙_ (ModuleCat.{w} K)) (k := K) (M := 𝟙_ (ModuleCat.{w} K))
      (prodThomPairSnd B F) 0) (rankZeroFiberClass (K := K))
    simp only [ConcreteCategory.comp_apply] at hnat
    exact hnat.symm.trans ((congrArg _ hπ0).trans
      (singularCohomologyMap_singularCohomologyZeroOne _))
  -- Applying `singularCohomologyπ` turns `pullbackCup` into `(prodThomPairProj B F)^*`.
  have hcomp : ⇑(P.singularCohomologyπ (𝟙_ (ModuleCat.{w} K)) K M p) ∘
      ⇑(P.pullbackCup M (prodThomPairProj B F) 0 p (p + 0) rfl u₀) =
      TopCat.singularCohomologyMap (R := 𝟙_ (ModuleCat.{w} K)) (k := K) (M := M)
        (prodThomPairProj B F) p := by
    funext a
    simp only [Function.comp_apply, TopPair.pullbackCup_apply]
    refine (P.singularCohomologyπ_singularCup K (λ_ (𝟙_ (ModuleCat.{w} K))).inv (ρ_ M).hom
      p 0 p (Nat.add_zero p) (TopCat.singularCohomologyMap (prodThomPairProj B F) p a) u₀).trans ?_
    rw [huπ, TopCat.singularCohomologyZeroOne_def]
    exact P.fst.singularCup_constSingularCocycle_right K (η := 𝟙 _)
      (by monoidal) (by monoidal) (Nat.add_zero p) _
  have hπbij : Function.Bijective (P.singularCohomologyπ (𝟙_ (ModuleCat.{w} K)) K M p) :=
    (asIso (P.singularCohomologyπ (𝟙_ (ModuleCat.{w} K)) K M p)).toLinearEquiv.bijective
  have hprojBij : Function.Bijective (TopCat.singularCohomologyMap
      (R := 𝟙_ (ModuleCat.{w} K)) (k := K) (M := M) (prodThomPairProj B F) p) :=
    ((singularCohomologyFunctor (𝟙_ (ModuleCat.{w} K)) K M p).mapIso
      (asIso (prodThomPairProj B F)).op).toLinearEquiv.bijective
  exact (hπbij.of_comp_iff' _).1 (hcomp ▸ hprojBij)

end RankZero

/-! ### Rank one: `S⁰ × Y` and the punctured line bundle -/

section SphereZero

/-- The positive pole `+e₀` of `TopCat.sphere 0`. -/
private def sphereZeroPos : TopCat.sphere.{w} 0 :=
  ⟨⟨EuclideanSpace.single 0 1, by simp⟩⟩

/-- The negative pole `-e₀` of `TopCat.sphere 0`. -/
private def sphereZeroNeg : TopCat.sphere.{w} 0 :=
  ⟨⟨-EuclideanSpace.single 0 1, by simp⟩⟩

private theorem sphereZeroPos_ne_sphereZeroNeg :
    (sphereZeroPos : TopCat.sphere.{w} 0) ≠ sphereZeroNeg := by
  intro h
  have h0 := congrFun (congrArg (fun s : TopCat.sphere.{w} 0 ↦ (s.down : Fin 1 → ℝ)) h) 0
  simp [sphereZeroPos, sphereZeroNeg] at h0
  linarith

private theorem eq_sphereZeroPos_or_neg (s : TopCat.sphere.{w} 0) :
    s = sphereZeroPos ∨ s = sphereZeroNeg := by
  have hp : EuclideanSpace.single (0 : Fin 1) (1 : ℝ) ∈
      Metric.sphere (0 : EuclideanSpace ℝ (Fin 1)) 1 := by simp
  have hs : (s.down : EuclideanSpace ℝ (Fin 1)) ∈
      ({EuclideanSpace.single 0 1, -EuclideanSpace.single 0 1} : Set _) := by
    rw [← sphere_eq_pair_of_finrank_eq_one (by simp) hp]
    exact s.down.2
  rcases hs with hs | hs
  · exact Or.inl (ULift.ext (Subtype.ext hs))
  · exact Or.inr (ULift.ext (Subtype.ext hs))

private instance discreteTopology_sphereZero : DiscreteTopology (TopCat.sphere.{w} 0) := by
  have : DiscreteTopology (Metric.sphere (0 : EuclideanSpace ℝ (Fin 1)) 1) :=
    discreteTopology_sphere_of_finrank_eq_one (by simp) 0 1
  -- `TopCat.sphere 0` has carrier `ULift` of the metric `0`-sphere.
  change DiscreteTopology (ULift.{w} (Metric.sphere (0 : EuclideanSpace ℝ (Fin 1)) 1))
  exact Homeomorph.ulift.symm.discreteTopology

private theorem eq_of_joined_sphereZero {x y : TopCat.sphere.{w} 0} (hxy : Joined x y) : x = y :=
  ZerothHomotopy.mk_injective_of_totallyDisconnectedSpace (Quotient.sound hxy)

/-- Homeomorphism between `(Σ _ : ULift Bool, Y)` and `S⁰ × Y`, identifying the two summands with
the slices at `sphereZeroPos` and `sphereZeroNeg`. -/
private def sigmaBoolHomeomorphSphereZeroProd (Y : TopCat.{w}) :
    (Σ _ : ULift.{w} Bool, Y) ≃ₜ ↑(TopCat.sphere.{w} 0 ⊗ Y : TopCat.{w}) where
  toFun p := (if p.1.down then sphereZeroPos else sphereZeroNeg, p.2)
  invFun q := by
    -- Decidable equality on `TopCat.sphere 0` selects the `Bool` summand.
    classical
    exact ⟨⟨decide (q.1 = sphereZeroPos)⟩, q.2⟩
  left_inv := by
    rintro ⟨⟨b⟩, y⟩
    cases b <;> simp [sphereZeroPos_ne_sphereZeroNeg.symm]
  right_inv q := by
    refine Prod.ext ?_ rfl
    rcases eq_sphereZeroPos_or_neg q.1 with h | h <;>
      simp [h, sphereZeroPos_ne_sphereZeroNeg.symm]
  continuous_toFun := continuous_sigma fun ⟨b⟩ ↦ by
    cases b <;> exact continuous_const.prodMk continuous_id
  continuous_invFun := by
    -- Match the `classical` decidable instance used in `invFun`.
    classical
    have hd : Continuous fun q : ↑(TopCat.sphere.{w} 0 ⊗ Y : TopCat.{w}) ↦
        (⟨decide (q.1 = sphereZeroPos)⟩ : ULift.{w} Bool) :=
      (continuous_of_discreteTopology (f := fun s : TopCat.sphere.{w} 0 ↦
        (⟨decide (s = sphereZeroPos)⟩ : ULift.{w} Bool))).comp continuous_fst
    have hsigma : Continuous fun p : ULift.{w} Bool × Y ↦
        (⟨p.1, p.2⟩ : Σ _ : ULift.{w} Bool, Y) := by
      have : DiscreteTopology (ULift.{w} Bool) := Homeomorph.ulift.symm.discreteTopology
      rw [continuous_prod_of_discrete_left]
      exact fun _ ↦ continuous_sigmaMk (σ := fun _ : ULift.{w} Bool ↦ Y)
    exact hsigma.comp (hd.prodMk continuous_snd)

variable {K : Type w} [CommRing K]

private theorem exists_sphereZeroGenerator :
    ∃ θ : (TopCat.sphere.{w} 0).singularCohomology
        (𝟙_ (ModuleCat.{w} K)) K (𝟙_ (ModuleCat.{w} K)) 0,
      singularCohomologyZeroEval sphereZeroPos θ = 1 ∧
        singularCohomologyZeroEval sphereZeroNeg θ = 0 := by
  -- Decidable equality on `TopCat.sphere 0` defines the `{0, 1}`-valued indicator function.
  classical
  obtain ⟨θ, hθ⟩ := exists_singularCohomologyZeroEval_eq (k := K) (X := TopCat.sphere.{w} 0)
    (fun s ↦ if s = sphereZeroPos then 1 else 0) fun x y hxy ↦ by
      rw [eq_of_joined_sphereZero hxy]
  exact ⟨θ, by simpa using hθ sphereZeroPos,
    by simpa [sphereZeroPos_ne_sphereZeroNeg.symm] using hθ sphereZeroNeg⟩

/-- The `0`-cohomology class on `S⁰` taking value `1` at `sphereZeroPos` and `0` at
`sphereZeroNeg`. -/
private def sphereZeroGenerator :
    (TopCat.sphere.{w} 0).singularCohomology
      (𝟙_ (ModuleCat.{w} K)) K (𝟙_ (ModuleCat.{w} K)) 0 :=
  (exists_sphereZeroGenerator (K := K)).choose

private theorem singularCohomologyZeroEval_sphereZeroGenerator_pos :
    singularCohomologyZeroEval sphereZeroPos (sphereZeroGenerator (K := K)) = 1 :=
  (exists_sphereZeroGenerator (K := K)).choose_spec.1

private theorem singularCohomologyZeroEval_sphereZeroGenerator_neg :
    singularCohomologyZeroEval sphereZeroNeg (sphereZeroGenerator (K := K)) = 0 :=
  (exists_sphereZeroGenerator (K := K)).choose_spec.2

/-- A class on `S⁰ × Y` vanishing on both slices `sphereZeroPos` and `sphereZeroNeg` is zero. -/
private theorem eq_zero_of_prodFiberInclusion_sphereZero_eq_zero (M : ModuleCat.{w} K)
    (Y : TopCat.{w}) {n : ℕ}
    (φ : (TopCat.sphere.{w} 0 ⊗ Y).singularCohomology (𝟙_ (ModuleCat.{w} K)) K M n)
    (hpos : TopCat.singularCohomologyMap
      (TopCat.prodFiberInclusion (TopCat.sphere.{w} 0) Y sphereZeroPos) n φ = 0)
    (hneg : TopCat.singularCohomologyMap
      (TopCat.prodFiberInclusion (TopCat.sphere.{w} 0) Y sphereZeroNeg) n φ = 0) :
    φ = 0 := by
  let e : TopCat.of (Σ _ : ULift.{w} Bool, Y) ≅ TopCat.sphere.{w} 0 ⊗ Y :=
    TopCat.isoOfHomeo (sigmaBoolHomeomorphSphereZeroProd Y)
  have hlim := isLimitFanSingularCohomology (fun _ : ULift.{w} Bool ↦ Y) (ModuleCat.{w} K)
    (𝟙_ (ModuleCat.{w} K)) K M n
  have hι (b : ULift.{w} Bool) :
      TopCat.sigmaι (fun _ : ULift.{w} Bool ↦ Y) b ≫ e.hom =
        TopCat.prodFiberInclusion (TopCat.sphere.{w} 0) Y
          (if b.down then sphereZeroPos else sphereZeroNeg) :=
    TopCat.ext fun x ↦ (TopCat.prodFiberInclusion_apply _ _ _ x).symm
  let N := (TopCat.of (Σ _ : ULift.{w} Bool, Y)).singularCohomology (𝟙_ (ModuleCat.{w} K)) K M n
  let x : N := TopCat.singularCohomologyMap e.hom n φ
  let f : ModuleCat.of K K ⟶ N := ConcreteCategory.ofHom (LinearMap.toSpanSingleton K N x)
  have hf0 : f = 0 := Fan.IsLimit.hom_ext hlim _ _ fun b ↦ by
    refine ModuleCat.hom_ext (LinearMap.ext fun r ↦ ?_)
    simp only [fan_mk_proj, ModuleCat.hom_comp, LinearMap.comp_apply, f,
      ConcreteCategory.hom_ofHom, LinearMap.toSpanSingleton_apply, map_smul, ModuleCat.hom_zero,
      LinearMap.zero_apply]
    rw [← ConcreteCategory.comp_apply, ← TopCat.singularCohomologyMap_comp, hι b]
    rcases b with ⟨_ | _⟩
    · simp [hneg]
    · simp [hpos]
  have hx : x = 0 := by
    have h1 := congrArg (fun g : ModuleCat.of K K ⟶ N ↦ g.hom (1 : K)) hf0
    simpa [f] using h1
  exact ((singularCohomologyFunctor (𝟙_ (ModuleCat.{w} K)) K M n).mapIso
    e.op).toLinearEquiv.injective (hx.trans (map_zero _).symm)

private theorem prodFiberInclusion_sphereZero_add_cup (M : ModuleCat.{w} K) (Y : TopCat.{w}) (n : ℕ)
    (s : TopCat.sphere.{w} 0)
    (bc : Y.singularCohomology (𝟙_ (ModuleCat.{w} K)) K M n ×
      Y.singularCohomology (𝟙_ (ModuleCat.{w} K)) K M n) :
    TopCat.singularCohomologyMap (TopCat.prodFiberInclusion (TopCat.sphere.{w} 0) Y s) n
        (TopCat.singularCohomologyMap (snd _ Y) n bc.1 +
          (TopCat.sphere.{w} 0 ⊗ Y).singularCup K (λ_ (𝟙_ (ModuleCat.{w} K))).inv (λ_ M).hom
            0 n n (Nat.zero_add n)
            (TopCat.singularCohomologyMap (fst _ Y) 0 (sphereZeroGenerator (K := K)))
            (TopCat.singularCohomologyMap (snd _ Y) n bc.2)) =
      bc.1 + (singularCohomologyZeroEval s (sphereZeroGenerator (K := K))) • bc.2 := by
  simp only [map_add, ← TopCat.singularCup_naturality, ← ConcreteCategory.comp_apply,
    ← TopCat.singularCohomologyMap_comp, TopCat.prodFiberInclusion_snd,
    TopCat.prodFiberInclusion_fst, TopCat.singularCohomologyMap_id, ConcreteCategory.id_apply,
    singularCohomologyMap_const_eq_singularCohomologyZeroEval_smul, map_smul,
    LinearMap.smul_apply, TopCat.singularCohomologyZeroOne_def]
  rw [Y.singularCup_constSingularCocycle_left K (η := 𝟙 _)
    (by monoidal) (by monoidal) (Nat.zero_add n)]

/-- Decomposition `Hⁿ(Y; M) × Hⁿ(Y; M) ≃ₗ[K] Hⁿ(S⁰ × Y; M)`,
`(b, c) ↦ pr₂^* b + pr₁^* θ₀ ⌣ pr₂^* c`. -/
private def sphereZeroProdEquiv (M : ModuleCat.{w} K) (Y : TopCat.{w}) (n : ℕ) :
    (Y.singularCohomology (𝟙_ (ModuleCat.{w} K)) K M n ×
      Y.singularCohomology (𝟙_ (ModuleCat.{w} K)) K M n) ≃ₗ[K]
      (TopCat.sphere.{w} 0 ⊗ Y).singularCohomology (𝟙_ (ModuleCat.{w} K)) K M n where
  toFun bc :=
    TopCat.singularCohomologyMap (snd _ Y) n bc.1 +
      (TopCat.sphere.{w} 0 ⊗ Y).singularCup K (λ_ (𝟙_ (ModuleCat.{w} K))).inv (λ_ M).hom
        0 n n (Nat.zero_add n)
        (TopCat.singularCohomologyMap (fst _ Y) 0 (sphereZeroGenerator (K := K)))
        (TopCat.singularCohomologyMap (snd _ Y) n bc.2)
  map_add' x y := by
    simp only [Prod.fst_add, Prod.snd_add, map_add]
    abel
  map_smul' r x := by
    simp only [Prod.smul_fst, Prod.smul_snd, map_smul, RingHom.id_apply, smul_add]
  invFun φ :=
    (TopCat.singularCohomologyMap
        (TopCat.prodFiberInclusion (TopCat.sphere.{w} 0) Y sphereZeroNeg) n φ,
      TopCat.singularCohomologyMap
        (TopCat.prodFiberInclusion (TopCat.sphere.{w} 0) Y sphereZeroPos) n φ -
        TopCat.singularCohomologyMap
          (TopCat.prodFiberInclusion (TopCat.sphere.{w} 0) Y sphereZeroNeg) n φ)
  left_inv bc := by
    ext
    · simp only [prodFiberInclusion_sphereZero_add_cup,
        singularCohomologyZeroEval_sphereZeroGenerator_neg, zero_smul, add_zero]
    · simp only [prodFiberInclusion_sphereZero_add_cup,
        singularCohomologyZeroEval_sphereZeroGenerator_pos,
        singularCohomologyZeroEval_sphereZeroGenerator_neg, one_smul, zero_smul, add_zero,
        add_sub_cancel_left]
  right_inv φ := by
    rw [← sub_eq_zero]
    refine eq_zero_of_prodFiberInclusion_sphereZero_eq_zero M Y _ ?_ ?_
    · rw [map_sub, prodFiberInclusion_sphereZero_add_cup,
        singularCohomologyZeroEval_sphereZeroGenerator_pos, one_smul, add_sub_cancel, sub_self]
    · rw [map_sub, prodFiberInclusion_sphereZero_add_cup,
        singularCohomologyZeroEval_sphereZeroGenerator_neg, zero_smul, add_zero, sub_self]

@[simp]
private theorem sphereZeroProdEquiv_apply (M : ModuleCat.{w} K) (Y : TopCat.{w}) (n : ℕ)
    (bc : Y.singularCohomology (𝟙_ (ModuleCat.{w} K)) K M n ×
      Y.singularCohomology (𝟙_ (ModuleCat.{w} K)) K M n) :
    sphereZeroProdEquiv M Y n bc =
      TopCat.singularCohomologyMap (snd _ Y) n bc.1 +
        (TopCat.sphere.{w} 0 ⊗ Y).singularCup K (λ_ (𝟙_ (ModuleCat.{w} K))).inv (λ_ M).hom
          0 n n (Nat.zero_add n)
          (TopCat.singularCohomologyMap (fst _ Y) 0 (sphereZeroGenerator (K := K)))
          (TopCat.singularCohomologyMap (snd _ Y) n bc.2) :=
  (rfl)

end SphereZero

private instance isIso_singularCohomologyMap_prodThomPairProj {K : Type w} [CommRing K]
    (M : ModuleCat.{w} K) (B : Type w) [TopologicalSpace B] {F : Type w} [TopologicalSpace F]
    [Zero F] [ContractibleSpace F] (m : ℕ) :
    IsIso (TopCat.singularCohomologyMap (R := 𝟙_ (ModuleCat.{w} K)) (k := K) (M := M)
      (prodThomPairProj B F) m) := by
  have hproj : prodThomPairProj B F = TopCat.ofHom ContinuousMap.fst :=
    TopCat.ext fun p ↦ prodThomPairProj_apply F p
  rw [hproj, ← ContinuousMap.HomotopyEquiv.prodContractible_toFun (X := B) (Y := F)]
  exact (ContinuousMap.HomotopyEquiv.prodContractible B F).isIso_singularCohomologyMap _ K M m

section RankOne

variable {K : Type w} [CommRing K] {F : Type w} [TopologicalSpace F] [AddCommMonoid F]
  [Module ℝ F]

/-- The homotopy equivalence `(prodThomPair B F).snd ≃ₕ S⁰ × B` as a morphism in `TopCat`. -/
private abbrev sphereZeroProdMap (B : Type w) [TopologicalSpace B]
    (e : F ≃L[ℝ] EuclideanSpace ℝ (Fin 1)) :
    (prodThomPair B F).snd ⟶ TopCat.sphere.{w} 0 ⊗ TopCat.of B :=
  TopCat.ofHom (prodThomPairPuncturedHomotopyEquiv B e).toFun

/-- The `0`-class `σ₀` on `B × (F ∖ {0})` pulled back from `sphereZeroGenerator` on `S⁰`. -/
private def rankOnePuncturedClass (B : Type w) [TopologicalSpace B]
    (e : F ≃L[ℝ] EuclideanSpace ℝ (Fin 1)) :
    (prodThomPair B F).snd.singularCohomology
      (𝟙_ (ModuleCat.{w} K)) K (𝟙_ (ModuleCat.{w} K)) 0 :=
  TopCat.singularCohomologyMap (sphereZeroProdMap B e ≫ fst _ _) 0 (sphereZeroGenerator (K := K))

/-- `rankOnePuncturedClass` is natural in the base `B`. -/
private theorem singularCohomologyMap_snd_prodThomPairMap_rankOnePuncturedClass
    {B B' : Type w} [TopologicalSpace B] [TopologicalSpace B'] (g : C(B, B'))
    (e : F ≃L[ℝ] EuclideanSpace ℝ (Fin 1)) :
    TopCat.singularCohomologyMap (TopPair.Hom.snd (prodThomPairMap F g)) 0
        (rankOnePuncturedClass (K := K) B' e) = rankOnePuncturedClass B e := by
  have h : TopPair.Hom.snd (prodThomPairMap F g) ≫ sphereZeroProdMap B' e ≫ fst _ _ =
      sphereZeroProdMap B e ≫ fst _ _ := by
    ext p
    apply ULift.ext
    apply Subtype.ext
    refine ((coe_prodThomPairPuncturedHomotopyEquiv_apply_fst e _).trans ?_).trans
      (coe_prodThomPairPuncturedHomotopyEquiv_apply_fst e p).symm
    exact congrArg (fun x : F ↦ ‖e x‖⁻¹ • e x)
      (congrArg Prod.snd (prodThomPairMap_snd_apply F g p))
  rw [rankOnePuncturedClass, rankOnePuncturedClass, ← ConcreteCategory.comp_apply,
    ← TopCat.singularCohomologyMap_comp, h]

/-- Decomposition `Hⁿ(B; M) × Hⁿ(B; M) ≃ₗ[K] Hⁿ(B × (F ∖ {0}); M)` in rank one. -/
private def rankOnePuncturedEquiv (M : ModuleCat.{w} K) (B : Type w) [TopologicalSpace B]
    (e : F ≃L[ℝ] EuclideanSpace ℝ (Fin 1)) (n : ℕ) :
    ((TopCat.of B).singularCohomology (𝟙_ (ModuleCat.{w} K)) K M n ×
      (TopCat.of B).singularCohomology (𝟙_ (ModuleCat.{w} K)) K M n) ≃ₗ[K]
      (prodThomPair B F).snd.singularCohomology (𝟙_ (ModuleCat.{w} K)) K M n :=
  haveI : IsIso (TopCat.singularCohomologyMap (R := 𝟙_ (ModuleCat.{w} K)) (k := K) (M := M)
      (sphereZeroProdMap B e) n) :=
    (prodThomPairPuncturedHomotopyEquiv B e).isIso_singularCohomologyMap _ K M n
  (sphereZeroProdEquiv M (TopCat.of B) n).trans
    (asIso (TopCat.singularCohomologyMap (sphereZeroProdMap B e) n)).toLinearEquiv

private theorem rankOnePuncturedEquiv_apply (M : ModuleCat.{w} K) (B : Type w) [TopologicalSpace B]
    (e : F ≃L[ℝ] EuclideanSpace ℝ (Fin 1)) (n : ℕ)
    (bc : (TopCat.of B).singularCohomology (𝟙_ (ModuleCat.{w} K)) K M n ×
      (TopCat.of B).singularCohomology (𝟙_ (ModuleCat.{w} K)) K M n) :
    rankOnePuncturedEquiv M B e n bc =
      TopCat.singularCohomologyMap (prodThomPairPuncturedProj B F) n bc.1 +
        (prodThomPair B F).snd.singularCup K (λ_ (𝟙_ (ModuleCat.{w} K))).inv (λ_ M).hom
          0 n n (Nat.zero_add n) (rankOnePuncturedClass B e)
          (TopCat.singularCohomologyMap (prodThomPairPuncturedProj B F) n bc.2) := by
  have hsnd : sphereZeroProdMap B e ≫ snd _ _ = prodThomPairPuncturedProj B F :=
    TopCat.ext fun p ↦ (prodThomPairPuncturedHomotopyEquiv_apply_snd e p).trans
      (prodThomPairPuncturedProj_apply F p).symm
  rw [← hsnd]
  simp only [rankOnePuncturedEquiv, LinearEquiv.trans_apply, sphereZeroProdEquiv_apply,
    Iso.toLinearEquiv_apply, map_add, rankOnePuncturedClass, TopCat.singularCohomologyMap_comp,
    ConcreteCategory.comp_apply, TopCat.singularCup_naturality]
  rfl

private theorem rankOnePuncturedEquiv_fst_zero (M : ModuleCat.{w} K) (B : Type w)
    [TopologicalSpace B] (e : F ≃L[ℝ] EuclideanSpace ℝ (Fin 1)) (n : ℕ)
    (b : (TopCat.of B).singularCohomology (𝟙_ (ModuleCat.{w} K)) K M n) :
    rankOnePuncturedEquiv M B e n (b, 0) =
      TopCat.singularCohomologyMap (prodThomPair B F).map n
        (TopCat.singularCohomologyMap (prodThomPairProj B F) n b) := by
  rw [rankOnePuncturedEquiv_apply, map_zero, map_zero, add_zero, ← ConcreteCategory.comp_apply,
    ← TopCat.singularCohomologyMap_comp, map_comp_prodThomPairProj]

private theorem injective_prodThomPairPuncturedProj_rankOne (M : ModuleCat.{w} K) (B : Type w)
    [TopologicalSpace B] (e : F ≃L[ℝ] EuclideanSpace ℝ (Fin 1)) (m : ℕ) :
    Function.Injective (TopCat.singularCohomologyMap (R := 𝟙_ (ModuleCat.{w} K)) (k := K)
      (M := M) (prodThomPairPuncturedProj B F) m) := by
  let v : F := e.symm (EuclideanSpace.single 0 1)
  have hv : v ≠ 0 := by simp [v]
  let s : TopCat.of B ⟶ (prodThomPair B F).snd :=
    TopCat.ofHom ⟨fun b ↦ ⟨(b, v), hv⟩, by fun_prop⟩
  have hs : s ≫ prodThomPairPuncturedProj B F = 𝟙 _ :=
    TopCat.ext fun b ↦ prodThomPairPuncturedProj_apply F (s b)
  refine Function.LeftInverse.injective (g := TopCat.singularCohomologyMap s m) fun b ↦ ?_
  rw [← ConcreteCategory.comp_apply, ← TopCat.singularCohomologyMap_comp, hs,
    TopCat.singularCohomologyMap_id, ConcreteCategory.id_apply]

/-- In rank one, `singularCohomologyπ : Hᵐ(B × F, B × (F ∖ {0}); M) → Hᵐ(B × F; M)` is zero
because the punctured projection `B × (F ∖ {0}) → B` admits a continuous section. -/
private theorem singularCohomologyπ_eq_zero_rankOne (M : ModuleCat.{w} K) (B : Type w)
    [TopologicalSpace B] (e : F ≃L[ℝ] EuclideanSpace ℝ (Fin 1)) (m : ℕ)
    (z : (prodThomPair B F).singularCohomology (𝟙_ (ModuleCat.{w} K)) K M m) :
    (prodThomPair B F).singularCohomologyπ (𝟙_ (ModuleCat.{w} K)) K M m z = 0 := by
  have := e.toHomeomorph.contractibleSpace
  let P := prodThomPair B F
  obtain ⟨b, hb⟩ :=
    ((ConcreteCategory.isIso_iff_bijective
      (TopCat.singularCohomologyMap (R := 𝟙_ (ModuleCat.{w} K)) (k := K) (M := M)
        (prodThomPairProj B F) m)).1 inferInstance).2
      (P.singularCohomologyπ (𝟙_ (ModuleCat.{w} K)) K M m z)
  have h0 := ConcreteCategory.congr_hom
    (P.singularCohomologyπ_comp_singularCohomologyMap (𝟙_ (ModuleCat.{w} K)) K M m) z
  rw [ConcreteCategory.comp_apply, ← hb, ← ConcreteCategory.comp_apply,
    ← TopCat.singularCohomologyMap_comp, map_comp_prodThomPairProj] at h0
  simp only [ModuleCat.hom_zero, LinearMap.zero_apply] at h0
  rw [← hb, injective_prodThomPairPuncturedProj_rankOne M B e m (h0.trans (map_zero _).symm),
    map_zero]

/-- In rank one, `c ↦ δ (σ₀ ⌣ π₀^* c)` is bijective `Hⁿ(B; M) → Hᵐ(B × F, B × (F ∖ {0}); M)` for
`n + 1 = m`. -/
private theorem bijective_rankOneDelta (M : ModuleCat.{w} K) (B : Type w) [TopologicalSpace B]
    (e : F ≃L[ℝ] EuclideanSpace ℝ (Fin 1)) {n m : ℕ} (h : n + 1 = m) :
    Function.Bijective (fun c : (TopCat.of B).singularCohomology (𝟙_ (ModuleCat.{w} K)) K M n ↦
      (prodThomPair B F).singularCohomologyδ (𝟙_ (ModuleCat.{w} K)) K M n m h
        ((prodThomPair B F).snd.singularCup K (λ_ (𝟙_ (ModuleCat.{w} K))).inv (λ_ M).hom
          0 n n (Nat.zero_add n) (rankOnePuncturedClass B e)
          (TopCat.singularCohomologyMap (prodThomPairPuncturedProj B F) n c))) := by
  have := e.toHomeomorph.contractibleSpace
  let P := prodThomPair B F
  let D := rankOnePuncturedEquiv M B e n
  let f : (TopCat.of B).singularCohomology (𝟙_ (ModuleCat.{w} K)) K M n →ₗ[K]
      P.singularCohomology (𝟙_ (ModuleCat.{w} K)) K M m :=
    (P.singularCohomologyδ (𝟙_ (ModuleCat.{w} K)) K M n m h).hom ∘ₗ
      D.toLinearMap ∘ₗ LinearMap.inr K _ _
  have hfeq : (fun c : (TopCat.of B).singularCohomology (𝟙_ (ModuleCat.{w} K)) K M n ↦
      P.singularCohomologyδ (𝟙_ (ModuleCat.{w} K)) K M n m h
        (P.snd.singularCup K (λ_ (𝟙_ (ModuleCat.{w} K))).inv (λ_ M).hom 0 n n (Nat.zero_add n)
          (rankOnePuncturedClass B e)
          (TopCat.singularCohomologyMap (prodThomPairPuncturedProj B F) n c))) = ⇑f := by
    ext c
    simp only [f, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearMap.inr_apply, D,
      rankOnePuncturedEquiv_apply, map_zero, zero_add]
    rfl
  rw [hfeq]
  refine ⟨(injective_iff_map_eq_zero f).2 fun c hc ↦ ?_, fun z ↦ ?_⟩
  · obtain ⟨y, hy⟩ := (ShortComplex.moduleCat_exact_iff _).1
      (P.singularCohomology_exact_subspace (𝟙_ (ModuleCat.{w} K)) K M n m h) (D (0, c)) hc
    obtain ⟨b, rfl⟩ :=
      ((ConcreteCategory.isIso_iff_bijective
        (TopCat.singularCohomologyMap (R := 𝟙_ (ModuleCat.{w} K)) (k := K) (M := M)
          (prodThomPairProj B F) n)).1 inferInstance).2 y
    have hy' : D (b, 0) = D (0, c) := (rankOnePuncturedEquiv_fst_zero M B e n b).trans hy
    exact congrArg Prod.snd (D.injective hy').symm
  · obtain ⟨x, rfl⟩ := (ShortComplex.moduleCat_exact_iff _).1
      (P.singularCohomology_exact_relative (𝟙_ (ModuleCat.{w} K)) K M n m h) z
      (singularCohomologyπ_eq_zero_rankOne M B e m z)
    obtain ⟨⟨b', c⟩, rfl⟩ := D.surjective x
    have hδ0 : P.singularCohomologyδ (𝟙_ (ModuleCat.{w} K)) K M n m h (D (b', 0)) = 0 := by
      rw [rankOnePuncturedEquiv_fst_zero M B e n b', ← ConcreteCategory.comp_apply,
        P.singularCohomologyMap_comp_singularCohomologyδ (𝟙_ (ModuleCat.{w} K)) K M n m h]
      simp only [ModuleCat.hom_zero, LinearMap.zero_apply]
    have hbc : ((b', c) : _ × _) = (b', 0) + (0, c) := by simp
    refine ⟨c, ?_⟩
    -- Unfold `f c` to `δ (D (0, c))` so `D (b', c) = D (b', 0) + D (0, c)` cancels `D (b', 0)`.
    change P.singularCohomologyδ (𝟙_ (ModuleCat.{w} K)) K M n m h (D (0, c)) =
      P.singularCohomologyδ (𝟙_ (ModuleCat.{w} K)) K M n m h (D (b', c))
    rw [hbc, map_add, map_add, hδ0, zero_add]

/-- The model fibre class in rank one: `δ σ₀` over a point, restricted to `(F, F ∖ {0})`. -/
private def rankOneFiberClass (e : F ≃L[ℝ] EuclideanSpace ℝ (Fin 1)) :
    (TopPair.ofSubset ({0}ᶜ : Set (TopCat.of F))).singularCohomology
      (ModuleCat.of K K) K (ModuleCat.of K K) 1 :=
  TopPair.singularCohomologyMap (prodThomPairFiberMap F (PUnit.unit : PUnit.{w + 1})) 1
    ((prodThomPair PUnit.{w + 1} F).singularCohomologyδ
      (𝟙_ (ModuleCat.{w} K)) K (𝟙_ (ModuleCat.{w} K)) 0 1 rfl
      (rankOnePuncturedClass PUnit.{w + 1} e))

/-- In rank one, `pullbackCup` with the pullback of `rankOneFiberClass` is bijective. -/
private theorem bijective_pullbackCup_rankOne (B : Type w) [TopologicalSpace B]
    (e : F ≃L[ℝ] EuclideanSpace ℝ (Fin 1)) (M : ModuleCat.{w} K) {p m : ℕ} (h : p + 1 = m) :
    Function.Bijective ((prodThomPair B F).pullbackCup M (prodThomPairProj B F) 1 p m h
      (TopPair.singularCohomologyMap (prodThomPairSnd B F) 1 (rankOneFiberClass (K := K) e))) := by
  -- Identify `pr₂^* g₁` with `δ σ₀` over `B` by naturality along `B → PUnit`.
  have hu : TopPair.singularCohomologyMap (prodThomPairSnd B F) 1 (rankOneFiberClass (K := K) e) =
      (prodThomPair B F).singularCohomologyδ
        (𝟙_ (ModuleCat.{w} K)) K (𝟙_ (ModuleCat.{w} K)) 0 1 rfl (rankOnePuncturedClass B e) := by
    rw [rankOneFiberClass, ← TopPair.singularCohomologyMap_comp_apply,
      ← prodThomPairMap_const_punit B F, ← ConcreteCategory.comp_apply,
      TopPair.singularCohomologyδ_naturality _ 0 1 rfl, ConcreteCategory.comp_apply,
      singularCohomologyMap_snd_prodThomPairMap_rankOnePuncturedClass]
  rw [hu, ← bijective_neg_one_pow_zsmul_comp_iff (p * 1)]
  have heq : (fun c ↦ ((-1 : ℤ) ^ (p * 1)) •
      (prodThomPair B F).pullbackCup M (prodThomPairProj B F) 1 p m h
        ((prodThomPair B F).singularCohomologyδ (𝟙_ (ModuleCat.{w} K)) K (𝟙_ (ModuleCat.{w} K))
          0 1 rfl (rankOnePuncturedClass B e)) c) =
      fun c ↦ (prodThomPair B F).singularCohomologyδ (𝟙_ (ModuleCat.{w} K)) K M p m h
        ((prodThomPair B F).snd.singularCup K (λ_ (𝟙_ (ModuleCat.{w} K))).inv (λ_ M).hom
          0 p p (Nat.zero_add p) (rankOnePuncturedClass B e)
          (TopCat.singularCohomologyMap (prodThomPairPuncturedProj B F) p c)) := by
    funext c
    have key := (singularCohomologyδ_singularCup_eq_zsmul_pullbackCup M (prodThomPair B F)
      (prodThomPairProj B F) (Nat.add_zero p) rfl h h (rankOnePuncturedClass B e) c).symm
    rwa [map_comp_prodThomPairProj] at key
  rw [heq]
  exact bijective_rankOneDelta M B e h

end RankOne

/-! ### Ranks at least two -/

section RankAtLeastTwo

variable {K : Type w} [CommRing K] {F : Type w} [TopologicalSpace F] [AddCommMonoid F]
  [Module ℝ F] {d : ℕ}

/-- The model fibre class in rank `d + 2`: `δ σ` over a point, restricted to `(F, F ∖ {0})`. -/
private def sphereFiberClass (e : F ≃L[ℝ] EuclideanSpace ℝ (Fin (d + 2))) :
    (TopPair.ofSubset ({0}ᶜ : Set (TopCat.of F))).singularCohomology
      (ModuleCat.of K K) K (ModuleCat.of K K) (d + 2) :=
  TopPair.singularCohomologyMap (prodThomPairFiberMap F (PUnit.unit : PUnit.{w + 1})) (d + 2)
    ((prodThomPair PUnit.{w + 1} F).singularCohomologyδ
      (𝟙_ (ModuleCat.{w} K)) K (𝟙_ (ModuleCat.{w} K)) (d + 1) (d + 2) rfl
      (prodThomPairPuncturedClass K PUnit.{w + 1} e))

/-- In rank `d + 2`, `pullbackCup` with the pullback of `sphereFiberClass` is bijective. -/
private theorem bijective_pullbackCup_sphere (B : Type w) [TopologicalSpace B]
    (e : F ≃L[ℝ] EuclideanSpace ℝ (Fin (d + 2))) (M : ModuleCat.{w} K) {p m : ℕ}
    (h : p + (d + 2) = m) :
    Function.Bijective ((prodThomPair B F).pullbackCup M (prodThomPairProj B F) (d + 2) p m h
      (TopPair.singularCohomologyMap (prodThomPairSnd B F) (d + 2)
        (sphereFiberClass (K := K) e))) := by
  have hu : TopPair.singularCohomologyMap (prodThomPairSnd B F) (d + 2)
        (sphereFiberClass (K := K) e) =
      (prodThomPair B F).singularCohomologyδ
        (𝟙_ (ModuleCat.{w} K)) K (𝟙_ (ModuleCat.{w} K)) (d + 1) (d + 2) rfl
        (prodThomPairPuncturedClass K B e) := by
    rw [sphereFiberClass, ← TopPair.singularCohomologyMap_comp_apply,
      ← prodThomPairMap_const_punit B F, ← ConcreteCategory.comp_apply,
      TopPair.singularCohomologyδ_naturality _ (d + 1) (d + 2) rfl, ConcreteCategory.comp_apply,
      singularCohomologyMap_snd_prodThomPairMap_prodThomPairPuncturedClass]
  rw [hu, ← bijective_neg_one_pow_zsmul_comp_iff (p * (d + 2))]
  have heq : (fun c ↦ ((-1 : ℤ) ^ (p * (d + 2))) •
      (prodThomPair B F).pullbackCup M (prodThomPairProj B F) (d + 2) p m h
        ((prodThomPair B F).singularCohomologyδ (𝟙_ (ModuleCat.{w} K)) K (𝟙_ (ModuleCat.{w} K))
          (d + 1) (d + 2) rfl (prodThomPairPuncturedClass K B e)) c) =
      ⇑(prodThomPairSingularCohomologySphereEquiv M B e p m h) := by
    funext c
    rw [prodThomPairSingularCohomologySphereEquiv_apply]
    have key := (singularCohomologyδ_singularCup_eq_zsmul_pullbackCup M (prodThomPair B F)
      (prodThomPairProj B F) (Nat.add_comm p (d + 1)) rfl (by omega) h
      (prodThomPairPuncturedClass K B e) c).symm
    rwa [map_comp_prodThomPairProj] at key
  rw [heq]
  exact (prodThomPairSingularCohomologySphereEquiv M B e p m h).bijective

end RankAtLeastTwo

/-! ### Arbitrary finite rank and arbitrary fibrewise-generating class -/

section General

variable {K : Type w} [CommRing K]

/-- Right cup multiplication `a ↦ a ⌣ γ` on `Hᵖ(B; M)` by a cup-invertible `0`-class `γ ∈ H⁰(B; K)`
is bijective. -/
private theorem bijective_singularCup_right_of_exists_inv (X : TopCat.{w}) (M : ModuleCat.{w} K)
    (p : ℕ) (γ γ' : X.singularCohomology (𝟙_ (ModuleCat.{w} K)) K (𝟙_ (ModuleCat.{w} K)) 0)
    (h₁ : X.singularCup K (λ_ _).inv (λ_ _).hom 0 0 0 rfl γ γ' = X.singularCohomologyZeroOne)
    (h₂ : X.singularCup K (λ_ _).inv (λ_ _).hom 0 0 0 rfl γ' γ = X.singularCohomologyZeroOne) :
    Function.Bijective (fun a : X.singularCohomology (𝟙_ (ModuleCat.{w} K)) K M p ↦
      X.singularCup K (λ_ (𝟙_ (ModuleCat.{w} K))).inv (ρ_ M).hom p 0 p (Nat.add_zero p) a γ) := by
  have step (u v : X.singularCohomology (𝟙_ (ModuleCat.{w} K)) K (𝟙_ (ModuleCat.{w} K)) 0)
      (huv : X.singularCup K (λ_ _).inv (λ_ _).hom 0 0 0 rfl u v = X.singularCohomologyZeroOne)
      (a : X.singularCohomology (𝟙_ (ModuleCat.{w} K)) K M p) :
      X.singularCup K (λ_ (𝟙_ (ModuleCat.{w} K))).inv (ρ_ M).hom p 0 p (Nat.add_zero p)
        (X.singularCup K (λ_ (𝟙_ (ModuleCat.{w} K))).inv (ρ_ M).hom p 0 p (Nat.add_zero p) a u)
        v = a := by
    rw [X.singularCup_assoc K (u₁₂ := (λ_ _).inv) (u := (λ_ _).inv) (u₂₃ := (λ_ _).inv)
      (u' := (λ_ _).inv) (by monoidal) (μ₁₂ := (ρ_ M).hom) (μ := (ρ_ M).hom)
      (μ₂₃ := (λ_ (𝟙_ (ModuleCat.{w} K))).hom) (μ' := (ρ_ M).hom) (by monoidal)
      (Nat.add_zero p) (Nat.add_zero p) rfl (Nat.add_zero p) a u v, huv,
      TopCat.singularCohomologyZeroOne_def]
    exact X.singularCup_constSingularCocycle_right K (e := 𝟙 _) (η := 𝟙 _)
      (by simp [unitors_inv_equal]) (by simp) (Nat.add_zero p) a
  exact ⟨Function.LeftInverse.injective (g := fun b ↦
      X.singularCup K (λ_ (𝟙_ (ModuleCat.{w} K))).inv (ρ_ M).hom p 0 p (Nat.add_zero p) b γ')
      (step γ γ' h₁),
    Function.RightInverse.surjective (g := fun b ↦
      X.singularCup K (λ_ (𝟙_ (ModuleCat.{w} K))).inv (ρ_ M).hom p 0 p (Nat.add_zero p) b γ')
      (step γ' γ h₂)⟩

variable {F : Type w} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

/-- Every finite-dimensional real normed space `F` has a class `g₀ ∈ Hʳ(F, F ∖ {0}; K)` whose
pullback `pr₂^* g₀` makes `pullbackCup` bijective over all bases `B`, coefficient modules `M`, and
degrees `p`. -/
private theorem exists_bijective_pullbackCup_prodThomPair_model :
    ∃ g₀ : (TopPair.ofSubset ({0}ᶜ : Set (TopCat.of F))).singularCohomology
        (ModuleCat.of K K) K (ModuleCat.of K K) (finrank ℝ F),
      ∀ (B' : Type w) [TopologicalSpace B'] (M : ModuleCat.{w} K) {p m : ℕ}
        (h : p + finrank ℝ F = m),
        Function.Bijective ((prodThomPair B' F).pullbackCup M (prodThomPairProj B' F)
          (finrank ℝ F) p m h (TopPair.singularCohomologyMap (prodThomPairSnd B' F)
            (finrank ℝ F) g₀)) := by
  generalize hr : finrank ℝ F = r
  rcases r with _ | _ | d
  · have : Subsingleton F := finrank_zero_iff.1 hr
    exact ⟨rankZeroFiberClass, fun B' _ M _ _ h ↦ bijective_pullbackCup_rankZero B' M h⟩
  · let e : F ≃L[ℝ] EuclideanSpace ℝ (Fin 1) :=
      (LinearEquiv.ofFinrankEq F (EuclideanSpace ℝ (Fin 1)) (by simp [hr])).toContinuousLinearEquiv
    exact ⟨rankOneFiberClass e, fun B' _ M _ _ h ↦ bijective_pullbackCup_rankOne B' e M h⟩
  · let e : F ≃L[ℝ] EuclideanSpace ℝ (Fin (d + 2)) :=
      (LinearEquiv.ofFinrankEq F (EuclideanSpace ℝ (Fin (d + 2)))
        (by simp [hr])).toContinuousLinearEquiv
    exact ⟨sphereFiberClass e, fun B' _ M _ _ h ↦ bijective_pullbackCup_sphere B' e M h⟩

/-- **The Thom isomorphism for a product bundle.** For a finite-dimensional real normed space `F`
of rank `r = finrank ℝ F` and a class `u ∈ Hʳ(B × F, B × (F ∖ {0}); K)` whose restriction to the
fibre pair `(F, F ∖ {0})` over every point `b : B` generates `Hʳ(F, F ∖ {0}; K)`, the map
`Hᵖ(B; M) ⟶ Hᵐ(B × F, B × (F ∖ {0}); M)`, `a ↦ π^* a ⌣ u`, is bijective for every `K`-module `M`
and every `p + r = m`. -/
theorem bijective_pullbackCup_prodThomPair {B : Type w} [TopologicalSpace B] (M : ModuleCat.{w} K)
    {p m : ℕ} (h : p + finrank ℝ F = m)
    {u : (prodThomPair B F).singularCohomology
      (ModuleCat.of K K) K (ModuleCat.of K K) (finrank ℝ F)}
    (hu : ∀ b : B, Submodule.span K
      {TopPair.singularCohomologyMap (prodThomPairFiberMap F b) (finrank ℝ F) u} = ⊤) :
    Function.Bijective
      ((prodThomPair B F).pullbackCup M (prodThomPairProj B F) (finrank ℝ F) p m h u) := by
  obtain ⟨g₀, hg₀⟩ := exists_bijective_pullbackCup_prodThomPair_model (K := K) (F := F)
  let u₀ := TopPair.singularCohomologyMap (prodThomPairSnd B F) (finrank ℝ F) g₀
  -- Express `u = π^* γ ⌣ u₀` using surjectivity for `u₀` in base degree `0` with `M = K`.
  obtain ⟨γ, hγ⟩ := (hg₀ B (ModuleCat.of K K) (Nat.zero_add (finrank ℝ F))).2 u
  -- Restricting to the fibre over `b` gives `u|_b = γ(b) • g₀`, so `γ(b)` is a unit of `K`.
  have hunit (b : B) : IsUnit (singularCohomologyZeroEval b γ) := by
    have hprojb : TopPair.Hom.fst (prodThomPairFiberMap F b) ≫ prodThomPairProj B F =
        TopCat.const b :=
      TopCat.ext fun x ↦ (congrArg (prodThomPairProj B F)
        (prodThomPairFiberMap_fst_apply F b x)).trans (prodThomPairProj_apply F (b, x))
    have hfib : TopPair.singularCohomologyMap (prodThomPairFiberMap F b) (finrank ℝ F) u =
        singularCohomologyZeroEval b γ • g₀ := by
      rw [← hγ, TopPair.pullbackCup_apply, ← TopPair.singularCup_naturality,
        ← ConcreteCategory.comp_apply, ← TopCat.singularCohomologyMap_comp, hprojb,
        ← TopPair.singularCohomologyMap_comp_apply, prodThomPairFiberMap_comp_prodThomPairSnd,
        TopPair.singularCohomologyMap_id, ConcreteCategory.id_apply,
        singularCohomologyMap_const_eq_singularCohomologyZeroEval_smul,
        map_smul, LinearMap.smul_apply, TopCat.singularCohomologyZeroOne_def]
      exact congrArg (singularCohomologyZeroEval b γ • ·)
        ((TopPair.ofSubset ({0}ᶜ : Set (TopCat.of F))).singularCup_constSingularCocycle_left K
          (η := 𝟙 _) (by monoidal) (by monoidal) (Nat.zero_add _) g₀)
    let φ := singularCohomologyComplSingletonFinrankEquivSelf (ModuleCat.of K K)
      (OpenPartialHomeomorph.refl F) (Set.mem_univ (0 : F))
    have hφ : IsUnit (φ (TopPair.singularCohomologyMap (prodThomPairFiberMap F b)
        (finrank ℝ F) u)) :=
      φ.span_singleton_eq_top_iff_isUnit.1 (hu b)
    rw [hfib, map_smul, smul_eq_mul] at hφ
    exact isUnit_of_mul_isUnit_left hφ
  obtain ⟨γ', h₁, h₂⟩ := exists_singularCup_eq_one (X := TopCat.of B) γ hunit
  -- By associativity, `pullbackCup u` is `pullbackCup u₀` composed with `a ↦ a ⌣ γ`.
  have hcomp : ⇑((prodThomPair B F).pullbackCup M (prodThomPairProj B F) (finrank ℝ F) p m h u) =
      ⇑((prodThomPair B F).pullbackCup M (prodThomPairProj B F) (finrank ℝ F) p m h u₀) ∘
        fun a ↦ (TopCat.of B).singularCup K (λ_ (𝟙_ (ModuleCat.{w} K))).inv (ρ_ M).hom
          p 0 p (Nat.add_zero p) a γ := by
    funext a
    simp only [Function.comp_apply, ← hγ, TopPair.pullbackCup_apply,
      ← TopCat.singularCup_naturality]
    exact ((prodThomPair B F).singularCup_assoc K (by monoidal) (by monoidal)
      (Nat.add_zero p) h (Nat.zero_add _) h _ _ u₀).symm
  rw [hcomp]
  exact (hg₀ B M h).comp (bijective_singularCup_right_of_exists_inv (TopCat.of B) M p γ γ' h₁ h₂)

/-- **The Thom isomorphism for `pr₂^* g` on a product bundle**: if `g` generates
`Hʳ(F, F ∖ {0}; K)`, then `pullbackCup` of `pr₂^* g` on `prodThomPair B F` is bijective in every
degree `p`. -/
theorem bijective_pullbackCup_prodThomPairSnd (B : Type w) [TopologicalSpace B]
    (M : ModuleCat.{w} K) {p m : ℕ} (h : p + finrank ℝ F = m)
    {g : (TopPair.ofSubset ({0}ᶜ : Set (TopCat.of F))).singularCohomology
      (ModuleCat.of K K) K (ModuleCat.of K K) (finrank ℝ F)}
    (hg : Submodule.span K {g} = ⊤) :
    Function.Bijective ((prodThomPair B F).pullbackCup M (prodThomPairProj B F) (finrank ℝ F) p m h
      (TopPair.singularCohomologyMap (prodThomPairSnd B F) (finrank ℝ F) g)) :=
  bijective_pullbackCup_prodThomPair M h fun b ↦ by
    rw [← TopPair.singularCohomologyMap_comp_apply, prodThomPairFiberMap_comp_prodThomPairSnd,
      TopPair.singularCohomologyMap_id, ConcreteCategory.id_apply]
    exact hg

variable {B : Type w} [TopologicalSpace B]

variable (M : ModuleCat.{w} K) in
/-- **The Thom isomorphism of a product bundle as a linear equivalence**,
`Hᵖ(B; M) ≃ₗ[K] Hᵐ(B × F, B × (F ∖ {0}); M)`, `a ↦ π^* a ⌣ u`, for `p + finrank ℝ F = m` and a
class `u` whose restriction to every fibre generates `Hʳ(F, F ∖ {0}; K)`. -/
def prodThomPairPullbackCupEquiv {p m : ℕ} (h : p + finrank ℝ F = m)
    {u : (prodThomPair B F).singularCohomology
      (ModuleCat.of K K) K (ModuleCat.of K K) (finrank ℝ F)}
    (hu : ∀ b : B, Submodule.span K
      {TopPair.singularCohomologyMap (prodThomPairFiberMap F b) (finrank ℝ F) u} = ⊤) :
    (TopCat.of B).singularCohomology (ModuleCat.of K K) K M p ≃ₗ[K]
      (prodThomPair B F).singularCohomology (ModuleCat.of K K) K M m :=
  LinearEquiv.ofBijective
    ((prodThomPair B F).pullbackCup M (prodThomPairProj B F) (finrank ℝ F) p m h u)
    (bijective_pullbackCup_prodThomPair M h hu)

@[simp]
theorem prodThomPairPullbackCupEquiv_apply (M : ModuleCat.{w} K) {p m : ℕ}
    (h : p + finrank ℝ F = m)
    {u : (prodThomPair B F).singularCohomology
      (ModuleCat.of K K) K (ModuleCat.of K K) (finrank ℝ F)}
    (hu : ∀ b : B, Submodule.span K
      {TopPair.singularCohomologyMap (prodThomPairFiberMap F b) (finrank ℝ F) u} = ⊤)
    (a : (TopCat.of B).singularCohomology (ModuleCat.of K K) K M p) :
    prodThomPairPullbackCupEquiv M h hu a =
      (prodThomPair B F).pullbackCup M (prodThomPairProj B F) (finrank ℝ F) p m h u a :=
  (rfl)

end General

end TauCeti
