/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.Bockstein.AllDegrees
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Cup.Cohomology
public import TauCeti.RepresentationTheory.Homological.ContCohomology.DegreeCast
import TauCeti.RepresentationTheory.Homological.ContCohomology.Cup.Functoriality
import TauCeti.RepresentationTheory.Homological.ContCohomology.Torsion

/-!
# The Leibniz rule for the Bockstein

A short exact sequence `0 → A → B → C → 0` of discrete `G`-modules over a compact group, whose
middle term carries a multiplication compatible with the sequence, has a connecting map `δ` that
is a graded derivation of the cup product:

```text
δ (x ⌣ y) = δ x ⌣ y + (-1)^m (x ⌣ δ y)   in H^{m+n+1}(G, A),  for x ∈ Hᵐ(G, C), y ∈ Hⁿ(G, C).
```

A derivation rule is not a statement until the products on both sides are named, so the
multiplicative structure is part of the input. It consists of a multiplication `μ` on `B`, a
multiplication `μC` on `C` for which the projection is multiplicative, and the two pairings
`μL : A × C → A` and `μR : C × A → A` through which a product with an element of the kernel
factors:

```text
incl a · b = incl (μL a (proj b)),        b · incl a = incl (μR (proj b) a).
```

The first summand `δ x ⌣ y` lives in degree `m + 1 + n` and is transported to `m + n + 1` by
`TauCeti.ContinuousCohomology.degreeCast`.

The instance the applications use is the cyclic Bockstein `TauCeti.cyclicBockstein` of
`0 → ℤ/n → ℤ/n² → ℤ/n → 0`, multiplication by `n` followed by reduction, for which all four
pairings are multiplication of residues. At `n = 2` the sign disappears and the mod-two
Bockstein is a derivation, `β (x ⌣ y) = β x ⌣ y + x ⌣ β y`, in every pair of degrees. With
`β ∘ β = 0` (`TauCeti.cyclicBockstein_cyclicBockstein`) this is the structure of the mod-two
Bockstein on the cohomology ring.

## Main definitions

* `TauCeti.cyclicMulPairing`: multiplication of `ℤ/n` as a coefficient pairing of the trivial
  `ℤ/n` coefficients of the cyclic Bockstein.

## Main results

* `TauCeti.ContCohomology.DiscreteShortExact.delta_cup`: the connecting map of a multiplicative
  short exact sequence is a graded derivation.
* `TauCeti.cyclicBockstein_cup`: the cyclic Bockstein is a graded derivation of the cup product.
* `TauCeti.cyclicBockstein_two_cup`: the mod-two Bockstein is a derivation.

## Implementation notes

The proof is the cochain computation. Lift cocycles `a` and `b` representing `x` and `y` to
cochains `a₂` and `b₂` with values in `B`, so that `d a₂` and `d b₂` are the images of cocycles
`a₁` and `b₁` representing `δ x` and `δ y`
(`TauCeti.ContCohomology.DiscreteShortExact.delta_apply`). Then `a₂ ⌣ b₂` lifts `a ⌣ b`, and by
the Leibniz rule for cochains (`TauCeti.TopPairing.cupCochain_leibniz`) its differential is the
image of `a₁ ⌣ b + (-1)^m (a ⌣ b₁)`.

## References

* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., Chapter I, §4:
  the cup product and the connecting homomorphisms.
* J.-P. Serre, *Galois Cohomology*, Chapter I, §4.5: the Bockstein of `0 → ℤ/p → ℤ/p² → ℤ/p → 0`.
-/

public section

namespace TauCeti

open CategoryTheory _root_.ContinuousCohomology TauCeti.ContinuousCohomology

universe u

namespace ContCohomology.DiscreteShortExact

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {A : Type u} [AddCommGroup A] [TopologicalSpace A] [DiscreteTopology A] [DistribMulAction G A]
  {B : Type u} [AddCommGroup B] [TopologicalSpace B] [DiscreteTopology B] [DistribMulAction G B]
  {C : Type u} [AddCommGroup C] [TopologicalSpace C] [DiscreteTopology C] [DistribMulAction G C]
  (S : DiscreteShortExact G A B C)

/-- The inclusion `A → B` as a coefficient morphism along the identity of `G`. -/
private abbrev inclPair :
    TopRep.res (ContinuousMonoidHom.id G : G →* G) (ofDiscreteModule ℤ G A) ⟶
      ofDiscreteModule ℤ G B :=
  ofDiscreteModulePair (ContinuousMonoidHom.id G : G →* G) S.incl.toIntLinearMap S.incl_equivariant

/-- The projection `B → C` as a coefficient morphism along the identity of `G`. -/
private abbrev projPair :
    TopRep.res (ContinuousMonoidHom.id G : G →* G) (ofDiscreteModule ℤ G B) ⟶
      ofDiscreteModule ℤ G C :=
  ofDiscreteModulePair (ContinuousMonoidHom.id G : G →* G) S.proj.toIntLinearMap S.proj_equivariant

-- The cochain maps of `continuousCochainsShortExact` are, by definition, the cochain maps of the
-- coefficient maps; these two lemmas restate them as `cochainsMap`, the form the cup product's
-- naturality `TauCeti.TopPairing.cupCochain_cochainsMap` is stated in.
private theorem f_f_apply (k : ℕ) (x : (TopRep.homogeneousCochains (ofDiscreteModule ℤ G A)).X k) :
    (S.continuousCochainsShortExact.f.f k).hom x =
      (cochainsMap (ContinuousMonoidHom.id G) S.inclPair).f k x := by
  rw [cochainsMap_ofDiscreteModulePair_id]
  rfl

private theorem g_f_apply (k : ℕ) (x : (TopRep.homogeneousCochains (ofDiscreteModule ℤ G B)).X k) :
    (S.continuousCochainsShortExact.g.f k).hom x =
      (cochainsMap (ContinuousMonoidHom.id G) S.projPair).f k x := by
  rw [cochainsMap_ofDiscreteModulePair_id]
  rfl

/-- On cochains, the inclusion carries `α ⌣ proj β` for the pairing `μL` to `incl α ⌣ β` for the
multiplication `μ` of `B`. Both are images of `α ⌣ β` for the pairing `(a, b) ↦ μL a (proj b)`. -/
private theorem inclPair_cupCochain_left (μ : B →+ B →+ B)
    (hμ : ∀ (g : G) (b b' : B), μ (g • b) (g • b') = g • μ b b')
    (μL : A →+ C →+ A) (hμL : ∀ (g : G) (a : A) (c : C), μL (g • a) (g • c) = g • μL a c)
    (hincl_left : ∀ (a : A) (b : B), μ (S.incl a) b = S.incl (μL a (S.proj b))) (k n : ℕ)
    (α : (TopRep.homogeneousCochains (ofDiscreteModule ℤ G A)).X k)
    (β : (TopRep.homogeneousCochains (ofDiscreteModule ℤ G B)).X n) :
    (cochainsMap (ContinuousMonoidHom.id G) S.inclPair).f (k + n)
        ((ofDiscreteModulePairing μL hμL).cupCochain k n α
          ((cochainsMap (ContinuousMonoidHom.id G) S.projPair).f n β)) =
      (ofDiscreteModulePairing μ hμ).cupCochain k n
        ((cochainsMap (ContinuousMonoidHom.id G) S.inclPair).f k α) β := by
  have hν (g : G) (a : A) (b : B) :
      μL.compl₂ S.proj (g • a) (g • b) = g • μL.compl₂ S.proj a b := by
    rw [AddMonoidHom.compl₂_apply, AddMonoidHom.compl₂_apply, S.proj_equivariant, hμL]
  have h₁ := (ofDiscreteModulePairing (μL.compl₂ S.proj) hν).cupCochain_cochainsMap
    (ofDiscreteModulePairing μL hμL) (ContinuousMonoidHom.id G) (𝟙 (ofDiscreteModule ℤ G A))
    S.projPair (𝟙 (ofDiscreteModule ℤ G A))
    (fun a b ↦ (ofDiscreteModulePairing_bil_apply (μL.compl₂ S.proj) hν a b).trans
      ((ofDiscreteModulePairing_bil_apply μL hμL a (S.proj b)).symm.trans
        (congrArg ((ofDiscreteModulePairing μL hμL).bil a)
          (ofDiscreteModulePair_hom_apply (ContinuousMonoidHom.id G : G →* G)
            S.proj.toIntLinearMap S.proj_equivariant (b : B)).symm))) k n α β
  have h₂ := (ofDiscreteModulePairing (μL.compl₂ S.proj) hν).cupCochain_cochainsMap
    (ofDiscreteModulePairing μ hμ) (ContinuousMonoidHom.id G) S.inclPair
    (𝟙 (ofDiscreteModule ℤ G B)) S.inclPair
    (fun a b ↦ (ofDiscreteModulePair_hom_apply (ContinuousMonoidHom.id G : G →* G)
        S.incl.toIntLinearMap S.incl_equivariant _).trans <|
      ((congrArg S.incl (ofDiscreteModulePairing_bil_apply (μL.compl₂ S.proj) hν a b)).trans
        (hincl_left a b).symm).trans <|
      (ofDiscreteModulePairing_bil_apply μ hμ (S.incl a) b).symm.trans
        (congrArg (fun a' ↦ (ofDiscreteModulePairing μ hμ).bil a' b)
          (ofDiscreteModulePair_hom_apply (ContinuousMonoidHom.id G : G →* G)
            S.incl.toIntLinearMap S.incl_equivariant (a : A)).symm))
    k n α β
  rw [cochainsMap_id] at h₁ h₂
  simp only [HomologicalComplex.id_f, ConcreteCategory.id_apply] at h₁ h₂
  rw [← h₁, h₂]

/-- On cochains, the inclusion carries `proj β ⌣ α` for the pairing `μR` to `β ⌣ incl α` for the
multiplication `μ` of `B`. Both are images of `β ⌣ α` for the pairing `(b, a) ↦ μR (proj b) a`. -/
private theorem inclPair_cupCochain_right (μ : B →+ B →+ B)
    (hμ : ∀ (g : G) (b b' : B), μ (g • b) (g • b') = g • μ b b')
    (μR : C →+ A →+ A) (hμR : ∀ (g : G) (c : C) (a : A), μR (g • c) (g • a) = g • μR c a)
    (hincl_right : ∀ (b : B) (a : A), μ b (S.incl a) = S.incl (μR (S.proj b) a)) (k n : ℕ)
    (β : (TopRep.homogeneousCochains (ofDiscreteModule ℤ G B)).X k)
    (α : (TopRep.homogeneousCochains (ofDiscreteModule ℤ G A)).X n) :
    (cochainsMap (ContinuousMonoidHom.id G) S.inclPair).f (k + n)
        ((ofDiscreteModulePairing μR hμR).cupCochain k n
          ((cochainsMap (ContinuousMonoidHom.id G) S.projPair).f k β) α) =
      (ofDiscreteModulePairing μ hμ).cupCochain k n β
        ((cochainsMap (ContinuousMonoidHom.id G) S.inclPair).f n α) := by
  have hν (g : G) (b : B) (a : A) :
      μR.comp S.proj (g • b) (g • a) = g • μR.comp S.proj b a := by
    rw [AddMonoidHom.comp_apply, AddMonoidHom.comp_apply, S.proj_equivariant, hμR]
  have h₁ := (ofDiscreteModulePairing (μR.comp S.proj) hν).cupCochain_cochainsMap
    (ofDiscreteModulePairing μR hμR) (ContinuousMonoidHom.id G) S.projPair
    (𝟙 (ofDiscreteModule ℤ G A)) (𝟙 (ofDiscreteModule ℤ G A))
    (fun b a ↦ (ofDiscreteModulePairing_bil_apply (μR.comp S.proj) hν b a).trans
      ((ofDiscreteModulePairing_bil_apply μR hμR (S.proj b) a).symm.trans
        (congrArg (fun c ↦ (ofDiscreteModulePairing μR hμR).bil c a)
          (ofDiscreteModulePair_hom_apply (ContinuousMonoidHom.id G : G →* G)
            S.proj.toIntLinearMap S.proj_equivariant (b : B)).symm))) k n β α
  have h₂ := (ofDiscreteModulePairing (μR.comp S.proj) hν).cupCochain_cochainsMap
    (ofDiscreteModulePairing μ hμ) (ContinuousMonoidHom.id G) (𝟙 (ofDiscreteModule ℤ G B))
    S.inclPair S.inclPair
    (fun b a ↦ (ofDiscreteModulePair_hom_apply (ContinuousMonoidHom.id G : G →* G)
        S.incl.toIntLinearMap S.incl_equivariant _).trans <|
      ((congrArg S.incl (ofDiscreteModulePairing_bil_apply (μR.comp S.proj) hν b a)).trans
        (hincl_right b a).symm).trans <|
      (ofDiscreteModulePairing_bil_apply μ hμ b (S.incl a)).symm.trans
        (congrArg ((ofDiscreteModulePairing μ hμ).bil b)
          (ofDiscreteModulePair_hom_apply (ContinuousMonoidHom.id G : G →* G)
            S.incl.toIntLinearMap S.incl_equivariant (a : A)).symm))
    k n β α
  rw [cochainsMap_id] at h₁ h₂
  simp only [HomologicalComplex.id_f, ConcreteCategory.id_apply] at h₁ h₂
  rw [← h₁, h₂]

variable [CompactSpace G] [ContinuousSMul G B]

/-- The data `TauCeti.ContCohomology.DiscreteShortExact.delta_apply` computes the connecting map
from: a lift `x₂` of the cocycle `z` to `B`, and a cocycle `z₁` on `A` whose image is `d x₂`. -/
private theorem exists_delta_witness (m : ℕ) (z : cocycles (ofDiscreteModule ℤ G C) m) :
    ∃ (x₂ : (TopRep.homogeneousCochains (ofDiscreteModule ℤ G B)).X m)
      (z₁ : cocycles (ofDiscreteModule ℤ G A) (m + 1)),
      (cochainsMap (ContinuousMonoidHom.id G) S.projPair).f m x₂ =
          (TopRep.homogeneousCochains (ofDiscreteModule ℤ G C)).iCycles m z ∧
        (cochainsMap (ContinuousMonoidHom.id G) S.inclPair).f (m + 1)
            ((TopRep.homogeneousCochains (ofDiscreteModule ℤ G A)).iCycles (m + 1) z₁) =
          ((TopRep.homogeneousCochains (ofDiscreteModule ℤ G B)).d m (m + 1)).hom x₂ := by
  obtain ⟨x₂, hx₂⟩ := S.continuousCochainsShortExact_g_surjective m
    ((TopRep.homogeneousCochains (ofDiscreteModule ℤ G C)).iCycles m z)
  have hg : (S.continuousCochainsShortExact.g.f (m + 1)).hom
      ((S.continuousCochainsShortExact.X₂.d m (m + 1)).hom x₂) = 0 := by
    rw [← ConcreteCategory.comp_apply, ← S.continuousCochainsShortExact.g.comm,
      ConcreteCategory.comp_apply, hx₂]
    exact ConcreteCategory.congr_hom
      ((TopRep.homogeneousCochains (ofDiscreteModule ℤ G C)).iCycles_d m (m + 1)) z
  obtain ⟨w, hw⟩ := (S.continuousCochainsShortExact_exact (m + 1) _).1 hg
  have hdw : ((TopRep.homogeneousCochains (ofDiscreteModule ℤ G A)).d (m + 1) (m + 1 + 1)).hom w
      = 0 := by
    have h₁ := ConcreteCategory.congr_hom
      (S.continuousCochainsShortExact.f.comm (m + 1) (m + 1 + 1)) w
    have h₂ := ConcreteCategory.congr_hom
      (S.continuousCochainsShortExact.X₂.d_comp_d m (m + 1) (m + 1 + 1)) x₂
    simp only [ConcreteCategory.comp_apply] at h₁ h₂
    rw [hw] at h₁
    apply S.continuousCochainsShortExact_f_injective (m + 1 + 1)
    exact h₁.symm.trans (h₂.trans (_root_.map_zero _).symm)
  refine ⟨x₂, (TopRep.homogeneousCochains (ofDiscreteModule ℤ G A)).cyclesMkOfEq w (m + 1 + 1)
    (CochainComplex.next ℕ (m + 1)) hdw, (S.g_f_apply m x₂).symm.trans hx₂, ?_⟩
  exact (S.f_f_apply _ _).symm.trans ((congrArg (S.continuousCochainsShortExact.f.f (m + 1)).hom
    (HomologicalComplex.iCycles_cyclesMkOfEq _ _ _ _ _)).trans hw)

omit [CompactSpace G] [ContinuousSMul G B] in
/-- The projection carries the `B`-valued cup product to the `C`-valued one. -/
private theorem projPair_cupCochain (μ : B →+ B →+ B)
    (hμ : ∀ (g : G) (b b' : B), μ (g • b) (g • b') = g • μ b b')
    (μC : C →+ C →+ C) (hμC : ∀ (g : G) (c c' : C), μC (g • c) (g • c') = g • μC c c')
    (hproj : ∀ b b' : B, S.proj (μ b b') = μC (S.proj b) (S.proj b')) (m n : ℕ)
    (a₂ : (TopRep.homogeneousCochains (ofDiscreteModule ℤ G B)).X m)
    (b₂ : (TopRep.homogeneousCochains (ofDiscreteModule ℤ G B)).X n) :
    (cochainsMap (ContinuousMonoidHom.id G) S.projPair).f (m + n)
        ((ofDiscreteModulePairing μ hμ).cupCochain m n a₂ b₂) =
      (ofDiscreteModulePairing μC hμC).cupCochain m n
        ((cochainsMap (ContinuousMonoidHom.id G) S.projPair).f m a₂)
        ((cochainsMap (ContinuousMonoidHom.id G) S.projPair).f n b₂) :=
  (ofDiscreteModulePairing μ hμ).cupCochain_cochainsMap
    (ofDiscreteModulePairing μC hμC) (ContinuousMonoidHom.id G) S.projPair S.projPair S.projPair
    (fun b b' ↦
      have hp (c : B) := ofDiscreteModulePair_hom_apply (ContinuousMonoidHom.id G : G →* G)
        S.proj.toIntLinearMap S.proj_equivariant c
      (hp _).trans <| (congrArg S.proj (ofDiscreteModulePairing_bil_apply μ hμ b b')).trans <|
        (hproj b b').trans <| (ofDiscreteModulePairing_bil_apply μC hμC _ _).symm.trans <|
          congrArg₂ (fun c c' : C ↦ (ofDiscreteModulePairing μC hμC).bil c c') (hp b).symm
            (hp b').symm) m n a₂ b₂

omit [CompactSpace G] [ContinuousSMul G B] in
/-- The first term of the Leibniz rule on lifts: if `a₂` lifts `a` and `d a₂` is the image of the
cocycle `a₁`, and `b₂` lifts `b`, then `d a₂ ⌣ b₂` is the image of `a₁ ⌣ b`, transported from
degree `m + 1 + n` to `m + n + 1`. -/
private theorem inclPair_iCycles_eq_d_cupCochain_left (μ : B →+ B →+ B)
    (hμ : ∀ (g : G) (b b' : B), μ (g • b) (g • b') = g • μ b b')
    (μL : A →+ C →+ A) (hμL : ∀ (g : G) (a : A) (c : C), μL (g • a) (g • c) = g • μL a c)
    (hincl_left : ∀ (a : A) (b : B), μ (S.incl a) b = S.incl (μL a (S.proj b))) (m n : ℕ)
    (b : cocycles (ofDiscreteModule ℤ G C) n)
    (a₂ : (TopRep.homogeneousCochains (ofDiscreteModule ℤ G B)).X m)
    (b₂ : (TopRep.homogeneousCochains (ofDiscreteModule ℤ G B)).X n)
    (a₁ : cocycles (ofDiscreteModule ℤ G A) (m + 1))
    (hb₂ : (cochainsMap (ContinuousMonoidHom.id G) S.projPair).f n b₂ =
      (TopRep.homogeneousCochains (ofDiscreteModule ℤ G C)).iCycles n b)
    (ha₁ : (cochainsMap (ContinuousMonoidHom.id G) S.inclPair).f (m + 1)
        ((TopRep.homogeneousCochains (ofDiscreteModule ℤ G A)).iCycles (m + 1) a₁) =
      ((TopRep.homogeneousCochains (ofDiscreteModule ℤ G B)).d m (m + 1)).hom a₂)
    (w : cocycles (ofDiscreteModule ℤ G A) (m + n + 1))
    (hw : (TopRep.homogeneousCochains (ofDiscreteModule ℤ G A)).iCycles (m + n + 1) w =
      ((TopRep.homogeneousCochains (ofDiscreteModule ℤ G A)).XIsoOfEq
        (Nat.add_right_comm m 1 n)).hom
        ((TopRep.homogeneousCochains (ofDiscreteModule ℤ G A)).iCycles (m + 1 + n)
          ((ofDiscreteModulePairing μL hμL).cupCocycles (m + 1) n a₁ b))) :
    (cochainsMap (ContinuousMonoidHom.id G) S.inclPair).f (m + n + 1)
        ((TopRep.homogeneousCochains (ofDiscreteModule ℤ G A)).iCycles (m + n + 1) w) =
      ((TopRep.homogeneousCochains (ofDiscreteModule ℤ G B)).XIsoOfEq
        (Nat.add_right_comm m 1 n)).hom
        ((ofDiscreteModulePairing μ hμ).cupCochain (m + 1) n
          (((TopRep.homogeneousCochains (ofDiscreteModule ℤ G B)).d m (m + 1)).hom a₂) b₂) := by
  have key := S.inclPair_cupCochain_left μ hμ μL hμL hincl_left (m + 1) n
    ((TopRep.homogeneousCochains (ofDiscreteModule ℤ G A)).iCycles (m + 1) a₁) b₂
  rw [ha₁, hb₂] at key
  rw [hw, TopPairing.iCycles_cupCocycles, ← key]
  exact (ConcreteCategory.congr_hom (HomologicalComplex.XIsoOfEq_hom_naturality
    (cochainsMap (ContinuousMonoidHom.id G) S.inclPair) (Nat.add_right_comm m 1 n)) _).symm

omit [CompactSpace G] [ContinuousSMul G B] in
/-- The second term of the Leibniz rule on lifts: if `a₂` lifts `a`, and `b₂` lifts `b` with
`d b₂` the image of the cocycle `b₁`, then `a₂ ⌣ d b₂` is the image of `a ⌣ b₁`. -/
private theorem inclPair_iCycles_eq_d_cupCochain_right (μ : B →+ B →+ B)
    (hμ : ∀ (g : G) (b b' : B), μ (g • b) (g • b') = g • μ b b')
    (μR : C →+ A →+ A) (hμR : ∀ (g : G) (c : C) (a : A), μR (g • c) (g • a) = g • μR c a)
    (hincl_right : ∀ (b : B) (a : A), μ b (S.incl a) = S.incl (μR (S.proj b) a)) (m n : ℕ)
    (a : cocycles (ofDiscreteModule ℤ G C) m)
    (a₂ : (TopRep.homogeneousCochains (ofDiscreteModule ℤ G B)).X m)
    (b₂ : (TopRep.homogeneousCochains (ofDiscreteModule ℤ G B)).X n)
    (b₁ : cocycles (ofDiscreteModule ℤ G A) (n + 1))
    (ha₂ : (cochainsMap (ContinuousMonoidHom.id G) S.projPair).f m a₂ =
      (TopRep.homogeneousCochains (ofDiscreteModule ℤ G C)).iCycles m a)
    (hb₁ : (cochainsMap (ContinuousMonoidHom.id G) S.inclPair).f (n + 1)
        ((TopRep.homogeneousCochains (ofDiscreteModule ℤ G A)).iCycles (n + 1) b₁) =
      ((TopRep.homogeneousCochains (ofDiscreteModule ℤ G B)).d n (n + 1)).hom b₂) :
    (cochainsMap (ContinuousMonoidHom.id G) S.inclPair).f (m + n + 1)
        ((TopRep.homogeneousCochains (ofDiscreteModule ℤ G A)).iCycles (m + n + 1)
          ((ofDiscreteModulePairing μR hμR).cupCocycles m (n + 1) a b₁)) =
      (ofDiscreteModulePairing μ hμ).cupCochain m (n + 1) a₂
        (((TopRep.homogeneousCochains (ofDiscreteModule ℤ G B)).d n (n + 1)).hom b₂) := by
  have key := S.inclPair_cupCochain_right μ hμ μR hμR hincl_right m (n + 1) a₂
    ((TopRep.homogeneousCochains (ofDiscreteModule ℤ G A)).iCycles (n + 1) b₁)
  rw [ha₂, hb₁, ← TopPairing.iCycles_cupCocycles] at key
  -- `m + n + 1` and `m + (n + 1)` are the same natural number by definition
  exact key

omit [CompactSpace G] [ContinuousSMul G B] in
/-- **The Leibniz rule on lifts.** If `a₂` and `b₂` lift the cocycles `a` and `b` to `B`, and
their differentials are the images of the cocycles `a₁` and `b₁`, then the differential of
`a₂ ⌣ b₂` is the image of `a₁ ⌣ b + (-1)^m (a ⌣ b₁)`, where `w` is `a₁ ⌣ b` transported from
degree `m + 1 + n` to `m + n + 1`. -/
private theorem inclPair_iCycles_eq_d_cupCochain (μ : B →+ B →+ B)
    (hμ : ∀ (g : G) (b b' : B), μ (g • b) (g • b') = g • μ b b')
    (μL : A →+ C →+ A) (hμL : ∀ (g : G) (a : A) (c : C), μL (g • a) (g • c) = g • μL a c)
    (μR : C →+ A →+ A) (hμR : ∀ (g : G) (c : C) (a : A), μR (g • c) (g • a) = g • μR c a)
    (hincl_left : ∀ (a : A) (b : B), μ (S.incl a) b = S.incl (μL a (S.proj b)))
    (hincl_right : ∀ (b : B) (a : A), μ b (S.incl a) = S.incl (μR (S.proj b) a)) (m n : ℕ)
    (a : cocycles (ofDiscreteModule ℤ G C) m) (b : cocycles (ofDiscreteModule ℤ G C) n)
    (a₂ : (TopRep.homogeneousCochains (ofDiscreteModule ℤ G B)).X m)
    (b₂ : (TopRep.homogeneousCochains (ofDiscreteModule ℤ G B)).X n)
    (a₁ : cocycles (ofDiscreteModule ℤ G A) (m + 1))
    (b₁ : cocycles (ofDiscreteModule ℤ G A) (n + 1))
    (ha₂ : (cochainsMap (ContinuousMonoidHom.id G) S.projPair).f m a₂ =
      (TopRep.homogeneousCochains (ofDiscreteModule ℤ G C)).iCycles m a)
    (hb₂ : (cochainsMap (ContinuousMonoidHom.id G) S.projPair).f n b₂ =
      (TopRep.homogeneousCochains (ofDiscreteModule ℤ G C)).iCycles n b)
    (ha₁ : (cochainsMap (ContinuousMonoidHom.id G) S.inclPair).f (m + 1)
        ((TopRep.homogeneousCochains (ofDiscreteModule ℤ G A)).iCycles (m + 1) a₁) =
      ((TopRep.homogeneousCochains (ofDiscreteModule ℤ G B)).d m (m + 1)).hom a₂)
    (hb₁ : (cochainsMap (ContinuousMonoidHom.id G) S.inclPair).f (n + 1)
        ((TopRep.homogeneousCochains (ofDiscreteModule ℤ G A)).iCycles (n + 1) b₁) =
      ((TopRep.homogeneousCochains (ofDiscreteModule ℤ G B)).d n (n + 1)).hom b₂)
    (w : cocycles (ofDiscreteModule ℤ G A) (m + n + 1))
    (hw : (TopRep.homogeneousCochains (ofDiscreteModule ℤ G A)).iCycles (m + n + 1) w =
      ((TopRep.homogeneousCochains (ofDiscreteModule ℤ G A)).XIsoOfEq
        (Nat.add_right_comm m 1 n)).hom
        ((TopRep.homogeneousCochains (ofDiscreteModule ℤ G A)).iCycles (m + 1 + n)
          ((ofDiscreteModulePairing μL hμL).cupCocycles (m + 1) n a₁ b))) :
    (cochainsMap (ContinuousMonoidHom.id G) S.inclPair).f (m + n + 1)
        ((TopRep.homogeneousCochains (ofDiscreteModule ℤ G A)).iCycles (m + n + 1)
          (w + (-1 : ℤ) ^ m • (ofDiscreteModulePairing μR hμR).cupCocycles m (n + 1) a b₁)) =
      ((TopRep.homogeneousCochains (ofDiscreteModule ℤ G B)).d (m + n) (m + n + 1)).hom
        ((ofDiscreteModulePairing μ hμ).cupCochain m n a₂ b₂) := by
  have hL := S.inclPair_iCycles_eq_d_cupCochain_left μ hμ μL hμL hincl_left m n b a₂ b₂ a₁ hb₂
    ha₁ w hw
  have hR := S.inclPair_iCycles_eq_d_cupCochain_right μ hμ μR hμR hincl_right m n a a₂ b₂ b₁ ha₂
    hb₁
  rw [TopPairing.cupCochain_leibniz, _root_.map_add, map_zsmul, _root_.map_add, map_zsmul]
  -- the Leibniz rule scales by the module structure, `map_zsmul` by the `ℤ`-action
  exact congrArg₂ HAdd.hAdd hL ((congrArg (HSMul.hSMul ((-1 : ℤ) ^ m)) hR).trans
    (int_smul_eq_zsmul _ _ _).symm)

/-- **The connecting map of a multiplicative short exact sequence is a graded derivation.** Let
`μ` be an equivariant multiplication on `B` for which the projection is multiplicative onto `μC`,
and through which products with the kernel factor as `incl a · b = incl (μL a (proj b))` and
`b · incl a = incl (μR (proj b) a)`. Then for `x` of degree `m` and `y` of degree `n`,
`δ (x ⌣ y) = δ x ⌣ y + (-1)^m (x ⌣ δ y)`, the three cup products being those of `μC`, `μL` and
`μR`, with `δ x ⌣ y` transported from degree `m + 1 + n` to `m + n + 1`. -/
theorem delta_cup (μ : B →+ B →+ B) (hμ : ∀ (g : G) (b b' : B), μ (g • b) (g • b') = g • μ b b')
    (μC : C →+ C →+ C) (hμC : ∀ (g : G) (c c' : C), μC (g • c) (g • c') = g • μC c c')
    (μL : A →+ C →+ A) (hμL : ∀ (g : G) (a : A) (c : C), μL (g • a) (g • c) = g • μL a c)
    (μR : C →+ A →+ A) (hμR : ∀ (g : G) (c : C) (a : A), μR (g • c) (g • a) = g • μR c a)
    (hproj : ∀ b b' : B, S.proj (μ b b') = μC (S.proj b) (S.proj b'))
    (hincl_left : ∀ (a : A) (b : B), μ (S.incl a) b = S.incl (μL a (S.proj b)))
    (hincl_right : ∀ (b : B) (a : A), μ b (S.incl a) = S.incl (μR (S.proj b) a))
    (m n : ℕ) (x : continuousCohomology m (ofDiscreteModule ℤ G C))
    (y : continuousCohomology n (ofDiscreteModule ℤ G C)) :
    (S.delta (m + n)).hom ((ofDiscreteModulePairing μC hμC).cup m n x y) =
      (degreeCast (ofDiscreteModule ℤ G A) (Nat.add_right_comm m 1 n)).hom
          ((ofDiscreteModulePairing μL hμL).cup (m + 1) n ((S.delta m).hom x) y) +
        (-1 : ℤ) ^ m • (ofDiscreteModulePairing μR hμR).cup m (n + 1) x ((S.delta n).hom y) := by
  obtain ⟨a, rfl⟩ := (TopRep.homogeneousCochains (ofDiscreteModule ℤ G C)).homologyπ_surjective m x
  obtain ⟨b, rfl⟩ := (TopRep.homogeneousCochains (ofDiscreteModule ℤ G C)).homologyπ_surjective n y
  obtain ⟨a₂, a₁, ha₂, ha₁⟩ := S.exists_delta_witness m a
  obtain ⟨b₂, b₁, hb₂, hb₁⟩ := S.exists_delta_witness n b
  have h₂ : (cochainsMap (ContinuousMonoidHom.id G) S.projPair).f (m + n)
      ((ofDiscreteModulePairing μ hμ).cupCochain m n a₂ b₂) =
      (TopRep.homogeneousCochains (ofDiscreteModule ℤ G C)).iCycles (m + n)
        ((ofDiscreteModulePairing μC hμC).cupCocycles m n a b) := by
    rw [S.projPair_cupCochain μ hμ μC hμC hproj, ha₂, hb₂]
    exact (TopPairing.iCycles_cupCocycles _ m n a b).symm
  -- the cocycle representing the right-hand side, and the Leibniz rule for the lift `a₂ ⌣ b₂`
  set w := cocyclesDegreeCast (X := ofDiscreteModule ℤ G A) (Nat.add_right_comm m 1 n)
    ((ofDiscreteModulePairing μL hμL).cupCocycles (m + 1) n a₁ b) with hw
  have h₁ : (cochainsMap (ContinuousMonoidHom.id G) S.inclPair).f (m + n + 1)
      ((TopRep.homogeneousCochains (ofDiscreteModule ℤ G A)).iCycles (m + n + 1)
        (w + (-1 : ℤ) ^ m • (ofDiscreteModulePairing μR hμR).cupCocycles m (n + 1) a b₁)) =
      ((TopRep.homogeneousCochains (ofDiscreteModule ℤ G B)).d (m + n) (m + n + 1)).hom
        ((ofDiscreteModulePairing μ hμ).cupCochain m n a₂ b₂) :=
    S.inclPair_iCycles_eq_d_cupCochain μ hμ μL hμL μR hμR hincl_left hincl_right m n a b a₂ b₂
      a₁ b₁ ha₂ hb₂ ha₁ hb₁ w (iCycles_cocyclesDegreeCast _ _)
  rw [TopPairing.cup_π, S.delta_apply m a a₂ ((S.g_f_apply m a₂).trans ha₂) a₁
      ((S.f_f_apply _ _).trans ha₁),
    S.delta_apply n b b₂ ((S.g_f_apply n b₂).trans hb₂) b₁ ((S.f_f_apply _ _).trans hb₁),
    TopPairing.cup_π, TopPairing.cup_π,
    S.delta_apply (m + n) _ ((ofDiscreteModulePairing μ hμ).cupCochain m n a₂ b₂)
      ((S.g_f_apply _ _).trans h₂) _ ((S.f_f_apply _ _).trans h₁),
    _root_.map_add, map_zsmul, hw, π_cocyclesDegreeCast]
  -- `m + n + 1` and `m + (n + 1)` are the same natural number by definition
  rfl

end ContCohomology.DiscreteShortExact

/-! ### The cyclic Bockstein -/

section Cyclic

attribute [local instance] trivialZModAction cyclicContinuousSMul

variable (G : Type u) [Group G] (n : ℕ)

/-- Multiplication of `ℤ/n` as a coefficient pairing of the trivial `ℤ/n` coefficients of the
cyclic Bockstein `TauCeti.cyclicBockstein`, lifted to the universe of the group. -/
def cyclicMulPairing :
    TopPairing (ofDiscreteModule ℤ G (ULift.{u} (ZMod n)))
      (ofDiscreteModule ℤ G (ULift.{u} (ZMod n))) (ofDiscreteModule ℤ G (ULift.{u} (ZMod n))) :=
  ofDiscreteModulePairing AddMonoidHom.mul fun _ _ _ ↦ rfl

/-- The cyclic multiplication pairing multiplies. -/
@[simp]
theorem cyclicMulPairing_bil_apply (x y : ULift.{u} (ZMod n)) :
    (cyclicMulPairing G n).bil x y = x * y :=
  ofDiscreteModulePairing_bil_apply _ _ x y

variable [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [NeZero n]

/-- **The Leibniz rule for the cyclic Bockstein.** The Bockstein `β` of
`0 → ℤ/n → ℤ/n² → ℤ/n → 0` is a graded derivation of the cup product of trivial `ℤ/n`
coefficients: `β (x ⌣ y) = β x ⌣ y + (-1)^i (x ⌣ β y)` for `x` of degree `i`, with `β x ⌣ y`
transported from degree `i + 1 + j` to `i + j + 1`. -/
theorem cyclicBockstein_cup (i j : ℕ)
    (x : continuousCohomology i (ofDiscreteModule ℤ G (ULift.{u} (ZMod n))))
    (y : continuousCohomology j (ofDiscreteModule ℤ G (ULift.{u} (ZMod n)))) :
    cyclicBockstein G n (i + j) ((cyclicMulPairing G n).cup i j x y) =
      (degreeCast _ (Nat.add_right_comm i 1 j)).hom
          ((cyclicMulPairing G n).cup (i + 1) j (cyclicBockstein G n i x) y) +
        (-1 : ℤ) ^ i • (cyclicMulPairing G n).cup i (j + 1) x (cyclicBockstein G n j y) := by
  rw [cyclicBockstein_def, cyclicBockstein_def, cyclicBockstein_def]
  exact (cyclicBocksteinShortExact G n).delta_cup AddMonoidHom.mul (fun _ _ _ ↦ rfl)
    AddMonoidHom.mul (fun _ _ _ ↦ rfl) AddMonoidHom.mul (fun _ _ _ ↦ rfl) AddMonoidHom.mul
    (fun _ _ _ ↦ rfl)
    (fun b b' ↦ ULift.ext (by
      simp only [AddMonoidHom.mul_apply, ULift.mul_down, cyclicBocksteinShortExact_proj_apply]
      exact map_mul _ _ _))
    (fun a b ↦ ULift.ext (by
      simp only [AddMonoidHom.mul_apply, ULift.mul_down, cyclicBocksteinShortExact_incl_apply,
        cyclicBocksteinShortExact_proj_apply]
      rw [mul_comm (ZMod.mulCastHom n rfl a.down), mul_comm a.down]
      exact (ZMod.mulCastHom_castHom_mul n rfl b.down a.down).symm))
    (fun b a ↦ ULift.ext (by
      simp only [AddMonoidHom.mul_apply, ULift.mul_down, cyclicBocksteinShortExact_incl_apply,
        cyclicBocksteinShortExact_proj_apply]
      exact (ZMod.mulCastHom_castHom_mul n rfl b.down a.down).symm))
    i j x y

/-- **The mod-two Bockstein is a derivation**: `β (x ⌣ y) = β x ⌣ y + x ⌣ β y` for the Bockstein
of `0 → ℤ/2 → ℤ/4 → ℤ/2 → 0` and the cup product of trivial `𝔽₂` coefficients, with `β x ⌣ y`
transported from degree `i + 1 + j` to `i + j + 1`. In characteristic two the sign of
`TauCeti.cyclicBockstein_cup` disappears. -/
theorem cyclicBockstein_two_cup (i j : ℕ)
    (x : continuousCohomology i (ofDiscreteModule ℤ G (ULift.{u} (ZMod 2))))
    (y : continuousCohomology j (ofDiscreteModule ℤ G (ULift.{u} (ZMod 2)))) :
    cyclicBockstein G 2 (i + j) ((cyclicMulPairing G 2).cup i j x y) =
      (degreeCast _ (Nat.add_right_comm i 1 j)).hom
          ((cyclicMulPairing G 2).cup (i + 1) j (cyclicBockstein G 2 i x) y) +
        (cyclicMulPairing G 2).cup i (j + 1) x (cyclicBockstein G 2 j y) := by
  rw [cyclicBockstein_cup]
  congr 1
  rcases neg_one_pow_eq_or ℤ i with h | h
  · rw [h, one_zsmul]
  · rw [h, neg_one_zsmul, neg_eq_iff_add_eq_zero, ← two_nsmul]
    have h2 : ∀ z : ULift.{u} (ZMod 2), 2 • z = 0 := by decide
    exact nsmul_continuousCohomology_eq_zero h2 _ _

end Cyclic

end TauCeti
