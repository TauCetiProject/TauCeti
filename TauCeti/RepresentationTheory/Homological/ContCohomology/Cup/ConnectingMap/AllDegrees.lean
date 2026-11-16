/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.Cup.Cohomology
public import TauCeti.RepresentationTheory.Homological.ContCohomology.HomologySequence
import TauCeti.RepresentationTheory.Homological.ContCohomology.Cup.Functoriality

/-!
# Cup products and connecting maps in all degrees

Two short exact sequences of discrete coefficients, together with three pairings intertwining
their inclusions and projections, give compatibility of their connecting maps with cup products.
All coefficients are discrete; the pairings are given as `TopPairing` values on the canonical
coefficient objects over `ℤ`. Pairing in the first variable gives `δ (x ⌣ y) = δ x ⌣ y`,
with the degree transport made explicit. Pairing in the second gives
`δ (x ⌣ y) = (-1)^m (x ⌣ δ y)` for a class `x` of degree `m`.

These are statements about the canonical continuous cohomology and its actual connecting maps,
for arbitrary bidegrees. The pairings on the middle, subobject and quotient coefficients are
specified separately, so neither identity assumes a multiplication on one coefficient sequence.

## References

* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., Chapter I,
  (1.4.3) and (1.4.5).
* J. S. Milne, *Arithmetic Duality Theorems*, 2nd ed., I §0, (0.1.1)-(0.1.6).

The representative computation follows the existing proof of
`TauCeti.ContCohomology.DiscreteShortExact.delta_cup`, using the cochain Leibniz rule with one
factor already a cocycle.
-/

public section

namespace TauCeti.ContCohomology.DiscreteShortExact

open CategoryTheory _root_.ContinuousCohomology TauCeti.ContinuousCohomology

universe u

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  {A₁ : Type u} [AddCommGroup A₁] [TopologicalSpace A₁] [DiscreteTopology A₁]
    [DistribMulAction G A₁]
  {A : Type u} [AddCommGroup A] [TopologicalSpace A] [DiscreteTopology A]
    [DistribMulAction G A] [ContinuousSMul G A]
  {A₂ : Type u} [AddCommGroup A₂] [TopologicalSpace A₂] [DiscreteTopology A₂]
    [DistribMulAction G A₂]
  {C₁ : Type u} [AddCommGroup C₁] [TopologicalSpace C₁] [DiscreteTopology C₁]
    [DistribMulAction G C₁]
  {C : Type u} [AddCommGroup C] [TopologicalSpace C] [DiscreteTopology C]
    [DistribMulAction G C] [ContinuousSMul G C]
  {C₂ : Type u} [AddCommGroup C₂] [TopologicalSpace C₂] [DiscreteTopology C₂]
    [DistribMulAction G C₂]
  (SA : DiscreteShortExact G A₁ A A₂) (SC : DiscreteShortExact G C₁ C C₂)
  {M : Type u} [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
    [DistribMulAction G M]

-- These adapters identify the coefficient-sequence maps with cup naturality before the
-- representative proof; inlining all four computations exceeds the default heartbeat limit.
omit [CompactSpace G] [ContinuousSMul G A] [ContinuousSMul G C] in
private theorem proj_cupCochain_left
    (P : TopPairing (ofDiscreteModule ℤ G A) (ofDiscreteModule ℤ G M) (ofDiscreteModule ℤ G C))
    (P₂ : TopPairing (ofDiscreteModule ℤ G A₂) (ofDiscreteModule ℤ G M) (ofDiscreteModule ℤ G C₂))
    (hproj : ∀ (a : A) (b : M), SC.proj (P.bil a b) = P₂.bil (SA.proj a) b)
    (m n : ℕ) (a : (TopRep.homogeneousCochains (ofDiscreteModule ℤ G A)).X m)
    (b : (TopRep.homogeneousCochains (ofDiscreteModule ℤ G M)).X n) :
    (SC.continuousCochainsShortExact.g.f (m + n)).hom (P.cupCochain m n a b) =
      P₂.cupCochain m n ((SA.continuousCochainsShortExact.g.f m).hom a) b := by
  rw [SC.continuousCochainsShortExact_g_f_apply,
    SA.continuousCochainsShortExact_g_f_apply]
  have h := P.cupCochain_cochainsMap P₂ (ContinuousMonoidHom.id G)
    (ofDiscreteModulePair (ContinuousMonoidHom.id G : G →* G)
      SA.proj.toIntLinearMap SA.proj_equivariant) (𝟙 (ofDiscreteModule ℤ G M))
    (ofDiscreteModulePair (ContinuousMonoidHom.id G : G →* G)
      SC.proj.toIntLinearMap SC.proj_equivariant)
    (fun a b ↦
      (ofDiscreteModulePair_hom_apply (ContinuousMonoidHom.id G : G →* G)
          SC.proj.toIntLinearMap SC.proj_equivariant _).trans
        ((hproj a b).trans (congrArg₂ (fun a b ↦ P₂.bil a b)
          (ofDiscreteModulePair_hom_apply (ContinuousMonoidHom.id G : G →* G)
          SA.proj.toIntLinearMap SA.proj_equivariant a).symm
          (TopRep.id_apply (ofDiscreteModule ℤ G M) b).symm)))
    m n a b
  rw [cochainsMap_id] at h
  simp only [HomologicalComplex.id_f, ConcreteCategory.id_apply] at h
  exact h

omit [CompactSpace G] [ContinuousSMul G A] [ContinuousSMul G C] in
private theorem incl_cupCochain_left
    (P₁ : TopPairing (ofDiscreteModule ℤ G A₁) (ofDiscreteModule ℤ G M) (ofDiscreteModule ℤ G C₁))
    (P : TopPairing (ofDiscreteModule ℤ G A) (ofDiscreteModule ℤ G M) (ofDiscreteModule ℤ G C))
    (hincl : ∀ (a : A₁) (b : M), SC.incl (P₁.bil a b) = P.bil (SA.incl a) b)
    (m n : ℕ) (a : (TopRep.homogeneousCochains (ofDiscreteModule ℤ G A₁)).X m)
    (b : (TopRep.homogeneousCochains (ofDiscreteModule ℤ G M)).X n) :
    (SC.continuousCochainsShortExact.f.f (m + n)).hom (P₁.cupCochain m n a b) =
      P.cupCochain m n ((SA.continuousCochainsShortExact.f.f m).hom a) b := by
  rw [SC.continuousCochainsShortExact_f_f_apply,
    SA.continuousCochainsShortExact_f_f_apply]
  have h := P₁.cupCochain_cochainsMap P (ContinuousMonoidHom.id G)
    (ofDiscreteModulePair (ContinuousMonoidHom.id G : G →* G)
      SA.incl.toIntLinearMap SA.incl_equivariant) (𝟙 (ofDiscreteModule ℤ G M))
    (ofDiscreteModulePair (ContinuousMonoidHom.id G : G →* G)
      SC.incl.toIntLinearMap SC.incl_equivariant)
    (fun a b ↦
      (ofDiscreteModulePair_hom_apply (ContinuousMonoidHom.id G : G →* G)
          SC.incl.toIntLinearMap SC.incl_equivariant _).trans
        ((hincl a b).trans (congrArg₂ (fun a b ↦ P.bil a b)
          (ofDiscreteModulePair_hom_apply (ContinuousMonoidHom.id G : G →* G)
          SA.incl.toIntLinearMap SA.incl_equivariant a).symm
          (TopRep.id_apply (ofDiscreteModule ℤ G M) b).symm)))
    m n a b
  rw [cochainsMap_id] at h
  simp only [HomologicalComplex.id_f, ConcreteCategory.id_apply] at h
  exact h

omit [CompactSpace G] [ContinuousSMul G A] [ContinuousSMul G C] in
private theorem proj_cupCochain_right
    (P : TopPairing (ofDiscreteModule ℤ G M) (ofDiscreteModule ℤ G A) (ofDiscreteModule ℤ G C))
    (P₂ : TopPairing (ofDiscreteModule ℤ G M) (ofDiscreteModule ℤ G A₂) (ofDiscreteModule ℤ G C₂))
    (hproj : ∀ (a : M) (b : A), SC.proj (P.bil a b) = P₂.bil a (SA.proj b))
    (m n : ℕ) (a : (TopRep.homogeneousCochains (ofDiscreteModule ℤ G M)).X m)
    (b : (TopRep.homogeneousCochains (ofDiscreteModule ℤ G A)).X n) :
    (SC.continuousCochainsShortExact.g.f (m + n)).hom (P.cupCochain m n a b) =
      P₂.cupCochain m n a ((SA.continuousCochainsShortExact.g.f n).hom b) := by
  rw [SC.continuousCochainsShortExact_g_f_apply,
    SA.continuousCochainsShortExact_g_f_apply]
  have h := P.cupCochain_cochainsMap P₂ (ContinuousMonoidHom.id G)
    (𝟙 (ofDiscreteModule ℤ G M)) (ofDiscreteModulePair (ContinuousMonoidHom.id G : G →* G)
      SA.proj.toIntLinearMap SA.proj_equivariant)
    (ofDiscreteModulePair (ContinuousMonoidHom.id G : G →* G)
      SC.proj.toIntLinearMap SC.proj_equivariant)
    (fun a b ↦
      (ofDiscreteModulePair_hom_apply (ContinuousMonoidHom.id G : G →* G)
          SC.proj.toIntLinearMap SC.proj_equivariant _).trans
        ((hproj a b).trans (congrArg₂ (fun a b ↦ P₂.bil a b)
          (TopRep.id_apply (ofDiscreteModule ℤ G M) a).symm
          (ofDiscreteModulePair_hom_apply (ContinuousMonoidHom.id G : G →* G)
          SA.proj.toIntLinearMap SA.proj_equivariant b).symm)))
    m n a b
  rw [cochainsMap_id] at h
  simp only [HomologicalComplex.id_f, ConcreteCategory.id_apply] at h
  exact h

omit [CompactSpace G] [ContinuousSMul G A] [ContinuousSMul G C] in
private theorem incl_cupCochain_right
    (P₁ : TopPairing (ofDiscreteModule ℤ G M) (ofDiscreteModule ℤ G A₁) (ofDiscreteModule ℤ G C₁))
    (P : TopPairing (ofDiscreteModule ℤ G M) (ofDiscreteModule ℤ G A) (ofDiscreteModule ℤ G C))
    (hincl : ∀ (a : M) (b : A₁), SC.incl (P₁.bil a b) = P.bil a (SA.incl b))
    (m n : ℕ) (a : (TopRep.homogeneousCochains (ofDiscreteModule ℤ G M)).X m)
    (b : (TopRep.homogeneousCochains (ofDiscreteModule ℤ G A₁)).X n) :
    (SC.continuousCochainsShortExact.f.f (m + n)).hom (P₁.cupCochain m n a b) =
      P.cupCochain m n a ((SA.continuousCochainsShortExact.f.f n).hom b) := by
  rw [SC.continuousCochainsShortExact_f_f_apply,
    SA.continuousCochainsShortExact_f_f_apply]
  have h := P₁.cupCochain_cochainsMap P (ContinuousMonoidHom.id G)
    (𝟙 (ofDiscreteModule ℤ G M)) (ofDiscreteModulePair (ContinuousMonoidHom.id G : G →* G)
      SA.incl.toIntLinearMap SA.incl_equivariant)
    (ofDiscreteModulePair (ContinuousMonoidHom.id G : G →* G)
      SC.incl.toIntLinearMap SC.incl_equivariant)
    (fun a b ↦
      (ofDiscreteModulePair_hom_apply (ContinuousMonoidHom.id G : G →* G)
          SC.incl.toIntLinearMap SC.incl_equivariant _).trans
        ((hincl a b).trans (congrArg₂ (fun a b ↦ P.bil a b)
          (TopRep.id_apply (ofDiscreteModule ℤ G M) a).symm
          (ofDiscreteModulePair_hom_apply (ContinuousMonoidHom.id G : G →* G)
          SA.incl.toIntLinearMap SA.incl_equivariant b).symm)))
    m n a b
  rw [cochainsMap_id] at h
  simp only [HomologicalComplex.id_f, ConcreteCategory.id_apply] at h
  exact h

/-- **A connecting map passes through a cup product in the first variable.** The three pairings
intertwine two short exact coefficient sequences in that variable. The fixed second factor is
a discrete coefficient module. The right side is transported from degree `m + 1 + n`
to degree `m + n + 1`. -/
theorem delta_cup_left
    (P : TopPairing (ofDiscreteModule ℤ G A) (ofDiscreteModule ℤ G M) (ofDiscreteModule ℤ G C))
    (P₁ : TopPairing (ofDiscreteModule ℤ G A₁) (ofDiscreteModule ℤ G M) (ofDiscreteModule ℤ G C₁))
    (P₂ : TopPairing (ofDiscreteModule ℤ G A₂) (ofDiscreteModule ℤ G M) (ofDiscreteModule ℤ G C₂))
    (hincl : ∀ (a : A₁) (b : M), SC.incl (P₁.bil a b) = P.bil (SA.incl a) b)
    (hproj : ∀ (a : A) (b : M), SC.proj (P.bil a b) = P₂.bil (SA.proj a) b)
    (m n : ℕ) (x : continuousCohomology m (ofDiscreteModule ℤ G A₂))
    (y : continuousCohomology n (ofDiscreteModule ℤ G M)) :
    (SC.delta (m + n)).hom (P₂.cup m n x y) =
      (degreeCast (ofDiscreteModule ℤ G C₁) (Nat.add_right_comm m 1 n)).hom
        (P₁.cup (m + 1) n ((SA.delta m).hom x) y) := by
  obtain ⟨a, rfl⟩ := (TopRep.homogeneousCochains (ofDiscreteModule ℤ G A₂)).homologyπ_surjective m x
  obtain ⟨b, rfl⟩ := (TopRep.homogeneousCochains (ofDiscreteModule ℤ G M)).homologyπ_surjective n y
  obtain ⟨a₂, a₁, ha₂, ha₁⟩ := SA.exists_delta_witness m a
  have h₂ : (SC.continuousCochainsShortExact.g.f (m + n)).hom
      (P.cupCochain m n a₂ ((TopRep.homogeneousCochains (ofDiscreteModule ℤ G M)).iCycles n b)) =
      (TopRep.homogeneousCochains (ofDiscreteModule ℤ G C₂)).iCycles (m + n)
        (P₂.cupCocycles m n a b) := by
    rw [proj_cupCochain_left SA SC P P₂ hproj, ha₂, TopPairing.iCycles_cupCocycles]
  set w := cocyclesDegreeCast (X := ofDiscreteModule ℤ G C₁) (Nat.add_right_comm m 1 n)
    (P₁.cupCocycles (m + 1) n a₁ b) with hw
  have h₁ : (SC.continuousCochainsShortExact.f.f (m + n + 1)).hom
      ((TopRep.homogeneousCochains (ofDiscreteModule ℤ G C₁)).iCycles (m + n + 1) w) =
      ((TopRep.homogeneousCochains (ofDiscreteModule ℤ G C)).d (m + n) (m + n + 1)).hom
        (P.cupCochain m n a₂
          ((TopRep.homogeneousCochains (ofDiscreteModule ℤ G M)).iCycles n b)) := by
    have key := incl_cupCochain_left SA SC P₁ P hincl (m + 1) n
      ((TopRep.homogeneousCochains (ofDiscreteModule ℤ G A₁)).iCycles (m + 1) a₁)
      ((TopRep.homogeneousCochains (ofDiscreteModule ℤ G M)).iCycles n b)
    rw [ha₁] at key
    have hw' : (TopRep.homogeneousCochains (ofDiscreteModule ℤ G C₁)).iCycles (m + n + 1) w =
        ((TopRep.homogeneousCochains (ofDiscreteModule ℤ G C₁)).XIsoOfEq
          (Nat.add_right_comm m 1 n)).hom
          (P₁.cupCochain (m + 1) n
            ((TopRep.homogeneousCochains (ofDiscreteModule ℤ G A₁)).iCycles (m + 1) a₁)
            ((TopRep.homogeneousCochains (ofDiscreteModule ℤ G M)).iCycles n b)) := by
      rw [hw, iCycles_cocyclesDegreeCast, TopPairing.iCycles_cupCocycles]
    have hd := P.cupCochain_leibniz m n a₂
      ((TopRep.homogeneousCochains (ofDiscreteModule ℤ G M)).iCycles n b)
    rw [(TopRep.homogeneousCochains (ofDiscreteModule ℤ G M)).d_iCycles_apply (n + 1) b,
      _root_.map_zero, smul_zero, add_zero] at hd
    exact (congrArg (SC.continuousCochainsShortExact.f.f (m + n + 1)).hom hw').trans
      ((ConcreteCategory.congr_hom (HomologicalComplex.XIsoOfEq_hom_naturality
        SC.continuousCochainsShortExact.f (Nat.add_right_comm m 1 n)) _).symm.trans
        ((congrArg ((TopRep.homogeneousCochains (ofDiscreteModule ℤ G C)).XIsoOfEq
          (Nat.add_right_comm m 1 n)).hom key).trans hd.symm))
  rw [TopPairing.cup_π, SA.delta_apply m a a₂ ha₂ a₁ ha₁, TopPairing.cup_π,
    SC.delta_apply (m + n) _ _ h₂ w h₁, hw, π_cocyclesDegreeCast]

/-- **A connecting map passes through a cup product in the second variable with the degree
sign.** The three pairings intertwine the coefficient inclusions and projections in that
variable. The fixed first factor is a discrete coefficient module, and its degree
`m` supplies the sign `(-1)^m`. -/
theorem delta_cup_right
    (P : TopPairing (ofDiscreteModule ℤ G M) (ofDiscreteModule ℤ G A) (ofDiscreteModule ℤ G C))
    (P₁ : TopPairing (ofDiscreteModule ℤ G M) (ofDiscreteModule ℤ G A₁) (ofDiscreteModule ℤ G C₁))
    (P₂ : TopPairing (ofDiscreteModule ℤ G M) (ofDiscreteModule ℤ G A₂) (ofDiscreteModule ℤ G C₂))
    (hincl : ∀ (a : M) (b : A₁), SC.incl (P₁.bil a b) = P.bil a (SA.incl b))
    (hproj : ∀ (a : M) (b : A), SC.proj (P.bil a b) = P₂.bil a (SA.proj b))
    (m n : ℕ) (x : continuousCohomology m (ofDiscreteModule ℤ G M))
    (y : continuousCohomology n (ofDiscreteModule ℤ G A₂)) :
    (SC.delta (m + n)).hom (P₂.cup m n x y) =
      (-1 : ℤ) ^ m • P₁.cup m (n + 1) x ((SA.delta n).hom y) := by
  obtain ⟨a, rfl⟩ := (TopRep.homogeneousCochains (ofDiscreteModule ℤ G M)).homologyπ_surjective m x
  obtain ⟨b, rfl⟩ := (TopRep.homogeneousCochains (ofDiscreteModule ℤ G A₂)).homologyπ_surjective n y
  obtain ⟨b₂, b₁, hb₂, hb₁⟩ := SA.exists_delta_witness n b
  have h₂ : (SC.continuousCochainsShortExact.g.f (m + n)).hom
      (P.cupCochain m n ((TopRep.homogeneousCochains (ofDiscreteModule ℤ G M)).iCycles m a) b₂) =
      (TopRep.homogeneousCochains (ofDiscreteModule ℤ G C₂)).iCycles (m + n)
        (P₂.cupCocycles m n a b) := by
    rw [proj_cupCochain_right SA SC P P₂ hproj, hb₂, TopPairing.iCycles_cupCocycles]
  have h₁ : (SC.continuousCochainsShortExact.f.f (m + n + 1)).hom
      ((TopRep.homogeneousCochains (ofDiscreteModule ℤ G C₁)).iCycles (m + n + 1)
        ((-1 : ℤ) ^ m • P₁.cupCocycles m (n + 1) a b₁)) =
      ((TopRep.homogeneousCochains (ofDiscreteModule ℤ G C)).d (m + n) (m + n + 1)).hom
        (P.cupCochain m n
          ((TopRep.homogeneousCochains (ofDiscreteModule ℤ G M)).iCycles m a) b₂) := by
    have key := incl_cupCochain_right SA SC P₁ P hincl m (n + 1)
      ((TopRep.homogeneousCochains (ofDiscreteModule ℤ G M)).iCycles m a)
      ((TopRep.homogeneousCochains (ofDiscreteModule ℤ G A₁)).iCycles (n + 1) b₁)
    rw [hb₁] at key
    have hz := congrArg (SC.continuousCochainsShortExact.f.f (m + n + 1)).hom
      (TopPairing.iCycles_cupCocycles P₁ m (n + 1) a b₁)
    have hd := P.cupCochain_leibniz m n
      ((TopRep.homogeneousCochains (ofDiscreteModule ℤ G M)).iCycles m a) b₂
    rw [(TopRep.homogeneousCochains (ofDiscreteModule ℤ G M)).d_iCycles_apply (m + 1) a,
      _root_.map_zero, LinearMap.zero_apply, _root_.map_zero, zero_add] at hd
    exact (congrArg (SC.continuousCochainsShortExact.f.f (m + n + 1)).hom
      (map_zsmul ((TopRep.homogeneousCochains (ofDiscreteModule ℤ G C₁)).iCycles
        (m + n + 1)).hom ((-1 : ℤ) ^ m) (P₁.cupCocycles m (n + 1) a b₁))).trans
      ((map_zsmul (SC.continuousCochainsShortExact.f.f (m + n + 1)).hom _ _).trans
        ((congrArg (HSMul.hSMul ((-1 : ℤ) ^ m)) (hz.trans key)).trans
          ((int_smul_eq_zsmul _ _ _).symm.trans hd.symm)))
  rw [TopPairing.cup_π, SA.delta_apply n b b₂ hb₂ b₁ hb₁, TopPairing.cup_π,
    SC.delta_apply (m + n) _ _ h₂ _ h₁, map_zsmul]
  rfl

end TauCeti.ContCohomology.DiscreteShortExact
