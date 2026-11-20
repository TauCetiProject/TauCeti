/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.CategoryWithFibrations
public import TauCeti.AlgebraicTopology.Quasicategory.RightFibration
public import TauCeti.AlgebraicTopology.SimplicialSet.Coslice
public import TauCeti.AlgebraicTopology.SimplicialSet.Join.StdSimplex

/-!
# Relative slices of inner fibrations

Let `p : X ⟶ S` be an inner fibration, `i : L ⟶ K` a monomorphism and `σ : K ⟶ X` a diagram. The
relative slice map `SSet.slice.restrictionMap i p σ`,
`X_{/σ} ⟶ X_{/i ≫ σ} ×_{S_{/i ≫ σ ≫ p}} S_{/σ ≫ p}`,
which restricts a cone over `σ` along `i` and pushes it forward along `p`, is a right fibration
(HTT Proposition 2.1.2.1). Dually, the relative coslice map `SSet.coslice.restrictionMap i p σ` is
a left fibration. Taking `S` a point, the restriction of cones `C_{/p} ⟶ C_{/j ≫ p}` along a
monomorphism `j` is a right fibration for a quasicategory `C`; taking moreover `L` empty, so is the
projection `C_{/p} ⟶ C`, and the slice `C_{/p}` is a quasicategory (Joyal). The same holds dually
for coslices.

The proof is by the join horn filtration. Through the universal properties of slices and coslices,
a lifting problem of a map `j : A ⟶ B` against the relative slice map for `i`, and a lifting
problem of `i` against the relative coslice map for `j`, are both extension problems along the
pushout-join of `j` and `i` for maps `B ⋆ K ⟶ X` over `S`
(`SSet.slice.forall_hasLiftingProperty_restrictionMap_iff`). For a horn `Λ[m, k] ⟶ Δ[m]` with
`0 < k`, the relative coslice map for it is a trivial fibration: by Mathlib's description of the
trivial fibrations as the maps lifting against boundary inclusions (`SSet.rlp_monomorphisms`), it
suffices to lift `∂Δ[n] ⟶ Δ[n]`, and the pushout-join `(Λ[m, k] ⋆ Δ[n]) ∪ (Δ[m] ⋆ ∂Δ[n])` is the
inner horn `Λ[m + n + 1, k]`, which lifts against the inner fibration `p`. Dually, for `k < m` the
relative slice map for `Λ[m, k] ⟶ Δ[m]` is a trivial fibration, by the inner horns
`(∂Δ[n] ⋆ Δ[m]) ∪ (Δ[n] ⋆ Λ[m, k])`.

## Main results

* `SSet.slice.forall_hasLiftingProperty_restrictionMap_iff`: lifting problems of `j` against the
  relative slice maps for `i` correspond to lifting problems of `i` against the relative coslice
  maps for `j`.
* `SSet.coslice.hasLiftingProperty_restrictionMap_horn_ι`,
  `SSet.slice.hasLiftingProperty_restrictionMap_horn_ι`: for an inner fibration `p`, the relative
  coslice map for `Λ[m, k] ⟶ Δ[m]` with `0 < k`, and the relative slice map for it with `k < m`,
  are trivial fibrations.
* `SSet.slice.rightFibration_restrictionMap`: **the relative slice map of an inner fibration along
  a monomorphism is a right fibration** (HTT Proposition 2.1.2.1);
  `SSet.coslice.leftFibration_restrictionMap`: dually, the relative coslice map is a left
  fibration.
* `SSet.slice.rightFibration_map`, `SSet.slice.rightFibration_π`, `SSet.slice.quasicategory`: for a
  quasicategory `C` and a monomorphism `j : L ⟶ K`, the restriction of cones `C_{/p} ⟶ C_{/j ≫ p}`
  and the projection `C_{/p} ⟶ C` are right fibrations, and `C_{/p}` is a quasicategory;
  `SSet.coslice.leftFibration_map`, `SSet.coslice.leftFibration_π`, `SSet.coslice.quasicategory`
  are the duals for coslices.
* `SSet.slice.hasLift_of_isEquivalence`: the restriction of cones along a monomorphism lifts, with
  prescribed source, every edge whose image in `C` is an equivalence.

## Implementation notes

The reduction to boundary inclusions and inner anodyne pushout-joins follows the shape of the
proof of Mathlib's `SSet.innerFibration_pullbackObjObjπ` by Jack McKoen and Joël Riou, with slices
and coslices playing the role of the internal hom.

## References

* J. Lurie, *Higher Topos Theory*, Lemma 2.1.2.3, Proposition 2.1.2.1 and Corollary 2.1.2.2.
* A. Joyal, *Quasi-categories and Kan complexes*, J. Pure Appl. Algebra 175 (2002).
-/

public section

open CategoryTheory Limits MorphismProperty Simplicial

universe u

namespace SSet

variable {A B K L X S : SSet.{u}} {m : ℕ} {k : Fin (m + 1)}

/-! ### Lifting problems for relative slices and coslices -/

namespace coslice

/-- For subcomplexes `A` of `K` and `B` of `L`, if the pushout-join inclusion
`(A ⋆ L) ∪ (K ⋆ B) ⟶ K ⋆ L` has the left lifting property with respect to `p : X ⟶ S`, then for
every `τ : K ⟶ X` the relative coslice map `X_{τ/} ⟶ X_{A ⟶ K ⟶ X/} ×_{S_{A ⟶ K ⟶ S/}} S_{τ ≫ p/}`
has the right lifting property with respect to the inclusion of `B`. Through the universal
property of the coslice, a lifting problem is a map `(A ⋆ L) ∪ (K ⋆ B) ⟶ X` and a map `K ⋆ L ⟶ S`
under it. -/
theorem hasLiftingProperty_restrictionMap_of_unionJoin (A : K.Subcomplex) (B : L.Subcomplex)
    (p : X ⟶ S) [HasLiftingProperty (A.unionJoin B).ι p] (τ : K ⟶ X) :
    HasLiftingProperty B.ι (restrictionMap A.ι p τ) := by
  refine ⟨fun {a b} sq ↦ ?_⟩
  obtain ⟨b₁, b₂, hb, rfl⟩ : ∃ b₁ b₂ hb, b = pullback.lift b₁ b₂ hb :=
    ⟨b ≫ pullback.fst _ _, b ≫ pullback.snd _ _, by simp [pullback.condition],
      pullback.hom_ext (by simp) (by simp)⟩
  -- The square amounts to maps `K ⋆ B ⟶ X` and `A ⋆ L ⟶ X` agreeing on `A ⋆ B`, and a map
  -- `K ⋆ L ⟶ S` under them. Glue the first two on the pushout-join and lift against `p`.
  have h₁ := congrArg (fun F ↦ (homEquiv F).1) (sq.w =≫ pullback.fst _ _)
  have h₂ := congrArg (fun F ↦ (homEquiv F).1) (sq.w =≫ pullback.snd _ _)
  have h₃ := congrArg (fun F ↦ (homEquiv F).1) hb
  simp only [Category.assoc, restrictionMap_fst, restrictionMap_snd, pullback.lift_fst,
    pullback.lift_snd, homEquiv_comp_map_coe, join.map_id, Category.id_comp,
    Category.comp_id] at h₁ h₂ h₃
  simp only [homEquiv_comp_coe] at h₁ h₂ h₃
  have hpush := Subcomplex.unionJoin.isPushout A B
  have sq' : CommSq (hpush.desc (homEquiv b₁).1 (homEquiv a).1 h₁.symm) (A.unionJoin B).ι p
      (homEquiv b₂).1 :=
    ⟨hpush.hom_ext (by simp [h₃]) (by simp [h₂])⟩
  have hl₁ : join.map A.ι (𝟙 _) ≫ sq'.lift = (homEquiv b₁).1 := by
    rw [← Subcomplex.unionJoin.ι₁_ι, Category.assoc, sq'.fac_left, IsPushout.inl_desc]
  have hl₂ : join.map (𝟙 _) B.ι ≫ sq'.lift = (homEquiv a).1 := by
    rw [← Subcomplex.unionJoin.ι₂_ι, Category.assoc, sq'.fac_left, IsPushout.inr_desc]
  refine ⟨⟨⟨homEquiv.symm ⟨sq'.lift, ?_⟩, hom_ext (by simp [hl₂]),
    pullback.hom_ext (hom_ext (by simp [hl₁])) (hom_ext (by simp))⟩⟩⟩
  calc join.inl K L ≫ sq'.lift = join.inl K B ≫ join.map (𝟙 K) B.ι ≫ sq'.lift := by
        simp only [join.inl_map_assoc, Category.id_comp]
    _ = τ := by rw [hl₂, (homEquiv a).2]

/-- A lifting problem of `i : L ⟶ K` against the relative coslice map for `j : A ⟶ B` at
`τ : B ⟶ X` is a lifting problem of `j` against a relative slice map for `i`. -/
private lemma hasLiftingProperty_restrictionMap_of_slice (j : A ⟶ B) (i : L ⟶ K) (p : X ⟶ S)
    (τ : B ⟶ X) (h : ∀ σ : K ⟶ X, HasLiftingProperty j (slice.restrictionMap i p σ)) :
    HasLiftingProperty i (restrictionMap j p τ) := by
  refine ⟨fun {a b} sq ↦ ?_⟩
  obtain ⟨b₁, b₂, hb, rfl⟩ : ∃ b₁ b₂ hb, b = pullback.lift b₁ b₂ hb :=
    ⟨b ≫ pullback.fst _ _, b ≫ pullback.snd _ _, by simp [pullback.condition],
      pullback.hom_ext (by simp) (by simp)⟩
  -- The square consists of `α : A ⋆ K ⟶ X`, `β : B ⋆ L ⟶ X` and `γ : B ⋆ K ⟶ S`, which form a
  -- square from `j` to the relative slice map for `i` at the restriction `σ : K ⟶ X` of `α`.
  have h₁ := congrArg (fun F ↦ (homEquiv F).1) (sq.w =≫ pullback.fst _ _)
  have h₂ := congrArg (fun F ↦ (homEquiv F).1) (sq.w =≫ pullback.snd _ _)
  have h₃ := congrArg (fun F ↦ (homEquiv F).1) hb
  simp only [Category.assoc, restrictionMap_fst, restrictionMap_snd, pullback.lift_fst,
    pullback.lift_snd, homEquiv_comp_map_coe, join.map_id, Category.id_comp,
    Category.comp_id] at h₁ h₂ h₃
  simp only [homEquiv_comp_coe] at h₁ h₂ h₃
  let σ : K ⟶ X := join.inr A K ≫ (homEquiv b₁).1
  have hβ : join.inr B L ≫ (homEquiv a).1 = i ≫ σ := by
    rw [← Category.id_comp (join.inr B L), ← join.inr_map j, Category.assoc, h₁,
      join.inr_map_assoc]
  have hγ : join.inr B K ≫ (homEquiv b₂).1 = σ ≫ p := by
    rw [Category.assoc, h₃, ← Category.assoc, join.inr_map, Category.id_comp]
  have sq' : CommSq (slice.homEquiv.symm ⟨(homEquiv b₁).1, rfl⟩) j (slice.restrictionMap i p σ)
      (pullback.lift (slice.homEquiv.symm ⟨(homEquiv a).1, hβ⟩)
        (slice.homEquiv.symm ⟨(homEquiv b₂).1, hγ⟩) (slice.hom_ext (by simp [h₂]))) :=
    ⟨pullback.hom_ext (slice.hom_ext (by simp [h₁])) (slice.hom_ext (by simp [h₃]))⟩
  have := h σ
  have hl₁ := congrArg (fun F ↦ (slice.homEquiv F).1) sq'.fac_left
  have hl₂ := congrArg (fun F ↦ (slice.homEquiv F).1) (sq'.fac_right =≫ pullback.fst _ _)
  have hl₃ := congrArg (fun F ↦ (slice.homEquiv F).1) (sq'.fac_right =≫ pullback.snd _ _)
  simp only [Category.assoc, slice.restrictionMap_fst, slice.restrictionMap_snd, pullback.lift_fst,
    pullback.lift_snd, slice.homEquiv_comp_map_coe, join.map_id, Category.id_comp,
    Category.comp_id, Equiv.apply_symm_apply] at hl₁ hl₂ hl₃
  simp only [slice.homEquiv_comp_coe] at hl₁ hl₂ hl₃
  refine ⟨⟨⟨homEquiv.symm ⟨(slice.homEquiv sq'.lift).1, ?_⟩, hom_ext (by simp [hl₂]),
    pullback.hom_ext (hom_ext (by simp [hl₁])) (hom_ext (by simp [hl₃]))⟩⟩⟩
  calc join.inl B K ≫ (slice.homEquiv sq'.lift).1 =
        join.inl B L ≫ join.map (𝟙 B) i ≫ (slice.homEquiv sq'.lift).1 := by
        simp only [join.inl_map_assoc, Category.id_comp]
    _ = τ := by rw [hl₂, (homEquiv a).2]

end coslice

namespace slice

/-- A lifting problem of `j : A ⟶ B` against the relative slice map for `i : L ⟶ K` at
`σ : K ⟶ X` is a lifting problem of `i` against a relative coslice map for `j`. -/
private lemma hasLiftingProperty_restrictionMap_of_coslice (j : A ⟶ B) (i : L ⟶ K) (p : X ⟶ S)
    (σ : K ⟶ X) (h : ∀ τ : B ⟶ X, HasLiftingProperty i (coslice.restrictionMap j p τ)) :
    HasLiftingProperty j (restrictionMap i p σ) := by
  refine ⟨fun {a b} sq ↦ ?_⟩
  obtain ⟨b₁, b₂, hb, rfl⟩ : ∃ b₁ b₂ hb, b = pullback.lift b₁ b₂ hb :=
    ⟨b ≫ pullback.fst _ _, b ≫ pullback.snd _ _, by simp [pullback.condition],
      pullback.hom_ext (by simp) (by simp)⟩
  -- The square consists of `α : A ⋆ K ⟶ X`, `β : B ⋆ L ⟶ X` and `γ : B ⋆ K ⟶ S`, which form a
  -- square from `i` to the relative coslice map for `j` at the restriction `τ : B ⟶ X` of `β`.
  have h₁ := congrArg (fun F ↦ (homEquiv F).1) (sq.w =≫ pullback.fst _ _)
  have h₂ := congrArg (fun F ↦ (homEquiv F).1) (sq.w =≫ pullback.snd _ _)
  have h₃ := congrArg (fun F ↦ (homEquiv F).1) hb
  simp only [Category.assoc, restrictionMap_fst, restrictionMap_snd, pullback.lift_fst,
    pullback.lift_snd, homEquiv_comp_map_coe, join.map_id, Category.id_comp,
    Category.comp_id] at h₁ h₂ h₃
  simp only [homEquiv_comp_coe] at h₁ h₂ h₃
  let τ : B ⟶ X := join.inl B L ≫ (homEquiv b₁).1
  have hα : join.inl A K ≫ (homEquiv a).1 = j ≫ τ := by
    rw [← Category.id_comp (join.inl A K), ← join.inl_map _ i, Category.assoc, h₁,
      join.inl_map_assoc]
  have hγ : join.inl B K ≫ (homEquiv b₂).1 = τ ≫ p := by
    rw [Category.assoc, h₃, ← Category.assoc, join.inl_map, Category.id_comp]
  have sq' : CommSq (coslice.homEquiv.symm ⟨(homEquiv b₁).1, rfl⟩) i
      (coslice.restrictionMap j p τ)
      (pullback.lift (coslice.homEquiv.symm ⟨(homEquiv a).1, hα⟩)
        (coslice.homEquiv.symm ⟨(homEquiv b₂).1, hγ⟩) (coslice.hom_ext (by simp [h₂]))) :=
    ⟨pullback.hom_ext (coslice.hom_ext (by simp [h₁])) (coslice.hom_ext (by simp [h₃]))⟩
  have := h τ
  have hl₁ := congrArg (fun F ↦ (coslice.homEquiv F).1) sq'.fac_left
  have hl₂ := congrArg (fun F ↦ (coslice.homEquiv F).1) (sq'.fac_right =≫ pullback.fst _ _)
  have hl₃ := congrArg (fun F ↦ (coslice.homEquiv F).1) (sq'.fac_right =≫ pullback.snd _ _)
  simp only [Category.assoc, coslice.restrictionMap_fst, coslice.restrictionMap_snd,
    pullback.lift_fst, pullback.lift_snd, coslice.homEquiv_comp_map_coe, join.map_id,
    Category.id_comp, Category.comp_id, Equiv.apply_symm_apply] at hl₁ hl₂ hl₃
  simp only [coslice.homEquiv_comp_coe] at hl₁ hl₂ hl₃
  refine ⟨⟨⟨homEquiv.symm ⟨(coslice.homEquiv sq'.lift).1, ?_⟩, hom_ext (by simp [hl₂]),
    pullback.hom_ext (hom_ext (by simp [hl₁])) (hom_ext (by simp [hl₃]))⟩⟩⟩
  calc join.inr B K ≫ (coslice.homEquiv sq'.lift).1 =
        join.inr A K ≫ join.map j (𝟙 K) ≫ (coslice.homEquiv sq'.lift).1 := by
        simp only [join.inr_map_assoc, Category.id_comp]
    _ = σ := by rw [hl₂, (homEquiv a).2]

/-- **Lifting problems for relative slices and relative coslices correspond.** For maps
`j : A ⟶ B`, `i : L ⟶ K` and `p : X ⟶ S`, the map `j` lifts against every relative slice map
`X_{/σ} ⟶ X_{/i ≫ σ} ×_{S_{/i ≫ σ ≫ p}} S_{/σ ≫ p}` exactly when `i` lifts against every relative
coslice map `X_{τ/} ⟶ X_{j ≫ τ/} ×_{S_{j ≫ τ ≫ p/}} S_{τ ≫ p/}`: through the universal properties,
both are extension problems along the pushout-join of `j` and `i` for maps `B ⋆ K ⟶ X` over
`S`. -/
theorem forall_hasLiftingProperty_restrictionMap_iff (j : A ⟶ B) (i : L ⟶ K) (p : X ⟶ S) :
    (∀ σ : K ⟶ X, HasLiftingProperty j (restrictionMap i p σ)) ↔
      ∀ τ : B ⟶ X, HasLiftingProperty i (coslice.restrictionMap j p τ) :=
  ⟨fun h τ ↦ coslice.hasLiftingProperty_restrictionMap_of_slice j i p τ h,
    fun h σ ↦ hasLiftingProperty_restrictionMap_of_coslice j i p σ h⟩

end slice

/-! ### Relative slices and coslices of inner fibrations -/

namespace coslice

/-- For an inner fibration `p : X ⟶ S`, a simplex `τ : Δ[m] ⟶ X` and `0 < k`, **the relative
coslice map `X_{τ/} ⟶ X_{(Λ[m, k] ⟶ Δ[m] ⟶ X)/} ×_{S_{(Λ[m, k] ⟶ Δ[m] ⟶ S)/}} S_{τ ≫ p/}` is a
trivial fibration**: it has the right lifting property with respect to every monomorphism
`j : A ⟶ B`. Through the universal property of the coslice, this says that maps
`(Λ[m, k] ⋆ B) ∪ (Δ[m] ⋆ A) ⟶ X` extending `τ` extend to `Δ[m] ⋆ B`, over any given map
`Δ[m] ⋆ B ⟶ S`. -/
theorem hasLiftingProperty_restrictionMap_horn_ι (p : X ⟶ S) [InnerFibration p] (hk : 0 < k)
    (τ : Δ[m] ⟶ X) (j : A ⟶ B) [Mono j] :
    HasLiftingProperty j (restrictionMap Λ[m, k].ι p τ) := by
  suffices (monomorphisms SSet.{u}).rlp (restrictionMap Λ[m, k].ι p τ) from
    this j (monomorphisms.infer_property j)
  rw [rlp_monomorphisms]
  rintro _ _ _ ⟨n⟩
  have := join.innerAnodyneExtensions_unionJoin_horn_boundary n hk p (mem_innerFibrations p)
  exact hasLiftingProperty_restrictionMap_of_unionJoin Λ[m, k] ∂Δ[n] p τ

end coslice

namespace slice

/-- For an inner fibration `p : X ⟶ S`, a simplex `σ : Δ[m] ⟶ X` and `k < m`, **the relative
slice map `X_{/σ} ⟶ X_{/(Λ[m, k] ⟶ Δ[m] ⟶ X)} ×_{S_{/(Λ[m, k] ⟶ Δ[m] ⟶ S)}} S_{/σ ≫ p}` is a
trivial fibration**: it has the right lifting property with respect to every monomorphism
`j : A ⟶ B`. Through the universal property of the slice, this says that maps
`(A ⋆ Δ[m]) ∪ (B ⋆ Λ[m, k]) ⟶ X` extending `σ` extend to `B ⋆ Δ[m]`, over any given map
`B ⋆ Δ[m] ⟶ S`. -/
theorem hasLiftingProperty_restrictionMap_horn_ι (p : X ⟶ S) [InnerFibration p]
    (hk : k < Fin.last m) (σ : Δ[m] ⟶ X) (j : A ⟶ B) [Mono j] :
    HasLiftingProperty j (restrictionMap Λ[m, k].ι p σ) := by
  suffices (monomorphisms SSet.{u}).rlp (restrictionMap Λ[m, k].ι p σ) from
    this j (monomorphisms.infer_property j)
  rw [rlp_monomorphisms]
  rintro _ _ _ ⟨n⟩
  have := join.innerAnodyneExtensions_unionJoin_boundary_horn n hk p (mem_innerFibrations p)
  exact (forall_hasLiftingProperty_restrictionMap_iff ∂Δ[n].ι Λ[m, k].ι p).2
    (coslice.hasLiftingProperty_restrictionMap_of_unionJoin ∂Δ[n] Λ[m, k] p) σ

/-- For an inner fibration `p : X ⟶ S`, a monomorphism `i : L ⟶ K`, a diagram `σ : K ⟶ X` and
`0 < k`, **the relative slice map `X_{/σ} ⟶ X_{/i ≫ σ} ×_{S_{/i ≫ σ ≫ p}} S_{/σ ≫ p}` has the
right lifting property with respect to the horn inclusion `Λ[m, k] ⟶ Δ[m]`**. -/
theorem hasLiftingProperty_horn_ι_restrictionMap (p : X ⟶ S) [InnerFibration p] (i : L ⟶ K)
    [Mono i] (σ : K ⟶ X) (hk : 0 < k) :
    HasLiftingProperty Λ[m, k].ι (restrictionMap i p σ) :=
  (forall_hasLiftingProperty_restrictionMap_iff Λ[m, k].ι i p).2
    (fun τ ↦ coslice.hasLiftingProperty_restrictionMap_horn_ι p hk τ i) σ

/-- **The relative slice map of an inner fibration is a right fibration** (HTT
Proposition 2.1.2.1): for an inner fibration `p : X ⟶ S`, a monomorphism `i : L ⟶ K` and a
diagram `σ : K ⟶ X`, the map `X_{/σ} ⟶ X_{/i ≫ σ} ×_{S_{/i ≫ σ ≫ p}} S_{/σ ≫ p}` is a right
fibration. -/
instance rightFibration_restrictionMap (p : X ⟶ S) [InnerFibration p] (i : L ⟶ K) [Mono i]
    (σ : K ⟶ X) : RightFibration (restrictionMap i p σ) :=
  (rightFibration_iff_hasLiftingProperty _).2 fun _ _ hk ↦
    hasLiftingProperty_horn_ι_restrictionMap p i σ hk

end slice

namespace coslice

/-- For an inner fibration `p : X ⟶ S`, a monomorphism `i : L ⟶ K`, a diagram `τ : K ⟶ X` and
`k < m`, **the relative coslice map `X_{τ/} ⟶ X_{i ≫ τ/} ×_{S_{i ≫ τ ≫ p/}} S_{τ ≫ p/}` has the
right lifting property with respect to the horn inclusion `Λ[m, k] ⟶ Δ[m]`**. -/
theorem hasLiftingProperty_horn_ι_restrictionMap (p : X ⟶ S) [InnerFibration p] (i : L ⟶ K)
    [Mono i] (τ : K ⟶ X) (hk : k < Fin.last m) :
    HasLiftingProperty Λ[m, k].ι (restrictionMap i p τ) :=
  (slice.forall_hasLiftingProperty_restrictionMap_iff i Λ[m, k].ι p).1
    (fun σ ↦ slice.hasLiftingProperty_restrictionMap_horn_ι p hk σ i) τ

/-- **The relative coslice map of an inner fibration is a left fibration**, dually to HTT
Proposition 2.1.2.1: for an inner fibration `p : X ⟶ S`, a monomorphism `i : L ⟶ K` and a
diagram `τ : K ⟶ X`, the map `X_{τ/} ⟶ X_{i ≫ τ/} ×_{S_{i ≫ τ ≫ p/}} S_{τ ≫ p/}` is a left
fibration. -/
instance leftFibration_restrictionMap (p : X ⟶ S) [InnerFibration p] (i : L ⟶ K) [Mono i]
    (τ : K ⟶ X) : LeftFibration (restrictionMap i p τ) :=
  (leftFibration_iff_hasLiftingProperty _).2 fun _ _ hk ↦
    hasLiftingProperty_horn_ι_restrictionMap p i τ hk

end coslice

/-! ### Slices and coslices of quasicategories -/

variable {C : SSet.{u}}

namespace slice

/-- For a quasicategory `C`, a diagram `p : K ⟶ C` and a monomorphism `j : L ⟶ K`, the
restriction of cones `C_{/p} ⟶ C_{/j ≫ p}` is a right fibration. It is the relative slice map of
`C ⟶ Δ[0]`, followed by an isomorphism. -/
instance rightFibration_map [Quasicategory C] (p : K ⟶ C) (j : L ⟶ K) [Mono j] :
    RightFibration (map j (𝟙 C) (by simp) : slice p ⟶ slice (j ≫ p)) := by
  have : IsIso (map j (𝟙 _) (by simp) :
      slice (p ≫ terminal.from C) ⟶ slice (j ≫ p ≫ terminal.from C)) :=
    isIso_of_isTerminal (isTerminal _ terminalIsTerminal) (isTerminal _ terminalIsTerminal) _
  rw [← restrictionMap_fst j (terminal.from C) p]
  infer_instance

/-- The projection of the slice of a quasicategory is a right fibration. It is the restriction of
cones to the empty diagram, followed by an isomorphism. -/
instance rightFibration_π [Quasicategory C] (p : K ⟶ C) : RightFibration (π p) := by
  -- The empty subcomplex has no vertex.
  have := isIso_π ((⊥ : K.Subcomplex).ι ≫ p) fun ⟨x⟩ ↦ x.2
  rw [← Category.comp_id (π p),
    ← map_π (q := (⊥ : K.Subcomplex).ι ≫ p) (⊥ : K.Subcomplex).ι (𝟙 C) (by simp)]
  infer_instance

/-- **The slice of a quasicategory is a quasicategory** (Joyal). -/
instance quasicategory [Quasicategory C] (p : K ⟶ C) : Quasicategory (slice p) :=
  quasicategory_of_innerFibration (π p)

open Edge in
/-- For a quasicategory `C`, a diagram `p : K ⟶ C` and a monomorphism `j : L ⟶ K`, **the
restriction of cones `C_{/p} ⟶ C_{/j ≫ p}` lifts, with prescribed source, every edge whose image
in `C` is an equivalence**: a commutative square from `Λ[1, 0] ⟶ Δ[1]` to it has a lift when the
edge of `C` underlying its bottom edge is an equivalence. Through the universal property of the
slice, maps `(Λ[1, 0] ⋆ K) ∪ (Δ[1] ⋆ L) ⟶ C` extend to `Δ[1] ⋆ K` when their edge `Δ[1] ⟶ C` is an
equivalence. -/
theorem hasLift_of_isEquivalence [Quasicategory C] (p : K ⟶ C) (j : L ⟶ K) [Mono j]
    {t : (Λ[1, 0] : SSet) ⟶ slice p} {b : Δ[1] ⟶ slice (j ≫ p)}
    (sq : CommSq t Λ[1, 0].ι (map j (𝟙 C) (by simp)) b)
    (hb : (Edge.mk' (yonedaEquiv (b ≫ π (j ≫ p)))).IsEquivalence) : sq.HasLift :=
  RightFibration.hasLift_of_isEquivalence _ sq
    ((isEquivalence_map_iff_of_rightFibration (π (j ≫ p)) _).1
      ((isEquivalence_iff_of_edge_eq (by rw [map_edge, mk'_edge, mk'_edge, yonedaEquiv_comp])).2
        hb))

end slice

namespace coslice

/-- For a quasicategory `C`, a diagram `p : K ⟶ C` and a monomorphism `j : L ⟶ K`, the
restriction of cocones `C_{p/} ⟶ C_{j ≫ p/}` is a left fibration. It is the relative coslice map
of `C ⟶ Δ[0]`, followed by an isomorphism. -/
instance leftFibration_map [Quasicategory C] (p : K ⟶ C) (j : L ⟶ K) [Mono j] :
    LeftFibration (map j (𝟙 C) (by simp) : coslice p ⟶ coslice (j ≫ p)) := by
  have : IsIso (map j (𝟙 _) (by simp) :
      coslice (p ≫ terminal.from C) ⟶ coslice (j ≫ p ≫ terminal.from C)) :=
    isIso_of_isTerminal (isTerminal _ terminalIsTerminal) (isTerminal _ terminalIsTerminal) _
  rw [← restrictionMap_fst j (terminal.from C) p]
  infer_instance

/-- The projection of the coslice of a quasicategory is a left fibration. It is the restriction of
cocones to the empty diagram, followed by an isomorphism. -/
instance leftFibration_π [Quasicategory C] (p : K ⟶ C) : LeftFibration (π p) := by
  -- The empty subcomplex has no vertex.
  have := isIso_π ((⊥ : K.Subcomplex).ι ≫ p) fun ⟨x⟩ ↦ x.2
  rw [← Category.comp_id (π p),
    ← map_π (q := (⊥ : K.Subcomplex).ι ≫ p) (⊥ : K.Subcomplex).ι (𝟙 C) (by simp)]
  infer_instance

/-- **The coslice of a quasicategory is a quasicategory** (Joyal). -/
instance quasicategory [Quasicategory C] (p : K ⟶ C) : Quasicategory (coslice p) :=
  quasicategory_of_innerFibration (π p)

end coslice

end SSet
