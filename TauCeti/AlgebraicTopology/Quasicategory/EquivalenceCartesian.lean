/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Quasicategory.Cartesian
public import TauCeti.AlgebraicTopology.Quasicategory.OuterHorn.Basic

/-!
# Equivalences are the edges Cartesian over a point

Let `X` be a quasicategory and `f : x ⟶ y` an edge of `X`. The following are equivalent
(HTT Proposition 2.4.1.5 over a point, Joyal):

* `f` is an equivalence;
* the restriction of cones `X_{/f} ⟶ X_{/y}` is a trivial fibration, that is, has the right
  lifting property with respect to all monomorphisms;
* `f` is Cartesian for the map from `X` to a terminal simplicial set.

The second and the third conditions agree for every simplicial set `X`
(`SSet.Edge.isCartesian_iff_rlp_slice_map`, in `TauCeti.AlgebraicTopology.Quasicategory.Cartesian`):
over a terminal simplicial set `S` every slice of `S` is terminal (`SSet.slice.isTerminal`), so
the map `X_{/f} ⟶ X_{/y} ×_{S_{/p y}} S_{/p f}` defining Cartesian edges is the restriction of
cones `X_{/f} ⟶ X_{/y}` followed by an isomorphism.

For the first two, a lifting problem of the boundary inclusion `∂Δ[n] ⟶ Δ[n]` against
`X_{/f} ⟶ X_{/y}` is, by the universal property of the slice, an extension problem for maps into
`X` along `(∂Δ[n] ⋆ Δ[1]) ∪ (Δ[n] ⋆ Λ[1, 1]) ⟶ Δ[n] ⋆ Δ[1]`, where `Λ[1, 1]` is the target vertex
of `Δ[1]`. Under `Δ[n] ⋆ Δ[1] ≅ Δ[n + 2]` this is the horn inclusion
`Λ[n + 2, n + 2] ⟶ Δ[n + 2]` (`SSet.join.preimage_unionJoin_boundary_horn`), and the final edge of
the horn, from `n + 1` to `n + 2`, is `f`. By Mathlib's description of the trivial fibrations
as the maps lifting against boundary inclusions (`SSet.rlp_monomorphisms`), the restriction of
cones is a trivial fibration exactly when all these horns can be filled, which by Joyal's
characterization of equivalences (`SSet.Edge.isEquivalence_iff_hornFilling_last`) means that `f`
is an equivalence. This reduction of outer horn filling to lifting against a restriction of cones,
through the identification of the horn with a pushout-join, is the method of Kerodon's proof of
Joyal's theorem (Kerodon Theorem 4.4.2.6), used in the same way in
`TauCeti.AlgebraicTopology.Quasicategory.OuterHorn.Basic`.

The same identification, applied to the relative restriction of cones
`X_{/f} ⟶ X_{/y} ×_{S_{/p y}} S_{/p f}` of a map `p : X ⟶ S`, shows that the horns
`Λ[n + 2, n + 2]` whose final edge is `p`-Cartesian lift along `p` (HTT Remark 2.4.1.4).

## Main results

* `SSet.Edge.IsCartesian.exists_lift_horn_last`: a horn `Λ[n + 2, n + 2]` whose final edge is
  `p`-Cartesian lifts along `p` over every `(n + 2)`-simplex of the base.

* `SSet.Edge.isEquivalence_iff_rlp_slice_map`: an edge `f : x ⟶ y` of a quasicategory is an
  equivalence exactly when the restriction of cones `X_{/f} ⟶ X_{/y}` is a trivial fibration.
* `SSet.Edge.isEquivalence_iff_isCartesian`: **an edge of a quasicategory is an equivalence
  exactly when it is Cartesian over a point.**
* `SSet.Edge.isCartesian_of_kanComplex`, `CategoryTheory.nerve.isCartesian_edgeMk_iff`,
  `SSet.stdSimplex.not_isCartesian_of_lt`: every edge of a Kan complex, for example of the nerve
  of a groupoid, is Cartesian over a point; an edge of the nerve of a category is Cartesian over
  a point exactly when its morphism is an isomorphism; and an edge of `Δ[n]` between distinct
  vertices, such as the edge from `0` to `1` of `Δ[1]`, is not.

## References

* J. Lurie, *Higher Topos Theory*, Proposition 1.2.4.3, Proposition 2.4.1.5 and Remark 2.4.1.4.
* A. Joyal, *Quasi-categories and Kan complexes*, J. Pure Appl. Algebra 175 (2002), Theorem 1.3.
* J. Lurie, *Kerodon*, Theorem 4.4.2.6 (the pushout-join description of outer horns, used for the
  equivalence of the first two conditions).
-/

public section

open CategoryTheory Limits MorphismProperty Simplicial

universe v u

namespace SSet

namespace Edge

variable {X : SSet.{u}}

section boundary

/-! ### Lifting boundaries against the restriction of cones to the target -/

variable (n : ℕ)

/-- Under `Δ[n] ⋆ Δ[1] ≅ Δ[n + 2]`, the pushout-join `(∂Δ[n] ⋆ Δ[1]) ∪ (Δ[n] ⋆ Λ[1, 1])` is the
horn `Λ[n + 2, n + 2]`. -/
private lemma preimage_unionJoin_eq :
    (Subcomplex.unionJoin ∂Δ[n] Λ[1, 1]).preimage (join.stdSimplexIso.{u} n 1).inv =
      Λ[n + 2, Fin.last (n + 2)] := by
  rw [join.preimage_unionJoin_boundary_horn n one_ne_zero 1]
  -- The horn vertex `Fin.cast _ (Fin.natAdd (n + 1) 1)` of `Δ[n + 1 + 1]` is `Fin.last (n + 2)`
  -- by definition, `n + 1 + 1` and `n + 2` being definitionally equal.
  rfl

/-- The isomorphism of the pushout-join `(∂Δ[n] ⋆ Δ[1]) ∪ (Δ[n] ⋆ Λ[1, 1])` with the horn
`Λ[n + 2, n + 2]`. -/
private noncomputable def unionJoinIso :
    (Subcomplex.unionJoin ∂Δ[n] Λ[1, 1] : SSet.{u}) ≅ Λ[n + 2, Fin.last (n + 2)] :=
  Subcomplex.isoOfPreimageEq (join.stdSimplexIso n 1) (preimage_unionJoin_eq n)

/-- Under the isomorphism with the horn, the edge `Δ[1]` of the pushout-join is the final edge of
`Λ[n + 2, n + 2]`, from `n + 1` to `n + 2`. -/
private lemma yonedaEquiv_inr_comp_unionJoinIso_hom :
    yonedaEquiv (join.inr (∂Δ[n] : SSet.{u}) Δ[1] ≫
        Subcomplex.unionJoin.ι₁ ∂Δ[n] Λ[1, 1] ≫ (unionJoinIso n).hom) =
      horn.edge (n + 2) (Fin.last (n + 2)) (Fin.last (n + 1)).castSucc (Fin.last (n + 2))
        (Fin.le_last _) (by simp) := by
  refine injective_of_mono (Subcomplex.ι.{u} Λ[n + 2, Fin.last (n + 2)] |>.app _) ?_
  rw [← yonedaEquiv_comp, Category.assoc, Category.assoc, unionJoinIso,
    Subcomplex.isoOfPreimageEq_hom_ι, Subcomplex.unionJoin.ι₁_ι_assoc, join.inr_map_assoc,
    Category.id_comp]
  refine stdSimplex.ext _ _ fun j ↦ ?_
  rw [join.yonedaEquiv_inr_comp_stdSimplexIso_hom]
  fin_cases j <;> rfl

variable {n}

/-- A lifting problem of `∂Δ[n] ⟶ Δ[n]` against the restriction of cones `X_{/f} ⟶ X_{/y}` for
the edge `f` given by `s` has a solution when every horn `Λ[n + 2, n + 2]` with final edge `s`
can be filled. -/
private lemma hasLiftingProperty_of_hornFilling (s : X _⦋1⦌)
    (H : ∀ σ₀ : (Λ[n + 2, Fin.last (n + 2)] : SSet) ⟶ X,
      σ₀.app _ (horn.edge (n + 2) (Fin.last (n + 2)) (Fin.last (n + 1)).castSucc
        (Fin.last (n + 2)) (Fin.le_last _) (by simp)) = s →
        ∃ σ : Δ[n + 2] ⟶ X, σ₀ = Λ[n + 2, Fin.last (n + 2)].ι ≫ σ) :
    HasLiftingProperty ∂Δ[n].ι (slice.map (stdSimplex.δ 0) (𝟙 X) (by simp) :
      slice (yonedaEquiv.symm s) ⟶ slice (stdSimplex.δ 0 ≫ yonedaEquiv.symm s)) := by
  refine ⟨fun {a b} sq ↦ ?_⟩
  -- The horn `Λ[1, 1]` is the target vertex of `Δ[1]`.
  let t := stdSimplex.isTerminalObj₀.{u}.from (Λ[1, 1] : SSet)
  have hΛ : Λ[1, 1].ι = t ≫ stdSimplex.δ 0 := by
    rw [horn_one_ι_eq_const, stdSimplex.δ_zero_eq_const, comp_const]
  have hpush := Subcomplex.unionJoin.isPushout ∂Δ[n] Λ[1, 1]
  -- The square amounts to maps `A : ∂Δ[n] ⋆ Δ[1] ⟶ X` and `B : Δ[n] ⋆ Δ[0] ⟶ X` agreeing on
  -- `∂Δ[n] ⋆ Δ[0]`; they glue to a map `φ` on the pushout-join, a horn `Λ[n + 2, n + 2]`.
  let A := (slice.homEquiv a).val
  let B := (slice.homEquiv b).val
  have hw : join.map (𝟙 _) (stdSimplex.δ 0) ≫ A = join.map ∂Δ[n].ι (𝟙 _) ≫ B := by
    simpa using congrArg (fun F ↦ (slice.homEquiv F).val) sq.w
  have hw' : join.map (𝟙 _) Λ[1, 1].ι ≫ A = join.map ∂Δ[n].ι (𝟙 _) ≫ join.map (𝟙 _) t ≫ B := by
    rw [hΛ, ← Category.id_comp (𝟙 (∂Δ[n] : SSet)), join.map_comp_assoc, hw]
    simp only [← join.map_comp_assoc, Category.id_comp, Category.comp_id, t]
  let φ := hpush.desc A (join.map (𝟙 _) t ≫ B) hw'
  obtain ⟨τ, hτ⟩ := H ((unionJoinIso n).inv ≫ φ) (by
    rw [← yonedaEquiv_inr_comp_unionJoinIso_hom, ← yonedaEquiv_comp]
    simp [φ, A, (slice.homEquiv a).property])
  -- The filler, read on `Δ[n] ⋆ Δ[1]`, extends `φ`.
  let L := (join.stdSimplexIso n 1).hom ≫ τ
  have hL : (Subcomplex.unionJoin ∂Δ[n] Λ[1, 1]).ι ≫ L = φ := by
    rw [← Subcomplex.isoOfPreimageEq_hom_ι_assoc (join.stdSimplexIso n 1) (preimage_unionJoin_eq n),
      ← hτ, ← unionJoinIso, Iso.hom_inv_id_assoc]
  have hL₁ : join.map ∂Δ[n].ι (𝟙 _) ≫ L = A := by
    rw [← Subcomplex.unionJoin.ι₁_ι_assoc, hL, hpush.inl_desc]
  have hL₂ : join.map (𝟙 _) Λ[1, 1].ι ≫ L = join.map (𝟙 _) t ≫ B := by
    rw [← Subcomplex.unionJoin.ι₂_ι_assoc, hL, hpush.inr_desc]
  refine ⟨⟨⟨slice.homEquiv.symm ⟨L, ?_⟩, ?_, ?_⟩⟩⟩
  · have hinr : join.inr (∂Δ[n] : SSet.{u}) Δ[1] ≫ join.map ∂Δ[n].ι (𝟙 _) = join.inr _ _ := by
      rw [join.inr_map, Category.id_comp]
    rw [← hinr, Category.assoc, hL₁]
    exact (slice.homEquiv a).property
  · exact slice.hom_ext (by rw [slice.homEquiv_comp_coe, Equiv.apply_symm_apply, hL₁])
  · have hδ : join.map (𝟙 _) (stdSimplex.δ 0) ≫ L = B := calc
      _ = join.map (𝟙 _) (horn.ι 1 0 (by decide)) ≫ join.map (𝟙 _) Λ[1, 1].ι ≫ L := by
        rw [← join.map_comp_assoc, Category.id_comp, horn.ι_ι]
      _ = B := by
        rw [hL₂, ← join.map_comp_assoc, Category.id_comp,
          stdSimplex.isTerminalObj₀.hom_ext (horn.ι 1 0 _ ≫ t) (𝟙 _), join.map_id,
          Category.id_comp]
    exact slice.hom_ext (by
      rw [slice.homEquiv_comp_map_coe, Equiv.apply_symm_apply, Category.comp_id, hδ])

end boundary

variable {x y : X _⦋0⦌}

/-- The lifting property of `∂Δ[n] ⟶ Δ[n]` against `X_{/f} ⟶ X_{/y} ×_{S_{/p y}} S_{/p f}` for a
`p`-Cartesian edge `f`, read through the universal property of slices: cones `A` over `f` and `B`
over its target, agreeing on `∂Δ[n] ⋆ Δ[0]`, and a cone `C` over `p f` under them, extend to a cone
`Δ[n] ⋆ Δ[1] ⟶ X` over `f` lying over `C`. -/
private lemma IsCartesian.exists_lift_join {S : SSet.{u}} {p : X ⟶ S} {f : Edge x y}
    (hf : f.IsCartesian p) {n : ℕ} (A : join (∂Δ[n] : SSet.{u}) Δ[1] ⟶ X)
    (B : join Δ[n] Δ[0] ⟶ X) (C : join Δ[n] Δ[1] ⟶ S)
    (hA : join.inr _ _ ≫ A = yonedaEquiv.symm f.edge)
    (hB : join.inr _ _ ≫ B = stdSimplex.δ 0 ≫ yonedaEquiv.symm f.edge)
    (hw : join.map (𝟙 _) (stdSimplex.δ 0) ≫ A = join.map ∂Δ[n].ι (𝟙 _) ≫ B)
    (hAC : A ≫ p = join.map ∂Δ[n].ι (𝟙 _) ≫ C)
    (hBC : B ≫ p = join.map (𝟙 _) (stdSimplex.δ 0) ≫ C) :
    ∃ L : join Δ[n] Δ[1] ⟶ X, join.map ∂Δ[n].ι (𝟙 _) ≫ L = A ∧
      join.map (𝟙 _) (stdSimplex.δ 0) ≫ L = B ∧ L ≫ p = C := by
  have := (isCartesian_iff f p).1 hf _ (MorphismProperty.monomorphisms.infer_property ∂Δ[n].ι)
  have hC : join.inr _ _ ≫ C = yonedaEquiv.symm f.edge ≫ p := by
    rw [← hA, Category.assoc, hAC, join.inr_map_assoc, Category.id_comp]
  let a : (∂Δ[n] : SSet) ⟶ slice (yonedaEquiv.symm f.edge) := slice.homEquiv.symm ⟨A, hA⟩
  let b : Δ[n] ⟶ slice (stdSimplex.δ 0 ≫ yonedaEquiv.symm f.edge) := slice.homEquiv.symm ⟨B, hB⟩
  let c : Δ[n] ⟶ slice (yonedaEquiv.symm f.edge ≫ p) := slice.homEquiv.symm ⟨C, hC⟩
  have sq : CommSq a ∂Δ[n].ι
      (slice.restrictionMap (stdSimplex.δ 0) p (yonedaEquiv.symm f.edge))
      (Limits.pullback.lift b c (slice.hom_ext (by simp [b, c, hBC]))) :=
    ⟨Limits.pullback.hom_ext (slice.hom_ext (by simp [a, b, hw]))
      (slice.hom_ext (by simp [a, c, hAC]))⟩
  have h₁ : join.map ∂Δ[n].ι (𝟙 _) ≫ (slice.homEquiv sq.lift).val = A := by
    rw [← slice.homEquiv_comp_coe, sq.fac_left, Equiv.apply_symm_apply]
  have h₂ := congrArg (fun F ↦ (slice.homEquiv F).val)
    (sq.fac_right =≫ Limits.pullback.fst _ _)
  have h₃ := congrArg (fun F ↦ (slice.homEquiv F).val)
    (sq.fac_right =≫ Limits.pullback.snd _ _)
  simp only [Category.assoc, slice.restrictionMap_fst, slice.restrictionMap_snd,
    Limits.pullback.lift_fst, Limits.pullback.lift_snd, slice.homEquiv_comp_map_coe,
    Equiv.apply_symm_apply, Category.comp_id, join.map_id, Category.id_comp, b, c] at h₂ h₃
  exact ⟨_, h₁, h₂, h₃⟩

/-- **Horn filling along a Cartesian edge** (HTT Remark 2.4.1.4). Let `f` be a `p`-Cartesian edge
for `p : X ⟶ S`. A horn `Λ[n + 2, n + 2] ⟶ X` whose final edge, from `n + 1` to `n + 2`, is `f`,
lying over an `(n + 2)`-simplex `τ` of `S`, extends to an `(n + 2)`-simplex of `X` over `τ`. -/
theorem IsCartesian.exists_lift_horn_last {S : SSet.{u}} {p : X ⟶ S} {f : Edge x y}
    (hf : f.IsCartesian p) {n : ℕ} (σ₀ : (Λ[n + 2, Fin.last (n + 2)] : SSet) ⟶ X)
    (hσ₀ : σ₀.app _ (horn.edge (n + 2) (Fin.last (n + 2)) (Fin.last (n + 1)).castSucc
      (Fin.last (n + 2)) (Fin.le_last _) (by simp)) = f.edge)
    (τ : Δ[n + 2] ⟶ S) (hτ : σ₀ ≫ p = Λ[n + 2, Fin.last (n + 2)].ι ≫ τ) :
    ∃ σ : Δ[n + 2] ⟶ X, Λ[n + 2, Fin.last (n + 2)].ι ≫ σ = σ₀ ∧ σ ≫ p = τ := by
  -- Under `Δ[n] ⋆ Δ[1] ≅ Δ[n + 2]` the horn is the pushout-join
  -- `(∂Δ[n] ⋆ Δ[1]) ∪ (Δ[n] ⋆ Λ[1, 1])`, so the extension problem is a lifting problem of
  -- `∂Δ[n] ⟶ Δ[n]` against the trivial fibration `X_{/f} ⟶ X_{/y} ×_{S_{/p y}} S_{/p f}`.
  -- The horn `Λ[1, 1]` is the target vertex `e` of `Δ[1]`.
  let e : Δ[0] ⟶ (Λ[1, 1] : SSet.{u}) := horn.ι 1 0 (by decide)
  let t := stdSimplex.isTerminalObj₀.{u}.from (Λ[1, 1] : SSet)
  have hΛ : Λ[1, 1].ι = t ≫ stdSimplex.δ 0 := by
    rw [horn_one_ι_eq_const, stdSimplex.δ_zero_eq_const, comp_const]
  have hte : t ≫ e = 𝟙 _ := by
    have := horn.isIso_ι_one (1 : Fin 2) 0 (by decide)
    rw [stdSimplex.isTerminalObj₀.hom_ext t (inv e)]
    exact IsIso.inv_hom_id e
  have he : e ≫ Λ[1, 1].ι = stdSimplex.δ 0 := horn.ι_ι _ _ _
  have hpush := Subcomplex.unionJoin.isPushout ∂Δ[n] Λ[1, 1]
  have hE : (unionJoinIso.{u} n).hom ≫ Λ[n + 2, Fin.last (n + 2)].ι =
      (Subcomplex.unionJoin ∂Δ[n] Λ[1, 1]).ι ≫ (join.stdSimplexIso.{u} n 1).hom :=
    Subcomplex.isoOfPreimageEq_hom_ι _ _
  -- Read on the pushout-join, `σ₀` consists of maps `A : ∂Δ[n] ⋆ Δ[1] ⟶ X` and
  -- `B : Δ[n] ⋆ Δ[0] ⟶ X`, cones over the edge `f` and over its target, and `τ` is a map
  -- `C : Δ[n] ⋆ Δ[1] ⟶ S`, a cone over `p f`.
  let φ := (unionJoinIso n).hom ≫ σ₀
  let A := Subcomplex.unionJoin.ι₁ ∂Δ[n] Λ[1, 1] ≫ φ
  let B := join.map (𝟙 _) e ≫ Subcomplex.unionJoin.ι₂ ∂Δ[n] Λ[1, 1] ≫ φ
  let C := (join.stdSimplexIso n 1).hom ≫ τ
  have hφ : φ ≫ p = (Subcomplex.unionJoin ∂Δ[n] Λ[1, 1]).ι ≫ C := by
    simp only [φ, C, Category.assoc, hτ]
    rw [← Category.assoc, hE, Category.assoc]
  have hA : join.inr _ _ ≫ A = yonedaEquiv.symm f.edge := by
    rw [← hσ₀, ← yonedaEquiv_inr_comp_unionJoinIso_hom, ← yonedaEquiv_comp, Equiv.symm_apply_apply]
    simp [A, φ]
  have hι : join.inr (Δ[n] : SSet.{u}) _ ≫ Subcomplex.unionJoin.ι₂ ∂Δ[n] Λ[1, 1] =
      Λ[1, 1].ι ≫ join.inr _ _ ≫ Subcomplex.unionJoin.ι₁ ∂Δ[n] Λ[1, 1] := by
    rw [← cancel_mono (Subcomplex.unionJoin ∂Δ[n] Λ[1, 1]).ι]
    simp
  have hB : join.inr _ _ ≫ B = stdSimplex.δ 0 ≫ yonedaEquiv.symm f.edge := by
    simp only [B, join.inr_map_assoc, reassoc_of% hι, ← hA, A]
    rw [horn.ι_ι_assoc]
  have hw : join.map (𝟙 _) (stdSimplex.δ 0) ≫ A = join.map ∂Δ[n].ι (𝟙 _) ≫ B := by
    simp only [A, B]
    rw [← horn.ι_ι (n := 0) 1 0 (by decide), ← Category.id_comp (𝟙 (∂Δ[n] : SSet)),
      join.map_comp_assoc, hpush.w_assoc]
    simp only [← join.map_comp_assoc, Category.id_comp, Category.comp_id, e]
  obtain ⟨L, hL₁, hL₂, hL₃⟩ := hf.exists_lift_join A B C hA hB hw
    (by simp only [A, Category.assoc, hφ, Subcomplex.unionJoin.ι₁_ι_assoc])
    (by simp only [B, Category.assoc, hφ, Subcomplex.unionJoin.ι₂_ι_assoc, ← he,
      ← join.map_comp_assoc, Category.id_comp])
  -- The lift `L : Δ[n] ⋆ Δ[1] ⟶ X` extends `φ`, hence is a filler of the horn.
  have hL : (Subcomplex.unionJoin ∂Δ[n] Λ[1, 1]).ι ≫ L = φ := by
    refine hpush.hom_ext ?_ ?_
    · rw [Subcomplex.unionJoin.ι₁_ι_assoc, hL₁]
    · rw [Subcomplex.unionJoin.ι₂_ι_assoc, hΛ, ← Category.id_comp (𝟙 (Δ[n] : SSet)),
        join.map_comp_assoc, hL₂]
      simp only [B]
      rw [← join.map_comp_assoc, Category.id_comp, hte, join.map_id, Category.id_comp]
  refine ⟨(join.stdSimplexIso n 1).inv ≫ L, ?_, ?_⟩
  · rw [← Subcomplex.isoOfPreimageEq_inv_ι_assoc (join.stdSimplexIso n 1)
      (preimage_unionJoin_eq n), hL, ← unionJoinIso, Iso.inv_hom_id_assoc]
  · rw [Category.assoc, hL₃, Iso.inv_hom_id_assoc]

/-- **An edge `f : x ⟶ y` of a quasicategory is an equivalence exactly when the restriction of
cones `X_{/f} ⟶ X_{/y}` is a trivial fibration**, that is, has the right lifting property with
respect to every monomorphism. -/
theorem isEquivalence_iff_rlp_slice_map [Quasicategory X] (f : Edge x y) :
    f.IsEquivalence ↔ (monomorphisms SSet.{u}).rlp (slice.map (stdSimplex.δ 0) (𝟙 X) (by simp) :
      slice (yonedaEquiv.symm f.edge) ⟶ slice (stdSimplex.δ 0 ≫ yonedaEquiv.symm f.edge)) := by
  refine ⟨fun hf ↦ ?_, fun H ↦ ?_⟩
  · rw [isEquivalence_iff_hornFilling_last] at hf
    rw [rlp_monomorphisms]
    exact fun _ _ _ ⟨n⟩ ↦ hasLiftingProperty_of_hornFilling f.edge (hf n)
  · -- Over the terminal `Δ[0]`, the lifting property makes `f` Cartesian, and Cartesian edges
    -- fill the horns `Λ[n + 2, n + 2]` with final edge `f`.
    have hf : f.IsCartesian (stdSimplex.isTerminalObj₀.from X) :=
      (isCartesian_iff_rlp_slice_map f _ stdSimplex.isTerminalObj₀).2 H
    rw [isEquivalence_iff_hornFilling_last]
    intro n σ₀ hσ₀
    obtain ⟨σ, hσ, -⟩ := hf.exists_lift_horn_last σ₀ hσ₀ (stdSimplex.isTerminalObj₀.from _)
      (stdSimplex.isTerminalObj₀.hom_ext _ _)
    exact ⟨σ, hσ.symm⟩

/-- **An edge of a quasicategory is an equivalence exactly when it is Cartesian over a point**
(HTT Proposition 2.4.1.5 over a point): for the map `p` to a terminal simplicial set, the
`p`-Cartesian edges are the equivalences. -/
theorem isEquivalence_iff_isCartesian [Quasicategory X] (f : Edge x y) {S : SSet.{u}}
    (p : X ⟶ S) (hS : IsTerminal S) : f.IsEquivalence ↔ f.IsCartesian p := by
  rw [isEquivalence_iff_rlp_slice_map, isCartesian_iff_rlp_slice_map f p hS]

/-- Every edge of a Kan complex, for example of the nerve of a groupoid, is Cartesian over a
point. -/
lemma isCartesian_of_kanComplex [KanComplex X] (f : Edge x y) {S : SSet.{u}} (p : X ⟶ S)
    (hS : IsTerminal S) : f.IsCartesian p :=
  (isEquivalence_iff_isCartesian f p hS).1 (isEquivalence_of_kanComplex f)

end Edge

namespace stdSimplex

/-- An edge of `Δ[n]` from a vertex `a` to a vertex `b > a`, such as the edge from `0` to `1` of
`Δ[1]`, is not Cartesian over a point: it has no inverse. -/
lemma not_isCartesian_of_lt {n : ℕ} {a b : Fin (n + 1)} (hab : a < b)
    (f : Edge (obj₀Equiv.{u}.symm a) (obj₀Equiv.symm b)) {S : SSet.{u}} (p : Δ[n] ⟶ S)
    (hS : IsTerminal S) : ¬ f.IsCartesian p := fun h ↦
  hab.not_ge ((nonempty_edge_iff b a).1
    ⟨((Edge.isEquivalence_iff_isCartesian f p hS).2 h).invStruct.inv⟩)

end stdSimplex

end SSet

namespace CategoryTheory.nerve

open SSet

variable {C : Type u} [Category.{v} C]

/-- An edge of the nerve of a category is Cartesian over a point exactly when the corresponding
morphism is an isomorphism. -/
lemma isCartesian_edgeMk_iff {x y : C} (f : x ⟶ y) {S : SSet.{max u v}} (p : nerve C ⟶ S)
    (hS : IsTerminal S) : (edgeMk f).IsCartesian p ↔ IsIso f :=
  (Edge.isEquivalence_iff_isCartesian (edgeMk f) p hS).symm.trans (isEquivalence_edgeMk_iff f)

end CategoryTheory.nerve
