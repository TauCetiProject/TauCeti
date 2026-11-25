/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.HomotopyCategory.MappingCone
public import TauCeti.Algebra.Homology.HomotopyCofiber
public import TauCeti.Algebra.Homology.ShortComplex.Splitting
public import TauCeti.KnotTheory.Khovanov.Resolution.AdjoinCircle
public import TauCeti.KnotTheory.Khovanov.Resolution.Reindex
public import TauCeti.KnotTheory.Khovanov.Resolution.Skein
public import TauCeti.KnotTheory.PDCode.Reidemeister.One.Planar
public import TauCeti.KnotTheory.PDCode.Reidemeister.One.ResolveCrossing

/-!
# The unnormalized Khovanov complex under the first Reidemeister move

Let `D` be a planar PD-code and `D' = D.reidemeisterOne h b` the code obtained by inserting a kink
into the arc of `D` ending at the half-edge `h`, with new crossing `c = Fin.last n`. The smoothing
`b` of `c` cuts off the loop of the kink, so the two resolutions of `D'` at `c` are `D` and `D`
with an adjoined crossing-free circle `O` (`TauCeti.PDCode.resolveCrossing_reidemeisterOne_last_not`
and `TauCeti.PDCode.resolveCrossing_reidemeisterOne_last_self`). This file shows that, in every
quantum degree, the unnormalized Khovanov complex `⟦D'⟧` is homotopy equivalent to a shift of
`⟦D⟧`:

* for `b = true`, `⟦D'⟧ʲ ≃ ⟦D⟧ʲ⁺¹`
  (`TauCeti.PDCode.khovanovBracketReidemeisterOneTrueHomotopyEquiv`);
* for `b = false`, `⟦D'⟧ʲ ≃ ⟦D⟧ʲ⁻²⟦-1⟧`, that is, with the cochain degree raised by one
  (`TauCeti.PDCode.khovanovBracketReidemeisterOneFalseHomotopyEquiv`).

By the skein mapping cone (`TauCeti.PDCode.khovanovBracketMappingConeIso`), `⟦D'⟧ʲ⟦1⟧` is the
mapping cone of the saddle map `⟦D'_A⟧ʲ ⟶ ⟦D'_B⟧ʲ⁻¹` at `c`. The complex of the resolution with
the loop splits as the direct sum of two copies of the complex of `D`, for the labels `1` and `X`
of the loop (`TauCeti.PDCode.khovanovBracketAdjoinCircleIso`). The loop passes through `c`, so the
saddle merges it into the circle of the arc carrying the kink, or splits it off that circle, and is
a relabelling of circles on every other circle.

* For `b = true` the saddle is the merge from the `A`-resolution `D ⊔ O` to `D`. A birth labelled
  `1` followed by this merge relabels the circles, so the saddle is an isomorphism on the summand
  with the loop labelled `1`. By Gaussian elimination
  (`CategoryTheory.ShortComplex.Splitting.ofIsIsoInlComp`) the saddle is a split epimorphism whose
  kernel is the summand with the loop labelled `X`, and its mapping cone is that summand shifted by
  one (`CategoryTheory.ShortComplex.Splitting.mappingConeGHomotopyEquiv`).
* For `b = false` the saddle is the split from `D` to the `B`-resolution `D ⊔ O`. This split
  followed by the death of the loop, reading off the coefficient of `X`, relabels the circles. By
  Gaussian elimination (`CategoryTheory.ShortComplex.Splitting.ofIsIsoCompSnd`) the saddle is a
  split monomorphism whose cokernel is the summand with the loop labelled `1`, and its mapping cone
  is that summand (`CategoryTheory.ShortComplex.Splitting.homotopyCofiberHomotopyEquiv`).

The splittings are constructed on the cubes of resolutions and carried to the complexes by the
additive totalization functor. The identifications of the cubes of the resolutions of `D'` with
those of `D` and `D ⊔ O` keep the crossings
(`TauCeti.PDCode.ResolutionEquiv.resolutionCubeNatIso`). The combinatorial input is that the
saddle correspondence at `c`, restricted to the circles of `D`, is injective, since the loop of the
kink passes through `c` and two circles pass through `c` on the face where it is cut off.

## Main definitions

* `TauCeti.PDCode.khovanovBracketReidemeisterOneTrueHomotopyEquiv`: `⟦D.reidemeisterOne h true⟧ʲ`
  is homotopy equivalent to `⟦D⟧ʲ⁺¹`.
* `TauCeti.PDCode.khovanovBracketReidemeisterOneFalseHomotopyEquiv`:
  `⟦D.reidemeisterOne h false⟧ʲ` is homotopy equivalent to `⟦D⟧ʲ⁻²⟦-1⟧`.

## References

* M. Khovanov, *A categorification of the Jones polynomial*, Duke Math. J. 101 (2000), §5.2
  (invariance under the first Reidemeister move).
* D. Bar-Natan, *On Khovanov's categorification of the Jones polynomial*,
  Algebr. Geom. Topol. 2 (2002), §3.5.
* D. Bar-Natan, *Fast Khovanov homology computations*, J. Knot Theory Ramifications 16 (2007),
  243--255, Lemma 4.2 (Gaussian elimination).
-/

public section

noncomputable section

open CategoryTheory Limits Finset PiTensorProduct DualNumber CochainComplex

namespace TauCeti.PDCode

universe u v

variable {n : ℕ} (D : PDCode n) (h : Fin (4 * n)) (b : Bool)

/-! ### The circles of the two faces of the kink -/

section Circles

private theorem apply_self_crossingEquiv (s : Fin n → Bool) (i : Fin n) :
    s ((ResolutionEquiv.resolveCrossingReidemeisterOneSelf D h b).crossingEquiv i) = s i := by
  simp

/-- The circles of `D` smoothed at the vertex `S`, together with the loop of the kink, as the
circles of the kink diagram at the vertex over `S` on the face `b`, where the smoothing of the new
crossing cuts off the loop. -/
private def kinkLoopCircleEquiv (S : Finset (Fin n)) :
    D.ResolvedCircle (cubeState S) ⊕ Unit ≃
      (D.reidemeisterOne h b).ResolvedCircle
        (cubeState (resolveCrossingVertex (Fin.last n) b S)) :=
  (D.adjoinCircleResolvedCircleEquiv (cubeState S)).symm.trans
    ((((ResolutionEquiv.resolveCrossingReidemeisterOneSelf D h b).smoothingEquiv
      (apply_self_crossingEquiv D h b (cubeState S))).resolvedCircleCongr).trans
      ((D.reidemeisterOne h b).resolveCrossingCubeCircleEquiv (Fin.last n) b S))

/-- The circles of `D` smoothed at the vertex `S`, as the circles of the kink diagram at the vertex
over `S` on the face `!b`, where the smoothing of the new crossing runs along the kink. -/
private def kinkCircleEquiv (S : Finset (Fin n)) :
    D.ResolvedCircle (cubeState S) ≃
      (D.reidemeisterOne h b).ResolvedCircle
        (cubeState (resolveCrossingVertex (Fin.last n) (!b) S)) :=
  (((ResolutionEquiv.resolveCrossingReidemeisterOneNot D h b).smoothingEquiv fun i ↦ by
      simp).resolvedCircleCongr).trans
    ((D.reidemeisterOne h b).resolveCrossingCubeCircleEquiv (Fin.last n) (!b) S)

/-- The loop of the kink passes through the new crossing. -/
private theorem kinkLoopCircleEquiv_inr (S : Finset (Fin n)) :
    D.kinkLoopCircleEquiv h b S (.inr ()) =
        .inl ⟦(D.reidemeisterOne h b).crossing (Fin.last n) 0⟧ ∨
      D.kinkLoopCircleEquiv h b S (.inr ()) =
        .inl ⟦(D.reidemeisterOne h b).crossing (Fin.last n) 2⟧ := by
  have hk : (ResolutionEquiv.resolveCrossingReidemeisterOneSelf D h b).crossinglessEquiv
      (Fin.cast (adjoinCircle_crossinglessComponentCount D).symm
        (Fin.last D.crossinglessComponentCount)) =
      (Fin.natAdd (D.reidemeisterOne h b).crossinglessComponentCount
        ⟨0, by simp [detachedCircleCount_reidemeisterOne_last]⟩).cast
        ((D.reidemeisterOne h b).resolveCrossing_crossinglessComponentCount (Fin.last n)
          b).symm := by
    ext
    simp
  simp only [kinkLoopCircleEquiv, Equiv.trans_apply, adjoinCircleResolvedCircleEquiv_symm_inr,
    SmoothingEquiv.resolvedCircleCongr_inr, ResolutionEquiv.smoothingEquiv_crossinglessEquiv, hk,
    resolveCrossingCubeCircleEquiv_inr_natAdd]
  split_ifs <;> simp

private theorem cubeState_resolveCrossingVertex_last_eq (S : Finset (Fin n)) (t t' : Bool)
    (j : Fin (n + 1)) (hj : j ≠ Fin.last n) :
    cubeState (resolveCrossingVertex (Fin.last n) t S) j =
      cubeState (resolveCrossingVertex (Fin.last n) t' S) j := by
  obtain ⟨k, rfl⟩ := Fin.exists_succAbove_eq hj
  simp [cubeState_resolveCrossingVertex]

/-- On the face `b`, where the loop of the kink is cut off, two circles pass through the new
crossing: the loop and the circle of the arc carrying the kink. -/
private theorem card_circlesAt_kink (S : Finset (Fin n)) :
    #((D.reidemeisterOne h b).circlesAt (cubeState (resolveCrossingVertex (Fin.last n) b S))
      (Fin.last n)) = 2 := by
  have hloop := (D.reidemeisterOne h b).stateLoopCount_add_card_circlesAt
    (cubeState_resolveCrossingVertex_last_eq S b (!b))
  have h₁ := Fintype.card_congr (D.kinkLoopCircleEquiv h b S)
  have h₂ := Fintype.card_congr (D.kinkCircleEquiv h b S)
  have e : Fintype.card (D.ResolvedCircle (cubeState S) ⊕ Unit) =
      D.stateLoopCount (cubeState S) + 1 := by
    rw [Fintype.card_sum, card_resolvedCircle, Fintype.card_unit]
  rw [e, card_resolvedCircle] at h₁
  rw [card_resolvedCircle, card_resolvedCircle] at h₂
  have := (D.reidemeisterOne h b).card_circlesAt_le_two
    (cubeState (resolveCrossingVertex (Fin.last n) b S)) (Fin.last n)
  have := ((D.reidemeisterOne h b).circlesAt_nonempty
    (cubeState (resolveCrossingVertex (Fin.last n) (!b) S)) (Fin.last n)).card_pos
  omega

/-- The saddle correspondence at the new crossing, from the face `b` to the face `!b`, is
injective on the circles of `D`: it only merges the loop of the kink into the circle of its
arc. -/
private theorem injective_saddleResolvedCircleMap_kinkLoopCircleEquiv_inl (S : Finset (Fin n))
    (hst : ∀ j, j ≠ Fin.last n → cubeState (resolveCrossingVertex (Fin.last n) b S) j =
      cubeState (resolveCrossingVertex (Fin.last n) (!b) S) j)
    (ht : #((D.reidemeisterOne h b).circlesAt
      (cubeState (resolveCrossingVertex (Fin.last n) (!b) S)) (Fin.last n)) = 1) :
    Function.Injective ((D.reidemeisterOne h b).saddleResolvedCircleMap hst ht ∘
      D.kinkLoopCircleEquiv h b S ∘ Sum.inl) := by
  intro x y hxy
  set e := D.kinkLoopCircleEquiv h b S
  refine Sum.inl_injective (e.injective ?_)
  rcases ((D.reidemeisterOne h b).saddleResolvedCircleMap_eq_iff hst ht _ _).1 hxy with
    hxy | ⟨hx, hy⟩
  · exact hxy
  have hox : e (.inl x) ≠ e (.inr ()) := e.injective.ne Sum.inl_ne_inr
  have hoy : e (.inl y) ≠ e (.inr ()) := e.injective.ne Sum.inl_ne_inr
  rcases D.kinkLoopCircleEquiv_inr h b S with ho | ho <;> rw [ho] at hox hoy <;>
    rcases hx with hx | hx <;> rcases hy with hy | hy <;>
    first | exact absurd hx hox | exact absurd hy hoy | exact hx.trans hy.symm

/-- The circles of `D` at `S`, carried across the saddle at the new crossing and back. -/
private def kinkSaddleCircleMap (S : Finset (Fin n))
    (hst : ∀ j, j ≠ Fin.last n → cubeState (resolveCrossingVertex (Fin.last n) b S) j =
      cubeState (resolveCrossingVertex (Fin.last n) (!b) S) j)
    (ht : #((D.reidemeisterOne h b).circlesAt
      (cubeState (resolveCrossingVertex (Fin.last n) (!b) S)) (Fin.last n)) = 1) :
    D.ResolvedCircle (cubeState S) → D.ResolvedCircle (cubeState S) :=
  (D.kinkCircleEquiv h b S).symm ∘ (D.reidemeisterOne h b).saddleResolvedCircleMap hst ht ∘
    D.kinkLoopCircleEquiv h b S ∘ Sum.inl

private theorem bijective_kinkSaddleCircleMap (S : Finset (Fin n))
    (hst : ∀ j, j ≠ Fin.last n → cubeState (resolveCrossingVertex (Fin.last n) b S) j =
      cubeState (resolveCrossingVertex (Fin.last n) (!b) S) j)
    (ht : #((D.reidemeisterOne h b).circlesAt
      (cubeState (resolveCrossingVertex (Fin.last n) (!b) S)) (Fin.last n)) = 1) :
    Function.Bijective (D.kinkSaddleCircleMap h b S hst ht) :=
  Finite.injective_iff_bijective.1 <| (D.kinkCircleEquiv h b S).symm.injective.comp
    (D.injective_saddleResolvedCircleMap_kinkLoopCircleEquiv_inl h b S hst ht)

end Circles

/-! ### A helper for isomorphisms of cubes -/

/-- A map of cubes of resolutions of `D` which on every vertex reindexes the circle tensor along a
bijection of the resolved circles is an isomorphism. -/
private theorem isIso_of_app_comp_resolutionCubeι {D : PDCode n} {hD : D.IsPlanar} {R : Type u}
    [CommRing R] {k : ℤ} (τ : D.resolutionCube hD R k ⟶ D.resolutionCube hD R k)
    (e : ∀ S : Finset (Fin n), D.ResolvedCircle (cubeState S) ≃ D.ResolvedCircle (cubeState S))
    (hτ : ∀ S, τ.app S ≫ D.resolutionCubeι hD R k S =
      D.resolutionCubeι hD R k S ≫ ModuleCat.ofHom (reindex R (fun _ ↦ R[ε]) (e S)).toLinearMap) :
    IsIso τ := by
  have (S : Finset (Fin n)) : IsIso (τ.app S) := by
    have hS : τ.app S = (D.resolutionCubeObjCongr hD R k hD (e S) rfl).toModuleIso.hom := by
      rw [← cancel_mono (D.resolutionCubeι hD R k S), hτ]
      ext x
      exact (D.resolutionCubeι_resolutionCubeObjCongr hD R k hD (e S) rfl x).symm
    rw [hS]
    infer_instance
  exact NatIso.isIso_of_isIso_app τ

/-! ### Composites of reindexings, saddles, births and deaths -/

section Composite

variable {R : Type u} [CommRing R] {σ ρ τ σ' : Type*}

/-- Reindexing circle tensors along `e₂` factors through reindexing along any `e₁`. -/
private theorem ofHom_reindex_eq_comp {α β γ : Type v} (e₁ : α ≃ β) (e₂ : α ≃ γ) :
    ModuleCat.ofHom (X := ModuleCat.of R (Khovanov.CircleTensor R α))
        (Y := ModuleCat.of R (Khovanov.CircleTensor R γ))
        (reindex R (fun _ ↦ R[ε]) e₂).toLinearMap =
      ModuleCat.ofHom (Y := ModuleCat.of R (Khovanov.CircleTensor R β))
          (reindex R (fun _ ↦ R[ε]) e₁).toLinearMap ≫
        ModuleCat.ofHom (reindex R (fun _ ↦ R[ε]) (e₁.symm.trans e₂)).toLinearMap := by
  have he : e₁.trans (e₁.symm.trans e₂) = e₂ := by
    rw [← Equiv.trans_assoc, Equiv.self_trans_symm, Equiv.refl_trans]
  rw [← ModuleCat.ofHom_comp, ← LinearEquiv.coe_trans, reindex_trans, he]

/-- A birth labelled `1`, reindexings and a merge compose to the merge along the composite of
the circle maps. -/
private theorem reindex_fiberwiseMul_reindex_insertCircle [Fintype σ] [Fintype ρ] [Finite τ]
    [DecidableEq τ] [DecidableEq σ'] (b : σ ⊕ Unit ≃ ρ) (g : ρ → τ) (a : τ ≃ σ')
    (x : Khovanov.CircleTensor R σ) :
    reindex R (fun _ ↦ R[ε]) a (fiberwiseMul (A := fun _ ↦ R[ε]) g
      (reindex R (fun _ ↦ R[ε]) b (Khovanov.insertCircle R false x))) =
      fiberwiseMul (A := fun _ ↦ R[ε]) (a ∘ g ∘ b ∘ Sum.inl) x := by
  classical
  have := Fintype.ofFinite τ
  rw [Khovanov.insertCircle_false, AlgHom.toLinearMap_apply,
    ← fiberwiseMul_equiv_apply, ← fiberwiseMul_equiv_apply]
  simp only [← AlgHom.comp_apply, fiberwiseMul_comp]

/-- Reindexings, a split and a death of the label `X` compose to the split along the composite of
the circle maps. -/
private theorem deleteCircle_reindex_fiberwiseSplit_reindex [Fintype σ] [Fintype ρ] [Fintype τ]
    [DecidableEq τ] [Fintype σ'] [DecidableEq σ'] (a : τ ≃ σ') (g : ρ → τ) (b : σ ⊕ Unit ≃ ρ)
    (x : Khovanov.CircleTensor R σ') :
    Khovanov.deleteCircle R true (reindex R (fun _ ↦ R[ε]) b.symm
      (Khovanov.fiberwiseSplit g (reindex R (fun _ ↦ R[ε]) a.symm x))) =
      Khovanov.fiberwiseSplit (a ∘ g ∘ b ∘ Sum.inl) x := by
  classical
  rw [Khovanov.deleteCircle_true, ← Khovanov.fiberwiseSplit_equiv_apply,
    ← Khovanov.fiberwiseSplit_equiv_apply]
  simp only [← LinearMap.comp_apply, Khovanov.fiberwiseSplit_comp, Function.comp_assoc]

end Composite

/-! ### The resolution of the kink which cuts off the loop -/

section Kink

variable (hD : D.IsPlanar) (R : Type u) [CommRing R]

private theorem hc (S : Finset (Fin n)) :
    cubeState (resolveCrossingVertex (Fin.last n) b S) (Fin.last n) ≠
      cubeState (resolveCrossingVertex (Fin.last n) (!b) S) (Fin.last n) := by
  rw [cubeState_resolveCrossingVertex, cubeState_resolveCrossingVertex]
  cases b <;> simp

/-- On the face `!b`, where the smoothing of the new crossing runs along the kink, one circle
passes through the new crossing. -/
private theorem ht (S : Finset (Fin n)) :
    #((D.reidemeisterOne h b).circlesAt (cubeState (resolveCrossingVertex (Fin.last n) (!b) S))
      (Fin.last n)) = 1 :=
  (D.reidemeisterOne h b).card_circlesAt_eq_one_of_card_circlesAt_eq_two
    (cubeState_resolveCrossingVertex_last_eq S b (!b)) (hc b S) (D.card_circlesAt_kink h b S)

/-- The cube of `D` as the cube of the resolution `!b` of the kink `D.reidemeisterOne h b`, which
runs along the kink. -/
private def kinkNotIso (k : ℤ) :
    D.resolutionCube hD R k ≅
      ((D.reidemeisterOne h b).resolveCrossing (Fin.last n) (!b)).resolutionCube
        (((isPlanar_reidemeisterOne D h b).2 hD).resolveCrossing _ _ (!b)) R k :=
  (ResolutionEquiv.resolveCrossingReidemeisterOneNot D h b).resolutionCubeNatIso (by simp) hD _ R k

/-- The cube of `D` with an adjoined circle as the cube of the resolution `b` of the kink
`D.reidemeisterOne h b`, which cuts off the loop. -/
private def kinkSelfIso (k : ℤ) :
    D.adjoinCircle.resolutionCube ((isPlanar_adjoinCircle_iff D).2 hD) R k ≅
      ((D.reidemeisterOne h b).resolveCrossing (Fin.last n) b).resolutionCube
        (((isPlanar_reidemeisterOne D h b).2 hD).resolveCrossing _ _ b) R k :=
  (ResolutionEquiv.resolveCrossingReidemeisterOneSelf D h b).resolutionCubeNatIso (by simp) _ _
    R k

/-- The cube of the resolution `b` of the kink `D.reidemeisterOne h b`, which cuts off the loop, is
the biproduct of two copies of the cube of `D`, for the labels `1` and `X` of the loop: the
biproduct decomposition of the cube of `D.adjoinCircle`, transported along `kinkSelfIso`.
It is reducible so that its point is reducibly the target of the saddle map of the kink when
`b = false`, which instance search needs for the invertibility of the saddle followed by `snd`. -/
@[reducible] private def kinkBicone {k k₀ k₁ : ℤ} (h₀ : k = k₀ + 1) (h₁ : k = k₁ - 1) :
    BinaryBicone (D.resolutionCube hD R k₀) (D.resolutionCube hD R k₁) where
  pt := ((D.reidemeisterOne h b).resolveCrossing (Fin.last n) b).resolutionCube
    (((isPlanar_reidemeisterOne D h b).2 hD).resolveCrossing _ _ b) R k
  fst := (D.kinkSelfIso h b hD R k).inv ≫ D.adjoinCircleCubeDelete hD R false (by simpa using h₀)
  snd := (D.kinkSelfIso h b hD R k).inv ≫
    D.adjoinCircleCubeDelete hD R true (by simpa [← sub_eq_add_neg] using h₁)
  inl := D.adjoinCircleCubeInsert hD R false (by simpa using h₀) ≫ (D.kinkSelfIso h b hD R k).hom
  inr := D.adjoinCircleCubeInsert hD R true (by simpa [← sub_eq_add_neg] using h₁) ≫
    (D.kinkSelfIso h b hD R k).hom
  inl_fst := by simp
  inl_snd := by simp
  inr_fst := by simp
  inr_snd := by simp

private theorem kinkBicone_total {k k₀ k₁ : ℤ} (h₀ : k = k₀ + 1) (h₁ : k = k₁ - 1) :
    (D.kinkBicone h b hD R h₀ h₁).fst ≫ (D.kinkBicone h b hD R h₀ h₁).inl +
      (D.kinkBicone h b hD R h₀ h₁).snd ≫ (D.kinkBicone h b hD R h₀ h₁).inr = 𝟙 _ := by
  have key := (D.kinkSelfIso h b hD R k).inv ≫=
    D.adjoinCircleCubeDelete_comp_adjoinCircleCubeInsert_add hD R h₀ h₁ =≫
      (D.kinkSelfIso h b hD R k).hom
  simp only [Preadditive.add_comp, Preadditive.comp_add, Category.assoc, Category.id_comp,
    Iso.inv_hom_id] at key
  -- Unfolded, the goal is `key` up to the proofs of the degree equations.
  simp only [kinkBicone, Category.assoc]
  exact key

end Kink

/-! ### The merge at a kink whose `A`-smoothing cuts off the loop -/

section Merge

variable (hD : D.IsPlanar) (R : Type u) [CommRing R] (j : ℤ)

/-- The saddle at the kink, restricted to the summand with the loop labelled `1` and read on the
cube of `D`. -/
private def kinkMergeTrue : D.resolutionCube hD R (j - 1) ⟶ D.resolutionCube hD R (j - 1) :=
  D.adjoinCircleCubeInsert hD R false (j := j) (j' := j - 1) (by simp) ≫
    (D.kinkSelfIso h true hD R j).hom ≫
      (D.reidemeisterOne h true).resolveCrossingSaddle (Fin.last n)
        ((isPlanar_reidemeisterOne D h true).2 hD) R j ≫ (D.kinkNotIso h true hD R (j - 1)).inv

private theorem kinkMergeTrue_app_comp_resolutionCubeι (S : Finset (Fin n)) :
    (D.kinkMergeTrue h hD R j).app S ≫ D.resolutionCubeι hD R (j - 1) S =
      D.resolutionCubeι hD R (j - 1) S ≫ ModuleCat.ofHom
        (fiberwiseMul (A := fun _ ↦ R[ε]) (D.kinkSaddleCircleMap h true S
          (cubeState_resolveCrossingVertex_last_eq S true false) (D.ht h true S))).toLinearMap := by
  have hs := D.card_circlesAt_kink h true S
  -- The saddle lands in the resolution `false`, which `kinkNotIso` writes as `!true`.
  have hsad : ((D.reidemeisterOne h true).resolveCrossingSaddle (Fin.last n)
      ((isPlanar_reidemeisterOne D h true).2 hD) R j).app S ≫
        ((D.reidemeisterOne h true).resolveCrossing (Fin.last n) (!true)).resolutionCubeι
          (((isPlanar_reidemeisterOne D h true).2 hD).resolveCrossing _ _ (!true)) R (j - 1) S ≫
          ModuleCat.ofHom (reindex R (fun _ ↦ R[ε])
            ((D.reidemeisterOne h true).resolveCrossingCubeCircleEquiv (Fin.last n) (!true)
              S)).toLinearMap = _ :=
    (D.reidemeisterOne h true).resolveCrossingSaddle_app_comp_resolutionCubeι
      (Fin.last n) ((isPlanar_reidemeisterOne D h true).2 hD) R j S
      (cubeState_resolveCrossingVertex_last_eq S true false) (hc true S) (Or.inl hs)
  rw [resolutionEdgeMap_eq_resolutionMergeMap _ _ _ _ _ hs, resolutionMergeMap_def] at hsad
  unfold kinkMergeTrue
  simp only [NatTrans.comp_app, Category.assoc]
  rw [kinkNotIso, ResolutionEquiv.resolutionCubeNatIso_inv_app_comp_resolutionCubeι _ _ _ _ _ _
    _ (by simp), ofHom_reindex_eq_comp
      ((D.reidemeisterOne h true).resolveCrossingCubeCircleEquiv (Fin.last n) (!true) S)]
  rw [reassoc_of% hsad, kinkSelfIso,
    ResolutionEquiv.resolutionCubeNatIso_hom_app_comp_resolutionCubeι_assoc _ _ _ _ _ _ _
      (by simp), adjoinCircleCubeInsert_app_comp_resolutionCubeι_assoc]
  congr 1
  refine ModuleCat.hom_ext (LinearMap.ext fun x ↦ ?_)
  simp only [ModuleCat.hom_comp, ModuleCat.hom_ofHom, LinearMap.comp_apply,
    AlgHom.toLinearMap_apply]
  rw [kinkSaddleCircleMap, ← reindex_fiberwiseMul_reindex_insertCircle]
  simp [kinkCircleEquiv, kinkLoopCircleEquiv, adjoinCircleInsert_apply, ← reindex_reindex]

private instance isIso_kinkMergeTrue : IsIso (D.kinkMergeTrue h hD R j) :=
  isIso_of_app_comp_resolutionCubeι _
    (fun S ↦ Equiv.ofBijective _ (D.bijective_kinkSaddleCircleMap h true S
      (cubeState_resolveCrossingVertex_last_eq S true false) (D.ht h true S)))
    fun S ↦ by
      rw [kinkMergeTrue_app_comp_resolutionCubeι, ← toLinearMap_fiberwiseMul_equiv]

/-- On the summand with the loop labelled `1`, the saddle at the kink is `kinkMergeTrue`. -/
private theorem kinkBicone_inl_comp_resolveCrossingSaddle_true :
    (D.kinkBicone h true hD R (sub_add_cancel j 1).symm (add_sub_cancel_right j 1).symm).inl ≫
        (D.reidemeisterOne h true).resolveCrossingSaddle (Fin.last n)
          ((isPlanar_reidemeisterOne D h true).2 hD) R j =
      D.kinkMergeTrue h hD R j ≫ (D.kinkNotIso h true hD R (j - 1)).hom := by
  simp [kinkBicone, kinkMergeTrue]

private instance isIso_kinkBicone_inl_comp_resolveCrossingSaddle_true :
    IsIso ((D.kinkBicone h true hD R (sub_add_cancel j 1).symm
        (add_sub_cancel_right j 1).symm).inl ≫
      (D.reidemeisterOne h true).resolveCrossingSaddle (Fin.last n)
        ((isPlanar_reidemeisterOne D h true).2 hD) R j) := by
  rw [kinkBicone_inl_comp_resolveCrossingSaddle_true]
  infer_instance

/-- The skein sequence at the kink, split at the cube level by the summand with the loop
labelled `1`. -/
private def kinkSplittingTrue :=
  ShortComplex.Splitting.ofIsIsoInlComp
    (D.kinkBicone h true hD R (sub_add_cancel j 1).symm (add_sub_cancel_right j 1).symm)
    (D.kinkBicone_total h true hD R _ _)
    ((D.reidemeisterOne h true).resolveCrossingSaddle (Fin.last n)
      ((isPlanar_reidemeisterOne D h true).2 hD) R j)

/-- **The first Reidemeister move, cutting off the loop by the `A`-smoothing.** For the kink
`D.reidemeisterOne h true` inserted into an arc of a planar code `D`, whose `A`-smoothing cuts off
the loop, the degree-`j` component of the unnormalized Khovanov complex is homotopy equivalent to
the degree-`j + 1` component of that of `D`, with no shift of the cochain degree. -/
def khovanovBracketReidemeisterOneTrueHomotopyEquiv :
    HomotopyEquiv
      ((D.reidemeisterOne h true).khovanovBracket ((isPlanar_reidemeisterOne D h true).2 hD) R j)
      (D.khovanovBracket hD R (j + 1)) :=
  let e : HomotopyEquiv
      (((D.reidemeisterOne h true).khovanovBracket ((isPlanar_reidemeisterOne D h true).2 hD) R
        j)⟦(1 : ℤ)⟧) ((D.khovanovBracket hD R (j + 1))⟦(1 : ℤ)⟧) :=
    (HomotopyEquiv.ofIso ((D.reidemeisterOne h true).khovanovBracketMappingConeIso (Fin.last n)
      _ R j).symm).trans
      (((D.kinkSplittingTrue h hD R j).map (cubeComplexFunctor (ModuleCat.{u} R) (Fin n))
        ).mappingConeGHomotopyEquiv.trans (HomotopyEquiv.ofIso
          ((CategoryTheory.shiftFunctor _ (1 : ℤ)).mapIso
            (eqToIso (D.khovanovBracket_apply hD R (j + 1)).symm))))
  (HomotopyEquiv.ofIso ((shiftFunctorCompIsoId _ (1 : ℤ) (-1) (by norm_num)).app _).symm).trans
    ((e.shift (-1)).trans
      (HomotopyEquiv.ofIso ((shiftFunctorCompIsoId _ (1 : ℤ) (-1) (by norm_num)).app _)))

end Merge

/-! ### The split at a kink whose `B`-smoothing cuts off the loop -/

private theorem sub_one_eq_sub_two_add_one (j : ℤ) : j - 1 = j - 2 + 1 := by
  ring

section Split

variable (hD : D.IsPlanar) (R : Type u) [CommRing R] (j : ℤ)

/-- The saddle at the kink, followed by the coefficient of the label `X` on the loop, read on the
cube of `D`. -/
private def kinkSplitFalse : D.resolutionCube hD R j ⟶ D.resolutionCube hD R j :=
  (D.kinkNotIso h false hD R j).hom ≫
    (D.reidemeisterOne h false).resolveCrossingSaddle (Fin.last n)
      ((isPlanar_reidemeisterOne D h false).2 hD) R j ≫
      (D.kinkSelfIso h false hD R (j - 1)).inv ≫
        D.adjoinCircleCubeDelete hD R true (j := j - 1) (j' := j) (by simp [sub_eq_add_neg])

private theorem kinkSplitFalse_app_comp_resolutionCubeι (S : Finset (Fin n)) :
    (D.kinkSplitFalse h hD R j).app S ≫ D.resolutionCubeι hD R j S =
      D.resolutionCubeι hD R j S ≫ ModuleCat.ofHom
        (Khovanov.fiberwiseSplit (D.kinkSaddleCircleMap h false S
          (cubeState_resolveCrossingVertex_last_eq S false true) (D.ht h false S))) := by
  have hs := D.card_circlesAt_kink h false S
  -- The saddle starts from the resolution `true`, which `kinkNotIso` writes as `!false`.
  have hsad : _ =
      ((D.reidemeisterOne h false).resolveCrossing (Fin.last n) (!false)).resolutionCubeι
          (((isPlanar_reidemeisterOne D h false).2 hD).resolveCrossing _ _ (!false)) R j S ≫
        ModuleCat.ofHom (reindex R (fun _ ↦ R[ε])
          ((D.reidemeisterOne h false).resolveCrossingCubeCircleEquiv (Fin.last n) (!false)
            S)).toLinearMap ≫
          ModuleCat.ofHom ((D.reidemeisterOne h false).resolutionEdgeMap _ _ _ R) :=
    (D.reidemeisterOne h false).resolveCrossingSaddle_app_comp_resolutionCubeι
      (Fin.last n) ((isPlanar_reidemeisterOne D h false).2 hD) R j S
      (cubeState_resolveCrossingVertex_last_eq S true false) (hc true S) (Or.inr hs)
  rw [resolutionEdgeMap_eq_resolutionSplitMap _ _ _ _ _ hs, resolutionSplitMap_def] at hsad
  unfold kinkSplitFalse
  simp only [NatTrans.comp_app, Category.assoc]
  rw [adjoinCircleCubeDelete_app_comp_resolutionCubeι, kinkSelfIso,
    ResolutionEquiv.resolutionCubeNatIso_inv_app_comp_resolutionCubeι_assoc _ _ _ _ _ _ _
      (by simp), ofHom_reindex_eq_comp
      ((D.reidemeisterOne h false).resolveCrossingCubeCircleEquiv (Fin.last n) false S),
    Category.assoc, reassoc_of% hsad, kinkNotIso,
    ResolutionEquiv.resolutionCubeNatIso_hom_app_comp_resolutionCubeι_assoc _ _ _ _ _ _ _
      (by simp)]
  congr 1
  refine ModuleCat.hom_ext (LinearMap.ext fun x ↦ ?_)
  simp only [ModuleCat.hom_comp, ModuleCat.hom_ofHom, LinearMap.comp_apply]
  rw [kinkSaddleCircleMap, ← deleteCircle_reindex_fiberwiseSplit_reindex]
  simp [kinkCircleEquiv, kinkLoopCircleEquiv, adjoinCircleDelete_apply, ← reindex_reindex]

private instance isIso_kinkSplitFalse : IsIso (D.kinkSplitFalse h hD R j) :=
  isIso_of_app_comp_resolutionCubeι _
    (fun S ↦ (Equiv.ofBijective _ (D.bijective_kinkSaddleCircleMap h false S
      (cubeState_resolveCrossingVertex_last_eq S false true) (D.ht h false S))).symm)
    fun S ↦ by
      rw [kinkSplitFalse_app_comp_resolutionCubeι, ← Khovanov.fiberwiseSplit_equiv]

/-- On the summand with the loop labelled `X`, the saddle at the kink is `kinkSplitFalse`. -/
private theorem kinkNotIso_hom_comp_resolveCrossingSaddle_comp_kinkBicone_snd :
    (D.kinkNotIso h false hD R j).hom ≫
        (D.reidemeisterOne h false).resolveCrossingSaddle (Fin.last n)
          ((isPlanar_reidemeisterOne D h false).2 hD) R j ≫
            (D.kinkBicone h false hD R (sub_one_eq_sub_two_add_one j) rfl).snd =
      D.kinkSplitFalse h hD R j := by
  simp [kinkSplitFalse]

private instance isIso_resolveCrossingSaddle_comp_kinkBicone_snd_false :
    IsIso ((D.reidemeisterOne h false).resolveCrossingSaddle (Fin.last n)
      ((isPlanar_reidemeisterOne D h false).2 hD) R j ≫
        (D.kinkBicone h false hD R (sub_one_eq_sub_two_add_one j) rfl).snd) := by
  have : IsIso ((D.kinkNotIso h false hD R j).hom ≫
      (D.reidemeisterOne h false).resolveCrossingSaddle (Fin.last n)
        ((isPlanar_reidemeisterOne D h false).2 hD) R j ≫
          (D.kinkBicone h false hD R (sub_one_eq_sub_two_add_one j) rfl).snd) := by
    rw [kinkNotIso_hom_comp_resolveCrossingSaddle_comp_kinkBicone_snd]
    infer_instance
  exact IsIso.of_isIso_comp_left (D.kinkNotIso h false hD R j).hom _

/-- The skein sequence at the kink, split at the cube level by the summand with the loop
labelled `X`. -/
private def kinkSplittingFalse :=
  ShortComplex.Splitting.ofIsIsoCompSnd
    (D.kinkBicone h false hD R (sub_one_eq_sub_two_add_one j) rfl)
    (D.kinkBicone_total h false hD R _ _)
    ((D.reidemeisterOne h false).resolveCrossingSaddle (Fin.last n)
      ((isPlanar_reidemeisterOne D h false).2 hD) R j)

/-- **The first Reidemeister move, cutting off the loop by the `B`-smoothing.** For the kink
`D.reidemeisterOne h false` inserted into an arc of a planar code `D`, whose `B`-smoothing cuts off
the loop, the degree-`j` component of the unnormalized Khovanov complex is homotopy equivalent to
the degree-`j - 2` component of that of `D`, with the cochain degree raised by one. -/
def khovanovBracketReidemeisterOneFalseHomotopyEquiv :
    HomotopyEquiv
      ((D.reidemeisterOne h false).khovanovBracket ((isPlanar_reidemeisterOne D h false).2 hD) R j)
      ((D.khovanovBracket hD R (j - 2))⟦(-1 : ℤ)⟧) :=
  let e : HomotopyEquiv
      (((D.reidemeisterOne h false).khovanovBracket ((isPlanar_reidemeisterOne D h false).2 hD) R
        j)⟦(1 : ℤ)⟧) (D.khovanovBracket hD R (j - 2)) :=
    (HomotopyEquiv.ofIso ((D.reidemeisterOne h false).khovanovBracketMappingConeIso (Fin.last n)
      _ R j).symm).trans
      ((((D.kinkSplittingFalse h hD R j).map (cubeComplexFunctor (ModuleCat.{u} R) (Fin n))
        ).homotopyCofiberHomotopyEquiv fun k ↦ ⟨k - 1, by simp⟩).trans
        (HomotopyEquiv.ofIso (eqToIso (D.khovanovBracket_apply hD R (j - 2)).symm)))
  (HomotopyEquiv.ofIso ((shiftFunctorCompIsoId _ (1 : ℤ) (-1) (by norm_num)).app _).symm).trans
    (e.shift (-1))

end Split

end TauCeti.PDCode
