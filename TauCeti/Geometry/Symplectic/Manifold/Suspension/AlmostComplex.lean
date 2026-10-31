/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Manifold.AlmostComplex.Descent
public import TauCeti.Geometry.Symplectic.Manifold.AlmostComplex.Prod
public import TauCeti.Geometry.Symplectic.Manifold.Suspension.Cover

/-!
# Block almost complex structures on a symplectic suspension

Let `φ : M ≃ₘ⟮I, I⟯ M` be a diffeomorphism of a locally compact Hausdorff smooth manifold
preserving a two-form `σ`, and let `X_φ = (ℝ / ℤ)_s × Y_φ` be the product of a circle with the
mapping torus `Y_φ = (ℝ × M) / ((t, x) ∼ (t + 1, φ⁻¹ x))`, carrying the form
`Ω = ds ∧ dt + σ_v` (`TauCeti.SmoothMappingTorus.suspensionForm`). The map

`q : (ℝ × ℝ) × M → X_φ`, `((s, t), x) ↦ ([s], [t, x])`

(`TauCeti.SmoothMappingTorus.suspensionCover φ`) is a surjective smooth local diffeomorphism, and
it pulls `Ω` back to the product form `ds ∧ dt + σ` of `(ℝ × ℝ) × M`.

On `(ℝ × ℝ) × M`, a jointly smooth family `K_((s,t),x)` of almost complex structures on the tangent
spaces of `M` gives the block structure `J'(a ∂_s + b ∂_t + v) = -b ∂_s + a ∂_t + K v`
(`TauCeti.SmoothAlmostComplexStructure.prodFamily`). This file descends it along `q`. The descent
needs two identities, which say that `J'` is invariant under the deck transformations generating
the fibres of `q`:

* periodicity in `s`, `K_((s + 1, t), x) = K_((s, t), x)`;
* the seam identity in `t`, `dφ⁻¹ ∘ K_((s, t), x) = K_((s, t + 1), φ⁻¹ x) ∘ dφ⁻¹`.

No `φ`-invariant almost complex structure on `M` is needed: the vertical family may vary with
`t` and only its values at times one apart are related. The descended structure
`TauCeti.SmoothMappingTorus.suspensionAlmostComplexStructure` acts on `a ∂_s + b ∂_t + v` at
`([s], [t, x])` as `J'` does, sending `∂_s` to the suspension vector field `T = ∂_t` and `T` to
`-∂_s`. Its quadratic form against `Ω` is `Ω(w, J w) = a² + b² + σ(v, K v)` for
`w = a ∂_s + b ∂_t + v`, and when each `K_((s,t),x)` is compatible with `σ`, the descended
structure is compatible with `Ω`.

## Main definitions

* `TauCeti.SmoothMappingTorus.suspensionCover φ`: the covering map `(ℝ × ℝ) × M → X_φ`.
* `TauCeti.SmoothMappingTorus.suspensionAlmostComplexStructure`: the block almost complex
  structure on `X_φ` descended from a periodic family satisfying the seam identity.

## Main results

* `TauCeti.SmoothMappingTorus.isLocalDiffeomorph_suspensionCover`,
  `TauCeti.SmoothMappingTorus.suspensionCover_surjective`: the covering map is a surjective
  smooth local diffeomorphism.
* `TauCeti.SmoothMappingTorus.suspensionCover_eq_suspensionCover_iff`: its fibres are the orbits
  of the deck transformations `((s, t), x) ↦ ((s + n, t + k), φ ^ (-k) x)`.
* `TauCeti.SmoothMappingTorus.mfderiv_suspensionCover_apply`: its differential in the coordinates
  `(s, t, x)`.
* `TauCeti.SmoothMappingTorus.mpullback_suspensionCover_suspensionForm`: it pulls `Ω` back to
  `ds ∧ dt + σ`.
* `TauCeti.SmoothMappingTorus.suspensionAlmostComplexStructure_apply_mfderiv`: the differential of
  the covering map is complex linear for the block structure and its descent.
* `TauCeti.SmoothMappingTorus.suspensionAlmostComplexStructure_mk`: the descended structure in the
  coordinates `(s, t, x)`.
* `TauCeti.SmoothMappingTorus.eval₂_suspensionForm_suspensionAlmostComplexStructure`:
  `Ω(w, J w) = a² + b² + σ(v, K v)`.
* `TauCeti.SmoothMappingTorus.tames_suspensionAlmostComplexStructure`: vertical tameness descends.
* `TauCeti.SmoothMappingTorus.compatible_suspensionAlmostComplexStructure`: a family of
  `σ`-compatible structures descends to an `Ω`-compatible structure.

## References

* Michael Hutchings and Michael Sullivan, *The periodic Floer homology of a Dehn twist*, Algebraic
  & Geometric Topology 5 (2005), 301–354, Section 2 (the symplectic form `ds ∧ dt + ω_φ` and the
  admissible almost complex structures on `ℝ × Y_φ`).
* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Section 2.2 (compatible almost complex structures).
-/

public noncomputable section

open Bundle Function
open scoped Manifold ContDiff

namespace TauCeti.SmoothMappingTorus

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  (φ : M ≃ₘ⟮I, I⟯ M)

/-- The two generating deck transformations of the covering map, `((s, t), x) ↦ ((s + 1, t), x)` and
`((s, t), x) ↦ ((s, t + 1), φ⁻¹ x)`. -/
private def DeckStep (p p' : (ℝ × ℝ) × M) : Prop :=
  p' = (p.1 + (1, 0), p.2) ∨ p' = (p.1 + (0, 1), φ.symm p.2)

/-- Iterates of the deck transformation `((s, t), x) ↦ ((s + 1, t), x)`. -/
private theorem eqvGen_deckStep_add_fst (n : ℤ) :
    ∀ p : (ℝ × ℝ) × M, Relation.EqvGen (DeckStep φ) p (p.1 + ((n : ℝ), 0), p.2) := by
  induction n using Int.induction_on with
  | zero => intro p; convert Relation.EqvGen.refl p; simp
  | succ i ih =>
    intro p
    convert (ih p).trans _ _ _ (Relation.EqvGen.rel _ _ (Or.inl rfl)) using 2
    ext <;> simp [add_assoc]
  | pred i ih =>
    intro p
    refine (ih p).trans _ _ _ (Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _ (Or.inl ?_)))
    ext <;> simp [add_assoc]

/-- Iterates of the deck transformation `((s, t), x) ↦ ((s, t + 1), φ⁻¹ x)`. -/
private theorem eqvGen_deckStep_add_snd (k : ℤ) :
    ∀ p : (ℝ × ℝ) × M,
      Relation.EqvGen (DeckStep φ) p (p.1 + (0, (k : ℝ)), (φ ^ (-k)) p.2) := by
  induction k using Int.induction_on with
  | zero => intro p; convert Relation.EqvGen.refl p <;> simp [Diffeomorph.one_apply]
  | succ i ih =>
    intro p
    convert (ih p).trans _ _ _ (Relation.EqvGen.rel _ _ (Or.inr rfl)) using 2
    · ext <;> simp [add_assoc]
    · dsimp only
      simp [neg_add_rev, zpow_add, Diffeomorph.mul_apply, Diffeomorph.inv_apply]
  | pred i ih =>
    intro p
    refine (ih p).trans _ _ _ (Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _ (Or.inr ?_)))
    ext
    · simp [add_assoc]
    · simp [add_assoc]
    · dsimp only
      have hexp : -(-(i : ℤ) - 1) = 1 + (i : ℤ) := by omega
      simp [hexp, zpow_add, Diffeomorph.mul_apply]

/-- The fibres of the covering map are generated by its two generating deck transformations. -/
private theorem eqvGen_deckStep_of_suspensionCover_eq {p p' : (ℝ × ℝ) × M}
    (h : suspensionCover φ p = suspensionCover φ p') : Relation.EqvGen (DeckStep φ) p p' := by
  obtain ⟨n, k, rfl⟩ := (suspensionCover_eq_suspensionCover_iff φ).1 h
  refine Relation.EqvGen.symm _ _ ?_
  convert (eqvGen_deckStep_add_snd φ k p').trans _ _ _
    (eqvGen_deckStep_add_fst φ n (p'.1 + (0, (k : ℝ)), (φ ^ (-k)) p'.2)) using 2
  ext <;> simp [add_comm]

variable [IsManifold I ∞ M] [T2Space M] [LocallyCompactSpace M]

variable {φ} {σ : SmoothTwoForm I M} {hσ : SmoothForm.mpullback φ φ.contMDiff σ = σ}

/-! ### Descending block structures -/

variable [FiniteDimensional ℝ E] (φ)
  (K : ∀ p : (ℝ × ℝ) × M, AlmostComplexStructure (TangentSpace I p.2))
  (hK : ContMDiff (𝓘(ℝ, ℝ × ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E)) ∞
    (fun p ↦ TotalSpace.mk' (E →L[ℝ] E)
      (E := fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x)
      p.2 (K p).toLinearMap.toContinuousLinearMap))

variable {K}
variable (hs : ∀ p : (ℝ × ℝ) × M, K (p.1 + (1, 0), p.2) = K p)
  (ht : ∀ (p : (ℝ × ℝ) × M) (v : TangentSpace I p.2),
    mfderiv I I φ.symm p.2 (K p v) = K (p.1 + (0, 1), φ.symm p.2) (mfderiv I I φ.symm p.2 v))

omit [LocallyCompactSpace M] in
include hs ht in
/-- Under periodicity in `s` and the seam identity in `t`, the two generating deck transformations
of the covering map preserve the block structure. -/
private theorem exists_deck_of_deckStep (p p' : (ℝ × ℝ) × M) (h : DeckStep φ p p') :
    ∃ g : (ℝ × ℝ) × M → (ℝ × ℝ) × M, g p = p' ∧
      MDifferentiableAt (𝓘(ℝ, ℝ × ℝ).prod I) (𝓘(ℝ, ℝ × ℝ).prod I) g p ∧
      suspensionCover φ ∘ g = suspensionCover φ ∧
      ∀ v, mfderiv (𝓘(ℝ, ℝ × ℝ).prod I) (𝓘(ℝ, ℝ × ℝ).prod I) g p
          (SmoothAlmostComplexStructure.prodFamily (AlmostComplexStructure.product ℝ).constSmooth
            K hK p v) =
        SmoothAlmostComplexStructure.prodFamily (AlmostComplexStructure.product ℝ).constSmooth
          K hK (g p) (mfderiv (𝓘(ℝ, ℝ × ℝ).prod I) (𝓘(ℝ, ℝ × ℝ).prod I) g p v) := by
  -- Each step is a translation of the time plane together with a fibre diffeomorphism `g`.
  have hdiff (c : ℝ × ℝ) (g : M ≃ₘ⟮I, I⟯ M) :
      MDifferentiableAt (𝓘(ℝ, ℝ × ℝ).prod I) (𝓘(ℝ, ℝ × ℝ).prod I)
        (Prod.map (fun q ↦ q + c) g) p :=
    (differentiableAt_id.add_const c).mdifferentiableAt.prodMap (g.mdifferentiable (by simp) p.2)
  rcases h with rfl | rfl
  · refine ⟨Prod.map (fun q ↦ q + (1, 0)) (Diffeomorph.refl I M ∞), rfl, hdiff _ _, ?_,
      (SmoothAlmostComplexStructure.mfderiv_translation_prodFamily_iff K hK _ _ p).2
        fun w ↦ ?_⟩
    · funext ⟨⟨s, t⟩, x⟩
      simp
    · simp [hs]
      -- The differential of the identity is the identity of the model space.
      rfl
  · refine ⟨Prod.map (fun q ↦ q + (0, 1)) φ.symm, rfl, hdiff _ _, ?_,
      (SmoothAlmostComplexStructure.mfderiv_translation_prodFamily_iff K hK _ _ p).2 (ht p)⟩
    funext ⟨⟨s, t⟩, x⟩
    simp [mk_add_one]

/-- The block almost complex structure on `(ℝ / ℤ) × Y_φ` descended from the block structure
`a ∂_s + b ∂_t + v ↦ -b ∂_s + a ∂_t + K v` on `(ℝ × ℝ) × M`. The vertical family `K` must be
periodic in `s` and satisfy the seam identity `dφ⁻¹ ∘ K_((s, t), x) = K_((s, t + 1), φ⁻¹ x) ∘ dφ⁻¹`
in `t`, so that the block structure is invariant under the deck transformations of the covering
map. -/
def suspensionAlmostComplexStructure :
    SmoothAlmostComplexStructure (𝓘(ℝ).prod (𝓘(ℝ).prod I))
      (UnitAddCircle × SmoothMappingTorus φ) :=
  SmoothAlmostComplexStructure.descend (isLocalDiffeomorph_suspensionCover φ)
    (suspensionCover_surjective φ)
    (SmoothAlmostComplexStructure.prodFamily (AlmostComplexStructure.product ℝ).constSmooth K hK)
    fun _ _ v v' h hv ↦ SmoothAlmostComplexStructure.mfderiv_apply_eq_of_eqvGen
      (isLocalDiffeomorph_suspensionCover φ) _ (exists_deck_of_deckStep φ hK hs ht)
      (eqvGen_deckStep_of_suspensionCover_eq φ h) v v' hv

/-- The differential of the covering map is complex linear for the block structure on
`(ℝ × ℝ) × M` and the descended structure on `(ℝ / ℤ) × Y_φ`. -/
@[simp]
theorem suspensionAlmostComplexStructure_apply_mfderiv (p : (ℝ × ℝ) × M)
    (v : TangentSpace (𝓘(ℝ, ℝ × ℝ).prod I) p) :
    suspensionAlmostComplexStructure φ hK hs ht (suspensionCover φ p)
        (mfderiv (𝓘(ℝ, ℝ × ℝ).prod I) (𝓘(ℝ).prod (𝓘(ℝ).prod I)) (suspensionCover φ) p v) =
      mfderiv (𝓘(ℝ, ℝ × ℝ).prod I) (𝓘(ℝ).prod (𝓘(ℝ).prod I)) (suspensionCover φ) p
        (SmoothAlmostComplexStructure.prodFamily (AlmostComplexStructure.product ℝ).constSmooth
          K hK p v) :=
  SmoothAlmostComplexStructure.descend_apply_mfderiv (isLocalDiffeomorph_suspensionCover φ)
    (suspensionCover_surjective φ) _ _ p v

/-- In the coordinates `(s, t, x)`, the descended structure sends `a ∂_s + b ∂_t + v` at
`([s], [t, x])` to `-b ∂_s + a ∂_t + K_((s, t), x) v`. In particular it sends `∂_s` to the
suspension vector field `T = ∂_t` and `T` to `-∂_s`. -/
theorem suspensionAlmostComplexStructure_mk (s t : ℝ) (x : M) (a b : ℝ) (v : TangentSpace I x) :
    suspensionAlmostComplexStructure φ hK hs ht ((s : UnitAddCircle), mk φ t x)
        ((Manifold.tangentSpaceProdEquiv _).symm
          (a, mfderiv (𝓘(ℝ).prod I) (𝓘(ℝ).prod I) (uncurry (mk φ)) (t, x)
            ((Manifold.tangentSpaceProdEquiv (t, x)).symm (b, v)))) =
      (Manifold.tangentSpaceProdEquiv _).symm
        (-b, mfderiv (𝓘(ℝ).prod I) (𝓘(ℝ).prod I) (uncurry (mk φ)) (t, x)
          ((Manifold.tangentSpaceProdEquiv (t, x)).symm (a, K ((s, t), x) v))) := by
  -- The tangent vectors `a ∂_s + b ∂_t + v` and `-b ∂_s + a ∂_t + K v` are images under the
  -- covering map; `([s], [t, x])` is the image of `((s, t), x)` by definition.
  have hv : mfderiv (𝓘(ℝ, ℝ × ℝ).prod I) (𝓘(ℝ).prod (𝓘(ℝ).prod I)) (suspensionCover φ) ((s, t), x)
      ((Manifold.tangentSpaceProdEquiv ((s, t), x)).symm
        ((NormedSpace.fromTangentSpace (𝕜 := ℝ) (s, t)).symm (a, b), v)) =
      (Manifold.tangentSpaceProdEquiv (I := 𝓘(ℝ)) (J := 𝓘(ℝ).prod I)
        ((s : UnitAddCircle), mk φ t x)).symm
        (a, mfderiv (𝓘(ℝ).prod I) (𝓘(ℝ).prod I) (uncurry (mk φ)) (t, x)
          ((Manifold.tangentSpaceProdEquiv (t, x)).symm (b, v))) := by
    rw [mfderiv_suspensionCover_apply, suspensionCover_apply]
    simp only [ContinuousLinearEquiv.apply_symm_apply]
  have hJv : mfderiv (𝓘(ℝ, ℝ × ℝ).prod I) (𝓘(ℝ).prod (𝓘(ℝ).prod I)) (suspensionCover φ)
      ((s, t), x) ((Manifold.tangentSpaceProdEquiv ((s, t), x)).symm
        ((NormedSpace.fromTangentSpace (𝕜 := ℝ) (s, t)).symm (-b, a), K ((s, t), x) v)) =
      (Manifold.tangentSpaceProdEquiv (I := 𝓘(ℝ)) (J := 𝓘(ℝ).prod I)
        ((s : UnitAddCircle), mk φ t x)).symm
        (-b, mfderiv (𝓘(ℝ).prod I) (𝓘(ℝ).prod I) (uncurry (mk φ)) (t, x)
          ((Manifold.tangentSpaceProdEquiv (t, x)).symm (a, K ((s, t), x) v))) := by
    rw [mfderiv_suspensionCover_apply, suspensionCover_apply]
    simp only [ContinuousLinearEquiv.apply_symm_apply]
  -- The standard structure of the plane sends `(a, b)` to `(-b, a)`.
  have hJ : (AlmostComplexStructure.product ℝ).constSmooth (s, t)
      ((NormedSpace.fromTangentSpace (𝕜 := ℝ) (s, t)).symm (a, b)) =
      (NormedSpace.fromTangentSpace (𝕜 := ℝ) (s, t)).symm (-b, a) := by
    apply (NormedSpace.fromTangentSpace (𝕜 := ℝ) (s, t)).injective
    rw [AlmostComplexStructure.fromTangentSpace_constSmooth_apply,
      ContinuousLinearEquiv.apply_symm_apply, ContinuousLinearEquiv.apply_symm_apply,
      AlmostComplexStructure.product_apply]
  rw [← hv, ← hJv, ← suspensionCover_apply φ s t x]
  refine (suspensionAlmostComplexStructure_apply_mfderiv φ hK hs ht ((s, t), x) _).trans ?_
  rw [SmoothAlmostComplexStructure.prodFamily_apply]
  simp only [ContinuousLinearEquiv.apply_symm_apply, hJ]

/-- The quadratic form of `Ω` and the descended structure: at `([s], [t, x])`,
`Ω(w, J w) = a² + b² + σ(v, K_((s, t), x) v)` for `w = a ∂_s + b ∂_t + v`. -/
theorem eval₂_suspensionForm_suspensionAlmostComplexStructure (s t : ℝ) (x : M) (a b : ℝ)
    (v : TangentSpace I x) :
    (suspensionForm φ σ hσ).eval₂ ((s : UnitAddCircle), mk φ t x)
        ((Manifold.tangentSpaceProdEquiv _).symm
          (a, mfderiv (𝓘(ℝ).prod I) (𝓘(ℝ).prod I) (uncurry (mk φ)) (t, x)
            ((Manifold.tangentSpaceProdEquiv (t, x)).symm (b, v))))
        (suspensionAlmostComplexStructure φ hK hs ht ((s : UnitAddCircle), mk φ t x)
          ((Manifold.tangentSpaceProdEquiv _).symm
            (a, mfderiv (𝓘(ℝ).prod I) (𝓘(ℝ).prod I) (uncurry (mk φ)) (t, x)
              ((Manifold.tangentSpaceProdEquiv (t, x)).symm (b, v))))) =
      a ^ 2 + b ^ 2 + σ.eval₂ x v (K ((s, t), x) v) := by
  rw [suspensionAlmostComplexStructure_mk, eval₂_suspensionForm_mk]
  ring

/-- If the fibre form tames every vertical structure, the suspension form tames the descended
block structure. -/
theorem tames_suspensionAlmostComplexStructure
    (htame : ∀ (p : (ℝ × ℝ) × M) (v : TangentSpace I p.2), v ≠ 0 →
      0 < σ.eval₂ p.2 v (K p v)) :
    (suspensionForm φ σ hσ).Tames (suspensionAlmostComplexStructure φ hK hs ht) := by
  refine (SmoothAlmostComplexStructure.tames_descend_iff _ _ _ _ _).2 ?_
  rw [mpullback_suspensionCover_suspensionForm]
  exact SmoothAlmostComplexStructure.tames_prodFamily _ K hK
    (SymplecticForm.compatible_constSmooth_iff.2 stdSymplecticForm_compatible_product).tames htame

/-- If every member of the vertical family is compatible with the nondegenerate form `σ`, the
descended block structure is compatible with `Ω = ds ∧ dt + σ_v`. -/
theorem compatible_suspensionAlmostComplexStructure (hσn : σ.IsNondegenerate)
    (hcompat : ∀ p : (ℝ × ℝ) × M, (hσn.symplecticFormAt p.2).Compatible (K p)) :
    (suspensionForm φ σ hσ).Compatible (suspensionAlmostComplexStructure φ hK hs ht) := by
  refine (SmoothAlmostComplexStructure.compatible_descend_iff _ _ _ _ _).2 ?_
  rw [mpullback_suspensionCover_suspensionForm]
  exact SmoothAlmostComplexStructure.compatible_prodFamily _ K hK
    (SymplecticForm.compatible_constSmooth_iff.2 stdSymplecticForm_compatible_product) hσn hcompat

end TauCeti.SmoothMappingTorus
