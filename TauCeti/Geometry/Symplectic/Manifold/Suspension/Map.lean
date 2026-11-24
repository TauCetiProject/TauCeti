/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Manifold.Suspension.SeamFamily

/-!
# Naturality of the block almost complex structures of symplectic suspensions

Let `φ : M ≃ₘ⟮I, I⟯ M` and `ψ : N ≃ₘ⟮J, J⟯ N` be diffeomorphisms and let `g : M → N` be a smooth map
intertwining them, `g ∘ φ = ψ ∘ g`. It induces the map `[t, x] ↦ [t, g x]` of mapping tori
(`TauCeti.SmoothMappingTorus.map`), and with it the map

`F : (ℝ / ℤ) × Y_φ → (ℝ / ℤ) × Y_ψ`, `(θ, [t, x]) ↦ (θ, [t, g x])`

of symplectic suspensions, which pulls `Ω = ds ∧ dt + τ_v` back to `ds ∧ dt + (g^* τ)_v`
(`TauCeti.SmoothMappingTorus.mpullback_prodMap_map_suspensionForm`). This file proves the
corresponding law for the block almost complex structures descended from vertical families
(`TauCeti.SmoothMappingTorus.suspensionAlmostComplexStructure`).

Let `K_((s,t),x)` be a vertical family for `φ` and `K'_((s,t),y)` one for `ψ`, both periodic in `s`
and seam compatible. Then `F` is pseudoholomorphic for the two descended structures exactly when
the differentials of `g` intertwine the vertical families,

`dg_x ∘ K_((s,t),x) = K'_((s,t),g x) ∘ dg_x`

(`TauCeti.SmoothMappingTorus.isPseudoholomorphic_prodMap_map_suspensionAlmostComplexStructure_iff`).
The proof works upstairs. On `(ℝ × ℝ) × M` the map `id × g` intertwines the block structures
`a ∂_s + b ∂_t + v ↦ -b ∂_s + a ∂_t + K v` and `a ∂_s + b ∂_t + w ↦ -b ∂_s + a ∂_t + K' w` exactly
when `dg` intertwines `K` and `K'`
(`TauCeti.SmoothAlmostComplexStructure.mfderiv_prodMap_prodFamily_iff`). The covering maps are
complex linear local diffeomorphisms onto the descended structures, and `F` composed with the
covering map of `φ` is the covering map of `ψ` composed with `id × g`
(`TauCeti.SmoothMappingTorus.prodMap_map_suspensionCover`), so the Cauchy–Riemann equation of `F`
at the image of a point is that of `id × g` at the point.

For the seam structures (`TauCeti.SmoothMappingTorus.seamAlmostComplexStructure`) the
intertwining needs no hypothesis beyond the conjugacy. Let `e : M ≃ₘ⟮I, J⟯ N` conjugate `φ` to
`ψ` and pull the almost complex structure `J₀'`, compatible with a `ψ`-invariant form `τ`, back to
the structure `J₀`, compatible with a `φ`-invariant form `σ`. Pulling back along `e` commutes with
the pullbacks along the powers of `φ` and `ψ` and with the Cayley path, so `de` intertwines the
seam family of `(φ, J₀)` with the seam family of `(ψ, J₀')`
(`TauCeti.SmoothMappingTorus.mfderiv_seamFamily_of_semiconj`). Hence the induced diffeomorphism
of suspensions is pseudoholomorphic from the seam structure of `(φ, J₀)` to the seam structure of
`(ψ, J₀')`
(`TauCeti.SmoothMappingTorus.isPseudoholomorphic_prodMap_map_seamAlmostComplexStructure`).
When moreover `e^* τ = σ`, it also pulls `ds ∧ dt + τ_v` back to `ds ∧ dt + σ_v`
(`TauCeti.SmoothMappingTorus.mpullback_prodMap_map_suspensionForm`). Composing with it carries
the pseudoholomorphic curves of one suspension to those of the other
(`TauCeti.IsPseudoholomorphic.comp`).

## Main results

All declarations are in the namespace `TauCeti.SmoothMappingTorus`.

* `isPseudoholomorphicAt_prodMap_map_suspensionCover_iff`,
  `isPseudoholomorphic_prodMap_map_suspensionAlmostComplexStructure_iff`: the induced map of
  suspensions is pseudoholomorphic for the descended block structures, at a point or everywhere,
  exactly when `dg` intertwines the vertical families there or everywhere.
* `isPseudoholomorphic_prodMap_map_seamAlmostComplexStructure`: for a conjugacy `e` pulling
  `J₀'` back to `J₀`, the induced diffeomorphism of suspensions is pseudoholomorphic
  from the seam structure of `(φ, J₀)` to that of `(ψ, J₀')`.

## References

* Michael Hutchings and Michael Sullivan, *The periodic Floer homology of a Dehn twist*,
  Algebraic & Geometric Topology 5 (2005), 301–354, Section 2 (the symplectic suspension and its
  almost complex structures).
* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Section 2.2 (the action `J ↦ φ^* J` of symplectomorphisms on almost complex structures).
-/

public noncomputable section

open Bundle Function
open scoped Manifold ContDiff

namespace TauCeti.SmoothMappingTorus

variable {E H M E' H' N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  {J : ModelWithCorners ℝ E' H'} [TopologicalSpace N] [ChartedSpace H' N]
  {φ : M ≃ₘ⟮I, I⟯ M} {ψ : N ≃ₘ⟮J, J⟯ N}

variable [FiniteDimensional ℝ E] [IsManifold I ∞ M] [T2Space M] [LocallyCompactSpace M]
  [FiniteDimensional ℝ E'] [IsManifold J ∞ N] [T2Space N] [LocallyCompactSpace N]

/-! ### Descended block structures -/

section Descended

variable {K : ∀ p : (ℝ × ℝ) × M, AlmostComplexStructure (TangentSpace I p.2)}
  {hK : ContMDiff (𝓘(ℝ, ℝ × ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E)) ∞
    (fun p ↦ TotalSpace.mk' (E →L[ℝ] E)
      (E := fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x)
      p.2 (K p).toLinearMap.toContinuousLinearMap)}
  {hs : ∀ p : (ℝ × ℝ) × M, K (p.1 + (1, 0), p.2) = K p}
  {ht : ∀ (p : (ℝ × ℝ) × M) (v : TangentSpace I p.2),
    mfderiv I I φ.symm p.2 (K p v) = K (p.1 + (0, 1), φ.symm p.2) (mfderiv I I φ.symm p.2 v)}
  {K' : ∀ p : (ℝ × ℝ) × N, AlmostComplexStructure (TangentSpace J p.2)}
  {hK' : ContMDiff (𝓘(ℝ, ℝ × ℝ).prod J) (J.prod 𝓘(ℝ, E' →L[ℝ] E')) ∞
    (fun p ↦ TotalSpace.mk' (E' →L[ℝ] E')
      (E := fun y : N ↦ TangentSpace J y →L[ℝ] TangentSpace J y)
      p.2 (K' p).toLinearMap.toContinuousLinearMap)}
  {hs' : ∀ p : (ℝ × ℝ) × N, K' (p.1 + (1, 0), p.2) = K' p}
  {ht' : ∀ (p : (ℝ × ℝ) × N) (v : TangentSpace J p.2),
    mfderiv J J ψ.symm p.2 (K' p v) = K' (p.1 + (0, 1), ψ.symm p.2) (mfderiv J J ψ.symm p.2 v)}

/-- For a smooth map `g` intertwining the monodromies `φ` and `ψ`, the induced map
`(θ, [t, x]) ↦ (θ, [t, g x])` is pseudoholomorphic at `([s], [t, x])`, from the block structure
descended from `K` to the block structure descended from `K'`, exactly when `dg_x` intertwines
`K_((s,t),x)` with `K'_((s,t),g x)`. -/
theorem isPseudoholomorphicAt_prodMap_map_suspensionCover_iff {g : M → N}
    (h : Semiconj g φ ψ) (hg : ContMDiff I J ∞ g) (p : (ℝ × ℝ) × M) :
    IsPseudoholomorphicAt (suspensionAlmostComplexStructure φ hK hs ht)
        (suspensionAlmostComplexStructure ψ hK' hs' ht') (Prod.map id (map φ ψ g h))
        (suspensionCover φ p) ↔
      ∀ v : TangentSpace I p.2,
        mfderiv I J g p.2 (K p v) = K' (p.1, g p.2) (mfderiv I J g p.2 v) := by
  have hF : ContMDiff (𝓘(ℝ).prod (𝓘(ℝ).prod I)) (𝓘(ℝ).prod (𝓘(ℝ).prod J)) ∞
      (Prod.map (id : UnitAddCircle → UnitAddCircle) (map φ ψ g h)) :=
    contMDiff_id.prodMap (contMDiff_map φ ψ g h hg)
  have hG : ContMDiff (𝓘(ℝ, ℝ × ℝ).prod I) (𝓘(ℝ, ℝ × ℝ).prod J) ∞
      (Prod.map (id : ℝ × ℝ → ℝ × ℝ) g) :=
    contMDiff_id.prodMap hg
  have hqφ := isLocalDiffeomorph_suspensionCover φ p
  have hqψ := isLocalDiffeomorph_suspensionCover ψ (Prod.map id g p)
  -- Chain rule: on the image of `dq_φ`, the differential of the induced map is `dq_ψ ∘ d(id × g)`.
  have hchain (v : TangentSpace (𝓘(ℝ, ℝ × ℝ).prod I) p) :
      mfderiv (𝓘(ℝ).prod (𝓘(ℝ).prod I)) (𝓘(ℝ).prod (𝓘(ℝ).prod J)) (Prod.map id (map φ ψ g h))
          (suspensionCover φ p)
          (mfderiv (𝓘(ℝ, ℝ × ℝ).prod I) (𝓘(ℝ).prod (𝓘(ℝ).prod I)) (suspensionCover φ) p v) =
        mfderiv (𝓘(ℝ, ℝ × ℝ).prod J) (𝓘(ℝ).prod (𝓘(ℝ).prod J)) (suspensionCover ψ)
          (Prod.map id g p)
          (mfderiv (𝓘(ℝ, ℝ × ℝ).prod I) (𝓘(ℝ, ℝ × ℝ).prod J) (Prod.map id g) p v) := by
    rw [← ContinuousLinearMap.comp_apply, ← ContinuousLinearMap.comp_apply,
      ← mfderiv_comp p ((hF.mdifferentiable (by simp)) _) (hqφ.mdifferentiableAt (by simp)),
      ← mfderiv_comp p (hqψ.mdifferentiableAt (by simp)) ((hG.mdifferentiable (by simp)) p)]
    exact congrArg (fun f ↦ mfderiv (𝓘(ℝ, ℝ × ℝ).prod I) (𝓘(ℝ).prod (𝓘(ℝ).prod J)) f p v)
      (funext (prodMap_map_suspensionCover h))
  -- Upstairs, the identity of the time plane intertwines its standard structure with itself, so
  -- `id × g` intertwines the block structures exactly when `dg` intertwines `K` and `K'`.
  refine Iff.trans ?_ ((SmoothAlmostComplexStructure.mfderiv_prodMap_prodFamily_iff
    (AlmostComplexStructure.product ℝ).constSmooth K hK K' hK' p mdifferentiableAt_id
    ((hg.mdifferentiable (by simp)) p.2)).trans
    (and_iff_right fun u ↦ by simp only [mfderiv_id, ContinuousLinearMap.id_apply, id_eq]))
  rw [isPseudoholomorphicAt_iff_mfderiv, and_iff_right ((hF.mdifferentiable (by simp)) _),
    (hqφ.isInvertible_mfderiv (by simp)).surjective.forall]
  -- On a vector `dq_φ v`, both sides of the Cauchy–Riemann equation of the induced map are the
  -- images under the injective map `dq_ψ` of the two sides of the equation of `id × g` on `v`.
  refine forall_congr' fun v ↦ ?_
  rw [suspensionAlmostComplexStructure_apply_mfderiv, hchain, hchain,
    prodMap_map_suspensionCover h p,
    suspensionAlmostComplexStructure_apply_mfderiv ψ hK' hs' ht' (Prod.map id g p)]
  exact (hqψ.isInvertible_mfderiv (by simp)).injective.eq_iff

/-- For a smooth map `g` intertwining the monodromies `φ` and `ψ`, the induced map
`(θ, [t, x]) ↦ (θ, [t, g x])` is pseudoholomorphic from the suspension of `φ` with the block
structure descended from `K` to the suspension of `ψ` with the block structure descended from `K'`
exactly when the differentials of `g` intertwine the vertical families,
`dg_x ∘ K_((s,t),x) = K'_((s,t),g x) ∘ dg_x`. -/
theorem isPseudoholomorphic_prodMap_map_suspensionAlmostComplexStructure_iff {g : M → N}
    (h : Semiconj g φ ψ) (hg : ContMDiff I J ∞ g) :
    IsPseudoholomorphic (suspensionAlmostComplexStructure φ hK hs ht)
        (suspensionAlmostComplexStructure ψ hK' hs' ht') (Prod.map id (map φ ψ g h)) ↔
      ∀ (p : (ℝ × ℝ) × M) (v : TangentSpace I p.2),
        mfderiv I J g p.2 (K p v) = K' (p.1, g p.2) (mfderiv I J g p.2 v) := by
  rw [isPseudoholomorphic_iff, (suspensionCover_surjective φ).forall]
  exact forall_congr' fun p ↦ isPseudoholomorphicAt_prodMap_map_suspensionCover_iff h hg p

end Descended

/-! ### Seam structures -/

section Seam

variable {σ : SmoothTwoForm I M} (hσ : SmoothForm.mpullback φ φ.contMDiff σ = σ)
  {J₀ : SmoothAlmostComplexStructure I M} (hJ₀ : σ.Compatible J₀)
  {τ : SmoothTwoForm J N} (hτ : SmoothForm.mpullback ψ ψ.contMDiff τ = τ)
  {J₀' : SmoothAlmostComplexStructure J N} (hJ₀' : τ.Compatible J₀')
  (e : M ≃ₘ⟮I, J⟯ N) (h : Semiconj e φ ψ)

/-- For a conjugacy `e` from `φ` to `ψ` pulling `J₀'` back to `J₀`, the induced diffeomorphism
`(θ, [t, x]) ↦ (θ, [t, e x])` of suspensions is pseudoholomorphic from the seam structure of
`(φ, J₀)` to the seam structure of `(ψ, J₀')`. -/
theorem isPseudoholomorphic_prodMap_map_seamAlmostComplexStructure (heJ : J₀'.pullback e = J₀) :
    IsPseudoholomorphic (seamAlmostComplexStructure hσ hJ₀) (seamAlmostComplexStructure hτ hJ₀')
      (Prod.map id (map φ ψ e h)) := by
  rw [seamAlmostComplexStructure_def, seamAlmostComplexStructure_def]
  exact (isPseudoholomorphic_prodMap_map_suspensionAlmostComplexStructure_iff h e.contMDiff).2
    (mfderiv_seamFamily_of_semiconj hσ hJ₀ hτ hJ₀' e h heJ)

end Seam

end TauCeti.SmoothMappingTorus
