/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.DGLocalSystem.Orientation.Basic
public import TauCeti.AlgebraicTopology.DGLocalSystem.Sign
public import TauCeti.AlgebraicTopology.Singular.LocalHomology.Orientation.LocalHomeomorph
public import TauCeti.Geometry.Manifold.Orientation.Cover.FundamentalClass
public import TauCeti.Topology.VectorBundle.Orientation.Cover.Character

/-!
# The homological orientation character is the orientation character of the tangent bundle

A smooth manifold `M` of dimension `d` has two orientation characters `π₁(M, x) →* ℤˣ`, which
record whether a loop preserves or reverses orientations:

* the **homological** one, `TauCeti.orientationCharacter`, by transport of the local orientations,
  the generators of the integral local homology `H_d(M, M ∖ {x}; ℤ)`;
* the one of the **tangent bundle**, `TauCeti.VectorBundleOrientationCover.orientationCharacter`,
  by transport of the orientations of the tangent space `TₓM` along the loop, that is, by path
  lifting in the orientation double cover `M'` of `M`.

They agree
(`TauCeti.Manifold.OrientationCover.orientationCharacter_eq_orientationCharacter_tangentSpace`):
for a smooth manifold, the first Stiefel–Whitney class of the tangent bundle, read on loops, is
the obstruction to orienting `M` homologically. Consequently the orientation local system of `M`
built from local homology is the sign local system of the orientation double cover, with
coefficients in any commutative ring
(`TauCeti.Manifold.OrientationCover.rankOneLocalSystem_orientation_eq_signRankOneLocalSystem`).

In positive dimension the proof reads the canonical homological orientation of the cover `M'`
(`TauCeti.Manifold.OrientationCover.homologicalOrientation`) in `M` through the covering map,
a local homeomorphism (`IsLocalHomeomorph.localOrientationEquiv`). At a point `p = (x, ω)` of
the cover, with `ω` an orientation of `TₓM`, this gives a local orientation `ℓ(p)` of `M` at `x`.

* The deck involution `(x, ω) ↦ (x, -ω)` has local index `-1` for the canonical orientation
  (`TauCeti.Manifold.OrientationCover.localIndex_deck`), and lies over the identity of `M`, so
  `ℓ(x, -ω) = -ℓ(x, ω)`.
* The covering map intertwines the transport of local orientations
  (`IsLocalHomeomorph.localOrientationEquiv_localOrientationTransport`), and the canonical
  orientation of `M'` is invariant under transport. So along a path `δ` in `M'`, transport in
  `M` along the projection of `δ` carries `ℓ` at the start of `δ` to `ℓ` at its end.

Lift a loop `γ` at `x` to `M'` from `(x, ω)`. It ends at `(x, ω)` exactly when the tangent
character of `γ` is `1`, and at `(x, -ω)` exactly when it is `-1`. Transport along `γ` then fixes,
respectively reverses, the local orientation `ℓ(x, ω)`, which is what the homological character
records.

In dimension `0` the manifold is discrete, so its fundamental groups are trivial and so are both
characters.

## Main results

* `TauCeti.Manifold.OrientationCover.orientationCharacter_eq_orientationCharacter_tangentSpace`:
  the homological orientation character of `M` is the orientation character of its tangent
  bundle.
* `TauCeti.Manifold.OrientationCover.rankOneLocalSystem_orientation_eq_signRankOneLocalSystem`:
  the orientation local system of `M` is the sign local system of its orientation double cover.

## References

* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Section 3.3 (local
  orientations and the orientation double cover).
* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton University Press, 1974, §12 (the orientation double cover and `w₁`).
-/

public section

noncomputable section

open CategoryTheory Module
open scoped Manifold

namespace TauCeti.Manifold.OrientationCover

variable {E M : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [T2Space M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) 1 M] {n : ℕ}
  (hE : finrank ℝ E = n + 1)

/-- The local orientation of `M` at `p.proj` read through the covering map from the canonical
homological orientation of the orientation cover at `p`. -/
private def coverLocalOrientation (p : OrientationCover 𝓘(ℝ, E) M) :
    LocalOrientation M p.proj (n + 1) :=
  (isCoveringMap_proj 𝓘(ℝ, E) M).isLocalHomeomorph.localOrientationEquiv p (n + 1)
    (homologicalOrientation hE p)

/-- **The local orientations read from the two points of a fibre are opposite.** The deck
involution has local index `-1` and lies over the identity of `M`. -/
private theorem coverLocalOrientation_neg (p : OrientationCover 𝓘(ℝ, E) M) :
    coverLocalOrientation hE ⟨p.proj, -p.orientation⟩ = -coverLocalOrientation hE p := by
  have hπ := (isCoveringMap_proj 𝓘(ℝ, E) M).isLocalHomeomorph
  -- A sheet `S` of the cover around `p`, on which the projection is an open embedding.
  obtain ⟨e, hp, he⟩ := hπ p
  have hS : Topology.IsOpenEmbedding (Subtype.val : e.source → OrientationCover 𝓘(ℝ, E) M) :=
    e.open_source.isOpenEmbedding_subtypeVal
  have hπS : Topology.IsOpenEmbedding (VectorBundleOrientationCover.proj ∘
      (Subtype.val : e.source → OrientationCover 𝓘(ℝ, E) M)) := by
    rw [he]; exact e.isOpenEmbedding_restrict
  -- The deck involution on `S`, written so that it lies over the projection definitionally.
  let τ : OrientationCover 𝓘(ℝ, E) M ≃ₜ OrientationCover 𝓘(ℝ, E) M :=
    VectorBundleOrientationCover.deck
  let j : e.source → OrientationCover 𝓘(ℝ, E) M := fun z ↦ ⟨z.val.proj, -z.val.orientation⟩
  have hjτ : j = τ ∘ Subtype.val :=
    funext fun z ↦ (VectorBundleOrientationCover.deck_apply z.val).symm
  have hj : Topology.IsOpenEmbedding j := hjτ ▸ τ.isOpenEmbedding.comp hS
  have hjdeck : (⟨j, hj.continuous⟩ : C(e.source, OrientationCover 𝓘(ℝ, E) M)) =
      (τ : C(OrientationCover 𝓘(ℝ, E) M, OrientationCover 𝓘(ℝ, E) M)).restrict e.source :=
    ContinuousMap.ext fun z ↦ congrFun hjτ z
  have hπj : Topology.IsOpenEmbedding (VectorBundleOrientationCover.proj ∘ j) := hπS
  let w : e.source := ⟨p, hp⟩
  -- The local orientation of `S` at `w` corresponding to the canonical one of the cover at `p`.
  let o := (hS.localOrientationEquiv w (n + 1)).symm (homologicalOrientation hE p)
  -- The deck involution carries it to minus the canonical local orientation at the other point.
  have hdeck : hj.localOrientationEquiv w (n + 1) o =
      -homologicalOrientation hE ⟨p.proj, -p.orientation⟩ := by
    have h := (homologicalOrientation hE).localHomologyMap_restrict_localOrientationEquiv_symm
      (homologicalOrientation hE) τ (VectorBundleOrientationCover.deck_apply p) e.open_source hp
      (fun z' _ h ↦ τ.injective (h.trans (VectorBundleOrientationCover.deck_apply p).symm))
    rw [localIndex_deck, neg_one_zsmul] at h
    apply Subtype.ext
    -- The map of local homology of `j` is the one of the deck involution restricted to `S`.
    rw [Topology.IsOpenEmbedding.coe_localOrientationEquiv, localHomologyIsoOfIsOpenEmbedding_hom,
      localHomologyMap_congr _ hjdeck]
    exact h
  -- Read in `M`, the canonical local orientation at `p` is `o` pushed forward by the projection,
  -- and the one at the other point is `-o` pushed forward by the deck involution followed by the
  -- projection.
  have h₁ : coverLocalOrientation hE p = hπS.localOrientationEquiv w (n + 1) o :=
    (congrArg (hπ.localOrientationEquiv p (n + 1))
      ((hS.localOrientationEquiv w (n + 1)).apply_symm_apply _)).symm.trans
      (DFunLike.congr_fun (hπ.localOrientationEquiv_trans hS hπS w (n + 1)) o)
  have h₂ : coverLocalOrientation hE ⟨p.proj, -p.orientation⟩ =
      -hπj.localOrientationEquiv w (n + 1) o := by
    rw [← hπ.localOrientationEquiv_trans hj hπj, Equiv.trans_apply, hdeck,
      IsLocalHomeomorph.localOrientationEquiv_neg, neg_neg]
    -- The point `j w` is `⟨p.proj, -p.orientation⟩` by definition.
    rfl
  -- The deck involution lies over the identity, so `π ∘ j` is the projection on `S`, and the
  -- two correspondences agree by definition.
  rw [h₁, h₂]

/-- **Transport of the local orientations read from the cover.** Along a path `δ` in the
orientation cover, transport in `M` along the projection of `δ` carries the local orientation read
at the start of `δ` to the one read at its end. -/
private theorem localOrientationTransport_coverLocalOrientation
    {p q : OrientationCover 𝓘(ℝ, E) M} (δ : Path p q) :
    localOrientationTransport M E (n + 1)
        (Path.Homotopic.Quotient.mk (δ.map VectorBundleOrientationCover.continuous_proj) :
          FundamentalGroupoid.mk p.proj ⟶ FundamentalGroupoid.mk q.proj)
        (coverLocalOrientation hE p) =
      coverLocalOrientation hE q := by
  have hπ := (isCoveringMap_proj 𝓘(ℝ, E) M).isLocalHomeomorph
  have h := hπ.localOrientationEquiv_localOrientationTransport (E := E)
    (Path.Homotopic.Quotient.mk δ : FundamentalGroupoid.mk p ⟶ FundamentalGroupoid.mk q)
    (homologicalOrientation hE p)
  rw [HomologicalOrientation.localOrientationTransport_apply] at h
  exact h.symm

/-- The homological orientation character of a manifold of positive dimension is the orientation
character of its tangent bundle. -/
private theorem orientationCharacter_eq_of_finrank_eq_succ (x : M) :
    TauCeti.orientationCharacter hE x =
      VectorBundleOrientationCover.orientationCharacter E (TangentSpace 𝓘(ℝ, E))
        (Fintype.card_fin (finrank ℝ E)) x := by
  have hcov := isCoveringMap_proj 𝓘(ℝ, E) M
  ext1 γ
  -- A point `p` of the cover over `x`, and a representative `g` of `γ`.
  obtain ⟨p, rfl⟩ := VectorBundleOrientationCover.surjective_proj (F := E)
    (E := TangentSpace 𝓘(ℝ, E)) (Fintype.card_fin (finrank ℝ E)) x
  obtain ⟨g, hg⟩ : ∃ g : Path p.proj p.proj, (Path.Homotopic.Quotient.mk g :
      FundamentalGroupoid.mk p.proj ⟶ FundamentalGroupoid.mk p.proj) = γ.asHom :=
    Quotient.exists_rep _
  -- The lift `Γ` of `g` from `p` ends at `p` or at the opposite orientation.
  let Γ := hcov.liftPath g p g.source
  have hΓ : VectorBundleOrientationCover.proj ∘ Γ = g := hcov.liftPath_lifts g p g.source
  have hΓ0 : Γ 0 = p := hcov.liftPath_zero g p g.source
  have hΓ1 : (Γ 1).proj = p.proj := (congrFun hΓ 1).trans g.target
  have hmono : (hcov.monodromy γ.toPath ⟨p, rfl⟩ : OrientationCover 𝓘(ℝ, E) M) = Γ 1 := by
    rw [FundamentalGroup.toPath, FundamentalGroup.toArrow, ← hg]
    exact hcov.monodromy_eq_apply_one hΓ hΓ0
  -- Over `p.proj`, the projection of the lift is a representative of `γ`.
  have hmk (o : _root_.Orientation ℝ (TangentSpace 𝓘(ℝ, E) p.proj) (Fin (finrank ℝ E)))
      (h1 : Γ 1 = ⟨p.proj, o⟩) :
      (Path.Homotopic.Quotient.mk
        ((⟨Γ, hΓ0, h1⟩ : Path p ⟨p.proj, o⟩).map VectorBundleOrientationCover.continuous_proj) :
          FundamentalGroupoid.mk p.proj ⟶ FundamentalGroupoid.mk p.proj) = γ.asHom := by
    rw [← hg]
    congr 1
    ext t
    exact congrFun hΓ t
  rcases VectorBundleOrientationCover.eq_or_eq_deck (Fintype.card_fin (finrank ℝ E)) hΓ1
    with h1 | h1
  · -- The lift is a loop: both characters are `1`.
    have h1' : Γ 1 = ⟨p.proj, p.orientation⟩ := h1
    have hγ := localOrientationTransport_coverLocalOrientation hE ⟨Γ, hΓ0, h1'⟩
    rw [hmk _ h1'] at hγ
    rw [(TauCeti.orientationCharacter_eq_one_iff hE γ _).2 hγ,
      (VectorBundleOrientationCover.orientationCharacter_eq_one_iff_monodromy_eq _ γ
        ⟨p, rfl⟩).2 (Subtype.ext (hmono.trans h1))]
  · -- The lift ends at the opposite orientation: both characters are `-1`.
    have h1' : Γ 1 = ⟨p.proj, -p.orientation⟩ :=
      h1.trans (VectorBundleOrientationCover.deck_apply p)
    have hγ := localOrientationTransport_coverLocalOrientation hE ⟨Γ, hΓ0, h1'⟩
    rw [hmk _ h1', coverLocalOrientation_neg] at hγ
    rw [(TauCeti.orientationCharacter_eq_neg_one_iff hE γ _).2 hγ,
      (VectorBundleOrientationCover.orientationCharacter_eq_neg_one_iff _ γ ⟨p, rfl⟩).2
        (hmono.trans h1)]

/-- **The homological orientation character is the orientation character of the tangent
bundle.** For a smooth manifold `M` of dimension `d` and a loop at `x`, transport along the loop
preserves the local orientations of `M` at `x`, the generators of `H_d(M, M ∖ {x}; ℤ)`, exactly
when it preserves the orientations of the tangent space `TₓM`. -/
theorem orientationCharacter_eq_orientationCharacter_tangentSpace {d : ℕ}
    (hd : finrank ℝ E = d) (x : M) :
    TauCeti.orientationCharacter hd x =
      VectorBundleOrientationCover.orientationCharacter E (TangentSpace 𝓘(ℝ, E))
        (Fintype.card_fin (finrank ℝ E)) x := by
  cases d with
  | succ n => exact orientationCharacter_eq_of_finrank_eq_succ hd x
  | zero =>
    -- A manifold of dimension `0` is discrete, so its loops are constant.
    have : Subsingleton E := Module.finrank_zero_iff.1 hd
    have : DiscreteTopology M := ChartedSpace.discreteTopology (H := E) M
    ext1 γ
    obtain ⟨g, hg⟩ : ∃ g : Path x x, (Path.Homotopic.Quotient.mk g :
        FundamentalGroupoid.mk x ⟶ FundamentalGroupoid.mk x) = γ.asHom :=
      Quotient.exists_rep _
    have hg' : g = Path.refl x :=
      Path.ext (funext fun t ↦ (g.continuous.isConst_of_preconnectedSpace t 0).trans g.source)
    subst hg'
    have hγ : γ = 1 := by
      rw [FundamentalGroup.one_def]
      exact (congrArg CategoryTheory.End.of hg).symm
    rw [hγ, map_one, map_one]

/-- **The orientation local system of a manifold is the sign local system of its orientation
double cover.** With coefficients in a commutative ring `R`, the rank-one local system of local
orientations of `M` (`TauCeti.RankOneLocalSystem.orientation`) is the sign local system of the
orientation double cover of the tangent bundle. -/
theorem rankOneLocalSystem_orientation_eq_signRankOneLocalSystem (R : Type*) [CommRing R]
    {d : ℕ} (hd : finrank ℝ E = d) (x : M) :
    RankOneLocalSystem.orientation R hd x =
      (isCoveringMap_proj 𝓘(ℝ, E) M).signRankOneLocalSystem R
        (VectorBundleOrientationCover.finite_fiber (Fintype.card_fin (finrank ℝ E)) x) :=
  RankOneLocalSystem.monodromy_injective <| by
    rw [RankOneLocalSystem.monodromy_orientation,
      IsCoveringMap.monodromy_signRankOneLocalSystem,
      orientationCharacter_eq_orientationCharacter_tangentSpace hd,
      VectorBundleOrientationCover.orientationCharacter_eq_signCharacter]

end TauCeti.Manifold.OrientationCover
