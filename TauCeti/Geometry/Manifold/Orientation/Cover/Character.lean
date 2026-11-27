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
public import TauCeti.Topology.VectorBundle.Orientation.Cover.Character.Basic

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
the cover, with `ω` an orientation of `TₓM`, this gives a local orientation `ℓ(p)` of `M` at `x`
(`TauCeti.Manifold.OrientationCover.coverLocalOrientation`).

* The deck involution `(x, ω) ↦ (x, -ω)` has local index `-1` for the canonical orientation
  (`TauCeti.Manifold.OrientationCover.localIndex_deck`), and lies over the identity of `M`, so
  `ℓ(x, -ω) = -ℓ(x, ω)` (`TauCeti.Manifold.OrientationCover.coverLocalOrientation_neg`).
* The covering map intertwines the transport of local orientations
  (`IsLocalHomeomorph.localOrientationEquiv_localOrientationTransport`), and the canonical
  orientation of `M'` is invariant under transport. So along a path `δ` in `M'`, transport in
  `M` along the projection of `δ` carries `ℓ` at the start of `δ` to `ℓ` at its end
  (`TauCeti.Manifold.OrientationCover.localOrientationTransport_coverLocalOrientation`).

Lift a loop `γ` at `x` to `M'` from `(x, ω)`. It ends at `(x, ω)` exactly when the tangent
character of `γ` is `1`, and at `(x, -ω)` exactly when it is `-1`. Transport along `γ` then fixes,
respectively reverses, the local orientation `ℓ(x, ω)`, which is what the homological character
records.

In dimension `0` the manifold is discrete, so its fundamental groups are trivial and so are both
characters.

The same two facts identify the local systems themselves, with integer coefficients and not only
their monodromy. The orientation local system `o(TM)` of the tangent bundle
(`TauCeti.VectorBundleOrientationCover.signLocalSystem`), whose fibre over `x` is the integer
functions on the two orientations of `TₓM` that change sign under reversal, is isomorphic to the
local homology system `x ↦ H_d(M, M ∖ {x}; ℤ)` (`TauCeti.localHomologySystem`) when `d > 0`
(`TauCeti.Manifold.OrientationCover.signLocalSystemIsoLocalHomologySystem`): a sign function `f`
goes to `f ω • ℓ(x, ω)`, which does not depend on the choice of `ω`, since both factors change sign
with it, and which commutes with transport, since the lift of a path from `(x, ω)` carries the
value of `f` at `ω` and the local orientation `ℓ(x, ω)` to the corresponding data at its end. No
connectedness of `M` is needed. So homology twisted by `o(TM)` is homology with coefficients in the
homological orientation system of `M`, the coefficients of Poincaré duality for nonorientable
manifolds.

## Main results

* `TauCeti.Manifold.OrientationCover.orientationCharacter_eq_orientationCharacter_tangentSpace`:
  the homological orientation character of `M` is the orientation character of its tangent
  bundle.
* `TauCeti.Manifold.OrientationCover.rankOneLocalSystem_orientation_eq_signRankOneLocalSystem`:
  the orientation local system of `M` is the sign local system of its orientation double cover.
* `TauCeti.Manifold.OrientationCover.signLocalSystemIsoLocalHomologySystem`: the orientation local
  system of the tangent bundle is isomorphic to the local homology system of `M` in its dimension,
  computed on fibres by
  `TauCeti.Manifold.OrientationCover.signLocalSystemIsoLocalHomologySystem_hom_app_apply`.

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

/-- **The local orientation of `M` read from a point of its orientation cover.** At a point
`p = (x, ω)` of the cover, with `ω` an orientation of `TₓM`, the canonical homological orientation
of the cover at `p`, read in `M` through the covering map, a local homeomorphism, is a local
orientation of `M` at `x`, a generator of `H_d(M, M ∖ {x}; ℤ)`. -/
def coverLocalOrientation (p : OrientationCover 𝓘(ℝ, E) M) :
    LocalOrientation M p.proj (n + 1) :=
  (isCoveringMap_proj 𝓘(ℝ, E) M).isLocalHomeomorph.localOrientationEquiv p (n + 1)
    (homologicalOrientation hE p)

/-- The local orientation read from a point `p` of the orientation cover is the canonical
homological orientation of the cover at `p`, read in `M` through the covering map. -/
theorem coverLocalOrientation_def (p : OrientationCover 𝓘(ℝ, E) M) :
    coverLocalOrientation hE p =
      (isCoveringMap_proj 𝓘(ℝ, E) M).isLocalHomeomorph.localOrientationEquiv p (n + 1)
        (homologicalOrientation hE p) :=
  (rfl)

/-- **The local orientations read from the two points of a fibre are opposite**: reversing the
orientation of `TₓM` reverses the local orientation of `M` at `x` read from the cover. -/
theorem coverLocalOrientation_neg (p : OrientationCover 𝓘(ℝ, E) M) :
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
theorem localOrientationTransport_coverLocalOrientation
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

/-! ### The orientation local system -/

section LocalSystem

open VectorBundleOrientationCover

/-- The orientation of `TₓM` given by a basis of the model space. It selects the components of
`TauCeti.Manifold.OrientationCover.signLocalSystemIsoLocalHomologySystem`, which do not depend on
it. -/
private def baseOrientation (x : M) :
    _root_.Orientation ℝ (TangentSpace 𝓘(ℝ, E) x) (Fin (finrank ℝ E)) :=
  (Module.finBasis ℝ E).orientation

/-- On the fibre over `x`, read at an orientation `ω` of `TₓM`: a sign function `f` goes to
`f ω • ℓ(x, ω)`, with `ℓ(x, ω)` the local orientation read from the cover. -/
private def fiberLinearEquiv (x : M)
    (ω : _root_.Orientation ℝ (TangentSpace 𝓘(ℝ, E) x) (Fin (finrank ℝ E))) :
    (signLocalSystem E (TangentSpace 𝓘(ℝ, E) : M → Type) ℤ (Fintype.card_fin _)).obj
        (FundamentalGroupoid.mk x) ≃ₗ[ℤ]
      (localHomologySystem (A := ModuleCat.{0} ℤ) (ModuleCat.of ℤ (ULift.{0} ℤ)) M E
        (n + 1)).obj (FundamentalGroupoid.mk x) :=
  (signLocalSystemFiberEquiv (Fintype.card_fin _) ω).trans
    ((coverLocalOrientation hE ⟨x, ω⟩).property.linearEquiv
      (singularHomologyComplSingletonIsoOfFinrankEq (A := ModuleCat.{0} ℤ)
        (ModuleCat.of ℤ (ULift.{0} ℤ)) (chartAt E x) (mem_chart_source E x) hE))

private theorem fiberLinearEquiv_apply (x : M)
    (ω : _root_.Orientation ℝ (TangentSpace 𝓘(ℝ, E) x) (Fin (finrank ℝ E)))
    (f : (signLocalSystem E (TangentSpace 𝓘(ℝ, E) : M → Type) ℤ (Fintype.card_fin _)).obj
      (FundamentalGroupoid.mk x)) :
    fiberLinearEquiv hE x ω f =
      signLocalSystemFiberEquiv (Fintype.card_fin _) ω f • (coverLocalOrientation hE ⟨x, ω⟩).val :=
  IsLocalOrientation.linearEquiv_apply _ _ _

/-- Read at a point `p` of the cover over `x`, the fibre map is evaluation at `p` times the local
orientation read from `p`, whichever orientation `ω` of `TₓM` it was defined with. -/
private theorem fiberLinearEquiv_eq (p : OrientationCover 𝓘(ℝ, E) M)
    (ω : _root_.Orientation ℝ (TangentSpace 𝓘(ℝ, E) p.proj) (Fin (finrank ℝ E)))
    (f : (signLocalSystem E (TangentSpace 𝓘(ℝ, E) : M → Type) ℤ (Fintype.card_fin _)).obj
      (FundamentalGroupoid.mk p.proj)) :
    fiberLinearEquiv hE p.proj ω f =
      liftFiberEquiv (Fintype.card_fin _) p rfl f • (coverLocalOrientation hE p).val := by
  obtain ⟨x, o⟩ := p
  rw [fiberLinearEquiv_apply]
  rw [liftFiberEquiv_apply]
  rcases _root_.Orientation.eq_or_eq_neg ω o (Nat.card_fin _) with h | h
  · rw [h, signLocalSystemFiberEquiv_apply]
  · -- Both the evaluation and the local orientation change sign with the orientation.
    rw [h, signLocalSystemFiberEquiv_neg, coverLocalOrientation_neg hE ⟨x, o⟩,
      LocalOrientation.coe_neg, signLocalSystemFiberEquiv_apply]
    -- The two signs cancel: `(-a) • -v = a • v`.
    rw [zsmul_neg', neg_neg]

/-- **Naturality of the fibre maps.** Transport along a path class `γ` from `x` to `y` in the
orientation local system of the tangent bundle and in the local homology system is intertwined by
the fibre maps: the lift of `γ` to the cover from `(x, ω)` carries both the value of a sign
function at `ω` and the local orientation read from `(x, ω)` to the corresponding data at its
end. -/
private theorem fiberLinearEquiv_naturality {x y : M}
    (γ : FundamentalGroupoid.mk x ⟶ FundamentalGroupoid.mk y)
    (f : (signLocalSystem E (TangentSpace 𝓘(ℝ, E) : M → Type) ℤ (Fintype.card_fin _)).obj
      (FundamentalGroupoid.mk x)) :
    fiberLinearEquiv hE y (baseOrientation y)
        ((signLocalSystem E (TangentSpace 𝓘(ℝ, E) : M → Type) ℤ (Fintype.card_fin _)).map γ f) =
      (localHomologySystem (A := ModuleCat.{0} ℤ) (ModuleCat.of ℤ (ULift.{0} ℤ)) M E (n + 1)).map γ
        (fiberLinearEquiv hE x (baseOrientation x) f) := by
  have hcov := isCoveringMap_proj 𝓘(ℝ, E) M
  let p : OrientationCover 𝓘(ℝ, E) M := ⟨x, baseOrientation x⟩
  -- Lift a representative `g` of `γ` to the cover from `p`.
  obtain ⟨g, hg⟩ : ∃ g : Path x y, (Path.Homotopic.Quotient.mk g :
      FundamentalGroupoid.mk x ⟶ FundamentalGroupoid.mk y) = γ := Quotient.exists_rep _
  obtain ⟨Γ, hΓ, hΓ0⟩ : ∃ Γ : C(unitInterval, OrientationCover 𝓘(ℝ, E) M),
      VectorBundleOrientationCover.proj ∘ Γ = g ∧ Γ 0 = p :=
    ⟨_, hcov.liftPath_lifts g p g.source, hcov.liftPath_zero g p g.source⟩
  have hΓ1 : (Γ 1).proj = y := (congrFun hΓ 1).trans g.target
  subst hΓ1
  have hmono : hcov.monodromy γ ⟨p, rfl⟩ = ⟨Γ 1, rfl⟩ := by
    rw [← hg]
    exact Subtype.ext (hcov.monodromy_eq_apply_one hΓ hΓ0)
  -- The projection of the lift is a representative of `γ`.
  have hγ : (Path.Homotopic.Quotient.mk
      ((⟨Γ, hΓ0, rfl⟩ : Path p (Γ 1)).map VectorBundleOrientationCover.continuous_proj) :
        FundamentalGroupoid.mk x ⟶ FundamentalGroupoid.mk (Γ 1).proj) = γ := by
    rw [← hg]
    congr 1
    ext t
    exact congrFun hΓ t
  -- Transport carries the local orientation read from `p` to the one read from `Γ 1`.
  have htr := congrArg Subtype.val (localOrientationTransport_coverLocalOrientation hE
    (⟨Γ, hΓ0, rfl⟩ : Path p (Γ 1)))
  rw [coe_localOrientationTransport, hγ] at htr
  have htr' (c : ℤ) : (localHomologySystem (A := ModuleCat.{0} ℤ) (ModuleCat.of ℤ (ULift.{0} ℤ))
      M E (n + 1)).map γ (c • (coverLocalOrientation hE p).val) =
        c • (coverLocalOrientation hE (Γ 1)).val :=
    (map_zsmul _ c _).trans (congrArg (c • ·) htr)
  -- Transport carries the value of a sign function at `p` to its value at `Γ 1`.
  have hval := signLocalSystemObjEquiv_map_apply_monodromy (Fintype.card_fin _) γ f ⟨p, rfl⟩
  rw [hmono] at hval
  rw [fiberLinearEquiv_eq hE (Γ 1), fiberLinearEquiv_apply, htr', liftFiberEquiv_apply, hval,
    signLocalSystemFiberEquiv_apply]

/-- **The orientation local system of the tangent bundle is the homological orientation system.**
For a manifold `M` of dimension `n + 1`, the integral orientation local system `o(TM)` of its
tangent bundle, whose fibre over `x` is the functions on the two orientations of `TₓM` that change
sign under reversal (`TauCeti.VectorBundleOrientationCover.signLocalSystem`), is isomorphic to the
local homology system `x ↦ Hₙ₊₁(M, M ∖ {x}; ℤ)` (`TauCeti.localHomologySystem`), the orientation
local system of `M` built from local homology. On the fibre over `x` the isomorphism sends a sign
function `f` to `f ω • ℓ(x, ω)` for either orientation `ω` of `TₓM`, where `ℓ(x, ω)` is the local
orientation read from the point `(x, ω)` of the orientation cover
(`TauCeti.Manifold.OrientationCover.signLocalSystemIsoLocalHomologySystem_hom_app_apply`). -/
def signLocalSystemIsoLocalHomologySystem :
    signLocalSystem E (TangentSpace 𝓘(ℝ, E) : M → Type) ℤ (Fintype.card_fin _) ≅
      localHomologySystem (A := ModuleCat.{0} ℤ) (ModuleCat.of ℤ (ULift.{0} ℤ)) M E (n + 1) :=
  NatIso.ofComponents (fun X ↦ (fiberLinearEquiv hE X.as (baseOrientation X.as)).toModuleIso)
    fun {X Y} γ ↦ ModuleCat.hom_ext (LinearMap.ext (fiberLinearEquiv_naturality hE (x := X.as)
      (y := Y.as) γ))

/-- **The isomorphism of orientation local systems on a fibre.** For either orientation `ω` of
`TₓM`, `TauCeti.Manifold.OrientationCover.signLocalSystemIsoLocalHomologySystem` sends a sign
function `f` on the orientations of `TₓM` to its value at `ω` times the local orientation of `M` at
`x` read from the point `(x, ω)` of the orientation cover. -/
theorem signLocalSystemIsoLocalHomologySystem_hom_app_apply (x : M)
    (ω : _root_.Orientation ℝ (TangentSpace 𝓘(ℝ, E) x) (Fin (finrank ℝ E)))
    (f : (signLocalSystem E (TangentSpace 𝓘(ℝ, E) : M → Type) ℤ (Fintype.card_fin _)).obj
      (FundamentalGroupoid.mk x)) :
    (signLocalSystemIsoLocalHomologySystem hE).hom.app (FundamentalGroupoid.mk x) f =
      signLocalSystemFiberEquiv (Fintype.card_fin _) ω f • (coverLocalOrientation hE ⟨x, ω⟩).val :=
  (fiberLinearEquiv_eq hE ⟨x, ω⟩ _ f).trans (by
    rw [liftFiberEquiv_apply, signLocalSystemFiberEquiv_apply])

end LocalSystem

end TauCeti.Manifold.OrientationCover
