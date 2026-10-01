/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.Cup.Cohomology
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Functoriality

/-!
# Naturality of the cup product on continuous cohomology

Let `φ : H →ₜ* G` be a continuous homomorphism of topological groups, `P : TopPairing X Y Z` a
coefficient pairing of topological `G`-representations and `P' : TopPairing X' Y' Z'` one of
topological `H`-representations. Morphisms `fX : res φ X ⟶ X'`, `fY : res φ Y ⟶ Y'` and
`fZ : res φ Z ⟶ Z'` intertwining the two pairings, `fZ (P.bil x y) = P'.bil (fX x) (fY y)`, make
the maps `ContinuousCohomology.map φ f` of the three compatible pairs multiplicative for the cup
products of `TauCeti.TopPairing.cup`:

```text
map φ fZ (a ⌣ b) = map φ fX a ⌣ map φ fY b.
```

The identity is available at every level of the construction, not only on cohomology classes:
on the coinduced resolution, for the Alexander–Whitney pairing `TauCeti.TopPairing.resolutionCup`
and the map `F ↦ f ∘ F ∘ φ` of the compatible pair; on homogeneous cochains, for
`TauCeti.TopPairing.cupCochain` and `ContinuousCohomology.cochainsMap`; and on cocycles, for
`TauCeti.TopPairing.cupCocycles` and `ContinuousCohomology.cocyclesMap`. Arguments that work with
explicit representatives can therefore compare the images of a cup product and the cup product of
the images before passing to classes.

The three named instances of `ContinuousCohomology.map` give the three compatibilities of the cup
product with the change-of-group and change-of-coefficient maps: restriction to a subgroup,
inflation from a quotient, and a coefficient map. In each, the second pairing is supplied
together with its defining relation to the first, since restriction leaves the coefficient map
unchanged while inflation compares the pairings after including the invariants into the ambient
objects. The restricted pairing `TauCeti.TopPairing.res` is the canonical choice in the first case.

## Main results

* `TauCeti.TopPairing.resolutionCup_resolutionMap`, `TauCeti.TopPairing.cupCochain_cochainsMap`,
  `TauCeti.TopPairing.cupCocycles_cocyclesMap`: naturality on the resolution, on homogeneous
  cochains and on cocycles.
* `TauCeti.TopPairing.cup_map`: **naturality of the cup product in compatible pairs**.
* `TauCeti.TopPairing.cup_res`, `TauCeti.TopPairing.cup_infl`, `TauCeti.TopPairing.cup_coeffMap`:
  compatibility with restriction, inflation and coefficient maps;
  `TauCeti.TopPairing.cup_coeffMap_left_id` is the case of a coefficient map on the right factor
  only.

## References

* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., Springer (2008),
  Chapter I, §4, (1.4.2), and §5, (1.5.3).
* K. S. Brown, *Cohomology of Groups*, GTM 87, Springer (1982), Chapter V, §3.
-/

public section

namespace TauCeti

open CategoryTheory _root_.ContinuousCohomology

universe u v w

namespace TopPairing

/-! ### Naturality in compatible pairs -/

section Map

variable {R : Type u} [CommRing R] [TopologicalSpace R]
  {G H : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
  {X Y Z : TopRep.{max v w} R G} {X' Y' Z' : TopRep.{max v w} R H}
  (P : TopPairing X Y Z) (P' : TopPairing X' Y' Z') (φ : H →ₜ* G)
  (fX : TopRep.res (φ : H →* G) X ⟶ X') (fY : TopRep.res (φ : H →* G) Y ⟶ Y')
  (fZ : TopRep.res (φ : H →* G) Z ⟶ Z')
  (hpair : ∀ (x : X.V) (y : Y.V), fZ (P.bil x y) = P'.bil (fX x) (fY y))

include hpair

/-- The pointwise pairing is natural in compatible pairs. -/
theorem pointwise_resolutionMap : ∀ (n k : ℕ) (hk : k = n) (x : X.V)
    (F : (TopRep.resolutionX Y n).V),
    (resolutionMap φ fZ k) (P.pointwise n k hk (x, F)) =
      P'.pointwise n k hk (fX x, (resolutionMap φ fY n) F)
  | 0, 0, _, x, F => by
    rw [pointwise_zero_apply, pointwise_zero_apply]
    exact hpair x F
  | n + 1, k + 1, hk, x, F => ContinuousMap.ext fun h ↦ by
    rw [ContinuousCohomology.resolutionMap_succ_apply, pointwise_succ_apply, pointwise_succ_apply,
      ContinuousCohomology.resolutionMap_succ_apply]
    exact pointwise_resolutionMap n k (Nat.succ.inj hk) x (F (φ h))

/-- **The Alexander–Whitney pairing on the resolution is natural in compatible pairs**: the map
`F ↦ f ∘ F ∘ φ` induced on the resolution takes `a ⌣ b` to the pairing of the images. -/
theorem resolutionCup_resolutionMap : ∀ (m n k : ℕ) (hk : k = n + m)
    (a : (TopRep.resolutionX X (m + 1)).V) (b : (TopRep.resolutionX Y (n + 1)).V),
    (resolutionMap φ fZ (k + 1)) (P.resolutionCup m n k hk (a, b)) =
      P'.resolutionCup m n k hk
        ((resolutionMap φ fX (m + 1)) a, (resolutionMap φ fY (n + 1)) b)
  -- The induced map acts pointwise on the values and by precomposition on the arguments; both
  -- commute with the Alexander–Whitney formula, so the identity is checked argument by argument
  -- along the recursion defining `resolutionCup`.
  | 0, n, k, hk, a, b => ContinuousMap.ext fun h ↦ by
    simp only [ContinuousCohomology.resolutionMap_succ_apply φ fZ,
      ContinuousCohomology.resolutionMap_succ_apply φ fX,
      ContinuousCohomology.resolutionMap_succ_apply φ fY, P.resolutionCup_zero_apply,
      P'.resolutionCup_zero_apply, P.pointwise_resolutionMap P' φ fX fY fZ hpair,
      resolutionMap_zero]
  | m + 1, n, k + 1, hk, a, b => ContinuousMap.ext fun h ↦ by
    rw [ContinuousCohomology.resolutionMap_succ_apply, resolutionCup_succ_apply,
      resolutionCup_succ_apply, ContinuousCohomology.resolutionMap_succ_apply]
    exact resolutionCup_resolutionMap m n k (Nat.succ.inj hk) (a (φ h)) b

/-- The resolution pairing in degree `m + n` is natural in compatible pairs. -/
theorem resolutionCupPairing_resolutionMap (m n : ℕ) (a : (TopRep.resolution'X X m).V)
    (b : (TopRep.resolution'X Y n).V) :
    (resolutionMap φ fZ (m + n + 1)) (P.resolutionCupPairing m n a b) =
      P'.resolutionCupPairing m n ((resolutionMap φ fX (m + 1)) a)
        ((resolutionMap φ fY (n + 1)) b) := by
  rw [resolutionCupPairing_apply, resolutionCupPairing_apply]
  exact P.resolutionCup_resolutionMap P' φ fX fY fZ hpair m n (m + n) _ a b

/-- **The cup product of homogeneous cochains is natural in compatible pairs.** -/
theorem cupCochain_cochainsMap (m n : ℕ) (a : (TopRep.homogeneousCochains X).X m)
    (b : (TopRep.homogeneousCochains Y).X n) :
    (cochainsMap φ fZ).f (m + n) (P.cupCochain m n a b) =
      P'.cupCochain m n ((cochainsMap φ fX).f m a) ((cochainsMap φ fY).f n b) := by
  apply Subtype.ext
  rw [ContinuousCohomology.coe_cochainsMap_f_apply, coe_cupCochain, coe_cupCochain,
    ContinuousCohomology.coe_cochainsMap_f_apply, ContinuousCohomology.coe_cochainsMap_f_apply]
  exact P.resolutionCupPairing_resolutionMap P' φ fX fY fZ hpair m n a.1 b.1

/-- **The cup product of cocycles is natural in compatible pairs.** -/
theorem cupCocycles_cocyclesMap (m n : ℕ) (a : cocycles X m) (b : cocycles Y n) :
    cocyclesMap φ fZ (m + n) (P.cupCocycles m n a b) =
      P'.cupCocycles m n (cocyclesMap φ fX m a) (cocyclesMap φ fY n b) := by
  apply (TopRep.homogeneousCochains Z').iCycles_injective (m + n)
  rw [ContinuousCohomology.iCycles_cocyclesMap_apply, iCycles_cupCocycles, iCycles_cupCocycles,
    ContinuousCohomology.iCycles_cocyclesMap_apply, ContinuousCohomology.iCycles_cocyclesMap_apply]
  exact P.cupCochain_cochainsMap P' φ fX fY fZ hpair m n _ _

/-- **Naturality of the cup product in compatible pairs** (NSW (1.4.2)): for a continuous
homomorphism `φ : H →ₜ* G` and morphisms `fX`, `fY`, `fZ` of the coefficients intertwining the
pairings `P` and `P'`, the induced maps on continuous cohomology satisfy
`map φ fZ (a ⌣ b) = map φ fX a ⌣ map φ fY b`. -/
theorem cup_map (m n : ℕ) (a : continuousCohomology m X) (b : continuousCohomology n Y) :
    _root_.ContinuousCohomology.map φ fZ (m + n) (P.cup m n a b) =
      P'.cup m n (_root_.ContinuousCohomology.map φ fX m a)
        (_root_.ContinuousCohomology.map φ fY n b) := by
  obtain ⟨a, rfl⟩ := (TopRep.homogeneousCochains X).homologyπ_surjective m a
  obtain ⟨b, rfl⟩ := (TopRep.homogeneousCochains Y).homologyπ_surjective n b
  rw [cup_π, ContinuousCohomology.map_π_apply, ContinuousCohomology.map_π_apply,
    ContinuousCohomology.map_π_apply, cup_π]
  exact congrArg _ (P.cupCocycles_cocyclesMap P' φ fX fY fZ hpair m n a b)

end Map

/-! ### Restriction, inflation and coefficient maps -/

section Instances

variable {R : Type u} [CommRing R] [TopologicalSpace R]
  {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {X Y Z : TopRep.{max v w} R G} (P : TopPairing X Y Z)

/-- **Naturality of the cup product in the coefficients** (NSW (1.4.2)): coefficient morphisms
`f`, `g`, `h` intertwining the pairings `P` and `P'` satisfy
`coeffMap h (a ⌣ b) = coeffMap f a ⌣ coeffMap g b`. -/
theorem cup_coeffMap {X' Y' Z' : TopRep.{max v w} R G} (P' : TopPairing X' Y' Z')
    (f : X ⟶ X') (g : Y ⟶ Y') (h : Z ⟶ Z')
    (hcompat : ∀ (x : X.V) (y : Y.V), h (P.bil x y) = P'.bil (f x) (g y)) (m n : ℕ)
    (a : continuousCohomology m X) (b : continuousCohomology n Y) :
    ContinuousCohomology.coeffMap h (m + n) (P.cup m n a b) =
      P'.cup m n (ContinuousCohomology.coeffMap f m a) (ContinuousCohomology.coeffMap g n b) := by
  simp only [ContinuousCohomology.coeffMap_def]
  exact P.cup_map P' (ContinuousMonoidHom.id G) f g h hcompat m n a b

/-- Naturality of the cup product in the coefficients of the right factor only: coefficient
morphisms `g`, `h` with `h (P.bil x y) = P'.bil x (g y)` satisfy
`coeffMap h (a ⌣ b) = a ⌣' coeffMap g b`. This is `cup_coeffMap` with `f = 𝟙 X`. -/
theorem cup_coeffMap_left_id {Y' Z' : TopRep.{max v w} R G} (P' : TopPairing X Y' Z')
    (g : Y ⟶ Y') (h : Z ⟶ Z')
    (hcompat : ∀ (x : X.V) (y : Y.V), h (P.bil x y) = P'.bil x (g y)) (m n : ℕ)
    (a : continuousCohomology m X) (b : continuousCohomology n Y) :
    ContinuousCohomology.coeffMap h (m + n) (P.cup m n a b) =
      P'.cup m n a (ContinuousCohomology.coeffMap g n b) := by
  have := P.cup_coeffMap P' (𝟙 X) g h (fun x y ↦ by rw [hcompat, CategoryTheory.id_apply]) m n a b
  rwa [ContinuousCohomology.coeffMap_id] at this

/-- **Restriction preserves cup products** (NSW (1.5.3)(i)): for a subgroup `S ≤ G` and a pairing
`Pres` of the restricted coefficients with the same underlying bilinear map as `P`,
`res S (a ⌣ b) = res S a ⌣ res S b`. -/
theorem cup_res (S : Subgroup G)
    (Pres : TopPairing (TopRep.res S.subtype X) (TopRep.res S.subtype Y) (TopRep.res S.subtype Z))
    (hPres : Pres.bil = P.bil) (m n : ℕ) (a : continuousCohomology m X)
    (b : continuousCohomology n Y) :
    ContinuousCohomology.res S Z (m + n) (P.cup m n a b) =
      Pres.cup m n (ContinuousCohomology.res S X m a) (ContinuousCohomology.res S Y n b) := by
  simp only [ContinuousCohomology.res_def]
  exact P.cup_map Pres (ContinuousMonoidHom.subgroupSubtype S) (𝟙 _) (𝟙 _) (𝟙 _)
    (fun x y ↦ by rw [hPres]; rfl) m n a b

/-- **Inflation preserves cup products** (NSW (1.5.3)(iii)): for a normal subgroup `N ≤ G` and a
pairing `Pinv` of the `N`-invariants that agrees with `P` after inclusion of the invariants into
the ambient objects, `infl N (a ⌣ b) = infl N a ⌣ infl N b`. -/
theorem cup_infl (N : Subgroup G) [N.Normal]
    (Pinv : TopPairing (TopRep.quotientToInvariants X N) (TopRep.quotientToInvariants Y N)
      (TopRep.quotientToInvariants Z N))
    (hPinv : ∀ (x : (TopRep.quotientToInvariants X N).V) (y : (TopRep.quotientToInvariants Y N).V),
      TopRep.quotientToInvariantsι Z N (Pinv.bil x y) =
        P.bil (TopRep.quotientToInvariantsι X N x) (TopRep.quotientToInvariantsι Y N y))
    (m n : ℕ) (a : continuousCohomology m (TopRep.quotientToInvariants X N))
    (b : continuousCohomology n (TopRep.quotientToInvariants Y N)) :
    -- Ascribed: without the ascriptions, elaborating `=` between the two sides runs a coercion
    -- search on the cohomology carriers over `G ⧸ N` that does not terminate in time. (This
    -- follows the ascription idiom of #8346.)
    (ContinuousCohomology.infl N Z (m + n) (Pinv.cup m n a b) :) =
      (P.cup m n (ContinuousCohomology.infl N X m a) (ContinuousCohomology.infl N Y n b) :) := by
  simp only [ContinuousCohomology.infl_def]
  exact Pinv.cup_map P (ContinuousMonoidHom.quotientMk N) (TopRep.quotientToInvariantsι X N)
    (TopRep.quotientToInvariantsι Y N) (TopRep.quotientToInvariantsι Z N) hPinv m n a b

end Instances

end TopPairing

end TauCeti
