/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.VectorBundle.FiberCast
public import TauCeti.Topology.VectorBundle.Thom.FiberwiseEquiv
public import TauCeti.Topology.VectorBundle.Thom.Orientation.TwistedLift

/-!
# The Thom isomorphism of a cover lifting to the orientation cover

Let `E → B` be a real vector bundle of rank `r`, `B'` its orientation double cover, whose points
are the pairs of a point of `B` and an orientation of the fibre there, and let `f : X → B` be a
continuous map with a continuous lift `s : X → B'`, so that `s x` is an orientation of the fibre
of `E` over `f x`. Equivalently, `s` is an orientation of the pull-back `f^*E`. Then `f^*E` maps to
the pull-back `E'` of `E` to the orientation cover, by the identity of each fibre `E_{f x}`, read
as the fibre of `E'` over `s x` (`TauCeti.VectorBundleOrientationCover.thomPairMapOfLift`). This
is a map of Thom pairs `(f^*E, (f^*E)₀) ⟶ (E', E'₀)` over `s`, and followed by the projection
`(E', E'₀) ⟶ (E, E₀)` it is the canonical map of the pull-back
(`TauCeti.VectorBundleOrientationCover.thomPairMapOfLift_comp_coverThomPairMap`).

Now let a group `G` act on `X` and on the Thom pair of `f^*E`, compatibly with the projection and
keeping the underlying vectors of `E`, and suppose that `s` is equivariant for a homomorphism
`ρ : G →* ℤˣ`: `s(g • x) = ρ(g) • s(x)`, where `-1` reverses the orientation. Then the map of Thom
pairs over `s` is equivariant along `ρ`
(`TauCeti.VectorBundleOrientationCover.thomPairMapOfLift_fst_smul`), so it pulls the Thom cocycle
of `E'` which the deck involution negates
(`TauCeti.VectorBundleOrientationCover.exists_isSemiInvariantCocycle_isThomClass`) back to a Thom
cocycle of `f^*E` which is semi-invariant for the character `χ = ρ` of `G` with values in `kˣ`
(`TauCeti.VectorBundleOrientationCover.exists_isSemiInvariantCocycle_isThomClass_of_lift`). If
moreover `(f^*E, (f^*E)₀) ⟶ (E, E₀)` and `f : X → B` are quotient covering maps for `G`, the
equivariant descent of the Thom isomorphism (`TauCeti.quotientTwistedHomologyThomIso`) gives, for
every commutative ring `k` and every representation `D` of `G`,

`H_{q + r}(E, E₀; L_D) ≅ H_q(B; L_{D ⊗ k_χ})`,

where `L_D` and `L_{D ⊗ k_χ}` are the local systems associated to `D` and `D ⊗ k_χ` through the
covers `f^*E → E` and `X → B`
(`TauCeti.VectorBundleOrientationCover.nonempty_twistedHomology_iso_twistedHomology_of_lift`, stated
for any quotient `(Q, Q₀)` of the Thom pair of `f^*E` and any quotient `Z` of `X`). No orientation
of `E` and no hypothesis on `2` in `k` are needed.

The orientation double cover itself is the case `X = B'` with `s` the identity. Since the acting
group must lie in the universe of `B`, there `G` is the copy `ULift ℤˣ` of `ℤˣ` and `ρ` is
`MulEquiv.ulift`, so `L_{k_χ}` is the local system of the sign representation, which is the
orientation local system `o(E)`
(`TauCeti.VectorBundleOrientationCover.associatedLocalSystemSignIso`). That case, the Thom
isomorphism `H_{q + r}(E, E₀; k) ≅ H_q(B; o(E) ⊗ k)`, is proved in
`TauCeti.Topology.VectorBundle.Thom.Orientation.Cover.Descent`
(`TauCeti.VectorBundleOrientationCover.thomPairSingularHomologyIsoTwistedHomology`) and is not
restated here. For the universal cover of a locally path-connected, semilocally simply connected
base, `G = π₁(B)` acts by deck transformations, and
since the universal cover is simply connected its projection lifts to the orientation cover,
equivariantly along the orientation character `w₁ : π₁(B) →* ℤˣ` of `E`
(`TauCeti.VectorBundleOrientationCover.orientationCharacter`), which records whether a deck
transformation preserves or reverses the lifted orientations
(`TauCeti.VectorBundleOrientationCover.exists_lift_universalCover`, in
`TauCeti.Topology.VectorBundle.Orientation.Cover.UniversalCover`). Since every local system on a
path-connected such base is associated to its monodromy representation
(`TauCeti.UniversalCover.associatedLocalSystemMonodromyIso`), one can take for `D` the monodromy
of a local system `L` on `B`. Identifying `L_D` with `π^*L` and `L_{D ⊗ k_χ}` with `o(E) ⊗ L` would
then turn this case into the Thom isomorphism `H_{q + r}(E, E₀; π^*L) ≅ H_q(B; o(E) ⊗ L)`. Those
identifications, and the deck action on the Thom pair of the pull-back of `E` to the universal
cover, are not carried out here.

## Main definitions and results

In the namespace `TauCeti.VectorBundleOrientationCover`:

* `thomPairMapOfLift`: the map of Thom pairs `(f^*E, (f^*E)₀) ⟶ (E', E'₀)` over a lift `s` of `f`
  to the orientation cover.
* `thomPairMapOfLift_fst_apply`: its value on a vector.
* `TauCeti.IsThomClass.thomPairMapOfLift`: it pulls Thom classes back to Thom classes.
* `thomPairMapOfLift_fst_smul`: it is equivariant along `ρ` when `s` is.
* `exists_isSemiInvariantCocycle_isThomClass_of_lift`: `f^*E` has a Thom cocycle which is
  semi-invariant for the character `ρ`.
* `nonempty_twistedHomology_iso_twistedHomology_of_lift`: the Thom isomorphism
  `H_{q + r}(Q, Q₀; L_D) ≅ H_q(Z; L_{D ⊗ k_χ})` for quotients `(Q, Q₀)` of the Thom pair of `f^*E`
  and `Z` of `X` by quotient covering maps for `G`; the intended case is `(Q, Q₀) = (E, E₀)` and
  `Z = B`, once the caller supplies a `G`-action under which the canonical maps are such maps.

## References

* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton (1974), §10 (the Thom isomorphism) and §12 (the orientation double cover and twisted
  coefficients).
* E. H. Spanier, *Algebraic Topology*, McGraw-Hill (1966), Chapter 5, Section 7 (the Thom
  isomorphism with local coefficients).
-/

public section

noncomputable section

open Bundle CategoryTheory Module MonoidalCategory

namespace TauCeti.VectorBundleOrientationCover

universe u

variable {B : Type u} [TopologicalSpace B] {F : Type u} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {E : B → Type u} [TopologicalSpace (TotalSpace F E)] [∀ b, AddCommMonoid (E b)]
  [∀ b, Module ℝ (E b)] [∀ b, TopologicalSpace (E b)] [FiberBundle F E] [VectorBundle ℝ F E]
  {ι : Type} {X : Type u} [TopologicalSpace X] {f : C(X, B)}
  {s : C(X, VectorBundleOrientationCover F E ι)}

/-- The action `thomPairFstMulAction` of `ℤˣ` on the total space of the Thom pair of the pull-back
of `E` to the orientation cover, `-1` acting by the lift of the deck involution. -/
local instance liftThomPairFstMulAction : MulAction ℤˣ
    (thomPair F ((projection : C(VectorBundleOrientationCover F E ι, B)) *ᵖ E)).fst :=
  thomPairFstMulAction

/-- The action of `ℤˣ` on the total space of the Thom pair of the pull-back of `E` to the
orientation cover is continuous (`thomPairFstMulAction_continuousConstSMul`). -/
local instance liftThomPairFstContinuousConstSMul : ContinuousConstSMul ℤˣ
    (thomPair F ((projection : C(VectorBundleOrientationCover F E ι, B)) *ᵖ E)).fst :=
  thomPairFstMulAction_continuousConstSMul

/-! ### The map of Thom pairs over a lift to the orientation cover -/

section Map

/-- The identity of the fibres of `E`, from the pull-back `f^*E` to the pull-back of `E` to the
orientation cover over a lift `s` of `f`, is continuous on total spaces. -/
private theorem continuous_mk_fiberCast (hs : ∀ x, (s x).proj = f x) :
    Continuous fun v : TotalSpace F ((⇑f) *ᵖ E) ↦
      TotalSpace.mk' F (E := (projection : C(VectorBundleOrientationCover F E ι, B)) *ᵖ E)
        (s v.proj) (fiberCast (R := ℝ) (E := E) (hs v.proj).symm v.snd) := by
  refine Pullback.continuous_iff.2 ⟨s.continuous.comp (Pullback.continuous_proj F E f), ?_⟩
  -- the image in the total space of `E` keeps each vector
  convert Pullback.continuous_lift F E f using 1
  funext v
  exact mk_fiberCast (hs v.proj).symm v.snd

variable (F E) in
/-- **The map of Thom pairs over a lift to the orientation cover.** For a continuous map
`f : X → B` with a continuous lift `s : X → B'` to the orientation double cover of `E`, the map of
Thom pairs `(f^*E, (f^*E)₀) ⟶ (E', E'₀)` from the pull-back of `E` along `f` to its pull-back `E'`
to the orientation cover, which sends a vector of the fibre `E_{f x}` over `x` to the same vector
of the fibre `E_{f x}` of `E'` over `s x`. -/
def thomPairMapOfLift (hs : ∀ x, (s x).proj = f x) :
    thomPair F ((⇑f) *ᵖ E) ⟶
      thomPair F ((projection : C(VectorBundleOrientationCover F E ι, B)) *ᵖ E) :=
  thomPairMapOfFiberwise (g := s) (φ := fun x ↦ fiberCast (hs x).symm) (continuous_mk_fiberCast hs)

-- Not a simp lemma, as for `deckThomPairMap_fst_apply`: simplifying the coercion of the bundled
-- projection changes the implicit pull-back bundle in the right-hand side.
/-- The map of Thom pairs over a lift `s` sends a vector of the fibre `E_{f x}` over `x` to the same
vector, read as a vector of the fibre of `E'` over `s x`. -/
theorem thomPairMapOfLift_fst_apply (hs : ∀ x, (s x).proj = f x)
    (v : TotalSpace F ((⇑f) *ᵖ E)) :
    TopPair.Hom.fst (thomPairMapOfLift F E hs) v =
      TotalSpace.mk' F (E := (projection : C(VectorBundleOrientationCover F E ι, B)) *ᵖ E)
        (s v.proj) (fiberCast (R := ℝ) (E := E) (hs v.proj).symm v.snd) :=
  thomPairMapOfFiberwise_fst_apply _ v

-- Not a simp lemma, as for `deckThomPairMap_fst_proj`: simplifying the coercion of the bundled
-- projection changes the implicit pull-back bundle in the left-hand side.
/-- The map of Thom pairs over a lift `s` covers `s`. -/
theorem thomPairMapOfLift_fst_proj (hs : ∀ x, (s x).proj = f x)
    (v : TotalSpace F ((⇑f) *ᵖ E)) :
    (TopPair.Hom.fst (thomPairMapOfLift F E hs) v).proj = s v.proj :=
  congrArg TotalSpace.proj (thomPairMapOfLift_fst_apply hs v)

-- Not a simp lemma, for the same reason as `thomPairMapOfLift_fst_proj`.
/-- The map of Thom pairs over a lift keeps the underlying vectors of `E`. -/
theorem lift_thomPairMapOfLift_fst (hs : ∀ x, (s x).proj = f x)
    (v : TotalSpace F ((⇑f) *ᵖ E)) :
    Pullback.lift (projection : C(VectorBundleOrientationCover F E ι, B))
        (TopPair.Hom.fst (thomPairMapOfLift F E hs) v) = Pullback.lift f v :=
  (congrArg (Pullback.lift _) (thomPairMapOfLift_fst_apply hs v)).trans
    (mk_fiberCast (hs v.proj).symm v.snd)

/-- **The map of Thom pairs over a lift pulls Thom classes back to Thom classes.** The pull-back of
a Thom class of the pull-back `E'` of `E` to the orientation cover along the map of Thom pairs over
a lift `s` of `f` is a Thom class of `f^*E`: the map is the identity of each fibre `E_{f x}`. -/
theorem _root_.TauCeti.IsThomClass.thomPairMapOfLift {C : Type*} [Category C]
    [Limits.HasCoproducts.{u} C] [Abelian C] {R : C} {k : Type*} [Ring k] [Linear k C] {M : C}
    {u : TopPair.singularCohomology
      (thomPair F ((projection : C(VectorBundleOrientationCover F E ι, B)) *ᵖ E)) R k M
      (finrank ℝ F)}
    (hu : IsThomClass F _ u) (hs : ∀ x, (s x).proj = f x) :
    IsThomClass F ((⇑f) *ᵖ E) (TopPair.singularCohomologyMap (thomPairMapOfLift F E hs) _ u) :=
  hu.thomPairMapOfFiberwise (continuous_mk_fiberCast hs)

/-- Followed by the projection `(E', E'₀) ⟶ (E, E₀)` of the orientation cover, the map of Thom
pairs over a lift of `f` is the canonical map `(f^*E, (f^*E)₀) ⟶ (E, E₀)` of the pull-back. -/
theorem thomPairMapOfLift_comp_coverThomPairMap (hs : ∀ x, (s x).proj = f x) :
    thomPairMapOfLift F E hs ≫ coverThomPairMap F E ι = pullbackThomPairMap F E f := by
  rw [coverThomPairMap_eq_pullbackThomPairMap]
  -- the composite is evaluated by `exact`: its source reads the zeros of the fibres of `E'`
  -- through `TauCeti.pullbackFiberZero` and the target of `thomPairMapOfLift` through the module
  -- structure, so the composition lemmas do not rewrite it
  exact TopPair.hom_ext_of_fst _ (TopCat.ext fun v ↦
    (pullbackThomPairMap_fst_apply F E projection _).trans
      ((lift_thomPairMapOfLift_fst hs v).trans (pullbackThomPairMap_fst_apply F E f v).symm))

/-- **The map of Thom pairs over an equivariant lift is equivariant.** Let `G` act on `X` and on the
total space of `f^*E`, compatibly with the projection and so that the canonical map to the total
space of `E` is invariant. If the lift `s` satisfies `s(g • x) = ρ(g) • s(x)` for a homomorphism
`ρ : G →* ℤˣ`, then so does the map of Thom pairs over `s`, for the action of `ℤˣ` on the Thom
pair of the orientation cover. -/
theorem thomPairMapOfLift_fst_smul {G : Type*} [Monoid G] [MulAction G (TopCat.of X)]
    [MulAction G (thomPair F ((⇑f) *ᵖ E)).fst] (hs : ∀ x, (s x).proj = f x) (ρ : G →* ℤˣ)
    (hρ : ∀ (g : G) (x : TopCat.of X), s (g • x) = ρ g • s x)
    (hp₀ : ∀ (g : G) x,
      thomPairProj F ((⇑f) *ᵖ E) (g • x) = g • thomPairProj F ((⇑f) *ᵖ E) x)
    (hlift : ∀ (g : G) (v : (thomPair F ((⇑f) *ᵖ E)).fst),
      Pullback.lift f (g • v : TotalSpace F ((⇑f) *ᵖ E)) = Pullback.lift f v)
    (g : G) (v : (thomPair F ((⇑f) *ᵖ E)).fst) :
    TopPair.Hom.fst (thomPairMapOfLift F E hs) (g • v) =
      ρ g • TopPair.Hom.fst (thomPairMapOfLift F E hs) v := by
  -- A point of the total space of `E'` is determined by its projection to the orientation cover
  -- and its image in the total space of `E`, both of which `ℤˣ` acts on by definition
  -- (`proj_smul_totalSpace`, `lift_smul`); the points of the Thom pair are those of the total
  -- spaces only after unfolding `thomPair`, so the chains are closed by `exact`.
  refine Pullback.totalSpace_ext ?_ ?_
  · have hv : (g • v : TotalSpace F ((⇑f) *ᵖ E)).proj = g • (v : TotalSpace F ((⇑f) *ᵖ E)).proj :=
      (thomPairProj_apply F _ (g • v)).symm.trans
        ((hp₀ g v).trans (congrArg (g • ·) (thomPairProj_apply F _ v)))
    exact (thomPairMapOfLift_fst_proj hs (g • v)).trans <| (congrArg s hv).trans <|
      (hρ g _).trans <| congrArg (ρ g • ·) (thomPairMapOfLift_fst_proj hs v).symm
  · exact (lift_thomPairMapOfLift_fst hs (g • v)).trans <| (hlift g v).trans
      (lift_thomPairMapOfLift_fst hs v).symm

end Map

/-! ### A semi-invariant Thom cocycle and the Thom isomorphism -/

section ThomIsomorphism

variable [Fintype ι] [FiniteDimensional ℝ F] (hι : Fintype.card ι = finrank ℝ F)
  (k : Type u) [CommRing k]

include hι in
/-- **A semi-invariant Thom cocycle from an equivariant lift to the orientation cover.** Let `G`
act on `X` and on the total space of `f^*E`, compatibly with the projection and so that the
canonical map to the total space of `E` is invariant, and let the lift `s` of `f` to the
orientation cover satisfy `s(g • x) = ρ(g) • s(x)` for a homomorphism `ρ : G →* ℤˣ`. Then, for
every commutative ring `k`, the Thom pair of `f^*E` has a relative cocycle of degree `r` whose class
is a Thom class of `f^*E` and which is semi-invariant for the character `ρ` with values in `kˣ`:
the pull-back along the map of Thom pairs over `s` of a Thom cocycle of the orientation cover
which the deck involution negates. -/
theorem exists_isSemiInvariantCocycle_isThomClass_of_lift {G : Type u} [Monoid G]
    [MulAction G (TopCat.of X)] [MulAction G (thomPair F ((⇑f) *ᵖ E)).fst]
    [ContinuousConstSMul G (thomPair F ((⇑f) *ᵖ E)).fst] (hs : ∀ x, (s x).proj = f x)
    (ρ : G →* ℤˣ) (hρ : ∀ (g : G) (x : TopCat.of X), s (g • x) = ρ g • s x)
    (hp₀ : ∀ (g : G) x,
      thomPairProj F ((⇑f) *ᵖ E) (g • x) = g • thomPairProj F ((⇑f) *ᵖ E) x)
    (hlift : ∀ (g : G) (v : (thomPair F ((⇑f) *ᵖ E)).fst),
      Pullback.lift f (g • v : TotalSpace F ((⇑f) *ᵖ E)) = Pullback.lift f v) :
    ∃ φ : ((thomPair F ((⇑f) *ᵖ E)).singularCochainComplex (ModuleCat.of k k) k
        (ModuleCat.of k k)).cycles (finrank ℝ F),
      TopPair.IsSemiInvariantCocycle ((Units.map (Int.castRingHom k).toMonoidHom).comp ρ) φ ∧
      IsThomClass F ((⇑f) *ᵖ E)
        ((TopPair.singularCochainComplex _ (ModuleCat.of k k) k (ModuleCat.of k k)).homologyπ
          (finrank ℝ F) φ) := by
  obtain ⟨φ, hφ, hu⟩ := exists_isSemiInvariantCocycle_isThomClass (F := F) (E := E) hι k
  -- `ℤˣ` acts on the Thom pair of the orientation cover through its copy `ULift ℤˣ`, whose sign
  -- character read along `ρ` is `ρ` with values in `kˣ`
  have hχ : (uliftIntUnitsSign k).comp (MulEquiv.ulift.symm.toMonoidHom.comp ρ) =
      (Units.map (Int.castRingHom k).toMonoidHom).comp ρ :=
    MonoidHom.ext fun g ↦ Units.ext (uliftIntUnitsSign_apply k _)
  refine ⟨HomologicalComplex.cyclesMap
    (TopPair.singularCochainComplexMap (thomPairMapOfLift F E hs)) (finrank ℝ F) φ,
    hχ ▸ hφ.cyclesMap_singularCochainComplexMap _ (MulEquiv.ulift.symm.toMonoidHom.comp ρ)
      (thomPairMapOfLift_fst_smul hs ρ hρ hp₀ hlift), ?_⟩
  -- the map of Thom pairs over `s` is a fibrewise isomorphism, so it pulls Thom classes back to
  -- Thom classes, and the class of the pulled-back cocycle is the pulled-back class
  have h := ConcreteCategory.congr_hom (HomologicalComplex.homologyπ_naturality
    (TopPair.singularCochainComplexMap (thomPairMapOfLift F E hs)) (finrank ℝ F)) φ
  rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at h
  have hu' : IsThomClass F ((⇑f) *ᵖ E) (TopPair.singularCohomologyMap (thomPairMapOfLift F E hs)
      (finrank ℝ F) ((TopPair.singularCochainComplex _ (ModuleCat.of k k) k
        (ModuleCat.of k k)).homologyπ (finrank ℝ F) φ)) :=
    hu.thomPairMapOfLift hs
  exact (congrArg (IsThomClass F _) h).mp hu'

include hι in
/-- **The Thom isomorphism of a cover lifting to the orientation cover.** Let `G` act on `X` and on
the Thom pair of `f^*E`, compatibly with its inclusion and projection and keeping the underlying
vectors of `E`, and let the lift `s` of `f` to the orientation cover satisfy
`s(g • x) = ρ(g) • s(x)` for a homomorphism `ρ : G →* ℤˣ`. Let the Thom pair of `f^*E` map to a pair
`(Q, Q₀)` by quotient covering maps for `G` and `X` map to a space `Z` by a quotient covering map.
Then for every commutative ring `k`, every representation `D` of `G` and every `q`,
`H_{q + r}(Q, Q₀; L_D) ≅ H_q(Z; L_{D ⊗ k_χ})`, where `χ : G →* kˣ` is `ρ` with values in `kˣ` and
`L_D`, `L_{D ⊗ k_χ}` are the associated local systems. The intended case is `(Q, Q₀) = (E, E₀)`
and `Z = B`, with the canonical maps `f^*E → E` and `f : X → B` as the quotient maps; this theorem
does not construct that case, which requires the caller to supply a `G`-action on the Thom pair of
`f^*E` under which these canonical maps are quotient covering maps for `G`. -/
theorem nonempty_twistedHomology_iso_twistedHomology_of_lift {G : Type u} [Group G]
    [MulAction G (TopCat.of X)] [ContinuousConstSMul G (TopCat.of X)]
    [MulAction G (thomPair F ((⇑f) *ᵖ E)).fst]
    [ContinuousConstSMul G (thomPair F ((⇑f) *ᵖ E)).fst]
    [MulAction G (thomPair F ((⇑f) *ᵖ E)).snd]
    [ContinuousConstSMul G (thomPair F ((⇑f) *ᵖ E)).snd] {P : TopPair.{u}}
    {ψ : thomPair F ((⇑f) *ᵖ E) ⟶ P} (hfst : IsQuotientCoveringMap (TopPair.Hom.fst ψ) G)
    (hsnd : IsQuotientCoveringMap (TopPair.Hom.snd ψ) G) {Z : TopCat.{u}} {p : TopCat.of X ⟶ Z}
    (hp : IsQuotientCoveringMap p G)
    (hP : ∀ (g : G) x,
      (thomPair F ((⇑f) *ᵖ E)).map (g • x) = g • (thomPair F ((⇑f) *ᵖ E)).map x)
    (hp₀ : ∀ (g : G) x,
      thomPairProj F ((⇑f) *ᵖ E) (g • x) = g • thomPairProj F ((⇑f) *ᵖ E) x)
    (hlift : ∀ (g : G) (v : (thomPair F ((⇑f) *ᵖ E)).fst),
      Pullback.lift f (g • v : TotalSpace F ((⇑f) *ᵖ E)) = Pullback.lift f v)
    (hs : ∀ x, (s x).proj = f x) (ρ : G →* ℤˣ)
    (hρ : ∀ (g : G) (x : TopCat.of X), s (g • x) = ρ g • s x) (D : Rep.{u} k G) (q : ℕ) :
    Nonempty (P.twistedHomology (hfst.associatedLocalSystem k D) (q + finrank ℝ F) ≅
      LocalCoefficientSystem.twistedHomology (hp.associatedLocalSystem k
        (D ⊗ Rep.of (Representation.ofLinearCharacter
          ((Units.map (Int.castRingHom k).toMonoidHom).comp ρ)))) q) := by
  obtain ⟨φ, hφ, hu⟩ :=
    exists_isSemiInvariantCocycle_isThomClass_of_lift hι k hs ρ hρ hp₀ hlift
  exact ⟨quotientTwistedHomologyThomIso hfst hsnd hp hP hp₀ _ hφ hu D q⟩

end ThomIsomorphism

end TauCeti.VectorBundleOrientationCover
