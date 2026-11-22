/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.LocalHomology.Orientation.Linear
public import TauCeti.AlgebraicTopology.Singular.Twisted.Zero
public import TauCeti.Topology.VectorBundle.MayerVietoris.RankDegree
public import TauCeti.Topology.VectorBundle.Orientation.LocalSystem
import TauCeti.AlgebraicTopology.Singular.Twisted.CompactSupport.Basic
import TauCeti.Topology.Homotopy.Covering
import TauCeti.Topology.VectorBundle.Thom.Class

/-!
# The homology of the Thom pair in the rank degree, with orientation coefficients

Let `E → B` be a real vector bundle of rank `r = n + 1` over an arbitrary base, with Thom pair
`(E, E₀)`, `E₀` the complement of the zero section, and let `o(E)` be its integral orientation
local system (`TauCeti.VectorBundleOrientationCover.signLocalSystem`), whose fibre over `b` is the
group of functions `σ` on the two orientations of `E_b` with `σ(-o) = -σ(o)`. This file computes the
first group of the Thom pair that does not vanish, with integral coefficients and without an
orientation of the bundle:

`Hᵣ(E, E₀; ℤ) ≅ H₀(B; o(E))`

(`TauCeti.thomPairSingularHomologyIsoTwistedHomology`). An orientation `o` of a fibre `E_b`
selects a local orientation of the fibre pair `(E_b, E_b ∖ {0})`, a generator of its homology in
degree `r` (`TauCeti.fiberLocalOrientation`), and the isomorphism sends the image of this generator
in `Hᵣ(E, E₀; ℤ)` to the class of the element of the fibre of `o(E)` over `b` with value `1` at
`o` (`TauCeti.thomPairSingularHomologyIsoTwistedHomology_hom_apply`). Reversing `o` changes the
sign of both. This is the bottom degree of the Thom isomorphism `Hₖ₊ᵣ(E, E₀; L) ≅ Hₖ(B; o(E) ⊗ L)`
with local coefficients. For an orientable bundle `o(E)` is trivial and `H₀(B; o(E)) ≅ H₀(B; ℤ)`;
for the Möbius line over the circle, `H₀(S¹; o(E)) ≅ ℤ/2`.

This is the identification that crossing the level of a Morse–Bott critical submanifold `C` of
index `λ` produces in the lowest degree: the relative homology of the attachment of the negative
disc bundle `ν⁻` along its sphere bundle is that of the Thom pair of `ν⁻`, so
`H_λ(M_{c+ε}, M_{c-ε}; ℤ) ≅ H₀(C; o(ν⁻))`.

## The proof

The map `H₀(B; o(E)) ⟶ Hᵣ(E, E₀; ℤ)` is defined on the classes of the elements `σ` of the fibres
by `σ ↦ σ(o) [E_b, o]`, which does not depend on the orientation `o` of `E_b`. Twisted zeroth
homology is the colimit of the local system over the fundamental groupoid
(`TauCeti.LocalCoefficientSystem.isColimitTwistedHomology₀Cocone`), so the map exists once the
fibre classes are compatible with transport along paths. Transport along a path precomposes with
path lifting in the orientation double cover, and the fibre classes are constant along paths in
the cover: over the base set of a trivialization they are read in the product `W × F`, where the
fibre inclusions over points joined by a path agree (in `Bundle.Trivialization`,
`singularHomologyMap_complZeroPairIso_inv_comp_fiberThomPairOverMap_eq_of_joinedIn`).

The same construction over every subset `W` of the base gives maps
`H₀(W; o(E)) ⟶ Hᵣ(E|_W, E₀|_W; ℤ)` commuting with the restrictions. Over a subset of the base set
of a trivialization of the atlas, the orientation of the fibres read as a fixed orientation of the
model fibre trivializes `o(E)`
(`TauCeti.VectorBundleOrientationCover.mem_sheet_of_forall_proj_mem_baseSet`,
`TauCeti.VectorBundleOrientationCover.signLocalSystem_map_mk_signLocalSystemFiberEquiv_symm`), and
the map becomes the computation `Hᵣ(W × F, W × (F ∖ {0})) ≅ H₀(W)` of the product bundle, with
the model orientation chosen to select the class of the point
(`TauCeti.complZeroPairPointHom`). The Mayer–Vietoris argument over finite unions of trivializing
open sets and the passage to the whole base by compact supports
(`TauCeti.isIso_of_isColimit_biUnion_baseSet`) then give the isomorphism over `B`.

## Main definitions and results

* `TauCeti.fiberLocalOrientation`: the local orientation of the fibre pair `(E_b, E_b ∖ {0})`
  selected by an orientation of `E_b`; it does not depend on the trivialization reading it
  (`TauCeti.fiberLocalOrientation_eq_map`).
* `TauCeti.thomPairSingularHomologyIsoTwistedHomology`: `Hᵣ(E, E₀; ℤ) ≅ H₀(B; o(E))`.
* `TauCeti.thomPairSingularHomologyIsoTwistedHomology_hom_apply`: it sends the local orientation of
  the fibre over `b` selected by `o` to the element with value `1` at `o`.

## References

* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton (1974), §10, Lemma 10.3 and the proof of Theorem 10.4, and §12 (twisted coefficients).
* A. Hatcher, *Algebraic Topology*, Section 3.H (local coefficients) and Section 4.D,
  Theorem 4D.10 and its proof.
* R. L. Cohen, K. Iga and P. Norbury, *Topics in Morse theory: lecture notes*, 2006,
  Theorem 15.4.
-/

public section

noncomputable section

open Bundle CategoryTheory Limits Set Module AlgebraicTopology Topology

universe w

namespace TauCeti

section LocalOrientation

variable {B : Type w} [TopologicalSpace B] {F : Type w} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {E : B → Type w} [TopologicalSpace (TotalSpace F E)]
  [∀ b, AddCommMonoid (E b)] [∀ b, Module ℝ (E b)] [∀ b, TopologicalSpace (E b)]
  [FiberBundle F E] [VectorBundle ℝ F E] {n : ℕ} (hF : finrank ℝ F = n + 1)

/-- The local orientation of the fibre pair `(E_b, E_b ∖ {0})` selected by an orientation of `E_b`,
read through the trivialization at `b`. -/
def fiberLocalOrientation (b : B) (o : Orientation ℝ (E b) (Fin (n + 1))) :
    LocalOrientation (E b) 0 (n + 1) :=
  ((trivializationAt F E b).mapOrientation (Fin (n + 1)) (mem_baseSet_trivializationAt F E b) o
    |>.localOrientation hF).map
    ((trivializationAt F E b).continuousLinearEquivAt ℝ b
      (mem_baseSet_trivializationAt F E b)).complZeroPairIso.symm

/-- Any linear trivialization at `b` reads the same local orientation. -/
theorem fiberLocalOrientation_eq_map (e : Trivialization F (π F E)) [e.IsLinear ℝ] {b : B}
    (hb : b ∈ e.baseSet) (o : Orientation ℝ (E b) (Fin (n + 1))) :
    fiberLocalOrientation hF b o =
      ((e.mapOrientation (Fin (n + 1)) hb o).localOrientation hF).map
        (e.continuousLinearEquivAt ℝ b hb).complZeroPairIso.symm := by
  set e₀ := trivializationAt F E b
  have hb₀ : b ∈ e₀.baseSet := mem_baseSet_trivializationAt F E b
  set c := e₀.coordChangeL ℝ e b
  rw [fiberLocalOrientation, e₀.mapOrientation_eq_map_coordChangeL e hb₀ hb,
    Orientation.localOrientation_map c _ hF hF,
    ← e₀.continuousLinearEquivAt_trans_coordChangeL ℝ e hb₀ hb,
    ContinuousLinearEquiv.complZeroPairIso_trans, ← LocalOrientation.map_trans]
  congr 1
  rw [Iso.trans_symm, ← Iso.trans_assoc, Iso.self_symm_id, Iso.refl_trans]

@[simp]
theorem fiberLocalOrientation_neg (b : B) (o : Orientation ℝ (E b) (Fin (n + 1))) :
    fiberLocalOrientation hF b (-o) = -fiberLocalOrientation hF b o := by
  simp [fiberLocalOrientation]

end LocalOrientation

section Fiber

variable {B : Type w} [TopologicalSpace B] {F : Type w} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {E : B → Type w} [TopologicalSpace (TotalSpace F E)]
  [∀ b, AddCommMonoid (E b)] [∀ b, Module ℝ (E b)] [∀ b, TopologicalSpace (E b)]
  [FiberBundle F E] [VectorBundle ℝ F E] {n : ℕ} (hF : finrank ℝ F = n + 1)

variable (F E) in
/-- The class in `Hₙ₊₁(E|_W, E₀|_W; ℤ)` of the local orientation of the fibre over `b ∈ W`
selected by an orientation `o` of `E_b`. -/
private def fiberClassOver (W : Set B) {b : B} (hb : b ∈ W)
    (o : Orientation ℝ (E b) (Fin (n + 1))) :
    ((thomPairOver F E W).singularHomology (ModuleCat.of ℤ (ULift.{w} ℤ)) (n + 1) :
      ModuleCat.{w} ℤ) :=
  TopPair.singularHomologyMap (fiberThomPairOverMap F E hb) (ModuleCat.of ℤ (ULift.{w} ℤ)) (n + 1)
    (fiberLocalOrientation hF b o).val

private theorem fiberClassOver_neg (W : Set B) {b : B} (hb : b ∈ W)
    (o : Orientation ℝ (E b) (Fin (n + 1))) :
    fiberClassOver F E hF W hb (-o) = -fiberClassOver F E hF W hb o := by
  simp [fiberClassOver, LocalOrientation.coe_neg]

private theorem singularHomologyMap_thomPairOverMap_fiberClassOver {W W' : Set B} (h : W ⊆ W')
    {b : B} (hb : b ∈ W) (o : Orientation ℝ (E b) (Fin (n + 1))) :
    TopPair.singularHomologyMap (thomPairOverMap F E h) (ModuleCat.of ℤ (ULift.{w} ℤ)) (n + 1)
        (fiberClassOver F E hF W hb o) = fiberClassOver F E hF W' (h hb) o := by
  rw [fiberClassOver, fiberClassOver, ← ConcreteCategory.comp_apply,
    ← TopPair.singularHomologyMap_comp, fiberThomPairOverMap_comp_thomPairOverMap]

/-- A linear trivialization over `W` carries the fibre class over `b` to the image, under the
inclusion of the fibre over `b` of the product, of the local orientation of `F` selected by the
orientation read in the trivialization. -/
private theorem singularHomologyMap_thomPairOverIso_fiberClassOver (e : Trivialization F (π F E))
    [e.IsLinear ℝ] {W : Set B} (hW : W ⊆ e.baseSet) {b : B} (hb : b ∈ W)
    (o : Orientation ℝ (E b) (Fin (n + 1))) :
    TopPair.singularHomologyMap (e.thomPairOverIso ℝ hW).hom (ModuleCat.of ℤ (ULift.{w} ℤ))
        (n + 1) (fiberClassOver F E hF W hb o) =
      TopPair.singularHomologyMap (prodThomPairFiberMap F (⟨b, hb⟩ : W))
        (ModuleCat.of ℤ (ULift.{w} ℤ)) (n + 1)
        ((e.mapOrientation (Fin (n + 1)) (hW hb) o).localOrientation hF).val := by
  rw [fiberClassOver, ← ConcreteCategory.comp_apply, ← TopPair.singularHomologyMap_comp,
    Bundle.Trivialization.fiberThomPairOverMap_comp_thomPairOverIso_hom ℝ e hW hb,
    TopPair.singularHomologyMap_comp, ConcreteCategory.comp_apply,
    fiberLocalOrientation_eq_map hF e (hW hb), ← LocalOrientation.coe_map,
    ← LocalOrientation.map_trans, Iso.symm_self_id, LocalOrientation.map_refl]

variable [FiniteDimensional ℝ F]

/-- **Fibre classes are constant on the sheets of a trivialization**: the fibre classes over two
points of `W` joined by a path in `W` within the base set of a linear trivialization, for
orientations which the trivialization reads as the same orientation of `F`, agree. -/
private theorem fiberClassOver_eq_of_mapOrientation_eq (e : Trivialization F (π F E)) [e.IsLinear ℝ]
    {W : Set B} {b b' : B} (h : JoinedIn (W ∩ e.baseSet) b b')
    {o : Orientation ℝ (E b) (Fin (n + 1))}
    {o' : Orientation ℝ (E b') (Fin (n + 1))}
    (ho : e.mapOrientation (Fin (n + 1)) (h.source_mem.2) o =
      e.mapOrientation (Fin (n + 1)) (h.target_mem.2) o') :
    fiberClassOver F E hF W h.source_mem.1 o = fiberClassOver F E hF W h.target_mem.1 o' := by
  have key := ConcreteCategory.congr_hom
    (e.singularHomologyMap_complZeroPairIso_inv_comp_fiberThomPairOverMap_eq_of_joinedIn
      (ModuleCat.of ℤ (ULift.{w} ℤ)) h (n + 1) hF)
    ((e.mapOrientation (Fin (n + 1)) h.target_mem.2 o').localOrientation hF).val
  simp only [TopPair.singularHomologyMap_comp, ConcreteCategory.comp_apply] at key
  rw [fiberClassOver, fiberClassOver, fiberLocalOrientation_eq_map hF e h.source_mem.2,
    fiberLocalOrientation_eq_map hF e h.target_mem.2, ho, LocalOrientation.coe_map,
    LocalOrientation.coe_map, Iso.symm_hom, Iso.symm_hom]
  exact key

/-- **Fibre classes are constant along paths in the orientation double cover**: along a path of
fibre orientations whose base points stay in `W`, the fibre classes over `W` do not change. -/
private theorem fiberClassOver_eq_of_continuous (W : Set B)
    (Γ : C(unitInterval, VectorBundleOrientationCover F E (Fin (n + 1))))
    (hΓ : ∀ t, (Γ t).proj ∈ W) {c₀ c₁ : VectorBundleOrientationCover F E (Fin (n + 1))}
    (h₀ : Γ 0 = c₀) (h₁ : Γ 1 = c₁) (hc₀ : c₀.proj ∈ W) (hc₁ : c₁.proj ∈ W) :
    fiberClassOver F E hF W hc₀ c₀.orientation = fiberClassOver F E hF W hc₁ c₁.orientation := by
  subst h₀ h₁
  have : LocallyPathConnectedSpace unitInterval :=
    Convex.locallyPathConnectedSpace ℝ (convex_Icc (0 : ℝ) 1)
  have hcont : Continuous fun t ↦ (Γ t).proj :=
    VectorBundleOrientationCover.continuous_proj.comp Γ.continuous
  have hlc : IsLocallyConstant fun t ↦ fiberClassOver F E hF W (hΓ t) (Γ t).orientation := by
    refine (IsLocallyConstant.iff_eventually_eq _).2 fun t ↦ ?_
    -- Near `t`, the path stays in the sheet of the trivialization at `Γ t` through `Γ t`.
    let e := trivializationAt F E (Γ t).proj
    have he : (Γ t).proj ∈ e.baseSet := mem_baseSet_trivializationAt F E _
    let ω := e.mapOrientation (Fin (n + 1)) he (Γ t).orientation
    have hO : Γ ⁻¹' VectorBundleOrientationCover.sheet e ω ∈ 𝓝 t :=
      ((VectorBundleOrientationCover.isOpen_sheet_trivializationAt _ ω).preimage
        Γ.continuous).mem_nhds (VectorBundleOrientationCover.mem_sheet_iff.2 ⟨he, rfl⟩)
    filter_upwards [pathComponentIn_mem_nhds hO] with s hs
    have hsO : s ∈ Γ ⁻¹' VectorBundleOrientationCover.sheet e ω := pathComponentIn_subset hs
    obtain ⟨hse, hsω⟩ := VectorBundleOrientationCover.mem_sheet_iff.1 hsO
    have hJ : JoinedIn (W ∩ e.baseSet) (Γ t).proj (Γ s).proj :=
      (hs.map hcont.continuousOn).mono (by
        rintro _ ⟨u, hu, rfl⟩
        exact ⟨hΓ u, (VectorBundleOrientationCover.mem_sheet_iff.1 hu).1⟩)
    exact (fiberClassOver_eq_of_mapOrientation_eq hF e hJ hsω.symm).symm
  exact hlc.apply_eq_of_preconnectedSpace 0 1

omit [FiniteDimensional ℝ F] in
include hF in
private theorem card_fin_eq_finrank : Fintype.card (Fin (n + 1)) = finrank ℝ F :=
  (Fintype.card_fin _).trans hF.symm

/-- An orientation of the model fibre selecting the point class
`TauCeti.complZeroPairPointHom` of `1` (`TauCeti.localOrientation_modelOrientation`). -/
private def modelOrientation : Orientation ℝ F (Fin (n + 1)) :=
  (Orientation.localOrientationEquiv hF).symm
    ⟨_, isLocalOrientation_complZeroPairPointHom_one F (n + 1) hF⟩

private theorem localOrientation_modelOrientation :
    ((modelOrientation hF).localOrientation hF).val =
      complZeroPairPointHom (ModuleCat.of ℤ (ULift.{w} ℤ)) F (n + 1) hF (ULift.up 1) :=
  congrArg Subtype.val (Orientation.localOrientation_localOrientationEquiv_symm hF _)

variable (E) in
/-- A chosen orientation of the fibre over `b`: the one read as `TauCeti.modelOrientation` in the
trivialization at `b`. -/
private def chosenOrientation (b : B) : Orientation ℝ (E b) (Fin (n + 1)) :=
  ((trivializationAt F E b).mapOrientation (Fin (n + 1))
    (mem_baseSet_trivializationAt F E b)).symm (modelOrientation hF)

/-- Every orientation of a fibre is the chosen one or its opposite. -/
private theorem eq_or_eq_neg_chosenOrientation {b : B} (o : Orientation ℝ (E b) (Fin (n + 1))) :
    o = chosenOrientation E hF b ∨ o = -chosenOrientation E hF b := by
  set f := (trivializationAt F E b).mapOrientation (Fin (n + 1))
    (mem_baseSet_trivializationAt F E b)
  rcases Orientation.eq_or_eq_neg (f o) (modelOrientation hF)
    (Nat.card_eq_fintype_card.trans (card_fin_eq_finrank hF)) with h | h
  · exact Or.inl ((Equiv.eq_symm_apply f).2 h)
  · refine Or.inr (f.injective ?_)
    simp only [h, f, chosenOrientation, Bundle.Trivialization.mapOrientation_neg,
      Equiv.apply_symm_apply]

open VectorBundleOrientationCover in
variable (F E) in
/-- The map from the fibre over `b ∈ W` of the orientation local system to
`Hₙ₊₁(E|_W, E₀|_W; ℤ)` sending an element `σ` to `σ(o)` times the fibre class of `o`, for any
orientation `o` of `E_b` (`TauCeti.fiberHom_apply`). -/
private def fiberHom (W : Set B) {b : B} (hb : b ∈ W) :
    (signLocalSystem F E ℤ (card_fin_eq_finrank hF)).obj (FundamentalGroupoid.mk b) ⟶
      ((thomPairOver F E W).singularHomology (ModuleCat.of ℤ (ULift.{w} ℤ)) (n + 1) :
        ModuleCat.{w} ℤ) :=
  ModuleCat.ofHom ((LinearMap.toSpanSingleton ℤ _
      (fiberClassOver F E hF W hb (chosenOrientation E hF b))) ∘ₗ
    (signLocalSystemFiberEquiv (card_fin_eq_finrank hF) (chosenOrientation E hF b)).toLinearMap)

open VectorBundleOrientationCover in
private theorem fiberHom_apply (W : Set B) {b : B} (hb : b ∈ W)
    (o : Orientation ℝ (E b) (Fin (n + 1)))
    (σ : (signLocalSystem F E ℤ (card_fin_eq_finrank hF)).obj (FundamentalGroupoid.mk b)) :
    fiberHom F E hF W hb σ =
      signLocalSystemFiberEquiv (card_fin_eq_finrank hF) o σ • fiberClassOver F E hF W hb o := by
  rcases eq_or_eq_neg_chosenOrientation hF o with h | h
  -- The codomain of `fiberHom` is the homology only by unfolding, so `rw` cannot see through
  -- `ModuleCat.ofHom`; the apply lemmas are chained as terms. `Int.cast_smul_eq_zsmul` turns the
  -- module action used by `toSpanSingleton` into `zsmul`.
  · subst h
    exact (ModuleCat.ofHom_apply _ σ).trans ((LinearMap.comp_apply _ _ σ).trans
      ((LinearMap.toSpanSingleton_apply ℤ _ _ _).trans (Int.cast_smul_eq_zsmul ℤ _ _)))
  · subst h
    rw [fiberClassOver_neg, VectorBundleOrientationCover.signLocalSystemFiberEquiv_neg, zsmul_neg,
      neg_zsmul, neg_neg]
    exact (ModuleCat.ofHom_apply _ σ).trans ((LinearMap.comp_apply _ _ σ).trans
      ((LinearMap.toSpanSingleton_apply ℤ _ _ _).trans (Int.cast_smul_eq_zsmul ℤ _ _)))

open VectorBundleOrientationCover in
/-- The value of `TauCeti.fiberHom` read at any point `c` of the orientation double cover over
`b`. -/
private theorem fiberHom_apply_mem (W : Set B) {b : B} (hb : b ∈ W)
    (c : (proj ⁻¹' {b} : Set (VectorBundleOrientationCover F E (Fin (n + 1)))))
    (σ : (signLocalSystem F E ℤ (card_fin_eq_finrank hF)).obj (FundamentalGroupoid.mk b)) :
    fiberHom F E hF W hb σ =
      (signLocalSystemObjEquiv (card_fin_eq_finrank hF) (FundamentalGroupoid.mk b) σ :
        (proj ⁻¹' {b} : Set (VectorBundleOrientationCover F E (Fin (n + 1)))) → ℤ) c •
        fiberClassOver F E hF W (by rw [show c.val.proj = b from c.property]; exact hb)
          c.val.orientation := by
  obtain ⟨⟨b', o⟩, hb'⟩ := c
  obtain rfl : b' = b := hb'
  rw [fiberHom_apply hF W hb o, signLocalSystemFiberEquiv_apply]

open VectorBundleOrientationCover in
/-- **The fibre maps are natural along paths**: transport in the orientation local system along a
path in `W` followed by the fibre map at its end is the fibre map at its start. -/
private theorem map_mk_comp_fiberHom (W : Set B) {x y : B} (γ : Path x y) (hγ : ∀ t, γ t ∈ W)
    (hx : x ∈ W) (hy : y ∈ W) :
    (signLocalSystem F E ℤ (card_fin_eq_finrank hF)).map (Path.Homotopic.Quotient.mk γ) ≫
        fiberHom F E hF W hy = fiberHom F E hF W hx := by
  set hι := card_fin_eq_finrank hF
  set cov := isCoveringMap_proj (F := F) (E := E) hι
  -- The reversed path, lifted through the chosen orientation at its start `y`.
  let c₀ : (proj ⁻¹' {y} : Set (VectorBundleOrientationCover F E (Fin (n + 1)))) :=
    ⟨⟨y, chosenOrientation E hF y⟩, rfl⟩
  have hc₀ : γ.symm 0 = proj c₀.val := by simp [c₀]
  let Γ := cov.liftPath γ.symm c₀.val hc₀
  have hΓ (t : unitInterval) : (Γ t).proj ∈ W := by
    rw [show (Γ t).proj = γ.symm t from congrFun (cov.liftPath_lifts γ.symm c₀.val hc₀) t]
    exact hγ _
  let q : FundamentalGroupoid.mk (X := TopCat.of B) x ⟶ FundamentalGroupoid.mk y :=
    Path.Homotopic.Quotient.mk γ
  ext σ
  rw [ModuleCat.hom_comp, LinearMap.comp_apply, fiberHom_apply_mem hF W hy c₀,
    fiberHom_apply_mem hF W hx (cov.monodromy (inv q) c₀),
    signLocalSystemObjEquiv_map_apply]
  congr 1
  exact fiberClassOver_eq_of_continuous hF W Γ hΓ (cov.liftPath_zero _ _ _)
    (cov.coe_monodromy_inv_mk γ c₀).symm _ _

/-- The fibre maps commute with the restrictions of Thom pairs. -/
@[reassoc]
private theorem fiberHom_comp_singularHomologyMap_thomPairOverMap {W W' : Set B} (h : W ⊆ W')
    {b : B} (hb : b ∈ W) :
    fiberHom F E hF W hb ≫
        TopPair.singularHomologyMap (thomPairOverMap F E h) (ModuleCat.of ℤ (ULift.{w} ℤ)) (n + 1) =
      fiberHom F E hF W' (h hb) := by
  ext σ
  rw [ModuleCat.hom_comp, LinearMap.comp_apply, fiberHom_apply hF W hb (chosenOrientation E hF b),
    fiberHom_apply hF W' (h hb) (chosenOrientation E hF b), map_zsmul,
    singularHomologyMap_thomPairOverMap_fiberClassOver]

end Fiber

section Twisted

open VectorBundleOrientationCover LocalCoefficientSystem

variable {B : Type w} [TopologicalSpace B] {F : Type w} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F] {E : B → Type w} [TopologicalSpace (TotalSpace F E)]
  [∀ b, AddCommMonoid (E b)] [∀ b, Module ℝ (E b)] [∀ b, TopologicalSpace (E b)]
  [FiberBundle F E] [VectorBundle ℝ F E] {n : ℕ} (hF : finrank ℝ F = n + 1)

variable (F E) in
/-- The restriction to `W` of the integral orientation local system of `E`. -/
private abbrev orientationSystemOver (W : Set B) :
    LocalCoefficientSystem.{0, w, w} ℤ (TopCat.of W) :=
  (LocalCoefficientSystem.pullback (X := TopCat.of W) (ContinuousMap.subtypeVal W)).obj
    (signLocalSystem F E ℤ (card_fin_eq_finrank hF))

variable (F E) in
/-- The zeroth homology of the restrictions of the orientation local system to the subsets of the
base, as a functor of the subset. -/
private abbrev orientationHomologyFunctor : Set B ⥤ ModuleCat.{w} ℤ :=
  subsetTwistedHomologyFunctor.{0, w, w, w} (signLocalSystem F E ℤ (card_fin_eq_finrank hF))
    (U := (id : Set B → Set B)) monotone_id 0

omit [FiniteDimensional ℝ F] in
/-- The restriction maps of `TauCeti.orientationHomologyFunctor` send the class of a coefficient
over a point to the class of the same coefficient. -/
@[reassoc]
private theorem ιTwistedHomology₀_orientationHomologyFunctor_map {W W' : Set B} (h : W ⊆ W')
    (x : W) :
    ιTwistedHomology₀ (orientationSystemOver F E hF W) x ≫
        (orientationHomologyFunctor F E hF).map (homOfLE h) =
      ιTwistedHomology₀ (orientationSystemOver F E hF W') (inclusion h x) :=
  ιTwistedHomology₀_homologyMap_subsetTwistedChainComplexMap
    (signLocalSystem F E ℤ (card_fin_eq_finrank hF)) h x

variable (F E) in
/-- The fibre maps over `W`, as a cocone on the restriction to `W` of the orientation local
system. -/
private def fiberHomCocone (W : Set B) :
    Cocone (orientationSystemOver F E hF W) where
  pt := (thomPairOver F E W).singularHomology (ModuleCat.of ℤ (ULift.{w} ℤ)) (n + 1)
  ι :=
    { app x := fiberHom F E hF W x.as.property
      naturality x y p := by
        induction p using Path.Homotopic.Quotient.ind with
        | mk γ =>
          exact (map_mk_comp_fiberHom hF W (γ.map continuous_subtypeVal) (fun t ↦ (γ t).property)
            x.as.property y.as.property).trans (Category.comp_id _).symm }

variable (F E) in
/-- The map `H₀(W; o(E)) ⟶ Hₙ₊₁(E|_W, E₀|_W; ℤ)` sending the class of `σ` over `b` to the fibre
class `σ(o) [E_b, o]`, for any orientation `o` of `E_b`. -/
private def thomPairOverHomologyMap (W : Set B) :
    twistedHomology.{0, w, w} (orientationSystemOver F E hF W) 0 ⟶
      (thomPairOver F E W).singularHomology (ModuleCat.of ℤ (ULift.{w} ℤ)) (n + 1) :=
  (isColimitTwistedHomology₀Cocone.{0, w, w} (orientationSystemOver F E hF W)).desc
    (fiberHomCocone F E hF W)

@[reassoc]
private theorem ιTwistedHomology₀_thomPairOverHomologyMap (W : Set B) (x : W) :
    ιTwistedHomology₀ (orientationSystemOver F E hF W) x ≫ thomPairOverHomologyMap F E hF W =
      fiberHom F E hF W x.property :=
  (isColimitTwistedHomology₀Cocone (orientationSystemOver F E hF W)).fac
    (fiberHomCocone F E hF W) (FundamentalGroupoid.mk x)

private theorem thomPairOverHomologyMap_ιTwistedHomology₀_apply (W : Set B) (x : W)
    (σ : (orientationSystemOver F E hF W).obj (FundamentalGroupoid.mk x)) :
    thomPairOverHomologyMap F E hF W (ιTwistedHomology₀ (orientationSystemOver F E hF W) x σ) =
      fiberHom F E hF W x.property σ :=
  ConcreteCategory.congr_hom (ιTwistedHomology₀_thomPairOverHomologyMap hF W x) σ

/-- `TauCeti.fiberHom_apply` for an element of the fibre of the restricted local system. -/
private theorem fiberHom_apply_orientationSystemOver (W : Set B) (x : W)
    (o : Orientation ℝ (E x) (Fin (n + 1)))
    (σ : (orientationSystemOver F E hF W).obj (FundamentalGroupoid.mk x)) :
    fiberHom F E hF W x.property σ =
      signLocalSystemFiberEquiv (card_fin_eq_finrank hF) o σ •
        fiberClassOver F E hF W x.property o :=
  fiberHom_apply hF W x.property o σ

/-- The maps `TauCeti.thomPairOverHomologyMap` commute with the restrictions. -/
private theorem orientationHomologyFunctor_map_comp_thomPairOverHomologyMap {W W' : Set B}
    (h : W ⊆ W') :
    (orientationHomologyFunctor F E hF).map (homOfLE h) ≫ thomPairOverHomologyMap F E hF W' =
      thomPairOverHomologyMap F E hF W ≫
        TopPair.singularHomologyMap (thomPairOverMap F E h) (ModuleCat.of ℤ (ULift.{w} ℤ))
          (n + 1) := by
  refine twistedHomology₀_hom_ext (orientationSystemOver F E hF W) fun x ↦ ?_
  -- The fibres of the restricted local systems over `x` are that of `B` only by unfolding, so the
  -- steps are chained as terms, compared up to unfolding.
  have h1 := ιTwistedHomology₀_orientationHomologyFunctor_map (E := E) hF h x
  have h2 := ιTwistedHomology₀_thomPairOverHomologyMap (E := E) hF W' (inclusion h x)
  have h3 := ιTwistedHomology₀_thomPairOverHomologyMap (E := E) hF W x
  have h4 := fiberHom_comp_singularHomologyMap_thomPairOverMap (E := E) hF h x.property
  exact (Category.assoc _ _ _).symm.trans ((eq_whisker h1 _).trans (h2.trans
    (h4.symm.trans ((eq_whisker h3.symm _).trans (Category.assoc _ _ _)))))

section Trivial

variable (b₀ : B) {W : Set B} (hW : W ⊆ (trivializationAt F E b₀).baseSet)

/-- The orientation of the fibre over `x` read as `TauCeti.modelOrientation` in the trivialization
at `b₀`. -/
private abbrev trivOrientation (x : W) : Orientation ℝ (E x) (Fin (n + 1)) :=
  ((trivializationAt F E b₀).mapOrientation (Fin (n + 1)) (hW x.property)).symm
    (modelOrientation hF)

/-- The element of the fibre of the orientation local system over `x` with value `1` at
`TauCeti.trivOrientation`. -/
private def trivGen (x : W) : (orientationSystemOver F E hF W).obj (FundamentalGroupoid.mk x) :=
  (signLocalSystemFiberEquiv (card_fin_eq_finrank hF) (trivOrientation hF b₀ hW x)).symm 1

private theorem signLocalSystemFiberEquiv_trivGen (x : W) :
    signLocalSystemFiberEquiv (card_fin_eq_finrank hF) (trivOrientation hF b₀ hW x)
      (trivGen hF b₀ hW x) = 1 :=
  LinearEquiv.apply_symm_apply _ _

/-- Every element of the fibre over `x` is a multiple of `TauCeti.trivGen`. -/
private theorem eq_smul_trivGen (x : W)
    (σ : (orientationSystemOver F E hF W).obj (FundamentalGroupoid.mk x)) :
    σ = signLocalSystemFiberEquiv (card_fin_eq_finrank hF) (trivOrientation hF b₀ hW x) σ •
      trivGen hF b₀ hW x := by
  apply (signLocalSystemFiberEquiv (card_fin_eq_finrank hF) (trivOrientation hF b₀ hW x)).injective
  -- The fibre of the restricted system is that of `B` only by unfolding, so the equalities are
  -- chained as terms.
  exact ((map_zsmul (signLocalSystemFiberEquiv (card_fin_eq_finrank hF)
    (trivOrientation hF b₀ hW x)) _ _).trans
      ((congrArg _ (signLocalSystemFiberEquiv_trivGen hF b₀ hW x)).trans (mul_one _))).symm

/-- The element `TauCeti.trivGen`, as a map out of the coefficients. -/
private def trivGenHom (x : W) :
    ModuleCat.of ℤ (ULift.{w} ℤ) ⟶
      (orientationSystemOver F E hF W).obj (FundamentalGroupoid.mk x) :=
  ModuleCat.ofHom ((LinearMap.toSpanSingleton ℤ _ (trivGen hF b₀ hW x)) ∘ₗ
    ULift.moduleEquiv.toLinearMap)

private theorem trivGenHom_apply (x : W) (c : ULift.{w} ℤ) :
    trivGenHom hF b₀ hW x c = c.down • trivGen hF b₀ hW x :=
  -- The fibre of the restricted system is that of `B` only by unfolding, so `rw` cannot see
  -- through `ModuleCat.ofHom`; the apply lemmas are chained as terms. `Int.cast_smul_eq_zsmul`
  -- turns the module action used by `toSpanSingleton` into `zsmul`.
  (ModuleCat.ofHom_apply _ c).trans ((LinearMap.comp_apply _ _ c).trans
    ((LinearMap.toSpanSingleton_apply ℤ _ _ _).trans (Int.cast_smul_eq_zsmul ℤ _ _)))

private theorem trivGenHom_comp_map {x y : TopCat.of W}
    (p : FundamentalGroupoid.mk x ⟶ FundamentalGroupoid.mk y) :
    trivGenHom hF b₀ hW x ≫ (orientationSystemOver F E hF W).map p = trivGenHom hF b₀ hW y := by
  induction p using Path.Homotopic.Quotient.ind with
  | mk γ =>
    ext c
    have h := signLocalSystem_map_mk_signLocalSystemFiberEquiv_symm (card_fin_eq_finrank hF)
      (trivializationAt F E b₀) (modelOrientation hF)
      (γ.map continuous_subtypeVal) (fun t ↦ hW (γ t).property) (hW x.property) (hW y.property)
      (1 : ℤ)
    rw [ModuleCat.hom_comp, LinearMap.comp_apply, trivGenHom_apply, trivGenHom_apply, map_zsmul,
      pullback_obj_map, FundamentalGroupoid.map_map, ← Path.Homotopic.Quotient.mk_map, trivGen,
      trivGen]
    exact congrArg _ h

/-- The inverse over `W`: the map `H₀(W; ℤ) ⟶ H₀(W; o(E))` sending the class of `x` to the class
of the element with value `1` at `TauCeti.trivOrientation`. -/
private def trivInv : ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{w} ℤ) 0).obj
      (ModuleCat.of ℤ (ULift.{w} ℤ))).obj (TopCat.of W) ⟶
    twistedHomology (orientationSystemOver F E hF W) 0 :=
  singularHomology₀Desc _ (fun x ↦ trivGenHom hF b₀ hW x ≫ ιTwistedHomology₀ _ x) fun x y γ ↦ by
    rw [← map_ιTwistedHomology₀ (orientationSystemOver F E hF W)
      (Path.Homotopic.Quotient.mk γ : FundamentalGroupoid.mk x ⟶ FundamentalGroupoid.mk y),
      reassoc_of% (trivGenHom_comp_map hF b₀ hW)]

@[reassoc]
private theorem singularHomology₀Section_trivInv (x : W) :
    singularHomology₀Section _ (X := TopCat.of W) x ≫ trivInv hF b₀ hW =
      trivGenHom hF b₀ hW x ≫ ιTwistedHomology₀ (orientationSystemOver F E hF W) x := by
  rw [trivInv, singularHomology₀Section_singularHomology₀Desc]

/-- The trivialization over `W` and the product computation, `Hₙ₊₁(E|_W, E₀|_W) ≅ H₀(W; ℤ)`. -/
private def trivIso : (thomPairOver F E W).singularHomology (ModuleCat.of ℤ (ULift.{w} ℤ)) (n + 1) ≅
    ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{w} ℤ) 0).obj
      (ModuleCat.of ℤ (ULift.{w} ℤ))).obj (TopCat.of W) :=
  asIso (TopPair.singularHomologyMap ((trivializationAt F E b₀).thomPairOverIso ℝ hW).hom
      (ModuleCat.of ℤ (ULift.{w} ℤ)) (n + 1)) ≪≫
    prodThomPairSingularHomologyIso (ModuleCat.of ℤ (ULift.{w} ℤ)) W F 0 (n + 1) (by lia)

/-- The fibre class of `TauCeti.trivOrientation` is the class of the point. -/
private theorem trivIso_hom_fiberClassOver (x : W) :
    (trivIso hF b₀ hW).hom (fiberClassOver F E hF W x.property (trivOrientation hF b₀ hW x)) =
      singularHomology₀Section (ModuleCat.of ℤ (ULift.{w} ℤ)) (X := TopCat.of W) x
        (ULift.up 1) := by
  have h := congrArg (fun f ↦ f (ULift.up 1))
    (complZeroPairPointHom_comp_singularHomologyMap_prodThomPairFiberMap
      (ModuleCat.of ℤ (ULift.{w} ℤ)) W F (n + 1) hF x)
  simp only [ConcreteCategory.comp_apply] at h
  rw [trivIso, Iso.trans_hom, asIso_hom, ConcreteCategory.comp_apply,
    singularHomologyMap_thomPairOverIso_fiberClassOver hF _ hW x.property, Equiv.apply_symm_apply,
    localOrientation_modelOrientation, h, ← ConcreteCategory.comp_apply, Iso.inv_hom_id,
    ConcreteCategory.id_apply]

/-- `TauCeti.trivInv` followed by the twisted map and the trivialization is the identity. -/
private theorem trivInv_comp_thomPairOverHomologyMap_comp_trivIso_hom :
    trivInv hF b₀ hW ≫ thomPairOverHomologyMap F E hF W ≫ (trivIso hF b₀ hW).hom = 𝟙 _ := by
  refine singularHomology₀_hom_ext _ fun x ↦ ?_
  rw [singularHomology₀Section_trivInv_assoc, Category.comp_id]
  ext c
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply]
  rw [trivGenHom_apply, map_zsmul, map_zsmul, thomPairOverHomologyMap_ιTwistedHomology₀_apply,
    fiberHom_apply_orientationSystemOver hF W x (trivOrientation hF b₀ hW x),
    signLocalSystemFiberEquiv_trivGen, one_zsmul, map_zsmul, trivIso_hom_fiberClassOver,
    ← map_zsmul]
  congr 1
  ext
  simp

/-- The twisted map followed by the trivialization and `TauCeti.trivInv` is the identity. -/
private theorem thomPairOverHomologyMap_comp_trivIso_hom_comp_trivInv :
    thomPairOverHomologyMap F E hF W ≫ (trivIso hF b₀ hW).hom ≫ trivInv hF b₀ hW = 𝟙 _ := by
  refine twistedHomology₀_hom_ext (orientationSystemOver F E hF W) fun x ↦ ?_
  rw [Category.comp_id]
  ext σ
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply]
  rw [thomPairOverHomologyMap_ιTwistedHomology₀_apply,
    fiberHom_apply_orientationSystemOver hF W x (trivOrientation hF b₀ hW x), map_zsmul,
    trivIso_hom_fiberClassOver,
    map_zsmul, ← ConcreteCategory.comp_apply, singularHomology₀Section_trivInv,
    ConcreteCategory.comp_apply, trivGenHom_apply, one_zsmul, ← map_zsmul,
    ← eq_smul_trivGen hF b₀ hW x σ]

include hW in
private theorem isIso_thomPairOverHomologyMap_of_subset :
    IsIso (thomPairOverHomologyMap F E hF W) := by
  refine ⟨(trivIso hF b₀ hW).hom ≫ trivInv hF b₀ hW,
    thomPairOverHomologyMap_comp_trivIso_hom_comp_trivInv hF b₀ hW, ?_⟩
  rw [← cancel_mono (trivIso hF b₀ hW).hom, Category.assoc, Category.assoc,
    trivInv_comp_thomPairOverHomologyMap_comp_trivIso_hom, Category.comp_id, Category.id_comp]

end Trivial

variable (F E) in
/-- The fibre maps into the Thom pair `(E, E₀)`, as a cocone on the orientation local system. -/
private def fiberHomBaseCocone : Cocone (signLocalSystem F E ℤ (card_fin_eq_finrank hF)) where
  pt := (thomPair F E).singularHomology (ModuleCat.of ℤ (ULift.{w} ℤ)) (n + 1)
  ι :=
    { app x := fiberHom F E hF univ (mem_univ x.as) ≫ TopPair.singularHomologyMap
        (thomPairOverUnivIso F E).hom (ModuleCat.of ℤ (ULift.{w} ℤ)) (n + 1)
      naturality x y p := by
        induction p using Path.Homotopic.Quotient.ind with
        | mk γ =>
          exact (Category.assoc _ _ _).symm.trans ((eq_whisker (map_mk_comp_fiberHom hF univ γ
            (fun _ ↦ mem_univ _) (mem_univ _) (mem_univ _)) _).trans (Category.comp_id _).symm) }

variable (F E) in
/-- The map `H₀(B; o(E)) ⟶ Hₙ₊₁(E, E₀; ℤ)` sending the class of `σ` over `b` to the fibre class
`σ(o) [E_b, o]`, for any orientation `o` of `E_b`. -/
private def thomPairHomologyMap :
    twistedHomology.{0, w, w} (signLocalSystem F E ℤ (card_fin_eq_finrank hF)) 0 ⟶
      (thomPair F E).singularHomology (ModuleCat.of ℤ (ULift.{w} ℤ)) (n + 1) :=
  (isColimitTwistedHomology₀Cocone.{0, w, w}
    (signLocalSystem F E ℤ (card_fin_eq_finrank hF))).desc (fiberHomBaseCocone F E hF)

@[reassoc]
private theorem ιTwistedHomology₀_thomPairHomologyMap (b : B) :
    ιTwistedHomology₀.{0, w, w} (signLocalSystem F E ℤ (card_fin_eq_finrank hF)) b ≫
        thomPairHomologyMap F E hF =
      fiberHom F E hF univ (mem_univ b) ≫ TopPair.singularHomologyMap
        (thomPairOverUnivIso F E).hom (ModuleCat.of ℤ (ULift.{w} ℤ)) (n + 1) :=
  (isColimitTwistedHomology₀Cocone.{0, w, w} _).fac (fiberHomBaseCocone F E hF)
    (FundamentalGroupoid.mk b)

/-- Over a subset `W`, the map on the whole base restricts to the map over `W`. -/
private theorem twistedHomologyMap_subtypeVal_comp_thomPairHomologyMap (W : Set B) :
    twistedHomologyMap (TopCat.ofHom (ContinuousMap.subtypeVal W))
        (signLocalSystem F E ℤ (card_fin_eq_finrank hF)) 0 ≫ thomPairHomologyMap F E hF =
      thomPairOverHomologyMap F E hF W ≫ TopPair.singularHomologyMap
        (thomPairOverMap F E (subset_univ W) ≫ (thomPairOverUnivIso F E).hom)
        (ModuleCat.of ℤ (ULift.{w} ℤ)) (n + 1) := by
  refine twistedHomology₀_hom_ext (orientationSystemOver F E hF W) fun x ↦ ?_
  have h1 := ιTwistedHomology₀_homologyMap_assoc (signLocalSystem F E ℤ (card_fin_eq_finrank hF))
    (TopCat.ofHom (ContinuousMap.subtypeVal W)) x (thomPairHomologyMap F E hF)
  have h2 := ιTwistedHomology₀_thomPairHomologyMap (E := E) hF x.val
  have h3 := ιTwistedHomology₀_thomPairOverHomologyMap (E := E) hF W x
  have h4 :=
    fiberHom_comp_singularHomologyMap_thomPairOverMap (E := E) hF (subset_univ W) x.property
  rw [TopPair.singularHomologyMap_comp]
  -- The fibres over `x` and over `x` as a point of `B` agree only by unfolding, so the steps are
  -- chained as terms.
  exact h1.trans (h2.trans ((eq_whisker h4 _).symm.trans ((Category.assoc _ _ _).trans
    ((eq_whisker h3 _).symm.trans (Category.assoc _ _ _)))))

private theorem isIso_thomPairHomologyMap : IsIso (thomPairHomologyMap F E hF) := by
  have hK (K : Set (TopCat.of B)) (hK : IsCompact K) :
      ∃ s : Finset B, K ⊆ ⋃ b ∈ s, (trivializationAt F E b).baseSet :=
    hK.elim_finite_subcover _ (fun b ↦ (trivializationAt F E b).open_baseSet) fun b _ ↦
      mem_iUnion.2 ⟨b, mem_baseSet_trivializationAt F E b⟩
  exact isIso_of_isColimit_biUnion_baseSet (A := orientationHomologyFunctor F E hF)
    (ψ := thomPairOverHomologyMap F E hF) hF.ge
    (orientationHomologyFunctor_map_comp_thomPairOverHomologyMap hF)
    (fun _ _ ↦ epi_biprod_desc_homologyMap_subsetTwistedChainComplexMap _ _ _)
    (isZero_twistedHomology_zero_of_isEmpty (X := TopCat.of (∅ : Set B)) _)
    (fun b _ hW ↦ isIso_thomPairOverHomologyMap_of_subset hF b hW)
    (isColimitSubsetTwistedHomologyCocone (signLocalSystem F E ℤ (card_fin_eq_finrank hF))
      (monotone_biUnion_baseSet_trivializationAt F E) 0 hK)
    (thomPairHomologyMap F E hF) fun s ↦
      twistedHomologyMap_subtypeVal_comp_thomPairHomologyMap hF _

omit [FiniteDimensional ℝ F] in
variable (F E) in
/-- **The homology of the Thom pair in the rank degree, with orientation coefficients**: for a
real vector bundle `E → B` of rank `r = n + 1`, `Hᵣ(E, E₀; ℤ) ≅ H₀(B; o(E))`, the zeroth homology
of the base with coefficients in the orientation local system of `E`. -/
def thomPairSingularHomologyIsoTwistedHomology :
    (thomPair F E).singularHomology (ModuleCat.of ℤ (ULift.{w} ℤ)) (n + 1) ≅
      twistedHomology.{0, w, w}
        (signLocalSystem F E ℤ ((Fintype.card_fin (n + 1)).trans hF.symm)) 0 :=
  have := FiniteDimensional.of_finrank_eq_succ hF
  have := isIso_thomPairHomologyMap (E := E) hF
  (asIso (thomPairHomologyMap F E hF)).symm

omit [FiniteDimensional ℝ F] in
/-- The isomorphism sends the class of the local orientation of the fibre over `b` selected by an
orientation `o` of `E_b` to the class of the element of the fibre of `o(E)` with value `1` at
`o`. -/
theorem thomPairSingularHomologyIsoTwistedHomology_hom_apply (b : B)
    (o : Orientation ℝ (E b) (Fin (n + 1))) :
    (thomPairSingularHomologyIsoTwistedHomology F E hF).hom
        (TopPair.singularHomologyMap (fiberThomPairMap F E b) (ModuleCat.of ℤ (ULift.{w} ℤ))
          (n + 1) (fiberLocalOrientation hF b o).val) =
      ιTwistedHomology₀ (signLocalSystem F E ℤ ((Fintype.card_fin (n + 1)).trans hF.symm)) b
        ((signLocalSystemFiberEquiv ((Fintype.card_fin (n + 1)).trans hF.symm) o).symm 1) := by
  have := FiniteDimensional.of_finrank_eq_succ hF
  have := isIso_thomPairHomologyMap (E := E) hF
  have h : thomPairHomologyMap F E hF (ιTwistedHomology₀ (signLocalSystem F E ℤ
      (card_fin_eq_finrank hF)) b ((signLocalSystemFiberEquiv (card_fin_eq_finrank hF) o).symm 1)) =
      TopPair.singularHomologyMap (fiberThomPairMap F E b) (ModuleCat.of ℤ (ULift.{w} ℤ)) (n + 1)
        (fiberLocalOrientation hF b o).val := by
    rw [← ConcreteCategory.comp_apply, ιTwistedHomology₀_thomPairHomologyMap,
      ConcreteCategory.comp_apply, fiberHom_apply hF univ _ o, LinearEquiv.apply_symm_apply,
      one_zsmul, fiberClassOver, ← ConcreteCategory.comp_apply,
      ← TopPair.singularHomologyMap_comp, fiberThomPairOverMap_comp_thomPairOverUnivIso_hom]
  rw [← h, thomPairSingularHomologyIsoTwistedHomology, Iso.symm_hom, asIso_inv,
    ← ConcreteCategory.comp_apply, IsIso.hom_inv_id, ConcreteCategory.id_apply]

end Twisted

end TauCeti
