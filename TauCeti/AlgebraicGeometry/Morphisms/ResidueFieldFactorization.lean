/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.ResidueField
import TauCeti.AlgebraicGeometry.AffineScheme.Basic
import TauCeti.AlgebraicGeometry.Scheme.LocalSpectrum

/-!
# Morphisms from reduced schemes onto a point factor through its residue field

Let `f : Y ⟶ X` be a morphism of schemes with `Y` reduced. If every point of `Y` maps to a single
point `x`, then `f` factors through the canonical morphism `Spec κ(x) ⟶ X`, uniquely, since that
morphism is a monomorphism (Stacks, Lemma 0H1M). More generally, if `X` is locally Noetherian and
`f` maps every point into a set `E` of points with no nontrivial specializations between them, the
fibres of `f` over the points of `E` are open, and `f` factors through
`∐_{x ∈ E} Spec κ(x) ⟶ X` (Stacks, Lemma 0H1N). Thus `Spec κ(x)` is terminal among reduced
schemes over `X` whose image is `{x}`; residual gerbes of points of algebraic stacks are
a generalization of this factorization property to stacks.

## Main declarations

* `AlgebraicGeometry.Scheme.Hom.toSpecResidueField`: the factorization `Y ⟶ Spec κ(x)` of a
  morphism from a reduced scheme all of whose points map to `x`, with
  `Scheme.Hom.toSpecResidueField_fromSpecResidueField` and the uniqueness statement
  `Scheme.Hom.eq_toSpecResidueField`.
* `AlgebraicGeometry.Scheme.Hom.exists_comp_fromSpecResidueField_eq_iff`: a morphism from a
  reduced scheme factors through `Spec κ(x) ⟶ X` if and only if all of its points map to `x`.
* `AlgebraicGeometry.Scheme.Hom.isOpen_preimage_singleton`: over a locally Noetherian scheme, the
  fibres of a morphism with image in a set of points without nontrivial specializations are open.
* `AlgebraicGeometry.Scheme.Hom.exists_comp_sigmaDesc_fromSpecResidueField_eq`: such a morphism
  from a reduced scheme factors through `∐_{x ∈ E} Spec κ(x) ⟶ X`.

## Implementation notes

The ring map `κ(x) ⟶ Γ(Y, ⊤)` inducing `Scheme.Hom.toSpecResidueField` is obtained from the
compatible maps `Γ(X, U) ⟶ Γ(Y, f ⁻¹ U) = Γ(Y, ⊤)` for the open neighbourhoods `U` of `x`, which
descend to the stalk at `x` and kill its maximal ideal because `Y` is reduced. The openness of the
fibres uses that the prime ideal of `x` in an affine Noetherian neighbourhood is finitely
generated: near a point of the fibre the pullbacks of the generators have nilpotent germs, so a
neighbourhood of the point maps into the closure of `x`, and hence to `x`. This differs from the
proof in the Stacks project, which reduces to finitely many minimal primes of the image ring.

## References

* [Stacks Project, Lemma 0H1M](https://stacks.math.columbia.edu/tag/0H1M)
* [Stacks Project, Lemma 0H1N](https://stacks.math.columbia.edu/tag/0H1N)
-/

public section

open CategoryTheory Limits TopologicalSpace Opposite

namespace AlgebraicGeometry.Scheme.Hom

universe u

variable {X Y : Scheme.{u}} (f : Y ⟶ X) {x : X}

private lemma appLE_eq_zero_of_notMem_basicOpen [IsReduced Y] (hf : ∀ y, f y = x) {U : X.Opens}
    (e : ⊤ ≤ f ⁻¹ᵁ U) {s : Γ(X, U)} (hs : x ∉ X.basicOpen s) : f.appLE U ⊤ e s = 0 :=
  (basicOpen_eq_bot_iff _).mp (basicOpen_appLE_eq_bot f hf e hs)

private noncomputable def stalkToΓ (hf : ∀ y, f y = x) : X.presheaf.stalk x ⟶ Γ(Y, ⊤) :=
  colimit.desc _
    { pt := Γ(Y, ⊤)
      ι :=
        { app U := f.appLE U.unop.val ⊤ (top_le_preimage f hf U.unop.property)
          naturality U V i := by
            simp only [Functor.const_obj_map]
            exact Hom.map_appLE _ _ _ } }

private lemma germ_stalkToΓ (hf : ∀ y, f y = x) {U : X.Opens} (hxU : x ∈ U) :
    X.presheaf.germ U x hxU ≫ stalkToΓ f hf =
      f.appLE U ⊤ (top_le_preimage f hf hxU) :=
  colimit.ι_desc (F := (OpenNhds.inclusion x).op ⋙ X.presheaf) _ (op ⟨U, hxU⟩)

private lemma stalkToΓ_eq_zero [IsReduced Y] (hf : ∀ y, f y = x) {a : X.presheaf.stalk x}
    (ha : a ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk x)) : stalkToΓ f hf a = 0 := by
  obtain ⟨U, hxU, s, rfl⟩ := X.presheaf.exists_germ_eq a
  rw [← CommRingCat.comp_apply, germ_stalkToΓ]
  refine appLE_eq_zero_of_notMem_basicOpen f hf _ ?_
  rwa [X.mem_basicOpen s x hxU, ← mem_nonunits_iff, ← IsLocalRing.mem_maximalIdeal]

private noncomputable def residueFieldToΓ [IsReduced Y] (hf : ∀ y, f y = x) :
    X.residueField x ⟶ Γ(Y, ⊤) :=
  CommRingCat.ofHom <| (IsLocalRing.residue _).liftOfSurjective IsLocalRing.residue_surjective
    ⟨(stalkToΓ f hf).hom, fun a ha ↦ stalkToΓ_eq_zero f hf (by rwa [IsLocalRing.ker_residue] at ha)⟩

private lemma residue_residueFieldToΓ [IsReduced Y] (hf : ∀ y, f y = x) :
    X.residue x ≫ residueFieldToΓ f hf = stalkToΓ f hf := by
  ext a
  exact RingHom.liftOfSurjective_comp_apply _ _ _ a

/-- A morphism from a reduced scheme all of whose points map to `x` factors through
`Spec κ(x) ⟶ X` (`Scheme.Hom.toSpecResidueField_fromSpecResidueField`). -/
noncomputable def toSpecResidueField [IsReduced Y] (hf : ∀ y, f y = x) :
    Y ⟶ Spec (X.residueField x) :=
  Y.toSpecΓ ≫ Spec.map (residueFieldToΓ f hf)

/-- A morphism from a reduced scheme all of whose points map to `x` factors through
`Spec κ(x) ⟶ X`. -/
@[reassoc (attr := simp), stacks 0H1M]
theorem toSpecResidueField_fromSpecResidueField [IsReduced Y] (hf : ∀ y, f y = x) :
    f.toSpecResidueField hf ≫ X.fromSpecResidueField x = f := by
  obtain ⟨_, ⟨U, hU : IsAffineOpen U, rfl⟩, hxU : x ∈ U, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  -- Through an affine neighbourhood `U` of `x`, the composite is induced by the ring map
  -- `Γ(X, U) ⟶ 𝒪_{X,x} ⟶ κ(x) ⟶ Γ(Y, ⊤)`, which is `f.appLE U ⊤ _`.
  rw [toSpecResidueField, fromSpecResidueField, ← hU.fromSpecStalk_eq_fromSpecStalk hxU]
  simp only [IsAffineOpen.fromSpecStalk, Category.assoc, ← Spec.map_comp_assoc,
    residue_residueFieldToΓ, germ_stalkToΓ]
  exact toSpecΓ_SpecMap_appLE_fromSpec f hU _

/-- The factorization of `Scheme.Hom.toSpecResidueField` is unique, since `Spec κ(x) ⟶ X` is a
monomorphism. -/
theorem eq_toSpecResidueField [IsReduced Y] (hf : ∀ y, f y = x) {g : Y ⟶ Spec (X.residueField x)}
    (hg : g ≫ X.fromSpecResidueField x = f) : g = f.toSpecResidueField hf := by
  rw [← cancel_mono (X.fromSpecResidueField x), hg, toSpecResidueField_fromSpecResidueField]

/-- A morphism from a reduced scheme factors through `Spec κ(x) ⟶ X` if and only if all of its
points map to `x`. -/
theorem exists_comp_fromSpecResidueField_eq_iff [IsReduced Y] :
    (∃ g : Y ⟶ Spec (X.residueField x), g ≫ X.fromSpecResidueField x = f) ↔ ∀ y, f y = x := by
  refine ⟨?_, fun hf ↦ ⟨_, toSpecResidueField_fromSpecResidueField f hf⟩⟩
  rintro ⟨g, rfl⟩ y
  rw [Scheme.Hom.comp_apply, Scheme.fromSpecResidueField_apply]

/-- Let `E` be a set of points of a locally Noetherian scheme `X` with no nontrivial
specializations between them. If a morphism maps every point into `E`, the preimage of each point
is open. -/
theorem isOpen_preimage_singleton [IsLocallyNoetherian X] {E : Set X}
    (hE : ∀ x ∈ E, ∀ x' ∈ E, x ⤳ x' → x = x') (hf : ∀ y, f y ∈ E) (x : X) :
    IsOpen (f ⁻¹' {x}) := by
  rw [isOpen_iff_forall_mem_open]
  intro y hy
  rw [Set.mem_preimage, Set.mem_singleton_iff] at hy
  subst hy
  obtain ⟨_, ⟨U, hU : IsAffineOpen U, rfl⟩, hxU : f y ∈ U, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (f y)) isOpen_univ
  have : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  obtain ⟨S, hS⟩ := IsNoetherian.noetherian (hU.primeIdealOf ⟨f y, hxU⟩).asIdeal
  have hy : y ∈ f ⁻¹ᵁ U := f.mem_preimage.mpr hxU
  -- Near `y`, the pullbacks of the finitely many generators `S` of the prime of `f y` vanish.
  refine ⟨(f ⁻¹ᵁ U : Set Y) ∩ ⋂ s ∈ S, (closure (Y.basicOpen (f.app U s) : Set Y))ᶜ, ?_,
    (f ⁻¹ᵁ U).isOpen.inter (isOpen_biInter_finset fun _ _ ↦ isClosed_closure.isOpen_compl), hy,
    Set.mem_iInter₂.mpr fun s hs ↦ ?_⟩
  · rintro y' ⟨hy'U, hy'S⟩
    have hy'U : f y' ∈ U := f.mem_preimage.mp hy'U
    have hle : (hU.primeIdealOf ⟨f y, hxU⟩).asIdeal ≤ (hU.primeIdealOf ⟨f y', hy'U⟩).asIdeal := by
      rw [← hS, Ideal.span_le]
      intro s hs
      by_contra h
      rw [SetLike.mem_coe, ← hU.mem_basicOpen_iff_notMem_primeIdealOf] at h
      exact Set.mem_iInter₂.mp hy'S s hs (subset_closure (by rwa [← preimage_basicOpen]))
    have hspec := ((PrimeSpectrum.le_iff_specializes _ _).mp hle).map hU.fromSpec.continuous
    rw [hU.fromSpec_primeIdealOf, hU.fromSpec_primeIdealOf] at hspec
    exact (hE _ (hf y) _ (hf y') hspec).symm
  · exact notMem_closure_basicOpen_of_isNilpotent_germ hy <|
      f.isNilpotent_germ_app (fun y' hy' ↦ hE _ (hf y') _ (hf y) (hy'.map f.continuous)) hy
        fun h ↦ (hU.mem_basicOpen_iff_notMem_primeIdealOf ⟨f y, hxU⟩ s).mp h
          (hS ▸ Submodule.subset_span hs)

/-- Let `E` be a set of points of a locally Noetherian scheme `X` with no nontrivial
specializations between them. A morphism from a reduced scheme mapping every point into `E`
factors through the disjoint union `∐_{x ∈ E} Spec κ(x) ⟶ X` of the canonical morphisms. -/
@[stacks 0H1N]
theorem exists_comp_sigmaDesc_fromSpecResidueField_eq [IsLocallyNoetherian X] [IsReduced Y]
    {E : Set X} (hE : ∀ x ∈ E, ∀ x' ∈ E, x ⤳ x' → x = x') (hf : ∀ y, f y ∈ E) :
    ∃ g : Y ⟶ ∐ fun x : E ↦ Spec (X.residueField x),
      g ≫ Sigma.desc (fun x : E ↦ X.fromSpecResidueField x) = f := by
  -- `Y` is the disjoint union of the open fibres `W x = f ⁻¹ {x}`.
  let W (x : E) : Y.Opens := ⟨f ⁻¹' {x.val}, f.isOpen_preimage_singleton hE hf x⟩
  obtain ⟨hc⟩ := nonempty_isColimit_cofanMk_of (fun x ↦ (W x).ι)
    (eq_top_iff.mpr fun y _ ↦ by simpa using ⟨f y, hf y, rfl⟩)
    (fun x x' hxx' ↦ by
      simp only [Function.onFun, Scheme.Opens.opensRange_ι, ← Opens.coe_disjoint]
      refine Set.disjoint_left.mpr fun y hy hy' ↦ hxx' (Subtype.ext ?_)
      rw [SetLike.mem_coe, Opens.mem_mk, Set.mem_preimage, Set.mem_singleton_iff] at hy hy'
      exact hy.symm.trans hy')
  have hW (x : E) (y : (W x).toScheme) : ((W x).ι ≫ f) y = x := by
    rw [Scheme.Hom.comp_apply, Scheme.Opens.ι_apply (W x) y, ← Set.mem_singleton_iff,
      ← Set.mem_preimage]
    exact Opens.mem_mk.mp y.property
  let g (x : E) := ((W x).ι ≫ f).toSpecResidueField (hW x) ≫
    Sigma.ι (fun x : E ↦ Spec (X.residueField x)) x
  refine ⟨Cofan.IsColimit.desc hc g, Cofan.IsColimit.hom_ext hc _ _ fun x ↦ ?_⟩
  have : (W x).ι ≫ Cofan.IsColimit.desc hc g = g x := Cofan.IsColimit.fac hc g x
  simp [reassoc_of% this, g]

end AlgebraicGeometry.Scheme.Hom
